#include <assert.h>
#include <errno.h>
#include <ctype.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


// Utilities

static FILE *open_file (const char *filename, const char *mode) {
    FILE *f = fopen (filename, mode);
    assert (f);                 // XXX handle properly
    return f;
}

// Really strdup, but that name may be taken.
static char *copy (const char *s) {
    char *result = malloc (strlen (s) + 1);
    assert (result);  // XXX
    strcpy (result, s);
    return result;
}

static int is_blank (const char *s) {
    const char *t = s + strspn (s, " \t");
    return *t == '\0';
}


// ANSI terminal control

#define ansi "\x1b["

static void aterm_clear_screen (void)    { printf (ansi "2J" ansi "H"); }
static void aterm_clear_to_bottom (void) { printf (ansi "J"); }
static void aterm_home (void)            { printf (ansi "H"); }
static void aterm_normal (void)          { printf (ansi "0m"); }
static void aterm_reverse (void)         { printf (ansi "7m"); }

enum {
    aterm_black = 0,
    aterm_red,
    aterm_green,
    aterm_yellow,
    aterm_blue,
    aterm_magenta,
    aterm_cyan,
    aterm_white
};
static void aterm_set_foreground (unsigned color) { printf (ansi "%um", 30 + color); }


// Evaluating expressions

typedef double Value;

static const char *get_value (Value *value, unsigned row, unsigned column);

typedef struct Context Context;
struct Context {
    const char *p;
    unsigned row;
    unsigned col;
    int token;
    Value token_value;
    const char *plaint;
};

static void complain (Context *s, const char *msg) {
    if (s->plaint == NULL) {
        s->plaint = msg;
        s->p += strlen (s->p);
    }
}

static void next (Context *s) {
    while (isspace (*s->p))
        s->p++;
    if (*s->p == '\0' || *s->p == '#')
        s->token = '\0';
    else if (isdigit (*s->p)) {
        char *endptr;
        s->token = '0';
        s->token_value = strtod (s->p, &endptr);
        s->p = endptr;
    }
    else if (strchr ("@+-*/%^()cr", *s->p))
        s->token = *s->p++;
    else {
        complain (s, "Syntax error: unknown token type");
        s->token = '\0';
    }
}

static Value parse_expr (Context *s, int precedence);

static Value parse_factor (Context *s) {
    Value v = s->token_value;
    switch (s->token) {
        case '0': next (s); return v;
        case '-': next (s); return -parse_factor (s);
        case 'c': next (s); return s->col;
        case 'r': next (s); return s->row;
        case '(':
            next (s); 
            v = parse_expr (s, 0);
            if (s->token != ')')
                complain (s, "Syntax error: expected ')'");
            next (s);
            return v;
        default:
            complain (s, "Syntax error: expected a factor");
            next (s);
            return 0;
    }
}

static Value apply (Context *s, char rator, Value lhs, Value rhs) {
    switch (rator) {
        case '+': return lhs + rhs;
        case '-': return lhs - rhs;
        case '*': return lhs * rhs;
        case '/': return lhs / rhs;  // XXX check for 0
        case '%': return fmod (lhs, rhs);
        case '^': return pow (lhs, rhs);
        case '@': {
            Value value;
            const char *plaint = get_value (&value, (unsigned) lhs, (unsigned) rhs);
            if (plaint)
                complain (s, "");
            return value;
        }
        default: assert (0); return 0;
    }
}

static Value parse_expr (Context *s, int precedence) {
    Value lhs = parse_factor (s);
    for (;;) {
        int lp, rp, rator = s->token;  // left/right precedence and operator
        switch (rator) {
            case '+': lp = 1; rp = 2; break;
            case '-': lp = 1; rp = 2; break;
            case '*': lp = 3; rp = 4; break;
            case '/': lp = 3; rp = 4; break;
            case '%': lp = 3; rp = 4; break;
            case '^': lp = 5; rp = 5; break;
            case '@': lp = 7; rp = 8; break;
            default: return lhs;
        }
        if (lp < precedence)
            return lhs;
        next (s);
        lhs = apply (s, rator, lhs, parse_expr (s, rp));
    }
}

// XXX rename
static const char *get_formula (const char *s) {
    const char *t = s + strspn (s, " \t");
    return *t == '=' ? t + 1 : NULL;
}

static const char *evaluate (Value *result, 
                             const char *expression, unsigned r, unsigned c) {
    Context context;
    context.plaint = NULL;
    context.p = get_formula (expression);
    if (!context.p)
        return "No formula";
    context.row = r;
    context.col = c;
    next (&context);
    *result = parse_expr (&context, 0);
    if (context.token != '\0')
        complain (&context, "Syntax error: unexpected token");
    return context.plaint;
}


// The array of spreadsheet cells

static const char *the_plaint = NULL;

static void error (const char *plaint) {
    if (!the_plaint)
        the_plaint = plaint;
}

typedef struct Cell Cell;
struct Cell {
    char *formula;
    enum { unknown, calculating, failed, valid } state;
    Value value;
    const char *plaint;
};

enum { rows = 24, cols = 4 };

static Cell cells[rows][cols];

static void setup (void) {
    unsigned r, c;
    for (r = 0; r < rows; ++r)
        for (c = 0; c < cols; ++c) {
            cells[r][c].formula = copy ("");
            cells[r][c].plaint = NULL;
        }
}

static void set_formula (unsigned row, unsigned col, const char *formula) {
    assert (row < rows && col < cols);
    if (cells[row][col].formula == formula) return;
    free (cells[row][col].formula);
    cells[row][col].formula = copy (formula);
    unsigned r, c;
    for (r = 0; r < rows; ++r)
        for (c = 0; c < cols; ++c) {
            cells[r][c].state = unknown;
            cells[r][c].plaint = NULL;
        }
}

static void update (unsigned r, unsigned c) {
    assert (r < rows && c < cols);
    cells[r][c].state = calculating;
    const char *plaint = evaluate (&cells[r][c].value, cells[r][c].formula, r, c);
    if (plaint) {
        cells[r][c].state = failed;
        cells[r][c].plaint = plaint;
        error (plaint);
    } else
        cells[r][c].state = valid;
}

static const char *get_value (Value *value, unsigned r, unsigned c) {
    if (rows <= r || cols <= c) {
        *value = 0;
        return "Cell out of range";
    }
    Cell *cell = &cells[r][c];
    if (cell->state == unknown)
        update (r, c);
    if (cell->state == calculating) {
        *value = 0;
        return "Circular reference";
    }
    if (cell->state == failed) {
        *value = 0;
        return cell->plaint;
    }
    assert (cell->state == valid);
    *value = cell->value;
    return NULL;
}


// File loading/saving

static const char *filename = NULL;

static void write_file (void) {
    assert (filename);
    FILE *file = open_file (filename, "w");
    unsigned r, c;
    for (r = 0; r < rows; ++r)
        for (c = 0; c < cols; ++c) {
            const char *formula = cells[r][c].formula;
            if (!is_blank (formula))
                fprintf (file, "%u %u %s\n", r, c, formula);
        }
    fclose (file);
}

static void read_file (void) {
    assert (filename);
    FILE *file = fopen (filename, "r");
    if (!file) {
        error (strerror (errno));
        return;
    }
    char line[1024];
    while (fgets (line, sizeof line, file)) {
        unsigned r, c;
        char formula[sizeof line];
        if (3 != sscanf (line, "%u %u %[^\n]", &r, &c, formula))
            error ("Bad line in file");
        else if (rows <= r || cols <= c)
            error ("Row or column number out of range in file");
        else
            set_formula (r, c, formula);
    }    
    fclose (file);
}


// UI display

enum { colwidth = 18 };

typedef enum { formulas, values } View;

static void show_at (unsigned r, unsigned c, View view) {
    char text[1024];
    unsigned color = aterm_black;
    const char *formula = get_formula (cells[r][c].formula);
    if (view == formulas || !formula)
        strncpy (text, formula ? formula : cells[r][c].formula, sizeof text);
    else {
        Value value;
        const char *plaint = get_value (&value, r, c);
        if (plaint) {
            color = aterm_red;
            strncpy (text, plaint, sizeof text);
        }
        else
            snprintf (text, sizeof text, "%*g", colwidth, value);
    }
    if (colwidth < strlen (text))
        strcpy (text + colwidth - 3, "...");
    aterm_set_foreground (color);
    printf (" %*s", colwidth, text);
    aterm_set_foreground (aterm_black);
}

static const char *orelse (const char *s1, const char *s2) {
    return s1 ? s1 : s2;
}

static void show (View view, unsigned cursor_row, unsigned cursor_col) {
    unsigned r, c;
    aterm_home ();
    printf ("%-79.79s\r\n", cells[cursor_row][cursor_col].formula);
    aterm_reverse ();
    printf ("%s%*u",
            view == formulas ? "(formulas)" : "          ",
            (int) (colwidth - sizeof "(formulas)" + 4), 0);
    for (c = 1; c < cols; ++c)
        printf (" %*u", colwidth, c);
    printf ("\r\n");
    for (r = 0; r < rows; ++r) {
        aterm_reverse ();
        printf ("%2u", r);
        aterm_normal ();
        for (c = 0; c < cols; ++c) {
            if (r == cursor_row && c == cursor_col)
                aterm_reverse ();
            show_at (r, c, view);
            if (r == cursor_row && c == cursor_col)
                aterm_normal ();
        }
        printf ("\r\n");
    }
    printf ("%-80.80s",
            orelse (the_plaint, orelse (cells[cursor_row][cursor_col].plaint, "")));
    the_plaint = NULL;
    aterm_clear_to_bottom ();
}


// Main program

static View view = values;
static unsigned row = 0;
static unsigned col = 0;

static void refresh (void) {
    show (view, row, col);
}

static char input[81];

static void show_input (void) {
    refresh ();
    printf ("? %s", input);
    fflush (stdout);
}

// Return true iff the user commits a change.
static int edit_loop (void) {
    size_t p = strlen (input);
    for (;;) {
        show_input ();
        int c = getchar ();
        if (c == '\r' || c == EOF)
            return 1;
        else if (c == 7) // C-g
            return 0;
        else if (c == '\b' || c == 127) { // backspace
            if (0 < p)
                input[--p] = '\0';
        }
        else if (p + 1 < sizeof input) {
            input[p++] = c;
            input[p] = '\0';
        }
    }
}

static void enter_formula (void) {
    strncpy (input, cells[row][col].formula, sizeof input - 1);
    if (edit_loop ())
        set_formula (row, col, input);
    else
        error ("Aborted");
}

static void copy_formula (unsigned r, unsigned c) {
    set_formula (r, c, cells[row][col].formula);
    row = r;
    col = c;
}

static void reactor_loop (void) {
    for (;;) {
        refresh ();
        int ch = getchar ();
        if      (ch == ' ') enter_formula ();
        else if (ch == 'f') view = formulas;
        else if (ch == 'h') col = (col == 0 ? 0 : col-1);        // left
        else if (ch == 'j') row = (row == 0 ? 0 : row-1);        // up
        else if (ch == 'k') row = (row+1 == rows ? row : row+1); // down
        else if (ch == 'l') col = (col+1 == cols ? col : col+1); // right
        else if (ch == 'q') break;
        else if (ch == 'v') view = values;
        else if (ch == 'w') write_file ();
        else if (ch == 'H') copy_formula (row, col == 0 ? 0 : col-1);
        else if (ch == 'J') copy_formula (row == 0 ? 0 : row-1, col);
        else if (ch == 'K') copy_formula (row+1 == rows ? row : row+1, col);
        else if (ch == 'L') copy_formula (row, col+1 == cols ? col : col+1);
        else                error ("Unknown key");
    }
}

int main (int argc, char **argv) {
    assert (argc <= 2);
    setup ();
    if (argc == 2) {
        filename = argv[1];
        read_file ();
    }
    system ("stty raw");
    aterm_clear_screen ();
    reactor_loop ();
    system ("stty sane");
    return 0;
}