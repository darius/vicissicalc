#include <assert.h>
#include <errno.h>
#include <ctype.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


// ANSI screen output

#define ANSI "\x1b["

#define HOME             ANSI "H"
#define CLEAR_LINE_RIGHT ANSI "K"
#define CLEAR_TO_BOTTOM  ANSI "J"
#define CLEAR_SCREEN     ANSI "2J" HOME
#define HIDE_CURSOR      ANSI "?25l"
#define SHOW_CURSOR      ANSI "?25h"
#define NEWLINE          CLEAR_LINE_RIGHT "\r\n"

static void screen_reset(void) { printf("\x1b" "c"); fflush(stdout); }

static void set_foreground(unsigned color) { printf(ANSI "%um", 30 + color); }
static void set_background(unsigned color) { printf(ANSI "%um", 40 + color); }

// Colors. This is a macro for the sake of use in constant expressions:
#define bright(color)   (60 + (color))  
enum {
    black = 0,
    red,
    green,
    yellow,
    blue,
    magenta,
    cyan,
    white
};


// Keyboard input

// Just making up our own coding for non-ASCII keys. k is an input byte:
#define nonascii(k) (256 + 8 * (k))

enum {
    esc       = 27,
    key_up    = nonascii('A'),
    key_down  = nonascii('B'),
    key_right = nonascii('C'),
    key_left  = nonascii('D'),
    key_weirdo = nonascii(256), // Some keycode we didn't understand

    key_shift = 1<<0, // Key-chord modifiers go in the low 3 bits of our code
    key_alt   = 1<<1,
    key_ctrl  = 1<<2,
};

// N.B. here we've thrown away the m/n bits if there were any.
// TODO preserve all the info even for keys we don't understand.
static int weirdo(int last_keycode) {
    return last_keycode == EOF ? EOF : key_weirdo;
}

// Turn an input escape sequence into our own encoding of a keychord.
// m1 and n1 are from the sequence's optional modifier prefix.
static int chord(int m1, int n1, int key) {
    if (!(1 <= m1 && m1 <= 8 && 1 <= n1 && n1 <= 8))
        return weirdo(key);
    int m_bits = m1-1, n_bits = n1-1;
    if (m_bits != 0) return weirdo(key); // I dunno the meaning of nondefault m
    if (n_bits != (n_bits & 7)) return weirdo(key);
    // TODO for the Home key this would need adjustment:
    return nonascii(key) | n_bits;
}

static int get_key(void) {
    int k0 = getchar();
    if (k0 != esc) return k0;
    // We just saw the start of an esc sequence. N.B. we can't tell if
    // a bare esc key was hit by the user. We could guess it was, if
    // we were to block on reading the next byte, but that behavior
    // doesn't seem to be 100% correlated with that keyboard event,
    // and we'd need underlying OS functions in place of getchar(). So
    // we don't even try: this program doesn't use the bare esc key
    // for anything.
    int k1 = getchar();
    if (k1 != '[') return weirdo(k1);
    // This started a sequence like
    //   esc, '[', optional(digit, optional(';', digit)), character.
    // Call the digits `m1` and `n1`; they default to 1.
    int m1 = 1, n1 = 1;
    int k = getchar();
    if (isdigit(k)) {
        m1 = k - '0'; k = getchar();
        if (k == ';') {
            k = getchar();
            if (!isdigit(k)) return weirdo(k);
            n1 = k - '0'; k = getchar();
        }
    }
    return chord(m1, n1, k); // k being the last byte of the above sequence
}


 // Utilities

static void panic(const char *plaint) {
    system("stty sane"); screen_reset();
    fprintf(stderr, "%s\n", plaint);
    exit(1);
}

// Copy into dest as much of `s` as will fit.
// strncpy won't do because it can leave dest unterminated.
static void stuff(char *dest, size_t dest_size, const char *s) {
    assert(0 < dest_size);
    size_t i;
    for (i = 0; i < dest_size-1; ++i)
        if ((dest[i] = s[i]) == 0) return;
    dest[i] = 0;
}

// Really strdup, but that name may be taken.
static char *dupe(const char *s) {
    char *result = malloc(strlen(s) + 1);
    if (!result) panic("Out of memory");
    strcpy(result, s);
    return result;
}

static const char *skip_blanks(const char *s) {
    return s + strspn(s, " \t\r\n\f\v");
}

static const char *orelse(const char *s1, const char *s2) {
    return s1 ? s1 : s2;
}

static int min(int x, int y) { return x < y ? x : y; }
static int max(int x, int y) { return x > y ? x : y; }


// Evaluating cell formulas (called 'expressions' here)

typedef double Value;

typedef struct Evaluator Evaluator;
struct Evaluator {
    unsigned row, col;   // Which cell we're evaluating.
    int token;           // The kind of lexical token we just scanned.
    Value token_value;   //   Its value, if any.
    const char *s;       // The rest of the expression to scan.
    const char *plaint;  // The first error message; NULL if none yet.
};

static void fail(Evaluator *e, const char *plaint) {
    if (e->plaint == NULL) {
        // On the first failure, skip right to the end of the expression,
        // making finishing the parsing effectively a no-op.
        e->plaint = plaint;
        e->s += strlen(e->s);
    }
}

// Scan the next lexical token, and advance past it.
static void lex(Evaluator *e) {
    e->s = skip_blanks(e->s);
    if (*e->s == '\0')
        e->token = 0;   // (token 0 means end of input)
    else if (isdigit(*e->s)) {
        char *endptr;
        e->token = '0'; // (meaning a number)
        e->token_value = strtod(e->s, &endptr);
        e->s = endptr; // grumble: you can't just pass &e->s above
    }
    else if (strchr("+-*/%^@cr()", *e->s))
        e->token = *e->s++;
    else {
        fail(e, "Syntax error: unknown token type");
        e->token = 0;
    }
}

// These parser functions also evaluate as they parse, and return the value.
static Value parse_expr(Evaluator *e, int precedence);

static Value parse_factor(Evaluator *e) {
    Value v = e->token_value;
    switch (e->token) {
        case '0': lex(e); return v;
        case '-': lex(e); return -parse_factor(e);
        case 'c': lex(e); return e->col;
        case 'r': lex(e); return e->row;
        case '(':
            lex(e); 
            v = parse_expr(e, 0);
            if (e->token != ')')
                fail(e, "Syntax error: expected ')'");
            lex(e);
            return v;
        default:
            fail(e, "Syntax error: expected a factor");
            lex(e);
            return 0;
    }
}

static Value zero_divide(Evaluator *e) {
    fail(e, "Divide by 0");
    return 0;
}

static Value refer(Evaluator *e, Value r, Value c);

static Value apply(Evaluator *e, int rator, Value lhs, Value rhs) {
    switch (rator) {
        case '+': return lhs + rhs;
        case '-': return lhs - rhs;
        case '*': return lhs * rhs;
        case '/': return rhs == 0 ? zero_divide(e) : lhs / rhs;
        case '%': return rhs == 0 ? zero_divide(e) : fmod(lhs, rhs);
        case '^': return pow(lhs, rhs); // XXX report domain errors
        case '@': return refer(e, lhs, rhs);
        default: assert(0); return 0;
    }
}

// Parse an infix subexpression, in the right-context of an operator
// binding of tightness `precedence` (lower numbers meaning less tightly).
// (This method is called precedence-climbing.)
static Value parse_expr(Evaluator *e, int precedence) {
    Value lhs = parse_factor(e); // left-hand side of a potentially infix expr
    for (;;) {
        int lp, rp, rator = e->token;  // left/right precedence and operator
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
        if (lp < precedence) return lhs;
        lex(e);
        lhs = apply(e, rator, lhs, parse_expr(e, rp));
    }
}

// Evaluate a complete formula.
static const char *evaluate(Value *result, Evaluator *e) {
    lex(e);
    *result = parse_expr(e, 0);
    if (e->token != 0) fail(e, "Syntax error: unexpected token");
    return e->plaint;
}


// The array of spreadsheet cells

static const char *the_plaint = NULL;

static void oops(const char *plaint) {
    if (!the_plaint)
        the_plaint = plaint;
}

typedef struct Cell Cell;
struct Cell {
    char *text;          // malloced
    const char *plaint;  // in static memory
    Value value;         // valid if plaint is NULL
};

// These other states for a cell's plaint have special meaning:
static const char stale[] = "Stale"; // N.B. never seen in the UI.
static const char cycle[] = "Cycle";
static const char no_formula[] = "No value for referred cell";

enum { nrows = 20, ncols = 4 };
static Cell cells[nrows][ncols];

// Invalidate any cached cell values, because a formula might have changed.
static void text_updated(void) {
    for (unsigned r = 0; r < nrows; ++r)
        for (unsigned c = 0; c < ncols; ++c)
            cells[r][c].plaint = stale;
}

static void set_up(void) {
    for (unsigned r = 0; r < nrows; ++r)
        for (unsigned c = 0; c < ncols; ++c)
            cells[r][c].text = dupe("");
    text_updated();
}

// (You should use set_text() by default; set_text_only() is for when
// you want to amortize text_updated() over a whole batch of changes.)
static void set_text_only(unsigned row, unsigned col, const char *text) {
    assert(row < nrows && col < ncols);
    if (cells[row][col].text == text) return;
    free(cells[row][col].text);
    cells[row][col].text = dupe(text);
}

static void set_text(unsigned row, unsigned col, const char *text) {
    set_text_only(row, col, text);
    text_updated();
}

// A formula, if it's given, follows the '=' prefix.
static const char *find_formula(const char *s) {
    const char *t = skip_blanks(s);
    return *t == '=' ? t + 1 : NULL;
}

// Reevaluate the cell at (r,c).
static void recalculate(unsigned r, unsigned c) {
    assert(r < nrows && c < ncols);
    Cell *cell = &cells[r][c];
    const char *formula = find_formula(cell->text);
    Evaluator evaluator = {.row = r, .col = c, .s = formula, .plaint = NULL};
    cell->plaint = cycle; // Provisionally.
    cell->plaint = !formula ? no_formula : evaluate(&cell->value, &evaluator);
    oops(cell->plaint);
}

// Set *value to the value of the cell at (r,c), unless computing it
// yields an error. Return the plaint.
static const char *get_value(Value *value, unsigned r, unsigned c) {
    if (nrows <= r || ncols <= c)
        return "Cell out of range";
    Cell *cell = &cells[r][c];
    if (cell->plaint == stale) recalculate(r, c);
    if (!cell->plaint) *value = cell->value;
    return cell->plaint;
}

// The `r@c` operation in expressions, for row r, column c.
static Value refer(Evaluator *e, Value r, Value c) {
    if (r != (int)r || c != (int)c) {
        fail(e, "Non-integer cell coordinate");
        return 0;
    }
    Value value = 0;
    const char *plaint = get_value(&value, (int)r, (int)c);
    if (plaint && plaint != no_formula && plaint != cycle) plaint = "";
    if (plaint) fail(e, plaint);
    // A plaint of "" is for when there's an error at the other end of
    // the reference, but we don't want to redundantly report it here,
    // ('here' meaning for the cell making the reference to the other
    // cell) since the same plaint already shows over there in the
    // cell-to-blame. The "Cycle" case propagates through because we
    // don't track *who* to blame for a cycle.
    return value;
}


// Entering or editing a line of text

static char input[81];

// Return true iff the user commits a change.
static int edit_input(void) {
    size_t p = strlen(input);
    for (;;) {
        printf("\r" CLEAR_LINE_RIGHT "? %s" SHOW_CURSOR, input); fflush(stdout);
        int key = get_key();
        printf(HIDE_CURSOR);
        if (key == '\r' || key == EOF)
            return 1;
        else if (key == 7) // ctrl-G to abort
            return 0;
        else if (key == '\b' || key == 127) { // backspace
            if (0 < p)
                input[--p] = '\0';
        }
        else if (isprint(key) && p+1 < sizeof input) {
            input[p++] = key;
            input[p] = '\0';
            putchar(key); fflush(stdout);
        }
    }
}


// Loading and saving of files

static FILE *open_file(const char *filename, const char *mode,
                       const char *plaint) {
    FILE *file = fopen(filename, mode);
    if (!file) oops(orelse(plaint, strerror(errno)));
    return file;
}

static char spreadsheet_filename[1024]; // (wish I could use PATH_MAX)

static void write_file(void) {
    stuff(input, sizeof input, spreadsheet_filename);
    if (!edit_input()) {
        oops("Aborted");
        return;
    }
    stuff(spreadsheet_filename, sizeof spreadsheet_filename, input);

    FILE *file = open_file(spreadsheet_filename, "w", NULL);
    if (!file) return;
    for (unsigned r = 0; r < nrows; ++r)
        for (unsigned c = 0; c < ncols; ++c) {
            const char *text = cells[r][c].text;
            if (*skip_blanks(text))
                fprintf(file, "%u %u %s\n", r, c, text);
        }
    fclose(file);
    oops("File written"); // (The message is not really an oops, though.)
}

static void read_file(void) {
    assert(*spreadsheet_filename); // Should be nonempty if we get here.
    FILE *file = open_file(spreadsheet_filename, "r", "Fresh file");
    if (!file) return;
    char line[1024];
    while (fgets(line, sizeof line, file)) {
        unsigned r, c;
        char text[sizeof line];
        if (3 != sscanf(line, "%u %u %[^\n]", &r, &c, text))
            oops("Bad line in file");
        else if (nrows <= r || ncols <= c)
            oops("Row or column number out of range in file");
        else
            set_text_only(r, c, text);
    }
    text_updated();
    fclose(file);
}


// UI display

enum { colwidth = 18 };

typedef struct Colors Colors;
struct Colors {
    unsigned fg, bg;
};
static void set_color(Colors colors) {
    set_background(colors.bg);
    set_foreground(colors.fg);
}

typedef struct Style Style;
struct Style {
    Colors unhighlighted, highlighted;
};
static Style ok_style = {
    .unhighlighted = { .fg = black,         .bg = white },
    .highlighted   = { .fg = bright(white), .bg = bright(blue) }
};
static Style oops_style = {
    .unhighlighted = { .fg = black,         .bg = bright(cyan) },
    .highlighted   = { .fg = bright(white), .bg = bright(red) }
};
static Colors border_colors = { .fg = blue, .bg = bright(yellow) };

typedef enum { formulas, values } View;

// For the cell at (r,c), show its content or formula according to
// `view`, in style according to `highlighted`.
static void show_at(unsigned r, unsigned c, View view, int highlighted) {
    char text[1024];
    const Style *style = &ok_style;
    const char *formula = find_formula(cells[r][c].text);
    if (view == formulas || !formula)
        stuff(text, sizeof text, orelse(formula, cells[r][c].text));
    else {
        Value value;
        const char *plaint = get_value(&value, r, c);
        if (plaint) {
            style = &oops_style;
            stuff(text, sizeof text, plaint);
        }
        else
            snprintf(text, sizeof text, "%*g", colwidth, value);
    }
    if (colwidth < strlen(text))
        strcpy(text + colwidth - 3, "...");
    set_color(highlighted ? style->highlighted : style->unhighlighted);
    printf(" %*s", colwidth, text);
}

static void show(View view, unsigned cursor_row, unsigned cursor_col) {
    printf(HOME);
    set_color(ok_style.unhighlighted);
    printf("%-79.79s", cells[cursor_row][cursor_col].text);
    printf(NEWLINE);
    set_color(border_colors);
    printf("%s%*u",
           view == formulas ? "(formulas)" : "          ",
           (int) (colwidth - sizeof "(formulas)" + 4), 0);
    for (unsigned c = 1; c < ncols; ++c)
        printf(" %*u", colwidth, c);
    printf(NEWLINE);
    for (unsigned r = 0; r < nrows; ++r) {
        set_color(border_colors);
        printf("%2u", r);
        for (unsigned c = 0; c < ncols; ++c)
            show_at(r, c, view, r == cursor_row && c == cursor_col);
        printf(NEWLINE);
    }
    const char *focus_plaint = cells[cursor_row][cursor_col].plaint;
    if (focus_plaint == stale) focus_plaint = NULL; // `stale` here means not a formula cell
    printf("%-80.80s", orelse(the_plaint, orelse(focus_plaint, "")));
    printf(CLEAR_TO_BOTTOM);
}


// Main interaction loop and main program

static View view = values;
static int row = 0, col = 0;  // The cursor

static void enter_text(void) {
    stuff(input, sizeof input, cells[row][col].text);
    if (edit_input())
        set_text(row, col, input);
    else
        oops("Aborted");
}

static void copy_text(unsigned r, unsigned c) {
    set_text(r, c, cells[row][col].text);
    row = r;
    col = c;
}

static void react(int key) {
    switch (key) {
    case ' ': enter_text(); break;

    case 'w': write_file(); break;

    case 'f': view = (view == formulas ? values : formulas); break;

    case key_left:  col = max(col-1, 0);       break;
    case key_right: col = min(col+1, ncols-1); break;
    case key_down:  row = min(row+1, nrows-1); break;
    case key_up:    row = max(row-1, 0);       break;

    case key_ctrl|key_left:  copy_text(row,         max(col-1, 0));       break;
    case key_ctrl|key_right: copy_text(row,         min(col+1, ncols-1)); break;
    case key_ctrl|key_down:  copy_text(min(row+1, nrows-1), col);         break;
    case key_ctrl|key_up:    copy_text(max(row-1, 0),       col);         break;

    default: oops("Unknown key");
    }
}

static void reactor_loop(void) {
    for (;;) {
        show(view, row, col);
        the_plaint = NULL;
        int key = get_key();
        if (key == 'q') break;
        react(key);
    }
}

int main(int argc, char **argv) {
    if (2 < argc) panic("usage: vicissicalc [filename]");
    set_up();
    if (argc == 2) {
        stuff(spreadsheet_filename, sizeof spreadsheet_filename, argv[1]);
        read_file();
    }
    system("stty raw -echo");
    printf(HIDE_CURSOR CLEAR_SCREEN);
    reactor_loop();
    system("stty sane"); screen_reset();
    return 0;
}
