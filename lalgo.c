/*
 * lalgo.c -- LAlgo lexical analyzer
 *
 * PUP COSC 303 - Group 4
 *
 * RULES FOLLOWED
 *   1. NO string comparison anywhere (no strcmp/strncmp/memcmp, and <string.h>
 *      is not even included).
 *        - Tokens are recognized by DFAs simulated with TRANSITION TABLES.
 *        - Keywords are recognized by a keyword DFA (a trie turned into a
 *          transition table), NOT by comparing the lexeme to a list.
 *   2. Written in C (C99).
 *
 * BUILD :  gcc -std=c99 -Wall -Wextra -o lalgo lalgo.c
 * RUN   :  ./lalgo sample.lal        token table + lexical errors on screen,
 *                                    Symbol Table written to symbol_table.txt
 *          Only .lal files are accepted; any other filetype is rejected.
 */
 
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
 
/* ========================================================================== */
/* 1. TOKEN TYPES (names match Section 2.3.12 of the spec)                    */
/* ========================================================================== */
 
#define TOKEN_LIST(X)                                                          \
    X(IDENT) X(INTEGER) X(DECIMAL) X(STRING) X(CHAR) X(TRUE) X(FALSE)          \
    X(KW_INTEGER) X(KW_DECIMAL) X(KW_CHARACTER) X(KW_BOOLEAN) X(KW_ARRAY)      \
    X(KW_STRING)                                                               \
    X(KW_IF) X(KW_ELSE) X(KW_WHILE) X(KW_FOR) X(KW_INPUT) X(KW_OUTPUT)         \
    X(DIV) X(AND) X(OR) X(NOT)                                                 \
    X(PLUS) X(MINUS) X(STAR) X(SLASH) X(PERCENT) X(CARET)                      \
    X(ASSIGN) X(EQ) X(NEQ) X(LT) X(GT) X(LE) X(GE)                             \
    X(LPAREN) X(RPAREN) X(LBRACKET) X(RBRACKET) X(LBRACE) X(RBRACE)            \
    X(COMMA) X(SEMICOLON) X(COLON) X(DOT)                                      \
    X(NOISE_SET) X(NOISE_THE)                                                  \
    X(RES_ALGORITHM) X(RES_RETURN) X(RES_TRACE) X(RES_INVARIANT)               \
    X(INVALID) X(LINE_COMMENT) X(BLOCK_COMMENT)
 
#define X_ENUM(n) T_##n,
#define X_NAME(n) #n,
enum { TOKEN_LIST(X_ENUM) T_EOF, NUM_TOKENS };
static const char *TOKEN_NAMES[] = { TOKEN_LIST(X_NAME) "EOF" };
 
typedef struct {
    int   type;
    char *lexeme;
    int   line, col;
    int   nl_before;   /* precededByNewline   */
    int   suspected;   /* suspectedKeyword    */
} Token;
 
static Token *toks;
static int    ntoks, captoks;
 
/* ========================================================================== */
/* 2. CHARACTER CLASSES (columns of every transition table)                   */
/* ========================================================================== */
 
typedef enum {
    C_LETTER, C_DIGIT, C_UNDERSCORE, C_DOT, C_EQ, C_BANG, C_LT, C_GT,
    C_SLASH, C_STAR, C_DQUOTE, C_SQUOTE, C_BACKSLASH, C_NEWLINE, C_SPACE,
    C_TAB, C_ARITH /* + - % ^ */, C_DELIM /* ( ) [ ] { } , ; : */,
    C_OTHER   /* other printable ASCII: legal only inside literals/comments */,
    C_ILLEGAL /* control chars, lone CR, non-ASCII ... */,
    C_EOF,    /* virtual class: end of input */
    NUM_CLASSES
} CharClass;
 
static unsigned char CLS[256];          /* byte -> character class            */
static unsigned char SINGLE_TOK[256];   /* byte -> token type (1-char tokens) */
static unsigned char REL_ONE[256];      /* '=' '<' '>' -> ASSIGN LT GT        */
static unsigned char REL_TWO[256];      /* '=' '<' '>' '!' + '=' -> EQ LE GE NEQ */
 
static void init_tables(void)
{
    int c, i;
    const char *delims = "()[]{},;:";
 
    for (c = 0; c < 256; c++) CLS[c] = C_ILLEGAL;
    for (c = 33; c <= 126; c++) CLS[c] = C_OTHER;
    for (c = 'a'; c <= 'z'; c++) CLS[c] = C_LETTER;
    for (c = 'A'; c <= 'Z'; c++) CLS[c] = C_LETTER;
    for (c = '0'; c <= '9'; c++) CLS[c] = C_DIGIT;
    CLS['_'] = C_UNDERSCORE;  CLS['.'] = C_DOT;   CLS['='] = C_EQ;
    CLS['!'] = C_BANG;        CLS['<'] = C_LT;    CLS['>'] = C_GT;
    CLS['/'] = C_SLASH;       CLS['*'] = C_STAR;  CLS['"'] = C_DQUOTE;
    CLS['\''] = C_SQUOTE;     CLS['\\'] = C_BACKSLASH;
    CLS['\n'] = C_NEWLINE;    CLS[' '] = C_SPACE; CLS['\t'] = C_TAB;
    CLS['+'] = C_ARITH; CLS['-'] = C_ARITH; CLS['%'] = C_ARITH; CLS['^'] = C_ARITH;
    for (i = 0; delims[i]; i++) CLS[(unsigned char)delims[i]] = C_DELIM;
 
    SINGLE_TOK['+'] = T_PLUS;     SINGLE_TOK['-'] = T_MINUS;
    SINGLE_TOK['*'] = T_STAR;     SINGLE_TOK['%'] = T_PERCENT;
    SINGLE_TOK['^'] = T_CARET;
    SINGLE_TOK['('] = T_LPAREN;   SINGLE_TOK[')'] = T_RPAREN;
    SINGLE_TOK['['] = T_LBRACKET; SINGLE_TOK[']'] = T_RBRACKET;
    SINGLE_TOK['{'] = T_LBRACE;   SINGLE_TOK['}'] = T_RBRACE;
    SINGLE_TOK[','] = T_COMMA;    SINGLE_TOK[';'] = T_SEMICOLON;
    SINGLE_TOK[':'] = T_COLON;    SINGLE_TOK['.'] = T_DOT;
 
    REL_ONE['='] = T_ASSIGN; REL_ONE['<'] = T_LT; REL_ONE['>'] = T_GT;
    REL_TWO['='] = T_EQ;     REL_TWO['<'] = T_LE; REL_TWO['>'] = T_GE;
    REL_TWO['!'] = T_NEQ;
}
 
/* ========================================================================== */
/* 3. DFA ENGINE: M = (Q, Sigma, delta, q0, F) stored as a transition table   */
/* ========================================================================== */
 
#define MAX_STATES 8
 
typedef struct {
    signed char   delta[MAX_STATES][NUM_CLASSES];  /* -1 = implicit error state */
    unsigned char accept[MAX_STATES];              /* F                         */
    unsigned char committed[MAX_STATES];           /* stopping here = lex error */
} DFA;                                             /* q0 is always state 0      */
 
static void dfa_reset(DFA *d)
{
    int s, c;
    for (s = 0; s < MAX_STATES; s++) {
        for (c = 0; c < NUM_CLASSES; c++) d->delta[s][c] = -1;
        d->accept[s] = 0;
        d->committed[s] = 0;
    }
}
static void dfa_on(DFA *d, int from, int cls, int to)
{ d->delta[from][cls] = (signed char)to; }
 
static void dfa_on_all(DFA *d, int from, int to)   /* every real char, not EOF */
{ int c; for (c = 0; c < C_EOF; c++) d->delta[from][c] = (signed char)to; }
 
static DFA D_ID, D_NUM, D_REL, D_SLASH, D_STR, D_CHR, D_WS, D_DELIM, D_ARITH;
 
static void init_dfas(void)
{
    /* --- 2.3.2 identifiers/keywords: q0 -letter-> q1, q1 loops ------------ */
    dfa_reset(&D_ID);
    dfa_on(&D_ID, 0, C_LETTER, 1);
    dfa_on(&D_ID, 1, C_LETTER, 1);
    dfa_on(&D_ID, 1, C_DIGIT, 1);
    dfa_on(&D_ID, 1, C_UNDERSCORE, 1);
    D_ID.accept[1] = 1;
 
    /* --- 2.3.3 numbers: q1 = INTEGER, q3 = DECIMAL, q2 = "digits then ." -- */
    dfa_reset(&D_NUM);
    dfa_on(&D_NUM, 0, C_DIGIT, 1);
    dfa_on(&D_NUM, 1, C_DIGIT, 1);
    dfa_on(&D_NUM, 1, C_DOT, 2);
    dfa_on(&D_NUM, 2, C_DIGIT, 3);
    dfa_on(&D_NUM, 3, C_DIGIT, 3);
    D_NUM.accept[1] = D_NUM.accept[3] = 1;
 
    /* --- 2.3.4 relational/assignment -------------------------------------- */
    dfa_reset(&D_REL);
    dfa_on(&D_REL, 0, C_EQ, 1);   dfa_on(&D_REL, 1, C_EQ, 2);   /* = ==      */
    dfa_on(&D_REL, 0, C_BANG, 3); dfa_on(&D_REL, 3, C_EQ, 4);   /* ! (bad) != */
    dfa_on(&D_REL, 0, C_LT, 5);   dfa_on(&D_REL, 0, C_GT, 5);   /* < >       */
    dfa_on(&D_REL, 5, C_EQ, 6);                                 /* <= >=     */
    D_REL.accept[1] = D_REL.accept[2] = D_REL.accept[4] = 1;
    D_REL.accept[5] = D_REL.accept[6] = 1;
 
    /* --- 2.3.5 division / line comment / block comment -------------------- */
    dfa_reset(&D_SLASH);
    dfa_on(&D_SLASH, 0, C_SLASH, 1);              /* q1: division                */
    dfa_on(&D_SLASH, 1, C_SLASH, 2);              /* q2: line comment            */
    dfa_on(&D_SLASH, 1, C_STAR, 3);               /* q3: inside a block comment */
    dfa_on_all(&D_SLASH, 2, 2);
    dfa_on(&D_SLASH, 2, C_NEWLINE, -1);
    dfa_on_all(&D_SLASH, 3, 3);
    dfa_on(&D_SLASH, 3, C_STAR, 4);               /* q4: saw '*' in block     */
    dfa_on_all(&D_SLASH, 4, 3);
    dfa_on(&D_SLASH, 4, C_STAR, 4);
    dfa_on(&D_SLASH, 4, C_SLASH, 5);              /* q5: block comment closed    */
    D_SLASH.accept[1] = D_SLASH.accept[2] = D_SLASH.accept[5] = 1;
    D_SLASH.committed[3] = D_SLASH.committed[4] = 1;
 
    /* --- 2.3.6 string literal --------------------------------------------- */
    dfa_reset(&D_STR);
    dfa_on(&D_STR, 0, C_DQUOTE, 1);
    dfa_on_all(&D_STR, 1, 1);
    dfa_on(&D_STR, 1, C_DQUOTE, 2);
    dfa_on(&D_STR, 1, C_BACKSLASH, -1);
    dfa_on(&D_STR, 1, C_NEWLINE, -1);
    dfa_on(&D_STR, 1, C_ILLEGAL, -1);
    D_STR.accept[2] = 1;
    D_STR.committed[1] = 1;
 
    /* --- 2.3.7 character literal ------------------------------------------ */
    dfa_reset(&D_CHR);
    dfa_on(&D_CHR, 0, C_SQUOTE, 1);
    dfa_on_all(&D_CHR, 1, 2);
    dfa_on(&D_CHR, 1, C_SQUOTE, -1);
    dfa_on(&D_CHR, 1, C_BACKSLASH, -1);
    dfa_on(&D_CHR, 1, C_NEWLINE, -1);
    dfa_on(&D_CHR, 1, C_ILLEGAL, -1);
    dfa_on(&D_CHR, 2, C_SQUOTE, 3);
    D_CHR.accept[3] = 1;
    D_CHR.committed[1] = D_CHR.committed[2] = 1;
 
    /* --- 2.3.8 whitespace -------------------------------------------------- */
    dfa_reset(&D_WS);
    dfa_on(&D_WS, 0, C_SPACE, 1);  dfa_on(&D_WS, 0, C_TAB, 1);  dfa_on(&D_WS, 0, C_NEWLINE, 1);
    dfa_on(&D_WS, 1, C_SPACE, 1);  dfa_on(&D_WS, 1, C_TAB, 1);  dfa_on(&D_WS, 1, C_NEWLINE, 1);
    D_WS.accept[1] = 1;
 
    /* --- 2.3.9 delimiters -------------------------------------------------- */
    dfa_reset(&D_DELIM);
    dfa_on(&D_DELIM, 0, C_DELIM, 1);
    dfa_on(&D_DELIM, 0, C_DOT, 1);
    D_DELIM.accept[1] = 1;
 
    /* --- arithmetic (+ - * % ^) ------------------------------------------- */
    dfa_reset(&D_ARITH);
    dfa_on(&D_ARITH, 0, C_ARITH, 1);
    dfa_on(&D_ARITH, 0, C_STAR, 1);
    D_ARITH.accept[1] = 1;
}
 
/* ========================================================================== */
/* 4. KEYWORD DFA (trie stored as a transition table)              */
/* ========================================================================== */
 
typedef struct { const char *word; int type; } KwDef;
static const KwDef KEYWORDS[] = {
    {"INTEGER", T_KW_INTEGER}, {"DECIMAL", T_KW_DECIMAL},
    {"CHARACTER", T_KW_CHARACTER}, {"BOOLEAN", T_KW_BOOLEAN},
    {"ARRAY", T_KW_ARRAY}, {"STRING", T_KW_STRING},
    {"IF", T_KW_IF}, {"ELSE", T_KW_ELSE}, {"WHILE", T_KW_WHILE},
    {"FOR", T_KW_FOR}, {"INPUT", T_KW_INPUT}, {"OUTPUT", T_KW_OUTPUT},
    {"TRUE", T_TRUE}, {"FALSE", T_FALSE},
    {"DIV", T_DIV}, {"AND", T_AND}, {"OR", T_OR}, {"NOT", T_NOT},
    {"ALGORITHM", T_RES_ALGORITHM}, {"RETURN", T_RES_RETURN},
    {"TRACE", T_RES_TRACE}, {"INVARIANT", T_RES_INVARIANT},
    {"SET", T_NOISE_SET}, {"THE", T_NOISE_THE},
    {0, 0}
};
 
#define MAX_TRIE 160
static short KW_DELTA[MAX_TRIE][26];   /* state x letter -> state (0 = dead)   */
static int   KW_ACCEPT[MAX_TRIE];      /* token type if accepting, else -1     */
static int   kw_states = 1;            /* state 0 = start                      */
 
static void init_keyword_dfa(void)
{
    int w, i, s, idx;
    for (s = 0; s < MAX_TRIE; s++) KW_ACCEPT[s] = -1;
    for (w = 0; KEYWORDS[w].word; w++) {
        s = 0;
        for (i = 0; KEYWORDS[w].word[i]; i++) {
            idx = KEYWORDS[w].word[i] - 'A';
            if (KW_DELTA[s][idx] == 0) KW_DELTA[s][idx] = (short)kw_states++;
            s = KW_DELTA[s][idx];
        }
        KW_ACCEPT[s] = KEYWORDS[w].type;
    }
}
 
/* Run the keyword DFA over s[0..len). fold=1 maps a-z to A-Z first.
 * Returns the keyword token type, or -1 if the DFA dies / ends in a
 * non-accepting state. */
static int keyword_run(const char *s, int len, int fold)
{
    int state = 0, k;
    for (k = 0; k < len; k++) {
        int c = (unsigned char)s[k];
        if (fold && c >= 'a' && c <= 'z') c -= 32;
        if (c < 'A' || c > 'Z') return -1;      /* digit, '_' or lowercase */
        state = KW_DELTA[state][c - 'A'];
        if (state == 0) return -1;
    }
    return KW_ACCEPT[state];
}
 
/* ========================================================================== */
/* 5. LEXER STATE, ERRORS, TOKEN EMISSION                                     */
/* ========================================================================== */
 
typedef struct {
    char *src;
    int   len, pos, line, col;
    int   pending_nl;      /* a line feed was passed since the last real token  */
    int   aux_nl;          /* a line feed was passed since the last token of any
                              kind (comments / invalid lexemes included)       */
} Lexer;
 
typedef struct { int line, col; char msg[160]; } LexError;
static LexError *errs;
static int nerrs, caperrs;
 
static void *xrealloc(void *p, size_t n)
{
    void *q = realloc(p, n);
    if (!q) { fprintf(stderr, "out of memory\n"); exit(1); }
    return q;
}
 
static void lex_error(int line, int col, const char *fmt, ...)
{
    va_list ap;
    if (nerrs == caperrs) {
        caperrs = caperrs ? caperrs * 2 : 16;
        errs = xrealloc(errs, (size_t)caperrs * sizeof(LexError));
    }
    errs[nerrs].line = line;
    errs[nerrs].col = col;
    va_start(ap, fmt);
    vsnprintf(errs[nerrs].msg, sizeof errs[nerrs].msg, fmt, ap);
    va_end(ap);
    nerrs++;
}
 
static int class_at(const Lexer *lx, int p)
{
    if (p < 0 || p >= lx->len) return C_EOF;
    return CLS[(unsigned char)lx->src[p]];
}
 
static void advance(Lexer *lx, int n)
{
    int i;
    for (i = 0; i < n && lx->pos < lx->len; i++) {
        if (lx->src[lx->pos] == '\n') { lx->line++; lx->col = 1; lx->pending_nl = lx->aux_nl = 1; }
        else lx->col++;
        lx->pos++;
    }
}
 
static void emit(Lexer *lx, int type, int start, int len, int line, int col, int suspected)
{
    Token *t;
    int i;
    if (ntoks == captoks) {
        captoks = captoks ? captoks * 2 : 64;
        toks = xrealloc(toks, (size_t)captoks * sizeof(Token));
    }
    t = &toks[ntoks++];
    t->lexeme = xrealloc(NULL, (size_t)len + 1);
    for (i = 0; i < len; i++) t->lexeme[i] = lx->src[start + i];
    t->lexeme[len] = '\0';
    t->type = type;
    t->line = line;
    t->col = col;
    t->nl_before = lx->pending_nl;
    t->suspected = suspected;
    lx->pending_nl = lx->aux_nl = 0;
}
 
/* Comments and invalid lexemes are reported as tokens too, but they must not
 * change the precededByNewline flag of the next real token. */
static void emit_aux(Lexer *lx, int type, int start, int len, int line, int col)
{
    int keep = lx->pending_nl, vis = lx->aux_nl;
    emit(lx, type, start, len, line, col, 0);
    toks[ntoks - 1].nl_before = vis;   /* newline since the previous visible token */
    lx->pending_nl = keep;             /* real tokens keep their original flag     */
    lx->aux_nl = 0;
}
 
/* ---- DFA runner: maximal munch with "remember last accepting position" --- */
 
typedef struct {
    int len;        /* length of the longest accepted prefix (0 = none)        */
    int acc_state;  /* accepting state of that prefix, -1 if none              */
    int stop_state; /* state the DFA was in when it stopped                    */
} Run;
 
static Run dfa_run(const DFA *d, const Lexer *lx)
{
    Run r;
    int s = 0, i = 0, nx;
    r.len = 0; r.acc_state = -1;
    for (;;) {
        nx = d->delta[s][class_at(lx, lx->pos + i)];
        if (nx < 0) break;                       /* implicit error state */
        s = nx;
        i++;
        if (d->accept[s]) { r.len = i; r.acc_state = s; }
    }
    r.stop_state = s;
    return r;
}
 
/* ========================================================================== */
/* 6. MASTER LEXER DISPATCH (Section 2.3.1)                                   */
/* ========================================================================== */
 
enum { R_ILLEGAL, R_ID, R_NUM, R_REL, R_STR, R_SLASH, R_DELIM, R_ARITH,
       R_CHAR, R_WS, R_EOF };
static unsigned char DISPATCH[NUM_CLASSES];
 
static void init_dispatch(void)
{
    int c;
    for (c = 0; c < NUM_CLASSES; c++) DISPATCH[c] = R_ILLEGAL;
    DISPATCH[C_LETTER] = R_ID;
    DISPATCH[C_DIGIT] = R_NUM;
    DISPATCH[C_EQ] = DISPATCH[C_BANG] = DISPATCH[C_LT] = DISPATCH[C_GT] = R_REL;
    DISPATCH[C_DQUOTE] = R_STR;
    DISPATCH[C_SLASH] = R_SLASH;
    DISPATCH[C_DELIM] = DISPATCH[C_DOT] = R_DELIM;
    DISPATCH[C_ARITH] = DISPATCH[C_STAR] = R_ARITH;
    DISPATCH[C_SQUOTE] = R_CHAR;
    DISPATCH[C_SPACE] = DISPATCH[C_TAB] = DISPATCH[C_NEWLINE] = R_WS;
    DISPATCH[C_EOF] = R_EOF;
}
 
/* error recovery for quoted literals: consume through the closing quote, or
 * stop before a line feed / EOF. Returns total length consumed; *closed says
 * whether a closing quote was found. */
static int skip_quoted(const Lexer *lx, int quote_class, int *closed)
{
    int j = 1, c;
    for (;;) {
        c = class_at(lx, lx->pos + j);
        if (c == C_EOF || c == C_NEWLINE) { *closed = 0; return j; }
        if (c == quote_class) { *closed = 1; return j + 1; }
        j++;
    }
}
 
static void scan(Lexer *lx)
{
    for (;;) {
        int cls = class_at(lx, lx->pos);
        int line = lx->line, col = lx->col, start = lx->pos;
        Run r;
 
        switch (DISPATCH[cls]) {
 
        case R_EOF:
            emit(lx, T_EOF, start, 0, line, col, 0);
            return;
 
        case R_WS:                                    /* 2.3.8: discard */
            r = dfa_run(&D_WS, lx);
            advance(lx, r.len);
            break;
 
        case R_ID: {                                  /* 2.3.2 + keyword DFA */
            int type, susp = 0;
            r = dfa_run(&D_ID, lx);
            type = keyword_run(lx->src + start, r.len, 0);
            if (type < 0) {
                type = T_IDENT;
                if (keyword_run(lx->src + start, r.len, 1) >= 0) susp = 1;
            }
            emit(lx, type, start, r.len, line, col, susp);
            advance(lx, r.len);
            break;
        }
 
        case R_NUM: {                                 /* 2.3.3 */
            int next;
            r = dfa_run(&D_NUM, lx);
            next = class_at(lx, start + r.len);
            if (next == C_LETTER || next == C_UNDERSCORE) {   /* 2low, 1.5abc */
                int j = r.len, c;
                for (;;) {
                    c = class_at(lx, start + j);
                    if (c == C_LETTER || c == C_DIGIT || c == C_UNDERSCORE) j++;
                    else break;
                }
                lex_error(line, col, "Malformed number '%.*s'", j, lx->src + start);
                emit_aux(lx, T_INVALID, start, j, line, col);
                advance(lx, j);
            } else if (r.acc_state == 1) {                    /* INTEGER */
                long v = 0;
                int k, bad = 0;
                for (k = 0; k < r.len; k++) {
                    v = v * 10 + (lx->src[start + k] - '0');
                    if (v > 2147483647L) { bad = 1; break; }
                }
                if (bad) {
                    lex_error(line, col, "Integer literal '%.*s' out of range (max 2147483647)",
                              r.len, lx->src + start);
                    emit_aux(lx, T_INVALID, start, r.len, line, col);
                } else emit(lx, T_INTEGER, start, r.len, line, col, 0);
                advance(lx, r.len);
            } else {                                          /* DECIMAL */
                emit(lx, T_DECIMAL, start, r.len, line, col, 0);
                advance(lx, r.len);
            }
            break;
        }
 
        case R_REL:                                   /* 2.3.4 */
            r = dfa_run(&D_REL, lx);
            if (r.acc_state < 0) {                    /* only a lone '!' fails */
                lex_error(line, col, "Illegal character '!' (lone '!' is not an operator)");
                emit_aux(lx, T_INVALID, start, 1, line, col);
                advance(lx, 1);
            } else {
                unsigned char first = (unsigned char)lx->src[start];
                emit(lx, r.len == 1 ? REL_ONE[first] : REL_TWO[first],
                     start, r.len, line, col, 0);
                advance(lx, r.len);
            }
            break;
 
        case R_STR:                                   /* 2.3.6 */
            r = dfa_run(&D_STR, lx);
            if (r.acc_state == 2) {
                emit(lx, T_STRING, start, r.len, line, col, 0);
                advance(lx, r.len);
            } else {
                int closed, n = skip_quoted(lx, C_DQUOTE, &closed);
                if (closed) lex_error(line, col, "Invalid character inside string literal");
                else        lex_error(line, col, "Unterminated string literal");
                emit_aux(lx, T_INVALID, start, n, line, col);
                advance(lx, n);
            }
            break;
 
        case R_CHAR:                                  /* 2.3.7 */
            r = dfa_run(&D_CHR, lx);
            if (r.acc_state == 3) {
                emit(lx, T_CHAR, start, r.len, line, col, 0);
                advance(lx, r.len);
            } else {
                int closed, n = skip_quoted(lx, C_SQUOTE, &closed);
                if (closed) lex_error(line, col, "Invalid character literal (need exactly one permitted character)");
                else        lex_error(line, col, "Unterminated character literal");
                emit_aux(lx, T_INVALID, start, n, line, col);
                advance(lx, n);
            }
            break;
 
        case R_SLASH:                                 /* 2.3.5 */
            r = dfa_run(&D_SLASH, lx);
            if (D_SLASH.committed[r.stop_state]) {    /* block comment never closed */
                lex_error(line, col, "Unterminated block comment");
                emit_aux(lx, T_INVALID, start, lx->len - lx->pos, line, col);
                advance(lx, lx->len - lx->pos);       /* consume to EOF */
            } else if (r.acc_state == 1) {            /* division */
                emit(lx, T_SLASH, start, 1, line, col, 0);
                advance(lx, 1);
            } else {                                  /* line or block comment */
                int k, ln = line, cl = col;
                emit_aux(lx, r.acc_state == 2 ? T_LINE_COMMENT : T_BLOCK_COMMENT,
                         start, r.len, line, col);
                for (k = 0; k < r.len; k++) {         /* check body characters */
                    int c = class_at(lx, start + k);
                    if (c == C_ILLEGAL)
                        lex_error(ln, cl, "Illegal character in comment (ASCII %d)",
                                  (unsigned char)lx->src[start + k]);
                    if (c == C_NEWLINE) { ln++; cl = 1; } else cl++;
                }
                advance(lx, r.len);
            }
            break;
 
        case R_DELIM:                                 /* 2.3.9 */
        case R_ARITH:
            emit(lx, SINGLE_TOK[(unsigned char)lx->src[start]], start, 1, line, col, 0);
            advance(lx, 1);
            break;
 
        default: {                                    /* illegal standalone char */
            int ch = (unsigned char)lx->src[start];
            if (ch >= 32 && ch <= 126) lex_error(line, col, "Illegal character '%c'", ch);
            else                       lex_error(line, col, "Illegal character (ASCII %d)", ch);
            emit_aux(lx, T_INVALID, start, 1, line, col);
            advance(lx, 1);
            break;
        }
        }
    }
}
 
 
/* ========================================================================== */
/* 7. MAIN: input check, token table, lexical errors, Symbol Table file       */
/* ========================================================================== */
 
#define SYMTAB_FILE "symbol_table.txt"
 
/* Only files carrying the LAlgo extension (.lal) may be read. The test is done
 * character by character (no string comparison). Case is ignored. */
static int has_lal_ext(const char *path)
{
    int len = 0;
    while (path[len]) len++;
    return len > 4 && path[len - 4] == '.' &&
           (path[len - 3] | 32) == 'l' &&
           (path[len - 2] | 32) == 'a' &&
           (path[len - 1] | 32) == 'l';
}
 
static int is_aux_token(int t)
{
    return t == T_INVALID || t == T_LINE_COMMENT || t == T_BLOCK_COMMENT;
}
 
/* Lexeme as it should be printed. Comments and invalid lexemes can span lines
 * or hold odd bytes, so they are escaped and cut to at most max characters
 * (buf must hold max+1). Every other token is printed unchanged. */
static const char *shown(const Token *t, char *buf, int max)
{
    int o = 0, i, k, el, cut = 0;
    char e[2];
    if (!is_aux_token(t->type)) return t->lexeme;
    for (i = 0; t->lexeme[i]; i++) {
        unsigned char c = (unsigned char)t->lexeme[i];
        e[0] = (char)c; e[1] = '\0'; el = 1;
        if (c == '\n')      { e[0] = '\\'; e[1] = 'n'; el = 2; }
        else if (c == '\t') { e[0] = '\\'; e[1] = 't'; el = 2; }
        else if (c < 32 || c > 126) e[0] = '?';
        if (o + el > max) { cut = 1; break; }
        for (k = 0; k < el; k++) buf[o++] = e[k];
    }
    if (cut) { o = max - 3; buf[o++] = '.'; buf[o++] = '.'; buf[o++] = '.'; }
    buf[o] = '\0';
    return buf;
}
 
int main(int argc, char **argv)
{
    FILE *f, *sym;
    Lexer lx;
    long n, r, w;
    int i, count, invalid;
    char buf[64];
 
    if (argc < 2) {
        fprintf(stderr, "usage: %s <source.lal>\n", argv[0]);
        return 2;
    }
    if (!has_lal_ext(argv[1])) {
        fprintf(stderr, "error: '%s' is not a LAlgo source file (expected a .lal file)\n", argv[1]);
        return 2;
    }
 
    f = fopen(argv[1], "rb");
    if (!f) { fprintf(stderr, "cannot open %s\n", argv[1]); return 2; }
    fseek(f, 0, SEEK_END); n = ftell(f); fseek(f, 0, SEEK_SET);
    lx.src = xrealloc(NULL, (size_t)n + 1);
    n = (long)fread(lx.src, 1, (size_t)n, f);
    fclose(f);
 
    /* CRLF -> LF (an isolated CR stays and is later reported as illegal) */
    for (r = w = 0; r < n; r++) {
        if (lx.src[r] == '\r' && r + 1 < n && lx.src[r + 1] == '\n') continue;
        lx.src[w++] = lx.src[r];
    }
    lx.len = (int)w; lx.src[w] = '\0';
    lx.pos = 0; lx.line = 1; lx.col = 1; lx.pending_nl = lx.aux_nl = 0;
 
    init_tables(); init_dfas(); init_keyword_dfa(); init_dispatch();
    scan(&lx);
 
    /* ---- token table ---- */
    printf("=== TOKENS ===\n");
    printf("%-8s %-14s %-24s %-8s %s\n", "line:col", "type", "lexeme", "newline", "suspectedKeyword");
    for (i = 0; i < ntoks; i++)
        printf("%3d:%-4d %-14s %-24s %-8s %s\n",
               toks[i].line, toks[i].col, TOKEN_NAMES[toks[i].type],
               shown(&toks[i], buf, 24), toks[i].nl_before ? "TRUE" : "FALSE",
               toks[i].suspected ? "TRUE" : "");
 
    /* ---- lexical errors ---- */
    printf("\n=== LEXICAL ERRORS: %d ===\n", nerrs);
    for (i = 0; i < nerrs; i++)
        printf("line %d, col %d: %s\n", errs[i].line, errs[i].col, errs[i].msg);
 
    /* ---- Symbol Table (output text file) ---- */
    sym = fopen(SYMTAB_FILE, "w");
    if (!sym) { fprintf(stderr, "cannot write %s\n", SYMTAB_FILE); return 2; }
    fprintf(sym, "SYMBOL TABLE\nSource file: %s\n\n", argv[1]);
    fprintf(sym, "%-5s %-40s %-14s %s\n", "No.", "Lexeme", "Token type", "Line:Col");
    fprintf(sym, "%-5s %-40s %-14s %s\n", "---", "------", "----------", "--------");
    count = invalid = 0;
    for (i = 0; i < ntoks; i++) {
        if (toks[i].type == T_EOF) continue;
        if (toks[i].type == T_INVALID) invalid++;
        fprintf(sym, "%-5d %-40s %-14s %d:%d\n", ++count,
                shown(&toks[i], buf, 40), TOKEN_NAMES[toks[i].type],
                toks[i].line, toks[i].col);
    }
    fprintf(sym, "\nTotal entries: %d (invalid: %d)\n", count, invalid);
    fclose(sym);
    printf("\nSymbol table written to %s (%d entries)\n", SYMTAB_FILE, count);
 
    return nerrs > 0 ? 1 : 0;
}
 