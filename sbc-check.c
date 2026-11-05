/* sbc-check.c -- check that every PR line of a DPR proof is a set-blocked
 * clause with respect to all the clauses preceding it.
 *
 *     gcc -O2 -std=c99 -o sbc-check sbc-check.c
 *     ./sbc-check formula.cnf proof.pr
 *
 * This is NOT a proof checker: it says nothing about the RUP lines and it
 * does not verify that the proof refutes the formula (use dpr-trim for
 * that).  It only certifies that the redundancy used on each PR line is
 * the weak kind allowed in SBC^-, i.e. that the proof lives in SBC^- and
 * not merely in PR^-.
 *
 * Everything is held in one read-only array of literals, `buf`, with 0
 * ending each clause.  The CNF occupies buf[0..pstart), the proof
 * buf[pstart..bsize).  All the work is done with indices into it.
 *
 * Line format (as emitted by `emit_CA`):
 *
 *     <autarky> <conditional> <autarky> <negated conditional> 0
 *     \______________________/\_______________________________/
 *            clause C                   witness sigma
 *
 * The witness is located, as dpr-trim does it, at the second occurrence
 * of the clause's first literal; a line without one is a RUP/RAT line and
 * is skipped (but still enters Gamma for the lines that follow).
 *
 * The test is Observation 2.4 of Bonacina-Bonet-Kolokolova-Lauria, SAT
 * 2026: with sigma = alpha + beta, the implication alpha -> beta is a
 * conditional autarky for Gamma -- equivalently C is set-blocked by beta
 * (Proposition 2.7) -- iff
 *
 *     for every D in Gamma:  sigma(D) = 1  or  dom(beta) n vars(D) = {}
 *
 * The partition of C is read off the witness: a literal l of C belongs to
 * the autarky part beta when l is in sigma, and to the conditional part
 * when -l is in sigma.
 */
#include <stdio.h>
#include <stdlib.h>

static int  *buf;              /* every literal of CNF then proof, 0-terminated */
static long  bsize, bcap;      /* used / allocated length of buf */
static long  pstart;           /* where the proof begins */
static int   nvar;             /* from the `p cnf` header */

/* per-variable scratch, all cleared again after each check */
static signed char *sig;       /* +1: var true in sigma, -1: false, 0: untouched */
static signed char *bet;       /* 1: var in dom(beta) */
static signed char *inc;       /* +1: var occurs positively in C, -1: negatively */

static void push(int l)
{
    if (bsize == bcap) {
        bcap = bcap ? 2 * bcap : (1 << 20);
        if (!(buf = realloc(buf, bcap * sizeof *buf))) { perror("realloc"); exit(2); }
    }
    buf[bsize++] = l;
}

/* Read a DIMACS CNF or a deletion-free DPR proof: comments, the header and
 * whitespace are skipped, every other token is a literal pushed as is. */
static void slurp(const char *path, int is_cnf)
{
    FILE *f = fopen(path, "r");
    int ch, l, m;
    if (!f) { perror(path); exit(2); }
    for (;;) {
        ch = getc(f);
        if (ch == EOF) break;
        if (ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r') continue;
        if (ch == 'c' || ch == '%') {                     /* comment */
            while ((ch = getc(f)) != EOF && ch != '\n') ;
            continue;
        }
        if (ch == 'p') {                                  /* p cnf <n> <m> */
            if (fscanf(f, " cnf %d %d", &nvar, &m) != 2) {
                fprintf(stderr, "%s: malformed header\n", path); exit(2);
            }
            continue;
        }
        if (ch == 'd') {
            fprintf(stderr, "%s: deletion lines are not supported\n", path); exit(2);
        }
        ungetc(ch, f);
        if (fscanf(f, "%d", &l) != 1) {
            fprintf(stderr, "%s: malformed literal near offset %ld\n", path, ftell(f));
            exit(2);
        }
        if (l > nvar || -l > nvar) {
            fprintf(stderr, "%s: literal %d exceeds %d variables\n", path, l, nvar);
            exit(2);
        }
        push(l);
    }
    if (bsize && buf[bsize - 1] != 0) push(0);            /* tolerate a missing final 0 */
    fclose(f);
    (void) is_cnf;
}

/* Delimit the line starting at s.  Returns the index of its terminating 0
 * and stores in *clause_end the end of the clause part, which is the start
 * of the witness when there is one, and the terminating 0 otherwise. */
static long scan_line(long s, long *clause_end)
{
    long e = s, ce;
    while (buf[e] != 0) e++;
    ce = e;
    if (s >= pstart && e > s) {
        for (long i = s + 1; i < e; i++)
            if (buf[i] == buf[s]) { ce = i; break; }
    }
    *clause_end = ce;
    return e;
}

#define VAR(l)  ((l) > 0 ?  (l) : -(l))
#define SGN(l)  ((l) > 0 ?    1  :   -1)

/* Is the clause buf[cs..ce), split by the witness buf[ws..we), set-blocked
 * with respect to every clause in buf[0..cs)?  On failure the reason is
 * printed and 0 returned. */
static int check_sbc(long cs, long ce, long ws, long we, long lineno)
{
    long nbeta = 0, t;
    int ok = 1;

    /* --- mark C ------------------------------------------------------- */
    for (long i = cs; i < ce; i++)
        inc[VAR(buf[i])] = SGN(buf[i]);

    /* --- mark sigma, and split C into conditional part + beta --------- */
    for (long i = ws; i < we && ok; i++) {
        int l = buf[i], v = VAR(l), s = SGN(l);
        if (sig[v] == -s) {
            printf("line %ld: witness assigns variable %d both ways\n", lineno, v);
            ok = 0;
        }
        sig[v] = s;
        if (inc[v] == s) { bet[v] = 1; nbeta++; }         /* l in C: autarky part */
        else if (inc[v] == 0) {
            printf("line %ld: witness touches variable %d, which is not in the clause\n",
                   lineno, v);
            ok = 0;
        }
        /* inc[v] == -s : conditional part, nothing to record */
    }
    if (ok && nbeta == 0) {
        printf("line %ld: empty autarky part\n", lineno);
        ok = 0;
    }
    /* every literal of C must fall in one of the two parts */
    for (long i = cs; i < ce && ok; i++)
        if (sig[VAR(buf[i])] == 0) {
            printf("line %ld: literal %d of the clause is not covered by the witness\n",
                   lineno, buf[i]);
            ok = 0;
        }

    /* --- the autarky condition, against every preceding clause -------- */
    for (t = 0; t < cs && ok; ) {
        long dce, de = scan_line(t, &dce);
        int sat = 0, touched = 0;
        for (long i = t; i < dce; i++) {
            int l = buf[i], v = VAR(l);
            if (sig[v] == SGN(l)) { sat = 1; break; }
            if (bet[v]) touched = 1;
        }
        if (!sat && touched) {
            printf("line %ld: the autarky part touches the unsatisfied clause at offset %ld (",
                   lineno, t);
            for (long i = t; i < dce; i++) printf("%d ", buf[i]);
            printf(")\n");
            ok = 0;
        }
        t = de + 1;
    }

    /* --- clear the scratch -------------------------------------------- */
    for (long i = cs; i < ce; i++) inc[VAR(buf[i])] = 0;
    for (long i = ws; i < we; i++) { sig[VAR(buf[i])] = 0; bet[VAR(buf[i])] = 0; }
    return ok;
}

int main(int argc, char **argv)
{
    long npr = 0, nrup = 0, nbad = 0, lineno = 0;

    if (argc != 3) {
        fprintf(stderr, "usage: %s formula.cnf proof.pr\n", argv[0]);
        return 2;
    }
    slurp(argv[1], 1);
    pstart = bsize;
    slurp(argv[2], 0);

    if (!(sig = calloc(nvar + 1, 1)) || !(bet = calloc(nvar + 1, 1))
        || !(inc = calloc(nvar + 1, 1))) { perror("calloc"); return 2; }

    for (long s = pstart; s < bsize; ) {
        long ce, e = scan_line(s, &ce);
        lineno++;
        if (ce < e) {
            npr++;
            if (!check_sbc(s, ce, ce, e, lineno)) nbad++;
        } else {
            nrup++;
        }
        s = e + 1;
    }

    printf("c %ld PR lines, %ld without a witness\n", npr, nrup);
    if (nbad) {
        printf("s NOT SBC (%ld bad lines)\n", nbad);
        return 1;
    }
    printf("s SBC\n");
    return 0;
}
