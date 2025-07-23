/*
 * Compute least models from logic rules using definite clause expansion.
 * Style: Salvatore Sanfilippo (aka antirez) — clear, minimal, human-focused.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

/* malloc wrapper: exit on failure */
void *smalloc(size_t size) {
    void *ptr = malloc(size);
    if (!ptr) {
        perror("malloc");
        exit(1);
    }
    return ptr;
}

/* realloc wrapper: exit on failure */
void *srealloc(void *ptr, size_t size) {
    void *newptr = realloc(ptr, size);
    if (!newptr) {
        perror("realloc");
        exit(1);
    }
    return newptr;
}

typedef char Atom;

typedef enum {
    IMPERATIVE,
    PERMISSIVE
} RuleType;

typedef struct {
    Atom *body;
    int n_body;
    Atom *head;
    int n_head;
    RuleType type;
} Rule;

typedef struct {
    Atom *body;
    int n_body;
    Atom head;
} Clause;

typedef struct {
    Clause *clauses;
    int n;
} Program;

typedef struct {
    Atom *acts;
    int n;
    int cap;
} Model;

void init_model(Model *M) {
    M->n = 0;
    M->cap = 4;
    M->acts = smalloc(M->cap * sizeof(Atom));
}

void push_model(Model *M, Atom a) {
    if (M->n == M->cap) {
        M->cap *= 2;
        M->acts = srealloc(M->acts, M->cap * sizeof(Atom));
    }
    M->acts[M->n++] = a;
}

Rule rule(int n_body, int n_head, Atom *body, Atom *head, RuleType type) {
    Rule r;
    r.n_body = n_body;
    r.body = smalloc(n_body * sizeof(Atom));
    for (int i = 0; i < n_body; i++) r.body[i] = body[i];
    r.n_head = n_head;
    r.head = smalloc(n_head * sizeof(Atom));
    for (int i = 0; i < n_head; i++) r.head[i] = head[i];
    r.type = type;
    return r;
}

Program *defr(Rule r, int *n_out) {
    int total = 1 << r.n_head;
    Program *out = smalloc(total * sizeof(Program));
    int count = 0;

    for (int m = 0; m < total; m++) {
        int n_clauses = 0;
        for (int i = 0; i < r.n_head; i++) if (m & (1 << i)) n_clauses++;

        if (n_clauses == 0 && r.type == IMPERATIVE) continue;

        if (n_clauses == 0 && r.type == PERMISSIVE) {
            out[count].n = 0;
            out[count].clauses = NULL;
            count++;
            continue;
        }

        out[count].n = n_clauses;
        out[count].clauses = smalloc(n_clauses * sizeof(Clause));
        int k = 0;
        for (int i = 0; i < r.n_head; i++) {
            if (m & (1 << i)) {
                out[count].clauses[k].head = r.head[i];
                out[count].clauses[k].n_body = r.n_body;
                out[count].clauses[k].body = smalloc(r.n_body * sizeof(Atom));
                for (int j = 0; j < r.n_body; j++) {
                    out[count].clauses[k].body[j] = r.body[j];
                }
                k++;
            }
        }
        count++;
    }

    *n_out = count;
    return out;
}

Program *def(Rule *rules, int n_rules, int *n_out) {
    Program **sets = smalloc(n_rules * sizeof(Program *));
    int *sizes = smalloc(n_rules * sizeof(int));

    for (int i = 0; i < n_rules; i++) sets[i] = defr(rules[i], &sizes[i]);

    int total = 1;
    for (int i = 0; i < n_rules; i++) total *= sizes[i];
    *n_out = total;

    Program *out = smalloc(total * sizeof(Program));

    for (int p = 0; p < total; p++) {
        int *choice = smalloc(n_rules * sizeof(int));
        int q = p;
        for (int i = n_rules - 1; i >= 0; i--) {
            choice[i] = q % sizes[i];
            q /= sizes[i];
        }

        int n_clauses = 0;
        for (int i = 0; i < n_rules; i++) {
            n_clauses += sets[i][choice[i]].n;
        }

        out[p].n = n_clauses;
        out[p].clauses = smalloc(n_clauses * sizeof(Clause));

        int idx = 0;
        for (int i = 0; i < n_rules; i++) {
            Program pr = sets[i][choice[i]];
            for (int j = 0; j < pr.n; j++) {
                Clause c = pr.clauses[j];
                out[p].clauses[idx].n_body = c.n_body;
                out[p].clauses[idx].body = smalloc(c.n_body * sizeof(Atom));
                for (int k = 0; k < c.n_body; k++) out[p].clauses[idx].body[k] = c.body[k];
                out[p].clauses[idx].head = c.head;
                idx++;
            }
        }
        free(choice);
    }

    for (int i = 0; i < n_rules; i++) free(sets[i]);
    free(sets);
    free(sizes);
    return out;
}

Atom *least_model(Program P, Atom *facts, int n_facts, int *out_n) {
    Model M;
    init_model(&M);
    for (int i = 0; i < n_facts; i++) push_model(&M, facts[i]);

    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < P.n; i++) {
            Clause c = P.clauses[i];
            bool ok = true;
            for (int j = 0; j < c.n_body; j++) {
                Atom a = c.body[j];
                bool found = false;
                for (int k = 0; k < M.n; k++) {
                    if (M.acts[k] == a) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    ok = false;
                    break;
                }
            }
            if (ok) {
                Atom h = c.head;
                bool in = false;
                for (int k = 0; k < M.n; k++) {
                    if (M.acts[k] == h) {
                        in = true;
                        break;
                    }
                }
                if (!in) {
                    push_model(&M, h);
                    changed = true;
                }
            }
        }
    }

    *out_n = M.n;
    return M.acts;
}

void print_atoms(Atom *a, int n) {
    for (int i = 0; i < n; i++) {
        printf("%c", a[i]);
        if (i < n - 1) printf(", ");
    }
    printf("\n");
}

int main(void) {
    Atom facts[] = { 'p', 'q', 'r' };
    int n_facts = 3;

    Rule *R = smalloc(3 * sizeof(Rule));

    Atom b1[] = { 'p', 'q' }, h1[] = { 'r', 's' };
    R[0] = rule(2, 2, b1, h1, PERMISSIVE);

    Atom b2[] = { 'r', 's' }, h2[] = { 't', 'u' };
    R[1] = rule(2, 2, b2, h2, IMPERATIVE);

    Atom b3[] = { 'x', 'y' }, h3[] = { '/' };
    R[2] = rule(2, 1, b3, h3, IMPERATIVE);

    int n_models;
    Program *P = def(R, 3, &n_models);

    for (int i = 0; i < n_models; i++) {
        int size;
        Atom *m = least_model(P[i], facts, n_facts, &size);
        print_atoms(m, size);
    }

    return 0;
}
