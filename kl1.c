#include <stdio.h>
#include <stdlib.h>

/* Define data structure for atoms. */
typedef char Atom;

/* Define data structure for rules. */
typedef enum {
    IMPERATIVE,
    PERMISSIVE
} RuleType;

typedef struct {
    Atom *body;
    int n_atoms_in_body;
    Atom *head;
    int n_atoms_in_head;
    RuleType ruletype;
} Rule;

/* Define data structure for definite clauses. */
typedef struct {
    Atom *body;
    int n_atoms_in_body;
    Atom head;
} DefiniteClause;

/* Safe malloc */
void *safemalloc(size_t size) {
    void *ptr = malloc(size);
    if (!ptr) {
        perror("malloc failed!");
        exit(EXIT_FAILURE);
    }
    return ptr;
}

/* Print all atoms already performed, A in paper. */
void printfacts(Atom facts[], int n_atoms_in_facts) {
    printf("Facts: ");
    for (int i=0; i<n_atoms_in_facts; i++) {
        printf("%c", facts[i]);
        if (i<n_atoms_in_facts-1) printf(", ");
    }
    printf("\n");
}

/* Print a single rule. */
void printrule(Rule r) {
    printf("Rule: ");
    for (int i = 0; i < r.n_atoms_in_body; i++) {
        printf("%c", r.body[i]);
        if (i < r.n_atoms_in_body-1) printf(", ");
    }
    printf(" ⇒ ");
    for (int i = 0; i < r.n_atoms_in_head; i++) {
        printf("%c", r.head[i]);
        if (i < r.n_atoms_in_head-1) printf(", ");
    }
    printf("\n");
}

/* Function for encoding single rule */
Rule encoderule(int n_atoms_in_body, int n_atoms_in_head, char body[], char head[], RuleType ruletype) {
    Rule r;
    r.n_atoms_in_body = n_atoms_in_body;
    r.body = safemalloc(n_atoms_in_body*sizeof(char));
    for (int i=0; i<n_atoms_in_body; i++) r.body[i] = body[i];
    r.n_atoms_in_head = n_atoms_in_head;
    r.head = safemalloc(n_atoms_in_head*sizeof(char));
    for (int i=0; i<n_atoms_in_head; i++) r.head[i] = head[i];
    r.ruletype = ruletype;
    return r;
}

/* Function for encoding definite clauses, defr in paper. */
DefiniteClause *encodedefiniteclauses(Rule rule, int *n_definite_clauses) {
    int n_defr = rule.n_atoms_in_head;

    if (rule.ruletype == PERMISSIVE) {
        n_defr += 1; // Add space for the case in which we don't chooose ay
    }

    DefiniteClause *defr = safemalloc(n_defr*sizeof(DefiniteClause));
    int offset = 0;
    
    // If head is empty, return an empty clause
    if (rule.head[0] == '/') {
        defr[0].body = safemalloc(sizeof(Atom));
        defr[0].body[0] = '/';
        defr[0].head = '/';
        defr[0].n_atoms_in_body = 1;
        *n_definite_clauses = n_defr;
        return defr;
    }

    if (rule.ruletype == PERMISSIVE) {
        defr[0].body = safemalloc(sizeof(Atom));
        defr[0].body[0] = '0';
        defr[0].head = '0';
        defr[0].n_atoms_in_body = 1;
        offset = 1;
    } 
    
    for (int i=0; i<rule.n_atoms_in_head; i++) {
        if (rule.ruletype == PERMISSIVE) {
            defr[i+offset].n_atoms_in_body = rule.n_atoms_in_body;
            defr[i+offset].body = safemalloc(rule.n_atoms_in_body*sizeof(Atom));
            for (int j=0; j<rule.n_atoms_in_body; j++) defr[i+offset].body[j] = rule.body[j];
            defr[i+offset].head = rule.head[i];
        } else {
            defr[i].n_atoms_in_body = rule.n_atoms_in_body;
            defr[i].body = safemalloc(rule.n_atoms_in_body*sizeof(Atom));
            for (int j=0; j<rule.n_atoms_in_body; j++) defr[i].body[j] = rule.body[j];
            defr[i].head = rule.head[i];
        }     
    }

    *n_definite_clauses = n_defr;
    return defr;
}


void printdefiniteclauses(DefiniteClause *defr, int n_clauses) {
    for (int i=0; i<n_clauses; i++) {
        printf("Clause %d ", i);
        for (int j=0; j<defr[i].body[j]; j++) printf("%c ", defr[i].body[j]);
        printf("=> %c\n", defr[i].head);
    }
}

int main() {
    // Add facts
    int n_atoms_in_facts = 3;
    char facts[] = {'p', 'q', 'r'};
        
    // Add rules to array of rules
    int n_of_rules = 3;
    Rule *rules = safemalloc(n_of_rules * sizeof(Rule));

    Atom r1_body[] = { 'p', 'q' };
    Atom r1_head[] = { 'r', 's' };
    rules[0] = encoderule(2, 2, r1_body, r1_head, IMPERATIVE);

    Atom r2_body[] = { 'r', 's' }; 
    Atom r2_head[] = { 'r', 's' };
    rules[1] = encoderule(2, 2, r2_body, r2_head, PERMISSIVE);
    
    Atom r3_body[] = { 'x', 'y' }; 
    Atom r3_head[] = { '/' };
    rules[2] = encoderule(2, 1, r3_body, r3_head, IMPERATIVE);
    
    // Initialize definite clauses
    int n_clauses1;
    int n_clauses2;
    int n_clauses3;
    DefiniteClause *defr1 = encodedefiniteclauses(rules[0], &n_clauses1);
    DefiniteClause *defr2 = encodedefiniteclauses(rules[1], &n_clauses2);
    DefiniteClause *defr3 = encodedefiniteclauses(rules[2], &n_clauses3);
    
    printfacts(facts, n_atoms_in_facts);

    for (int i=0; i<n_of_rules; i++) printrule(rules[i]);

    printdefiniteclauses(defr1, n_clauses1);
    printdefiniteclauses(defr2, n_clauses2);
    printdefiniteclauses(defr3, n_clauses3);

    for (int i=0; i<n_of_rules; i++) {
        free(rules[i].body);
        free(rules[i].head);
    }
    free(rules);

    return 0;
}

