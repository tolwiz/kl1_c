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

/* Function for encoding definite clauses, defr in paper. */
DefiniteClause *encodedefiniteclauses(Rule rule, int *n_definite_clauses) {
    int n_defr = rule.n_atoms_in_head;

    if (rule.ruletype == PERMISSIVE) {
        n_defr += 1; // Add space for the case in which we don't chooose ay
    }

    DefiniteClause *defr = safemalloc(n_defr*sizeof(DefiniteClause));

    char *B = rule.body;
   
   int offset = 0;
    if (rule.ruletype == PERMISSIVE) {
        defr[0].body = safemalloc(sizeof(Atom));
        defr[0].body[0] = '0';
        defr[0].head = '0';
        defr[0].n_atoms_in_body = 1;
        offset = 1;
    } 
    
    for (int i=0; i<rule.n_atoms_in_head; i++) {
        if (rule.ruletype == PERMISSIVE) {
            defr[i+offset].body = B;
            defr[i+offset].head = rule.head[i];
            defr[i+offset].n_atoms_in_body = rule.n_atoms_in_body;
        }     
    }

    *n_definite_clauses = n_defr;
    return defr;
}

int main() {
    // Add facts
    int n_atoms_in_facts = 3;
    char facts[] = {'p', 'q', 'r'};
        
    // Add rules to array of rules
    int n_of_rules = 2;
    Rule *rules = safemalloc(n_of_rules * sizeof(Rule));

    // r1
    rules[0].n_atoms_in_body = 2;
    rules[0].body = safemalloc(rules[0].n_atoms_in_body*sizeof(char));
    rules[0].body[0] = 'p';
    rules[0].body[1] = 'q';
    rules[0].n_atoms_in_head = 2;
    rules[0].head = safemalloc(rules[0].n_atoms_in_head*sizeof(char));
    rules[0].head[0] = 'r';
    rules[0].head[1] = 's';
    rules[0].ruletype = IMPERATIVE;

    // r2
    rules[1].n_atoms_in_body = 2;
    rules[1].body = safemalloc(rules[1].n_atoms_in_body*sizeof(char));
    rules[1].body[0] = 'r';
    rules[1].body[1] = 's';
    rules[1].n_atoms_in_head = 2;
    rules[1].head = safemalloc(rules[1].n_atoms_in_head*sizeof(char));
    rules[1].head[0] = 'r';
    rules[1].head[1] = 's';
    rules[1].ruletype = PERMISSIVE;

    // Initialize definite clauses
    //DefiniteClause defr* = safemalloc(n_of_rules * sizeof(DefiniteClause));

    printfacts(facts, n_atoms_in_facts);

    for (int i=0; i<n_of_rules; i++) {
        printrule(rules[i]);
    }

    for (int i=0; i<n_of_rules; i++) {
        free(rules[i].body);
        free(rules[i].head);
    }
    free(rules);

    return 0;
}
