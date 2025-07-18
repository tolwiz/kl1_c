#include <stdio.h>
#include <stdlib.h>

/* Define data structure for atoms. */
typedef char  Atom;

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
DefiniteClause *encodedefiniteclauses(Rule rule) {
    DefiniteClause *defr = malloc(rule.n_atoms_in_head*sizeof(DefiniteClause));

    char *B = rule.body;
    
    if (rule.ruletype == PERMISSIVE) {
        defr[0].body[0] = '/';
        defr[0].head = '/';
        defr[0].n_atoms_in_body = 0; 
    } 
    
    for (int i=0; i<rule.n_atoms_in_head; i++) {
        if (rule.ruletype == PERMISSIVE) {
            defr[i+1].body = B;
            defr[i+1].head = rule.head[i]; 
        } else {
            defr[i].body = B;
            defr[i].head = rule.head[i];
        }
    }

    return defr;
}

int main() {
    // Add facts
    int n_atoms_in_facts = 3;
    char facts[] = {'p', 'q', 'r'};
        
    // Add rules to array of rules
    int n_of_rules = 2;
    Rule *rules = malloc(n_of_rules * sizeof(Rule));

    // r1
    rules[0].n_atoms_in_body = 2;
    rules[0].body = malloc(rules[0].n_atoms_in_body*sizeof(char));
    rules[0].body[0] = 'p';
    rules[0].body[1] = 'q';
    rules[0].n_atoms_in_head = 2;
    rules[0].head = malloc(rules[0].n_atoms_in_head*sizeof(char));
    rules[0].head[0] = 'r';
    rules[0].head[1] = 's';
    rules[0].ruletype = IMPERATIVE;

    // r2
    rules[1].n_atoms_in_body = 2;
    rules[1].body = malloc(rules[1].n_atoms_in_body*sizeof(char));
    rules[1].body[0] = 'r';
    rules[1].body[1] = 's';
    rules[1].n_atoms_in_head = 2;
    rules[1].head = malloc(rules[1].n_atoms_in_head*sizeof(char));
    rules[1].head[0] = 'r';
    rules[1].head[1] = 's';
    rules[1].ruletype = PERMISSIVE;

    // Initialize definite clauses
    //DefiniteClause defr* = malloc(n_of_rules * sizeof(DefiniteClause));

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
