#include <stdio.h>
#include <stdlib.h>

/* Define data structure for rules.  */
typedef enum {
    IMPERATIVE,
    PERMISSIVE
} RuleType;

typedef struct {
    char *body;
    int n_atoms_in_body;
    char *head;
    int n_atoms_in_head;
    RuleType ruletype;
} Rule;

/* Print all atoms already performed, A in paper. */
void printfacts(char facts[], int n_atoms_in_facts) {
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

/* Function for encoding definite clauses, defr in paper.
void defr(Rule rules[],int n_of_rules) {
    for (int i=0; i<n_of_rules; i++) {
        char *B = rules[i].body;
        char *C = rules[i].head;
        
        if(rules[i].ruletype == IMPERATIVE) {
            
        } else {

        }
    }
} */

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
