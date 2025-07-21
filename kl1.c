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

/* Define data structure for a single definite clause. */
typedef struct {
    Atom *body;
    int n_atoms_in_body;
    Atom head;
} DefiniteClause;

/* Define data structure for defr. */
typedef struct {
    DefiniteClause *clauses;
    int n_clauses;
} Defr;

/* Safe malloc. */
void *safe_malloc(size_t size) {
    void *ptr = malloc(size);
    if (!ptr) {
        perror("Malloc failed!");
        exit(EXIT_FAILURE);
    }
    return ptr;
}

/* Function for encoding single rule. */
Rule encode_rule(int n_atoms_in_body, int n_atoms_in_head, char body[], char head[], RuleType ruletype) {
    Rule r;
    r.n_atoms_in_body = n_atoms_in_body;
    r.body = safe_malloc(n_atoms_in_body * sizeof(char));
    for (int i = 0; i < n_atoms_in_body; i++) r.body[i] = body[i];
    r.n_atoms_in_head = n_atoms_in_head;
    r.head = safe_malloc(n_atoms_in_head * sizeof(char));
    for (int i = 0; i < n_atoms_in_head; i++) r.head[i] = head[i];
    r.ruletype = ruletype;
    return r;
}

/* Function for encoding defr. */
Defr *encode_defr(Rule rule, int *n_clause_sets) {
    int n_atoms_in_head = rule.n_atoms_in_head;

    // Void head
    if (n_atoms_in_head == 0) {
        Defr *defr = safe_malloc(sizeof(Defr));
        defr[0].n_clauses = 1;
        defr[0].clauses = safe_malloc(sizeof(DefiniteClause));
        defr[0].clauses[0].head = '/';
        defr[0].clauses[0].n_atoms_in_body = rule.n_atoms_in_body;
        defr[0].clauses[0].body = safe_malloc(rule.n_atoms_in_body * sizeof(Atom));
        for (int i = 0; i < rule.n_atoms_in_body; i++) defr[0].clauses[0].body[i] = rule.body[i];
        *n_clause_sets = 1;
        return defr;
    }

    int total_subsets = 1 << n_atoms_in_head; // 2^n possible subsets of C
    int exclude_void_subset = (rule.ruletype == IMPERATIVE) ? 1 : 0; // Exclude void subset if the rule is imperative
    Defr *defr = safe_malloc(total_subsets * sizeof(Defr));
    int n_clause_sets_generated = 0;
    for(int bitmask = exclude_void_subset; bitmask < total_subsets; bitmask++) { // Cycle through all possible binary masks ie all possible subsets of C
        int clause_count = 0;
        for (int i = 0; i < n_atoms_in_head; i++) if (bitmask & (1 << i)) clause_count++; // Count how many atoms we have in the subset mask, to know how many clauses there will be in defr for this subset
        if(clause_count == 0) continue; // For imperatives this never happens because of exclude_void_subset, and for permissives it jumps at the next iteration, since the case is already managed previously
        defr[n_clause_sets_generated].n_clauses = clause_count; 
        defr[n_clause_sets_generated].clauses   = safe_malloc(clause_count * sizeof(DefiniteClause)); // Alloc the right number of clauses in defr

        int clause_index = 0; // Every time an atom is selected in bitmask, write it in clauses[clause_index], then iterate at next slot
        for (int i = 0; i < n_atoms_in_head; i++) {
            if (bitmask & (1 << i)) {
                defr[n_clause_sets_generated].clauses[clause_index].head            = rule.head[i];
                defr[n_clause_sets_generated].clauses[clause_index].n_atoms_in_body = rule.n_atoms_in_body;
                defr[n_clause_sets_generated].clauses[clause_index].body            = safe_malloc(rule.n_atoms_in_body * sizeof(Atom));
                for (int j = 0; j < rule.n_atoms_in_body; j++) defr[n_clause_sets_generated].clauses[clause_index].body[j] = rule.body[j];
                clause_index++;
            }
        }
        n_clause_sets_generated++;
    }
    *n_clause_sets = n_clause_sets_generated;
    return defr;
}

/* Print all atoms already performed, A in paper. */
void print_facts(Atom facts[], int n_atoms_in_facts) {
    printf("Facts: ");
    for (int i=0; i<n_atoms_in_facts; i++) {
        printf("%c", facts[i]);
        if (i<n_atoms_in_facts-1) printf(", ");
    }
    printf("\n");
}

void print_rule(Rule r) {
    for (int i = 0; i < r.n_atoms_in_body; i++) {
        printf("%c", r.body[i]);
        if (i < r.n_atoms_in_body - 1) printf(", ");
    }

    if (r.ruletype == IMPERATIVE) {
        printf(" ⊢ ");
    } else {
        printf(" ⊣ ");
    }

    if (r.head[0] == '/') {
        printf("⊥");
    } else {
        for (int i = 0; i < r.n_atoms_in_head; i++) {
            printf("%c", r.head[i]);
            if (i < r.n_atoms_in_head - 1) printf(" ∨ ");
        }
    }
}

/* Function for printing a single definite clause. */
void print_definite_clause(DefiniteClause c) {
    if (c.head == '/') {
        printf("⊥ ← ");
    } else {
        printf("%c ← ", c.head);
    }
    for (int i = 0; i < c.n_atoms_in_body; i++) {
        printf("%c", c.body[i]);
        if (i < c.n_atoms_in_body - 1) printf(", ");
    }
    printf("\n");
}

/* Function for printing defr of a single rule. */
void print_defr(Defr *sets, int n_sets, Rule rule) {
    printf("defᵣ(");
    print_rule(rule);
    printf(") = {");

    for (int i = 0; i < n_sets; i++) {
        printf("{");
        for (int j = 0; j < sets[i].n_clauses; j++) {
            DefiniteClause c = sets[i].clauses[j];
            
            if (c.head == '/') {
                printf("⊥ ← ");
            } else {
                printf("%c ← ", c.head);
            }
            
            printf("{");
            for (int k = 0; k < c.n_atoms_in_body; k++) {
                printf("%c", c.body[k]);
                if (k < c.n_atoms_in_body - 1) printf(", ");
            }
            printf("}");

            if (j < sets[i].n_clauses - 1) printf(", ");
        }
        printf("}");
        if (i < n_sets - 1) printf(", ");
    }
    printf("}\n");
}

int main() {
    // Add facts
    int n_atoms_in_facts = 3;
    char facts[] = {'p', 'q', 'r'};
        
    // Add rules to array of rules
    int n_of_rules = 3;
    Rule *rules = safe_malloc(n_of_rules * sizeof(Rule));

    Atom r1_body[] = { 'p', 'q' };
    Atom r1_head[] = { 'r', 's' };
    rules[0] = encode_rule(2, 2, r1_body, r1_head, IMPERATIVE);

    Atom r2_body[] = { 'r', 's' }; 
    Atom r2_head[] = { 't', 'u' };
    rules[1] = encode_rule(2, 2, r2_body, r2_head, PERMISSIVE);
    
    Atom r3_body[] = { 'x', 'y' }; 
    Atom r3_head[] = { '/' };
    rules[2] = encode_rule(2, 1, r3_body, r3_head, IMPERATIVE);
    
    // Initialize definite clauses
    int n_clauses1;
    int n_clauses2;
    int n_clauses3;
    Defr *defr1 = encode_defr(rules[0], &n_clauses1);
    Defr *defr2 = encode_defr(rules[1], &n_clauses2);
    Defr *defr3 = encode_defr(rules[2], &n_clauses3);
    
    // Print stuff
    print_facts(facts, n_atoms_in_facts);
    printf("Rules: \n");
    for (int i = 0; i < n_of_rules; i++) {
        print_rule(rules[i]);
        printf("\n");
    }
    print_defr(defr1, n_clauses1, rules[0]);
    print_defr(defr2, n_clauses2, rules[1]);
    print_defr(defr3, n_clauses3, rules[2]);

    // Free memory allocations
    for (int i=0; i<n_of_rules; i++) {
        free(rules[i].body);
        free(rules[i].head);
    }
    free(rules);
    return 0;
}

