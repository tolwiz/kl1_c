#include <stdio.h>
#include <stdlib.h>

/* Safe malloc. */
void *safe_malloc(size_t size) {
    void *ptr = malloc(size);
    if (!ptr) {
        perror("Malloc failed!");
        exit(EXIT_FAILURE);
    }
    return ptr;
}

/* Define data structure for a single atom. */
typedef char Atom;

/* Define data structure for a single rule. */
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

/* Define data structure for a single definite program. */
typedef struct {
    DefiniteClause *clauses;
    int n_clauses;
} DefiniteProgram;

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
DefiniteProgram *encode_defr(Rule rule, int *n_definite_programs) {
    int n_atoms_in_head = rule.n_atoms_in_head;

    /* Void head. */
    if (n_atoms_in_head == 0) {
        DefiniteProgram *defr = safe_malloc(sizeof(DefiniteProgram));
        defr[0].n_clauses = 1;
        defr[0].clauses = safe_malloc(sizeof(DefiniteClause));
        defr[0].clauses[0].head = '/';
        defr[0].clauses[0].n_atoms_in_body = rule.n_atoms_in_body;
        defr[0].clauses[0].body = safe_malloc(rule.n_atoms_in_body * sizeof(Atom));
        for (int i = 0; i < rule.n_atoms_in_body; i++) defr[0].clauses[0].body[i] = rule.body[i];
        *n_definite_programs = 1;
        return defr;
    }

    /* 2^n possible subsets of C. */
    int total_subsets = 1 << n_atoms_in_head;
    DefiniteProgram *defr = safe_malloc(total_subsets * sizeof(DefiniteProgram));
    int n_definite_programs_generated = 0;

    /* Cycle through all possible binary masks ie all 
     * possible subsets of C. */
    for(int bitmask = 0; bitmask < total_subsets; bitmask++) { 
        int clause_count = 0;

        /* Count how many atoms we have in the subset 
         * mask, to know how many clauses there will be in 
         * defr for this subset. */
        for (int i = 0; i < n_atoms_in_head; i++) 
            if (bitmask & (1 << i)) clause_count++; 

        /* If void subset and rule is imperative, skip. */
        if (clause_count == 0 && rule.ruletype == IMPERATIVE) continue;

        /* If void subset and rule is permissive, add empty program. */
        if (clause_count == 0 && rule.ruletype == PERMISSIVE) {
            defr[n_definite_programs_generated].n_clauses = 0;
            defr[n_definite_programs_generated].clauses = NULL;
            n_definite_programs_generated++;
            continue;
        }
        defr[n_definite_programs_generated].n_clauses = clause_count; 

        /* Allocate the right number of clauses in defr. */
        defr[n_definite_programs_generated].clauses = safe_malloc(clause_count * sizeof(DefiniteClause));

        /* Every time an atom is selected in bitmask, write 
         * it in clauses[clause_index], then iterate at next slot. */
        int clause_index = 0; 
        for (int i = 0; i < n_atoms_in_head; i++) {
            if (bitmask & (1 << i)) {
                defr[n_definite_programs_generated].clauses[clause_index].head = rule.head[i];
                defr[n_definite_programs_generated].clauses[clause_index].n_atoms_in_body = rule.n_atoms_in_body;
                defr[n_definite_programs_generated].clauses[clause_index].body = safe_malloc(rule.n_atoms_in_body * sizeof(Atom));
                for (int j = 0; j < rule.n_atoms_in_body; j++) 
                    defr[n_definite_programs_generated].clauses[clause_index].body[j] = rule.body[j];
                clause_index++;
            }
        }
        n_definite_programs_generated++;
    }
    *n_definite_programs = n_definite_programs_generated;
    return defr;
}

/* Function for translating a set of rules into a set of 
 * definite programs, namely def(R). */
DefiniteProgram *encode_def(Rule *rules, int n_rules, int *n_total_programs) {
    
    /* Compute defᵣ(r) for each rule. */
    int *n_options = safe_malloc(n_rules * sizeof(int)); // Total number of definite programs 
    DefiniteProgram **defrs = safe_malloc(n_rules * sizeof(DefiniteProgram *));    
    for (int i = 0; i < n_rules; i++) {
        defrs[i] = encode_defr(rules[i], &n_options[i]);
    }
    
    /* Compute total number of definite programs in def(R). */
    int total = 1;
    for (int i = 0; i < n_rules; i++) total *= n_options[i];
    *n_total_programs = total;
    DefiniteProgram *all_programs = safe_malloc(total * sizeof(DefiniteProgram));
    
    /* Cycle through all the combinations. p is the index for the 
     * current combination, compute which element of defᵣ(rᵢ) to choose 
     * for each rule, using division and module to run through all 
     * combinations. */
    for (int p = 0; p < total; p++) {
        int *choice = safe_malloc(n_rules * sizeof(int));
        int quotient = p;
        for (int i = n_rules - 1; i >= 0; i--) {
            choice[i] = quotient % n_options[i];
            quotient /= n_options[i];
        }
        
        /* Unify all choosen clauses in a definite program, adding
         * the number of total clauses of the current combination and 
         * allocating the space for the current definite program. */
        int total_clauses = 0;
        for (int i = 0; i < n_rules; i++) {
            total_clauses += defrs[i][choice[i]].n_clauses;
        }
        all_programs[p].n_clauses = total_clauses;
        all_programs[p].clauses = safe_malloc(total_clauses * sizeof(DefiniteClause));
        
        /* Copy the clauses from each choosen definite program. */
        int idx = 0;
        for (int i = 0; i < n_rules; i++) {
            DefiniteProgram selected = defrs[i][choice[i]];
            for (int j = 0; j < selected.n_clauses; j++) {
                all_programs[p].clauses[idx].n_atoms_in_body = selected.clauses[j].n_atoms_in_body;
                all_programs[p].clauses[idx].body = safe_malloc(selected.clauses[j].n_atoms_in_body * sizeof(Atom));
                for (int k = 0; k < selected.clauses[j].n_atoms_in_body; k++) {
                    all_programs[p].clauses[idx].body[k] = selected.clauses[j].body[k];
                }
                all_programs[p].clauses[idx].head = selected.clauses[j].head;
                idx++;
            }
        }
        free(choice);
    }
    for (int i = 0; i < n_rules; i++) free(defrs[i]);
    free(defrs);
    free(n_options);
    return all_programs;
}

/* Function for printing all atoms already performed, A in paper. */
void print_facts(Atom facts[], int n_atoms_in_facts) {
    printf("Facts: ");
    for (int i = 0; i < n_atoms_in_facts; i++) {
        printf("%c", facts[i]);
        if (i < n_atoms_in_facts-1) printf(", ");
    }
    printf("\n");
}

/* Function for printing a single rule. */
void print_rule(Rule r) {
    for (int i = 0; i < r.n_atoms_in_body; i++) {
        printf("%c", r.body[i]);
        if (i < r.n_atoms_in_body - 1) printf("∧");
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
            if (i < r.n_atoms_in_head - 1) printf("∨");
        }
    }
}

/* Function for printing a single definite clause, with optional trailing comma. */
void print_definite_clause(DefiniteClause c, int with_comma) {
    if (c.head == '/') {
        printf("⊥ ← ");
    } else {
        printf("%c ← ", c.head);
    }
    if (c.n_atoms_in_body == 0) {
        printf("{}");
    } else {
        printf("{");
        for (int i = 0; i < c.n_atoms_in_body; i++) {
            printf("%c", c.body[i]);
            if (i < c.n_atoms_in_body - 1) printf(", ");
        }
        printf("}");
    }
    if (with_comma) printf(", ");
}

/* Function for printing a single definite program. */
void print_definite_program(DefiniteProgram prog) {
    printf("{");
    for (int j = 0; j < prog.n_clauses; j++) {
        print_definite_clause(prog.clauses[j], j < prog.n_clauses - 1);
    }
    printf("}");
}

/* Function for printing defᵣ(r). */
void print_defr(DefiniteProgram *sets, int n_sets, Rule rule) {
    printf("defᵣ(");
    print_rule(rule);
    printf(") = {\n");
    for (int i = 0; i < n_sets; i++) {
        printf("  ");
        print_definite_program(sets[i]);
        if (i < n_sets - 1) printf(",\n");
        else printf("\n");
    }
    printf("}\n");
}

/* Function for printing def(R). */
void print_def(DefiniteProgram *def, int n_programs) {
    printf("def(R) = {\n");
    for (int i = 0; i < n_programs; i++) {
        printf("  ");
        print_definite_program(def[i]);
        if (i < n_programs - 1) printf(",\n");
        else printf("\n");
    }
    printf("}\n");
}

int main() {
    int n_atoms_in_facts = 3;
    char facts[] = {'p', 'q', 'r'};
        
    int n_of_rules = 2;
    Rule *rules = safe_malloc(n_of_rules * sizeof(Rule));

    Atom r1_body[] = { 'p' };
    Atom r1_head[] = { 'q', 'r' };
    rules[0] = encode_rule(1, 2, r1_body, r1_head, PERMISSIVE);

    Atom r2_body[] = { 'r' }; 
    Atom r2_head[] = { 's' };
    rules[1] = encode_rule(1, 1, r2_body, r2_head, IMPERATIVE);
    
    int n_clauses1;
    int n_clauses2;
    DefiniteProgram *defr1 = encode_defr(rules[0], &n_clauses1);
    DefiniteProgram *defr2 = encode_defr(rules[1], &n_clauses2);
    
    print_facts(facts, n_atoms_in_facts);
    printf("Rules: \n");
    for (int i = 0; i < n_of_rules; i++) {
        print_rule(rules[i]);
        printf("\n");
    }
    print_defr(defr1, n_clauses1, rules[0]);
    print_defr(defr2, n_clauses2, rules[1]);
    
    int n_total_programs;
    DefiniteProgram *def = encode_def(rules, 2, &n_total_programs);
    print_def(def, n_total_programs);

    for (int i = 0; i < n_total_programs; i++) {
        for (int j = 0; j < def[i].n_clauses; j++) {
            free(def[i].clauses[j].body);
        }
        free(def[i].clauses);
    }
    free(def);

    for (int i = 0; i < 2; i++) {
        free(rules[i].body);
        free(rules[i].head);
    }
    return 0;
}

