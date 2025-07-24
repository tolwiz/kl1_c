#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

/* ============ Typedef ============ */

/* Typedef for a single atom. */
typedef char Atom;

/* Typedef for a single rule. */
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

/* Typedef for a single definite clause. */
typedef struct {
    Atom *body;
    int n_atoms_in_body;
    Atom head;
} DefiniteClause;

/* Typedef for a single definite program. */
typedef struct {
    DefiniteClause *clauses;
    int n_clauses;
} DefiniteProgram;

/* Typedef for performed acts. */
typedef struct {
    Atom *acts;
    int n_atoms_in_performed_acts;
    int capacity;
} PerformedActs;

/* ============ Utils ============ */

/* Safe malloc. */
void *safe_malloc(size_t size) {
    void *ptr = malloc(size);
    if (!ptr) {
        perror("Malloc failed!");
        exit(EXIT_FAILURE);
    }
    return ptr;
}

/* Safe realloc. */
void *safe_realloc(void *ptr, size_t size) {
    void *new_ptr = realloc(ptr, size);
    if (!new_ptr) {
        perror("Realloc failed!");
        exit(EXIT_FAILURE);
    }
    return new_ptr;
}

/* Function for initializing performed acts. */
void init_performed_acts(PerformedActs *acts) {
    acts->n_atoms_in_performed_acts = 0;
    acts->capacity = 4;
    acts->acts = safe_malloc(acts->capacity * sizeof(Atom));
}

/* Function for adding an atom to performed acts. */
void push_atom_to_performed_acts(PerformedActs *acts, Atom a) {
    if (acts->n_atoms_in_performed_acts == acts->capacity) {
        acts->capacity *= 2;
        acts->acts = safe_realloc(acts->acts, acts->capacity * sizeof(Atom));
    }
    acts->acts[acts->n_atoms_in_performed_acts++] = a;
}

/* ============ Functions for computing stuff ============ */

/* Encode a rule given body, head, and rule type.
 * Allocate and copy both body and head into the rule structure.
 */
Rule encode_rule(int n_body, int n_head, Atom *body, Atom *head, RuleType ruletype) {
    Rule r;

    // Copy body
    r.n_atoms_in_body = n_body;
    r.body = safe_malloc(n_body * sizeof(Atom));
    for (int i = 0; i < n_body; i++) {
        r.body[i] = body[i];
    }

    // Copy head or set ⊥ for constraint
    if (n_head == 0) {
        r.n_atoms_in_head = 1;
        r.head = safe_malloc(sizeof(Atom));
        r.head[0] = '/';  // Special char meaning ⊥
    } else {
        r.n_atoms_in_head = n_head;
        r.head = safe_malloc(n_head * sizeof(Atom));
        for (int i = 0; i < n_head; i++) {
            r.head[i] = head[i];
        }
    }
    r.ruletype = ruletype;
    return r;
}

/* Function for computing defr. */
DefiniteProgram *compute_defr(Rule rule, int *n_definite_programs) {
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
 * definite programs, namely def(R). 
 * TODO: enum for constraints */
DefiniteProgram *compute_def(Rule *rules, int n_rules, int *n_total_programs) {
    
    /* Compute defᵣ(r) for each rule. */
    int *n_options = safe_malloc(n_rules * sizeof(int)); // Total number of definite programs 
    DefiniteProgram **defrs = safe_malloc(n_rules * sizeof(DefiniteProgram *));    
    for (int i = 0; i < n_rules; i++) {
        defrs[i] = compute_defr(rules[i], &n_options[i]);
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

/* Compute the least model of a definite program D given
 * an initial set of facts A. This is a fixed-point computation:
 * at each step, we add to the model all heads of clauses whose
 * bodies are satisfied by the current model.
 */
Atom *compute_least_model(DefiniteProgram D, Atom *facts, int n_facts, int *out_size) {
    PerformedActs M;
    init_performed_acts(&M);

    /* M0(D, A) = A */
    for (int i = 0; i < n_facts; i++)
        push_atom_to_performed_acts(&M, facts[i]);

    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < D.n_clauses; i++) {
            if (D.clauses[i].head == '/') continue;
            /* Check if all atoms in the body are already in M. */
            bool body_ok = true;
            for (int j = 0; j < D.clauses[i].n_atoms_in_body; j++) {
                Atom a = D.clauses[i].body[j];
                bool found = false;
                for (int k = 0; k < M.n_atoms_in_performed_acts; k++) {
                    if (M.acts[k] == a) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    body_ok = false;
                    break;
                }
            }

            /* If body is satisfied and head not already in M, add it. */
            if (body_ok) {
                Atom h = D.clauses[i].head;
                bool in_M = false;
                for (int k = 0; k < M.n_atoms_in_performed_acts; k++) {
                    if (M.acts[k] == h) {
                        in_M = true;
                        break;
                    }
                }
                if (!in_M) {
                    push_atom_to_performed_acts(&M, h);
                    changed = true;
                }
            }
        }
    }
    *out_size = M.n_atoms_in_performed_acts;
    return M.acts;
}

/* Function for computing cnsᵈ(R, A). */
Atom **compute_cnsd(Rule *R, int n_rules, Atom *A, int n_facts, int *n_out_models, int **model_sizes) {
    int n_total_programs;
    DefiniteProgram *def = compute_def(R, n_rules, &n_total_programs);
    Atom **cnsd = safe_malloc(n_total_programs * sizeof(Atom *));
    *model_sizes = safe_malloc(n_total_programs * sizeof(int));
    *n_out_models = 0;

    for (int i = 0; i < n_total_programs; i++) {
        int model_size;
        Atom *model = compute_least_model(def[i], A, n_facts, &model_size);

        /* Check for duplicates. */
        int duplicate = 0;
        for (int j = 0; j < *n_out_models; j++) {
            if (model_size != (*model_sizes)[j]) continue;
            int equal = 1;
            for (int k = 0; k < model_size; k++) {
                int found = 0;
                for (int l = 0; l < model_size; l++) {
                    if (model[k] == cnsd[j][l]) {
                        found = 1;
                        break;
                    }
                }
                if (!found) {
                    equal = 0;
                    break;
                }
            }
            if (equal) {
                duplicate = 1;
                break;
            }
        }
        if (!duplicate) {
            cnsd[*n_out_models] = model;
            (*model_sizes)[*n_out_models] = model_size;
            (*n_out_models)++;
        } else {
            free(model);
        }
    }
    free(def);
    return cnsd;
}

/* Function for checking if a model satisfies constraints. */
bool satisfies_constraints(Rule *R, int n_rules, Atom *model, int model_size) {
    for (int i = 0; i < n_rules; i++) {
        Rule r = R[i];
        if (r.ruletype == IMPERATIVE &&
            r.n_atoms_in_head == 1 &&
            r.head[0] == '/') {

            /* Constraint: ⊢ ⊥ means body must NOT be satisfied */
            bool violated = true;
            for (int j = 0; j < r.n_atoms_in_body; j++) {
                Atom a = r.body[j];
                bool found = false;
                for (int k = 0; k < model_size; k++) {
                    if (model[k] == a) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    violated = false;
                    break;
                }
            }
            /* Constraint violated. */
            if (violated) return false;
        }
    }
    /* All constraints are satisfied. */
    return true;
}

/* Function for computing out1. */
Atom **compute_out1(Rule *R, int n_rules, Atom *A, int n_facts, int *n_models, int **model_sizes) {
    /* Compute all M(D, A). */
    int total;
    int *sizes;
    Atom **cnsd = compute_cnsd(R, n_rules, A, n_facts, &total, &sizes);

    /* Filter the models which violate constraints. */    
    Atom **out1 = safe_malloc(total * sizeof(Atom *));
    *model_sizes = safe_malloc(total * sizeof(int));
    *n_models = 0;

    for (int i = 0; i < total; i++) {
        if (satisfies_constraints(R, n_rules, cnsd[i], sizes[i])) {
            out1[*n_models] = cnsd[i];
            (*model_sizes)[*n_models] = sizes[i];
            (*n_models)++;
        } else {
            free(cnsd[i]);
        }
    }
    free(cnsd);
    free(sizes);
    return out1;
}

/* ============ Functions for I/O  ============ */

/* Function for printing a set of atoms. */
void print_atoms(Atom facts[], int n_atoms_in_facts) {
    printf("A: \n");
    for (int i = 0; i < n_atoms_in_facts; i++) {
        printf("%c", facts[i]);
        if (i < n_atoms_in_facts-1) printf(", ");
    }
    printf("\n\n");
}

/* Function for printing a single rule. */
void print_rule(Rule r) {
    for (int i = 0; i < r.n_atoms_in_body; i++) {
        printf("%c", r.body[i]);
        if (i < r.n_atoms_in_body - 1) printf(" ∧ ");
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

/* Function for printing a set of models. */
void print_models(const char *label, Atom **models, int *sizes, int n_models) {
    printf("%s = {\n", label);
    for (int i = 0; i < n_models; i++) {
        printf("  {");
        for (int j = 0; j < sizes[i]; j++) {
            printf("%c", models[i][j]);
            if (j < sizes[i] - 1) printf(", ");
        }
        printf("}");
        if (i < n_models - 1) printf(",\n");
        else printf("\n");
    }
    printf("}\n");
}

/* Read facts and rules from the user.
 * Each fact is a single lowercase letter.
 * Each rule has a body (AND of atoms) and a head (OR of atoms),
 * and is either imperative (⊢) or permissive (⊣).
 * A rule with no head atoms and ruletype == IMPERATIVE is treated as a constraint (⊢ ⊥).
 */
void read_input(Atom **facts, int *n_facts, Rule **rules, int *n_rules) {
    printf("Number of facts: ");
    scanf("%d", n_facts);
    *facts = safe_malloc(*n_facts * sizeof(Atom));
    printf("Enter facts (single lowercase letters):\n");
    for (int i = 0; i < *n_facts; i++) {
        printf("  Fact %d: ", i + 1);
        scanf(" %c", &(*facts)[i]);
    }
    printf("\nNumber of rules: ");
    scanf("%d", n_rules);
    *rules = safe_malloc(*n_rules * sizeof(Rule));
    for (int i = 0; i < *n_rules; i++) {
        printf("\n--- Rule %d ---\n", i + 1);

        // === Body ===
        int n_body;
        printf("  Number of atoms in body: ");
        scanf("%d", &n_body);
        Atom *body = safe_malloc(n_body * sizeof(Atom));
        for (int j = 0; j < n_body; j++) {
            printf("    Body atom %d: ", j + 1);
            scanf(" %c", &body[j]);
        }

        // === Head ===
        int n_head;
        printf("  Number of atoms in head (0 for constraint): ");
        scanf("%d", &n_head);
        Atom *head = NULL;
        if (n_head > 0) {
            head = safe_malloc(n_head * sizeof(Atom));
            for (int j = 0; j < n_head; j++) {
                printf("    Head atom %d: ", j + 1);
                scanf(" %c", &head[j]);
            }
        }

        // === Rule type ===
        char type;
        printf("  Rule type (i = ⊢, p = ⊣): ");
        scanf(" %c", &type);
        RuleType ruletype = (type == 'i') ? IMPERATIVE : PERMISSIVE;

        // === Store rule ===
        Rule r;
        r.n_atoms_in_body = n_body;
        r.body = safe_malloc(n_body * sizeof(Atom));
        for (int j = 0; j < n_body; j++) r.body[j] = body[j];
        if (n_head == 0) {
        
            /* Encode constraint as head = { '/'} and n_atoms_in_head = 1 */
            r.n_atoms_in_head = 1;
            r.head = safe_malloc(sizeof(Atom));
            r.head[0] = '/';
        } else {
            r.n_atoms_in_head = n_head;
            r.head = safe_malloc(n_head * sizeof(Atom));
            for (int j = 0; j < n_head; j++) r.head[j] = head[j];
        }

        r.ruletype = ruletype;
        (*rules)[i] = r;

        free(body);
        if (head) free(head);
    }
}

/* ============ Main ============ */
int main() {
    Atom *facts;
    int n_facts;
    Rule *rules;
    int n_rules;

    read_input(&facts, &n_facts, &rules, &n_rules);
    printf("\x1b[3J\x1b[H\x1b[2J"); 
    print_atoms(facts, n_facts);
    
    printf("R:\n");
    for (int i = 0; i < n_rules; i++) {
        print_rule(rules[i]);
        printf("\n");
    }
    
    printf("===========================================================\n");
    printf("Definite programs:\n");
    for (int i = 0; i < n_rules; i++) {
        int n_variants;
        DefiniteProgram *defr_i = compute_defr(rules[i], &n_variants);
        print_defr(defr_i, n_variants, rules[i]);
        for (int j = 0; j < n_variants; j++) {
            for (int k = 0; k < defr_i[j].n_clauses; k++)
                free(defr_i[j].clauses[k].body);
            free(defr_i[j].clauses);
        }
        free(defr_i);
    }

    int n_total_programs;
    DefiniteProgram *def = compute_def(rules, n_rules, &n_total_programs);
    printf("===========================================================\n");
    print_def(def, n_total_programs);

    int n_models;
    int *sizes;
    Atom **cnsd = compute_cnsd(rules, n_rules, facts, n_facts, &n_models, &sizes);
    printf("===========================================================\n");
    print_models("cnsᵈ(R,A)", cnsd, sizes, n_models);

    int n_out;
    int *out_sizes;
    Atom **out1 = compute_out1(rules, n_rules, facts, n_facts, &n_out, &out_sizes);
    printf("===========================================================\n");
    print_models("out₁(R,A)", out1, out_sizes, n_out);

    /* Free memory */
    for (int i = 0; i < n_total_programs; i++) {
        for (int j = 0; j < def[i].n_clauses; j++)
            free(def[i].clauses[j].body);
        free(def[i].clauses);
    }
    free(def);

    for (int i = 0; i < n_models; i++) free(cnsd[i]);
    free(cnsd);
    free(sizes);

    for (int i = 0; i < n_out; i++) free(out1[i]);
    free(out1);
    free(out_sizes);

    for (int i = 0; i < n_rules; i++) {
        free(rules[i].body);
        free(rules[i].head);
    }
    free(rules);
    free(facts);

    return 0;
}
