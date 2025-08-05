/* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                                                         *
 * Simple implementation of the KL1 logic                                                  *
 *                                                                                         *
 * This program takes as input:                                                            *
 *   - A set of facts A                                                                    *
 *   - A set of rules R, which can be imperative (⊢) or permissive (⊣)                     *
 *                                                                                         *
 * It computes:                                                                            *
 *   - def(R): all definite programs derived from R (via defᵣ(r) for each r ∈ R)           *
 *   - cnsᵈ(R,A): all least models M(D,A) for D ∈ def(R)                                   *
 *   - out₁(R,A): all models from cnsᵈ(R,A) that satisfy all imperative constraints        *
 *                                                                                         *
 * Rules with no head atoms and ruletype IMPERATIVE are interpreted as constraints (⊢ ⊥).  *
 *                                                                                         *
 * This code uses verbose variable names to highlight the semantic correspondence          *
 * with the KL1 logic formalism and is not optimized in terms of computational             *
 * cost, aiming to make the implementation didactically clear.                             *
 *                                                                                         *
 * Compile with:                                                                           *
 *   gcc kl1.c -o kl1                                                                      *
 *                                                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * */

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

/* * * * * * * * * * * * * * * * * * * * Typedef * * * * * * * * * * * * * * * * * * * * * */

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

/* Typedef for grouping input data (facts and rules). */
typedef struct {
    Atom *facts;
    int n_facts;
    Rule *rules;
    int n_rules;
} KnowledgeBase;

/* Typedef for grouping result sets of computations. */
typedef struct {
    DefiniteProgram *def_programs;
    int n_def_programs;
    Atom **cnsd;
    int *cnsd_sizes;
    int n_cnsd_models;
    Atom **out1;
    int *out1_sizes;
    int n_out1_models;
} Results;

/* * * * * * * * * * * * * * * * * * * * Utils * * * * * * * * * * * * * * * * * * * * * * */

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

/* * * * * * * * * * * * * * * * * * * Computation * * * * * * * * * * * * * * * * * * * * */

/* Encode a rule given body, head, and rule type.
 * Allocate and copy both body and head into the rule structure.
 */
Rule encode_rule(int n_body, int n_head, Atom *body, Atom *head, RuleType ruletype) {
    Rule r;
    
    /* Copy body */
    r.n_atoms_in_body = n_body;
    r.body = safe_malloc(n_body * sizeof(Atom));
    for (int i = 0; i < n_body; i++) {
        r.body[i] = body[i];
    }
    
    /* Copy head or set ⊥ for constraint */
    if (n_head == 0) {
        r.n_atoms_in_head = 1;
        r.head = safe_malloc(sizeof(Atom));
        
        /* Special char meaning ⊥. */
        r.head[0] = '/'; 
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

/* Function for computing defᵣ for a given rule. */
DefiniteProgram *defr(Rule rule, int *n_definite_programs) {
    int n_atoms_in_head = rule.n_atoms_in_head;
    
    /* Void head. */
    if (n_atoms_in_head == 0) {
        DefiniteProgram *defr = safe_malloc(sizeof(DefiniteProgram));
        defr[0].n_clauses = 1;
        defr[0].clauses = safe_malloc(sizeof(DefiniteClause));
        defr[0].clauses[0].head = '/';
        defr[0].clauses[0].n_atoms_in_body = rule.n_atoms_in_body;
        defr[0].clauses[0].body = safe_malloc(rule.n_atoms_in_body * sizeof(Atom));
        for (int i = 0; i < rule.n_atoms_in_body; i++) {
            defr[0].clauses[0].body[i] = rule.body[i];
        }
        *n_definite_programs = 1;
        return defr;
    }
    
    /* 2^n possible subsets of head (C). */
    int total_subsets = 1 << n_atoms_in_head;
    DefiniteProgram *defr = safe_malloc(total_subsets * sizeof(DefiniteProgram));
    int n_definite_programs_generated = 0;
    
    /* Cycle through all possible binary masks i.e., all subsets of head atoms. */
    for (int bitmask = 0; bitmask < total_subsets; bitmask++) {
        int clause_count = 0;
        
        /* Count how many atoms are in this subset (bitmask). */
        for (int i = 0; i < n_atoms_in_head; i++) {
            if (bitmask & (1 << i)) clause_count++;
        }
        
        /* If void subset and rule is imperative, skip (constraint cannot be empty for ⊢). */
        if (clause_count == 0 && rule.ruletype == IMPERATIVE) continue;
        
        /* If void subset and rule is permissive, add an empty program. */
        if (clause_count == 0 && rule.ruletype == PERMISSIVE) {
            defr[n_definite_programs_generated].n_clauses = 0;
            defr[n_definite_programs_generated].clauses = NULL;
            n_definite_programs_generated++;
            continue;
        }
        defr[n_definite_programs_generated].n_clauses = clause_count;
        
        /* Allocate the right number of clauses in defr. */
        defr[n_definite_programs_generated].clauses = safe_malloc(clause_count * sizeof(DefiniteClause));
        
        /* For each selected atom in bitmask, create a clause in the definite program. */
        int clause_index = 0;
        for (int i = 0; i < n_atoms_in_head; i++) {
            if (bitmask & (1 << i)) {
                defr[n_definite_programs_generated].clauses[clause_index].head = rule.head[i];
                defr[n_definite_programs_generated].clauses[clause_index].n_atoms_in_body = rule.n_atoms_in_body;
                defr[n_definite_programs_generated].clauses[clause_index].body = safe_malloc(rule.n_atoms_in_body * sizeof(Atom));
                for (int j = 0; j < rule.n_atoms_in_body; j++) {
                    defr[n_definite_programs_generated].clauses[clause_index].body[j] = rule.body[j];
                }
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
DefiniteProgram *defR(Rule *rules, int n_rules, int *n_total_programs) {
    
    /* Compute defᵣ(r) for each rule and count options per rule. */
    int *n_options = safe_malloc(n_rules * sizeof(int));
    DefiniteProgram **defrs = safe_malloc(n_rules * sizeof(DefiniteProgram *));
    for (int i = 0; i < n_rules; i++) {
        defrs[i] = defr(rules[i], &n_options[i]);
    }
    
    /* Compute total number of definite programs in def(R). */
    int total = 1;
    for (int i = 0; i < n_rules; i++) {
        total *= n_options[i];
    }
    *n_total_programs = total;
    DefiniteProgram *all_programs = safe_malloc(total * sizeof(DefiniteProgram));
    
    /* Cycle through all combinations of choices (one from each defᵣ(rᵢ)). */
    for (int p = 0; p < total; p++) {
        int *choice = safe_malloc(n_rules * sizeof(int));
        int quotient = p;
        for (int i = n_rules - 1; i >= 0; i--) {
            choice[i] = quotient % n_options[i];
            quotient /= n_options[i];
        }
        
        /* Combine chosen clauses from each rule to form one definite program. */
        int total_clauses = 0;
        for (int i = 0; i < n_rules; i++) {
            total_clauses += defrs[i][choice[i]].n_clauses;
        }
        all_programs[p].n_clauses = total_clauses;
        all_programs[p].clauses = safe_malloc(total_clauses * sizeof(DefiniteClause));
        
        /* Copy clauses from each selected definite program into all_programs[p]. */
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
Atom *least_model(DefiniteProgram D, Atom *facts, int n_facts, int *out_size) {
    PerformedActs M;
    init_performed_acts(&M);
    
    /* M0(D, A) = A */
    for (int i = 0; i < n_facts; i++) {
        push_atom_to_performed_acts(&M, facts[i]);
    }
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < D.n_clauses; i++) {

            /* Skip constraints (head = ⊥). */
            if (D.clauses[i].head == '/') continue; 
            
            /* Check if all atoms in the clause's body are already in M. */
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
Atom **cns_star(Rule *R, int n_rules, Atom *A, int n_facts, int *n_out_models, int **model_sizes) {
    int n_total_programs;
    DefiniteProgram *def = defR(R, n_rules, &n_total_programs);
    Atom **cnsd = safe_malloc(n_total_programs * sizeof(Atom *));
    *model_sizes = safe_malloc(n_total_programs * sizeof(int));
    *n_out_models = 0;
    for (int i = 0; i < n_total_programs; i++) {
        int model_size;
        Atom *model = least_model(def[i], A, n_facts, &model_size);
        
        /* Check for duplicates before adding the model to cnsd. */
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

/* Function for checking if a model satisfies all constraints in R. */
bool satisfies_constraints(Rule *R, int n_rules, Atom *model, int model_size) {
    for (int i = 0; i < n_rules; i++) {
        Rule r = R[i];
        if (r.ruletype == IMPERATIVE &&
            r.n_atoms_in_head == 1 &&
            r.head[0] == '/') {
            
            /* Constraint (⊢ ⊥): the rule's body must *not* be fully satisfied by the model. */
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
            
            /* If constraint is violated (body satisfied => ⊥), model is not valid. */
            if (violated) return false;
        }
    }

    /* All constraints satisfied. */
    return true;
}

/* Function for computing out₁(R, A). */
Atom **out(Rule *R, int n_rules, Atom *A, int n_facts, int *n_models, int **model_sizes) {
    
    /* Compute all models M(D, A) for each definite program D in def(R). */
    int total;
    int *sizes;
    Atom **cnsd = cns_star(R, n_rules, A, n_facts, &total, &sizes);
    
    /* Filter out models that violate any constraints in R. */
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

/* * * * * * * * * * * * * * * * * * * * I/O * * * * * * * * * * * * * * * * * * * * * */

/* Function for printing a set of atoms. */
void print_atoms(Atom facts[], int n_atoms_in_facts) {
    printf("A: \n");
    for (int i = 0; i < n_atoms_in_facts; i++) {
        printf("%c", facts[i]);
        if (i < n_atoms_in_facts - 1) printf(", ");
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

/* Function for printing a single definite clause (with optional trailing comma). */
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
 * A rule with no head atoms and ruletype == IMPERATIVE is treated as a 
 * constraint (⊢ ⊥).
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
        
        /* === Body === */
        int n_body;
        printf("  Number of atoms in body: ");
        scanf("%d", &n_body);
        Atom *body = safe_malloc(n_body * sizeof(Atom));
        for (int j = 0; j < n_body; j++) {
            printf("    Body atom %d: ", j + 1);
            scanf(" %c", &body[j]);
        }

        /* === Head === */
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

        /* === Rule type === */
        char type;
        printf("  Rule type (i = ⊢, p = ⊣): ");
        scanf(" %c", &type);
        RuleType ruletype = (type == 'i') ? IMPERATIVE : PERMISSIVE;
        
        /* === Store rule === */
        Rule r;
        r.n_atoms_in_body = n_body;
        r.body = safe_malloc(n_body * sizeof(Atom));
        for (int j = 0; j < n_body; j++) r.body[j] = body[j];
        if (n_head == 0) {

            /* Encode constraint as head = {'/'} and n_atoms_in_head = 1 */
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

/* * * * * * * * * * * * * * * * * * * Session * * * * * * * * * * * * * * * * * * * * */

/* Utility function to print a separator line for output sections. */
void print_separator(void) {
    printf("===========================================================\n");
}

/* Function to clear screen and display all input facts and rules. */
void print_knowledge_base(const KnowledgeBase *kb) {
    printf("\x1b[3J\x1b[H\x1b[2J");
    print_atoms(kb->facts, kb->n_facts);
    printf("R:\n");
    for (int i = 0; i < kb->n_rules; i++) {
        print_rule(kb->rules[i]);
        printf("\n");
    }
}

/* Free an array of DefiniteProgram structures and their contents. */
void free_definite_programs(DefiniteProgram *programs, int count) {
    for (int i = 0; i < count; i++) {
        for (int j = 0; j < programs[i].n_clauses; j++) {
            free(programs[i].clauses[j].body);
        }
        free(programs[i].clauses);
    }
    free(programs);
}

/* Free an array of models (Atom arrays) and their sizes. */
void free_models(Atom **models, int *sizes, int count) {
    for (int i = 0; i < count; i++) {
        free(models[i]);
    }
    free(models);
    free(sizes);
}

/* Free an array of Rule structures and their allocated fields. */
void free_rules(Rule *rules, int count) {
    for (int i = 0; i < count; i++) {
        free(rules[i].body);
        free(rules[i].head);
    }
    free(rules);
}

/* Free all memory associated with a KnowledgeBase (facts and rules). */
void free_knowledge_base(KnowledgeBase *kb) {
    free_rules(kb->rules, kb->n_rules);
    free(kb->facts);
}

/* Run the interactive session: read input and compute all outputs. */
void run_interactive_session(void) {
    
    /* Read input data from user. */
    KnowledgeBase kb;
    read_input(&kb.facts, &kb.n_facts, &kb.rules, &kb.n_rules);

    /* Display the input data. */
    print_knowledge_base(&kb);

    /* Compute and display defᵣ for each rule. */
    print_separator();
    printf("Definite programs:\n");
    for (int i = 0; i < kb.n_rules; i++) {
        int n_variants;
        DefiniteProgram *defr_set = defr(kb.rules[i], &n_variants);
        print_defr(defr_set, n_variants, kb.rules[i]);
        free_definite_programs(defr_set, n_variants);
    }

    /* Compute and display def(R). */
    Results results;
    results.def_programs = defR(kb.rules, kb.n_rules, &results.n_def_programs);
    print_separator();
    print_def(results.def_programs, results.n_def_programs);

    /* Compute and display cnsᵈ(R,A). */
    results.cnsd = cns_star(kb.rules, kb.n_rules, kb.facts, kb.n_facts, &results.n_cnsd_models, &results.cnsd_sizes);
    print_separator();
    print_models("cnsᵈ(R,A)", results.cnsd, results.cnsd_sizes, results.n_cnsd_models);

    /* Compute and display out₁(R,A). */
    results.out1 = out(kb.rules, kb.n_rules, kb.facts, kb.n_facts, &results.n_out1_models, &results.out1_sizes);
    print_separator();
    print_models("out₁(R,A)", results.out1, results.out1_sizes, results.n_out1_models);

    /* Free all allocated memory. */
    free_definite_programs(results.def_programs, results.n_def_programs);
    free_models(results.cnsd, results.cnsd_sizes, results.n_cnsd_models);
    free_models(results.out1, results.out1_sizes, results.n_out1_models);
    free_knowledge_base(&kb);
}

/* * * * * * * * * * * * * * * * * * * Main * * * * * * * * * * * * * * * * * * * * */

int main() {
    run_interactive_session();
    return 0;
}
