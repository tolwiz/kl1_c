![KL1 Logic](./1.jpg)

# kl1

A tiny interactive implementation of KL1 logic in plain C.

You provide:
- a set of facts `A` (atoms)
- a set of rules `R` (imperative ⊢ or permissive ⊣)

It computes:
- `def(R)` — all definite programs derived from R
- `cnsᵈ(R,A)` — all least models M(D,A) for D in def(R)
- `out₁(R,A)` — all models that satisfy all constraints

## How to build

```sh
gcc kl1.c -o kl1
