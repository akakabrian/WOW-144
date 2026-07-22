# WOW II Conjecture 144

Isolated research and Lean formalization workspace for Written on the Wall II Conjecture 144.

## Integrity rules

- The upstream theorem statement is preserved exactly.
- No `sorry`, axioms, or theorem-statement changes are accepted in candidate proof files.
- The upstream Formal Conjectures dependency is pinned to a specific commit.
- This repository is not a submission and does not modify the shared upstream checkout.

## Lean

GitHub Actions installs the pinned Lean toolchain, fetches Mathlib caches, and builds the `WOW144` library.

Current formal artifacts:

- `WOW144/Audit.lean`: checks the exact upstream theorem and definitions.
- `WOW144/Arithmetic.lean`: proves the natural-number-to-real arithmetic reduction used by the target theorem.
