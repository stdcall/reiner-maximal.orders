# Mathematical checks

Exact computations are run by `just check-sage` (SageMath, `sage -python`;
CI uses the official SageMath container). Lean declarations and their
assumptions are audited by `just check-lean`; each declaration is linked in
`lean-proofs.json` to the passages of the book it establishes, with its
limitations.

## Exact computations (`sage/`)

Each script states in its docstring what it checks, where each expected
value comes from (printed page and label of this edition) and what it does
not establish. Expected values are the book's; where the book is wrong, the
printed reading is kept as a refuted check beside the corrected one. Every
script fails on a false check and ends with `ok <name>: N checks`.

| Script | Sections |
|---|---|
| `s01_05_commutative_algebra.py` | 1–5: integral closure, homological algebra, localization, Dedekind domains, completions |
| `s06_07_radicals_semisimple.py` | 6–7: radicals, semisimple and simple algebras |
| `s08_11_orders.py` | 8–11: orders, reduced norms and traces, maximal orders, localization |
| `s12_14_local_skewfields.py` | 12–14: maximal orders in local skewfields |
| `s15_16_morita.py` | 15–16: progenerators, Morita correspondence |
| `s17_20_maximal_orders_dvr.py` | 17–20: maximal orders over discrete valuation rings, ideals, different |
| `s21_25_ideal_theory.py` | 21–25: global ideal theory, norms, different and discriminant |
| `s26_27_classes_genus.py` | 26–27: ideal classes, genus |
| `s28_29_crossed_products.py` | 28–29: Brauer groups, crossed-product algebras |
| `s30_31_cyclic_algebras.py` | 30–31: cyclic algebras, Hasse invariants |
| `s32_local_invariants.py` | 32: splitting of simple algebras, local invariants |
| `s33_reduced_norms.py` | 33: reduced norms, Hasse–Schilling–Maass |
| `s34_eichler.py` | 34: Eichler's Theorem |
| `s35_36_class_groups.py` | 35–36: ideal class groups, $K_0$ |
| `s37_picard.py` | 37–38: Picard groups, non-maximal orders |
| `s38_finite_quaternion_groups.py` | 38: finite subgroups of the quaternions |
| `s39_hereditary_local.py` | 39: hereditary orders, local case |
| `s40_hereditary_global.py` | 40: hereditary orders, global case |
| `s41_group_rings.py` | 41: integral group rings |

## Formal proofs (`lean/`)

Lean 4 with mathlib, pinned by `lean/lean-toolchain` and
`lean/lake-manifest.json`. `lean/check_axioms.py` compiles every file listed
in `lean-proofs.json` without warnings and allows only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The files formalize bounded steps:
identities, counting bounds and group-theoretic deductions; the surrounding
theory is a hypothesis, as each record's `limitations` states.

| File | Passage |
|---|---|
| `IdempotentLifting.lean` | (6.7), (6.18): lifting idempotents |
| `HereditaryComponents.lean` | (10.8): splitting a hereditary order along a central idempotent |
| `PrimeElementMatrix.lean` | (14.6), Exercise 14.5: the prime element $\pi_D^*$ |
| `CrossedProduct.lean` | (29.1)–(29.3), Exercise 29.1: factor sets |
| `SchurExponent.lean` | (29.21), (29.22): the exponent divides the index |
| `CyclicAlgebra.lean` | (30.3)(iii): $(cu)^n = N_{L/K}(c)\,u^n$ |
| `UnramifiedNormBound.lean` | (33.12): the counting bound |
| `PicentMatrixOrder.lean` | (37.36)(ii), (37.40) |
| `HereditaryRadicalGenerator.lean` | (39.14): $\Pi^n = \pi_D$ |
