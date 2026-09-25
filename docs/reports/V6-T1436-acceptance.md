# T1436/T1437 scheduler acceptance — 2026-09-25

T1436 delivered actual worker final PASS (`docs/reports/T1436.md`), followed by T1437 independent final PASS (`docs/reports/T1437.md`). T1437 jointly audited the two previously compiled but unaccepted dependency sources T1409 and T1426 as well as T1436. The scheduler directly reviewed their definitions, theorem statements, finite-product/coordinate contraction proof, reports, manuscript formulas (2.22)–(2.25), and exact SHA-256 values:

| Source | SHA-256 |
|---|---|
| `RBM1D/Flow/OUComparisonHessian.lean` | `2dfc2c0fee2c7d80e43467ece116737a2d13e562b7f5cebb60e855a4e568c27a` |
| `RBM1D/Flow/OUComparisonContraction.lean` | `041632da40b993977be6ff941dc20aa500b46f0302e968e219f9305898b5d312` |
| `RBM1D/Flow/OUComparisonProductContraction.lean` | `4ce781f84e216cbb6ced436d6b0842058164e38bf4a87cb6be2b1f072e1503f5` |
| `paper/250520-YinJun-v2.pdf` | `bd6f7e32bee30a28202e147742b28e88e85bdd6a691ae8fa89e3aedae22bbb43` |

The accepted public theorem `RBM.centeredVariance_wirtProduct_contraction_eq` is a **deterministic pointwise equality** for a finite product of `Im stieltjes` factors at one Hermitian matrix, all spectral parameters with nonzero imaginary part, any `Gauss.Dims` and sequence index including zero. Its centered covariance is the actual `Sblk - M⁻¹`, with physical dimension `M = card (d.Idx N)`. It separates the single-factor `2 Im paperK1Contraction` terms and ordered distinct-factor `-1/4` four-sign `paperK2Contraction` terms, leaving the norm outside the signed block contractions. The jointly audited T1409/T1426 source facts are accepted **only as dependencies of this pointwise identity**, not as their previously failed full-ticket targets. The empty/singleton formulas and repeated spectral-value case are covered. Paper `Im z > 0` lies within the source's `Im z ≠ 0` domain.

The independent audit found a numerical wording error in T1436's witness report: `-1/64` is the two-label value. For three distinct labels with `H=diag(1,0,0,0)` and `z=i`, the corrected total is `-35/2048`; the single and ordered cross contributions are simultaneously nonzero on the same Hermitian matrix. This does not alter any Lean statement or proof. Both worker report and audit correction remain preserved.

Scheduler replay: `lake build RBM1D.Flow.OUComparisonProductContraction` passed (3,710 jobs); the reviewed module was point-imported into `RBM1D.lean`; `lake build RBM1D` passed (9,613 jobs). The root `#assert_rbm_axioms` checked 20,306 `RBM` declarations and found only `propext`, `Classical.choice`, `Quot.sound`. Separate root-imported `#print axioms` checks on the product expansion, both one-/two-factor contractions, main product theorem, and empty/singleton theorems listed exactly those three. No `sorry`, `admit`, or declared axiom occurs in the three reviewed sources; `git diff --check` passed.

**Scope limit:** the absolute-value `paperL1Kernel`/`paperL2Kernel` bound, expectation derivative and time integral (2.25), a law-carrying OU path, Green comparison, and Theorem 2.6 remain unproved. No stopped-process, paper-wide, or full-theorem acceptance follows. No commit or push is claimed.
