# V6 scheduler acceptance — T1440/T1441 (2026-09-25)

**Accepted only for the abstract finite multiaffine shifted-face derivative and convex norm bound.** T1440 delivered worker final PASS (`docs/reports/T1440.md`), T1441 delivered independent final PASS (`docs/reports/T1441.md`), and the scheduler inspected the statements, actual `deriv`-based mixed-partial definition, reports and source. Exact source SHA-256 `49e529252630e3633d6219fa1da80935a5e81f19e0ef1abbefad56b2c46280eb` for `RBM1D/Gauss/MultiaffineShiftedFaces.lean` remained unchanged through replay. The scheduler point-imported this module in `RBM1D.lean`.

For every finite coordinate type, vertex family, coordinate subset `J` and interpolation point, `cubeMixedPartial_shiftedFaces` proves that the iterated scalar-coordinate derivatives of the standard multiaffine interpolation equal the weighted sum of **all complementary shifted `J`-face differences**. `cubeMixedPartial_shiftedFaces_weights_sum` and `_weights_nonneg_on_unitCube` establish convex weights, and `_norm_le_on_unitCube` derives a norm bound from a uniform bound on all shifted faces. Empty/full/singleton sets, `Fin 0` and a nonzero second-face scalar witness are covered. The derivative operator is defined by `deriv` after coordinate update, not postulated. No repeated FTC or stochastic assertion is imported.

Scheduler replay:

- `lake build RBM1D.Gauss.MultiaffineShiftedFaces`: PASS (8924 jobs).
- `lake build RBM1D` after the point import: PASS (9610 jobs).
- Root `#assert_rbm_axioms`: 20260 `RBM` declarations, only `propext`, `Classical.choice`, `Quot.sound`.
- Separate `lake env lean` importing `RBM1D` printed axioms for the main formula, weight sum/nonnegativity, norm bound, empty/full/singleton/`Fin 0` cases and both witness theorems: only the same permitted three.
- Source has no `sorry`, `admit`, declared axiom, unaccepted T1432/T1438 import or frozen-signature change.

This is Arrow S toward T1424's corrected abstract cube estimate. Local-neighborhood all-order FTC, cube composition, actual Gaussian `Pr`/`Yr`, the unsmoothed random-scale paper (4.12), later-cell Eq45, cutoff, T615, and full-paper theorem remain open. Historical T1438 INCOMPLETE and T1439 gate-only verdicts are unchanged.
