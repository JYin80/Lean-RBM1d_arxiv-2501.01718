# V6 scheduler acceptance — T1434/T1435 (2026-09-25)

**Accepted only for the finite even-power-sum all-order multilinear derivative formula and dimension-free q-norm Hölder bound.** T1434 delivered final worker PASS (`docs/reports/T1434.md`); T1435 delivered independent final PASS on the exact source (`docs/reports/T1435.md`). The scheduler inspected the source and reports, verified source SHA-256 `0b03a0b89e1fc9544e71a69f3834abfe9adb7f294c52f8c67c53688a8af80445` for `RBM1D/Gauss/PowerSumHigherDerivatives.lean`, and point-imported only this accepted module in `RBM1D.lean`.

The public result quantifies over every finite coordinate type, even `q ≥ 2`, `1 ≤ j ≤ q`, all base vectors including zero coordinates and every tuple of directions. `iteratedFDeriv_powerSum_apply` gives the exact `q.descFactorial j` formula. `abs_iteratedFDeriv_powerSum_le` gives the finite q-norm estimate with no coordinate-cardinality factor and the coefficient bound `q.descFactorial j ≤ q^j`, including `j=q`. `nonzero_zero_coordinate_witness` uses one base vector `(1,0)` and first-coordinate directions in `Fin 2`; it has a zero coordinate and a nonzero derivative on that same deterministic instance. This is the inner polynomial arrow of T1424 formula (A), not its outer fractional-power composition or an actual Gaussian formula (4.12) producer.

Scheduler replay:

- `lake build RBM1D.Gauss.PowerSumHigherDerivatives`: PASS (2957 jobs).
- `lake build RBM1D` after the point import: PASS (9609 jobs).
- Root `#assert_rbm_axioms`: 20161 `RBM` declarations, only `propext`, `Classical.choice`, `Quot.sound`.
- Separate `lake env lean` of a file importing `RBM1D` and printing axioms of `qNorm_pow`, the exact derivative, both public estimates and the witness: each lists only those same three axioms.
- Source has no `sorry`, `admit`, declared axiom, unaccepted T1430/T1432 import or frozen-signature change. The source hash was unchanged during replay.

The full smooth-norm derivative, reciprocal calculus, finite-cube composition, actual same-event `Pr`/`Yr`, and paper (4.12) remain open. This acceptance does not change any earlier INCOMPLETE or FAIL verdict.
