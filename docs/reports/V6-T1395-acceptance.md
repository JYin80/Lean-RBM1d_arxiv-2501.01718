# V6 T1395/T1396 acceptance — Stieltjes scale monotonicity

Accepted scope: the deterministic finite-Hermitian implication immediately after paper (2.27), `η Im m(E+iη) ≤ η̃ Im m(E+iη̃)` for `0 < η ≤ η̃`, using the actual `RBM.stieltjes` sign and normalization. The accepted module also provides its spectral formula, an upper-bound transfer, band-index cardinality `B.size N = L N * W N`, and a strict finite-matrix witness. It does not prove OU flow, (2.26), (2.27), full (2.28), or Theorem 2.6.

- T1395 worker final PASS and report: `docs/reports/T1395.md`.
- T1396 independent final PASS and report: `docs/reports/T1396.md`.
- Reviewed source: `RBM1D/Flow/StieltjesEtaMonotone.lean`, SHA-256 `03904aad69985bebf76a9e4e652a5f3c8ac812d74ece617f5fcd4f6657b01d70`, matching both reports after scheduler review.
- Scheduler replay: `lake build RBM1D.Flow.StieltjesEtaMonotone` succeeded (3,467 jobs); point import in `RBM1D.lean`; `lake build RBM1D` succeeded (9,598 jobs).
- Module public `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`. The imported-root audit reported 20,001 `RBM` declarations with only those three axioms. No `sorry`, declared axiom, or frozen-signature change was found in the reviewed module.

The concrete `Fin 1` zero Hermitian matrix at `E=1`, `η=1/2`, `η̃=1` gives strict sides `1/5 < 1/2`. This verifies nonvacuity of the scale assumptions without requiring a nonzero matrix or claiming an OU probabilistic witness.
