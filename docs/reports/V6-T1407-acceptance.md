# T1407/T1408 scheduler acceptance — 2026-09-25

T1407 worker final PASS and T1408 independent final PASS are recorded in `docs/reports/T1407.md` and `docs/reports/T1408.md`. The accepted source is `RBM1D/Flow/GreenComparisonSpectralProduct.lean`, SHA-256 `597dfc064258d8146f4fa6cca889b36e50af4b5ba7c1b2d5bd79bd0d53d9c944`.

The scheduler reviewed the pointwise finite-Hermitian product formula from the accepted one-factor `stieltjes_im_eq_normalized_specWeight`, including the exact `(card n)^(-k)` factor, the partition of all eigenvalue tuples into injective and colliding functions, and the shared zero `Fin 2` Hermitian witness where both contributions are positive. The source matches the deterministic expansion preceding the paper's (2.23)–(2.24) comparison. It does not estimate collisions, identify the full correlation pairing, prove Green comparison, or establish Theorem 2.6.

Scheduler replay passed `lake build RBM1D.Flow.GreenComparisonSpectralProduct` (3,468 jobs), point-imported the module, and passed `lake build RBM1D` (9,601 jobs). The root `#assert_rbm_axioms` checked 20,020 `RBM` declarations within `propext`, `Classical.choice`, `Quot.sound`; the four public `#print axioms` outputs list only those axioms. The reviewed source contains no `sorry`, `admit`, declared axiom or frozen-signature edit.
