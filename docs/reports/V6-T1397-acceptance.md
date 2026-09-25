# T1397/T1398 scheduler acceptance — 2026-09-25

T1397 worker final PASS and T1398 independent final PASS are recorded in `docs/reports/T1397.md` and `docs/reports/T1398.md`. The accepted source is `RBM1D/Flow/GreenSpectralL1.lean`, SHA-256 `29dfceba3d35fc381b479b878de51799756eaa6aeb5ceef22740e8bcf23796e5`.

The scheduler reviewed the finite-Hermitian diagonal spectral expansions for both `G` and `G*`, including the squared first pole, the centered variance `Svar-N⁻¹`, and the exact substitution of `blockM_eq`. The triangle bound retains the full weighted second spectral sum `∑γ |p_{σ₂,γ}(z)| |ψγ(y)|²`; no delocalization or sharp all-spectrum estimate is assumed. This is the deterministic precursor to paper (2.31), not its stochastic domination, (2.29), StepTwoClaim or Theorem 2.6. The theorem applies on a nonempty actual Gaussian sample at any fixed positive broadening; no nonzero upper-bound integrand is required.

Scheduler replay passed `lake build RBM1D.Flow.GreenSpectralL1` (3,467 jobs), point-imported the module, and passed `lake build RBM1D` (9,602 jobs). The root `#assert_rbm_axioms` checked 20,033 `RBM` declarations within `propext`, `Classical.choice`, `Quot.sound`; the module's seven public `#print axioms` outputs list only those axioms. The reviewed source contains no `sorry`, `admit`, declared axiom or frozen-signature edit.
