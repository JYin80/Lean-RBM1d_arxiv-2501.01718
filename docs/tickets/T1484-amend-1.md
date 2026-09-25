Ticket: T1484 (amend-1; supersedes T1484.md, withdrawn before any work started)
Group / type: pilot-TruePath (G1b) / prove — pilot P4 (the BDG replacement)
Role: prover-hard
Release condition for the audit stage: prove report shows math preflight PASS; `lake build RBM1D.Gauss.GridAzuma` succeeds.
Math source and targets: `docs/claude-team/pilot-P4P5-paper.md` §4 and §9 repair (A). Pure probability on an arbitrary probability space `(Ω', μ)` with a filtration `ℱ : Filtration ℕ _`; nothing RBM-specific.
  (T1) `azuma_two_sided`: if `StronglyAdapted ℱ Y`, `HasSubgaussianMGF (Y 0) (c 0) μ`, and `∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i+1)) (c (i+1)) μ` with deterministic `c : ℕ → ℝ≥0`, then for `ε ≥ 0`: `μ.real {ω | ε ≤ |∑ i ∈ range n, Y i ω|} ≤ 2 * exp (-ε^2 / (2 * ∑ i ∈ range n, c i))`. From Mathlib `measure_sum_ge_le_of_hasCondSubgaussianMGF` applied to `Y` and `-Y`.
  (T2) `azuma_complex`: the same for `Z : ℕ → Ω' → ℂ` whose real and imaginary parts each satisfy the hypotheses of (T1) with the same `c`: `μ.real {ω | ε ≤ ‖∑ Z i ω‖} ≤ 4 * exp (-ε^2 / (4 * ∑ c i))`.
  (T3) `doob_L2_max`: for a real martingale `M` w.r.t. `ℱ` with `M 0 = 0` and `M k` square-integrable, and `x > 0`: `μ.real {ω | x ≤ (range (K+1)).sup' _ (fun k => |M k ω|)} ≤ (∫ ω, (M K ω)^2 ∂μ) / x^2`. From Mathlib `maximal_ineq` applied to the nonnegative submartingale `(M k)^2`.
  (T4) `martingale_sq_eq_sum`: for the same `M`, `∫ (M K)^2 = ∑ k ∈ range K, ∫ (M (k+1) - M k)^2` (orthogonality of increments).
  (T5) `stopped_martingale`: if `M` is a martingale and `τ` a bounded stopping time, `fun k => M (min k τ)` is a martingale (cite Mathlib if present; otherwise prove via T1483 (T5)-style indicator sums).
Step 0 (read-only checks): (a) exact signatures of `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` (`Mathlib/Probability/Moments/SubGaussian.lean:921`) and `MeasureTheory.maximal_ineq` (`Mathlib/Probability/Martingale/OptionalStopping.lean:144`); (b) whether Mathlib already has (T5) (`Martingale.stoppedProcess` or similar). **Failure signal (pilot rule):** if any target turns out to need continuous-time stochastic calculus, a BDG/Burkholder inequality, or any other result not derivable from the two Mathlib theorems above plus elementary measure theory, stop, write `preflight-fail` with the exact missing statement, and do not work around it.
Dependencies (must already be accepted): none (generic).
Upstream / downstream: consumed by the A5 Step 2 assembly together with T1482 (T2). prover-hard: quantifier and integrability bookkeeping across Mathlib's subgaussian API.
Sole writable files: `RBM1D/Gauss/GridAzuma.lean`        Must not touch: every other file.
Root import: none.
Branch: t/T1484
Required reading (only these): `CLAUDE.md` §3; `Mathlib/Probability/Moments/SubGaussian.lean` (statements in the `Martingale` section); `Mathlib/Probability/Martingale/OptionalStopping.lean` (statements); `RBM1D/Gauss/PermutationFourierDoobAzumaScalar.lean` (repo precedent for using Mathlib's Azuma); `docs/claude-team/pilot-P4P5-paper.md` §4, §9.
Acceptance criteria: (T1)–(T5) with these names in `RBM.Gauss.Grid`; no `sorry`/`admit`/`axiom`; auditor checks that every constant `c i` is deterministic in the statements, that (T3) bounds the maximum over all `k ≤ K` simultaneously, and that no hypothesis is vacuous (witness: `Y ≡ 0`, `c ≡ 0`, and one nonzero Gaussian-increment example).
