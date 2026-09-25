Ticket: T1482 (amend-1; supersedes T1482.md, withdrawn before any work started)
Group / type: pilot-TruePath (G1b) / prove — pilot P2
Role: prover
Release condition for the audit stage: prove report shows math preflight PASS; `lake build RBM1D.Gauss.GridMarkov` succeeds.
Math source and targets: the conditional structure used in `docs/claude-team/pilot-P4P5-paper.md` §3–§4 (drift = conditional expectation; linear part of the martingale difference is conditionally Gaussian). Notation from T1481-amend-1.
  (T1) **Freezing lemma** `condExp_freeze`: for `k`, an `filt d k`-measurable `Y : Ωg d → β` (β a standard Borel space) and a jointly measurable `F : β → Ω d → ℝ` with `F (Y ·) (· (k+1))` integrable, `(Pg d)[fun ω => F (Y ω) (ω (k+1)) | filt d k] =ᵐ fun ω => ∫ x, F (Y ω) x ∂(Gauss.P d)`. Built from T1481 (T6) and Mathlib `condExp_indep_eq` / kernel-disintegration lemmas.
  (T2) **Conditional Gaussian MGF of a frozen linear functional** `hasCondSubgaussianMGF_linear`: let `A : Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ` be `filt d k`-measurable, `lin A X := Re (trace (A * X))` (and the same with `Im`), `v A := ∑_c gvar d c · (coefficient of coordinate c in lin A)²` (explicit formula, one real Gaussian per `Coord`), `E ∈ filt d k` a set, `c ≥ 0` deterministic with `∀ ω ∈ E, step s t K N * v (A ω) ≤ c`. Then `HasCondSubgaussianMGF (filt d k) _ (fun ω => E.indicator (fun ω => √(step s t K N) * lin (A ω) (Xmat d N (ω (k+1)))) ω) ⟨c, _⟩ (Pg d)`.
  (T3) `condExp_linear_eq_zero`: under the hypotheses of (T2) plus integrability, the conditional expectation of the same variable is `0` a.e.
Step 0 (read-only checks): (a) T1481 accepted (`lake build RBM1D.Gauss.GridPath` on `main` after its merge); (b) the signature of `ProbabilityTheory.HasCondSubgaussianMGF` in `Mathlib/Probability/Moments/SubGaussian.lean`; (c) the repo's existing conditional-MGF pattern `RBM.Gauss.uniformPerm_prefixFourierReal_hasCondSubgaussianMGF` (`Gauss/PermutationFourierDoobCondMGF.lean:131`) for proof shape. If (T1) needs a Mathlib lemma that does not exist and cannot be proved in ≲300 lines, report `preflight-fail` with the missing statement.
Dependencies (must already be accepted): T1481.
Upstream / downstream: downstream T1484's application (A5 tickets). prover: standard measure theory.
Sole writable files: `RBM1D/Gauss/GridMarkov.lean`        Must not touch: every other file.
Root import: none.
Branch: t/T1482
Required reading (only these): `CLAUDE.md` §3; `RBM1D/Gauss/GridPath.lean`; `RBM1D/Gauss/Model.lean` lines 195–260; `RBM1D/Gauss/PermutationFourierDoobCondMGF.lean`; `docs/claude-team/pilot-P4P5-paper.md` §4.
Acceptance criteria: (T1)–(T3) with these names in `RBM.Gauss.Grid`; no `sorry`/`admit`/`axiom`; auditor checks that `v` is the true conditional variance (compute it for `A = single entry` and compare with `gvar`), that the subgaussian constant in (T2) is deterministic, and that (T2) is non-vacuous (witness `E = univ`, `A = 0`, `c = 0`, and one nonzero `A`).
