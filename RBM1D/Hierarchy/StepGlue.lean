/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBound
import RBM1D.Hierarchy.Step2
import RBM1D.Hierarchy.Step2Moment
import RBM1D.Hierarchy.Step45

/-!
# The deterministic glue between Steps 1–2 and Steps 3–5

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, the proof of (2.77) in §5.6 ("With
the bound (2.73) for `L` and (3.46) for `K`, `S(m,l,s,u,t)` holds for `l = 0` and any `m ≥ 1`.
By (2.75), (2.76), and a standard continuity argument based on Step 1, (5.92), and the initial
bound (5.110), `S(m,l,s,u,t)` holds for every `l` and `m = 1,2`") and Step 4 in §5.7 ("By
(2.76), (4.5) and Step 3 for `(L-K)`-loops of length 1 and 2 and the condition (2.72), we have
`Ξ^{(L-K)}_{t,1} ≺ 1`, `Ξ^{(L-K)}_{t,2} ≺ (W ℓ_t η_t)^{1/4}`").

These sentences turn the outputs (2.73), (2.75), (2.76) of Steps 1–2 into the inputs of
Steps 3–5: `S(m,0)` for `m ≥ 1`, `S(m,l)` for `m ≤ 2`, `Ξ^{(L-K)}_{u,1} ≺ 1` and
`Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}`.  This file contains two deterministic pieces of that
bookkeeping; the bookkeeping along the flow, at an `N`-dependent energy, is in
`RBM1D/EnergyN/Hierarchy/StepGlue.lean` (`RBM.StepGlue.stochDom_flowXiLKN`,
`RBM.StepGlue.flow_S_zero'N`, `RBM.StepGlue.flow_S_one'N`).

## Main results

* `RBM.StepGlue.norm_lkErr_one_le` — the `1`-loop `L - K` is bounded by `‖G_u - m‖_max`, for
  both charges.
* `RBM.StepGlue.rpow_half_le_psi` — `(W ℓ_s η_s)^{1/2} ≤ Ψ(n,k)`, the first summand of (5.108).

## The charges of `Ξ^{(L-K)}_{u,2}`

(2.76) is stated **only for `σ = (+,-)`** (Theorem 2.21; §5.3 opens with "In this section, we
focus on the `(+,-)` `2`-`G`-loop, i.e. `σ = (+,-)`.  The subscript `σ` will be dropped in this
subsection").  But `Ξ^{(L-K)}_{u,2}` is defined in (5.76) as a maximum over **all**
`σ ∈ {+,-}²`, and `S(2,l)` for large `l` needs `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}`, which is a
factor `W ℓ_u η_u` better than what (2.73) or (2.75) give for any charge.  Of the four charges,
`(+,-)` is covered by (2.76); `(-,+)` reduces to it by trace cyclicity (`RBM.gloop_rotate`), and
`(-,-)` to `(+,+)` by conjugation (`RBM1D/Hierarchy/ChargeReduce.lean`).  For the constant
charges the paper uses the continuity argument based on Step 1, (5.92) and (5.110).

## Deviations from the paper

* (2.76) is used with its decay profile dropped (`decayProf ≤ 2`), which is all Step 3 needs.
-/

namespace RBM

open MeasureTheory Filter

namespace StepGlue

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-! ### The `1`-loop is controlled by `‖G_u - m‖_max` -/

/-- **The `1`-loop `L - K` is bounded by `‖G_u - m‖_max`.**  For a loop of length `1`,
`L_{u,(σ),(a)} - K_{u,(σ),(a)} = ⟨(G_u(σ) - m(σ)) E_a⟩` is an average of `W` diagonal entries
of `G_u(σ) - m(σ)`; for `σ = -` these are the complex conjugates of the entries of `G_u - m`
(`RBM.Gsig_conjTranspose`, `RBM.mSigma_false`), so **both charges** are covered. -/
theorem norm_lkErr_one_le (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}
    (v : LoopData (B.L N) 1) {c : ℝ}
    (h : ∀ ij : B.Idx N × B.Idx N, X.llErr E N u ω ij ≤ c) :
    X.lkErr E N u ω v.idx ≤ c := by
  set H := X.H N u ω with hHdef
  set z := zt E u with hzdef
  have hidx : v.idx = (⟨[v.1 0], [v.2 0]⟩ : LoopIdx (ZMod (B.L N))) := by simp [LoopData.idx]
  -- the diagonal entries of `G(σ) - m(σ)` have the norms of those of `G - m`
  have hdiag : ∀ p : B.Idx N, ‖(Gsig H z (v.1 0) - mSigma E (v.1 0) •
      (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) p p‖ ≤ c := by
    intro p
    have hbase := h (p, p)
    simp only [Sample.llErr, Sample.G, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, ← hHdef, ← hzdef] at hbase
    cases hv : v.1 0 with
    | true =>
      simpa [Gsig_true, mSigma_true, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
        using hbase
    | false =>
      have hG : Gsig H z false = Matrix.conjTranspose (Gsig H z true) :=
        (Gsig_conjTranspose (X.hermitian N u ω) z true).symm
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hG,
        mSigma_false, Matrix.conjTranspose_apply, Gsig_true]
      rw [Complex.star_def, ← map_sub (starRingEnd ℂ), Complex.norm_conj]
      exact hbase
  -- the average
  have hLK : X.Lval E N u ω v.idx - B.Kval E N u v.idx
      = Matrix.trace ((Gsig H z (v.1 0) - mSigma E (v.1 0) •
          (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0)) := by
    rw [hidx, Sample.Lval, Band.Kval, Kgen_one, gloop, gloopProd_cons, gloopProd_nil,
      Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, trace_Eblk, mul_one]
  rw [Sample.lkErr, hLK, trace_sub_mul_Eblk]
  calc ‖∑ k, (blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
        (Gsig H z (v.1 0) k k - mSigma E (v.1 0))‖
      ≤ ∑ k, ‖(blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
        (Gsig H z (v.1 0) k k - mSigma E (v.1 0))‖ := norm_sum_le _ _
    _ ≤ ∑ k, |blkCoef (B.L N) (B.W N) (v.2 0) k| * c := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := hdiag k
        simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq] using this
    _ = c := by rw [← Finset.sum_mul, sum_abs_blkCoef, one_mul]

/-! ### Scale facts from (2.72) with a gain -/

/-- `(W ℓ_s η_s)^{1/2} ≤ Ψ(n,k)` for every `n`, `k`: the first summand of (5.108). -/
theorem rpow_half_le_psi {As R Au : ℝ} (hAs : 0 ≤ As) (hR : 0 ≤ R) (hAu : 0 ≤ Au) (n k : ℕ) :
    As ^ ((1 : ℝ) / 2) ≤ Step3.psi As R Au n k := by
  unfold Step3.psi Step3.Psi
  split_ifs
  · have : 0 ≤ R ^ (n - 1) * Au := by positivity
    linarith
  · have : 0 ≤ R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4) := by positivity
    linarith

/-! ### `S(m,0)` from (2.73) and (2.59) -/

/-! ### `S(1,l)` from (2.75) -/

/-! ### The two missing random-layer inputs -/

/-! ### `S(2,l)` and Step 4's base cases -/

/-! ### The packaged conclusions -/

end StepGlue

end RBM

