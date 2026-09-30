/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseGrid
import RBM1D.Gauss.LoopIto
import RBM1D.Gauss.GridLoopStep

/-!
# Lemma 2.11 for `S_GUE`, and the one-step GUE-phase drift

The generator identity of Lemma 2.11 is re-derived
with the band variance profile `S^{(B)}` replaced everywhere by the constant GUE-phase profile
`1/M` (`M = L·W = RBM.Flow.ouMatrixSize`), and the one-step conditional drift on the GUE-phase
grid (`RBM.Gauss.GUEGrid.gueH`, `RBM.Gauss.GUEGrid.Pgue`) is bounded by the frozen entrywise
Taylor route described below.

## Route

`generator_add_zMotion_gue` re-runs the pointwise (deterministic) part of
`RBM.Gauss.generator_add_zMotion_gauss` (`Gauss/LoopIto.lean`) with `Sblk (d.L N) (d.W N) i
j` replaced by the constant `(ouMatrixSize d N : ℝ)⁻¹` throughout the `wirtSecond` contraction,
and `SB` replaced by `GUEPhase.SBgue` in the resulting charge-indexed sum.  The only property of
`S^{(B)}` that the deterministic `m`-cancellation (`eGterm_sub_eGterm`) uses is the row-sum
identity `∑_a S^{(B)}_{ab} = 1`; `SBgue` satisfies it (`L · L⁻¹ = 1`), so the same cancellation
identity holds verbatim with `eGtermGUE` replacing `eGterm`.

`condExp_loop_drift_gue` follows the band proof's decomposition
(`Grid.norm_loop_step_drift_le`) but replaces its Lipschitz-generator step by a **direct
third-order Taylor bound**:
* freezing: `Pgue = infinitePi gueStepMeasure`, so the increment `ω (k+1)` is independent of
  `Grid.filt d k` with law `gueUnit d`, and `gueH (k+1) = gueH k + Hflow (Δ/M) (ω (k+1))`;
* time error: `Grid.loop_step_time_err`, pointwise in the increment;
* `z`-motion re-centring: `Grid.norm_zMotion_sub_le_ofM`;
* space error: along `s ↦ M + sδ` (Hermitian), the loop product has `‖∂³‖ ≤ 6(n+1)³η^{-(n+3)}‖δ‖³`
  (Leibniz + `norm_iteratedDeriv_green_le`), the trace costs `card = M`, the first-order term has
  mean zero, the second-order term has mean `(Δ/M) ∑_{ij} ∂_ij∂_ji` (coordinate covariance
  `gueUnitVar`, `sum_used_eq_sum_pairs` with the constant profile), and
  `E‖X‖³ ≤ 52 M⁴` (`‖X‖² ≤ 2 ∑ y_t²`, fourth Gaussian moments).
The `η`-exponent is `n+3` (not `driftLip`'s `2n+6`); the constants add up to
`318 (n+1)³ M⁵ (1+η⁻¹)^{n+3} Δ^{3/2} ≤ 2^{4n+8} M^{n+4} (1+η⁻¹)^{n+4} Δ^{3/2}`.
-/

noncomputable section

namespace RBM.Gauss.GUEGrid

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Gauss.Grid
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### The `Ẽ` term and the GUE-phase loop drift -/

/-- The `Ẽ` term (2.47) of the GUE phase: `eGterm` with `S^{(B)} → S^{(B)}_{GUE}`. -/
def eGtermGUE (L W : ℕ) [NeZero L] [NeZero W] (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    Matrix.trace ((Gsig M z (I.σ.getD (k - 1) true)
        - m (I.σ.getD (k - 1) true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue k b)

variable (d : Dims)

/-- The GUE-phase loop drift: `Ẽ_{GUE} + W ∑_{k<l} (G^L ∘ L) S^(B)_{GUE} (G^R ∘ L)`. -/
def loopDriftGUE (E u : ℝ) (N : ℕ) (I : LoopIdx (ZMod (d.L N)))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  eGtermGUE (d.L N) (d.W N) (mSigma E) M (zt E u) I
    + GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N) M (zt E u)) I

/-! ### Helper section: the constant-weight (`(ouMatrixSize d N)⁻¹`) contraction

Mirrors the contraction sections of `Gauss/LoopIto.lean` (the linearity of the `½ ∑ S_ij`
contraction, the generic contraction, the `Finset.range` bookkeeping and the frozen cut-and-glue
identity): all lemmas below are `private`.  The weight `Sblk (d.L N) (d.W N) i j` is replaced by
the *constant* `(ouMatrixSize d N : ℝ)⁻¹`, and `SB` by `GUEPhase.SBgue`. -/

section GUEContraction

variable {d} {N : ℕ}

/-- `∑_i A_ii = W · ∑_a ⟨A E_a⟩`, the same reindexing `sumSblk_diag_mul` uses. -/
private theorem gueStep_diag_eq (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ i : d.Idx N, A i i
      = (d.W N : ℂ) * ∑ a : ZMod (d.L N), Matrix.trace (A * Eblk (d.L N) (d.W N) a) := by
  have hW : (d.W N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (d.W_pos N).ne'
  rw [Fintype.sum_prod_type (f := fun i : d.Idx N => A i i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sumSblk_trace_mul_Eblk A a, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]

/-- **The constant-weight analogue of `sumSblk_diag_mul`**, targeting `GUEPhase.SBgue`. -/
private theorem gueStep_diag_mul (A C : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A i i * C j j)
      = (d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
          Matrix.trace (A * Eblk (d.L N) (d.W N) a) * GUEPhase.SBgue (d.L N) a b
            * Matrix.trace (C * Eblk (d.L N) (d.W N) b) := by
  have hL : (d.L N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (d.L N))
  have hW : (d.W N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (d.W_pos N).ne'
  have hMeq : ((ouMatrixSize d N : ℝ)⁻¹ : ℂ) = ((d.L N : ℂ) * (d.W N : ℂ))⁻¹ := by
    have hcast : (ouMatrixSize d N : ℝ) = (d.L N : ℝ) * (d.W N : ℝ) := by
      unfold ouMatrixSize; push_cast; ring
    rw [hcast]; push_cast; ring
  have hLHS : ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A i i * C j j)
      = ((d.L N : ℂ) * (d.W N : ℂ))⁻¹
          * ((∑ i : d.Idx N, A i i) * (∑ j : d.Idx N, C j j)) := by
    rw [hMeq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hRHS : ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
      Matrix.trace (A * Eblk (d.L N) (d.W N) a) * GUEPhase.SBgue (d.L N) a b
        * Matrix.trace (C * Eblk (d.L N) (d.W N) b)
      = (d.L N : ℂ)⁻¹ * ((∑ a : ZMod (d.L N), Matrix.trace (A * Eblk (d.L N) (d.W N) a))
          * (∑ b : ZMod (d.L N), Matrix.trace (C * Eblk (d.L N) (d.W N) b))) := by
    have hstep : ∀ a b : ZMod (d.L N),
        Matrix.trace (A * Eblk (d.L N) (d.W N) a) * GUEPhase.SBgue (d.L N) a b
            * Matrix.trace (C * Eblk (d.L N) (d.W N) b)
          = (d.L N : ℂ)⁻¹ * (Matrix.trace (A * Eblk (d.L N) (d.W N) a)
              * Matrix.trace (C * Eblk (d.L N) (d.W N) b)) := by
      intro a b; rw [GUEPhase.SBgue_apply]; ring
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => hstep a b
  rw [hLHS, gueStep_diag_eq A, gueStep_diag_eq C, hRHS]
  field_simp

/-- The `wirtPairTr` pattern, unweighted (independent of the profile). -/
private theorem gueStep_wirtPairTr_eq (A C : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    wirtPairTr d N A C i j = (A i i * C j j + A j j * C i i) / 2 := by
  rw [wirtPairTr_eq]; exact traceBB_wirtPair A C i j

/-- **The constant-weight analogue of `sumSblk_half_wirtPair`.** -/
private theorem gueStep_half_wirtPair (A C : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) •
        wirtPairTr d N A C i j
      = (1 / 2 : ℂ) * ((d.W N : ℂ) * ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
            Matrix.trace (A * Eblk (d.L N) (d.W N) a) * GUEPhase.SBgue (d.L N) a b
              * Matrix.trace (C * Eblk (d.L N) (d.W N) b)) := by
  have h1 : ∑ i : d.Idx N, ∑ j : d.Idx N,
      ((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A j j * C i i)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A i i * C j j) := by
    rw [Finset.sum_comm]
  have e : ∀ i j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹ : ℂ)
        * ((A i i * C j j + A j j * C i i) / 2)
      = (((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A i i * C j j)) / 2
        + (((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A j j * C i i)) / 2 := by
    intro i j; ring
  have key : ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹ : ℂ)
        * ((A i i * C j j + A j j * C i i) / 2)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹ : ℂ) * (A i i * C j j) := by
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [h1]
    ring
  rw [← gueStep_diag_mul A C, ← key]
  simp only [gueStep_wirtPairTr_eq]
  simp only [Complex.real_smul]
  push_cast
  ring

end GUEContraction

/-! ### Linearity of the constant-weight contraction (mirrors the linearity of the
`½ ∑ S_ij` contraction in `Gauss/LoopIto.lean`; the three proofs are unchanged, since they never
use any property of the weight beyond it being a function of `i, j` — here the constant
`(ouMatrixSize d N : ℝ)⁻¹`). -/

section GUEConstLinear

variable {d} {N : ℕ}

private theorem gueStep_const_half_add (F G : d.Idx N → d.Idx N → ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
        ((ouMatrixSize d N : ℝ)⁻¹) • (F i j + G i j)
      = (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) • F i j
        + (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) • G i j := by
  simp only [smul_add, Finset.sum_add_distrib]

private theorem gueStep_const_half_mul (c : ℂ) (F : d.Idx N → d.Idx N → ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) • (c * F i j)
      = c * ((1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
          ((ouMatrixSize d N : ℝ)⁻¹) • F i j) := by
  simp only [← mul_smul_comm, ← Finset.mul_sum]

private theorem gueStep_const_half_sum {ι : Type*} (s : Finset ι) (F : ι → d.Idx N → d.Idx N → ℂ) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
        ((ouMatrixSize d N : ℝ)⁻¹) • (∑ x ∈ s, F x i j)
      = ∑ x ∈ s, (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
          ((ouMatrixSize d N : ℝ)⁻¹) • F x i j := by
  have step : ∀ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) • (∑ x ∈ s, F x i j)
      = ∑ x ∈ s, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) • F x i j := by
    intro i
    simp only [Finset.smul_sum]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm, ← Finset.smul_sum]

end GUEConstLinear

/-! ### The generic contraction (mirrors the generic contraction of `Gauss/LoopIto.lean`) -/

section GUEGeneric

variable {d} {N : ℕ}

/-- **The constant-weight analogue of `sumSblk_half_wirtSecond_eq`.** -/
private theorem gueStep_half_wirtSecond_eq {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (nn : ℕ)
    (A C : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ)
    (A' C' : ℕ → ℕ → Matrix (d.Idx N) (d.Idx N) ℂ)
    (h : ∀ (i j : d.Idx N) (b : Bool), i ≠ j ∨ b = true → coordD2 d N Φ M (i, j, b)
      = 2 * (∑ k ∈ Finset.range nn,
            Matrix.trace (A k * Bmat d N i j b * C k * Bmat d N i j b))
        + 2 * (∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn,
            Matrix.trace (A' p q * Bmat d N i j b * C' p q * Bmat d N i j b))) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) •
        wirtSecond d N Φ M i j
      = 2 * ∑ k ∈ Finset.range nn, (1 / 2 : ℂ) * ((d.W N : ℂ) *
            ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
              Matrix.trace (A k * Eblk (d.L N) (d.W N) a) * GUEPhase.SBgue (d.L N) a b
                * Matrix.trace (C k * Eblk (d.L N) (d.W N) b))
        + 2 * ∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn, (1 / 2 : ℂ) * ((d.W N : ℂ) *
            ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
              Matrix.trace (A' p q * Eblk (d.L N) (d.W N) a) * GUEPhase.SBgue (d.L N) a b
                * Matrix.trace (C' p q * Eblk (d.L N) (d.W N) b)) := by
  have hw : ∀ i j : d.Idx N, wirtSecond d N Φ M i j
      = 2 * (∑ k ∈ Finset.range nn, wirtPairTr d N (A k) (C k) i j)
        + 2 * (∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn,
            wirtPairTr d N (A' p q) (C' p q) i j) := by
    intro i j
    rw [wirtSecond_eq_wirtCombine,
      wirtCombine_congr i j (fun b => coordD2 d N Φ M (i, j, b))
        (fun b => 2 * (∑ k ∈ Finset.range nn,
              Matrix.trace (A k * Bmat d N i j b * C k * Bmat d N i j b))
          + 2 * (∑ p ∈ Finset.range nn, ∑ q ∈ Finset.Ioo p nn,
              Matrix.trace (A' p q * Bmat d N i j b * C' p q * Bmat d N i j b)))
        (h i j true (Or.inr rfl)) (fun hne => h i j false (Or.inl hne)),
      wirtCombine_add, wirtCombine_mul_left, wirtCombine_mul_left,
      wirtCombine_sum, wirtCombine_sum]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [wirtCombine_sum]
    rfl
  simp only [hw]
  rw [gueStep_const_half_add, gueStep_const_half_mul, gueStep_const_half_mul,
    gueStep_const_half_sum, gueStep_const_half_sum]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun k _ => gueStep_half_wirtPair (A k) (C k)
  · congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [gueStep_const_half_sum]
    exact Finset.sum_congr rfl fun q _ => gueStep_half_wirtPair (A' p q) (C' p q)

end GUEGeneric

/-! ### `eGtermGUE`/`primRhsGUE` in `Finset.range` bookkeeping (mirrors the
`eGterm`/`primRhs` bookkeeping of `Gauss/LoopIto.lean`) -/

section GUERangeForm

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem primRhsGUE_range_eq (K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    GUEPhase.primRhsGUE L W K I
      = ∑ p ∈ Finset.range I.a.length, ∑ q ∈ Finset.Ioo p I.a.length,
          (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
            K (I.cutGlueL (p + 1) (q + 1) a) * GUEPhase.SBgue L a b
              * K (I.cutGlueR (p + 1) (q + 1) b) := by
  rw [GUEPhase.primRhsGUE, GUEPhase.primBilGUE, sum_Icc_one_eq_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_Ioc_succ_eq_Ioo, Finset.mul_sum]
  rfl

private theorem eGtermGUE_zero_range_eq (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) :
    eGtermGUE L W 0 M z I
      = ∑ k ∈ Finset.range I.a.length, (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          Matrix.trace (Gsig M z (I.σ.getD k true) * Eblk L W a) * GUEPhase.SBgue L a b
            * gloop L W M z (I.cutGlue (k + 1) b) := by
  rw [eGtermGUE, sum_Icc_one_eq_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.zero_apply, zero_smul, sub_zero, Nat.add_sub_cancel]

end GUERangeForm

/-! ### The frozen (`m = 0`) identity (mirrors the frozen cut-and-glue identity of
`Gauss/LoopIto.lean`) -/

section GUEFrozen

variable {d} {N : ℕ}

/-- **The constant-weight analogue of `loopIto_second_frozen`.** -/
private theorem gueStep_second_frozen {z : ℂ} {I : LoopIdx (ZMod (d.L N))}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hC : ContDiff ℝ 2 (loopObs d N z I)) (hM : M.IsHermitian) (hz : z.im ≠ 0)
    (hwf : I.WF) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) •
        wirtSecond d N (loopObs d N z I) M i j
      = eGtermGUE (d.L N) (d.W N) 0 M z I
        + GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) I := by
  set l := I.σ.zip (I.a.map (Eblk (d.L N) (d.W N))) with hl
  have hlen : l.length = I.a.length := by
    rw [hl, List.length_zip, List.length_map, hwf, Nat.min_self]
  have hsplit : ∀ (i j : d.Idx N) (bb : Bool), i ≠ j ∨ bb = true →
      coordD2 d N (loopObs d N z I) M (i, j, bb)
        = 2 * (∑ k ∈ Finset.range I.a.length,
              Matrix.trace ((gprodM z (l.drop k) M * gprodM z (l.take k) M
                  * Gsig M z (l.getD k (true, 0)).1) * Bmat d N i j bb
                * Gsig M z (l.getD k (true, 0)).1 * Bmat d N i j bb))
          + 2 * (∑ p ∈ Finset.range I.a.length, ∑ q ∈ Finset.Ioo p I.a.length,
              Matrix.trace ((gprodM z (l.drop q) M * gprodM z (l.take p) M
                  * Gsig M z (l.getD p (true, 0)).1) * Bmat d N i j bb
                * (gprodM z ((l.drop p).take (q - p)) M
                  * Gsig M z (l.getD q (true, 0)).1) * Bmat d N i j bb)) := by
    intro i j bb hb
    rw [coordD2_loopObs_eq hC hM hz hwf i j bb (isHermitian_Bmat_of i j bb hb), ← hl,
      ← hlen, sum_insB_insB_eq (Bmat d N i j bb) l fun ll => Matrix.trace (gprodM z ll M),
      hlen]
    simp only [trace_gprodM_dblB, trace_gprodM_ins2B, nsmul_eq_mul, Nat.cast_ofNat]
  rw [gueStep_half_wirtSecond_eq I.a.length
      (fun k => gprodM z (l.drop k) M * gprodM z (l.take k) M
        * Gsig M z (l.getD k (true, 0)).1)
      (fun k => Gsig M z (l.getD k (true, 0)).1)
      (fun p q => gprodM z (l.drop q) M * gprodM z (l.take p) M
        * Gsig M z (l.getD p (true, 0)).1)
      (fun p q => gprodM z ((l.drop p).take (q - p)) M
        * Gsig M z (l.getD q (true, 0)).1)
      hsplit,
    eGtermGUE_zero_range_eq, primRhsGUE_range_eq]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hch : (l.getD k (true, 0)).1 = I.σ.getD k true := by
      rw [hl]
      exact charge_getD_zip I.σ (I.a.map (Eblk (d.L N) (d.W N))) true 0
        (by rw [hwf]; exact hk) (by simpa using hk)
    have hAtr : ∀ a : ZMod (d.L N),
        Matrix.trace (gprodM z (l.drop k) M * gprodM z (l.take k) M
            * Gsig M z (l.getD k (true, 0)).1 * Eblk (d.L N) (d.W N) a)
          = gloop (d.L N) (d.W N) M z (I.cutGlue (k + 1) a) := by
      intro a
      rw [hl]
      exact trace_block_cutGlue M z I hwf hk a
    have hsum : (∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
          gloop (d.L N) (d.W N) M z (I.cutGlue (k + 1) a) * GUEPhase.SBgue (d.L N) a b
            * Matrix.trace (Gsig M z (I.σ.getD k true) * Eblk (d.L N) (d.W N) b))
        = ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
            Matrix.trace (Gsig M z (I.σ.getD k true) * Eblk (d.L N) (d.W N) a)
              * GUEPhase.SBgue (d.L N) a b * gloop (d.L N) (d.W N) M z (I.cutGlue (k + 1) b) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show GUEPhase.SBgue (d.L N) b a = GUEPhase.SBgue (d.L N) a b by
        rw [GUEPhase.SBgue_apply, GUEPhase.SBgue_apply]]
      ring
    simp only [hAtr]
    rw [hch, hsum]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_range] at hp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_Ioo] at hq
    have hLtr : ∀ a : ZMod (d.L N),
        Matrix.trace (gprodM z (l.drop q) M * gprodM z (l.take p) M
            * Gsig M z (l.getD p (true, 0)).1 * Eblk (d.L N) (d.W N) a)
          = gloop (d.L N) (d.W N) M z (I.cutGlueL (p + 1) (q + 1) a) := by
      intro a
      rw [hl]
      exact trace_block_cutGlueL M z I hwf hq.1 hq.2 a
    have hRtr : ∀ b : ZMod (d.L N),
        Matrix.trace (gprodM z ((l.drop p).take (q - p)) M
            * Gsig M z (l.getD q (true, 0)).1 * Eblk (d.L N) (d.W N) b)
          = gloop (d.L N) (d.W N) M z (I.cutGlueR (p + 1) (q + 1) b) := by
      intro b
      rw [hl]
      exact trace_block_cutGlueR M z I hwf hq.1 hq.2 b
    simp only [hLtr, hRtr]
    ring

/-- The same identity with no smoothness hypothesis. -/
private theorem gueStep_second_frozen_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ)⁻¹) •
        wirtSecond d N (loopObs d N z I) M i j
      = eGtermGUE (d.L N) (d.W N) 0 M z I
        + GUEPhase.primRhsGUE (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) I :=
  gueStep_second_frozen
    (bddC2_loopObs hz (abs_pos.mpr hz) le_rfl hwf).contDiff hM hz hwf

end GUEFrozen

/-! ### The `m`-cancellation (mirrors `eGterm_sub_eGterm`) -/

section GUEZMotion

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The constant-weight analogue of `eGterm_sub_eGterm`.** The only property of the profile
that this identity uses is the row sum `∑_a S_{ab} = 1`; `GUEPhase.SBgue` satisfies it since
`L · L⁻¹ = 1`. -/
private theorem eGtermGUE_sub_eGtermGUE (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) :
    eGtermGUE L W m M z I - eGtermGUE L W 0 M z I = zMotion L W m M z I := by
  simp only [zMotion]
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hcol : ∀ b : ZMod L, ∑ a : ZMod L, GUEPhase.SBgue L a b = 1 := by
    intro b
    simp only [GUEPhase.SBgue_apply, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
  simp only [eGtermGUE, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [sum_Icc_one_eq_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : k + 1 - 1 = k := by omega
  simp only [hk]
  have hexp : ∀ a : ZMod L,
      Matrix.trace ((Gsig M z (I.σ.getD k true)
            - m (I.σ.getD k true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)
        - Matrix.trace ((Gsig M z (I.σ.getD k true)
            - (0 : Bool → ℂ) (I.σ.getD k true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)
        = -(m (I.σ.getD k true)) := by
    intro a
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, trace_Eblk]
    simp
  calc (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        (Matrix.trace ((Gsig M z (I.σ.getD k true)
            - m (I.σ.getD k true) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue (k + 1) b)
          - Matrix.trace ((Gsig M z (I.σ.getD k true)
            - (0 : Bool → ℂ) (I.σ.getD k true)
              • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a) * GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue (k + 1) b))
      = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          (-(m (I.σ.getD k true)))
            * (GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue (k + 1) b)) := by
        refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
        rw [← sub_mul, ← sub_mul, hexp a]
        ring
    _ = (-(m (I.σ.getD k true)))
          * ((W : ℂ) * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b)) := by
        have hinner : ∑ a : ZMod L, ∑ b : ZMod L,
            (-(m (I.σ.getD k true))) * (GUEPhase.SBgue L a b * gloop L W M z (I.cutGlue (k + 1) b))
              = (-(m (I.σ.getD k true)))
                * ∑ b : ZMod L, gloop L W M z (I.cutGlue (k + 1) b) := by
          simp only [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_mul, hcol b, one_mul]
        rw [hinner]
        ring

end GUEZMotion

/-! ### **Lemma 2.11 for the GUE profile** -/

/-- **Lemma 2.11 for the GUE profile** (generator with entry variance `1/M`, plus `z`-motion). -/
theorem generator_add_zMotion_gue {N : ℕ} {E u : ℝ} (hz : (zt E u).im ≠ 0)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (hM : M.IsHermitian)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, ((ouMatrixSize d N : ℝ))⁻¹ •
          wirtSecond d N (loopObs d N (zt E u) I) M i j
        + zMotion (d.L N) (d.W N) (mSigma E) M (zt E u) I
      = loopDriftGUE d E u N I M := by
  have hsecond := gueStep_second_frozen_of_im_ne_zero hz M hM I hwf
  have hzsub := eGtermGUE_sub_eGtermGUE (mSigma E) M (zt E u) I
  unfold loopDriftGUE
  rw [hsecond, ← hzsub]
  ring

/-! ### The one-step conditional drift on the GUE-phase grid

The route: a direct third-order Taylor bound along the Hermitian segment
(no `driftLip`/`genPtLip`), the Gaussian moments of `gueUnit d` (mean zero, covariance
`gueUnitVar`, fourth moment `3 v²`), and the freezing lemma for the mixed step law of `Pgue d`. -/

section GUELineTaylor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent along a Hermitian line is `C^ω` (it is `Ring.inverse` of an affine path of
units). -/
private theorem gueStep_contDiff_green_line {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ContDiff ℝ ⊤ (fun s : ℝ => green (M + (s : ℂ) • A) z) := by
  have hgr : (fun s : ℝ => green (M + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    funext s
    change (M + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  rw [hgr, contDiff_iff_contDiffAt]
  intro s
  have hU : IsUnit (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    have he : M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
        = (M + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
    rw [he]
    exact isUnit_sub_smul_one_of_im_ne_zero (isHermitian_add_realSmul hM hA s) hz
  have h1 : ContDiffAt ℝ ⊤ Ring.inverse (M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    have := contDiffAt_ringInverse ℝ (n := ⊤) hU.unit
    rwa [hU.unit_spec] at this
  have h2 : ContDiff ℝ ⊤ (fun s : ℝ => M - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) :=
    contDiff_const.add (Complex.ofRealCLM.contDiff.smul contDiff_const)
  exact h1.comp s h2.contDiffAt

/-- One factor `G(σ)(M + sA) E` of the loop product along a Hermitian line: `C^ω`, and its
`i`-th derivative is bounded by `i! η^{-(i+1)} ‖A‖^i` when `‖E‖ ≤ 1`. -/
private theorem gueStep_factor_line {M A : Matrix n n ℂ} (hM : M.IsHermitian)
    (hA : A.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hzη : η ≤ |z.im|) (σ : Bool)
    {E : Matrix n n ℂ} (hE : ‖E‖ ≤ 1) :
    ContDiff ℝ ⊤ (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ * E) ∧
      ∀ (i : ℕ) (t : ℝ), ‖iteratedFDeriv ℝ i (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ * E) t‖
        ≤ (i.factorial : ℝ) * η⁻¹ ^ (i + 1) * ‖A‖ ^ i := by
  set z' : ℂ := if σ then z else (starRingEnd ℂ) z with hz'
  have hz'η : η ≤ |z'.im| := by rw [hz', abs_im_ite_conj]; exact hzη
  have hz'0 : z'.im ≠ 0 := fun h => by rw [h, abs_zero] at hz'η; linarith
  have hG : ContDiff ℝ ⊤ (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ) :=
    gueStep_contDiff_green_line hM hA hz'0
  have hGE : ContDiff ℝ ⊤ (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ * E) :=
    hG.mul contDiff_const
  refine ⟨hGE, fun i t => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hG (contDiff_const (c := E)) t
    (n := i) (by exact_mod_cast le_top)
  have hsum : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ) t‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun _ : ℝ => E) t‖
      = ‖iteratedFDeriv ℝ i (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ) t‖ * ‖E‖ := by
    rw [Finset.sum_eq_single i]
    · rw [Nat.choose_self, Nat.sub_self, norm_iteratedFDeriv_zero, Nat.cast_one, one_mul]
    · intro j hj hji
      have hj' : i - j ≠ 0 := by
        rw [Finset.mem_range] at hj; omega
      rw [iteratedFDeriv_const_of_ne hj']
      simp
    · intro h; exact absurd (Finset.self_mem_range_succ i) h
  rw [hsum] at hmul
  have hGb : ‖iteratedFDeriv ℝ i (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ) t‖
      ≤ (i.factorial : ℝ) * η⁻¹ ^ (i + 1) * ‖A‖ ^ i := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact norm_iteratedDeriv_green_le hM hA hη hz'η i t
  calc ‖iteratedFDeriv ℝ i (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ * E) t‖
      ≤ ‖iteratedFDeriv ℝ i (fun s : ℝ => Gsig (M + (s : ℂ) • A) z σ) t‖ * ‖E‖ := hmul
    _ ≤ ((i.factorial : ℝ) * η⁻¹ ^ (i + 1) * ‖A‖ ^ i) * 1 :=
        mul_le_mul hGb hE (norm_nonneg _) (by positivity)
    _ = (i.factorial : ℝ) * η⁻¹ ^ (i + 1) * ‖A‖ ^ i := mul_one _

/-- `∑_{i ≤ k} x^{k-i} ≤ (x+1)^k` for `x ≥ 0` (binomial expansion, all coefficients `≥ 1`). -/
private theorem gueStep_sum_pow_le {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), x ^ (k - i) ≤ (x + 1) ^ k := by
  rw [add_comm x 1, add_pow]
  refine Finset.sum_le_sum fun i hi => ?_
  have hc : (1 : ℝ) ≤ (k.choose i : ℝ) := by
    rw [Finset.mem_range] at hi
    exact_mod_cast Nat.choose_pos (by omega)
  rw [one_pow, one_mul]
  exact le_mul_of_one_le_right (by positivity) hc

end GUELineTaylor


/-! #### The loop product along a Hermitian line -/

section GUELineProd

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The loop product `∏ G(σ_i)(M + sA) E_{a_i}` along the line `s ↦ M + sA`. -/
private def gueStep_lineProd (M A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (l : List (Bool × ZMod L)) (s : ℝ) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  l.foldr (fun p X => Gsig (M + (s : ℂ) • A) z p.1 * Eblk L W p.2 * X) 1

/-- **The Leibniz bound for the loop product along a Hermitian line**:
`‖∂^k P‖ ≤ (n+1)^k k! η^{-(n+k)} ‖A‖^k` for a product of `n` factors. -/
private theorem gueStep_lineProd_bound {M A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) (hA : A.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hzη : η ≤ |z.im|) :
    ∀ l : List (Bool × ZMod L), ContDiff ℝ ⊤ (gueStep_lineProd M A z l) ∧
      ∀ (k : ℕ) (t : ℝ), ‖iteratedFDeriv ℝ k (gueStep_lineProd M A z l) t‖
        ≤ ((l.length : ℝ) + 1) ^ k * (k.factorial : ℝ) * η⁻¹ ^ (l.length + k) * ‖A‖ ^ k := by
  intro l
  induction l with
  | nil =>
      have hfun : gueStep_lineProd M A z ([] : List (Bool × ZMod L))
          = fun _ : ℝ => (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) := rfl
      rw [hfun]
      refine ⟨contDiff_const, fun k t => ?_⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [norm_iteratedFDeriv_zero, norm_one]
        simp
      · rw [iteratedFDeriv_const_of_ne hk.ne']
        simp only [Pi.zero_apply, norm_zero]
        positivity
  | cons p l ih =>
      have hF := gueStep_factor_line hM hA hη hzη p.1 (norm_Eblk_le_one' (W := W) p.2)
      have hfun : gueStep_lineProd M A z (p :: l)
          = fun s : ℝ => (Gsig (M + (s : ℂ) • A) z p.1 * Eblk L W p.2)
              * gueStep_lineProd M A z l s := rfl
      rw [hfun]
      refine ⟨hF.1.mul ih.1, fun k t => ?_⟩
      have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hF.1 ih.1 t (n := k)
        (by exact_mod_cast le_top)
      set m : ℕ := l.length with hm
      set a : ℝ := ‖A‖ with ha
      have ha0 : 0 ≤ a := norm_nonneg _
      have hη0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
      have hterm : ∀ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i
              (fun s : ℝ => Gsig (M + (s : ℂ) • A) z p.1 * Eblk L W p.2) t‖
            * ‖iteratedFDeriv ℝ (k - i) (gueStep_lineProd M A z l) t‖
          ≤ ((k.factorial : ℝ) * η⁻¹ ^ (m + 1 + k) * a ^ k) * ((m : ℝ) + 1) ^ (k - i) := by
        intro i hi
        have hik : i ≤ k := by rw [Finset.mem_range] at hi; omega
        have h1 := hF.2 i t
        have h2 := ih.2 (k - i) t
        have hc0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
        calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i
                (fun s : ℝ => Gsig (M + (s : ℂ) • A) z p.1 * Eblk L W p.2) t‖
              * ‖iteratedFDeriv ℝ (k - i) (gueStep_lineProd M A z l) t‖
            ≤ (k.choose i : ℝ) * ((i.factorial : ℝ) * η⁻¹ ^ (i + 1) * a ^ i)
              * (((m : ℝ) + 1) ^ (k - i) * ((k - i).factorial : ℝ) * η⁻¹ ^ (m + (k - i))
                * a ^ (k - i)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hc0) h2 (norm_nonneg _)
                (by positivity)
          _ = ((k.factorial : ℝ) * η⁻¹ ^ (m + 1 + k) * a ^ k) * ((m : ℝ) + 1) ^ (k - i) := by
              have hfac : (k.choose i : ℝ) * (i.factorial : ℝ) * ((k - i).factorial : ℝ)
                  = (k.factorial : ℝ) := by
                exact_mod_cast Nat.choose_mul_factorial_mul_factorial hik
              have hηp : η⁻¹ ^ (i + 1) * η⁻¹ ^ (m + (k - i)) = η⁻¹ ^ (m + 1 + k) := by
                rw [← pow_add]; congr 1; omega
              have hap : a ^ i * a ^ (k - i) = a ^ k := by
                rw [← pow_add]; congr 1; omega
              rw [← hfac, ← hηp, ← hap]
              ring
      calc ‖iteratedFDeriv ℝ k (fun s : ℝ => (Gsig (M + (s : ℂ) • A) z p.1 * Eblk L W p.2)
              * gueStep_lineProd M A z l s) t‖
          ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i
              (fun s : ℝ => Gsig (M + (s : ℂ) • A) z p.1 * Eblk L W p.2) t‖
              * ‖iteratedFDeriv ℝ (k - i) (gueStep_lineProd M A z l) t‖ := hmul
        _ ≤ ∑ i ∈ Finset.range (k + 1),
              ((k.factorial : ℝ) * η⁻¹ ^ (m + 1 + k) * a ^ k) * ((m : ℝ) + 1) ^ (k - i) :=
            Finset.sum_le_sum hterm
        _ = ((k.factorial : ℝ) * η⁻¹ ^ (m + 1 + k) * a ^ k)
              * ∑ i ∈ Finset.range (k + 1), ((m : ℝ) + 1) ^ (k - i) := by
            rw [Finset.mul_sum]
        _ ≤ ((k.factorial : ℝ) * η⁻¹ ^ (m + 1 + k) * a ^ k) * (((m : ℝ) + 1) + 1) ^ k :=
            mul_le_mul_of_nonneg_left (gueStep_sum_pow_le (by positivity) k) (by positivity)
        _ = (((p :: l).length : ℝ) + 1) ^ k * (k.factorial : ℝ)
              * η⁻¹ ^ ((p :: l).length + k) * a ^ k := by
            rw [List.length_cons, ← hm]
            push_cast
            ring

/-- The trace of the loop product along the line: `C^ω`, with the `k`-th derivative bounded by
`card · (n+1)^k k! η^{-(n+k)} ‖A‖^k`. -/
private theorem gueStep_trace_lineProd_bound
    {M A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) (hA : A.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hzη : η ≤ |z.im|) (l : List (Bool × ZMod L)) :
    ContDiff ℝ ⊤ (fun s : ℝ => Matrix.trace (gueStep_lineProd M A z l s)) ∧
      ∀ (k : ℕ) (t : ℝ),
        ‖iteratedDeriv k (fun s : ℝ => Matrix.trace (gueStep_lineProd M A z l s)) t‖
          ≤ (Fintype.card (ZMod L × Fin W) : ℝ) * (((l.length : ℝ) + 1) ^ k
              * (k.factorial : ℝ) * η⁻¹ ^ (l.length + k) * ‖A‖ ^ k) := by
  have hP := gueStep_lineProd_bound hM hA hη hzη l
  have hfun : (fun s : ℝ => Matrix.trace (gueStep_lineProd M A z l s))
      = (traceCLM (ZMod L × Fin W)) ∘ gueStep_lineProd M A z l := rfl
  rw [hfun]
  refine ⟨(traceCLM (ZMod L × Fin W)).contDiff.comp hP.1, fun k t => ?_⟩
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    (traceCLM (ZMod L × Fin W)).iteratedFDeriv_comp_left hP.1.contDiffAt
      (i := k) (by exact_mod_cast le_top)]
  refine ((traceCLM (ZMod L × Fin W)).norm_compContinuousMultilinearMap_le _).trans ?_
  exact mul_le_mul norm_traceCLM_le (hP.2 k t) (norm_nonneg _) (Nat.cast_nonneg _)

end GUELineProd

/-! #### A third-order Taylor bound on `[0, 1]` (the mean value inequality, three times) -/

/-- `‖f 1 - f 0 - f'(0) - ½ f''(0)‖ ≤ sup ‖f'''‖` for a `C^ω` function of a real variable (the
crude constant `1` in place of `1/6` is enough here). -/
private theorem gueStep_taylor3 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : ContDiff ℝ ⊤ f) {C : ℝ} (hC : ∀ s, ‖iteratedDeriv 3 f s‖ ≤ C) :
    ‖f 1 - f 0 - deriv f 0 - (1 / 2 : ℝ) • deriv (deriv f) 0‖ ≤ C := by
  have hd : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m f) := fun m =>
    hf.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _)
  have e3 : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  have hf0 : ∀ x, HasDerivAt f (deriv f x) x := fun x => by
    have := (hd 0 x).hasDerivAt; rwa [iteratedDeriv_zero] at this
  have hf1 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x => by
    have := (hd 1 x).hasDerivAt; rwa [iteratedDeriv_one] at this
  have hf2 : ∀ x, HasDerivAt (deriv (deriv f)) (iteratedDeriv 3 f x) x := fun x => by
    have := (hd 2 x).hasDerivAt
    rwa [iteratedDeriv_succ, iteratedDeriv_one, ← e3] at this
  set f1 := deriv f with hf1def
  set f2 := deriv f1 with hf2def
  -- step A: `‖f₂ x - f₂ 0‖ ≤ C x`
  have hA : ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f2 x - f2 0‖ ≤ C * (x - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ => (hf2 x).hasDerivWithinAt)
      (fun x _ => hC x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- step B: `g₁ s = f₁ s - s f₂(0)`
  have hB : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(f1 x - x • f2 0) - (f1 0 - (0 : ℝ) • f2 0)‖ ≤ C * (x - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => f1 s - s • f2 0)
      (f' := fun s => f2 s - f2 0) (fun x _ => ?_) (fun x hx => ?_)
    · have h := (hf1 x).sub ((hasDerivAt_id x).smul_const (f2 0))
      simp only [id, one_smul] at h
      exact h.hasDerivWithinAt
    · have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      refine (hA x hx').trans ?_
      nlinarith [hx'.1, hx'.2]
  -- step C: `g₀ s = f s - s f₁(0) - (s²/2) f₂(0)`
  have hC' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖(f x - x • f1 0 - (x ^ 2 / 2) • f2 0)
          - (f 0 - (0 : ℝ) • f1 0 - ((0 : ℝ) ^ 2 / 2) • f2 0)‖ ≤ C * (x - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => f s - s • f1 0 - (s ^ 2 / 2) • f2 0)
      (f' := fun s => (f1 s - s • f2 0) - (f1 0 - (0 : ℝ) • f2 0)) (fun x _ => ?_)
      (fun x hx => ?_)
    · have h := ((hf0 x).sub ((hasDerivAt_id x).smul_const (f1 0))).sub
        (((hasDerivAt_pow 2 x).div_const 2).smul_const (f2 0))
      have heq : f1 x - (1 : ℝ) • f1 0 - ((((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2) • f2 0
          = (f1 x - x • f2 0) - (f1 0 - (0 : ℝ) • f2 0) := by
        have h2 : ((((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2) = x := by norm_num
        rw [h2, one_smul, zero_smul, sub_zero]
        abel
      simp only [id] at h
      rw [heq] at h
      exact h.hasDerivWithinAt
    · have hx' : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
      refine (hB x hx').trans ?_
      nlinarith [hx'.1, hx'.2]
  have h1 := hC' 1 ⟨zero_le_one, le_rfl⟩
  have heq : (f 1 - (1 : ℝ) • f1 0 - ((1 : ℝ) ^ 2 / 2) • f2 0)
        - (f 0 - (0 : ℝ) • f1 0 - ((0 : ℝ) ^ 2 / 2) • f2 0)
      = f 1 - f 0 - f1 0 - (1 / 2 : ℝ) • f2 0 := by
    have h2 : ((1 : ℝ) ^ 2 / 2) = 1 / 2 := by norm_num
    have h3 : ((0 : ℝ) ^ 2 / 2) = 0 := by norm_num
    rw [h2, h3, one_smul, zero_smul, zero_smul, sub_zero, sub_zero]
    abel
  rw [heq] at h1
  simpa using h1

/-! #### The third-order Taylor bound for the loop observable -/

section GUELoopTaylor

variable {d} {N : ℕ}

private theorem gueStep_card_idx : (Fintype.card (d.Idx N) : ℝ) = (ouMatrixSize d N : ℝ) := by
  simp [ouMatrixSize, Fintype.card_prod, ZMod.card]

/-- **Direct third-order Taylor bound for the loop observable**: for Hermitian
`M, A` and `|Im z| ≥ η > 0`,
`‖Φ(M+A) - Φ(M) - DΦ(M)[A] - ½D²Φ(M)[A,A]‖ ≤ card · 6 (n+1)³ η^{-(n+3)} ‖A‖³`. -/
private theorem gueStep_taylor_loopObs {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    {M A : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (hA : A.IsHermitian) :
    ‖loopObs d N z I (M + A) - loopObs d N z I M - fderiv ℝ (loopObs d N z I) M A
        - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (loopObs d N z I)) M A A‖
      ≤ (ouMatrixSize d N : ℝ) * (6 * ((I.length : ℝ) + 1) ^ 3 * η⁻¹ ^ (I.length + 3)
          * ‖A‖ ^ 3) := by
  have hTF : TestFun d N (loopObs d N z I) := testFun_loopObs_of_im_le hz hη hzη hwf hn
  set Φ := loopObs d N z I with hΦ
  set f : ℝ → ℂ := fun s => Φ (M + (s : ℂ) • A) with hfdef
  have hlen : (I.σ.zip I.a).length = I.length := by
    rw [List.length_zip, hwf]; simp [LoopIdx.length]
  have hfeq : f = fun s : ℝ => Matrix.trace (gueStep_lineProd M A z (I.σ.zip I.a) s) := by
    funext s
    simp only [hfdef, hΦ]
    rw [loopObs_of_isHermitian (isHermitian_add_realSmul hM hA s)]
    rfl
  have hT := gueStep_trace_lineProd_bound hM hA hη hzη (I.σ.zip I.a)
  have hfC : ContDiff ℝ ⊤ f := by rw [hfeq]; exact hT.1
  have hbound : ∀ s, ‖iteratedDeriv 3 f s‖
      ≤ (ouMatrixSize d N : ℝ) * (6 * ((I.length : ℝ) + 1) ^ 3 * η⁻¹ ^ (I.length + 3)
          * ‖A‖ ^ 3) := by
    intro s
    rw [hfeq]
    refine (hT.2 3 s).trans (le_of_eq ?_)
    rw [hlen, gueStep_card_idx]
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6]
    ring
  have htay := gueStep_taylor3 hfC hbound
  have hd1 : ∀ s : ℝ, HasDerivAt f (fderiv ℝ Φ (M + (s : ℂ) • A) A) s := fun s =>
    ((hTF.differentiable _).hasFDerivAt).comp_hasDerivAt s (hasDerivAt_line M A s)
  have hderiv : deriv f = fun s : ℝ => fderiv ℝ Φ (M + (s : ℂ) • A) A :=
    funext fun s => (hd1 s).deriv
  have hd2 : HasDerivAt (fun s : ℝ => fderiv ℝ Φ (M + (s : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ Φ) M A A) 0 := by
    have h := (hasFDerivAt_fderiv_apply hTF A (M + ((0 : ℝ) : ℂ) • A)).comp_hasDerivAt 0
      (hasDerivAt_line M A 0)
    simp only [Complex.ofReal_zero, zero_smul, add_zero, ContinuousLinearMap.flip_apply] at h
    exact h
  have hf1 : f 1 = Φ (M + A) := by simp [hfdef]
  have hf0 : f 0 = Φ M := by simp [hfdef]
  have hd10 : deriv f 0 = fderiv ℝ Φ M A := by rw [hderiv]; simp
  have hd20 : deriv (deriv f) 0 = fderiv ℝ (fderiv ℝ Φ) M A A := by
    rw [hderiv]; exact hd2.deriv
  rw [hf1, hf0, hd10, hd20] at htay
  exact htay

end GUELoopTaylor

/-! #### Gaussian moments of the unit GUE field `gueUnit d` -/

section GUEMoments

variable {d}

private theorem gueStep_map_coord (c : Coord d) :
    (gueUnit d).map (fun y : Ω d => y c) = gaussianReal 0 (gueUnitVar d c) :=
  Measure.infinitePi_map_eval _ c

private theorem gueStep_integrable_pow (c : Coord d) (k : ℕ) :
    Integrable (fun y : Ω d => (y c) ^ k) (gueUnit d) := by
  have hf : AEMeasurable (fun y : Ω d => y c) (gueUnit d) := (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x ^ k) ((gueUnit d).map fun y => y c) := by
    rw [gueStep_map_coord]; exact RBM.integrable_pow_gaussianReal _ k
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

private theorem gueStep_integrable_coord (c : Coord d) :
    Integrable (fun y : Ω d => y c) (gueUnit d) := by
  simpa using gueStep_integrable_pow c 1

private theorem gueStep_integral_pow (c : Coord d) (k : ℕ) :
    ∫ y, (y c) ^ k ∂(gueUnit d) = ∫ x, x ^ k ∂(gaussianReal 0 (gueUnitVar d c)) := by
  rw [← gueStep_map_coord c,
    integral_map (measurable_pi_apply c).aemeasurable (by fun_prop)]

private theorem gueStep_integral_coord (c : Coord d) : ∫ y, y c ∂(gueUnit d) = 0 := by
  have h := gueStep_integral_pow c 1
  simp only [pow_one] at h
  rw [h, integral_id_gaussianReal]

private theorem gueStep_integral_sq (c : Coord d) :
    ∫ y, (y c) ^ 2 ∂(gueUnit d) = (gueUnitVar d c : ℝ) := by
  rw [gueStep_integral_pow, show (2 : ℕ) = 2 * 1 from rfl, RBM.integral_pow_gaussianReal]
  simp

private theorem gueStep_integral_four (c : Coord d) :
    ∫ y, (y c) ^ 4 ∂(gueUnit d) = 3 * (gueUnitVar d c : ℝ) ^ 2 := by
  rw [gueStep_integral_pow, show (4 : ℕ) = 2 * 2 from rfl, RBM.integral_pow_gaussianReal]
  simp [Finset.prod_range_succ]
  norm_num

private theorem gueStep_var_le_one (c : Coord d) : (gueUnitVar d c : ℝ) ≤ 1 := by
  unfold gueUnitVar; split_ifs <;> norm_num

private theorem gueStep_var_nonneg (c : Coord d) : 0 ≤ (gueUnitVar d c : ℝ) :=
  NNReal.coe_nonneg _

/-- Distinct coordinates of `gueUnit d` are uncorrelated. -/
private theorem gueStep_integral_mul {c c' : Coord d} (h : c ≠ c') :
    ∫ y, y c * y c' ∂(gueUnit d) = 0 := by
  have hI : iIndepFun (fun (i : Coord d) (y : Ω d) => id (y i)) (gueUnit d) :=
    iIndepFun_infinitePi (P := fun c => gaussianReal 0 (gueUnitVar d c)) (X := fun _ => id)
      (fun _ => measurable_id)
  have hind : IndepFun (fun y : Ω d => y c) (fun y : Ω d => y c') (gueUnit d) := hI.indepFun h
  rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply c).aestronglyMeasurable
    (measurable_pi_apply c').aestronglyMeasurable]
  simp [gueStep_integral_coord c]

private theorem gueStep_integrable_mul (c c' : Coord d) :
    Integrable (fun y : Ω d => y c * y c') (gueUnit d) := by
  refine Integrable.mono' ((gueStep_integrable_pow c 2).add (gueStep_integrable_pow c' 2))
    ((measurable_pi_apply c).mul (measurable_pi_apply c')).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  change |y c| * |y c'| ≤ y c ^ 2 + y c' ^ 2
  nlinarith [sq_nonneg (|y c| - |y c'|), sq_abs (y c), sq_abs (y c'), abs_nonneg (y c),
    abs_nonneg (y c')]

end GUEMoments

/-! #### The first- and second-order expectations, and the moments of `‖X‖` -/

section GUEExpect

variable {d} {N : ℕ}

private theorem gueStep_Hflow_eq_sum (v : ℝ) (y : Ω d) :
    Hflow d N v y = ∑ p ∈ usedCoord d N,
      (Real.sqrt v * y (crd d N p)) • Bmat d N p.1 p.2.1 p.2.2 := by
  rw [Hflow_eq_realSmul, Xmat_eq_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [smul_smul]

/-- **The first-order term has mean zero** under `gueUnit d`. -/
private theorem gueStep_first (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (v : ℝ) :
    Integrable (fun y => fderiv ℝ Φ M (Hflow d N v y)) (gueUnit d) ∧
      ∫ y, fderiv ℝ Φ M (Hflow d N v y) ∂(gueUnit d) = 0 := by
  have hrep : (fun y => fderiv ℝ Φ M (Hflow d N v y))
      = fun y => ∑ p ∈ usedCoord d N, (Real.sqrt v * y (crd d N p)) • coordD1 d N Φ M p := by
    funext y
    rw [gueStep_Hflow_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun p _ => map_smul _ _ _
  rw [hrep]
  have hint : ∀ p ∈ usedCoord d N, Integrable
      (fun y : Ω d => (Real.sqrt v * y (crd d N p)) • coordD1 d N Φ M p) (gueUnit d) :=
    fun p _ => ((gueStep_integrable_coord _).const_mul _).smul_const _
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_smul_const, integral_const_mul, gueStep_integral_coord, mul_zero, zero_smul]

/-- **The second-order term**: `E D²Φ[H_v, H_v] = v ∑_{p used} gueUnitVar_p ∂_p²Φ`. -/
private theorem gueStep_second (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun y => fderiv ℝ (fderiv ℝ Φ) M (Hflow d N v y) (Hflow d N v y)) (gueUnit d) ∧
      ∫ y, fderiv ℝ (fderiv ℝ Φ) M (Hflow d N v y) (Hflow d N v y) ∂(gueUnit d)
        = v • ∑ p ∈ usedCoord d N, (gueUnitVar d (crd d N p) : ℝ) • coordD2 d N Φ M p := by
  set D2 := fderiv ℝ (fderiv ℝ Φ) M with hD2
  have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv
  have hrep : (fun y => D2 (Hflow d N v y) (Hflow d N v y))
      = fun y => ∑ q ∈ usedCoord d N, ∑ p ∈ usedCoord d N,
          (v * (y (crd d N p) * y (crd d N q))) •
            D2 (Bmat d N p.1 p.2.1 p.2.2) (Bmat d N q.1 q.2.1 q.2.2) := by
    funext y
    rw [gueStep_Hflow_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, ← ContinuousLinearMap.flip_apply D2, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, ContinuousLinearMap.flip_apply, smul_smul]
    congr 1
    linear_combination (y (crd d N p) * y (crd d N q)) * hsq
  have hint2 : ∀ p q : d.Idx N × d.Idx N × Bool, Integrable
      (fun y : Ω d => (v * (y (crd d N p) * y (crd d N q))) •
        D2 (Bmat d N p.1 p.2.1 p.2.2) (Bmat d N q.1 q.2.1 q.2.2)) (gueUnit d) :=
    fun p q => ((gueStep_integrable_mul _ _).const_mul v).smul_const _
  rw [hrep]
  refine ⟨integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun p _ => hint2 p q, ?_⟩
  rw [integral_finsetSum _ fun q _ => integrable_finsetSum _ fun p _ => hint2 p q,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_finsetSum _ fun p _ => hint2 p q, Finset.sum_eq_single q]
  · rw [integral_smul_const, integral_const_mul]
    have hqq : ∫ y, y (crd d N q) * y (crd d N q) ∂(gueUnit d)
        = (gueUnitVar d (crd d N q) : ℝ) := by
      rw [← gueStep_integral_sq]
      exact integral_congr_ae (Eventually.of_forall fun y => (sq _).symm)
    rw [hqq, smul_smul]
    rfl
  · intro p _ hpq
    rw [integral_smul_const, integral_const_mul,
      gueStep_integral_mul (fun h => hpq (crd_injective d N h)), mul_zero, zero_smul]
  · intro h; exact absurd hq h

/-- The `gueUnitVar`-weighted coordinate sum is the paper's `∑_{ij} ∂_ij ∂_ji` (constant profile
`1`; `gueUnitVar` is `1` on the diagonal and `1/2` off it, the pattern of `gvar`). -/
private theorem gueStep_sum_used_wirt (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ p ∈ usedCoord d N, (gueUnitVar d (crd d N p) : ℝ) • coordD2 d N Φ M p
      = ∑ i : d.Idx N, ∑ j : d.Idx N, wirtSecond d N Φ M i j := by
  have hvar : ∀ p : d.Idx N × d.Idx N × Bool, (gueUnitVar d (crd d N p) : ℝ)
      = if p.1 = p.2.1 then (fun _ _ : d.Idx N => (1 : ℝ)) p.1 p.2.1
        else (fun _ _ : d.Idx N => (1 : ℝ)) p.1 p.2.1 / 2 := by
    intro p
    unfold gueUnitVar
    by_cases h : p.1 = p.2.1
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl fun p _ => by rw [hvar p]]
  rw [show usedCoord d N = Finset.univ.filter (fun p : d.Idx N × d.Idx N × Bool =>
      idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl]
  rw [sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N)
    (fun _ _ : d.Idx N => (1 : ℝ)) (fun _ _ => rfl) (coordD2 d N Φ M)
    (fun i j => coordD2_swap Φ M i j true) (fun i j => coordD2_swap Φ M i j false)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [one_smul]
  rfl

private theorem gueStep_S_ge_one : (1 : ℝ) ≤ (ouMatrixSize d N : ℝ) := by
  have h : 1 ≤ ouMatrixSize d N := by
    unfold ouMatrixSize
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne _) (d.W_pos N).ne')
  exact_mod_cast h

private theorem gueStep_card_coords :
    (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ) = 2 * (ouMatrixSize d N : ℝ) ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card, Fintype.card_fin, ouMatrixSize]
  push_cast
  ring

private theorem gueStep_measurable_coordSq : Measurable (coordSq d N) := by
  unfold coordSq
  exact Finset.measurable_sum _ fun t _ => (measurable_pi_apply _).pow_const 2

private theorem gueStep_integrable_coordSq : Integrable (coordSq d N) (gueUnit d) := by
  unfold coordSq
  exact integrable_finsetSum _ fun t _ => gueStep_integrable_pow _ 2

private theorem gueStep_integral_coordSq_le :
    ∫ y, coordSq d N y ∂(gueUnit d) ≤ 2 * (ouMatrixSize d N : ℝ) ^ 2 := by
  unfold coordSq
  rw [integral_finsetSum _ fun t _ => gueStep_integrable_pow _ 2, ← gueStep_card_coords]
  calc ∑ t : d.Idx N × d.Idx N × Bool, ∫ y, (y ⟨N, t⟩) ^ 2 ∂(gueUnit d)
      ≤ ∑ _t : d.Idx N × d.Idx N × Bool, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ => by rw [gueStep_integral_sq]; exact gueStep_var_le_one _
    _ = (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ) := by simp

private theorem gueStep_coordSq_sq_le (y : Ω d) :
    coordSq d N y ^ 2 ≤ (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ)
      * ∑ t : d.Idx N × d.Idx N × Bool, (y ⟨N, t⟩) ^ 4 := by
  unfold coordSq
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (d.Idx N × d.Idx N × Bool)))
    (f := fun t => (y ⟨N, t⟩) ^ 2)
  simp only [Finset.card_univ] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun t _ => by ring

private theorem gueStep_integrable_coordSq_sq :
    Integrable (fun y => coordSq d N y ^ 2) (gueUnit d) := by
  refine Integrable.mono' ((integrable_finsetSum
      (Finset.univ : Finset (d.Idx N × d.Idx N × Bool)) fun t _ =>
      gueStep_integrable_pow (d := d) ⟨N, t⟩ 4).const_mul
      (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ))
    (gueStep_measurable_coordSq.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa using gueStep_coordSq_sq_le y

private theorem gueStep_integral_coordSq_sq_le :
    ∫ y, coordSq d N y ^ 2 ∂(gueUnit d) ≤ 12 * (ouMatrixSize d N : ℝ) ^ 4 := by
  have hint4 : Integrable (fun y : Ω d => (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ)
      * ∑ t : d.Idx N × d.Idx N × Bool, (y ⟨N, t⟩) ^ 4) (gueUnit d) :=
    (integrable_finsetSum (Finset.univ : Finset (d.Idx N × d.Idx N × Bool)) fun t _ =>
      gueStep_integrable_pow (d := d) ⟨N, t⟩ 4).const_mul _
  refine (integral_mono gueStep_integrable_coordSq_sq hint4 gueStep_coordSq_sq_le).trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun t _ => gueStep_integrable_pow _ 4]
  have hsum : ∑ t : d.Idx N × d.Idx N × Bool, ∫ y, (y ⟨N, t⟩) ^ 4 ∂(gueUnit d)
      ≤ 3 * (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ) := by
    calc ∑ t : d.Idx N × d.Idx N × Bool, ∫ y, (y ⟨N, t⟩) ^ 4 ∂(gueUnit d)
        ≤ ∑ _t : d.Idx N × d.Idx N × Bool, (3 : ℝ) := by
          refine Finset.sum_le_sum fun t _ => ?_
          rw [gueStep_integral_four]
          have h1 := gueStep_var_le_one (d := d) ⟨N, t⟩
          have h0 := gueStep_var_nonneg (d := d) ⟨N, t⟩
          nlinarith
      _ = 3 * (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ) := by simp [mul_comm]
  have hc0 : (0 : ℝ) ≤ (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ) := Nat.cast_nonneg _
  calc (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ)
        * ∑ t : d.Idx N × d.Idx N × Bool, ∫ y, (y ⟨N, t⟩) ^ 4 ∂(gueUnit d)
      ≤ (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ)
          * (3 * (Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ = 12 * (ouMatrixSize d N : ℝ) ^ 4 := by rw [gueStep_card_coords]; ring

private theorem gueStep_norm_Xmat_sq_le (y : Ω d) :
    ‖Xmat d N y‖ ^ 2 ≤ 2 * coordSq d N y :=
  (l2_opNorm_sq_le_frobSq _).trans (frobSq_Xmat_le y)

private theorem gueStep_norm_Xmat_le (y : Ω d) :
    ‖Xmat d N y‖ ≤ 1 + 2 * coordSq d N y := by
  have h := gueStep_norm_Xmat_sq_le (N := N) y
  nlinarith [sq_nonneg (‖Xmat d N y‖ - 1), norm_nonneg (Xmat d N y)]

private theorem gueStep_norm_Xmat_cube_le (y : Ω d) :
    ‖Xmat d N y‖ ^ 3 ≤ 4 * coordSq d N y ^ 2 + 2 * coordSq d N y := by
  have h := gueStep_norm_Xmat_sq_le (N := N) y
  set a := ‖Xmat d N y‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  have h3 : a ^ 3 ≤ a ^ 4 + a ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg (a - 1)), sq_nonneg a]
  have h4 : a ^ 4 ≤ 4 * coordSq d N y ^ 2 := by
    have : a ^ 4 = (a ^ 2) ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg a]
  linarith

private theorem gueStep_moment1 :
    Integrable (fun y => ‖Xmat d N y‖) (gueUnit d) ∧
      ∫ y, ‖Xmat d N y‖ ∂(gueUnit d) ≤ 5 * (ouMatrixSize d N : ℝ) ^ 2 := by
  have hbint : Integrable (fun y => 1 + 2 * coordSq d N y) (gueUnit d) :=
    (integrable_const 1).add (gueStep_integrable_coordSq.const_mul 2)
  have hint : Integrable (fun y => ‖Xmat d N y‖) (gueUnit d) :=
    Integrable.mono' hbint (continuous_Xmat d N).norm.aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact gueStep_norm_Xmat_le y)
  refine ⟨hint, (integral_mono hint hbint gueStep_norm_Xmat_le).trans ?_⟩
  rw [integral_add (integrable_const 1) (gueStep_integrable_coordSq.const_mul 2),
    integral_const_mul, integral_const]
  have h1 := gueStep_integral_coordSq_le (d := d) (N := N)
  have hS := gueStep_S_ge_one (d := d) (N := N)
  simp only [probReal_univ, smul_eq_mul, mul_one]
  nlinarith

private theorem gueStep_moment3 :
    Integrable (fun y => ‖Xmat d N y‖ ^ 3) (gueUnit d) ∧
      ∫ y, ‖Xmat d N y‖ ^ 3 ∂(gueUnit d) ≤ 52 * (ouMatrixSize d N : ℝ) ^ 4 := by
  have hbint : Integrable (fun y => 4 * coordSq d N y ^ 2 + 2 * coordSq d N y) (gueUnit d) :=
    (gueStep_integrable_coordSq_sq.const_mul 4).add (gueStep_integrable_coordSq.const_mul 2)
  have hint : Integrable (fun y => ‖Xmat d N y‖ ^ 3) (gueUnit d) :=
    Integrable.mono' hbint ((continuous_Xmat d N).norm.pow 3).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (by positivity)]; exact gueStep_norm_Xmat_cube_le y)
  refine ⟨hint, (integral_mono hint hbint gueStep_norm_Xmat_cube_le).trans ?_⟩
  rw [integral_add (gueStep_integrable_coordSq_sq.const_mul 4)
      (gueStep_integrable_coordSq.const_mul 2), integral_const_mul, integral_const_mul]
  have h1 := gueStep_integral_coordSq_le (d := d) (N := N)
  have h2 := gueStep_integral_coordSq_sq_le (d := d) (N := N)
  have hS := gueStep_S_ge_one (d := d) (N := N)
  nlinarith [pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) hS 2]

end GUEExpect

/-! #### The space error at a single time (the third-order Taylor remainder, averaged) -/

section GUESpaceErr

variable {d} {N : ℕ}

private theorem gueStep_integrable_cont_bdd {E : Type*} [NormedAddCommGroup E]
    {f : Ω d → E} (hf : Continuous f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    Integrable f (gueUnit d) :=
  (memLp_top_of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)).integrable le_top

private theorem gueStep_norm_integral_le {f : Ω d → ℂ} (hf : Integrable f (gueUnit d)) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) : ‖∫ y, f y ∂(gueUnit d)‖ ≤ C := by
  calc ‖∫ y, f y ∂(gueUnit d)‖ ≤ ∫ y, ‖f y‖ ∂(gueUnit d) := norm_integral_le_integral_norm _
    _ ≤ ∫ _y, C ∂(gueUnit d) := integral_mono hf.norm (integrable_const C) hC
    _ = C := by simp

/-- **The space error** of one GUE step at a fixed spectral parameter:
`‖E Φ(M + H_v) - Φ(M) - (v/2) ∑_{ij} ∂_ij∂_ji Φ(M)‖`
`≤ card · 6(n+1)³ η^{-(n+3)} v^{3/2} · 52 card⁴`. -/
private theorem gueStep_space_err {z : ℂ} {η : ℝ} (hz : z.im ≠ 0) (hη : 0 < η)
    (hzη : η ≤ |z.im|) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) {v : ℝ} (hv : 0 ≤ v) :
    ‖(∫ y, loopObs d N z I (M + Hflow d N v y) ∂(gueUnit d)) - loopObs d N z I M
        - (v / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, wirtSecond d N (loopObs d N z I) M i j‖
      ≤ (ouMatrixSize d N : ℝ) * (6 * ((I.length : ℝ) + 1) ^ 3 * η⁻¹ ^ (I.length + 3))
          * (Real.sqrt v ^ 3 * (52 * (ouMatrixSize d N : ℝ) ^ 4)) := by
  have hTF := testFun_loopObs_of_im_le hz hη hzη hwf hn
  set Φ := loopObs d N z I with hΦ
  obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
  set K3 : ℝ := (ouMatrixSize d N : ℝ) * (6 * ((I.length : ℝ) + 1) ^ 3 * η⁻¹ ^ (I.length + 3))
    with hK3
  have hK30 : 0 ≤ K3 := by positivity
  have hcont : Continuous fun y : Ω d => Φ (M + Hflow d N v y) :=
    hTF.contDiff.continuous.comp (continuous_const.add (continuous_Hflow d N v))
  have hIA : Integrable (fun y => Φ (M + Hflow d N v y)) (gueUnit d) :=
    gueStep_integrable_cont_bdd hcont fun y => hC₀ _
  obtain ⟨hI1, hE1⟩ := gueStep_first (N := N) Φ M v
  obtain ⟨hI2, hE2⟩ := gueStep_second (N := N) Φ M hv
  set T : Ω d → ℂ := fun y => Φ (M + Hflow d N v y) - Φ M - fderiv ℝ Φ M (Hflow d N v y)
    - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Φ) M (Hflow d N v y) (Hflow d N v y) with hT
  have hIT : Integrable T (gueUnit d) :=
    ((hIA.sub (integrable_const _)).sub hI1).sub (hI2.smul (1 / 2 : ℝ))
  have hTval : ∫ y, T y ∂(gueUnit d) = (∫ y, Φ (M + Hflow d N v y) ∂(gueUnit d)) - Φ M
      - (v / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N, wirtSecond d N Φ M i j := by
    have h1' : Integrable (fun y => Φ (M + Hflow d N v y) - Φ M) (gueUnit d) :=
      hIA.sub (integrable_const _)
    have h2' : Integrable (fun y => Φ (M + Hflow d N v y) - Φ M
        - fderiv ℝ Φ M (Hflow d N v y)) (gueUnit d) := h1'.sub hI1
    have h3' : Integrable (fun y => (1 / 2 : ℝ) •
        fderiv ℝ (fderiv ℝ Φ) M (Hflow d N v y) (Hflow d N v y)) (gueUnit d) :=
      hI2.smul (1 / 2 : ℝ)
    simp only [hT]
    rw [integral_sub h2' h3', integral_sub h1' hI1, integral_sub hIA (integrable_const _),
      integral_const, integral_smul, hE1, hE2, gueStep_sum_used_wirt, smul_smul]
    simp only [probReal_univ, one_smul, sub_zero]
    congr 2
    ring
  have hTb : ∀ y, ‖T y‖ ≤ K3 * (Real.sqrt v ^ 3 * ‖Xmat d N y‖ ^ 3) := by
    intro y
    have h := gueStep_taylor_loopObs hz hη hzη hwf hn hM (Hflow_isHermitian d N v y)
    have hnorm : ‖Hflow d N v y‖ = Real.sqrt v * ‖Xmat d N y‖ := by
      rw [Hflow_eq_realSmul, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    refine h.trans (le_of_eq ?_)
    rw [hnorm, hK3]
    ring
  obtain ⟨hI3, hE3⟩ := gueStep_moment3 (d := d) (N := N)
  rw [← hTval]
  calc ‖∫ y, T y ∂(gueUnit d)‖ ≤ ∫ y, ‖T y‖ ∂(gueUnit d) := norm_integral_le_integral_norm _
    _ ≤ ∫ y, K3 * (Real.sqrt v ^ 3 * ‖Xmat d N y‖ ^ 3) ∂(gueUnit d) :=
        integral_mono hIT.norm ((hI3.const_mul _).const_mul _) hTb
    _ = K3 * (Real.sqrt v ^ 3 * ∫ y, ‖Xmat d N y‖ ^ 3 ∂(gueUnit d)) := by
        rw [integral_const_mul, integral_const_mul]
    _ ≤ K3 * (Real.sqrt v ^ 3 * (52 * (ouMatrixSize d N : ℝ) ^ 4)) := by
        gcongr
    _ = _ := by rw [hK3]

end GUESpaceErr

/-! #### The freezing lemma for `Pgue d` (the proof of `Grid.condExp_freeze`, with the mixed step
law) -/

section GUEFreeze

variable {d}

/-- The increment `ω (k+1)` is independent of `Grid.filt d k` under `Pgue d`. -/
private theorem gueStep_indep_incr (k : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : Ωg d => ω (k + 1)) inferInstance) (filt d k)
      (Pgue d) := by
  have hI : iIndepFun (fun i : ℕ => (fun ω : Ωg d => ω i)) (Pgue d) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : Ω d → Ω d)) (mX := fun _ => measurable_id)
  have hIndep : iIndep (fun n : ℕ => MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance)
      (Pgue d) := (iIndepFun_iff_iIndep (fun _ : ℕ => (inferInstance : MeasurableSpace (Ω d)))
        (fun i ω => ω i) (Pgue d)).mp hI
  have hle : ∀ n : ℕ, MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance
      ≤ (inferInstance : MeasurableSpace (Ωg d)) :=
    fun n => le_iSup (fun n => MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance) n
  have hsplit := indep_biSup_compl hle hIndep (Set.Iic k)
  have hfilt : filt d k
      = ⨆ n ∈ Set.Iic k, MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance := by
    have hshow : filt d k =
        (inferInstance : MeasurableSpace (↥(Set.Iic k) → Ω d)).comap
          (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) := rfl
    have hpi : (inferInstance : MeasurableSpace (↥(Set.Iic k) → Ω d))
        = ⨆ a : ↥(Set.Iic k),
            MeasurableSpace.comap (fun g : ↥(Set.Iic k) → Ω d => g a) inferInstance := rfl
    rw [hshow, hpi, MeasurableSpace.comap_iSup, iSup_subtype]
    simp only [MeasurableSpace.comap_comp]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro _
    rfl
  rw [hfilt]
  have hmono : MeasurableSpace.comap (fun ω : Ωg d => ω (k + 1)) inferInstance
      ≤ ⨆ n ∈ (Set.Iic k)ᶜ, MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance := by
    have hmem : (k + 1) ∈ (Set.Iic k)ᶜ := by simp
    exact le_biSup (fun n => MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance) hmem
  exact indep_of_indep_of_le_left hsplit.symm hmono

/-- The law of the increment `ω (k+1)` under `Pgue d` is `gueUnit d`. -/
private theorem gueStep_map_incr (k : ℕ) :
    (Pgue d).map (fun ω : Ωg d => ω (k + 1)) = gueUnit d :=
  Measure.infinitePi_map_eval _ (k + 1)

/-- **The freezing lemma for `Pgue d`** (real-valued). -/
private theorem gueStep_condExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : Ωg d → β} (hY : Measurable[filt d k] Y)
    {F : β → Ω d → ℝ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set μ : Measure (Ωg d) := Pgue d with hμdef
  set Z : Ωg d → Ω d := fun ω => ω (k + 1) with hZdef
  set Φ : Ωg d → β × Ω d := fun ω => (Y ω, Z ω) with hΦdef
  set ν : Measure (Ω d) := gueUnit d with hνdef
  set G : β → ℝ := fun y => ∫ x, F y x ∂ν with hGdef
  have hYmeas : Measurable Y := hY.mono ((filt d).le k) le_rfl
  have hZmeas : Measurable Z := measurable_pi_apply (k + 1)
  have hΦmeas : Measurable Φ := hYmeas.prodMk hZmeas
  have hFsm : StronglyMeasurable (fun p : β × Ω d => F p.1 p.2) := hF.stronglyMeasurable
  have hνmap : μ.map Z = ν := gueStep_map_incr k
  have hindYZ : IndepFun Y Z μ := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt d k := hY.comap_le
    exact (indep_of_indep_of_le_right (gueStep_indep_incr k) hcle).symm
  have hIntΦ : Integrable (fun p : β × Ω d => F p.1 p.2) (μ.map Φ) := by
    rw [integrable_map_measure hFsm.aestronglyMeasurable hΦmeas.aemeasurable]
    exact hInt
  have hprodglobal : μ.map Φ = (μ.map Y).prod ν := by
    rw [← hνmap]
    exact hindYZ.map_prod_eq_prod_map_map hYmeas.aemeasurable hZmeas.aemeasurable
  have hGmeas : StronglyMeasurable G := hFsm.integral_prod_right'
  have hkey : ∀ A : Set (Ωg d), MeasurableSet[filt d k] A →
      ∫ ω in A, F (Y ω) (Z ω) ∂μ = ∫ ω in A, G (Y ω) ∂μ := by
    intro A hA
    have hprodA : (μ.restrict A).map Φ = ((μ.restrict A).map Y).prod ν := by
      refine (Measure.prod_eq ?_).symm
      intro s t hs ht
      have hpre : Φ ⁻¹' (s ×ˢ t) = Y ⁻¹' s ∩ Z ⁻¹' t := by
        ext ω; simp [Φ, Set.mem_prod]
      rw [Measure.map_apply hΦmeas (hs.prod ht), Measure.map_apply hYmeas hs,
        Measure.restrict_apply (hΦmeas (hs.prod ht)), Measure.restrict_apply (hYmeas hs), hpre]
      have hrearrange : Y ⁻¹' s ∩ Z ⁻¹' t ∩ A = Z ⁻¹' t ∩ (A ∩ Y ⁻¹' s) := by
        ext ω; simp only [Set.mem_inter_iff]; tauto
      rw [hrearrange]
      have hASmem : MeasurableSet[filt d k] (A ∩ Y ⁻¹' s) := hA.inter (hY hs)
      have hZTmem : MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' t) :=
        ⟨t, ht, rfl⟩
      have hindep := (Indep_iff (MeasurableSpace.comap Z inferInstance) (filt d k) μ).1
        (gueStep_indep_incr k) (Z ⁻¹' t) (A ∩ Y ⁻¹' s) hZTmem hASmem
      rw [hindep, ← Measure.map_apply hZmeas ht, hνmap, Set.inter_comm (Y ⁻¹' s) A]
      ring
    have hIntΦA : Integrable (fun p : β × Ω d => F p.1 p.2) ((μ.restrict A).map Φ) :=
      hIntΦ.mono_measure (Measure.map_mono Measure.restrict_le_self hΦmeas)
    calc
      ∫ ω in A, F (Y ω) (Z ω) ∂μ
          = ∫ p, F p.1 p.2 ∂((μ.restrict A).map Φ) :=
            (integral_map hΦmeas.aemeasurable hFsm.aestronglyMeasurable).symm
      _ = ∫ p, F p.1 p.2 ∂(((μ.restrict A).map Y).prod ν) := by rw [hprodA]
      _ = ∫ y, G y ∂((μ.restrict A).map Y) := integral_prod _ (hprodA ▸ hIntΦA)
      _ = ∫ ω in A, G (Y ω) ∂μ := integral_map hYmeas.aemeasurable hGmeas.aestronglyMeasurable
  have hIntG : Integrable G (μ.map Y) := by
    have hIntΦY : Integrable (fun p : β × Ω d => F p.1 p.2) ((μ.map Y).prod ν) :=
      hprodglobal ▸ hIntΦ
    exact hIntΦY.integral_prod_left
  have hGYint : Integrable (fun ω => G (Y ω)) μ :=
    (integrable_map_measure hGmeas.aestronglyMeasurable hYmeas.aemeasurable).mp hIntG
  have hGYmeas : StronglyMeasurable[filt d k] (fun ω => G (Y ω)) := hGmeas.comp_measurable hY
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((filt d).le k) hInt
    (fun s _ _ => hGYint.integrableOn) (fun s hs _ => (hkey s hs).symm)
    hGYmeas.aestronglyMeasurable).symm

/-- **The freezing lemma for `Pgue d`**, complex-valued (real and imaginary parts). -/
private theorem gueStep_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : Ωg d → β} (hY : Measurable[filt d k] Y)
    {F : β → Ω d → ℂ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (gueUnit d))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set f : Ωg d → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Ω d → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Ω d → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Ω d => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Ω d => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (Pgue d) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (Pgue d) := hInt.im
  have hfreezeRe := gueStep_condExp_freeze k hY hFre hIntRe
  have hfreezeIm := gueStep_condExp_freeze k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := filt d k) hInt
  have hReComb : (fun ω => RCLike.re ((Pgue d)[f | filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fre (Y ω) x ∂(gueUnit d) := by
    have hRe' : (fun ω => RCLike.re ((Pgue d)[f | filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fre (Y ω) (ω (k + 1)) | filt d k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((Pgue d)[f | filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fim (Y ω) x ∂(gueUnit d) := by
    have hIm' : (fun ω => RCLike.im ((Pgue d)[f | filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fim (Y ω) (ω (k + 1)) | filt d k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(gueUnit d) = RCLike.re (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(gueUnit d) = RCLike.im (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((Pgue d)[f | filt d k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωre, hreEq]
  · change RCLike.im ((Pgue d)[f | filt d k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωim, himEq]

end GUEFreeze

/-! #### Continuity of the `z`-motion term along a continuous Hermitian path -/

section GUEZMotionCont

variable {d} {N : ℕ}

private theorem gueStep_continuous_Gsig_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) :
    Continuous fun ω => Gsig (f ω) z σ := by
  cases σ with
  | false => exact continuous_green_comp hf hherm (by simpa using hz)
  | true => exact continuous_green_comp hf hherm hz

private theorem gueStep_continuous_foldr_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (l : List (Bool × ZMod (d.L N))) :
    Continuous fun ω => l.foldr (fun p A => Gsig (f ω) z p.1 * Eblk (d.L N) (d.W N) p.2 * A)
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  induction l with
  | nil => exact continuous_const
  | cons p l ih =>
      exact ((gueStep_continuous_Gsig_comp hf hherm hz p.1).mul continuous_const).mul ih

private theorem gueStep_continuous_gloop_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω => gloop (d.L N) (d.W N) (f ω) z I :=
  continuous_matrixTrace.comp (gueStep_continuous_foldr_comp hf hherm hz (I.σ.zip I.a))

private theorem gueStep_continuous_zMotion_comp {f : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hf : Continuous f) (hherm : ∀ ω, (f ω).IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (m : Bool → ℂ) (I : LoopIdx (ZMod (d.L N))) :
    Continuous fun ω => zMotion (d.L N) (d.W N) m (f ω) z I := by
  simp only [zMotion]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact continuous_const.mul
    (continuous_finsetSum _ fun b _ => gueStep_continuous_gloop_comp hf hherm hz _)

end GUEZMotionCont

/-! #### The GUE-phase grid step, and the conditional expectation of the next loop -/

section GUEGridStep

variable {d}

private theorem gueStep_gueH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Ωg d) :
    gueH d t1 t0 K N (k + 1) ω = gueH d t1 t0 K N k ω
      + Hflow d N (step t1 t0 K N / (ouMatrixSize d N : ℝ)) (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  change gueH d t1 t0 K N (k + 1) ω = gueH d t1 t0 K N k ω
    + (Real.sqrt (step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ) • Xmat d N (ω (k + 1))
  unfold gueH
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

private theorem gueStep_gueH_measurable_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    Measurable[filt d k] (gueH d t1 t0 K N k) :=
  (@Matrix.measurable_iff (d.Idx N) (d.Idx N) ℂ _ (Ωg d) (filt d k)
      (fun ω => gueH d t1 t0 K N k ω)).mpr
    (fun i j => stronglyMeasurable_iff_measurable.mp (gueH_adapted d t1 t0 K N k i j))

/-- **Freezing on the GUE-phase grid**: conditioning on `filt d k` averages the fresh unit-GUE
increment against `gueUnit d`. -/
private theorem gueStep_condExp_loop_step (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (hz : (zt E (time t1 t0 K N (k + 1))).im ≠ 0) :
    (Pgue d)[fun ω' : Ωg d => loopObs d N (zt E (time t1 t0 K N (k + 1))) I
          (gueH d t1 t0 K N (k + 1) ω') | filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, loopObs d N (zt E (time t1 t0 K N (k + 1))) I
        (gueH d t1 t0 K N k ω + Hflow d N (step t1 t0 K N / (ouMatrixSize d N : ℝ)) x)
          ∂(gueUnit d) := by
  have hTF : TestFun d N (loopObs d N (zt E (time t1 t0 K N (k + 1))) I) :=
    testFun_loopObs_of_im_le hz (abs_pos.mpr hz) le_rfl hwf hn
  obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
  set v : ℝ := step t1 t0 K N / (ouMatrixSize d N : ℝ) with hv
  have hYmeas := gueStep_gueH_measurable_filt (d := d) t1 t0 K N k
  have hFmeas : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      loopObs d N (zt E (time t1 t0 K N (k + 1))) I (p.1 + Hflow d N v p.2)) :=
    (hTF.contDiff.continuous.comp
      (continuous_fst.add ((continuous_Hflow d N v).comp continuous_snd))).measurable
  have hFInt : ∀ p : Matrix (d.Idx N) (d.Idx N) ℂ,
      Integrable (fun x => loopObs d N (zt E (time t1 t0 K N (k + 1))) I
        (p + Hflow d N v x)) (gueUnit d) := fun p =>
    gueStep_integrable_cont_bdd
      (hTF.contDiff.continuous.comp (continuous_const.add (continuous_Hflow d N v)))
      fun x => hC₀ _
  have hHk1meas : Measurable (fun ω : Ωg d => gueH d t1 t0 K N (k + 1) ω) :=
    gueH_measurable d t1 t0 K N (k + 1)
  have hIntTarget : Integrable
      (fun ω : Ωg d => loopObs d N (zt E (time t1 t0 K N (k + 1))) I
        (gueH d t1 t0 K N (k + 1) ω)) (Pgue d) :=
    (memLp_top_of_bound (hTF.contDiff.continuous.measurable.comp hHk1meas).aestronglyMeasurable
      C₀ (Eventually.of_forall fun ω => hC₀ _)).integrable le_top
  have hEq : (fun ω : Ωg d => loopObs d N (zt E (time t1 t0 K N (k + 1))) I
        (gueH d t1 t0 K N (k + 1) ω))
      = fun ω => loopObs d N (zt E (time t1 t0 K N (k + 1))) I
          (gueH d t1 t0 K N k ω + Hflow d N v (ω (k + 1))) := by
    funext ω; rw [gueStep_gueH_succ]
  rw [hEq] at hIntTarget ⊢
  exact gueStep_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget

/-- The grid bookkeeping of the hypotheses of `condExp_loop_drift_gue`. -/
private theorem gueStep_grid_facts (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ht1 : 0 ≤ t1 N)
    (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hk : k < K N) :
    0 ≤ step t1 t0 K N ∧ step t1 t0 K N ≤ 1 ∧ 0 ≤ time t1 t0 K N k ∧
      time t1 t0 K N (k + 1) = time t1 t0 K N k + step t1 t0 K N ∧
      time t1 t0 K N (k + 1) < 1 := by
  have hKpos : (0 : ℝ) < (K N : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hK1 : (1 : ℝ) ≤ (K N : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hk1 : (k : ℝ) + 1 ≤ (K N : ℝ) := by exact_mod_cast hk
  have hΔ0 : 0 ≤ step t1 t0 K N := by unfold step; exact div_nonneg (by linarith) hKpos.le
  have hKΔ : (K N : ℝ) * step t1 t0 K N = t0 N - t1 N := by
    unfold step; field_simp
  refine ⟨hΔ0, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · unfold time; positivity
  · unfold time; push_cast; ring
  · have h : time t1 t0 K N (k + 1) = t1 N + ((k : ℝ) + 1) * step t1 t0 K N := by
      unfold time; push_cast; ring
    rw [h]
    nlinarith

end GUEGridStep

/-! #### The deterministic core of one GUE step, and the step bound -/

section GUEStepCore

variable {d}

/-- `318 (n+1)³ ≤ 2^{4n+8}` for `n ≥ 1`. -/
private theorem gueStep_const_le {n : ℕ} (hn : 1 ≤ n) :
    (318 : ℝ) * ((n : ℝ) + 1) ^ 3 ≤ (2 : ℝ) ^ (4 * n + 8) := by
  have h1 : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have h2 : (n + 1) ^ 3 ≤ 2 ^ (3 * n) := by
    calc (n + 1) ^ 3 ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = 2 ^ (3 * n) := by rw [← pow_mul, mul_comm]
  have h3 : 318 * 2 ^ (3 * n) ≤ 2 ^ (4 * n + 8) := by
    calc 318 * 2 ^ (3 * n) ≤ 2 ^ 9 * 2 ^ (3 * n) := by gcongr; norm_num
      _ = 2 ^ (3 * n + 9) := by rw [← pow_add, add_comm]
      _ ≤ 2 ^ (4 * n + 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 318 * (n + 1) ^ 3 ≤ 2 ^ (4 * n + 8) :=
    (Nat.mul_le_mul_left 318 h2).trans h3
  exact_mod_cast h4

/-- Monotonicity of a product of four nonnegative factors. -/
private theorem gueStep_mul4_le {a b c e a' b' c' e' : ℝ} (ha : a ≤ a') (hb : b ≤ b')
    (hc : c ≤ c') (he : e ≤ e') (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (he0 : 0 ≤ e) :
    a * b * c * e ≤ a' * b' * c' * e' := by
  have ha0' : 0 ≤ a' := ha0.trans ha
  have hb0' : 0 ≤ b' := hb0.trans hb
  have hc0' : 0 ≤ c' := hc0.trans hc
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha0'
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0 (mul_nonneg ha0' hb0')
  exact mul_le_mul h2 he he0 (mul_nonneg (mul_nonneg ha0' hb0') hc0')

set_option maxHeartbeats 1000000 in
-- many local abbreviations and integrability side conditions (same budget as the band
-- analogue `Grid.norm_loop_step_drift_le`).
/-- **The deterministic core of one GUE step**, at a fixed Hermitian `M`: the remainder
`2^{4n+8} M^{n+4} (1 + η_{k+1}^{-1})^{n+4} Δ^{3/2}`. -/
private theorem gueStep_det_core (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    (hEb : |E| < 2) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (ht1 : 0 ≤ t1 N) (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hk : k < K N)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    ‖(∫ x, loopObs d N (zt E (time t1 t0 K N (k + 1))) I
          (M + Hflow d N (step t1 t0 K N / (ouMatrixSize d N : ℝ)) x) ∂(gueUnit d))
        - loopObs d N (zt E (time t1 t0 K N k)) I M
        - (step t1 t0 K N : ℂ) • loopDriftGUE d E (time t1 t0 K N k) N I M‖
      ≤ (2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4) *
          (1 + ((zt E (time t1 t0 K N (k + 1))).im)⁻¹) ^ (I.length + 4) *
          step t1 t0 K N ^ ((3 : ℝ) / 2) := by
  obtain ⟨hΔ0, hΔ1, hu0, hu1eq, hu1lt⟩ := gueStep_grid_facts t1 t0 K N k ht1 hst ht0 hk
  set S : ℝ := (ouMatrixSize d N : ℝ) with hSdef
  set n : ℕ := I.length with hndef
  set Δ : ℝ := step t1 t0 K N with hΔdef
  set u0 : ℝ := time t1 t0 K N k with hu0def
  set u1 : ℝ := time t1 t0 K N (k + 1) with hu1def
  set v : ℝ := Δ / S with hvdef
  have hn1 : 1 ≤ n := hn
  have hS1 : 1 ≤ S := gueStep_S_ge_one
  have hS0 : 0 < S := by linarith
  have hmE : 0 < (mE E).im := mE_im_pos hEb
  have hmE1 : ‖mE E‖ = 1 := norm_mE hEb.le
  have hη1 : (zt E u1).im = (1 - u1) * (mE E).im := zt_im E u1
  have hη0 : (zt E u0).im = (1 - u0) * (mE E).im := zt_im E u0
  have hη1pos : 0 < (zt E u1).im := by rw [hη1]; exact mul_pos (by linarith) hmE
  have hη0pos : 0 < (zt E u0).im := by rw [hη0]; exact mul_pos (by linarith) hmE
  have hη01 : (zt E u1).im ≤ (zt E u0).im := by
    rw [hη0, hη1]; exact mul_le_mul_of_nonneg_right (by linarith) hmE.le
  set K0 : ℝ := 1 + ((zt E u1).im)⁻¹ with hK0def
  have hinv1 : 0 ≤ ((zt E u1).im)⁻¹ := inv_nonneg.mpr hη1pos.le
  have hK01 : 1 ≤ K0 := by linarith
  have hinv0 : ((zt E u0).im)⁻¹ ≤ ((zt E u1).im)⁻¹ := inv_anti₀ hη1pos hη01
  have hRHS0 : 0 ≤ (2 : ℝ) ^ (4 * n + 8) * S ^ (n + 4) * K0 ^ (n + 4) * Δ ^ ((3 : ℝ) / 2) := by
    have : 0 ≤ Δ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    positivity
  rcases hΔ0.eq_or_lt with hΔz | hΔpos
  · -- `Δ = 0`: nothing moves.
    have hu10 : u1 = u0 := by rw [hu1eq, ← hΔz, add_zero]
    have hH0 : ∀ x : Ω d, Hflow d N v x = 0 := by
      intro x
      rw [hvdef, ← hΔz, zero_div]
      simp [Hflow]
    have hLHS : (∫ x, loopObs d N (zt E u1) I (M + Hflow d N v x) ∂(gueUnit d))
        - loopObs d N (zt E u0) I M - (Δ : ℂ) • loopDriftGUE d E u0 N I M = 0 := by
      simp only [hH0, add_zero, hu10, integral_const, probReal_univ, one_smul, ← hΔz,
        Complex.ofReal_zero, zero_smul, sub_self]
    rw [hLHS, norm_zero]
    exact hRHS0
  · -- `Δ > 0`
    have hz0 : (zt E u0).im ≠ 0 := hη0pos.ne'
    have hz1 : (zt E u1).im ≠ 0 := hη1pos.ne'
    have habs0 : |(zt E u0).im| = (zt E u0).im := abs_of_pos hη0pos
    have hv0 : 0 ≤ v := div_nonneg hΔ0 hS0.le
    have hvΔ : v ≤ Δ := div_le_self hΔ0 hS1
    set r : ℝ := Real.sqrt Δ with hrdef
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hr1 : r ≤ 1 := Real.sqrt_le_one.mpr hΔ1
    have hr2 : r ^ 2 = Δ := Real.sq_sqrt hΔ0
    have hsv : Real.sqrt v ≤ r := Real.sqrt_le_sqrt hvΔ
    have hsv0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg _
    have hrpow : Δ ^ ((3 : ℝ) / 2) = r ^ 3 := by
      rw [hrdef, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hΔ0]
      norm_num
    have hTF1 := testFun_loopObs_of_im_le hz1 (abs_pos.mpr hz1) le_rfl hwf hn
    have hTF0 := testFun_loopObs_of_im_le hz0 (abs_pos.mpr hz0) le_rfl hwf hn
    obtain ⟨C1, hC1⟩ := hTF1.bdd₀
    obtain ⟨C0, hC0⟩ := hTF0.bdd₀
    have hHerm : ∀ x : Ω d, (M + Hflow d N v x).IsHermitian :=
      fun x => hM.add (Hflow_isHermitian d N v x)
    have hcontShift : Continuous fun x : Ω d => M + Hflow d N v x :=
      continuous_const.add (continuous_Hflow d N v)
    set A : Ω d → ℂ := fun x => loopObs d N (zt E u1) I (M + Hflow d N v x) with hAdef
    set B : Ω d → ℂ := fun x => loopObs d N (zt E u0) I (M + Hflow d N v x) with hBdef
    set Z : Ω d → ℂ := fun x =>
      zMotion (d.L N) (d.W N) (mSigma E) (M + Hflow d N v x) (zt E u0) I with hZdef
    set z00 : ℂ := zMotion (d.L N) (d.W N) (mSigma E) M (zt E u0) I with hz00def
    set gen : ℂ := (1 / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
      ((ouMatrixSize d N : ℝ))⁻¹ • wirtSecond d N (loopObs d N (zt E u0) I) M i j with hgendef
    have hIA : Integrable A (gueUnit d) :=
      gueStep_integrable_cont_bdd (hTF1.contDiff.continuous.comp hcontShift) fun x => hC1 _
    have hIB : Integrable B (gueUnit d) :=
      gueStep_integrable_cont_bdd (hTF0.contDiff.continuous.comp hcontShift) fun x => hC0 _
    have hIZ : Integrable Z (gueUnit d) :=
      gueStep_integrable_cont_bdd
        (gueStep_continuous_zMotion_comp hcontShift hHerm hz0 (mSigma E) I)
        (fun x => norm_zMotion_le (hHerm x) (abs_pos.mpr hz0) le_rfl (mSigma E) I hwf)
    -- target 1 at `u_k`
    have hgen : gen + z00 = loopDriftGUE d E u0 N I M :=
      generator_add_zMotion_gue d hz0 M hM I hwf hn
    -- (R1) the time error, pointwise in the increment
    set ZZ : ℝ := zMotionZLip (d.L N) (d.W N) I.σ.length ((1 - u1) * (mE E).im) (mSigma E)
      * ‖mE E‖ * Δ ^ 2 / 2 with hZZdef
    have hR1pt : ∀ x : Ω d, ‖A x - B x - (Δ : ℂ) * Z x‖ ≤ ZZ := by
      intro x
      have hlt : u0 < u1 := by rw [hu1eq]; linarith
      have h := loop_step_time_err (u := u0) (u' := u1) E hEb hwf (hHerm x) hu0 hlt hu1lt
      have hsub : u1 - u0 = Δ := by rw [hu1eq]; ring
      rw [hsub, Complex.real_smul] at h
      exact h
    have hR1int : Integrable (fun x => A x - B x - (Δ : ℂ) * Z x) (gueUnit d) :=
      (hIA.sub hIB).sub (hIZ.const_mul _)
    have hR1 : ‖∫ x, (A x - B x - (Δ : ℂ) * Z x) ∂(gueUnit d)‖ ≤ ZZ :=
      gueStep_norm_integral_le hR1int hR1pt
    -- (R2) the `M`-Lipschitz bound of the `z`-motion term
    set ZL : ℝ := zMotionLip (d.L N) (d.W N) I.σ.length |(zt E u0).im| (mSigma E) with hZLdef
    have hZL0 : 0 ≤ ZL := by rw [hZLdef]; unfold zMotionLip; positivity
    obtain ⟨hIX1, hEX1⟩ := gueStep_moment1 (d := d) (N := N)
    have hR2pt : ∀ x : Ω d, ‖Z x - z00‖ ≤ ZL * (Real.sqrt v * ‖Xmat d N x‖) := by
      intro x
      have h := norm_zMotion_sub_le_ofM hz0 (hHerm x) hM hwf
      have heq : M + Hflow d N v x - M = Hflow d N v x := by abel
      rw [heq, Hflow_eq_realSmul, norm_smul, Real.norm_of_nonneg hsv0] at h
      exact h
    have hR2 : ‖(∫ x, Z x ∂(gueUnit d)) - z00‖
        ≤ ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d)) := by
      have hsub : (∫ x, Z x ∂(gueUnit d)) - z00 = ∫ x, (Z x - z00) ∂(gueUnit d) := by
        rw [integral_sub hIZ (integrable_const z00)]
        simp
      rw [hsub]
      calc ‖∫ x, (Z x - z00) ∂(gueUnit d)‖ ≤ ∫ x, ‖Z x - z00‖ ∂(gueUnit d) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, ZL * (Real.sqrt v * ‖Xmat d N x‖) ∂(gueUnit d) :=
            integral_mono (hIZ.sub (integrable_const z00)).norm
              ((hIX1.const_mul _).const_mul _) hR2pt
        _ = ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d)) := by
            rw [integral_const_mul, integral_const_mul]
    -- (R3) the space error at `u_k`
    have hR3 := gueStep_space_err hz0 (abs_pos.mpr hz0) le_rfl hwf hn hM hv0
    have hgenv : (v / 2 : ℝ) • ∑ i : d.Idx N, ∑ j : d.Idx N,
          wirtSecond d N (loopObs d N (zt E u0) I) M i j = (Δ : ℂ) * gen := by
      rw [← Complex.real_smul, hgendef]
      simp only [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [hvdef, hSdef]
      field_simp
    rw [hgenv] at hR3
    -- the exact decomposition
    have hident : (∫ x, A x ∂(gueUnit d)) - loopObs d N (zt E u0) I M
          - (Δ : ℂ) • loopDriftGUE d E u0 N I M
        = (∫ x, (A x - B x - (Δ : ℂ) * Z x) ∂(gueUnit d))
          + (Δ : ℂ) * ((∫ x, Z x ∂(gueUnit d)) - z00)
          + ((∫ x, B x ∂(gueUnit d)) - loopObs d N (zt E u0) I M - (Δ : ℂ) * gen) := by
      have hAB : Integrable (fun x => A x - B x) (gueUnit d) := hIA.sub hIB
      have hZc : Integrable (fun x => (Δ : ℂ) * Z x) (gueUnit d) := hIZ.const_mul _
      rw [integral_sub hAB hZc, integral_sub hIA hIB, integral_const_mul, ← hgen, smul_eq_mul]
      ring
    have hΔnorm : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ0]
    have hmain : ‖(∫ x, A x ∂(gueUnit d)) - loopObs d N (zt E u0) I M
          - (Δ : ℂ) • loopDriftGUE d E u0 N I M‖
        ≤ ZZ + Δ * (ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d)))
          + S * (6 * ((n : ℝ) + 1) ^ 3 * |(zt E u0).im|⁻¹ ^ (n + 3))
            * (Real.sqrt v ^ 3 * (52 * S ^ 4)) := by
      rw [hident]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hR1 ?_))
        hR3)
      rw [norm_mul, hΔnorm]
      exact mul_le_mul_of_nonneg_left hR2 hΔ0
    -- the explicit constants
    have hσ : I.σ.length = n := hwf
    have hmax : max ‖mSigma E true‖ ‖mSigma E false‖ = 1 := by
      rw [norm_mSigma_eq, norm_mSigma_eq, max_self, hmE1]
    set P0 : ℝ := K0 ^ (n + 3) with hP0def
    have hP01 : 1 ≤ P0 := one_le_pow₀ hK01
    have hZZ : ZZ = (n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0 * (Δ ^ 2 / 2) := by
      rw [hZZdef]
      unfold zMotionZLip
      rw [hσ, hmax, hmE1, ← hη1, hP0def, hK0def, hSdef]
      unfold ouMatrixSize
      push_cast
      ring
    have hZLb : ZL ≤ (n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0 := by
      rw [hZLdef]
      unfold zMotionLip
      rw [hσ, hmax, habs0]
      have hA1 : (1 + ((zt E u0).im)⁻¹) ^ (n + 1) ≤ K0 ^ (n + 1) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have hA2 : ((zt E u0).im)⁻¹ ^ 2 ≤ K0 ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.mpr hη0pos.le) (by linarith) _
      have hprod : (1 + ((zt E u0).im)⁻¹) ^ (n + 1) * ((zt E u0).im)⁻¹ ^ 2 ≤ P0 := by
        have hsplit : P0 = K0 ^ (n + 1) * K0 ^ 2 := by rw [hP0def, ← pow_add]
        rw [hsplit]
        exact mul_le_mul hA1 hA2 (pow_nonneg (inv_nonneg.mpr hη0pos.le) 2)
          (pow_nonneg (by linarith) _)
      have hcoef : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) * S ^ 2 := by positivity
      calc (n : ℝ) * (1 * (d.W N : ℝ) * (d.L N : ℝ) * ((d.L N : ℝ) * (d.W N : ℝ)
              * ((n : ℝ) + 1) * (1 + ((zt E u0).im)⁻¹) ^ (n + 1))) * ((zt E u0).im)⁻¹ ^ 2
          = (n : ℝ) * ((n : ℝ) + 1) * S ^ 2
              * ((1 + ((zt E u0).im)⁻¹) ^ (n + 1) * ((zt E u0).im)⁻¹ ^ 2) := by
            rw [hSdef]; unfold ouMatrixSize; push_cast; ring
        _ ≤ (n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0 := mul_le_mul_of_nonneg_left hprod hcoef
    have hη0inv : |(zt E u0).im|⁻¹ ^ (n + 3) ≤ P0 := by
      rw [habs0, hP0def]
      exact pow_le_pow_left₀ (inv_nonneg.mpr hη0pos.le) (by linarith) _
    -- numerical assembly; `X := (n+1)³ S⁵ P0 r³`
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hna : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 3 := by
      nlinarith [pow_nonneg hn0 3, sq_nonneg (n : ℝ)]
    have hS25 : S ^ 2 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
    have hS45 : S ^ 4 ≤ S ^ 5 := pow_le_pow_right₀ hS1 (by norm_num)
    have hr43 : r ^ 4 ≤ r ^ 3 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
    have hP00 : 0 ≤ P0 := by linarith
    set X : ℝ := ((n : ℝ) + 1) ^ 3 * S ^ 5 * P0 * r ^ 3 with hXdef
    have hX0 : 0 ≤ X := by positivity
    have hT1 : ZZ ≤ (1 / 2) * X := by
      rw [hZZ, ← hr2]
      have key : (n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0 * r ^ 4 ≤ X :=
        gueStep_mul4_le hna hS25 le_rfl hr43 (by positivity) (by positivity) hP00
          (by positivity)
      have e : (n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0 * ((r ^ 2) ^ 2 / 2)
          = (1 / 2) * ((n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0 * r ^ 4) := by ring
      rw [e]
      linarith
    have hT2 : Δ * (ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d))) ≤ 5 * X := by
      have hI10 : 0 ≤ ∫ x, ‖Xmat d N x‖ ∂(gueUnit d) := integral_nonneg fun x => norm_nonneg _
      have h1 : Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d) ≤ r * (5 * S ^ 2) :=
        mul_le_mul hsv hEX1 hI10 hr0
      have h2 : ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d))
          ≤ ((n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0) * (r * (5 * S ^ 2)) :=
        mul_le_mul hZLb h1 (by positivity) (by positivity)
      have h3 : Δ * (ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d)))
          ≤ Δ * (((n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0) * (r * (5 * S ^ 2))) :=
        mul_le_mul_of_nonneg_left h2 hΔ0
      have key : (n : ℝ) * ((n : ℝ) + 1) * S ^ 4 * P0 * r ^ 3 ≤ X :=
        gueStep_mul4_le hna hS45 le_rfl le_rfl (by positivity) (by positivity) hP00
          (by positivity)
      have e : Δ * (((n : ℝ) * ((n : ℝ) + 1) * S ^ 2 * P0) * (r * (5 * S ^ 2)))
          = 5 * ((n : ℝ) * ((n : ℝ) + 1) * S ^ 4 * P0 * r ^ 3) := by rw [← hr2]; ring
      rw [e] at h3
      linarith
    have hT3 : S * (6 * ((n : ℝ) + 1) ^ 3 * |(zt E u0).im|⁻¹ ^ (n + 3))
          * (Real.sqrt v ^ 3 * (52 * S ^ 4)) ≤ 312 * X := by
      have hsv3 : Real.sqrt v ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hsv0 hsv 3
      have h1 : S * (6 * ((n : ℝ) + 1) ^ 3 * |(zt E u0).im|⁻¹ ^ (n + 3))
          ≤ S * (6 * ((n : ℝ) + 1) ^ 3 * P0) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hη0inv (by positivity)) hS0.le
      have h2 : Real.sqrt v ^ 3 * (52 * S ^ 4) ≤ r ^ 3 * (52 * S ^ 4) :=
        mul_le_mul_of_nonneg_right hsv3 (by positivity)
      have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
      have e : S * (6 * ((n : ℝ) + 1) ^ 3 * P0) * (r ^ 3 * (52 * S ^ 4)) = 312 * X := by
        rw [hXdef]; ring
      rw [e] at h3
      exact h3
    have hfinal : (318 : ℝ) * X ≤ (2 : ℝ) ^ (4 * n + 8) * S ^ (n + 4) * K0 ^ (n + 4) * r ^ 3 := by
      have hc := gueStep_const_le hn1
      have hSn : S ^ 5 ≤ S ^ (n + 4) := pow_le_pow_right₀ hS1 (by omega)
      have hKn : P0 ≤ K0 ^ (n + 4) := by rw [hP0def]; exact pow_le_pow_right₀ hK01 (by omega)
      have e : (318 : ℝ) * X = (318 * ((n : ℝ) + 1) ^ 3) * S ^ 5 * P0 * r ^ 3 := by
        rw [hXdef]; ring
      rw [e]
      exact gueStep_mul4_le hc hSn hKn le_rfl (by positivity) (by positivity) hP00
        (by positivity)
    rw [hrpow]
    calc _ ≤ ZZ + Δ * (ZL * (Real.sqrt v * ∫ x, ‖Xmat d N x‖ ∂(gueUnit d)))
          + S * (6 * ((n : ℝ) + 1) ^ 3 * |(zt E u0).im|⁻¹ ^ (n + 3))
            * (Real.sqrt v ^ 3 * (52 * S ^ 4)) := hmain
      _ ≤ (318 : ℝ) * X := by linarith
      _ ≤ _ := hfinal

end GUEStepCore

section GUEStepMain

/-- **One GUE step**: conditional expectation of the next loop, with an explicit polynomial
remainder `≤ 2^{4n+8} M^{n+4} (1 + η_{k+1}^{-1})^{n+4} Δ^{3/2}`. -/
theorem condExp_loop_drift_gue (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ) (hEb : |E| < 2)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) (ht1 : 0 ≤ t1 N)
    (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hk : k < K N) :
    ∀ᵐ ω ∂(Pgue d),
      ‖(Pgue d)[fun ω' : Grid.Ωg d => loopObs d N (zt E (Grid.time t1 t0 K N (k + 1))) I
            (gueH d t1 t0 K N (k + 1) ω') | Grid.filt d k] ω
          - loopObs d N (zt E (Grid.time t1 t0 K N k)) I (gueH d t1 t0 K N k ω)
          - (Grid.step t1 t0 K N : ℂ) •
              loopDriftGUE d E (Grid.time t1 t0 K N k) N I (gueH d t1 t0 K N k ω)‖
        ≤ (2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4) *
            (1 + ((zt E (Grid.time t1 t0 K N (k + 1))).im)⁻¹) ^ (I.length + 4) *
            Grid.step t1 t0 K N ^ ((3 : ℝ) / 2) := by
  obtain ⟨_, _, _, _, hu1lt⟩ := gueStep_grid_facts t1 t0 K N k ht1 hst ht0 hk
  have hz1 : (zt E (Grid.time t1 t0 K N (k + 1))).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1lt
  filter_upwards [gueStep_condExp_loop_step t1 t0 K N k E hwf hn hz1] with ω hω
  rw [hω]
  exact gueStep_det_core t1 t0 K N k E hEb hwf hn ht1 hst ht0 hk
    (gueH_isHermitian d t1 t0 K N k ω)

end GUEStepMain

end RBM.Gauss.GUEGrid
