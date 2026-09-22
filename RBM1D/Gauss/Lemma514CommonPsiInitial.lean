/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514FpathZero
import RBM1D.Gauss.Lemma514QAssembly

/-!
# A common projected envelope at the first-cell initial time

The finite sum contains the three literal interior tensors of the weighted Q
producer.  This file proves pointwise envelopes and the zero initial moment;
it does not assert a positive-time moment estimate.
-/

#check @RBM.Gauss.Qop_Fpath_zero_at_initial
#check @RBM.Gauss.driftF_zero_at_initial
#check @RBM.DriftDef.Fpath_eq_driftF_of_lt_one
#check @RBM.Sample.Lval_zero_eq_Kval
#check @RBM.FastDecayFlow.commS_zero
#check @RBM.MomentDuhamel.momNorm_zero
#check @RBM.MomentDuhamel.gaussHypOfMoments
#check @RBM.Gauss.first_cell_window_nondegenerate
#check @RBM.Band.scale_pos'

namespace RBM.Gauss

open Finset Filter MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B)
  {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- The three literal interior tensors in the weighted Q producer. -/
noncomputable def commonPsiTerm (H : MomentDuhamel.Hyp X E s t n)
    (N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) : ℝ :=
  ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖
    + ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
        (SumZeroDyn.lkT X E N u ω q.1) b‖
    + ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
        SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖

/-- The three literal projected integrands, summed over the finite loop
argument type and normalized at their own time.  Taking `max 0` of the scale
makes the definition nonnegative even outside the physical window. -/
noncomputable def commonPsiInitial (H : MomentDuhamel.Hyp X E s t n)
    (N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) : ℝ :=
  (max 0 (B.scale E N u)) ^ (n + 2) *
    ∑ b : LoopArg (B.L N) (n + 2), commonPsiTerm X H N u q ω b

theorem commonPsiTerm_nonneg (H : MomentDuhamel.Hyp X E s t n)
    (N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    0 ≤ commonPsiTerm X H N u q ω b := by
  unfold commonPsiTerm
  positivity

theorem commonPsiInitial_nonneg (H : MomentDuhamel.Hyp X E s t n)
    (N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) :
    0 ≤ commonPsiInitial X H N u q ω := by
  unfold commonPsiInitial
  apply mul_nonneg (pow_nonneg (le_max_left 0 _) _)
  exact Finset.sum_nonneg fun b _ => commonPsiTerm_nonneg X H N u q ω b

private theorem commonPsiTerm_le_sum (H : MomentDuhamel.Hyp X E s t n)
    (N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    commonPsiTerm X H N u q ω b ≤
      ∑ c : LoopArg (B.L N) (n + 2), commonPsiTerm X H N u q ω c := by
  exact Finset.single_le_sum (fun c _ => commonPsiTerm_nonneg X H N u q ω c)
    (Finset.mem_univ b)

private theorem lkT_zero_at_initial (hE : |E| < 2)
    (N : ℕ) (ω : Ω) (σ : Fin (n + 2) → Bool) :
    SumZeroDyn.lkT X E N 0 ω σ = 0 := by
  funext b
  change X.Lval E N 0 ω (LoopData.idx (σ, b)) -
    B.Kval E N 0 (LoopData.idx (σ, b)) = 0
  apply sub_eq_zero.mpr
  exact X.Lval_zero_eq_Kval hE.le N ω (LoopData.idx (σ, b))
    (LoopData.idx_wf _) (by simp only [LoopData.idx_length]; omega)

theorem commonPsiInitial_zero_at_initial (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs : ∀ N, s N = 0) (ht : ∀ N, 0 ≤ t N)
    (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) :
    commonPsiInitial X H N 0 q ω = 0 := by
  have hT := lkT_zero_at_initial X hE N ω q.1
  have hF := Qop_Fpath_zero_at_initial X H hE hs ht N ω q.1
  change Qop (B.L N) (0 : ℂ)
    (H.F N 0 (X.H N 0 ω) q.1) = 0 at hF
  have hterm : ∀ b : LoopArg (B.L N) (n + 2),
      commonPsiTerm X H N 0 q ω b = 0 := by
    intro b
    unfold commonPsiTerm
    change ‖Qop (B.L N) (0 : ℂ) (H.F N 0 (X.H N 0 ω) q.1) b‖ +
        ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (0 : ℂ)
          (SumZeroDyn.lkT X E N 0 ω q.1) b‖ +
        ‖Psum (B.L N) (SumZeroDyn.lkT X E N 0 ω q.1) (b 0) *
          SumZeroDyn.varthetaDot (B.L N) 0 b‖ = 0
    rw [hF, hT, FastDecayFlow.commS_zero]
    simp [Psum]
  unfold commonPsiInitial
  simp [hterm]

private theorem le_commonPsiInitial_of_le_term (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) (Y : ℝ)
    (hY : Y ≤ commonPsiTerm X H N u q ω b) :
    Y ≤ (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω := by
  have hA : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
  have hcancel : (B.scale E N u)⁻¹ ^ (n + 2) *
      (max 0 (B.scale E N u)) ^ (n + 2) = 1 := by
    rw [max_eq_right hA.le, ← mul_pow, inv_mul_cancel₀ hA.ne', one_pow]
  calc
    Y ≤ commonPsiTerm X H N u q ω b := hY
    _ ≤ ∑ c : LoopArg (B.L N) (n + 2), commonPsiTerm X H N u q ω c :=
      commonPsiTerm_le_sum X H N u q ω b
    _ = (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω := by
      unfold commonPsiInitial
      rw [← mul_assoc, hcancel, one_mul]

/-- Exact `hEnvF` pointwise row, with zero offset. -/
theorem norm_Qop_F_le_commonPsiInitial (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖ ≤
      (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω := by
  apply le_commonPsiInitial_of_le_term X H hE N hu0 hu1 q ω b
  unfold commonPsiTerm
  have hC : 0 ≤ ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
      (SumZeroDyn.lkT X E N u ω q.1) b‖ := norm_nonneg _
  have hD : 0 ≤ ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
      SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ := norm_nonneg _
  linarith

/-- Exact `hEnvC` pointwise row, with zero offset and no charge guard. -/
theorem norm_commS_le_commonPsiInitial (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
      (SumZeroDyn.lkT X E N u ω q.1) b‖ ≤
      (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω := by
  apply le_commonPsiInitial_of_le_term X H hE N hu0 hu1 q ω b
  unfold commonPsiTerm
  have hF : 0 ≤ ‖Qop (B.L N) (u : ℂ)
      (H.F N u (X.H N u ω) q.1) b‖ := norm_nonneg _
  have hD : 0 ≤ ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
      SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ := norm_nonneg _
  linarith

/-- Exact `hEnvD` pointwise row, with zero offset and no charge guard. -/
theorem norm_dot_le_commonPsiInitial (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
      SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ ≤
      (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω := by
  apply le_commonPsiInitial_of_le_term X H hE N hu0 hu1 q ω b
  unfold commonPsiTerm
  have hF : 0 ≤ ‖Qop (B.L N) (u : ℂ)
      (H.F N u (X.H N u ω) q.1) b‖ := norm_nonneg _
  have hC : 0 ≤ ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
      (SumZeroDyn.lkT X E N u ω q.1) b‖ := norm_nonneg _
  linarith

/-- Exact `hEnvI` row at `s_N=0`, allowing the producer's nonnegative offset. -/
theorem norm_Qop_lkT_initial_le_commonPsiInitial
    (H : MomentDuhamel.Hyp X E s t n) (hE : |E| < 2)
    (hs : ∀ N, s N = 0)
    {ζ : ℕ → ℝ} (hζ : ∀ N, 0 ≤ ζ N)
    (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖Qop (B.L N) ((s N : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N (s N) ω q.1) b‖ ≤
      (B.scale E N (s N))⁻¹ ^ (n + 2) *
        commonPsiInitial X H N (s N) q ω + ζ N := by
  rw [hs N, lkT_zero_at_initial X hE N ω q.1, FastDecayFlow.Qop_zero]
  simp only [Pi.zero_apply, norm_zero]
  have hA : 0 < B.scale E N 0 := B.scale_pos' hE N le_rfl one_pos
  exact add_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hA.le) _)
    (commonPsiInitial_nonneg X H N 0 q ω)) (hζ N)

/-- The common envelope's first-cell initial moment is exactly zero for every
moment order and every charge, with the weighted Q producer's quantifier order. -/
theorem commonPsiInitial_hMψI (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs : ∀ N, s N = 0) (ht : ∀ N, 0 ≤ t N)
    {Phi : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hPhi : ∀ N q, 0 ≤ Phi N q) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (commonPsiInitial X H N (s N) q) ≤
          C * ((N : ℝ) ^ (ε / 2) * Phi N q) := by
  intro ε hε p hp
  refine ⟨1, one_pos, Filter.Eventually.of_forall ?_⟩
  intro N q
  have hzero : commonPsiInitial X H N (s N) q = fun _ => 0 := by
    funext ω
    rw [hs N]
    exact commonPsiInitial_zero_at_initial X H hE hs ht N q ω
  rw [hzero, momNorm_zero B.P (by omega)]
  simpa only [one_mul] using
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hPhi N q))

/-- The initial moment row with a strictly positive deterministic control. -/
theorem commonPsiInitial_hMψI_one (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs : ∀ N, s N = 0) (ht : ∀ N, 0 ≤ t N) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (commonPsiInitial X H N (s N) q) ≤
          C * ((N : ℝ) ^ (ε / 2) * (1 : ℝ)) := by
  exact commonPsiInitial_hMψI X H hE hs ht (fun _ _ => zero_le_one)

/-- The literal `hEnvF` row on a first-cell prefix, with the same
nonnegative offset as the weighted Q producer. -/
theorem commonPsiInitial_hEnvF (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs : ∀ N, s N = 0)
    {v ζ : ℕ → ℝ} (hvt : ∀ N, v N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hζ : ∀ N, 0 ≤ ζ N) :
    ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖ ≤
        (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω + ζ N := by
  intro N u hsu huv q ω b
  have hu0 : 0 ≤ u := by simpa only [hs N] using hsu
  exact (norm_Qop_F_le_commonPsiInitial X H hE N hu0
    (huv.trans_lt ((hvt N).trans_lt (ht1 N))) q ω b).trans
      (le_add_of_nonneg_right (hζ N))

/-- The literal, unguarded `hEnvC` row on a first-cell prefix. -/
theorem commonPsiInitial_hEnvC (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs : ∀ N, s N = 0)
    {v ζ : ℕ → ℝ} (hvt : ∀ N, v N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hζ : ∀ N, 0 ≤ ζ N) :
    ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
        (SumZeroDyn.lkT X E N u ω q.1) b‖ ≤
        (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω + ζ N := by
  intro N u hsu huv q ω b
  have hu0 : 0 ≤ u := by simpa only [hs N] using hsu
  exact (norm_commS_le_commonPsiInitial X H hE N hu0
    (huv.trans_lt ((hvt N).trans_lt (ht1 N))) q ω b).trans
      (le_add_of_nonneg_right (hζ N))

/-- The literal, unguarded `hEnvD` row on a first-cell prefix. -/
theorem commonPsiInitial_hEnvD (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs : ∀ N, s N = 0)
    {v ζ : ℕ → ℝ} (hvt : ∀ N, v N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hζ : ∀ N, 0 ≤ ζ N) :
    ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) (n + 2)),
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
        SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ ≤
        (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiInitial X H N u q ω + ζ N := by
  intro N u hsu huv q ω b
  have hu0 : 0 ≤ u := by simpa only [hs N] using hsu
  exact (norm_dot_le_commonPsiInitial X H hE N hu0
    (huv.trans_lt ((hvt N).trans_lt (ht1 N))) q ω b).trans
      (le_add_of_nonneg_right (hζ N))

/-! ### H-free actual Gaussian/sample core -/

/-- The literal projected terms, with the drift pinned directly to the actual
sample flow rather than to an as-yet-unconstructed `MomentDuhamel.Hyp`. -/
noncomputable def commonPsiDriftTerm (N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) : ℝ :=
  ‖Qop (B.L N) (u : ℂ)
      (DriftDef.driftF B E N u (X.H N u ω) q.1) b‖
    + ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
        (SumZeroDyn.lkT X E N u ω q.1) b‖
    + ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
        SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖

/-- A concrete common envelope on the actual sample flow.  This definition
requires no stochastic moment inequality and no `Hyp` value. -/
noncomputable def commonPsiDrift (N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω) : ℝ :=
  (max 0 (B.scale E N u)) ^ (n + 2) *
    ∑ b : LoopArg (B.L N) (n + 2), commonPsiDriftTerm (E := E) X N u q ω b

theorem commonPsiDriftTerm_nonneg (N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    0 ≤ commonPsiDriftTerm (E := E) X N u q ω b := by
  unfold commonPsiDriftTerm
  positivity

theorem commonPsiDrift_nonneg (N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω) :
    0 ≤ commonPsiDrift (E := E) X N u q ω := by
  unfold commonPsiDrift
  apply mul_nonneg (pow_nonneg (le_max_left 0 _) _)
  exact Finset.sum_nonneg fun b _ => commonPsiDriftTerm_nonneg (E := E) X N u q ω b

private theorem commonPsiDriftTerm_le_sum (N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    commonPsiDriftTerm (E := E) X N u q ω b ≤
      ∑ c : LoopArg (B.L N) (n + 2), commonPsiDriftTerm (E := E) X N u q ω c := by
  exact Finset.single_le_sum (fun c _ => commonPsiDriftTerm_nonneg (E := E) X N u q ω c)
    (Finset.mem_univ b)

/-- The H-free common envelope is exactly zero at the first-cell left
endpoint for every actual sample, charge, and dimension. -/
theorem commonPsiDrift_zero_at_initial (hE : |E| < 2)
    (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) :
    commonPsiDrift (E := E) X N 0 q ω = 0 := by
  have hT := lkT_zero_at_initial X hE N ω q.1
  have hF : DriftDef.driftF B E N 0 (X.H N 0 ω) q.1 = 0 := by
    funext b
    exact driftF_zero_at_initial X hE N n ω q.1 b
  have hterm : ∀ b : LoopArg (B.L N) (n + 2),
      commonPsiDriftTerm (E := E) X N 0 q ω b = 0 := by
    intro b
    unfold commonPsiDriftTerm
    change ‖Qop (B.L N) (0 : ℂ)
        (DriftDef.driftF B E N 0 (X.H N 0 ω) q.1) b‖ +
        ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (0 : ℂ)
          (SumZeroDyn.lkT X E N 0 ω q.1) b‖ +
        ‖Psum (B.L N) (SumZeroDyn.lkT X E N 0 ω q.1) (b 0) *
          SumZeroDyn.varthetaDot (B.L N) 0 b‖ = 0
    rw [hF, FastDecayFlow.Qop_zero, hT, FastDecayFlow.commS_zero]
    simp [Psum]
  unfold commonPsiDrift
  simp [hterm]

private theorem le_commonPsiDrift_of_le_term (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) (Y : ℝ)
    (hY : Y ≤ commonPsiDriftTerm (E := E) X N u q ω b) :
    Y ≤ (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiDrift (E := E) X N u q ω := by
  have hA : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
  have hcancel : (B.scale E N u)⁻¹ ^ (n + 2) *
      (max 0 (B.scale E N u)) ^ (n + 2) = 1 := by
    rw [max_eq_right hA.le, ← mul_pow, inv_mul_cancel₀ hA.ne', one_pow]
  calc
    Y ≤ commonPsiDriftTerm (E := E) X N u q ω b := hY
    _ ≤ ∑ c : LoopArg (B.L N) (n + 2), commonPsiDriftTerm (E := E) X N u q ω c :=
      commonPsiDriftTerm_le_sum (E := E) X N u q ω b
    _ = (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiDrift (E := E) X N u q ω := by
      unfold commonPsiDrift
      rw [← mul_assoc, hcancel, one_mul]

theorem norm_Qop_driftF_le_commonPsiDrift (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖Qop (B.L N) (u : ℂ)
      (DriftDef.driftF B E N u (X.H N u ω) q.1) b‖ ≤
      (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiDrift (E := E) X N u q ω := by
  apply le_commonPsiDrift_of_le_term X hE N hu0 hu1 q ω b
  unfold commonPsiDriftTerm
  have hC : 0 ≤ ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
      (SumZeroDyn.lkT X E N u ω q.1) b‖ := norm_nonneg _
  have hD : 0 ≤ ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
      SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ := norm_nonneg _
  linarith

theorem norm_commS_le_commonPsiDrift (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
      (SumZeroDyn.lkT X E N u ω q.1) b‖ ≤
      (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiDrift (E := E) X N u q ω := by
  apply le_commonPsiDrift_of_le_term X hE N hu0 hu1 q ω b
  unfold commonPsiDriftTerm
  have hF : 0 ≤ ‖Qop (B.L N) (u : ℂ)
      (DriftDef.driftF B E N u (X.H N u ω) q.1) b‖ := norm_nonneg _
  have hD : 0 ≤ ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
      SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ := norm_nonneg _
  linarith

theorem norm_dot_le_commonPsiDrift (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0) *
      SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖ ≤
      (B.scale E N u)⁻¹ ^ (n + 2) * commonPsiDrift (E := E) X N u q ω := by
  apply le_commonPsiDrift_of_le_term X hE N hu0 hu1 q ω b
  unfold commonPsiDriftTerm
  have hF : 0 ≤ ‖Qop (B.L N) (u : ℂ)
      (DriftDef.driftF B E N u (X.H N u ω) q.1) b‖ := norm_nonneg _
  have hC : 0 ≤ ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) (u : ℂ)
      (SumZeroDyn.lkT X E N u ω q.1) b‖ := norm_nonneg _
  linarith

/-- The unconditional actual-sample initial datum row. -/
theorem norm_Qop_lkT_initial_le_commonPsiDrift
    (hE : |E| < 2) {ζ : ℕ → ℝ} (hζ : ∀ N, 0 ≤ ζ N)
    (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (b : LoopArg (B.L N) (n + 2)) :
    ‖Qop (B.L N) (0 : ℂ) (SumZeroDyn.lkT X E N 0 ω q.1) b‖ ≤
      (B.scale E N 0)⁻¹ ^ (n + 2) * commonPsiDrift (E := E) X N 0 q ω + ζ N := by
  rw [lkT_zero_at_initial X hE N ω q.1, FastDecayFlow.Qop_zero]
  simp only [Pi.zero_apply, norm_zero]
  have hA : 0 < B.scale E N 0 := B.scale_pos' hE N le_rfl one_pos
  exact add_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hA.le) _)
    (commonPsiDrift_nonneg (E := E) X N 0 q ω)) (hζ N)

/-- All initial moments of the unconditional actual-sample common envelope
vanish, for every charge and every positive deterministic control. -/
theorem commonPsiDrift_hMψI (hE : |E| < 2)
    {Phi : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hPhi : ∀ N q, 0 < Phi N q) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (commonPsiDrift (E := E) X N 0 q) ≤
          C * ((N : ℝ) ^ (ε / 2) * Phi N q) := by
  intro ε hε p hp
  refine ⟨1, one_pos, Filter.Eventually.of_forall ?_⟩
  intro N q
  have hzero : commonPsiDrift (E := E) X N 0 q = fun _ => 0 := by
    funext ω
    exact commonPsiDrift_zero_at_initial (E := E) X hE N q ω
  rw [hzero, momNorm_zero B.P (by omega)]
  simpa only [one_mul] using
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hPhi N q).le)

/-- On the physical window, the conditional `Hyp.Fpath` envelope agrees
pointwise with the unconditional actual-drift envelope. -/
theorem commonPsiInitial_eq_commonPsiDrift
    (H : MomentDuhamel.Hyp X E s t n) (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hsu : s N ≤ u) (hut : u ≤ t N)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω) :
    commonPsiInitial X H N u q ω = commonPsiDrift (E := E) X N u q ω := by
  have hF : H.F N u (X.H N u ω) q.1 =
      DriftDef.driftF B E N u (X.H N u ω) q.1 := by
    funext b
    exact DriftDef.Fpath_eq_driftF_of_lt_one H hE hu0 hu1 hsu hut ω q.1 b
  unfold commonPsiInitial commonPsiDrift commonPsiTerm commonPsiDriftTerm
  simp only [hF]

end RBM.Gauss

namespace RBM.Gauss

open Filter MomentDuhamel

/-- The Gaussian `Hyp` boundary is explicit: both moment inequalities are
inputs, exactly as in `gaussHypOfMoments`.  Conditional on them, the common
envelope has the full initial-moment quantifier order. -/
theorem commonPsiInitial_gauss_hMψI (d : Dims)
    {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2) (hs : ∀ N, s N = 0)
    (ht : ∀ N, 0 ≤ t N) (ht1 : ∀ N, t N < 1)
    (cMD : ℕ → ℝ) (hcMD : ∀ p, 0 ≤ cMD p)
    (hmd : MomentDuhamel.MomentIneq (sample d) E s t n cMD)
    (hmdQ : MomentDuhamel.MomentIneqQ (sample d) E s t n cMD)
    {Phi : ∀ N, LoopData ((band d).L N) (n + 2) → ℝ}
    (hPhi : ∀ N q, 0 ≤ Phi N q) :
    let H := MomentDuhamel.gaussHypOfMoments d E s t n hE
      (fun N => by rw [hs N]) ht1 cMD hcMD hmd hmdQ
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ q : LoopData ((band d).L N) (n + 2),
        momNorm (band d).P (2 * p)
          (commonPsiInitial (sample d) H N (s N) q) ≤
          C * ((N : ℝ) ^ (ε / 2) * Phi N q) := by
  exact commonPsiInitial_hMψI (sample d)
    (MomentDuhamel.gaussHypOfMoments d E s t n hE
      (fun N => by rw [hs N]) ht1 cMD hcMD hmd hmdQ)
    hE hs ht hPhi

/-- All first-cell initial moments for the actual Gaussian sample, without
constructing or assuming a `MomentDuhamel.Hyp`.  The control is `1>0`. -/
theorem commonPsiDrift_gauss_hMψI_one (d : Dims) {E : ℝ} {n : ℕ}
    (hE : |E| < 2) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop, ∀ q : LoopData ((band d).L N) (n + 2),
        momNorm (band d).P (2 * p)
          (commonPsiDrift (E := E) (sample d) N 0 q) ≤
          C * ((N : ℝ) ^ (ε / 2) * (1 : ℝ)) := by
  exact commonPsiDrift_hMψI (sample d) hE (fun _ _ => one_pos)

/-- A noncollapsed growing Gaussian first cell, with positive normalization,
strictly positive control, and an inhabited actual-sample zero identity.
No `MomentDuhamel.Hyp` is assumed. -/
theorem commonPsiDrift_positive_first_cell_exampleGrow :
    ∀ᶠ N : ℕ in atTop,
      let d := Dims.exampleGrow
      let s : ℕ → ℝ := fun k => gridT ((band d).W k : ℝ) 1 (1 / 2 : ℝ) 0
      let t : ℕ → ℝ := fun k => gridT ((band d).W k : ℝ) 1 (1 / 2 : ℝ) 1
      s N < t N ∧ 0 < (band d).scale 0 N 0 ∧ 0 < (1 : ℝ) ∧
        (∃ (q : LoopData ((band d).L N) 2) (ω : Ω d),
          commonPsiDrift (E := 0) (n := 0) (sample d) N 0 q ω = 0) ∧
        ∀ (n : ℕ) (q : LoopData ((band d).L N) (n + 2)) (ω : Ω d),
          commonPsiDrift (E := 0) (sample d) N 0 q ω = 0 := by
  filter_upwards [first_cell_window_nondegenerate Dims.exampleGrow one_pos] with N hwin
  dsimp
  refine ⟨hwin, ?_, one_pos, ?_, ?_⟩
  · exact (band Dims.exampleGrow).scale_pos' (by norm_num : |(0 : ℝ)| < 2)
      N le_rfl one_pos
  · refine ⟨(fun _ => false, fun _ => 0), (fun _ => 0), ?_⟩
    exact commonPsiDrift_zero_at_initial (sample Dims.exampleGrow)
      (by norm_num : |(0 : ℝ)| < 2) N _ _
  · intro n q ω
    exact commonPsiDrift_zero_at_initial (sample Dims.exampleGrow)
      (by norm_num : |(0 : ℝ)| < 2) N q ω

end RBM.Gauss

#print axioms RBM.Gauss.commonPsiInitial_nonneg
#print axioms RBM.Gauss.commonPsiInitial_zero_at_initial
#print axioms RBM.Gauss.norm_Qop_F_le_commonPsiInitial
#print axioms RBM.Gauss.norm_commS_le_commonPsiInitial
#print axioms RBM.Gauss.norm_dot_le_commonPsiInitial
#print axioms RBM.Gauss.norm_Qop_lkT_initial_le_commonPsiInitial
#print axioms RBM.Gauss.commonPsiInitial_hMψI
#print axioms RBM.Gauss.commonPsiInitial_hMψI_one
#print axioms RBM.Gauss.commonPsiInitial_hEnvF
#print axioms RBM.Gauss.commonPsiInitial_hEnvC
#print axioms RBM.Gauss.commonPsiInitial_hEnvD
#print axioms RBM.Gauss.commonPsiInitial_gauss_hMψI
#print axioms RBM.Gauss.commonPsiDrift_nonneg
#print axioms RBM.Gauss.commonPsiDrift_zero_at_initial
#print axioms RBM.Gauss.norm_Qop_driftF_le_commonPsiDrift
#print axioms RBM.Gauss.norm_commS_le_commonPsiDrift
#print axioms RBM.Gauss.norm_dot_le_commonPsiDrift
#print axioms RBM.Gauss.norm_Qop_lkT_initial_le_commonPsiDrift
#print axioms RBM.Gauss.commonPsiDrift_hMψI
#print axioms RBM.Gauss.commonPsiInitial_eq_commonPsiDrift
#print axioms RBM.Gauss.commonPsiDrift_gauss_hMψI_one
#print axioms RBM.Gauss.commonPsiDrift_positive_first_cell_exampleGrow
