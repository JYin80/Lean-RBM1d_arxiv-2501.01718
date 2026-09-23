/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothWeightActual
import RBM1D.Gauss.APrimeDriftTimeFamily
import RBM1D.Gauss.APrimeNormalizedTestFun
import RBM1D.Gauss.APrimeBadSplit
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore

/-! The actual smooth-prefix covariance cross term. -/

namespace RBM.APrimeCrossJointSplit

open MeasureTheory Real RBM.Gauss RBM.APrimeDuhamelModel
open scoped Matrix.Norms.L2Operator



noncomputable def prefixGradient (d : Gauss.Dims) (E D δ : ℝ)
    (s mesh : ℕ → ℝ) (N k m : ℕ) (ω : Gauss.Ω d) : ℝ :=
  √(Gauss.quadVar d N
    (fun M => ((APrimeSmoothWeightActual.prefixMatrix d E D s mesh N k m M : ℝ) : ℂ))
    (Gauss.Xmat d N ω)) / APrimeSmoothWeightActual.threshold δ N

noncomputable def jointRate (d : Gauss.Dims) (E D δ : ℝ)
    (s mesh : ℕ → ℝ) (N k m : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ)
    (ω : Gauss.Ω d) : ℝ :=
  (transition d E D δ s mesh N k m).indicator
    (fun ω => prefixGradient d E D δ s mesh N k m ω *
      √(APrimeDriftTimeFamily.qvAt d E D N σ a (s N) v r ω)) ω

private theorem abs_cutChiD_le_indicator (x : ℝ) :
    |Cutoff.cutChiD x| ≤ (15 / 8 : ℝ) * (if 1 < x ∧ x < 2 then 1 else 0) := by
  split_ifs with h
  · simpa using Cutoff.abs_cutChiD_le x
  · have hx : x ≤ 1 ∨ 2 ≤ x := by
      by_cases h1 : 1 < x
      · exact Or.inr (le_of_not_gt (by simpa [h1] using h))
      · exact Or.inl (le_of_not_gt h1)
    rcases hx with hx | hx
    · simp [Cutoff.cutChiD_eq_zero_left hx]
    · simp [Cutoff.cutChiD_eq_zero_right hx]

private theorem cutWeight_fderiv (d : Gauss.Dims) (N : ℕ)
    (g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ)
    (hg : ContDiff ℝ 1 g) (Θ : ℝ) (hΘ : 0 < Θ) (p : ℕ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    fderiv ℝ (fun X => Cutoff.cutChi (g X / Θ) ^ (2 * p)) M =
      (((2 * p : ℕ) : ℝ) * Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) *
        Cutoff.cutChiD (g M / Θ) / Θ) • fderiv ℝ g M := by
  let c : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ :=
    fun X => Cutoff.cutChi (g X / Θ)
  have hdiv : HasFDerivAt (fun X => g X / Θ)
      (Θ⁻¹ • fderiv ℝ g M) M := by
    have hd := ((hg.differentiable (by norm_num) M).hasFDerivAt).const_mul (Θ⁻¹ : ℝ)
    simpa [div_eq_inv_mul] using hd
  have hc : HasFDerivAt c
      (Cutoff.cutChiD (g M / Θ) • (Θ⁻¹ • fderiv ℝ g M)) M := by
    simpa only [c, Function.comp_def] using
      (Cutoff.hasDerivAt_cutChi (g M / Θ)).comp_hasFDerivAt M hdiv
  have hpw := (hc.pow (2 * p)).fderiv
  change fderiv ℝ (fun X => c X ^ (2 * p)) M = _
  rw [hpw]
  simp only [nsmul_eq_mul, smul_smul]
  congr 1
  simp only [c]
  ring

private theorem sqrt_quadVar_cutWeight_le (d : Gauss.Dims) (N : ℕ)
    (g : Matrix (d.Idx N) (d.Idx N) ℂ → ℝ)
    (hg : ContDiff ℝ 1 g) (Θ : ℝ) (hΘ : 0 < Θ) (p : ℕ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    √(Gauss.quadVar d N
      (fun X => ((Cutoff.cutChi (g X / Θ) ^ (2 * p) : ℝ) : ℂ)) M) ≤
      ((2 * p : ℕ) : ℝ) * Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) *
        (15 / 8 : ℝ) *
        (if 1 < g M / Θ ∧ g M / Θ < 2 then 1 else 0) *
        (√(Gauss.quadVar d N (fun X => ((g X : ℝ) : ℂ)) M) / Θ) := by
  let L : ℝ := ((2 * p : ℕ) : ℝ) * Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) *
        (15 / 8 : ℝ) *
        (if 1 < g M / Θ ∧ g M / Θ < 2 then 1 else 0) / Θ
  have hL : 0 ≤ L := by
    dsimp [L]
    have hc : 0 ≤ Cutoff.cutChi (g M / Θ) := Cutoff.cutChi_nonneg _
    split_ifs <;> simp_all <;> positivity
  have hdiff : DifferentiableAt ℝ (fun X => Cutoff.cutChi (g X / Θ) ^ (2 * p)) M :=
    ((Cutoff.contDiff_cutChi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp
      (hg.div_const Θ)).pow (2 * p) |>.differentiable (by norm_num) M
  have hpoint : ∀ q ∈ Gauss.usedCoord d N,
      ‖Gauss.coordD1 d N
        (fun X => ((Cutoff.cutChi (g X / Θ) ^ (2 * p) : ℝ) : ℂ)) M q‖ ≤
        L * ‖Gauss.coordD1 d N (fun X => ((g X : ℝ) : ℂ)) M q‖ := by
    intro q _
    rw [Gauss.norm_coordD1_ofReal hdiff q,
      Gauss.norm_coordD1_ofReal (hg.differentiable (by norm_num) M) q,
      cutWeight_fderiv d N g hg Θ hΘ p M,
      ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul]
    have hfac : |((2 * p : ℕ) : ℝ) * Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) *
        Cutoff.cutChiD (g M / Θ) / Θ| ≤ L := by
      rw [abs_div, abs_of_pos hΘ]
      have hnonneg : 0 ≤ ((2 * p : ℕ) : ℝ) *
          Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) := by
        exact mul_nonneg (by positivity) (pow_nonneg (Cutoff.cutChi_nonneg _) _)
      rw [abs_mul, abs_of_nonneg hnonneg]
      dsimp [L]
      have hh := mul_le_mul_of_nonneg_left
        (abs_cutChiD_le_indicator (g M / Θ)) hnonneg
      have hh' : ((2 * p : ℕ) : ℝ) * Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) *
          |Cutoff.cutChiD (g M / Θ)| ≤
          ((2 * p : ℕ) : ℝ) * Cutoff.cutChi (g M / Θ) ^ (2 * p - 1) *
            (15 / 8 : ℝ) * (if 1 < g M / Θ ∧ g M / Θ < 2 then 1 else 0) := by
        convert hh using 1 <;> ring
      exact div_le_div_of_nonneg_right hh' hΘ.le
    exact mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
  have h := Gauss.sqrt_quadVar_le_of_apply_le hL hpoint
  convert h using 1 <;> dsimp [L] <;> ring

private theorem contDiff_coordAt (d : Gauss.Dims) (E D : ℝ) (N : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) {s v r : ℝ}
    (hE : |E| < 2) (hs0 : 0 ≤ s) (hv1 : v < 1)
    (hr : r ∈ Set.Icc s v) :
    ContDiff ℝ 1 (APrimeDriftTimeFamily.coordAt d E D N σ a s v r) := by
  obtain ⟨cK, _, hK, _⟩ := Gauss.exists_bdd_Kval_Kprim
    (d := d) E N hE.le hs0 hv1 σ
  have hη := Gauss.window_eta_pos hE hv1
  have hz := Gauss.window_im_ne_zero hE hv1 r hr
  have hzη := Gauss.window_le_abs_im hE hv1 r hr
  have hraw := Gauss.bddC2C_ukerObsT (d := d) (N := N)
    (σ := List.ofFn σ) (m := 2) hη hz hzη (List.length_ofFn)
    (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
    (fun u b => (Gauss.band d).Kval E N u (LoopData.idx (σ, b))) a
    (hK r hr)
  unfold APrimeDriftTimeFamily.coordAt
  exact (hraw.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).div_const _

private theorem cross_cauchy_twoMatrices (d : Gauss.Dims) (N : ℕ)
    (F G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (M M' : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
      (‖Gauss.coordD1 d N F M q‖ * ‖Gauss.coordD1 d N G M' q‖) ≤
      √(Gauss.quadVar d N F M) * √(Gauss.quadVar d N G M') := by
  let A : d.Idx N × d.Idx N × Bool → ℝ :=
    fun q => √((Gauss.gvar d (Gauss.crd d N q) : ℝ)) * ‖Gauss.coordD1 d N F M q‖
  let B : d.Idx N × d.Idx N × Bool → ℝ :=
    fun q => √((Gauss.gvar d (Gauss.crd d N q) : ℝ)) * ‖Gauss.coordD1 d N G M' q‖
  have hsq : ∀ q : d.Idx N × d.Idx N × Bool,
      √((Gauss.gvar d (Gauss.crd d N q) : ℝ)) ^ 2 =
        (Gauss.gvar d (Gauss.crd d N q) : ℝ) :=
    fun q => Real.sq_sqrt (Gauss.gvar d (Gauss.crd d N q)).2
  have hA : ∑ q ∈ Gauss.usedCoord d N, A q ^ 2 = Gauss.quadVar d N F M := by
    unfold Gauss.quadVar
    apply Finset.sum_congr rfl
    intro q _
    dsimp [A]
    rw [mul_pow, hsq q]
  have hB : ∑ q ∈ Gauss.usedCoord d N, B q ^ 2 = Gauss.quadVar d N G M' := by
    unfold Gauss.quadVar
    apply Finset.sum_congr rfl
    intro q _
    dsimp [B]
    rw [mul_pow, hsq q]
  have hprod : ∑ q ∈ Gauss.usedCoord d N,
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (‖Gauss.coordD1 d N F M q‖ * ‖Gauss.coordD1 d N G M' q‖) =
      ∑ q ∈ Gauss.usedCoord d N, A q * B q := by
    apply Finset.sum_congr rfl
    intro q _
    dsimp [A, B]
    have hh : √((Gauss.gvar d (Gauss.crd d N q) : ℝ)) *
        √((Gauss.gvar d (Gauss.crd d N q) : ℝ)) =
        (Gauss.gvar d (Gauss.crd d N q) : ℝ) :=
      Real.mul_self_sqrt (Gauss.gvar d (Gauss.crd d N q)).2
    calc
      (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
          (‖Gauss.coordD1 d N F M q‖ * ‖Gauss.coordD1 d N G M' q‖) =
          (√((Gauss.gvar d (Gauss.crd d N q) : ℝ)) *
            √((Gauss.gvar d (Gauss.crd d N q) : ℝ))) *
          (‖Gauss.coordD1 d N F M q‖ * ‖Gauss.coordD1 d N G M' q‖) := by
            rw [hh]
      _ = _ := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Gauss.usedCoord d N) A B
  rw [hA, hB] at hcs
  have hnonneg : 0 ≤ ∑ q ∈ Gauss.usedCoord d N, A q * B q := by
    apply Finset.sum_nonneg
    intro q _
    dsimp [A, B]
    positivity
  rw [hprod, ← Real.sqrt_mul (Gauss.quadVar_nonneg F M)]
  calc
    ∑ q ∈ Gauss.usedCoord d N, A q * B q =
        √((∑ q ∈ Gauss.usedCoord d N, A q * B q) ^ 2) :=
      (Real.sqrt_sq hnonneg).symm
    _ ≤ √(Gauss.quadVar d N F M * Gauss.quadVar d N G M') :=
      Real.sqrt_le_sqrt hcs

/- S5-joint for the active actual smooth prefix and the uncut evolved coordinate. -/
set_option maxHeartbeats 1000000 in
theorem crossAbsSum_active_le (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ)
    (hE : |E| < 2) (hs : s N < 1) (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, CutHypTheta.cutNetPt s mesh N j < 1)
    (hs0 : 0 ≤ s N) (hv1 : v < 1) (hr : r ∈ Set.Icc (s N) v)
    (hk : k ≤ CutHypTheta.cutNetTop s t mesh N) (hN₀ : N₀ ≤ N)
    (hp : 1 ≤ p) (ω : Gauss.Ω d) :
    APrimeBadSplit.crossAbsSum d N
      (APrimeDriftTimeFamily.momentAt d E D N p σ a (s N) v)
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m) r ω ≤
      ((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ) *
        (APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
          ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
            (Gauss.Hflow d N r ω)‖) ^ (2 * p - 1) *
        jointRate d E D δ s mesh N k m σ a v r ω := by
  let g := APrimeSmoothWeightActual.prefixMatrix d E D s mesh N k m
  let M := Gauss.Xmat d N ω
  let F := APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
  let c := APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω
  have hg : ContDiff ℝ 1 g :=
    APrimeSmoothWeightActual.contDiff_prefixMatrix d hE hs hN hm hu
  have hF : ContDiff ℝ 1 F := contDiff_coordAt d E D N σ a hE hs0 hv1 hr
  have hΘ : 0 < APrimeSmoothWeightActual.threshold δ N :=
    APrimeSmoothWeightActual.threshold_pos hN
  have hmoment : APrimeDriftTimeFamily.momentAt d E D N p σ a (s N) v r =
      fun X => ((‖F X‖ ^ (2 * p) : ℝ) : ℂ) := rfl
  have hW : APrimeSmoothWeightActual.weightMatrix d E D δ s t mesh
      N₀ p N k m = fun X => Cutoff.cutChi (g X /
        APrimeSmoothWeightActual.threshold δ N) ^ (2 * p) := by
    funext X
    simp [APrimeSmoothWeightActual.weightMatrix, APrimeSmoothWeightActual.cutoffMatrix,
      g, hk, hN₀]
  have hterm : APrimeBadSplit.crossAbsSum d N
      (APrimeDriftTimeFamily.momentAt d E D N p σ a (s N) v)
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m) r ω =
      ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
        (‖Gauss.coordD1 d N
            (fun X => ((Cutoff.cutChi (g X / APrimeSmoothWeightActual.threshold δ N) ^
              (2 * p) : ℝ) : ℂ)) M q‖ *
         ‖Gauss.coordD1 d N (fun X => ((‖F X‖ ^ (2 * p) : ℝ) : ℂ))
            (Gauss.Hflow d N r ω) q‖) := by
    unfold APrimeBadSplit.crossAbsSum
    apply Finset.sum_congr rfl
    intro q _
    rw [show APrimeSmoothWeightActual.weightD d E D δ s t mesh
        N₀ p N k m q ω = fderiv ℝ (fun X => Cutoff.cutChi
          (g X / APrimeSmoothWeightActual.threshold δ N) ^ (2 * p)) M
          (Gauss.Bmat d N q.1 q.2.1 q.2.2) by rw [APrimeSmoothWeightActual.weightD, hW]]
    have hdiff : DifferentiableAt ℝ
        (fun X => Cutoff.cutChi (g X / APrimeSmoothWeightActual.threshold δ N) ^
          (2 * p)) M :=
      (((Cutoff.contDiff_cutChi.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp
        (hg.div_const _)).pow (2 * p)).differentiable (by norm_num) M
    rw [Gauss.norm_coordD1_ofReal hdiff q]
    rfl
  rw [hterm]
  have hcs := cross_cauchy_twoMatrices d N
    (fun X => ((Cutoff.cutChi (g X / APrimeSmoothWeightActual.threshold δ N) ^
      (2 * p) : ℝ) : ℂ))
    (fun X => ((‖F X‖ ^ (2 * p) : ℝ) : ℂ))
    M (Gauss.Hflow d N r ω)
  have hwgrad := sqrt_quadVar_cutWeight_le d N g hg
    (APrimeSmoothWeightActual.threshold δ N) hΘ p M
  have hmomentgrad := Gauss.sqrt_quadVar_norm_pow_le hF hp (Gauss.Hflow d N r ω)
  have hupper0 : 0 ≤ ((2 * p : ℕ) : ℝ) * Cutoff.cutChi
      (g M / APrimeSmoothWeightActual.threshold δ N) ^ (2 * p - 1) *
        (15 / 8 : ℝ) *
        (if 1 < g M / APrimeSmoothWeightActual.threshold δ N ∧
            g M / APrimeSmoothWeightActual.threshold δ N < 2 then 1 else 0) *
        (√(Gauss.quadVar d N (fun X => ((g X : ℝ) : ℂ)) M) /
          APrimeSmoothWeightActual.threshold δ N) := by
    have hc0 := Cutoff.cutChi_nonneg (g M / APrimeSmoothWeightActual.threshold δ N)
    split_ifs <;> positivity
  have hboth := mul_le_mul hwgrad hmomentgrad
    (Real.sqrt_nonneg _) hupper0
  have hgoal := hcs.trans hboth
  -- The remaining step is rearrangement and the exact T292 QV identification.
  by_cases hband : 1 < g M / APrimeSmoothWeightActual.threshold δ N ∧
      g M / APrimeSmoothWeightActual.threshold δ N < 2
  · have hω : ω ∈ transition d E D δ s mesh N k m := hband
    refine hgoal.trans ?_
    simp only [jointRate, Set.indicator_of_mem hω,
      prefixGradient, APrimeDriftTimeFamily.qvAt,
      APrimeSmoothWeightActual.cutoff, APrimeSmoothWeightActual.prefixSample,
      if_pos hband, mul_pow, g, F, M, c,
      mul_assoc, mul_comm, mul_left_comm]
    exact le_of_eq (by ring)
  · have hω : ω ∉ transition d E D δ s mesh N k m := hband
    simpa only [jointRate, Set.indicator_of_notMem hω,
      if_neg hband, mul_zero, zero_mul] using hgoal

/-- The exponent-zero actual weight has zero coordinate derivative. -/
theorem weightD_zero_p0 (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m : ℕ)
    (q : d.Idx N × d.Idx N × Bool) (ω : Gauss.Ω d) :
    APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ 0 N k m q ω = 0 := by
  unfold APrimeSmoothWeightActual.weightD APrimeSmoothWeightActual.weightMatrix
  split_ifs <;> simp

/-- The inactive actual weight has zero coordinate derivative. -/
theorem weightD_zero_inactive (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m p : ℕ)
    (h : ¬(k ≤ CutHypTheta.cutNetTop s t mesh N ∧ N₀ ≤ N))
    (q : d.Idx N × d.Idx N × Bool) (ω : Gauss.Ω d) :
    APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m q ω = 0 := by
  unfold APrimeSmoothWeightActual.weightD APrimeSmoothWeightActual.weightMatrix
  simp [h]

/-- A zero prefix has constant weight, including its active branch. -/
theorem weightD_zero_k0 (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N m p : ℕ)
    (hm : 1 ≤ m) (q : d.Idx N × d.Idx N × Bool) (ω : Gauss.Ω d) :
    APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N 0 m q ω = 0 := by
  have hprefix : APrimeSmoothWeightActual.prefixMatrix d E D s mesh N 0 m =
      fun _ => (0 : ℝ) := by
    funext X
    simp only [APrimeSmoothWeightActual.prefixMatrix, Step2Bootstrap.softMax,
      Finset.range_zero, Finset.sum_empty]
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    exact Real.zero_rpow (ne_of_gt (by positivity : (0 : ℝ) < 1 / (2 * (m : ℝ))))
  have hconst : APrimeSmoothWeightActual.weightMatrix d E D δ s t mesh
      N₀ p N 0 m = fun _ => (1 : ℝ) := by
    funext X
    unfold APrimeSmoothWeightActual.weightMatrix APrimeSmoothWeightActual.cutoffMatrix
    split_ifs
    · rw [hprefix]
      simp [Cutoff.cutChi_eq_one (show (0 : ℝ) ≤ 1 by norm_num)]
    · rfl
  unfold APrimeSmoothWeightActual.weightD
  rw [hconst]
  simp

private theorem crossPart_zero_of_weightD_zero (d : Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ)
    (r : ℝ) (hw : ∀ q ω, wD q ω = 0) :
    APrimeDuhamelModel.crossPart d N Ψ wD r = 0 := by
  unfold APrimeDuhamelModel.crossPart
  simp [hw]

/-- Formal value at time zero; the generator identity is used at positive time. -/
theorem crossPart_zero_r0 (d : Gauss.Dims) (N : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ) :
    APrimeDuhamelModel.crossPart d N Ψ wD 0 = 0 := by
  simp [APrimeDuhamelModel.crossPart]

theorem crossPart_zero_p0 (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m : ℕ)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (r : ℝ) :
    APrimeDuhamelModel.crossPart d N Ψ
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ 0 N k m) r = 0 := by
  exact crossPart_zero_of_weightD_zero d N Ψ _ r
    (fun q ω => weightD_zero_p0 d E D δ s t mesh N₀ N k m q ω)

theorem crossPart_zero_inactive (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m p : ℕ)
    (h : ¬(k ≤ CutHypTheta.cutNetTop s t mesh N ∧ N₀ ≤ N))
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (r : ℝ) :
    APrimeDuhamelModel.crossPart d N Ψ
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m) r = 0 := by
  exact crossPart_zero_of_weightD_zero d N Ψ _ r
    (fun q ω => weightD_zero_inactive d E D δ s t mesh N₀ N k m p h q ω)

theorem crossPart_zero_k0 (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N m p : ℕ) (hm : 1 ≤ m)
    (Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (r : ℝ) :
    APrimeDuhamelModel.crossPart d N Ψ
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N 0 m) r = 0 := by
  exact crossPart_zero_of_weightD_zero d N Ψ _ r
    (fun q ω => weightD_zero_k0 d E D δ s t mesh N₀ N m p hm q ω)

theorem jointRate_nonneg (d : Gauss.Dims) (E D δ : ℝ)
    (s mesh : ℕ → ℝ) (N k m : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ)
    (hN : 0 < N) (ω : Gauss.Ω d) :
    0 ≤ jointRate d E D δ s mesh N k m σ a v r ω := by
  have hΘ := APrimeSmoothWeightActual.threshold_pos (δ := δ) hN
  by_cases hω : ω ∈ transition d E D δ s mesh N k m
  · rw [jointRate, Set.indicator_of_mem hω]
    exact mul_nonneg
      (div_nonneg (Real.sqrt_nonneg _) hΘ.le)
      (Real.sqrt_nonneg _)
  · rw [jointRate, Set.indicator_of_notMem hω]

/-- The event split is on the full early-gradient/current-QV product. -/
theorem jointRate_norm_le_event (d : Gauss.Dims) (E D δ : ℝ)
    (s mesh : ℕ → ℝ) (N k m p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ)
    (hN : 0 < N) (hp : 1 ≤ p)
    {Good : Set (Gauss.Ω d)} (hGood : MeasurableSet Good)
    {b q Eall ρ : ℝ} (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hEall : 0 ≤ Eall) (hρ : 0 ≤ ρ)
    (hBgood : ∀ ω ∈ Good ∩ transition d E D δ s mesh N k m,
      prefixGradient d E D δ s mesh N k m ω ≤ b)
    (hQgood : ∀ ω ∈ Good ∩ transition d E D δ s mesh N k m,
      APrimeDriftTimeFamily.qvAt d E D N σ a (s N) v r ω ≤ q)
    (hAll : ∀ ω, prefixGradient d E D δ s mesh N k m ω *
      √(APrimeDriftTimeFamily.qvAt d E D N σ a (s N) v r ω) ≤ Eall)
    (hP : ((Gauss.P d) Goodᶜ).toReal ≤ ρ)
    (hZi : Integrable (fun ω => |jointRate d E D δ s mesh N k m σ a v r ω| ^
      (2 * p)) (Gauss.P d)) :
    (∫ ω, |jointRate d E D δ s mesh N k m σ a v r ω| ^ (2 * p)
      ∂(Gauss.P d)) ^ ((1 : ℝ) / (2 * p)) ≤
      b * √q + Eall * ρ ^ ((1 : ℝ) / (2 * p)) := by
  have hgood : ∀ ω ∈ Good,
      |jointRate d E D δ s mesh N k m σ a v r ω| ≤ b * √q := by
    intro ω hω
    rw [abs_of_nonneg (jointRate_nonneg d E D δ s mesh N k m σ a v r hN ω)]
    by_cases htrans : ω ∈ transition d E D δ s mesh N k m
    · rw [jointRate, Set.indicator_of_mem htrans]
      have hevent : ω ∈ Good ∩ transition d E D δ s mesh N k m := ⟨hω, htrans⟩
      exact mul_le_mul (hBgood ω hevent)
        (Real.sqrt_le_sqrt (hQgood ω hevent)) (Real.sqrt_nonneg _) hb
    · rw [jointRate, Set.indicator_of_notMem htrans]
      positivity
  have hall : ∀ ω,
      |jointRate d E D δ s mesh N k m σ a v r ω| ≤ Eall := by
    intro ω
    rw [abs_of_nonneg (jointRate_nonneg d E D δ s mesh N k m σ a v r hN ω)]
    by_cases htrans : ω ∈ transition d E D δ s mesh N k m
    · rw [jointRate, Set.indicator_of_mem htrans]
      exact hAll ω
    · rw [jointRate, Set.indicator_of_notMem htrans]
      exact hEall
  have hh := APrimeBadSplit.weighted_norm_le_of_event
    (P := Gauss.P d) (q := 2 * p) (W := fun _ => (1 : ℝ))
    (Z := jointRate d E D δ s mesh N k m σ a v r)
    (by omega : 2 * p ≠ 0) (by simp) (by simp) (by simpa using hZi)
    hGood (mul_nonneg hb (Real.sqrt_nonneg _)) hEall hρ hgood hall hP
  simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using hh

/-- The positive-time cross consumer for a joint product rate. The bound on the
cross sum is global, while a favorable bound on `Z` may be event restricted. -/
theorem crossPart_le_jointHolder (d : Gauss.Dims) (N p : ℕ) (hp : 1 ≤ p)
    {T : Set ℝ} {Ψ : ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    {w : Gauss.Ω d → ℝ}
    {wD : (d.Idx N × d.Idx N × Bool) → Gauss.Ω d → ℝ}
    (hTF : Gauss.TestFunT₁ d N T Ψ) (hw : Gauss.WeightC1 d N w wD)
    {r : ℝ} (hrT : r ∈ T) (hr0 : 0 < r)
    {Y Z : Gauss.Ω d → ℝ} {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS5 : ∀ ω, APrimeBadSplit.crossAbsSum d N Ψ wD r ω ≤
      Cs * (|Y ω| ^ (2 * p - 1) * |Z ω|))
    (hYm : AEStronglyMeasurable Y (Gauss.P d))
    (hZm : AEStronglyMeasurable Z (Gauss.P d))
    (hYi : Integrable (fun ω => |Y ω| ^ (2 * p)) (Gauss.P d))
    (hZi : Integrable (fun ω => |Z ω| ^ (2 * p)) (Gauss.P d))
    (hProdInt : Integrable (fun ω => |Y ω| ^ (2 * p - 1) * |Z ω|)
      (Gauss.P d)) :
    APrimeDuhamelModel.crossPart d N Ψ wD r ≤
      (1 / (2 * √r)) * Cs *
        (∫ ω, |Y ω| ^ (2 * p) ∂(Gauss.P d)) ^
          ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
        (∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d)) ^
          ((1 : ℝ) / (2 * (p : ℝ))) := by
  have hmono : (∫ ω, APrimeBadSplit.crossAbsSum d N Ψ wD r ω ∂(Gauss.P d)) ≤
      ∫ ω, Cs * (|Y ω| ^ (2 * p - 1) * |Z ω|) ∂(Gauss.P d) :=
    integral_mono (APrimeDuhamelModel.integrable_crossSum hTF hw hrT)
      (hProdInt.const_mul Cs) hS5
  have hholder := MomentDuhamel.integral_pow_sub_one_mul_le
    (P := Gauss.P d) hp hYm hZm hYi hZi
  have hnorm : MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z =
      (∫ ω, |Z ω| ^ (2 * p) ∂(Gauss.P d)) ^
        ((1 : ℝ) / (2 * (p : ℝ))) := by
    simp only [MomentDuhamel.momNorm, Nat.cast_mul, Nat.cast_ofNat]
  have hfac0 : 0 ≤ (1 / (2 * √r)) * Cs := by positivity
  calc
    APrimeDuhamelModel.crossPart d N Ψ wD r ≤
        (1 / (2 * √r)) *
          ∫ ω, APrimeBadSplit.crossAbsSum d N Ψ wD r ω ∂(Gauss.P d) :=
      APrimeDuhamelModel.crossPart_le_integral hTF hw hrT hr0
    _ ≤ (1 / (2 * √r)) *
          ∫ ω, Cs * (|Y ω| ^ (2 * p - 1) * |Z ω|) ∂(Gauss.P d) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (1 / (2 * √r)) * Cs *
          ∫ ω, |Y ω| ^ (2 * p - 1) * |Z ω| ∂(Gauss.P d) := by
      rw [integral_const_mul]
      ring
    _ ≤ (1 / (2 * √r)) * Cs *
          ((∫ ω, |Y ω| ^ (2 * p) ∂(Gauss.P d)) ^
            ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
            MomentDuhamel.momNorm (Gauss.P d) (2 * p) Z) := by
      exact mul_le_mul_of_nonneg_left hholder hfac0
    _ = _ := by rw [hnorm]; ring

/-- The actual positive-time cross term, with the endpoint and prefix frozen. -/
theorem crossPart_active_le_jointNorm (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ)
    (hE : |E| < 2) (hs : s N < 1) (hs0 : 0 ≤ s N)
    (hv1 : v < 1) (hr : r ∈ Set.Icc (s N) v) (hr0 : 0 < r)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, CutHypTheta.cutNetPt s mesh N j < 1)
    (hk : k ≤ CutHypTheta.cutNetTop s t mesh N) (hN₀ : N₀ ≤ N)
    (hp : 1 ≤ p)
    (hYm : AEStronglyMeasurable
      (fun ω => APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖) (Gauss.P d))
    (hZm : AEStronglyMeasurable
      (jointRate d E D δ s mesh N k m σ a v r) (Gauss.P d))
    (hYi : Integrable
      (fun ω => |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p)) (Gauss.P d))
    (hZi : Integrable
      (fun ω => |jointRate d E D δ s mesh N k m σ a v r ω| ^ (2 * p))
      (Gauss.P d))
    (hProdInt : Integrable
      (fun ω => |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p - 1) *
        |jointRate d E D δ s mesh N k m σ a v r ω|) (Gauss.P d)) :
    APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d E D N p σ a (s N) v)
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m) r ≤
      (1 / (2 * √r)) * (((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)) *
      (∫ ω, |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p) ∂(Gauss.P d)) ^
        ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
      (∫ ω, |jointRate d E D δ s mesh N k m σ a v r ω| ^ (2 * p)
        ∂(Gauss.P d)) ^ ((1 : ℝ) / (2 * (p : ℝ))) := by
  let Y : Gauss.Ω d → ℝ := fun ω =>
    APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
      ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
        (Gauss.Hflow d N r ω)‖
  let Z := jointRate d E D δ s mesh N k m σ a v r
  have hY0 : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact mul_nonneg (Cutoff.cutChi_nonneg _) (norm_nonneg _)
  have hZ0 : ∀ ω, 0 ≤ Z ω := jointRate_nonneg d E D δ s mesh N k m σ a v r hN
  have hS5 : ∀ ω,
      APrimeBadSplit.crossAbsSum d N
        (APrimeDriftTimeFamily.momentAt d E D N p σ a (s N) v)
        (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m) r ω ≤
      (((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)) *
        (|Y ω| ^ (2 * p - 1) * |Z ω|) := by
    intro ω
    have hh := crossAbsSum_active_le d E D δ s t mesh N₀ N k m p
      σ a v r hE hs hN hm hu hs0 hv1 hr hk hN₀ hp ω
    simpa only [Y, Z, abs_of_nonneg (hY0 ω), abs_of_nonneg (hZ0 ω),
      mul_assoc] using hh
  have hsv : s N ≤ v := hr.1.trans hr.2
  have hTF := APrimeNormalizedTestFun.normalizedTestFunBridge d E D N p σ a
    hE hs0 hsv hv1
  have hw := APrimeSmoothWeightActual.weightC1 d (E := E) (D := D)
    (δ := δ) (s := s) (t := t) (mesh := mesh) (N₀ := N₀)
    (p := p) (N := N) (k := k) (m := m) hE hs hN hm hu
  exact crossPart_le_jointHolder d N p hp hTF hw hr hr0
    (by positivity) hS5 hYm hZm hYi hZi hProdInt

/-- Conditional actual cross bound with one measurable common Good event. -/
theorem crossPart_active_le_jointEvent (d : Gauss.Dims) (E D δ : ℝ)
    (s t mesh : ℕ → ℝ) (N₀ N k m p : ℕ)
    (σ : Fin 2 → Bool) (a : LoopArg (d.L N) 2) (v r : ℝ)
    (hE : |E| < 2) (hs : s N < 1) (hs0 : 0 ≤ s N)
    (hv1 : v < 1) (hr : r ∈ Set.Icc (s N) v) (hr0 : 0 < r)
    (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, CutHypTheta.cutNetPt s mesh N j < 1)
    (hk : k ≤ CutHypTheta.cutNetTop s t mesh N) (hN₀ : N₀ ≤ N)
    (hp : 1 ≤ p)
    {Good : Set (Gauss.Ω d)} (hGood : MeasurableSet Good)
    {b q Eall ρ : ℝ} (hb : 0 ≤ b) (hq : 0 ≤ q)
    (hEall : 0 ≤ Eall) (hρ : 0 ≤ ρ)
    (hBgood : ∀ ω ∈ Good ∩ transition d E D δ s mesh N k m,
      prefixGradient d E D δ s mesh N k m ω ≤ b)
    (hQgood : ∀ ω ∈ Good ∩ transition d E D δ s mesh N k m,
      APrimeDriftTimeFamily.qvAt d E D N σ a (s N) v r ω ≤ q)
    (hAll : ∀ ω, prefixGradient d E D δ s mesh N k m ω *
      √(APrimeDriftTimeFamily.qvAt d E D N σ a (s N) v r ω) ≤ Eall)
    (hP : ((Gauss.P d) Goodᶜ).toReal ≤ ρ)
    (hYm : AEStronglyMeasurable
      (fun ω => APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖) (Gauss.P d))
    (hZm : AEStronglyMeasurable
      (jointRate d E D δ s mesh N k m σ a v r) (Gauss.P d))
    (hYi : Integrable
      (fun ω => |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p)) (Gauss.P d))
    (hZi : Integrable
      (fun ω => |jointRate d E D δ s mesh N k m σ a v r ω| ^ (2 * p))
      (Gauss.P d))
    (hProdInt : Integrable
      (fun ω => |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p - 1) *
        |jointRate d E D δ s mesh N k m σ a v r ω|) (Gauss.P d)) :
    APrimeDuhamelModel.crossPart d N
      (APrimeDriftTimeFamily.momentAt d E D N p σ a (s N) v)
      (APrimeSmoothWeightActual.weightD d E D δ s t mesh N₀ p N k m) r ≤
      (1 / (2 * √r)) * (((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)) *
      (∫ ω, |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p) ∂(Gauss.P d)) ^
        ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) *
      (b * √q + Eall * ρ ^ ((1 : ℝ) / (2 * (p : ℝ)))) := by
  have hcross := crossPart_active_le_jointNorm d E D δ s t mesh N₀ N k m p
    σ a v r hE hs hs0 hv1 hr hr0 hN hm hu hk hN₀ hp
    hYm hZm hYi hZi hProdInt
  have hnorm := jointRate_norm_le_event d E D δ s mesh N k m p
    σ a v r hN hp hGood hb hq hEall hρ hBgood hQgood hAll hP hZi
  have hφ0 : 0 ≤ ∫ ω,
      |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p) ∂(Gauss.P d) :=
    integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _
  have hfac0 : 0 ≤ (1 / (2 * √r)) *
      (((2 * p : ℕ) : ℝ) ^ 2 * (15 / 8 : ℝ)) *
      (∫ ω, |APrimeSmoothWeightActual.cutoff d E D δ s mesh N k m ω *
        ‖APrimeDriftTimeFamily.coordAt d E D N σ a (s N) v r
          (Gauss.Hflow d N r ω)‖| ^ (2 * p) ∂(Gauss.P d)) ^
        ((2 * (p : ℝ) - 1) / (2 * (p : ℝ))) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity))
      (Real.rpow_nonneg hφ0 _)
  exact hcross.trans (mul_le_mul_of_nonneg_left hnorm hfac0)

#print axioms crossAbsSum_active_le
#print axioms weightD_zero_p0
#print axioms weightD_zero_inactive
#print axioms weightD_zero_k0
#print axioms crossPart_zero_r0
#print axioms jointRate_norm_le_event
#print axioms crossPart_le_jointHolder
#print axioms crossPart_active_le_jointNorm
#print axioms crossPart_active_le_jointEvent

end RBM.APrimeCrossJointSplit
