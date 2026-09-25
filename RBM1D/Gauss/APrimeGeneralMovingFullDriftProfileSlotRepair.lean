/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftNearQuadraticSlot
import RBM1D.Gauss.APrimeGeneralMovingDriftFarNonlinearSlot
import RBM1D.Gauss.APrimeGeneralMovingDriftFarLinearEndpointSlotRepair

/-!
# T1055: full deterministic T615 drift profile at the T995 schedule

The interval continuity arguments below are reconstructed from public
producer definitions in this assembly module. No rejected producer is imported.
-/

namespace RBM.APrimeGeneralMovingFullDriftProfileSlotRepair

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open APrimeGeneralMovingDriftFarLinearSlot (normalizedFarLinear)

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]


private theorem continuousOn_nearMain {E : Real} {s : Nat → Real} {N : Nat}
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaSrc zetaCtr : Real) :
    ContinuousOn (fun u => APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain E s zetaSrc zetaCtr N v u)
      (Set.Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Set.Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hsEll : 0 < B.ell N (s N) :=
    zero_lt_one.trans_le (one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1)
  have hratio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Set.Icc (s N) v) := hEll.div_const _
  have hEta : ContinuousOn (fun u => etaT E u) (Set.Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ Set.Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Set.Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Set.Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u ∈ Set.Icc (s N) v, 1 - u ≠ 0 := by
      intro u hu
      linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRpos : ∀ u, u ∈ Set.Icc (s N) v → 0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRpow : ContinuousOn (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real))
      (Set.Icc (s N) v) := hR.rpow_const (fun u hu => Or.inl (ne_of_gt (hRpos u hu)))
  have hc : ContinuousOn (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u))
      (Set.Icc (s N) v) := by
    have hEllpos : ∀ u, u ∈ Set.Icc (s N) v → B.ell N u ≠ 0 := by
      intro u hu
      exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
        (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1)))
    have hinv : ContinuousOn (fun u => (B.ell N u)⁻¹) (Set.Icc (s N) v) :=
      hEll.inv₀ hEllpos
    have hpoly : ContinuousOn (fun u =>
        2 * Real.log (d.W N : Real) ^ (3 : Real) + 2 * (B.ell N u)⁻¹)
        (Set.Icc (s N) v) := by fun_prop
    have hexp : ContinuousOn (fun _ : Real =>
        Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)))
        (Set.Icc (s N) v) := continuousOn_const
    have hEq : (fun u => Lemma57.cNear (d.W N : Real) (B.ell N u)) =
        (fun u => (2 * Real.log (d.W N : Real) ^ (3 : Real) +
          2 * (B.ell N u)⁻¹) * Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real))) := by
      funext u
      simp [Lemma57.cNear, div_eq_mul_inv]
    exact hEq ▸ hpoly.mul hexp
  have hmain : ContinuousOn (fun u => APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain E s zetaSrc zetaCtr N v u)
      (Set.Icc (s N) v) := by
    unfold APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
    have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Set.Icc (s N) v) :=
      hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
    have hratio3 : ContinuousOn (fun u => (B.ell N u / B.ell N (s N)) ^ 3)
        (Set.Icc (s N) v) := hratio.pow 3
    have hinner : ContinuousOn (fun u =>
        4 * (N : Real) ^ (zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
          (B.ell N u / B.ell N (s N)) ^ 3 *
          Lemma57.cNear (d.W N : Real) (B.ell N u)) (Set.Icc (s N) v) := by
      have hscalar : ContinuousOn (fun _ : Real =>
          4 * (N : Real) ^ (zetaCtr + zetaSrc)) (Set.Icc (s N) v) := continuousOn_const
      have hprod := (hscalar.mul hEtaInv).mul (hratio3.mul hc)
      convert hprod using 1 <;> ext u <;> simp only [Pi.mul_apply] <;> ring
    exact ((continuousOn_const.mul hRpow).mul continuousOn_const).mul hinner
  exact hmain


private theorem continuousOn_nearTail {E D : Real} {s : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2)
    (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (ζ τ κ : Real) :
    ContinuousOn (fun u => APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail E D s ζ τ κ N v u)
      (Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hEll0 : ∀ u ∈ Icc (s N) v, B.ell N u ≠ 0 := by
    intro u hu
    have h := one_le_ellHat_of_nonneg (B.one_le_L N)
      (hs0.trans hu.1) (hu.2.trans_lt hv1)
    have hh : 1 ≤ B.ell N u := by simpa only [Band.ell] using h
    exact ne_of_gt (by linarith : 0 < B.ell N u)
  have hsEll : B.ell N (s N) ≠ 0 := by
    have h := one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1
    have hh : 1 ≤ B.ell N (s N) := by simpa only [Band.ell] using h
    exact ne_of_gt (by linarith : 0 < B.ell N (s N))
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEta0 : ∀ u ∈ Icc (s N) v, etaT E u ≠ 0 := by
    intro u hu
    exact (Step2.etaT_pos' hE (hu.2.trans_lt hv1)).ne'
  have hR : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u
        unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
        rw [Step2.etaT_ratio hE]]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    exact continuousOn_const.div hden (by
      intro u hu
      linarith [hu.2])
  have hRpos : ∀ u ∈ Icc (s N) v, Step2Moment.ratR E s N u ≠ 0 := by
    intro u hu
    exact (Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)).ne'
  have hGap : ContinuousOn
      (fun u => APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    unfold APrimeDriftNearAbsorb.gap Lemma57.ellStarStar ellStar
    fun_prop
  have hTail : ContinuousOn
      (fun u => tailT (d.W N : Real) (B.ell N u) (etaT E u) D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)))
      (Icc (s N) v) := by
    have hA : ContinuousOn
        (fun u => ((d.W N : Real) * B.ell N u * etaT E u)^2)
        (Icc (s N) v) := by fun_prop
    have hA0 : ∀ u ∈ Icc (s N) v,
        ((d.W N : Real) * B.ell N u * etaT E u)^2 ≠ 0 := by
      intro u hu
      have hW : 0 < (d.W N : Real) := by exact_mod_cast B.W_pos N
      have he : 0 < B.ell N u := by
        have hh := one_le_ellHat_of_nonneg (B.one_le_L N)
          (hs0.trans hu.1) (hu.2.trans_lt hv1)
        have hhh : 1 ≤ B.ell N u := by simpa only [Band.ell] using hh
        linarith
      have ht : 0 < etaT E u := Step2.etaT_pos' hE (hu.2.trans_lt hv1)
      positivity
    have hInv := hA.inv₀ hA0
    have hDiv := hGap.div hEll hEll0
    have hExp := Real.continuous_exp.comp_continuousOn hDiv.sqrt.neg
    change ContinuousOn
      (fun u => Real.exp (-Real.sqrt
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u) / B.ell N u)))
      (Icc (s N) v) at hExp
    change ContinuousOn
      (fun u => (((d.W N : Real) * B.ell N u * etaT E u)^2)⁻¹ *
        Real.exp (-Real.sqrt
          (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u) / B.ell N u)) +
          (d.W N : Real)^(-D)) (Icc (s N) v)
    exact (hInv.mul hExp).add continuousOn_const
  have hRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  have hRpow : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real))
      (Icc (s N) v) := hR.rpow_const (fun u hu => Or.inl (hRpos u hu))
  let F : Real → Real := fun u =>
    4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (Step2Moment.ratR E s N u) ^ (-2 : Real) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) *
      ((N : Real)^ζ * (d.L N : Real) *
        APrimeGeneralMovingDriftSource.blockCap E s τ κ N u *
        (d.W N : Real)^2 * B.ell N u *
        (B.ell N u / B.ell N (s N)) *
        Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real)) *
        tailT (d.W N : Real) (B.ell N u) (etaT E u) D
          (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)))
  have hF : ContinuousOn F (Icc (s N) v) := by
    dsimp [F, APrimeGeneralMovingDriftSource.blockCap]
    fun_prop
  apply hF.congr
  intro u hu
  have hellne := hEll0 u hu
  have he := hEta0 u hu
  have hrune : B.ell N u / B.ell N (s N) ≠ 0 := div_ne_zero hellne hsEll
  dsimp [F, APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail]
  field_simp [hellne, hsEll, he, hrune]



private theorem continuousOn_farLinear {E D : Real} {s t : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N)
    (hsv : s N ≤ v) (hv1 : v < 1) (zetaCtr tauG delta : Real) :
    ContinuousOn (fun u => normalizedFarLinear E D s t zetaCtr tauG delta N v u)
      (Icc (s N) v) := by
  have hs1 : s N < 1 := hsv.trans_lt hv1
  have hEll : ContinuousOn (fun u => B.ell N u) (Icc (s N) v) :=
    Step2.continuousOn_ell B N hv1
  have hEta : ContinuousOn (fun u => etaT E u) (Icc (s N) v) := by
    rw [show (fun u => etaT E u) = (fun u => (mE E).im * (1 - u)) by
      funext u; rw [Step2.etaT_eq]; ring]
    fun_prop
  have hEtaPos : ∀ u, u ∈ Icc (s N) v → 0 < etaT E u := by
    intro u hu
    exact Step2.etaT_pos' hE (hu.2.trans_lt hv1)
  have hRat : ContinuousOn (fun u => Step2Moment.ratR E s N u) (Icc (s N) v) := by
    rw [show (fun u => Step2Moment.ratR E s N u) =
      (fun u => APrimeDriftIntegralBudget.ratio (s N) u) by
        funext u; exact ratR_eq_ratio hE]
    unfold APrimeDriftIntegralBudget.ratio
    have hden : ContinuousOn (fun u : Real => 1 - u) (Icc (s N) v) :=
      continuousOn_const.sub continuousOn_id
    have hden0 : ∀ u, u ∈ Icc (s N) v → 1 - u ≠ 0 := by
      intro u hu; linarith [hu.2]
    exact continuousOn_const.div hden hden0
  have hRatPos : ∀ u, u ∈ Icc (s N) v →
      0 < Step2Moment.ratR E s N u := by
    intro u hu
    exact Step2Moment.ratR_pos hE hs1 (hu.2.trans_lt hv1)
  have hRatInv : ContinuousOn
      (fun u => (Step2Moment.ratR E s N u) ^ (-2 : Real)) (Icc (s N) v) :=
    hRat.rpow_const (fun u hu => Or.inl (ne_of_gt (hRatPos u hu)))
  have hEllPos : ∀ u, u ∈ Icc (s N) v → B.ell N u ≠ 0 := by
    intro u hu
    exact ne_of_gt (zero_lt_one.trans_le (one_le_ellHat_of_nonneg
      (B.one_le_L N) (hs0.trans hu.1) (hu.2.trans_lt hv1)))
  have hEllInv : ContinuousOn (fun u => (B.ell N u)⁻¹) (Icc (s N) v) :=
    hEll.inv₀ hEllPos
  have hcFar : ContinuousOn (fun u => Lemma57.cFar (B.W N : Real) (B.ell N u))
      (Icc (s N) v) := by
    unfold Lemma57.cFar
    have hpoly : ContinuousOn (fun u =>
        4 * Real.log (B.W N : Real) ^ (3 / 2 : Real) + 8 * (B.ell N u)⁻¹)
        (Icc (s N) v) := by fun_prop
    exact hpoly.mul continuousOn_const
  have hcap : ContinuousOn
      (fun u => APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u)
      (Icc (s N) v) := by
    unfold APrimeGeneralMovingDriftSource.blockCap Step2Moment.ratR
    have hpow : ContinuousOn (fun u =>
        (Step2Moment.ratR E s N u) ^ (4 : Nat)) (Icc (s N) v) := by
      exact hRat.pow 4
    fun_prop
  have hEtaInv : ContinuousOn (fun u => (etaT E u)⁻¹) (Icc (s N) v) :=
    hEta.inv₀ (fun u hu => (hEtaPos u hu).ne')
  have hEllRatio : ContinuousOn (fun u => B.ell N u / B.ell N (s N))
      (Icc (s N) v) := hEll.div_const _
  unfold normalizedFarLinear
  have hmain : ContinuousOn (fun u =>
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) *
        ((etaT E u)⁻¹ * (4 * (N : Real)^zetaCtr *
          (B.ell N u / B.ell N (s N))) *
          (Lemma57.cFar (B.W N : Real) (B.ell N u) *
            APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u *
            (flowDelta d E t N + (B.W N : Real)⁻¹)))) (Icc (s N) v) := by
    fun_prop
  exact hmain


/-- The complete near source is integrable on every valid cut interval. -/
theorem intervalIntegrable_normalizedNearSource
    {E D : Real} {s : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (δ : Real) :
    IntervalIntegrable
      (fun u => APrimeGeneralMovingDriftNearCombinedSlot.normalizedNearSource
        E D s δ N v u) volume (s N) v := by
  have hmain := (continuousOn_nearMain hE hs0 hsv hv1
    (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
    (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)).intervalIntegrable_of_Icc (μ := volume) hsv
  have htail := (continuousOn_nearTail (D := D) hE hs0 hsv hv1
    (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
    (APrimeGeneralMovingSlotLossSchedule.tauG δ)
    (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)).intervalIntegrable_of_Icc (μ := volume) hsv
  convert hmain.add htail using 1
  ext u
  exact (APrimeGeneralMovingDriftNearCombinedSlot.normalized_near_source_split
    E D s δ N v u)

/-- The literal far-linear source is integrable on every valid cut interval. -/
theorem intervalIntegrable_normalizedFarLinear
    {E D : Real} {s t : Nat → Real} {N : Nat} {v : Real}
    (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (δ : Real) :
    IntervalIntegrable
      (fun u => normalizedFarLinear E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u)
      volume (s N) v :=
  (continuousOn_farLinear hE hs0 hsv hv1 _ _ _).intervalIntegrable_of_Icc hsv

/-- Literal four-component decomposition of T615's full capped profile. -/
theorem profile_eq_four_components
    (E D : Real) (s t : Nat → Real) (δ : Real)
    (N : Nat) (v u : Real) :
    APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
      (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u =
      APrimeGeneralMovingDriftNearCombinedSlot.normalizedNearSource
        E D s δ N v u +
      normalizedFarLinear E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u +
      APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear E D s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u +
      APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic E D s
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u := by
  rw [APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear_eq_T615_residual]
  unfold APrimeGeneralMovingSmoothDriftNormBudget.profile
    APrimeGeneralMovingDriftNearCombinedSlot.normalizedNearSource
    APrimeGeneralMovingDriftFarLinearSlot.normalizedFarLinear
    APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic
  ring

/-- The exact T615 full deterministic drift profile fits the T995 slot,
uniformly over every active cell, including the zero-length cell. -/
theorem eventually_full_profile_integral_le_small_slot
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        (11 / (mE E).im + 2) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
  have hnearquad :=
    APrimeGeneralMovingDriftNearQuadraticSlot.eventually_near_plus_quadratic_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hfar :=
    APrimeGeneralMovingDriftFarLinearEndpointSlotRepair.eventually_far_linear_integral_le_small_slot_endpoint
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hnonlin :=
    APrimeGeneralMovingDriftFarNonlinearSlot.eventually_far_nonlinear_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  filter_upwards [hnearquad, hfar, hnonlin] with N hnearquadN hfarN hnonlinN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  let fNear : Real → Real := fun u =>
    APrimeGeneralMovingDriftNearCombinedSlot.normalizedNearSource E D s δ N v u
  let fFar : Real → Real := fun u =>
    normalizedFarLinear E D s t
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  let fNonlin : Real → Real := fun u =>
    APrimeGeneralMovingDriftFarNonlinearSlot.normalizedFarNonlinear E D s
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  let fQuad : Real → Real := fun u =>
    APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic E D s
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u
  have hni : IntervalIntegrable fNear volume (s N) v :=
    intervalIntegrable_normalizedNearSource hE (hs0 N) hv.1 hv1 δ
  have hfi : IntervalIntegrable fFar volume (s N) v :=
    intervalIntegrable_normalizedFarLinear hE (hs0 N) hv.1 hv1 δ
  have hnli : IntervalIntegrable fNonlin volume (s N) v :=
    APrimeGeneralMovingDriftFarNonlinearSlot.intervalIntegrable_normalizedFarNonlinear
      hE (hs0 N) hv.1 hv1 _ _ _
  have hqi : IntervalIntegrable fQuad volume (s N) v :=
    APrimeGeneralMovingDriftQuadraticSlotRepair.intervalIntegrable_normalizedQuadratic
      hE (hs0 N) hv.1 hv1 _
  have hfun : (fun u =>
      APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) =
      (fun u => ((fNear u + fFar u) + fNonlin u) + fQuad u) := by
    funext u
    simpa only [fNear, fFar, fNonlin, fQuad] using
      profile_eq_four_components E D s t δ N v u
  have hsplit :
      (∫ u in (s N)..v,
        APrimeGeneralMovingSmoothDriftNormBudget.profile E D s t
          (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) =
      ((∫ u in (s N)..v, fNear u) +
        (∫ u in (s N)..v, fFar u) +
        (∫ u in (s N)..v, fNonlin u)) +
        (∫ u in (s N)..v, fQuad u) := by
    rw [hfun, intervalIntegral.integral_add ((hni.add hfi).add hnli) hqi,
      intervalIntegral.integral_add (hni.add hfi) hnli,
      intervalIntegral.integral_add hni hfi]
  have hnearquadK := hnearquadN k hk
  have hfarK := hfarN k hk
  have hnonlinK := hnonlinN k hk
  change (∫ u in (s N)..v, fNear u) +
    (∫ u in (s N)..v, fQuad u) ≤ _ at hnearquadK
  change (∫ u in (s N)..v, fFar u) ≤ _ at hfarK
  change (∫ u in (s N)..v, fNonlin u) ≤ _ at hnonlinK
  have hsum := add_le_add (add_le_add hnearquadK hfarK) hnonlinK
  calc
    _ = ((∫ u in (s N)..v, fNear u) +
        (∫ u in (s N)..v, fQuad u) +
        (∫ u in (s N)..v, fFar u)) +
        (∫ u in (s N)..v, fNonlin u) := by rw [hsplit]; ring
    _ ≤ ((((8 / (mE E).im + 1) + 1 / (mE E).im) *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real)) +
         (1 / (mE E).im) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real)) +
        ((1 / (mE E).im + 1) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real)) := hsum
    _ = (11 / (mE E).im + 2) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by ring

/-- The accepted T995 same-resident positive-cell witness at this schedule. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_full_profile_integral_le_small_slot
#print axioms nondegenerate_positive_cell_witness

#print axioms intervalIntegrable_normalizedNearSource
#print axioms intervalIntegrable_normalizedFarLinear
#print axioms profile_eq_four_components

end
end RBM.APrimeGeneralMovingFullDriftProfileSlotRepair
