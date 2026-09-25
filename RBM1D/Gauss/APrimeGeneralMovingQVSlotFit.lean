/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingQVNormBudget
import RBM1D.Gauss.APrimeGeneralMovingQVAbsorption
import RBM1D.Gauss.APrimeDriftIntegralBudget
import RBM1D.Gauss.APrimeInit
import RBM1D.Gauss.APrimeFirstCellQVFixedTwo

/-!
# T997: deterministic general-moving QV profile to A-prime N2

The T591 whole-root profile is retained. This module develops the exact
scale, exponent and integral estimates needed for its N2 fit.
-/

namespace RBM.APrimeGeneralMovingQVSlotFit

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem scale_interpolation_poly {A n R : ℝ}
    (hA0 : 0 ≤ A) (hR1 : 1 ≤ R)
    (hn : n ≤ A) (hR : R ^ 30 ≤ A) :
    n * R ^ 120 ≤ A ^ 5 := by
  have hR4 : (R ^ 30) ^ 4 ≤ A ^ 4 :=
    pow_le_pow_left₀ (pow_nonneg (by linarith : 0 ≤ R) _) hR 4
  have hp : n * (R ^ 30) ^ 4 ≤ A * A ^ 4 :=
    mul_le_mul hn hR4 (by positivity) hA0
  convert hp using 1 <;> ring

-- Exact numerical room for the near source, repaired residual, and far row.
private theorem slot_exponent_room {δ c : ℝ} (hδ : 0 < δ)
    (hc : 100 * δ ≤ c) :
    δ / 3200 + 3 * (δ / 100) < 5 * δ / 16 ∧
    2 * (δ / 100) < 5 * δ / 16 ∧
    3 * (δ / 1600) + 6 * (δ / 50) + 2 * (δ / 100) - c / 15 <
      5 * δ / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

-- The complement exponent is strictly below the squared N2 slot,
-- after Cond272Reg yields R^4 ≤ N^(2/15).
private theorem complement_exponent_room {δ : ℝ} (hδ : 0 < δ) :
    -(1 : ℝ) + 2 / 15 < 5 * δ / 16 := by linarith

private theorem near_integral_bound {s v m : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : 0 < m) :
    (∫ u in s..v,
      RBM.APrimeDriftIntegralBudget.ratio s u ^ (-(3/2 : ℝ)) / (m * (1-u))) ≤
      2 / (3*m) := by
  rw [RBM.APrimeDriftIntegralBudget.integral_ratio_power hs hsv hv hm.ne'
    (by norm_num : (-(3/2 : ℝ)) ≠ 0)]
  have hR : 0 ≤ RBM.APrimeDriftIntegralBudget.ratio s v ^ (-(3/2 : ℝ)) := by
    exact Real.rpow_nonneg (by unfold RBM.APrimeDriftIntegralBudget.ratio; positivity) _
  have hrewrite :
      (RBM.APrimeDriftIntegralBudget.ratio s v ^ (-(3/2 : ℝ)) - 1) /
          (m * -(3/2 : ℝ)) =
      (1 - RBM.APrimeDriftIntegralBudget.ratio s v ^ (-(3/2 : ℝ))) /
          (m * (3/2 : ℝ)) := by ring
  rw [hrewrite]
  have hden : 0 < 3*m := by positivity
  apply (div_le_div_iff₀ (by positivity : 0 < m * (3/2 : ℝ)) hden).2
  nlinarith [hR]

private theorem far_integral_bound {s v m : ℝ}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : 0 < m) :
    (∫ u in s..v,
      RBM.APrimeDriftIntegralBudget.ratio s u ^ (8 : ℝ) / (m * (1-u))) ≤
      RBM.APrimeDriftIntegralBudget.ratio s v ^ (8 : ℝ) / (8*m) := by
  rw [RBM.APrimeDriftIntegralBudget.integral_ratio_power hs hsv hv hm.ne'
    (by norm_num : (8 : ℝ) ≠ 0)]
  have hden : 0 < 8*m := by positivity
  apply (div_le_div_iff₀ (by positivity : 0 < m * (8 : ℝ)) hden).2
  nlinarith

private theorem scale_interpolation_rpow {A n R : ℝ}
    (hn : 0 < n) (hA : 0 < A) (hR : 1 ≤ R)
    (hna : n ≤ A) (hRA : R ^ 30 ≤ A) :
    A ^ (-(1/3 : ℝ)) ≤ n ^ (-(1/15 : ℝ)) * R ^ (-(8 : ℝ)) := by
  have hRpos : 0 < R := by linarith
  have hpoly : n * R ^ 120 ≤ A ^ 5 :=
    scale_interpolation_poly hA.le hR hna hRA
  have hpos : 0 < n * R ^ 120 := by positivity
  have hp := Real.rpow_le_rpow hpos.le hpoly (by norm_num : (0 : ℝ) ≤ 1/15)
  have hleft : (n * R ^ 120) ^ (1/15 : ℝ) = n ^ (1/15 : ℝ) * R ^ (8 : ℝ) := by
    rw [Real.mul_rpow hn.le (pow_nonneg hRpos.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul hRpos.le]
    norm_num
  have hright : (A ^ 5) ^ (1/15 : ℝ) = A ^ (1/3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    norm_num
  rw [hleft, hright] at hp
  have hleftpos : 0 < n ^ (1/15 : ℝ) * R ^ (8 : ℝ) := by positivity
  have hinv := inv_anti₀ hleftpos hp
  rw [Real.rpow_neg hA.le, Real.rpow_neg hn.le, Real.rpow_neg hRpos.le]
  calc
    (A ^ (1/3 : ℝ))⁻¹ ≤ (n ^ (1/15 : ℝ) * R ^ (8 : ℝ))⁻¹ := hinv
    _ = (n ^ (1/15 : ℝ))⁻¹ * (R ^ (8 : ℝ))⁻¹ := by rw [mul_inv_rev]; ring

private theorem blockCap_le_const
    {E : Real} {s : Nat -> Real} {tau delta : Real} {N : Nat} {u : Real}
    (hN : 1 <= N) (htau : 0 <= tau) (hdelta : 0 <= delta)
    (hR : 1 <= Step2Moment.ratR E s N u) :
    APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tau delta N u <=
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        (N : Real) ^ (tau + 2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
  have hn : (1 : Real) <= N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
  have hR4 : 1 <= Step2Moment.ratR E s N u ^ 4 := one_le_pow₀ hR
  have htauPow : 1 <= (N : Real) ^ tau := Real.one_le_rpow hn htau
  have hdeltaPow : 1 <= (N : Real) ^ (2 * delta) :=
    Real.one_le_rpow hn (by positivity)
  have hX1 : 1 <= (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
      Step2Moment.ratR E s N u ^ 4 := by
    nlinarith [mul_le_mul htauPow hdeltaPow (by positivity) (by positivity),
      mul_le_mul (mul_le_mul htauPow hdeltaPow (by positivity) (by positivity)) hR4
        (by positivity) (by positivity)]
  have htauX : (N : Real) ^ tau <=
      (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
    have hmul : 1 <= (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4 := by
      nlinarith [mul_le_mul hdeltaPow hR4 (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hmul
      (Real.rpow_nonneg hn0.le tau)]
  have hpow : (N : Real) ^ tau * (N : Real) ^ (2 * delta) =
      (N : Real) ^ (tau + 2 * delta) := by rw [Real.rpow_add hn0]
  unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap
  calc
    1 + (N : Real) ^ tau *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
            Step2Moment.ratR E s N u ^ 4) + 2) <=
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        ((N : Real) ^ tau * (N : Real) ^ (2 * delta)) *
        Step2Moment.ratR E s N u ^ 4 := by
      let X := (N : Real) ^ tau * (N : Real) ^ (2 * delta) *
        Step2Moment.ratR E s N u ^ 4
      have hmain : (N : Real) ^ tau *
          (9 * Real.exp (Real.sqrt 3) *
            ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta) *
              Step2Moment.ratR E s N u ^ 4)) =
          (9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) * X := by
        dsimp [X]
        ring
      rw [mul_add, hmain]
      dsimp only [X] at hX1 htauX ⊢
      nlinarith
    _ = _ := by rw [hpow]



private theorem eventually_cNear2_le {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {θ : Real} (hθ : 0 < θ) :
    ∀ᶠ N : Nat in atTop, ∀ u : TimeIcc s t N,
      Lemma57.cNear2 (B.W N : Real) (B.ell N (u : Real)) ≤ (N : Real) ^ θ := by
  have ha : 0 < θ / 2 := by positivity
  have hlogR : ∀ᶠ W : Real in atTop,
      4 * Real.log W ^ (3 : Real) ≤ W ^ (θ / 2) := by
    have hsmall := (Asymptotics.isLittleO_iff_nat_mul_le'.1
      (isLittleO_log_rpow_rpow_atTop (3 : Real) ha)) 4
    filter_upwards [hsmall, eventually_ge_atTop 1] with W hsmall hW1
    have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ W) _)] using hsmall
  have hlog := (Step2.tendsto_W B).eventually hlogR
  have hexp := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 4 ha)
  have hfour := ((tendsto_rpow_atTop ha).comp
    (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [hlog, hexp, hfour, B.dim, eventually_ge_atTop 1]
    with N hlogN hexpN hfourN hdim hN u
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : Real) < B.W N := by linarith
  have hWN : (B.W N : Real) ≤ N := by
    have hL1 : (1 : Real) ≤ B.L N := by exact_mod_cast B.one_le_L N
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hell : (1 : Real) ≤ B.ell N (u : Real) :=
    one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans u.2.1)
      (u.2.2.trans_lt (ht1 N))
  have hlog0 : 0 ≤ Real.log (B.W N : Real) := Real.log_nonneg hW1
  have hfourN' : (4 : Real) ≤ (B.W N : Real) ^ (θ / 2) := by
    simpa only [Function.comp_apply] using hfourN
  have hpoly : 2 * Real.log (B.W N : Real) ^ (3 : Real) +
      2 / B.ell N (u : Real) ≤ (B.W N : Real) ^ (θ / 2) := by
    have hdiv : 2 / B.ell N (u : Real) ≤ 2 :=
      (div_le_iff₀ (by linarith)).2 (by nlinarith)
    nlinarith [hlogN, hfourN']
  have hexp' : Real.exp (4 * Real.log (B.W N : Real) ^ (3 / 4 : Real)) ≤
      (B.W N : Real) ^ (θ / 2) := by
    simpa only [one_mul] using hexpN
  calc
    _ ≤ (B.W N : Real) ^ (θ / 2) * (B.W N : Real) ^ (θ / 2) := by
      unfold Lemma57.cNear2
      exact mul_le_mul hpoly hexp' (Real.exp_pos _).le
        (Real.rpow_nonneg hW0.le _)
    _ = (B.W N : Real) ^ θ := by
      rw [← Real.rpow_add hW0]
      congr 1
      ring
    _ ≤ (N : Real) ^ θ := Real.rpow_le_rpow hW0.le hWN hθ.le


private theorem scale_le_N (hE : |E| < 2) {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {N : Nat} (hdim : B.W N * B.L N ≤ N) (u : TimeIcc s t N) :
    B.scale E N (u : Real) ≤ (N : Real) := by
  obtain ⟨_, _, _, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hdim
  change (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) ≤ (N : Real)
  calc
    _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
    _ = (B.W N : Real) * (B.L N : Real) := by ring
    _ ≤ (N : Real) := hWL

private theorem eventually_Qexact_le_absorbed
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {zetaSrc tauG deltaCap : Real}
    (hsrc : 0 < zetaSrc) (htau : 0 < tauG) (hcap : 0 < deltaCap)
    (hsrcTau : zetaSrc ≤ tauG)
    (htauCap : tauG ≤ deltaCap / 16) (hcapC : deltaCap ≤ c / 20) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N) (APrimeGeneralMovingQVNormBudget.endpoint s t D N k),
      ∀ a : LoopArg (d.L N) 2,
        APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG deltaCap N k a u ≤
          (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u
            (APrimeGeneralMovingQVNormBudget.endpoint s t D N k) D
            (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u)
            a) ^ 2 := by
  have hquad := APrimeGeneralMovingQVAbsorption.eventually_quadratic_source_comparison
    hE hs0 hst ht1 hc hreg hsrc htau hcap hsrcTau htauCap hcapC
  have hscale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hquad, hscale, B.dim, hNW, eventually_ge_atTop 1]
    with N hquadN hscaleN hdimN hNWN hN
  intro k hk u hu a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let Jbar := APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans hv.2 |>.trans_lt (ht1 N)
  have hellu : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hells : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
      ((hst N).trans_lt (ht1 N))
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hA : 1 ≤ B.scale E N u :=
    (Real.one_le_rpow hNr hc.le).trans (hscaleN uu).1
  have hAN : B.scale E N u ≤ (N : Real) :=
    scale_le_N hE hs0 ht1 hdimN.1 uu
  have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
    exact_mod_cast hdimN.1
  have heta1 : etaT E u ≤ 1 := etaT_le_one hE hu0
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hleak : (B.W N : Real) * (B.L N : Real) *
      (B.W N : Real) ^ (-D) ≤ (etaT E u)⁻¹ * (B.scale E N u)⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hNr
      (lt_of_lt_of_le zero_lt_one hA) heta hWL hAN hNWN heta1 (by linarith)
  have hJ1 : (1 : Real) ≤ Jbar := by
    dsimp [Jbar, APrimeGeneralMovingQVProfile.generalMovingBlockCap]
    apply le_add_of_nonneg_right
    positivity
  have hfar := APrimeGeneralMovingQVAbsorption.diagFarRate_source_le_absorbed
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u)
    (D := D) (J := Jbar) hN hells hellu heta hA hJ1
    (hquadN uu) hleak
  have hroot := APrimeGeneralMovingQVAbsorption.normalized_rootProfile_le_absorbed
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u)
    (v := v) (D := D) (J := Jbar) hE hu.1 hu.2
    (hv.2.trans_lt (ht1 N)) hN hells hfar a
  have hscaleInv : 0 ≤
      (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d hE hv.1
      (hv.2.trans_lt (ht1 N)) N a)).le
  have hroot0 : 0 ≤ APrimeFullQV.rootProfile B E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) Jbar
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((B.W N : Real)⁻¹) a :=
    APrimeFirstCellQVFixedTwo.rootProfile_nonneg B E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) Jbar
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((B.W N : Real)⁻¹) a (by positivity)
  have hsq := pow_le_pow_left₀ (mul_nonneg hscaleInv hroot0) hroot 2
  simpa [APrimeGeneralMovingQVNormBudget.Qexact,
    APrimeGeneralMovingQVNormBudget.endpoint, v, Jbar, d, B] using hsq


private theorem margin_to_inv_cubic {A N r e : Real}
    (hA : 0 < A) (hN : 0 < N) (hr : 0 < r)
    (hmargin : N ^ e * r ^ (27 : Real) ≤ A) :
    A ^ (-(1/3 : Real)) ≤ N ^ (-(e/3)) * r ^ (-(9 : Real)) := by
  have hleftpos : 0 < N ^ e * r ^ (27 : Real) := by positivity
  have hp := Real.rpow_le_rpow hleftpos.le hmargin
    (by norm_num : (0 : Real) ≤ 1/3)
  have hleft : (N ^ e * r ^ (27 : Real)) ^ (1/3 : Real) =
      N ^ (e/3) * r ^ (9 : Real) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hr.le _),
      ← Real.rpow_mul hN.le, ← Real.rpow_mul hr.le]
    congr 1 <;> ring
  rw [hleft] at hp
  have hden : 0 < N ^ (e/3) * r ^ (9 : Real) := by positivity
  have hinv := inv_anti₀ hden hp
  rw [Real.rpow_neg hA.le, Real.rpow_neg hN.le, Real.rpow_neg hr.le]
  calc
    (A ^ (1/3 : Real))⁻¹ ≤ (N ^ (e/3) * r ^ (9 : Real))⁻¹ := hinv
    _ = (N ^ (e/3))⁻¹ * (r ^ (9 : Real))⁻¹ := by rw [mul_inv_rev]; ring


private theorem whole_root_square {F near far K L : Real}
    (hn : 0 ≤ near) (hf : 0 ≤ far) :
    (F * (√near * K + √far * L)) ^ 2 ≤
      2 * F ^ 2 * (near * K ^ 2 + far * L ^ 2) := by
  have hsum : (√near * K + √far * L) ^ 2 ≤
      2 * ((√near * K) ^ 2 + (√far * L) ^ 2) := by
    nlinarith [sq_nonneg (√near * K - √far * L)]
  have h := mul_le_mul_of_nonneg_left hsum (sq_nonneg F)
  simp only [mul_pow, Real.sq_sqrt hn, Real.sq_sqrt hf] at h
  nlinarith [h]


private theorem ratio_fifth_le_cube {ellr r : Real}
    (hell : 0 ≤ ellr) (hr : 1 ≤ r) (h : ellr ^ 2 ≤ r) :
    ellr ^ 5 ≤ r ^ 3 := by
  have hellr : ellr ≤ r := by
    have hr2 : r ≤ r ^ 2 := by nlinarith
    nlinarith [sq_nonneg (ellr + r)]
  calc
    ellr ^ 5 = ellr * (ellr ^ 2) ^ 2 := by ring
    _ ≤ r * r ^ 2 := by gcongr
    _ = r ^ 3 := by ring


private theorem absorbed_root_square_split
    (E : Real) (s : Nat → Real) (zetaSrc : Real) (N : Nat)
    (u v D J : Real) (a : LoopArg (d.L N) 2)
    (hW : 1 ≤ (B.W N : Real)) (hell : 0 < B.ell N u)
    (hells : 0 < B.ell N (s N)) (heta : 0 < etaT E u)
    (hA : 0 < B.scale E N u) (hN : 0 ≤ (N : Real)) (hJ : 0 ≤ J) :
    (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D J a) ^ 2 ≤
      2 * (Step2Moment.ratR E s N u ^ (-(2 : Real)) *
        Step2Moment.ratR E s N v ^ (-(2 : Real))) ^ 2 *
        ((APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
          2 * (B.W N : Real)⁻¹) *
          (Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
              (if (zdist (B.L N) (a 0 - a 1) : Real) ≤
                6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0) +
            256 * Real.exp 3 * (B.W N : Real) ^ (-D)) ^ 2 +
          APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u J *
            Step2.xiK (B.L N) (B.W N : Real) (mE E).im ^ 2) := by
  have hnear : 0 ≤ APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
      2 * (B.W N : Real)⁻¹ := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    have hcn := Lemma57.cNear2_nonneg hW hell
    have hratio : 0 ≤ B.ell N u / B.ell N (s N) := by positivity
    positivity
  have hfar : 0 ≤ APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u J := by
    unfold APrimeGeneralMovingQVAbsorption.absorbedFarRate
    positivity
  exact whole_root_square hnear hfar


private theorem strict_uniform_exponent_room {δ c : Real}
    (hδ : 0 < δ) (hc : 100 * δ ≤ c) :
    δ / 3200 + 3 * (δ / 100) < δ / 16 ∧
    2 * (δ / 100) < δ / 16 ∧
    3 * (δ / 1600) + 6 * (δ / 50) + 2 * (δ / 100) - c / 30 <
      δ / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem eta_inv_eq {E u : Real} (hu : u < 1) :
    (etaT E u)⁻¹ = 1 / ((mE E).im * (1 - u)) := by
  rw [Step2.etaT_eq]
  ring

private theorem inverse_ratio_integral_bound {s v m : Real}
    (hs : s < 1) (hsv : s ≤ v) (hv : v < 1) (hm : 0 < m) :
    (∫ u in s..v, APrimeDriftIntegralBudget.powerRate m s (-(1 : Real)) u) ≤
      1 / m := by
  rw [APrimeDriftIntegralBudget.integral_powerRate hs hsv hv hm.ne'
    (by norm_num : (-(1 : Real)) ≠ 0)]
  have hR : 0 ≤ APrimeDriftIntegralBudget.ratio s v ^ (-(1 : Real)) := by
    exact Real.rpow_nonneg (by unfold APrimeDriftIntegralBudget.ratio; positivity) _
  have hrewrite :
      (APrimeDriftIntegralBudget.ratio s v ^ (-(1 : Real)) - 1) /
          (m * (-(1 : Real))) =
      (1 - APrimeDriftIntegralBudget.ratio s v ^ (-(1 : Real))) / m := by ring
  rw [hrewrite]
  exact (div_le_div_iff₀ hm hm).2 (by nlinarith [hR])


private theorem near_kernel_le {Xi W D N eps chi : Real}
    (hXi0 : 0 ≤ Xi) (hXi : Xi ≤ N ^ eps)
    (hW : 1 ≤ W) (hD : 0 ≤ D)
    (hN : 1 ≤ N) (heps : 0 ≤ eps)
    (hchi : 0 ≤ chi) (hchi1 : chi ≤ 1) :
    Xi * chi + 256 * Real.exp 3 * W ^ (-D) ≤
      (1 + 256 * Real.exp 3) * N ^ eps := by
  have hNpow : 1 ≤ N ^ eps := Real.one_le_rpow hN heps
  have hWD : W ^ (-D) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW (by linarith)
  have hXiChi : Xi * chi ≤ Xi := by
    nlinarith [mul_le_mul_of_nonneg_left hchi1 hXi0]
  have hleak : 256 * Real.exp 3 * W ^ (-D) ≤ 256 * Real.exp 3 := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hWD
        (show 0 ≤ 256 * Real.exp 3 by positivity))
  have hconst : 256 * Real.exp 3 ≤ 256 * Real.exp 3 * N ^ eps := by
    nlinarith [mul_le_mul_of_nonneg_left hNpow
      (show 0 ≤ 256 * Real.exp 3 by positivity)]
  nlinarith


private theorem near_source_scalar_le {N ζ eps η c ellr r : Real}
    (hN : 0 < N) (hη : 0 < η) (hc0 : 0 ≤ c)
    (hcn : c ≤ N ^ eps) (hell : 0 ≤ ellr)
    (hr : 1 ≤ r) (hratio : ellr ^ 2 ≤ r) :
    4 * N ^ ζ * η⁻¹ * c * ellr ^ 5 ≤
      4 * N ^ (ζ + eps) * η⁻¹ * r ^ 3 := by
  have hratio5 := ratio_fifth_le_cube hell hr hratio
  have hmul : c * ellr ^ 5 ≤ N ^ eps * r ^ 3 :=
    mul_le_mul hcn hratio5 (pow_nonneg hell _) (by positivity)
  have hfac : 0 ≤ 4 * N ^ ζ * η⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmul hfac
  calc
    4 * N ^ ζ * η⁻¹ * c * ellr ^ 5 =
        (4 * N ^ ζ * η⁻¹) * (c * ellr ^ 5) := by ring
    _ ≤ (4 * N ^ ζ * η⁻¹) * (N ^ eps * r ^ 3) := hscaled
    _ = 4 * N ^ (ζ + eps) * η⁻¹ * r ^ 3 := by
      rw [Real.rpow_add hN]
      ring


private theorem far_scalar_le {A N r J C e t : Real}
    (hA : 0 < A) (hN : 0 < N) (hr : 0 < r)
    (hJ0 : 0 ≤ J) (hC : 0 ≤ C)
    (hmargin : N ^ e * r ^ (27 : Real) ≤ A)
    (hcap : J ≤ C * N ^ t * r ^ (4 : Nat)) :
    A ^ (-(1/3 : Real)) * J ^ (3 : Nat) ≤
      C ^ (3 : Nat) * N ^ (3*t - e/3) * r ^ (3 : Nat) := by
  have hAinv := margin_to_inv_cubic hA hN hr hmargin
  have hJ3 := pow_le_pow_left₀ hJ0 hcap 3
  have hprod := mul_le_mul hAinv hJ3 (pow_nonneg hJ0 3)
    (by positivity : 0 ≤ N ^ (-(e/3)) * r ^ (-(9 : Real)))
  have hNpow : N ^ (-(e/3)) * (N ^ t) ^ (3 : Nat) =
      N ^ (3*t - e/3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_add hN]
    congr 1 <;> ring
  have hrpow : r ^ (-(9 : Real)) * (r ^ (4 : Nat)) ^ (3 : Nat) =
      r ^ (3 : Nat) := by
    rw [← pow_mul, show 4 * 3 = (12 : Nat) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_add hr]
    norm_num
  calc
    A ^ (-(1/3 : Real)) * J ^ (3 : Nat) ≤
      (N ^ (-(e/3)) * r ^ (-(9 : Real))) *
        (C * N ^ t * r ^ (4 : Nat)) ^ (3 : Nat) := hprod
    _ = C ^ (3 : Nat) * N ^ (3*t - e/3) * r ^ (3 : Nat) := by
      rw [mul_pow, mul_pow, ← hNpow, ← hrpow]
      ring


private theorem normalized_factor_near_id {r R : Real}
    (hr : 0 < r) (hR : 0 < R) :
    (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * r ^ 3 =
      r ^ (-(1 : Real)) * R ^ (-(4 : Real)) := by
  rw [Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_neg hR.le,
    Real.rpow_neg hR.le]
  norm_num [Real.rpow_natCast]
  field_simp

private theorem normalized_factor_id {r R : Real}
    (hr : 0 < r) (hR : 0 < R) :
    (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 =
      r ^ (-(4 : Real)) * R ^ (-(4 : Real)) := by
  rw [Real.rpow_neg hr.le, Real.rpow_neg hr.le, Real.rpow_neg hR.le,
    Real.rpow_neg hR.le]
  norm_num [Real.rpow_natCast]
  field_simp


private theorem near_integrand_bound {N r R ζ eps η C near K : Real}
    (hN : 0 < N) (hr : 1 ≤ r) (hR : 0 < R)
    (hη : 0 < η) (hC : 0 ≤ C) (hnear0 : 0 ≤ near) (hK0 : 0 ≤ K)
    (hnear : near ≤ 4 * N ^ (ζ + eps) * η⁻¹ * r ^ 3 + 2)
    (hK : K ≤ C * N ^ eps) :
    (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * near * K ^ 2 ≤
      C ^ 2 * R ^ (-(4 : Real)) *
        (4 * N ^ (ζ + 3*eps) * η⁻¹ * r ^ (-(1 : Real)) +
          2 * N ^ (2*eps)) := by
  have hr0 : 0 < r := by linarith
  have hF0 : 0 ≤ (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 := by positivity
  have hS0 : 0 ≤ 4 * N ^ (ζ + eps) * η⁻¹ * r ^ 3 + 2 := by positivity
  have hK2 := pow_le_pow_left₀ hK0 hK 2
  have hstep : (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * near * K ^ 2 ≤
      (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 *
        (4 * N ^ (ζ + eps) * η⁻¹ * r ^ 3 + 2) * (C * N ^ eps) ^ 2 := by
    gcongr
  have hN1 : N ^ (ζ + eps) * (N ^ eps) ^ 2 = N ^ (ζ + 3*eps) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN]
    congr 1 <;> ring
  have hN2 : (N ^ eps) ^ 2 = N ^ (2*eps) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1 <;> ring
  have hr4 : r ^ (-(4 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr (by norm_num)
  have hrest : C ^ 2 * R ^ (-(4 : Real)) * (2 * N ^ (2*eps) * r ^ (-(4 : Real))) ≤
      C ^ 2 * R ^ (-(4 : Real)) * (2 * N ^ (2*eps)) := by
    have hcoeff : 0 ≤ C ^ 2 * R ^ (-(4 : Real)) * (2 * N ^ (2*eps)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_left hr4 hcoeff]
  calc
    _ ≤ (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 *
        (4 * N ^ (ζ + eps) * η⁻¹ * r ^ 3 + 2) * (C * N ^ eps) ^ 2 := hstep
    _ = C ^ 2 * R ^ (-(4 : Real)) *
        (4 * N ^ (ζ + 3*eps) * η⁻¹ * r ^ (-(1 : Real)) +
          2 * N ^ (2*eps) * r ^ (-(4 : Real))) := by
      calc
        _ = 4 * N ^ (ζ + eps) * η⁻¹ * (C * N ^ eps) ^ 2 *
              ((r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * r ^ 3) +
            2 * (C * N ^ eps) ^ 2 *
              (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 := by ring
        _ = _ := by
          rw [normalized_factor_near_id hr0 hR,
            normalized_factor_id hr0 hR, mul_pow, ← hN1, ← hN2]
          ring
    _ ≤ C ^ 2 * R ^ (-(4 : Real)) *
        (4 * N ^ (ζ + 3*eps) * η⁻¹ * r ^ (-(1 : Real)) +
          2 * N ^ (2*eps)) := by
      nlinarith [hrest]


private theorem far_integrand_bound {N r R e eps η C far Xi : Real}
    (hN : 0 < N) (hr : 0 < r) (hR : 0 < R)
    (hη : 0 < η) (hC : 0 ≤ C) (hfar0 : 0 ≤ far) (hXi0 : 0 ≤ Xi)
    (hfar : far ≤ 1200 * C ^ 3 * N ^ e * η⁻¹ * r ^ 3)
    (hXi : Xi ≤ N ^ eps) :
    (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * far * Xi ^ 2 ≤
      1200 * C ^ 3 * R ^ (-(4 : Real)) *
        N ^ (e + 2*eps) * η⁻¹ * r ^ (-(1 : Real)) := by
  have hF0 : 0 ≤ (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 := by positivity
  have hS0 : 0 ≤ 1200 * C ^ 3 * N ^ e * η⁻¹ * r ^ 3 := by positivity
  have hXi2 := pow_le_pow_left₀ hXi0 hXi 2
  have hstep : (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * far * Xi ^ 2 ≤
      (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 *
        (1200 * C ^ 3 * N ^ e * η⁻¹ * r ^ 3) * (N ^ eps) ^ 2 := by
    gcongr
  have hNid : N ^ e * (N ^ eps) ^ 2 = N ^ (e + 2*eps) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      ← Real.rpow_add hN]
    congr 1 <;> ring
  calc
    _ ≤ (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 *
        (1200 * C ^ 3 * N ^ e * η⁻¹ * r ^ 3) * (N ^ eps) ^ 2 := hstep
    _ = 1200 * C ^ 3 * R ^ (-(4 : Real)) *
        N ^ (e + 2*eps) * η⁻¹ * r ^ (-(1 : Real)) := by
      calc
        _ = 1200 * C ^ 3 * N ^ e * η⁻¹ * (N ^ eps) ^ 2 *
            ((r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * r ^ 3) := by ring
        _ = _ := by rw [normalized_factor_near_id hr hR, ← hNid]; ring


private noncomputable def capConst : Real :=
  3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)

private noncomputable def nearConst : Real := 1 + 256 * Real.exp 3

private theorem capConst_nonneg : 0 ≤ capConst := by
  unfold capConst
  positivity

private theorem nearConst_nonneg : 0 ≤ nearConst := by
  unfold nearConst
  positivity

private theorem eventually_Qabs_pointwise_budget
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {zetaSrc tauG deltaCap eps : Real} (htau : 0 ≤ tauG)
    (hcap : 0 ≤ deltaCap) (heps : 0 < eps) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N) (APrimeGeneralMovingQVNormBudget.endpoint s t D N k),
      ∀ a : LoopArg (d.L N) 2,
        let R := Step2Moment.ratR E s N
          (APrimeGeneralMovingQVNormBudget.endpoint s t D N k)
        let r := Step2Moment.ratR E s N u
        let rate := APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u
        (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u
          (APrimeGeneralMovingQVNormBudget.endpoint s t D N k) D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u)
          a) ^ 2 ≤
          2 * R ^ (-(4 : Real)) *
            (nearConst ^ 2 * (4 * (N : Real) ^ (zetaSrc + 3*eps) * rate +
              2 * (N : Real) ^ (2*eps)) +
             1200 * capConst ^ 3 *
               (N : Real) ^ (3*(tauG+2*deltaCap) - c/30 + 2*eps) * rate) := by
  have hnearEvent := eventually_cNear2_le hs0 ht1 heps
  have hXiEvent := Step2FarInputs.eventually_xiK_le B (mE E).im heps
  have hmargin := hreg.margin hE hst ht1 hc
    (e := c/10) (b := 27) (a := 1) (by positivity) (by norm_num)
    (by field_simp [hc.ne']; norm_num)
  filter_upwards [hnearEvent, hXiEvent, hmargin, eventually_ge_atTop 1]
    with N hnearN hXiN hmarginN hN
  intro k hk u hu a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let r := Step2Moment.ratR E s N u
  let R := Step2Moment.ratR E s N v
  let eta := etaT E u
  let A := B.scale E N u
  let J := APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u
  let Xi := Step2.xiK (B.L N) (B.W N : Real) (mE E).im
  let chi : Real := if (zdist (B.L N) (a 0 - a 1) : Real) ≤
    6 * ellStar (B.W N : Real) (B.ell N v) then 1 else 0
  let K := Xi * chi + 256 * Real.exp 3 * (B.W N : Real) ^ (-D)
  let near := APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
    2 * (B.W N : Real)⁻¹
  let far := APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u J
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans hv.2 |>.trans_lt (ht1 N)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hellu : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hells : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
      ((hst N).trans_lt (ht1 N))
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have heta : 0 < eta := Step2.etaT_pos' hE hu1
  have hr : 1 ≤ r := Step2Moment.one_le_ratR hE hu.1 hu1
  have hR : 1 ≤ R := Step2Moment.one_le_ratR hE hv.1 hv1
  have hrpos : 0 < r := by linarith
  have hRpos : 0 < R := by linarith
  have hA : 0 < A := by
    dsimp only [A]
    rw [B.scale_eq_flowScale]
    exact flowScale_pos (by exact_mod_cast B.W_pos N) (B.one_le_L N) hE hu1
  have hW : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hchi : 0 ≤ chi := by dsimp only [chi]; split_ifs <;> norm_num
  have hchi1 : chi ≤ 1 := by dsimp only [chi]; split_ifs <;> norm_num
  have hXi0 : 0 ≤ Xi := Step2.xiK_nonneg _ _ _
  have hXi : Xi ≤ (N : Real) ^ eps := hXiN
  have hK : K ≤ nearConst * (N : Real) ^ eps := by
    dsimp [K, nearConst]
    exact near_kernel_le hXi0 hXi hW (by linarith) hNr heps.le hchi hchi1
  have hK0 : 0 ≤ K := by
    dsimp [K]
    positivity
  have hEllratio0 : 0 ≤ B.ell N u / B.ell N (s N) := by positivity
  have hEllratio2 : (B.ell N u / B.ell N (s N)) ^ 2 ≤ r := by
    dsimp [r]
    exact Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hu.1 hu1
  have hsource :
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u ≤
        4 * (N : Real) ^ (zetaSrc + eps) * eta⁻¹ * r ^ 3 := by
    unfold APrimeGeneralMovingQVAbsorption.nearSourceRate
    exact near_source_scalar_le hNpos heta
      (Lemma57.cNear2_nonneg hW hellu) (hnearN uu) hEllratio0 hr hEllratio2
  have hWinv : (B.W N : Real)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW
  have hnear : near ≤ 4 * (N : Real) ^ (zetaSrc + eps) * eta⁻¹ * r ^ 3 + 2 := by
    dsimp only [near]
    nlinarith [hsource, hWinv]
  have hnear0 : 0 ≤ near := by
    dsimp [near, APrimeGeneralMovingQVAbsorption.nearSourceRate]
    have hcn := Lemma57.cNear2_nonneg hW hellu
    positivity
  have hmarginUreal : (N : Real) ^ (c/10) * r ^ (27 : Real) ≤ A := by
    change (N : Real) ^ (c/10) *
      (etaT E (s N) / etaT E u) ^ (27 : Real) ≤ B.scale E N u
    simpa only [Real.rpow_one] using hmarginN uu
  have hcapJ : J ≤ capConst * (N : Real) ^ (tauG+2*deltaCap) * r ^ 4 := by
    dsimp [J, capConst, r]
    exact blockCap_le_const hN htau hcap hr
  have hJ0 : 0 ≤ J := by
    dsimp [J, APrimeGeneralMovingQVProfile.generalMovingBlockCap]
    positivity
  have hfarScalar := far_scalar_le hA hNpos hrpos hJ0 capConst_nonneg
    hmarginUreal hcapJ
  have hfar : far ≤ 1200 * capConst ^ 3 *
      (N : Real) ^ (3*(tauG+2*deltaCap) - c/30) * eta⁻¹ * r ^ 3 := by
    have hfac : 0 ≤ 1200 * eta⁻¹ := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hfarScalar hfac
    change 1200 * eta⁻¹ * A ^ (-(1/3 : Real)) * J ^ 3 ≤ _
    calc
      _ = (1200 * eta⁻¹) * (A ^ (-(1/3 : Real)) * J ^ 3) := by ring
      _ ≤ (1200 * eta⁻¹) *
        (capConst ^ 3 * (N : Real) ^ (3*(tauG+2*deltaCap)-c/30) * r ^ 3) :=
          by simpa only [show c / 10 / 3 = c / 30 by ring] using hscaled
      _ = _ := by ring
  have hfar0 : 0 ≤ far := by
    dsimp [far, APrimeGeneralMovingQVAbsorption.absorbedFarRate]
    positivity
  have hnearInt := near_integrand_bound hNpos hr hRpos heta nearConst_nonneg
    hnear0 hK0 hnear hK
  have hfarInt := far_integrand_bound hNpos hrpos hRpos heta capConst_nonneg
    hfar0 hXi0 hfar hXi
  have hsplit := absorbed_root_square_split E s zetaSrc N u v D J a
    hW hellu hells heta hA (by positivity) hJ0
  have hrate : eta⁻¹ * r ^ (-(1 : Real)) =
      APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u := by
    dsimp [eta, r, APrimeDriftIntegralBudget.powerRate]
    rw [ratR_eq_ratio hE, eta_inv_eq hu1]
    ring
  calc
    _ ≤ 2 * ((r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * near * K ^ 2 +
      (r ^ (-(2 : Real)) * R ^ (-(2 : Real))) ^ 2 * far * Xi ^ 2) := by
      convert hsplit using 1 <;> ring
    _ ≤ 2 * (nearConst ^ 2 * R ^ (-(4 : Real)) *
        (4 * (N : Real) ^ (zetaSrc+3*eps) *
            eta⁻¹ * r ^ (-(1 : Real)) +
          2 * (N : Real) ^ (2*eps)) +
        1200 * capConst ^ 3 * R ^ (-(4 : Real)) *
          (N : Real) ^ (3*(tauG+2*deltaCap)-c/30+2*eps) *
          eta⁻¹ * r ^ (-(1 : Real))) := by
      have hsum := add_le_add hnearInt hfarInt
      have hscaled := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : Real) ≤ 2)
      convert hscaled using 1 <;> ring
    _ = _ := by
      rw [← hrate]
      dsimp only [R, v]
      ring


private theorem integral_of_powerRate_envelope
    {Q : Real → Real} {s v m K : Real}
    (hsv : s ≤ v) (hv : v < 1) (hm : 0 < m) (hK : 0 ≤ K)
    (hQi : IntervalIntegrable Q volume s v)
    (hpoint : ∀ u ∈ Icc s v,
      Q u ≤ K * (APrimeDriftIntegralBudget.powerRate m s (-(1 : Real)) u + 1)) :
    (∫ u in s..v, Q u) ≤ K * (1/m + (v-s)) := by
  have hs : s < 1 := hsv.trans_lt hv
  have hri := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
    (q := (-(1 : Real))) hsv hv hm.ne'
  have hdomi : IntervalIntegrable
      (fun u => K * (APrimeDriftIntegralBudget.powerRate m s (-(1 : Real)) u + 1))
      volume s v := (hri.add intervalIntegrable_const).const_mul K
  have hmono := intervalIntegral.integral_mono_on hsv hQi hdomi hpoint
  calc
    (∫ u in s..v, Q u) ≤
      ∫ u in s..v, K *
        (APrimeDriftIntegralBudget.powerRate m s (-(1 : Real)) u + 1) := hmono
    _ = K * ((∫ u in s..v,
          APrimeDriftIntegralBudget.powerRate m s (-(1 : Real)) u) + (v-s)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add hri intervalIntegrable_const,
        intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one]
    _ ≤ K * (1/m + (v-s)) := by
      gcongr
      exact inverse_ratio_integral_bound hs hsv hv hm


private theorem three_rows_le_rate_plus_one {F A B C rate : Real}
    (hF : 0 ≤ F) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hrate : 0 ≤ rate) :
    F * (A * rate + B + C * rate) ≤
      F * (A+B+C) * (rate+1) := by
  have hgap : 0 ≤ F * (A+B+C+B*rate) := by positivity
  nlinarith


private noncomputable def totalConst : Real :=
  2 * (6 * nearConst ^ 2 + 1200 * capConst ^ 3)

private theorem totalConst_nonneg : 0 ≤ totalConst := by
  unfold totalConst
  have hc := capConst_nonneg
  positivity

private theorem eventually_coefficient_le
    {δ e1 e2 e3 : Real} (hδ : 0 < δ)
    (he1 : e1 ≤ δ/16) (he2 : e2 ≤ δ/16) (he3 : e3 ≤ δ/16) :
    ∀ᶠ N : Nat in atTop,
      2 * (nearConst ^ 2 * (4 * (N : Real) ^ e1 + 2 * (N : Real) ^ e2) +
        1200 * capConst ^ 3 * (N : Real) ^ e3) ≤
        (N : Real) ^ (δ/8) := by
  have hgap : 0 < δ/16 := by positivity
  filter_upwards [eventually_le_rpow totalConst hgap,
    eventually_ge_atTop 1] with N hconst hN
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have h1 : (N : Real) ^ e1 ≤ (N : Real) ^ (δ/16) :=
    Real.rpow_le_rpow_of_exponent_le hNr he1
  have h2 : (N : Real) ^ e2 ≤ (N : Real) ^ (δ/16) :=
    Real.rpow_le_rpow_of_exponent_le hNr he2
  have h3 : (N : Real) ^ e3 ≤ (N : Real) ^ (δ/16) :=
    Real.rpow_le_rpow_of_exponent_le hNr he3
  have hcoef :
      2 * (nearConst ^ 2 * (4 * (N : Real) ^ e1 + 2 * (N : Real) ^ e2) +
        1200 * capConst ^ 3 * (N : Real) ^ e3) ≤
        totalConst * (N : Real) ^ (δ/16) := by
    unfold totalConst
    have hc1 : 0 ≤ nearConst ^ 2 := by positivity
    have hc2 : 0 ≤ capConst ^ 3 := by exact pow_nonneg capConst_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 8 * nearConst ^ 2 by positivity),
      mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * nearConst ^ 2 by positivity),
      mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2400 * capConst ^ 3 by positivity)]
  calc
    _ ≤ totalConst * (N : Real) ^ (δ/16) := hcoef
    _ ≤ (N : Real) ^ (δ/16) * (N : Real) ^ (δ/16) := by
      exact mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = (N : Real) ^ (δ/8) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring


private theorem eventually_Qexact_integral_budget
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {zetaSrc tauG deltaCap eps : Real}
    (hsrc : 0 < zetaSrc) (htau : 0 < tauG) (hcap : 0 < deltaCap)
    (heps : 0 < eps) (hsrcTau : zetaSrc ≤ tauG)
    (htauCap : tauG ≤ deltaCap / 16) (hcapC : deltaCap ≤ c / 20) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
        let R := Step2Moment.ratR E s N v
        let coeff := 2 * (nearConst ^ 2 *
          (4 * (N : Real) ^ (zetaSrc+3*eps) + 2 * (N : Real) ^ (2*eps)) +
          1200 * capConst ^ 3 *
            (N : Real) ^ (3*(tauG+2*deltaCap)-c/30+2*eps))
        (∫ u in s N..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG deltaCap N k a u) ≤
          R ^ (-(4 : Real)) * coeff * (1 / (mE E).im + (v-s N)) := by
  have hQ := eventually_Qexact_le_absorbed hE hD hs0 hst ht1 hc hreg
    hsrc htau hcap hsrcTau htauCap hcapC
  have hP := eventually_Qabs_pointwise_budget (zetaSrc := zetaSrc)
    hE hD hs0 hst ht1 hc hreg htau.le hcap.le heps
  filter_upwards [hQ, hP, eventually_ge_atTop 1] with N hQN hPN hN
  intro k hk a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let R := Step2Moment.ratR E s N v
  let e1 := zetaSrc + 3*eps
  let e2 := 2*eps
  let e3 := 3*(tauG+2*deltaCap)-c/30+2*eps
  let coeff := 2 * (nearConst ^ 2 *
    (4 * (N : Real) ^ e1 + 2 * (N : Real) ^ e2) +
    1200 * capConst ^ 3 * (N : Real) ^ e3)
  let K := R ^ (-(4 : Real)) * coeff
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hR : 0 < R := by
    exact Step2Moment.ratR_pos hE (hv.1.trans_lt hv1) hv1
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    have hc := capConst_nonneg
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQi := APrimeGeneralMovingQVNormBudget.intervalIntegrable_Qexact
    (zetaSrc := zetaSrc) (tauG := tauG) (delta := deltaCap)
    hE hs0 hst ht1 hk a
  have hpoint : ∀ u ∈ Icc (s N) v,
      APrimeGeneralMovingQVNormBudget.Qexact E D s t zetaSrc tauG deltaCap N k a u ≤
        K * (APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u + 1) := by
    intro u hu
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hrate : 0 ≤ APrimeDriftIntegralBudget.powerRate (mE E).im (s N)
        (-(1 : Real)) u :=
      (APrimeDriftIntegralBudget.powerRate_pos hm (hv.1.trans_lt hv1) hu1).le
    have hrows := three_rows_le_rate_plus_one
      (F := 2 * R ^ (-(4 : Real)))
      (A := nearConst ^ 2 * (4 * (N : Real) ^ e1))
      (B := nearConst ^ 2 * (2 * (N : Real) ^ e2))
      (C := 1200 * capConst ^ 3 * (N : Real) ^ e3)
      (rate := APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u)
      (by positivity) (by positivity) (by positivity)
      (by have hc := capConst_nonneg; positivity) hrate
    calc
      _ ≤ (APrimeGeneralMovingQVAbsorption.absorbedRootProfile E s zetaSrc N u v D
          (APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG deltaCap N u) a) ^ 2 :=
        hQN k hk u hu a
      _ ≤ 2 * R ^ (-(4 : Real)) *
        (nearConst ^ 2 * (4 * (N : Real) ^ e1 *
            APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u +
          2 * (N : Real) ^ e2) +
         1200 * capConst ^ 3 * (N : Real) ^ e3 *
           APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u) := by
        simpa only [v, R, e1, e2, e3] using hPN k hk u hu a
      _ ≤ K * (APrimeDriftIntegralBudget.powerRate (mE E).im (s N) (-(1 : Real)) u + 1) := by
        convert hrows using 1 <;> simp only [K, coeff, e1, e2, e3] <;> ring
  have hbound := integral_of_powerRate_envelope hv.1 hv1 hm hK hQi hpoint
  simpa only [v, R, coeff, e1, e2, e3, K] using hbound


private theorem eventually_R4_le_N_two_fifteenths
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      (Step2Moment.ratR E s N
        (APrimeGeneralMovingQVNormBudget.endpoint s t D N k)) ^ 4 ≤
        (N : Real) ^ (2/15 : Real) := by
  have hmargin := hreg.margin hE hst ht1 hc
    (e := 0) (b := 30) (a := 1) (by norm_num) (by norm_num)
    (by field_simp [hc.ne']; norm_num)
  filter_upwards [hmargin, B.dim, eventually_ge_atTop 1]
    with N hmarginN hdim hN
  intro k hk
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  let vv : TimeIcc s t N := ⟨v, hv⟩
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hv.1.trans_lt (hv.2.trans_lt (ht1 N)))
      (hv.2.trans_lt (ht1 N))
  have hR30 : (Step2Moment.ratR E s N v) ^ (30 : Real) ≤ B.scale E N v := by
    have h := hmarginN vv
    simpa only [zero_div, zero_add, one_div, div_self hc.ne', zero_add,
      Real.rpow_zero, one_mul, Real.rpow_one, Step2Moment.ratR] using h
  have hAN : B.scale E N v ≤ (N : Real) :=
    scale_le_N hE hs0 ht1 hdim.1 vv
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hRpos.le _)
    (hR30.trans hAN) (by norm_num : (0 : Real) ≤ 2/15)
  have hid : ((Step2Moment.ratR E s N v) ^ (30 : Real)) ^ (2/15 : Real) =
      (Step2Moment.ratR E s N v) ^ 4 := by
    rw [← Real.rpow_mul hRpos.le]
    norm_num
  simpa only [v, hid] using hpow


private theorem complement_le_slot_scale {N R δ : Real}
    (hN : 1 ≤ N) (hR : 1 ≤ R) (hδ : 0 < δ)
    (hR4 : R ^ (4 : Nat) ≤ N ^ (2/15 : Real)) :
    N ^ (-(1 : Real)) ≤ R ^ (-(4 : Real)) * N ^ (3*δ/16) := by
  have hNpos : 0 < N := by linarith
  have hRpos : 0 < R := by linarith
  have hexp : N ^ (2/15 : Real) ≤ N ^ (1+3*δ/16) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hNid : N ^ (1+3*δ/16) = N * N ^ (3*δ/16) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  have hmul : N ^ (-(1 : Real)) * R ^ (4 : Nat) ≤ N ^ (3*δ/16) := by
    have hbound := hR4.trans (hexp.trans_eq hNid)
    rw [Real.rpow_neg hNpos.le, Real.rpow_one, mul_comm, ← div_eq_mul_inv]
    exact (div_le_iff₀ hNpos).2 (by nlinarith [hbound])
  have hfinal := (le_div_iff₀ (pow_pos hRpos 4)).2 hmul
  calc
    _ ≤ N ^ (3*δ/16) / R ^ (4 : Nat) := hfinal
    _ = R ^ (-(4 : Real)) * N ^ (3*δ/16) := by
      rw [Real.rpow_neg hRpos.le]
      norm_num [Real.rpow_natCast]
      ring


-- The endpoint proof combines two large eventual estimates and needs extra
-- elaboration time; the limit is local to this theorem.
set_option maxHeartbeats 1000000 in
/-- The exact T591 deterministic profile plus its paid `β=1` complement
fits a single N2 squared budget, uniformly over every cut-net cell. -/
theorem eventually_Qexact_plus_complement_le
    {E D c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hδ : 0 < δ) (hsmall : δ ≤ min 1 (c/100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
        let R := Step2Moment.ratR E s N v
        (∫ u in s N..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) +
          (v-s N) * (N : Real) ^ (-(1 : Real)) ≤
          2 * R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16) := by
  let ζ := APrimeGeneralMovingSlotLossSchedule.zetaSrc δ
  let τ := APrimeGeneralMovingSlotLossSchedule.tauG δ
  let cap := APrimeGeneralMovingSlotLossSchedule.deltaCap δ
  let eps := δ/100
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hsmall
  rcases hroom with ⟨_, _, hcap0, htau0, hζ0, _, _, hζτ, hτcap, hcapC, _, _, _⟩
  have hζ : 0 < ζ := hζ0
  have hτ : 0 < τ := htau0
  have hcap' : 0 < cap := hcap0
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hδc : 100 * δ ≤ c := by
    have hh := hsmall.trans (min_le_right _ _)
    linarith
  have hExp := strict_uniform_exponent_room hδ hδc
  have he1 : ζ + 3*eps ≤ δ/16 := by
    dsimp [ζ, eps, APrimeGeneralMovingSlotLossSchedule.zetaSrc]
    exact hExp.1.le
  have he2 : 2*eps ≤ δ/16 := hExp.2.1.le
  have he3 : 3*(τ+2*cap)-c/30+2*eps ≤ δ/16 := by
    dsimp [τ, cap, eps, APrimeGeneralMovingSlotLossSchedule.tauG,
      APrimeGeneralMovingSlotLossSchedule.deltaCap]
    convert hExp.2.2.le using 1 <;> ring
  have hInt := eventually_Qexact_integral_budget hE hD hs0 hst ht1 hc hreg
    hζ hτ hcap' heps hζτ hτcap hcapC
  have hCoeff := eventually_coefficient_le hδ he1 he2 he3
  have hm : 0 < (mE E).im := mE_im_pos hE
  have hgap : 0 < δ/16 := by positivity
  have hConst := eventually_le_rpow (1/(mE E).im+1) hgap
  have hR4 := eventually_R4_le_N_two_fifteenths (D := D)
    hE hs0 hst ht1 hc hreg
  filter_upwards [hInt, hCoeff, hConst, hR4, eventually_ge_atTop 1]
    with N hIntN hCoeffN hConstN hR4N hN
  intro k hk a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let R := Step2Moment.ratR E s N v
  let coeff : Real := 2 * (nearConst ^ 2 *
    (4 * (N : Real) ^ (ζ+3*eps) + 2 * (N : Real) ^ (2*eps)) +
    1200 * capConst ^ 3 * (N : Real) ^ (3*(τ+2*cap)-c/30+2*eps))
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hlen0 : 0 ≤ v-s N := sub_nonneg.mpr hv.1
  have hlen1 : v-s N ≤ 1 := by linarith [hs0 N, hv.2, ht1 N]
  have hRpos : 0 < R := Step2Moment.ratR_pos hE
    (hv.1.trans_lt (hv.2.trans_lt (ht1 N))) (hv.2.trans_lt (ht1 N))
  have hR1 : 1 ≤ R := Step2Moment.one_le_ratR hE hv.1 (hv.2.trans_lt (ht1 N))
  have hCoeffBd : coeff ≤ (N : Real) ^ (δ/8) := by
    simpa only [coeff, ζ, τ, cap, eps] using hCoeffN
  have hIntBd :
      (∫ u in s N..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t ζ τ cap N k a u) ≤
        R ^ (-(4 : Real)) * coeff * (1/(mE E).im+(v-s N)) := by
    simpa only [v, R, coeff, ζ, τ, cap, eps] using hIntN k hk a
  have hlength : 1/(mE E).im+(v-s N) ≤ (N : Real) ^ (δ/16) := by
    linarith [hConstN]
  have hIntSmall :
      (∫ u in s N..v,
          APrimeGeneralMovingQVNormBudget.Qexact E D s t ζ τ cap N k a u) ≤
        R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16) := by
    have hcoeff0 : 0 ≤ coeff := by
      dsimp [coeff]
      have hc := capConst_nonneg
      positivity
    have hRinv : 0 ≤ R ^ (-(4 : Real)) := by positivity
    have hlength0 : 0 ≤ 1/(mE E).im+(v-s N) := by
      have : 0 ≤ 1/(mE E).im := by positivity
      linarith
    have hbound : coeff * (1/(mE E).im+(v-s N)) ≤
        (N : Real) ^ (δ/8) * (N : Real) ^ (δ/16) := by
      calc
        _ ≤ (N : Real) ^ (δ/8) * (1/(mE E).im+(v-s N)) :=
          mul_le_mul_of_nonneg_right hCoeffBd hlength0
        _ ≤ _ := mul_le_mul_of_nonneg_left hlength (by positivity)
    have hpow : (N : Real) ^ (δ/8) * (N : Real) ^ (δ/16) =
        (N : Real) ^ (3*δ/16) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    calc
      _ ≤ R ^ (-(4 : Real)) * coeff * (1/(mE E).im+(v-s N)) := hIntBd
      _ = R ^ (-(4 : Real)) *
          (coeff * (1/(mE E).im+(v-s N))) := by ring
      _ ≤ R ^ (-(4 : Real)) *
          ((N : Real) ^ (δ/8) * (N : Real) ^ (δ/16)) :=
        mul_le_mul_of_nonneg_left hbound hRinv
      _ = _ := by rw [hpow]
  have hcomp : (v-s N) * (N : Real) ^ (-(1 : Real)) ≤
      R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16) := by
    have hR4N := hR4N k hk
    have hbase := complement_le_slot_scale hNr hR1 hδ hR4N
    have hpow0 : 0 ≤ (N : Real) ^ (-(1 : Real)) := by positivity
    nlinarith
  have hsum := add_le_add hIntSmall hcomp
  simpa only [ζ, τ, cap, v, R] using (show
    (∫ u in s N..v,
        APrimeGeneralMovingQVNormBudget.Qexact E D s t ζ τ cap N k a u) +
      (v-s N) * (N : Real) ^ (-(1 : Real)) ≤
      2 * R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16) by nlinarith [hsum])

private theorem small_slot_tail_lower {x R : Real}
    (hx : 0 < x) (hR : 0 < R) :
    x ^ (5/4 : Real) * R ^ (-(2 : Real)) ≤
      APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
  have hprod : x * APrimeInit.slotKappa' x = x ^ (5/4 : Real) := by
    unfold APrimeInit.slotKappa'
    calc
      x * x ^ (1/4 : Real) = x ^ (1 : Real) * x ^ (1/4 : Real) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : Real) + 1/4) := (Real.rpow_add hx 1 (1/4)).symm
      _ = x ^ (5/4 : Real) := by norm_num
  have hκ := APrimeSlotArith.tailTerm_ge_kappa
    (x := x) (R := R) (κ := APrimeInit.slotKappa' x) hx.le
  have hid : x ^ (5/4 : Real) * R ^ (-(2 : Real)) =
      (x * R ^ (2 : Nat) * APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
    rw [Real.rpow_neg hR.le, ← hprod]
    field_simp <;> ring <;> norm_num [Real.rpow_natCast]
  rw [hid]
  exact div_le_div_of_nonneg_right hκ (by positivity)

-- The fixed-moment conversion unfolds the exact integral profile again, so
-- keep the larger elaboration limit local to this theorem.
set_option maxHeartbeats 1000000 in
/-- The literal T591 profile and its `β=1` complement occupy the small
`κ=x^(1/4)` N2 slot for each fixed moment order. -/
theorem eventually_Qexact_N2_slot
    {E D c δ : Real} {s t : Nat → Real} {p : Nat}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hδ : 0 < δ) (hsmall : δ ≤ min 1 (c/100)) (hp : 1 ≤ p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ a : LoopArg (d.L N) 2,
        let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
        let R := Step2Moment.ratR E s N v
        let x := (N : Real) ^ (δ/8)
        Real.sqrt ((2 * (p : Real) - 1) *
          ((∫ u in s N..v,
            APrimeGeneralMovingQVNormBudget.Qexact E D s t
              (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
              (APrimeGeneralMovingSlotLossSchedule.tauG δ)
              (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) +
            (v-s N) * (N : Real) ^ (-(1 : Real)))) ≤
          APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) := by
  have hbudget := eventually_Qexact_plus_complement_le hE hD hs0 hst ht1 hc
    hreg hδ hsmall
  have hpReal : (1 : Real) ≤ p := by exact_mod_cast hp
  have hfactor0 : 0 ≤ 2 * (p : Real) - 1 := by linarith
  have hfactor := eventually_le_rpow (2 * (2 * (p : Real) - 1))
    (show 0 < δ/8 by positivity)
  filter_upwards [hbudget, hfactor, eventually_ge_atTop 1]
    with N hbudgetN hfactorN hN
  intro k hk a
  let v := APrimeGeneralMovingQVNormBudget.endpoint s t D N k
  let R := Step2Moment.ratR E s N v
  let x := (N : Real) ^ (δ/8)
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hx : 0 < x := by dsimp [x]; positivity
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hR : 0 < R := Step2Moment.ratR_pos hE
    (hv.1.trans_lt (hv.2.trans_lt (ht1 N))) (hv.2.trans_lt (ht1 N))
  let S : Real :=
    (∫ u in s N..v,
      APrimeGeneralMovingQVNormBudget.Qexact E D s t
        (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N k a u) +
      (v-s N) * (N : Real) ^ (-(1 : Real))
  have hS : S ≤ 2 * R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16) := by
    simpa only [S, v, R] using hbudgetN k hk a
  have hfactorN' : 2 * (2 * (p : Real) - 1) ≤ (N : Real) ^ (δ/8) := hfactorN
  have hpow0 : (N : Real) ^ (5*δ/32) * R ^ (-(2 : Real)) ≥ 0 := by
    positivity
  have hpow : ((N : Real) ^ (5*δ/32) * R ^ (-(2 : Real))) ^ 2 =
      R ^ (-(4 : Real)) * (N : Real) ^ (5*δ/16) := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hNpos.le, ← Real.rpow_mul hR.le]
    have he1 : (5*δ/32) * (2 : Real) = 5*δ/16 := by ring
    norm_num only [Nat.cast_ofNat]
    rw [he1]
    ring
  have hq : (2 * (p : Real) - 1) * S ≤
      ((N : Real) ^ (5*δ/32) * R ^ (-(2 : Real))) ^ 2 := by
    rw [hpow]
    have hbase : 0 ≤ R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hS hfactor0
    have hmul2 := mul_le_mul_of_nonneg_right hfactorN' hbase
    have hpow' : (N : Real) ^ (δ/8) *
        (R ^ (-(4 : Real)) * (N : Real) ^ (3*δ/16)) =
        R ^ (-(4 : Real)) * (N : Real) ^ (5*δ/16) := by
      calc
        _ = R ^ (-(4 : Real)) *
            ((N : Real) ^ (δ/8) * (N : Real) ^ (3*δ/16)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
    rw [← hpow']
    nlinarith [hmul, hmul2]
  have hslot := small_slot_tail_lower hx hR
  have hxpow : x ^ (5/4 : Real) = (N : Real) ^ (5*δ/32) := by
    dsimp [x]
    rw [← Real.rpow_mul hNpos.le]
    congr 1
    ring
  rw [hxpow] at hslot
  simpa only [S, v, R, x] using
    (show Real.sqrt ((2 * (p : Real) - 1) * S) ≤
      APrimeOneStep.tailTerm x R (APrimeInit.slotKappa' x) / R ^ (4 : Nat) by
      calc
        _ ≤ Real.sqrt (((N : Real) ^ (5*δ/32) * R ^ (-(2 : Real))) ^ 2) :=
          Real.sqrt_le_sqrt hq
        _ = (N : Real) ^ (5*δ/32) * R ^ (-(2 : Real)) :=
          Real.sqrt_sq_eq_abs _ |>.trans (abs_of_nonneg hpow0)
        _ ≤ _ := hslot)

end
end RBM.APrimeGeneralMovingQVSlotFit
