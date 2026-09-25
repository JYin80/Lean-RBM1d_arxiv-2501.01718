/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftNearMainSlot
import RBM1D.Gauss.APrimeGeneralMovingDriftNearTailSlot
import RBM1D.Gauss.APrimeGeneralMovingQVProfile
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.APrimeDriftIntegralBudget

/-!
T1293 proves the two literal T615 near-source rows at a corrected common loss
schedule. The source, center, and gradient losses equal lam / 1000; the actual
weight and buffer losses equal lam, and the cap loss is 2 * lam. The endpoint
ratR(v)^(-2) factor is retained in both integrated bounds.
-/

namespace RBM.APrimeFreeLossNear

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def actualWeightLoss (lam : Real) : Real := lam
noncomputable def bufferLoss (lam : Real) : Real := lam
noncomputable def capLoss (lam : Real) : Real := 2 * lam
noncomputable def hLoss (lam : Real) : Real := lam / 1000
noncomputable def sourceLoss (lam : Real) : Real := hLoss lam
noncomputable def centerLoss (lam : Real) : Real := hLoss lam
noncomputable def gradientLoss (lam : Real) : Real := hLoss lam
noncomputable def scalarEpsilonLoss (lam : Real) : Real := hLoss lam

noncomputable abbrev normalizedNearMain :=
  APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
noncomputable abbrev normalizedNearTail :=
  APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail

private theorem floor_le_N_inv_thirty {N W D : Real}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N ≤ W ^ 2) (hD : 60 ≤ D) :
    W ^ (-D) ≤ N ^ (-(30 : Real)) := by
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (30 : Nat) ≤ (W^2) ^ (30 : Nat) :=
    pow_le_pow_left₀ hN0.le hNW 30
  have hpos : 0 < N ^ (30 : Nat) := by positivity
  have hinv := (inv_anti₀ hpos hpow)
  have heq : W ^ (-(60 : Real)) = ((W^2) ^ (30 : Nat))⁻¹ := by
    rw [Real.rpow_neg hW0.le]
    congr 1
    rw [← pow_mul]
    norm_num
  calc
    W ^ (-D) ≤ W ^ (-(60 : Real)) :=
      Real.rpow_le_rpow_of_exponent_le hW (by linarith)
    _ = ((W^2) ^ (30 : Nat))⁻¹ := heq
    _ ≤ (N ^ (30 : Nat))⁻¹ := hinv
    _ = N ^ (-(30 : Real)) := by
      rw [Real.rpow_neg hN0.le]
      norm_cast

private theorem residual_crude {N W D ζ Xi Ru Rv L J ell r X T : Real}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hWN : W ≤ N) (hRv : 0 < Rv)
    (hRu : 1 ≤ Ru) (_hXi0 : 0 ≤ Xi) (hXi : Xi ≤ N)
    (_hζ0 : 0 ≤ N ^ ζ) (hζ : N ^ ζ ≤ N)
    (hL0 : 0 ≤ L) (hL : L ≤ N) (hJ0 : 0 ≤ J) (hJ : J ≤ N)
    (hell0 : 0 ≤ ell) (hell : ell ≤ N) (hr0 : 0 ≤ r) (hr : r ≤ N)
    (hX0 : 0 ≤ X) (hX : X ≤ N) (hT0 : 0 ≤ T)
    (hT : T ≤ 2 * W ^ (-D)) :
    4 * Xi * Ru ^ (-2 : Real) * Rv ^ (-2 : Real) *
        (N ^ ζ * L * J * W ^ 2 * ell * r * X * T) ≤
      8 * N ^ (9 : Nat) * W ^ (-D) * Rv ^ (-2 : Real) := by
  have hRuInv : Ru ^ (-2 : Real) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hRu (by norm_num)
  have hRuInv0 : 0 ≤ Ru ^ (-2 : Real) := Real.rpow_nonneg (by linarith) _
  have hRvInv0 : 0 ≤ Rv ^ (-2 : Real) := Real.rpow_nonneg hRv.le _
  have hW2 : W ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by linarith) hWN 2
  have hfloor0 : 0 ≤ W ^ (-D) := Real.rpow_nonneg (by linarith) _
  calc
    _ ≤ 4 * N * 1 * Rv ^ (-2 : Real) *
        (N * N * N * N ^ 2 * N * N * N * (2 * W ^ (-D))) := by
          gcongr
    _ = 8 * N ^ (9 : Nat) * W ^ (-D) * Rv ^ (-2 : Real) := by ring

theorem corrected_schedule_identities (lam : Real) :
    actualWeightLoss lam = lam /\
    bufferLoss lam = lam /\
    capLoss lam = actualWeightLoss lam + bufferLoss lam /\
    sourceLoss lam = lam / 1000 /\
    centerLoss lam = lam / 1000 /\
    gradientLoss lam = lam / 1000 /\
    scalarEpsilonLoss lam = lam / 1000 := by
  simp [actualWeightLoss, bufferLoss, capLoss, hLoss, sourceLoss,
    centerLoss, gradientLoss, scalarEpsilonLoss]
  <;> ring

/-- This is the literal T615 near-source split, with both transport factors
and the local residual definition tied back to the producer. -/
theorem literal_near_source_split (E D : Real) (s : Nat -> Real)
    (zetaSrc zetaCtr tauG deltaCap : Real) (N : Nat) (v u : Real) :
    Step2.xiK (d.L N) (d.W N) (mE E).im *
      (Step2Moment.ratR E s N u) ^ (-2 : Real) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) *
      APrimeGeneralMovingDriftAtProfile.nearSourceCoeff E D s
        zetaSrc zetaCtr tauG deltaCap N u =
    normalizedNearMain E s zetaSrc zetaCtr N v u +
      normalizedNearTail E D s zetaCtr tauG deltaCap N v u := by
  simpa [normalizedNearMain, normalizedNearTail,
    APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain] using
    APrimeGeneralMovingDriftNearTailSlot.near_source_split E D s
      zetaSrc zetaCtr tauG deltaCap N v u

private theorem integral_ratR_eta_inv_neg_half
    {E s0 v : Real} (hE : |E| < 2) (hs0 : s0 ≤ v) (hv1 : v < 1) :
    (∫ u in s0..v,
        APrimeDriftIntegralBudget.ratio s0 u ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) ≤ 2 / (mE E).im := by
  have hs1 : s0 < 1 := hs0.trans_lt hv1
  have hm := mE_im_pos hE
  have hq : (-(1 / 2 : Real)) ≠ 0 := by norm_num
  have hi := APrimeDriftIntegralBudget.integral_ratio_power
    hs1 hs0 hv1 hm.ne' hq
  have hfun : (fun u => APrimeDriftIntegralBudget.ratio s0 u ^ (-(1 / 2 : Real)) *
      (etaT E u)⁻¹) =
      (fun u => APrimeDriftIntegralBudget.ratio s0 u ^ (-(1 / 2 : Real)) /
        ((mE E).im * (1 - u))) := by
    funext u
    rw [Step2.etaT_eq]
    field_simp [ne_of_gt hm]
    <;> ring
  rw [hfun, hi]
  have hR1 : 1 ≤ APrimeDriftIntegralBudget.ratio s0 v := by
    unfold APrimeDriftIntegralBudget.ratio
    rw [le_div_iff₀ (by linarith : 0 < 1 - v)]
    linarith
  have hR0 : 0 < APrimeDriftIntegralBudget.ratio s0 v := zero_lt_one.trans_le hR1
  have hpow0 : 0 ≤ APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) :=
    Real.rpow_nonneg hR0.le _
  have heq :
      (APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) - 1) /
          ((mE E).im * (-(1 / 2 : Real))) =
        2 / (mE E).im -
          2 * APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) /
            (mE E).im := by
    field_simp [hm.ne']
    ring
  rw [heq]
  have hsub : 0 ≤
      2 * APrimeDriftIntegralBudget.ratio s0 v ^ (-(1 / 2 : Real)) /
        (mE E).im := by positivity
  linarith

private theorem ratio_cube_normalized_le
    {r R : Real} (hr : 0 ≤ r) (hR : 0 < R) (hR1 : 1 ≤ R) (h : r ^ 2 ≤ R) :
    r ^ 3 * R ^ (-2 : Real) ≤ R ^ (-(1 / 2 : Real)) := by
  have hRnonneg : 0 ≤ R := hR.le
  have hsqrt : r ≤ R ^ (1 / 2 : Real) := by
    have hsq : r ≤ Real.sqrt R := by
      rw [Real.le_sqrt hr hRnonneg]
      simpa [pow_two] using h
    simpa [Real.sqrt_eq_rpow] using hsq
  have hcube : r ^ 3 ≤ R ^ (3 / 2 : Real) := by
    have hpow := pow_le_pow_left₀ hr hsqrt 3
    have hright : (R ^ (1 / 2 : Real)) ^ (3 : Nat) = R ^ (3 / 2 : Real) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hRnonneg]
      congr 1
      ring
    exact le_trans hpow (le_of_eq hright)
  calc
    r ^ 3 * R ^ (-2 : Real) ≤ R ^ (3 / 2 : Real) * R ^ (-2 : Real) :=
      mul_le_mul_of_nonneg_right hcube (Real.rpow_nonneg hR.le _)
    _ = R ^ (-(1 / 2 : Real)) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring

private theorem ratR_eq_ratio {E : Real} {s : Nat → Real} {N : Nat} {u : Real}
    (hE : |E| < 2) :
    Step2Moment.ratR E s N u = APrimeDriftIntegralBudget.ratio (s N) u := by
  unfold Step2Moment.ratR APrimeDriftIntegralBudget.ratio
  rw [Step2.etaT_ratio hE]

private theorem eventually_cNear_le {s t : Nat → Real}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {theta : Real} (htheta : 0 < theta) :
    ∀ᶠ N : Nat in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      Lemma57.cNear (d.W N : Real) (B.ell N u) ≤ (N : Real) ^ theta := by
  have ha : 0 < theta / 4 := by positivity
  have hlogR : ∀ᶠ W : Real in atTop,
      4 * Real.log W ^ (3 : Real) ≤ W ^ (theta / 4) := by
    have hsmall := (Asymptotics.isLittleO_iff_nat_mul_le'.1
      (isLittleO_log_rpow_rpow_atTop (3 : Real) ha)) 4
    filter_upwards [hsmall, eventually_ge_atTop 1] with W hsmall hW1
    have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ W) _)] using hsmall
  have hlog := (Step2.tendsto_W B).eventually hlogR
  have hexp := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 1 ha)
  have hfour := ((tendsto_rpow_atTop ha).comp (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [hlog, hexp, hfour, B.dim, eventually_ge_atTop 1]
    with N hlogN hexpN hfourN hdim hN u hu
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : Real) < N := by linarith
  change 4 ≤ (B.W N : Real) ^ (theta / 4) at hfourN
  change 4 ≤ (B.W N : Real) ^ (theta / 4) at hfourN
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : Real) < B.W N := by linarith
  have hWN : (B.W N : Real) ≤ N := by
    have hL1 : (1 : Real) ≤ B.L N := by exact_mod_cast B.one_le_L N
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  have hell : (1 : Real) ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hcmono := Step2FarInputs.cNear_le_cNear_one hW1 hell
  have hlog0 : 0 ≤ Real.log (B.W N : Real) := Real.log_nonneg hW1
  have hpoly : 2 * Real.log (B.W N : Real) ^ (3 : Real) + 2 ≤
      (B.W N : Real) ^ (theta / 4) := by nlinarith
  have hexp' : Real.exp (Real.log (B.W N : Real) ^ (3 / 4 : Real)) ≤
      (B.W N : Real) ^ (theta / 4) := by simpa only [one_mul] using hexpN
  have hc : Lemma57.cNear (B.W N : Real) 1 ≤
      (B.W N : Real) ^ (theta / 4) * (B.W N : Real) ^ (theta / 4) := by
    unfold Lemma57.cNear
    have hpoly' : 2 * Real.log (B.W N : Real) ^ (3 : Real) + 2 / 1 ≤
        (B.W N : Real) ^ (theta / 4) := by simpa using hpoly
    exact mul_le_mul hpoly' hexp' (Real.exp_pos _).le
      (Real.rpow_nonneg hW0.le _)
  calc
    Lemma57.cNear (d.W N : Real) (B.ell N u) ≤ Lemma57.cNear (d.W N : Real) 1 := hcmono
    _ ≤ (B.W N : Real) ^ (theta / 4) * (B.W N : Real) ^ (theta / 4) := hc
    _ = (B.W N : Real) ^ (theta / 2) := by
      rw [← Real.rpow_add hW0]
      congr 1
      ring
    _ ≤ (N : Real) ^ (theta / 2) := Real.rpow_le_rpow hW0.le hWN (by positivity)
    _ ≤ (N : Real) ^ theta := Real.rpow_le_rpow_of_exponent_le hNr (by linarith)

private theorem continuousOn_nearMain {E : Real} {s : Nat → Real} {N : Nat}
    {v : Real} (hE : |E| < 2) (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (zetaSrc zetaCtr : Real) :
    ContinuousOn (fun u => normalizedNearMain E s zetaSrc zetaCtr N v u)
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
  have hmain : ContinuousOn (fun u => normalizedNearMain E s zetaSrc zetaCtr N v u)
      (Set.Icc (s N) v) := by
    unfold normalizedNearMain
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


theorem eventually_corrected_near_main_integral
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) {lam : Real} (hlam : 0 < lam)
    (hlamsmall : lam ≤ min (1 / 10000) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        normalizedNearMain E s
          (hLoss lam)
          (hLoss lam)
          N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u
        ≤ (8 / (mE E).im) * (N : Real) ^ (4 * hLoss lam) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  have hm := mE_im_pos hE
  have htheta : 0 < hLoss lam := by dsimp [hLoss]; positivity
  have hcn := eventually_cNear_le hs0 hst ht1 htheta
  have hxi := Step2FarInputs.eventually_xiK_le B (mE E).im htheta
  filter_upwards [hcn, hxi, eventually_ge_atTop 1] with N hcnN hxiN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvIcc : v ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _ (cutNetPt_mem_netFinset hk)
  have hNpos : 0 < (N : Real) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hv1 : v < 1 := hvIcc.2.trans_lt (ht1 N)
  have hRatV : 0 < Step2Moment.ratR E s N v := Step2Moment.ratR_pos hE hs1 hv1
  have hmainInt : IntervalIntegrable
      (fun u => normalizedNearMain E s
        (hLoss lam)
        (hLoss lam) N v u)
      volume (s N) v :=
    (continuousOn_nearMain hE (hs0 N) hvIcc.1 hv1 _ _).intervalIntegrable_of_Icc hvIcc.1
  have hkernelInt : IntervalIntegrable
      (fun u => (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
        (etaT E u)⁻¹) volume (s N) v := by
    have hpowInt := APrimeDriftIntegralBudget.intervalIntegrable_powerRate
      (s := s N) (v := v) (q := -(1 / 2 : Real)) hvIcc.1 hv1 (ne_of_gt hm)
    have heq : (fun u => APrimeDriftIntegralBudget.powerRate (mE E).im (s N)
        (-(1 / 2 : Real)) u) =
        (fun u => (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := by
      funext u
      rw [APrimeDriftIntegralBudget.powerRate, Step2.etaT_eq]
      field_simp [ne_of_gt hm]
      <;> ring
    rw [← heq]
    exact hpowInt
  have hboundPoint : ∀ u ∈ Set.Icc (s N) v,
      normalizedNearMain E s
          (hLoss lam)
          (hLoss lam) N v u ≤
        (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (hLoss lam +
            hLoss lam) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
            (etaT E u)⁻¹) := by
    intro u hu
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hellU : 0 < B.ell N u := zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans hu.1) hu1)
    have hellS : 0 < B.ell N (s N) := zero_lt_one.trans_le
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1)
    have hratio0 : 0 ≤ B.ell N u / B.ell N (s N) := div_nonneg hellU.le hellS.le
    have hratio_sq : (B.ell N u / B.ell N (s N)) ^ 2 ≤
        Step2Moment.ratR E s N u := by
      have hh := Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hu.1 hu1
      rw [ratR_eq_ratio hE]
      simpa [APrimeDriftIntegralBudget.ratio, Step2.etaT_ratio hE] using hh
    have hratio : 0 < Step2Moment.ratR E s N u := Step2Moment.ratR_pos hE hs1 hu1
    have hratio1 : 1 ≤ Step2Moment.ratR E s N u := by
      rw [ratR_eq_ratio hE]
      unfold APrimeDriftIntegralBudget.ratio
      rw [le_div_iff₀ (by linarith : 0 < 1 - u)]
      linarith [hu.1]
    have hcube := ratio_cube_normalized_le hratio0 hratio
      hratio1
      hratio_sq
    rw [ratR_eq_ratio hE] at hcube
    unfold normalizedNearMain APrimeGeneralMovingDriftNearMainSlot.normalizedNearMain
    have hRatUeq : Step2Moment.ratR E s N u =
        APrimeDriftIntegralBudget.ratio (s N) u := ratR_eq_ratio hE
    rw [hRatUeq]
    have hW1 : 1 ≤ (d.W N : Real) := by exact_mod_cast B.one_le_W N
    have hcnear0 : 0 ≤ Lemma57.cNear (d.W N : Real) (B.ell N u) :=
      Lemma57.cNear_nonneg hW1 hellU
    have hcoef0 : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (hLoss lam +
          hLoss lam) *
        Lemma57.cNear (d.W N : Real) (B.ell N u) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      have hWxi := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hWxi)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hcnear0)
        (Real.rpow_nonneg (Step2Moment.ratR_pos hE hs1 hv1).le _)
    have heta0 : 0 ≤ (etaT E u)⁻¹ :=
      inv_nonneg.mpr (Step2.etaT_pos' hE hu1).le
    have hnonneg : 0 ≤ (B.ell N u / B.ell N (s N)) ^ 3 := by positivity
    have hcancel := mul_le_mul_of_nonneg_right hcube heta0
    have hfac : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (hLoss lam +
          hLoss lam) *
        Lemma57.cNear (d.W N : Real) (B.ell N u) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := hcoef0
    calc
      _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (hLoss lam +
            hLoss lam) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((B.ell N u / B.ell N (s N)) ^ 3 *
            (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-2 : Real) * (etaT E u)⁻¹) := by
          simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
          (N : Real) ^ (hLoss lam +
            hLoss lam) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
            (etaT E u)⁻¹) := by
          gcongr
  let C : Real := 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (hLoss lam +
        hLoss lam) *
      (N : Real) ^ (hLoss lam) * (Step2Moment.ratR E s N v) ^ (-2 : Real)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hXi := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
    have hNpow : 0 ≤ (N : Real) ^ (hLoss lam +
        hLoss lam) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hRpow : 0 ≤ (Step2Moment.ratR E s N v) ^ (-2 : Real) :=
      Real.rpow_nonneg hRatV.le _
    positivity
  have hpoint' : ∀ u ∈ Set.Icc (s N) v,
      normalizedNearMain E s
          (hLoss lam)
          (hLoss lam) N v u ≤
        C * ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := by
    intro u hu
    have hcu := hcnN u ⟨hu.1, hu.2.trans hvIcc.2⟩
    have hnonneg : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (N : Real) ^ (hLoss lam +
          hLoss lam) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      have hxi0 := Step2.xiK_nonneg (d.L N) (d.W N) (mE E).im
      have hNpow : 0 ≤ (N : Real) ^
          (hLoss lam +
            hLoss lam) :=
        Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hRvpow : 0 ≤ (Step2Moment.ratR E s N v) ^ (-2 : Real) :=
        Real.rpow_nonneg hRatV.le _
      positivity
    have hu1 : u < 1 := hu.2.trans_lt hv1
    have hratioPos : 0 < APrimeDriftIntegralBudget.ratio (s N) u := by
      unfold APrimeDriftIntegralBudget.ratio
      exact div_pos (by linarith [hu.1]) (by linarith [hu.2, hv1])
    have hkernel0 : 0 ≤ (APrimeDriftIntegralBudget.ratio (s N) u) ^
        (-(1 / 2 : Real)) * (etaT E u)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg hratioPos.le _)
        (inv_nonneg.mpr (Step2.etaT_pos' hE hu1).le)
    calc
      _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
              (N : Real) ^ (hLoss lam +
                hLoss lam) *
          Lemma57.cNear (d.W N : Real) (B.ell N u) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
          ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
            (etaT E u)⁻¹) := hboundPoint u hu
      _ ≤ C * ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := by
          dsimp [C]
          apply mul_le_mul_of_nonneg_right _ hkernel0
          have hfactor : 0 ≤ 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
              (N : Real) ^ (hLoss lam +
                hLoss lam) *
              (Step2Moment.ratR E s N v) ^ (-2 : Real) := hnonneg
          calc
            _ = (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
                (N : Real) ^ (hLoss lam +
                  hLoss lam) *
                (Step2Moment.ratR E s N v) ^ (-2 : Real)) *
                Lemma57.cNear (d.W N : Real) (B.ell N u) := by
              dsimp [d, B]
              ac_rfl
            _ ≤ (4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
                (N : Real) ^ (hLoss lam +
                  hLoss lam) *
                (Step2Moment.ratR E s N v) ^ (-2 : Real)) * (N : Real) ^ (hLoss lam) :=
              mul_le_mul_of_nonneg_left hcu hfactor
            _ = C := by dsimp [C]; ring
  have hmono := intervalIntegral.integral_mono_on hvIcc.1 hmainInt
    (hkernelInt.const_mul C) hpoint'
  have hkernelBound :
      (∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) ≤ 2 / (mE E).im := by
    have hInt := integral_ratR_eta_inv_neg_half hE hvIcc.1 hv1
    exact hInt
  have hCbound : C ≤ 4 * (N : Real) ^ (4 * hLoss lam) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
    have hxiN' : Step2.xiK (d.L N) (d.W N) (mE E).im ≤
        (N : Real) ^ (hLoss lam) := hxiN
    have heq : (N : Real) ^ (hLoss lam + hLoss lam) *
        (N : Real) ^ (hLoss lam) * (N : Real) ^ (hLoss lam) =
          (N : Real) ^ (4 * hLoss lam) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    change 4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
      (N : Real) ^ (hLoss lam + hLoss lam) *
      (N : Real) ^ (hLoss lam) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) ≤ _
    calc
      _ ≤ 4 * (N : Real) ^ (hLoss lam) *
          (N : Real) ^ (hLoss lam + hLoss lam) *
          (N : Real) ^ (hLoss lam) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
            gcongr
      _ = 4 * ((N : Real) ^ (hLoss lam + hLoss lam) *
          (N : Real) ^ (hLoss lam) * (N : Real) ^ (hLoss lam)) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by ring
      _ = 4 * (N : Real) ^ (4 * hLoss lam) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
            rw [heq]
  calc
    _ ≤ ∫ u in (s N)..v,
        C * ((APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹) := hmono
    _ = C * ∫ u in (s N)..v,
        (APrimeDriftIntegralBudget.ratio (s N) u) ^ (-(1 / 2 : Real)) *
          (etaT E u)⁻¹ := by rw [intervalIntegral.integral_const_mul]
    _ ≤ C * (2 / (mE E).im) := mul_le_mul_of_nonneg_left hkernelBound hC0
    _ ≤ (8 / (mE E).im) * (N : Real) ^ (4 * hLoss lam) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      have hm0 : 0 ≤ 2 / (mE E).im := by positivity
      calc
        _ = C * (2 / (mE E).im) := rfl
        _ ≤ (4 * (N : Real) ^ (4 * hLoss lam) *
            (Step2Moment.ratR E s N v) ^ (-2 : Real)) * (2 / (mE E).im) :=
          mul_le_mul_of_nonneg_right hCbound hm0
        _ = _ := by ring


set_option maxHeartbeats 1000000 in
-- The continuity proof elaborates the nested gap/tail composition and its
-- endpoint-dependent block cap; no additional mathematical hypothesis is used.
private theorem continuousOn_nearTail {E D : Real} {s : Nat → Real}
    {N : Nat} {v : Real} (hE : |E| < 2)
    (hs0 : 0 ≤ s N) (hsv : s N ≤ v) (hv1 : v < 1)
    (ζ τ κ : Real) :
    ContinuousOn (fun u => normalizedNearTail E D s ζ τ κ N v u)
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
  dsimp [F, normalizedNearTail,
    APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail]
  field_simp [hellne, hsEll, he, hrune]


theorem eventually_corrected_near_residual_pointwise
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lam : Real} (hlam : 0 < lam)
    (hlamsmall : lam ≤ min (1 / 10000) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        normalizedNearTail E D s
          (hLoss lam)
          (hLoss lam)
          (capLoss lam)
          N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u ≤
          8 * (N : Real) ^ (-(21 : Real)) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  have htauPos : 0 < hLoss lam := by dsimp [hLoss]; positivity
  have hcapPos : 0 < capLoss lam := by dsimp [capLoss]; positivity
  have hroomNum : hLoss lam + 2 * capLoss lam + (2 : Real) / 15 < 1 := by
    unfold hLoss capLoss
    have hlam10000 : lam ≤ 1 / 10000 :=
      hlamsmall.trans (min_le_left _ _)
    norm_num at hlam10000 ⊢
    nlinarith
  have hcr := SumZeroDyn.flow_crude hE hs0 hst ht1 hreg.1
  have hJ := APrimeGeneralMovingQVProfile.eventually_generalMovingBlockCap_le_N
    hE hs0 hst ht1 hc hreg htauPos hcapPos hroomNum
  have hNW := Step2.eventually_le_W_sq B
  have hXi := Step2FarInputs.eventually_xiK_le B (mE E).im (by norm_num : (0 : Real) < 1)
  have hWbig := (Step2.tendsto_W B).eventually_ge_atTop (Real.exp ((4 * D)^2))
  filter_upwards [hcr, hJ, hNW, hXi, hWbig, eventually_ge_atTop 1]
    with N hcrN hJN hNWN hXiN hWbigN hN
  intro k hk u hu
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  have hW1 : (1 : Real) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : Real) < B.W N := by linarith
  have hL0 : (0 : Real) ≤ B.L N := Nat.cast_nonneg _
  have hells : (1 : Real) ≤ B.ell N (s N) :=
    one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
  have hellu : (1 : Real) ≤ B.ell N u :=
    one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hellL : B.ell N u ≤ (B.L N : Real) :=
    SumZeroDyn.ellHat_real_le_L hu1
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hru1 : 1 ≤ B.ell N u / B.ell N (s N) := by
    rw [one_le_div (by linarith : 0 < B.ell N (s N))]
    exact Step3.ellHat_mono hu.1 hu1
  have hruN : B.ell N u / B.ell N (s N) ≤ (N : Real) := by
    apply (div_le_iff₀ (by linarith : 0 < B.ell N (s N))).2
    have hEllN : B.ell N u ≤ (N : Real) := hellL.trans hcrN.1
    nlinarith
  have hRu : 1 ≤ Step2Moment.ratR E s N u :=
    Step2Moment.one_le_ratR hE hu.1 hu1
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  have hlog : (4 * D)^2 ≤ Real.log (B.W N : Real) := by
    calc
      (4 * D)^2 = Real.log (Real.exp ((4 * D)^2)) := (Real.log_exp _).symm
      _ ≤ Real.log (B.W N : Real) :=
        Real.log_le_log (Real.exp_pos _) hWbigN
  have hlog4 : 4 ≤ Real.log (B.W N : Real) := by
    nlinarith [hD]
  have hWe : Real.exp 1 ≤ (B.W N : Real) := by
    exact (Real.exp_le_exp.mpr (by nlinarith [hD] : 1 ≤ (4 * D)^2)).trans hWbigN
  have hA : 1 ≤ B.scale E N u := (hcrN.2.2.2 uu).1
  have htail := APrimeDriftNearAbsorb.gap_tail_le_two_floor
    hWe (by linarith : 0 < B.ell N u) heta hA (by linarith : 0 ≤ D)
    hlog4 hlog
  have hexp := APrimeDriftNearAbsorb.exp_subpow_le_W hW0 (by linarith : 1 ≤ Real.log (B.W N : Real))
  have hzeta : (N : Real) ^ (hLoss lam) ≤ N := by
    have hexp : hLoss lam ≤ 1 := by
      unfold hLoss
      have hlam10000 : lam ≤ 1 / 10000 :=
        hlamsmall.trans (min_le_left _ _)
      nlinarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr hexp
  have hWleN : (B.W N : Real) ≤ N := hcrN.2.1
  have hJle : APrimeGeneralMovingDriftSource.blockCap E s
      (hLoss lam)
      (capLoss lam) N u ≤ (N : Real) := by
    simpa only [APrimeGeneralMovingQVProfile.generalMovingBlockCap,
      APrimeGeneralMovingDriftSource.blockCap] using hJN uu
  have hJ0 : 0 ≤ APrimeGeneralMovingDriftSource.blockCap E s
      (hLoss lam)
      (capLoss lam) N u := by
    unfold APrimeGeneralMovingDriftSource.blockCap
    positivity
  have hfloor := floor_le_N_inv_thirty hNr hW1 hNWN hD
  have hbound := residual_crude hNr hW1 hWleN hRv hRu
    (Step2.xiK_nonneg _ _ _) (by simpa only [Real.rpow_one] using hXiN)
    (by positivity) hzeta hL0 hcrN.1 hJ0 hJle (by linarith)
    (hellL.trans hcrN.1) (by positivity) hruN
    (Real.exp_pos _).le (hexp.trans hWleN)
    (tailT_nonneg (by linarith : 0 ≤ (d.W N : Real)) _) htail
  have hpower : (N : Real) ^ (9 : Nat) * (N : Real) ^ (-(30 : Real)) =
      (N : Real) ^ (-(21 : Real)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
    norm_num
  have hpoint : normalizedNearTail E D s
      (hLoss lam)
      (hLoss lam)
      (capLoss lam) N v u =
      4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) *
        ((N : Real) ^ (hLoss lam) *
          (d.L N : Real) *
          APrimeGeneralMovingDriftSource.blockCap E s
            (hLoss lam)
            (capLoss lam) N u *
          (d.W N : Real)^2 * B.ell N u *
          (B.ell N u / B.ell N (s N)) *
          Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)) *
          tailT (d.W N : Real) (B.ell N u) (etaT E u) D
            (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) := by
    have hellne : B.ell N u ≠ 0 := by linarith
    have hellsne : B.ell N (s N) ≠ 0 := by linarith
    have hrune : B.ell N u / B.ell N (s N) ≠ 0 :=
      div_ne_zero hellne hellsne
    unfold normalizedNearTail APrimeGeneralMovingDriftNearTailSlot.normalizedNearTail
    dsimp only
    field_simp [hellne, hellsne, heta.ne', hrune]
  rw [hpoint]
  calc
    _ ≤ 8 * (N : Real) ^ (9 : Nat) * (d.W N : Real) ^ (-D) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := hbound
    _ ≤ 8 * (N : Real) ^ (9 : Nat) * (N : Real) ^ (-(30 : Real)) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
          gcongr
          exact hfloor
    _ = _ := by
      dsimp only [v]
      calc
        8 * (N : Real) ^ (9 : Nat) * (N : Real) ^ (-(30 : Real)) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) =
          8 * ((N : Real) ^ (9 : Nat) * (N : Real) ^ (-(30 : Real))) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by ring
        _ = _ := by rw [hpower]



/-- The literal near residual integrates over every active target cell. Its
actual T615 definition is kept, and its endpoint transport loss remains
ratR(v)^(-2). -/
theorem eventually_corrected_near_residual_integral
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lam : Real} (hlam : 0 < lam)
    (hlamsmall : lam <= min (1 / 10000) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      (∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        normalizedNearTail E D s (hLoss lam) (hLoss lam) (capLoss lam)
          N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u) <=
        8 * (N : Real) ^ (-(21 : Real)) *
          (Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  have hpoint := eventually_corrected_near_residual_pointwise
    hE hD hs0 hst ht1 hc hreg hlam hlamsmall
  filter_upwards [hpoint, eventually_ge_atTop 1] with N hpointN hN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hv : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hk)
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := hv.1.trans_lt hv1
  have hRv : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE hs1 hv1
  let C : Real := 8 * (N : Real) ^ (-(21 : Real)) *
    (Step2Moment.ratR E s N v) ^ (-2 : Real)
  have hC0 : 0 <= C := by dsimp [C]; positivity
  have hInt : IntervalIntegrable
      (fun u => normalizedNearTail E D s (hLoss lam) (hLoss lam)
        (capLoss lam) N v u) volume (s N) v :=
    (continuousOn_nearTail hE (hs0 N) hv.1 hv1
      (hLoss lam) (hLoss lam) (capLoss lam)).intervalIntegrable_of_Icc hv.1
  have hmono := intervalIntegral.integral_mono_on hv.1 hInt
    intervalIntegrable_const (fun u hu => hpointN k hk u hu)
  have hlen : v - s N <= 1 := by linarith [hs0 N, hv1]
  calc
    _ <= ∫ u in (s N)..v, C := hmono
    _ = (v - s N) * C := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
    _ <= C := by nlinarith
    _ = 8 * (N : Real) ^ (-(21 : Real)) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := rfl


/-- The exact T615 near-main term and the literal near residual both satisfy
their integrated bounds on one common eventual set, uniformly for every active
cell and every loop output. -/
theorem eventually_corrected_near_rows_integral
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {lam : Real} (hlam : 0 < lam)
    (hlamsmall : lam <= min (1 / 10000) (c / 10000)) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall a : LoopArg (d.L N) 2,
        (∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          normalizedNearMain E s (hLoss lam) (hLoss lam) N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u) <=
          (8 / (mE E).im) * (N : Real) ^ (4 * hLoss lam) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) /\
        (∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
          normalizedNearTail E D s (hLoss lam) (hLoss lam) (capLoss lam)
            N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u) <=
          8 * (N : Real) ^ (-(21 : Real)) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  have hMain := eventually_corrected_near_main_integral
    hE hD hs0 hst ht1 hc hlam hlamsmall
  have hTail := eventually_corrected_near_residual_integral
    hE hD hs0 hst ht1 hc hreg hlam hlamsmall
  filter_upwards [hMain, hTail] with N hMainN hTailN
  intro k hk a
  exact ⟨hMainN k hk, hTailN k hk⟩

/-- A nondegenerate same-sample witness satisfies the corrected structural
assumptions with a positive window and a positive loss. -/
theorem corrected_schedule_nonempty :
    exists c : Real, 0 < c /\
      exists s t : Nat -> Real,
        (forall N, s N = 0) /\
        (forall N, 0 <= s N) /\
        (forall N, s N <= t N) /\
        (forall N, t N < 1) /\
        Cond272Reg B 0 s t c /\
        BoundsCore (Gauss.sample d) 0 s /\
        exists lam : Real,
          0 < lam /\
          lam <= min (1 / 10000) (c / 10000) /\
          ∀ᶠ N : Nat in atTop,
            s N < t N /\
            1 <= cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N /\
            exists omega,
              omega ∈ APrimeGeneralMovingCommonSources.commonEvent
                0 60 s t (hLoss lam) (hLoss lam) (hLoss lam) N /\
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh 60)) 1
                (APrimeGeneralMovingDetFields.J 0 60 s) s t
                (APrimeGeneralMovingMesh.targetMesh 60)
                (actualWeightLoss lam) 1 N 1 omega = 1 /\
              0 < APrimeSmoothWeightActual.weight d 0 60
                (actualWeightLoss lam) s t
                (APrimeGeneralMovingMesh.targetMesh 60) 2 1 N 1
                (APrimeSmoothWeightActual.canonicalM d s t
                  (APrimeGeneralMovingMesh.targetMesh 60) N) omega := by
  obtain ⟨_tauPrime, _htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, _hStep, hresident⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  have hm1 : (0 : Real) < 1 / 10000 := by norm_num
  have hm2 : 0 < c / 10000 := by positivity
  have hm : 0 < min (1 / 10000) (c / 10000) := lt_min hm1 hm2
  let lam : Real := min (1 / 10000) (c / 10000) / 2
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hlamsmall : lam <= min (1 / 10000) (c / 10000) := by
    dsimp [lam]
    linarith
  have hevent := hresident (hLoss lam) (hLoss lam) (hLoss lam)
    (actualWeightLoss lam) (by dsimp [hLoss]; positivity)
    (by dsimp [hLoss]; positivity) (by dsimp [hLoss]; positivity)
    (by dsimp [actualWeightLoss, lam]; linarith)
  refine ⟨c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
    lam, hlam, hlamsmall, ?_⟩
  filter_upwards [hevent] with N hN
  rcases hN with ⟨hwindow, omega, hω, hactive, hwide⟩
  have hwideOne :
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t
        (APrimeGeneralMovingMesh.targetMesh 60)
        (actualWeightLoss lam) 1 N 1 omega = 1 := hwide 1
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60) (δ := actualWeightLoss lam)
    (s := s) (t := t) (mesh := APrimeGeneralMovingMesh.targetMesh 60)
    (by norm_num) (by dsimp [actualWeightLoss]; exact hlam.le) N 1 1 omega
    (hst N) (ht1 N) (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwidePos :
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 s) s t
        (APrimeGeneralMovingMesh.targetMesh 60)
        (actualWeightLoss lam) 1 N 1 omega := by
    rw [hwideOne]
    norm_num
  have hweightPos :
      0 < APrimeSmoothWeightActual.weight d 0 60
        (actualWeightLoss lam) s t (APrimeGeneralMovingMesh.targetMesh 60)
        2 1 N 1
        (APrimeSmoothWeightActual.canonicalM d s t
          (APrimeGeneralMovingMesh.targetMesh 60) N) omega :=
    hwidePos.trans_le hcompare
  exact ⟨hwindow, hactive, omega, hω, hwideOne, hweightPos⟩

#print axioms corrected_schedule_identities
#print axioms literal_near_source_split
#print axioms eventually_corrected_near_main_integral
#print axioms eventually_corrected_near_residual_pointwise
#print axioms eventually_corrected_near_residual_integral
#print axioms eventually_corrected_near_rows_integral
#print axioms corrected_schedule_nonempty

end
end RBM.APrimeFreeLossNear
