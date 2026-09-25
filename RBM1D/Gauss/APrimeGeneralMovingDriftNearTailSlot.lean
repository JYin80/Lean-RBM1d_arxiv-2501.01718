/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftAtProfile
import RBM1D.Gauss.APrimeGeneralMovingQVProfile
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeDriftIntegralBudget

/-!
# T1005: the literal general-moving near-tail drift residual

Only the second summand of `APrimeGeneralMovingDriftAtProfile.nearSourceCoeff`
is treated here. The common-event and transport profile are inherited from T615.
-/

namespace RBM.APrimeGeneralMovingDriftNearTailSlot

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal second near-source summand of T615, including both moving
transport factors. -/
noncomputable def normalizedNearTail (E D : Real) (s : Nat → Real)
    (zetaCtr tauG deltaCap : Real) (N : Nat) (v u : Real) : Real :=
  let ellu := B.ell N u
  let etau := etaT E u
  let ru := ellu / B.ell N (s N)
  let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG deltaCap N u
  Step2.xiK (d.L N) (d.W N) (mE E).im *
    (Step2Moment.ratR E s N u) ^ (-2 : Real) *
    (Step2Moment.ratR E s N v) ^ (-2 : Real) *
    ((4 * (N : Real)^zetaCtr *
        ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
        (((d.W N : Real) * ellu * etau)^2 *
          Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
        tailT (d.W N : Real) ellu etau D
          (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
      (etau⁻¹ * ru^3))

/-- Definition-level check that this is exactly the second summand of the
T615 near coefficient, after the unchanged transport multiplier. -/
theorem near_source_split (E D : Real) (s : Nat → Real)
    (zetaSrc zetaCtr tauG deltaCap : Real) (N : Nat) (v u : Real) :
    Step2.xiK (d.L N) (d.W N) (mE E).im *
      (Step2Moment.ratR E s N u) ^ (-2 : Real) *
      (Step2Moment.ratR E s N v) ^ (-2 : Real) *
      APrimeGeneralMovingDriftAtProfile.nearSourceCoeff E D s
        zetaSrc zetaCtr tauG deltaCap N u =
      Step2.xiK (d.L N) (d.W N) (mE E).im *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) *
        (4 * (N : Real)^(zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
          (B.ell N u / B.ell N (s N))^3 *
          Lemma57.cNear (d.W N : Real) (B.ell N u)) +
      normalizedNearTail E D s zetaCtr tauG deltaCap N v u := by
  unfold APrimeGeneralMovingDriftAtProfile.nearSourceCoeff normalizedNearTail
  ring

private theorem floor_le_N_inv_thirty {N W D : Real}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N ≤ W ^ 2) (hD : 60 ≤ D) :
    W ^ (-D) ≤ N ^ (-(30 : Real)) := by
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hpow : N ^ (30 : Nat) ≤ (W^2) ^ (30 : Nat) :=
    pow_le_pow_left₀ hN0.le hNW 30
  have hpos : 0 < N ^ (30 : Nat) := pow_pos hN0 _
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

private theorem residual_algebra {W L ell eta J r X T : Real}
    (hell : ell ≠ 0) (heta : eta ≠ 0) (hr : r ≠ 0) :
    ((L * J / (ell * eta * r ^ 2)) *
      ((W * ell * eta) ^ 2 * X) * T) * (eta⁻¹ * r ^ 3) =
      L * J * W ^ 2 * ell * r * X * T := by
  field_simp

private theorem residual_crude {N W D ζ Xi Ru Rv L J ell r X T : Real}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hWN : W ≤ N) (hRv : 0 < Rv)
    (hRu : 1 ≤ Ru) (_hXi0 : 0 ≤ Xi) (hXi : Xi ≤ N)
    (_hζ0 : 0 ≤ N ^ ζ) (hζ : N ^ ζ ≤ N)
    (hL0 : 0 ≤ L) (hL : L ≤ N) (hJ0 : 0 ≤ J) (hJ : J ≤ N)
    (hell0 : 0 ≤ ell) (hell : ell ≤ N) (hr0 : 0 ≤ r) (hr : r ≤ N)
    (hX0 : 0 ≤ X) (hX : X ≤ N) (hT0 : 0 ≤ T) (hT : T ≤ 2 * W ^ (-D)) :
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

/-- Uniform numerical compression of the exact residual, retaining the
terminal transport factor. The bound is for every active cell, including
the zero cell. -/
theorem eventually_near_tail_pointwise
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ u ∈ Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        normalizedNearTail E D s
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
          N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u ≤
          8 * (N : Real) ^ (-(21 : Real)) *
            (Step2Moment.ratR E s N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  have htauPos : 0 < APrimeGeneralMovingSlotLossSchedule.tauG δ := by
    unfold APrimeGeneralMovingSlotLossSchedule.tauG
    positivity
  have hcapPos : 0 < APrimeGeneralMovingSlotLossSchedule.deltaCap δ := by
    unfold APrimeGeneralMovingSlotLossSchedule.deltaCap
    positivity
  have hroomNum : APrimeGeneralMovingSlotLossSchedule.tauG δ +
      2 * APrimeGeneralMovingSlotLossSchedule.deltaCap δ + (2 : Real) / 15 < 1 := by
    unfold APrimeGeneralMovingSlotLossSchedule.tauG
      APrimeGeneralMovingSlotLossSchedule.deltaCap
    linarith [hδsmall.trans (min_le_left _ _)]
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
  have hzeta : (N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) ≤ N := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hNr (show
        APrimeGeneralMovingSlotLossSchedule.zetaCtr δ ≤ 1 by
        dsimp [APrimeGeneralMovingSlotLossSchedule.zetaCtr]
        linarith [hδsmall.trans (min_le_left _ _)]))
  have hWleN : (B.W N : Real) ≤ N := hcrN.2.1
  have hJle : APrimeGeneralMovingDriftSource.blockCap E s
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u ≤ (N : Real) := by
    simpa only [APrimeGeneralMovingQVProfile.generalMovingBlockCap,
      APrimeGeneralMovingDriftSource.blockCap] using hJN uu
  have hJ0 : 0 ≤ APrimeGeneralMovingDriftSource.blockCap E s
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u := by
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
      (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
      (APrimeGeneralMovingSlotLossSchedule.tauG δ)
      (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u =
      4 * Step2.xiK (d.L N) (d.W N) (mE E).im *
        (Step2Moment.ratR E s N u) ^ (-2 : Real) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) *
        ((N : Real) ^ (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ) *
          (d.L N : Real) *
          APrimeGeneralMovingDriftSource.blockCap E s
            (APrimeGeneralMovingSlotLossSchedule.tauG δ)
            (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N u *
          (d.W N : Real)^2 * B.ell N u *
          (B.ell N u / B.ell N (s N)) *
          Real.exp (Real.log (d.W N : Real) ^ (3 / 4 : Real)) *
          tailT (d.W N : Real) (B.ell N u) (etaT E u) D
            (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) := by
    have hellne : B.ell N u ≠ 0 := by linarith
    have hellsne : B.ell N (s N) ≠ 0 := by linarith
    have hrune : B.ell N u / B.ell N (s N) ≠ 0 :=
      div_ne_zero hellne hellsne
    unfold normalizedNearTail
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
  dsimp [F, normalizedNearTail]
  field_simp [hellne, hsEll, he, hrune]

/-- The literal T615 near-tail residual integrates into a strict small-slot
power. The endpoint `R_v^{-2}` is kept, and the assertion includes `k=0`.
The exponent `δ/8` is strictly below the consumer's `5δ/32`. -/
theorem eventually_near_tail_integral_le_strict_slot
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ) (hδsmall : δ ≤ min 1 (c / 100)) :
    δ / 8 < 5 * δ / 32 ∧
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      (∫ u in (s N)..(cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        normalizedNearTail E D s
          (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
          (APrimeGeneralMovingSlotLossSchedule.tauG δ)
          (APrimeGeneralMovingSlotLossSchedule.deltaCap δ)
          N (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k) u) ≤
        (N : Real) ^ (δ / 8) *
          (Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k)) ^ (-2 : Real) := by
  constructor
  · linarith
  have hpoint := eventually_near_tail_pointwise hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hpow := SumZeroDyn.eventually_const_mul_rpow_le (8 : Real)
    (show -(21 : Real) < δ / 8 by linarith)
  filter_upwards [hpoint, hpow] with N hpointN hpowN
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
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hInt : IntervalIntegrable
      (fun u => normalizedNearTail E D s
        (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
        (APrimeGeneralMovingSlotLossSchedule.tauG δ)
        (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u)
      volume (s N) v :=
    (continuousOn_nearTail hE (hs0 N) hv.1 hv1 _ _ _).intervalIntegrable_of_Icc hv.1
  have hmono := intervalIntegral.integral_mono_on hv.1 hInt
    (intervalIntegrable_const) (hpointN k hk)
  have hlen : v - s N ≤ 1 := by linarith [hs0 N, hv1]
  calc
    _ ≤ ∫ u in (s N)..v, C := hmono
    _ = (v - s N) * C := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    _ ≤ C := by nlinarith
    _ ≤ (N : Real) ^ (δ / 8) *
        (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
      dsimp [C]
      exact mul_le_mul_of_nonneg_right hpowN (Real.rpow_nonneg hRv.le _)

/-- The exact T995 schedule has a same-resident positive first cell with
`E=0`, `D=60`, and strictly positive actual smooth weight. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms normalizedNearTail
#print axioms near_source_split
#print axioms floor_le_N_inv_thirty
#print axioms residual_algebra
#print axioms residual_crude
#print axioms eventually_near_tail_pointwise
#print axioms eventually_near_tail_integral_le_strict_slot
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingDriftNearTailSlot
