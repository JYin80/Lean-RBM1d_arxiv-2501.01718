/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.APrimeJGWidened

/-!
# T584: the positive-cell general-moving evolved-QV profile

This module specializes the actual full evolved quadratic-variation estimate
to T579's one common event.  The support-local block cap keeps the literal
moving factor `ratR ^ 4`; no paper-level exponent simplification is made.
-/

namespace RBM.APrimeGeneralMovingQVProfile

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The exact support-local block cap supplied by T579. -/
noncomputable def generalMovingBlockCap (E : Real) (s : Nat -> Real)
    (tauG delta : Real) (N : Nat) (u : Real) : Real :=
  1 + (N : Real)^tauG *
    (9 * Real.exp (Real.sqrt 3) *
      ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
        Step2Moment.ratR E s N u ^ 4) + 2)

private theorem endpointKernel_nonneg (E : Real) (N : Nat) (u v D : Real)
    (a : LoopArg (B.L N) 2) :
    0 <= ((1 - u) / (1 - v)) ^ 2 *
      Step2.xiK (B.L N) (B.W N : Real) (mE E).im *
      Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
  have hT : 0 <= Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg (show 0 <= (B.W N : Real) by positivity)
        (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 <= Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  positivity

private theorem rootProfile_nonneg (E : Real) (N : Nat)
    (u v D ellSource J Smax epsilon : Real) (a : LoopArg (B.L N) 2) :
    0 <= APrimeFullQV.rootProfile B E N u v D ellSource J Smax epsilon a := by
  have hT : 0 <= Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg (show 0 <= (B.W N : Real) by positivity)
        (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 <= Step2.xiK (B.L N) (B.W N : Real) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hchi : 0 <= (if (zdist (B.L N) (a 0 - a 1) : Real) <=
      6 * ellStar (B.W N : Real) (B.ell N v) then (1 : Real) else 0) := by
    split_ifs <;> norm_num
  unfold APrimeFullQV.rootProfile
  positivity

/-- A neutral, local monotonicity proof for the full root profile.  This is
kept private so the general-moving module does not import the first-cell QV
stack merely for its analogous helper. -/
private theorem rootProfile_mono_J (E : Real) (N : Nat)
    (u v D ellSource Smax epsilon : Real) (a : LoopArg (B.L N) 2)
    {J J' : Real} (hell : 0 < B.ell N u) (heta : 0 < etaT E u)
    (hJ0 : 0 <= J) (hJJ' : J <= J') :
    APrimeFullQV.rootProfile B E N u v D ellSource J Smax epsilon a <=
      APrimeFullQV.rootProfile B E N u v D ellSource J' Smax epsilon a := by
  have hfar := APrimeJGWidened.diagFarRate_mono
    (D := D) (Smax := Smax) (B.one_le_W N) hell heta hJ0 hJJ'
  have hK := endpointKernel_nonneg E N u v D a
  unfold APrimeFullQV.rootProfile
  exact add_le_add_right
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfar) hK) _

private theorem scale_le_N (hE : |E| < 2) {s t : Nat -> Real}
    (hs0 : forall N, 0 <= s N) (ht1 : forall N, t N < 1)
    {N : Nat} (hdim : B.W N * B.L N <= N) (u : TimeIcc s t N) :
    B.scale E N (u : Real) <= (N : Real) := by
  obtain ⟨_, heta0, heta1, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
  have hWL : (B.W N : Real) * (B.L N : Real) <= (N : Real) := by
    exact_mod_cast hdim
  change (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) <= (N : Real)
  calc
    (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) <=
        (B.W N : Real) * (B.L N : Real) * 1 := by
          gcongr
    _ = (B.W N : Real) * (B.L N : Real) := by ring
    _ <= (N : Real) := hWL

private theorem ratR_four_le_rpow_two_fifteenths
    (hE : |E| < 2) {s t : Nat -> Real}
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    {N : Nat} (hN : 1 <= N) (hdim : B.W N * B.L N <= N)
    (h30 : forall u : TimeIcc s t N,
      Step2Moment.ratR E s N (u : Real) ^ 30 <= B.scale E N (u : Real))
    (hs0 : forall N, 0 <= s N) (u : TimeIcc s t N) :
    Step2Moment.ratR E s N (u : Real) ^ 4 <=
      (N : Real) ^ ((2 : Real) / 15) := by
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hR1 : (1 : Real) <= Step2Moment.ratR E s N (u : Real) :=
    Step2Moment.one_le_ratR hE u.2.1 (u.2.2.trans_lt (ht1 N))
  have hR30 : Step2Moment.ratR E s N (u : Real) ^ 30 <= (N : Real) :=
    (h30 u).trans (scale_le_N hE hs0 ht1 hdim u)
  have h := rpow_mul_rpow_le_of_pow_thirty
    (A := (N : Real)) (R := Step2Moment.ratR E s N (u : Real))
    (Nr := (N : Real)) (c := 1) (e := 0) (b := 4)
    (a := (2 : Real) / 15) hNr hR1 (by norm_num) (by norm_num)
    (by norm_num) hR30 (by simp) (by norm_num)
  simpa using h

private theorem blockCap_le_const_mul_rpow
    {E : Real} {s : Nat -> Real} {tauG delta : Real} {N : Nat} {u : Real}
    (hN : 1 <= N) (htauG : 0 <= tauG) (hdelta : 0 <= delta)
    (hR : Step2Moment.ratR E s N u ^ 4 <=
      (N : Real) ^ ((2 : Real) / 15)) :
    generalMovingBlockCap E s tauG delta N u <=
      (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
  have hn : (1 : Real) <= N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
  have hpow0 : 0 <= (N : Real) ^ tauG := by positivity
  have hdeltaPow0 : 0 <= (N : Real) ^ (2 * delta) := by positivity
  have hmain : (N : Real) ^ tauG *
      ((N : Real) ^ (2 * delta) * (N : Real) ^ ((2 : Real) / 15)) =
      (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    ring_nf
  have htau : (N : Real) ^ tauG <=
      (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hone : (1 : Real) <=
      (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) :=
    Real.one_le_rpow hn (by linarith)
  have hterm : (N : Real)^tauG *
      (9 * Real.exp (Real.sqrt 3) *
        ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
          (N : Real) ^ ((2 : Real) / 15))) =
      (9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
    rw [← hmain]
    ring
  unfold generalMovingBlockCap
  calc
    1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
            Step2Moment.ratR E s N u ^ 4) + 2) <=
      1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
            (N : Real) ^ ((2 : Real) / 15)) + 2) := by gcongr
    _ <= (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) *
        (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
          rw [mul_add, hterm]
          nlinarith [Real.exp_pos (Real.sqrt 3), Real.exp_pos 1,
            Real.rpow_nonneg hn0.le (tauG + 2 * delta + (2 : Real) / 15)]

/-- The exact cap, including its additive constants, is eventually at most
`N` under precisely the room condition used by the absorbed full-QV theorem. -/
theorem eventually_generalMovingBlockCap_le_N
    {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    {tauG delta : Real} (htauG : 0 < tauG) (hdelta : 0 < delta)
    (hroom : tauG + 2 * delta + (2 : Real) / 15 < 1) :
    ∀ᶠ N : Nat in atTop, forall u : TimeIcc s t N,
      generalMovingBlockCap E s tauG delta N (u : Real) <= (N : Real) := by
  have h30 := hreg.1.pow_thirty_le hE hst ht1
  have habs := SumZeroDyn.eventually_const_mul_rpow_le
    (3 + 9 * Real.exp (Real.sqrt 3) * (4 * Real.exp 1 + 2)) hroom
  filter_upwards [h30, d.dim, habs, eventually_ge_atTop 1]
    with N h30N hdim habsN hN u
  have hR := ratR_four_le_rpow_two_fifteenths hE hst ht1 hN hdim.1 h30N hs0 u
  exact (blockCap_le_const_mul_rpow hN htauG.le hdelta.le hR).trans (by
    simpa only [Real.rpow_one] using habsN)

/-- On every positive active cell, one resident of T579's literal common
event carries both the exact block cap and the actual evolved-QV profile.
The `W^-1` repair and every quadratic/cubic/spatial row remain inside the
literal `rootProfile`. -/
theorem eventually_qv_profile_on_common_support
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc)
    (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG)
    (hdelta : 0 < delta)
    (hroom : tauG + 2 * delta + (2 : Real) / 15 < 1)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈
        APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingDetFields.J E D s) s t
        (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega ->
      ∀ u ∈ Set.Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      forall a : LoopArg (d.L N) 2,
        let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
        let Jbar := generalMovingBlockCap E s tauG delta N u
        APrimeJG.jG (Gauss.sample d) E N u omega
            (B.ell N u) (etaT E u) D <= Jbar /\
        APrimeDriftTimeFamily.qvAt
            d E D N Step2.sigPM a (s N) v u omega <=
          ((APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ *
            APrimeFullQV.rootProfile B E N u v D
              (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
              Jbar
              (APrimeGeneralMovingRawSources.sourceC4
                E s zetaSrc N u)
              ((d.W N : Real)⁻¹) a)^2 := by
  have hsources := APrimeGeneralMovingCommonSources.eventually_common_sources
    hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG
  have hblock :=
    APrimeGeneralMovingCommonSources.eventually_block_cap_on_widened_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdelta p hp
  have hcap := eventually_generalMovingBlockCap_le_N
    hE hs0 hst ht1 hc hreg htauG hdelta hroom
  have hscale := Step1.eventually_scale_facts
    hE hst ht1 hreg.1 hreg.2
  have hetaT := Gauss.rpow_neg_one_le_etaT_of_scale_ge
    d hE ht1 hc hreg.2
  have hWlarge := B.eventually_le_W (Real.exp ((4 * D) ^ 2))
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hsources, hblock, hcap, hscale, hetaT, hWlarge,
    d.dim, hNW, eventually_ge_atTop 1] with
      N hsourcesN hblockN hcapN hscaleN hetaTN hWlargeN hdimN hNWN hN
  intro k hk hkTop omega homega hwide u hu a
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  let Jbar := generalMovingBlockCap E s tauG delta N u
  have hv : v ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Set.Icc (s N) (t N) := ⟨hu.1, hu.2.trans hv.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hJ := (hblockN k hk hkTop omega homega hwide u hu).2
  have hsource := (hsourcesN omega homega uu).1
  have hJcap : APrimeJG.jG (Gauss.sample d) E N u omega
      (B.ell N u) (etaT E u) D <= (N : Real) :=
    hJ.trans (hcapN uu)
  have hu0 : 0 <= u := (hs0 N).trans hu.1
  have huv : u <= v := hu.2
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hu1 : u < 1 := huv.trans_lt hv1
  have hellu : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hetau : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hellSource : 0 < APrimeGeneralMovingRawSources.sourceEll s zetaSrc N := by
    unfold APrimeGeneralMovingRawSources.sourceEll
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hells := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
    have hNr : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    have hq : 0 < (N : Real) ^ zetaSrc := Real.rpow_pos_of_pos hNr _
    have : 0 < B.ell N (s N) := by
      simpa only [Band.ell] using
        (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
    positivity
  have hW : Real.exp 1 <= (B.W N : Real) := by
    exact (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (4 * D)])).trans hWlargeN
  have hlog : (4 * D) ^ 2 <= Real.log (B.W N : Real) := by
    rw [← Real.log_exp ((4 * D) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) hWlargeN
  have hlog4 : 4 <= Real.log (B.W N : Real) := by
    have : (4 : Real) <= (4 * D) ^ 2 := by nlinarith
    exact this.trans hlog
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have heta : (N : Real)⁻¹ <= etaT E u :=
    by simpa only [Real.rpow_neg_one] using
      hetaTN.trans (Gauss.etaT_le_of_le hE huWindow.2)
  have hAu : 1 <= B.scale E N u := by
    exact (Real.one_le_rpow hNr hc.le).trans (hscaleN uu).1
  have hAN : B.scale E N u <= (N : Real) :=
    scale_le_N hE hs0 ht1 hdimN.1 uu
  have hWL : (d.W N : Real) * (d.L N : Real) <= (N : Real) := by
    exact_mod_cast hdimN.1
  have hraw := APrimeFullQV.qvAt_full_absorbed d
    (E := E) (D := D) (s := s N) (u := u) (v := v)
    hE hu.1 hu0 huv hv1 N omega a hsource hellSource hD hW hlog4 hlog
    hNr heta hAu hAN hWL hNWN hJcap
  have hmono := rootProfile_mono_J E N u v D
    (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
    (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
    ((d.W N : Real)⁻¹) a hellu hetau
    (zero_le_one.trans (APrimeJG.one_le_jG (Gauss.sample d) E N u omega
      (by exact_mod_cast d.W_pos N))) hJ
  have hscaleInv : 0 <=
      (APrimeDriftTimeFamily.driftScale d E D N a (s N) v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d hE
      hv.1 hv1 N a)).le
  have hroot : 0 <= APrimeFullQV.rootProfile B E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
      (APrimeJG.jG (Gauss.sample d) E N u omega
        (B.ell N u) (etaT E u) D)
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((d.W N : Real)⁻¹) a :=
    rootProfile_nonneg E N u v D
      (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
      (APrimeJG.jG (Gauss.sample d) E N u omega
        (B.ell N u) (etaT E u) D)
      (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
      ((d.W N : Real)⁻¹) a
  have hsq := pow_le_pow_left₀ (mul_nonneg hscaleInv hroot)
    (mul_le_mul_of_nonneg_left hmono hscaleInv) 2
  exact ⟨hJ, hraw.trans hsq⟩

/-- A genuine positive-duration first cell realizes the same event and
positive widened support used by the profile theorem, with independent
positive losses satisfying the exact room condition. -/
theorem positive_first_cell_profile_hypotheses_witness :
    exists tauPrime c : Real, exists s t : Nat -> Real,
      0 < tauPrime /\ 0 < c /\
      (forall N, s N = 0) /\
      (forall N, 0 <= s N) /\
      (forall N, s N <= t N) /\
      (forall N, t N < 1) /\
      Cond272Reg B 0 s t c /\
      BoundsCore (Gauss.sample d) 0 s /\
      (1 / 100 : Real) + 2 * (1 / 100 : Real) + 2 / 15 < 1 /\
      ∀ᶠ N : Nat in atTop,
        s N < t N /\
        exists omega,
          omega ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t (1 / 100) (1 / 100) (1 / 100) N /\
          1 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N /\
          0 < APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t
              (APrimeGeneralMovingMesh.targetMesh 60)) 1
            (APrimeGeneralMovingDetFields.J 0 60 s) s t
            (APrimeGeneralMovingMesh.targetMesh 60) (1 / 100) 1 N 1 omega := by
  obtain ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
      hreg, hB, _hStep, hw⟩ :=
    APrimeGeneralMovingCommonSources.positive_length_common_support_witness
  refine ⟨tauPrime, c, s, t, htauPrime, hc, hsEq, hs0, hst, ht1,
    hreg, hB, by norm_num, ?_⟩
  have h := hw (1 / 100) (1 / 100) (1 / 100) (1 / 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [h] with N hN
  obtain ⟨hlen, omega, homega, hactive, hwide⟩ := hN
  exact ⟨hlen, omega, homega, hactive, by rw [hwide]; norm_num⟩

#print axioms generalMovingBlockCap
#print axioms eventually_generalMovingBlockCap_le_N
#print axioms eventually_qv_profile_on_common_support
#print axioms positive_first_cell_profile_hypotheses_witness

end
end RBM.APrimeGeneralMovingQVProfile
