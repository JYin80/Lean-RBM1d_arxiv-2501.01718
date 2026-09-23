/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothTransitionSupport
import RBM1D.Gauss.APrimeGeneralMovingQVAbsorption

/-!
# T613: same-time raw QV on the smooth transition

This module bounds the literal smooth-prefix gradient from the same-time raw
coordinate quadratic variation at every stored time.  In particular, the
first stored time is retained and no evolved `qvAt` profile is used.
-/

namespace RBM.APrimeGeneralMovingTransitionPrefixGradient

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d

private theorem band_toDims_eq (d' : Dims) : (band d').toDims = d' := by
  cases d'
  rfl

private theorem quadVar_band_toDims_eq (N : Nat)
    (F : Matrix (d.Idx N) (d.Idx N) Complex -> Complex)
    (M : Matrix (d.Idx N) (d.Idx N) Complex) :
    Gauss.quadVar (band d).toDims N F M = Gauss.quadVar d N F M := by
  rfl

/-- The literal block cap obtained from T597 on the smooth transition. -/
noncomputable def transitionBlockCap
    (E : Real) (s : Nat -> Real) (tauG delta : Real)
    (N : Nat) (u : Real) : Real :=
  1 + (N : Real)^tauG *
    (9 * Real.exp (Real.sqrt 3) *
      (((16 * (Real.exp 1)^2 + 1) * (N : Real)^(2 * delta)) *
        Step2Moment.ratR E s N u ^ 4) + 2)

/-- The absorbed same-time coordinate-QV rate. -/
noncomputable def transitionRawCoordRate
    (E : Real) (s : Nat -> Real)
    (zetaSrc tauG delta : Real) (N : Nat) (u : Real) : Real :=
  APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
    2 * (B.W N : Real)⁻¹ +
    APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u
      (transitionBlockCap E s tauG delta N u)

/-- The stored root rate in the exact T333 normalization. -/
noncomputable def storedRootRate
    (E : Real) (s : Nat -> Real)
    (zetaSrc tauG delta : Real) (N : Nat) (u : Real) : Real :=
  (Step2Moment.ratR E s N u ^ 4)⁻¹ *
    Real.sqrt (transitionRawCoordRate E s zetaSrc tauG delta N u) /
    APrimeSmoothWeightActual.threshold delta N

/-- The deterministic favorable bound for the full stored smooth prefix. -/
noncomputable def transitionPrefixGradientRate
    (E D : Real) (s t : Nat -> Real)
    (zetaSrc tauG delta : Real) (N k : Nat) : Real :=
  if hk : 0 < k then
    Real.exp 1 *
      (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
        Real.sqrt
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) *
          storedRootRate E s zetaSrc tauG delta N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j))
  else 0

/-- The prefix-gradient rate is nonnegative, including its inactive branch. -/
theorem transitionPrefixGradientRate_nonneg
    (E D : Real) (s t : Nat -> Real)
    (zetaSrc tauG delta : Real) (N k : Nat) :
    0 <= transitionPrefixGradientRate E D s t
      zetaSrc tauG delta N k := by
  classical
  rw [transitionPrefixGradientRate]
  split_ifs with hk
  · have hterm : 0 <=
        Real.sqrt (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) *
          storedRootRate E s zetaSrc tauG delta N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) := by
      have hroot : 0 <= storedRootRate E s
          zetaSrc tauG delta N
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) := by
        have hpow : 0 <= Step2Moment.ratR E s N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N 0) ^ 4 := by
          positivity
        unfold storedRootRate
        apply div_nonneg
        · exact mul_nonneg (inv_nonneg.mpr hpow) (Real.sqrt_nonneg _)
        · unfold APrimeSmoothWeightActual.threshold
          positivity
      exact mul_nonneg (Real.sqrt_nonneg _) hroot
    have hsup : 0 <=
        (Finset.range k).sup' ⟨0, Finset.mem_range.mpr hk⟩ (fun j =>
          Real.sqrt
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) *
            storedRootRate E s zetaSrc tauG delta N
              (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j)) :=
      hterm.trans (Finset.le_sup'
        (fun j => Real.sqrt
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j) *
          storedRootRate E s zetaSrc tauG delta N
            (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j))
        (Finset.mem_range.mpr hk))
    positivity
  · norm_num

private theorem scale_le_N (hE : |E| < 2) {s t : Nat -> Real}
    (hs0 : forall N, 0 <= s N) (ht1 : forall N, t N < 1)
    {N : Nat} (hdim : B.W N * B.L N <= N) (u : TimeIcc s t N) :
    B.scale E N (u : Real) <= (N : Real) := by
  obtain ⟨_, _heta0, _heta1, _, hellL⟩ := EEBridge.eeFacts B hE hs0 ht1 N u
  have hWL : (B.W N : Real) * (B.L N : Real) <= (N : Real) := by
    exact_mod_cast hdim
  change (B.W N : Real) * B.ell N (u : Real) * etaT E (u : Real) <= (N : Real)
  calc
    _ <= (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
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

private theorem transitionBlockCap_le_const_mul_rpow
    {E : Real} {s : Nat -> Real} {tauG delta : Real} {N : Nat} {u : Real}
    (hN : 1 <= N) (htauG : 0 <= tauG) (hdelta : 0 <= delta)
    (hR : Step2Moment.ratR E s N u ^ 4 <=
      (N : Real) ^ ((2 : Real) / 15)) :
    transitionBlockCap E s tauG delta N u <=
      (3 + 9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)) *
        (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
  have hn : (1 : Real) <= N := by exact_mod_cast hN
  have hn0 : (0 : Real) < N := by linarith
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
        (((16 * (Real.exp 1)^2 + 1) * (N : Real)^(2 * delta)) *
          (N : Real) ^ ((2 : Real) / 15))) =
      (9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)) *
        (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
    rw [← hmain]
    ring
  unfold transitionBlockCap
  calc
    1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          (((16 * (Real.exp 1)^2 + 1) * (N : Real)^(2 * delta)) *
            Step2Moment.ratR E s N u ^ 4) + 2) <=
      1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          (((16 * (Real.exp 1)^2 + 1) * (N : Real)^(2 * delta)) *
            (N : Real) ^ ((2 : Real) / 15)) + 2) := by gcongr
    _ <= (3 + 9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)) *
        (N : Real) ^ (tauG + 2 * delta + (2 : Real) / 15) := by
      rw [mul_add, hterm]
      nlinarith [Real.exp_pos (Real.sqrt 3), Real.exp_pos 1,
        Real.rpow_nonneg hn0.le (tauG + 2 * delta + (2 : Real) / 15)]

private theorem eventually_transitionBlockCap_le_N
    {E c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    {tauG delta : Real} (htauG : 0 < tauG) (hdelta : 0 < delta)
    (hroom : tauG + 2 * delta + (2 : Real) / 15 < 1) :
    ∀ᶠ N : Nat in atTop, forall u : TimeIcc s t N,
      transitionBlockCap E s tauG delta N (u : Real) <= (N : Real) := by
  have h30 := hreg.1.pow_thirty_le hE hst ht1
  have habs := SumZeroDyn.eventually_const_mul_rpow_le
    (3 + 9 * Real.exp (Real.sqrt 3) * (16 * (Real.exp 1)^2 + 1)) hroom
  filter_upwards [h30, d.dim, habs, eventually_ge_atTop 1]
    with N h30N hdim habsN hN u
  have hR := ratR_four_le_rpow_two_fifteenths hE hst ht1 hN hdim.1 h30N hs0 u
  exact (transitionBlockCap_le_const_mul_rpow hN htauG.le hdelta.le hR).trans (by
    simpa only [Real.rpow_one] using habsN)

private theorem generalMovingBlockCap_le_transitionBlockCap
    (E : Real) (s : Nat -> Real) (tauG delta : Real) (N : Nat) (u : Real) :
    APrimeGeneralMovingQVProfile.generalMovingBlockCap E s tauG delta N u <=
      transitionBlockCap E s tauG delta N u := by
  have he1 : (1 : Real) <= Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcoef : 4 * Real.exp 1 + 2 <= 16 * (Real.exp 1)^2 + 1 := by
    nlinarith [sq_nonneg (Real.exp 1 - 1)]
  unfold APrimeGeneralMovingQVProfile.generalMovingBlockCap transitionBlockCap
  gcongr

private theorem quadVar_coordFun_eq_stored
    {E : Real} (hE : |E| < 2) (N : Nat) (u : Real) (hu : u < 1)
    (omega : Gauss.Ω d) (a : LoopArg (d.L N) 2) :
    Gauss.quadVar d N (APrimeSmoothPrefix.coordFun d E N u a)
        ((Real.sqrt u : Complex) • Gauss.Xmat d N omega) =
      Gauss.quadVar d N
        (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a)
        (Gauss.Hflow d N u omega) := by
  have hz : (zt E u).im ≠ 0 := Gauss.zt_im_ne_zero_of_lt_one hE hu
  have hherm := Gauss.Hflow_isHermitian d N u omega
  calc
    _ = Gauss.quadVar d N
        (Gauss.loopObs d N (zt E u)
          (LoopData.idx ((Step2.sigPM, a) : LoopData (d.L N) 2)))
        (Gauss.Hflow d N u omega) := by
      rw [Gauss.Hflow_eq_realSmul]
      exact Gauss.quadVar_sub_const _ _ _
    _ = _ := by
      have hh := (EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs
        (B := B) hz Step2.sigPM hherm a).symm
      have hd : (band d).toDims = d := band_toDims_eq d
      cases hd
      exact hh

set_option maxHeartbeats 2000000 in
-- The proof expands the full raw-QV profile and its finite-dimensional casts.
/-- Every stored raw coordinate row, including `j = 0`, obeys the exact
same-time normalization on the identical common-event/transition sample. -/
theorem eventually_stored_raw_coord_qv_le
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
    (hzetaTau : zetaSrc <= tauG)
    (htauDelta : tauG <= delta / 16)
    (hdeltaC : delta <= c / 20)
    (hcapRoom : tauG + 2 * delta + (2 : Real) / 15 < 1) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall omega,
      omega ∈ (
        APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N ∩
        APrimeCrossJointSplit.transition d E D delta s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N)) ->
      ∀ j < k, ∀ a : LoopArg (d.L N) 2,
        let u := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N j
        (Step2Moment.ratR E s N u ^ 4)⁻¹ *
          (Real.sqrt
            (Gauss.quadVar d N
              (APrimeSmoothPrefix.coordFun d E N u a)
              ((Real.sqrt u : Complex) • Gauss.Xmat d N omega)) /
            Step2.tT B E N D u (zdist (d.L N) (a 0 - a 1))) /
          APrimeSmoothWeightActual.threshold delta N <=
        storedRootRate E s zetaSrc tauG delta N u := by
  have hsources := APrimeGeneralMovingCommonSources.eventually_common_sources
    hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG
  have hrunning :=
    APrimeGeneralMovingSmoothTransitionSupport.eventually_running_cap_on_smooth_transition
      (zetaSrc := zetaSrc) (zetaCtr := zetaCtr) (tauG := tauG)
      hE hD hs0 hst ht1 hc hreg hdelta
  have hcap := eventually_transitionBlockCap_le_N
    hE hs0 hst ht1 hc hreg htauG hdelta hcapRoom
  have hquad := APrimeGeneralMovingQVAbsorption.eventually_quadratic_source_comparison
    hE hs0 hst ht1 hc hreg hzetaSrc htauG hdelta
      hzetaTau htauDelta hdeltaC
  have hscale := Step1.eventually_scale_facts hE hst ht1 hreg.1 hreg.2
  have hetaT := Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hWlarge := B.eventually_le_W (Real.exp ((4 * D) ^ 2))
  have hNW := Step2.eventually_le_W_sq B
  filter_upwards [hsources, hrunning, hcap, hquad, hscale, hetaT,
    hWlarge, d.dim, hNW, eventually_ge_atTop 1] with
      N hsourcesN hrunningN hcapN hquadN hscaleN hetaTN hWlargeN
        hdimN hNWN hN
  intro k hk hkTop omega homega j hj a
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let u := cutNetPt s mesh N j
  let Jbar := transitionBlockCap E s tauG delta N u
  have huPrefix : u ∈ Set.Icc (s N) (cutNetPt s mesh N k) := by
    exact Step2Bootstrap.cutNetPt_mem_Icc
      (APrimeGeneralMovingMesh.targetMesh_pos D N) hj.le
  have hvWindow : cutNetPt s mesh N k ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Set.Icc (s N) (t N) :=
    ⟨huPrefix.1, huPrefix.2.trans hvWindow.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hsourceAll := hsourcesN omega homega.1 uu
  have hJnorm := hrunningN k hk hkTop omega homega.1 homega.2 u huPrefix
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N u :=
    Step2Moment.ratR_pos hE hs1 hu1
  have hJS : Step2.jS (Gauss.sample d) E D N u omega =
      APrimeGeneralMovingDetFields.J E D s N u omega *
        Step2Moment.ratR E s N u ^ 4 := by
    dsimp [APrimeGeneralMovingDetFields.J, Step2Moment.jSnorm]
    exact (div_mul_cancel₀ _ (pow_ne_zero 4 hR.ne')).symm
  have hJSto : Step2.jS (Gauss.sample d) E D N u omega <=
      ((16 * (Real.exp 1)^2 + 1) * (N : Real) ^ (2 * delta)) *
        Step2Moment.ratR E s N u ^ 4 := by
    rw [hJS]
    exact mul_le_mul_of_nonneg_right hJnorm (by positivity)
  have hJ : APrimeJG.jG (Gauss.sample d) E N u omega
      (B.ell N u) (etaT E u) D <= Jbar := by
    have hb := hsourceAll.2.2.2
    dsimp [uu] at hb
    exact hb.trans (by
      dsimp [Jbar, transitionBlockCap]
      gcongr)
  have hJcap : APrimeJG.jG (Gauss.sample d) E N u omega
      (B.ell N u) (etaT E u) D <= (N : Real) :=
    hJ.trans (hcapN uu)
  have hu0 : 0 <= u := (hs0 N).trans huWindow.1
  have hellu : 0 < B.ell N u := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have hells : 0 < B.ell N (s N) := by
    have hh := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (s N : Complex) by linarith)
  have hellSource : 0 < APrimeGeneralMovingRawSources.sourceEll s zetaSrc N := by
    unfold APrimeGeneralMovingRawSources.sourceEll
    have hNr0 : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have heta : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hW : Real.exp 1 <= (B.W N : Real) := by
    exact (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (4 * D)])).trans hWlargeN
  have hlog : (4 * D) ^ 2 <= Real.log (B.W N : Real) := by
    rw [← Real.log_exp ((4 * D) ^ 2)]
    exact Real.log_le_log (Real.exp_pos _) hWlargeN
  have hlog4 : 4 <= Real.log (B.W N : Real) := by
    have : (4 : Real) <= (4 * D) ^ 2 := by nlinarith
    exact this.trans hlog
  have hNr : (1 : Real) <= N := by exact_mod_cast hN
  have hetaN : (N : Real)⁻¹ <= etaT E u := by
    simpa only [Real.rpow_neg_one] using
      hetaTN.trans (Gauss.etaT_le_of_le hE huWindow.2)
  have hA : 1 <= B.scale E N u :=
    (Real.one_le_rpow hNr hc.le).trans (hscaleN uu).1
  have hAN : B.scale E N u <= (N : Real) :=
    scale_le_N hE hs0 ht1 hdimN.1 uu
  have hWL : (B.W N : Real) * (B.L N : Real) <= (N : Real) := by
    exact_mod_cast hdimN.1
  have heta1 : etaT E u <= 1 := etaT_le_one hE hu0
  have hW1 : (1 : Real) <= B.W N := by exact_mod_cast B.W_pos N
  have hleak : (B.W N : Real) * (B.L N : Real) *
      (B.W N : Real) ^ (-D) <= (etaT E u)⁻¹ * (B.scale E N u)⁻¹ :=
    APrimeFullQV.ExponentRows.leak_paid_by_dims hW1 hNr
      (lt_of_lt_of_le zero_lt_one hA) heta hWL hAN hNWN heta1 (by linarith)
  have hJbar1 : (1 : Real) <= Jbar := by
    dsimp [Jbar, transitionBlockCap]
    apply le_add_of_nonneg_right
    positivity
  have hcapCompare := generalMovingBlockCap_le_transitionBlockCap
    E s tauG delta N u
  have hquadJ : Lemma57.cFar2 (B.W N : Real) (B.ell N u) *
        (N : Real) ^ (zetaSrc / 2) *
        (B.ell N u / B.ell N (s N)) ^ ((3 : Real) / 2) <=
      B.scale E N u ^ ((1 : Real) / 6) * Jbar :=
    (hquadN uu).trans
      (mul_le_mul_of_nonneg_left hcapCompare (Real.rpow_nonneg
        (B.scale_nonneg E N hu1.le) _))
  have hfarMono := APrimeJGWidened.diagFarRate_mono
    (B := B) (D := D)
    (Smax := APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u)
    hW1 hellu heta
    (zero_le_one.trans (APrimeJG.one_le_jG (Gauss.sample d) E N u omega
      (by exact_mod_cast d.W_pos N))) hJ
  have hfarAbs := APrimeGeneralMovingQVAbsorption.diagFarRate_source_le_absorbed
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u)
    (D := D) (J := Jbar) hN hells hellu heta hA hJbar1 hquadJ hleak
  have hfar : APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D
        (APrimeJG.jG (Gauss.sample d) E N u omega
          (B.ell N u) (etaT E u) D)
        (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u) <=
      APrimeGeneralMovingQVAbsorption.absorbedFarRate E N u Jbar :=
    hfarMono.trans hfarAbs
  have hnear := APrimeGeneralMovingQVAbsorption.diagNearRate_source_eq
    (E := E) (zetaSrc := zetaSrc) (s := s) (N := N) (u := u) hN hells
  have hnear' :
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) (etaT E u) +
        2 * (B.W N : Real)⁻¹ =
      APrimeGeneralMovingQVAbsorption.nearSourceRate E s zetaSrc N u +
        2 * (B.W N : Real)⁻¹ := by
    exact hnear
  have hx : 0 < Step2Moment.ratR E s N u := hR
  have htheta : 0 < APrimeSmoothWeightActual.threshold delta N :=
    APrimeSmoothWeightActual.threshold_pos (δ := delta) (by omega)
  have hraw0 := APrimeFullQV.early_normalized_full (Gauss.sample d)
    hE hu0 hu1 N omega a hsourceAll.1 hellSource hD hW hlog4 hlog
    hNr hetaN hA hAN hWL hNWN hJcap hx htheta
  rw [Gauss.sample_H] at hraw0
  have hbridge : Gauss.quadVar d N
        (APrimeSmoothPrefix.coordFun d E N u a)
        ((Real.sqrt u : Complex) • Gauss.Xmat d N omega) =
      Gauss.quadVar (band d).toDims N
        (fun M' => MomentDuhamel.lkFun (band d) E N u M' Step2.sigPM a)
        (Gauss.Hflow d N u omega) := by
    calc
      _ = Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a)
          (Gauss.Hflow d N u omega) :=
        quadVar_coordFun_eq_stored hE N u hu1 omega a
      _ = _ := (quadVar_band_toDims_eq N
        (fun M' => MomentDuhamel.lkFun (band d) E N u M' Step2.sigPM a)
        (Gauss.Hflow d N u omega)).symm
  rw [← hbridge] at hraw0
  let q : Real := Gauss.quadVar d N
    (APrimeSmoothPrefix.coordFun d E N u a)
    ((Real.sqrt u : Complex) • Gauss.Xmat d N omega)
  let T : Real := Step2.tT B E N D u (zdist (d.L N) (a 0 - a 1))
  let x : Real := Step2Moment.ratR E s N u
  let theta : Real := APrimeSmoothWeightActual.threshold delta N
  let rate : Real := transitionRawCoordRate E s zetaSrc tauG delta N u
  have hrate :
      APrimeQVEndpoint.diagNearRate B N (B.ell N u)
          (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N) (etaT E u) +
        2 * (B.W N : Real)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D
          (APrimeJG.jG (Gauss.sample d) E N u omega
            (B.ell N u) (etaT E u) D)
          (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u) <= rate := by
    dsimp [rate, transitionRawCoordRate, Jbar]
    exact (add_le_add_left (le_of_eq hnear') _).trans
      (add_le_add_right hfar _)
  have hden : 0 <= x ^ 8 * theta ^ 2 := by positivity
  have hstored : q / (T ^ 2 * x ^ 8 * theta ^ 2) <= rate / (x ^ 8 * theta ^ 2) := by
    have hh := hraw0.trans (div_le_div_of_nonneg_right hrate hden)
    dsimp only [q, T, x, theta]
    exact hh
  have hT : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos (by exact_mod_cast B.W_pos N) _
  have hrate0 : 0 <= rate := by
    dsimp [rate, transitionRawCoordRate,
      APrimeGeneralMovingQVAbsorption.nearSourceRate,
      APrimeGeneralMovingQVAbsorption.absorbedFarRate, Jbar]
    have hcnear := Lemma57.cNear2_nonneg hW1 hellu
    positivity
  let z : Real := (x ^ 4)⁻¹ * (Real.sqrt q / T) / theta
  let C : Real := (x ^ 4)⁻¹ * Real.sqrt rate / theta
  have hq0 : 0 <= q := Gauss.quadVar_nonneg _ _
  have hxinv : 0 <= (x ^ 4)⁻¹ := inv_nonneg.mpr (pow_nonneg hx.le 4)
  have hz0 : 0 <= z := by
    dsimp [z]
    exact div_nonneg
      (mul_nonneg hxinv (div_nonneg (Real.sqrt_nonneg _) hT.le)) htheta.le
  have hC0 : 0 <= C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg hxinv (Real.sqrt_nonneg _)) htheta.le
  have hzsq : z ^ 2 = q / (T ^ 2 * x ^ 8 * theta ^ 2) := by
    dsimp [z]
    field_simp [hx.ne', hT.ne', htheta.ne']
    rw [Real.sq_sqrt hq0]
  have hCsq : C ^ 2 = rate / (x ^ 8 * theta ^ 2) := by
    dsimp [C]
    field_simp [hx.ne', htheta.ne']
    rw [Real.sq_sqrt hrate0]
  change z <= C
  nlinarith [hstored, hzsq, hCsq]

/-- The literal prefix gradient is bounded by the stored raw-QV rate on the
same smooth-transition sample. -/
theorem eventually_prefixGradient_le_on_smooth_transition
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
    (hzetaTau : zetaSrc <= tauG)
    (htauDelta : tauG <= delta / 16)
    (hdeltaC : delta <= c / 20)
    (hcapRoom : tauG + 2 * delta + (2 : Real) / 15 < 1) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      forall omega,
      omega ∈ (
        APrimeGeneralMovingCommonSources.commonEvent
          E D s t zetaSrc zetaCtr tauG N ∩
        APrimeCrossJointSplit.transition d E D delta s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N)) ->
        APrimeCrossJointSplit.prefixGradient d E D delta s
          (APrimeGeneralMovingMesh.targetMesh D) N k
          (APrimeSmoothWeightActual.canonicalM d s t
            (APrimeGeneralMovingMesh.targetMesh D) N) omega <=
        transitionPrefixGradientRate E D s t
          zetaSrc tauG delta N k := by
  classical
  have hrows := eventually_stored_raw_coord_qv_le
    hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdelta
      hzetaTau htauDelta hdeltaC hcapRoom
  filter_upwards [hrows, eventually_ge_atTop 1] with N hrowsN hN
  intro k hk hkTop omega homega
  let mesh := APrimeGeneralMovingMesh.targetMesh D
  let m := APrimeSmoothWeightActual.canonicalM d s t mesh N
  let Kraw : Nat -> Real := fun j =>
    (Finset.univ : Finset (LoopArg (d.L N) 2)).sup' Finset.univ_nonempty
      (fun a =>
        Real.sqrt (Gauss.quadVar d N
          (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
          ((Real.sqrt (cutNetPt s mesh N j) : Complex) •
            Gauss.Xmat d N omega)) /
        Step2.tT B E N D (cutNetPt s mesh N j)
          (zdist (d.L N) (a 0 - a 1)))
  let G : Nat -> Real := fun j =>
    Real.sqrt (cutNetPt s mesh N j) *
      ((Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4)⁻¹ * Kraw j)
  let R : Real := (Finset.range k).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun j => Real.sqrt (cutNetPt s mesh N j) *
      storedRootRate E s zetaSrc tauG delta N (cutNetPt s mesh N j))
  have hNpos : 0 < N := by omega
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hm : 1 <= m := APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hu1 : ∀ j < k, cutNetPt s mesh N j < 1 := by
    intro j hj
    have huWindow := MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset (hj.le.trans hkTop))
    exact huWindow.2.trans_lt (ht1 N)
  have htheta : 0 < APrimeSmoothWeightActual.threshold delta N :=
    APrimeSmoothWeightActual.threshold_pos (δ := delta) hNpos
  have hKraw : ∀ j < k,
      Kraw j <= Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4 *
        APrimeSmoothWeightActual.threshold delta N *
        storedRootRate E s zetaSrc tauG delta N (cutNetPt s mesh N j) := by
    intro j hj
    apply Finset.sup'_le
    intro a _ha
    have hr := hrowsN k hk hkTop omega homega j hj a
    let u := cutNetPt s mesh N j
    have hx : 0 < Step2Moment.ratR E s N u :=
      Step2Moment.ratR_pos hE hs1 (hu1 j hj)
    have hmul := mul_le_mul_of_nonneg_right hr
      (mul_nonneg (pow_nonneg hx.le 4) htheta.le)
    dsimp only [u] at hx hmul ⊢
    calc
      _ = ((Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4)⁻¹ *
            (Real.sqrt (Gauss.quadVar d N
              (APrimeSmoothPrefix.coordFun d E N (cutNetPt s mesh N j) a)
              ((Real.sqrt (cutNetPt s mesh N j) : Complex) •
                Gauss.Xmat d N omega)) /
              Step2.tT B E N D (cutNetPt s mesh N j)
                (zdist (d.L N) (a 0 - a 1))) /
            APrimeSmoothWeightActual.threshold delta N) *
          (Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4 *
            APrimeSmoothWeightActual.threshold delta N) := by
        field_simp [hx.ne', htheta.ne']
      _ <= storedRootRate E s zetaSrc tauG delta N
            (cutNetPt s mesh N j) *
          (Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4 *
            APrimeSmoothWeightActual.threshold delta N) := hmul
      _ = _ := by ring
  have hG : ∀ j < k,
      G j <= APrimeSmoothWeightActual.threshold delta N *
        (Real.sqrt (cutNetPt s mesh N j) *
          storedRootRate E s zetaSrc tauG delta N (cutNetPt s mesh N j)) := by
    intro j hj
    have hraw := hKraw j hj
    have hx : 0 < Step2Moment.ratR E s N (cutNetPt s mesh N j) :=
      Step2Moment.ratR_pos hE hs1 (hu1 j hj)
    have hsqrt : 0 <= Real.sqrt (cutNetPt s mesh N j) := Real.sqrt_nonneg _
    have hinv : 0 <=
        (Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4)⁻¹ := by positivity
    dsimp only [G]
    calc
      _ <= Real.sqrt (cutNetPt s mesh N j) *
          ((Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4)⁻¹ *
            (Step2Moment.ratR E s N (cutNetPt s mesh N j) ^ 4 *
              APrimeSmoothWeightActual.threshold delta N *
              storedRootRate E s zetaSrc tauG delta N
                (cutNetPt s mesh N j))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hraw hinv) hsqrt
      _ = _ := by field_simp [hx.ne']
  have hS : (Finset.range k).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ G <=
      APrimeSmoothWeightActual.threshold delta N * R := by
    apply Finset.sup'_le
    intro j hjmem
    have hj : j < k := Finset.mem_range.mp hjmem
    calc
      G j <= APrimeSmoothWeightActual.threshold delta N *
          (Real.sqrt (cutNetPt s mesh N j) *
            storedRootRate E s zetaSrc tauG delta N
              (cutNetPt s mesh N j)) := hG j hj
      _ <= APrimeSmoothWeightActual.threshold delta N * R :=
        mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun i => Real.sqrt (cutNetPt s mesh N i) *
            storedRootRate E s zetaSrc tauG delta N
              (cutNetPt s mesh N i)) hjmem) htheta.le
  have hpref := APrimeSmoothWeightActual.sqrt_quadVar_prefixMatrix_le_exp_max d
    (E := E) (D := D) (s := s) (mesh := mesh) (N := N) (k := k) (m := m)
    hE hs1 hNpos (by omega) hm hu1
    (APrimeSmoothWeightActual.canonicalM_calibration d s t mesh N k hkTop)
    (Gauss.Xmat d N omega)
  have hpref' : Real.sqrt (Gauss.quadVar d N
      (fun X => ((APrimeSmoothWeightActual.prefixMatrix d E D s mesh N k m X : Real) : Complex))
      (Gauss.Xmat d N omega)) <=
      Real.exp 1 * (Finset.range k).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ G := by
    simpa only [G, Kraw] using hpref
  change Real.sqrt (Gauss.quadVar d N
      (fun X => ((APrimeSmoothWeightActual.prefixMatrix d E D s mesh N k m X : Real) : Complex))
      (Gauss.Xmat d N omega)) /
      APrimeSmoothWeightActual.threshold delta N <=
      transitionPrefixGradientRate E D s t zetaSrc tauG delta N k
  calc
    _ <= (Real.exp 1 *
          (Finset.range k).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ G) /
        APrimeSmoothWeightActual.threshold delta N :=
      div_le_div_of_nonneg_right hpref' htheta.le
    _ <= (Real.exp 1 *
          (APrimeSmoothWeightActual.threshold delta N * R)) /
        APrimeSmoothWeightActual.threshold delta N :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS (Real.exp_pos 1).le) htheta.le
    _ = transitionPrefixGradientRate E D s t zetaSrc tauG delta N k := by
      rw [transitionPrefixGradientRate, dif_pos (by omega)]
      dsimp only [R, mesh]
      field_simp [htheta.ne']

#print axioms transitionBlockCap
#print axioms transitionRawCoordRate
#print axioms storedRootRate
#print axioms transitionPrefixGradientRate
#print axioms transitionPrefixGradientRate_nonneg
#print axioms eventually_stored_raw_coord_qv_le
#print axioms eventually_prefixGradient_le_on_smooth_transition

end
end RBM.APrimeGeneralMovingTransitionPrefixGradient
