/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import RBM1D.Gauss.APrimeFirstCellEGFar

/-!
# T586: pointwise drift sources on the general moving common event

The source package below is pathwise on T579's single sample.  It keeps the
raw length-three source, the two-charge centered loss, the literal flow good
event, and the actual block-resolved Green control separate.  The far theorem
then applies the generic deterministic proof of (5.35), before time
integration or any stopping argument.
-/

namespace RBM.APrimeGeneralMovingDriftSource

open Filter Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- T579's exact support-local cap, with the moving `ratR ^ 4` left visible. -/
noncomputable def blockCap (E : Real) (s : Nat -> Real)
    (tauG delta : Real) (N : Nat) (u : Real) : Real :=
  1 + (N : Real)^tauG *
    (9 * Real.exp (Real.sqrt 3) *
      ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
        Step2Moment.ratR E s N u ^ 4) + 2)

/-- The exact pointwise sources used by the deterministic proof of (5.35).
All four rows are read from the same `omega` and the same moving time `u`.
The centered coefficient is `4 * N^zetaCtr * r_u`: the event contributes
`2 * qExt`, while `EGDef.norm_eGpm_le` contributes its outer factor `2W`. -/
theorem pointwise_source_package
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    {zetaSrc zetaCtr tauG : Real}
    {N : Nat} {omega : Ω d}
    (homega : omega ∈
      APrimeGeneralMovingCommonSources.commonEvent
        E D s t zetaSrc zetaCtr tauG N)
    (u : TimeIcc s t N) (a1 a2 : ZMod (d.L N)) :
    let ellu := B.ell N (u : Real)
    let ells := B.ell N (s N)
    let etau := etaT E (u : Real)
    let ru := ellu / ells
    let L3 : ZMod (d.L N) -> Real := fun b =>
      norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
        (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
    (forall b, L3 b <=
      (N : Real)^zetaSrc * ru^2 * (B.scale E N (u : Real))⁻¹ ^ (2 : Nat)) /\
    norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      (4 * (N : Real)^zetaCtr * ru) * (ellu * etau)⁻¹ *
        ∑ b, L3 b /\
    (forall (x : ZMod (d.L N)) (p : ZMod (d.L N) × Fin (d.W N)),
      ∑ r, Lemma57.blkW (d.L N) (d.W N) r x *
          norm (green (Hflow d N (u : Real) omega) (zt E (u : Real)) r p) <=
        flowDelta d E t N + (d.W N : Real)⁻¹) /\
    (forall (y : ZMod (d.L N)) (r : ZMod (d.L N) × Fin (d.W N)),
      ∑ p, Lemma57.blkW (d.L N) (d.W N) p y *
          norm (green (Hflow d N (u : Real) omega) (zt E (u : Real)) r p) <=
        flowDelta d E t N + (d.W N : Real)⁻¹) := by
  dsimp only
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  have hCarrier :=
    APrimeGeneralMovingCommonSources.commonEvent_subset_rawCarrier
      E D s t zetaSrc zetaCtr tauG N homega
  rcases hCarrier with ⟨⟨⟨hSource, hGood⟩, hCentered⟩, _hBlock⟩
  have hu0 : 0 <= (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hellu : 0 < B.ell N (u : Real) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) ((u : Real) : Complex) by linarith)
  have hells : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) ((s N : Real) : Complex) by linarith)
  have heta : 0 < etaT E (u : Real) := etaT_pos hE hu1
  have hW : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
  let L3 : ZMod (d.L N) -> Real := fun b =>
    norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
  have hL3 : forall b, L3 b <=
      (N : Real)^zetaSrc * (B.ell N (u : Real) / B.ell N (s N))^2 *
        (B.scale E N (u : Real))⁻¹ ^ (2 : Nat) := by
    intro b
    let v : LoopData (d.L N) 3 := (![false, true, true], ![a2, b, a1])
    have hv := APrimeGeneralMovingRawSources.rawThree_on_sourceGood u hSource v
    have hidx : v.idx = (⟨[false, true, true], [a2, b, a1]⟩ :
        LoopIdx (ZMod (d.L N))) := by
      simp [v, LoopData.idx, List.ofFn_succ]
    rw [Gauss.sample_Lval, hidx] at hv
    simpa only [L3, APrimeGeneralMovingRawSources.sourceC3, mul_assoc] using hv
  let csrc : Real := (N : Real)^zetaCtr *
    (2 * APrimeGeneralMovingControlExtension.qExt E s t N (u : Real))
  have hone : forall sigma (b : ZMod (d.L N)),
      norm (Matrix.trace ((Gsig (Hflow d N (u : Real) omega) (zt E (u : Real)) sigma -
        mSigma E sigma • (1 : Matrix (d.Idx N) (d.Idx N) Complex)) *
          Eblk (d.L N) (d.W N) b)) <= csrc := by
    intro sigma b
    simpa only [APrimeGeneralMovingTwoChargeModulus.centeredTrace, csrc] using
      hCentered sigma (u, b)
  have hbase := EGDef.norm_eGpm_le (d.three_le_L N)
    (Hflow_isHermitian d N (u : Real) omega) (mSigma E) hone a1 a2
  have hq : APrimeGeneralMovingControlExtension.qExt E s t N (u : Real) =
      (B.ell N (u : Real) / B.ell N (s N)) /
        B.scale E N (u : Real) := by
    rw [APrimeGeneralMovingControlExtension.qExt_eq_q u.2]
    rfl
  have hcoef : 2 * (d.W N : Real) * csrc =
      (4 * (N : Real)^zetaCtr *
        (B.ell N (u : Real) / B.ell N (s N))) *
          (B.ell N (u : Real) * etaT E (u : Real))⁻¹ := by
    dsimp [csrc]
    rw [hq]
    change 2 * (d.W N : Real) *
      ((N : Real)^zetaCtr *
        (2 * ((B.ell N (u : Real) / B.ell N (s N)) /
          ((d.W N : Real) * B.ell N (u : Real) * etaT E (u : Real))))) = _
    field_simp
    ring
  rw [hcoef] at hbase
  have hm : norm (mE E) = 1 := norm_mE hE.le
  have hgoodU : GoodEvent (green (Hflow d N (u : Real) omega) (zt E (u : Real)))
      (mE E) (flowDelta d E t N) := hGood (u : Real) u.2
  refine ⟨hL3, ?_, ?_, ?_⟩
  · simpa only [L3, mul_assoc] using hbase
  · intro x p
    exact APrimeFirstCellEGFar.goodEvent_column_block_average hgoodU hm x p
  · intro y r
    exact APrimeFirstCellEGFar.goodEvent_row_block_average hgoodU hm y r

/-- The far branch of (5.35) at one time and one sample of T579's common
event.  The block variable is the actual `jG`; no first-cell cap or
`Step2.jS` substitution is made. -/
theorem pointwise_far_source_bound
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    {zetaSrc zetaCtr tauG : Real}
    {N : Nat} {omega : Ω d}
    (homega : omega ∈
      APrimeGeneralMovingCommonSources.commonEvent
        E D s t zetaSrc zetaCtr tauG N)
    (u : TimeIcc s t N) (a1 a2 : ZMod (d.L N))
    (hfar : ellStar (d.W N : Real) (B.ell N (u : Real)) <=
      (zdist (d.L N) (a2 - a1) : Real)) :
    let ellu := B.ell N (u : Real)
    let ells := B.ell N (s N)
    let etau := etaT E (u : Real)
    let ru := ellu / ells
    let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
    let kappa1 := 4 * (N : Real)^zetaCtr * ru
    let kappa2 := flowDelta d E t N + (d.W N : Real)⁻¹
    norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      etau⁻¹ * kappa1 *
        (Lemma57.cFar (d.W N : Real) ellu * J * kappa2 +
          J * Real.sqrt J *
            (168 * ((d.W N : Real) * ellu * etau)⁻¹ +
              (d.L N : Real) * Real.sqrt ((d.W N : Real)^(-D)) / ellu)) *
        tailT (d.W N : Real) ellu etau D (zdist (d.L N) (a2 - a1)) := by
  dsimp only
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  have hu0 : 0 <= (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hW : 1 <= (d.W N : Real) := by exact_mod_cast B.one_le_W N
  have hWpos : 0 < (d.W N : Real) := by linarith
  have hellu : 1 <= B.ell N (u : Real) :=
    one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hells : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) ((s N : Real) : Complex) by linarith)
  have heta : 0 < etaT E (u : Real) := etaT_pos hE hu1
  let ellu := B.ell N (u : Real)
  let etau := etaT E (u : Real)
  let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
  let kappa1 := 4 * (N : Real)^zetaCtr *
    (ellu / B.ell N (s N))
  let kappa2 := flowDelta d E t N + (d.W N : Real)⁻¹
  let Gm := APrimeJG.gmBlk (sample d) E N (u : Real) omega
  let L2 : ZMod (d.L N) -> ZMod (d.L N) -> Real := fun x y =>
    (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[true, false], [x, y]⟩).re
  let L3 : ZMod (d.L N) -> Real := fun b =>
    norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
  have hsrc := pointwise_source_package hE hs0 hst ht1 homega u a1 a2
  dsimp only at hsrc
  rcases hsrc with ⟨_hL3, hEG, hC, hR⟩
  have hJ : 1 <= J :=
    APrimeJG.one_le_jG (sample d) E N (u : Real) omega hWpos
  have hJ0 : 0 <= J := by linarith
  have hkappa1 : 0 <= kappa1 := by
    dsimp [kappa1, ellu]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (div_nonneg (by linarith) hells.le)
  have hkappa2 : 0 <= kappa2 := by
    dsimp [kappa2, flowDelta]
    exact add_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr
        (B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _)
      (inv_nonneg.mpr hWpos.le)
  have hGm : forall x y, 0 <= Gm x y :=
    APrimeJG.gmBlk_nonneg (sample d) E N (u : Real) omega
  have h531 : forall x y : ZMod (d.L N),
      ellStar (d.W N : Real) ellu / 2 <= (zdist (d.L N) (x - y) : Real) ->
      L2 x y <= J * tailT (d.W N : Real) ellu etau D
        (zdist (d.L N) (x - y)) := by
    intro x y hxy
    exact (APrimeFirstCellEGFar.two_loop_re_le_gsqBlk
      (sample d) E N (u : Real) omega x y).trans
      (APrimeJG.gsqBlk_le_jG_mul_tailT
        (sample d) E N (u : Real) omega hWpos x y hxy)
  have h42 : forall x y : ZMod (d.L N),
      ellStar (d.W N : Real) ellu / 2 <= (zdist (d.L N) (x - y) : Real) ->
      Gm x y <= Real.sqrt J *
        Real.sqrt (tailT (d.W N : Real) ellu etau D
          (zdist (d.L N) (x - y))) := by
    intro x y hxy
    have h := APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail
      (sample d) E N (u : Real) omega (ℓu := ellu) (ηu := etau)
        (D := D) x y hxy
    rw [Real.sqrt_mul hJ0] at h
    exact h
  have h558a : forall b, (zdist (d.L N) (a2 - b) : Real) <=
      ellStar (d.W N : Real) ellu / 2 ->
      L3 b <= (L2 a1 a2 + L2 a1 b) * kappa2 := by
    intro b _
    exact Lemma57.gloop_h558a' (d.L N) (d.W N)
      (Hflow_isHermitian d N (u : Real) omega) a2 a1 b hkappa2
      (fun p _ => hC a2 p) (fun r _ => hR b r)
  have h558b : forall b, (zdist (d.L N) (a1 - b) : Real) <=
      ellStar (d.W N : Real) ellu / 2 ->
      L3 b <= (L2 a1 a2 + L2 b a2) * kappa2 := by
    intro b _
    exact Lemma57.gloop_h558b' (d.L N) (d.W N)
      (Hflow_isHermitian d N (u : Real) omega) a2 a1 b hkappa2
      (fun p _ => hC b p) (fun r _ => hR a1 r)
  have h560 : forall b, L3 b <= Gm a2 b * Gm a1 b * Gm a2 a1 := by
    intro b
    exact APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk
      (sample d) E N (u : Real) omega a1 a2 b
  have hEG' :
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
        kappa1 * (ellu * etau)⁻¹ * ∑ b, L3 b := by
    simpa only [kappa1, ellu, etau, L3, mul_assoc] using hEG
  exact Lemma57.eG_far_le (d.L N) hW (by simpa only [ellu] using hellu)
    (by simpa only [etau] using heta) hJ hfar hkappa1 hkappa2 hGm
      h531 h42 h558a h558b h560 hEG'

private theorem pointwise_near_source_bound
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    {zetaSrc zetaCtr tauG : Real}
    {N : Nat} (hN : 0 < N) {omega : Ω d}
    (homega : omega ∈
      APrimeGeneralMovingCommonSources.commonEvent
        E D s t zetaSrc zetaCtr tauG N)
    (u : TimeIcc s t N) (hlog : 4 <= Real.log (d.W N : Real))
    (a1 a2 : ZMod (d.L N))
    (hnear : (zdist (d.L N) (a2 - a1) : Real) <=
      ellStar (d.W N : Real) (B.ell N (u : Real))) :
    let ellu := B.ell N (u : Real)
    let ells := B.ell N (s N)
    let etau := etaT E (u : Real)
    let ru := ellu / ells
    let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
    norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
          Lemma57.cNear (d.W N : Real) ellu *
            tailT (d.W N : Real) ellu etau D (zdist (d.L N) (a2 - a1)) +
        (4 * (N : Real)^zetaCtr * ru) * (ellu * etau)⁻¹ * (d.L N : Real) *
          (etau⁻¹ * J *
            tailT (d.W N : Real) ellu etau D
              (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) := by
  dsimp only
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  have hu0 : 0 <= (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hW : 1 <= (d.W N : Real) := by exact_mod_cast B.one_le_W N
  have hellu : 1 <= B.ell N (u : Real) :=
    one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hells : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) ((s N : Real) : Complex) by linarith)
  have heta : 0 < etaT E (u : Real) := etaT_pos hE hu1
  have hNr : 0 < (N : Real) := by exact_mod_cast hN
  let ellu := B.ell N (u : Real)
  let etau := etaT E (u : Real)
  let ru := ellu / B.ell N (s N)
  let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
  let L3 : ZMod (d.L N) -> Real := fun b =>
    norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
  have hsrc := pointwise_source_package hE hs0 hst ht1 homega u a1 a2
  dsimp only at hsrc
  rcases hsrc with ⟨hL3src, hEGsrc, _hC, _hR⟩
  have hL3 : forall b, L3 b <=
      1 * (N : Real)^zetaSrc * ru^2 *
        (((B.W N : Real) * ellu * etau)^2)⁻¹ := by
    intro b
    have hb := hL3src b
    simpa only [one_mul, L3, ru, ellu, etau, Band.scale, inv_pow, mul_assoc] using hb
  have hEG :
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
        (2 * (2 : Real) * (N : Real)^zetaCtr * ru) *
          (ellu * etau)⁻¹ * ∑ b, L3 b := by
    change norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      (4 * (N : Real)^zetaCtr * ru) *
        (ellu * etau)⁻¹ * ∑ b, L3 b at hEGsrc
    convert hEGsrc using 1 <;> ring
  have hJ : 1 <= J := APrimeJG.one_le_jG
    (sample d) E N (u : Real) omega (by exact_mod_cast d.W_pos N)
  let rho := etau⁻¹ * J *
    tailT (d.W N : Real) ellu etau D
      (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)
  have hrho : 0 <= rho := by
    dsimp [rho]
    have htail : 0 <= tailT (d.W N : Real) ellu etau D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu) :=
      tailT_nonneg (by positivity) _
    positivity
  have h554 : forall b,
      Lemma57.ellStarStar (d.W N : Real) ellu <
        (zdist (d.L N) (a2 - b) : Real) ->
      L3 b <= rho := by
    intro b hb
    have htriple := APrimeDriftNearTriple.gaussian_three_near_far_le
      d hE N hu1 omega (D := D) (by linarith : 0 < ellu) hlog
        a1 a2 b hnear hb
    simpa only [L3, rho, J, ellu, etau, Gauss.sample_H,
      APrimeDriftNearAbsorb.gap] using htriple
  have hnear' : (zdist (d.L N) (a2 - a1) : Real) <=
      ellStar (d.W N : Real) ellu := by simpa only [ellu] using hnear
  have hsplit := APrimeEGNearScaled.eG_near_le_scaled
    (d.L N) (D := D) hW (by simpa only [ellu] using hellu)
      hells (by simpa only [etau] using heta) hNr
      (by norm_num : (0 : Real) < 2) (by norm_num : (0 : Real) < 1)
      hrho hnear' hL3 h554 hEG
  change norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <= _ at hsplit
  simpa only [one_mul, mul_one, rho, J, ru, ellu, etau] using
    (hsplit.trans_eq (by ring))

private theorem far_rhs_mono
    {W L ell eta D kappa1 kappa2 J K dist : Real}
    (hW : 1 <= W) (hell : 1 <= ell) (heta : 0 < eta)
    (hL : 0 <= L)
    (hkappa1 : 0 <= kappa1) (hkappa2 : 0 <= kappa2)
    (hJ : 1 <= J) (hJK : J <= K) :
    eta⁻¹ * kappa1 *
        (Lemma57.cFar W ell * J * kappa2 +
          J * Real.sqrt J *
            (168 * (W * ell * eta)⁻¹ +
              L * Real.sqrt (W^(-D)) / ell)) *
        tailT W ell eta D dist <=
      eta⁻¹ * kappa1 *
        (Lemma57.cFar W ell * K * kappa2 +
          K * Real.sqrt K *
            (168 * (W * ell * eta)⁻¹ +
              L * Real.sqrt (W^(-D)) / ell)) *
        tailT W ell eta D dist := by
  have hJ0 : 0 <= J := by linarith
  have hK0 : 0 <= K := hJ0.trans hJK
  have hcFar : 0 <= Lemma57.cFar W ell :=
    Lemma57.cFar_nonneg hW (by linarith)
  have hspatial : 0 <= 168 * (W * ell * eta)⁻¹ +
      L * Real.sqrt (W^(-D)) / ell := by positivity
  have hcase1 : Lemma57.cFar W ell * J * kappa2 <=
      Lemma57.cFar W ell * K * kappa2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJK hcFar) hkappa2
  have hsqrt : Real.sqrt J <= Real.sqrt K := Real.sqrt_le_sqrt hJK
  have hJsqrt : J * Real.sqrt J <= K * Real.sqrt K :=
    mul_le_mul hJK hsqrt (Real.sqrt_nonneg _) hK0
  have hcase2 : J * Real.sqrt J *
      (168 * (W * ell * eta)⁻¹ + L * Real.sqrt (W^(-D)) / ell) <=
      K * Real.sqrt K *
      (168 * (W * ell * eta)⁻¹ + L * Real.sqrt (W^(-D)) / ell) :=
    mul_le_mul_of_nonneg_right hJsqrt hspatial
  have hsum := add_le_add hcase1 hcase2
  have hpre : 0 <= eta⁻¹ * kappa1 := by positivity
  have htail : 0 <= tailT W ell eta D dist :=
    tailT_nonneg (by linarith) dist
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum hpre) htail

/-- On positive widened support, the far branch uses T579's literal running
cap.  The quantifier order keeps the three stochastic losses independent and
the same resident `omega` supplies both the drift sources and the cap. -/
theorem eventually_far_on_common_support
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
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
      ∀ a1 a2 : ZMod (d.L N),
      ellStar (d.W N : Real) (B.ell N u) <=
        (zdist (d.L N) (a2 - a1) : Real) ->
      let Jbar := blockCap E s tauG delta N u
      APrimeJG.jG (sample d) E N u omega
          (B.ell N u) (etaT E u) D <= Jbar /\
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N u omega) (zt E u) a1 a2) <=
        (etaT E u)⁻¹ *
          (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
          (Lemma57.cFar (d.W N : Real) (B.ell N u) * Jbar *
              (flowDelta d E t N + (d.W N : Real)⁻¹) +
            Jbar * Real.sqrt Jbar *
              (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ +
                (d.L N : Real) * Real.sqrt ((d.W N : Real)^(-D)) /
                  B.ell N u)) *
          tailT (d.W N : Real) (B.ell N u) (etaT E u) D
            (zdist (d.L N) (a2 - a1)) := by
  have hcap :=
    APrimeGeneralMovingCommonSources.eventually_block_cap_on_widened_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdelta p hp
  filter_upwards [hcap] with N hcapN
  intro k hk hkTop omega homega hwide u hu a1 a2 hfar
  have hcapU := hcapN k hk hkTop omega homega hwide u hu
  have hend : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Set.Icc (s N) (t N) :=
    ⟨hu.1, hu.2.trans hend.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hbase := pointwise_far_source_bound hE hs0 hst ht1
    homega uu a1 a2 hfar
  dsimp only at hbase
  let J := APrimeJG.jG (sample d) E N u omega
    (B.ell N u) (etaT E u) D
  let Jbar := blockCap E s tauG delta N u
  have hW : 1 <= (d.W N : Real) := by exact_mod_cast B.one_le_W N
  have hu0 : 0 <= u := (hs0 N).trans huWindow.1
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hell : 1 <= B.ell N u :=
    one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have heta : 0 < etaT E u := etaT_pos hE hu1
  have hJ : 1 <= J := APrimeJG.one_le_jG
    (sample d) E N u omega (by exact_mod_cast d.W_pos N)
  have hJcap : J <= Jbar := by
    simpa only [J, Jbar, blockCap] using hcapU.2
  have hkappa1 : 0 <=
      4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N)) := by
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hells : 0 < B.ell N (s N) := by
      have h := one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1
      simpa only [Band.ell] using
        (show 0 < ellHat (B.L N) ((s N : Real) : Complex) by linarith)
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (div_nonneg (by linarith) hells.le)
  have hkappa2 : 0 <= flowDelta d E t N + (d.W N : Real)⁻¹ := by
    have hWpos : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
    unfold flowDelta
    exact add_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr
        (B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _)
      (inv_nonneg.mpr hWpos.le)
  have hmono := far_rhs_mono hW hell heta (Nat.cast_nonneg _) hkappa1 hkappa2 hJ hJcap
    (L := (d.L N : Real)) (D := D)
    (dist := (zdist (d.L N) (a2 - a1) : Real))
  refine ⟨?_, hbase.trans ?_⟩
  · exact hJcap
  · simpa only [J, Jbar] using hmono

/-- The matching near-output branch on the same common resident and the
same running cap.  The raw length-three loss `zetaSrc` and the centered loss
`zetaCtr` remain independent; the far-internal remainder is displayed
explicitly and is not time-integrated or absorbed into a stopping argument. -/
theorem eventually_near_on_common_support
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
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
      ∀ a1 a2 : ZMod (d.L N),
      (zdist (d.L N) (a2 - a1) : Real) <=
        ellStar (d.W N : Real) (B.ell N u) ->
      let Jbar := blockCap E s tauG delta N u
      APrimeJG.jG (sample d) E N u omega
          (B.ell N u) (etaT E u) D <= Jbar /\
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N u omega) (zt E u) a1 a2) <=
        4 * (N : Real)^(zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
            (B.ell N u / B.ell N (s N))^3 *
            Lemma57.cNear (d.W N : Real) (B.ell N u) *
              tailT (d.W N : Real) (B.ell N u) (etaT E u) D
                (zdist (d.L N) (a2 - a1)) +
          (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
            (B.ell N u * etaT E u)⁻¹ * (d.L N : Real) *
              ((etaT E u)⁻¹ * Jbar *
                tailT (d.W N : Real) (B.ell N u) (etaT E u) D
                  (APrimeDriftNearAbsorb.gap
                    (d.W N : Real) (B.ell N u))) := by
  have hcap :=
    APrimeGeneralMovingCommonSources.eventually_block_cap_on_widened_support
      hE hD hs0 hst ht1 hc hreg hB hzetaSrc hzetaCtr htauG hdelta p hp
  have hlog : ∀ᶠ N : Nat in atTop, 4 <= Real.log (d.W N : Real) :=
    (Real.tendsto_log_atTop.comp (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [hcap, hlog, eventually_ge_atTop 1] with N hcapN hlogN hN
  intro k hk hkTop omega homega hwide u hu a1 a2 hnear
  have hcapU := hcapN k hk hkTop omega homega hwide u hu
  have hend : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Set.Icc (s N) (t N) :=
    ⟨hu.1, hu.2.trans hend.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hbase := pointwise_near_source_bound hE hs0 hst ht1
    (by omega : 0 < N) homega uu hlogN a1 a2 hnear
  dsimp only at hbase
  let J := APrimeJG.jG (sample d) E N u omega
    (B.ell N u) (etaT E u) D
  let Jbar := blockCap E s tauG delta N u
  have hJcap : J <= Jbar := by
    simpa only [J, Jbar, blockCap] using hcapU.2
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hells : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) ((s N : Real) : Complex) by linarith)
  have hu0 : 0 <= u := (hs0 N).trans huWindow.1
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hellu : 0 < B.ell N u := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat (B.L N) (u : Complex) by linarith)
  have heta : 0 < etaT E u := etaT_pos hE hu1
  have hcoef : 0 <=
      (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
        (B.ell N u * etaT E u)⁻¹ * (d.L N : Real) := by positivity
  have htail : 0 <= tailT (d.W N : Real) (B.ell N u) (etaT E u) D
      (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)) :=
    tailT_nonneg (by positivity) _
  have hrem :
      (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
          (B.ell N u * etaT E u)⁻¹ * (d.L N : Real) *
            ((etaT E u)⁻¹ * J *
              tailT (d.W N : Real) (B.ell N u) (etaT E u) D
                (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) <=
        (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
          (B.ell N u * etaT E u)⁻¹ * (d.L N : Real) *
            ((etaT E u)⁻¹ * Jbar *
              tailT (d.W N : Real) (B.ell N u) (etaT E u) D
                (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u))) := by
    apply mul_le_mul_of_nonneg_left _ hcoef
    apply mul_le_mul_of_nonneg_right _ htail
    exact mul_le_mul_of_nonneg_left hJcap (inv_nonneg.mpr heta.le)
  refine ⟨?_, hbase.trans ?_⟩
  · exact hJcap
  · exact add_le_add le_rfl hrem

/-- The assumptions of both supported drift branches have a genuine
positive-length same-event realization. -/
theorem positive_length_drift_source_witness :
    ∃ tauPrime : Real, 0 < tauPrime ∧
    ∃ c : Real, 0 < c ∧
    ∃ s t : Nat -> Real,
      (forall N, s N = 0) ∧
      (forall N, 0 <= s N) ∧
      (forall N, s N <= t N) ∧
      (forall N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (sample d) 0 s ∧
      Step1.Hyp (sample d) 0 s t ∧
      forall zetaSrc zetaCtr tauG delta : Real,
        0 < zetaSrc -> 0 < zetaCtr -> 0 < tauG -> 0 < delta ->
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ APrimeGeneralMovingCommonSources.commonEvent
              0 60 s t zetaSrc zetaCtr tauG N ∧
            1 <= cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            ∀ p : Nat,
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh 60)) 1
                (APrimeGeneralMovingDetFields.J 0 60 s) s t
                (APrimeGeneralMovingMesh.targetMesh 60)
                delta p N 1 omega = 1 :=
  APrimeGeneralMovingCommonSources.positive_length_common_support_witness

#print axioms blockCap
#print axioms pointwise_source_package
#print axioms pointwise_far_source_bound
#print axioms eventually_far_on_common_support
#print axioms eventually_near_on_common_support
#print axioms positive_length_drift_source_witness

end
end RBM.APrimeGeneralMovingDriftSource
