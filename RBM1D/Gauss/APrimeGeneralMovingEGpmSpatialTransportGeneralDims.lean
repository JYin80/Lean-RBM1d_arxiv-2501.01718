/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftAtProfileGeneralDims
import RBM1D.Gauss.APrimeQVEndpoint

/-!
# T1476: generic actual linear eGpm spatial transport

This module preserves T1399's actual same-event source, splits its linear
`eGpm` part at `ellStar_u`, and transports that split with the generic two-loop
kernel estimates. It does not transport the quadratic drift row.
-/

namespace RBM.APrimeGeneralMovingEGpmSpatialTransportGeneralDims

open Filter Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private abbrev nearSourceCoeff :=
  APrimeGeneralMovingDriftAtProfileGeneralDims.nearSourceCoeff
private abbrev farSourceCoeff :=
  APrimeGeneralMovingDriftAtProfileGeneralDims.farSourceCoeff

noncomputable def eGpmSource (d : Dims) (E : Real) (N : Nat) (u : Real)
    (omega : Ω d) : LoopArg (d.L N) 2 → Complex :=
  fun b => EGDef.eGpm (d.L N) (d.W N) (mSigma E)
    (Hflow d N u omega) (zt E u) (b 0) (b 1)

noncomputable def eGpmNearPart (d : Dims) (E D : Real) (N : Nat) (u : Real)
    (omega : Ω d) : LoopArg (d.L N) 2 → Complex := fun b =>
  eGpmSource d E N u omega b *
    (if (zdist (d.L N) (b 0 - b 1) : Real) <=
        ellStar (d.W N : Real) ((band d).ell N u) then (1 : Real) else 0 : Complex)

noncomputable def eGpmFarPart (d : Dims) (E D : Real) (N : Nat) (u : Real)
    (omega : Ω d) : LoopArg (d.L N) 2 → Complex := fun b =>
  eGpmSource d E N u omega b - eGpmNearPart d E D N u omega b

private theorem normalized_transport_identity
    {M Xi T etaU etaV : Real}
    (hT : T ≠ 0) (hEtaU : 0 < etaU) (hEtaV : 0 < etaV) :
    (M * (etaU / etaV)^2 * Xi * T) / T =
      M * (etaU / etaV)^2 * Xi := by
  field_simp

/-- The accepted near and far branches give the exact T1474 source
coefficients, with the near branch retained only on its source support. -/
theorem eventually_source_split (d : Dims)
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hreg : Cond272 (band d) E s t)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈ APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
        d E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingLoopModulusGeneralDims.actualJ d E D s)
        s t (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega ->
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      ∀ u ∈ Icc (s N) v,
      ∀ b : LoopArg (d.L N) 2,
      let ellu := (band d).ell N u
        let etau := etaT E u
        let dist := (zdist (d.L N) (b 0 - b 1) : Real)
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
          (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
              tailT (d.W N : Real) ellu etau D dist *
                (if dist <= ellStar (d.W N : Real) ellu then 1 else 0) +
            farSourceCoeff d E D s t zetaCtr tauG delta N u *
              tailT (d.W N : Real) ellu etau D dist ∧
        norm (eGpmNearPart d E D N u omega b) <=
          nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D dist *
              (if dist <= ellStar (d.W N : Real) ellu then 1 else 0) ∧
        norm (eGpmFarPart d E D N u omega b) <=
          farSourceCoeff d E D s t zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D dist := by
  have hnear :=
    APrimeGeneralMovingNearFarSupportGeneralDims.eventually_near_on_common_support d
      hE hD hs0 hst ht1 hreg hzetaSrc hzetaCtr htauG hdelta p hp
  have hfar :=
    APrimeGeneralMovingNearFarSupportGeneralDims.eventually_far_on_common_support d
      hE hD hs0 hst ht1 hreg hzetaSrc hzetaCtr htauG hdelta p hp
  filter_upwards [hnear, hfar, eventually_ge_atTop 1]
    with N hnearN hfarN hN
  intro k hk hkTop omega homega hwide
  dsimp only
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvWindow : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have hv1 : v < 1 := hvWindow.2.trans_lt (ht1 N)
  intro u hu b
  have huWindow : u ∈ Icc (s N) (t N) :=
    ⟨hu.1, hu.2.trans hvWindow.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hu0 : 0 <= u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt hv1
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hW : 1 <= (d.W N : Real) := by exact_mod_cast (band d).one_le_W N
  have hW0 : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
  have hellS : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N)
      (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((s N : Real) : Complex) by linarith)
  have hellU : 0 < (band d).ell N u := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) (u : Complex) by linarith)
  have heta : 0 < etaT E u := etaT_pos hE hu1
  let ellu := (band d).ell N u
  let etau := etaT E u
  let ru := ellu / (band d).ell N (s N)
  let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
  let dist : Real := zdist (d.L N) (b 0 - b 1)
  have hru : 0 < ru := div_pos (by simpa only [ellu] using hellU) hellS
  have hJbar : 0 <= Jbar := by
    unfold Jbar APrimeGeneralMovingDriftSource.blockCap
    positivity
  have htail (x : Real) : 0 < tailT (d.W N : Real) ellu etau D x :=
    tailT_pos hW0 x
  have hCn : 0 <= nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u := by
    unfold nearSourceCoeff APrimeGeneralMovingDriftAtProfileGeneralDims.nearSourceCoeff
    dsimp only
    have hcNear : 0 <= Lemma57.cNear (d.W N : Real) ellu :=
      Lemma57.cNear_nonneg hW (by linarith : 0 < ellu)
    have hTgap : 0 <= tailT (d.W N : Real) ellu etau D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu) :=
      tailT_nonneg hW0.le _
    have hNreal : 1 <= (N : Real) := by exact_mod_cast hN
    have hNnonneg : (0 : Real) <= (N : Real) := by linarith
    positivity
  have hCf : 0 <= farSourceCoeff d E D s t zetaCtr tauG delta N u := by
    unfold farSourceCoeff APrimeGeneralMovingDriftAtProfileGeneralDims.farSourceCoeff
    dsimp only
    have hcFar : 0 <= Lemma57.cFar (d.W N : Real) ellu :=
      Lemma57.cFar_nonneg hW (by linarith : 0 < ellu)
    have hflow : 0 <= flowDelta d E t N := by
      unfold flowDelta
      exact Real.rpow_nonneg (inv_nonneg.mpr
        ((band d).scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _
    have hNnonneg : (0 : Real) <= (N : Real) := Nat.cast_nonneg _
    positivity
  let bdist := (zdist (d.L N) (b 0 - b 1) : Real)
  have hsymm : zdist (d.L N) (b 1 - b 0) = zdist (d.L N) (b 0 - b 1) := by
    rw [<- zdist_neg (d.L N) (b 0 - b 1), neg_sub]
  by_cases hnear : bdist <= ellStar (d.W N : Real) ellu
  · have hn := hnearN k hk hkTop omega homega hwide u hu (b 0) (b 1)
      (by simpa only [bdist, ellu, hsymm] using hnear)
    have hratio := APrimeDriftNearAbsorb.residual_ratio_le
      (W := (d.W N : Real)) (L := (d.L N : Real)) (ℓu := ellu)
      (ηu := etau) (D := D) (J := Jbar) (r := ru) (C := 2)
      (N := (N : Real)) (ζ := zetaCtr) (d := bdist)
      (by exact_mod_cast (band d).one_le_W N)
      (by simpa only [ellu] using hellU) (by simpa only [etau] using heta)
      hru (Nat.cast_nonneg _) hJbar (by norm_num)
      (by
        have hNnat : 0 < N := by omega
        exact_mod_cast hNnat)
      (by simpa only [bdist, ellu] using hnear)
    have hres :
        APrimeDriftNearAbsorb.residual (d.W N : Real) (d.L N : Real)
            ellu etau D Jbar ru 2 (N : Real) zetaCtr <=
          (4 * (N : Real)^zetaCtr *
              ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
              (((d.W N : Real) * ellu * etau)^2 *
                Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
              tailT (d.W N : Real) ellu etau D
                (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
            (etau⁻¹ * ru^3 * tailT (d.W N : Real) ellu etau D bdist) := by
      have hRate : 0 < APrimeDriftNearAbsorb.nearRate
          (d.W N : Real) ellu etau D ru bdist := by
        unfold APrimeDriftNearAbsorb.nearRate
        exact mul_pos (mul_pos (inv_pos.mpr heta) (pow_pos hru _))
          (htail bdist)
      have hres0 := (div_le_iff₀ hRate).mp hratio
      convert hres0 using 1
      all_goals simp only [APrimeDriftNearAbsorb.nearRate]
      all_goals ring
    have hnbase := hn.2
    rw [hsymm] at hnbase
    have hn' :
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
            (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          (4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
              Lemma57.cNear (d.W N : Real) ellu +
            (4 * (N : Real)^zetaCtr *
              ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
              (((d.W N : Real) * ellu * etau)^2 *
                Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
              tailT (d.W N : Real) ellu etau D
                (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
            (etau⁻¹ * ru^3)) * tailT (d.W N : Real) ellu etau D bdist := by
      have hbase :
          norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
              (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
            4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
                Lemma57.cNear (d.W N : Real) ellu *
                tailT (d.W N : Real) ellu etau D bdist +
              APrimeDriftNearAbsorb.residual (d.W N : Real) (d.L N : Real)
                ellu etau D Jbar ru 2 (N : Real) zetaCtr := by
        change _ <= _ at hnbase
        convert hnbase using 1
        all_goals simp only [APrimeGeneralMovingDriftAtProfileGeneralDims.nearSourceCoeff,
          ellu, etau, ru, Jbar, dist, bdist, APrimeDriftNearAbsorb.residual]
        all_goals ring
      calc
        _ <= 4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
              Lemma57.cNear (d.W N : Real) ellu *
              tailT (d.W N : Real) ellu etau D bdist +
            APrimeDriftNearAbsorb.residual (d.W N : Real) (d.L N : Real)
              ellu etau D Jbar ru 2 (N : Real) zetaCtr := hbase
        _ <= 4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
              Lemma57.cNear (d.W N : Real) ellu *
              tailT (d.W N : Real) ellu etau D bdist +
            (4 * (N : Real)^zetaCtr *
              ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
              (((d.W N : Real) * ellu * etau)^2 *
                Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
              tailT (d.W N : Real) ellu etau D
                (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
            (etau⁻¹ * ru^3 * tailT (d.W N : Real) ellu etau D bdist) :=
          add_le_add le_rfl hres
        _ = _ := by ring
    have hnCoeff :
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
            (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D bdist := by
      simpa only [nearSourceCoeff,
        APrimeGeneralMovingDriftAtProfileGeneralDims.nearSourceCoeff,
        ellu, etau, ru, Jbar] using hn'
    have htailNonneg : 0 <= tailT (d.W N : Real) ellu etau D bdist :=
      (htail bdist).le
    have hsplit := add_le_add_right hnCoeff (farSourceCoeff d E D s t zetaCtr tauG delta N u *
      tailT (d.W N : Real) ellu etau D bdist)
    have hgoal :
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
            (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
              tailT (d.W N : Real) ellu etau D bdist * 1 +
            farSourceCoeff d E D s t zetaCtr tauG delta N u *
              tailT (d.W N : Real) ellu etau D bdist := by
      nlinarith [mul_nonneg hCf htailNonneg]
    have hnearPart :
        norm (eGpmNearPart d E D N u omega b) <=
          nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D bdist := by
      simpa [eGpmNearPart, eGpmSource, bdist, ellu, etau, hnear] using hnCoeff
    have hfarPart :
        norm (eGpmFarPart d E D N u omega b) <=
          farSourceCoeff d E D s t zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D bdist := by
      simp [eGpmFarPart, eGpmNearPart, eGpmSource, bdist, ellu, etau, hnear]
      exact mul_nonneg hCf htailNonneg
    refine ⟨?_, ?_, hfarPart⟩
    · simpa [bdist, ellu, etau, hnear] using hgoal
    · simpa [bdist, ellu, etau, hnear] using hnearPart
  · have hfar : ellStar (d.W N : Real) ellu <= bdist :=
      le_of_not_ge hnear
    have hf := hfarN k hk hkTop omega homega hwide u hu (b 0) (b 1)
      (by simpa only [bdist, ellu, hsymm] using hfar)
    have hf' :
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
            (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          farSourceCoeff d E D s t zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D bdist := by
      simpa only [farSourceCoeff,
        APrimeGeneralMovingDriftAtProfileGeneralDims.farSourceCoeff,
        ellu, etau, ru, Jbar, bdist, hsymm] using hf.2
    have hzero : (if bdist <= ellStar (d.W N : Real) ellu then (1 : Real) else 0) = 0 := by
      simp [hnear]
    have hnearPart :
        norm (eGpmNearPart d E D N u omega b) <=
          nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D bdist * 0 := by
      simp [eGpmNearPart, eGpmSource, bdist, ellu, etau, hnear]
    have hfarPart :
        norm (eGpmFarPart d E D N u omega b) <=
          farSourceCoeff d E D s t zetaCtr tauG delta N u *
            tailT (d.W N : Real) ellu etau D bdist := by
      simpa [eGpmFarPart, eGpmNearPart, eGpmSource, bdist, ellu, etau, hnear] using hf'
    refine ⟨?_, ?_, hfarPart⟩
    · simpa [bdist, ellu, etau, hnear] using hf'
    · simpa [bdist, ellu, etau, hnear] using hnearPart

/-- The actual `eGpm` source obeys the exact pointwise near-indicator/far-tail
split on T1399's common event and positive widened prefix. -/
abbrev eventually_eGpm_source_split := eventually_source_split

/-- The positive-prefix spatial transport of the actual linear Gaussian
source. The output near radius is `3 * ellStar_v`; the cubic near loss and
the explicit `256 * exp 3` leakage are retained literally. -/
theorem eventually_linear_spatial_transport (d : Dims)
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hreg : Cond272 (band d) E s t)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈ APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
        d E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingLoopModulusGeneralDims.actualJ d E D s)
        s t (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega ->
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      ∀ u ∈ Icc (s N) v,
      ∀ a : LoopArg (d.L N) 2,
        let W := (d.W N : Real)
        let ellu := (band d).ell N u
        let ellv := (band d).ell N v
        let etau := etaT E u
        let etav := etaT E v
        let dist := (zdist (d.L N) (a 0 - a 1) : Real)
        let Tu := tailT W ellu etau D 0
        let Tv := tailT W ellv etav D dist
        let R := (1 - u) / (1 - v)
        norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex)
          (eGpmSource d E N u omega) a) / Tv <=
          R^2 *
            (Step2.xiK (d.L N) W (mE E).im *
                nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
                (if dist <= 3 * ellStar W ellv then 1 else 0) +
              Step2.xiK (d.L N) W (mE E).im *
                farSourceCoeff d E D s t zetaCtr tauG delta N u +
              256 * Real.exp 3 *
                nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u * W^(-D)) := by
  have hsrc := eventually_source_split d hE hD hs0 hst ht1 hreg
    hzetaSrc hzetaCtr htauG hdelta p hp
  have hWbig := (Step2.tendsto_W (band d)).eventually_ge_atTop
    (Real.exp ((4 * D)^2))
  filter_upwards [hsrc, hreg, hWbig, eventually_ge_atTop 1]
    with N hsrcN hcondN hWbigN hN
  intro k hk hkTop omega homega hwide
  dsimp only
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvWindow : v ∈ Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have hv0 : 0 <= v := (hs0 N).trans hvWindow.1
  have hv1 : v < 1 := hvWindow.2.trans_lt (ht1 N)
  have hNposNat : 0 < N := by omega
  have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast hNposNat
  have hWe : Real.exp 1 <= (d.W N : Real) := by
    calc
      Real.exp 1 <= Real.exp ((4 * D)^2) :=
        Real.exp_le_exp.mpr (by nlinarith [hD])
      _ <= (d.W N : Real) := by simpa only [Gauss.band_W] using hWbigN
  have hW0 : 0 < (d.W N : Real) := (Real.exp_pos 1).trans_le hWe
  have hW1 : 1 <= (d.W N : Real) := (Real.one_le_exp (by norm_num)).trans hWe
  have hlog : (4 * D)^2 <= Real.log (d.W N : Real) := by
    have hWbigD : Real.exp ((4 * D)^2) <= (d.W N : Real) := by
      simpa only [Gauss.band_W] using hWbigN
    have h := Real.log_le_log (Real.exp_pos ((4 * D)^2)) hWbigD
    simpa only [Real.log_exp] using h
  have hD0 : 0 <= D := by linarith
  have hNreal : 1 <= (N : Real) := by exact_mod_cast hN
  intro u hu a
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hvWindow.2⟩
  have hu0 : 0 <= u := (hs0 N).trans hu.1
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  let W : Real := (d.W N : Real)
  let ellu : Real := (band d).ell N u
  let ellv : Real := (band d).ell N v
  let etau : Real := etaT E u
  let etav : Real := etaT E v
  let dist : Real := zdist (d.L N) (a 0 - a 1)
  let Tu : Real := tailT W ellu etau D 0
  let Tv : Real := tailT W ellv etav D dist
  let R : Real := (1 - u) / (1 - v)
  let Cn : Real := nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u
  let Cf : Real := farSourceCoeff d E D s t zetaCtr tauG delta N u
  let Fn := eGpmNearPart d E D N u omega
  let Ff := eGpmFarPart d E D N u omega
  have hsource := hsrcN k hk hkTop omega homega hwide u hu
  rcases hsource a with ⟨_hsplit, hnearSource, hfarSource⟩
  have htailU0 : 0 <= Tu := tailT_nonneg hW0.le _
  have htailU (r : Real) : 0 < tailT W ellu etau D r := tailT_pos hW0 r
  have htailV : 0 < Tv := tailT_pos hW0 _
  have hetaU : 0 < etau := etaT_pos hE hu1
  have hetaV : 0 < etav := etaT_pos hE hv1
  have hellS : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N)
      (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((s N : Real) : Complex) by linarith)
  have hellU : 0 < ellu := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
    simpa only [ellu, Band.ell] using
      (show 0 < ellHat ((band d).L N) (u : Complex) by linarith)
  have hJbar : 0 <=
      APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u := by
    unfold APrimeGeneralMovingDriftSource.blockCap
    positivity
  have hCn : 0 <= Cn := by
    unfold Cn nearSourceCoeff APrimeGeneralMovingDriftAtProfileGeneralDims.nearSourceCoeff
    dsimp only
    have hcNear : 0 <= Lemma57.cNear W ellu := Lemma57.cNear_nonneg hW1 hellU
    have hTgap : 0 <= tailT W ellu etau D
        (APrimeDriftNearAbsorb.gap W ellu) := tailT_nonneg hW0.le _
    positivity
  have hCf : 0 <= Cf := by
    unfold Cf farSourceCoeff APrimeGeneralMovingDriftAtProfileGeneralDims.farSourceCoeff
    dsimp only
    have hcFar : 0 <= Lemma57.cFar W ellu := Lemma57.cFar_nonneg hW1 hellU
    have hflow : 0 <= flowDelta d E t N := by
      unfold flowDelta
      exact Real.rpow_nonneg (inv_nonneg.mpr
        ((band d).scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _
    positivity
  have hScaleTpos : 0 < (band d).scale E N (t N) :=
    (band d).scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have h1s : 0 < 1 - s N := by linarith [hst N, ht1 N]
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have hratio0 : 0 <= (1 - t N) / (1 - s N) :=
    div_nonneg h1t.le h1s.le
  have hratio1 : (1 - t N) / (1 - s N) <= 1 := by
    rw [div_le_iff₀ h1s]
    linarith [hst N]
  have hratioPow : ((1 - t N) / (1 - s N))^30 <= 1 :=
    pow_le_one₀ hratio0 hratio1
  have hScaleTinv : ((band d).scale E N (t N))⁻¹ <= 1 :=
    (hcondN.trans hratioPow)
  have hScaleT : 1 <= (band d).scale E N (t N) :=
    (inv_le_one₀ hScaleTpos).1 hScaleTinv
  have hScaleMono := flowScale_antitoneOn hW0.le (d.L N) E
    (Set.mem_Iic.2 (huWindow.2.trans_lt (ht1 N)).le)
    (Set.mem_Iic.2 (ht1 N).le) huWindow.2
  have hScaleU : 1 <= (band d).scale E N u := hScaleT.trans hScaleMono
  have hAu : 1 <= W * ellu * etau := by
    simpa only [Band.scale, Gauss.band_W, W, ellu, etau, etaT] using hScaleU
  have hru : 0 < ellu / (band d).ell N (s N) := div_pos hellU hellS
  have hWcast : Real.exp 1 <= W := by simpa only [W] using hWe
  have hL : 3 <= d.L N := d.three_le_L N
  have hDelta : 0 < ellStar W ellv := by
    have hlog1 : 1 <= Real.log W := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hWcast
    have hellV : 0 < ellv := by
      have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hv0 hv1
      simpa only [ellv, Band.ell] using (show 0 < ellHat ((band d).L N) (v : Complex) by linarith)
    unfold ellStar
    positivity
  have hstarMono : ellStar W ellu <= ellStar W ellv :=
    Step2FarMart.ellStar_mono_time (B := band d) hW1 hu.2 hv1
  have hRpos : 0 < R := by
    unfold R
    exact div_pos (by linarith [huWindow.2]) (by linarith [hv1])
  have hnearSourceProfile : ∀ b : LoopArg (d.L N) 2,
      norm (Fn b) <= Cn * Step2.tT (band d) E N D u
        (zdist (d.L N) (b 0 - b 1)) := by
    intro b
    have hb := (hsource b).2.1
    have hbCondition : norm (Fn b) <= Cn *
        tailT W ellu etau D (zdist (d.L N) (b 0 - b 1)) *
          (if (zdist (d.L N) (b 0 - b 1) : Real) <= ellStar W ellu then 1 else 0) := by
      simpa [Fn, Cn, W, ellu, etau] using hb
    have hTpos : 0 <= tailT W ellu etau D
        (zdist (d.L N) (b 0 - b 1)) := tailT_nonneg hW0.le _
    have hIndicator : (if (zdist (d.L N) (b 0 - b 1) : Real) <=
        ellStar W ellu then (1 : Real) else 0) <= 1 := by
      split_ifs <;> norm_num
    have hb' : norm (Fn b) <= Cn *
        tailT W ellu etau D (zdist (d.L N) (b 0 - b 1)) := by
      calc
        _ <= Cn * tailT W ellu etau D (zdist (d.L N) (b 0 - b 1)) *
            (if (zdist (d.L N) (b 0 - b 1) : Real) <= ellStar W ellu then 1 else 0) := hbCondition
        _ <= Cn * tailT W ellu etau D (zdist (d.L N) (b 0 - b 1)) * 1 :=
          mul_le_mul_of_nonneg_left hIndicator (mul_nonneg hCn hTpos)
        _ = _ := by ring
    simpa [Step2.tT, W, ellu, etau] using hb'
  have hfarSourceProfile : ∀ b : LoopArg (d.L N) 2,
      norm (Ff b) <= Cf * Step2.tT (band d) E N D u
        (zdist (d.L N) (b 0 - b 1)) := by
    intro b
    simpa [Ff, Cf, W, ellu, etau, Step2.tT] using (hsource b).2.2
  have hUnear := Step2.norm_Uker_flow (B := band d)
    (E := E) (N := N) (u := u) (v := v) (D := D) (M := Cn) (A := Fn)
    hE hu0 hu.2 hv0 hv1 hWcast hCn hnearSourceProfile a
  have hUnear : norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
      (u : Complex) (v : Complex) Fn a) <= Cn * R^2 *
        Step2.xiK (d.L N) W (mE E).im * Tv := by
    rw [Step2.etaT_ratio hE] at hUnear
    exact hUnear
  have hUfar := Step2.norm_Uker_flow (B := band d)
    (E := E) (N := N) (u := u) (v := v) (D := D) (M := Cf) (A := Ff)
    hE hu0 hu.2 hv0 hv1 hWcast hCf hfarSourceProfile a
  have hUfar : norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
      (u : Complex) (v : Complex) Ff a) <= Cf * R^2 *
        Step2.xiK (d.L N) W (mE E).im * Tv := by
    rw [Step2.etaT_ratio hE] at hUfar
    exact hUfar
  let Mnear : Real := Cn * Tu
  have hMnear : 0 <= Mnear := mul_nonneg hCn htailU0
  have hnearSupport : ∀ b : LoopArg (d.L N) 2,
      norm (Fn b) <= Mnear * (if (zdist (d.L N) (b 0 - b 1) : Real) <=
        ellStar W ellu then 1 else 0) := by
    intro b
    have hb := (hsource b).2.1
    have hbCondition : norm (Fn b) <= Cn *
        tailT W ellu etau D (zdist (d.L N) (b 0 - b 1)) *
          (if (zdist (d.L N) (b 0 - b 1) : Real) <= ellStar W ellu then 1 else 0) := by
      simpa [Fn, Cn, W, ellu, etau] using hb
    by_cases hnb : (zdist (d.L N) (b 0 - b 1) : Real) <= ellStar W ellu
    · have hTailMono : tailT W ellu etau D
          (zdist (d.L N) (b 0 - b 1)) <= Tu := by
        exact tailT_antitone hellU (Nat.cast_nonneg _)
      have hb' : norm (Fn b) <= Cn *
          tailT W ellu etau D (zdist (d.L N) (b 0 - b 1)) := by
        simpa [hnb] using hbCondition
      have hb'' : norm (Fn b) <= Cn * Tu :=
        hb'.trans (mul_le_mul_of_nonneg_left hTailMono hCn)
      simpa [Mnear, hnb, Tu, W, ellu, etau] using hb''
    · have hzero : norm (Fn b) <= 0 := by simpa [hnb] using hbCondition
      have hzero' : norm (Fn b) = 0 := le_antisymm hzero (norm_nonneg _)
      simp [Mnear, hnb, hzero']
  have hdecomp : eGpmSource d E N u omega = Fn + Ff := by
    funext b
    simp [Fn, Ff, eGpmFarPart]
  have hUsplit : Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
      (u : Complex) (v : Complex) (eGpmSource d E N u omega) =
        Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex) Fn +
        Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex) Ff := by
    rw [hdecomp, Uker_add]
  have hxi0 : 0 <= Step2.xiK (d.L N) W (mE E).im := Step2.xiK_nonneg _ _ _
  have hR2 : 0 <= R^2 := sq_nonneg _
  by_cases houtput : dist <= 3 * ellStar W ellv
  · have hnearIndicator :
        (if dist <= 3 * ellStar W ellv then (1 : Real) else 0) = 1 := if_pos houtput
    have htotal :
        norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex)
          (eGpmSource d E N u omega) a) <=
          Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 1 +
            Step2.xiK (d.L N) W (mE E).im * Cf +
            256 * Real.exp 3 * Cn * W^(-D))) := by
      rw [hUsplit]
      calc
        _ <= norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex) Fn a) +
              norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex) Ff a) :=
          norm_add_le _ _
        _ <= Cn * R^2 * Step2.xiK (d.L N) W (mE E).im * Tv +
              Cf * R^2 * Step2.xiK (d.L N) W (mE E).im * Tv := add_le_add hUnear hUfar
        _ = Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 1 +
              Step2.xiK (d.L N) W (mE E).im * Cf)) := by ring
        _ <= Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 1 +
              Step2.xiK (d.L N) W (mE E).im * Cf +
              256 * Real.exp 3 * Cn * W^(-D))) := by
          apply mul_le_mul_of_nonneg_left _ htailV.le
          apply mul_le_mul_of_nonneg_left _ hR2
          exact le_add_of_nonneg_right (by positivity :
            0 <= 256 * Real.exp 3 * Cn * W^(-D))
    have htotal' : norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
        (u : Complex) (v : Complex) (eGpmSource d E N u omega) a) <=
        (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 1 +
          Step2.xiK (d.L N) W (mE E).im * Cf +
          256 * Real.exp 3 * Cn * W^(-D))) * Tv := by
      calc
        _ <= Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 1 +
              Step2.xiK (d.L N) W (mE E).im * Cf +
              256 * Real.exp 3 * Cn * W^(-D))) := htotal
        _ = _ := by ring
    have hquot := (div_le_iff₀ htailV).2 htotal'
    rw [hnearIndicator]
    exact hquot
  · have hfarOutput : 3 * ellStar W ellv <= dist := le_of_not_ge houtput
    have hsep : ellStar W ellu + 2 * ellStar W ellv <= dist := by
      calc
        ellStar W ellu + 2 * ellStar W ellv <=
            ellStar W ellv + 2 * ellStar W ellv := add_le_add hstarMono le_rfl
        _ = 3 * ellStar W ellv := by ring
        _ <= dist := hfarOutput
    have hUnearFarRaw := Step2MomentStep.norm_Uker_supp_far_le
      (d.L N) hL hu0 hu.2 hv1 hMnear hDelta
      (A := Fn) hnearSupport a hsep
    have hUnearFar := hUnearFarRaw
    rw [← Step2.sigPM_xi hE.le] at hUnearFar
    have hellV : 0 < ellv := by
      have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hv0 hv1
      have hEllHat : 0 < ellHat ((band d).L N) (v : Complex) := by linarith
      simpa only [ellv, Band.ell] using hEllHat
    have hEllHatVPos : 0 < ellHat (d.L N) (v : Complex) := by
      simpa only [ellv, Band.ell, band_L] using hellV
    have hleak := APrimeQVEndpoint.nearLeak_le_farTail (d.L N)
      (m := (mE E).im) (u := u) (v := v) (W := W) (D := D)
      hWcast hD0 hAu hEllHatVPos hlog a
    have hUnearLeak : norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
        (u : Complex) (v : Complex) Fn a) <=
        Cn * (256 * Real.exp 3 * R^2 * W^(-D) * Tv) := by
      calc
        _ <= 128 * Real.exp 3 * Mnear * R^2 *
              Real.exp (-(ellStar W ellv / ellv / 2)) := hUnearFar
        _ = Cn * (Tu * (128 * Real.exp 3 * R^2 *
              Real.exp (-(ellStar W ellv / ellv / 2)))) := by
          simp only [Mnear, Tu]
          ring
        _ <= Cn * (256 * Real.exp 3 * R^2 * W^(-D) * Tv) := by
          apply mul_le_mul_of_nonneg_left _ hCn
          simpa only [Tu, Tv, R, W, ellu, ellv, etau, etav, dist,
            Band.ell, band_L, Step2.etaT_eq] using hleak
    have hzero : (if dist <= 3 * ellStar W ellv then (1 : Real) else 0) = 0 := by
      simp [houtput]
    have htotal :
        norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex)
          (eGpmSource d E N u omega) a) <=
          Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 0 +
            Step2.xiK (d.L N) W (mE E).im * Cf +
            256 * Real.exp 3 * Cn * W^(-D))) := by
      rw [hUsplit]
      calc
        _ <= norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex) Fn a) +
              norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM) (u : Complex) (v : Complex) Ff a) :=
          norm_add_le _ _
        _ <= Cn * (256 * Real.exp 3 * R^2 * W^(-D) * Tv) +
              Cf * R^2 * Step2.xiK (d.L N) W (mE E).im * Tv :=
          add_le_add hUnearLeak hUfar
        _ = Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 0 +
              Step2.xiK (d.L N) W (mE E).im * Cf +
              256 * Real.exp 3 * Cn * W^(-D))) := by ring
    have htotal' : norm (Uker (d.L N) (xiOf (mSigma E) Step2.sigPM)
        (u : Complex) (v : Complex) (eGpmSource d E N u omega) a) <=
        (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 0 +
          Step2.xiK (d.L N) W (mE E).im * Cf +
          256 * Real.exp 3 * Cn * W^(-D))) * Tv := by
      calc
        _ <= Tv * (R^2 * (Step2.xiK (d.L N) W (mE E).im * Cn * 0 +
              Step2.xiK (d.L N) W (mE E).im * Cf +
              256 * Real.exp 3 * Cn * W^(-D))) := htotal
        _ = _ := by ring
    have hquot := (div_le_iff₀ htailV).2 htotal'
    rw [hzero]
    exact hquot

/-- Reuse the accepted T1399 simultaneous actual-model witness: the first cell
has positive length, and one resident of its common event has widened weight
one at the same active index. The upper-bound argument needs no nonzero
integrand witness. -/
theorem positive_length_exampleGrow_same_event_witness :
    ∃ tauPrime : ℝ, 0 < tauPrime ∧
    ∃ c : ℝ, 0 < c ∧
    ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧
      (∀ N, 0 ≤ s N) ∧
      (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧
      Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
      BoundsCore (sample Dims.exampleGrow) 0 s ∧
      ∀ zetaSrc zetaCtr tauG delta : ℝ,
        0 < zetaSrc → 0 < zetaCtr → 0 < tauG → 0 < delta →
        ∀ᶠ N : ℕ in atTop,
          s N < t N ∧
          1 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N ∧
          ∃ omega : Ω Dims.exampleGrow,
            omega ∈ APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
              Dims.exampleGrow 0 60 s t zetaSrc zetaCtr tauG N ∧
            APrimeWeight.widenedW
              (APrimeWeight.canonicalR s t
                (APrimeGeneralMovingMesh.targetMesh 60)) 1
              (APrimeGeneralMovingLoopModulusGeneralDims.actualJ
                Dims.exampleGrow 0 60 s)
              s t (APrimeGeneralMovingMesh.targetMesh 60)
              delta 1 N 1 omega = 1 :=
  APrimeGeneralMovingNearFarSupportGeneralDims.positive_length_exampleGrow_same_event_witness

#print axioms eventually_source_split
#print axioms eventually_linear_spatial_transport
#print axioms positive_length_exampleGrow_same_event_witness

end
end RBM.APrimeGeneralMovingEGpmSpatialTransportGeneralDims
