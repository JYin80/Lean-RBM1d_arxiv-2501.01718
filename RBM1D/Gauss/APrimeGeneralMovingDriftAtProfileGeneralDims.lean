/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftSourceGeneralDims
import RBM1D.Gauss.APrimeGeneralMovingNearFarSupportGeneralDims
import RBM1D.Gauss.APrimeDriftTimeFamily

/-!
# T1474: arbitrary-Dims actual transported two-loop drift profile

This file combines T586's two branches of the linear source (5.35) with
the literal quadratic gluing row (5.34), transports their sum by (5.41),
and divides by the actual `driftScale`. The coefficients and theorem are
parameterized by the actual dimension.
The pointwise source and positive running-prefix support come from accepted
T1389/T1399 sources on one common-event sample.

The linear coefficient below is the sum of the near and far coefficients.
This is a deliberate weakening of `max (near) (far)`: the sum dominates
whichever geometric branch applies, while retaining every `N`, `W`, time,
and spatial-leakage factor literally.  In particular `Step2.jS` in (5.34)
is not replaced by T586's unrelated block cap `Jbar`.
-/

namespace RBM.APrimeGeneralMovingDriftAtProfileGeneralDims

open Filter Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

/-- T586's near coefficient after converting its explicit residual to a
multiple of the output tail with `residual_ratio_le`. -/
noncomputable def nearSourceCoeff (d : Dims) (E D : Real) (s : Nat -> Real)
    (zetaSrc zetaCtr tauG delta : Real) (N : Nat) (u : Real) : Real :=
  let ellu := (band d).ell N u
  let etau := etaT E u
  let ru := ellu / (band d).ell N (s N)
  let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
  4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
      Lemma57.cNear (d.W N : Real) ellu +
    (4 * (N : Real)^zetaCtr *
        ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
        (((d.W N : Real) * ellu * etau)^2 *
          Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
        tailT (d.W N : Real) ellu etau D
          (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
      (etau⁻¹ * ru^3)

/-- T586's far coefficient, retaining the literal block cap, the
`flowDelta + W⁻¹` row, and both spatial leakage terms. -/
noncomputable def farSourceCoeff (d : Dims) (E D : Real) (s t : Nat -> Real)
    (zetaCtr tauG delta : Real) (N : Nat) (u : Real) : Real :=
  let ellu := (band d).ell N u
  let etau := etaT E u
  let ru := ellu / (band d).ell N (s N)
  let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
  etau⁻¹ * (4 * (N : Real)^zetaCtr * ru) *
    (Lemma57.cFar (d.W N : Real) ellu * Jbar *
        (flowDelta d E t N + (d.W N : Real)⁻¹) +
      Jbar * Real.sqrt Jbar *
        (168 * ((d.W N : Real) * ellu * etau)⁻¹ +
          (d.L N : Real) * Real.sqrt ((d.W N : Real)^(-D)) / ellu))

/-- The exact (5.34) quadratic coefficient, with the actual `Step2.jS`.
There is intentionally no comparison with T586's `Jbar`. -/
noncomputable def quadCoeff (d : Dims) (E D : Real) (N : Nat) (u : Real)
    (omega : Ω d) : Real :=
  Real.exp 1 * (Step2.jS (sample d) E D N u omega)^2 *
    (36 * ((etaT E u)⁻¹ *
      (((d.W N : Real) * (band d).ell N u * etaT E u)⁻¹)) +
      (d.W N : Real) * (d.L N : Real) * (d.W N : Real)^(-D))

private theorem normalized_transport_identity
    {M Xi T etaS etaU etaV : Real}
    (hT : T ≠ 0) (hEtaS : 0 < etaS)
    (hEtaU : 0 < etaU) (hEtaV : 0 < etaV) :
    (M * (etaU / etaV)^2 * Xi * T) /
        (T * (etaS / etaV)^4) =
      Xi * (etaS / etaU)^(-2 : Real) *
        (etaS / etaV)^(-2 : Real) * M := by
  have hSU : 0 <= etaS / etaU := by positivity
  have hSV : 0 <= etaS / etaV := by positivity
  rw [Real.rpow_neg hSU, Real.rpow_two,
    Real.rpow_neg hSV, Real.rpow_two]
  field_simp

/-- On one accepted generic common-event resident and its positive T1399
running support, the full
`(+,-)` drift at every point of the closed prefix has the exact endpoint
factor `xiK * ratR_u⁻² * ratR_v⁻²`.  The source coefficient is the explicit
sum of the near and far branches; the last summand is literally (5.34). -/
theorem eventually_driftAt_le_profile (d : Dims)
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, forall k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈
        APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
          d E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingLoopModulusGeneralDims.actualJ d E D s) s t
        (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega ->
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      ∀ u ∈ Set.Icc (s N) v,
      ∀ a : LoopArg (d.L N) 2,
        APrimeDriftTimeFamily.driftAt
            d E D N Step2.sigPM a (s N) v u omega <=
          Step2.xiK (d.L N) (d.W N) (mE E).im *
            (Step2Moment.ratR E s N u)^(-2 : Real) *
            (Step2Moment.ratR E s N v)^(-2 : Real) *
            (nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u +
              farSourceCoeff d E D s t zetaCtr tauG delta N u +
              quadCoeff d E D N u omega) := by
  let B : Band (Ω d) := band d
  have hfar :=
    APrimeGeneralMovingNearFarSupportGeneralDims.eventually_far_on_common_support d
      hE hD hs0 hst ht1 hreg.1 hzetaSrc hzetaCtr htauG hdelta p hp
  have hnear :=
    APrimeGeneralMovingNearFarSupportGeneralDims.eventually_near_on_common_support d
      hE hD hs0 hst ht1 hreg.1 hzetaSrc hzetaCtr htauG hdelta p hp
  filter_upwards [hfar, hnear, B.eventually_le_W (Real.exp 1),
      eventually_ge_atTop 1] with N hfarN hnearN hW hN
  intro k hk hkTop omega homega hwide
  dsimp only
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hvWindow : v ∈ Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have hv0 : 0 <= v := (hs0 N).trans hvWindow.1
  have hv1 : v < 1 := hvWindow.2.trans_lt (ht1 N)
  intro u hu a
  have hu0 : 0 <= u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt hv1
  have hetaS : 0 < etaT E (s N) :=
    Step2.etaT_pos' hE ((hst N).trans_lt (ht1 N))
  have hetaU : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hetaV : 0 < etaT E v := Step2.etaT_pos' hE hv1
  have hellS : 0 < B.ell N (s N) := by
    exact lt_of_lt_of_le zero_lt_one
      (one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N)
        ((hst N).trans_lt (ht1 N)))
  have hellU : 1 <= B.ell N u :=
    one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hellU0 : 0 < B.ell N u := zero_lt_one.trans_le hellU
  have hW0 : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
  have hW1 : 1 <= (d.W N : Real) := by exact_mod_cast B.one_le_W N
  have hJbar : 0 <=
      APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u := by
    unfold APrimeGeneralMovingDriftSource.blockCap
    positivity
  have hJ : 0 <= Step2.jS (sample d) E D N u omega :=
    (Step2.one_le_jStar hW0 (fun b => norm_nonneg _)).trans' (by norm_num)
  have hNearCoeff : 0 <=
      nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u := by
    unfold nearSourceCoeff
    dsimp only
    have hcNear : 0 <= Lemma57.cNear (d.W N : Real) (B.ell N u) :=
      Lemma57.cNear_nonneg hW1 hellU0
    have hTail : 0 <= tailT (d.W N : Real) (B.ell N u) (etaT E u) D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) (B.ell N u)) :=
      tailT_nonneg hW0.le _
    positivity
  have hFarCoeff : 0 <=
      farSourceCoeff d E D s t zetaCtr tauG delta N u := by
    unfold farSourceCoeff
    dsimp only
    have hcFar : 0 <= Lemma57.cFar (d.W N : Real) (B.ell N u) :=
      Lemma57.cFar_nonneg hW1 hellU0
    have hFlow : 0 <= flowDelta d E t N := by
      unfold flowDelta
      exact Real.rpow_nonneg
        (inv_nonneg.mpr
          (B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _
    positivity
  have hQuadCoeff : 0 <= quadCoeff d E D N u omega := by
    unfold quadCoeff
    positivity
  have hFullCoeff : 0 <=
      nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u +
        farSourceCoeff d E D s t zetaCtr tauG delta N u +
        quadCoeff d E D N u omega := by positivity
  have hSource : forall b : LoopArg (d.L N) 2,
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
        (nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u +
          farSourceCoeff d E D s t zetaCtr tauG delta N u) *
          Step2.tT B E N D u (zdist (d.L N) (b 0 - b 1)) := by
    intro b
    let ellu := (band d).ell N u
    let etau := etaT E u
    let ru := ellu / (band d).ell N (s N)
    let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
    let dist : Real := zdist (d.L N) (b 0 - b 1)
    have hru : 0 < ru := div_pos (by simpa only [ellu] using hellU0) hellS
    have hTail : 0 < tailT (d.W N : Real) ellu etau D dist := tailT_pos hW0 _
    have hdist : zdist (d.L N) (b 1 - b 0) = zdist (d.L N) (b 0 - b 1) := by
      rw [<- zdist_neg (d.L N) (b 0 - b 1), neg_sub]
    rcases le_total dist (ellStar (d.W N : Real) ellu) with hgeom | hgeom
    · have hn := hnearN k hk hkTop omega homega hwide u hu (b 0) (b 1)
          (by simpa only [dist, ellu, hdist] using hgeom)
      change _ /\
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
          (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          4 * (N : Real)^(zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
              (B.ell N u / B.ell N (s N))^3 *
              Lemma57.cNear (d.W N : Real) (B.ell N u) *
                tailT (d.W N : Real) (B.ell N u) (etaT E u) D
                  (zdist (d.L N) (b 1 - b 0)) +
            (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
              (B.ell N u * etaT E u)⁻¹ * (d.L N : Real) *
                ((etaT E u)⁻¹ *
                  APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u *
                  tailT (d.W N : Real) (B.ell N u) (etaT E u) D
                    (APrimeDriftNearAbsorb.gap
                      (d.W N : Real) (B.ell N u))) at hn
      have hratio := APrimeDriftNearAbsorb.residual_ratio_le
        (W := (d.W N : Real)) (L := (d.L N : Real))
        (ℓu := ellu) (ηu := etau) (D := D) (J := Jbar)
        (r := ru) (C := 2) (N := (N : Real)) (ζ := zetaCtr)
        (d := dist) (by exact_mod_cast B.one_le_W N)
        (by simpa only [ellu] using hellU0)
        (by simpa only [etau] using hetaU) hru (Nat.cast_nonneg _) hJbar
        (by norm_num) (by exact_mod_cast hN) (by simpa only [dist, ellu] using hgeom)
      have hres :
          APrimeDriftNearAbsorb.residual (d.W N : Real) (d.L N : Real)
              ellu etau D Jbar ru 2 (N : Real) zetaCtr <=
            (4 * (N : Real)^zetaCtr *
                ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
                (((d.W N : Real) * ellu * etau)^2 *
                  Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
                tailT (d.W N : Real) ellu etau D
                  (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
              (etau⁻¹ * ru^3 * tailT (d.W N : Real) ellu etau D dist) := by
        have hRate : 0 < APrimeDriftNearAbsorb.nearRate
            (d.W N : Real) ellu etau D ru dist := by
          unfold APrimeDriftNearAbsorb.nearRate
          have htail : 0 < tailT (d.W N : Real) ellu etau D dist :=
            tailT_pos hW0 _
          positivity
        have hres0 := (div_le_iff₀ hRate).mp hratio
        convert hres0 using 1
        all_goals simp only [APrimeDriftNearAbsorb.nearRate]
        all_goals ring
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
                (etau⁻¹ * ru^3)) *
              tailT (d.W N : Real) ellu etau D dist := by
        calc
          _ <= 4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
                Lemma57.cNear (d.W N : Real) ellu *
                tailT (d.W N : Real) ellu etau D dist +
              APrimeDriftNearAbsorb.residual (d.W N : Real) (d.L N : Real)
                ellu etau D Jbar ru 2 (N : Real) zetaCtr := by
                  have hnbase := hn.2
                  rw [hdist] at hnbase
                  convert hnbase using 1
                  all_goals simp only [ellu, etau, ru, Jbar, dist,
                    APrimeDriftNearAbsorb.residual]
                  all_goals ring
          _ <= _ := by
            calc
              _ <= 4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
                    Lemma57.cNear (d.W N : Real) ellu *
                    tailT (d.W N : Real) ellu etau D dist +
                  (4 * (N : Real)^zetaCtr *
                    ((d.L N : Real) * Jbar / (ellu * etau * ru^2)) *
                    (((d.W N : Real) * ellu * etau)^2 *
                      Real.exp (Real.log (d.W N : Real)^(3 / 4 : Real))) *
                    tailT (d.W N : Real) ellu etau D
                      (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) *
                    (etau⁻¹ * ru^3 *
                      tailT (d.W N : Real) ellu etau D dist) :=
                        add_le_add le_rfl hres
              _ = _ := by ring
      have hnCoeff :
          norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
            (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
            nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u *
              tailT (d.W N : Real) ellu etau D dist := by
        simpa only [nearSourceCoeff, ellu, etau, ru, Jbar] using hn'
      exact hnCoeff.trans (by
        unfold Step2.tT
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right hFarCoeff) hTail.le)
    · have hf := hfarN k hk hkTop omega homega hwide u hu (b 0) (b 1)
          (by simpa only [dist, ellu, hdist] using hgeom)
      change _ /\
        norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
          (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
          (etaT E u)⁻¹ *
            (4 * (N : Real)^zetaCtr * (B.ell N u / B.ell N (s N))) *
            (Lemma57.cFar (d.W N : Real) (B.ell N u) *
                APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u *
                (flowDelta d E t N + (d.W N : Real)⁻¹) +
              APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u *
                Real.sqrt
                  (APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u) *
                (168 * ((d.W N : Real) * B.ell N u * etaT E u)⁻¹ +
                  (d.L N : Real) * Real.sqrt ((d.W N : Real)^(-D)) /
                    B.ell N u)) *
            tailT (d.W N : Real) (B.ell N u) (etaT E u) D
              (zdist (d.L N) (b 1 - b 0)) at hf
      have hf' :
          norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
            (Hflow d N u omega) (zt E u) (b 0) (b 1)) <=
            farSourceCoeff d E D s t zetaCtr tauG delta N u *
              tailT (d.W N : Real) ellu etau D dist := by
        simpa only [farSourceCoeff, ellu, etau, ru, Jbar, dist, hdist] using hf.2
      exact hf'.trans (by
        unfold Step2.tT
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left hNearCoeff) hTail.le)
  have hDrift : forall b : LoopArg (d.L N) 2,
      norm (DriftDef.driftF B E N u ((sample d).H N u omega)
        Step2.sigPM b) <=
        (nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u +
          farSourceCoeff d E D s t zetaCtr tauG delta N u +
          quadCoeff d E D N u omega) *
          Step2.tT B E N D u (zdist (d.L N) (b 0 - b 1)) := by
    intro b
    have hquad := Step2.norm_eLL_le (L := d.L N) (d.three_le_L N)
      (W := (d.W N : Real)) (ℓu := B.ell N u) (ηu := etaT E u)
      hW0 hellU hetaU D (Step2.lk (sample d) E N u omega) ![b 0, b 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hquad
    rw [<- Step2FarInputs.etaExpand_two b]
    change norm (DriftDef.driftF (band d) E N u ((sample d).H N u omega)
      ![true, false] ![b 0, b 1]) <= _
    have hdec := DriftDef.driftF_zero_eq_eGpm_add_quadGlue
      (band d) E N u ((sample d).H N u omega) (b 0) (b 1)
    have hq := Step2FarInputs.quadGlue_pm_eq_eLL
      (sample d) E N u omega (b 0) (b 1)
    rw [hdec, hq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hquad' :
        norm (Step2.eLL (d.L N) (d.W N : Real)
          (Step2.lk (sample d) E N u omega) ![b 0, b 1]) <=
          quadCoeff d E D N u omega *
            Step2.tT B E N D u (zdist (d.L N) (b 0 - b 1)) := by
      change norm (Step2.eLL (d.L N) (d.W N : Real)
          (Step2.lk (sample d) E N u omega) ![b 0, b 1]) <=
        Real.exp 1 * (Step2.jS (sample d) E D N u omega)^2 *
          (36 * ((etaT E u)⁻¹ *
            (((d.W N : Real) * B.ell N u * etaT E u)⁻¹)) +
            (d.W N : Real) * (d.L N : Real) * (d.W N : Real)^(-D)) *
          tailT (d.W N : Real) (B.ell N u) (etaT E u) D
            (zdist (d.L N) (b 0 - b 1))
      simpa only [Step2.jS, B, Gauss.band_L, Gauss.band_W] using hquad
    calc
      _ <= norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
              (Hflow d N u omega) (zt E u) (b 0) (b 1)) +
            norm (Step2.eLL (d.L N) (d.W N : Real)
              (Step2.lk (sample d) E N u omega) ![b 0, b 1]) :=
        norm_add_le _ _
      _ <= (nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u +
              farSourceCoeff d E D s t zetaCtr tauG delta N u) *
              Step2.tT B E N D u (zdist (d.L N) (b 0 - b 1)) +
            quadCoeff d E D N u omega *
              Step2.tT B E N D u (zdist (d.L N) (b 0 - b 1)) :=
        add_le_add (hSource b) hquad'
      _ = _ := by ring
  have hU := Step2.norm_Uker_flow (B := B) (E := E) (D := D)
    hE hu0 hu.2 hv0 hv1 hW hFullCoeff hDrift a
  have hscale : 0 < APrimeDriftTimeFamily.driftScale
      d E D N a (s N) v :=
    APrimeDriftTimeFamily.driftScale_pos d hE
      (hu.1.trans hu.2) hv1 N a
  have hT : 0 < Step2.tT B E N D v
      (zdist (d.L N) (a 0 - a 1)) := by
    unfold Step2.tT
    exact tailT_pos hW0 _
  rw [APrimeDriftTimeFamily.driftAt]
  calc
    _ <= ((nearSourceCoeff d E D s zetaSrc zetaCtr tauG delta N u +
          farSourceCoeff d E D s t zetaCtr tauG delta N u +
          quadCoeff d E D N u omega) *
          (etaT E u / etaT E v)^2 *
          Step2.xiK (d.L N) (d.W N) (mE E).im *
          Step2.tT B E N D v (zdist (d.L N) (a 0 - a 1))) /
        APrimeDriftTimeFamily.driftScale d E D N a (s N) v :=
      div_le_div_of_nonneg_right hU hscale.le
    _ = _ := by
      unfold APrimeDriftTimeFamily.driftScale Step2Moment.ratR
      exact normalized_transport_identity hT.ne' hetaS hetaU hetaV

/-- T1399's positive first-cell witness is reused without changing its
actual Gaussian sample, generic common event, or p=1 widened support. -/
theorem positive_cell_full_drift_hypotheses_witness :
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

#print axioms nearSourceCoeff
#print axioms farSourceCoeff
#print axioms quadCoeff
#print axioms eventually_driftAt_le_profile
#print axioms positive_cell_full_drift_hypotheses_witness

end
end RBM.APrimeGeneralMovingDriftAtProfileGeneralDims
