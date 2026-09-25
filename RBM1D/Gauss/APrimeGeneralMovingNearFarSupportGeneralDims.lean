/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftSourceGeneralDims
import RBM1D.Gauss.APrimeGeneralMovingLoopModulusGeneralDims
import RBM1D.Gauss.APrimeGeneralMovingDriftSource
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeFirstCellCommon

/-!
# T1399: arbitrary-Dims near/far drift bounds on positive running support

The actual pointwise source bounds from T1389 are transported to every point
of a positive widened-weight prefix.  The running cap uses only the bare
paper condition (2.72), through T1383, and the norm event is extracted from
T1389's sourceGood carrier on the same Gaussian sample.  The high-probability
producer for that common event remains a separate theorem with its existing
stronger hypotheses.
-/

namespace RBM.APrimeGeneralMovingNearFarSupportGeneralDims

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private theorem far_rhs_mono
    {W L ell eta D kappa1 kappa2 J K dist : ℝ}
    (hW : 1 ≤ W) (hell : 1 ≤ ell) (heta : 0 < eta)
    (hL : 0 ≤ L)
    (hkappa1 : 0 ≤ kappa1) (hkappa2 : 0 ≤ kappa2)
    (hJ : 1 ≤ J) (hJK : J ≤ K) :
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
  have hJ0 : 0 ≤ J := by linarith
  have hK0 : 0 ≤ K := hJ0.trans hJK
  have hcFar : 0 ≤ Lemma57.cFar W ell :=
    Lemma57.cFar_nonneg hW (by linarith)
  have hspatial : 0 ≤ 168 * (W * ell * eta)⁻¹ +
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

/-- On one T1389 common resident, sourceGood supplies the exact norm event
needed by T1383, so the normalized-loop cap and the block cap hold on the same
positive widened-weight prefix.  Only bare Cond272 is used here. -/
private theorem eventually_common_event_block_cap (d : Dims)
    {E D δ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg : Cond272 (band d) E s t) (hδ : 0 < δ)
    {zetaSrc zetaCtr tauG : ℝ}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k → k ≤ cutNetTop s t
        (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ omega ∈ APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
        d E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingLoopModulusGeneralDims.actualJ d E D s)
        s t (APrimeGeneralMovingMesh.targetMesh D) δ p N k omega →
      ∀ u ∈ Icc (s N)
        (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      Step2Moment.jSnorm (sample d) E D s N u omega <=
          (4 * Real.exp 1 + 2) * (N : ℝ)^(2 * δ) ∧
      APrimeJG.jG (sample d) E N u omega
        ((band d).ell N u) (etaT E u) D <=
          APrimeGeneralMovingDriftSource.blockCap E s tauG δ N u := by
  have hcap :=
    APrimeGeneralMovingLoopModulusGeneralDims.eventually_running_prefix_cap d
      hE hD hs0 hst ht1 hreg hδ p hp
  filter_upwards [hcap] with N hcapN
  intro k hk hkTop omega homega hwide u hu
  have hCarrier :=
    APrimeGeneralMovingDriftSourceGeneralDims.commonEvent_subset_rawCarrier
      d E D s t zetaSrc zetaCtr tauG N homega
  rcases hCarrier with ⟨⟨⟨hSource, _hGood⟩, _hCentered⟩, hBlock⟩
  have hNorm : omega ∈
      APrimeGeneralMovingLoopModulusGeneralDims.normEvent d N := by
    have h := APrimeRawSourcesGeneralDims.sourceGood_subset_normX
      d E s t zetaSrc N hSource
    simpa only [APrimeGeneralMovingLoopModulusGeneralDims.normEvent] using h
  have hJbound := hcapN k hk hkTop omega hNorm hwide u hu
  have hend : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hend.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hBlockU := hBlock uu
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hR : 0 < Step2Moment.ratR E s N u :=
    Step2Moment.ratR_pos hE hs1 hu1
  have hJS : Step2.jS (sample d) E D N u omega =
      Step2Moment.jSnorm (sample d) E D s N u omega *
        Step2Moment.ratR E s N u ^ 4 := by
    dsimp [Step2Moment.jSnorm]
    exact (div_mul_cancel₀ _ (pow_ne_zero 4 hR.ne')).symm
  have hJSto : Step2.jS (sample d) E D N u omega <=
      ((4 * Real.exp 1 + 2) * (N : ℝ)^(2 * δ)) *
        Step2Moment.ratR E s N u ^ 4 := by
    rw [hJS]
    exact mul_le_mul_of_nonneg_right hJbound (by positivity)
  refine ⟨hJbound, ?_⟩
  dsimp [APrimeGeneralMovingDriftSource.blockCap]
  dsimp only [uu] at hBlockU
  calc
    APrimeJG.jG (sample d) E N u omega
        ((band d).ell N u) (etaT E u) D
      <= 1 + (N : ℝ)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          (Step2.jS (sample d) E D N u omega) + 2) := hBlockU
    _ <= 1 + (N : ℝ)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          (((4 * Real.exp 1 + 2) * (N : ℝ)^(2 * δ)) *
            Step2Moment.ratR E s N u ^ 4) + 2) := by
      gcongr

/-- The far branch of T586 is bounded on every positive widened-weight
prefix.  Its original `N` losses, `r_u`, and spatial terms remain explicit. -/
theorem eventually_far_on_common_support (d : Dims)
    {E D : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg : Cond272 (band d) E s t)
    {zetaSrc zetaCtr tauG delta : ℝ}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k →
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ omega ∈ APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
        d E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingLoopModulusGeneralDims.actualJ d E D s)
        s t (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega →
      ∀ u ∈ Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      ∀ a1 a2 : ZMod (d.L N),
      ellStar (d.W N : ℝ) ((band d).ell N u) <=
        (zdist (d.L N) (a2 - a1) : ℝ) →
      let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
      APrimeJG.jG (sample d) E N u omega
          ((band d).ell N u) (etaT E u) D <= Jbar ∧
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N u omega) (zt E u) a1 a2) <=
        (etaT E u)⁻¹ *
          (4 * (N : ℝ)^zetaCtr *
            ((band d).ell N u / (band d).ell N (s N))) *
          (Lemma57.cFar (d.W N : ℝ) ((band d).ell N u) * Jbar *
              (Gauss.flowDelta d E t N + (d.W N : ℝ)⁻¹) +
            Jbar * Real.sqrt Jbar *
              (168 * ((d.W N : ℝ) * (band d).ell N u * etaT E u)⁻¹ +
                (d.L N : ℝ) * Real.sqrt ((d.W N : ℝ)^(-D)) /
                  (band d).ell N u)) *
          tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
            (zdist (d.L N) (a2 - a1)) := by
  have hcap := eventually_common_event_block_cap d hE hD hs0 hst ht1
    hreg hdelta hzetaSrc hzetaCtr htauG p hp
  filter_upwards [hcap] with N hcapN
  intro k hk hkTop omega homega hwide u hu a1 a2 hfar
  have hcapU := hcapN k hk hkTop omega homega hwide u hu
  have hend : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hend.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hbase :=
    APrimeGeneralMovingDriftSourceGeneralDims.pointwise_far_source_bound
      d hE hs0 hst ht1 homega uu a1 a2 hfar
  dsimp only at hbase
  let J := APrimeJG.jG (sample d) E N u omega
    ((band d).ell N u) (etaT E u) D
  let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
  have hW : 1 ≤ (d.W N : ℝ) := by exact_mod_cast (band d).one_le_W N
  have hu0 : 0 ≤ u := (hs0 N).trans huWindow.1
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hell : 1 ≤ (band d).ell N u :=
    one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
  have heta : 0 < etaT E u := etaT_pos hE hu1
  have hJ : 1 ≤ J := APrimeJG.one_le_jG
    (sample d) E N u omega (by exact_mod_cast d.W_pos N)
  have hJcap : J <= Jbar := by
    simpa only [J, Jbar, APrimeGeneralMovingDriftSource.blockCap] using hcapU.2
  have hkappa1 : 0 <=
      4 * (N : ℝ)^zetaCtr *
        ((band d).ell N u / (band d).ell N (s N)) := by
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have hells : 0 < (band d).ell N (s N) := by
      have h := one_le_ellHat ((band d).L N)
        ((band d).three_le_L N) (hs0 N) hs1
      simpa only [Band.ell] using
        (show 0 < ellHat ((band d).L N) ((s N : ℝ) : ℂ) by linarith)
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (div_nonneg (by linarith) hells.le)
  have hkappa2 : 0 <= Gauss.flowDelta d E t N + (d.W N : ℝ)⁻¹ := by
    have hWpos : 0 < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
    unfold Gauss.flowDelta
    exact add_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr
        ((band d).scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _)
      (inv_nonneg.mpr hWpos.le)
  have hmono := far_rhs_mono hW hell heta (Nat.cast_nonneg _)
    hkappa1 hkappa2 hJ hJcap
    (L := (d.L N : ℝ)) (D := D)
    (dist := (zdist (d.L N) (a2 - a1) : ℝ))
  refine ⟨hJcap, hbase.trans ?_⟩
  simpa only [J, Jbar] using hmono

/-- The near branch of T586 is bounded on the same positive widened-weight
prefix.  The far-internal-label leakage, `N` losses, and near-log guard remain
in the original output form. -/
theorem eventually_near_on_common_support (d : Dims)
    {E D : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (hreg : Cond272 (band d) E s t)
    {zetaSrc zetaCtr tauG delta : ℝ}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr)
    (htauG : 0 < tauG) (hdelta : 0 < delta)
    (p : ℕ) (hp : 1 ≤ p) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ,
      1 ≤ k →
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      ∀ omega ∈ APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
        d E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingLoopModulusGeneralDims.actualJ d E D s)
        s t (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega →
      ∀ u ∈ Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
      ∀ a1 a2 : ZMod (d.L N),
      (zdist (d.L N) (a2 - a1) : ℝ) <=
        ellStar (d.W N : ℝ) ((band d).ell N u) →
      let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
      APrimeJG.jG (sample d) E N u omega
          ((band d).ell N u) (etaT E u) D <= Jbar ∧
      norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N u omega) (zt E u) a1 a2) <=
        4 * (N : ℝ)^(zetaCtr + zetaSrc) * (etaT E u)⁻¹ *
            ((band d).ell N u / (band d).ell N (s N))^3 *
            Lemma57.cNear (d.W N : ℝ) ((band d).ell N u) *
              tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
                (zdist (d.L N) (a2 - a1)) +
          (4 * (N : ℝ)^zetaCtr *
              ((band d).ell N u / (band d).ell N (s N))) *
            ((band d).ell N u * etaT E u)⁻¹ * (d.L N : ℝ) *
              ((etaT E u)⁻¹ * Jbar *
                tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
                  (APrimeDriftNearAbsorb.gap
                    (d.W N : ℝ) ((band d).ell N u))) := by
  have hcap := eventually_common_event_block_cap d hE hD hs0 hst ht1
    hreg hdelta hzetaSrc hzetaCtr htauG p hp
  have hlog : ∀ᶠ N : ℕ in atTop, 4 <= Real.log (d.W N : ℝ) :=
    (Real.tendsto_log_atTop.comp (Step2.tendsto_W (band d))).eventually_ge_atTop 4
  filter_upwards [hcap, hlog, eventually_ge_atTop 1]
    with N hcapN hlogN hN
  intro k hk hkTop omega homega hwide u hu a1 a2 hnear
  have hcapU := hcapN k hk hkTop omega homega hwide u hu
  have hend : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Icc (s N) (t N) := ⟨hu.1, hu.2.trans hend.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hbase :=
    APrimeGeneralMovingDriftSourceGeneralDims.pointwise_near_source_bound
      d hE hs0 hst ht1 (by omega : 0 < N) homega uu hlogN a1 a2 hnear
  dsimp only at hbase
  let J := APrimeJG.jG (sample d) E N u omega
    ((band d).ell N u) (etaT E u) D
  let Jbar := APrimeGeneralMovingDriftSource.blockCap E s tauG delta N u
  have hJcap : J <= Jbar := by
    simpa only [J, Jbar, APrimeGeneralMovingDriftSource.blockCap] using hcapU.2
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hells : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N)
      ((band d).three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((s N : ℝ) : ℂ) by linarith)
  have hu0 : 0 <= u := (hs0 N).trans huWindow.1
  have hu1 : u < 1 := huWindow.2.trans_lt (ht1 N)
  have hellu : 0 < (band d).ell N u := by
    have h := one_le_ellHat ((band d).L N)
      ((band d).three_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) (u : ℂ) by linarith)
  have heta : 0 < etaT E u := etaT_pos hE hu1
  have hcoef : 0 <=
      (4 * (N : ℝ)^zetaCtr *
        ((band d).ell N u / (band d).ell N (s N))) *
        ((band d).ell N u * etaT E u)⁻¹ * (d.L N : ℝ) := by positivity
  have htail : 0 <= tailT (d.W N : ℝ) ((band d).ell N u)
      (etaT E u) D
      (APrimeDriftNearAbsorb.gap (d.W N : ℝ) ((band d).ell N u)) :=
    tailT_nonneg (by positivity) _
  have hrem :
      (4 * (N : ℝ)^zetaCtr *
          ((band d).ell N u / (band d).ell N (s N))) *
        ((band d).ell N u * etaT E u)⁻¹ * (d.L N : ℝ) *
          ((etaT E u)⁻¹ * J *
            tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
              (APrimeDriftNearAbsorb.gap
                (d.W N : ℝ) ((band d).ell N u))) <=
      (4 * (N : ℝ)^zetaCtr *
          ((band d).ell N u / (band d).ell N (s N))) *
        ((band d).ell N u * etaT E u)⁻¹ * (d.L N : ℝ) *
          ((etaT E u)⁻¹ * Jbar *
            tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
              (APrimeDriftNearAbsorb.gap
                (d.W N : ℝ) ((band d).ell N u))) := by
    apply mul_le_mul_of_nonneg_left _ hcoef
    apply mul_le_mul_of_nonneg_right _ htail
    exact mul_le_mul_of_nonneg_left hJcap (inv_nonneg.mpr heta.le)
  refine ⟨hJcap, hbase.trans ?_⟩
  exact add_le_add le_rfl hrem

private theorem eventually_firstCellT_half_local {tauPrime : ℝ}
    (htauPrime : 0 < tauPrime) :
    ∀ᶠ N : ℕ in atTop, firstCellT tauPrime N = 1 / 2 := by
  have hWt : Tendsto (fun N : ℕ =>
      ((Dims.exampleGrow.W N : ℝ)) ^ (-tauPrime)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop htauPrime).comp
      (Step2.tendsto_W (band Dims.exampleGrow))
  filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hW
  change gridT ((band Dims.exampleGrow).W N : ℝ) tauPrime
    (1 / 2 : ℝ) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  have hW' : ((Dims.growW N : ℝ)) ^ (-tauPrime) < 1 / 2 := by
    simpa only [Dims.exampleGrow_W] using hW
  linarith

private theorem eventually_firstCell_kOne_widenedW_one
    {tauPrime delta : ℝ} (htauPrime : 0 < tauPrime) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      firstCellS tauPrime N < firstCellT tauPrime N ∧
      1 <= cutNetTop (firstCellS tauPrime) (firstCellT tauPrime)
        (APrimeGeneralMovingMesh.targetMesh 60) N ∧
      ∀ omega : Ω Dims.exampleGrow, ∀ p : ℕ,
        APrimeWeight.widenedW
          (APrimeWeight.canonicalR (firstCellS tauPrime) (firstCellT tauPrime)
            (APrimeGeneralMovingMesh.targetMesh 60)) 1
          (APrimeGeneralMovingDetFields.J 0 60 (firstCellS tauPrime))
          (firstCellS tauPrime) (firstCellT tauPrime)
          (APrimeGeneralMovingMesh.targetMesh 60) delta p N 1 omega = 1 := by
  filter_upwards [eventually_firstCellT_half_local htauPrime,
    eventually_ge_atTop 2] with N ht hN
  let s := firstCellS tauPrime
  let t := firstCellT tauPrime
  let mesh := APrimeGeneralMovingMesh.targetMesh 60
  let J := APrimeGeneralMovingDetFields.J 0 60 s
  have hs : s N = 0 := by
    change gridT ((band Dims.exampleGrow).W N : ℝ) tauPrime
      (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hactive : 1 <= cutNetTop s t mesh N := by
    unfold cutNetTop mesh APrimeGeneralMovingMesh.targetMesh
    rw [hs, show t N = 1 / 2 by exact ht,
      APrimeGeneralMovingMesh.polynomialMesh_eq_of_pos (by omega)]
    apply Nat.le_floor
    norm_num
    have hNr : (2 : ℝ) <= N := by exact_mod_cast hN
    have hNone : (1 : ℝ) <= N := by linarith
    have hpow : (2 : ℝ) <= (N : ℝ) ^
        (2 * (2 * (60 : ℝ) + 7) + 4) := by
      calc
        (2 : ℝ) <= N := hNr
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ <= (N : ℝ) ^ (2 * (2 * (60 : ℝ) + 7) + 4) :=
          Real.rpow_le_rpow_of_exponent_le hNone (by norm_num)
    norm_num at hpow
    calc
      (1 : ℝ) = (1 / 2) * 2 := by norm_num
      _ <= _ := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hsfun : s = fun _ => (0 : ℝ) := by
    funext M
    change gridT ((band Dims.exampleGrow).W M : ℝ) tauPrime
      (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hpref : ∀ omega : Ω Dims.exampleGrow,
      omega ∈ prefNet J s mesh
        (fun M _ => (M : ℝ) ^ (2 * delta) * 1) N 1 := by
    intro omega j hj
    have hj0 : j = 0 := by
      simpa only [Finset.mem_range, Nat.lt_one_iff] using hj
    subst j
    have hJzero : J N (cutNetPt s mesh N 0) omega = 1 := by
      simp only [cutNetPt_zero]
      rw [hs]
      dsimp [J, APrimeGeneralMovingDetFields.J]
      rw [hsfun]
      exact APrimeFirstCellCommon.J_zero N omega
    rw [hJzero]
    have hNreal : (1 : ℝ) <= N := by exact_mod_cast (show 1 <= N by omega)
    have hpow : 1 <= (N : ℝ) ^ (2 * delta) :=
      Real.one_le_rpow hNreal (by linarith)
    simpa using hpow
  refine ⟨?_, hactive, ?_⟩
  · change s N < t N
    rw [hs, show t N = 1 / 2 by exact ht]
    norm_num
  · intro omega p
    have hpieceLower : 1 <= APrimeWeight.piecewiseW
        (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta N 1 omega :=
      APrimeWeight.piecewiseW_dom_canonical
        (APrimeGeneralMovingDetFields.J_nonneg 0 60 s) delta N 1 omega
        (hpref omega)
    have hpieceUpper := APrimeWeight.piecewiseW_le_one
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta N 1 omega
    have hpiece : APrimeWeight.piecewiseW
        (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta N 1 omega = 1 :=
      le_antisymm hpieceUpper hpieceLower
    have hlower := APrimeWeight.piecewiseW_le_widenedW
      (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
      (J := J) (s := s) (t := t) (mesh := mesh)
      (by norm_num) delta p N 1 omega
    have hupper := APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh delta p N 1 omega
    rw [hpiece] at hlower
    exact le_antisymm hupper hlower

/-- A positive first cell has an actual resident of the generic T1389 event,
and that same resident has universally positive widened weight at `k=1`.
The plateau identity is proved here for all samples; the sample itself comes
from the high-probability common-event producer. -/
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
              delta 1 N 1 omega = 1 := by
  obtain ⟨tauPrime, htauPrime, c, hc, hsEq, hs0, hst, ht1, hreg, hB,
      hpositive⟩ :=
    APrimeGeneralMovingInitialHinit.positive_length_hinit_witness
  let s := firstCellS tauPrime
  let t := firstCellT tauPrime
  change (∀ N, s N = 0) at hsEq
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  change Cond272Reg (band Dims.exampleGrow) 0 s t c at hreg
  change BoundsCore (sample Dims.exampleGrow) 0 s at hB
  change ∀ᶠ N : ℕ in atTop, s N < t N at hpositive
  have hHP : ∀ zetaSrc zetaCtr tauG : ℝ,
      0 < zetaSrc → 0 < zetaCtr → 0 < tauG →
      HighProb (P Dims.exampleGrow)
        (fun N =>
          APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
            Dims.exampleGrow 0 60 s t zetaSrc zetaCtr tauG N) := by
    intro zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG
    exact APrimeGeneralMovingDriftSourceGeneralDims.highProb_commonEvent
      Dims.exampleGrow (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
      zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG
  refine ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
    hreg, hB, ?_⟩
  intro zetaSrc zetaCtr tauG delta hzetaSrc hzetaCtr htauG hdelta
  have hresident : ∀ᶠ N : ℕ in atTop,
      (APrimeGeneralMovingDriftSourceGeneralDims.commonEvent
        Dims.exampleGrow 0 60 s t zetaSrc zetaCtr tauG N).Nonempty :=
    (hHP zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG).nonempty (by simp)
  have hplateau := eventually_firstCell_kOne_widenedW_one htauPrime hdelta
  filter_upwards [hresident, hpositive, hplateau] with N hmem hlen hplateauN
  obtain ⟨omega, homega⟩ := hmem
  have hweight := hplateauN.2.2 omega 1
  have hweight' : APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t
        (APrimeGeneralMovingMesh.targetMesh 60)) 1
      (APrimeGeneralMovingLoopModulusGeneralDims.actualJ
        Dims.exampleGrow 0 60 s)
      s t (APrimeGeneralMovingMesh.targetMesh 60) delta 1 N 1 omega = 1 := by
    simpa only [APrimeGeneralMovingLoopModulusGeneralDims.actualJ,
      APrimeGeneralMovingDetFields.J] using hweight
  exact ⟨hlen, hplateauN.2.1, omega, homega, hweight'⟩

#print axioms eventually_far_on_common_support
#print axioms eventually_near_on_common_support
#print axioms positive_length_exampleGrow_same_event_witness

end
end RBM.APrimeGeneralMovingNearFarSupportGeneralDims
