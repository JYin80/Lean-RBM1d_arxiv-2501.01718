/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingGoodSetFlowActual
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeGeneralMovingRawSources
import RBM1D.Gauss.APrimeGeneralMovingTwoChargeAllTimeOneLoop
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.LkGoodMeasurable

/-!
# T579: one common event for the general-moving sources

The measurable core below carries the unchanged raw Step-1 sources, the
literal `goodSetFlow`, both centered charges, and the block-resolved Green
bound on one sample.  The only downstream consequence proved here is the
support-local block cap, with the full moving factor `ratR ^ 4` retained.
-/

namespace RBM.APrimeGeneralMovingCommonSources

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The two centered charges, with one fixed loss, on the whole moving window. -/
def centeredEvent (E : Real) (s t : Nat -> Real) (zetaCtr : Real)
    (N : Nat) : Set (Ω d) :=
  {omega | forall sigma : Bool,
    forall p : TimeIcc s t N × ZMod (d.L N),
      norm (APrimeGeneralMovingTwoChargeModulus.centeredTrace
        E N (p.1 : Real) omega sigma p.2) <=
      (N : Real)^zetaCtr *
        (2 * APrimeGeneralMovingControlExtension.qExt
          E s t N (p.1 : Real))}

/-- The all-time block-resolved Green event supplied by `APrimeJG`. -/
def blockEvent (E D : Real) (s t : Nat -> Real) (tauG : Real)
    (N : Nat) : Set (Ω d) :=
  {omega | forall u : TimeIcc s t N,
    APrimeJG.jG (Gauss.sample d) E N (u : Real) omega
      (B.ell N (u : Real)) (etaT E (u : Real)) D <=
    1 + (N : Real)^tauG *
      (9 * Real.exp (Real.sqrt 3) *
        Step2.jS (Gauss.sample d) E D N (u : Real) omega + 2)}

/-- The literal intersection of the four source events. -/
def rawCarrier (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) : Set (Ω d) :=
  APrimeGeneralMovingRawSources.sourceGood E s t zetaSrc N ∩
  Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t) N ∩
  centeredEvent E s t zetaCtr N ∩
  blockEvent E D s t tauG N

/-- A measurable subset of the literal carrier with the same complement measure. -/
noncomputable def commonEvent (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) : Set (Ω d) :=
  Gauss.measCore (Gauss.P d)
    (rawCarrier E D s t zetaSrc zetaCtr tauG N)

theorem measurableSet_commonEvent (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) :
    MeasurableSet (commonEvent E D s t zetaSrc zetaCtr tauG N) :=
  Gauss.measurableSet_measCore _ _

theorem commonEvent_subset_rawCarrier (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) :
    commonEvent E D s t zetaSrc zetaCtr tauG N ⊆
      rawCarrier E D s t zetaSrc zetaCtr tauG N :=
  Gauss.measCore_subset _ _

/-- All four source components hold with high probability on one measurable event. -/
theorem highProb_commonEvent
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    forall zetaSrc zetaCtr tauG : Real,
      0 < zetaSrc -> 0 < zetaCtr -> 0 < tauG ->
      HighProb (Gauss.P d)
        (commonEvent E D s t zetaSrc zetaCtr tauG) := by
  let kappa : Real := (2 - |E|) / 2
  have hkappa : 0 < kappa := by
    dsimp [kappa]
    linarith
  have hEkappa : |E| <= 2 - kappa := by
    dsimp [kappa]
    linarith
  have hStep : Step1.Hyp (Gauss.sample d) E s t :=
    Gauss.step1Hyp_gauss_of_scale'' d hkappa hEkappa hB hs0 hst ht1
      hreg.1 hc hreg.2
  intro zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG
  have hSource : HighProb (Gauss.P d)
      (APrimeGeneralMovingRawSources.sourceGood E s t zetaSrc) :=
    (APrimeGeneralMovingRawSources.general_moving_raw_sources
      hE hs0 hst ht1 hc hreg hB hStep zetaSrc hzetaSrc).1
  have hGood : HighProb (Gauss.P d)
      (Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t)) :=
    APrimeGeneralMovingGoodSetFlowActual.highProb_goodSetFlow
      hE hs0 hst ht1 hc hreg hB
  have hTwo :=
    APrimeGeneralMovingTwoChargeAllTimeOneLoop.centeredTrace_twoCharge_stochDom_timeIcc
      hE hs0 hst ht1 hc hreg hB hStep
  have hFalse := (hTwo false).highProb hzetaCtr
  have hTrue := (hTwo true).highProb hzetaCtr
  have hCentered : HighProb (Gauss.P d) (centeredEvent E s t zetaCtr) := by
    refine (hFalse.inter hTrue).mono ?_
    filter_upwards with N omega homega
    intro sigma p
    cases sigma with
    | false => exact homega.1 p
    | true => exact homega.2 p
  have hEta : ∀ᶠ N : Nat in atTop,
      (N : Real) ^ (-(1 : Real)) <= etaT E (t N) :=
    Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hDelta : ∀ᶠ N : Nat in atTop,
      Gauss.flowDelta d E t N <= (N : Real) ^ (-(c / 6)) :=
    Gauss.flowDelta_le_rpow_neg d hreg.2
  have hEntry : Gauss.EntryBoundFlow' d E s t
      (fun N => 2 * (N : Real) ^ (-D)) :=
    Gauss.entryBoundFlow_floor d hE hs0 hst ht1 zero_le_one hEta
      (by linarith : (0 : Real) < c / 6) hDelta (by linarith)
  have hBlock : HighProb (Gauss.P d) (blockEvent E D s t tauG) := by
    change HighProb (Gauss.P d) (fun N => {omega | forall u : TimeIcc s t N,
      APrimeJG.jG (Gauss.sample d) E N (u : Real) omega
        (B.ell N (u : Real)) (etaT E (u : Real)) D <=
      1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) *
          Step2.jS (Gauss.sample d) E D N (u : Real) omega + 2)})
    exact APrimeJG.highProb_jG_le_of_entryBoundFlow d hE hs0 hst ht1
      hreg.1 D (by linarith) hEntry hGood htauG
  have hAll := (((hSource.inter hGood).inter hCentered).inter hBlock)
  change HighProb (Gauss.P d) (fun N => Gauss.measCore (Gauss.P d)
    (rawCarrier E D s t zetaSrc zetaCtr tauG N))
  exact Gauss.highProb_measCore hAll

/-- The raw, centered, and block sources hold pathwise on the same sample. -/
theorem eventually_common_sources
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (_hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG : Real}
    (hzetaSrc : 0 < zetaSrc)
    (_hzetaCtr : 0 < zetaCtr)
    (_htauG : 0 < tauG) :
    ∀ᶠ N : Nat in atTop,
      ∀ omega ∈ commonEvent E D s t zetaSrc zetaCtr tauG N,
      ∀ u : TimeIcc s t N,
        APrimeFullQV.SourceEvent (Gauss.sample d) E N (u : Real) omega
          (APrimeGeneralMovingRawSources.sourceEll s zetaSrc N)
          (APrimeGeneralMovingRawSources.sourceC4 E s zetaSrc N u) ∧
        (∀ a : LoopData (d.L N) 3,
          norm ((Gauss.sample d).Lval E N (u : Real) omega a.idx) <=
            APrimeGeneralMovingRawSources.sourceC3 E s zetaSrc N u) ∧
        (∀ sigma : Bool, ∀ b : ZMod (d.L N),
          norm (APrimeGeneralMovingTwoChargeModulus.centeredTrace
            E N (u : Real) omega sigma b) <=
          (N : Real)^zetaCtr *
            (2 * APrimeGeneralMovingControlExtension.qExt
              E s t N (u : Real))) ∧
        APrimeJG.jG (Gauss.sample d) E N (u : Real) omega
          (B.ell N (u : Real)) (etaT E (u : Real)) D <=
          1 + (N : Real)^tauG *
            (9 * Real.exp (Real.sqrt 3) *
              Step2.jS (Gauss.sample d) E D N (u : Real) omega + 2) := by
  let kappa : Real := (2 - |E|) / 2
  have hkappa : 0 < kappa := by dsimp [kappa]; linarith
  have hEkappa : |E| <= 2 - kappa := by dsimp [kappa]; linarith
  have hStep : Step1.Hyp (Gauss.sample d) E s t :=
    Gauss.step1Hyp_gauss_of_scale'' d hkappa hEkappa hB hs0 hst ht1
      hreg.1 hc hreg.2
  have hSources :=
    (APrimeGeneralMovingRawSources.general_moving_raw_sources
      hE hs0 hst ht1 hc hreg hB hStep zetaSrc hzetaSrc).2.2.2
  filter_upwards [hSources] with N hN omega homega u
  have hCarrier := commonEvent_subset_rawCarrier
    E D s t zetaSrc zetaCtr tauG N homega
  rcases hCarrier with ⟨⟨⟨hSource, _hGood⟩, hCentered⟩, hBlock⟩
  have hRaw := hN omega hSource u
  exact ⟨hRaw.1, hRaw.2, fun sigma b => hCentered sigma (u, b), hBlock u⟩

/-- On positive widened support the block estimate retains the exact moving
normalization `ratR E s N u ^ 4`. -/
theorem eventually_block_cap_on_widened_support
    {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    (_hB : BoundsCore (Gauss.sample d) E s)
    {zetaSrc zetaCtr tauG delta : Real}
    (_hzetaSrc : 0 < zetaSrc) (_hzetaCtr : 0 < zetaCtr)
    (_htauG : 0 < tauG) (hdelta : 0 < delta)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      1 <= k ->
      k <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N ->
      ∀ omega ∈ commonEvent E D s t zetaSrc zetaCtr tauG N,
      0 < APrimeWeight.widenedW
        (APrimeWeight.canonicalR s t
          (APrimeGeneralMovingMesh.targetMesh D)) 1
        (APrimeGeneralMovingDetFields.J E D s) s t
        (APrimeGeneralMovingMesh.targetMesh D) delta p N k omega ->
      ∀ u ∈ Set.Icc (s N)
          (cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k),
        APrimeGeneralMovingDetFields.J E D s N u omega <=
          (4 * Real.exp 1 + 2) * (N : Real)^(2*delta) ∧
        APrimeJG.jG (Gauss.sample d) E N u omega
          (B.ell N u) (etaT E u) D <=
          1 + (N : Real)^tauG *
            (9 * Real.exp (Real.sqrt 3) *
              ((4 * Real.exp 1 + 2) * (N : Real)^(2*delta) *
                Step2Moment.ratR E s N u ^ 4) + 2) := by
  have hcap := APrimeGeneralMovingPrefixSupport.eventually_running_cap
    hE hD hs0 hst ht1 hc hreg hdelta p hp
  filter_upwards [hcap] with N hcapN
  intro k hk hkTop omega homega hwide u hu
  have hCarrier := commonEvent_subset_rawCarrier
    E D s t zetaSrc zetaCtr tauG N homega
  rcases hCarrier with ⟨⟨⟨hSource, _hGood⟩, _hCentered⟩, hBlock⟩
  have hGoodMesh := APrimeGeneralMovingRawSources.sourceGood_subset_good
    E s t zetaSrc N hSource
  have hJ := hcapN k hk hkTop omega hGoodMesh hwide u hu
  have hend : cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k ∈
      Set.Icc (s N) (t N) :=
    MomentDuhamelCut.netFinset_subset_Icc (hst N)
      (APrimeGeneralMovingMesh.targetMesh_pos D N) _
      (cutNetPt_mem_netFinset hkTop)
  have huWindow : u ∈ Set.Icc (s N) (t N) :=
    ⟨hu.1, hu.2.trans hend.2⟩
  let uu : TimeIcc s t N := ⟨u, huWindow⟩
  have hBlockU := hBlock uu
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
      ((4 * Real.exp 1 + 2) * (N : Real) ^ (2 * delta)) *
        Step2Moment.ratR E s N u ^ 4 := by
    rw [hJS]
    exact mul_le_mul_of_nonneg_right hJ (by positivity)
  refine ⟨hJ, hBlockU.trans ?_⟩
  dsimp [uu] at hBlockU ⊢
  gcongr

private theorem eventually_firstCellT_half {tauPrime : Real} (htauPrime : 0 < tauPrime) :
    ∀ᶠ N : Nat in atTop, firstCellT tauPrime N = 1 / 2 := by
  have hWt : Tendsto (fun N : Nat => ((d.W N : Real)) ^ (-tauPrime))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop htauPrime).comp (Step2.tendsto_W B)
  filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)]
    with N hW
  change gridT ((B.W N : Real)) tauPrime (1 / 2 : Real) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Dims.growW N : Real) ^ (-tauPrime) < 1 / 2 at hW
  linarith

private theorem eventually_firstCell_kOne_widenedW_one
    {tauPrime delta : Real} (htauPrime : 0 < tauPrime) (hdelta : 0 < delta) :
    ∀ᶠ N : Nat in atTop,
      firstCellS tauPrime N < firstCellT tauPrime N ∧
      1 <= cutNetTop (firstCellS tauPrime) (firstCellT tauPrime)
        (APrimeGeneralMovingMesh.targetMesh 60) N ∧
      ∀ omega : Ω d, ∀ p : Nat,
        APrimeWeight.widenedW
          (APrimeWeight.canonicalR (firstCellS tauPrime) (firstCellT tauPrime)
            (APrimeGeneralMovingMesh.targetMesh 60)) 1
          (APrimeGeneralMovingDetFields.J 0 60 (firstCellS tauPrime))
          (firstCellS tauPrime) (firstCellT tauPrime)
          (APrimeGeneralMovingMesh.targetMesh 60) delta p N 1 omega = 1 := by
  filter_upwards [eventually_firstCellT_half htauPrime, eventually_ge_atTop 2]
    with N ht hN
  let s := firstCellS tauPrime
  let t := firstCellT tauPrime
  let mesh := APrimeGeneralMovingMesh.targetMesh 60
  let J := APrimeGeneralMovingDetFields.J 0 60 s
  have hs : s N = 0 := by
    change gridT ((B.W N : Real)) tauPrime (1 / 2 : Real) 0 = 0
    exact gridT_zero (by norm_num)
  have hactive : 1 <= cutNetTop s t mesh N := by
    unfold cutNetTop mesh APrimeGeneralMovingMesh.targetMesh
    rw [hs, show t N = 1 / 2 by exact ht,
      APrimeGeneralMovingMesh.polynomialMesh_eq_of_pos (by omega)]
    apply Nat.le_floor
    norm_num
    have hNr : (2 : Real) <= N := by exact_mod_cast hN
    have hNone : (1 : Real) <= N := by linarith
    have hpow : (2 : Real) <= (N : Real) ^
        (2 * (2 * (60 : Real) + 7) + 4) := by
      calc
        (2 : Real) <= N := hNr
        _ = (N : Real) ^ (1 : Real) := (Real.rpow_one _).symm
        _ <= (N : Real) ^ (2 * (2 * (60 : Real) + 7) + 4) :=
          Real.rpow_le_rpow_of_exponent_le hNone (by norm_num)
    norm_num at hpow
    calc
      (1 : Real) = (1 / 2) * 2 := by norm_num
      _ <= _ := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hsfun : s = fun _ => (0 : Real) := by
    funext M
    change gridT ((B.W M : Real)) tauPrime (1 / 2 : Real) 0 = 0
    exact gridT_zero (by norm_num)
  have hpref : ∀ omega : Ω d,
      omega ∈ prefNet J s mesh (fun M _ => (M : Real) ^ (2 * delta) * 1) N 1 := by
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
    have hNreal : (1 : Real) <= N := by
      exact_mod_cast (show 1 <= N by omega)
    have hpow : 1 <= (N : Real) ^ (2 * delta) :=
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
        (APrimeGeneralMovingDetFields.J_nonneg 0 60 s) delta N 1 omega (hpref omega)
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

/-- A strict first cell has a resident of the common event on which every
moment order has widened weight one.  This theorem is only a satisfiability
witness for the general event package. -/
theorem positive_length_common_support_witness :
    ∃ tauPrime : Real, 0 < tauPrime ∧
    ∃ c : Real, 0 < c ∧
    ∃ s t : Nat -> Real,
      (forall N, s N = 0) ∧
      (forall N, 0 <= s N) ∧
      (forall N, s N <= t N) ∧
      (forall N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧
      BoundsCore (Gauss.sample d) 0 s ∧
      Step1.Hyp (Gauss.sample d) 0 s t ∧
      forall zetaSrc zetaCtr tauG delta : Real,
        0 < zetaSrc -> 0 < zetaCtr -> 0 < tauG -> 0 < delta ->
        ∀ᶠ N : Nat in atTop,
          s N < t N ∧
          ∃ omega,
            omega ∈ commonEvent 0 60 s t zetaSrc zetaCtr tauG N ∧
            1 <= cutNetTop s t
              (APrimeGeneralMovingMesh.targetMesh 60) N ∧
            ∀ p : Nat,
              APrimeWeight.widenedW
                (APrimeWeight.canonicalR s t
                  (APrimeGeneralMovingMesh.targetMesh 60)) 1
                (APrimeGeneralMovingDetFields.J 0 60 s) s t
                (APrimeGeneralMovingMesh.targetMesh 60)
                delta p N 1 omega = 1 := by
  obtain ⟨tauPrime, htauPrime, c, hc, hsEq, hs0, hst, ht1, hreg, hB, hpos⟩ :=
    APrimeGeneralMovingInitialHinit.positive_length_hinit_witness
  let s := firstCellS tauPrime
  let t := firstCellT tauPrime
  change (forall N, s N = 0) at hsEq
  change (forall N, 0 <= s N) at hs0
  change (forall N, s N <= t N) at hst
  change (forall N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  change BoundsCore (Gauss.sample d) 0 s at hB
  change ∀ᶠ N : Nat in atTop, s N < t N at hpos
  have hStep : Step1.Hyp (Gauss.sample d) 0 s t :=
    Gauss.step1Hyp_gauss_of_scale'' d (κ := 1) (by norm_num) (by norm_num)
      hB hs0 hst ht1 hreg.1 hc hreg.2
  refine ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
    hreg, hB, hStep, ?_⟩
  intro zetaSrc zetaCtr tauG delta hzetaSrc hzetaCtr htauG hdelta
  have hHP : HighProb (Gauss.P d)
      (commonEvent 0 60 s t zetaSrc zetaCtr tauG) :=
    highProb_commonEvent (E := 0) (D := 60) (c := c)
      (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
      zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG
  have hnonempty : ∀ᶠ N : Nat in atTop,
      (commonEvent 0 60 s t zetaSrc zetaCtr tauG N).Nonempty :=
    hHP.nonempty (by simp)
  have hplateau := eventually_firstCell_kOne_widenedW_one htauPrime hdelta
  change ∀ᶠ N : Nat in atTop,
      s N < t N ∧
      1 <= cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N ∧
      ∀ omega : Ω d, ∀ p : Nat,
        APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t
            (APrimeGeneralMovingMesh.targetMesh 60)) 1
          (APrimeGeneralMovingDetFields.J 0 60 s) s t
          (APrimeGeneralMovingMesh.targetMesh 60) delta p N 1 omega = 1 at hplateau
  filter_upwards [hpos, hnonempty, hplateau] with N hposN hnonemptyN hplateauN
  obtain ⟨omega, homega⟩ := hnonemptyN
  exact ⟨hposN, omega, homega, hplateauN.2.1, hplateauN.2.2 omega⟩

#print axioms centeredEvent
#print axioms blockEvent
#print axioms rawCarrier
#print axioms commonEvent
#print axioms measurableSet_commonEvent
#print axioms commonEvent_subset_rawCarrier
#print axioms highProb_commonEvent
#print axioms eventually_common_sources
#print axioms eventually_block_cap_on_widened_support
#print axioms positive_length_common_support_witness

end
end RBM.APrimeGeneralMovingCommonSources
