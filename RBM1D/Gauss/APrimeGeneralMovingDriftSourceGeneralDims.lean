/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeRawSourcesGeneralDims
import RBM1D.Gauss.APrimeAllTimeOneLoopGeneralDims
import RBM1D.Gauss.APrimeGoodSetFlowGeneralDims
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.APrimeFirstCellEGFar
import RBM1D.Gauss.APrimeDriftNearTriple
import RBM1D.Gauss.APrimeEGNearScaled
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore
import RBM1D.Gauss.LkGoodMeasurable

/-!
# T1389: arbitrary-dimension actual Gaussian near/far drift sources

This module lifts the accepted actual pointwise near and far source arguments
from `exampleGrow` to every `d : Dims`.  Its common event intersects the raw
3/4/6-loop carrier, the all-time Green good event, both centered charges, and
the all-time block `jG` source on one actual Gaussian sample.
-/

namespace RBM.APrimeGeneralMovingDriftSourceGeneralDims

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

/-- The joint centered source event at both charges on the full moving window. -/
def centeredEvent (d : Dims) (E ζ : Real) (s t : Nat -> Real) (N : Nat) :
    Set (Ω d) :=
  {omega | forall p : TimeIcc s t N × ZMod (d.L N), forall sigma : Bool,
    norm (APrimeCenteredModulusGeneralDims.centeredTrace d E N
      (p.1 : Real) omega sigma p.2) <=
      (N : Real)^ζ * (2 * APrimeAllTimeOneLoopGeneralDims.qExt d E s t N
        (p.1 : Real))}

/-- The accepted all-time block source, with the actual `jS` on the right. -/
def blockEvent (d : Dims) (E D : Real) (s t : Nat -> Real)
    (tauG : Real) (N : Nat) : Set (Ω d) :=
  {omega | forall u : TimeIcc s t N,
    APrimeJG.jG (sample d) E N (u : Real) omega
      ((band d).ell N (u : Real)) (etaT E (u : Real)) D <=
    1 + (N : Real)^tauG *
      (9 * Real.exp (Real.sqrt 3) * Step2.jS (sample d) E D N (u : Real) omega + 2)}

/-- Literal intersection of the accepted actual source events. -/
def rawCarrier (d : Dims) (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) : Set (Ω d) :=
  APrimeRawSourcesGeneralDims.sourceGood d E s t zetaSrc N ∩
    Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t) N ∩
    centeredEvent d E zetaCtr s t N ∩
    blockEvent d E D s t tauG N

/-- A measurable core of the four-source carrier, preserving its high probability. -/
noncomputable def commonEvent (d : Dims) (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) : Set (Ω d) :=
  Gauss.measCore (Gauss.P d)
    (rawCarrier d E D s t zetaSrc zetaCtr tauG N)

theorem measurableSet_commonEvent (d : Dims) (E D : Real) (s t : Nat -> Real)
    (zetaSrc zetaCtr tauG : Real) (N : Nat) :
    MeasurableSet (commonEvent d E D s t zetaSrc zetaCtr tauG N) :=
  Gauss.measurableSet_measCore _ _

theorem commonEvent_subset_rawCarrier (d : Dims) (E D : Real)
    (s t : Nat -> Real) (zetaSrc zetaCtr tauG : Real) (N : Nat) :
    commonEvent d E D s t zetaSrc zetaCtr tauG N ⊆
      rawCarrier d E D s t zetaSrc zetaCtr tauG N :=
  Gauss.measCore_subset _ _

/-- All four actual source components hold with high probability on one sample. -/
theorem highProb_commonEvent (d : Dims) {E D c : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    forall zetaSrc zetaCtr tauG : Real,
      0 < zetaSrc -> 0 < zetaCtr -> 0 < tauG ->
      HighProb (Gauss.P d)
        (commonEvent d E D s t zetaSrc zetaCtr tauG) := by
  let kappa : Real := (2 - |E|) / 2
  have hkappa : 0 < kappa := by dsimp [kappa]; linarith
  have hEkappa : |E| <= 2 - kappa := by dsimp [kappa]; linarith
  have hStep : Step1.Hyp (sample d) E s t :=
    Gauss.step1Hyp_gauss_of_scale'' d hkappa hEkappa hB hs0 hst ht1
      hreg.1 hc hreg.2
  intro zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG
  have hSource : HighProb (P d)
      (APrimeRawSourcesGeneralDims.sourceGood d E s t zetaSrc) :=
    (APrimeRawSourcesGeneralDims.general_moving_raw_sources
      d hE hs0 hst ht1 hc hreg hB hStep zetaSrc hzetaSrc).1
  have hGood : HighProb (P d)
      (Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t)) :=
    APrimeGoodSetFlowGeneralDims.highProb_goodSetFlow
      d hE hs0 hst ht1 hc hreg hB
  have hCentered : HighProb (P d) (centeredEvent d E zetaCtr s t) :=
    APrimeAllTimeOneLoopGeneralDims.highProb_centeredEvent d
      hE hs0 hst ht1 hc hzetaCtr hreg hB hStep
  have hEta : ∀ᶠ N : Nat in atTop,
      (N : Real)^(-(1 : Real)) <= etaT E (t N) :=
    Gauss.rpow_neg_one_le_etaT_of_scale_ge d hE ht1 hc hreg.2
  have hDelta : ∀ᶠ N : Nat in atTop,
      Gauss.flowDelta d E t N <= (N : Real)^(-(c / 6)) :=
    Gauss.flowDelta_le_rpow_neg d hreg.2
  have hEntry : Gauss.EntryBoundFlow' d E s t
      (fun N => 2 * (N : Real)^(-D)) :=
    Gauss.entryBoundFlow_floor d hE hs0 hst ht1 zero_le_one hEta
      (by linarith : (0 : Real) < c / 6) hDelta (by linarith)
  have hBlock : HighProb (P d) (blockEvent d E D s t tauG) := by
    change HighProb (P d) (fun N => {omega | forall u : TimeIcc s t N,
      APrimeJG.jG (sample d) E N (u : Real) omega
        ((band d).ell N (u : Real)) (etaT E (u : Real)) D <=
      1 + (N : Real)^tauG *
        (9 * Real.exp (Real.sqrt 3) * Step2.jS (sample d) E D N (u : Real) omega + 2)})
    exact APrimeJG.highProb_jG_le_of_entryBoundFlow d hE hs0 hst ht1
      hreg.1 D (by linarith) hEntry hGood htauG
  have hAll := (((hSource.inter hGood).inter hCentered).inter hBlock)
  change HighProb (Gauss.P d) (fun N =>
    Gauss.measCore (Gauss.P d)
      (rawCarrier d E D s t zetaSrc zetaCtr tauG N))
  exact Gauss.highProb_measCore hAll

theorem eventually_commonEvent_nonempty (d : Dims) {E D c : Real}
    {s t : Nat -> Real} (hE : |E| < 2) (hD : 60 <= D)
    (hs0 : forall N, 0 <= s N) (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    {zetaSrc zetaCtr tauG : Real}
    (hzetaSrc : 0 < zetaSrc) (hzetaCtr : 0 < zetaCtr) (htauG : 0 < tauG) :
    ∀ᶠ N : Nat in atTop,
      (commonEvent d E D s t zetaSrc zetaCtr tauG N).Nonempty := by
  exact (highProb_commonEvent d hE hD hs0 hst ht1 hc hreg hB
    zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG).nonempty (by simp)

/-- The raw, centered, good-flow, and block sources at one time and sample. -/
theorem pointwise_source_package (d : Dims)
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    {zetaSrc zetaCtr tauG : Real} {N : Nat} {omega : Ω d}
    (homega : omega ∈ commonEvent d E D s t zetaSrc zetaCtr tauG N)
    (u : TimeIcc s t N) (a1 a2 : ZMod (d.L N)) :
    let ellu := (band d).ell N (u : Real)
    let ells := (band d).ell N (s N)
    let etau := etaT E (u : Real)
    let ru := ellu / ells
    let L3 : ZMod (d.L N) -> Real := fun b =>
      norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
        (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
    (forall b, L3 b <=
      (N : Real)^zetaSrc * ru^2 *
        ((band d).scale E N (u : Real))⁻¹ ^ (2 : Nat)) /\
    norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      (4 * (N : Real)^zetaCtr * ru) * (ellu * etau)⁻¹ *
        ∑ b, L3 b /\
    (forall (x : ZMod (d.L N)) (p : ZMod (d.L N) × Fin (d.W N)),
      ∑ r, Lemma57.blkW (d.L N) (d.W N) r x *
        norm (green (Hflow d N (u : Real) omega) (zt E (u : Real)) r p) <=
          Gauss.flowDelta d E t N + (d.W N : Real)⁻¹) /\
    (forall (y : ZMod (d.L N)) (r : ZMod (d.L N) × Fin (d.W N)),
      ∑ p, Lemma57.blkW (d.L N) (d.W N) p y *
        norm (green (Hflow d N (u : Real) omega) (zt E (u : Real)) r p) <=
          Gauss.flowDelta d E t N + (d.W N : Real)⁻¹) := by
  dsimp only
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  have hCarrier := commonEvent_subset_rawCarrier d E D s t
    zetaSrc zetaCtr tauG N homega
  rcases hCarrier with ⟨⟨⟨hSource, hGood⟩, hCentered⟩, _hBlock⟩
  have hu0 : 0 <= (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hellu : 0 < (band d).ell N (u : Real) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((u : Real) : Complex) by linarith)
  have hells : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((s N : Real) : Complex) by linarith)
  have heta : 0 < etaT E (u : Real) := etaT_pos hE hu1
  have hW : 0 < (d.W N : Real) := by exact_mod_cast d.W_pos N
  let L3 : ZMod (d.L N) -> Real := fun b =>
    norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
  have hL3 : forall b, L3 b <=
      (N : Real)^zetaSrc *
        ((band d).ell N (u : Real) / (band d).ell N (s N))^2 *
        ((band d).scale E N (u : Real))⁻¹ ^ (2 : Nat) := by
    intro b
    let v : LoopData (d.L N) 3 := (![false, true, true], ![a2, b, a1])
    have hv := APrimeRawSourcesGeneralDims.rawThree_on_sourceGood d u hSource v
    have hidx : v.idx = (⟨[false, true, true], [a2, b, a1]⟩ :
        LoopIdx (ZMod (d.L N))) := by
      simp [v, LoopData.idx, List.ofFn_succ]
    rw [Gauss.sample_Lval, hidx] at hv
    simpa only [L3, APrimeRawSourcesGeneralDims.sourceC3, mul_assoc] using hv
  let csrc : Real := (N : Real)^zetaCtr *
    (2 * APrimeAllTimeOneLoopGeneralDims.qExt d E s t N (u : Real))
  have hone : forall sigma (b : ZMod (d.L N)),
      norm (Matrix.trace ((Gsig (Hflow d N (u : Real) omega) (zt E (u : Real)) sigma -
        mSigma E sigma • (1 : Matrix (d.Idx N) (d.Idx N) Complex)) *
          Eblk (d.L N) (d.W N) b)) <= csrc := by
    intro sigma b
    simpa only [APrimeCenteredModulusGeneralDims.centeredTrace, csrc] using
      hCentered (u, b) sigma
  have hbase := EGDef.norm_eGpm_le (d.three_le_L N)
    (Hflow_isHermitian d N (u : Real) omega) (mSigma E) hone a1 a2
  have hq : APrimeAllTimeOneLoopGeneralDims.qExt d E s t N (u : Real) =
      ((band d).ell N (u : Real) / (band d).ell N (s N)) /
        (band d).scale E N (u : Real) := by
    rw [APrimeAllTimeOneLoopGeneralDims.qExt_eq_q u.2]
    rfl
  have hcoef : 2 * (d.W N : Real) * csrc =
      (4 * (N : Real)^zetaCtr *
        ((band d).ell N (u : Real) / (band d).ell N (s N))) *
          ((band d).ell N (u : Real) * etaT E (u : Real))⁻¹ := by
    dsimp [csrc]
    rw [hq]
    change 2 * (d.W N : Real) *
      ((N : Real)^zetaCtr *
        (2 * (((band d).ell N (u : Real) / (band d).ell N (s N)) /
          ((d.W N : Real) * (band d).ell N (u : Real) *
            etaT E (u : Real))))) = _
    field_simp
    ring
  rw [hcoef] at hbase
  have hm : norm (mE E) = 1 := norm_mE hE.le
  have hGoodU : GoodEvent
      (green (Hflow d N (u : Real) omega) (zt E (u : Real)))
      (mE E) (Gauss.flowDelta d E t N) := hGood (u : Real) u.2
  refine ⟨hL3, ?_, ?_, ?_⟩
  · simpa only [L3, mul_assoc] using hbase
  · intro x p
    exact APrimeFirstCellEGFar.goodEvent_column_block_average hGoodU hm x p
  · intro y r
    exact APrimeFirstCellEGFar.goodEvent_row_block_average hGoodU hm y r

private theorem norm_gloop_three_le_gmBlk (d : Dims) (X : Sample (band d))
    (E : Real) (N : Nat) (u : Real) (omega : Ω d)
    (a1 a2 b : ZMod ((band d).L N)) :
    norm (gloop ((band d).L N) ((band d).W N) (X.H N u omega) (zt E u)
      ⟨[false, true, true], [a2, b, a1]⟩) <=
      APrimeJG.gmBlk X E N u omega a2 b *
        APrimeJG.gmBlk X E N u omega a1 b *
          APrimeJG.gmBlk X E N u omega a2 a1 := by
  letI : NeZero ((band d).L N) :=
    ⟨by have := (band d).three_le_L N; omega⟩
  letI : NeZero ((band d).W N) :=
    ⟨by have := (band d).W_pos N; omega⟩
  have h := Lemma57.norm_gloop_three_le (L := (band d).L N)
    (Wb := (band d).W N) (H := X.H N u omega) (z := zt E u)
    false true true a2 b a1 (APrimeJG.gmBlk_nonneg X E N u omega)
    (by
      intro p q hp hq
      rcases p with ⟨px, pi⟩
      rcases q with ⟨qy, qi⟩
      dsimp at hp hq ⊢
      subst px
      subst qy
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u omega false a1 a2 pi qi)
    (by
      intro q r hq hr
      rcases q with ⟨qx, qi⟩
      rcases r with ⟨ry, ri⟩
      dsimp at hq hr ⊢
      subst qx
      subst ry
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u omega true a2 b qi ri)
    (by
      intro r p hr hp
      rcases r with ⟨rx, ri⟩
      rcases p with ⟨py, pi⟩
      dsimp at hr hp ⊢
      subst rx
      subst py
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u omega true b a1 ri pi)
  rw [APrimeDriftNearTriple.gmBlk_comm X E N u omega b a1,
    APrimeDriftNearTriple.gmBlk_comm X E N u omega a1 a2] at h
  convert h using 1 <;> ring

private theorem two_loop_re_le_gsqBlk (d : Dims) (X : Sample (band d))
    (E : Real) (N : Nat) (u : Real) (omega : Ω d)
    (x y : ZMod ((band d).L N)) :
    (gloop ((band d).L N) ((band d).W N) (X.H N u omega) (zt E u)
      ⟨[true, false], [x, y]⟩).re <= APrimeJG.gsqBlk X E N u omega x y := by
  letI : NeZero ((band d).L N) :=
    ⟨by have := (band d).three_le_L N; omega⟩
  letI : NeZero ((band d).W N) :=
    ⟨by have := (band d).W_pos N; omega⟩
  let M : Real := APrimeJG.gmBlk X E N u omega x y
  have hM : 0 <= M := APrimeJG.gmBlk_nonneg X E N u omega x y
  have hterm (p q : ZMod ((band d).L N) × Fin ((band d).W N)) :
      Lemma57.blkW ((band d).L N) ((band d).W N) p y *
          (Lemma57.blkW ((band d).L N) ((band d).W N) q x *
            norm (green (X.H N u omega) (zt E u) p q) ^ 2) <=
      Lemma57.blkW ((band d).L N) ((band d).W N) p y *
          (Lemma57.blkW ((band d).L N) ((band d).W N) q x * M ^ 2) := by
    by_cases hp : p.1 = y
    · by_cases hq : q.1 = x
      · have hentry : norm (green (X.H N u omega) (zt E u) p q) <= M := by
          rcases p with ⟨px, pi⟩
          rcases q with ⟨qx, qi⟩
          dsimp at hp hq ⊢
          subst px
          subst qx
          have h := APrimeJG.norm_Gsig_le_gmBlk X E N u omega true y x pi qi
          rw [Gsig_true] at h
          rw [APrimeDriftNearTriple.gmBlk_comm X E N u omega y x] at h
          exact h
        have hsq : norm (green (X.H N u omega) (zt E u) p q) ^ 2 <= M ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hentry 2
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq
            (Lemma57.blkW_nonneg ((band d).L N) ((band d).W N) q x))
          (Lemma57.blkW_nonneg ((band d).L N) ((band d).W N) p y)
      · simp only [Lemma57.blkW, if_neg hq, zero_mul, mul_zero]
        exact le_rfl
    · simp only [Lemma57.blkW, if_neg hp, zero_mul]
      exact le_rfl
  calc
    (gloop ((band d).L N) ((band d).W N) (X.H N u omega) (zt E u)
        ⟨[true, false], [x, y]⟩).re =
        ∑ p : ZMod ((band d).L N) × Fin ((band d).W N),
          ∑ q : ZMod ((band d).L N) × Fin ((band d).W N),
            Lemma57.blkW ((band d).L N) ((band d).W N) p y *
              (Lemma57.blkW ((band d).L N) ((band d).W N) q x *
                norm (green (X.H N u omega) (zt E u) p q) ^ 2) :=
      (Lemma57.sum_blkW_normSq ((band d).L N) ((band d).W N)
        (X.hermitian N u omega) x y).symm
    _ <= ∑ p : ZMod ((band d).L N) × Fin ((band d).W N),
          ∑ q : ZMod ((band d).L N) × Fin ((band d).W N),
            Lemma57.blkW ((band d).L N) ((band d).W N) p y *
              (Lemma57.blkW ((band d).L N) ((band d).W N) q x * M ^ 2) := by
      exact Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = M ^ 2 := by
      have hinner (p : ZMod ((band d).L N) × Fin ((band d).W N)) :
          (∑ q : ZMod ((band d).L N) × Fin ((band d).W N),
              Lemma57.blkW ((band d).L N) ((band d).W N) p y *
                (Lemma57.blkW ((band d).L N) ((band d).W N) q x * M ^ 2)) =
            Lemma57.blkW ((band d).L N) ((band d).W N) p y * M ^ 2 := by
        rw [← Finset.mul_sum, ← Finset.sum_mul,
          Lemma57.sum_blkW, one_mul]
      simp_rw [hinner, ← Finset.sum_mul, Lemma57.sum_blkW, one_mul]
    _ <= APrimeJG.gsqBlk X E N u omega x y := by
      have hcomm : M = APrimeJG.gmBlk X E N u omega y x :=
        APrimeDriftNearTriple.gmBlk_comm X E N u omega x y
      rw [show M ^ 2 = APrimeJG.gmBlk X E N u omega x y *
        APrimeJG.gmBlk X E N u omega y x from by
          change M ^ 2 = M * APrimeJG.gmBlk X E N u omega y x
          rw [← hcomm]
          ring]
      exact APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u omega x y

/-- The far branch of (5.35), at one time and one actual Gaussian sample. -/
theorem pointwise_far_source_bound (d : Dims)
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    {zetaSrc zetaCtr tauG : Real} {N : Nat} {omega : Ω d}
    (homega : omega ∈ commonEvent d E D s t zetaSrc zetaCtr tauG N)
    (u : TimeIcc s t N) (a1 a2 : ZMod (d.L N))
    (hfar : ellStar (d.W N : Real) ((band d).ell N (u : Real)) <=
      (zdist (d.L N) (a2 - a1) : Real)) :
    let ellu := (band d).ell N (u : Real)
    let ells := (band d).ell N (s N)
    let etau := etaT E (u : Real)
    let ru := ellu / ells
    let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
    let kappa1 := 4 * (N : Real)^zetaCtr * ru
    let kappa2 := Gauss.flowDelta d E t N + (d.W N : Real)⁻¹
    norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      etau⁻¹ * kappa1 *
        (Lemma57.cFar (d.W N : Real) ellu * J * kappa2 +
          J * Real.sqrt J *
            (168 * ((d.W N : Real) * ellu * etau)⁻¹ +
              (d.L N : Real) * Real.sqrt ((d.W N : Real)^(-D)) / ellu)) *
        tailT (d.W N : Real) ellu etau D
          (zdist (d.L N) (a2 - a1)) := by
  dsimp only
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  letI : NeZero (d.W N) := ⟨by have := d.W_pos N; omega⟩
  have hu0 : 0 <= (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hW : 1 <= (d.W N : Real) := by exact_mod_cast (band d).one_le_W N
  have hWpos : 0 < (d.W N : Real) := by linarith
  have hellu : 1 <= (band d).ell N (u : Real) :=
    one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
  have hells : 0 < (band d).ell N (s N) := by
    have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((s N : Real) : Complex) by linarith)
  have heta : 0 < etaT E (u : Real) := etaT_pos hE hu1
  let ellu := (band d).ell N (u : Real)
  let etau := etaT E (u : Real)
  let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
  let kappa1 := 4 * (N : Real)^zetaCtr * (ellu / (band d).ell N (s N))
  let kappa2 := Gauss.flowDelta d E t N + (d.W N : Real)⁻¹
  let Gm := APrimeJG.gmBlk (sample d) E N (u : Real) omega
  let L2 : ZMod (d.L N) -> ZMod (d.L N) -> Real := fun x y =>
    (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[true, false], [x, y]⟩).re
  let L3 : ZMod (d.L N) -> Real := fun b =>
    norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
  have hsrc := pointwise_source_package d hE hs0 hst ht1 homega u a1 a2
  dsimp only at hsrc
  rcases hsrc with ⟨_hL3, hEG, hC, hR⟩
  have hJ : 1 <= J := APrimeJG.one_le_jG
    (sample d) E N (u : Real) omega hWpos
  have hJ0 : 0 <= J := by linarith
  have hkappa1 : 0 <= kappa1 := by
    dsimp [kappa1, ellu]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (div_nonneg (by linarith) hells.le)
  have hkappa2 : 0 <= kappa2 := by
    dsimp [kappa2, Gauss.flowDelta]
    exact add_nonneg
      (Real.rpow_nonneg (inv_nonneg.mpr
        ((band d).scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)).le) _)
      (inv_nonneg.mpr hWpos.le)
  have hGm : forall x y, 0 <= Gm x y :=
    APrimeJG.gmBlk_nonneg (sample d) E N (u : Real) omega
  have h531 : forall x y : ZMod (d.L N),
      ellStar (d.W N : Real) ellu / 2 <= (zdist (d.L N) (x - y) : Real) ->
      L2 x y <= J * tailT (d.W N : Real) ellu etau D
        (zdist (d.L N) (x - y)) := by
    intro x y hxy
    exact (two_loop_re_le_gsqBlk d (sample d) E N (u : Real) omega x y).trans
      (APrimeJG.gsqBlk_le_jG_mul_tailT
        (sample d) E N (u : Real) omega hWpos x y hxy)
  have h42 : forall x y : ZMod (d.L N),
      ellStar (d.W N : Real) ellu / 2 <= (zdist (d.L N) (x - y) : Real) ->
      Gm x y <= Real.sqrt J * Real.sqrt
        (tailT (d.W N : Real) ellu etau D (zdist (d.L N) (x - y))) := by
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
    exact norm_gloop_three_le_gmBlk d (sample d) E N (u : Real) omega a1 a2 b
  have hEG' : norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      kappa1 * (ellu * etau)⁻¹ * ∑ b, L3 b := by
    simpa only [kappa1, ellu, etau, L3, mul_assoc] using hEG
  exact Lemma57.eG_far_le (d.L N) hW (by simpa only [ellu] using hellu)
    (by simpa only [etau] using heta) hJ hfar hkappa1 hkappa2 hGm
      h531 h42 h558a h558b h560 hEG'

/-- The near branch of (5.35), retaining the exact far-internal-label leakage. -/
theorem pointwise_near_source_bound (d : Dims)
    {E D : Real} {s t : Nat -> Real}
    (hE : |E| < 2) (hs0 : forall N, 0 <= s N)
    (hst : forall N, s N <= t N) (ht1 : forall N, t N < 1)
    {zetaSrc zetaCtr tauG : Real} {N : Nat} (hN : 0 < N)
    {omega : Ω d}
    (homega : omega ∈ commonEvent d E D s t zetaSrc zetaCtr tauG N)
    (u : TimeIcc s t N) (hlog : 4 <= Real.log (d.W N : Real))
    (a1 a2 : ZMod (d.L N))
    (hnear : (zdist (d.L N) (a2 - a1) : Real) <=
      ellStar (d.W N : Real) ((band d).ell N (u : Real))) :
    let ellu := (band d).ell N (u : Real)
    let ells := (band d).ell N (s N)
    let etau := etaT E (u : Real)
    let ru := ellu / ells
    let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
    norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      4 * (N : Real)^(zetaCtr + zetaSrc) * etau⁻¹ * ru^3 *
          Lemma57.cNear (d.W N : Real) ellu *
            tailT (d.W N : Real) ellu etau D (zdist (d.L N) (a2 - a1)) +
        (4 * (N : Real)^zetaCtr * ru) * (ellu * etau)⁻¹ *
          (d.L N : Real) *
          (etau⁻¹ * J * tailT (d.W N : Real) ellu etau D
            (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)) := by
  dsimp only
  letI : NeZero (d.L N) := ⟨by have := d.three_le_L N; omega⟩
  have hu0 : 0 <= (u : Real) := (hs0 N).trans u.2.1
  have hu1 : (u : Real) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hW : 1 <= (d.W N : Real) := by exact_mod_cast (band d).one_le_W N
  have hellu : 1 <= (band d).ell N (u : Real) :=
    one_le_ellHat ((band d).L N) ((band d).three_le_L N) hu0 hu1
  have hells : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using
      (show 0 < ellHat ((band d).L N) ((s N : Real) : Complex) by linarith)
  have heta : 0 < etaT E (u : Real) := etaT_pos hE hu1
  have hNr : 0 < (N : Real) := by exact_mod_cast hN
  let ellu := (band d).ell N (u : Real)
  let etau := etaT E (u : Real)
  let ru := ellu / (band d).ell N (s N)
  let J := APrimeJG.jG (sample d) E N (u : Real) omega ellu etau D
  let L3 : ZMod (d.L N) -> Real := fun b =>
    norm (gloop (d.L N) (d.W N) (Hflow d N (u : Real) omega)
      (zt E (u : Real)) ⟨[false, true, true], [a2, b, a1]⟩)
  have hsrc := pointwise_source_package d hE hs0 hst ht1 homega u a1 a2
  dsimp only at hsrc
  rcases hsrc with ⟨hL3src, hEGsrc, _hC, _hR⟩
  have hL3 : forall b, L3 b <=
      1 * (N : Real)^zetaSrc * ru^2 *
        (((band d).W N * ellu * etau)^2)⁻¹ := by
    intro b
    have hb := hL3src b
    simpa only [one_mul, L3, ru, ellu, etau, Band.scale, inv_pow, mul_assoc] using hb
  have hEG : norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
      (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      (2 * (2 : Real) * (N : Real)^zetaCtr * ru) *
        (ellu * etau)⁻¹ * ∑ b, L3 b := by
    change norm (EGDef.eGpm (d.L N) (d.W N) (mSigma E)
        (Hflow d N (u : Real) omega) (zt E (u : Real)) a1 a2) <=
      (4 * (N : Real)^zetaCtr * ru) * (ellu * etau)⁻¹ * ∑ b, L3 b at hEGsrc
    convert hEGsrc using 1 <;> ring
  have hJ : 1 <= J := APrimeJG.one_le_jG
    (sample d) E N (u : Real) omega (by exact_mod_cast d.W_pos N)
  let rho := etau⁻¹ * J * tailT (d.W N : Real) ellu etau D
    (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu)
  have hrho : 0 <= rho := by
    dsimp [rho]
    have htail : 0 <= tailT (d.W N : Real) ellu etau D
        (APrimeDriftNearAbsorb.gap (d.W N : Real) ellu) :=
      tailT_nonneg (by positivity) _
    positivity
  have h554 : forall b,
      Lemma57.ellStarStar (d.W N : Real) ellu <
        (zdist (d.L N) (a2 - b) : Real) -> L3 b <= rho := by
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

/-- One actual resident exists on the common event in a positive first time
cell; the same cell includes its zero-time endpoint. -/
theorem positive_length_exampleGrow_resident :
    ∃ τ' : Real, 0 < τ' ∧ ∃ c : Real, 0 < c ∧
      ∃ s t : Nat -> Real,
        (forall N, s N = 0) ∧ (forall N, 0 <= s N) ∧
        (forall N, s N <= t N) ∧ (forall N, t N < 1) ∧
        Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
        BoundsCore (sample Dims.exampleGrow) 0 s ∧
        Step1.Hyp (sample Dims.exampleGrow) 0 s t ∧
        (∀ᶠ N : Nat in atTop, s N < t N) ∧
        forall zetaSrc zetaCtr tauG : Real,
          0 < zetaSrc -> 0 < zetaCtr -> 0 < tauG ->
          ∀ᶠ N : Nat in atTop,
            exists omega : Ω Dims.exampleGrow,
              omega ∈ commonEvent Dims.exampleGrow 0 60 s t
                zetaSrc zetaCtr tauG N ∧
              exists u : TimeIcc s t N,
                (u : Real) = 0 ∧ s N < t N ∧ 0 < N := by
  rcases APrimeAllTimeOneLoopGeneralDims.positive_length_exampleGrow_witness with
    ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpositive, _hmeas, _hhigh, _hnonempty, _hmod, _htwo⟩
  refine ⟨tauPrime, htauPrime, c, hc, s, t, hsEq, hs0, hst, ht1,
    hreg, hB, hStep, hpositive, ?_⟩
  intro zetaSrc zetaCtr tauG hzetaSrc hzetaCtr htauG
  have hresident := eventually_commonEvent_nonempty Dims.exampleGrow
    (E := 0) (D := 60) (c := c) (s := s) (t := t)
    (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
    hzetaSrc hzetaCtr htauG
  filter_upwards [hresident, hpositive, eventually_ge_atTop 1]
    with N hmem hlen hN
  obtain ⟨omega, homega⟩ := hmem
  let u : TimeIcc s t N := ⟨s N, ⟨le_rfl, hst N⟩⟩
  have hu0 : (u : Real) = 0 := by simp [u, hsEq N]
  have hNpos : 0 < N := by omega
  exact ⟨omega, homega, u, hu0, hlen, hNpos⟩

#print axioms measurableSet_commonEvent
#print axioms highProb_commonEvent
#print axioms eventually_commonEvent_nonempty
#print axioms pointwise_source_package
#print axioms pointwise_far_source_bound
#print axioms pointwise_near_source_bound
#print axioms positive_length_exampleGrow_resident

end
end RBM.APrimeGeneralMovingDriftSourceGeneralDims
