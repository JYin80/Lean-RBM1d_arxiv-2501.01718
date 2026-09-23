/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingPrefixSupport
import RBM1D.Gauss.APrimeFullQV
import RBM1D.Gauss.APrimeFirstCellNearSources

/-!
# T491: raw Step-1 sources on a general moving window

The length-three, length-four, and length-six laws are placed on one
measurable high-probability event together with the fixed Gaussian norm
event.  The length-four and length-six bounds are then converted to the
actual pointwise quadratic-variation source event.
-/

namespace RBM.APrimeGeneralMovingRawSources

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

noncomputable def sourceEll (s : ℕ → ℝ) (ζ : ℝ) (N : ℕ) : ℝ :=
  B.ell N (s N) * (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ))

noncomputable def sourceC3 (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N)) ^ (2 : ℕ) *
    (B.scale E N u)⁻¹ ^ (2 : ℕ)

noncomputable def sourceC4 (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N)) ^ (3 : ℕ) *
    (B.scale E N u)⁻¹ ^ (3 : ℕ)

noncomputable def sourceC6 (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N)) ^ (5 : ℕ) *
    (B.scale E N u)⁻¹ ^ (5 : ℕ)

def rawEvent (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (n N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc s t N × LoopData (d.L N) n,
    ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ * Step1.aprioriRhs B E s t n N p ω}

def sourceGood (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (N : ℕ) : Set (Ω d) :=
  APrimeGeneralMovingGoodMesh.good N ∩
    rawEvent E s t ζ 3 N ∩
    rawEvent E s t ζ 4 N ∩
    rawEvent E s t ζ 6 N

theorem sourceGood_subset_good (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ) (N : ℕ) :
    sourceGood E s t ζ N ⊆ APrimeGeneralMovingGoodMesh.good N :=
  fun _ hω => hω.1.1.1

private theorem rawEvent_isClosed {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    (ζ : ℝ) (n N : ℕ) : IsClosed (rawEvent E s t ζ n N) := by
  have heq : rawEvent E s t ζ n N =
      ⋂ p : TimeIcc s t N × LoopData (d.L N) n,
        {ω : Ω d |
          ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ * Step1.aprioriRhs B E s t n N p ω} := by
    ext ω
    simp [rawEvent]
  rw [heq]
  apply isClosed_iInter
  intro p
  have hu : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hcont : Continuous (fun ω : Ω d =>
      ‖(sample d).Lval E N p.1 ω p.2.idx‖) := by
    simpa only [sample_Lval] using
      (continuous_gloop_Hflow d N (p.1 : ℝ)
        (zt_im_ne_zero_of_lt_one hE hu) p.2.idx).norm
  exact isClosed_le hcont (by dsimp [Step1.aprioriRhs]; fun_prop)

theorem measurableSet_sourceGood {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    (ζ : ℝ) (N : ℕ) : MeasurableSet (sourceGood E s t ζ N) := by
  exact (((APrimeGeneralMovingGoodMesh.measurableSet_good N).inter
    (rawEvent_isClosed hE ht1 ζ 3 N).measurableSet).inter
    (rawEvent_isClosed hE ht1 ζ 4 N).measurableSet).inter
    (rawEvent_isClosed hE ht1 ζ 6 N).measurableSet

private theorem source_level_identity {ellu ells A q : ℝ}
    (hells : 0 < ells) (hA : 0 < A) (hq : 0 < q) :
    2 * (q * (ellu / ells) ^ 5 * (A⁻¹) ^ 5) =
      (ellu / (ells * (2 * q) ^ (-(1 / 5 : ℝ)))) ^ 5 *
        (((A ^ 2)⁻¹) ^ 2) * A⁻¹ := by
  have hb : 0 < 2 * q := by positivity
  have hr : ((2 * q) ^ (-(1 / 5 : ℝ))) ^ 5 = (2 * q)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hb.le]
    norm_num [Real.rpow_neg_one]
  simp only [div_pow, mul_pow, hr]
  field_simp

theorem sourceEvent_on_sourceGood {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {ζ : ℝ} (_hζ : 0 < ζ) {N : ℕ} (hN : 0 < N)
    (u : TimeIcc s t N) {ω : Ω d} (hω : ω ∈ sourceGood E s t ζ N) :
    APrimeFullQV.SourceEvent (sample d) E N (u : ℝ) ω
      (sourceEll s ζ N) (sourceC4 E s ζ N u) := by
  have h4 : ∀ p : LoopData (d.L N) 4,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC4 E s ζ N u := by
    intro p
    have hp := hω.1.2 (u, p)
    simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC4, mul_assoc] using hp
  have h6 : ∀ p : LoopData (d.L N) 6,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC6 E s ζ N u := by
    intro p
    have hp := hω.2 (u, p)
    simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC6, mul_assoc] using hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) ^ ζ := Real.rpow_pos_of_pos hNr _
  have hs1 : s N < 1 := u.2.1.trans_lt (u.2.2.trans_lt (ht1 N))
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hells : 0 < B.ell N (s N) := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) (s N : ℂ) by linarith)
  have hA : 0 < B.scale E N u := B.scale_pos' hE N (hs0 N |>.trans u.2.1) hu1
  have hlevel : 2 * sourceC6 E s ζ N u ≤
      (B.ell N u / sourceEll s ζ N) ^ 5 *
        ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹) ^ 2 *
        ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ := by
    unfold sourceC6 sourceEll
    exact le_of_eq (by simpa only [Band.scale] using
      (source_level_identity (ellu := B.ell N u) (ells := B.ell N (s N))
        (A := B.scale E N u) (q := (N : ℝ) ^ ζ) hells hA hq))
  exact APrimeFullQV.sourceEvent_of_step1 (sample d) E N (u : ℝ) ω h4 h6 hlevel

theorem rawThree_on_sourceGood {E : ℝ} {s t : ℕ → ℝ}
    {ζ : ℝ} {N : ℕ} (u : TimeIcc s t N)
    {ω : Ω d} (hω : ω ∈ sourceGood E s t ζ N) :
    ∀ p : LoopData (d.L N) 3,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC3 E s ζ N u := by
  intro p
  have hp := hω.1.1.2 (u, p)
  simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC3, mul_assoc] using hp

theorem highProb_sourceGood {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t)
    {ζ : ℝ} (hζ : 0 < ζ) :
    HighProb (P d) (sourceGood E s t ζ) := by
  let κ : ℝ := (2 - |E|) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hEκ : |E| ≤ 2 - κ := by dsimp [κ]; linarith
  have h3 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1 hreg.1 hc hreg.2
    hStep 3 (by norm_num)
  have h4 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1 hreg.1 hc hreg.2
    hStep 4 (by norm_num)
  have h6 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1 hreg.1 hc hreg.2
    hStep 6 (by norm_num)
  have hp3 : HighProb (P d) (rawEvent E s t ζ 3) := h3.highProb hζ
  have hp4 : HighProb (P d) (rawEvent E s t ζ 4) := h4.highProb hζ
  have hp6 : HighProb (P d) (rawEvent E s t ζ 6) := h6.highProb hζ
  exact (((APrimeGeneralMovingGoodMesh.highProb_good.inter hp3).inter hp4).inter hp6)

theorem general_moving_raw_sources {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (sourceGood E s t ζ) ∧
      (∀ N, MeasurableSet (sourceGood E s t ζ N)) ∧
      (∀ N, sourceGood E s t ζ N ⊆ APrimeGeneralMovingGoodMesh.good N) ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ sourceGood E s t ζ N,
        ∀ u : TimeIcc s t N,
          APrimeFullQV.SourceEvent (sample d) E N (u : ℝ) ω
            (sourceEll s ζ N) (sourceC4 E s ζ N u) ∧
          (∀ p : LoopData (d.L N) 3,
            ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC3 E s ζ N u) := by
  intro ζ hζ
  refine ⟨highProb_sourceGood hE hs0 hst ht1 hc hreg hB hStep hζ,
    measurableSet_sourceGood hE ht1 ζ,
    sourceGood_subset_good E s t ζ, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN ω hω u
  exact ⟨sourceEvent_on_sourceGood hE hs0 ht1 hζ (by omega) u hω,
    rawThree_on_sourceGood u hω⟩

/-- The all-time statement includes the empty-prefix source time `u₀=s_N`. -/
theorem eventually_source_at_kZero {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ sourceGood E s t ζ N,
      APrimeFullQV.SourceEvent (sample d) E N (s N) ω
        (sourceEll s ζ N) (sourceC4 E s ζ N (s N)) ∧
      (∀ p : LoopData (d.L N) 3,
        ‖(sample d).Lval E N (s N) ω p.idx‖ ≤ sourceC3 E s ζ N (s N)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN ω hω
  let u : TimeIcc s t N := ⟨s N, le_rfl, hst N⟩
  exact ⟨sourceEvent_on_sourceGood hE hs0 ht1 hζ (by omega) u hω,
    rawThree_on_sourceGood u hω⟩

private theorem eventually_firstCellT_half {τ' : ℝ} (hτ' : 0 < τ') :
    ∀ᶠ N : ℕ in atTop, firstCellT τ' N = 1 / 2 := by
  have hWt : Tendsto (fun N : ℕ => ((d.W N : ℝ)) ^ (-τ'))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W B)
  filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with N hW
  change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1 = 1 / 2
  apply gridT_of_le
  rw [gridS]
  norm_num
  change (Dims.growW N : ℝ) ^ (-τ') < 1 / 2 at hW
  linarith

private theorem eventually_firstCell_kOne_widenedW_one
    {τ' δ : ℝ} (hτ' : 0 < τ') (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      firstCellS τ' N < firstCellT τ' N ∧
      1 ≤ cutNetTop (firstCellS τ') (firstCellT τ')
        (APrimeGeneralMovingMesh.targetMesh 60) N ∧
      ∀ ω : Ω d, ∀ p : ℕ,
        APrimeWeight.widenedW
          (APrimeWeight.canonicalR (firstCellS τ') (firstCellT τ')
            (APrimeGeneralMovingMesh.targetMesh 60)) 1
          (APrimeGeneralMovingDetFields.J 0 60 (firstCellS τ'))
          (firstCellS τ') (firstCellT τ')
          (APrimeGeneralMovingMesh.targetMesh 60) δ p N 1 ω = 1 := by
  filter_upwards [eventually_firstCellT_half hτ', eventually_ge_atTop 2]
    with N ht hN
  let s := firstCellS τ'
  let t := firstCellT τ'
  let mesh := APrimeGeneralMovingMesh.targetMesh 60
  let J := APrimeGeneralMovingDetFields.J 0 60 s
  have hs : s N = 0 := by
    change gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hactive : 1 ≤ cutNetTop s t mesh N := by
    unfold cutNetTop mesh APrimeGeneralMovingMesh.targetMesh
    rw [hs, show t N = 1 / 2 by exact ht,
      APrimeGeneralMovingMesh.polynomialMesh_eq_of_pos (by omega)]
    apply Nat.le_floor
    norm_num
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hNone : (1 : ℝ) ≤ N := by linarith
    have hpow : (2 : ℝ) ≤ (N : ℝ) ^
        (2 * (2 * (60 : ℝ) + 7) + 4) := by
      calc
        (2 : ℝ) ≤ N := hNr
        _ = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (2 * (2 * (60 : ℝ) + 7) + 4) :=
          Real.rpow_le_rpow_of_exponent_le hNone (by norm_num)
    norm_num at hpow
    calc
      (1 : ℝ) = (1 / 2) * 2 := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hsfun : s = fun _ => (0 : ℝ) := by
    funext M
    change gridT ((B.W M : ℝ)) τ' (1 / 2 : ℝ) 0 = 0
    exact gridT_zero (by norm_num)
  have hpref : ∀ ω : Ω d,
      ω ∈ prefNet J s mesh (fun M _ => (M : ℝ) ^ (2 * δ) * 1) N 1 := by
    intro ω j hj
    have hj0 : j = 0 := by
      simpa only [Finset.mem_range, Nat.lt_one_iff] using hj
    subst j
    have hJzero : J N (cutNetPt s mesh N 0) ω = 1 := by
      simp only [cutNetPt_zero]
      rw [hs]
      dsimp [J, APrimeGeneralMovingDetFields.J]
      rw [hsfun]
      exact APrimeFirstCellCommon.J_zero N ω
    rw [hJzero]
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hpow : 1 ≤ (N : ℝ) ^ (2 * δ) :=
      Real.one_le_rpow hNreal (by linarith)
    simpa using hpow
  refine ⟨?_, hactive, ?_⟩
  · change s N < t N
    rw [hs, show t N = 1 / 2 by exact ht]
    norm_num
  · intro ω p
    have hpieceLower : 1 ≤ APrimeWeight.piecewiseW
        (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ N 1 ω :=
      APrimeWeight.piecewiseW_dom_canonical
        (APrimeGeneralMovingDetFields.J_nonneg 0 60 s) δ N 1 ω (hpref ω)
    have hpieceUpper := APrimeWeight.piecewiseW_le_one
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ N 1 ω
    have hpiece : APrimeWeight.piecewiseW
        (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ N 1 ω = 1 :=
      le_antisymm hpieceUpper hpieceLower
    have hlower := APrimeWeight.piecewiseW_le_widenedW
      (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
      (J := J) (s := s) (t := t) (mesh := mesh)
      (by norm_num) δ p N 1 ω
    have hupper := APrimeWeight.widenedW_le_one
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N 1 ω
    rw [hpiece] at hlower
    exact le_antisymm hupper hlower

/-- A positive first cell contains one sample on the same raw-source event
and positive `k=1` widened support.  The source holds at every running time,
including `k=0`. -/
theorem positive_length_same_source_support_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ δ : ℝ, 0 < ζ → 0 < δ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Ω d,
        ω ∈ sourceGood 0 (firstCellS τ') (firstCellT τ') ζ N ∧
        MeasurableSet (sourceGood 0 (firstCellS τ') (firstCellT τ') ζ N) ∧
        firstCellS τ' N < firstCellT τ' N ∧
        1 ≤ cutNetTop (firstCellS τ') (firstCellT τ')
          (APrimeGeneralMovingMesh.targetMesh 60) N ∧
        (∀ p : ℕ,
          APrimeWeight.widenedW
            (APrimeWeight.canonicalR (firstCellS τ') (firstCellT τ')
              (APrimeGeneralMovingMesh.targetMesh 60)) 1
            (APrimeGeneralMovingDetFields.J 0 60 (firstCellS τ'))
            (firstCellS τ') (firstCellT τ')
            (APrimeGeneralMovingMesh.targetMesh 60) δ p N 1 ω = 1) ∧
        (∀ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
          APrimeFullQV.SourceEvent (sample d) 0 N (u : ℝ) ω
            (sourceEll (firstCellS τ') ζ N)
            (sourceC4 0 (firstCellS τ') ζ N u) ∧
          (∀ p : LoopData (d.L N) 3,
            ‖(sample d).Lval 0 N (u : ℝ) ω p.idx‖ ≤
              sourceC3 0 (firstCellS τ') ζ N u)) := by
  obtain ⟨τ', hτ', _hll, h3, h4, h6⟩ :=
    APrimeFirstCellNearSources.firstCell_raw346_localLaw_same_parameter
  refine ⟨τ', hτ', ?_⟩
  intro ζ δ hζ hδ
  have hp3 : HighProb (P d)
      (rawEvent 0 (firstCellS τ') (firstCellT τ') ζ 3) := by
    exact h3.highProb hζ
  have hp4 : HighProb (P d)
      (rawEvent 0 (firstCellS τ') (firstCellT τ') ζ 4) := by
    exact h4.highProb hζ
  have hp6 : HighProb (P d)
      (rawEvent 0 (firstCellS τ') (firstCellT τ') ζ 6) := by
    exact h6.highProb hζ
  have hp : HighProb (P d)
      (sourceGood 0 (firstCellS τ') (firstCellT τ') ζ) :=
    (((APrimeGeneralMovingGoodMesh.highProb_good.inter hp3).inter hp4).inter hp6)
  have hne := HighProb.nonempty (by simp) hp
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    rw [firstCellS_eq_zero]
  have ht1 : ∀ N, firstCellT τ' N < 1 := fun N =>
    (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  filter_upwards [hne, eventually_firstCell_kOne_widenedW_one hτ' hδ,
    eventually_ge_atTop 1] with N hneN hsupport hN
  obtain ⟨ω, hω⟩ := hneN
  refine ⟨ω, hω, measurableSet_sourceGood (by norm_num) ht1 ζ N,
    hsupport.1, hsupport.2.1, hsupport.2.2 ω, ?_⟩
  intro u
  exact ⟨sourceEvent_on_sourceGood (by norm_num) hs0 ht1 hζ (by omega) u hω,
    rawThree_on_sourceGood u hω⟩

#print axioms sourceGood_subset_good
#print axioms measurableSet_sourceGood
#print axioms sourceEvent_on_sourceGood
#print axioms rawThree_on_sourceGood
#print axioms highProb_sourceGood
#print axioms general_moving_raw_sources
#print axioms eventually_source_at_kZero
#print axioms positive_length_same_source_support_witness

end
end RBM.APrimeGeneralMovingRawSources
