/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingRawSources
import RBM1D.Gauss.APrimeFullQV
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.Step1Hyp

/-!
# T1367: the Gaussian raw-source carrier for arbitrary dimensions

The event below puts the Gaussian norm bound and the order-three, order-four,
and order-six moving-window Step-1 estimates on one sample.  The length-four
and length-six bounds give the actual quadratic-variation `SourceEvent`.
-/

namespace RBM.APrimeRawSourcesGeneralDims

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The Gaussian norm-good event in dimension `d`. -/
def normGood (d : Dims) (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- The order-`n` moving-window raw Step-1 estimate, in dimension `d`. -/
def rawEvent (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (n N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc s t N × LoopData (d.L N) n,
    ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ * Step1.aprioriRhs (band d) E s t n N p ω}

/-- The shared Gaussian carrier for the norm bound and raw orders 3, 4, 6. -/
def sourceGood (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (ζ : ℝ)
    (N : ℕ) : Set (Ω d) :=
  normGood d N ∩ rawEvent d E s t ζ 3 N ∩
    rawEvent d E s t ζ 4 N ∩ rawEvent d E s t ζ 6 N

/-- Source scale from the band at the initial time. -/
noncomputable def sourceEll (d : Dims) (s : ℕ → ℝ) (ζ : ℝ) (N : ℕ) : ℝ :=
  (band d).ell N (s N) * (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ))

/-- The raw order-three source coefficient. -/
noncomputable def sourceC3 (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * ((band d).ell N u / (band d).ell N (s N)) ^ (2 : ℕ) *
    ((band d).scale E N u)⁻¹ ^ (2 : ℕ)

/-- The raw order-four source coefficient. -/
noncomputable def sourceC4 (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * ((band d).ell N u / (band d).ell N (s N)) ^ (3 : ℕ) *
    ((band d).scale E N u)⁻¹ ^ (3 : ℕ)

/-- The raw order-six source coefficient. -/
noncomputable def sourceC6 (d : Dims) (E : ℝ) (s : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * ((band d).ell N u / (band d).ell N (s N)) ^ (5 : ℕ) *
    ((band d).scale E N u)⁻¹ ^ (5 : ℕ)

theorem sourceGood_subset_normGood (d : Dims) (E : ℝ) (s t : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) :
    sourceGood d E s t ζ N ⊆ normGood d N :=
  fun _ hω => hω.1.1.1

theorem sourceGood_subset_normX (d : Dims) (E : ℝ) (s t : ℕ → ℝ)
    (ζ : ℝ) (N : ℕ) :
    sourceGood d E s t ζ N ⊆ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)} :=
  sourceGood_subset_normGood d E s t ζ N

private theorem rawEvent_isClosed (d : Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    (ζ : ℝ) (n N : ℕ) : IsClosed (rawEvent d E s t ζ n N) := by
  have heq : rawEvent d E s t ζ n N =
      ⋂ p : TimeIcc s t N × LoopData (d.L N) n,
        {ω : Ω d |
          ‖(sample d).Lval E N p.1 ω p.2.idx‖ ≤
            (N : ℝ) ^ ζ * Step1.aprioriRhs (band d) E s t n N p ω} := by
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

theorem measurableSet_normGood (d : Dims) (N : ℕ) :
    MeasurableSet (normGood d N) :=
  Gauss.measurableSet_normX_le d N

theorem measurableSet_sourceGood (d : Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1)
    (ζ : ℝ) (N : ℕ) : MeasurableSet (sourceGood d E s t ζ N) := by
  exact (((Gauss.measurableSet_normX_le d N).inter
    (rawEvent_isClosed d hE ht1 ζ 3 N).measurableSet).inter
    (rawEvent_isClosed d hE ht1 ζ 4 N).measurableSet).inter
    (rawEvent_isClosed d hE ht1 ζ 6 N).measurableSet

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

theorem sourceEvent_on_sourceGood (d : Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {ζ : ℝ} (_hζ : 0 < ζ) {N : ℕ} (hN : 0 < N)
    (u : TimeIcc s t N) {ω : Ω d}
    (hω : ω ∈ sourceGood d E s t ζ N) :
    APrimeFullQV.SourceEvent (sample d) E N (u : ℝ) ω
      (sourceEll d s ζ N) (sourceC4 d E s ζ N u) := by
  have h4 : ∀ p : LoopData (d.L N) 4,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC4 d E s ζ N u := by
    intro p
    have hp := hω.1.2 (u, p)
    simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC4, mul_assoc] using hp
  have h6 : ∀ p : LoopData (d.L N) 6,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC6 d E s ζ N u := by
    intro p
    have hp := hω.2 (u, p)
    simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC6, mul_assoc] using hp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : 0 < (N : ℝ) ^ ζ := Real.rpow_pos_of_pos hNr _
  have hs1 : s N < 1 := u.2.1.trans_lt (u.2.2.trans_lt (ht1 N))
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hells : 0 < (band d).ell N (s N) := by
    have h := one_le_ellHat ((band d).L N) ((band d).three_le_L N)
      (hs0 N) hs1
    simpa only [Band.ell] using (show 0 < ellHat ((band d).L N) (s N : ℂ) by linarith)
  have hA : 0 < (band d).scale E N (u : ℝ) :=
    (band d).scale_pos' hE N ((hs0 N).trans u.2.1) hu1
  have hlevel : 2 * sourceC6 d E s ζ N (u : ℝ) ≤
      ((band d).ell N (u : ℝ) / sourceEll d s ζ N) ^ 5 *
        ((((band d).W N : ℝ) * (band d).ell N (u : ℝ) *
          etaT E (u : ℝ)) ^ 2)⁻¹ ^ 2 *
        ((band d).W N * (band d).ell N (u : ℝ) * etaT E (u : ℝ))⁻¹ := by
    unfold sourceC6 sourceEll
    exact le_of_eq (by simpa only [Band.scale] using
      (source_level_identity
        (ellu := (band d).ell N (u : ℝ))
        (ells := (band d).ell N (s N))
        (A := (band d).scale E N (u : ℝ))
        (q := (N : ℝ) ^ ζ) hells hA hq))
  exact APrimeFullQV.sourceEvent_of_step1 (sample d) E N (u : ℝ) ω h4 h6 hlevel

theorem rawThree_on_sourceGood (d : Dims) {E : ℝ} {s t : ℕ → ℝ}
    {ζ : ℝ} {N : ℕ} (u : TimeIcc s t N) {ω : Ω d}
    (hω : ω ∈ sourceGood d E s t ζ N) :
    ∀ p : LoopData (d.L N) 3,
      ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC3 d E s ζ N u := by
  intro p
  have hp := hω.1.1.2 (u, p)
  simpa only [Step1.aprioriRhs, Nat.reduceSub, sourceC3, mul_assoc] using hp

theorem highProb_sourceGood (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t)
    {ζ : ℝ} (hζ : 0 < ζ) :
    HighProb (P d) (sourceGood d E s t ζ) := by
  let κ : ℝ := (2 - |E|) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hEκ : |E| ≤ 2 - κ := by dsimp [κ]; linarith
  have h3 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 3 (by norm_num)
  have h4 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 4 (by norm_num)
  have h6 := Step1.apriori (sample d) hκ hEκ hB hs0 hst ht1
    hreg.1 hc hreg.2 hStep 6 (by norm_num)
  have hp3 : HighProb (P d) (rawEvent d E s t ζ 3) := h3.highProb hζ
  have hp4 : HighProb (P d) (rawEvent d E s t ζ 4) := h4.highProb hζ
  have hp6 : HighProb (P d) (rawEvent d E s t ζ 6) := h6.highProb hζ
  change HighProb (P d) (fun N =>
    (((normGood d N ∩ rawEvent d E s t ζ 3 N) ∩
      rawEvent d E s t ζ 4 N) ∩ rawEvent d E s t ζ 6 N))
  exact (((Gauss.highProb_norm_Xmat_le d).inter hp3).inter hp4).inter hp6

/-- The generic raw-source carrier under the same Step-1 and Gaussian inputs
as the fixed-example carrier.  All conclusions use one sample at every time. -/
theorem general_moving_raw_sources (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (sourceGood d E s t ζ) ∧
      (∀ N, MeasurableSet (sourceGood d E s t ζ N)) ∧
      (∀ N, sourceGood d E s t ζ N ⊆ normGood d N) ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ sourceGood d E s t ζ N,
        ∀ u : TimeIcc s t N,
          APrimeFullQV.SourceEvent (sample d) E N (u : ℝ) ω
            (sourceEll d s ζ N) (sourceC4 d E s ζ N u) ∧
          (∀ p : LoopData (d.L N) 3,
            ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC3 d E s ζ N u) := by
  intro ζ hζ
  refine ⟨highProb_sourceGood d hE hs0 hst ht1 hc hreg hB hStep hζ,
    measurableSet_sourceGood d hE ht1 ζ,
    sourceGood_subset_normGood d E s t ζ, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN ω hω u
  exact ⟨sourceEvent_on_sourceGood d hE hs0 ht1 hζ (by omega) u hω,
    rawThree_on_sourceGood d u hω⟩

/-- A closed-input wrapper: the already compiled Gaussian construction of
`Step1.Hyp` discharges that premise from `BoundsCore` and `Cond272Reg`. -/
theorem general_moving_raw_sources_of_scale (d : Dims) {E c : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s) :
    ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (sourceGood d E s t ζ) ∧
      (∀ N, MeasurableSet (sourceGood d E s t ζ N)) ∧
      (∀ N, sourceGood d E s t ζ N ⊆ normGood d N) ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ sourceGood d E s t ζ N,
        ∀ u : TimeIcc s t N,
          APrimeFullQV.SourceEvent (sample d) E N (u : ℝ) ω
            (sourceEll d s ζ N) (sourceC4 d E s ζ N u) ∧
          (∀ p : LoopData (d.L N) 3,
            ‖(sample d).Lval E N (u : ℝ) ω p.idx‖ ≤ sourceC3 d E s ζ N u) := by
  let κ : ℝ := (2 - |E|) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hEκ : |E| ≤ 2 - κ := by dsimp [κ]; linarith
  have hStep := Gauss.step1Hyp_gauss_of_scale'' d hκ hEκ hB hs0 hst ht1
    hreg.1 hc hreg.2
  exact general_moving_raw_sources d hE hs0 hst ht1 hc hreg hB hStep

/-- At `d = exampleGrow`, this is exactly the frozen event consumed by the
existing fixed-dimension source chain. -/
@[simp] theorem sourceGood_exampleGrow_eq {E : ℝ} {s t : ℕ → ℝ} {ζ : ℝ}
    (N : ℕ) :
    sourceGood Dims.exampleGrow E s t ζ N =
      APrimeGeneralMovingRawSources.sourceGood E s t ζ N := rfl

@[simp] theorem sourceEll_exampleGrow {s : ℕ → ℝ} {ζ : ℝ} (N : ℕ) :
    sourceEll Dims.exampleGrow s ζ N =
      APrimeGeneralMovingRawSources.sourceEll s ζ N := rfl

@[simp] theorem sourceC3_exampleGrow {E : ℝ} {s : ℕ → ℝ}
    {ζ : ℝ} (N : ℕ) (u : ℝ) :
    sourceC3 Dims.exampleGrow E s ζ N u =
      APrimeGeneralMovingRawSources.sourceC3 E s ζ N u := rfl

@[simp] theorem sourceC4_exampleGrow {E : ℝ} {s : ℕ → ℝ}
    {ζ : ℝ} (N : ℕ) (u : ℝ) :
    sourceC4 Dims.exampleGrow E s ζ N u =
      APrimeGeneralMovingRawSources.sourceC4 E s ζ N u := rfl

@[simp] theorem sourceC6_exampleGrow {E : ℝ} {s : ℕ → ℝ}
    {ζ : ℝ} (N : ℕ) (u : ℝ) :
    sourceC6 Dims.exampleGrow E s ζ N u =
      APrimeGeneralMovingRawSources.sourceC6 E s ζ N u := rfl

/-- The generic theorem specializes to the old five fields, including the
identical event and actual pointwise source conclusions. -/
theorem exampleGrow_specialization {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272Reg (band Dims.exampleGrow) E s t c)
    (hB : BoundsCore (sample Dims.exampleGrow) E s)
    (hStep : Step1.Hyp (sample Dims.exampleGrow) E s t) :
    ∀ ζ : ℝ, 0 < ζ →
      HighProb (P Dims.exampleGrow)
          (APrimeGeneralMovingRawSources.sourceGood E s t ζ) ∧
      (∀ N, MeasurableSet
          (APrimeGeneralMovingRawSources.sourceGood E s t ζ N)) ∧
      (∀ N, APrimeGeneralMovingRawSources.sourceGood E s t ζ N ⊆
          APrimeGeneralMovingGoodMesh.good N) ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ ω ∈ APrimeGeneralMovingRawSources.sourceGood E s t ζ N,
        ∀ u : TimeIcc s t N,
          APrimeFullQV.SourceEvent (sample Dims.exampleGrow) E N (u : ℝ) ω
            (APrimeGeneralMovingRawSources.sourceEll s ζ N)
            (APrimeGeneralMovingRawSources.sourceC4 E s ζ N u) ∧
          (∀ p : LoopData (Dims.exampleGrow.L N) 3,
            ‖(sample Dims.exampleGrow).Lval E N (u : ℝ) ω p.idx‖ ≤
              APrimeGeneralMovingRawSources.sourceC3 E s ζ N u) := by
  intro ζ hζ
  obtain ⟨hp, hmeas, hnorm, hsource⟩ :=
    general_moving_raw_sources Dims.exampleGrow hE hs0 hst ht1 hc hreg hB hStep ζ hζ
  have heq : (fun N => sourceGood Dims.exampleGrow E s t ζ N) =
      APrimeGeneralMovingRawSources.sourceGood E s t ζ := by
    funext N
    exact sourceGood_exampleGrow_eq N
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact heq ▸ hp
  · intro N
    have h := hmeas N
    rw [sourceGood_exampleGrow_eq N] at h
    exact h
  · intro N ω hω
    have hmem : ω ∈ sourceGood Dims.exampleGrow E s t ζ N ↔
        ω ∈ APrimeGeneralMovingRawSources.sourceGood E s t ζ N := by
      rw [sourceGood_exampleGrow_eq N]
    have hω' : ω ∈ sourceGood Dims.exampleGrow E s t ζ N := hmem.mpr hω
    have hω'' : ω ∈ normGood Dims.exampleGrow N := hnorm N hω'
    simpa [normGood, APrimeGeneralMovingGoodMesh.good] using hω''
  · filter_upwards [hsource] with N hsourceN ω hω u
    have hmem : ω ∈ sourceGood Dims.exampleGrow E s t ζ N ↔
        ω ∈ APrimeGeneralMovingRawSources.sourceGood E s t ζ N := by
      rw [sourceGood_exampleGrow_eq N]
    have hω' : ω ∈ sourceGood Dims.exampleGrow E s t ζ N := hmem.mpr hω
    simpa using hsourceN ω hω' u

/-- The accepted fixed-example first-cell witness remains a nonempty,
positive-length resident of this same generic event. -/
theorem exampleGrow_positive_length_same_event_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ δ : ℝ, 0 < ζ → 0 < δ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Ω Dims.exampleGrow,
        ω ∈ sourceGood Dims.exampleGrow 0
          (firstCellS τ') (firstCellT τ') ζ N ∧
        firstCellS τ' N < firstCellT τ' N ∧
        ∀ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
          APrimeFullQV.SourceEvent (sample Dims.exampleGrow) 0 N (u : ℝ) ω
            (sourceEll Dims.exampleGrow (firstCellS τ') ζ N)
            (sourceC4 Dims.exampleGrow 0 (firstCellS τ') ζ N u) ∧
          (∀ p : LoopData (Dims.exampleGrow.L N) 3,
            ‖(sample Dims.exampleGrow).Lval 0 N (u : ℝ) ω p.idx‖ ≤
              sourceC3 Dims.exampleGrow 0 (firstCellS τ') ζ N u) := by
  obtain ⟨τ', hτ', hwitness⟩ :=
    APrimeGeneralMovingRawSources.positive_length_same_source_support_witness
  refine ⟨τ', hτ', ?_⟩
  intro ζ δ hζ hδ
  filter_upwards [hwitness ζ δ hζ hδ] with N hN
  obtain ⟨ω, hω, _hmeas, hlen, _hcut, _hsupport, hsource⟩ := hN
  refine ⟨ω, ?_, hlen, ?_⟩
  · rw [sourceGood_exampleGrow_eq]
    exact hω
  · simpa using hsource

/-- The empty-prefix time `u = s_N` is included in the all-time source
statement. -/
theorem eventually_source_at_kZero (d : Dims) {E : ℝ}
    (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ sourceGood d E s t ζ N,
      APrimeFullQV.SourceEvent (sample d) E N (s N) ω
        (sourceEll d s ζ N) (sourceC4 d E s ζ N (s N)) ∧
      (∀ p : LoopData (d.L N) 3,
        ‖(sample d).Lval E N (s N) ω p.idx‖ ≤ sourceC3 d E s ζ N (s N)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN ω hω
  let u : TimeIcc s t N := ⟨s N, le_rfl, hst N⟩
  exact ⟨sourceEvent_on_sourceGood d hE hs0 ht1 hζ (by omega) u hω,
    rawThree_on_sourceGood d u hω⟩

#print axioms sourceGood_subset_normGood
#print axioms measurableSet_sourceGood
#print axioms sourceEvent_on_sourceGood
#print axioms rawThree_on_sourceGood
#print axioms highProb_sourceGood
#print axioms general_moving_raw_sources
#print axioms general_moving_raw_sources_of_scale
#print axioms sourceGood_exampleGrow_eq
#print axioms exampleGrow_specialization
#print axioms exampleGrow_positive_length_same_event_resident
#print axioms eventually_source_at_kZero

end
end RBM.APrimeRawSourcesGeneralDims
