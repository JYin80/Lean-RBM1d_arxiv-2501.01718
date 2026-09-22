/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellCommon

/-!
# T384: actual first-cell sources at every running time

The raw length-four and length-six events are already uniform over the full
first cell.  This module converts them to `SourceEvent` at each running time,
retaining the `N^ζ` losses and the factor two in the six-loop level.
-/

namespace RBM.APrimeFirstCellSourceAllTime

open Filter MeasureTheory Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable def sourceC4 (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * (band d).ell N u ^ (3 : ℕ) *
    ((band d).scale 0 N u)⁻¹ ^ (3 : ℕ)

noncomputable def sourceC6 (ζ : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (N : ℝ) ^ ζ * (band d).ell N u ^ (5 : ℕ) *
    ((band d).scale 0 N u)⁻¹ ^ (5 : ℕ)

noncomputable def ellSource (ζ : ℝ) (N : ℕ) : ℝ :=
  (2 * (N : ℝ) ^ ζ) ^ (-(1 / 5 : ℝ))

private def rawEvent (τ' ζ : ℝ) (n N : ℕ) : Set (Ω d) :=
  {ω | ∀ p : TimeIcc (firstCellS τ') (firstCellT τ') N ×
      LoopData (d.L N) n,
    ‖(sample d).Lval 0 N p.1 ω p.2.idx‖ ≤
      (N : ℝ) ^ ζ *
        Step1.aprioriRhs (band d) 0 (firstCellS τ') (firstCellT τ') n N p ω}

/-- The same measurable Gaussian event as T348, with its raw laws quantified
over every running time and every loop label. -/
def commonEvent (τ' ζ : ℝ) (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)} ∩
    rawEvent τ' ζ 4 N ∩ rawEvent τ' ζ 6 N ∩
    goodSetFlow d 0 (firstCellS τ') (firstCellT τ') firstCellDelta N

theorem commonEvent_measurable (τ' ζ : ℝ) (N : ℕ) :
    MeasurableSet (commonEvent τ' ζ N) := by
  have h := APrimeFirstCellCommon.commonEvent_measurable τ' ζ N
  change MeasurableSet (commonEvent τ' ζ N) at h
  exact h

theorem exists_highProb_common :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (commonEvent τ' ζ) := by
  obtain ⟨τ', hτ', hp⟩ := APrimeFirstCellCommon.exists_highProb_firstCell_common
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  have h := hp ζ hζ
  change HighProb (P d) (commonEvent τ' ζ) at h
  exact h

private theorem source_level_identity {ell A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    2 * (q * ell ^ 5 * (A⁻¹) ^ 5) =
      (ell / (2 * q) ^ (-(1 / 5 : ℝ))) ^ 5 * (((A ^ 2)⁻¹) ^ 2) * A⁻¹ := by
  have hb : 0 < 2 * q := by positivity
  have hr : ((2 * q) ^ (-(1 / 5 : ℝ))) ^ 5 = (2 * q)⁻¹ := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hb.le]
    norm_num [Real.rpow_neg_one]
  rw [div_pow, hr]
  field_simp

private theorem firstCellS_zero (τ' : ℝ) (N : ℕ) : firstCellS τ' N = 0 := by
  change gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0 = 0
  exact gridT_zero (by norm_num)

/-- Exact raw levels and the six-loop factor-two identity at each running
time, on the one T348 event. -/
theorem sourceEvent_of_common {τ' ζ : ℝ} {N : ℕ} (hN : 0 < N)
    (u : TimeIcc (firstCellS τ') (firstCellT τ') N)
    {ω : Ω d} (hω : ω ∈ commonEvent τ' ζ N) :
    APrimeFullQV.SourceEvent (sample d) 0 N (u : ℝ) ω
      (ellSource ζ N) (sourceC4 ζ N u) := by
  have hℓs : (band d).ell N (firstCellS τ' N) = 1 := by
    rw [firstCellS_zero]
    exact ellHat_zero _ ((band d).three_le_L N)
  rcases hω with ⟨⟨⟨_, h4ev⟩, h6ev⟩, _⟩
  have h4 : ∀ p : LoopData ((band d).L N) 4,
      ‖(sample d).Lval 0 N (u : ℝ) ω p.idx‖ ≤ sourceC4 ζ N u := by
    intro p
    have hp := h4ev (u, p)
    convert hp using 1 <;> simp [Step1.aprioriRhs, hℓs, sourceC4, mul_assoc]
  have h6 : ∀ p : LoopData ((band d).L N) 6,
      ‖(sample d).Lval 0 N (u : ℝ) ω p.idx‖ ≤ sourceC6 ζ N u := by
    intro p
    have hp := h6ev (u, p)
    convert hp using 1 <;> simp [Step1.aprioriRhs, hℓs, sourceC6, mul_assoc]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : (0 : ℝ) < (N : ℝ) ^ ζ := Real.rpow_pos_of_pos hNr _
  have hu0 : 0 ≤ (u : ℝ) := by
    simpa only [firstCellS_zero] using u.2.1
  have hu1 : (u : ℝ) < 1 :=
    u.2.2.trans_lt ((gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num))
  have hA : 0 < (band d).scale 0 N u :=
    (band d).scale_pos' (by norm_num) N hu0 hu1
  have hlevel : 2 * sourceC6 ζ N u ≤
      ((band d).ell N u / ellSource ζ N) ^ 5 *
        (((((band d).W N : ℝ) * (band d).ell N u * etaT 0 u) ^ 2)⁻¹) ^ 2 *
        (((band d).W N : ℝ) * (band d).ell N u * etaT 0 u)⁻¹ := by
    unfold sourceC6 ellSource
    exact le_of_eq (by simpa only [Band.scale] using
      (source_level_identity (ell := (band d).ell N u)
        (A := (band d).scale 0 N u)
        (q := (N : ℝ) ^ ζ) hA hq))
  exact APrimeFullQV.sourceEvent_of_step1 (sample d) 0 N (u : ℝ) ω h4 h6 hlevel

/-- One first-cell parameter gives a measurable, high-probability event whose
every member carries the actual source event at every running time. -/
theorem exists_highProb_source_allTime :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      HighProb (P d) (commonEvent τ' ζ) ∧
      (∀ N, MeasurableSet (commonEvent τ' ζ N)) ∧
      ∀ᶠ N : ℕ in atTop, ∀ ω ∈ commonEvent τ' ζ N,
        ∀ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
          APrimeFullQV.SourceEvent (sample d) 0 N (u : ℝ) ω
            (ellSource ζ N) (sourceC4 ζ N u) := by
  obtain ⟨τ', hτ', hp⟩ := exists_highProb_common
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  refine ⟨hp ζ hζ, commonEvent_measurable τ' ζ, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN ω hω u
  exact sourceEvent_of_common (by omega) u hω

/-- The same event has an actual positive running time and one Gaussian
sample carrying the source at that time and throughout the cell. -/
theorem exists_positive_time_source_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ N : ℕ in atTop, ∃ ω : Ω d,
        ω ∈ commonEvent τ' ζ N ∧
        MeasurableSet (commonEvent τ' ζ N) ∧
        ∃ u : TimeIcc (firstCellS τ') (firstCellT τ') N,
          0 < (u : ℝ) ∧ 0 < ellSource ζ N ∧ ellSource ζ N < 1 ∧
          APrimeFullQV.SourceEvent (sample d) 0 N (u : ℝ) ω
            (ellSource ζ N) (sourceC4 ζ N u) ∧
          ∀ v : TimeIcc (firstCellS τ') (firstCellT τ') N,
            APrimeFullQV.SourceEvent (sample d) 0 N (v : ℝ) ω
              (ellSource ζ N) (sourceC4 ζ N v) := by
  obtain ⟨τ', hτ', hp⟩ := exists_highProb_common
  refine ⟨τ', hτ', ?_⟩
  intro ζ hζ
  have hne := HighProb.nonempty (by simp) (hp ζ hζ)
  filter_upwards [hne, first_cell_window_nondegenerate d hτ',
    eventually_ge_atTop 2] with N hneN hwin hN
  obtain ⟨ω, hω⟩ := hneN
  have hs : firstCellS τ' N = 0 := firstCellS_zero τ' N
  have hu : 0 < firstCellT τ' N := by
    change firstCellS τ' N < firstCellT τ' N at hwin
    rw [hs] at hwin
    exact hwin
  let u : TimeIcc (firstCellS τ') (firstCellT τ') N :=
    ⟨firstCellT τ' N, hwin.le, le_rfl⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hq : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hNr hζ.le
  have hb : 1 < 2 * (N : ℝ) ^ ζ := by linarith
  have hellpos : 0 < ellSource ζ N := by
    unfold ellSource
    positivity
  have helllt : ellSource ζ N < 1 := by
    unfold ellSource
    exact Real.rpow_lt_one_of_one_lt_of_neg hb (by norm_num)
  exact ⟨ω, hω, commonEvent_measurable τ' ζ N, u, hu, hellpos, helllt,
    sourceEvent_of_common (by omega) u hω,
    fun v => sourceEvent_of_common (by omega) v hω⟩

#print axioms commonEvent_measurable
#print axioms exists_highProb_common
#print axioms sourceEvent_of_common
#print axioms exists_highProb_source_allTime
#print axioms exists_positive_time_source_witness

end RBM.APrimeFirstCellSourceAllTime
