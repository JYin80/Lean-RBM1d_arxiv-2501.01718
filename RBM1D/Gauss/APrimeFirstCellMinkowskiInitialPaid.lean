/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellMinkowskiExact
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget

/-!
# T505: actual first-cell Minkowski with the initial moment paid

The uniform T500 initial budget is substituted into T494's literal
canonical-weight Minkowski inequality.  Both integrals and the quadratic
variation square root remain unchanged.  The closed producer retains
T500's one first-cell parameter, literal sharp event, and positive resident.
-/

namespace RBM.APrimeFirstCellMinkowskiInitialPaid

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellInitialMomentBudget.delta

theorem delta_eq_one_over_two_thousand : delta = 1 / 2000 := rfl

/-- The actual Minkowski bound with only the initial term replaced by its
exact `N^(5 delta / 32) R_v^(-2)` budget. -/
def initialPaidBoundAt (τ' α : ℝ) (p N k : ℕ)
    (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight τ' p N k) p (Y N k a (endpoint N k)) ≤
    (N : ℝ) ^ (5 * delta / 32) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) +
      2 * (∫ r in (0 : ℝ)..endpoint N k,
        (A τ' p N k a r + B τ' α p N k r)) +
      Real.sqrt ((2 * (p : ℝ) - 1) *
        ∫ r in (0 : ℝ)..endpoint N k, g τ' p N k a r)

/-- Direct substitution adds no size, bandwidth, or time factor. -/
theorem initialPaidBoundAt_of_initial_le {τ' α : ℝ} {p N k : ℕ}
    {a : LoopArg (d.L N) 2}
    (hmink : minkowskiBoundAt τ' α p N k a)
    (hinit : momNormW (P d) (weight τ' p N k) p (initial N k a) ≤
      (N : ℝ) ^ (5 * delta / 32) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :
    initialPaidBoundAt τ' α p N k a := by
  exact hmink.trans (add_le_add (add_le_add hinit le_rfl) le_rfl)

/-- The moment order and loss parameter are fixed before the common
eventual size threshold for all active positive indices and outputs. -/
def actualInitialPaidBound (τ' α : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    ∀ a : LoopArg (d.L N) 2, initialPaidBoundAt τ' α p N k a

/-- T500's single eventual threshold is intersected with the threshold of
the same-parameter T494 inequality, before choosing an endpoint or output. -/
theorem actualInitialPaidBound_of_minkowski {τ' α : ℝ}
    (hτ' : 0 < τ') (p : ℕ) (hp : 1 ≤ p)
    (hmink : actualMinkowskiBound τ' α p) :
    actualInitialPaidBound τ' α p := by
  filter_upwards [hmink,
    APrimeFirstCellInitialMomentBudget.eventually_initial_simplified hτ' p hp]
      with N hminkN hinitN
  intro k hk1 hk a
  exact initialPaidBoundAt_of_initial_le (hminkN k hk1 hk a) (hinitN k hk a)

/-- Closed actual first-cell bound for every positive first-cell parameter. -/
theorem eventually_initialPaidBoundAt {τ' α : ℝ}
    (hτ' : 0 < τ') (hα : 0 < α) (p : ℕ) (hp : 1 ≤ p) :
    actualInitialPaidBound τ' α p :=
  actualInitialPaidBound_of_minkowski hτ' p hp
    (APrimeFirstCellMinkowskiExact.eventually_minkowskiBoundAt hτ' hα p hp)

/-- Both unchanged integrated terms vanish exactly at the zero mesh index. -/
theorem integral_terms_k_zero (τ' α : ℝ) (p N : ℕ)
    (a : LoopArg (d.L N) 2) :
    2 * (∫ r in (0 : ℝ)..endpoint N 0,
      (A τ' p N 0 a r + B τ' α p N 0 r)) = 0 ∧
    Real.sqrt ((2 * (p : ℝ) - 1) *
      ∫ r in (0 : ℝ)..endpoint N 0, g τ' p N 0 a r) = 0 := by
  simp [endpoint, cutNetPt_zero]

/-- The zero-index branch retains the literal bound and its exact zero-time
reduction. -/
def kZeroInitialPaidBound (τ' α : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧ initialPaidBoundAt τ' α p N 0 a ∧
      momNormW (P d) (weight τ' p N 0) p (Y N 0 a (endpoint N 0)) ≤
        (N : ℝ) ^ (5 * delta / 32)

theorem eventually_kZeroInitialPaidBound {τ' : ℝ} (hτ' : 0 < τ')
    (α : ℝ) (p : ℕ) (hp : 1 ≤ p) :
    kZeroInitialPaidBound τ' α p := by
  filter_upwards
    [APrimeFirstCellInitialMomentBudget.eventually_initial_simplified hτ' p hp]
      with N hinit a
  obtain ⟨hv, hmink⟩ := minkowskiBoundAt_k_zero τ' α p N a
  have hpaid := initialPaidBoundAt_of_initial_le hmink (hinit 0 (Nat.zero_le _) a)
  refine ⟨hv, hpaid, ?_⟩
  simpa [initialPaidBoundAt, hv, etaT, mE_zero] using hpaid

/-- A concrete positive moving `k = 2` resident on the same literal sharp
event, with actual canonical weight one and all-output initial-paid bounds. -/
def positiveTwoInitialPaidResident (τ' α : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N,
    endpoint N 0 = 0 ∧ 0 < endpoint N 1 ∧ endpoint N 1 < endpoint N 2 ∧
    endpoint N 2 ≤ firstCellT τ' N ∧
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    weight τ' p N 2 ω = 1 ∧
    ∀ a : LoopArg (d.L N) 2, initialPaidBoundAt τ' α p N 2 a

/-- T500's resident is reused without replacing its parameter, sample, or
event.  Its exact initial-slot bound is simplified at that same endpoint. -/
theorem positiveTwoInitialPaidResident_of_initialResident {τ' α : ℝ} {p : ℕ}
    (hτ' : 0 < τ')
    (hresident : APrimeFirstCellInitialMomentBudget.positiveTwoInitialResident τ' α p) :
    positiveTwoInitialPaidResident τ' α p := by
  filter_upwards [hresident, eventually_ge_atTop 1] with N hr hN
  obtain ⟨ω, hω, hu0, hu1, hu12, hv, hk, hw, hall⟩ := hr
  refine ⟨ω, hω, hu0, hu1, hu12, hv, hk, hw, ?_⟩
  intro a
  obtain ⟨hinit, hmink⟩ := hall a
  unfold APrimeFirstCellInitialMomentBudget.initialBoundAt at hinit
  rw [APrimeFirstCellInitialMomentBudget.initialBudget_eq hτ' hN hk] at hinit
  exact initialPaidBoundAt_of_initial_le hmink hinit

/-- One T500/T494 parameter supplies the literal measurable, high-probability,
eventually nonempty sharp event, the uniform initial-paid bound, its zero
branch, and a positive actual canonical-weight-one resident. -/
theorem exists_initialPaid_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ α : ℝ, 0 < α → ∀ p : ℕ, 1 ≤ p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N)) ∧
        HighProb (P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α) ∧
        (∀ᶠ N : ℕ in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta α N).Nonempty) ∧
        actualInitialPaidBound τ' α p ∧
        kZeroInitialPaidBound τ' α p ∧
        positiveTwoInitialPaidResident τ' α p := by
  obtain ⟨τ', hτ', _hreg, _hB, hall⟩ :=
    APrimeFirstCellInitialMomentBudget.exists_initialMomentBudget_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro α hα p hp
  obtain ⟨hm, hprob, hne, _hinit, hmink, _hzero, hresident⟩ := hall α hα p hp
  exact ⟨hm, hprob, hne, actualInitialPaidBound_of_minkowski hτ' p hp hmink,
    eventually_kZeroInitialPaidBound hτ' α p hp,
    positiveTwoInitialPaidResident_of_initialResident hτ' hresident⟩

#print axioms initialPaidBoundAt_of_initial_le
#print axioms actualInitialPaidBound_of_minkowski
#print axioms eventually_initialPaidBoundAt
#print axioms integral_terms_k_zero
#print axioms eventually_kZeroInitialPaidBound
#print axioms positiveTwoInitialPaidResident_of_initialResident
#print axioms exists_initialPaid_with_resident

end

end RBM.APrimeFirstCellMinkowskiInitialPaid
