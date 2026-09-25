/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

/-!
# Grid stopping times

Generic (filtration-agnostic) construction of the grid stopping times used in the
pilot true-path argument, `docs/claude-team/pilot-P4P5-paper.md` §4, §6: the first
grid index at which an adapted real process reaches a threshold (formula (5.43),
with the `N^δ` correction discussed in §6), and the minimum of two such times.

`Mathlib.Probability.Process.HittingTime` no longer exposes `MeasureTheory.hitting`;
the current API is `MeasureTheory.hittingBtwn` (bounded, "else the right endpoint")
and `MeasureTheory.hittingAfter` (unbounded, "else `⊤`"). `firstHit` below is built
on `hittingBtwn`, which already has the "else `K`" convention the paper wants.
-/

namespace RBM.Gauss.Grid

open MeasureTheory

variable {Ω' : Type*} {m : MeasurableSpace Ω'}

/-- (T1) The first grid index `j ≤ K` at which `J j ω` reaches the threshold `θ`
(i.e. lands in `Set.Ici θ`), or `K` if it never does before the grid horizon. -/
noncomputable def firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) : Ω' → ℕ :=
  fun ω => MeasureTheory.hittingBtwn J (Set.Ici θ) 0 K ω

section OneProcess

variable {ℱ : Filtration ℕ m}

/-- (T2, part 1) `firstHit` is a stopping time for the filtration `ℱ`, provided the
underlying process `J` is `ℱ`-adapted. -/
theorem isStoppingTime_firstHit (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (hJ : Adapted ℱ J) :
    IsStoppingTime ℱ (fun ω => (firstHit J θ K ω : ℕ)) :=
  hJ.isStoppingTime_hittingBtwn measurableSet_Ici

/-- (T2, part 2) `firstHit` never exceeds the grid horizon `K`. -/
theorem firstHit_le (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (ω : Ω') :
    firstHit J θ K ω ≤ K :=
  MeasureTheory.hittingBtwn_le ω

/-- (T3, part 1) The event that the grid has not stopped by time `j` is
`ℱ j`-measurable. -/
theorem lt_firstHit_measurableSet (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) (hJ : Adapted ℱ J)
    (j : ℕ) : MeasurableSet[ℱ j] {ω | j < firstHit J θ K ω} := by
  have hτ := isStoppingTime_firstHit (ℱ := ℱ) J θ K hJ
  have hmeas : MeasurableSet[ℱ j] {ω : Ω' | firstHit J θ K ω ≤ j} := by
    have h' := hτ.measurableSet_le j
    simpa using h'
  have hset : {ω : Ω' | j < firstHit J θ K ω} = {ω : Ω' | firstHit J θ K ω ≤ j}ᶜ := by
    ext ω; simp [not_le]
  rw [hset]
  exact hmeas.compl

/-- (T3, part 2) Strictly before the grid stops, the process is strictly below the
threshold. -/
theorem lt_firstHit_imp (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {j : ℕ} {ω : Ω'}
    (h : j < firstHit J θ K ω) : J j ω < θ := by
  have hnotmem : J j ω ∉ Set.Ici θ :=
    MeasureTheory.notMem_of_lt_hittingBtwn (u := J) (s := Set.Ici θ) (n := 0) h
      (Nat.zero_le j)
  simpa [Set.mem_Ici, not_le] using hnotmem

end OneProcess

section TwoProcesses

variable {ℱ : Filtration ℕ m}

/-- (T4, part 1) The minimum of two grid stopping times `firstHit J θ K` and
`firstHit J' θ' K` (over the same grid horizon `K`) is again a stopping time.
Cites Mathlib's `IsStoppingTime.min`. -/
theorem isStoppingTime_min_firstHit (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ)
    (hJ : Adapted ℱ J) (hJ' : Adapted ℱ J') :
    IsStoppingTime ℱ
      (fun ω => (min (firstHit J θ K ω) (firstHit J' θ' K ω) : ℕ)) := by
  have h1 := isStoppingTime_firstHit (ℱ := ℱ) J θ K hJ
  have h2 := isStoppingTime_firstHit (ℱ := ℱ) J' θ' K hJ'
  intro i
  have hunion := (h1.measurableSet_le i).union (h2.measurableSet_le i)
  convert hunion using 2
  ext ω
  simp [min_le_iff]

/-- (T4, part 2) The event that neither grid time has stopped by `j` is
`ℱ j`-measurable. -/
theorem lt_min_firstHit_measurableSet (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ)
    (hJ : Adapted ℱ J) (hJ' : Adapted ℱ J') (j : ℕ) :
    MeasurableSet[ℱ j]
      {ω | j < min (firstHit J θ K ω) (firstHit J' θ' K ω)} := by
  have hτ := isStoppingTime_min_firstHit (ℱ := ℱ) J J' θ θ' K hJ hJ'
  have hmeas :
      MeasurableSet[ℱ j]
        {ω : Ω' | min (firstHit J θ K ω) (firstHit J' θ' K ω) ≤ j} := by
    have h' := hτ.measurableSet_le j
    simpa using h'
  have hset :
      {ω : Ω' | j < min (firstHit J θ K ω) (firstHit J' θ' K ω)}
        = {ω : Ω' | min (firstHit J θ K ω) (firstHit J' θ' K ω) ≤ j}ᶜ := by
    ext ω; simp [not_le]
  rw [hset]
  exact hmeas.compl

/-- (T4, part 3) Strictly before both grid times stop, both processes are
strictly below their respective thresholds. -/
theorem lt_min_firstHit_imp (J J' : ℕ → Ω' → ℝ) (θ θ' : ℝ) (K : ℕ) {j : ℕ} {ω : Ω'}
    (h : j < min (firstHit J θ K ω) (firstHit J' θ' K ω)) :
    J j ω < θ ∧ J' j ω < θ' := by
  rw [lt_min_iff] at h
  exact ⟨lt_firstHit_imp J θ K h.1, lt_firstHit_imp J' θ' K h.2⟩

end TwoProcesses

/-- (T5) Per-`ω` identity turning a sum stopped at `τ` into a sum over the full
grid range with the stopped-indicator inserted, used to put stopped sums in Azuma
form. Purely combinatorial: no measurability or stopping-time hypothesis needed. -/
theorem sum_stopped {M : Type*} [AddCommMonoid M] (Y : ℕ → Ω' → M) (τ : Ω' → ℕ)
    (k : ℕ) (ω : Ω') :
    ∑ j ∈ Finset.range (min k (τ ω)), Y (j + 1) ω
      = ∑ j ∈ Finset.range k, ({ω' | j < τ ω'}.indicator (Y (j + 1))) ω := by
  have hfilter : (Finset.range k).filter (fun j => j < τ ω) = Finset.range (min k (τ ω)) := by
    ext j
    simp [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j < τ ω <;> simp [hj]

end RBM.Gauss.Grid
