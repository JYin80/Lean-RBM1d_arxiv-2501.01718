/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridBootstrap
import RBM1D.Gauss.GridGoodEvent
import RBM1D.Gauss.GridDriftPoint
import RBM1D.Gauss.GridStepBound

/-!
# Step 2 on the grid: interface bridges and the a.e. data at the endpoint

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3 (Step 2 of Theorem 2.21,
(2.75)–(2.76)) for the Gaussian model, along the discrete grid.

This file supplies bridges between the grid step bound and threshold improvement
(`GridStepBound.lean`), the grid stopping time and good event (`GridGoodEvent.lean`), the drift
bound on the good set (`GridDriftPoint.lean`), the grid expansion (`GridExpansion.lean`) and the
bootstrap core with the `jSMat → lkErrMat` conversion (`GridBootstrap.lean`).

## Interface bridges

* `H_eq_H_zero_of_eq`, `time_eq_time_zero_of_eq`: the degenerate grid `u N = s N` (the grid
  expansion needs `s N < u N`).
* `rowSet`, `measurableSet_rowSet`: the row form of (5.57), absent from `goodSet`.
* `mgDrift_nonneg`: the drift constant of the good-set drift bound is nonnegative.

## The a.e. data at the grid endpoint

* `GridAE`, `ae_gridAE`: the grid expansion identity and the remainder bound hold a.e. on a
  nondegenerate grid.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

/-! ### Bridge 2: the degenerate grid `u N = s N` -/

theorem time_eq_time_zero_of_eq {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (h : s N = u N) (k : ℕ) :
    time s u K N k = time s u K N 0 := by
  simp [time, step, h]

theorem H_eq_H_zero_of_eq {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (h : s N = u N) (k : ℕ)
    (ω : Ωg d) : H d s u K N k ω = H d s u K N 0 ω := by
  simp [H, step, h]

/-! ### Bridge 3: the row form of (5.57) on the grid -/

/-- The matrix-set form of `(5.57)`, **row** orientation, at the (2.73)-reduced strength
(`eq557Set` is the column half). -/
def rowSet (E : ℝ) (N : ℕ) (v ℓs τ : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ x y : ZMod (d.L N), ∀ r : ZMod (d.L N) × Fin (d.W N), r.1 = x →
    ∑ p, RBM.Lemma57.blkW (d.L N) (d.W N) p y * ‖green M (zt E v) r p‖ ≤
      (N : ℝ) ^ τ * Real.sqrt ((band d).ell N v / ℓs) * (Real.sqrt ((band d).scale E N v))⁻¹}

theorem measurableSet_rowSet (E : ℝ) (N : ℕ) (v ℓs τ : ℝ) :
    MeasurableSet (rowSet d E N v ℓs τ) := by
  have heq : rowSet d E N v ℓs τ =
      ⋂ x : ZMod (d.L N), ⋂ y : ZMod (d.L N), ⋂ r : ZMod (d.L N) × Fin (d.W N),
        {M | r.1 = x → ∑ p, RBM.Lemma57.blkW (d.L N) (d.W N) p y * ‖green M (zt E v) r p‖ ≤
          (N : ℝ) ^ τ * Real.sqrt ((band d).ell N v / ℓs) *
            (Real.sqrt ((band d).scale E N v))⁻¹} := by
    unfold rowSet; ext M; simp
  rw [heq]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    MeasurableSet.iInter fun r => ?_
  by_cases hr : r.1 = x
  · have hm : MeasurableSet {M : Matrix (d.Idx N) (d.Idx N) ℂ |
        ∑ p, RBM.Lemma57.blkW (d.L N) (d.W N) p y * ‖green M (zt E v) r p‖ ≤
          (N : ℝ) ^ τ * Real.sqrt ((band d).ell N v / ℓs) *
            (Real.sqrt ((band d).scale E N v))⁻¹} :=
      measurableSet_le (Finset.measurable_sum _ fun p _ =>
        measurable_const.mul (measurable_green_matrix d N (zt E v) r p).norm) measurable_const
    convert hm using 2
    simp [hr]
  · convert MeasurableSet.univ using 2
    simp [hr]

/-! ### Bridge 4: the drift constant of the good-set drift bound -/

theorem mgDrift_nonneg (ζ : ℝ) (N : ℕ) : 0 ≤ mgDrift (band d) ζ N := by
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
  unfold mgDrift
  have h1 := Lemma57.cNear_nonneg hW1 (one_pos : (0 : ℝ) < 1)
  have h2 := Lemma57.cFar_nonneg hW1 (one_pos : (0 : ℝ) < 1)
  positivity

/-! ### The a.e. data at the grid endpoint -/

/-- The grid expansion identity (all `k ≤ K N`) and the remainder bound (all `j < K N`),
at one `ω`: the expansion and remainder inputs of the grid step bound. -/
def GridAE (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) : Prop :=
  (∀ k : ℕ, k ≤ K N → ∀ b : LoopArg ((band d).L N) 2,
      Agrid (band d) E s u K N k ω b
        = Uker ((band d).L N) (fun _ => (1 : ℂ)) (time s u K N 0 : ℂ) (time s u K N k : ℂ)
              (Agrid (band d) E s u K N 0 ω) b
          + (∑ j ∈ Finset.range k, Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Zvec (band d) E s u K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Yvec (band d) E s u K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, step s u K N • Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Dgrid (band d) E s u K N j ω)) b
          + (∑ j ∈ Finset.range k, Uker ((band d).L N) (fun _ => (1 : ℂ))
                (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
                (Rgrid (band d) E s u K N j ω)) b) ∧
  (∀ j < K N, ∀ b : LoopArg ((band d).L N) 2, ‖Rgrid (band d) E s u K N j ω b‖ ≤
      stepErr (band d) E N (time s u K N j) (time s u K N (j + 1)) (step s u K N))

/-- `GridAE` holds a.e. on a nondegenerate grid (`s N < u N < 1`): `grid_expansion_all'`
and `condExp_A_succ` (countably many `j`). -/
theorem ae_gridAE {E : ℝ} (hE : |E| < 2) {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N)
    (hsu : s N < u N) (hu1 : u N < 1) (hK0 : K N ≠ 0) :
    ∀ᵐ ω ∂(Pg d), GridAE d E s u K N ω := by
  have hK1 : 1 ≤ K N := Nat.one_le_iff_ne_zero.2 hK0
  have h1 := grid_expansion_all' (band d) s u K N E hE hs0 hsu hu1 hK1
  have h2 : ∀ᵐ ω ∂(Pg d), ∀ j : ℕ, j < K N → ∀ b : LoopArg ((band d).L N) 2,
      ‖Rgrid (band d) E s u K N j ω b‖ ≤
        stepErr (band d) E N (time s u K N j) (time s u K N (j + 1)) (step s u K N) := by
    refine ae_all_iff.mpr fun j => ?_
    by_cases hj : j < K N
    · have hu0 : 0 ≤ time s u K N j := hs0.trans (s_le_time s u K N hsu.le j)
      have hu1' : time s u K N (j + 1) < 1 :=
        (time_le_t s u K N hsu.le hK1 (by omega)).trans_lt hu1
      filter_upwards [condExp_A_succ (band d) s u K N j E hE hsu hj hu0 hu1'] with ω hω _ b
      exact (hω b).2
    · exact Filter.Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [h1, h2] with ω h1ω h2ω
  exact ⟨h1ω, h2ω⟩

end RBM.Gauss.Grid

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix RBM

variable (d : Dims)

end RBM.Gauss

end

