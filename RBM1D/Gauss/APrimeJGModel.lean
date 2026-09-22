/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.APrimeNearRem
import RBM1D.Gauss.APrimePrior
import RBM1D.Gauss.APrimeSlotFields

/-!
# T286: audit of the block-resolved (S3) level

`APrimeJG.highProb_jG_le_of_entryBoundFlow` gives `J ≤ 1 + N^τ(A·jS+2)` on its
high-probability event, where `A=9 exp(√3)`. `APrimePrior.le_cWt_mul_priorLevel`
gives `jS ≤ cWt·Λ` only on the soft-weight support. The certificate below shows
that these two inequalities do not imply `J ≤ cWt·Λ`, even on a common event and
even if the first inequality is strengthened to a deterministic one.
-/

namespace RBM.APrimeJGModel

open Real

noncomputable def entryFactor : ℝ := 9 * exp (sqrt 3)

theorem entryFactor_pos : 0 < entryFactor := by
  unfold entryFactor
  positivity

theorem priorWeight_pos : 0 < StepSideAPrime.cWt := by
  unfold StepSideAPrime.cWt
  positivity

/-- The strongest direct substitution of the available prior `jS` bound into the
event version of (4.2). The factor `q=N^τ` remains outside the prior level. -/
theorem jG_le_relaxed_of_prior {q Λ S J : ℝ} (hq : 0 ≤ q)
    (hS : S ≤ StepSideAPrime.cWt * Λ)
    (hJ : J ≤ 1 + q * (entryFactor * S + 2)) :
    J ≤ 1 + q * (entryFactor * (StepSideAPrime.cWt * Λ) + 2) := by
  have hA : 0 ≤ entryFactor := entryFactor_pos.le
  have hmul : 0 ≤ q * entryFactor := mul_nonneg hq hA
  have hdiff : 0 ≤ (q * entryFactor) * (StepSideAPrime.cWt * Λ - S) :=
    mul_nonneg hmul (sub_nonneg.mpr hS)
  nlinarith

#print axioms jG_le_relaxed_of_prior

/-- A positive, nontrivial joint witness to both available upper bounds, for every
gain factor `q ≥ 1`; it violates the requested unchanged prior level. -/
theorem no_same_level_from_jG_event (q : ℝ) (hq : 1 ≤ q) :
    ¬ ∀ Λ S J : ℝ,
      0 < Λ → 1 ≤ S → S ≤ StepSideAPrime.cWt * Λ →
      1 ≤ J → J ≤ 1 + q * (entryFactor * S + 2) →
      J ≤ StepSideAPrime.cWt * Λ := by
  intro h
  let L := StepSideAPrime.cWt
  let A := entryFactor
  have hL : 0 < L := priorWeight_pos
  have hA : 0 < A := entryFactor_pos
  have hA1 : 1 < A := by
    dsimp [A, entryFactor]
    have he := Real.one_le_exp (Real.sqrt_nonneg 3)
    nlinarith
  have hS : 1 ≤ L := by
    dsimp [L, StepSideAPrime.cWt]
    have he := Real.exp_pos 1
    linarith
  have hJ : 1 ≤ 1 + q * (A * L + 2) := by
    have hq0 : 0 ≤ q := by linarith
    nlinarith [mul_nonneg hq0 (by positivity : 0 ≤ A * L + 2)]
  have hfinal := h 1 L (1 + q * (A * L + 2)) (by norm_num)
    hS (by simp [L]) hJ (by simp [A, L])
  have hqmul : A * L + 2 ≤ q * (A * L + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hq)
      (by positivity : 0 ≤ A * L + 2)]
  have hAL : L < A * L + 2 := by
    nlinarith [mul_pos (sub_pos.mpr hA1) hL]
  have hfinal' : 1 + q * (A * L + 2) ≤ L := by
    simpa only [mul_one] using hfinal
  linarith

#print axioms no_same_level_from_jG_event

/-- Nonemptiness of the `(4.2) ∩ goodSetFlow` event and nonemptiness of the
soft-weight support separately do not establish a common sample point. -/
theorem separate_nonempty_events_need_not_intersect :
    ∃ A B : Set (Fin 2), A.Nonempty ∧ B.Nonempty ∧ ¬(A ∩ B).Nonempty := by
  refine ⟨{0}, {1}, ?_, ?_, ?_⟩
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · simp

#print axioms separate_nonempty_events_need_not_intersect

end RBM.APrimeJGModel
