/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationNextImageCondExp

/-!
# Conditional expectation for a finite set of next images

The conditional expectation of the indicator that the next image lies in a
finite set is the number of still-unused values in that set divided by the
number of unused values. The proof is a finite sum of the accepted singleton
conditional-expectation theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace RBM.Gauss

private noncomputable def nextImageFinsetMean (W : ℕ) (k : Fin W)
    (A : Finset (Fin W)) : PermΩ W → ℝ :=
  fun π =>
    ((A.filter (fun v => v ∈ unusedImages W k π)).card : ℝ) /
      ((W - k.val : ℕ) : ℝ)

/-- The conditional expectation of the indicator that a uniformly random
permutation sends `k` into `A`, given the images before `k`, is the proportion
of currently unused values that lie in `A`. This is an almost-everywhere
statement; it makes no pointwise choice of conditional-expectation
representative. -/
theorem uniformPerm_nextImage_finset_condExp
    (W : ℕ) (k : Fin W) (A : Finset (Fin W)) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k ∈ A then (1 : ℝ) else 0) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      ((A.filter (fun v => v ∈ unusedImages W k π)).card : ℝ) /
        ((W - k.val : ℕ) : ℝ)) := by
  classical
  let f : Fin W → PermΩ W → ℝ :=
    fun v ρ => if ρ k = v then (1 : ℝ) else 0
  let g := fun v : Fin W =>
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k = v then (1 : ℝ) else 0) | prefixSigma W k.val]
  let q := fun v : Fin W => fun π : PermΩ W =>
    if v ∈ unusedImages W k π
    then (1 : ℝ) / ((W - k.val : ℕ) : ℝ) else 0
  have hindicator :
      (fun ρ : PermΩ W => if ρ k ∈ A then (1 : ℝ) else 0) =
        ∑ v ∈ A, f v := by
    funext ρ
    simp [f, eq_comm, Finset.sum_ite_eq']
  have hcond :
      (uniformPerm W)[∑ v ∈ A, f v | prefixSigma W k.val] =ᵐ[uniformPerm W]
        ∑ v ∈ A, g v := by
    simpa [f, g] using
      (condExp_finsetSum
        (μ := uniformPerm W) (s := A)
        (f := fun (v : Fin W) (ρ : PermΩ W) => if ρ k = v then (1 : ℝ) else 0)
        (fun v hv => Integrable.of_finite)
        (prefixSigma W k.val))
  have hcondIndicator := condExp_congr_ae
    (μ := uniformPerm W) (m := prefixSigma W k.val)
    (Filter.Eventually.of_forall (fun ρ => congrFun hindicator ρ))
  have hsingle : ∀ v : Fin W, g v =ᵐ[uniformPerm W] q v := by
    intro v
    simpa [g, q] using uniformPerm_nextImage_condExp W k v
  have hall : ∀ᵐ π ∂uniformPerm W, ∀ v : Fin W, g v π = q v π :=
    ae_all_iff.2 hsingle
  have hsum : (∑ v ∈ A, g v) =ᵐ[uniformPerm W] ∑ v ∈ A, q v := by
    filter_upwards [hall] with π hπ
    simpa only [Finset.sum_apply] using
      (Finset.sum_congr rfl (fun v _ => hπ v))
  have hcollapse :
      (∑ v ∈ A, q v) =ᵐ[uniformPerm W]
        nextImageFinsetMean W k A := by
    apply Filter.Eventually.of_forall
    intro π
    simp only [Finset.sum_apply]
    rw [nextImageFinsetMean]
    simp only [q]
    rw [← Finset.sum_filter]
    simp [div_eq_mul_inv, mul_comm]
  calc
    (uniformPerm W)[(fun ρ : PermΩ W => if ρ k ∈ A then (1 : ℝ) else 0) |
        prefixSigma W k.val]
        =ᵐ[uniformPerm W]
          (uniformPerm W)[∑ v ∈ A, f v | prefixSigma W k.val] := hcondIndicator
    _ =ᵐ[uniformPerm W] ∑ v ∈ A, g v := hcond
    _ =ᵐ[uniformPerm W] ∑ v ∈ A, q v := hsum
    _ =ᵐ[uniformPerm W] nextImageFinsetMean W k A := hcollapse

/-- Width zero has no valid next-image index. -/
theorem uniformPerm_nextImage_finset_condExp_no_index_zero : ¬ Nonempty (Fin 0) :=
  uniformPerm_nextImage_condExp_no_index_zero

/-- At width one, the event that the next image lies in `A` is deterministic. -/
theorem uniformPerm_nextImage_finset_condExp_one (A : Finset (Fin 1)) :
    (uniformPerm 1)[(fun ρ : PermΩ 1 =>
      if ρ 0 ∈ A then (1 : ℝ) else 0) | prefixSigma 1 0]
      =ᵐ[uniformPerm 1]
    (fun _ => if (0 : Fin 1) ∈ A then (1 : ℝ) else 0) := by
  have h := uniformPerm_nextImage_finset_condExp 1 (0 : Fin 1) A
  have hu (π : PermΩ 1) : unusedImages 1 0 π = {0} := by
    ext v
    fin_cases v <;> simp [unusedImages]
  by_cases h0 : (0 : Fin 1) ∈ A
  · have hfilter : A.filter (fun v : Fin 1 => v = 0) = {0} := by
      ext v
      fin_cases v <;> simp [h0]
    filter_upwards [h] with π hπ
    simpa [hu π, hfilter, h0] using hπ
  · have hfilter : A.filter (fun v : Fin 1 => v = 0) = ∅ := by
      ext v
      fin_cases v <;> simp [h0]
    filter_upwards [h] with π hπ
    simpa [hu π, hfilter, h0] using hπ

/-- At width two before any reveal, a singleton next-image event has
conditional probability one half. -/
theorem uniformPerm_nextImage_finset_condExp_two_singleton :
    (uniformPerm 2)[(fun ρ : PermΩ 2 =>
      if ρ 0 ∈ ({0} : Finset (Fin 2)) then (1 : ℝ) else 0) |
        prefixSigma 2 0]
      =ᵐ[uniformPerm 2] (fun _ => (1 : ℝ) / 2) := by
  simpa [unusedImages] using
    uniformPerm_nextImage_finset_condExp 2 (0 : Fin 2) ({0} : Finset (Fin 2))

/-- At width two, the singleton next-image event is nonempty and proper:
identity realizes it, while the transposition does not. -/
theorem uniformPerm_nextImage_finset_condExp_two_event_nonempty_proper :
    (Equiv.refl (Fin 2) : PermΩ 2) ∈
        {π : PermΩ 2 | π 0 ∈ ({0} : Finset (Fin 2))} ∧
      (Equiv.swap (0 : Fin 2) 1 : PermΩ 2) ∉
        {π : PermΩ 2 | π 0 ∈ ({0} : Finset (Fin 2))} := by
  constructor <;> simp

/-- On the last valid reveal, the finite-set formula has denominator one. -/
theorem uniformPerm_nextImage_finset_condExp_last (W : ℕ) (k : Fin W)
    (A : Finset (Fin W)) (hk : k.val + 1 = W) :
    (uniformPerm W)[(fun ρ : PermΩ W =>
      if ρ k ∈ A then (1 : ℝ) else 0) | prefixSigma W k.val]
      =ᵐ[uniformPerm W]
    (fun π : PermΩ W =>
      ((A.filter (fun v => v ∈ unusedImages W k π)).card : ℝ) / 1) := by
  have h : W - k.val = 1 := by omega
  simpa [h] using uniformPerm_nextImage_finset_condExp W k A

#print axioms uniformPerm_nextImage_finset_condExp
#print axioms uniformPerm_nextImage_finset_condExp_no_index_zero
#print axioms uniformPerm_nextImage_finset_condExp_one
#print axioms uniformPerm_nextImage_finset_condExp_two_singleton
#print axioms uniformPerm_nextImage_finset_condExp_two_event_nonempty_proper
#print axioms uniformPerm_nextImage_finset_condExp_last

end RBM.Gauss
