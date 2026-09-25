/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CutoffBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.MeanInequalities

/-!
# Higher derivatives of the finite even power sum

This file proves the explicit multilinear derivatives of `x ↦ ∑ i, x i ^ q` and the
dimension-free q-norm Hölder estimate needed in the coefficient check for formula (A) of
T1424 §3.2. It does not prove the outer fractional-power chain rule or the later cube or random
matrix estimates.
-/

noncomputable section

open Finset Real
open scoped ContDiff

namespace RBM.Gauss.PowerSumHigherDerivatives

variable {ι : Type*} [Fintype ι]

def powerSum (q : ℕ) (x : ι → ℝ) : ℝ := ∑ i, x i ^ q

/-- The finite-coordinate q-norm, expressed using real powers. -/
def qNorm (q : ℕ) (x : ι → ℝ) : ℝ :=
  (∑ i, |x i| ^ q) ^ ((q : ℝ)⁻¹)

theorem qNorm_nonneg (q : ℕ) (x : ι → ℝ) : 0 ≤ qNorm q x := by
  apply Real.rpow_nonneg
  exact Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg (x i)) q

theorem qNorm_pow (q : ℕ) (hq : 0 < q) (x : ι → ℝ) :
    qNorm q x ^ q = ∑ i, |x i| ^ q := by
  unfold qNorm
  exact Real.rpow_inv_natCast_pow
    (Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg (x i)) q) hq.ne'

private theorem qNorm_eq_zero_iff (q : ℕ) (hq : 0 < q) (x : ι → ℝ) :
    qNorm q x = 0 ↔ ∀ i, x i = 0 := by
  constructor
  · intro hx i
    have hsum0 : (∑ i, |x i| ^ q) = 0 := by
      have h := qNorm_pow q hq x
      rw [hx] at h
      simpa [hq.ne'] using h.symm
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => pow_nonneg (abs_nonneg (x i)) q)).mp hsum0 i (mem_univ i)
    exact abs_eq_zero.mp ((pow_eq_zero_iff hq.ne').mp hterm)
  · intro hx
    unfold qNorm
    simp [hx, hq.ne']

private theorem qNorm_normalized_sum_eq_one (q : ℕ) (hq : 0 < q)
    (x : ι → ℝ) (hx : 0 < qNorm q x) :
    ∑ i, (|x i| / qNorm q x) ^ q = 1 := by
  calc
    ∑ i, (|x i| / qNorm q x) ^ q =
        (∑ i, |x i| ^ q) / qNorm q x ^ q := by
          calc
            ∑ i, (|x i| / qNorm q x) ^ q =
                ∑ i, |x i| ^ q / qNorm q x ^ q := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [div_pow]
            _ = (∑ i, |x i| ^ q) / qNorm q x ^ q := by rw [← Finset.sum_div]
    _ = 1 := by
      rw [← qNorm_pow q hq x]
      exact div_self (pow_ne_zero q hx.ne')

private theorem normalized_mixed_sum_le_one (q j : ℕ) (hq : 0 < q) (hj : j ≤ q)
    (x : ι → ℝ) (v : Fin j → ι → ℝ) (A : ℝ) (B : Fin j → ℝ)
    (hA : 0 < A) (hB : ∀ m, 0 < B m)
    (hX : j = q ∨ ∑ i, (|x i| / A) ^ q = 1)
    (hV : ∀ m, ∑ i, (|v m i| / B m) ^ q = 1) :
    ∑ i, (|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m) ≤ 1 := by
  let w : Option (Fin j) → ℝ := fun a =>
    match a with
    | none => ((q - j : ℕ) : ℝ) / (q : ℝ)
    | some _ => (q : ℝ)⁻¹
  let z : ι → Option (Fin j) → ℝ := fun i a =>
    match a with
    | none => (|x i| / A) ^ q
    | some m => (|v m i| / B m) ^ q
  have hw : ∀ a, 0 ≤ w a := by
    intro a
    cases a <;> simp [w] <;> positivity
  have hwsum : ∑ a : Option (Fin j), w a = 1 := by
    rw [Fintype.sum_option]
    simp only [w]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hj]
    field_simp [Nat.cast_ne_zero.mpr hq.ne']
    ring
  have hz : ∀ i a, 0 ≤ z i a := by
    intro i a
    cases a with
    | none => simp [z]; positivity
    | some m =>
        simp [z]
        exact pow_nonneg (div_nonneg (abs_nonneg _) (hB m).le) q
  have hbase (i : ι) :
      ((|x i| / A) ^ q) ^ (((q - j : ℕ) : ℝ) / (q : ℝ)) =
        (|x i| / A) ^ (q - j) := by
    have hnonneg : 0 ≤ |x i| / A := div_nonneg (abs_nonneg _) hA.le
    have hexp : (q : ℝ) * (((q - j : ℕ) : ℝ) / (q : ℝ)) = ((q - j : ℕ) : ℝ) := by
      rw [Nat.cast_sub hj]
      field_simp [Nat.cast_ne_zero.mpr hq.ne']
    calc
      ((|x i| / A) ^ q) ^ (((q - j : ℕ) : ℝ) / (q : ℝ)) =
          ((|x i| / A) ^ (q : ℝ)) ^ (((q - j : ℕ) : ℝ) / (q : ℝ)) := by
            rw [← Real.rpow_natCast]
      _ = (|x i| / A) ^ ((q : ℝ) * (((q - j : ℕ) : ℝ) / (q : ℝ))) := by
            rw [← Real.rpow_mul hnonneg]
      _ = (|x i| / A) ^ ((q - j : ℕ) : ℝ) := by rw [hexp]
      _ = (|x i| / A) ^ (q - j) := by rw [Real.rpow_natCast]
  have hdir (m : Fin j) (i : ι) :
      ((|v m i| / B m) ^ q) ^ ((q : ℝ)⁻¹) = |v m i| / B m :=
    Real.pow_rpow_inv_natCast
      (div_nonneg (abs_nonneg _) (hB m).le) hq.ne'
  have hprod (i : ι) :
      ∏ a : Option (Fin j), z i a ^ w a =
        (|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m) := by
    rw [Fintype.prod_option]
    simp only [z, w]
    rw [hbase i]
    congr 1
    apply Finset.prod_congr rfl
    intro m hm
    exact hdir m i
  have hgeom (i : ι) :
      ∏ a : Option (Fin j), z i a ^ w a ≤ ∑ a, w a * z i a :=
    Real.geom_mean_le_arith_mean_weighted (Finset.univ)
      w (z i) (fun a _ => hw a) hwsum (fun a _ => hz i a)
  calc
    ∑ i, (|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m) =
        ∑ i, ∏ a : Option (Fin j), z i a ^ w a := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hprod i).symm
    _ ≤ ∑ i, ∑ a : Option (Fin j), w a * z i a :=
          Finset.sum_le_sum fun i _ => hgeom i
    _ = ∑ a : Option (Fin j), w a * ∑ i, z i a := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_sum]
    _ = w none * ∑ i, z i none +
          ∑ m : Fin j, w (some m) * ∑ i, z i (some m) := by
          rw [Fintype.sum_option]
    _ = 1 := by
          rcases hX with hjq | hX
          · subst j
            simp_rw [z, hV]
            simp [w, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            field_simp [Nat.cast_ne_zero.mpr hq.ne']
          · simp_rw [z, hX, hV]
            simp [w, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            rw [Nat.cast_sub hj]
            field_simp [Nat.cast_ne_zero.mpr hq.ne']
            ring

private theorem mixed_sum_scale_identity (q j : ℕ) (hj : j ≤ q)
    (x : ι → ℝ) (v : Fin j → ι → ℝ) (A : ℝ) (B : Fin j → ℝ)
    (hA : 0 < A) (hB : ∀ m, 0 < B m) :
    ∑ i, |x i| ^ (q - j) * ∏ m, |v m i| =
      (A ^ (q - j) * ∏ m, B m) *
        ∑ i, (|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m) := by
  have hBprod : (∏ m : Fin j, B m) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact (hB m).ne'
  have hterm (i : ι) :
      |x i| ^ (q - j) * ∏ m, |v m i| =
        (A ^ (q - j) * ∏ m, B m) *
          ((|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m)) := by
    rw [div_pow, Finset.prod_div_distrib]
    field_simp [hA.ne', hBprod]
  calc
    ∑ i, |x i| ^ (q - j) * ∏ m, |v m i| =
        ∑ i, (A ^ (q - j) * ∏ m, B m) *
          ((|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
    _ = (A ^ (q - j) * ∏ m, B m) *
          ∑ i, (|x i| / A) ^ (q - j) * ∏ m, (|v m i| / B m) := by
            rw [Finset.mul_sum]

private theorem mixed_sum_holder (q j : ℕ) (hq : 0 < q) (hj : j ≤ q)
    (x : ι → ℝ) (v : Fin j → ι → ℝ) :
    ∑ i, |x i| ^ (q - j) * ∏ m, |v m i| ≤
      qNorm q x ^ (q - j) * ∏ m, qNorm q (v m) := by
  by_cases hVzero : ∃ m : Fin j, qNorm q (v m) = 0
  · rcases hVzero with ⟨m, hm⟩
    have hvzero : ∀ i, v m i = 0 := (qNorm_eq_zero_iff q hq (v m)).mp hm
    have hprod (i : ι) : ∏ m' : Fin j, |v m' i| = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ m)]
      simp [hvzero i]
    have hnormprod : ∏ m' : Fin j, qNorm q (v m') = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ m)]
      exact hm
    simp_rw [hprod, hnormprod]
    simp
  · have hVne : ∀ m : Fin j, qNorm q (v m) ≠ 0 := by
      intro m hm
      exact hVzero ⟨m, hm⟩
    have hVpos : ∀ m : Fin j, 0 < qNorm q (v m) := by
      intro m
      exact (qNorm_nonneg q (v m)).lt_of_ne' (hVne m)
    have hVunit : ∀ m : Fin j, ∑ i, (|v m i| / qNorm q (v m)) ^ q = 1 := by
      intro m
      exact qNorm_normalized_sum_eq_one q hq (v m) (hVpos m)
    by_cases hjq : j = q
    · let A : ℝ := 1
      have hA : 0 < A := by simp [A]
      have hXunit : j = q ∨ ∑ i, (|x i| / A) ^ q = 1 := Or.inl hjq
      have hnorm := normalized_mixed_sum_le_one q j hq hj x v A
        (fun m => qNorm q (v m)) hA hVpos hXunit hVunit
      have hscale := mixed_sum_scale_identity q j hj x v A
        (fun m => qNorm q (v m)) hA hVpos
      have hr0 : q - j = 0 := by omega
      have hnorm' : ∑ i, ∏ m, (|v m i| / qNorm q (v m)) ≤ 1 := by
        simpa [hr0] using hnorm
      have hscale' : ∑ i, ∏ m, |v m i| =
          (∏ m, qNorm q (v m)) * ∑ i, ∏ m, (|v m i| / qNorm q (v m)) := by
        simpa [A, hr0] using hscale
      calc
        ∑ i, |x i| ^ (q - j) * ∏ m, |v m i| =
            (∏ m, qNorm q (v m)) *
              ∑ i, ∏ m, (|v m i| / qNorm q (v m)) := by
                simpa [hr0] using hscale'
        _ ≤ (∏ m, qNorm q (v m)) * 1 :=
              mul_le_mul_of_nonneg_left hnorm'
                (Finset.prod_nonneg fun m hm => qNorm_nonneg q (v m))
        _ = qNorm q x ^ (q - j) * ∏ m, qNorm q (v m) := by simp [hr0]
    · have hjlt : j < q := by omega
      by_cases hXzero : qNorm q x = 0
      · have hxzero : ∀ i, x i = 0 := (qNorm_eq_zero_iff q hq x).mp hXzero
        have hsubne : q - j ≠ 0 := by omega
        simp [hxzero, hXzero, hsubne]
      · have hXpos : 0 < qNorm q x := (qNorm_nonneg q x).lt_of_ne' hXzero
        have hXunit : j = q ∨ ∑ i, (|x i| / qNorm q x) ^ q = 1 :=
          Or.inr (qNorm_normalized_sum_eq_one q hq x hXpos)
        have hnorm := normalized_mixed_sum_le_one q j hq hj x v
          (qNorm q x) (fun m => qNorm q (v m)) hXpos hVpos hXunit hVunit
        have hscale := mixed_sum_scale_identity q j hj x v
          (qNorm q x) (fun m => qNorm q (v m)) hXpos hVpos
        have hscaleNonneg : 0 ≤ qNorm q x ^ (q - j) * ∏ m, qNorm q (v m) :=
          mul_nonneg (pow_nonneg (qNorm_nonneg q x) (q - j))
            (Finset.prod_nonneg fun m hm => qNorm_nonneg q (v m))
        simpa only [mul_one] using hscale.trans_le
          (mul_le_mul_of_nonneg_left hnorm hscaleNonneg)

private theorem coord_power_iteratedFDeriv (q j : ℕ) (hj : j ≤ q)
    (x : ι → ℝ) (i : ι) (v : Fin j → ι → ℝ) :
    (iteratedFDeriv ℝ j (fun y : ι → ℝ => y i ^ q) x) v =
      (q.descFactorial j : ℝ) * x i ^ (q - j) * ∏ m : Fin j, v m i := by
  let p : (ι → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hj' : (j : ℕ∞ω) ≤ q := by exact_mod_cast hj
  have hp := p.iteratedFDeriv_comp_right (f := fun t : ℝ => t ^ q)
    (contDiff_id.pow q) x (hi := hj')
  change (iteratedFDeriv ℝ j ((fun t : ℝ => t ^ q) ∘ p) x) v = _
  rw [hp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_pow]
  simp only [p, ContinuousLinearMap.proj_apply]
  ring_nf

/-- The exact j-th continuous multilinear derivative of the finite power sum. -/
theorem iteratedFDeriv_powerSum_apply (q j : ℕ) (hj : j ≤ q)
    (x : ι → ℝ) (v : Fin j → ι → ℝ) :
    (iteratedFDeriv ℝ j (powerSum q) x) v =
      (q.descFactorial j : ℝ) * ∑ i, x i ^ (q - j) * ∏ m : Fin j, v m i := by
  have hcont : ∀ i : ι, ContDiff ℝ q (fun y : ι → ℝ => y i ^ q) := by
    intro i
    have hid : ContDiff ℝ q (fun t : ℝ => t) := contDiff_id
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (hid.pow q).comp_continuousLinearMap
        (g := (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))
  have heq : powerSum q = ∑ i : ι, (fun y : ι → ℝ => y i ^ q) := by
    funext y
    simp [powerSum, Finset.sum_apply]
  have hj' : (j : ℕ∞ω) ≤ q := by exact_mod_cast hj
  have hsum := iteratedFDeriv_sum_apply (𝕜 := ℝ) (x := x) (u := (univ : Finset ι))
    (n := j) (f := fun i y => y i ^ q)
    (fun i hi => (hcont i).contDiffAt.of_le hj')
  rw [heq, hsum]
  simp_rw [ContinuousMultilinearMap.sum_apply, coord_power_iteratedFDeriv q j hj x]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The generalized finite Hölder bound, before replacing the falling factorial by q^j. -/
theorem abs_iteratedFDeriv_powerSum_le_factorial (q j : ℕ) (hq : 0 < q) (hj : j ≤ q)
    (x : ι → ℝ) (v : Fin j → ι → ℝ) :
    |(iteratedFDeriv ℝ j (powerSum q) x) v| ≤
      (q.descFactorial j : ℝ) * qNorm q x ^ (q - j) *
        ∏ m : Fin j, qNorm q (v m) := by
  rw [iteratedFDeriv_powerSum_apply q j hj]
  have hfall : 0 ≤ (q.descFactorial j : ℝ) := Nat.cast_nonneg _
  calc
    |(q.descFactorial j : ℝ) * ∑ i, x i ^ (q - j) * ∏ m : Fin j, v m i| =
        (q.descFactorial j : ℝ) *
          |∑ i, x i ^ (q - j) * ∏ m : Fin j, v m i| := by
            rw [abs_mul, abs_of_nonneg hfall]
    _ ≤ (q.descFactorial j : ℝ) *
          ∑ i, |x i ^ (q - j) * ∏ m : Fin j, v m i| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hfall
    _ = (q.descFactorial j : ℝ) *
          ∑ i, |x i| ^ (q - j) * ∏ m : Fin j, |v m i| := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [abs_mul, abs_pow, Finset.abs_prod]
    _ ≤ (q.descFactorial j : ℝ) *
          (qNorm q x ^ (q - j) * ∏ m : Fin j, qNorm q (v m)) :=
          mul_le_mul_of_nonneg_left (mixed_sum_holder q j hq hj x v) hfall
    _ = (q.descFactorial j : ℝ) * qNorm q x ^ (q - j) *
          ∏ m : Fin j, qNorm q (v m) := by ring

/-- The dimension-free q-norm estimate, including the falling-factorial and q^j bounds. -/
theorem abs_iteratedFDeriv_powerSum_le (q j : ℕ) (hqeven : Even q) (hq : 2 ≤ q)
    (hjpos : 1 ≤ j) (hj : j ≤ q) (x : ι → ℝ) (v : Fin j → ι → ℝ) :
    |(iteratedFDeriv ℝ j (powerSum q) x) v| ≤
      (q.descFactorial j : ℝ) * qNorm q x ^ (q - j) *
        ∏ m : Fin j, qNorm q (v m) ∧
      |(iteratedFDeriv ℝ j (powerSum q) x) v| ≤
        (q : ℝ) ^ j * qNorm q x ^ (q - j) *
          ∏ m : Fin j, qNorm q (v m) := by
  have hfact := abs_iteratedFDeriv_powerSum_le_factorial q j (by omega) hj x v
  have hcoeff : (q.descFactorial j : ℝ) ≤ (q : ℝ) ^ j := by
    exact_mod_cast Nat.descFactorial_le_pow q j
  have hbound : 0 ≤ qNorm q x ^ (q - j) * ∏ m : Fin j, qNorm q (v m) :=
    mul_nonneg (pow_nonneg (qNorm_nonneg q x) _)
      (Finset.prod_nonneg fun m hm => qNorm_nonneg q (v m))
  refine ⟨hfact, ?_⟩
  calc
    |(iteratedFDeriv ℝ j (powerSum q) x) v| ≤
        (q.descFactorial j : ℝ) * qNorm q x ^ (q - j) *
          ∏ m : Fin j, qNorm q (v m) := hfact
    _ ≤ (q : ℝ) ^ j * qNorm q x ^ (q - j) *
          ∏ m : Fin j, qNorm q (v m) := by
          calc
            ((q.descFactorial j : ℝ) * qNorm q x ^ (q - j)) *
                ∏ m : Fin j, qNorm q (v m) =
                (q.descFactorial j : ℝ) *
                  (qNorm q x ^ (q - j) * ∏ m : Fin j, qNorm q (v m)) := by ring
            _ ≤ (q : ℝ) ^ j *
                  (qNorm q x ^ (q - j) * ∏ m : Fin j, qNorm q (v m)) :=
                mul_le_mul_of_nonneg_right hcoeff hbound
            _ = ((q : ℝ) ^ j * qNorm q x ^ (q - j)) *
                  ∏ m : Fin j, qNorm q (v m) := by ring

/-- A nonzero coordinate witness with another coordinate equal to zero. -/
theorem nonzero_zero_coordinate_witness (q j : ℕ) (hqeven : Even q)
    (hq : 2 ≤ q) (hjpos : 1 ≤ j) (hj : j ≤ q) :
    (iteratedFDeriv ℝ j (powerSum q : (Fin 2 → ℝ) → ℝ)
      (fun i => if i = 0 then 1 else 0))
      (fun _ i => if i = 0 then 1 else 0) ≠ 0 := by
  rw [iteratedFDeriv_powerSum_apply q j hj]
  have hjne : j ≠ 0 := by omega
  apply mul_ne_zero
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hj))
  · simp [Fin.sum_univ_two, hjne]

end RBM.Gauss.PowerSumHigherDerivatives
