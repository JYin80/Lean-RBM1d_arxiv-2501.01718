/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PowerSumHigherDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Higher derivatives of the outer smooth-norm power

This file composes the accepted all-order derivative estimate for the finite even power sum
with the scalar fractional-power derivative. It treats both the norm and its reciprocal away
from the origin, including vectors with zero coordinates.
-/

noncomputable section

open Finset Real
open scoped ContDiff

namespace RBM.Gauss.SmoothNormOuterHigherDerivatives

open RBM.Gauss.PowerSumHigherDerivatives

variable {ι : Type*} [Fintype ι]

/-- The `s`-th smooth-norm power, written as a scalar power of the even power sum. -/
def smoothNormPower (q : ℕ) (s : ℤ) (x : ι → ℝ) : ℝ :=
  (powerSum q x) ^ ((s : ℝ) / (q : ℝ))

/-- A dimension-free explicit constant: the weighted number of ordered set partitions. -/
def outerDerivativeConstant (k : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition k, (Nat.factorial c.length : ℝ)

theorem powerSum_eq_qNorm_pow (q : ℕ) (hqeven : Even q) (hq : 2 ≤ q)
    (x : ι → ℝ) :
    powerSum q x = qNorm q x ^ q := by
  rw [qNorm_pow q (by omega) x]
  unfold powerSum
  apply Finset.sum_congr rfl
  intro i hi
  exact (hqeven.pow_abs (x i)).symm

theorem powerSum_pos_of_ne_zero (q : ℕ) (hqeven : Even q) (hq : 2 ≤ q)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < powerSum q x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hx
    funext i
    exact h i
  have hiPos : 0 < x i ^ q := by
    rw [← hqeven.pow_abs]
    exact pow_pos (abs_pos.mpr hi) q
  unfold powerSum
  exact lt_of_lt_of_le hiPos (Finset.single_le_sum (fun j hj => hqeven.pow_nonneg (x j)) (Finset.mem_univ i))

theorem qNorm_pos_of_ne_zero (q : ℕ) (hqeven : Even q) (hq : 2 ≤ q)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < qNorm q x := by
  have hp : 0 < powerSum q x := powerSum_pos_of_ne_zero q hqeven hq hx
  rw [powerSum_eq_qNorm_pow q hqeven hq] at hp
  by_contra hnot
  have hzero : qNorm q x = 0 := le_antisymm (le_of_not_gt hnot) (qNorm_nonneg q x)
  rw [hzero] at hp
  have hq0 : q ≠ 0 := by omega
  simp [hq0] at hp

theorem smoothNormPower_contDiffAt (q : ℕ) (s : ℤ) (n : ℕ∞ω)
    (x : ι → ℝ) (hqeven : Even q) (hq : 2 ≤ q) (hx : x ≠ 0) :
    ContDiffAt ℝ n (smoothNormPower q s) x := by
  have hp : powerSum q x ≠ 0 := (powerSum_pos_of_ne_zero q hqeven hq hx).ne'
  have hP : ContDiff ℝ n (powerSum q : (ι → ℝ) → ℝ) := by
    change ContDiff ℝ n (fun y : ι → ℝ => ∑ i, y i ^ q)
    exact ContDiff.sum (s := Finset.univ) (fun i hi => by fun_prop)
  exact (Real.contDiffAt_rpow_const_of_ne hp).comp x hP.contDiffAt

theorem smoothNormPower_eq_qNorm_rpow (q : ℕ) (s : ℤ) (x : ι → ℝ)
    (hqeven : Even q) (hq : 2 ≤ q) (hx : x ≠ 0) :
    smoothNormPower q s x = qNorm q x ^ (s : ℝ) := by
  rw [smoothNormPower, powerSum_eq_qNorm_pow q hqeven hq]
  have hxq : 0 < qNorm q x := qNorm_pos_of_ne_zero q hqeven hq hx
  rw [← Real.rpow_natCast, ← Real.rpow_mul hxq.le]
  congr 1
  field_simp

private theorem outerCoefficient_bound (q p : ℕ) (s : ℤ)
    (hq : 2 ≤ q) (hs : s = 1 ∨ s = -1) (hp : 1 ≤ p) :
    |(descPochhammer ℝ p).eval ((s : ℝ) / (q : ℝ))| ≤
      (Nat.factorial p : ℝ) / (q : ℝ) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqhalf : (1 : ℝ) / (q : ℝ) ≤ 1 := by
    rw [div_le_one hqpos]
    exact_mod_cast (show 1 ≤ q by omega)
  have hsmall : |(s : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) := by
    rcases hs with hs | hs
    · subst s
      rw [Int.cast_one, abs_of_pos (one_div_pos.mpr hqpos)]
    · subst s
      rw [Int.cast_neg, Int.cast_one, neg_div, abs_neg,
        abs_of_pos (one_div_pos.mpr hqpos)]
  have hfactor (n : ℕ) :
      |(s : ℝ) / (q : ℝ) - (n : ℝ)| ≤ (n : ℝ) + 1 := by
    calc
      |(s : ℝ) / (q : ℝ) - (n : ℝ)| ≤ |(s : ℝ) / (q : ℝ)| + |(n : ℝ)| := abs_sub _ _
      _ ≤ 1 / (q : ℝ) + (n : ℝ) := by
        rw [abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
        nlinarith [hsmall]
      _ ≤ (n : ℝ) + 1 := by nlinarith [hqhalf]
  have hind : ∀ n : ℕ, 1 ≤ n →
      |(descPochhammer ℝ n).eval ((s : ℝ) / (q : ℝ))| ≤ (Nat.factorial n : ℝ) / (q : ℝ) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp only [descPochhammer_succ_eval, descPochhammer_zero, Polynomial.eval_one,
          Nat.factorial_one, Nat.cast_one]
        simpa using hsmall
      · have hnpos : 1 ≤ n := by omega
        have hi := ih hnpos
        rw [descPochhammer_succ_eval]
        calc
          |(descPochhammer ℝ n).eval ((s : ℝ) / (q : ℝ)) *
              ((s : ℝ) / (q : ℝ) - (n : ℝ))|
              = |(descPochhammer ℝ n).eval ((s : ℝ) / (q : ℝ))| *
                |(s : ℝ) / (q : ℝ) - (n : ℝ)| := abs_mul _ _
          _ ≤ ((Nat.factorial n : ℝ) / (q : ℝ)) * ((n : ℝ) + 1) :=
            mul_le_mul hi (hfactor n) (abs_nonneg _) (by positivity)
          _ = (Nat.factorial (n + 1) : ℝ) / (q : ℝ) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
  exact hind p hp

private theorem sum_partSize_eq {k : ℕ} (c : OrderedFinpartition k) :
    ∑ m : Fin c.length, c.partSize m = k := by
  have hcard := Fintype.card_congr c.equivSigma
  simpa using hcard

private theorem outer_iteratedDeriv_bound (q p : ℕ) (s : ℤ) (x : ι → ℝ)
    (hqeven : Even q) (hq : 2 ≤ q) (hs : s = 1 ∨ s = -1) (hp : 1 ≤ p)
    (hx : x ≠ 0) :
    |iteratedDeriv p (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) (powerSum q x)| ≤
      (Nat.factorial p : ℝ) / (q : ℝ) *
        qNorm q x ^ ((s : ℝ) - (p : ℝ) * (q : ℝ)) := by
  have hP : 0 < powerSum q x := powerSum_pos_of_ne_zero q hqeven hq hx
  have hA : 0 < qNorm q x := qNorm_pos_of_ne_zero q hqeven hq hx
  have hpow :
      (powerSum q x) ^ ((s : ℝ) / (q : ℝ) - (p : ℝ)) =
        qNorm q x ^ ((s : ℝ) - (p : ℝ) * (q : ℝ)) := by
    rw [powerSum_eq_qNorm_pow q hqeven hq]
    rw [← Real.rpow_natCast (qNorm q x) q]
    rw [← Real.rpow_mul hA.le]
    congr 1
    field_simp
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hP _), hpow]
  exact mul_le_mul_of_nonneg_right
    (outerCoefficient_bound q p s hq hs hp)
    (Real.rpow_nonneg (qNorm_nonneg q _) _)

private theorem orderedPartition_inner_product_bound (q k : ℕ)
    (c : OrderedFinpartition k) (x : ι → ℝ) (v : Fin k → ι → ℝ)
    (hqeven : Even q) (hq : 2 ≤ q) (hkpos : 1 ≤ k) (hkq : k ≤ q)
    (hx : x ≠ 0) :
    (∏ m : Fin c.length,
        |(iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
          (fun r => v (c.emb m r))|) ≤
      (q : ℝ) ^ k * qNorm q x ^ (c.length * q - k) *
        ∏ j : Fin k, qNorm q (v j) := by
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hA : 0 ≤ qNorm q x := qNorm_nonneg q x
  have hlen : 1 ≤ c.length := c.length_pos hkpos
  have hkpq : k ≤ c.length * q := by
    exact le_trans hkq (by simpa using Nat.mul_le_mul_right q hlen)
  have hpartsCast :
      (∑ m : Fin c.length, (c.partSize m : ℝ)) = (k : ℝ) := by
    exact_mod_cast sum_partSize_eq c
  have hsize (m : Fin c.length) : c.partSize m ≤ q :=
    le_trans (OrderedFinpartition.partSize_le c m) hkq
  have hblock (m : Fin c.length) :
      |(iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
        (fun r => v (c.emb m r))| ≤
        (q : ℝ) ^ (c.partSize m) * qNorm q x ^ (q - c.partSize m) *
          ∏ r : Fin (c.partSize m), qNorm q (v (c.emb m r)) := by
    have hj : 1 ≤ c.partSize m := OrderedFinpartition.partSize_pos c m
    exact (abs_iteratedFDeriv_powerSum_le q (c.partSize m) hqeven hq hj
      (hsize m) x (fun r => v (c.emb m r))).2
  have hqprod :
      (∏ m : Fin c.length, (q : ℝ) ^ (c.partSize m)) = (q : ℝ) ^ k := by
    calc
      (∏ m : Fin c.length, (q : ℝ) ^ (c.partSize m)) =
          ∏ m : Fin c.length, (q : ℝ) ^ ((c.partSize m : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro m hm
            exact (Real.rpow_natCast (q : ℝ) (c.partSize m)).symm
      _ = (q : ℝ) ^ (∑ m : Fin c.length, (c.partSize m : ℕ) : ℝ) := by
            rw [← Real.rpow_sum_of_pos hqpos (fun m : Fin c.length => (c.partSize m : ℝ))
              Finset.univ]
      _ = (q : ℝ) ^ k := by
            rw [hpartsCast]
            exact Real.rpow_natCast (q : ℝ) k
  have hAsum :
      (∑ m : Fin c.length, ((q - c.partSize m : ℕ) : ℝ)) =
        (c.length : ℝ) * (q : ℝ) - (k : ℝ) := by
    calc
      (∑ m : Fin c.length, ((q - c.partSize m : ℕ) : ℝ)) =
          ∑ m : Fin c.length, ((q : ℝ) - (c.partSize m : ℝ)) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Nat.cast_sub (hsize m)]
      _ = (c.length : ℝ) * (q : ℝ) - (k : ℝ) := by
            rw [Finset.sum_sub_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, hpartsCast]
  have hAprod :
      (∏ m : Fin c.length, qNorm q x ^ (q - c.partSize m)) =
        qNorm q x ^ (c.length * q - k) := by
    calc
      (∏ m : Fin c.length, qNorm q x ^ (q - c.partSize m)) =
          ∏ m : Fin c.length, qNorm q x ^ ((q - c.partSize m : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro m hm
            exact (Real.rpow_natCast (qNorm q x) (q - c.partSize m)).symm
      _ = qNorm q x ^ (∑ m : Fin c.length, ((q - c.partSize m : ℕ) : ℝ)) := by
            rw [← Real.rpow_sum_of_pos
              (qNorm_pos_of_ne_zero q hqeven hq hx)
              (fun m : Fin c.length => ((q - c.partSize m : ℕ) : ℝ)) Finset.univ]
      _ = qNorm q x ^ (c.length * q - k) := by
            rw [hAsum]
            have hexp :
                (c.length : ℝ) * (q : ℝ) - (k : ℝ) =
                  ((c.length * q - k : ℕ) : ℝ) := by
              rw [Nat.cast_sub hkpq, Nat.cast_mul]
            rw [hexp, Real.rpow_natCast]
  have hnormprod :
      (∏ m : Fin c.length, ∏ r : Fin (c.partSize m),
        qNorm q (v (c.emb m r))) = ∏ j : Fin k, qNorm q (v j) :=
    c.prod_sigma_eq_prod (fun j => qNorm q (v j))
  have hprod :
      (∏ m : Fin c.length,
        |(iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
          (fun r => v (c.emb m r))|) ≤
        ∏ m : Fin c.length,
          ((q : ℝ) ^ (c.partSize m) * qNorm q x ^ (q - c.partSize m) *
            ∏ r : Fin (c.partSize m), qNorm q (v (c.emb m r))) := by
    apply Finset.prod_le_prod₀
    · intro m hm
      exact abs_nonneg _
    · intro m hm
      exact hblock m
  calc
    (∏ m : Fin c.length,
        |(iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
          (fun r => v (c.emb m r))|) ≤
        ∏ m : Fin c.length,
          ((q : ℝ) ^ (c.partSize m) * qNorm q x ^ (q - c.partSize m) *
            ∏ r : Fin (c.partSize m), qNorm q (v (c.emb m r))) := hprod
    _ = (∏ m : Fin c.length, (q : ℝ) ^ (c.partSize m)) *
          (∏ m : Fin c.length, qNorm q x ^ (q - c.partSize m)) *
          (∏ m : Fin c.length, ∏ r : Fin (c.partSize m),
            qNorm q (v (c.emb m r))) := by
          simp_rw [mul_assoc]
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = (q : ℝ) ^ k * qNorm q x ^ (c.length * q - k) *
          ∏ j : Fin k, qNorm q (v j) := by rw [hqprod, hAprod, hnormprod]

private theorem iteratedFDeriv_smoothNormPower_apply_eq_sum (q k : ℕ) (s : ℤ)
    (x : ι → ℝ) (v : Fin k → ι → ℝ)
    (hqeven : Even q) (hq : 2 ≤ q) (hx : x ≠ 0) :
    (iteratedFDeriv ℝ k (smoothNormPower q s) x) v =
      ∑ c : OrderedFinpartition k,
        (∏ m : Fin c.length,
          (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
            (fun r => v (c.emb m r))) *
          iteratedDeriv c.length
            (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) (powerSum q x) := by
  have hP : ContDiff ℝ k (powerSum q : (ι → ℝ) → ℝ) := by
    change ContDiff ℝ k (fun y : ι → ℝ => ∑ i, y i ^ q)
    exact ContDiff.sum (s := Finset.univ) (fun i hi => by fun_prop)
  have houter : ContDiffAt ℝ k
      (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) (powerSum q x) :=
    Real.contDiffAt_rpow_const_of_ne
      (powerSum_pos_of_ne_zero q hqeven hq hx).ne'
  have hcomp := iteratedFDeriv_comp houter hP.contDiffAt (i := k) le_rfl
  have hcoeff (n : ℕ) :
      (ftaylorSeries ℝ (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
        (powerSum q x)).coeff n =
        iteratedDeriv n (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) (powerSum q x) := by
    change (iteratedFDeriv ℝ n (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
      (powerSum q x)) (1 : Fin n → ℝ) = _
    rw [iteratedDeriv_eq_iteratedFDeriv]
    congr 1
  change (iteratedFDeriv ℝ k
    ((fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) ∘
      (powerSum q : (ι → ℝ) → ℝ)) x) v = _
  rw [hcomp]
  simp [FormalMultilinearSeries.taylorComp,
    OrderedFinpartition.compAlongOrderedFinpartition,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  simp only [hcoeff]
  simp only [ftaylorSeries]
  apply Finset.sum_congr rfl
  intro c hc
  congr 2

/-- All-order, dimension-free derivative bound for both the norm and reciprocal powers. -/
theorem abs_iteratedFDeriv_smoothNormPower_le (M q k : ℕ) (s : ℤ)
    (hqeven : Even q) (hqM : max 2 (4 * M) ≤ q)
    (hkpos : 1 ≤ k) (hkle : k ≤ M) (hs : s = 1 ∨ s = -1)
    (x : ι → ℝ) (hx : x ≠ 0) (v : Fin k → ι → ℝ) :
    |(iteratedFDeriv ℝ k (smoothNormPower q s) x) v| ≤
      outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
        qNorm q x ^ ((s : ℝ) - (k : ℝ)) *
          ∏ j : Fin k, qNorm q (v j) := by
  have hq2 : 2 ≤ q := le_trans (le_max_left 2 (4 * M)) hqM
  have hMq : M ≤ q := by
    calc
      M ≤ 4 * M := by omega
      _ ≤ q := le_trans (le_max_right 2 (4 * M)) hqM
  have hkq : k ≤ q := le_trans hkle hMq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hA : 0 < qNorm q x := qNorm_pos_of_ne_zero q hqeven hq2 hx
  let B : ℝ := (q : ℝ) ^ (k - 1) *
    qNorm q x ^ ((s : ℝ) - (k : ℝ)) *
      ∏ j : Fin k, qNorm q (v j)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (by positivity) _
      · exact Real.rpow_nonneg hA.le _
    · exact Finset.prod_nonneg fun j hj => qNorm_nonneg q (v j)
  have hqFactor (p : ℕ) :
      (Nat.factorial p : ℝ) / (q : ℝ) * (q : ℝ) ^ k =
        (Nat.factorial p : ℝ) * (q : ℝ) ^ (k - 1) := by
    have hkEq : k = (k - 1) + 1 := by omega
    have hpow : (q : ℝ) ^ k = (q : ℝ) ^ (k - 1) * (q : ℝ) := by
      conv_lhs => rw [hkEq]
      rw [pow_succ]
    calc
      (Nat.factorial p : ℝ) / (q : ℝ) * (q : ℝ) ^ k =
          (Nat.factorial p : ℝ) / (q : ℝ) *
            ((q : ℝ) ^ (k - 1) * (q : ℝ)) := by rw [hpow]
      _ = (Nat.factorial p : ℝ) * (q : ℝ) ^ (k - 1) := by
            field_simp [hqpos.ne']
  have hnormFactor (p : ℕ) (hpq : k ≤ p * q) :
      qNorm q x ^ (p * q - k) * qNorm q x ^ ((s : ℝ) - (p : ℝ) * (q : ℝ)) =
        qNorm q x ^ ((s : ℝ) - (k : ℝ)) := by
    have hexp : ((p * q - k : ℕ) : ℝ) +
        ((s : ℝ) - (p : ℝ) * (q : ℝ)) = (s : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hpq, Nat.cast_mul]
      ring
    rw [← Real.rpow_natCast (qNorm q x) (p * q - k)]
    rw [← Real.rpow_add hA]
    rw [hexp]
  have hterm (c : OrderedFinpartition k) :
      |((∏ m : Fin c.length,
          (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
            (fun r => v (c.emb m r))) *
        iteratedDeriv c.length (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
          (powerSum q x))| ≤ (Nat.factorial c.length : ℝ) * B := by
    have hp : 1 ≤ c.length := c.length_pos hkpos
    have hpq : k ≤ c.length * q := by
      exact le_trans hkq (by simpa using Nat.mul_le_mul_right q hp)
    have hinner := orderedPartition_inner_product_bound q k c x v
      hqeven hq2 hkpos hkq hx
    have houter := outer_iteratedDeriv_bound q c.length s x
      hqeven hq2 hs hp hx
    have hinnerAbs :
        |∏ m : Fin c.length,
          (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
            (fun r => v (c.emb m r))| =
          ∏ m : Fin c.length,
            |(iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
              (fun r => v (c.emb m r))| := by
      exact Finset.abs_prod _ _
    have hinnerNonneg :
        0 ≤ (q : ℝ) ^ k * qNorm q x ^ (c.length * q - k) *
          ∏ j : Fin k, qNorm q (v j) := by
      apply mul_nonneg
      · apply mul_nonneg
        · exact pow_nonneg (by positivity) _
        · exact pow_nonneg (qNorm_nonneg q x) _
      · exact Finset.prod_nonneg fun j hj => qNorm_nonneg q (v j)
    calc
      |((∏ m : Fin c.length,
          (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
            (fun r => v (c.emb m r))) *
        iteratedDeriv c.length (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
          (powerSum q x))|
          = |∏ m : Fin c.length,
              (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
                (fun r => v (c.emb m r))| *
            |iteratedDeriv c.length (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
              (powerSum q x)| := abs_mul _ _
      _ ≤ ((q : ℝ) ^ k * qNorm q x ^ (c.length * q - k) *
            ∏ j : Fin k, qNorm q (v j)) *
          ((Nat.factorial c.length : ℝ) / (q : ℝ) *
            qNorm q x ^ ((s : ℝ) - (c.length : ℝ) * (q : ℝ))) := by
          rw [hinnerAbs]
          exact mul_le_mul hinner houter (abs_nonneg _) hinnerNonneg
      _ = (Nat.factorial c.length : ℝ) * B := by
          calc
            _ = ((Nat.factorial c.length : ℝ) / (q : ℝ) * (q : ℝ) ^ k) *
                (qNorm q x ^ (c.length * q - k) *
                  qNorm q x ^ ((s : ℝ) - (c.length : ℝ) * (q : ℝ))) *
                ∏ j : Fin k, qNorm q (v j) := by ring
            _ = (Nat.factorial c.length : ℝ) * B := by
                rw [hqFactor c.length, hnormFactor c.length hpq]
                dsimp [B]
                ring
  calc
    |(iteratedFDeriv ℝ k (smoothNormPower q s) x) v| =
        |∑ c : OrderedFinpartition k,
          (∏ m : Fin c.length,
            (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
              (fun r => v (c.emb m r))) *
            iteratedDeriv c.length (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
              (powerSum q x)| := by
          rw [iteratedFDeriv_smoothNormPower_apply_eq_sum q k s x v hqeven hq2 hx]
    _ ≤ ∑ c : OrderedFinpartition k,
        |(∏ m : Fin c.length,
          (iteratedFDeriv ℝ (c.partSize m) (powerSum q) x)
            (fun r => v (c.emb m r))) *
          iteratedDeriv c.length (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
            (powerSum q x)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : OrderedFinpartition k, (Nat.factorial c.length : ℝ) * B :=
        Finset.sum_le_sum fun c hc => hterm c
    _ = (∑ c : OrderedFinpartition k, (Nat.factorial c.length : ℝ)) * B := by
        rw [Finset.sum_mul]
    _ = outerDerivativeConstant k * B := rfl
    _ = outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
        qNorm q x ^ ((s : ℝ) - (k : ℝ)) *
          ∏ j : Fin k, qNorm q (v j) := by
        dsimp [B]
        ring

/-- The same `(1, 0)` point has a nonzero first derivative and a zero coordinate. -/
theorem fin2_smoothNormPower_first_derivative_witness (q : ℕ) (s : ℤ)
    (_hqeven : Even q) (hq : 2 ≤ q) (hs : s = 1 ∨ s = -1) :
    (fun i : Fin 2 => if i = 0 then 1 else 0) 0 = 1 ∧
    (fun i : Fin 2 => if i = 0 then 1 else 0) 1 = 0 ∧
    (iteratedFDeriv ℝ 1 (smoothNormPower q s : (Fin 2 → ℝ) → ℝ)
      (fun i => if i = 0 then 1 else 0))
      (fun _ i => if i = 0 then 1 else 0) ≠ 0 := by
  constructor
  · norm_num
  constructor
  · norm_num
  let x : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let v : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  have hq0 : q ≠ 0 := by omega
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [x] at h0
  have hPx : powerSum q x = 1 := by
    simp [powerSum, x, Fin.sum_univ_two, hq0]
  have hPdiff : DifferentiableAt ℝ (powerSum q : (Fin 2 → ℝ) → ℝ) x := by
    have hcont : ContDiff ℝ 1 (powerSum q : (Fin 2 → ℝ) → ℝ) := by
      change ContDiff ℝ 1 (fun y : Fin 2 → ℝ => ∑ i, y i ^ q)
      exact ContDiff.sum (s := Finset.univ) (fun i hi => by fun_prop)
    exact hcont.contDiffAt.differentiableAt (by norm_num)
  have houterDiff :
      DifferentiableAt ℝ (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) (powerSum q x) := by
    have hPne : powerSum q x ≠ 0 := by rw [hPx]; norm_num
    exact (Real.contDiffAt_rpow_const_of_ne (x := powerSum q x)
      (p := (s : ℝ) / (q : ℝ)) (n := (1 : ℕ∞ω)) hPne).differentiableAt (by norm_num)
  have hinner : (fderiv ℝ (powerSum q) x) v = (q : ℝ) := by
    have hformula :
        (iteratedFDeriv ℝ 1 (powerSum q) x) (fun _ : Fin 1 => v) = (q : ℝ) := by
      rw [iteratedFDeriv_powerSum_apply q 1 (by omega)]
      simp [powerSum, x, v, Fin.sum_univ_two, hq0]
    simpa only [iteratedFDeriv_one_apply] using hformula
  have houter :
      deriv (fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) 1 = (s : ℝ) / (q : ℝ) := by
    rw [Real.deriv_rpow_const]
    simp
  have hcomp := fderiv_comp (f := powerSum q) (g := fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ)))
    (x := x) houterDiff hPdiff
  have hderiv :
      (fderiv ℝ (smoothNormPower q s) x) v = (s : ℝ) := by
    change (fderiv ℝ
      ((fun y : ℝ => y ^ ((s : ℝ) / (q : ℝ))) ∘ powerSum q) x) v = _
    rw [hcomp, ContinuousLinearMap.comp_apply, hPx, fderiv_eq_deriv_mul,
      houter, hinner]
    field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq0]
  rw [iteratedFDeriv_one_apply]
  change (fderiv ℝ (smoothNormPower q s) x) v ≠ 0
  rw [hderiv]
  rcases hs with hs | hs <;> simp [hs]

end RBM.Gauss.SmoothNormOuterHigherDerivatives
