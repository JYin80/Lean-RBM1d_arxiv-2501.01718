/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Dist
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sums on the cycle `ZMod L`

Shared summation tools, used by `Propagator/Edges.lean` (the `ℓ¹` bounds (3.36)) and
`Loop/Cor35.lean` (Corollary 3.5), and collected here so that each is proved once:

* `sum_zmod_val` : `∑_{u : ZMod L} f(u.val) = ∑_{v < L} f v`
* `sum_pow_val_le`, `sum_pow_sub_val_le`, `sum_pow_zdist_le` : geometric sums, uniformly in `L`
* `zdist_neg` : the cycle distance is even
* `one_sub_exp_neg_ge`, `sum_exp_neg_zdist_le`, `sum_exp_zdist_le` : exponential decay of
  length `1/λ` sums to `O(1/λ)`

Only `Defs/Dist.lean` (`zdist`) is used.
-/

namespace RBM

open Finset

section Sums

variable (L : ℕ) [NeZero L]

/-- `ZMod.val` identifies `ZMod L` with `Finset.range L`. -/
theorem image_val_eq_range :
    (Finset.univ : Finset (ZMod L)).image ZMod.val = Finset.range L := by
  refine Finset.eq_of_subset_of_card_le (fun v hv => ?_) ?_
  · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_range.mpr (ZMod.val_lt u)
  · rw [Finset.card_range, Finset.card_image_of_injective _ (ZMod.val_injective L),
      Finset.card_univ, ZMod.card]

theorem sum_zmod_val (f : ℕ → ℝ) :
    ∑ u : ZMod L, f u.val = ∑ v ∈ Finset.range L, f v := by
  rw [← image_val_eq_range L,
    Finset.sum_image (fun a _ b _ h => ZMod.val_injective L h)]

/-- The distance on the cycle is even: `‖-u‖ = ‖u‖`. -/
theorem zdist_neg (u : ZMod L) : zdist L (-u) = zdist L u := by
  have hu := ZMod.val_lt u
  rw [zdist, zdist, ZMod.neg_val]
  split_ifs with h
  · subst h; simp
  · omega

theorem geom_sum_range_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ v ∈ Finset.range n, r ^ v ≤ (1 - r)⁻¹ := by
  rw [range_eq_Ico]
  simpa using geom_sum_Ico_le_of_lt_one hr0 hr1 (m := 0) (n := n)

/-- A geometric sum over `ZMod L`, indexed by `val`. -/
theorem sum_pow_val_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ u.val ≤ (1 - r)⁻¹ := by
  rw [sum_zmod_val L fun v => r ^ v]
  exact geom_sum_range_le hr0 hr1 L

/-- The same sum with the reflected exponent `L - val`. -/
theorem sum_pow_sub_val_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ (L - u.val) ≤ (1 - r)⁻¹ := by
  rw [sum_zmod_val L fun v => r ^ (L - v)]
  have hstep : ∀ v ∈ Finset.range L, r ^ (L - v) ≤ r ^ (L - 1 - v) := by
    intro v hv
    exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_range_reflect (fun v => r ^ v) L]
  exact geom_sum_range_le hr0 hr1 L

omit [NeZero L] in
/-- The key splitting: a function of the cycle distance is bounded by the sum of the two
one-sided terms, because the distance is one of them and both are nonnegative. -/
theorem pow_zdist_le_add {r : ℝ} (hr0 : 0 ≤ r) (u : ZMod L) :
    r ^ zdist L u ≤ r ^ u.val + r ^ (L - u.val) := by
  rcases min_cases u.val (L - u.val) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    · rw [zdist, h]
      have h1 : (0 : ℝ) ≤ r ^ u.val := by positivity
      have h2 : (0 : ℝ) ≤ r ^ (L - u.val) := by positivity
      linarith

/-- `∑_u r^{‖u‖} ≤ 2/(1-r)` on the cycle, uniformly in `L`. -/
theorem sum_pow_zdist_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ u : ZMod L, r ^ zdist L u ≤ 2 * (1 - r)⁻¹ := by
  have h1 : ∑ u : ZMod L, r ^ zdist L u
      ≤ ∑ u : ZMod L, (r ^ u.val + r ^ (L - u.val)) :=
    Finset.sum_le_sum fun u _ => pow_zdist_le_add L hr0 u
  rw [Finset.sum_add_distrib] at h1
  have h2 := sum_pow_val_le L hr0 hr1
  have h3 := sum_pow_sub_val_le L hr0 hr1
  linarith

/-- `1/(1 - e^{-λ}) ≤ (1 + λ)/λ`, the elementary bound behind summing an exponential
decay of length `1/λ`. -/
theorem one_sub_exp_neg_ge {lam : ℝ} (hlam : 0 < lam) :
    lam / (1 + lam) ≤ 1 - Real.exp (-lam) := by
  have hexp : (1 : ℝ) + lam ≤ Real.exp lam := by
    have := Real.add_one_le_exp lam; linarith
  have hpos : 0 < Real.exp lam := Real.exp_pos _
  have hkey : (1 + lam) * Real.exp (-lam) ≤ 1 := by
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ hpos]
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith [hkey]

/-- `∑_u e^{-λ‖u‖} ≤ 2(1+λ)/λ` on the cycle: an exponential of decay length `1/λ`
sums to `O(1/λ)`, uniformly in `L`. -/
theorem sum_exp_neg_zdist_le {lam : ℝ} (hlam : 0 < lam) :
    ∑ u : ZMod L, Real.exp (-(lam * (zdist L u : ℝ))) ≤ 2 * ((1 + lam) / lam) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-lam) := (Real.exp_pos _).le
  have hr1 : Real.exp (-lam) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hterm : ∀ u : ZMod L,
      Real.exp (-(lam * (zdist L u : ℝ))) = Real.exp (-lam) ^ zdist L u := by
    intro u
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [hterm]
  refine (sum_pow_zdist_le L hr0 hr1).trans ?_
  have h1 : lam / (1 + lam) ≤ 1 - Real.exp (-lam) := one_sub_exp_neg_ge hlam
  have h2 : 0 < lam / (1 + lam) := by positivity
  have key : (1 - Real.exp (-lam))⁻¹ ≤ (1 + lam) / lam := by
    calc (1 - Real.exp (-lam))⁻¹ = 1 / (1 - Real.exp (-lam)) := by rw [inv_eq_one_div]
      _ ≤ 1 / (lam / (1 + lam)) := one_div_le_one_div_of_le h2 h1
      _ = (1 + lam) / lam := by rw [one_div_div]
  linarith

/-- The shifted form: `∑_x e^{-λ‖x - c‖} ≤ 2/(1 - e^{-λ})`, uniformly in `L` and `c`. -/
theorem sum_exp_zdist_le {lam : ℝ} (hlam : 0 < lam) (c : ZMod L) :
    ∑ x : ZMod L, Real.exp (-(lam * zdist L (x - c))) ≤ 2 / (1 - Real.exp (-lam)) := by
  have hr1 : Real.exp (-lam) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have e : ∀ x : ZMod L,
      Real.exp (-(lam * zdist L (x - c))) = Real.exp (-lam) ^ zdist L (x - c) := by
    intro x; rw [← Real.exp_nat_mul]; congr 1; ring
  simp_rw [e]
  have h := (Equiv.subRight c).sum_comp (fun u => Real.exp (-lam) ^ zdist L u)
  simp only [Equiv.subRight_apply] at h
  rw [h, div_eq_mul_inv]
  exact sum_pow_zdist_le L (Real.exp_pos _).le hr1

end Sums


section Moved

variable (L : ℕ) [NeZero L]

/-! ### An elementary lower bound for `1 - r^L`

The prefactor of (2.52) is `1/(|1-ξ| ℓ̂)` with `ℓ̂ = min(|1-ξ|^{-1/2}, L)`, and the
`ℓ̂` in it comes entirely from the factor `1 - ρ^L` in `AA_eq`: it interpolates
between `1` (when `L(1-ρ) ≳ 1`) and `L(1-ρ)` (when `L(1-ρ) ≲ 1`).  The
following two lemmas are that interpolation, with no exponentials: Bernoulli
`1 + Lx ≤ (1+x)^L` plus `(1-x)(1+x) ≤ 1` give `(1-x)^L (1 + Lx) ≤ 1`. -/

theorem pow_mul_one_add_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (L : ℕ) :
    (1 - x) ^ L * (1 + L * x) ≤ 1 := by
  have h1 : (1 : ℝ) + L * x ≤ (1 + x) ^ L := one_add_mul_le_pow (by linarith) L
  have h2 : (0 : ℝ) ≤ (1 - x) ^ L := pow_nonneg (by linarith) L
  calc (1 - x) ^ L * (1 + L * x) ≤ (1 - x) ^ L * (1 + x) ^ L :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = ((1 - x) * (1 + x)) ^ L := (mul_pow _ _ _).symm
    _ = (1 - x ^ 2) ^ L := by ring_nf
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- `1 - r^L ≥ L(1-r) / (1 + L(1-r))`.  The right-hand side is `≍ min(1, L(1-r))`. -/
theorem le_one_sub_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (L : ℕ) :
    (L : ℝ) * (1 - r) / (1 + L * (1 - r)) ≤ 1 - r ^ L := by
  have hx0 : (0 : ℝ) ≤ 1 - r := by linarith
  have hd : (0 : ℝ) < 1 + L * (1 - r) := by positivity
  rw [div_le_iff₀ hd]
  have h := pow_mul_one_add_le hx0 (by linarith) L
  have hr : (1 : ℝ) - (1 - r) = r := by ring
  rw [hr] at h
  nlinarith [h]

theorem mul_exp_neg_le_exp_neg_one {x : ℝ} (hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (x - 1)
  have hx' : x ≤ Real.exp (-1) / Real.exp (-x) := by
    rw [← Real.exp_sub]
    have : -1 - -x = x - 1 := by ring
    rw [this]
    linarith
  have hpos : 0 < Real.exp (-x) := Real.exp_pos _
  calc x * Real.exp (-x) ≤ (Real.exp (-1) / Real.exp (-x)) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hx' hpos.le
    _ = Real.exp (-1) := div_mul_cancel₀ _ (ne_of_gt hpos)

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := by
    rw [Real.exp_neg]
  rw [h2]
  rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith

theorem two_mul_zdist_le (u : ZMod L) : 2 * zdist L u ≤ L := by
  have h := ZMod.val_lt u
  rw [zdist]
  rcases le_total u.val (L - u.val) with h' | h'
  · rw [min_eq_left h']; omega
  · rw [min_eq_right h']; omega

end Moved

end RBM
