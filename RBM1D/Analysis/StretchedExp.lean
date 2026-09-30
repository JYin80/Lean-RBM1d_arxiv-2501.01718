/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Sums
import RBM1D.Defs.Domination
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stretched-exponential tail functions

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, the purely real-analytic
ingredients of Section 5.3 (step 2 of the proof of Theorem 2.21) and of (7.12).

The paper measures the off-diagonal decay of the `2`-loops by the tail function (5.27)
`T_{u,D}(ℓ) = (W ℓ_u η_u)^{-2} exp(-(ℓ/ℓ_u)_+^{1/2}) + W^{-D}`.  Everything here is about
this explicit function; no randomness is involved.

## Main definitions

* `RBM.tailT W ℓu ηu D ℓ`   : `T_{u,D}(ℓ)`, (5.27)
* `RBM.ellStar W ℓu`         : `ℓ*_u = (log W)^{3/2} ℓ_u`

## Main results

* `tailT_antitone` : `T_{u,D}` is non-increasing
* `tailT_sub_le` : (5.32), `T_{u,D}(ℓ - C ℓ*_u) ≺ T_{u,D}(ℓ)`, in explicit form (factor
  `exp(√C (log W)^{3/4})`)
* `inv_sq_le_tailT` : the near region `d ≤ C ℓ*_u`, `(W ℓ_u η_u)^{-2} ≺ T_{u,D}(d)`
* `integral_exp_neg_mul_sqrt_le`, `sum_exp_neg_mul_sqrt_zdist_le` : `∫_0^a exp(-k√x) dx ≤ 2/k²`
  and `∑_{u ∈ ZMod L} exp(-k√‖u‖) ≤ 2(1 + 2/k²)`, uniformly in `a` and `L`
* `sum_tailT_mul_tailT_le`, `mul_sum_tailT_mul_tailT_le` : the discrete convolution bound
  behind (5.50) and (5.72)

The constants (`16`, `64`, `36`, …) are explicit and not optimal.
-/

namespace RBM

open Real MeasureTheory Set Filter Topology

/-! ### Elementary square-root inequalities -/

/-- Subadditivity of `√`, with the first argument allowed to be negative (`√` of a negative
number is `0`). -/
theorem sqrt_add_le_add_sqrt (x : ℝ) {s : ℝ} (hs : 0 ≤ s) : √(x + s) ≤ √x + √s := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt' (x := x)
  have h2 := Real.sq_sqrt hs
  have h3 : 0 ≤ √x * √s := by positivity
  nlinarith [le_max_left x 0]

/-- The key inequality behind all the stretched-exponential convolutions:
if `0 ≤ x ≤ y` then `√(x + y) ≤ √y + √x / 2`. -/
theorem sqrt_add_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : √(x + y) ≤ √y + √x / 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 : √x ≤ √y := Real.sqrt_le_sqrt hxy
  have h4 : √x * √x ≤ √x * √y := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg x)
  nlinarith [Real.sqrt_nonneg x]

/-! ### The integrals (5.49) -/

/-- An antiderivative of `exp(-k√x)` on `x > 0`. -/
noncomputable def sqrtExpPrim (k x : ℝ) : ℝ := -(2 / k ^ 2) * ((1 + k * √x) * exp (-(k * √x)))

theorem hasDerivAt_sqrtExpPrim {k x : ℝ} (hk : k ≠ 0) (hx : 0 < x) :
    HasDerivAt (sqrtExpPrim k) (exp (-(k * √x))) x := by
  have hs : 0 < √x := Real.sqrt_pos.2 hx
  have h1 : HasDerivAt (fun y => k * √y) (k * (1 / (2 * √x))) x :=
    (Real.hasDerivAt_sqrt hx.ne').const_mul k
  have h2 : HasDerivAt (fun y => exp (-(k * √y))) (exp (-(k * √x)) * -(k * (1 / (2 * √x)))) x :=
    h1.neg.exp
  have h3 : HasDerivAt (fun y => 1 + k * √y) (k * (1 / (2 * √x))) x := h1.const_add 1
  have h4 : HasDerivAt (fun y => -(2 / k ^ 2) * ((1 + k * √y) * exp (-(k * √y))))
      (-(2 / k ^ 2) * (k * (1 / (2 * √x)) * exp (-(k * √x)) +
        (1 + k * √x) * (exp (-(k * √x)) * -(k * (1 / (2 * √x)))))) x :=
    (h3.mul h2).const_mul _
  refine h4.congr_deriv ?_
  field_simp
  ring

theorem continuous_sqrtExpPrim (k : ℝ) : Continuous (sqrtExpPrim k) := by
  unfold sqrtExpPrim; fun_prop

/-- `∫_0^a exp(-k√x) dx = 2/k² - (2/k²)(1 + k√a) exp(-k√a)`. -/
theorem integral_exp_neg_mul_sqrt {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) :
    ∫ x in (0 : ℝ)..a, exp (-(k * √x)) =
      2 / k ^ 2 - 2 / k ^ 2 * ((1 + k * √a) * exp (-(k * √a))) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha
    (continuous_sqrtExpPrim k).continuousOn (fun x hx => hasDerivAt_sqrtExpPrim hk.ne' hx.1)]
  · simp [sqrtExpPrim]; ring
  · exact (by fun_prop : Continuous fun x => exp (-(k * √x))).intervalIntegrable _ _

/-- `∫_0^a exp(-k√x) dx ≤ 2/k²`, uniformly in `a`. -/
theorem integral_exp_neg_mul_sqrt_le {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) :
    ∫ x in (0 : ℝ)..a, exp (-(k * √x)) ≤ 2 / k ^ 2 := by
  rw [integral_exp_neg_mul_sqrt hk ha]
  have : 0 ≤ 2 / k ^ 2 * ((1 + k * √a) * exp (-(k * √a))) := by positivity
  linarith

/-! ### Stretched-exponential sums on the cycle -/

/-- `∑_{n < N} exp(-k√n) ≤ 1 + 2/k²`, uniformly in `N`. -/
theorem sum_range_exp_neg_mul_sqrt_le {k : ℝ} (hk : 0 < k) (n : ℕ) :
    ∑ i ∈ Finset.range n, exp (-(k * √(i : ℝ))) ≤ 1 + 2 / k ^ 2 := by
  have hanti : Antitone fun x : ℝ => exp (-(k * √x)) := fun x y hxy =>
    exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) hk.le))
  rcases n with _ | m
  · simp only [Finset.range_zero, Finset.sum_empty]; positivity
  · rw [Finset.sum_range_succ']
    have h := (hanti.antitoneOn (Icc (0 : ℝ) (0 + m))).sum_le_integral (x₀ := 0) (a := m)
    simp only [zero_add] at h
    have hint := integral_exp_neg_mul_sqrt_le hk (a := m) (Nat.cast_nonneg m)
    simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, neg_zero, exp_zero]
    have : ∑ i ∈ Finset.range m, exp (-(k * √((i + 1 : ℕ) : ℝ))) ≤ 2 / k ^ 2 :=
      h.trans hint
    push_cast at this ⊢
    linarith

variable (L : ℕ) [NeZero L]

/-- `∑_{u ∈ ZMod L} exp(-k√‖u‖) ≤ 2(1 + 2/k²)`, uniformly in `L`. -/
theorem sum_exp_neg_mul_sqrt_zdist_le {k : ℝ} (hk : 0 < k) :
    ∑ u : ZMod L, exp (-(k * √(zdist L u : ℝ))) ≤ 2 * (1 + 2 / k ^ 2) := by
  set g : ℕ → ℝ := fun n => exp (-(k * √(n : ℝ))) with hg
  have hanti : ∀ {m n : ℕ}, m ≤ n → g n ≤ g m := fun {m n} hmn =>
    exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (Nat.cast_le.2 hmn)) hk.le))
  have hpt : ∀ u : ZMod L, g (zdist L u) ≤ g u.val + g (L - u.val) := by
    intro u
    have h1 : 0 ≤ g u.val := (exp_pos _).le
    have h2 : 0 ≤ g (L - u.val) := (exp_pos _).le
    rcases min_cases u.val (L - u.val) with ⟨h, _⟩ | ⟨h, _⟩ <;>
      · rw [zdist, h]; linarith
  have hsum1 : ∑ u : ZMod L, g u.val ≤ 1 + 2 / k ^ 2 := by
    rw [sum_zmod_val L g]; exact sum_range_exp_neg_mul_sqrt_le hk L
  have hsum2 : ∑ u : ZMod L, g (L - u.val) ≤ 1 + 2 / k ^ 2 := by
    rw [sum_zmod_val L fun v => g (L - v)]
    have hstep : ∀ v ∈ Finset.range L, g (L - v) ≤ g (L - 1 - v) := fun v _ => hanti (by omega)
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.sum_range_reflect g L]
    exact sum_range_exp_neg_mul_sqrt_le hk L
  have := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hpt u
  rw [Finset.sum_add_distrib] at this
  change ∑ u : ZMod L, g (zdist L u) ≤ _
  linarith

/-- The shifted, rescaled form: `∑_x exp(-c√(‖a - x‖/ℓ)) ≤ 2(1 + 2ℓ/c²)`. -/
theorem sum_exp_neg_mul_sqrt_zdist_div_le {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 < ℓ) (a : ZMod L) :
    ∑ x : ZMod L, exp (-(c * √((zdist L (a - x) : ℝ) / ℓ))) ≤ 2 * (1 + 2 * ℓ / c ^ 2) := by
  have hsl : 0 < √ℓ := Real.sqrt_pos.2 hℓ
  have hk : 0 < c / √ℓ := div_pos hc hsl
  have h := (Equiv.subLeft a).sum_comp
    (fun u => exp (-(c * √((zdist L u : ℝ) / ℓ))))
  simp only [Equiv.subLeft_apply] at h
  rw [h]
  have e : ∀ u : ZMod L, exp (-(c * √((zdist L u : ℝ) / ℓ))) =
      exp (-(c / √ℓ * √(zdist L u : ℝ))) := by
    intro u; rw [Real.sqrt_div' _ hℓ.le]; ring_nf
  simp_rw [e]
  refine (sum_exp_neg_mul_sqrt_zdist_le L hk).trans (le_of_eq ?_)
  have : √ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  field_simp
  rw [this]

/-! ### The tail function `T_{u,D}` -/

/-- (5.27): `T_{u,D}(ℓ) = (W ℓ_u η_u)^{-2} exp(-(ℓ/ℓ_u)_+^{1/2}) + W^{-D}`.
The positive part is automatic: `Real.sqrt` of a negative number is `0`. -/
noncomputable def tailT (W ℓu ηu D ℓ : ℝ) : ℝ :=
  ((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu)) + W ^ (-D)

/-- The scale `ℓ*_u = (log W)^{3/2} ℓ_u` (defined before Lemma 5.6). -/
noncomputable def ellStar (W ℓu : ℝ) : ℝ := log W ^ (3 / 2 : ℝ) * ℓu

section Tail

variable {W ℓu ηu D : ℝ}

theorem rpow_neg_le_tailT (ℓ : ℝ) : W ^ (-D) ≤ tailT W ℓu ηu D ℓ := by
  have : 0 ≤ ((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu)) := by positivity
  rw [tailT]; linarith

theorem tailT_nonneg (hW : 0 ≤ W) (ℓ : ℝ) : 0 ≤ tailT W ℓu ηu D ℓ :=
  (Real.rpow_nonneg hW _).trans (rpow_neg_le_tailT ℓ)

theorem tailT_pos (hW : 0 < W) (ℓ : ℝ) : 0 < tailT W ℓu ηu D ℓ :=
  (Real.rpow_pos_of_pos hW _).trans_le (rpow_neg_le_tailT ℓ)

/-- `T_{u,D}` is non-increasing in `ℓ`. -/
theorem tailT_antitone (hℓu : 0 < ℓu) : Antitone (tailT W ℓu ηu D) := by
  intro ℓ₁ ℓ₂ h
  unfold tailT
  have : exp (-√(ℓ₂ / ℓu)) ≤ exp (-√(ℓ₁ / ℓu)) :=
    exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right h hℓu.le)))
  have h0 : 0 ≤ ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  nlinarith

/-- `√((log W)^{3/2}) = (log W)^{3/4}`. -/
theorem sqrt_log_rpow_three_halves (hW : 1 ≤ W) :
    √(log W ^ (3 / 2 : ℝ)) = log W ^ (3 / 4 : ℝ) := by
  have hl : 0 ≤ log W := Real.log_nonneg hW
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hl]
  norm_num

/-- (5.32), explicit form:
`T_{u,D}(ℓ - C ℓ*_u) ≤ exp(√C (log W)^{3/4}) T_{u,D}(ℓ)`. -/
theorem tailT_sub_le (hW : 1 ≤ W) (hℓu : 0 < ℓu) {C : ℝ} (hC : 0 ≤ C) (ℓ : ℝ) :
    tailT W ℓu ηu D (ℓ - C * ellStar W ℓu) ≤
      exp (√C * log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D ℓ := by
  have hl : 0 ≤ log W := Real.log_nonneg hW
  set s : ℝ := C * log W ^ (3 / 2 : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  have hsqrt : √s = √C * log W ^ (3 / 4 : ℝ) := by
    rw [hs, Real.sqrt_mul hC, sqrt_log_rpow_three_halves hW]
  have hsplit : ℓ / ℓu = (ℓ - C * ellStar W ℓu) / ℓu + s := by
    rw [ellStar, hs]; field_simp; ring
  have hkey : √(ℓ / ℓu) ≤ √((ℓ - C * ellStar W ℓu) / ℓu) + √s := by
    rw [hsplit]; exact sqrt_add_le_add_sqrt _ hs0
  have hexp : exp (-√((ℓ - C * ellStar W ℓu) / ℓu)) ≤ exp √s * exp (-√(ℓ / ℓu)) := by
    rw [← exp_add, exp_le_exp]; linarith
  have h1 : 1 ≤ exp √s := Real.one_le_exp (Real.sqrt_nonneg _)
  have hA : 0 ≤ ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hε : 0 ≤ W ^ (-D) := Real.rpow_nonneg (by linarith) _
  rw [← hsqrt]
  unfold tailT
  have := mul_le_mul_of_nonneg_left hexp hA
  nlinarith

/-- **The near region.**  For `d ≤ C ℓ*_u` with `C ≥ 0`,
`(W ℓ_u η_u)^{-2} ≤ exp(√C (log W)^{3/4}) T_{u,D}(d)`: on the scale `C ℓ*_u` the tail
function is still within `W^{o(1)}` of its maximum.  This is (5.32) at the shift
`C ℓ*_u`, applied at a `d` for which the shifted argument is already `≤ 0`.

`RBM.Lemma57.inv_sq_le_tailT` (`C = 1`) and `RBM.Step45.inv_sq_le_tailT` (`C = 6`) are
the two instances used in the proofs of (5.35) and of Step 5. -/
theorem inv_sq_le_tailT {C d : ℝ} (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hC : 0 ≤ C)
    (hd : d ≤ C * ellStar W ℓu) :
    ((W * ℓu * ηu) ^ 2)⁻¹ ≤ exp (√C * log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d := by
  refine le_trans ?_ (tailT_sub_le (ℓu := ℓu) (ηu := ηu) (D := D) hW hℓu hC d)
  have h0 : √((d - C * ellStar W ℓu) / ℓu) = 0 :=
    Real.sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hℓu.le)
  have hWD : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg (by linarith) _
  rw [tailT, h0, neg_zero, Real.exp_zero, mul_one]
  linarith

/-- For every `τ > 0`, eventually `exp(C (log W)^{3/4}) ≤ W^τ`: the loss in (5.32) is
`W^{o(1)}`. -/
theorem eventually_exp_mul_log_rpow_le (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ W : ℝ in atTop, exp (C * log W ^ (3 / 4 : ℝ)) ≤ W ^ τ := by
  have h1 : Tendsto (fun W => log W ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  filter_upwards [h1.eventually_ge_atTop (C / τ), eventually_ge_atTop 1] with W hW1 hW2
  have hl : 0 ≤ log W := Real.log_nonneg hW2
  rw [Real.rpow_def_of_pos (show (0 : ℝ) < W by linarith) τ, exp_le_exp]
  have hsplit : log W = log W ^ (1 / 4 : ℝ) * log W ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add' hl (by norm_num)]; norm_num
  have hC : C ≤ log W ^ (1 / 4 : ℝ) * τ := (div_le_iff₀ hτ).1 hW1
  have h34 : 0 ≤ log W ^ (3 / 4 : ℝ) := Real.rpow_nonneg hl _
  have := mul_le_mul_of_nonneg_right hC h34
  calc C * log W ^ (3 / 4 : ℝ) ≤ log W ^ (1 / 4 : ℝ) * τ * log W ^ (3 / 4 : ℝ) := this
    _ = log W * τ := by rw [mul_right_comm, ← hsplit]

end Tail

/-! ### The discrete convolution bound (5.50), (5.72) -/

/-- Pointwise form of the convolution trick: if `d ≤ d₁ + d₂` then
`e^{-√(d₁/ℓ)} e^{-√(d₂/ℓ)} ≤ e^{-√(d/ℓ)} (e^{-√(d₁/ℓ)/2} + e^{-√(d₂/ℓ)/2})`. -/
theorem exp_neg_sqrt_mul_exp_neg_sqrt_le {d₁ d₂ d ℓ : ℝ} (h₁ : 0 ≤ d₁) (h₂ : 0 ≤ d₂)
    (hℓ : 0 < ℓ) (hd : d ≤ d₁ + d₂) :
    exp (-√(d₁ / ℓ)) * exp (-√(d₂ / ℓ)) ≤
      exp (-√(d / ℓ)) * (exp (-(1 / 2 * √(d₁ / ℓ))) + exp (-(1 / 2 * √(d₂ / ℓ)))) := by
  have hp : 0 ≤ d₁ / ℓ := div_nonneg h₁ hℓ.le
  have hq : 0 ≤ d₂ / ℓ := div_nonneg h₂ hℓ.le
  have hr : √(d / ℓ) ≤ √(d₁ / ℓ + d₂ / ℓ) := by
    rw [← add_div]; exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hd hℓ.le)
  have e1 := exp_pos (-√(d / ℓ))
  have e2 := exp_pos (-(1 / 2 * √(d₁ / ℓ)))
  have e3 := exp_pos (-(1 / 2 * √(d₂ / ℓ)))
  rw [← exp_add]
  rcases le_total (d₁ / ℓ) (d₂ / ℓ) with h | h
  · have hs := sqrt_add_le_of_le hp h
    have : exp (-√(d₁ / ℓ) + -√(d₂ / ℓ)) ≤ exp (-√(d / ℓ)) * exp (-(1 / 2 * √(d₁ / ℓ))) := by
      rw [← exp_add, exp_le_exp]; linarith
    nlinarith
  · have hs := sqrt_add_le_of_le hq h
    rw [add_comm] at hs
    have : exp (-√(d₁ / ℓ) + -√(d₂ / ℓ)) ≤ exp (-√(d / ℓ)) * exp (-(1 / 2 * √(d₂ / ℓ))) := by
      rw [← exp_add, exp_le_exp]; linarith
    nlinarith

/-- The triangle inequality in the form used below: `‖a₁ - a₂‖ ≤ ‖a₁ - x‖ + ‖a₂ - x‖`. -/
theorem zdist_sub_le_add (a₁ a₂ x : ZMod L) :
    (zdist L (a₁ - a₂) : ℝ) ≤ zdist L (a₁ - x) + zdist L (a₂ - x) := by
  have h := zdist_add_le L (a₁ - x) (-(a₂ - x))
  rw [zdist_neg] at h
  have e : a₁ - x + -(a₂ - x) = a₁ - a₂ := by ring
  rw [e] at h
  exact_mod_cast h

/-- The discrete convolution bound, the content of (5.72) (and of (5.50), see
`mul_sum_tailT_mul_tailT_le`):
`∑_x T_{u,D}(‖a₁ - x‖) T_{u,D}(‖a₂ - x‖) ≤ (36 ℓ_u (W ℓ_u η_u)^{-2} + L W^{-D}) T_{u,D}(‖a₁ - a₂‖)`.
The second term in the bracket is the (negligible for large `D`) contribution of
`W^{-D} · W^{-D}` summed over the `L` sites. -/
theorem sum_tailT_mul_tailT_le {W ℓu ηu : ℝ} (hW : 0 < W) (hℓu : 1 ≤ ℓu) (D : ℝ)
    (a₁ a₂ : ZMod L) :
    ∑ x : ZMod L, tailT W ℓu ηu D (zdist L (a₁ - x)) * tailT W ℓu ηu D (zdist L (a₂ - x)) ≤
      (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
  have hℓ : 0 < ℓu := by linarith
  set A : ℝ := ((W * ℓu * ηu) ^ 2)⁻¹ with hA
  set ε : ℝ := W ^ (-D) with hε
  have hA0 : 0 ≤ A := by positivity
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hW.le _
  set e : ℝ := exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓu)) with he
  have he0 : 0 ≤ e := (exp_pos _).le
  -- the four stretched-exponential sums
  set E : ZMod L → ZMod L → ℝ := fun a x => exp (-√((zdist L (a - x) : ℝ) / ℓu)) with hE
  set H : ZMod L → ZMod L → ℝ :=
    fun a x => exp (-(1 / 2 * √((zdist L (a - x) : ℝ) / ℓu))) with hH
  have hsE : ∀ a, ∑ x, E a x ≤ 2 * (1 + 2 * ℓu / 1 ^ 2) := by
    intro a
    have := sum_exp_neg_mul_sqrt_zdist_div_le L one_pos hℓ a
    simpa [hE] using this
  have hsH : ∀ a, ∑ x, H a x ≤ 2 * (1 + 2 * ℓu / (1 / 2) ^ 2) := fun a =>
    sum_exp_neg_mul_sqrt_zdist_div_le L (by norm_num) hℓ a
  -- pointwise bound
  have hpt : ∀ x : ZMod L,
      tailT W ℓu ηu D (zdist L (a₁ - x)) * tailT W ℓu ηu D (zdist L (a₂ - x)) ≤
        A ^ 2 * e * (H a₁ x + H a₂ x) + A * ε * (E a₁ x + E a₂ x) + ε ^ 2 := by
    intro x
    have hc := exp_neg_sqrt_mul_exp_neg_sqrt_le (Nat.cast_nonneg (zdist L (a₁ - x)))
      (Nat.cast_nonneg (zdist L (a₂ - x))) hℓ (zdist_sub_le_add L a₁ a₂ x)
    rw [← he] at hc
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    have := mul_le_mul_of_nonneg_left hc hA2
    simp only [tailT, hE, hH]
    nlinarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul] at hsum
  have hb1 : A ^ 2 * e * (∑ x, H a₁ x + ∑ x, H a₂ x) ≤ A ^ 2 * e * (36 * ℓu) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := hsH a₁; have h2 := hsH a₂
    norm_num at h1 h2
    linarith
  have hb2 : A * ε * (∑ x, E a₁ x + ∑ x, E a₂ x) ≤ A * ε * (36 * ℓu) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := hsE a₁; have h2 := hsE a₂
    norm_num at h1 h2
    linarith
  have hb3 : 0 ≤ (L : ℝ) * ε * (A * e) := by positivity
  have hT : tailT W ℓu ηu D (zdist L (a₁ - a₂)) = A * e + ε := rfl
  rw [hT]
  nlinarith

/-- (5.50): `W ∑_x T_{u,D}(‖a₁ - x‖) T_{u,D}(‖a₂ - x‖)
≤ (36 η_u^{-1} (W ℓ_u η_u)^{-1} + W L W^{-D}) T_{u,D}(‖a₁ - a₂‖)`. -/
theorem mul_sum_tailT_mul_tailT_le {W ℓu ηu : ℝ} (hW : 0 < W) (hℓu : 1 ≤ ℓu) (hη : 0 < ηu)
    (D : ℝ) (a₁ a₂ : ZMod L) :
    W * ∑ x : ZMod L,
        tailT W ℓu ηu D (zdist L (a₁ - x)) * tailT W ℓu ηu D (zdist L (a₂ - x)) ≤
      (36 * (ηu⁻¹ * (W * ℓu * ηu)⁻¹) + W * L * W ^ (-D)) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
  have hℓ : 0 < ℓu := by linarith
  have h := mul_le_mul_of_nonneg_left (sum_tailT_mul_tailT_le L (ηu := ηu) hW hℓu D a₁ a₂) hW.le
  refine h.trans (le_of_eq ?_)
  have e : W * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)) =
      36 * (ηu⁻¹ * (W * ℓu * ηu)⁻¹) + W * L * W ^ (-D) := by
    field_simp
  rw [← mul_assoc, e]

/-! ### (7.12) -/

end RBM
