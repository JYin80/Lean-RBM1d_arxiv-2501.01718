/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Analysis.StretchedExp
import RBM1D.Loop.GLoop

/-!
# Lemma 5.7, the estimate (5.35)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, pp. 59–61: the proof of **(5.35)**,

`E^{(G)}_{u,σ,a} / T_{t,D}(‖a₁-a₂‖) ≺ η_u^{-1} (ℓ_u/ℓ_s)² 1(‖a₁-a₂‖ ≤ ℓ*_u)
   + η_u^{-1} (W η_u ℓ_u)^{-1/3} (J*_{u,D})³`,

which today enters the repository only as the hypothesis `RBM.Step2.Hyp.eG`
(`RBM1D/Hierarchy/Step2.lean`).  Everything here is **deterministic arithmetic**: the case
analysis (5.51)–(5.63) with all its inputs — (4.2)/(4.5), (2.73)/(2.74), (5.31), (5.32) — taken
as explicit hypotheses, and all constants explicit (not optimal).

## The chain

| display | statement |
|---|---|
| (5.53)+(5.54) | `sum_le_split_one`, `card_zdist_le_real` — the `b`-sum split at `ℓ**_u` |
| (5.55) | `eG_near_le` — the near field `‖a₁-a₂‖ ≤ ℓ*_u` |
| (5.58)+(5.31)+(5.32) | `case1_pointwise` — Case 1 of the far field |
| (5.60)+(4.2)+(5.31) | `case2_pointwise` — Case 2 of the far field |
| (5.62) | `sum_sqrt_tailT_mul_le` — `∑_b √(T(‖a₁-b‖) T(‖a₂-b‖)) ≤ C ℓ_u A_u^{-1} √(T(‖a₁-a₂‖))` |
| (5.63) | `sum_far_le` |
| (5.35) | `eG_le` (master), `eG_le_paper` (shape 1), `eG_le_reduced` (shape 2) |
| (5.60) | `norm_gloop_three_le` — from the definition of the `3`-loop, `RBM.gloop` |
| (5.56)/(5.58) | `norm_gloop_three_le_schwarz`, `gloop_h558a`, `gloop_h558b` — also from the definition of the `3`-loop, via `sum_blkW_normSq` |

## (5.36), pp. 61–63

| display | statement |
|---|---|
| (5.64) | `ee_near_le` — Case 1, `‖a₁-a₂‖ ≤ 4ℓ*_u`, from (2.73) at `n = 6` |
| (5.67)+(5.71) | `case2a_pointwise` — Case 2(1a), intrinsic `(J*)²` |
| (5.67)+(5.72) | `case2b_pointwise` — Case 2(1b), intrinsic `(J*)³` |
| (5.71)+(5.72) | `sum_ee_far_le` (one half), `ee_far_le` (both halves) |
| (5.36) | `ee_le` (master), `ee_le_paper` (with `μ` from (2.73) at `n = 4`) |

The intrinsic super-linear powers of `J*` in (5.36) are **confirmed**, and for the same
structural reason as in (5.61): Case 2(1a) needs `T_{u,D}(‖a₁-a₂‖) T_{u,D}(‖b-a₂‖)`, one
tail function from each of the two squared `G`-pairs of (5.65), to produce the
`T_{u,D}(‖a₁-a₂‖)²` normalization; Case 2(1b) needs a third, from `G†E_b G`, to feed the
convolution `∑_b T(‖a₁-b‖) T(‖a₂-b‖) ≺ ℓ_u A_u^{-2} T(‖a₁-a₂‖)`.  Replacing any one of
them by the (2.73) bound, which carries no tail function, leaves a `T` short.

Their `A_u` weights, however, are **not** both `A_u^{-1}`: after the `W ∑_b` of (5.22),
Case 2(1a) gives `η_u^{-1} (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} (J*)²` and Case 2(1b) gives
`36 η_u^{-1} A_u^{-1} (J*)³`.  The `A_u^{-1/2}` of (1a) is exactly what (5.36) states.

## The two shapes

* `eG_le_paper` — the paper's literal statement, with `A_u^{-1/3} (J*)³`.
* `eG_le_reduced` — the **(2.73)-reduced** form: both `(1 + J* A_u^{-1})` factors (from (4.5) at
  (5.52) and from (4.2) at (5.57)/(5.58)) replaced by what Step 1 gives directly,
  `L_{u,(+,-)} ≺ r A_u^{-1}` with `r = ℓ_u/ℓ_s`.  The far-field bracket becomes
  `r^{3/2} A_u^{-1/2} J* + r A_u^{-1} (J*)^{3/2}`.

The `(J*)^{3/2}` of Case 2 is **intrinsic**: in `sum_far_le` the factor `√(T(‖a₁-a₂‖))` coming
from the `a₁–a₂` edge is what turns the convolution bound `∑_b √(T_{1b} T_{2b}) ≺ ℓ_u A_u^{-1}
√(T_{12})` into a full `T_{12}`.  Replacing any one of the three `G`-edges of (5.61) by the
(2.73) bound, which carries no tail function, leaves `T^{1/2}` missing.

## Deviations from the literal paper statement (to be recorded in `docs/paper-deltas.md`)

1. The tail function is `T_{u,D}` throughout, not the paper's `T_{t,D}`; this matches
   `RBM.Step2.Hyp.eG`, and the two differ by (5.32) + `T_{u,D} ≤ T_{t,D}` for `u ≤ t`.
2. The Case-1 site count is `ℓ*_u = (log W)^{3/2} ℓ_u`, not the paper's `ℓ_u` in (5.59); the
   `(log W)^{3/2}` sits in the `W^{o(1)}` coefficient `cFar`.  Likewise the near-field count is
   `ℓ**_u = (log W)^3 ℓ_u` and the `A_u^{-2} / T_{u,D}` conversion costs `e^{(log W)^{3/4}}`;
   both live in `cNear`.  All of these are `≺ 1`.
3. `eG_le_paper` needs `J* ≤ A_u`, which the paper does not write: (5.55) has the factor
   `1 + (J*)² A_u^{-1}` while (5.35)'s first term has none, and `r² (J*)² A_u^{-1}` fits inside
   `A_u^{-1/3}(J*)³` only if `r² ≤ J* A_u^{2/3}`.
4. `eG_le_reduced`'s near-field term is `r³`, not `r²`: the (5.52) prefactor is `r` there.
5. The `b`-sum over `‖a₁-b‖ > ℓ**_u`, which the paper calls negligible after (5.54), is kept as
   an **explicit** additive remainder `κ₁ (ℓ_u η_u)^{-1} L ρ`; and the `W^{-D}` floor of
   `T_{u,D}` summed over the `L` sites is kept explicit (`hD` in the two shapes), exactly as in
   `RBM.mul_sum_tailT_mul_tailT_le'`.

6. (5.36) is formalized at `a' = a` and at `b' = b` (the paper itself says "we can treat
   `b = b'` for all practical purposes"); for general `a'` with `‖aᵢ - aᵢ'‖ ≤ ℓ*_t` the
   passage is (5.32) again, i.e. `tailT_sub_le`, exactly as in `case1_pointwise`.
7. `ee_far_le` and `ee_le` carry a hypothesis `hsym` for the half `‖a₂ - b‖ < ‖a₁ - b‖`.
   The paper's "by symmetry, we only consider the first case" is the `k = 1` / `k = 2`
   symmetry of (5.22) (Figure 14), **not** a relabelling inside one term: on that half the
   `(b, a₂)` pair of `G`-edges of (5.65) is short, so (5.31) does not apply to it and the
   `k = 1` term alone does not give the bound there.  Discharging `hsym` needs the second
   term of (5.22), which is not in the repository.
8. `ee_le_paper` keeps the factor `(ℓ_u/ℓ_s)^{3/2}` that (2.73) at `n = 4` produces in the
   line after (5.67); the statement of (5.36) drops it.
9. The `k`-sum of (5.22) is taken in the form `E⊗E ≤ W ∑_b L^{(1)}(b)` (`hEE`), matching
   the power counting (5.38); the expansion itself is not in the repository.

`RBM.Lemma57.inv_sq_le_tailT` and `RBM.Step45.inv_sq_le_tailT` are now the `C = 1` and
`C = 6` instances of the single lemma `RBM.inv_sq_le_tailT` in `Analysis/StretchedExp.lean`.
-/

namespace RBM
namespace Lemma57

open Real Finset

variable (L : ℕ) [NeZero L]

/-! ### Counting the sites near a given one -/

/-- There are at most `2m + 2` sites within (cyclic) distance `m` of a given site. -/
theorem card_zdist_le (a : ZMod L) (m : ℕ) :
    (Finset.univ.filter fun b : ZMod L => zdist L (a - b) ≤ m).card ≤ 2 * m + 2 := by
  classical
  set s : Finset (ZMod L) := Finset.univ.filter fun b : ZMod L => zdist L (a - b) ≤ m with hs
  have hmap : s.image (fun b : ZMod L => (a - b).val) ⊆
      Finset.range (m + 1) ∪ Finset.Ico (L - m) L := by
    intro k hk
    simp only [Finset.mem_image, hs, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    obtain ⟨b, hb, rfl⟩ := hk
    have hlt : (a - b).val < L := ZMod.val_lt _
    have := hb
    rw [zdist] at this
    rcases min_cases (a - b).val (L - (a - b).val) with ⟨he, _⟩ | ⟨he, _⟩
    · exact Finset.mem_union_left _ (Finset.mem_range.2 (by omega))
    · refine Finset.mem_union_right _ (Finset.mem_Ico.2 ⟨by omega, hlt⟩)
  have hinj : Set.InjOn (fun b : ZMod L => (a - b).val) s := by
    intro x _ y _ h
    have : a - x = a - y := ZMod.val_injective L h
    have := congrArg (fun z => a - z) this
    simpa using this
  have hcard := Finset.card_le_card hmap
  rw [Finset.card_image_of_injOn hinj] at hcard
  refine hcard.trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  simp only [Finset.card_range, Nat.card_Ico]
  omega

/-- `‖x - y‖ = ‖y - x‖` on `ZMod L`. -/
theorem zdist_sub_comm (x y : ZMod L) : zdist L (x - y) = zdist L (y - x) := by
  rw [← zdist_neg L (x - y)]
  congr 1
  ring

/-! ### `√(T_{u,D})` and the half-exponent convolution behind (5.62) -/

section Sqrt

variable {W ℓu ηu D : ℝ}

/-- `√(T_{u,D}(ℓ)) ≤ (W ℓ_u η_u)^{-1} e^{-√(ℓ/ℓ_u)/2} + √(W^{-D})`. -/
theorem sqrt_tailT_le (hW : 0 < W) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (ℓ : ℝ) :
    √(tailT W ℓu ηu D ℓ) ≤
      (W * ℓu * ηu)⁻¹ * exp (-(1 / 2 * √(ℓ / ℓu))) + √(W ^ (-D)) := by
  have hA : (0 : ℝ) < W * ℓu * ηu := by positivity
  have he2 : exp (-(1 / 2 * √(ℓ / ℓu))) ^ 2 = exp (-√(ℓ / ℓu)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsq : ((W * ℓu * ηu)⁻¹ * exp (-(1 / 2 * √(ℓ / ℓu)))) ^ 2
      = ((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu)) := by
    rw [mul_pow, he2, inv_pow]
  have h1 : √(((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu)))
      = (W * ℓu * ηu)⁻¹ * exp (-(1 / 2 * √(ℓ / ℓu))) := by
    rw [← hsq, Real.sqrt_sq (by positivity)]
  calc √(tailT W ℓu ηu D ℓ)
      = √(((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu)) + W ^ (-D)) := rfl
    _ ≤ √(((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu))) + √(W ^ (-D)) :=
        sqrt_add_le_add_sqrt _ (Real.rpow_nonneg hW.le _)
    _ = _ := by rw [h1]

/-- `(W ℓ_u η_u)^{-1} e^{-√(ℓ/ℓ_u)/2} ≤ √(T_{u,D}(ℓ))`. -/
theorem le_sqrt_tailT (hW : 0 < W) (hℓu : 0 < ℓu) (hηu : 0 < ηu) (ℓ : ℝ) :
    (W * ℓu * ηu)⁻¹ * exp (-(1 / 2 * √(ℓ / ℓu))) ≤ √(tailT W ℓu ηu D ℓ) := by
  have hA : (0 : ℝ) < W * ℓu * ηu := by positivity
  have he2 : exp (-(1 / 2 * √(ℓ / ℓu))) ^ 2 = exp (-√(ℓ / ℓu)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsq : ((W * ℓu * ηu)⁻¹ * exp (-(1 / 2 * √(ℓ / ℓu)))) ^ 2
      = ((W * ℓu * ηu) ^ 2)⁻¹ * exp (-√(ℓ / ℓu)) := by
    rw [mul_pow, he2, inv_pow]
  rw [show √(tailT W ℓu ηu D ℓ) = √(tailT W ℓu ηu D ℓ) from rfl]
  refine Real.le_sqrt' (by positivity) |>.2 ?_
  rw [hsq]
  have : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  unfold tailT
  linarith

/-- `√(W^{-D}) ≤ √(T_{u,D}(ℓ))`. -/
theorem sqrt_rpow_neg_le_sqrt_tailT (ℓ : ℝ) :
    √(W ^ (-D)) ≤ √(tailT W ℓu ηu D ℓ) :=
  Real.sqrt_le_sqrt (rpow_neg_le_tailT ℓ)

/-- Half-exponent form of the convolution trick: if `d ≤ d₁ + d₂` then
`e^{-√(d₁/ℓ)/2} e^{-√(d₂/ℓ)/2} ≤ e^{-√(d/ℓ)/2}(e^{-√(d₁/ℓ)/4} + e^{-√(d₂/ℓ)/4})`. -/
theorem exp_half_mul_exp_half_le {d₁ d₂ d ℓ : ℝ} (h₁ : 0 ≤ d₁) (h₂ : 0 ≤ d₂)
    (hℓ : 0 < ℓ) (hd : d ≤ d₁ + d₂) :
    exp (-(1 / 2 * √(d₁ / ℓ))) * exp (-(1 / 2 * √(d₂ / ℓ))) ≤
      exp (-(1 / 2 * √(d / ℓ))) *
        (exp (-(1 / 4 * √(d₁ / ℓ))) + exp (-(1 / 4 * √(d₂ / ℓ)))) := by
  have hp : 0 ≤ d₁ / ℓ := div_nonneg h₁ hℓ.le
  have hq : 0 ≤ d₂ / ℓ := div_nonneg h₂ hℓ.le
  have hr : √(d / ℓ) ≤ √(d₁ / ℓ + d₂ / ℓ) := by
    rw [← add_div]; exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hd hℓ.le)
  have e1 := exp_pos (-(1 / 2 * √(d / ℓ)))
  have e2 := exp_pos (-(1 / 4 * √(d₁ / ℓ)))
  have e3 := exp_pos (-(1 / 4 * √(d₂ / ℓ)))
  rw [← exp_add]
  rcases le_total (d₁ / ℓ) (d₂ / ℓ) with h | h
  · have hs := sqrt_add_le_of_le hp h
    have key : exp (-(1 / 2 * √(d₁ / ℓ)) + -(1 / 2 * √(d₂ / ℓ))) ≤
        exp (-(1 / 2 * √(d / ℓ))) * exp (-(1 / 4 * √(d₁ / ℓ))) := by
      rw [← exp_add, exp_le_exp]; linarith
    nlinarith
  · have hs := sqrt_add_le_of_le hq h
    rw [add_comm] at hs
    have key : exp (-(1 / 2 * √(d₁ / ℓ)) + -(1 / 2 * √(d₂ / ℓ))) ≤
        exp (-(1 / 2 * √(d / ℓ))) * exp (-(1 / 4 * √(d₂ / ℓ))) := by
      rw [← exp_add, exp_le_exp]; linarith
    nlinarith

/-- **The summation kernel of (5.62)**:
`∑_b √(T_{u,D}(‖a₁-b‖)) √(T_{u,D}(‖a₂-b‖))
  ≤ (168 ℓ_u (W ℓ_u η_u)^{-1} + L √(W^{-D})) √(T_{u,D}(‖a₁-a₂‖))`.

This is the discrete form of the paper's
`∫_0^a exp(-√((a-x)/2) - √(x/2) + √(a/2)) dx ≤ C` (the display after (5.62)). -/
theorem sum_sqrt_tailT_mul_le (hW : 0 < W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu) (D : ℝ)
    (a₁ a₂ : ZMod L) :
    ∑ b : ZMod L, √(tailT W ℓu ηu D (zdist L (a₁ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₂ - b))) ≤
      (168 * ℓu * (W * ℓu * ηu)⁻¹ + L * √(W ^ (-D))) *
        √(tailT W ℓu ηu D (zdist L (a₁ - a₂))) := by
  have hℓ : 0 < ℓu := by linarith
  set A : ℝ := (W * ℓu * ηu)⁻¹ with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set ε : ℝ := √(W ^ (-D)) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  set e : ℝ := exp (-(1 / 2 * √((zdist L (a₁ - a₂) : ℝ) / ℓu))) with he
  have he0 : 0 < e := exp_pos _
  set H : ZMod L → ZMod L → ℝ :=
    fun a x => exp (-(1 / 2 * √((zdist L (a - x) : ℝ) / ℓu))) with hH
  set Gg : ZMod L → ZMod L → ℝ :=
    fun a x => exp (-(1 / 4 * √((zdist L (a - x) : ℝ) / ℓu))) with hG
  have hsH : ∀ a, ∑ x, H a x ≤ 2 * (1 + 2 * ℓu / (1 / 2 : ℝ) ^ 2) := fun a =>
    sum_exp_neg_mul_sqrt_zdist_div_le L (by norm_num) hℓ a
  have hsG : ∀ a, ∑ x, Gg a x ≤ 2 * (1 + 2 * ℓu / (1 / 4 : ℝ) ^ 2) := fun a =>
    sum_exp_neg_mul_sqrt_zdist_div_le L (by norm_num) hℓ a
  -- pointwise bound
  have hpt : ∀ b : ZMod L,
      √(tailT W ℓu ηu D (zdist L (a₁ - b))) * √(tailT W ℓu ηu D (zdist L (a₂ - b))) ≤
        A ^ 2 * e * (Gg a₁ b + Gg a₂ b) + A * ε * (H a₁ b + H a₂ b) + ε ^ 2 := by
    intro b
    have b1 := sqrt_tailT_le (D := D) hW hℓ hηu ((zdist L (a₁ - b) : ℝ))
    have b2 := sqrt_tailT_le (D := D) hW hℓ hηu ((zdist L (a₂ - b) : ℝ))
    have hs1 : 0 ≤ √(tailT W ℓu ηu D (zdist L (a₁ - b))) := Real.sqrt_nonneg _
    have hs2 : 0 ≤ √(tailT W ℓu ηu D (zdist L (a₂ - b))) := Real.sqrt_nonneg _
    have hc := exp_half_mul_exp_half_le (Nat.cast_nonneg (zdist L (a₁ - b)))
      (Nat.cast_nonneg (zdist L (a₂ - b))) hℓ (zdist_sub_le_add L a₁ a₂ b)
    rw [← he] at hc
    have hmul : √(tailT W ℓu ηu D (zdist L (a₁ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₂ - b))) ≤
        (A * H a₁ b + ε) * (A * H a₂ b + ε) := by
      refine mul_le_mul b1 b2 hs2 (by positivity)
    refine hmul.trans ?_
    have h1 : 0 ≤ A ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hc h1
    have hHp : 0 < H a₁ b := exp_pos _
    have hHq : 0 < H a₂ b := exp_pos _
    nlinarith
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hpt b
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul] at hsum
  have hb1 : A ^ 2 * e * (∑ x, Gg a₁ x + ∑ x, Gg a₂ x) ≤ A ^ 2 * e * (132 * ℓu) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := hsG a₁; have h2 := hsG a₂
    norm_num at h1 h2
    linarith
  have hb2 : A * ε * (∑ x, H a₁ x + ∑ x, H a₂ x) ≤ A * ε * (36 * ℓu) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := hsH a₁; have h2 := hsH a₂
    norm_num at h1 h2
    linarith
  -- lower bounds on the target
  have hlow1 : A * e ≤ √(tailT W ℓu ηu D (zdist L (a₁ - a₂))) :=
    le_sqrt_tailT (D := D) hW hℓ hηu _
  have hlow2 : ε ≤ √(tailT W ℓu ηu D (zdist L (a₁ - a₂))) :=
    sqrt_rpow_neg_le_sqrt_tailT _
  set S : ℝ := √(tailT W ℓu ηu D (zdist L (a₁ - a₂))) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have t1 : A ^ 2 * e * (132 * ℓu) ≤ 132 * ℓu * A * S := by
    calc A ^ 2 * e * (132 * ℓu) = 132 * ℓu * A * (A * e) := by ring
      _ ≤ 132 * ℓu * A * S := mul_le_mul_of_nonneg_left hlow1 (by positivity)
  have t2 : A * ε * (36 * ℓu) ≤ 36 * ℓu * A * S := by
    calc A * ε * (36 * ℓu) = 36 * ℓu * A * ε := by ring
      _ ≤ 36 * ℓu * A * S := mul_le_mul_of_nonneg_left hlow2 (by positivity)
  have t3 : (L : ℝ) * ε ^ 2 ≤ (L : ℝ) * ε * S := by
    calc (L : ℝ) * ε ^ 2 = (L : ℝ) * ε * ε := by ring
      _ ≤ (L : ℝ) * ε * S := mul_le_mul_of_nonneg_left hlow2 (by positivity)
  have hR : (168 * ℓu * A + (L : ℝ) * ε) * S
      = 132 * ℓu * A * S + 36 * ℓu * A * S + (L : ℝ) * ε * S := by ring
  rw [hR]
  linarith

end Sqrt

/-! ### Splitting the `∑_b` of (5.52) -/

section Split

/-- Real-threshold form of `card_zdist_le`. -/
theorem card_zdist_le_real (a : ZMod L) {x : ℝ} (hx : 0 ≤ x) :
    (((Finset.univ.filter fun b : ZMod L => (zdist L (a - b) : ℝ) ≤ x).card : ℕ) : ℝ)
      ≤ 2 * x + 2 := by
  classical
  have hsub : (Finset.univ.filter fun b : ZMod L => (zdist L (a - b) : ℝ) ≤ x) ⊆
      Finset.univ.filter fun b : ZMod L => zdist L (a - b) ≤ ⌊x⌋₊ := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact Nat.le_floor hb
  have h1 := Finset.card_le_card hsub
  have h2 := card_zdist_le L a ⌊x⌋₊
  have h3 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx
  have : ((Finset.univ.filter fun b : ZMod L => (zdist L (a - b) : ℝ) ≤ x).card : ℝ)
      ≤ ((2 * ⌊x⌋₊ + 2 : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
  refine this.trans ?_
  push_cast
  linarith

/-- The split of `∑_b` used for the near field (5.53)/(5.54): the sites with
`‖a - b‖ ≤ x` contribute at most `(2x+2) c₁`, the rest at most `∑_b g b`. -/
theorem sum_le_split_one {f g : ZMod L → ℝ} (hg : ∀ b, 0 ≤ g b)
    {x : ℝ} (hx : 0 ≤ x) (a : ZMod L) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (h₁ : ∀ b, (zdist L (a - b) : ℝ) ≤ x → f b ≤ c₁)
    (h₂ : ∀ b, x < (zdist L (a - b) : ℝ) → f b ≤ g b) :
    ∑ b : ZMod L, f b ≤ (2 * x + 2) * c₁ + ∑ b : ZMod L, g b := by
  classical
  set p : ZMod L → Prop := fun b => (zdist L (a - b) : ℝ) ≤ x with hp
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod L)) p f
  have hA : ∑ b ∈ Finset.univ.filter p, f b ≤ (2 * x + 2) * c₁ := by
    have h1 : ∑ b ∈ Finset.univ.filter p, f b ≤
        ∑ _b ∈ Finset.univ.filter p, c₁ :=
      Finset.sum_le_sum fun b hb => h₁ b (by
        simpa [hp, Finset.mem_filter] using (Finset.mem_filter.1 hb).2)
    refine h1.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_zdist_le_real L a hx) hc₁
  have hB : ∑ b ∈ Finset.univ.filter (fun b => ¬ p b), f b ≤ ∑ b : ZMod L, g b := by
    refine (Finset.sum_le_sum (fun b hb => h₂ b ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun b _ _ => hg b)
    have := (Finset.mem_filter.1 hb).2
    simpa [hp, not_le] using this
  linarith [hsplit]

/-- The split of `∑_b` used in the far field: Case 1 is `min_i ‖a_i - b‖ ≤ x`
(at most `4x + 4` sites, each contributing at most `c₁`), Case 2 is the rest. -/
theorem sum_le_split_two {f g : ZMod L → ℝ} (hg : ∀ b, 0 ≤ g b)
    {x : ℝ} (hx : 0 ≤ x) (a₁ a₂ : ZMod L) {c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (h₁ : ∀ b, ((zdist L (a₁ - b) : ℝ) ≤ x ∨ (zdist L (a₂ - b) : ℝ) ≤ x) → f b ≤ c₁)
    (h₂ : ∀ b, x < (zdist L (a₁ - b) : ℝ) → x < (zdist L (a₂ - b) : ℝ) → f b ≤ g b) :
    ∑ b : ZMod L, f b ≤ (4 * x + 4) * c₁ + ∑ b : ZMod L, g b := by
  classical
  set p : ZMod L → Prop :=
    fun b => (zdist L (a₁ - b) : ℝ) ≤ x ∨ (zdist L (a₂ - b) : ℝ) ≤ x with hp
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod L)) p f
  have hcard : ((Finset.univ.filter p).card : ℝ) ≤ 4 * x + 4 := by
    have hsub : Finset.univ.filter p ⊆
        (Finset.univ.filter fun b : ZMod L => (zdist L (a₁ - b) : ℝ) ≤ x) ∪
          (Finset.univ.filter fun b : ZMod L => (zdist L (a₂ - b) : ℝ) ≤ x) := by
      intro b hb
      have hb2 := (Finset.mem_filter.1 hb).2
      rw [hp] at hb2
      rcases hb2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    have h0 := Finset.card_le_card hsub
    have h1 := Finset.card_union_le
      (Finset.univ.filter fun b : ZMod L => (zdist L (a₁ - b) : ℝ) ≤ x)
      (Finset.univ.filter fun b : ZMod L => (zdist L (a₂ - b) : ℝ) ≤ x)
    have h2 := card_zdist_le_real L a₁ hx
    have h3 := card_zdist_le_real L a₂ hx
    have hc : ((Finset.univ.filter p).card : ℝ) ≤
        ((Finset.univ.filter fun b : ZMod L => (zdist L (a₁ - b) : ℝ) ≤ x).card : ℝ) +
        ((Finset.univ.filter fun b : ZMod L => (zdist L (a₂ - b) : ℝ) ≤ x).card : ℝ) := by
      exact_mod_cast h0.trans h1
    linarith
  have hA : ∑ b ∈ Finset.univ.filter p, f b ≤ (4 * x + 4) * c₁ := by
    have h1 : ∑ b ∈ Finset.univ.filter p, f b ≤ ∑ _b ∈ Finset.univ.filter p, c₁ :=
      Finset.sum_le_sum fun b hb => h₁ b (Finset.mem_filter.1 hb).2
    refine h1.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hc₁
  have hB : ∑ b ∈ Finset.univ.filter (fun b => ¬ p b), f b ≤ ∑ b : ZMod L, g b := by
    refine (Finset.sum_le_sum (fun b hb => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun b _ _ => hg b)
    have hnp := (Finset.mem_filter.1 hb).2
    rw [hp] at hnp
    simp only [not_or, not_le] at hnp
    exact h₂ b hnp.1 hnp.2
  linarith [hsplit]

end Split

/-! ### The far field `‖a₁ - a₂‖ ≥ ℓ*_u`: (5.56)–(5.63) -/

section FarField

variable {W ℓu ηu D J : ℝ}

/-- The loss factor of (5.32) at `C = 1/2`: `T_{u,D}(ℓ - ℓ*_u/2) ≤ κ₃ T_{u,D}(ℓ)` with
`κ₃ = exp(√(1/2) (log W)^{3/4})`, which is `W^{o(1)}`
(`RBM.eventually_exp_mul_log_rpow_le`). -/
noncomputable def loss32 (W : ℝ) : ℝ := exp (√(1 / 2 : ℝ) * log W ^ (3 / 4 : ℝ))

theorem one_le_loss32 {W : ℝ} (hW : 1 ≤ W) : 1 ≤ loss32 W := by
  have : 0 ≤ log W := Real.log_nonneg hW
  exact Real.one_le_exp (by positivity)

theorem loss32_pos (W : ℝ) : 0 < loss32 W := exp_pos _

/-- **Case 1 of (5.56)–(5.59), pointwise.**  If `b` is within `ℓ*_u/2` of one of the two
external labels, the Schwarz step (5.58) plus the loop decay (5.31) and the shift
estimate (5.32) give `|L_{u,(-,+,+),(a₁,b,a₂)}| ≤ 2 J κ₃ T_{u,D}(‖a₁-a₂‖) κ₂`. -/
theorem case1_pointwise (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {L2 : ZMod L → ZMod L → ℝ}
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    {L3 : ZMod L → ℝ} {κ₂ : ℝ} (hκ₂ : 0 ≤ κ₂)
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * κ₂) :
    ∀ b : ZMod L,
      ((zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 ∨
        (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2) →
      L3 b ≤ 2 * J * loss32 W * tailT W ℓu ηu D (zdist L (a₁ - a₂)) * κ₂ := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hκ₃ := one_le_loss32 hW
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hzs : ∀ x y : ZMod L, zdist L (x - y) = zdist L (y - x) := by
    intro x y
    rw [← zdist_neg L (x - y)]
    congr 1
    ring
  have h12 : L2 a₂ a₁ ≤ J * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
    have := h531 a₂ a₁ (by rw [← hzs]; linarith)
    rwa [← hzs] at this
  -- the shifted tail estimate (5.32) at `C = 1/2`
  have hshift : ∀ y : ZMod L, (zdist L (a₁ - a₂) : ℝ) - ellStar W ℓu / 2 ≤
      (zdist L y : ℝ) → tailT W ℓu ηu D (zdist L y) ≤
        loss32 W * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
    intro y hy
    have h1 : tailT W ℓu ηu D (zdist L y) ≤
        tailT W ℓu ηu D ((zdist L (a₁ - a₂) : ℝ) - 1 / 2 * ellStar W ℓu) :=
      tailT_antitone hℓu (by linarith)
    refine h1.trans ?_
    rw [loss32]
    exact tailT_sub_le (ℓu := ℓu) (ηu := ηu) (D := D) hW hℓu
      (by norm_num : (0 : ℝ) ≤ 1 / 2) ((zdist L (a₁ - a₂) : ℝ))
  intro b hb
  have htri := zdist_sub_le_add L a₁ a₂ b
  rcases hb with h | h
  · -- `‖a₁ - b‖ ≤ ℓ*_u/2`, so `‖a₂ - b‖ ≥ ‖a₁ - a₂‖ - ℓ*_u/2 ≥ ℓ*_u/2`
    have hd2 : (zdist L (a₁ - a₂) : ℝ) - ellStar W ℓu / 2 ≤ (zdist L (a₂ - b) : ℝ) := by
      linarith
    have hd2' : ellStar W ℓu / 2 ≤ (zdist L (a₂ - b) : ℝ) := by linarith
    have hstep : L2 a₂ b ≤ J * (loss32 W * tailT W ℓu ηu D (zdist L (a₁ - a₂))) :=
      (h531 a₂ b hd2').trans (mul_le_mul_of_nonneg_left (hshift (a₂ - b) hd2) hJ0)
    refine (h558a b h).trans (mul_le_mul_of_nonneg_right ?_ hκ₂)
    nlinarith [mul_nonneg (mul_nonneg hJ0 hT0) (sub_nonneg.2 hκ₃)]
  · have hd1 : (zdist L (a₁ - a₂) : ℝ) - ellStar W ℓu / 2 ≤ (zdist L (a₁ - b) : ℝ) := by
      linarith
    have hd1' : ellStar W ℓu / 2 ≤ (zdist L (a₁ - b) : ℝ) := by linarith
    have hstep : L2 b a₁ ≤ J * (loss32 W * tailT W ℓu ηu D (zdist L (a₁ - a₂))) := by
      have h1 : L2 b a₁ ≤ J * tailT W ℓu ηu D (zdist L (a₁ - b)) := by
        have := h531 b a₁ (by rw [← hzs]; exact hd1')
        rwa [← hzs] at this
      exact h1.trans (mul_le_mul_of_nonneg_left (hshift (a₁ - b) hd1) hJ0)
    refine (h558b b h).trans (mul_le_mul_of_nonneg_right ?_ hκ₂)
    nlinarith [mul_nonneg (mul_nonneg hJ0 hT0) (sub_nonneg.2 hκ₃)]

omit [NeZero L] in
/-- **Case 2 of (5.60)–(5.61), pointwise.**  If `b` is at distance `≥ ℓ*_u/2` from both
external labels, then all three `G`-edges of the `3`-loop are long, (4.2) turns each of
them into a `2`-loop and (5.31) into a tail function:
`|L_{u,(-,+,+),(a₁,b,a₂)}| ≤ J^{3/2} (T(‖a₁-a₂‖) T(‖a₁-b‖) T(‖a₂-b‖))^{1/2}`. -/
theorem case2_pointwise (hJ : 0 ≤ J)
    {a₁ a₂ : ZMod L} {Gm : ZMod L → ZMod L → ℝ} (hGm : ∀ x y, 0 ≤ Gm x y)
    (hfar : ellStar W ℓu / 2 ≤ (zdist L (a₁ - a₂) : ℝ))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    {L3 : ZMod L → ℝ}
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂) :
    ∀ b : ZMod L, ellStar W ℓu / 2 < (zdist L (a₁ - b) : ℝ) →
      ellStar W ℓu / 2 < (zdist L (a₂ - b) : ℝ) →
      L3 b ≤ J * √J * (√(tailT W ℓu ηu D (zdist L (a₁ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₂ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₁ - a₂)))) := by
  intro b hb1 hb2
  have e1 := h42 a₁ b hb1.le
  have e2 := h42 a₂ b hb2.le
  have e3 := h42 a₁ a₂ hfar
  have hJ0 : 0 ≤ √J := Real.sqrt_nonneg _
  have hJ2 : √J * √J = J := Real.mul_self_sqrt hJ
  have p1 : Gm a₁ b * Gm a₂ b ≤
      (√J * √(tailT W ℓu ηu D (zdist L (a₁ - b)))) *
        (√J * √(tailT W ℓu ηu D (zdist L (a₂ - b)))) :=
    mul_le_mul e1 e2 (hGm _ _) (by positivity)
  have p2 : Gm a₁ b * Gm a₂ b * Gm a₁ a₂ ≤
      ((√J * √(tailT W ℓu ηu D (zdist L (a₁ - b)))) *
        (√J * √(tailT W ℓu ηu D (zdist L (a₂ - b))))) *
        (√J * √(tailT W ℓu ηu D (zdist L (a₁ - a₂)))) :=
    mul_le_mul p1 e3 (hGm _ _) (by positivity)
  refine (h560 b).trans (p2.trans (le_of_eq ?_))
  have hr : ((√J * √(tailT W ℓu ηu D (zdist L (a₁ - b)))) *
      (√J * √(tailT W ℓu ηu D (zdist L (a₂ - b))))) *
      (√J * √(tailT W ℓu ηu D (zdist L (a₁ - a₂))))
      = (√J * √J) * √J * (√(tailT W ℓu ηu D (zdist L (a₁ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₂ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₁ - a₂)))) := by ring
  rw [hr, hJ2]

/-- **(5.63)**, the far field `‖a₁ - a₂‖ ≥ ℓ*_u`:
`∑_b |L_{u,(-,+,+),(a₁,b,a₂)}| ≤ [(4 ℓ*_u + 8) J κ₃ κ₂ + J^{3/2}(168 ℓ_u A_u^{-1}
+ L √(W^{-D}))] T_{u,D}(‖a₁-a₂‖)`, where `κ₂` is the single-`G` bound of (5.57). -/
theorem sum_far_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {κ₂ : ℝ} (hκ₂ : 0 ≤ κ₂)
    (hGm : ∀ x y, 0 ≤ Gm x y)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * κ₂)
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂) :
    ∑ b : ZMod L, L3 b ≤
      ((4 * ellStar W ℓu + 8) * (J * loss32 W * κ₂)
        + J * √J * (168 * ℓu * (W * ℓu * ηu)⁻¹ + L * √(W ^ (-D))))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hsJ : 0 ≤ √J := Real.sqrt_nonneg _
  set T12 : ℝ := tailT W ℓu ηu D (zdist L (a₁ - a₂)) with hT12
  set g : ZMod L → ℝ := fun b => J * √J * (√(tailT W ℓu ηu D (zdist L (a₁ - b))) *
    √(tailT W ℓu ηu D (zdist L (a₂ - b))) * √T12) with hgdef
  have hg0 : ∀ b, 0 ≤ g b := fun b => by rw [hgdef]; positivity
  have hc1 : (0 : ℝ) ≤ 2 * J * loss32 W * T12 * κ₂ := by
    have := (one_le_loss32 hW).trans_lt' zero_lt_one
    positivity
  have hsplit := sum_le_split_two L hg0 (by positivity : (0:ℝ) ≤ ellStar W ℓu / 2) a₁ a₂ hc1
    (case1_pointwise L hW hℓ hJ hfar h531 hκ₂ h558a h558b)
    (case2_pointwise L hJ0 hGm (by linarith) h42 h560)
  -- the Case-2 sum
  have hgsum : ∑ b : ZMod L, g b = (J * √J * √T12) *
      ∑ b : ZMod L, (√(tailT W ℓu ηu D (zdist L (a₁ - b))) *
        √(tailT W ℓu ηu D (zdist L (a₂ - b)))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hgdef]; ring
  have hconv := sum_sqrt_tailT_mul_le L hW0 hℓu hηu D a₁ a₂
  have hsq : √T12 * √T12 = T12 := Real.mul_self_sqrt hT0
  have hcase2 : ∑ b : ZMod L, g b ≤
      J * √J * (168 * ℓu * (W * ℓu * ηu)⁻¹ + L * √(W ^ (-D))) * T12 := by
    rw [hgsum]
    have := mul_le_mul_of_nonneg_left hconv (by positivity : (0:ℝ) ≤ J * √J * √T12)
    refine this.trans (le_of_eq ?_)
    rw [show J * √J * √T12 * ((168 * ℓu * (W * ℓu * ηu)⁻¹ + L * √(W ^ (-D))) * √T12)
      = J * √J * (168 * ℓu * (W * ℓu * ηu)⁻¹ + L * √(W ^ (-D))) * (√T12 * √T12) from by ring,
      hsq]
  refine hsplit.trans ?_
  have hcase1 : (4 * (ellStar W ℓu / 2) + 4) * (2 * J * loss32 W * T12 * κ₂)
      = (4 * ellStar W ℓu + 8) * (J * loss32 W * κ₂) * T12 := by ring
  rw [hcase1]
  nlinarith [hcase2]

end FarField

/-! ### The near field `‖a₁ - a₂‖ ≤ ℓ*_u`: (5.53)–(5.55) -/

section NearField

variable {W ℓu ℓs ηu D : ℝ}

/-- `ℓ**_u = (log W)^3 ℓ_u` (defined just before (5.53)). -/
noncomputable def ellStarStar (W ℓu : ℝ) : ℝ := log W ^ (3 : ℝ) * ℓu

theorem ellStarStar_nonneg (hW : 1 ≤ W) (hℓu : 0 ≤ ℓu) : 0 ≤ ellStarStar W ℓu := by
  have := Real.log_nonneg hW; unfold ellStarStar; positivity

/-- In the near field `‖a₁ - a₂‖ ≤ ℓ*_u` the prefactor of `T_{u,D}` is comparable to
`(W ℓ_u η_u)^{-2}`: `A_u^{-2} ≤ e^{(log W)^{3/4}} T_{u,D}(‖a₁-a₂‖)`. -/
theorem inv_sq_le_tailT (hW : 1 ≤ W) (hℓu : 0 < ℓu) (_hηu : 0 < ηu) {d : ℝ}
    (hd : d ≤ ellStar W ℓu) :
    ((W * ℓu * ηu) ^ 2)⁻¹ ≤ exp (log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d := by
  have h := RBM.inv_sq_le_tailT (ℓu := ℓu) (ηu := ηu) (D := D) hW hℓu
    (by norm_num : (0 : ℝ) ≤ 1) (by linarith : d ≤ 1 * ellStar W ℓu)
  rwa [Real.sqrt_one, one_mul] at h

/-- **(5.53)+(5.54)+(5.55)**, the near field `‖a₁ - a₂‖ ≤ ℓ*_u`.

The `b`-sum splits at `ℓ**_u = (log W)^3 ℓ_u`: the `≤ ℓ**_u` part is `(2ℓ**_u + 2)` sites
each carrying the `n = 3` case of the a-priori loop bound (2.73), the `> ℓ**_u` part is
the remainder `ρ` of (5.54), kept explicit.  `κ₁` is the (5.52) prefactor. -/
theorem eG_near_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    {a₁ a₂ : ZMod L} (hnear : (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu)
    {L3 : ZMod L → ℝ} {ρ κ₁ EG : ℝ} (hρ : 0 ≤ ρ) (hκ₁ : 0 ≤ κ₁)
    (h273 : ∀ b, L3 b ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L3 b ≤ ρ)
    (hEG : EG ≤ κ₁ * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * κ₁ * ((2 * log W ^ (3 : ℝ) + 2 / ℓu) * (ℓu / ℓs) ^ 2 *
          exp (log W ^ (3 / 4 : ℝ))) * tailT W ℓu ηu D (zdist L (a₁ - a₂))
        + κ₁ * (ℓu * ηu)⁻¹ * L * ρ := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hlog : 0 ≤ log W := Real.log_nonneg hW
  have hss : 0 ≤ ellStarStar W ℓu := ellStarStar_nonneg hW hℓ.le
  have hq : (0 : ℝ) ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hsplit := sum_le_split_one L (fun _ => hρ) hss a₁ hq
    (fun b _ => h273 b) (fun b hb => h554 b hb)
  have hconst : ∑ _b : ZMod L, ρ = (L : ℝ) * ρ := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hconst] at hsplit
  -- convert `A^{-2}` into `T`
  have hinv := inv_sq_le_tailT (D := D) hW hℓ hηu hnear
  have hr : (0 : ℝ) ≤ (ℓu / ℓs) ^ 2 := by positivity
  have hpre : (0 : ℝ) ≤ κ₁ * (ℓu * ηu)⁻¹ := by positivity
  have hmain : κ₁ * (ℓu * ηu)⁻¹ * ((2 * ellStarStar W ℓu + 2) *
        ((ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)) ≤
      ηu⁻¹ * κ₁ * ((2 * log W ^ (3 : ℝ) + 2 / ℓu) * (ℓu / ℓs) ^ 2 *
        exp (log W ^ (3 / 4 : ℝ))) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
    have hstep : (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹ ≤
        (ℓu / ℓs) ^ 2 * (exp (log W ^ (3 / 4 : ℝ)) *
          tailT W ℓu ηu D (zdist L (a₁ - a₂))) := mul_le_mul_of_nonneg_left hinv hr
    have hfac : (0 : ℝ) ≤ κ₁ * (ℓu * ηu)⁻¹ * (2 * ellStarStar W ℓu + 2) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hstep hfac
    refine le_trans (le_of_eq (by ring)) (h1.trans (le_of_eq ?_))
    rw [ellStarStar]
    field_simp
  calc EG ≤ κ₁ * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b := hEG
    _ ≤ κ₁ * (ℓu * ηu)⁻¹ * ((2 * ellStarStar W ℓu + 2) *
          ((ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹) + (L : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_left hsplit hpre
    _ = κ₁ * (ℓu * ηu)⁻¹ * ((2 * ellStarStar W ℓu + 2) *
          ((ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)) + κ₁ * (ℓu * ηu)⁻¹ * ((L : ℝ) * ρ) := by
        ring
    _ ≤ _ := by linarith [hmain]

end NearField

/-! ### (5.56), (5.58), (5.60) from the definition of the `3`-loop -/

section Loop3

open Matrix

variable (Wb : ℕ) [NeZero Wb] {H : Matrix (ZMod L × Fin Wb) (ZMod L × Fin Wb) ℂ} {z : ℂ}

set_option linter.unusedSectionVars false in
theorem gloop_three_expand (s₁ s₂ s₃ : Bool) (a₁ a₂ a₃ : ZMod L) :
    gloop L Wb H z ⟨[s₁, s₂, s₃], [a₁, a₂, a₃]⟩
      = ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        (Gsig H z s₁ p q * (if q.1 = a₁ then (Wb : ℂ)⁻¹ else 0)) *
        ((Gsig H z s₂ q r * (if r.1 = a₂ then (Wb : ℂ)⁻¹ else 0)) *
         (Gsig H z s₃ r p * (if p.1 = a₃ then (Wb : ℂ)⁻¹ else 0))) := by
  rw [gloop, Matrix.trace]
  simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one, diag_apply, Matrix.mul_apply,
    Eblk, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.mul_sum]

omit [NeZero Wb] in
theorem sum_blockIndicator (a : ZMod L) (c : ℝ) :
    ∑ x : ZMod L × Fin Wb, (if x.1 = a then c else 0) = Wb * c := by
  rw [Fintype.sum_prod_type]
  have h : ∀ x : ZMod L, (∑ _y : Fin Wb, (if x = a then c else 0))
      = (Wb : ℝ) * (if x = a then c else 0) := by
    intro x; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [h]
  rw [← Finset.mul_sum]
  simp

theorem sum_blockWeight (a : ZMod L) (c : ℝ) :
    ∑ x : ZMod L × Fin Wb, ((if x.1 = a then (Wb : ℝ)⁻¹ else 0) * c) = c := by
  have hWb : (Wb : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne Wb)
  have h : ∀ x : ZMod L × Fin Wb, ((if x.1 = a then (Wb : ℝ)⁻¹ else 0) * c)
      = (if x.1 = a then (Wb : ℝ)⁻¹ * c else 0) := by intro x; split_ifs <;> ring
  simp_rw [h, sum_blockIndicator]
  field_simp

/-- **(5.60)**: every entry of the `3`-loop is a product of three `G`-entries, one per
pair of external labels. -/
theorem norm_gloop_three_le {Gm : ZMod L → ZMod L → ℝ} (s₁ s₂ s₃ : Bool) (a₁ a₂ a₃ : ZMod L)
    (hGm : ∀ x y, 0 ≤ Gm x y)
    (h1 : ∀ p q : ZMod L × Fin Wb, p.1 = a₃ → q.1 = a₁ → ‖Gsig H z s₁ p q‖ ≤ Gm a₃ a₁)
    (h2 : ∀ q r : ZMod L × Fin Wb, q.1 = a₁ → r.1 = a₂ → ‖Gsig H z s₂ q r‖ ≤ Gm a₁ a₂)
    (h3 : ∀ r p : ZMod L × Fin Wb, r.1 = a₂ → p.1 = a₃ → ‖Gsig H z s₃ r p‖ ≤ Gm a₂ a₃) :
    ‖gloop L Wb H z ⟨[s₁, s₂, s₃], [a₁, a₂, a₃]⟩‖ ≤ Gm a₃ a₁ * (Gm a₁ a₂ * Gm a₂ a₃) := by
  classical
  set C : ℝ := Gm a₃ a₁ * (Gm a₁ a₂ * Gm a₂ a₃) with hC
  have hC0 : 0 ≤ C := by rw [hC]; exact mul_nonneg (hGm _ _) (mul_nonneg (hGm _ _) (hGm _ _))
  rw [gloop_three_expand]
  have hnorm : ‖∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        (Gsig H z s₁ p q * (if q.1 = a₁ then (Wb : ℂ)⁻¹ else 0)) *
        ((Gsig H z s₂ q r * (if r.1 = a₂ then (Wb : ℂ)⁻¹ else 0)) *
         (Gsig H z s₃ r p * (if p.1 = a₃ then (Wb : ℂ)⁻¹ else 0)))‖ ≤
      ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        ‖(Gsig H z s₁ p q * (if q.1 = a₁ then (Wb : ℂ)⁻¹ else 0)) *
        ((Gsig H z s₂ q r * (if r.1 = a₂ then (Wb : ℂ)⁻¹ else 0)) *
         (Gsig H z s₃ r p * (if p.1 = a₃ then (Wb : ℂ)⁻¹ else 0)))‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    exact norm_sum_le _ _
  refine hnorm.trans ?_
  have hpt : ∀ p q r : ZMod L × Fin Wb,
      ‖(Gsig H z s₁ p q * (if q.1 = a₁ then (Wb : ℂ)⁻¹ else 0)) *
        ((Gsig H z s₂ q r * (if r.1 = a₂ then (Wb : ℂ)⁻¹ else 0)) *
         (Gsig H z s₃ r p * (if p.1 = a₃ then (Wb : ℂ)⁻¹ else 0)))‖ ≤
      (if p.1 = a₃ then (Wb : ℝ)⁻¹ else 0) *
        ((if q.1 = a₁ then (Wb : ℝ)⁻¹ else 0) *
          ((if r.1 = a₂ then (Wb : ℝ)⁻¹ else 0) * C)) := by
    intro p q r
    by_cases hp : p.1 = a₃
    · by_cases hq : q.1 = a₁
      · by_cases hr : r.1 = a₂
        · have b1 := h1 p q hp hq
          have b2 := h2 q r hq hr
          have b3 := h3 r p hr hp
          have hn1 : 0 ≤ ‖Gsig H z s₁ p q‖ := norm_nonneg _
          have hn2 : 0 ≤ ‖Gsig H z s₂ q r‖ := norm_nonneg _
          have hn3 : 0 ≤ ‖Gsig H z s₃ r p‖ := norm_nonneg _
          have hWbi : (0 : ℝ) ≤ (Wb : ℝ)⁻¹ := by positivity
          have hw : ‖(Wb : ℂ)⁻¹‖ = (Wb : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
          have hprod : ‖Gsig H z s₁ p q‖ * ‖Gsig H z s₂ q r‖ * ‖Gsig H z s₃ r p‖ ≤ C := by
            rw [hC]
            calc ‖Gsig H z s₁ p q‖ * ‖Gsig H z s₂ q r‖ * ‖Gsig H z s₃ r p‖
                ≤ Gm a₃ a₁ * Gm a₁ a₂ * Gm a₂ a₃ :=
                  mul_le_mul (mul_le_mul b1 b2 hn2 (hGm _ _)) b3 hn3
                    (mul_nonneg (hGm _ _) (hGm _ _))
              _ = Gm a₃ a₁ * (Gm a₁ a₂ * Gm a₂ a₃) := by ring
          simp only [hp, hq, hr, ite_true, norm_mul, hw]
          calc ‖Gsig H z s₁ p q‖ * (Wb : ℝ)⁻¹ *
                (‖Gsig H z s₂ q r‖ * (Wb : ℝ)⁻¹ * (‖Gsig H z s₃ r p‖ * (Wb : ℝ)⁻¹))
              = (‖Gsig H z s₁ p q‖ * ‖Gsig H z s₂ q r‖ * ‖Gsig H z s₃ r p‖) *
                  ((Wb : ℝ)⁻¹ * ((Wb : ℝ)⁻¹ * (Wb : ℝ)⁻¹)) := by ring
            _ ≤ C * ((Wb : ℝ)⁻¹ * ((Wb : ℝ)⁻¹ * (Wb : ℝ)⁻¹)) :=
                mul_le_mul_of_nonneg_right hprod (by positivity)
            _ = (Wb : ℝ)⁻¹ * ((Wb : ℝ)⁻¹ * ((Wb : ℝ)⁻¹ * C)) := by ring
        · simp [hr]
      · simp [hq]
    · simp [hp]
  refine (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ =>
    Finset.sum_le_sum fun r _ => hpt p q r).trans ?_
  have e1 : ∀ p q : ZMod L × Fin Wb,
      (∑ r : ZMod L × Fin Wb, (if p.1 = a₃ then (Wb : ℝ)⁻¹ else 0) *
        ((if q.1 = a₁ then (Wb : ℝ)⁻¹ else 0) *
          ((if r.1 = a₂ then (Wb : ℝ)⁻¹ else 0) * C)))
      = (if p.1 = a₃ then (Wb : ℝ)⁻¹ else 0) * ((if q.1 = a₁ then (Wb : ℝ)⁻¹ else 0) * C) := by
    intro p q
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_blockWeight]
  simp_rw [e1]
  have e2 : ∀ p : ZMod L × Fin Wb,
      (∑ q : ZMod L × Fin Wb, (if p.1 = a₃ then (Wb : ℝ)⁻¹ else 0) *
        ((if q.1 = a₁ then (Wb : ℝ)⁻¹ else 0) * C))
      = (if p.1 = a₃ then (Wb : ℝ)⁻¹ else 0) * C := by
    intro p
    rw [← Finset.mul_sum, sum_blockWeight]
  simp_rw [e2]
  exact le_of_eq (sum_blockWeight L Wb a₃ C)

/-! #### The Cauchy–Schwarz step (5.56)/(5.58) -/

/-- Pointwise Cauchy–Schwarz behind (5.56): `|αβγ| ≤ ½(|α|² + |β|²)|γ|`. -/
theorem norm_mul_three_le (α β γ : ℂ) :
    ‖α * β * γ‖ ≤ (‖α‖ ^ 2 + ‖β‖ ^ 2) / 2 * ‖γ‖ := by
  rw [norm_mul, norm_mul]
  have h : ‖α‖ * ‖β‖ ≤ (‖α‖ ^ 2 + ‖β‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖α‖ - ‖β‖)]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg γ)

omit [NeZero Wb] in
theorem sum3_comm (F : (ZMod L × Fin Wb) → (ZMod L × Fin Wb) → (ZMod L × Fin Wb) → ℝ) :
    ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb, F p q r
      = ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb, ∑ p : ZMod L × Fin Wb, F p q r := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_comm

/-- `w(x, a) = W^{-1} 1(x ∈ I_a)`, the weight a block label attaches to a site. -/
noncomputable def blkW (x : ZMod L × Fin Wb) (a : ZMod L) : ℝ :=
  if x.1 = a then (Wb : ℝ)⁻¹ else 0

omit [NeZero L] [NeZero Wb] in
theorem blkW_nonneg (x : ZMod L × Fin Wb) (a : ZMod L) : 0 ≤ blkW L Wb x a := by
  unfold blkW; split_ifs
  · positivity
  · exact le_rfl

/-- `RBM.sum_block_ite` at the real scalars. -/
theorem sum_block_ite_real (f : (ZMod L × Fin Wb) → (ZMod L × Fin Wb) → ℝ) (a b : ZMod L) :
    (∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb,
        (if p.1 = b then (if q.1 = a then f p q else 0) else 0))
      = ∑ β : Fin Wb, ∑ α : Fin Wb, f (b, β) (a, α) := by
  have h := sum_block_ite (L := L) (W := Wb) (fun p q => ((f p q : ℝ) : ℂ)) a b
  have h2 := congrArg Complex.re h
  simpa [Complex.re_sum, apply_ite Complex.re] using h2

/-- **The `blkW`-weighted square sum of `G`-entries between two blocks is the `(+,-)`
`2`-loop**: `W^{-2} ∑_{x ∈ I_b, y ∈ I_a} |G_{xy}|² = L_{(+,-),(a,b)}`.  This is what turns
the Cauchy–Schwarz step (5.56) into the loop statement (5.58). -/
theorem sum_blkW_normSq (hH : H.IsHermitian) (a b : ZMod L) :
    (∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb,
        blkW L Wb p b * (blkW L Wb q a * ‖green H z p q‖ ^ 2))
      = (gloop L Wb H z ⟨[true, false], [a, b]⟩).re := by
  have hL : ∀ p q : ZMod L × Fin Wb,
      blkW L Wb p b * (blkW L Wb q a * ‖green H z p q‖ ^ 2)
      = (if p.1 = b then (if q.1 = a then
          (Wb : ℝ)⁻¹ * ((Wb : ℝ)⁻¹ * ‖green H z p q‖ ^ 2) else 0) else 0) := by
    intro p q; unfold blkW; split_ifs <;> ring
  simp_rw [hL]
  rw [sum_block_ite_real, gloop_two_plus_minus_blocks hH a b]
  simp only [Complex.normSq_eq_norm_sq]
  have hc : ((Wb : ℂ))⁻¹ ^ 2 * ∑ β : Fin Wb, ∑ α : Fin Wb,
      ((‖green H z (b, β) (a, α)‖ ^ 2 : ℝ) : ℂ)
      = (((Wb : ℝ)⁻¹ ^ 2 *
          ∑ β : Fin Wb, ∑ α : Fin Wb, ‖green H z (b, β) (a, α)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [hc, Complex.ofReal_re, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- The `σ = -` version of `sum_blkW_normSq`: `|G(z̄)_{qr}| = |G(z)_{rq}|` for Hermitian `H`. -/
theorem sum_blkW_normSq_conj (hH : H.IsHermitian) (a b : ZMod L) :
    (∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        blkW L Wb q a * (blkW L Wb r b * ‖Gsig H z false q r‖ ^ 2))
      = (gloop L Wb H z ⟨[true, false], [a, b]⟩).re := by
  have hct : (Gsig H z true)ᴴ = Gsig H z false := by
    simpa using Gsig_conjTranspose hH z true
  have hconj : ∀ q r : ZMod L × Fin Wb, ‖Gsig H z false q r‖ = ‖green H z r q‖ := by
    intro q r
    have he : Gsig H z false q r = (starRingEnd ℂ) (green H z r q) := by
      calc Gsig H z false q r = ((Gsig H z true)ᴴ) q r := by rw [hct]
        _ = (starRingEnd ℂ) (green H z r q) := by rw [Matrix.conjTranspose_apply]; rfl
    rw [he, RCLike.norm_conj]
  simp_rw [hconj]
  rw [Finset.sum_comm]
  rw [← sum_blkW_normSq (z := z) L Wb hH a b]
  exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ => by ring

/-- **(5.56)/(5.58)**: the Cauchy–Schwarz step on the `3`-loop.  `S₁`, `S₂` bound the two
squared edges (which `sum_blkW_normSq` identifies with `2`-loops) and `κ` bounds the
`W^{-1}`-normalized block sum of the remaining edge, which is the quantity (5.57)
estimates. -/
theorem norm_gloop_three_le_schwarz (s₁ s₂ s₃ : Bool) (a₁ a₂ a₃ : ZMod L) {S₁ S₂ κ : ℝ}
    (hκ : 0 ≤ κ)
    (hR₁ : ∀ p : ZMod L × Fin Wb, p.1 = a₃ →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r a₂ * ‖Gsig H z s₃ r p‖ ≤ κ)
    (hR₂ : ∀ r : ZMod L × Fin Wb, r.1 = a₂ →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p a₃ * ‖Gsig H z s₃ r p‖ ≤ κ)
    (hS₁ : ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb,
      blkW L Wb p a₃ * (blkW L Wb q a₁ * ‖Gsig H z s₁ p q‖ ^ 2) ≤ S₁)
    (hS₂ : ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
      blkW L Wb q a₁ * (blkW L Wb r a₂ * ‖Gsig H z s₂ q r‖ ^ 2) ≤ S₂) :
    ‖gloop L Wb H z ⟨[s₁, s₂, s₃], [a₁, a₂, a₃]⟩‖ ≤ (S₁ + S₂) / 2 * κ := by
  classical
  set G₁ := fun (p q : ZMod L × Fin Wb) => Gsig H z s₁ p q with hG₁
  set G₂ := fun (q r : ZMod L × Fin Wb) => Gsig H z s₂ q r with hG₂
  set G₃ := fun (r p : ZMod L × Fin Wb) => Gsig H z s₃ r p with hG₃
  set w := blkW L Wb with hw
  have hw0 : ∀ x a, 0 ≤ w x a := blkW_nonneg L Wb
  rw [gloop_three_expand]
  have hnorm : ‖∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        (G₁ p q * (if q.1 = a₁ then (Wb : ℂ)⁻¹ else 0)) *
        ((G₂ q r * (if r.1 = a₂ then (Wb : ℂ)⁻¹ else 0)) *
         (G₃ r p * (if p.1 = a₃ then (Wb : ℂ)⁻¹ else 0)))‖ ≤
      ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        (w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * (w r a₂ * ‖G₃ r p‖) / 2
          + w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * (w p a₃ * ‖G₃ r p‖) / 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    have hwq : ‖(if q.1 = a₁ then (Wb : ℂ)⁻¹ else 0)‖ = w q a₁ := by
      rw [hw, blkW]; split_ifs <;> simp
    have hwr : ‖(if r.1 = a₂ then (Wb : ℂ)⁻¹ else 0)‖ = w r a₂ := by
      rw [hw, blkW]; split_ifs <;> simp
    have hwp : ‖(if p.1 = a₃ then (Wb : ℂ)⁻¹ else 0)‖ = w p a₃ := by
      rw [hw, blkW]; split_ifs <;> simp
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hwp, hwq, hwr]
    set x := ‖G₁ p q‖ with hx
    set y := ‖G₂ q r‖ with hy
    set g := ‖G₃ r p‖ with hg
    have hx0 : 0 ≤ x := norm_nonneg _
    have hy0 : 0 ≤ y := norm_nonneg _
    have hg0 : 0 ≤ g := norm_nonneg _
    have hup := hw0 p a₃
    have huq := hw0 q a₁
    have hur := hw0 r a₂
    have key : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith [sq_nonneg (x - y)]
    have hfac : (0 : ℝ) ≤ w p a₃ * w q a₁ * w r a₂ * g := by positivity
    calc x * w q a₁ * (y * w r a₂ * (g * w p a₃))
        = (w p a₃ * w q a₁ * w r a₂ * g) * (x * y) := by ring
      _ ≤ (w p a₃ * w q a₁ * w r a₂ * g) * ((x ^ 2 + y ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left key hfac
      _ = w p a₃ * (w q a₁ * x ^ 2) * (w r a₂ * g) / 2
            + w q a₁ * (w r a₂ * y ^ 2) * (w p a₃ * g) / 2 := by ring
  refine hnorm.trans ?_
  have hsplit : ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        (w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * (w r a₂ * ‖G₃ r p‖) / 2
          + w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * (w p a₃ * ‖G₃ r p‖) / 2)
      = (∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
          w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * (w r a₂ * ‖G₃ r p‖) / 2)
        + ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
          w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * (w p a₃ * ‖G₃ r p‖) / 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_add_distrib
  rw [hsplit]
  have hA : (∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * (w r a₂ * ‖G₃ r p‖) / 2) ≤ S₁ / 2 * κ := by
    have hstep : ∀ p q : ZMod L × Fin Wb,
        (∑ r : ZMod L × Fin Wb, w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * (w r a₂ * ‖G₃ r p‖) / 2)
          ≤ w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * κ / 2 := by
      intro p q
      have hpull : (∑ r : ZMod L × Fin Wb,
            w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * (w r a₂ * ‖G₃ r p‖) / 2)
          = (w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) / 2) *
            ∑ r : ZMod L × Fin Wb, w r a₂ * ‖G₃ r p‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
      rw [hpull]
      by_cases hp : p.1 = a₃
      · have hc : (0 : ℝ) ≤ w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) / 2 := by
          have := hw0 p a₃; have := hw0 q a₁; positivity
        have := mul_le_mul_of_nonneg_left (hR₁ p hp) hc
        calc _ ≤ w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) / 2 * κ := this
          _ = w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * κ / 2 := by ring
      · have h0 : w p a₃ = 0 := by rw [hw, blkW]; simp [hp]
        simp [h0]
    refine (Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hstep p q).trans ?_
    have hfold : (∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb,
          w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) * κ / 2)
        = (κ / 2) * ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb,
            w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hfold]
    have := mul_le_mul_of_nonneg_left hS₁ (by positivity : (0 : ℝ) ≤ κ / 2)
    calc (κ / 2) * ∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb,
          w p a₃ * (w q a₁ * ‖G₁ p q‖ ^ 2) ≤ (κ / 2) * S₁ := this
      _ = S₁ / 2 * κ := by ring
  have hB : (∑ p : ZMod L × Fin Wb, ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
        w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * (w p a₃ * ‖G₃ r p‖) / 2) ≤ S₂ / 2 * κ := by
    rw [sum3_comm L Wb]
    have hstep : ∀ q r : ZMod L × Fin Wb,
        (∑ p : ZMod L × Fin Wb, w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * (w p a₃ * ‖G₃ r p‖) / 2)
          ≤ w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * κ / 2 := by
      intro q r
      have hpull : (∑ p : ZMod L × Fin Wb,
            w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * (w p a₃ * ‖G₃ r p‖) / 2)
          = (w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) / 2) *
            ∑ p : ZMod L × Fin Wb, w p a₃ * ‖G₃ r p‖ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
      rw [hpull]
      by_cases hr : r.1 = a₂
      · have hc : (0 : ℝ) ≤ w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) / 2 := by
          have := hw0 q a₁; have := hw0 r a₂; positivity
        have := mul_le_mul_of_nonneg_left (hR₂ r hr) hc
        calc _ ≤ w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) / 2 * κ := this
          _ = w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * κ / 2 := by ring
      · have h0 : w r a₂ = 0 := by rw [hw, blkW]; simp [hr]
        simp [h0]
    refine (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun r _ => hstep q r).trans ?_
    have hfold : (∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
          w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) * κ / 2)
        = (κ / 2) * ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
            w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hfold]
    have := mul_le_mul_of_nonneg_left hS₂ (by positivity : (0 : ℝ) ≤ κ / 2)
    calc (κ / 2) * ∑ q : ZMod L × Fin Wb, ∑ r : ZMod L × Fin Wb,
          w q a₁ * (w r a₂ * ‖G₂ q r‖ ^ 2) ≤ (κ / 2) * S₂ := this
      _ = S₂ / 2 * κ := by ring
  have hfin : S₁ / 2 * κ + S₂ / 2 * κ = (S₁ + S₂) / 2 * κ := by ring
  linarith [hA, hB]

/-- One rotation of a `3`-loop (`RBM.gloop_rotate`). -/
theorem gloop_rot1 (s₁ s₂ s₃ : Bool) (c₁ c₂ c₃ : ZMod L) :
    gloop L Wb H z ⟨[s₁, s₂, s₃], [c₁, c₂, c₃]⟩
      = gloop L Wb H z ⟨[s₂, s₃, s₁], [c₂, c₃, c₁]⟩ := by
  have h := gloop_rotate (L := L) (W := Wb) (H := H) (z := z) s₁ c₁
    (σ := [s₂, s₃]) (a := [c₂, c₃]) rfl
  simpa using h

/-- **(5.58)**, the branch the paper's "WLOG `|a₁ - b| ≤ ℓ*_u/2`" uses: the two squared
edges are `a₁–a₂` and `a₂–b`, the surviving one is `b–a₁`. -/
theorem gloop_h558a (hH : H.IsHermitian) (a₁ a₂ b : ZMod L) {κ : ℝ} (hκ : 0 ≤ κ)
    (hC : ∀ p : ZMod L × Fin Wb, p.1 = b →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r a₁ * ‖green H z r p‖ ≤ κ)
    (hR : ∀ r : ZMod L × Fin Wb, r.1 = a₁ →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p b * ‖green H z r p‖ ≤ κ) :
    ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      ((gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re
        + (gloop L Wb H z ⟨[true, false], [a₂, b]⟩).re) / 2 * κ := by
  rw [gloop_rot1, gloop_rot1]
  have hs := norm_gloop_three_le_schwarz (z := z) L Wb true false true a₂ a₁ b
    (S₁ := (gloop L Wb H z ⟨[true, false], [a₂, b]⟩).re)
    (S₂ := (gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re) hκ hC hR
    (le_of_eq (sum_blkW_normSq L Wb hH a₂ b))
    (le_of_eq (sum_blkW_normSq_conj L Wb hH a₂ a₁))
  calc ‖gloop L Wb H z ⟨[true, false, true], [a₂, a₁, b]⟩‖
      ≤ ((gloop L Wb H z ⟨[true, false], [a₂, b]⟩).re
          + (gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re) / 2 * κ := hs
    _ = ((gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re
          + (gloop L Wb H z ⟨[true, false], [a₂, b]⟩).re) / 2 * κ := by ring

/-- **(5.58)**, the symmetric branch (`|a₂ - b| ≤ ℓ*_u/2`): the squared edges are `a₁–a₂`
and `a₁–b`, the surviving one is `b–a₂`. -/
theorem gloop_h558b (hH : H.IsHermitian) (a₁ a₂ b : ZMod L) {κ : ℝ} (hκ : 0 ≤ κ)
    (hC : ∀ p : ZMod L × Fin Wb, p.1 = a₂ →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r b * ‖green H z r p‖ ≤ κ)
    (hR : ∀ r : ZMod L × Fin Wb, r.1 = b →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p a₂ * ‖green H z r p‖ ≤ κ) :
    ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      ((gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re
        + (gloop L Wb H z ⟨[true, false], [b, a₁]⟩).re) / 2 * κ :=
  norm_gloop_three_le_schwarz (z := z) L Wb false true true a₁ b a₂
    (S₁ := (gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re)
    (S₂ := (gloop L Wb H z ⟨[true, false], [b, a₁]⟩).re) hκ hC hR
    (le_of_eq (sum_blkW_normSq_conj L Wb hH a₂ a₁))
    (le_of_eq (sum_blkW_normSq L Wb hH b a₁))

end Loop3

/-! ### (5.35) -/

section Main

variable {W ℓu ℓs ηu D J : ℝ}

/-- The `W^{o(1)}` coefficient of the near-field term of (5.35). -/
noncomputable def cNear (W ℓu : ℝ) : ℝ :=
  (2 * log W ^ (3 : ℝ) + 2 / ℓu) * exp (log W ^ (3 / 4 : ℝ))

/-- The `W^{o(1)}` coefficient of the Case-1 far-field term of (5.35). -/
noncomputable def cFar (W ℓu : ℝ) : ℝ :=
  (4 * log W ^ (3 / 2 : ℝ) + 8 / ℓu) * loss32 W

theorem cNear_nonneg (hW : 1 ≤ W) (hℓu : 0 < ℓu) : 0 ≤ cNear W ℓu := by
  have := Real.log_nonneg hW; unfold cNear; positivity

theorem cFar_nonneg (hW : 1 ≤ W) (hℓu : 0 < ℓu) : 0 ≤ cFar W ℓu := by
  have := Real.log_nonneg hW
  have h2 : 0 < loss32 W := loss32_pos W
  unfold cFar; positivity

/-- **The far field of (5.35)**: for `‖a₁ - a₂‖ ≥ ℓ*_u`,
`E^{(G)} ≤ η_u^{-1} κ₁ (c_far J κ₂ + J^{3/2}(168 A_u^{-1} + L √(W^{-D}) / ℓ_u))
 T_{u,D}(‖a₁-a₂‖)`. -/
theorem eG_far_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {κ₁ κ₂ EG : ℝ}
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * κ₂)
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ κ₁ * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * κ₁ * (cFar W ℓu * J * κ₂
        + J * √J * (168 * (W * ℓu * ηu)⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
  have hℓ : 0 < ℓu := by linarith
  have hpre : (0 : ℝ) ≤ κ₁ * (ℓu * ηu)⁻¹ := by positivity
  refine hEG.trans ((mul_le_mul_of_nonneg_left
    (sum_far_le L hW hℓu hηu hJ hfar hκ₂ hGm h531 h42 h558a h558b h560) hpre).trans
    (le_of_eq ?_))
  unfold cFar ellStar
  field_simp

/-- **(5.35)**, in the explicit form the proof on pp. 59–61 gives.

`κ₁` is the (5.52) prefactor (the paper's `Ξ^{(L)}_{u,2} A_u` from (4.5), or the loop bound
(2.73)); `κ₂` is the single-`G` bound of (5.57); `ρ` is the (5.54) remainder.
`cNear` and `cFar` are `W^{o(1)}`. -/
theorem eG_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (a₁ a₂ : ZMod L)
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {κ₁ κ₂ ρ EG : ℝ}
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, L3 b ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L3 b ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * κ₂)
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ κ₁ * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * κ₁ * (cNear W ℓu * (ℓu / ℓs) ^ 2 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0)
        + cFar W ℓu * J * κ₂
        + J * √J * (168 * (W * ℓu * ηu)⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂))
      + κ₁ * (ℓu * ηu)⁻¹ * L * ρ := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hsJ : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hcF : 0 ≤ cFar W ℓu := cFar_nonneg hW hℓ
  have hcN : 0 ≤ cNear W ℓu := cNear_nonneg hW hℓ
  have hε : (0 : ℝ) ≤ √(W ^ (-D)) := Real.sqrt_nonneg _
  have hrem : (0 : ℝ) ≤ κ₁ * (ℓu * ηu)⁻¹ * L * ρ := by positivity
  have hfarterm : (0 : ℝ) ≤ ηu⁻¹ * κ₁ * (cFar W ℓu * J * κ₂
      + J * √J * (168 * (W * ℓu * ηu)⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by positivity
  have hnearterm : (0 : ℝ) ≤ ηu⁻¹ * κ₁ * (cNear W ℓu * (ℓu / ℓs) ^ 2) *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by positivity
  split_ifs with hd
  · have := eG_near_le (D := D) L hW hℓu hℓs hηu hd hρ hκ₁ h273 h554 hEG
    have heq : ηu⁻¹ * κ₁ * ((2 * log W ^ (3 : ℝ) + 2 / ℓu) * (ℓu / ℓs) ^ 2 *
        exp (log W ^ (3 / 4 : ℝ))) * tailT W ℓu ηu D (zdist L (a₁ - a₂))
        = ηu⁻¹ * κ₁ * (cNear W ℓu * (ℓu / ℓs) ^ 2 * 1) *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
      unfold cNear; ring
    rw [heq] at this
    nlinarith [this, hfarterm]
  · rw [not_le] at hd
    have := eG_far_le L hW hℓu hηu hJ hd.le hκ₁ hκ₂ hGm h531 h42 h558a h558b h560 hEG
    nlinarith [this, hrem]

/-! ### The two shapes -/

section Shapes

/-- `A^{-1/2} ≤ A^{-1/3}` and `A^{-1} ≤ A^{-1/3}` for `A ≥ 1`, in the `rpow` spelling
used by `RBM.Step2.Hyp.eG`. -/
theorem inv_sqrt_le_rpow_third {A : ℝ} (hA : 1 ≤ A) :
    (√A)⁻¹ ≤ A⁻¹ ^ ((1 : ℝ) / 3) := by
  have hA0 : 0 < A := by linarith
  have h1 : (0 : ℝ) < A⁻¹ := by positivity
  have h2 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have := Real.rpow_le_rpow_of_exponent_ge h1 h2 (by norm_num : (1 : ℝ) / 3 ≤ 1 / 2)
  rwa [show A⁻¹ ^ ((1 : ℝ) / 2) = (√A)⁻¹ by rw [← Real.sqrt_eq_rpow, Real.sqrt_inv]] at this

theorem inv_le_rpow_third {A : ℝ} (hA : 1 ≤ A) : A⁻¹ ≤ A⁻¹ ^ ((1 : ℝ) / 3) := by
  have hA0 : 0 < A := by linarith
  have h1 : (0 : ℝ) < A⁻¹ := by positivity
  have h2 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have := Real.rpow_le_rpow_of_exponent_ge h1 h2 (by norm_num : (1 : ℝ) / 3 ≤ 1)
  rwa [Real.rpow_one] at this

theorem sqrt_le_self {J : ℝ} (hJ : 1 ≤ J) : √J ≤ J := by
  nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ J), Real.sqrt_nonneg J,
    Real.one_le_sqrt.2 hJ]

variable {W ℓu ℓs ηu D J : ℝ}

/-- **Shape 1 — (5.35) exactly as the paper writes it**, with the `A_u^{-1/3}(J*)³` term.

The (5.52) prefactor is the one (4.5) gives, `κ₁ = 1 + J* A_u^{-1}`, and the single-`G`
bound (5.57) is the one (4.2) gives, `κ₂ = A_u^{-1/2}(1 + J* A_u^{-1})`.

Two side conditions the paper leaves implicit are explicit here:
`hJA : J* ≤ A_u` (without it the `(J*)² A_u^{-1}` of (5.55) does not fit inside
`A_u^{-1/3}(J*)³` on the near-field indicator), and `hD`, which says the `W^{-D}` floor of
`T_{u,D}` summed over the `L` sites is below `ℓ_u A_u^{-1}` — the same regime condition as
in `RBM.mul_sum_tailT_mul_tailT_le'`.  `cNear` and `cFar` are `W^{o(1)}`. -/
theorem eG_le_paper_of_schwarz (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ W * ℓu * ηu) (hJA : J ≤ W * ℓu * ηu)
    (hD : (L : ℝ) * √(W ^ (-D)) ≤ ℓu * (W * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L)
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {ρ EG : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, L3 b ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L3 b ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * ((√(W * ℓu * ηu))⁻¹ * (1 + J * (W * ℓu * ηu)⁻¹)))
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * ((√(W * ℓu * ηu))⁻¹ * (1 + J * (W * ℓu * ηu)⁻¹)))
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ (1 + J * (W * ℓu * ηu)⁻¹) * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * (2 * cNear W ℓu * (ℓu / ℓs) ^ 2 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0)
        + (4 * cFar W ℓu + 338) * (W * ℓu * ηu)⁻¹ ^ ((1 : ℝ) / 3) * J ^ 3)
      * tailT W ℓu ηu D (zdist L (a₁ - a₂))
      + 2 * (ℓu * ηu)⁻¹ * L * ρ := by
  set A : ℝ := W * ℓu * ηu with hAdef
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hsJ : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hcF : 0 ≤ cFar W ℓu := cFar_nonneg hW hℓ
  have hcN : 0 ≤ cNear W ℓu := cNear_nonneg hW hℓ
  have hκ₁0 : (0 : ℝ) ≤ 1 + J * A⁻¹ := by positivity
  have hκ₁2 : 1 + J * A⁻¹ ≤ 2 := by
    have : J * A⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hA0, one_mul]; exact hJA
    linarith
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  have hκ₂0 : (0 : ℝ) ≤ (√A)⁻¹ * (1 + J * A⁻¹) := by positivity
  have hmaster := eG_le L hW hℓu hℓs hηu hJ a₁ a₂ hκ₁0 hκ₂0 hρ hGm h273 h554 h531 h42
    h558a h558b h560 hEG
  refine hmaster.trans ?_
  set ind : ℝ := if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0 with hind
  have hind0 : (0 : ℝ) ≤ ind := by rw [hind]; split_ifs <;> norm_num
  set P : ℝ := A⁻¹ ^ ((1 : ℝ) / 3) with hP
  have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg (by positivity) _
  have hη0 : (0 : ℝ) < ηu⁻¹ := by positivity
  have hfloor : (L : ℝ) * √(W ^ (-D)) / ℓu ≤ A⁻¹ := by
    rw [div_le_iff₀ hℓ]
    calc (L : ℝ) * √(W ^ (-D)) ≤ ℓu * A⁻¹ := hD
      _ = A⁻¹ * ℓu := by ring
  have h13 := inv_sqrt_le_rpow_third hA
  have h13' := inv_le_rpow_third hA
  have hJ2 : J ^ 2 ≤ J ^ 3 := pow_le_pow_right₀ hJ (by norm_num)
  have hJJ : J * √J ≤ J ^ 3 := by
    have h1 : J * √J ≤ J * J := mul_le_mul_of_nonneg_left (sqrt_le_self hJ) hJ0
    nlinarith
  have hJ1 : J ≤ J ^ 3 := by
    have := pow_le_pow_right₀ hJ (by norm_num : 1 ≤ 3)
    simpa using this
  have hnear0 : (0 : ℝ) ≤ cNear W ℓu * (ℓu / ℓs) ^ 2 * ind := mul_nonneg (by positivity) hind0
  have hX0 : (0 : ℝ) ≤ cNear W ℓu * (ℓu / ℓs) ^ 2 * ind
      + cFar W ℓu * J * ((√A)⁻¹ * (1 + J * A⁻¹))
      + J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu) := by
    have p2 : (0 : ℝ) ≤ cFar W ℓu * J * ((√A)⁻¹ * (1 + J * A⁻¹)) := by positivity
    have p3 : (0 : ℝ) ≤ J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu) := by positivity
    linarith
  -- Case 1's single-`G` factor: `A^{-1/2}(1 + J A^{-1}) ≤ 2 A^{-1/3}`
  have u1 : (√A)⁻¹ * (1 + J * A⁻¹) ≤ 2 * P := by
    have a1 : (√A)⁻¹ * (1 + J * A⁻¹) ≤ (√A)⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hκ₁2 (by positivity)
    have a2 : (√A)⁻¹ * 2 ≤ P * 2 := mul_le_mul_of_nonneg_right h13 (by norm_num)
    linarith
  have b1 : J * ((√A)⁻¹ * (1 + J * A⁻¹)) ≤ J ^ 3 * (2 * P) :=
    mul_le_mul hJ1 u1 hκ₂0 (by positivity)
  have t1 := mul_le_mul_of_nonneg_left b1 (by positivity : (0 : ℝ) ≤ 2 * cFar W ℓu)
  -- Case 2's factor: `J^{3/2}(168 A^{-1} + L√(W^{-D})/ℓ_u) ≤ 169 J³ A^{-1/3}`
  have u2 : 168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu ≤ 169 * P := by
    have hx : A⁻¹ ≤ P := h13'
    linarith [hfloor]
  have b2 : J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu) ≤ J ^ 3 * (169 * P) :=
    mul_le_mul hJJ u2 (by positivity) (by positivity)
  have t2 := mul_le_mul_of_nonneg_left b2 (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
  have h2XY : 2 * (cNear W ℓu * (ℓu / ℓs) ^ 2 * ind
        + cFar W ℓu * J * ((√A)⁻¹ * (1 + J * A⁻¹))
        + J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu)) ≤
      2 * cNear W ℓu * (ℓu / ℓs) ^ 2 * ind + (4 * cFar W ℓu + 338) * P * J ^ 3 := by
    linarith [t1, t2]
  have hXY : (1 + J * A⁻¹) * (cNear W ℓu * (ℓu / ℓs) ^ 2 * ind
        + cFar W ℓu * J * ((√A)⁻¹ * (1 + J * A⁻¹))
        + J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu)) ≤
      2 * cNear W ℓu * (ℓu / ℓs) ^ 2 * ind + (4 * cFar W ℓu + 338) * P * J ^ 3 :=
    (mul_le_mul_of_nonneg_right hκ₁2 hX0).trans h2XY
  have hTt := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY hη0.le) hT0
  have hrem : (1 + J * A⁻¹) * ((ℓu * ηu)⁻¹ * L * ρ) ≤ 2 * ((ℓu * ηu)⁻¹ * L * ρ) :=
    mul_le_mul_of_nonneg_right hκ₁2 (by positivity)
  linarith [hTt, hrem]

/-- **Shape 2 — the (2.73)-reduced form of (5.35)**, the one the moment route needs.

Both `(1 + J* A_u^{-1})` factors of the paper's proof — the one from (4.5) at (5.52) and
the one from (4.2) at (5.57)/(5.58) — are replaced by what Step 1's loop bound (2.73)
gives directly: `L_{u,(+,-)} ≺ r A_u^{-1}` with `r = ℓ_u/ℓ_s`, so `κ₁ = r` and
`κ₂ = r^{1/2} A_u^{-1/2}`.  The far-field bracket becomes

`r^{3/2} A_u^{-1/2} J*  +  r A_u^{-1} (J*)^{3/2}`,

i.e. the **first** power of `J*` in the leading term and `3/2` in the subleading one, and
the near-field term becomes `r³` (not `r²`: `κ₁ = r` multiplies the `r²` of (5.53)). -/
theorem eG_le_reduced_of_schwarz (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ W * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * √(W ^ (-D)) ≤ ℓu * (W * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L)
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {ρ EG : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, L3 b ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L3 b ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * (√(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹))
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * (√(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹))
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * (cNear W ℓu * (ℓu / ℓs) ^ 3 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0)
        + cFar W ℓu * ((ℓu / ℓs) * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ * J)
        + 169 * ((ℓu / ℓs) * (W * ℓu * ηu)⁻¹ * (J * √J)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂))
      + (ℓu / ℓs) * (ℓu * ηu)⁻¹ * L * ρ := by
  set A : ℝ := W * ℓu * ηu with hAdef
  set r : ℝ := ℓu / ℓs with hrdef
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hsJ : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hcF : 0 ≤ cFar W ℓu := cFar_nonneg hW hℓ
  have hcN : 0 ≤ cNear W ℓu := cNear_nonneg hW hℓ
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  have hκ₂0 : (0 : ℝ) ≤ √r * (√A)⁻¹ := by positivity
  have hmaster := eG_le L hW hℓu hℓs hηu hJ a₁ a₂ hr0 hκ₂0 hρ hGm h273 h554 h531 h42
    h558a h558b h560 hEG
  refine hmaster.trans ?_
  set ind : ℝ := if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0 with hind
  have hind0 : (0 : ℝ) ≤ ind := by rw [hind]; split_ifs <;> norm_num
  have hη0 : (0 : ℝ) < ηu⁻¹ := by positivity
  have hfloor : (L : ℝ) * √(W ^ (-D)) / ℓu ≤ A⁻¹ := by
    rw [div_le_iff₀ hℓ]
    calc (L : ℝ) * √(W ^ (-D)) ≤ ℓu * A⁻¹ := hD
      _ = A⁻¹ * ℓu := by ring
  have u2 : 168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu ≤ 169 * A⁻¹ := by linarith [hfloor]
  have t2 := mul_le_mul_of_nonneg_left u2 (by positivity : (0 : ℝ) ≤ r * (J * √J))
  have hXY : r * (cNear W ℓu * r ^ 2 * ind + cFar W ℓu * J * (√r * (√A)⁻¹)
        + J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu)) ≤
      cNear W ℓu * r ^ 3 * ind + cFar W ℓu * (r * √r * (√A)⁻¹ * J)
        + 169 * (r * A⁻¹ * (J * √J)) := by
    linarith [t2]
  have hTt := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY hη0.le) hT0
  linarith [hTt]

end Shapes

/-! ### The two shapes, with (5.58) discharged -/

section ShapesGloop

open Matrix

variable {ℓu ℓs ηu D J : ℝ}
variable (Wb : ℕ) [NeZero Wb] {H : Matrix (ZMod L × Fin Wb) (ZMod L × Fin Wb) ℂ} {z : ℂ}

/-- The `(+,-)` `2`-loop is a nonnegative real (`RBM.gloop_two_plus_minus_nonneg`). -/
theorem gloop_two_re_nonneg (hH : H.IsHermitian) (a b : ZMod L) :
    0 ≤ (gloop L Wb H z ⟨[true, false], [a, b]⟩).re := by
  obtain ⟨r, hr0, hr⟩ := gloop_two_plus_minus_nonneg hH a b
  rw [hr, Complex.ofReal_re]
  exact hr0

/-- `gloop_h558a` with the harmless factor `1/2` dropped, i.e. exactly the hypothesis
`h558a` of `case1_pointwise`. -/
theorem gloop_h558a' (hH : H.IsHermitian) (a₁ a₂ b : ZMod L) {κ : ℝ} (hκ : 0 ≤ κ)
    (hC : ∀ p : ZMod L × Fin Wb, p.1 = b →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r a₁ * ‖green H z r p‖ ≤ κ)
    (hR : ∀ r : ZMod L × Fin Wb, r.1 = a₁ →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p b * ‖green H z r p‖ ≤ κ) :
    ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      ((gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re
        + (gloop L Wb H z ⟨[true, false], [a₂, b]⟩).re) * κ := by
  refine (gloop_h558a L Wb hH a₁ a₂ b hκ hC hR).trans ?_
  have h1 := gloop_two_re_nonneg L Wb (z := z) hH a₂ a₁
  have h2 := gloop_two_re_nonneg L Wb (z := z) hH a₂ b
  nlinarith [mul_nonneg (add_nonneg h1 h2) hκ]

/-- `gloop_h558b` with the harmless factor `1/2` dropped, i.e. exactly the hypothesis
`h558b` of `case1_pointwise`. -/
theorem gloop_h558b' (hH : H.IsHermitian) (a₁ a₂ b : ZMod L) {κ : ℝ} (hκ : 0 ≤ κ)
    (hC : ∀ p : ZMod L × Fin Wb, p.1 = a₂ →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r b * ‖green H z r p‖ ≤ κ)
    (hR : ∀ r : ZMod L × Fin Wb, r.1 = b →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p a₂ * ‖green H z r p‖ ≤ κ) :
    ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      ((gloop L Wb H z ⟨[true, false], [a₂, a₁]⟩).re
        + (gloop L Wb H z ⟨[true, false], [b, a₁]⟩).re) * κ := by
  refine (gloop_h558b L Wb hH a₁ a₂ b hκ hC hR).trans ?_
  have h1 := gloop_two_re_nonneg L Wb (z := z) hH a₂ a₁
  have h2 := gloop_two_re_nonneg L Wb (z := z) hH b a₁
  nlinarith [mul_nonneg (add_nonneg h1 h2) hκ]

/-- **Shape 1 — (5.35) exactly as the paper writes it**, for the `3`-loops of
`RBM.gloop`, with the Schwarz step (5.58) **proved** rather than assumed: `h558a`/`h558b`
are replaced by the two orientations of the single-`G` estimate (5.57), which is the only
thing (5.58) needs beyond Cauchy–Schwarz. -/
theorem eG_le_paper (hH : H.IsHermitian) (hW : 1 ≤ (Wb : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hJ : 1 ≤ J) (hA : 1 ≤ (Wb : ℝ) * ℓu * ηu) (hJA : J ≤ (Wb : ℝ) * ℓu * ηu)
    (hD : (L : ℝ) * √((Wb : ℝ) ^ (-D)) ≤ ℓu * ((Wb : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ EG : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((Wb : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, ellStarStar (Wb : ℝ) ℓu < (zdist L (a₁ - b) : ℝ) →
      ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (Wb : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L Wb H z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (Wb : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (Wb : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT (Wb : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin Wb), p.1 = y →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r x * ‖green H z r p‖ ≤
        (√((Wb : ℝ) * ℓu * ηu))⁻¹ * (1 + J * ((Wb : ℝ) * ℓu * ηu)⁻¹))
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin Wb), r.1 = x →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p y * ‖green H z r p‖ ≤
        (√((Wb : ℝ) * ℓu * ηu))⁻¹ * (1 + J * ((Wb : ℝ) * ℓu * ηu)⁻¹))
    (h560 : ∀ b, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ (1 + J * ((Wb : ℝ) * ℓu * ηu)⁻¹) * (ℓu * ηu)⁻¹ *
      ∑ b : ZMod L, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖) :
    EG ≤ ηu⁻¹ * (2 * cNear (Wb : ℝ) ℓu * (ℓu / ℓs) ^ 2 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar (Wb : ℝ) ℓu then 1 else 0)
        + (4 * cFar (Wb : ℝ) ℓu + 338) *
            ((Wb : ℝ) * ℓu * ηu)⁻¹ ^ ((1 : ℝ) / 3) * J ^ 3)
      * tailT (Wb : ℝ) ℓu ηu D (zdist L (a₁ - a₂))
      + 2 * (ℓu * ηu)⁻¹ * L * ρ := by
  have hA0 : (0 : ℝ) < (Wb : ℝ) * ℓu * ηu := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hκ : (0 : ℝ) ≤ (√((Wb : ℝ) * ℓu * ηu))⁻¹ * (1 + J * ((Wb : ℝ) * ℓu * ηu)⁻¹) := by
    have : (0 : ℝ) < √((Wb : ℝ) * ℓu * ηu) := Real.sqrt_pos.2 hA0
    positivity
  exact eG_le_paper_of_schwarz L hW hℓu hℓs hηu hJ hA hJA hD a₁ a₂ hρ hGm h273 h554 h531 h42
    (fun b _ => gloop_h558a' L Wb hH a₁ a₂ b hκ (h557C a₁ b) (h557R a₁ b))
    (fun b _ => gloop_h558b' L Wb hH a₁ a₂ b hκ (h557C b a₂) (h557R b a₂)) h560 hEG

/-- **Shape 2 — the (2.73)-reduced form of (5.35)**, for the `3`-loops of `RBM.gloop`,
with the Schwarz step (5.58) **proved**: `h558a`/`h558b` are replaced by the two
orientations of (5.57), here at the strength Step 1's loop bound (2.73) gives,
`κ₂ = r^{1/2} A_u^{-1/2}`. -/
theorem eG_le_reduced (hH : H.IsHermitian) (hW : 1 ≤ (Wb : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hJ : 1 ≤ J) (hA : 1 ≤ (Wb : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * √((Wb : ℝ) ^ (-D)) ≤ ℓu * ((Wb : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ EG : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((Wb : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, ellStarStar (Wb : ℝ) ℓu < (zdist L (a₁ - b) : ℝ) →
      ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (Wb : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L Wb H z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (Wb : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (Wb : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT (Wb : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin Wb), p.1 = y →
      ∑ r : ZMod L × Fin Wb, blkW L Wb r x * ‖green H z r p‖ ≤
        √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹)
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin Wb), r.1 = x →
      ∑ p : ZMod L × Fin Wb, blkW L Wb p y * ‖green H z r p‖ ≤
        √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹)
    (h560 : ∀ b, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ *
      ∑ b : ZMod L, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖) :
    EG ≤ ηu⁻¹ * (cNear (Wb : ℝ) ℓu * (ℓu / ℓs) ^ 3 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar (Wb : ℝ) ℓu then 1 else 0)
        + cFar (Wb : ℝ) ℓu *
            ((ℓu / ℓs) * √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹ * J)
        + 169 * ((ℓu / ℓs) * ((Wb : ℝ) * ℓu * ηu)⁻¹ * (J * √J)))
      * tailT (Wb : ℝ) ℓu ηu D (zdist L (a₁ - a₂))
      + (ℓu / ℓs) * (ℓu * ηu)⁻¹ * L * ρ := by
  have hκ : (0 : ℝ) ≤ √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹ := by positivity
  exact eG_le_reduced_of_schwarz L hW hℓu hℓs hηu hJ hA hr hD a₁ a₂ hρ hGm h273 h554 h531 h42
    (fun b _ => gloop_h558a' L Wb hH a₁ a₂ b hκ (h557C a₁ b) (h557R a₁ b))
    (fun b _ => gloop_h558b' L Wb hH a₁ a₂ b hκ (h557C b a₂) (h557R b a₂)) h560 hEG

end ShapesGloop

end Main


/-! ### (5.36): the `E ⊗ E` estimate, pp. 61–63 -/

section EE

variable {W ℓu ℓs ηu D J : ℝ}

/-- The (5.32) loss at `C = 1`, `e^{(log W)^{3/4}}`; `W^{o(1)}`. -/
noncomputable def loss1 (W : ℝ) : ℝ := exp (log W ^ (3 / 4 : ℝ))

theorem one_le_loss1 {W : ℝ} (hW : 1 ≤ W) : 1 ≤ loss1 W := by
  have : 0 ≤ log W := Real.log_nonneg hW
  exact Real.one_le_exp (by positivity)

theorem loss1_pos (W : ℝ) : 0 < loss1 W := exp_pos _

/-- The `W^{o(1)}` coefficient of the near-field term of (5.36); `T_{u,D}` enters
**squared**, so the `A_u^{-2} / T_{u,D}` conversion of `inv_sq_le_tailT` is used twice and
at the larger scale `4 ℓ*_u`. -/
noncomputable def cNear2 (W ℓu : ℝ) : ℝ :=
  (2 * log W ^ (3 : ℝ) + 2 / ℓu) * exp (4 * log W ^ (3 / 4 : ℝ))

theorem cNear2_nonneg (hW : 1 ≤ W) (hℓu : 0 < ℓu) : 0 ≤ cNear2 W ℓu := by
  have := Real.log_nonneg hW; unfold cNear2; positivity

/-- `A_u^{-4} ≤ e^{4 (log W)^{3/4}} T_{u,D}(d)²` for `d ≤ 4 ℓ*_u`: the squared form of
`RBM.inv_sq_le_tailT` at `C = 4`. -/
theorem inv_four_le_tailT_sq (hW : 1 ≤ W) (hℓu : 0 < ℓu) {d : ℝ}
    (hd : d ≤ 4 * ellStar W ℓu) :
    (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 ≤
      exp (4 * log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d ^ 2 := by
  have hW0 : (0 : ℝ) < W := by linarith
  have h := RBM.inv_sq_le_tailT (ℓu := ℓu) (ηu := ηu) (D := D) hW hℓu
    (by norm_num : (0 : ℝ) ≤ 4) hd
  rw [show √(4 : ℝ) = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]] at h
  have h0 : (0 : ℝ) ≤ ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hT0 : 0 ≤ tailT W ℓu ηu D d := tailT_nonneg hW0.le _
  have hsq := mul_le_mul h h h0 (by positivity)
  rw [sq]
  refine hsq.trans (le_of_eq ?_)
  rw [show (2 : ℝ) * log W ^ (3 / 4 : ℝ) = 2 * log W ^ (3 / 4 : ℝ) from rfl]
  rw [show exp (2 * log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d *
      (exp (2 * log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d)
      = (exp (2 * log W ^ (3 / 4 : ℝ)) * exp (2 * log W ^ (3 / 4 : ℝ))) *
        tailT W ℓu ηu D d ^ 2 from by ring, ← Real.exp_add]
  congr 2
  ring

/-- **(5.64)**, Case 1 of (5.36): the near field `‖a₁ - a₂‖ ≤ 4 ℓ*_u`.

The `b`-sum splits at `ℓ**_u`; the near part carries the `n = 6` case of the a-priori loop
bound (2.73), `(ℓ_u/ℓ_s)^5 A_u^{-5}`, and the far part is the explicit remainder `ρ`. -/
theorem ee_near_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    {a₁ a₂ : ZMod L} (hnear : (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu)
    {L6 : ZMod L → ℝ} {ρ EE : ℝ} (hρ : 0 ≤ ρ)
    (h273 : ∀ b, L6 b ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹)
    (h564 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L6 b ≤ ρ)
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 + W * L * ρ := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hlog : 0 ≤ log W := Real.log_nonneg hW
  have hss : 0 ≤ ellStarStar W ℓu := ellStarStar_nonneg hW hℓ.le
  have hq : (0 : ℝ) ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹ := by
    positivity
  have hsplit := sum_le_split_one L (fun _ => hρ) hss a₁ hq (fun b _ => h273 b)
    (fun b hb => h564 b hb)
  have hconst : ∑ _b : ZMod L, ρ = (L : ℝ) * ρ := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hconst] at hsplit
  have hinv := inv_four_le_tailT_sq (ηu := ηu) (D := D) hW hℓ hnear
  have hT0 : (0 : ℝ) ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hr5 : (0 : ℝ) ≤ (ℓu / ℓs) ^ 5 := by positivity
  have hmain : W * ((2 * ellStarStar W ℓu + 2) *
        ((ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹)) ≤
      ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
    have hfac : (0 : ℝ) ≤ W * ((2 * ellStarStar W ℓu + 2) *
        ((ℓu / ℓs) ^ 5 * (W * ℓu * ηu)⁻¹)) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hinv hfac
    refine le_trans (le_of_eq (by ring)) (h1.trans (le_of_eq ?_))
    rw [ellStarStar, cNear2]
    field_simp
  calc EE ≤ W * ∑ b : ZMod L, L6 b := hEE
    _ ≤ W * ((2 * ellStarStar W ℓu + 2) *
          ((ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹) + (L : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_left hsplit hW0.le
    _ = W * ((2 * ellStarStar W ℓu + 2) *
          ((ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹))
          + W * (L : ℝ) * ρ := by ring
    _ ≤ _ := by linarith [hmain]

/-- **(5.67) + (5.71)**, Case 2(1a) pointwise.  `b` is within `ℓ*_u` of `a₁`, while
`‖a₁ - a₂‖ ≥ 4 ℓ*_u`.  The four `G`-edges of (5.65) are two on the pair `(a₁, a₂)` and two
on `(b, a₂)`; (4.2) + (5.31) turn each pair into `J* T_{u,D}`, and (5.32) turns
`T_{u,D}(‖a₂ - b‖)` into `T_{u,D}(‖a₁ - a₂‖)`.  The `(J*)²` is **intrinsic**: it is the
product of the two squared `G`-pairs, each of which must keep its tail function for the
`T_{u,D}²` normalization on the left of (5.36). -/
theorem case2a_pointwise (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : 4 * ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h566 : ∀ b, L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ) :
    ∀ b : ZMod L, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu →
      L6 b ≤ J ^ 2 * loss1 W * μ * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
  intro b hb
  have hW0 : (0 : ℝ) < W := by linarith
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have htri := zdist_sub_le_add L a₁ a₂ b
  have h12 : Gsq a₁ a₂ ≤ J * tailT W ℓu ηu D (zdist L (a₁ - a₂)) :=
    h42sq a₁ a₂ (by linarith)
  have hd2 : (zdist L (a₁ - a₂) : ℝ) - ellStar W ℓu ≤ (zdist L (a₂ - b) : ℝ) := by linarith
  have hb2 : Gsq b a₂ ≤ J * (loss1 W * tailT W ℓu ηu D (zdist L (a₁ - a₂))) := by
    have hle : Gsq b a₂ ≤ J * tailT W ℓu ηu D (zdist L (a₂ - b)) := by
      have := h42sq b a₂ (by rw [zdist_sub_comm]; linarith)
      rwa [zdist_sub_comm] at this
    refine hle.trans (mul_le_mul_of_nonneg_left ?_ hJ0)
    have h1 : tailT W ℓu ηu D (zdist L (a₂ - b)) ≤
        tailT W ℓu ηu D ((zdist L (a₁ - a₂) : ℝ) - 1 * ellStar W ℓu) :=
      tailT_antitone hℓu (by linarith)
    refine h1.trans ?_
    rw [loss1, show log W ^ (3 / 4 : ℝ) = √(1 : ℝ) * log W ^ (3 / 4 : ℝ) by
      rw [Real.sqrt_one, one_mul]]
    exact tailT_sub_le (ℓu := ℓu) (ηu := ηu) (D := D) hW hℓu (by norm_num : (0 : ℝ) ≤ 1) _
  have hprod : Gsq a₁ a₂ * Gsq b a₂ ≤
      J ^ 2 * loss1 W * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
    have := mul_le_mul h12 hb2 (hGsq _ _) (by positivity)
    refine this.trans (le_of_eq (by ring))
  refine (h566 b).trans ?_
  have := mul_le_mul_of_nonneg_right hprod hμ
  refine this.trans (le_of_eq (by ring))

/-- **(5.67) + (5.72)**, Case 2(1b) pointwise.  `b` is at distance `> ℓ*_u` from `a₁` and
(on the half `‖a₁ - b‖ ≤ ‖a₂ - b‖`) at distance `≥ ‖a₁ - a₂‖/2` from `a₂`.  Here
`(G†E_b G)_{x₁x₁'} ≺ J* T_{u,D}(‖b - a₁‖)` replaces the `4`-loop factor `μ` of (5.66), and
the total power of `J*` is **three**, again intrinsically: the three tail functions are
what the convolution `∑_b T(‖a₁-b‖) T(‖a₂-b‖) ≺ ℓ_u A_u^{-2} T(‖a₁-a₂‖)` needs in order to
produce the second power of `T_{u,D}(‖a₁-a₂‖)`. -/
theorem case2b_pointwise (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : 4 * ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ}
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h572 : ∀ b, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT W ℓu ηu D (zdist L (a₁ - b)))) :
    ∀ b : ZMod L, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ) →
      L6 b ≤ J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
        (tailT W ℓu ηu D (zdist L (a₁ - b)) * tailT W ℓu ηu D (zdist L (a₂ - b))) := by
  intro b hb hhalf
  have hW0 : (0 : ℝ) < W := by linarith
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have htri := zdist_sub_le_add L a₁ a₂ b
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hT1 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - b)) := tailT_nonneg hW0.le _
  have hT2 : 0 ≤ tailT W ℓu ηu D (zdist L (a₂ - b)) := tailT_nonneg hW0.le _
  have h12 : Gsq a₁ a₂ ≤ J * tailT W ℓu ηu D (zdist L (a₁ - a₂)) :=
    h42sq a₁ a₂ (by linarith)
  have hb2 : Gsq b a₂ ≤ J * tailT W ℓu ηu D (zdist L (a₂ - b)) := by
    have := h42sq b a₂ (by rw [zdist_sub_comm]; linarith)
    rwa [zdist_sub_comm] at this
  refine (h572 b hb).trans ?_
  have hp1 : Gsq a₁ a₂ * Gsq b a₂ ≤
      (J * tailT W ℓu ηu D (zdist L (a₁ - a₂))) *
        (J * tailT W ℓu ηu D (zdist L (a₂ - b))) :=
    mul_le_mul h12 hb2 (hGsq _ _) (by positivity)
  have hp2 := mul_le_mul_of_nonneg_right hp1
    (by positivity : (0 : ℝ) ≤ J * tailT W ℓu ηu D (zdist L (a₁ - b)))
  refine hp2.trans (le_of_eq (by ring))

/-- **(5.71) + (5.72)**: the far field of (5.36), summed over the half
`‖a₁ - b‖ ≤ ‖a₂ - b‖` on which the paper says "by symmetry, we only consider the first
case". -/
theorem sum_ee_far_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (_hηu : 0 < ηu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : 4 * ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (_hL6 : ∀ b, 0 ≤ L6 b) (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h566 : ∀ b, L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ)
    (h572 : ∀ b, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT W ℓu ηu D (zdist L (a₁ - b)))) :
    (∑ b ∈ Finset.univ.filter
        (fun b : ZMod L => (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ)), L6 b) ≤
      ((2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W * μ)
        + J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
  classical
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hstar : 0 ≤ ellStar W ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hTb : ∀ b : ZMod L, 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - b)) := fun b =>
    tailT_nonneg hW0.le _
  have hTb' : ∀ b : ZMod L, 0 ≤ tailT W ℓu ηu D (zdist L (a₂ - b)) := fun b =>
    tailT_nonneg hW0.le _
  have hloss := loss1_pos W
  have hfsum : (∑ b ∈ Finset.univ.filter
      (fun b : ZMod L => (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ)), L6 b)
      = ∑ b : ZMod L, (if (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ) then L6 b else 0) :=
    Finset.sum_filter _ _
  have hg0 : ∀ b : ZMod L, (0 : ℝ) ≤ J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
      (tailT W ℓu ηu D (zdist L (a₁ - b)) * tailT W ℓu ηu D (zdist L (a₂ - b))) := by
    intro b
    have := hTb b; have := hTb' b
    positivity
  have hc₁ : (0 : ℝ) ≤ J ^ 2 * loss1 W * μ *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by positivity
  have h1a := case2a_pointwise L hW hℓ hJ hfar hμ hGsq h42sq h566
  have h1b := case2b_pointwise L hW hℓ hJ hfar hGsq h42sq h572
  have hsplit := sum_le_split_one L
    (f := fun b : ZMod L =>
      if (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ) then L6 b else 0)
    (g := fun b : ZMod L => J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
      (tailT W ℓu ηu D (zdist L (a₁ - b)) * tailT W ℓu ηu D (zdist L (a₂ - b))))
    hg0 hstar a₁ hc₁
    (fun b hb => by
      by_cases hpb : (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ)
      · simpa [hpb] using h1a b hb
      · simpa [hpb] using hc₁)
    (fun b hb => by
      by_cases hpb : (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ)
      · simpa [hpb] using h1b b hb hpb
      · simpa [hpb] using hg0 b)
  rw [hfsum]
  refine hsplit.trans ?_
  have hconv := sum_tailT_mul_tailT_le L (ηu := ηu) hW0 hℓu D a₁ a₂
  have hgsum : (∑ b : ZMod L, J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
        (tailT W ℓu ηu D (zdist L (a₁ - b)) * tailT W ℓu ηu D (zdist L (a₂ - b))))
      = (J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂))) *
        ∑ b : ZMod L, (tailT W ℓu ηu D (zdist L (a₁ - b)) *
          tailT W ℓu ηu D (zdist L (a₂ - b))) := by
    rw [Finset.mul_sum]
  have hgbd : (∑ b : ZMod L, J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) *
        (tailT W ℓu ηu D (zdist L (a₁ - b)) * tailT W ℓu ηu D (zdist L (a₂ - b)))) ≤
      J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
    rw [hgsum]
    have := mul_le_mul_of_nonneg_left hconv
      (by positivity : (0 : ℝ) ≤ J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)))
    refine this.trans (le_of_eq (by ring))
  have he : (2 * ellStar W ℓu + 2) *
        (J ^ 2 * loss1 W * μ * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2)
      = (2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W * μ) *
        tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by ring
  rw [he]
  linarith [hgbd]

/-- The `W^{o(1)}` coefficient of the Case-2(1a) term of (5.36). -/
noncomputable def cFar2 (W ℓu : ℝ) : ℝ := (4 * log W ^ (3 / 2 : ℝ) + 4 / ℓu) * loss1 W

theorem cFar2_nonneg (hW : 1 ≤ W) (hℓu : 0 < ℓu) : 0 ≤ cFar2 W ℓu := by
  have := Real.log_nonneg hW
  have h2 : 0 < loss1 W := loss1_pos W
  unfold cFar2; positivity

/-- **(5.71) + (5.72)** assembled: the far field `‖a₁ - a₂‖ ≥ 4 ℓ*_u` of (5.36).

The paper's "by symmetry, we only consider the first case" — the half
`‖a₂ - b‖ < ‖a₁ - b‖`, which in the paper is handled by the `k = 2` term of (5.22)
(Figure 14), i.e. by the *same* estimate with `a₁` and `a₂` interchanged — is the
hypothesis `hsym`.  It is **not** a relabelling inside the `k = 1` term: on that half the
`(b, a₂)` pair of `G`-edges of (5.65) is short and (5.31) does not apply to it. -/
theorem ee_far_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {a₁ a₂ : ZMod L} (hfar : 4 * ellStar W ℓu ≤ (zdist L (a₁ - a₂) : ℝ))
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {μ EE : ℝ} (hμ : 0 ≤ μ)
    (hL6 : ∀ b, 0 ≤ L6 b) (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h566 : ∀ b, L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ)
    (h572 : ∀ b, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT W ℓu ηu D (zdist L (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter
        (fun b : ZMod L => ¬ ((zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ))), L6 b) ≤
      ((2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W * μ)
        + J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2)
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ))
        + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + 2 * W * L * W ^ (-D) * J ^ 3 * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
  classical
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have h1 := sum_ee_far_le L hW hℓu hηu hJ hfar hμ hL6 hGsq h42sq h566 h572
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod L))
    (fun b : ZMod L => (zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ)) L6
  have htot : ∑ b : ZMod L, L6 b ≤
      2 * (((2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W * μ)
        + J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2) := by
    linarith [h1, hsym, hsplit]
  have hmul := mul_le_mul_of_nonneg_left htot hW0.le
  refine hEE.trans (hmul.trans (le_of_eq ?_))
  rw [ellStar, cFar2, loss1]
  field_simp
  ring

/-- **(5.36)**: `E ⊗ E`, with the near field (5.64) and the far field (5.71)+(5.72)
combined.  `μ` is the `(max_{a,σ} L_{u,σ,a})^{1/2}` factor of (5.66); with (2.73) at
`n = 4` it is `(ℓ_u/ℓ_s)^{3/2} A_u^{-3/2}`, so `A_u μ = (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2}` and the
second term is the paper's `η_u^{-1} A_u^{-1/2} (J*)³` (up to the `(ℓ_u/ℓ_s)^{3/2}`, which
the paper drops). -/
theorem ee_le (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (a₁ a₂ : ZMod L)
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {μ ρ EE : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hL6 : ∀ b, 0 ≤ L6 b) (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, L6 b ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹)
    (h564 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L6 b ≤ ρ)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h566 : ∀ b, L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ)
    (h572 : ∀ b, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT W ℓu ηu D (zdist L (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter
        (fun b : ZMod L => ¬ ((zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ))), L6 b) ≤
      ((2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W * μ)
        + J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2)
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ))
        + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + (W * L * ρ + 2 * W * L * W ^ (-D) * J ^ 3 *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hcN : 0 ≤ cNear2 W ℓu := cNear2_nonneg hW hℓ
  have hcF : 0 ≤ cFar2 W ℓu := cFar2_nonneg hW hℓ
  have hA0 : (0 : ℝ) < W * ℓu * ηu := by positivity
  have hrem1 : (0 : ℝ) ≤ W * L * ρ := by positivity
  have hrem2 : (0 : ℝ) ≤ 2 * W * L * W ^ (-D) * J ^ 3 *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
    have : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    positivity
  have hnearterm : (0 : ℝ) ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5) *
      tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by positivity
  have hfarterm : (0 : ℝ) ≤ ηu⁻¹ * (cFar2 W ℓu * (J ^ 2 * ((W * ℓu * ηu) * μ))
      + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹) * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by
    positivity
  split_ifs with hd
  · have h := ee_near_le (D := D) L hW hℓu hℓs hηu hd hρ h273 h564 hEE
    nlinarith [h, hfarterm, hrem2]
  · rw [not_le] at hd
    have h := ee_far_le L hW hℓu hηu hJ hd.le hμ hL6 hGsq h42sq h566 h572 hsym hEE
    nlinarith [h, hrem1]

/-- **(5.36) in the paper's shape.**  `μ` is instantiated from (2.73) at `n = 4`:
`(max_{a,σ} L_{u,σ,a})^{1/2} ≺ ((ℓ_u/ℓ_s)³ A_u^{-3})^{1/2}`, written
`(ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} A_u^{-1}`.  The conclusion is

`(E⊗E) / T_{u,D}(‖a₁-a₂‖)² ≺ η_u^{-1}(ℓ_u/ℓ_s)^5 1(‖a₁-a₂‖ ≤ 4ℓ*_u)
   + η_u^{-1} (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} (J*)³`,

which is (5.36) except for the factor `(ℓ_u/ℓ_s)^{3/2}`: the paper writes it in the line
after (5.67) and then drops it from the statement of (5.36). -/
theorem ee_le_paper (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ W * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs) (a₁ a₂ : ZMod L)
    {Gsq : ZMod L → ZMod L → ℝ} {L6 : ZMod L → ℝ} {ρ EE : ℝ} (hρ : 0 ≤ ρ)
    (hL6 : ∀ b, 0 ≤ L6 b) (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, L6 b ≤ (ℓu / ℓs) ^ 5 * (((W * ℓu * ηu) ^ 2)⁻¹) ^ 2 * (W * ℓu * ηu)⁻¹)
    (h564 : ∀ b, ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L6 b ≤ ρ)
    (h42sq : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gsq x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h566 : ∀ b, L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ *
      (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)))
    (h572 : ∀ b, ellStar W ℓu < (zdist L (a₁ - b) : ℝ) →
      L6 b ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT W ℓu ηu D (zdist L (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter
        (fun b : ZMod L => ¬ ((zdist L (a₁ - b) : ℝ) ≤ (zdist L (a₂ - b) : ℝ))), L6 b) ≤
      ((2 * ellStar W ℓu + 2) * (J ^ 2 * loss1 W *
          (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹)))
        + J ^ 3 * (36 * ℓu * ((W * ℓu * ηu) ^ 2)⁻¹ + L * W ^ (-D)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2)
    (hEE : EE ≤ W * ∑ b : ZMod L, L6 b) :
    EE ≤ ηu⁻¹ * (cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0)
        + (cFar2 W ℓu + 72) * (ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹) * J ^ 3)
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2
      + (W * L * ρ + 2 * W * L * W ^ (-D) * J ^ 3 *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hA0 : (0 : ℝ) < W * ℓu * ηu := by linarith
  have hsA : (0 : ℝ) < √(W * ℓu * ηu) := Real.sqrt_pos.2 hA0
  have hr0 : (0 : ℝ) ≤ ℓu / ℓs := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hTsq : (0 : ℝ) ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) ^ 2 := by positivity
  have hcN : 0 ≤ cNear2 W ℓu := cNear2_nonneg hW hℓ
  have hcF : 0 ≤ cFar2 W ℓu := cFar2_nonneg hW hℓ
  have hη0 : (0 : ℝ) < ηu⁻¹ := by positivity
  have hμ : (0 : ℝ) ≤ ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹) := by
    positivity
  have hmain := ee_le L hW hℓu hℓs hηu hJ a₁ a₂ hμ hρ hL6 hGsq h273 h564 h42sq h566 h572
    hsym hEE
  refine hmain.trans ?_
  have hAμ : W * ℓu * ηu *
      (ℓu / ℓs * √(ℓu / ℓs) * ((√(W * ℓu * ηu))⁻¹ * (W * ℓu * ηu)⁻¹))
      = ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ := by
    field_simp
  rw [hAμ]
  set ν : ℝ := ℓu / ℓs * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ with hν
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hone : (1 : ℝ) ≤ ℓu / ℓs * √(ℓu / ℓs) := by
    have h1 : (1 : ℝ) ≤ √(ℓu / ℓs) := Real.one_le_sqrt.2 hr
    nlinarith
  have hinvA : (W * ℓu * ηu)⁻¹ ≤ ν := by
    have hsq : √(W * ℓu * ηu) ≤ W * ℓu * ηu := by
      nlinarith [Real.sq_sqrt hA0.le, Real.one_le_sqrt.2 hA, Real.sqrt_nonneg (W * ℓu * ηu)]
    have h1 : (W * ℓu * ηu)⁻¹ ≤ (√(W * ℓu * ηu))⁻¹ := inv_anti₀ hsA hsq
    have h2 : (√(W * ℓu * ηu))⁻¹ ≤ ν := by
      rw [hν]
      have := mul_le_mul_of_nonneg_right hone (le_of_lt (inv_pos.2 hsA))
      linarith [this]
    linarith
  have hJ23 : J ^ 2 ≤ J ^ 3 := pow_le_pow_right₀ hJ (by norm_num)
  have hbr : cFar2 W ℓu * (J ^ 2 * ν) + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹
      ≤ (cFar2 W ℓu + 72) * ν * J ^ 3 := by
    have t1 : cFar2 W ℓu * (J ^ 2 * ν) ≤ cFar2 W ℓu * (J ^ 3 * ν) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJ23 hν0) hcF
    have t2 : 72 * J ^ 3 * (W * ℓu * ηu)⁻¹ ≤ 72 * J ^ 3 * ν :=
      mul_le_mul_of_nonneg_left hinvA (by positivity)
    linarith
  set IND : ℝ := cNear2 W ℓu * (ℓu / ℓs) ^ 5 *
    (if (zdist L (a₁ - a₂) : ℝ) ≤ 4 * ellStar W ℓu then 1 else 0) with hIND
  have hbr' : IND + cFar2 W ℓu * (J ^ 2 * ν) + 72 * J ^ 3 * (W * ℓu * ηu)⁻¹
      ≤ IND + (cFar2 W ℓu + 72) * ν * J ^ 3 := by linarith
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbr' hη0.le) hTsq
  linarith [hstep]

end EE

end Lemma57
end RBM
