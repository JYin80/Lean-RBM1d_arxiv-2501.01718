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

`RBM.Lemma57.inv_sq_le_tailT` duplicates `RBM.Step45.inv_sq_le_tailT` with `C = 1` instead of
`C = 6`; the two files do not import each other.
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
      L3 b ≤ (L2 a₁ a₂ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * κ₂) :
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
  have h12 : L2 a₁ a₂ ≤ J * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := h531 a₁ a₂ (by linarith)
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
    have hstep : L2 a₁ b ≤ J * (loss32 W * tailT W ℓu ηu D (zdist L (a₁ - a₂))) :=
      (h531 a₁ b hd1').trans (mul_le_mul_of_nonneg_left (hshift (a₁ - b) hd1) hJ0)
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
      L3 b ≤ (L2 a₁ a₂ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * κ₂)
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
theorem inv_sq_le_tailT (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hηu : 0 < ηu) {d : ℝ}
    (hd : d ≤ ellStar W ℓu) :
    ((W * ℓu * ηu) ^ 2)⁻¹ ≤ exp (log W ^ (3 / 4 : ℝ)) * tailT W ℓu ηu D d := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hlog : 0 ≤ log W := Real.log_nonneg hW
  have hA : (0 : ℝ) < ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hdiv : d / ℓu ≤ log W ^ (3 / 2 : ℝ) := by
    rw [div_le_iff₀ hℓu]
    calc d ≤ ellStar W ℓu := hd
      _ = log W ^ (3 / 2 : ℝ) * ℓu := rfl
  have hsq : √(d / ℓu) ≤ log W ^ (3 / 4 : ℝ) := by
    have := Real.sqrt_le_sqrt hdiv
    rwa [sqrt_log_rpow_three_halves hW] at this
  have hexp : exp (-(log W ^ (3 / 4 : ℝ))) ≤ exp (-√(d / ℓu)) := by
    rw [exp_le_exp]; linarith
  have hfloor : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hT : ((W * ℓu * ηu) ^ 2)⁻¹ * exp (-(log W ^ (3 / 4 : ℝ))) ≤ tailT W ℓu ηu D d := by
    unfold tailT
    nlinarith [mul_le_mul_of_nonneg_left hexp hA.le]
  have hkey := mul_le_mul_of_nonneg_left hT (le_of_lt (exp_pos (log W ^ (3 / 4 : ℝ))))
  refine le_trans (le_of_eq ?_) hkey
  have hone : exp (log W ^ (3 / 4 : ℝ)) * exp (-(log W ^ (3 / 4 : ℝ))) = 1 := by
    rw [← Real.exp_add]; simp
  calc ((W * ℓu * ηu) ^ 2)⁻¹ = ((W * ℓu * ηu) ^ 2)⁻¹ * 1 := by ring
    _ = exp (log W ^ (3 / 4 : ℝ)) *
          (((W * ℓu * ηu) ^ 2)⁻¹ * exp (-(log W ^ (3 / 4 : ℝ)))) := by
        rw [← hone]; ring

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
      L3 b ≤ (L2 a₁ a₂ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * κ₂)
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
      L3 b ≤ (L2 a₁ a₂ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * κ₂)
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
theorem eG_le_paper (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
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
      L3 b ≤ (L2 a₁ a₂ + L2 a₂ b) * ((√(W * ℓu * ηu))⁻¹ * (1 + J * (W * ℓu * ηu)⁻¹)))
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * ((√(W * ℓu * ηu))⁻¹ * (1 + J * (W * ℓu * ηu)⁻¹)))
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
theorem eG_le_reduced (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
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
      L3 b ≤ (L2 a₁ a₂ + L2 a₂ b) * (√(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹))
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₁ a₂ + L2 a₁ b) * (√(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹))
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

end Main

/-! ### (5.60) from the definition of the `3`-loop -/

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

end Loop3

end Lemma57
end RBM
