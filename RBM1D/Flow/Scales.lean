/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Ward
import RBM1D.Propagator.Edges

/-!
# The scales of the flow and the time grid of the induction (pp. 21–24)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*: the deterministic
bookkeeping of the flow that surrounds Theorem 2.21 and the proof of Lemmas
2.18–2.20 on p. 24, and the scale dictionary of p. 21–22.

## The scale `A_t = W ℓ_t η_t`

* `RBM.flowScale W L E t := W · ℓ_t · η_t` with `ℓ_t = ℓ̂(t) = ellHat L t` (2.59) and
  `η_t = etaT E t = (1 - t) Im m^{(E)}` (2.35).
* `RBM.flowScale_eq` — the identity `A_t = W · Im m^{(E)} · min((1-t)^{1/2}, L(1-t))`
  for `t ≤ 1` (at `t = 1` both sides vanish).
* `RBM.flowScale_antitoneOn` — p. 24: `s ↦ W ℓ_s η_s` is non-increasing (on `(-∞, 1]`,
  in particular on `[0, 1]`).

## The time grid and (2.72)

* `RBM.gridS W τ' k := 1 - W^{-kτ'}`, so `s_0 = 0` and `1 - s_k = W^{-kτ'}`.
* `RBM.gridS_step_2_72` — the paper-literal step: if `(W ℓ_t η_t)⁻¹ ≤ W^{-30τ'}` at
  `t = s_{n₀}`, then (2.72) holds for every consecutive pair `(s_k, s_{k+1})`, `k + 1 ≤ n₀`,
  because `((1 - s_{k+1})/(1 - s_k))^{30} = W^{-30τ'}` (`gridS_ratio_pow`).

**Formulation choice for the grid (as prescribed by the ticket).**  The paper chooses
`τ'` and `n₀` *from* `t` so that `1 - t = W^{-n₀τ'}` exactly.  We instead **fix
`τ, τ', n₀` first and quantify over `t`**, using the *truncated grid*
`RBM.gridT W τ' t k := min (s_k, t)`:

* `RBM.gridT_zero`, `RBM.gridT_of_le` (`u_{n₀} = t` as soon as `t ≤ s_{n₀}`),
  `RBM.gridT_mono`, and
* `RBM.gridT_step_2_72` — for **every** `k`,
  `(W ℓ_{u_{k+1}} η_{u_{k+1}})⁻¹ ≤ ((1 - u_{k+1})/(1 - u_k))^{30}`, given only
  `(W ℓ_t η_t)⁻¹ ≤ W^{-30τ'}`.  Steps with `u_k = u_{k+1} = t` are trivial (the paper
  requires `t > s` in Theorem 2.21; a degenerate step `s = t` needs no theorem).
* `RBM.flow_grid_2_72` — the assembled statement.  Fix `0 < κ`, `0 ≤ τ`, `τ' > 0` with
  `60 τ' < τ`, and `n₀ ∈ ℕ` with `2 ≤ n₀ τ'` (so `n₀ = ⌈2/τ'⌉` works: **`n₀` depends on
  `τ'` only, not on `N`**).  Then there is `W₀` such that for all real `W ≥ W₀`, all
  `L ∈ ℕ` with `1 ≤ L ≤ W` (this is what `W ≥ N^{1/2+c}`, `N = WL`, (2.2) is used for),
  all `|E| ≤ 2 - κ` and all `t ≥ 0` with `N^{-1+τ} ≤ 1 - t`, the truncated grid
  `u_k = gridT W τ' t k` has `u_0 = 0`, `u_{n₀} = t`, is monotone, and satisfies (2.72)
  at every step.

The two quantitative inputs are `RBM.flowScale_ge` (`W ℓ_t η_t ≥ Im m · W^{τ/2}` when
`1 - t ≥ N^{-1+τ}` and `L ≤ W`) and `RBM.le_gridS_of` (`t ≤ s_{n₀}` when
`1 - t ≥ W^{-2}` and `n₀τ' ≥ 2`).

## The scale dictionary (p. 21–22)

* `RBM.ellZ L z = min((Im z)^{-1/2}, L) + 1` — the diffusion length (2.1).
* `RBM.etaT_le`, `RBM.le_etaT` — `η_t ≍ 1 - t` (constants `1` and `√(2κ)/2`).
* `RBM.ellHat_le_ellZ_zt`, `RBM.ellZ_zt_le` — `ℓ(z_t) ≍ ℓ_t`.
* `RBM.lemma28_scales` — for `z` as in (2.37)/(2.40) (`0 < Im z ≤ 1`, `|Re z| ≤ 2 - κ`),
  with `E, t` from Lemma 2.8: `(1 - t) ≍ Im z_t ≍ Im z` and `ℓ(z) ≍ ℓ(z_t) ≍ ℓ_t`.

## Deviations from the paper

* `W` is a real parameter `≥ 1` (the paper's `W ∈ ℕ` is a special case).
* The grid is truncated at `t` instead of solving `1 - t = W^{-n₀τ'}` for `τ'`; see above.
* The paper's requirement `W ≥ N^{1/2+c}` enters only as `L ≤ W` (i.e. `W ≥ N^{1/2}`), and
  "`N` large enough" as `W ≥ W₀(κ, τ, τ')`.
* `≍` is stated as two explicit inequalities with explicit constants.
-/

namespace RBM

open Real

section Scale

/-- The scale `A_t := W ℓ_t η_t` of the flow, `ℓ_t = ℓ̂(t)` (2.59), `η_t = Im z_t` (2.35). -/
noncomputable def flowScale (W : ℝ) (L : ℕ) (E t : ℝ) : ℝ := W * ellHat L (t : ℂ) * etaT E t

theorem mE_im_nonneg (E : ℝ) : 0 ≤ (mE E).im := by
  rw [mE_im]; positivity

/-- `ℓ̂(t) (1 - t) = min((1-t)^{1/2}, L(1-t))`. -/
theorem ellHat_mul_one_sub (L : ℕ) {t : ℝ} (ht1 : t ≤ 1) :
    ellHat L (t : ℂ) * (1 - t) = min (Real.sqrt (1 - t)) (L * (1 - t)) := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · rw [ellHat_ofReal L ht1, min_mul_of_nonneg _ _ (by linarith : (0 : ℝ) ≤ 1 - t),
      div_mul_eq_mul_div, one_mul, Real.div_sqrt]
  · simp

/-- **The key identity** `A_t = W · Im m^{(E)} · min((1-t)^{1/2}, L(1-t))`. -/
theorem flowScale_eq (W : ℝ) (L : ℕ) (E : ℝ) {t : ℝ} (ht1 : t ≤ 1) :
    flowScale W L E t = W * (mE E).im * min (Real.sqrt (1 - t)) (L * (1 - t)) := by
  rw [← ellHat_mul_one_sub L ht1, flowScale, etaT]
  ring

/-- p. 24: `s ↦ W ℓ_s η_s` is non-increasing on `(-∞, 1] ⊇ [0, 1]`. -/
theorem flowScale_antitoneOn {W : ℝ} (hW : 0 ≤ W) (L : ℕ) (E : ℝ) :
    AntitoneOn (flowScale W L E) (Set.Iic 1) := by
  intro a ha b hb hab
  rw [flowScale_eq W L E ha, flowScale_eq W L E hb]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hW (mE_im_nonneg E))
  exact min_le_min (Real.sqrt_le_sqrt (by linarith))
    (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg L))

theorem flowScale_pos {W : ℝ} (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L) {E : ℝ} (hE : |E| < 2)
    {t : ℝ} (ht1 : t < 1) : 0 < flowScale W L E t := by
  rw [flowScale_eq W L E ht1.le]
  have h1 : 0 < 1 - t := by linarith
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have := mE_im_pos hE
  have : 0 < min (Real.sqrt (1 - t)) (L * (1 - t)) :=
    lt_min (Real.sqrt_pos.mpr h1) (mul_pos hL' h1)
  positivity

/-- `(W ℓ_s η_s)⁻¹ ≤ (W ℓ_t η_t)⁻¹` for `s ≤ t < 1`. -/
theorem flowScale_inv_le {W : ℝ} (hW : 0 < W) {L : ℕ} (hL : 1 ≤ L) {E : ℝ} (hE : |E| < 2)
    {s t : ℝ} (hst : s ≤ t) (ht1 : t < 1) : (flowScale W L E s)⁻¹ ≤ (flowScale W L E t)⁻¹ :=
  inv_anti₀ (flowScale_pos hW hL hE ht1)
    (flowScale_antitoneOn hW.le L E (Set.mem_Iic.mpr (hst.trans ht1.le))
      (Set.mem_Iic.mpr ht1.le) hst)

end Scale

section Grid

variable {W τ' : ℝ}

/-- The geometric grid of p. 24: `1 - s_k = W^{-kτ'}`. -/
noncomputable def gridS (W τ' : ℝ) (k : ℕ) : ℝ := 1 - W ^ (-((k : ℝ) * τ'))

theorem gridS_zero : gridS W τ' 0 = 0 := by simp [gridS]

theorem one_sub_gridS (k : ℕ) : 1 - gridS W τ' k = W ^ (-((k : ℝ) * τ')) := by
  simp [gridS]

theorem gridS_lt_one (hW : 0 < W) (k : ℕ) : gridS W τ' k < 1 := by
  have := Real.rpow_pos_of_pos hW (-((k : ℝ) * τ'))
  rw [gridS]; linarith

theorem gridS_nonneg (hW : 1 ≤ W) (hτ : 0 ≤ τ') (k : ℕ) : 0 ≤ gridS W τ' k := by
  have := Real.rpow_le_one_of_one_le_of_nonpos hW
    (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg k) hτ))
  rw [gridS]; linarith

theorem gridS_mono (hW : 1 ≤ W) (hτ : 0 ≤ τ') : Monotone (gridS W τ') := by
  intro a b hab
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have := Real.rpow_le_rpow_of_exponent_le hW
    (neg_le_neg (mul_le_mul_of_nonneg_right hab' hτ))
  rw [gridS, gridS]; linarith

/-- `1 - s_{k+1} = W^{-τ'} (1 - s_k)`. -/
theorem one_sub_gridS_succ (hW : 0 < W) (k : ℕ) :
    1 - gridS W τ' (k + 1) = W ^ (-τ') * (1 - gridS W τ' k) := by
  rw [one_sub_gridS, one_sub_gridS, ← Real.rpow_add hW]
  congr 1
  push_cast
  ring

theorem rpow_neg_pow_thirty (hW : 0 < W) : (W ^ (-τ')) ^ 30 = W ^ (-(30 * τ')) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]
  congr 1
  push_cast
  ring

/-- `((1 - s_{k+1})/(1 - s_k))^{30} = W^{-30τ'}`, i.e. `((1-s_k)/(1-s_{k+1}))^{-30} = W^{-30τ'}`. -/
theorem gridS_ratio_pow (hW : 0 < W) (k : ℕ) :
    ((1 - gridS W τ' (k + 1)) / (1 - gridS W τ' k)) ^ 30 = W ^ (-(30 * τ')) := by
  have h0 : 1 - gridS W τ' k ≠ 0 := (sub_pos.mpr (gridS_lt_one hW k)).ne'
  rw [one_sub_gridS_succ hW, mul_div_assoc, div_self h0, mul_one, rpow_neg_pow_thirty hW]

/-- **(2.72) on the grid, paper-literal form.**  If `(W ℓ_t η_t)⁻¹ ≤ W^{-30τ'}` at
`t = s_{n₀}`, then every consecutive pair `(s_k, s_{k+1})` with `k + 1 ≤ n₀` satisfies (2.72). -/
theorem gridS_step_2_72 (hW : 1 ≤ W) (hτ : 0 ≤ τ') {L : ℕ} (hL : 1 ≤ L) {E : ℝ}
    (hE : |E| < 2) {n₀ : ℕ}
    (hA : (flowScale W L E (gridS W τ' n₀))⁻¹ ≤ W ^ (-(30 * τ'))) {k : ℕ} (hk : k + 1 ≤ n₀) :
    (flowScale W L E (gridS W τ' (k + 1)))⁻¹ ≤
      ((1 - gridS W τ' (k + 1)) / (1 - gridS W τ' k)) ^ 30 := by
  have hW0 : 0 < W := by linarith
  rw [gridS_ratio_pow hW0]
  exact (flowScale_inv_le hW0 hL hE (gridS_mono hW hτ hk) (gridS_lt_one hW0 n₀)).trans hA

/-- The grid truncated at `t`: `u_k = min(s_k, t)`. -/
noncomputable def gridT (W τ' t : ℝ) (k : ℕ) : ℝ := min (gridS W τ' k) t

theorem gridT_zero {t : ℝ} (ht0 : 0 ≤ t) : gridT W τ' t 0 = 0 := by
  rw [gridT, gridS_zero, min_eq_left ht0]

theorem gridT_of_le {t : ℝ} {n₀ : ℕ} (ht : t ≤ gridS W τ' n₀) : gridT W τ' t n₀ = t :=
  min_eq_right ht

theorem gridT_mono (hW : 1 ≤ W) (hτ : 0 ≤ τ') (t : ℝ) : Monotone (gridT W τ' t) :=
  fun _ _ hab => min_le_min_right t (gridS_mono hW hτ hab)

theorem gridT_le (t : ℝ) (k : ℕ) : gridT W τ' t k ≤ t := min_le_right _ _

/-- One step of the truncated grid shrinks `1 - u` by at most the factor `W^{-τ'}`. -/
theorem rpow_neg_mul_one_sub_gridT_le (hW : 1 ≤ W) (hτ : 0 ≤ τ') {t : ℝ} (ht1 : t < 1)
    (k : ℕ) : W ^ (-τ') * (1 - gridT W τ' t k) ≤ 1 - gridT W τ' t (k + 1) := by
  have hW0 : 0 < W := by linarith
  have hq0 : 0 < W ^ (-τ') := Real.rpow_pos_of_pos hW0 _
  have hq1 : W ^ (-τ') ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW (neg_nonpos.mpr hτ)
  have hrec := one_sub_gridS_succ (τ' := τ') hW0 k
  have ha1 := gridS_lt_one (τ' := τ') hW0 k
  set a := gridS W τ' k
  set b := gridS W τ' (k + 1)
  set q := W ^ (-τ')
  simp only [gridT]
  rcases le_total a t with hat | hta <;> rcases le_total b t with hbt | htb
  · rw [min_eq_left hat, min_eq_left hbt]; linarith
  · rw [min_eq_left hat, min_eq_right htb]; linarith
  · rw [min_eq_right hta, min_eq_left hbt]; nlinarith
  · rw [min_eq_right hta, min_eq_right htb]; nlinarith

/-- **(2.72) along the truncated grid.**  If `(W ℓ_t η_t)⁻¹ ≤ W^{-30τ'}`, then for **every** `k`
the pair `(u_k, u_{k+1})`, `u = gridT W τ' t`, satisfies (2.72):
`(W ℓ_{u_{k+1}} η_{u_{k+1}})⁻¹ ≤ ((1 - u_{k+1})/(1 - u_k))^{30}`. -/
theorem gridT_step_2_72 (hW : 1 ≤ W) (hτ : 0 ≤ τ') {L : ℕ} (hL : 1 ≤ L) {E : ℝ}
    (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) (hA : (flowScale W L E t)⁻¹ ≤ W ^ (-(30 * τ')))
    (k : ℕ) :
    (flowScale W L E (gridT W τ' t (k + 1)))⁻¹ ≤
      ((1 - gridT W τ' t (k + 1)) / (1 - gridT W τ' t k)) ^ 30 := by
  have hW0 : 0 < W := by linarith
  have hq0 : 0 < W ^ (-τ') := Real.rpow_pos_of_pos hW0 _
  have hu : 0 < 1 - gridT W τ' t k := by have := gridT_le (W := W) (τ' := τ') t k; linarith
  have hratio : W ^ (-τ') ≤ (1 - gridT W τ' t (k + 1)) / (1 - gridT W τ' t k) := by
    rw [le_div_iff₀ hu]
    exact rpow_neg_mul_one_sub_gridT_le hW hτ ht1 k
  calc (flowScale W L E (gridT W τ' t (k + 1)))⁻¹
      ≤ (flowScale W L E t)⁻¹ := flowScale_inv_le hW0 hL hE (gridT_le t (k + 1)) ht1
    _ ≤ W ^ (-(30 * τ')) := hA
    _ = (W ^ (-τ')) ^ 30 := (rpow_neg_pow_thirty hW0).symm
    _ ≤ _ := pow_le_pow_left₀ hq0.le hratio 30

end Grid

section Choice

/-! ### Choosing `τ'` and `n₀` -/

/-- `t ≤ s_{n₀}` as soon as `1 - t ≥ W^{-2}` and `n₀ τ' ≥ 2`. -/
theorem le_gridS_of {W τ' t : ℝ} (hW : 1 ≤ W) {n₀ : ℕ} (hn : 2 ≤ (n₀ : ℝ) * τ')
    (ht : W ^ (-2 : ℝ) ≤ 1 - t) : t ≤ gridS W τ' n₀ := by
  have := Real.rpow_le_rpow_of_exponent_le hW (neg_le_neg hn)
  rw [gridS]; linarith

/-- **Lower bound on the scale.**  If `1 ≤ L ≤ W` (i.e. `W ≥ N^{1/2}`, `N = WL`) and
`1 - t ≥ N^{-1+τ}` with `τ ≥ 0`, then `W ℓ_t η_t ≥ Im m^{(E)} · W^{τ/2}`. -/
theorem flowScale_ge {W : ℝ} {L : ℕ} (hL : 1 ≤ L) (hLW : (L : ℝ) ≤ W) (E : ℝ) {τ t : ℝ}
    (hτ : 0 ≤ τ) (ht : (W * L) ^ (-1 + τ) ≤ 1 - t) :
    (mE E).im * W ^ (τ / 2) ≤ flowScale W L E t := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hW1 : 1 ≤ W := hL1.trans hLW
  have hW0 : 0 < W := by linarith
  have hN1 : 1 ≤ W * L := by nlinarith
  have hN0 : 0 < W * L := by linarith
  have ht1 : t < 1 := by have := Real.rpow_pos_of_pos hN0 (-1 + τ); linarith
  have h1t : 0 < 1 - t := by linarith
  set P := (W * L) ^ τ with hP
  have hP' : (W * L) ^ (-1 + τ) = (W * L)⁻¹ * P := by
    rw [Real.rpow_add hN0, Real.rpow_neg_one]
  have hWP : W ^ τ ≤ P := Real.rpow_le_rpow hW0.le (by nlinarith) hτ
  set Q := W ^ (τ / 2) with hQ
  have hQ2 : Q ^ 2 = W ^ τ := by
    rw [hQ, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; norm_num
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hW1 (by linarith)
  have hNP : P ≤ W * L * (1 - t) := by
    rw [hP'] at ht
    calc P = W * L * ((W * L)⁻¹ * P) := by field_simp
      _ ≤ W * L * (1 - t) := mul_le_mul_of_nonneg_left ht hN0.le
  have hc1 : Q ≤ W * (L * (1 - t)) := by nlinarith
  have hc2 : Q ≤ W * Real.sqrt (1 - t) := by
    have hs := Real.sq_sqrt h1t.le
    have hsq : Q ^ 2 ≤ (W * Real.sqrt (1 - t)) ^ 2 := by
      rw [mul_pow, hs, hQ2]
      have : W * L * (1 - t) ≤ W ^ 2 * (1 - t) := by nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp hsq
  rw [flowScale_eq W L E ht1.le, mul_comm W, mul_assoc, mul_min_of_nonneg _ _ hW0.le]
  exact mul_le_mul_of_nonneg_left (le_min hc2 hc1) (mE_im_nonneg E)

/-- "`N` large enough": for `δ > 0`, `c₀ > 0` there is `W₀ ≥ 1` with `c₀⁻¹ ≤ W^δ` for `W ≥ W₀`. -/
theorem exists_inv_le_rpow {δ c₀ : ℝ} (hδ : 0 < δ) (hc : 0 < c₀) :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ W, W₀ ≤ W → c₀⁻¹ ≤ W ^ δ := by
  refine ⟨max 1 (c₀⁻¹ ^ δ⁻¹), le_max_left _ _, fun W hW => ?_⟩
  have h0 : 0 ≤ c₀⁻¹ ^ δ⁻¹ := Real.rpow_nonneg (inv_nonneg.mpr hc.le) _
  calc c₀⁻¹ = (c₀⁻¹ ^ δ⁻¹) ^ δ := (Real.rpow_inv_rpow (inv_nonneg.mpr hc.le) hδ.ne').symm
    _ ≤ W ^ δ := Real.rpow_le_rpow h0 ((le_max_right _ _).trans hW) hδ.le

/-- The hypothesis `(W ℓ_t η_t)⁻¹ ≤ W^{-30τ'}` of p. 24, from `flowScale_ge` and
`(Im m)⁻¹ ≤ W^{τ/2 - 30τ'}` ("`W` large"). -/
theorem flowScale_inv_le_rpow {W : ℝ} {L : ℕ} (hL : 1 ≤ L) (hLW : (L : ℝ) ≤ W) {E : ℝ}
    (hE : |E| < 2) {τ τ' t : ℝ} (hτ : 0 ≤ τ) (ht : (W * L) ^ (-1 + τ) ≤ 1 - t)
    (hbig : ((mE E).im)⁻¹ ≤ W ^ (τ / 2 - 30 * τ')) :
    (flowScale W L E t)⁻¹ ≤ W ^ (-(30 * τ')) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hW0 : 0 < W := by linarith
  have hm := mE_im_pos hE
  have hge := flowScale_ge hL hLW E hτ ht
  have hsplit : W ^ (τ / 2) = W ^ (τ / 2 - 30 * τ') * W ^ (30 * τ') := by
    rw [← Real.rpow_add hW0]; ring_nf
  have hpos : 0 < W ^ (30 * τ') := Real.rpow_pos_of_pos hW0 _
  have h1 : 1 ≤ (mE E).im * W ^ (τ / 2 - 30 * τ') := (inv_le_iff_one_le_mul₀' hm).mp hbig
  have h2 : W ^ (30 * τ') ≤ flowScale W L E t :=
    calc W ^ (30 * τ') ≤ ((mE E).im * W ^ (τ / 2 - 30 * τ')) * W ^ (30 * τ') := by nlinarith
      _ = (mE E).im * W ^ (τ / 2) := by rw [hsplit]; ring
      _ ≤ _ := hge
  rw [Real.rpow_neg hW0.le]
  exact inv_anti₀ hpos h2

/-- `Im m^{(E)} ≥ √(2κ)/2` for `|E| ≤ 2 - κ`. -/
theorem mE_im_ge {E κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2) (hE : |E| ≤ 2 - κ) :
    Real.sqrt (2 * κ) / 2 ≤ (mE E).im := by
  have := le_zt_im hκ0 hκ2 hE (t := 0) (by norm_num)
  rw [zt_im] at this
  simpa using this

/-- **The time grid of the proof of Lemmas 2.18–2.20 (p. 24), with (2.72) at every step.**
Fix `0 < κ`, `0 ≤ τ`, `0 < τ'` with `60 τ' < τ`, and `n₀` with `2 ≤ n₀ τ'`.  Then there is
`W₀` such that for all `W ≥ W₀`, `1 ≤ L ≤ W`, `|E| ≤ 2 - κ` and `0 ≤ t` with
`(WL)^{-1+τ} ≤ 1 - t`, the truncated grid `u_k = min(1 - W^{-kτ'}, t)` runs from `u_0 = 0` to
`u_{n₀} = t`, is monotone, `(W ℓ_t η_t)⁻¹ ≤ W^{-30τ'}`, and every step satisfies (2.72). -/
theorem flow_grid_2_72 {κ τ τ' : ℝ} (hκ : 0 < κ) (hτ : 0 ≤ τ) (hτ' : 0 < τ')
    (hττ' : 60 * τ' < τ) {n₀ : ℕ} (hn₀ : 2 ≤ (n₀ : ℝ) * τ') :
    ∃ W₀ : ℝ, 1 ≤ W₀ ∧ ∀ W : ℝ, W₀ ≤ W → ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ W →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℝ, 0 ≤ t → (W * L) ^ (-1 + τ) ≤ 1 - t →
        gridT W τ' t 0 = 0 ∧ gridT W τ' t n₀ = t ∧ Monotone (gridT W τ' t) ∧
        (flowScale W L E t)⁻¹ ≤ W ^ (-(30 * τ')) ∧
        ∀ k : ℕ, (flowScale W L E (gridT W τ' t (k + 1)))⁻¹ ≤
          ((1 - gridT W τ' t (k + 1)) / (1 - gridT W τ' t k)) ^ 30 := by
  set k₀ := min κ 2 with hk₀
  have hk0 : 0 < k₀ := lt_min hκ (by norm_num)
  have hk2 : k₀ ≤ 2 := min_le_right _ _
  set c₀ := Real.sqrt (2 * k₀) / 2 with hc₀
  have hc0 : 0 < c₀ := by rw [hc₀]; have := Real.sqrt_pos.mpr (by linarith : 0 < 2 * k₀); linarith
  obtain ⟨W₀, hW₀, hW⟩ := exists_inv_le_rpow (δ := τ / 2 - 30 * τ') (by linarith) hc0
  refine ⟨W₀, hW₀, fun W hW₀W L hL hLW E hE t ht0 ht => ?_⟩
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hW1 : 1 ≤ W := hL1.trans hLW
  have hW0 : 0 < W := by linarith
  have hτ'0 : 0 ≤ τ' := hτ'.le
  have hE' : |E| ≤ 2 - k₀ := hE.trans (by linarith [min_le_left κ 2])
  have hE2 : |E| < 2 := by linarith
  have hN1 : 1 ≤ W * L := by nlinarith
  have hN0 : 0 < W * L := by linarith
  have ht1 : t < 1 := by have := Real.rpow_pos_of_pos hN0 (-1 + τ); linarith
  have hbig : ((mE E).im)⁻¹ ≤ W ^ (τ / 2 - 30 * τ') :=
    (inv_anti₀ hc0 (mE_im_ge hk0 hk2 hE')).trans (hW W hW₀W)
  have hA := flowScale_inv_le_rpow hL hLW hE2 hτ ht hbig
  have hW2 : W ^ (-2 : ℝ) ≤ 1 - t := by
    have h1 : (W * L) ^ (-1 : ℝ) ≤ (W * L) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have h2 : W ^ (-2 : ℝ) ≤ (W * L) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hW0.le, Real.rpow_neg_one, Real.rpow_two]
      exact inv_anti₀ hN0 (by nlinarith)
    linarith
  have htn : t ≤ gridS W τ' n₀ := le_gridS_of hW1 hn₀ hW2
  exact ⟨gridT_zero ht0, gridT_of_le htn, gridT_mono hW1 hτ'0 t, hA,
    gridT_step_2_72 hW1 hτ'0 hL hE2 ht1 hA⟩

end Choice

section Dictionary

/-! ### The scale dictionary of p. 21–22 -/

/-- `η_t ≤ 1 - t`. -/
theorem etaT_le {E : ℝ} (hE : |E| ≤ 2) {t : ℝ} (ht : t ≤ 1) : etaT E t ≤ 1 - t := by
  rw [etaT_eq_zt_im]; exact zt_im_le hE ht

/-- `η_t ≥ (1 - t) √(2κ)/2` for `|E| ≤ 2 - κ`.  With `etaT_le`: `η_t ≍ 1 - t`. -/
theorem le_etaT {E κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2) (hE : |E| ≤ 2 - κ) {t : ℝ}
    (ht : t ≤ 1) : (1 - t) * (Real.sqrt (2 * κ) / 2) ≤ etaT E t := by
  rw [etaT_eq_zt_im]; exact le_zt_im hκ0 hκ2 hE ht

/-- `η ↦ min(η^{-1/2}, L) + 1`. -/
noncomputable def ellOf (L : ℕ) (η : ℝ) : ℝ := min (1 / Real.sqrt η) (L : ℝ) + 1

/-- The diffusion length at the block level (2.1): `ℓ(z) = min(η^{-1/2}, L) + 1`, `η = Im z`. -/
noncomputable def ellZ (L : ℕ) (z : ℂ) : ℝ := ellOf L z.im

theorem ellOf_antitone {L : ℕ} {η₁ η₂ : ℝ} (h0 : 0 < η₁) (h : η₁ ≤ η₂) :
    ellOf L η₂ ≤ ellOf L η₁ := by
  unfold ellOf
  have := one_div_le_one_div_of_le (Real.sqrt_pos.mpr h0) (Real.sqrt_le_sqrt h)
  linarith [min_le_min_right (L : ℝ) this]

/-- Comparable `η`'s give comparable `ℓ`'s: `η₁ ≤ K η₂` implies `ℓ(η₂) ≤ √K ℓ(η₁)`. -/
theorem ellOf_le_sqrt_mul {L : ℕ} {η₁ η₂ K : ℝ} (h0 : 0 < η₁) (hK : 1 ≤ K)
    (h : η₁ ≤ K * η₂) : ellOf L η₂ ≤ Real.sqrt K * ellOf L η₁ := by
  have hK0 : 0 < K := by linarith
  have hη₂ : 0 < η₂ := by
    by_contra hc
    push Not at hc
    nlinarith
  have hs1 : 1 ≤ Real.sqrt K := Real.one_le_sqrt.mpr hK
  have key : 1 / Real.sqrt η₂ ≤ Real.sqrt K * (1 / Real.sqrt η₁) := by
    have : Real.sqrt η₁ ≤ Real.sqrt K * Real.sqrt η₂ := by
      rw [← Real.sqrt_mul hK0.le]; exact Real.sqrt_le_sqrt h
    rw [mul_one_div, div_le_div_iff₀ (Real.sqrt_pos.mpr hη₂) (Real.sqrt_pos.mpr h0)]
    linarith
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hm : min (1 / Real.sqrt η₂) (L : ℝ) ≤ Real.sqrt K * min (1 / Real.sqrt η₁) L := by
    rw [mul_min_of_nonneg _ _ (by linarith)]
    exact min_le_min key (by nlinarith)
  unfold ellOf
  nlinarith

theorem ellOf_one_sub (L : ℕ) {t : ℝ} (ht1 : t < 1) : ellOf L (1 - t) = ellHat L (t : ℂ) + 1 := by
  rw [ellOf, ellHat_ofReal L ht1]

/-- `ℓ_t ≥ 1` for `0 ≤ t < 1` and `L ≥ 1`. -/
theorem one_le_ellHat_of_nonneg {L : ℕ} (hL : 1 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 ≤ ellHat L (t : ℂ) := by
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  have hsle : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  rw [ellHat_ofReal L ht1]
  exact le_min ((one_le_div hs).mpr hsle) (by exact_mod_cast hL)

/-- `ℓ_t ≤ ℓ(z_t)`. -/
theorem ellHat_le_ellZ_zt (L : ℕ) {E : ℝ} (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    ellHat L (t : ℂ) ≤ ellZ L (zt E t) := by
  have hη0 : 0 < (zt E t).im := by
    rw [zt_im]; exact mul_pos (by linarith) (mE_im_pos hE)
  have hη1 : (zt E t).im ≤ 1 - t := zt_im_le hE.le ht1.le
  have := ellOf_antitone (L := L) hη0 hη1
  rw [ellOf_one_sub L ht1] at this
  rw [ellZ]
  linarith

/-- `ℓ(z_t) ≤ C_κ ℓ_t` with `C_κ = 2 √(2/√(2κ))`.  With `ellHat_le_ellZ_zt`: `ℓ(z_t) ≍ ℓ_t`. -/
theorem ellZ_zt_le {L : ℕ} (hL : 1 ≤ L) {E κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2)
    (hE : |E| ≤ 2 - κ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ellZ L (zt E t) ≤ 2 * Real.sqrt (2 / Real.sqrt (2 * κ)) * ellHat L (t : ℂ) := by
  set r := Real.sqrt (2 * κ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by nlinarith)
  set K := 2 / r with hK
  have hK1 : 1 ≤ K := by rw [hK, le_div_iff₀ hr0]; linarith
  have hKr : K * (r / 2) = 1 := by rw [hK]; field_simp
  have hc := le_zt_im hκ0 hκ2 hE ht1.le
  have h1t : 1 - t ≤ K * (zt E t).im := by
    calc 1 - t = K * ((1 - t) * (r / 2)) := by linear_combination (t - 1) * hKr
      _ ≤ K * (zt E t).im := mul_le_mul_of_nonneg_left hc (by linarith)
  have h := ellOf_le_sqrt_mul (L := L) (by linarith : 0 < 1 - t) hK1 h1t
  rw [ellOf_one_sub L ht1] at h
  have hℓ := one_le_ellHat_of_nonneg hL ht0 ht1
  have hs : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  rw [ellZ]
  nlinarith

theorem sqrt_sixteen : Real.sqrt 16 = 4 := by
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The scale dictionary of p. 21–22.**  For `0 < Im z ≤ 1`, `|Re z| ≤ 2 - κ`, and `E, t`
from Lemma 2.8 (so that (2.37), (2.40) hold):
`(1 - t) ≍ Im z_t ≍ Im z`, `ℓ(z_t) ≍ ℓ_t`, `ℓ(z) ≍ ℓ(z_t)`, and hence `ℓ(z) ≍ ℓ_t`. -/
theorem lemma28_scales {κ : ℝ} (hκ0 : 0 < κ) (hκ2 : κ ≤ 2) {z : ℂ} (hz0 : 0 < z.im)
    (hz1 : z.im ≤ 1) (hκ : |z.re| ≤ 2 - κ) {L : ℕ} (hL : 1 ≤ L) :
    (1 - lemT z) * (Real.sqrt (2 * κ) / 2) ≤ (zt (lemE z) (lemT z)).im ∧
    (zt (lemE z) (lemT z)).im ≤ 1 - lemT z ∧
    (1 / 16 : ℝ) * z.im ≤ (zt (lemE z) (lemT z)).im ∧
    (zt (lemE z) (lemT z)).im ≤ 16 * z.im ∧
    ellHat L (lemT z : ℂ) ≤ ellZ L (zt (lemE z) (lemT z)) ∧
    ellZ L (zt (lemE z) (lemT z)) ≤ 2 * Real.sqrt (2 / Real.sqrt (2 * κ)) * ellHat L (lemT z : ℂ) ∧
    ellZ L z ≤ 4 * ellZ L (zt (lemE z) (lemT z)) ∧
    ellZ L (zt (lemE z) (lemT z)) ≤ 4 * ellZ L z ∧
    ellHat L (lemT z : ℂ) ≤ 4 * ellZ L z ∧
    ellZ L z ≤ 8 * Real.sqrt (2 / Real.sqrt (2 * κ)) * ellHat L (lemT z : ℂ) := by
  obtain ⟨hE, ht16, hlo, hhi⟩ := lemma28_quant hκ0 hz0 hz1 hκ
  have ht0 : 0 ≤ lemT z := by linarith
  have ht1 : lemT z < 1 := lemT_lt_one hz0
  have hE2 : |lemE z| < 2 := by linarith
  have hhi' : (zt (lemE z) (lemT z)).im ≤ 16 * z.im := by
    rw [show (16 : ℝ) = (1 / 16 : ℝ)⁻¹ by norm_num]; exact hhi
  have hηt : 0 < (zt (lemE z) (lemT z)).im := by linarith
  have h1 := le_zt_im hκ0 hκ2 hE ht1.le
  have h2 := zt_im_le (by linarith) ht1.le
  have h3 := ellHat_le_ellZ_zt L hE2 ht1
  have h4 := ellZ_zt_le hL hκ0 hκ2 hE ht0 ht1
  have h5 : ellZ L z ≤ 4 * ellZ L (zt (lemE z) (lemT z)) := by
    have := ellOf_le_sqrt_mul (L := L) hηt (by norm_num : (1 : ℝ) ≤ 16) hhi'
    rwa [sqrt_sixteen] at this
  have h6 : ellZ L (zt (lemE z) (lemT z)) ≤ 4 * ellZ L z := by
    have := ellOf_le_sqrt_mul (L := L) (η₂ := (zt (lemE z) (lemT z)).im) hz0
      (by norm_num : (1 : ℝ) ≤ 16) (by linarith)
    rwa [sqrt_sixteen] at this
  refine ⟨h1, h2, hlo, hhi', h3, h4, h5, h6, h3.trans h6, ?_⟩
  calc ellZ L z ≤ 4 * ellZ L (zt (lemE z) (lemT z)) := h5
    _ ≤ 4 * (2 * Real.sqrt (2 / Real.sqrt (2 * κ)) * ellHat L (lemT z : ℂ)) := by linarith
    _ = _ := by ring

end Dictionary

end RBM
