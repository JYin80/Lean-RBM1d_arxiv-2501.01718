/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57
import Mathlib.Analysis.MeanInequalities

/-!
# Quantitative derivative bounds for the smooth-cutoff scheme (T158)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Section 5.3 (step 2 of Theorem 2.21): the **deterministic, real-analytic** half of
the smooth-cutoff replacement for the paper's stopping time.

`docs/STATUS.md` ("T132c 第 0 步", subsection "⚠ 光滑截断方案：三个真实缺口") records why the
moment route cannot use a stopping time and therefore replaces it by the smooth weight
`χ(J_u/Θ_u)` attached to the state function `J_u = J(u, H_u)`, `J` a **smooth maximum** of the
ratios `|(L-K)_{u,(+,-),a}| / T_{u,D}(‖a₁-a₂‖)` of (5.28)/(5.29).  Turning that into a drift
estimate needs four deterministic ingredients; this file supplies them.  Nothing here is
random: every statement is about explicit real functions.

## 1. The smooth maximum and its weights

* `RBM.Cutoff.smoothMax r a = (∑_i a_i^r)^{1/r}`, `RBM.Cutoff.cutWeight r a i = (a_i/S)^{r-1}`.
* `le_smoothMax`, `smoothMax_le` — `max ≤ smoothMax ≤ (card ι)^{1/r} max`.
* `rpow_card_le_exp_one` — **`r ≍ log (card ι)` makes `(card ι)^{1/r} ≤ e`**: the whole point
  of the `r`-norm.
* `sum_rpow_sub_one_le`, `sum_cutWeight_le` — **the weight-sum bound** `∑_i w_i ≤
  (card ι)^{1/r}`, by Hölder (`Real.inner_le_weight_mul_Lp_of_nonneg`).  It is sharp: see the
  `example` after `sum_cutWeight_le`.
* `hasDerivAt_smoothMax` — **the chain rule**: `∂(smoothMax) = ∑_i w_i ∂a_i`.
* `abs_sum_cutWeight_mul_le` — the resulting `O(1)`-Lipschitz bound.
* `hasDerivAt_deriv_smoothMax`, `smoothMax_second_le` — the **second** derivative, with the
  nonpositive `-(r-1)(∑ a^{r-1}v)² P^{1/r-2}` term made explicit so that it can be dropped;
  the surviving cost of smoothing is one factor `r - 1 ≍ log N`, i.e. `N^{o(1)}`.

## 2. `∑ S |∂J|²` normalized by `T_{u,D}`, via (5.36)

* `sq_sum_weighted_le`, `sum_weighted_quadForm_le`, `sum_cutWeight_quadForm_le` — a weighted
  Cauchy–Schwarz turning a per-index bound `∑_x S_x (∂_x f_i)² ≤ B` into the same bound for
  the weighted combination, with the loss `(∑ w)²`.
* `one_le_rpow_mul_tailT_sq`, `inv_tailT_sq_le` — the `W^{-D}` floor of (5.27) absorbs an
  additive remainder into the `T_{u,D}²` normalization at the price `W^{2D}`.
* `sum_cutWeight_quadForm_tailT_le` — the two combined: from the shape of **(5.36)**, which is
  `RBM.Lemma57.ee_le` / `RBM.Lemma57.ee_le_paper` (T156, a theorem independent of the stopped
  martingale hypothesis), `∑_x S_x (∂_x J)² ≤ (card ι)^{2/r}(B + R W^{2D})`.

  Note that T133's `RBM.Gauss.BddC2C` constants (`Gauss/LoopC2.lean`) **cannot** play the role
  of `B`: they carry no `T_{u,D}` normalization and are off by `A^{O(1)}`; they are the
  dominated-convergence half, not the quantitative half.

## 3. `∂_u T_{u,D}`

* `hasDerivAt_tailT_flow` — `∂_u T_{u,D}(ℓ) = A_u^{-2}e^{-√(ℓ/ℓ_u)}(-2 ∂_u log A_u +
  √(ℓ/ℓ_u) ℓ'_u/(2ℓ_u))`, `A_u = W ℓ_u η_u`.  The `W^{-D}` floor is `u`-independent and
  contributes nothing.
* `neg_deriv_tailT_le`, `neg_deriv_tailT_div_le` — the second summand is **not uniformly
  bounded in `ℓ`**, but its sign is favourable as soon as `ℓ_u` is non-decreasing, so it can be
  dropped, leaving `-∂_u log T_{u,D}(ℓ) ≤ 2(∂_u log A_u)_+` uniformly in `ℓ`.  The floor enters
  only as `0 ≤ W^{-D}`, which is what makes `(T - W^{-D})/T ≤ 1` and so covers the floor
  region by the same bound.
* `tailT_le_tailT_of_flow` — the same sign statement without derivatives: `T_{u,D}` is
  non-decreasing in `u` when `ℓ_u` grows and `A_u` decreases (the flow of Section 2;
  `RBM.flowScale_antitoneOn`), so `J = T^{(L-K)}/T_{u,D}` only gets smaller.

## 4. The time dependence of the threshold

The term `-χ'(J_u/Θ_u)·(J_u/Θ_u)·Θ̇_u/Θ_u` that the original ticket omitted.

* `hasDerivAt_threshold` — for `Θ_u = c η_u^{-4}` and `∂_u η_u = -m` (the paper's
  `η_u = (1-u) Im m^{(E)}`), `Θ̇_u/Θ_u = 4m/η_u`.
* `hasDerivAt_cutComp` — the chain rule for `u ↦ χ(J_u/Θ_u)`, exhibiting that term.
* `abs_threshold_drift_le` — on the gap `J_u/Θ_u ∈ [1,2]` it is `≤ 8 C_χ m/η_u`, the same
  order `η_u^{-1}` as the other drift terms, hence harmless.

## Deliberately *not* here

* The **de-truncation** step.  It belongs at the probability level (a crossing argument plus a
  time net, `RBM.Step2Moment.MomentHyp.holder` + `RBM.stochDom_timeIcc_of_holder`), not at the
  moment level with an indicator: the latter raises the moment order by `(K+δ)/δ`.
* A concrete `C²` cutoff profile `χ`.  Every statement here takes `χ` through a `HasDerivAt`
  hypothesis and a bound on `|χ'|`, so nothing is assumed about `χ` beyond what a `ContDiffBump`
  provides; no structure is introduced that could be vacuous.
* The generator identity `(∂_u + 𝓛)(L-K) = F` itself (T132b) and the assembly of the three
  drift terms (T132c).

## Deviations

None from the paper's statements: (5.27)–(5.29) are used exactly as
`RBM.tailT` / `RBM.ratioJ` / `RBM.Step2.jStar` already formalize them, and the `r`-norm is a
Lean-side device with no counterpart in the paper (the paper uses a stopping time instead).
Constants (`e`, `8`, `W^{2D}`) are explicit and not optimal.
-/

namespace RBM
namespace Cutoff

open Real Finset

/-! ### The smooth maximum (`r`-norm) -/

variable {ι : Type*} [Fintype ι]

/-- The smooth maximum `(∑_i a_i^r)^{1/r}` of a family of nonnegative reals.  For
`r ≍ log (card ι)` it is within a factor `e` of `max_i a_i` (`le_smoothMax` and
`smoothMax_le_exp_one_mul`), and unlike `max` it is differentiable. -/
noncomputable def smoothMax (r : ℝ) (a : ι → ℝ) : ℝ := (∑ i, a i ^ r) ^ r⁻¹

/-- The chain-rule weight `w_i = (a_i / smoothMax r a)^{r-1}` attached to the index `i`. -/
noncomputable def cutWeight (r : ℝ) (a : ι → ℝ) (i : ι) : ℝ :=
  a i ^ (r - 1) / (∑ j, a j ^ r) ^ (1 - r⁻¹)

variable {r : ℝ} {a : ι → ℝ}

theorem sum_rpow_nonneg (ha : ∀ i, 0 ≤ a i) : 0 ≤ ∑ i, a i ^ r :=
  Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _

theorem smoothMax_nonneg (ha : ∀ i, 0 ≤ a i) : 0 ≤ smoothMax r a :=
  Real.rpow_nonneg (sum_rpow_nonneg ha) _

/-- `max ≤ smooth max`. -/
theorem le_smoothMax (hr : 0 < r) (ha : ∀ i, 0 ≤ a i) (j : ι) : a j ≤ smoothMax r a := by
  have h1 : a j ^ r ≤ ∑ i, a i ^ r :=
    Finset.single_le_sum (f := fun i => a i ^ r) (fun i _ => Real.rpow_nonneg (ha i) _)
      (Finset.mem_univ j)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (ha j) r) h1 (le_of_lt (inv_pos.2 hr))
  rwa [← Real.rpow_mul (ha j), mul_inv_cancel₀ hr.ne', Real.rpow_one] at h2

/-- `smooth max ≤ (card ι)^{1/r} · max`. -/
theorem smoothMax_le (hr : 0 < r) (ha : ∀ i, 0 ≤ a i) {b : ℝ} (hb : ∀ i, a i ≤ b) (hb0 : 0 ≤ b) :
    smoothMax r a ≤ (Fintype.card ι : ℝ) ^ r⁻¹ * b := by
  have hle : ∑ i, a i ^ r ≤ (Fintype.card ι : ℝ) * b ^ r := by
    calc ∑ i, a i ^ r ≤ ∑ _i : ι, b ^ r :=
          Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (ha i) (hb i) hr.le
      _ = (Fintype.card ι : ℝ) * b ^ r := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 := Real.rpow_le_rpow (sum_rpow_nonneg ha) hle (le_of_lt (inv_pos.2 hr))
  refine h2.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hb0 _), ← Real.rpow_mul hb0,
    mul_inv_cancel₀ hr.ne', Real.rpow_one]

/-- **`r ≍ log (card ι)` makes the smoothing constant `O(1)`**: as soon as `r ≥ log (card ι)`,
the factor `(card ι)^{1/r}` of `smoothMax_le` and of `sum_cutWeight_le` is at most `e`. -/
theorem rpow_card_le_exp_one (hr : 0 < r) (hlog : Real.log (Fintype.card ι) ≤ r) :
    (Fintype.card ι : ℝ) ^ r⁻¹ ≤ Real.exp 1 := by
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) (Fintype.card ι)) with h0 | h0
  · rw [← h0, Real.zero_rpow (inv_ne_zero hr.ne')]
    exact (Real.exp_pos 1).le
  · rw [Real.rpow_def_of_pos h0, Real.exp_le_exp]
    rcases le_or_gt (Real.log (Fintype.card ι)) 0 with hl | hl
    · have : Real.log (Fintype.card ι) * r⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl (by positivity)
      linarith
    · rw [mul_inv_le_iff₀ hr]; linarith

/-- **The weight bound, Hölder half.**  `∑_i a_i^{r-1} ≤ (card ι)^{1/r} (∑_i a_i^r)^{(r-1)/r}`. -/
theorem sum_rpow_sub_one_le (hr : 1 < r) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i ^ (r - 1) ≤ (Fintype.card ι : ℝ) ^ r⁻¹ * (∑ i, a i ^ r) ^ (1 - r⁻¹) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  set p : ℝ := r / (r - 1) with hp_def
  have hp1 : 1 ≤ p := by rw [hp_def, le_div_iff₀ hr1]; linarith
  have hpinv : 1 - p⁻¹ = r⁻¹ := by rw [hp_def, inv_div]; field_simp; ring
  have key := Real.inner_le_weight_mul_Lp_of_nonneg (Finset.univ : Finset ι) hp1
      (fun _ => (1 : ℝ)) (fun i => a i ^ (r - 1)) (fun _ => zero_le_one)
      (fun i => Real.rpow_nonneg (ha i) _)
  simp only [one_mul] at key
  have e1 : ∑ _i : ι, (1 : ℝ) = (Fintype.card ι : ℝ) := by simp
  have e2 : ∀ i : ι, (a i ^ (r - 1)) ^ p = a i ^ r := by
    intro i
    rw [← Real.rpow_mul (ha i), hp_def]
    congr 1
    field_simp
  rw [e1, hpinv] at key
  simp only [e2] at key
  have e3 : p⁻¹ = 1 - r⁻¹ := by rw [hp_def, inv_div]; field_simp
  rwa [e3] at key

theorem cutWeight_nonneg (ha : ∀ i, 0 ≤ a i) (i : ι) : 0 ≤ cutWeight r a i :=
  div_nonneg (Real.rpow_nonneg (ha i) _) (Real.rpow_nonneg (sum_rpow_nonneg ha) _)

/-- **The weight-sum bound**: `∑_i w_i ≤ (card ι)^{1/r}`, i.e. `O(1)` for `r ≍ log (card ι)`
by `rpow_card_le_exp_one`.  This is the elementary fact that makes the smooth maximum a
`O(1)`-Lipschitz replacement for `max`. -/
theorem sum_cutWeight_le (hr : 1 < r) (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i ^ r) :
    ∑ i, cutWeight r a i ≤ (Fintype.card ι : ℝ) ^ r⁻¹ := by
  have hP : (0 : ℝ) < (∑ i, a i ^ r) ^ (1 - r⁻¹) := Real.rpow_pos_of_pos hpos _
  have : ∑ i, cutWeight r a i = (∑ i, a i ^ (r - 1)) / (∑ i, a i ^ r) ^ (1 - r⁻¹) := by
    rw [Finset.sum_div]; rfl
  rw [this, div_le_iff₀ hP]
  exact sum_rpow_sub_one_le hr ha

/-- **Sharpness / sanity check for `sum_cutWeight_le`.**  At `a ≡ 1` the weight sum equals
`(card ι)^{1/r}` exactly, so the constant in `sum_cutWeight_le` cannot be improved, and a
mis-stated exponent in `cutWeight` would be caught here. -/
example :
    ∑ i : Fin 2, cutWeight r (fun _ => (1 : ℝ)) i = (Fintype.card (Fin 2) : ℝ) ^ r⁻¹ := by
  have hone : ∀ x : ℝ, (1 : ℝ) ^ x = 1 := fun x => Real.one_rpow x
  have key : (2 : ℝ) / (2 : ℝ) ^ (1 - r⁻¹) = (2 : ℝ) ^ r⁻¹ := by
    have h := Real.rpow_sub (by norm_num : (0 : ℝ) < 2) 1 (1 - r⁻¹)
    rw [Real.rpow_one] at h
    have e : (1 : ℝ) - (1 - r⁻¹) = r⁻¹ := by ring
    rw [e] at h
    exact h.symm
  simp only [cutWeight, hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  rw [← key]
  ring

/-! ### The chain rule for the smooth maximum -/

/-- **The chain rule.**  If each `t ↦ g t i` is differentiable at `x` with positive value,
then so is the smooth maximum, and its derivative is the `cutWeight`-weighted average of the
derivatives. -/
theorem hasDerivAt_smoothMax {g : ℝ → ι → ℝ} {g' : ι → ℝ} {x : ℝ} (hr : 1 < r)
    (hg : ∀ i, HasDerivAt (fun t => g t i) (g' i) x) (hpos : 0 < ∑ i, g x i ^ r) :
    HasDerivAt (fun t => smoothMax r (g t)) (∑ i, cutWeight r (g x) i * g' i) x := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hin : ∀ i : ι, HasDerivAt (fun t => g t i ^ r) (g' i * r * g x i ^ (r - 1)) x :=
    fun i => (hg i).rpow_const (Or.inr hr.le)
  have hsum : HasDerivAt (fun t => ∑ i, g t i ^ r)
      (∑ i, g' i * r * g x i ^ (r - 1)) x := by
    have h := HasDerivAt.sum (u := (Finset.univ : Finset ι))
      (A := fun i t => g t i ^ r) (A' := fun i => g' i * r * g x i ^ (r - 1))
      (fun i _ => hin i)
    have heq : (fun t => ∑ i, g t i ^ r) = ∑ i : ι, fun t => g t i ^ r := by
      funext t; simp [Finset.sum_apply]
    rw [heq]; exact h
  have hne : (∑ i, g x i ^ r) ≠ 0 := hpos.ne'
  have hout := hsum.rpow_const (p := r⁻¹) (Or.inl hne)
  refine hout.congr_deriv ?_
  have hPinv : (∑ i, g x i ^ r) ^ (r⁻¹ - 1) = ((∑ i, g x i ^ r) ^ (1 - r⁻¹))⁻¹ := by
    rw [← Real.rpow_neg hpos.le]; ring_nf
  have hc : ∑ i, cutWeight r (g x) i * g' i
      = (∑ i, g x i ^ (r - 1) * g' i) * ((∑ i, g x i ^ r) ^ (1 - r⁻¹))⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cutWeight]; ring
  have hs : ∑ i, g' i * r * g x i ^ (r - 1) = r * ∑ i, g x i ^ (r - 1) * g' i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hPinv, hc, hs]
  field_simp

/-- **The `O(1)`-Lipschitz bound.**  A pointwise bound `|g'_i| ≤ B` on the derivatives is
inherited by the smooth maximum with the loss `(card ι)^{1/r}` of `sum_cutWeight_le`. -/
theorem abs_sum_cutWeight_mul_le (hr : 1 < r) (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i ^ r)
    {v : ι → ℝ} {B : ℝ} (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
    |∑ i, cutWeight r a i * v i| ≤ (Fintype.card ι : ℝ) ^ r⁻¹ * B := by
  calc |∑ i, cutWeight r a i * v i| ≤ ∑ i, |cutWeight r a i * v i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, cutWeight r a i * |v i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (cutWeight_nonneg ha i)]
    _ ≤ ∑ i, cutWeight r a i * B :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv i) (cutWeight_nonneg ha i)
    _ = (∑ i, cutWeight r a i) * B := by rw [Finset.sum_mul]
    _ ≤ (Fintype.card ι : ℝ) ^ r⁻¹ * B :=
        mul_le_mul_of_nonneg_right (sum_cutWeight_le hr ha hpos) hB

/-! ### The weighted quadratic form: `∑ S |∂J|²` from `∑ S |∂(L-K)_a|²` -/

/-- Weighted Cauchy–Schwarz: `(∑ w_i v_i)² ≤ (∑ w_i)(∑ w_i v_i²)`. -/
theorem sq_sum_weighted_le {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) :
    (∑ i, w i * v i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * v i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
    (fun i => √(w i)) (fun i => √(w i) * v i)
  have e0 : ∀ i : ι, √(w i) * (√(w i) * v i) = w i * v i := by
    intro i; rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e1 : ∀ i : ι, √(w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw i)
  have e2 : ∀ i : ι, (√(w i) * v i) ^ 2 = w i * v i ^ 2 := by
    intro i; rw [mul_pow, e1]
  simp only [e0, e1, e2] at h
  exact h

/-- **The `Σ S |∂J|²` reduction.**  If every member `g i` of the family satisfies the
`(5.36)`-type bound `∑_x S_x (g i x)² ≤ B` — in the application `g i = ∂(L-K)_{a_i}/T_{u,D}(d_i)`
and `B` is the right-hand side of (5.36) after dividing by `T_{u,D}²` — then the
`w`-weighted combination satisfies the same bound with the loss `(∑ w)²`.  Combined with
`sum_cutWeight_le` this is `∑_x S_x |∂_x J|² ≤ (card ι)^{2/r} B`. -/
theorem sum_weighted_quadForm_le {α : Type*} [Fintype α] {w : ι → ℝ} {Sq : α → ℝ}
    {g : ι → α → ℝ} {κ B : ℝ} (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i ≤ κ) (hκ : 0 ≤ κ)
    (hSq : ∀ x, 0 ≤ Sq x) (hB0 : 0 ≤ B) (hB : ∀ i, ∑ x, Sq x * g i x ^ 2 ≤ B) :
    ∑ x, Sq x * (∑ i, w i * g i x) ^ 2 ≤ κ ^ 2 * B := by
  have h1 : ∑ x, Sq x * (∑ i, w i * g i x) ^ 2
      ≤ ∑ x, Sq x * (κ * ∑ i, w i * g i x ^ 2) := by
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hSq x)
    refine (sq_sum_weighted_le hw (fun i => g i x)).trans ?_
    exact mul_le_mul_of_nonneg_right hsum
      (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have h2 : ∑ x, Sq x * (κ * ∑ i, w i * g i x ^ 2)
      = κ * ∑ i, w i * ∑ x, Sq x * g i x ^ 2 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  have h3 : ∑ i, w i * ∑ x, Sq x * g i x ^ 2 ≤ ∑ i, w i * B :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i) (hw i)
  have h4 : ∑ i, w i * B = (∑ i, w i) * B := by rw [Finset.sum_mul]
  calc ∑ x, Sq x * (∑ i, w i * g i x) ^ 2
      ≤ κ * ∑ i, w i * ∑ x, Sq x * g i x ^ 2 := by rw [← h2]; exact h1
    _ ≤ κ * ((∑ i, w i) * B) := by rw [← h4]; exact mul_le_mul_of_nonneg_left h3 hκ
    _ ≤ κ * (κ * B) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hB0) hκ
    _ = κ ^ 2 * B := by ring

/-- `∑ S |∂J|² ≤ (card ι)^{2/r} · B` for the smooth maximum's own weights. -/
theorem sum_cutWeight_quadForm_le {α : Type*} [Fintype α] {Sq : α → ℝ} {g : ι → α → ℝ}
    {B : ℝ} (hr : 1 < r) (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i ^ r)
    (hSq : ∀ x, 0 ≤ Sq x) (hB0 : 0 ≤ B) (hB : ∀ i, ∑ x, Sq x * g i x ^ 2 ≤ B) :
    ∑ x, Sq x * (∑ i, cutWeight r a i * g i x) ^ 2
      ≤ ((Fintype.card ι : ℝ) ^ r⁻¹) ^ 2 * B :=
  sum_weighted_quadForm_le (cutWeight_nonneg ha) (sum_cutWeight_le hr ha hpos)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hSq hB0 hB

/-! ### `∂_u T_{u,D}` along the flow -/

section Flow

variable {W D ℓ : ℝ} {ℓf ηf : ℝ → ℝ} {ℓ' η' u : ℝ}

/-- The logarithmic derivative of the scale `A_u = W ℓ_u η_u`, as it appears in
`hasDerivAt_tailT_flow`. -/
noncomputable def logDerivA (W : ℝ) (ℓf ηf : ℝ → ℝ) (ℓ' η' u : ℝ) : ℝ :=
  W * (ℓ' * ηf u + ℓf u * η') / (W * ℓf u * ηf u)

/-- **`∂_u T_{u,D}(ℓ)`.**  Along a flow `u ↦ (ℓ_u, η_u)` the tail function (5.27) has

`∂_u T_{u,D}(ℓ) = A_u^{-2} e^{-√(ℓ/ℓ_u)} · ( -2 ∂_u log A_u + √(ℓ/ℓ_u) ℓ'_u / (2 ℓ_u) )`,
`A_u = W ℓ_u η_u`.

The `W^{-D}` floor of (5.27) is `u`-independent and therefore contributes nothing here; it
reappears in `neg_deriv_tailT_div_le` through `A_u^{-2} e^{-√(ℓ/ℓ_u)} = T_{u,D}(ℓ) - W^{-D}`. -/
theorem hasDerivAt_tailT_flow (hℓ : 0 < ℓ) (hℓu : 0 < ℓf u) (hW : W ≠ 0) (hηu : ηf u ≠ 0)
    (hℓd : HasDerivAt ℓf ℓ' u) (hηd : HasDerivAt ηf η' u) :
    HasDerivAt (fun v => tailT W (ℓf v) (ηf v) D ℓ)
      (((W * ℓf u * ηf u) ^ 2)⁻¹ * Real.exp (-√(ℓ / ℓf u)) *
        (-2 * logDerivA W ℓf ηf ℓ' η' u + √(ℓ / ℓf u) * ℓ' / (2 * ℓf u))) u := by
  have hA : W * ℓf u * ηf u ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hW hℓu.ne') hηu
  have hAd : HasDerivAt (fun v => W * ℓf v * ηf v) (W * (ℓ' * ηf u + ℓf u * η')) u := by
    have h1 : HasDerivAt (fun v => W * ℓf v) (W * ℓ') u := hℓd.const_mul W
    have h2 := h1.mul hηd
    convert h2 using 1; ring
  have hsq : HasDerivAt (fun v => (W * ℓf v * ηf v) ^ 2)
      (2 * (W * ℓf u * ηf u) * (W * (ℓ' * ηf u + ℓf u * η'))) u := by
    have h := hAd.pow 2
    convert h using 1
    norm_num
  have hsqne : (W * ℓf u * ηf u) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have hinv : HasDerivAt (fun v => ((W * ℓf v * ηf v) ^ 2)⁻¹)
      (-(2 * (W * ℓf u * ηf u) * (W * (ℓ' * ηf u + ℓf u * η')))
        / ((W * ℓf u * ηf u) ^ 2) ^ 2) u := hsq.inv hsqne
  have hratd : HasDerivAt (fun v => ℓ / ℓf v) (-(ℓ * ℓ') / ℓf u ^ 2) u := by
    have h := (hasDerivAt_const u ℓ).div hℓd hℓu.ne'
    convert h using 1; ring
  have hratpos : 0 < ℓ / ℓf u := div_pos hℓ hℓu
  have hsqrtd : HasDerivAt (fun v => √(ℓ / ℓf v))
      (-(ℓ * ℓ') / ℓf u ^ 2 / (2 * √(ℓ / ℓf u))) u := hratd.sqrt hratpos.ne'
  have hexpd : HasDerivAt (fun v => Real.exp (-√(ℓ / ℓf v)))
      (Real.exp (-√(ℓ / ℓf u)) * -(-(ℓ * ℓ') / ℓf u ^ 2 / (2 * √(ℓ / ℓf u)))) u :=
    hsqrtd.neg.exp
  have hprod := (hinv.mul hexpd).add_const (W ^ (-D))
  refine hprod.congr_deriv ?_
  rw [logDerivA]
  set s : ℝ := √(ℓ / ℓf u) with hsdef
  have hs2 : s ^ 2 = ℓ / ℓf u := Real.sq_sqrt hratpos.le
  have hspos : 0 < s := Real.sqrt_pos.2 hratpos
  have hℓeq : ℓ = s ^ 2 * ℓf u := by rw [hs2]; field_simp
  rw [hℓeq]
  field_simp

/-- **The favourable sign.**  The `−(ℓ/ℓ_u)^{1/2}` half of `∂_u T_{u,D}` is not uniformly
bounded in `ℓ`, but as long as the diffusion length `ℓ_u` is non-decreasing (`0 ≤ ℓ'`) it has
a favourable sign and may be dropped:

`-∂_u T_{u,D}(ℓ) ≤ 2 (∂_u log A_u) (T_{u,D}(ℓ) - W^{-D})`,

the right-hand side being `O(∂_u log A_u)` uniformly in `ℓ`. -/
theorem neg_deriv_tailT_le (hℓu : 0 < ℓf u) (hℓ' : 0 ≤ ℓ')
    (hA : 0 < W * ℓf u * ηf u) :
    -(((W * ℓf u * ηf u) ^ 2)⁻¹ * Real.exp (-√(ℓ / ℓf u)) *
        (-2 * logDerivA W ℓf ηf ℓ' η' u + √(ℓ / ℓf u) * ℓ' / (2 * ℓf u)))
      ≤ 2 * logDerivA W ℓf ηf ℓ' η' u * (tailT W (ℓf u) (ηf u) D ℓ - W ^ (-D)) := by
  set E : ℝ := ((W * ℓf u * ηf u) ^ 2)⁻¹ * Real.exp (-√(ℓ / ℓf u)) with hEdef
  set q : ℝ := logDerivA W ℓf ηf ℓ' η' u with hqdef
  set c : ℝ := √(ℓ / ℓf u) * ℓ' / (2 * ℓf u) with hcdef
  have hE : (0 : ℝ) < E := by rw [hEdef]; positivity
  have hc : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
  have hT : tailT W (ℓf u) (ηf u) D ℓ - W ^ (-D) = E := by rw [hEdef, tailT]; ring
  rw [hT]
  have hexp : -(E * (-2 * q + c)) = 2 * q * E - E * c := by ring
  rw [hexp]
  have : 0 ≤ E * c := mul_nonneg hE.le hc
  linarith

/-- The normalized form of `neg_deriv_tailT_le`: `-∂_u log T_{u,D}(ℓ) ≤ 2 (∂_u log A_u)_+`,
**uniformly in `ℓ`** — this is the bound that lets `∂_u J = ∂_u(T^{(L-K)}/T_{u,D})` be
controlled by `J` itself.  The `W^{-D}` floor enters only through `0 ≤ W^{-D}`, which makes
`(T - W^{-D})/T ≤ 1` and so lets the floor region be handled by the same bound. -/
theorem neg_deriv_tailT_div_le (hW : 0 < W) (hℓu : 0 < ℓf u) (hℓ' : 0 ≤ ℓ')
    (hA : 0 < W * ℓf u * ηf u) :
    -(((W * ℓf u * ηf u) ^ 2)⁻¹ * Real.exp (-√(ℓ / ℓf u)) *
        (-2 * logDerivA W ℓf ηf ℓ' η' u + √(ℓ / ℓf u) * ℓ' / (2 * ℓf u)))
        / tailT W (ℓf u) (ηf u) D ℓ
      ≤ 2 * max (logDerivA W ℓf ηf ℓ' η' u) 0 := by
  set q : ℝ := logDerivA W ℓf ηf ℓ' η' u with hqdef
  set T : ℝ := tailT W (ℓf u) (ηf u) D ℓ with hTdef
  have hTpos : 0 < T := by rw [hTdef]; exact tailT_pos hW ℓ
  have hfloor : (0 : ℝ) ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hdiff0 : 0 ≤ T - W ^ (-D) := by
    have := rpow_neg_le_tailT (W := W) (ℓu := ℓf u) (ηu := ηf u) (D := D) ℓ
    rw [hTdef]; linarith
  have h1 := neg_deriv_tailT_le (D := D) (ℓ := ℓ) (η' := η') hℓu hℓ' hA
  rw [div_le_iff₀ hTpos]
  refine h1.trans ?_
  rcases le_or_gt 0 q with hqs | hqs
  · have hq2 : q ≤ max q 0 := le_max_left _ _
    nlinarith
  · have hmax : max q 0 = 0 := max_eq_right hqs.le
    rw [hmax]
    nlinarith

/-- **The `u`-monotonicity of `T_{u,D}` in closed form** (no derivatives).  If the diffusion
length `ℓ_u` is non-decreasing and the scale `A_u = W ℓ_u η_u` is non-increasing — both true
along the flow of Section 2 (`RBM.flowScale_antitoneOn` for the second) — then `T_{u,D}(ℓ)`
is non-decreasing in `u` for every `ℓ ≥ 0`.  This is the sign statement of
`neg_deriv_tailT_le` in the form actually used: `J = T^{(L-K)}/T_{u,D}` only gets smaller. -/
theorem tailT_le_tailT_of_flow {ℓ₁ ℓ₂ η₁ η₂ : ℝ} (hℓ : 0 ≤ ℓ) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : ℓ₁ ≤ ℓ₂)
    (hA₂ : 0 < W * ℓ₂ * η₂) (hAle : W * ℓ₂ * η₂ ≤ W * ℓ₁ * η₁) :
    tailT W ℓ₁ η₁ D ℓ ≤ tailT W ℓ₂ η₂ D ℓ := by
  have hℓ₂0 : 0 < ℓ₂ := lt_of_lt_of_le hℓ₁ hℓ₂
  have hsq : (W * ℓ₂ * η₂) ^ 2 ≤ (W * ℓ₁ * η₁) ^ 2 := by nlinarith
  have hinv : ((W * ℓ₁ * η₁) ^ 2)⁻¹ ≤ ((W * ℓ₂ * η₂) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) hsq
  have hexp : Real.exp (-√(ℓ / ℓ₁)) ≤ Real.exp (-√(ℓ / ℓ₂)) := by
    rw [Real.exp_le_exp]
    have : ℓ / ℓ₂ ≤ ℓ / ℓ₁ := by gcongr
    exact neg_le_neg (Real.sqrt_le_sqrt this)
  have h1 : (0 : ℝ) ≤ Real.exp (-√(ℓ / ℓ₁)) := (Real.exp_pos _).le
  have h2 : (0 : ℝ) ≤ ((W * ℓ₂ * η₂) ^ 2)⁻¹ := by positivity
  unfold tailT
  nlinarith

end Flow

/-! ### The `W^{-D}` floor: absorbing an additive remainder into `T_{u,D}²` -/

section Floor

variable {W ℓu ηu D ℓ : ℝ}

/-- `1 ≤ W^{2D} T_{u,D}(ℓ)²`: the floor `W^{-D}` of (5.27) is exactly what lets an additive
remainder be absorbed into the `T_{u,D}²` normalization, at the cost of `W^{2D}`. -/
theorem one_le_rpow_mul_tailT_sq (hW : 1 ≤ W) :
    1 ≤ W ^ (2 * D) * tailT W ℓu ηu D ℓ ^ 2 := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hfl : (0 : ℝ) < W ^ (-D) := Real.rpow_pos_of_pos hW0 _
  have hle : W ^ (-D) ≤ tailT W ℓu ηu D ℓ := rpow_neg_le_tailT ℓ
  have hsq : (W ^ (-D)) ^ 2 ≤ tailT W ℓu ηu D ℓ ^ 2 := by nlinarith
  have hid : (W ^ (-D)) ^ 2 = W ^ (-(2 * D)) := by
    rw [sq, ← Real.rpow_add hW0]; ring_nf
  have hcancel : W ^ (2 * D) * W ^ (-(2 * D)) = 1 := by
    rw [← Real.rpow_add hW0]; simp
  have hpos : (0 : ℝ) < W ^ (2 * D) := Real.rpow_pos_of_pos hW0 _
  calc (1 : ℝ) = W ^ (2 * D) * W ^ (-(2 * D)) := hcancel.symm
    _ = W ^ (2 * D) * (W ^ (-D)) ^ 2 := by rw [hid]
    _ ≤ W ^ (2 * D) * tailT W ℓu ηu D ℓ ^ 2 := by nlinarith

/-- The inverse-square form of `one_le_rpow_mul_tailT_sq`, as used to normalize an additive
remainder of (5.36) by `T_{u,D}²`. -/
theorem inv_tailT_sq_le (hW : 1 ≤ W) :
    (tailT W ℓu ηu D ℓ ^ 2)⁻¹ ≤ W ^ (2 * D) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hT : 0 < tailT W ℓu ηu D ℓ := tailT_pos hW0 ℓ
  have hTsq : (0 : ℝ) < tailT W ℓu ηu D ℓ ^ 2 := by positivity
  rw [inv_le_iff_one_le_mul₀ hTsq]
  have h := one_le_rpow_mul_tailT_sq (W := W) (ℓu := ℓu) (ηu := ηu) (D := D) (ℓ := ℓ) hW
  linarith

end Floor

/-! ### `∑ S |∂J|²` from (5.36) -/

/-- **The `∂J` half of the cutoff drift, normalized by `T_{u,D}`.**  Let `J` be the smooth
maximum of the ratios `q_i = f_i / T_{u,D}(d_i)`, so that `∂_x J = ∑_i w_i ∂_x f_i /
T_{u,D}(d_i)` by `hasDerivAt_smoothMax`.  If each entry obeys the shape of (5.36) —
`RBM.Lemma57.ee_le` / `ee_le_paper`, i.e. `∑_x S_x (∂_x f_i)² ≤ B T_{u,D}(d_i)² + R` with an
additive remainder `R` (the `W L ρ + 2 W L W^{-D} J³ T²` of `ee_le`) — then

`∑_x S_x (∂_x J)² ≤ (card ι)^{2/r} (B + R W^{2D})`,

which for `r ≍ log (card ι)` is `e² (B + R W^{2D})`.  The `W^{2D}` is the price of the
`W^{-D}` floor of (5.27) and is the reason (5.36) is stated with that floor. -/
theorem sum_cutWeight_quadForm_tailT_le {α : Type*} [Fintype α] {Sq : α → ℝ}
    {W ℓu ηu D : ℝ} {d : ι → ℝ} {G : ι → α → ℝ} {B R : ℝ}
    (hr : 1 < r) (ha : ∀ i, 0 ≤ a i) (hpos : 0 < ∑ i, a i ^ r)
    (hSq : ∀ x, 0 ≤ Sq x) (hW : 1 ≤ W) (hB0 : 0 ≤ B) (hR0 : 0 ≤ R)
    (hEE : ∀ i, ∑ x, Sq x * G i x ^ 2 ≤ B * tailT W ℓu ηu D (d i) ^ 2 + R) :
    ∑ x, Sq x * (∑ i, cutWeight r a i * (G i x / tailT W ℓu ηu D (d i))) ^ 2
      ≤ ((Fintype.card ι : ℝ) ^ r⁻¹) ^ 2 * (B + R * W ^ (2 * D)) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hstep : ∀ i : ι, ∑ x, Sq x * (G i x / tailT W ℓu ηu D (d i)) ^ 2
      ≤ B + R * W ^ (2 * D) := by
    intro i
    have hT : 0 < tailT W ℓu ηu D (d i) := tailT_pos hW0 _
    have hTsq : (0 : ℝ) < tailT W ℓu ηu D (d i) ^ 2 := by positivity
    have hsplit : ∑ x, Sq x * (G i x / tailT W ℓu ηu D (d i)) ^ 2
        = (∑ x, Sq x * G i x ^ 2) / tailT W ℓu ηu D (d i) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun x _ => by rw [div_pow]; ring
    rw [hsplit, div_le_iff₀ hTsq]
    have hinv := inv_tailT_sq_le (ℓu := ℓu) (ηu := ηu) (D := D) (ℓ := d i) hW
    have hRle : R ≤ R * W ^ (2 * D) * tailT W ℓu ηu D (d i) ^ 2 := by
      have := one_le_rpow_mul_tailT_sq (W := W) (ℓu := ℓu) (ηu := ηu) (D := D) (ℓ := d i) hW
      nlinarith
    calc ∑ x, Sq x * G i x ^ 2 ≤ B * tailT W ℓu ηu D (d i) ^ 2 + R := hEE i
      _ ≤ B * tailT W ℓu ηu D (d i) ^ 2 + R * W ^ (2 * D) * tailT W ℓu ηu D (d i) ^ 2 := by
          linarith
      _ = (B + R * W ^ (2 * D)) * tailT W ℓu ηu D (d i) ^ 2 := by ring
  have hB : (0 : ℝ) ≤ B + R * W ^ (2 * D) := by
    have : (0 : ℝ) ≤ W ^ (2 * D) := (Real.rpow_pos_of_pos hW0 _).le
    nlinarith
  exact sum_weighted_quadForm_le (cutWeight_nonneg ha) (sum_cutWeight_le hr ha hpos)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hSq hB hstep

/-- **Repackaging (5.36).**  `RBM.Lemma57.ee_le` and `RBM.Lemma57.ee_le_paper` (T156) conclude

`EE ≤ B₁ T_{u,D}(d)² + (R + B₂ T_{u,D}(d)²)`,

with `R = W L ρ` (the only summand not proportional to `T²`) and
`B₂ = 2 W L W^{-D} J³`.  This puts it in the `B T² + R` shape consumed by
`sum_cutWeight_quadForm_tailT_le`. -/
theorem ee_shape {W ℓu ηu D ℓ : ℝ} {B₁ B₂ R EE : ℝ}
    (h : EE ≤ B₁ * tailT W ℓu ηu D ℓ ^ 2 + (R + B₂ * tailT W ℓu ηu D ℓ ^ 2)) :
    EE ≤ (B₁ + B₂) * tailT W ℓu ηu D ℓ ^ 2 + R := by
  nlinarith [h]

/-! ### The time dependence of the threshold: `Θ̇_u / Θ_u = 4 m / η_u` -/

section Threshold

variable {ηf : ℝ → ℝ} {m u c : ℝ}

/-- **The threshold's own time derivative.**  With `η_u` linear in the flow time,
`∂_u η_u = -m` (the paper's `η_u = (1-u) Im m^{(E)}`, so `m = Im m^{(E)}`), a threshold
`Θ_u = c η_u^{-4}` of the shape used in Step 2 satisfies `Θ̇_u / Θ_u = 4 m / η_u`.  This is
the drift term the original T158 ticket omitted; it is of the same order `η_u^{-1}` as the
other drift terms. -/
theorem hasDerivAt_threshold (hη : HasDerivAt ηf (-m) u) (hne : ηf u ≠ 0) :
    HasDerivAt (fun v => c / ηf v ^ 4) (4 * m / ηf u * (c / ηf u ^ 4)) u := by
  have hpow : HasDerivAt (fun v => ηf v ^ 4) (4 * ηf u ^ 3 * -m) u := by
    have h := hη.pow 4
    convert h using 1
  have hne4 : ηf u ^ 4 ≠ 0 := pow_ne_zero 4 hne
  have hdiv := (hasDerivAt_const u c).div hpow hne4
  refine hdiv.congr_deriv ?_
  field_simp
  ring

/-- **The chain rule for the cutoff weight `χ(J_u / Θ_u)`.**  The second summand is the term
carried by the threshold's time dependence; with `hasDerivAt_threshold` its factor
`Θ̇_u/Θ_u` is `4 m / η_u`. -/
theorem hasDerivAt_cutComp {J Θ : ℝ → ℝ} {J' Θ' : ℝ} {χ : ℝ → ℝ} {dχ : ℝ}
    (hJ : HasDerivAt J J' u) (hΘ : HasDerivAt Θ Θ' u) (hΘ0 : Θ u ≠ 0)
    (hχ : HasDerivAt χ dχ (J u / Θ u)) :
    HasDerivAt (fun v => χ (J v / Θ v))
      (dχ * (J' / Θ u) - dχ * (J u / Θ u) * (Θ' / Θ u)) u := by
  have hq : HasDerivAt (fun v => J v / Θ v) ((J' * Θ u - J u * Θ') / Θ u ^ 2) u :=
    hJ.div hΘ hΘ0
  have h := hχ.comp u hq
  refine h.congr_deriv ?_
  field_simp

/-- The gap bound for the threshold drift term: on the support of `χ'` the ratio `J_u/Θ_u`
lies in `[1, 2]`, so the term `χ'(J_u/Θ_u)·(J_u/Θ_u)·Θ̇_u/Θ_u` of `hasDerivAt_cutComp` is
bounded by `8 C_χ m / η_u` — the same order `η_u^{-1}` as the rest of the drift. -/
theorem abs_threshold_drift_le {dχ Cχ q η : ℝ} (hdχ : |dχ| ≤ Cχ) (hq0 : 0 ≤ q) (hq2 : q ≤ 2)
    (hm : 0 ≤ m) (hη : 0 < η) : |dχ * q * (4 * m / η)| ≤ 8 * Cχ * m / η := by
  have hC : 0 ≤ Cχ := le_trans (abs_nonneg dχ) hdχ
  have h1 : |dχ * q * (4 * m / η)| = |dχ| * q * (4 * m / η) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * m / η)]
  rw [h1]
  have h2 : |dχ| * q * (4 * m / η) ≤ Cχ * 2 * (4 * m / η) := by
    have hfac : (0 : ℝ) ≤ 4 * m / η := by positivity
    have : |dχ| * q ≤ Cχ * 2 := by nlinarith [abs_nonneg dχ]
    exact mul_le_mul_of_nonneg_right this hfac
  calc |dχ| * q * (4 * m / η) ≤ Cχ * 2 * (4 * m / η) := h2
    _ = 8 * Cχ * m / η := by field_simp; ring

end Threshold

/-! ### The second derivative -/

section SecondDeriv
variable {ι : Type*} [Fintype ι] {r : ℝ}

theorem hasDerivAt_deriv_smoothMax {g gd : ℝ → ι → ℝ} {gdd : ι → ℝ} {x : ℝ} (hr : 1 < r)
    (hg : ∀ i, HasDerivAt (fun t => g t i) (gd x i) x)
    (hgd : ∀ i, HasDerivAt (fun t => gd t i) (gdd i) x)
    (hgpos : ∀ i, 0 < g x i) (hgnn : ∀ t i, 0 ≤ g t i) (hP : 0 < ∑ i, g x i ^ r) :
    HasDerivAt (fun t => ∑ i, cutWeight r (g t) i * gd t i)
      ((r - 1) * ((∑ i, g x i ^ (r - 2) * gd x i ^ 2) * (∑ i, g x i ^ r) ^ (r⁻¹ - 1))
        + (∑ i, cutWeight r (g x) i * gdd i)
        - (r - 1) * ((∑ i, g x i ^ (r - 1) * gd x i) ^ 2 * (∑ i, g x i ^ r) ^ (r⁻¹ - 2))) x := by
  have hr0 : (0 : ℝ) < r := by linarith
  -- pieces
  have hpow : ∀ i : ι, HasDerivAt (fun t => g t i ^ (r - 1))
      (gd x i * (r - 1) * g x i ^ (r - 2)) x := by
    intro i
    have h := (hg i).rpow_const (p := r - 1) (Or.inl (hgpos i).ne')
    have e : r - 1 - 1 = r - 2 := by ring
    rwa [e] at h
  have hterm : ∀ i : ι, HasDerivAt (fun t => g t i ^ (r - 1) * gd t i)
      ((r - 1) * (g x i ^ (r - 2) * gd x i ^ 2) + g x i ^ (r - 1) * gdd i) x := by
    intro i
    have h := (hpow i).mul (hgd i)
    refine h.congr_deriv ?_
    ring
  have hN : HasDerivAt (fun t => ∑ i, g t i ^ (r - 1) * gd t i)
      (∑ i, ((r - 1) * (g x i ^ (r - 2) * gd x i ^ 2) + g x i ^ (r - 1) * gdd i)) x := by
    have h := HasDerivAt.sum (u := (Finset.univ : Finset ι))
      (A := fun i t => g t i ^ (r - 1) * gd t i)
      (A' := fun i => (r - 1) * (g x i ^ (r - 2) * gd x i ^ 2) + g x i ^ (r - 1) * gdd i)
      (fun i _ => hterm i)
    have heq : (fun t => ∑ i, g t i ^ (r - 1) * gd t i)
        = ∑ i : ι, fun t => g t i ^ (r - 1) * gd t i := by funext t; simp
    rw [heq]; exact h
  have hPd : HasDerivAt (fun t => ∑ i, g t i ^ r) (r * ∑ i, g x i ^ (r - 1) * gd x i) x := by
    have hin : ∀ i : ι, HasDerivAt (fun t => g t i ^ r) (gd x i * r * g x i ^ (r - 1)) x :=
      fun i => (hg i).rpow_const (Or.inr hr.le)
    have h := HasDerivAt.sum (u := (Finset.univ : Finset ι))
      (A := fun i t => g t i ^ r) (A' := fun i => gd x i * r * g x i ^ (r - 1))
      (fun i _ => hin i)
    have heq : (fun t => ∑ i, g t i ^ r) = ∑ i : ι, fun t => g t i ^ r := by funext t; simp
    rw [heq]
    refine h.congr_deriv ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hQ : HasDerivAt (fun t => (∑ i, g t i ^ r) ^ (r⁻¹ - 1))
      ((r * ∑ i, g x i ^ (r - 1) * gd x i) * (r⁻¹ - 1) * (∑ i, g x i ^ r) ^ (r⁻¹ - 2)) x := by
    have h := hPd.rpow_const (p := r⁻¹ - 1) (Or.inl hP.ne')
    have e : r⁻¹ - 1 - 1 = r⁻¹ - 2 := by ring
    rwa [e] at h
  have hF := hN.mul hQ
  have heqF : (fun t => ∑ i, cutWeight r (g t) i * gd t i)
      = fun t => (∑ i, g t i ^ (r - 1) * gd t i) * (∑ i, g t i ^ r) ^ (r⁻¹ - 1) := by
    funext t
    have hnn : (0 : ℝ) ≤ ∑ j, g t j ^ r := sum_rpow_nonneg (fun j => hgnn t j)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cutWeight]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnn]
    have e : -(1 - r⁻¹) = r⁻¹ - 1 := by ring
    rw [e]; ring
  rw [heqF]
  refine hF.congr_deriv ?_
  have hcut : ∑ i, cutWeight r (g x) i * gdd i
      = (∑ i, g x i ^ (r - 1) * gdd i) * (∑ i, g x i ^ r) ^ (r⁻¹ - 1) := by
    have hnn : (0 : ℝ) ≤ ∑ j, g x j ^ r := sum_rpow_nonneg (fun j => hgnn x j)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [cutWeight]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnn]
    have e : -(1 - r⁻¹) = r⁻¹ - 1 := by ring
    rw [e]; ring
  rw [hcut, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrr : (r * ∑ i, g x i ^ (r - 1) * gd x i) * (r⁻¹ - 1)
      = (1 - r) * ∑ i, g x i ^ (r - 1) * gd x i := by
    field_simp
  rw [hrr]
  ring


/-- **The second derivative costs one factor `r ≍ log N`.**  Dropping the (nonpositive)
`-(r-1) N² P^{1/r-2}` term of `hasDerivAt_deriv_smoothMax` and using `a_i ≥ 1` (true for
`J_{u,D} = T^{(L-K)}/T_{u,D} + 1`, (5.28)), the second derivative of the smooth maximum is
bounded by `(r-1)` times the weight-sum bound applied to the squared first derivatives, plus
the weight-sum bound applied to the second derivatives.  With `r ≍ log N` this is the
`N^{o(1)}` price of replacing `max` by the `r`-norm. -/
theorem smoothMax_second_le {a : ι → ℝ} (hr : 1 < r) (ha1 : ∀ i, 1 ≤ a i)
    (hP : 0 < ∑ i, a i ^ r) {v dd : ι → ℝ} {b c κ : ℝ}
    (hb : ∀ i, |v i| ≤ b) (hb0 : 0 ≤ b) (hc : ∀ i, dd i ≤ c) (hc0 : 0 ≤ c)
    (hκ : ∑ i, cutWeight r a i ≤ κ) :
    (r - 1) * ((∑ i, a i ^ (r - 2) * v i ^ 2) * (∑ i, a i ^ r) ^ (r⁻¹ - 1))
        + (∑ i, cutWeight r a i * dd i)
        - (r - 1) * ((∑ i, a i ^ (r - 1) * v i) ^ 2 * (∑ i, a i ^ r) ^ (r⁻¹ - 2))
      ≤ (r - 1) * (κ * b ^ 2) + κ * c := by
  have hr1 : (0 : ℝ) ≤ r - 1 := by linarith
  have ha0 : ∀ i, (0 : ℝ) ≤ a i := fun i => le_trans zero_le_one (ha1 i)
  have hQ : (0 : ℝ) < (∑ i, a i ^ r) ^ (r⁻¹ - 1) := Real.rpow_pos_of_pos hP _
  have hw : ∀ i : ι, cutWeight r a i = a i ^ (r - 1) * (∑ j, a j ^ r) ^ (r⁻¹ - 1) := by
    intro i
    simp only [cutWeight]
    rw [div_eq_mul_inv, ← Real.rpow_neg (sum_rpow_nonneg ha0)]
    have e : -(1 - r⁻¹) = r⁻¹ - 1 := by ring
    rw [e]
  -- the `(r-1) S₂ Q` term
  have hS2 : (∑ i, a i ^ (r - 2) * v i ^ 2) ≤ (∑ i, a i ^ (r - 1)) * b ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : a i ^ (r - 2) ≤ a i ^ (r - 1) :=
      Real.rpow_le_rpow_of_exponent_le (ha1 i) (by linarith)
    have h2 : v i ^ 2 ≤ b ^ 2 := by
      have := hb i
      nlinarith [abs_nonneg (v i), sq_abs (v i)]
    have h3 : (0 : ℝ) ≤ a i ^ (r - 2) := Real.rpow_nonneg (ha0 i) _
    have h4 : (0 : ℝ) ≤ v i ^ 2 := sq_nonneg _
    nlinarith [Real.rpow_nonneg (ha0 i) (r - 1)]
  have hsw : (∑ i, a i ^ (r - 1)) * (∑ j, a j ^ r) ^ (r⁻¹ - 1) = ∑ i, cutWeight r a i := by
    rw [Finset.sum_mul]
    exact (Finset.sum_congr rfl fun i _ => hw i).symm
  have hfirst : (∑ i, a i ^ (r - 2) * v i ^ 2) * (∑ i, a i ^ r) ^ (r⁻¹ - 1) ≤ κ * b ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hS2 hQ.le
    refine h1.trans ?_
    have : (∑ i, a i ^ (r - 1)) * b ^ 2 * (∑ i, a i ^ r) ^ (r⁻¹ - 1)
        = (∑ i, cutWeight r a i) * b ^ 2 := by rw [← hsw]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hκ (sq_nonneg b)
  -- the `Σ w dd` term
  have hsecond : (∑ i, cutWeight r a i * dd i) ≤ κ * c := by
    have h1 : (∑ i, cutWeight r a i * dd i) ≤ ∑ i, cutWeight r a i * c :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hc i) (cutWeight_nonneg ha0 i)
    rw [← Finset.sum_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hκ hc0)
  -- the dropped term
  have hthird : (0 : ℝ) ≤ (r - 1) * ((∑ i, a i ^ (r - 1) * v i) ^ 2 * (∑ i, a i ^ r) ^ (r⁻¹ - 2)) := by
    have : (0 : ℝ) < (∑ i, a i ^ r) ^ (r⁻¹ - 2) := Real.rpow_pos_of_pos hP _
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hfirst hr1]

end SecondDeriv

end Cutoff
end RBM

