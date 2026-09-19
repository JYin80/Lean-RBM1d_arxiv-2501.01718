/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Kernel
import RBM1D.Propagator.DiffComplex
import RBM1D.Propagator.Edges
import RBM1D.Analysis.StretchedExp

/-!
# Lemmas 7.2 and 7.3: the evolution kernel on decaying tensors

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Lemma 7.2 ((7.2)–(7.12), p. 77–78) and Lemma 7.3 ((7.13)–(7.24), p. 78–80).

Throughout, `U_{s,t,σ} = RBM.Uker L ξ s t` is the evolution kernel (5.17) of
`Hierarchy/Kernel.lean`, whose edge factor is `edgeKer = 1 + Ξ` with
`Ξ = -(s - t) ξ S^(B) Θ^(B)_{tξ}` ((7.18)).  The paper's scales are
`ℓ_u = ℓ̂(u) = min((1-u)^{-1/2}, L)` and `η_u = 1 - u` (see *Deviations*).

## Lemma 7.3

The proof is organised around an abstract kernel `kerOp L X A a = ∑_b ∏ᵢ (δ + Xᵢ)_{aᵢbᵢ} A_b`
(`Uker_eq_kerOp`).  Instead of the paper's induction on `n` via (7.19) we expand
`∏ᵢ (δ + Xᵢ)` over all subsets `S ⊆ [[1, n]]` (`prod_add_eq_sum_ite`, `kerOp_eq_sum_kerTerm`);
this is the same identity, unrolled.  Every term is summed "around an anchor"
(`sum_prod_anchor_le`): one coordinate is summed with the row bound of `Ξ`, all the others are
confined by the decay of `A` to a window of size `N = O(ℓ_s W^τ)` and cost the entry bound of
`Ξ` each.

* `RBM.FastDecay L ℓ δ A`   : **(7.13)**, the `(τ, D)` decay (`ℓ = ℓ_s W^τ`, `δ = W^{-D}`)
* `RBM.SumZeroAt L j A`     : **(7.15)**, the sum-zero property (at any coordinate `j`)
* `RBM.norm_kerOp_fastDecay_le`, `RBM.norm_kerOp_sumZero_le` : the abstract bounds, for any
  edge matrices with given entry / row / Lipschitz bounds
* `RBM.norm_Uker_fastDecay_le`       : **(7.14)**
  `|(U∘A)_a| ≤ C_n K^n (ℓ_t/ℓ_s)(ℓ_sη_s/(ℓ_tη_t))^n ‖A‖ + (η_s/η_t)^n δ`
* `RBM.norm_Uker_fastDecay_le_short` : **(7.16), Case 1** (one short edge `|1 - tξ_{i₀}| ≥ κ`)
  `|(U∘A)_a| ≤ C_{n,κ} K^n (ℓ_sη_s/(ℓ_tη_t))^n ‖A‖ + (η_s/η_t)^n δ`;
  `RBM.norm_Uker_fastDecay_le_of_eq` is the paper's form `σ_k = σ_{k+1}`, `|E| ≤ 2 - κ`
* `RBM.norm_Uker_fastDecay_le_sumZero` : **(7.16), Case 2** (sum-zero, (7.24))
  `|(U∘A)_a| ≤ C_n K^{2n} (ℓ_sη_s/(ℓ_tη_t))^n ‖A‖ + C'_n Lⁿ (η_s/η_t)^n δ`;
  `RBM.norm_Uker_fastDecay_le_sumZero_sigma` is the paper's form with `ξ = m(σᵢ)m(σᵢ₊₁)`

Here `K ≥ 1` plays the role of `W^τ`, so `K^n`, `K^{2n}` are the paper's `W^{C_n τ}`, and the
error terms `(η_s/η_t)^n δ`, `Lⁿ (η_s/η_t)^n δ` are the paper's `W^{-D + C_n}`.

## Lemma 7.2

* `RBM.sum_tail_core_le` : the kernel estimate: with `|K_{xc}| ≤ δ_{xc} + κ e^{-‖x-c‖/ℓ}`,
  `∑_{x,y} |K_{a₁x}||K_{a₂y}| e^{-√(‖x-y‖/ℓ')} ≤ (1 + 16e^{1/2}κℓ
   + C(κℓ)²((ℓ'/ℓ)² + (ℓ'/ℓ)e^{-d/(8ℓ)})) e^{-√(d/ℓ)}`, `d = ‖a₁ - a₂‖ ≥ ℓ`
* `RBM.norm_Uker_tail_le`         : **(7.2)**, explicit, for `‖a₁ - a₂‖ ≥ ℓ_t`
* `RBM.norm_Uker_tail_le_ellStar` : **(7.2)** for `‖a₁ - a₂‖ ≥ ℓ*_t = (log W)^{3/2} ℓ_t`:
  `|(U∘A)_a| ≤ C (1 + 2L e^{-(log W)^{3/2}/8}) T_t(a₁ - a₂) + (η_s/η_t)² W^{-D}`;
  `RBM.norm_Uker_tail_le_sigma` is the same with `ξ = xiOf (mSigma E) ![true, false]`

The paper's proof of (7.2) restricts the sums to `|aᵢ - bᵢ| ≤ ℓ*_t/4` and uses (7.12), at the
price of a factor `e^{C (log W)^{3/4}}`.  We instead split into `16 ℓ_s ≤ ℓ_t` (where either
the `Θ`-factors or the `A`-factor is super-polynomially small, `exp_three_le_short`) and
`ℓ_s ≍ ℓ_t` (plain triangle inequality for `√`); no logarithmic loss appears, only the factor
`1 + (ℓ_t/ℓ_s) e^{-d/(8ℓ_t)}`, which is `≤ 1 + 2L e^{-(log W)^{3/2}/8}` for `d ≥ ℓ*_t`.

## Deviations from the paper

* **Scales.**  `η_u := 1 - u` and `ℓ_u := ℓ̂(u) = min((1-u)^{-1/2}, L)` instead of
  `η_u = Im z_u`, `ℓ_u = min(η_u^{-1/2}, L)`.  They agree up to constants depending only on
  `κ` (`etaT_le`, `le_etaT`, `ellHat_le_ellZ_zt` in `Flow/Scales.lean`), which the paper's
  constants absorb.
* **Explicit constants instead of `≺`.**  All bounds are deterministic inequalities with
  explicit constants (`cKer`, `cKerShort`, `cKerSumZero`, `cKerSumZeroErr`, `cTail`), which is
  stronger than the `≺` / `W^{C_n τ}` / `W^{-D + C_n}` form.  `W^τ` is a free parameter
  `K ≥ 1`, and `O(W^{-D})` in (7.13) is an explicit `δ ≥ 0`.
* **Edge parameters.**  (7.14) holds for arbitrary `|ξᵢ| ≤ 1`, Case 2 for arbitrary
  `0 < |ξᵢ| ≤ 1` (it needs `ξᵢ ≠ 0` and `t > 0` for (2.53)); in particular Case 2 needs no alternation assumption on
  `σ` (the paper reduces to it via Case 1).  Case 1 is stated for any edge with
  `|1 - tξ_{i₀}| ≥ κ`.  The sum-zero property may be at any coordinate `j`.
* **Case 2 power of `W^τ`**: `K^{2n}` rather than `K^n` (the Lipschitz factor `‖bᵢ - b₁‖ ≤ ℓ_s K`
  costs one more `K` per edge); both are `W^{C_n τ}`.
* **Lemma 7.2** is stated for `ξ = (1, 1)`, i.e. `σ = (+, -)` with `|m| = 1`, as in the paper,
  and for `d ≥ ℓ_t` (resp. `d ≥ ℓ*_t` with `W ≥ e`).  Time range `0 ≤ s ≤ t < 1`, `t > 0`.
-/

namespace RBM

open Finset Real
open scoped Matrix.Norms.Operator

/-! ### Scalar expansion of a product of binomials -/

/-- `∏ᵢ (fᵢ + gᵢ) = ∑_S ∏ᵢ (i ∈ S ? fᵢ : gᵢ)`: the subset expansion behind (7.19). -/
theorem prod_add_eq_sum_ite {R : Type*} [CommSemiring R] {n : ℕ} (f g : Fin n → R) :
    ∏ i, (f i + g i) = ∑ S : Finset (Fin n), ∏ i, (if i ∈ S then f i else g i) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_ite]
  congr 1
  · congr 1; ext i; simp
  · congr 1; ext i; simp

theorem card_finset_fin (n : ℕ) : (Finset.univ : Finset (Finset (Fin n))).card = 2 ^ n := by
  simp [Fintype.card_finset]

/-! ### The window indicator -/

section Window

variable (L : ℕ) [NeZero L]

/-- The indicator of the window `‖u‖ < ℓ` on the cycle. -/
noncomputable def winInd (ℓ : ℝ) (u : ZMod L) : ℝ := if (zdist L u : ℝ) < ℓ then 1 else 0

omit [NeZero L] in
theorem winInd_nonneg (ℓ : ℝ) (u : ZMod L) : 0 ≤ winInd L ℓ u := by
  unfold winInd; split_ifs <;> norm_num

omit [NeZero L] in
theorem winInd_le_one (ℓ : ℝ) (u : ZMod L) : winInd L ℓ u ≤ 1 := by
  unfold winInd; split_ifs <;> norm_num

omit [NeZero L] in
theorem winInd_le_exp {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ZMod L) :
    winInd L ℓ u ≤ exp 1 * exp (-(1 / ℓ * (zdist L u : ℝ))) := by
  unfold winInd
  split_ifs with h
  · rw [← exp_add]
    apply one_le_exp
    have : 1 / ℓ * (zdist L u : ℝ) ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hℓ]; exact h.le
    linarith
  · positivity

/-- The number of sites in a window of radius `ℓ` is at most `2e(ℓ + 1)`. -/
theorem sum_winInd_le {ℓ : ℝ} (hℓ : 0 < ℓ) (x : ZMod L) :
    ∑ c : ZMod L, winInd L ℓ (c - x) ≤ 2 * exp 1 * (ℓ + 1) := by
  have hlam : 0 < 1 / ℓ := by positivity
  have h1 : ∑ c : ZMod L, winInd L ℓ (c - x)
      ≤ exp 1 * ∑ c : ZMod L, exp (-(1 / ℓ * (zdist L (c - x) : ℝ))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => winInd_le_exp L hℓ (c - x)
  have h2 := sum_exp_zdist_le L hlam x
  have h3 : 1 / ℓ / (1 + 1 / ℓ) ≤ 1 - exp (-(1 / ℓ)) := one_sub_exp_neg_ge hlam
  have h4 : 2 / (1 - exp (-(1 / ℓ))) ≤ 2 * (ℓ + 1) := by
    have hpos : 0 < 1 / ℓ / (1 + 1 / ℓ) := by positivity
    have e : 1 / ℓ / (1 + 1 / ℓ) = 1 / (ℓ + 1) := by field_simp
    rw [e] at h3 hpos
    rw [div_le_iff₀ (hpos.trans_le h3)]
    have : 1 ≤ (ℓ + 1) * (1 - exp (-(1 / ℓ))) := by
      rw [div_le_iff₀ (by linarith)] at h3; linarith
    linarith
  have he : 0 ≤ exp 1 := (exp_pos 1).le
  calc ∑ c : ZMod L, winInd L ℓ (c - x)
      ≤ exp 1 * ∑ c : ZMod L, exp (-(1 / ℓ * (zdist L (c - x) : ℝ))) := h1
    _ ≤ exp 1 * (2 * (ℓ + 1)) := mul_le_mul_of_nonneg_left (h2.trans h4) he
    _ = 2 * exp 1 * (ℓ + 1) := by ring

end Window

/-! ### Anchored product sums -/

section Anchor

variable (L : ℕ) [NeZero L]

/-- **Summing a product around an anchor.**  If the `i`-th factor depends on `bᵢ` and on the
anchor coordinate `bⱼ`, then fixing `bⱼ = x` factorizes the sum:
`∑_b ∏ᵢ gᵢ(bⱼ, bᵢ) ≤ R ∏_{i ≠ j} Bᵢ` whenever `∑ₓ gⱼ(x, x) ≤ R` and
`∑_c gᵢ(x, c) ≤ Bᵢ` for `i ≠ j`.  This is the mechanism of (7.22)–(7.24). -/
theorem sum_prod_anchor_le {n : ℕ} (g : Fin n → ZMod L → ZMod L → ℝ)
    (hg : ∀ i x c, 0 ≤ g i x c) (j : Fin n) {R : ℝ} (B : Fin n → ℝ)
    (hR : ∑ x : ZMod L, g j x x ≤ R) (hB : ∀ i, i ≠ j → ∀ x, ∑ c : ZMod L, g i x c ≤ B i) :
    ∑ b : LoopArg L n, ∏ i, g i (b j) (b i) ≤ R * ∏ i ∈ univ.erase j, B i := by
  classical
  set h : ZMod L → Fin n → ZMod L → ℝ := fun x i c =>
    if i = j then (if c = x then g i x c else 0) else g i x c with hh
  have h1 : ∀ b : LoopArg L n, ∏ i, g i (b j) (b i) = ∑ x : ZMod L, ∏ i, h x i (b i) := by
    intro b
    rw [Finset.sum_eq_single (b j)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hh]
      split_ifs with hi
      · rfl
      · subst hi; exact absurd rfl ‹¬b i = b i›
      · rfl
    · intro x _ hx
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [hh, ite_true]
      rw [ite_eq_right_iff]
      intro hbx; exact absurd hbx.symm hx
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have hBnn : ∀ i ∈ univ.erase j, 0 ≤ B i := by
    intro i hi
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    exact (Finset.sum_nonneg fun c _ => hg i 0 c).trans (hB i hij 0)
  have h2 : ∀ x : ZMod L, ∑ b : LoopArg L n, ∏ i, h x i (b i)
      ≤ g j x x * ∏ i ∈ univ.erase j, B i := by
    intro x
    rw [sum_prod_pi L (h x), ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hj : ∑ c : ZMod L, h x j c = g j x x := by
      simp only [hh, ite_true]
      rw [Finset.sum_ite_eq' Finset.univ x (g j x)]; simp
    rw [hj]
    refine mul_le_mul_of_nonneg_left ?_ (hg j x x)
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i hi => ?_)
    · exact Finset.sum_nonneg fun c _ => by
        simp only [hh]; split_ifs <;> first | exact hg _ _ _ | exact le_rfl
    · have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hh, hij, ite_false]
      exact hB i hij x
  rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_comm]
  calc ∑ x : ZMod L, ∑ b : LoopArg L n, ∏ i, h x i (b i)
      ≤ ∑ x : ZMod L, g j x x * ∏ i ∈ univ.erase j, B i := Finset.sum_le_sum fun x _ => h2 x
    _ = (∑ x : ZMod L, g j x x) * ∏ i ∈ univ.erase j, B i := by rw [Finset.sum_mul]
    _ ≤ R * ∏ i ∈ univ.erase j, B i :=
        mul_le_mul_of_nonneg_right hR (Finset.prod_nonneg hBnn)

end Anchor

/-! ### The kernel `∏ᵢ (δ + Xᵢ)` and its subset expansion -/

section Kernel

variable (L : ℕ) [NeZero L]

/-- The kernel `(a, b) ↦ ∏ᵢ (δ_{aᵢbᵢ} + (Xᵢ)_{aᵢbᵢ})` acting on a tensor.  With
`Xᵢ = edgeKer - 1 = Ξᵢ` this is `U_{s,t,σ}`, (7.17)–(7.18); see `Uker_eq_kerOp`. -/
noncomputable def kerOp {n : ℕ} (X : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) : ℂ :=
  ∑ b : LoopArg L n,
    (∏ i, ((1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i) + X i (a i) (b i))) * A b

/-- (7.17)–(7.18): `U_{s,t,σ}` is the kernel `∏ᵢ (δ + Ξᵢ)` with `Ξᵢ = edgeKer - 1`. -/
theorem Uker_eq_kerOp {n : ℕ} (ξ : Fin n → ℂ) (s t : ℂ) (A : LoopArg L n → ℂ)
    (a : LoopArg L n) :
    Uker L ξ s t A a = kerOp L (fun i => edgeKer L (ξ i) s t - 1) A a := by
  simp only [Uker, kerOp, Matrix.sub_apply, add_sub_cancel]

/-- The `S`-term of the subset expansion (7.19) of `∏ᵢ (δ + Xᵢ)`:
the factors with `i ∈ S` are `Xᵢ`, the others are `δ`. -/
noncomputable def kerTerm {n : ℕ} (X : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) (S : Finset (Fin n)) : ℂ :=
  ∑ b : LoopArg L n,
    (∏ i, if i ∈ S then X i (a i) (b i) else (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i)) * A b

theorem kerOp_eq_sum_kerTerm {n : ℕ} (X : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) :
    kerOp L X A a = ∑ S : Finset (Fin n), kerTerm L X A a S := by
  unfold kerOp kerTerm
  simp_rw [add_comm ((1 : Matrix (ZMod L) (ZMod L) ℂ) _ _), prod_add_eq_sum_ite, Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_norm_one_apply (x : ZMod L) :
    ∑ c : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x c‖ = 1 := by
  simp [Matrix.one_apply, apply_ite]

theorem kerOp_add {n : ℕ} (X : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (A B : LoopArg L n → ℂ) (a : LoopArg L n) :
    kerOp L X (A + B) a = kerOp L X A a + kerOp L X B a := by
  unfold kerOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.add_apply]; ring

/-- A tensor bounded by `δ` is mapped to one bounded by `δ (1 + r)ⁿ` (Lemma 7.1). -/
theorem norm_kerOp_le_of_bound {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ} {r δ : ℝ}
    (hr : ∀ i x, ∑ c : ZMod L, ‖X i x c‖ ≤ r) {D : LoopArg L n → ℂ} (hδ : 0 ≤ δ)
    (hD : ∀ b, ‖D b‖ ≤ δ) (a : LoopArg L n) :
    ‖kerOp L X D a‖ ≤ δ * (1 + r) ^ n := by
  unfold kerOp
  set g : Fin n → ZMod L → ℝ := fun i c =>
    ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c + X i (a i) c‖ with hg
  have hrow : ∀ i, ∑ c : ZMod L, g i c ≤ 1 + r := by
    intro i
    calc ∑ c : ZMod L, g i c
        ≤ ∑ c : ZMod L, (‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c‖ + ‖X i (a i) c‖) :=
          Finset.sum_le_sum fun c _ => norm_add_le _ _
      _ = 1 + ∑ c : ZMod L, ‖X i (a i) c‖ := by
          rw [Finset.sum_add_distrib, sum_norm_one_apply]
      _ ≤ 1 + r := by linarith [hr i (a i)]
  calc ‖∑ b : LoopArg L n,
        (∏ i, ((1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i) + X i (a i) (b i))) * D b‖
      ≤ ∑ b : LoopArg L n,
        ‖(∏ i, ((1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i) + X i (a i) (b i))) * D b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b : LoopArg L n, (∏ i, g i (b i)) * δ := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hD b) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = δ * ∏ i, ∑ c : ZMod L, g i c := by
        rw [← Finset.sum_mul, sum_prod_pi L g, mul_comm]
    _ ≤ δ * ∏ _i : Fin n, (1 + r) := by
        refine mul_le_mul_of_nonneg_left ?_ hδ
        exact Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun i _ => hrow i)
    _ = δ * (1 + r) ^ n := by simp

end Kernel

/-! ### Fast-decay tensors: (7.13) -/

section FastDecay

variable (L : ℕ)

/-- **(7.13)**: `A` is `(ℓ, δ)`-fast-decaying if `A_a` is at most `δ` as soon as two of the
indices are at distance `≥ ℓ`.  The paper's `(τ, D)` decay at time `s` is `ℓ = ℓ_s W^τ`,
`δ = W^{-D}` (the paper's `O(W^{-D})` is absorbed into `δ`). -/
def FastDecay {n : ℕ} (ℓ δ : ℝ) (A : LoopArg L n → ℂ) : Prop :=
  ∀ a : LoopArg L n, (∃ i j, ℓ ≤ (zdist L (a i - a j) : ℝ)) → ‖A a‖ ≤ δ

/-- **(7.15)**, the sum-zero property, at the coordinate `j`:
`∑_{b : b_j = x} A_b = 0` for every `x`.  The paper's (7.15) is `j = 0` (its `a₁`). -/
def SumZeroAt [NeZero L] {n : ℕ} (j : Fin n) (A : LoopArg L n → ℂ) : Prop :=
  ∀ x : ZMod L, ∑ b : LoopArg L n, (if b j = x then A b else 0) = 0

/-- A tensor supported in the window and bounded by `M`, in the form used by the anchored
sums: `|A_b| ≤ M ∏ᵢ 1(‖bᵢ - bⱼ‖ < ℓ)` for every anchor `j`. -/
def WinBound {n : ℕ} (ℓ M : ℝ) (A : LoopArg L n → ℂ) : Prop :=
  ∀ b : LoopArg L n, ∀ j : Fin n, ‖A b‖ ≤ M * ∏ i, winInd L ℓ (b i - b j)

open Classical in
/-- The part of `A` inside the window `max_{i,j} ‖bᵢ - bⱼ‖ < ℓ` (the paper's `A^T`). -/
noncomputable def winTrunc {n : ℕ} (ℓ : ℝ) (A : LoopArg L n → ℂ) : LoopArg L n → ℂ :=
  fun b => if ∀ i j, (zdist L (b i - b j) : ℝ) < ℓ then A b else 0

theorem winBound_winTrunc {n : ℕ} {ℓ M : ℝ} (hM : 0 ≤ M) {A : LoopArg L n → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ M) : WinBound L ℓ M (winTrunc L ℓ A) := by
  classical
  intro b j
  unfold winTrunc
  split_ifs with h
  · have : ∏ i, winInd L ℓ (b i - b j) = 1 := by
      refine Finset.prod_eq_one fun i _ => ?_
      unfold winInd; rw [ite_eq_left_iff]; intro h'; exact absurd (h i j) h'
    rw [this, mul_one]; exact hA b
  · rw [norm_zero]
    exact mul_nonneg hM (Finset.prod_nonneg fun i _ => winInd_nonneg L ℓ _)

theorem norm_sub_winTrunc_le {n : ℕ} {ℓ δ : ℝ} (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ}
    (hA : FastDecay L ℓ δ A) (b : LoopArg L n) : ‖A b - winTrunc L ℓ A b‖ ≤ δ := by
  classical
  unfold winTrunc
  split_ifs with h
  · rw [sub_self, norm_zero]; exact hδ
  · rw [sub_zero]
    apply hA b
    push Not at h
    exact h

theorem norm_winTrunc_le {n : ℕ} {ℓ M : ℝ} (hM : 0 ≤ M) {A : LoopArg L n → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ M) (b : LoopArg L n) : ‖winTrunc L ℓ A b‖ ≤ M := by
  classical
  unfold winTrunc
  split_ifs
  · exact hA b
  · rw [norm_zero]; exact hM

end FastDecay

/-! ### The terms of the expansion on window-supported tensors: (7.20)–(7.23) -/

section Terms

variable (L : ℕ) [NeZero L]

/-- Norm of a product of `ite`s, times window weights, as a product of real factors. -/
theorem norm_prod_ite_mul {n : ℕ} (P Q : Fin n → ℂ) (S : Finset (Fin n)) (w : Fin n → ℝ)
    (M : ℝ) :
    ‖∏ i, (if i ∈ S then P i else Q i)‖ * (M * ∏ i, w i)
      = M * ∏ i, ((if i ∈ S then ‖P i‖ else ‖Q i‖) * w i) := by
  rw [norm_prod, Finset.prod_mul_distrib]
  simp only [apply_ite norm]
  ring

/-- **The terms with `S ≠ [[1,n]]`** (the induction step (7.20)): some `δ`-factor pins
`b_j = a_j`, every other summation is confined to the window around `a_j`, and each such
summation costs `e · N` (entry bound × window size). -/
theorem norm_kerTerm_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M e N : ℝ} (hM : 0 ≤ M) (hA : WinBound L ℓ M A)
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hN : ∀ x, ∑ c : ZMod L, winInd L ℓ (c - x) ≤ N)
    (a : LoopArg L n) (S : Finset (Fin n)) {j : Fin n} (hj : j ∉ S) :
    ‖kerTerm L X A a S‖ ≤ M * (e * N) ^ S.card := by
  classical
  set g : Fin n → ZMod L → ZMod L → ℝ := fun i x c =>
    (if i ∈ S then ‖X i (a i) c‖ else ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c‖) *
      winInd L ℓ (c - x) with hg
  have hg0 : ∀ i x c, 0 ≤ g i x c := fun i x c =>
    mul_nonneg (by split_ifs <;> exact norm_nonneg _) (winInd_nonneg L ℓ _)
  have hR : ∑ x : ZMod L, g j x x ≤ 1 := by
    simp only [hg, hj, ite_false, sub_self]
    calc ∑ x : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a j) x‖ * winInd L ℓ 0
        ≤ ∑ x : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a j) x‖ :=
          Finset.sum_le_sum fun x _ =>
            mul_le_of_le_one_right (norm_nonneg _) (winInd_le_one L ℓ 0)
      _ = 1 := sum_norm_one_apply L (a j)
  have hB : ∀ i, i ≠ j → ∀ x, ∑ c : ZMod L, g i x c ≤ (if i ∈ S then e * N else 1) := by
    intro i _ x
    by_cases hi : i ∈ S
    · simp only [hg, hi, ite_true]
      calc ∑ c : ZMod L, ‖X i (a i) c‖ * winInd L ℓ (c - x)
          ≤ ∑ c : ZMod L, e * winInd L ℓ (c - x) :=
            Finset.sum_le_sum fun c _ =>
              mul_le_mul_of_nonneg_right (he i (a i) c) (winInd_nonneg L ℓ _)
        _ = e * ∑ c : ZMod L, winInd L ℓ (c - x) := by rw [Finset.mul_sum]
        _ ≤ e * N := mul_le_mul_of_nonneg_left (hN x)
            ((norm_nonneg _).trans (he i (a i) (a i)))
    · simp only [hg, hi, ite_false]
      calc ∑ c : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c‖ * winInd L ℓ (c - x)
          ≤ ∑ c : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) c‖ :=
            Finset.sum_le_sum fun c _ =>
              mul_le_of_le_one_right (norm_nonneg _) (winInd_le_one L ℓ _)
        _ = 1 := sum_norm_one_apply L (a i)
  have hanchor := sum_prod_anchor_le L g hg0 j _ hR hB
  have hprod : ∏ i ∈ univ.erase j, (if i ∈ S then e * N else 1) = (e * N) ^ S.card := by
    rw [Finset.prod_ite_mem, Finset.prod_const]
    congr 1
    congr 1
    ext i
    simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨fun hij => hj (hij ▸ h), h⟩
  rw [hprod, one_mul] at hanchor
  unfold kerTerm
  calc ‖∑ b : LoopArg L n, (∏ i, if i ∈ S then X i (a i) (b i)
          else (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i)) * A b‖
      ≤ ∑ b : LoopArg L n, ‖(∏ i, if i ∈ S then X i (a i) (b i)
          else (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : LoopArg L n, M * ∏ i, g i (b j) (b i) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul]
        calc ‖∏ i, if i ∈ S then X i (a i) (b i)
              else (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i)‖ * ‖A b‖
            ≤ ‖∏ i, if i ∈ S then X i (a i) (b i)
              else (1 : Matrix (ZMod L) (ZMod L) ℂ) (a i) (b i)‖ *
                (M * ∏ i, winInd L ℓ (b i - b j)) :=
              mul_le_mul_of_nonneg_left (hA b j) (norm_nonneg _)
          _ = M * ∏ i, g i (b j) (b i) := by rw [norm_prod_ite_mul]
    _ = M * ∑ b : LoopArg L n, ∏ i, g i (b j) (b i) := by rw [Finset.mul_sum]
    _ ≤ M * (e * N) ^ S.card := mul_le_mul_of_nonneg_left hanchor hM

/-- **The top term `S = [[1,n]]`**, (7.22)–(7.23): anchor at `i₀`, sum `b_{i₀}` freely with the
row bound `r₀` of `X_{i₀}`, and confine the other `n - 1` summations to the window. -/
theorem norm_kerTerm_univ_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M e N r₀ : ℝ} (hM : 0 ≤ M) (hA : WinBound L ℓ M A)
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hN : ∀ x, ∑ c : ZMod L, winInd L ℓ (c - x) ≤ N)
    (i₀ : Fin n) (hr₀ : ∀ x, ∑ c : ZMod L, ‖X i₀ x c‖ ≤ r₀) (a : LoopArg L n) :
    ‖kerTerm L X A a univ‖ ≤ M * (r₀ * (e * N) ^ (n - 1)) := by
  classical
  set g : Fin n → ZMod L → ZMod L → ℝ := fun i x c =>
    ‖X i (a i) c‖ * winInd L ℓ (c - x) with hg
  have hg0 : ∀ i x c, 0 ≤ g i x c := fun i x c =>
    mul_nonneg (norm_nonneg _) (winInd_nonneg L ℓ _)
  have hR : ∑ x : ZMod L, g i₀ x x ≤ r₀ := by
    simp only [hg, sub_self]
    calc ∑ x : ZMod L, ‖X i₀ (a i₀) x‖ * winInd L ℓ 0
        ≤ ∑ x : ZMod L, ‖X i₀ (a i₀) x‖ :=
          Finset.sum_le_sum fun x _ =>
            mul_le_of_le_one_right (norm_nonneg _) (winInd_le_one L ℓ 0)
      _ ≤ r₀ := hr₀ (a i₀)
  have hB : ∀ i, i ≠ i₀ → ∀ x, ∑ c : ZMod L, g i x c ≤ e * N := by
    intro i _ x
    calc ∑ c : ZMod L, ‖X i (a i) c‖ * winInd L ℓ (c - x)
        ≤ ∑ c : ZMod L, e * winInd L ℓ (c - x) :=
          Finset.sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_right (he i (a i) c) (winInd_nonneg L ℓ _)
      _ = e * ∑ c : ZMod L, winInd L ℓ (c - x) := by rw [Finset.mul_sum]
      _ ≤ e * N := mul_le_mul_of_nonneg_left (hN x) ((norm_nonneg _).trans (he i (a i) (a i)))
  have hanchor := sum_prod_anchor_le L g hg0 i₀ (fun _ => e * N) hR hB
  rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin] at hanchor
  unfold kerTerm
  simp only [Finset.mem_univ, ite_true]
  calc ‖∑ b : LoopArg L n, (∏ i, X i (a i) (b i)) * A b‖
      ≤ ∑ b : LoopArg L n, ‖(∏ i, X i (a i) (b i)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : LoopArg L n, M * ∏ i, g i (b i₀) (b i) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        calc (∏ i, ‖X i (a i) (b i)‖) * ‖A b‖
            ≤ (∏ i, ‖X i (a i) (b i)‖) * (M * ∏ i, winInd L ℓ (b i - b i₀)) :=
              mul_le_mul_of_nonneg_left (hA b i₀) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          _ = M * ∏ i, g i (b i₀) (b i) := by
              simp only [hg, Finset.prod_mul_distrib]; ring
    _ = M * ∑ b : LoopArg L n, ∏ i, g i (b i₀) (b i) := by rw [Finset.mul_sum]
    _ ≤ M * (r₀ * (e * N) ^ (n - 1)) := mul_le_mul_of_nonneg_left hanchor hM

end Terms

/-! ### (7.14) and Case 1 of (7.16), abstract form -/

section Main

variable (L : ℕ) [NeZero L]

theorem exists_not_mem_of_ne_univ {n : ℕ} {S : Finset (Fin n)} (hS : S ≠ univ) :
    ∃ j, j ∉ S := by
  by_contra h
  push Not at h
  exact hS (Finset.eq_univ_iff_forall.2 h)

theorem pow_card_le_one_add_pow {n : ℕ} {x : ℝ} (hx : 0 ≤ x) (S : Finset (Fin n)) :
    x ^ S.card ≤ (1 + x) ^ n := by
  calc x ^ S.card ≤ (1 + x) ^ S.card := pow_le_pow_left₀ hx (by linarith) _
    _ ≤ (1 + x) ^ n := by
        refine pow_le_pow_right₀ (by linarith) ?_
        simpa using Finset.card_le_univ S

/-- All the terms `S ≠ [[1,n]]` of the expansion together. -/
theorem norm_sum_kerTerm_erase_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M e N : ℝ} (hM : 0 ≤ M) (hA : WinBound L ℓ M A)
    (he0 : 0 ≤ e) (hN0 : 0 ≤ N)
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hN : ∀ x, ∑ c : ZMod L, winInd L ℓ (c - x) ≤ N)
    (a : LoopArg L n) :
    ‖∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ, kerTerm L X A a S‖
      ≤ 2 ^ n * (M * (1 + e * N) ^ n) := by
  have heN : 0 ≤ e * N := mul_nonneg he0 hN0
  refine (norm_sum_le _ _).trans ?_
  calc ∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ, ‖kerTerm L X A a S‖
      ≤ ∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ, M * (1 + e * N) ^ n := by
        refine Finset.sum_le_sum fun S hS => ?_
        obtain ⟨j, hj⟩ := exists_not_mem_of_ne_univ (Finset.ne_of_mem_erase hS)
        exact (norm_kerTerm_le L hM hA he hN a S hj).trans
          (mul_le_mul_of_nonneg_left (pow_card_le_one_add_pow heN S) hM)
    _ ≤ ∑ S : Finset (Fin n), M * (1 + e * N) ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
    _ = 2 ^ n * (M * (1 + e * N) ^ n) := by
        rw [Finset.sum_const, card_finset_fin, nsmul_eq_mul]; push_cast; ring

/-- The kernel on a window-supported tensor: all the terms of the expansion together. -/
theorem norm_kerOp_winBound_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M e N r₀ : ℝ} (hM : 0 ≤ M) (hA : WinBound L ℓ M A)
    (he0 : 0 ≤ e) (hN0 : 0 ≤ N)
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hN : ∀ x, ∑ c : ZMod L, winInd L ℓ (c - x) ≤ N)
    (i₀ : Fin n) (hr₀ : ∀ x, ∑ c : ZMod L, ‖X i₀ x c‖ ≤ r₀) (a : LoopArg L n) :
    ‖kerOp L X A a‖ ≤ M * (2 ^ n * (1 + e * N) ^ n + r₀ * (e * N) ^ (n - 1)) := by
  rw [kerOp_eq_sum_kerTerm, ← Finset.add_sum_erase _ _ (Finset.mem_univ univ)]
  have h1 := norm_kerTerm_univ_le L hM hA he hN i₀ hr₀ a
  have h2 := norm_sum_kerTerm_erase_le L hM hA he0 hN0 he hN a
  calc ‖kerTerm L X A a univ + ∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ,
        kerTerm L X A a S‖
      ≤ ‖kerTerm L X A a univ‖ + ‖∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ,
        kerTerm L X A a S‖ := norm_add_le _ _
    _ ≤ M * (r₀ * (e * N) ^ (n - 1)) + 2 ^ n * (M * (1 + e * N) ^ n) := add_le_add h1 h2
    _ = M * (2 ^ n * (1 + e * N) ^ n + r₀ * (e * N) ^ (n - 1)) := by ring

theorem kerOp_eq_winTrunc_add {n : ℕ} (X : Fin n → Matrix (ZMod L) (ZMod L) ℂ) (ℓ : ℝ)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) :
    kerOp L X A a = kerOp L X (winTrunc L ℓ A) a
      + kerOp L X (fun b => A b - winTrunc L ℓ A b) a := by
  rw [← kerOp_add]
  congr 1
  funext b
  simp

/-- **(7.14) and Case 1 of (7.16), abstract form.**  Let `Xᵢ` have entries `≤ e` and row
sums `≤ r`, let `X_{i₀}` have row sums `≤ r₀`, and let `A` be `(ℓ, δ)`-fast-decaying with
`‖A‖_max ≤ M`.  Then with `N = 2e(ℓ + 1)` (a bound for the size of a window)
`|(∏(δ + X) ∘ A)_a| ≤ M (2ⁿ (1 + eN)ⁿ + r₀ (eN)^{n-1}) + δ (1 + r)ⁿ`. -/
theorem norm_kerOp_fastDecay_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M δ e r r₀ : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hAM : ∀ b, ‖A b‖ ≤ M) (hA : FastDecay L ℓ δ A) (he0 : 0 ≤ e)
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hr : ∀ i x, ∑ c : ZMod L, ‖X i x c‖ ≤ r)
    (i₀ : Fin n) (hr₀ : ∀ x, ∑ c : ZMod L, ‖X i₀ x c‖ ≤ r₀) (a : LoopArg L n) :
    ‖kerOp L X A a‖ ≤
      M * (2 ^ n * (1 + e * (2 * exp 1 * (ℓ + 1))) ^ n
        + r₀ * (e * (2 * exp 1 * (ℓ + 1))) ^ (n - 1)) + δ * (1 + r) ^ n := by
  rw [kerOp_eq_winTrunc_add L X ℓ A a]
  have hN0 : 0 ≤ 2 * exp 1 * (ℓ + 1) := by positivity
  have h1 := norm_kerOp_winBound_le L hM (winBound_winTrunc L hM hAM) he0 hN0 he
    (sum_winInd_le L hℓ) i₀ hr₀ a
  have h2 := norm_kerOp_le_of_bound L hr hδ (norm_sub_winTrunc_le L hδ hA) a
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end Main

/-! ### Case 2 of (7.16): the sum-zero gain, abstract form -/

section SumZero

variable (L : ℕ) [NeZero L]

theorem card_loopArg (n : ℕ) : (Finset.univ : Finset (LoopArg L n)).card = L ^ n := by
  simp [Finset.card_univ, ZMod.card]

/-- Collecting the anchor coordinate: `∑_b F(b_j) G(b) = ∑_x F(x) ∑_{b : b_j = x} G(b)`. -/
theorem sum_anchor_eq {n : ℕ} (j : Fin n) (F : ZMod L → ℂ) (G : LoopArg L n → ℂ) :
    ∑ b : LoopArg L n, F (b j) * G b
      = ∑ x : ZMod L, F x * ∑ b : LoopArg L n, (if b j = x then G b else 0) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (b j)]
  · simp
  · intro x _ hx
    rw [ite_eq_right_iff.2 fun h => absurd h.symm hx, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The defect of the sum-zero property after truncation to the window is `≤ Lⁿ δ`. -/
theorem norm_sum_winTrunc_anchor_le {n : ℕ} {ℓ δ : ℝ} (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ}
    (hA : FastDecay L ℓ δ A) {j : Fin n} (hz : SumZeroAt L j A) (x : ZMod L) :
    ‖∑ b : LoopArg L n, (if b j = x then winTrunc L ℓ A b else 0)‖ ≤ (L : ℝ) ^ n * δ := by
  classical
  have h0 := hz x
  have e : ∑ b : LoopArg L n, (if b j = x then winTrunc L ℓ A b else 0)
      = -∑ b : LoopArg L n, (if b j = x then (A b - winTrunc L ℓ A b) else 0) := by
    rw [← Finset.sum_neg_distrib]
    have : ∑ b : LoopArg L n, (if b j = x then winTrunc L ℓ A b else 0)
        = ∑ b : LoopArg L n, ((if b j = x then A b else 0)
            + -(if b j = x then (A b - winTrunc L ℓ A b) else 0)) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> ring
    rw [this, Finset.sum_add_distrib, h0, zero_add]
  rw [e, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b : LoopArg L n, ‖if b j = x then (A b - winTrunc L ℓ A b) else 0‖
      ≤ ∑ _b : LoopArg L n, δ := Finset.sum_le_sum fun b _ => by
        split_ifs
        · exact norm_sub_winTrunc_le L hδ hA b
        · rw [norm_zero]; exact hδ
    _ = (L : ℝ) ^ n * δ := by rw [Finset.sum_const, card_loopArg, nsmul_eq_mul]; push_cast; ring

/-- The leading term of Case 2: after freezing every edge at the anchor, `∏ᵢ Ξ⁰ᵢ` does not
depend on the other coordinates and the sum-zero property kills it, up to the truncation
defect. -/
theorem norm_lead_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ} {ℓ δ e r : ℝ}
    (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ} (hA : FastDecay L ℓ δ A) {j : Fin n}
    (hz : SumZeroAt L j A) (he : ∀ i x c, ‖X i x c‖ ≤ e)
    (hr : ∀ i x, ∑ c : ZMod L, ‖X i x c‖ ≤ r) (a : LoopArg L n) :
    ‖∑ b : LoopArg L n, (∏ i, X i (a i) (b j)) * winTrunc L ℓ A b‖
      ≤ r * e ^ (n - 1) * ((L : ℝ) ^ n * δ) := by
  classical
  have he0 : 0 ≤ e := (norm_nonneg _).trans (he j (a j) (a j))
  rw [sum_anchor_eq L j (fun x => ∏ i, X i (a i) x)]
  refine (norm_sum_le _ _).trans ?_
  have hpt : ∀ x : ZMod L, ‖(∏ i, X i (a i) x) *
      ∑ b : LoopArg L n, (if b j = x then winTrunc L ℓ A b else 0)‖
      ≤ ‖X j (a j) x‖ * (e ^ (n - 1) * ((L : ℝ) ^ n * δ)) := by
    intro x
    rw [norm_mul, norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul ?_ (norm_sum_winTrunc_anchor_le L hδ hA hz x) (norm_nonneg _)
      (pow_nonneg he0 _)
    calc ∏ i ∈ univ.erase j, ‖X i (a i) x‖ ≤ ∏ _i ∈ univ.erase j, e :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => he i (a i) x)
      _ = e ^ (n - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, Fintype.card_fin]
  calc ∑ x : ZMod L, ‖(∏ i, X i (a i) x) *
        ∑ b : LoopArg L n, (if b j = x then winTrunc L ℓ A b else 0)‖
      ≤ ∑ x : ZMod L, ‖X j (a j) x‖ * (e ^ (n - 1) * ((L : ℝ) ^ n * δ)) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = (∑ x : ZMod L, ‖X j (a j) x‖) * (e ^ (n - 1) * ((L : ℝ) ^ n * δ)) := by
        rw [Finset.sum_mul]
    _ ≤ r * (e ^ (n - 1) * ((L : ℝ) ^ n * δ)) :=
        mul_le_mul_of_nonneg_right (hr j (a j)) (by positivity)
    _ = r * e ^ (n - 1) * ((L : ℝ) ^ n * δ) := by ring

/-- One term `T ≠ ∅` of the expansion of `∏ᵢ (Ξ⁰ᵢ + Ξ*ᵢ)` in Case 2, (7.24): each `Ξ*ᵢ`
(`i ∈ T`) is `≤ e' ‖bᵢ - b_j‖ ≤ e' ℓ` on the window, which is where the extra `ℓ_s/ℓ_t`
comes from. -/
theorem norm_remTerm_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M e e' N r : ℝ} (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M)
    (hA : WinBound L ℓ M A) (he0 : 0 ≤ e) (he'0 : 0 ≤ e') (hN0 : 0 ≤ N) (hr0 : 0 ≤ r)
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hr : ∀ i x, ∑ c : ZMod L, ‖X i x c‖ ≤ r)
    (hLip : ∀ i y c c', ‖X i y c - X i y c'‖ ≤ e' * zdist L (c - c'))
    (hN : ∀ x, ∑ c : ZMod L, winInd L ℓ (c - x) ≤ N) (j : Fin n) (a : LoopArg L n)
    (T : Finset (Fin n)) (hT : T ≠ ∅) :
    ‖∑ b : LoopArg L n, (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j)
        else X i (a i) (b j)) * A b‖
      ≤ M * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2)) := by
  classical
  set Y : ℝ := e' * ℓ * N with hY
  set Z : ℝ := e * N with hZ
  have hY0 : 0 ≤ Y := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  set g : Fin n → ZMod L → ZMod L → ℝ := fun i x c =>
    (if i ∈ T then ‖X i (a i) c - X i (a i) x‖ else ‖X i (a i) x‖) * winInd L ℓ (c - x)
    with hg
  have hg0 : ∀ i x c, 0 ≤ g i x c := fun i x c =>
    mul_nonneg (by split_ifs <;> exact norm_nonneg _) (winInd_nonneg L ℓ _)
  set R : ℝ := if j ∈ T then 0 else r with hRdef
  have hR : ∑ x : ZMod L, g j x x ≤ R := by
    by_cases hj : j ∈ T
    · simp [hg, hj, hRdef]
    · simp only [hg, hj, ite_false, hRdef, sub_self]
      calc ∑ x : ZMod L, ‖X j (a j) x‖ * winInd L ℓ 0
          ≤ ∑ x : ZMod L, ‖X j (a j) x‖ :=
            Finset.sum_le_sum fun x _ =>
              mul_le_of_le_one_right (norm_nonneg _) (winInd_le_one L ℓ 0)
        _ ≤ r := hr j (a j)
  have hB : ∀ i, i ≠ j → ∀ x, ∑ c : ZMod L, g i x c ≤ (if i ∈ T then Y else Z) := by
    intro i _ x
    by_cases hi : i ∈ T
    · simp only [hg, hi, ite_true]
      have hpt : ∀ c : ZMod L, ‖X i (a i) c - X i (a i) x‖ * winInd L ℓ (c - x)
          ≤ e' * ℓ * winInd L ℓ (c - x) := by
        intro c
        unfold winInd
        split_ifs with hc
        · rw [mul_one, mul_one]
          exact (hLip i (a i) c x).trans (mul_le_mul_of_nonneg_left hc.le he'0)
        · simp
      calc ∑ c : ZMod L, ‖X i (a i) c - X i (a i) x‖ * winInd L ℓ (c - x)
          ≤ ∑ c : ZMod L, e' * ℓ * winInd L ℓ (c - x) := Finset.sum_le_sum fun c _ => hpt c
        _ = e' * ℓ * ∑ c : ZMod L, winInd L ℓ (c - x) := by rw [Finset.mul_sum]
        _ ≤ Y := mul_le_mul_of_nonneg_left (hN x) (by positivity)
    · simp only [hg, hi, ite_false]
      calc ∑ c : ZMod L, ‖X i (a i) x‖ * winInd L ℓ (c - x)
          ≤ ∑ c : ZMod L, e * winInd L ℓ (c - x) :=
            Finset.sum_le_sum fun c _ =>
              mul_le_mul_of_nonneg_right (he i (a i) x) (winInd_nonneg L ℓ _)
        _ = e * ∑ c : ZMod L, winInd L ℓ (c - x) := by rw [Finset.mul_sum]
        _ ≤ Z := mul_le_mul_of_nonneg_left (hN x) he0
  have hanchor := sum_prod_anchor_le L g hg0 j _ hR hB
  have hfin : R * ∏ i ∈ univ.erase j, (if i ∈ T then Y else Z) ≤ r * Y * (Z + Y) ^ (n - 2) := by
    by_cases hj : j ∈ T
    · simp only [hRdef, hj, ite_true, zero_mul]; positivity
    · simp only [hRdef, hj, ite_false]
      obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hT
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      have hkmem : k ∈ univ.erase j := Finset.mem_erase.2 ⟨hkj, Finset.mem_univ _⟩
      have hrest : ∏ i ∈ (univ.erase j).erase k, (if i ∈ T then Y else Z)
          ≤ (Z + Y) ^ (n - 2) := by
        calc ∏ i ∈ (univ.erase j).erase k, (if i ∈ T then Y else Z)
            ≤ ∏ _i ∈ (univ.erase j).erase k, (Z + Y) :=
              Finset.prod_le_prod₀ (fun i _ => by split_ifs <;> assumption)
                (fun i _ => by split_ifs <;> linarith)
          _ = (Z + Y) ^ (n - 2) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem hkmem,
                Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                Fintype.card_fin, Nat.sub_sub]
      rw [← Finset.mul_prod_erase _ _ hkmem, ite_eq_left hk]
      calc r * (Y * ∏ i ∈ (univ.erase j).erase k, (if i ∈ T then Y else Z))
          ≤ r * (Y * (Z + Y) ^ (n - 2)) := by gcongr
        _ = r * Y * (Z + Y) ^ (n - 2) := by ring
  calc ‖∑ b : LoopArg L n, (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j)
        else X i (a i) (b j)) * A b‖
      ≤ ∑ b : LoopArg L n, ‖(∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j)
        else X i (a i) (b j)) * A b‖ := norm_sum_le _ _
    _ ≤ ∑ b : LoopArg L n, M * ∏ i, g i (b j) (b i) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul]
        calc ‖∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j)‖
              * ‖A b‖
            ≤ ‖∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j)‖
                * (M * ∏ i, winInd L ℓ (b i - b j)) :=
              mul_le_mul_of_nonneg_left (hA b j) (norm_nonneg _)
          _ = M * ∏ i, g i (b j) (b i) := by rw [norm_prod_ite_mul]
    _ = M * ∑ b : LoopArg L n, ∏ i, g i (b j) (b i) := by rw [Finset.mul_sum]
    _ ≤ M * (r * Y * (Z + Y) ^ (n - 2)) :=
        mul_le_mul_of_nonneg_left (hanchor.trans hfin) hM

/-- Splitting the top term at the anchor: `Ξᵢ(aᵢ, bᵢ) = Ξᵢ(aᵢ, b_j) + [Ξᵢ(aᵢ, bᵢ) - Ξᵢ(aᵢ, b_j)]`,
i.e. `Ξᵢ = Ξ⁰ᵢ + Ξ*ᵢ` in the notation of the proof of Case 2. -/
theorem kerTerm_univ_eq {n : ℕ} (X : Fin n → Matrix (ZMod L) (ZMod L) ℂ)
    (A : LoopArg L n → ℂ) (a : LoopArg L n) (j : Fin n) :
    kerTerm L X A a univ = ∑ b : LoopArg L n, (∏ i, X i (a i) (b j)) * A b
      + ∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅, ∑ b : LoopArg L n,
          (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j)) * A b := by
  classical
  have hexp : ∀ b : LoopArg L n, ∏ i, X i (a i) (b i) = ∏ i, X i (a i) (b j)
      + ∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅,
          ∏ i, (if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j)) := by
    intro b
    have h := prod_add_eq_sum_ite (fun i => X i (a i) (b i) - X i (a i) (b j))
      (fun i => X i (a i) (b j))
    simp only [sub_add_cancel] at h
    rw [h, ← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]
    simp
  unfold kerTerm
  simp only [Finset.mem_univ, ite_true]
  rw [Finset.sum_congr rfl fun b _ => by rw [hexp b]]
  simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (s := (univ : Finset (LoopArg L n)))]

/-- **Case 2 of (7.16), abstract form.**  If moreover `Xᵢ` is `e'`-Lipschitz in its second
index and `A` has the sum-zero property at `j`, the top term gains the factor
`e' ℓ / e`: with `N = 2e(ℓ + 1)`,
`|(∏(δ + X) ∘ A)_a| ≤ M (2ⁿ(1 + eN)ⁿ + 2ⁿ r (e'ℓN)(eN + e'ℓN)^{n-2})
  + δ ((1 + r)ⁿ + r e^{n-1} Lⁿ)`. -/
theorem norm_kerOp_sumZero_le {n : ℕ} {X : Fin n → Matrix (ZMod L) (ZMod L) ℂ}
    {A : LoopArg L n → ℂ} {ℓ M δ e e' r : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hAM : ∀ b, ‖A b‖ ≤ M) (hA : FastDecay L ℓ δ A) {j : Fin n} (hz : SumZeroAt L j A)
    (he0 : 0 ≤ e) (he'0 : 0 ≤ e')
    (he : ∀ i x c, ‖X i x c‖ ≤ e) (hr : ∀ i x, ∑ c : ZMod L, ‖X i x c‖ ≤ r)
    (hLip : ∀ i y c c', ‖X i y c - X i y c'‖ ≤ e' * zdist L (c - c')) (a : LoopArg L n) :
    ‖kerOp L X A a‖ ≤
      M * (2 ^ n * (1 + e * (2 * exp 1 * (ℓ + 1))) ^ n
        + 2 ^ n * (r * (e' * ℓ * (2 * exp 1 * (ℓ + 1)))
          * (e * (2 * exp 1 * (ℓ + 1)) + e' * ℓ * (2 * exp 1 * (ℓ + 1))) ^ (n - 2)))
      + δ * ((1 + r) ^ n + r * e ^ (n - 1) * (L : ℝ) ^ n) := by
  classical
  set N : ℝ := 2 * exp 1 * (ℓ + 1) with hNdef
  have hN0 : 0 ≤ N := by positivity
  have hN := sum_winInd_le L hℓ
  have hr0 : 0 ≤ r := (Finset.sum_nonneg fun c _ => norm_nonneg _).trans (hr j 0)
  have hWB := winBound_winTrunc L (ℓ := ℓ) hM hAM
  rw [kerOp_eq_winTrunc_add L X ℓ A a]
  have hD := norm_kerOp_le_of_bound L hr hδ (norm_sub_winTrunc_le L hδ hA) a
  rw [kerOp_eq_sum_kerTerm, ← Finset.add_sum_erase _ _ (Finset.mem_univ univ),
    kerTerm_univ_eq L X _ a j]
  have h1 := norm_lead_le L hδ hA hz he hr a (ℓ := ℓ)
  have h2 : ‖∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅, ∑ b : LoopArg L n,
        (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j))
          * winTrunc L ℓ A b‖
      ≤ 2 ^ n * (M * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅, ‖∑ b : LoopArg L n,
          (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j))
            * winTrunc L ℓ A b‖
        ≤ ∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅,
            M * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2)) :=
          Finset.sum_le_sum fun T hT =>
            norm_remTerm_le L hℓ.le hM hWB he0 he'0 hN0 hr0 he hr hLip hN j a T
              (Finset.ne_of_mem_erase hT)
      _ ≤ ∑ T : Finset (Fin n), M * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => by positivity)
      _ = 2 ^ n * (M * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2))) := by
          rw [Finset.sum_const, card_finset_fin, nsmul_eq_mul]; push_cast; ring
  have h3 := norm_sum_kerTerm_erase_le L hM hWB he0 hN0 he hN a
  calc ‖(∑ b : LoopArg L n, (∏ i, X i (a i) (b j)) * winTrunc L ℓ A b
        + ∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅, ∑ b : LoopArg L n,
          (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j))
            * winTrunc L ℓ A b
        + ∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ, kerTerm L X (winTrunc L ℓ A) a S)
        + kerOp L X (fun b => A b - winTrunc L ℓ A b) a‖
      ≤ (‖∑ b : LoopArg L n, (∏ i, X i (a i) (b j)) * winTrunc L ℓ A b‖
        + ‖∑ T ∈ (univ : Finset (Finset (Fin n))).erase ∅, ∑ b : LoopArg L n,
          (∏ i, if i ∈ T then X i (a i) (b i) - X i (a i) (b j) else X i (a i) (b j))
            * winTrunc L ℓ A b‖
        + ‖∑ S ∈ (univ : Finset (Finset (Fin n))).erase univ,
            kerTerm L X (winTrunc L ℓ A) a S‖)
        + ‖kerOp L X (fun b => A b - winTrunc L ℓ A b) a‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (r * e ^ (n - 1) * ((L : ℝ) ^ n * δ)
        + 2 ^ n * (M * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2)))
        + 2 ^ n * (M * (1 + e * N) ^ n)) + δ * (1 + r) ^ n := by gcongr
    _ = M * (2 ^ n * (1 + e * N) ^ n
        + 2 ^ n * (r * (e' * ℓ * N) * (e * N + e' * ℓ * N) ^ (n - 2)))
        + δ * ((1 + r) ^ n + r * e ^ (n - 1) * (L : ℝ) ^ n) := by ring

end SumZero

/-! ### Scales: `ℓ_u = ℓ̂(u)`, `η_u = 1 - u` -/

section Scales

theorem mul_min_inv_sqrt_mono {x y l : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hl : 0 ≤ l) :
    x * min (1 / √x) l ≤ y * min (1 / √y) l := by
  have hy : 0 < y := hx.trans_le hxy
  rw [mul_min_of_nonneg _ _ hx.le, mul_min_of_nonneg _ _ hy.le, mul_one_div, mul_one_div,
    Real.div_sqrt, Real.div_sqrt]
  exact min_le_min (Real.sqrt_le_sqrt hxy) (mul_le_mul_of_nonneg_right hxy hl)

theorem sqrt_mul_min_inv_sqrt_mono {x y l : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hl : 0 ≤ l) :
    √x * min (1 / √x) l ≤ √y * min (1 / √y) l := by
  have hy : 0 < y := hx.trans_le hxy
  have hsx : 0 < √x := Real.sqrt_pos.2 hx
  have hsy : 0 < √y := Real.sqrt_pos.2 hy
  rw [mul_min_of_nonneg _ _ hsx.le, mul_min_of_nonneg _ _ hsy.le, mul_one_div_cancel hsx.ne',
    mul_one_div_cancel hsy.ne']
  exact min_le_min le_rfl (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxy) hl)

variable (L : ℕ)

/-- `x ↦ x ℓ̂` is monotone in `x = |1 - ζ|`: this is what lets the real time `t` control every
spectral parameter `tξ` with `|ξ| ≤ 1`. -/
theorem one_sub_mul_ellHat_le {t : ℝ} {ζ : ℂ} (ht1 : t < 1) (h : 1 - t ≤ ‖1 - ζ‖) :
    (1 - t) * ellHat L (t : ℂ) ≤ ‖1 - ζ‖ * ellHat L ζ := by
  rw [ellHat_ofReal L ht1, ellHat]
  exact mul_min_inv_sqrt_mono (by linarith) h (Nat.cast_nonneg L)

theorem sqrt_one_sub_mul_ellHat_le {t : ℝ} {ζ : ℂ} (ht1 : t < 1) (h : 1 - t ≤ ‖1 - ζ‖) :
    √(1 - t) * ellHat L (t : ℂ) ≤ √‖1 - ζ‖ * ellHat L ζ := by
  rw [ellHat_ofReal L ht1, ellHat]
  exact sqrt_mul_min_inv_sqrt_mono (by linarith) h (Nat.cast_nonneg L)

theorem ellHat_real_le_inv_sqrt {t : ℝ} (ht1 : t < 1) : ellHat L (t : ℂ) ≤ 1 / √(1 - t) := by
  rw [ellHat_ofReal L ht1]; exact min_le_left _ _

theorem ellHat_real_mono {s t : ℝ} (hst : s ≤ t) (ht1 : t < 1) :
    ellHat L (s : ℂ) ≤ ellHat L (t : ℂ) := by
  rw [ellHat_ofReal L (hst.trans_lt ht1), ellHat_ofReal L ht1]
  refine min_le_min ?_ le_rfl
  have h1 : 0 < √(1 - t) := Real.sqrt_pos.2 (by linarith)
  exact one_div_le_one_div_of_le h1 (Real.sqrt_le_sqrt (by linarith))

theorem norm_one_sub_ofReal {s : ℝ} (hs : s ≤ 1) : ‖1 - (s : ℂ)‖ = 1 - s := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

/-- `ℓ_t η_t ≤ ℓ_s η_s` for `s ≤ t`, i.e. the ratio `ℓ_s η_s / (ℓ_t η_t)` of (7.14) is `≥ 1`. -/
theorem one_sub_mul_ellHat_anti {s t : ℝ} (hst : s ≤ t) (ht1 : t < 1) :
    (1 - t) * ellHat L (t : ℂ) ≤ (1 - s) * ellHat L (s : ℂ) := by
  have h := one_sub_mul_ellHat_le L ht1 (ζ := (s : ℂ))
    (by rw [norm_one_sub_ofReal (by linarith)]; linarith)
  rwa [norm_one_sub_ofReal (by linarith)] at h

variable [NeZero L]

theorem half_le_ellHat_real (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    1 / 2 ≤ ellHat L (t : ℂ) :=
  half_le_ellHat L hL (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1)

end Scales

/-! ### Telescoping along the cycle -/

section Telescope

variable (L : ℕ) [NeZero L]

omit [NeZero L] in
theorem norm_sub_add_nat_le (f : ZMod L → ℂ) {g : ℝ} (hf : ∀ y, ‖f y - f (y + 1)‖ ≤ g) :
    ∀ k : ℕ, ∀ y, ‖f y - f (y + k)‖ ≤ k * g := by
  intro k
  induction k with
  | zero => intro y; simp
  | succ k ih =>
    intro y
    have e : f y - f (y + ((k + 1 : ℕ) : ZMod L))
        = (f y - f (y + k)) + (f (y + k) - f (y + k + 1)) := by
      push_cast; rw [add_assoc]; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    push_cast
    linarith [ih y, hf (y + k)]

/-- A function on the cycle whose nearest-neighbour differences are `≤ g` is
`g`-Lipschitz for the graph distance. -/
theorem norm_sub_le_zdist_mul (f : ZMod L → ℂ) {g : ℝ} (hf : ∀ y, ‖f y - f (y + 1)‖ ≤ g)
    (c c' : ZMod L) : ‖f c - f c'‖ ≤ g * zdist L (c - c') := by
  have hg : 0 ≤ g := (norm_nonneg _).trans (hf 0)
  have h1 : ‖f c - f c'‖ ≤ (c' - c).val * g := by
    have := norm_sub_add_nat_le L f hf (c' - c).val c
    rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
  have h2 : ‖f c - f c'‖ ≤ (c - c').val * g := by
    have := norm_sub_add_nat_le L f hf (c - c').val c'
    rw [ZMod.natCast_zmod_val, add_sub_cancel, norm_sub_rev] at this
    exact this
  by_cases hcc : c = c'
  · subst hcc; simp
  · have hne : c - c' ≠ 0 := sub_ne_zero.2 hcc
    have hval : (c' - c).val = L - (c - c').val := by
      rw [← neg_sub, ZMod.neg_val, ite_eq_right hne]
    have hlt : (c - c').val < L := ZMod.val_lt _
    unfold zdist
    rcases min_choice (c - c').val (L - (c - c').val) with h | h
    · rw [h, mul_comm]; exact h2
    · rw [h, mul_comm, ← hval]; exact h1

end Telescope

/-! ### Edge bounds: (2.52), (2.53) and `S^(B)` -/

section EdgeBounds

variable (L : ℕ) [NeZero L]

theorem norm_ofReal_mul_lt_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    ‖(t : ℂ) * ξ‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  nlinarith [norm_nonneg ξ]

theorem one_sub_le_norm_one_sub_mul {t : ℝ} (ht0 : 0 ≤ t) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    1 - t ≤ ‖1 - (t : ℂ) * ξ‖ := by
  have h := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * ξ)
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at h
  nlinarith [norm_nonneg ξ]

theorem norm_sub_ofReal_mul_le {s t : ℝ} (hst : s ≤ t) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) :
    ‖((s : ℂ) - t) * ξ‖ ≤ t - s := by
  rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith)]
  nlinarith [norm_nonneg ξ]

/-- (2.52) at `tξ`, `|ξ| ≤ 1`, in terms of the real scales: `|Θ_{tξ}| ≤ C/(η_t ℓ_t)`. -/
theorem norm_Theta_mul_apply_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {ξ : ℂ}
    (hξ : ‖ξ‖ ≤ 1) (x y : ZMod L) :
    ‖Theta L ((t : ℂ) * ξ) x y‖ ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) := by
  have hζ := norm_ofReal_mul_lt_one ht0 ht1 hξ
  have h := norm_Theta_apply_le_complex hL hζ x y
  have hden : 0 < (1 - t) * ellHat L (t : ℂ) :=
    mul_pos (by linarith) (lt_of_lt_of_le (by norm_num) (half_le_ellHat_real L hL ht0 ht1))
  have hmono := one_sub_mul_ellHat_le L ht1 (one_sub_le_norm_one_sub_mul ht0 hξ)
  have hexp : exp (-(cZero * zdist L (x - y) / ellHat L ((t : ℂ) * ξ))) ≤ 1 := by
    rw [exp_le_one_iff]
    have : 0 ≤ cZero * zdist L (x - y) / ellHat L ((t : ℂ) * ξ) := by
      have := half_le_ellHat L hL hζ
      have := cZero_pos
      positivity
    linarith
  refine h.trans ?_
  calc cTwo52 * exp (-(cZero * zdist L (x - y) / ellHat L ((t : ℂ) * ξ)))
        / (‖1 - (t : ℂ) * ξ‖ * ellHat L ((t : ℂ) * ξ))
      ≤ cTwo52 / (‖1 - (t : ℂ) * ξ‖ * ellHat L ((t : ℂ) * ξ)) := by
        refine div_le_div_of_nonneg_right (mul_le_of_le_one_right cTwo52_pos.le hexp) ?_
        exact mul_nonneg (norm_nonneg _)
          ((by norm_num : (0 : ℝ) ≤ 1 / 2).trans (half_le_ellHat L hL hζ))
    _ ≤ cTwo52 / ((1 - t) * ellHat L (t : ℂ)) :=
        div_le_div_of_nonneg_left cTwo52_pos.le hden hmono

/-- (2.53) at `tξ`, `|ξ| ≤ 1`, `ξ ≠ 0`, `t > 0`, turned into a Lipschitz bound in the
second index: `|Θ_{x,c} - Θ_{x,c'}| ≤ 144 ‖c - c'‖ / (ℓ_t η_t^{1/2})`. -/
theorem norm_Theta_mul_sub_le (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {ξ : ℂ}
    (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ ≤ 1) (x c c' : ZMod L) :
    ‖Theta L ((t : ℂ) * ξ) x c - Theta L ((t : ℂ) * ξ) x c'‖
      ≤ 144 / (ellHat L (t : ℂ) * √(1 - t)) * zdist L (c - c') := by
  have hζ := norm_ofReal_mul_lt_one ht0.le ht1 hξ
  have hζ0 : (t : ℂ) * ξ ≠ 0 := mul_ne_zero (by exact_mod_cast ht0.ne') hξ0
  have hden : 0 < ellHat L (t : ℂ) * √(1 - t) :=
    mul_pos (lt_of_lt_of_le (by norm_num) (half_le_ellHat_real L hL ht0.le ht1))
      (Real.sqrt_pos.2 (by linarith))
  have hmono := sqrt_one_sub_mul_ellHat_le L ht1 (one_sub_le_norm_one_sub_mul ht0.le hξ)
  refine norm_sub_le_zdist_mul L (fun y => Theta L ((t : ℂ) * ξ) x y) (fun y => ?_) c c'
  refine (norm_Theta_sub_shift_le_complex L hL hζ0 hζ x y).trans ?_
  refine div_le_div_of_nonneg_left (by norm_num) hden ?_
  linarith [mul_comm (ellHat L (t : ℂ)) √(1 - t),
    mul_comm (ellHat L ((t : ℂ) * ξ)) √‖1 - (t : ℂ) * ξ‖]

theorem sum_norm_SB_apply_row (hL : 3 ≤ L) (x : ZMod L) : ∑ w : ZMod L, ‖SB L x w‖ = 1 := by
  have h := sum_nnnorm_SB_row L hL x
  have h2 : ((∑ w : ZMod L, ‖SB L x w‖₊ : NNReal) : ℝ) = 1 := by rw [h]; rfl
  simpa using h2

theorem norm_SB_mul_apply_le (hL : 3 ≤ L) {M : Matrix (ZMod L) (ZMod L) ℂ} {β : ℝ}
    {c : ZMod L} (hM : ∀ w, ‖M w c‖ ≤ β) (x : ZMod L) : ‖(SB L * M) x c‖ ≤ β := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ w : ZMod L, ‖SB L x w * M w c‖ ≤ ∑ w : ZMod L, ‖SB L x w‖ * β :=
        Finset.sum_le_sum fun w _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _)
    _ = β := by rw [← Finset.sum_mul, sum_norm_SB_apply_row L hL, one_mul]

theorem norm_SB_mul_sub_le (hL : 3 ≤ L) {M : Matrix (ZMod L) (ZMod L) ℂ} {β : ℝ}
    {c c' : ZMod L} (hM : ∀ w, ‖M w c - M w c'‖ ≤ β) (x : ZMod L) :
    ‖(SB L * M) x c - (SB L * M) x c'‖ ≤ β := by
  rw [Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ w : ZMod L, ‖SB L x w * M w c - SB L x w * M w c'‖
      ≤ ∑ w : ZMod L, ‖SB L x w‖ * β :=
        Finset.sum_le_sum fun w _ => by
          rw [← mul_sub, norm_mul]; exact mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _)
    _ = β := by rw [← Finset.sum_mul, sum_norm_SB_apply_row L hL, one_mul]

theorem sum_norm_SB_mul_row_le (hL : 3 ≤ L) {M : Matrix (ZMod L) (ZMod L) ℂ} {β : ℝ}
    (hM : ∀ w, ∑ c : ZMod L, ‖M w c‖ ≤ β) (x : ZMod L) :
    ∑ c : ZMod L, ‖(SB L * M) x c‖ ≤ β := by
  calc ∑ c : ZMod L, ‖(SB L * M) x c‖
      ≤ ∑ c : ZMod L, ∑ w : ZMod L, ‖SB L x w‖ * ‖M w c‖ :=
        Finset.sum_le_sum fun c _ => by
          rw [Matrix.mul_apply]
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
    _ = ∑ w : ZMod L, ‖SB L x w‖ * ∑ c : ZMod L, ‖M w c‖ := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ w : ZMod L, ‖SB L x w‖ * β :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hM w) (norm_nonneg _)
    _ = β := by rw [← Finset.sum_mul, sum_norm_SB_apply_row L hL, one_mul]

/-- (7.18): `Ξ = edgeKer - 1 = -(s - t) ξ S^(B) Θ^(B)_{tξ}`, entrywise. -/
theorem edgeKer_sub_one_apply (hL : 3 ≤ L) {ξ s t : ℂ} (ht : ‖t * ξ‖ < 1) (x c : ZMod L) :
    (edgeKer L ξ s t - 1) x c = -((s - t) * ξ) * (SB L * Theta L (t * ξ)) x c := by
  rw [edgeKer_eq L hL ht]
  simp [Matrix.sub_apply, Matrix.smul_apply]

end EdgeBounds

/-! ### The edge factors `Ξᵢ = edgeKer - 1` at real times -/

section XiBounds

variable (L : ℕ) [NeZero L]

/-- Entry bound for `Ξ`: `|Ξ_{xc}| ≤ (t - s) C/(η_t ℓ_t)`, from (2.52). -/
theorem norm_edgeKer_sub_one_apply_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (x c : ZMod L) :
    ‖(edgeKer L ξ s t - 1) x c‖ ≤ (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) := by
  rw [edgeKer_sub_one_apply L hL (norm_ofReal_mul_lt_one ht0 ht1 hξ), norm_mul, norm_neg]
  exact mul_le_mul (norm_sub_ofReal_mul_le hst hξ)
    (norm_SB_mul_apply_le L hL (fun w => norm_Theta_mul_apply_le L hL ht0 ht1 hξ w c) x)
    (norm_nonneg _) (by linarith)

theorem sum_norm_edgeKer_sub_one_le_aux (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {β : ℝ}
    (hβ : ∀ w, ∑ c : ZMod L, ‖Theta L ((t : ℂ) * ξ) w c‖ ≤ β) (x : ZMod L) :
    ∑ c : ZMod L, ‖(edgeKer L ξ s t - 1) x c‖ ≤ (t - s) * β := by
  have hζ := norm_ofReal_mul_lt_one ht0 ht1 hξ
  simp_rw [edgeKer_sub_one_apply L hL hζ, norm_mul, norm_neg]
  rw [← Finset.mul_sum]
  have hβ0 : 0 ≤ β := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hβ 0)
  exact mul_le_mul (norm_sub_ofReal_mul_le hst hξ) (sum_norm_SB_mul_row_le L hL hβ x)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by linarith)

/-- Row bound for `Ξ`: `∑_c |Ξ_{xc}| ≤ (t - s)/(1 - t)` (the `η_s/η_t` of Lemma 7.1). -/
theorem sum_norm_edgeKer_sub_one_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (x : ZMod L) :
    ∑ c : ZMod L, ‖(edgeKer L ξ s t - 1) x c‖ ≤ (t - s) * (1 - t)⁻¹ := by
  have hζ := norm_ofReal_mul_lt_one ht0 ht1 hξ
  refine sum_norm_edgeKer_sub_one_le_aux L hL hst ht0 ht1 hξ (fun w => ?_) x
  refine (sum_norm_Theta_row_le L hL hζ w).trans ?_
  have h1 : 1 - t ≤ 1 - ‖(t : ℂ) * ξ‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg ξ]
  exact inv_anti₀ (by linarith) h1

/-- Row bound for a **short edge** (Case 1): if `|1 - tξ| ≥ κ` then
`∑_c |Ξ_{xc}| ≤ (t - s) C/κ = O(1)`. -/
theorem sum_norm_edgeKer_sub_one_le_short (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {κ : ℝ} (hκ : 0 < κ)
    (hκt : κ ≤ ‖1 - (t : ℂ) * ξ‖) (x : ZMod L) :
    ∑ c : ZMod L, ‖(edgeKer L ξ s t - 1) x c‖ ≤ (t - s) * (2 * cTwo52 * (1 / cZero + 2) / κ) := by
  have hζ := norm_ofReal_mul_lt_one ht0 ht1 hξ
  refine sum_norm_edgeKer_sub_one_le_aux L hL hst ht0 ht1 hξ (fun w => ?_) x
  refine (sum_norm_Theta_row_le_complex L hL hζ w).trans ?_
  have : 0 ≤ 2 * cTwo52 * (1 / cZero + 2) := by
    have := cTwo52_pos; have := cZero_pos; positivity
  exact div_le_div_of_nonneg_left this hκ hκt

/-- Lipschitz bound for `Ξ` in its second index, from (2.53):
`|Ξ_{xc} - Ξ_{xc'}| ≤ (t - s) · 144/(ℓ_t η_t^{1/2}) · ‖c - c'‖`. -/
theorem norm_edgeKer_sub_one_sub_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht0 : 0 < t)
    (ht1 : t < 1) {ξ : ℂ} (hξ0 : ξ ≠ 0) (hξ : ‖ξ‖ ≤ 1) (x c c' : ZMod L) :
    ‖(edgeKer L ξ s t - 1) x c - (edgeKer L ξ s t - 1) x c'‖
      ≤ (t - s) * (144 / (ellHat L (t : ℂ) * √(1 - t))) * zdist L (c - c') := by
  have hζ := norm_ofReal_mul_lt_one ht0.le ht1 hξ
  rw [edgeKer_sub_one_apply L hL hζ, edgeKer_sub_one_apply L hL hζ, ← mul_sub, norm_mul,
    norm_neg, mul_assoc]
  exact mul_le_mul (norm_sub_ofReal_mul_le hst hξ)
    (norm_SB_mul_sub_le L hL (fun w => norm_Theta_mul_sub_le L hL ht0 ht1 hξ0 hξ w c c') x)
    (norm_nonneg _) (by linarith)

end XiBounds

/-! ### Elementary inequalities for the paper-form constants -/

section Algebra

theorem kerDecay_alg_one {n : ℕ} (hn : 1 ≤ n) {M X r c K R ρ : ℝ} (hM : 0 ≤ M)
    (hX0 : 0 ≤ X) (hX : X ≤ c * K * R) (hr : r ≤ ρ * R) (hc : 0 ≤ c)
    (hK : 1 ≤ K) (hR : 1 ≤ R) (hρ : 0 ≤ ρ) :
    M * (2 ^ n * (1 + X) ^ n + r * X ^ (n - 1))
      ≤ (2 ^ n * (1 + c) ^ n + ρ * c ^ (n - 1)) * K ^ n * R ^ n * M := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hKR : 1 ≤ K * R := one_le_mul_of_one_le_of_one_le hK hR
  have h1 : 1 + X ≤ (1 + c) * (K * R) := by nlinarith
  have h1' : (1 + X) ^ (m + 1) ≤ ((1 + c) * (K * R)) ^ (m + 1) :=
    pow_le_pow_left₀ (by linarith) h1 _
  have h2 : X ^ m ≤ (c * K * R) ^ m := pow_le_pow_left₀ hX0 hX m
  have h3 : r * X ^ m ≤ ρ * R * (c * K * R) ^ m :=
    mul_le_mul hr h2 (pow_nonneg hX0 _) (by positivity)
  have h4 : K ^ m ≤ K ^ (m + 1) := pow_le_pow_right₀ hK (Nat.le_succ m)
  have hR0 : 0 ≤ R := by linarith
  calc M * (2 ^ (m + 1) * (1 + X) ^ (m + 1) + r * X ^ m)
      ≤ M * (2 ^ (m + 1) * ((1 + c) * (K * R)) ^ (m + 1) + ρ * R * (c * K * R) ^ m) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1' (by positivity)) h3)
          hM
    _ = (2 ^ (m + 1) * (1 + c) ^ (m + 1) * K ^ (m + 1) + ρ * c ^ m * K ^ m) * R ^ (m + 1) * M := by
        simp only [mul_pow]; ring
    _ ≤ (2 ^ (m + 1) * (1 + c) ^ (m + 1) * K ^ (m + 1) + ρ * c ^ m * K ^ (m + 1))
          * R ^ (m + 1) * M := by gcongr
    _ = (2 ^ (m + 1) * (1 + c) ^ (m + 1) + ρ * c ^ m) * K ^ (m + 1) * R ^ (m + 1) * M := by ring

theorem kerDecay_alg_two {n : ℕ} (hn : 2 ≤ n) {M X Y r c₁ c₃ K R : ℝ} (hM : 0 ≤ M)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : X ≤ c₁ * K * R)
    (hrY : r * Y ≤ c₃ * K ^ 2 * R ^ 2) (hXY : X + Y ≤ (c₁ + c₃) * K ^ 2 * R) (hc₁ : 0 ≤ c₁)
    (hc₃ : 0 ≤ c₃) (hK : 1 ≤ K) (hR : 1 ≤ R) :
    M * (2 ^ n * (1 + X) ^ n + 2 ^ n * (r * Y * (X + Y) ^ (n - 2)))
      ≤ (2 ^ n * (1 + c₁) ^ n + 2 ^ n * (c₃ * (c₁ + c₃) ^ (n - 2))) * K ^ (2 * n) * R ^ n * M := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hKR : 1 ≤ K * R := one_le_mul_of_one_le_of_one_le hK hR
  have h1 : 1 + X ≤ (1 + c₁) * (K * R) := by nlinarith
  have h1' : (1 + X) ^ (m + 2) ≤ ((1 + c₁) * (K * R)) ^ (m + 2) :=
    pow_le_pow_left₀ (by linarith) h1 _
  have h2 : (X + Y) ^ m ≤ ((c₁ + c₃) * K ^ 2 * R) ^ m := pow_le_pow_left₀ (by linarith) hXY m
  have h3 : r * Y * (X + Y) ^ m ≤ c₃ * K ^ 2 * R ^ 2 * ((c₁ + c₃) * K ^ 2 * R) ^ m :=
    mul_le_mul hrY h2 (pow_nonneg (by linarith) _) (by positivity)
  have h4 : K ^ (m + 2) ≤ K ^ (2 * (m + 2)) := pow_le_pow_right₀ hK (by omega)
  have h5 : K ^ (2 * m + 2) ≤ K ^ (2 * (m + 2)) := pow_le_pow_right₀ hK (by omega)
  have hR0 : 0 ≤ R := by linarith
  calc M * (2 ^ (m + 2) * (1 + X) ^ (m + 2) + 2 ^ (m + 2) * (r * Y * (X + Y) ^ m))
      ≤ M * (2 ^ (m + 2) * ((1 + c₁) * (K * R)) ^ (m + 2)
          + 2 ^ (m + 2) * (c₃ * K ^ 2 * R ^ 2 * ((c₁ + c₃) * K ^ 2 * R) ^ m)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1' (by positivity))
          (mul_le_mul_of_nonneg_left h3 (by positivity))) hM
    _ = (2 ^ (m + 2) * (1 + c₁) ^ (m + 2) * K ^ (m + 2)
          + 2 ^ (m + 2) * (c₃ * (c₁ + c₃) ^ m) * K ^ (2 * m + 2)) * R ^ (m + 2) * M := by
        simp only [mul_pow, ← pow_mul]; ring
    _ ≤ (2 ^ (m + 2) * (1 + c₁) ^ (m + 2) * K ^ (2 * (m + 2))
          + 2 ^ (m + 2) * (c₃ * (c₁ + c₃) ^ m) * K ^ (2 * (m + 2))) * R ^ (m + 2) * M := by
        gcongr
    _ = (2 ^ (m + 2) * (1 + c₁) ^ (m + 2) + 2 ^ (m + 2) * (c₃ * (c₁ + c₃) ^ m))
          * K ^ (2 * (m + 2)) * R ^ (m + 2) * M := by ring

end Algebra

/-! ### Lemma 7.3 in the paper's scales -/

/-- `c₁ = 6e C_{2.52}`: window size × entry bound of `Ξ`, in units of `W^τ ℓ_sη_s/(ℓ_tη_t)`. -/
noncomputable def cWin : ℝ := 6 * exp 1 * cTwo52

/-- `c₂ = 2 C_{2.52}(1/c₀ + 2)`: the row bound of a short edge, in units of `1/κ`. -/
noncomputable def cShort : ℝ := 2 * cTwo52 * (1 / cZero + 2)

/-- `c₃ = 6e · 144`: window size × window radius × Lipschitz constant of `Ξ` (from (2.53)). -/
noncomputable def cLip : ℝ := 6 * exp 1 * 144

/-- The constant `C_n` of (7.14). -/
noncomputable def cKer (n : ℕ) : ℝ := 2 ^ n * (1 + cWin) ^ n + cWin ^ (n - 1)

/-- The constant `C_n` of Case 1 of (7.16) (it depends on the short-edge gap `κ`). -/
noncomputable def cKerShort (n : ℕ) (κ : ℝ) : ℝ :=
  2 ^ n * (1 + cWin) ^ n + cShort / κ * cWin ^ (n - 1)

/-- The constant `C_n` of Case 2 of (7.16). -/
noncomputable def cKerSumZero (n : ℕ) : ℝ :=
  2 ^ n * (1 + cWin) ^ n + 2 ^ n * (cLip * (cWin + cLip) ^ (n - 2))

/-- The constant in front of the `W^{-D}` error in Case 2 of (7.16). -/
noncomputable def cKerSumZeroErr (n : ℕ) : ℝ := 1 + (2 * cTwo52) ^ (n - 1)

theorem cWin_nonneg : 0 ≤ cWin := by unfold cWin; have := cTwo52_pos; positivity
theorem cLip_nonneg : 0 ≤ cLip := by unfold cLip; positivity
theorem cShort_nonneg : 0 ≤ cShort := by
  unfold cShort; have := cTwo52_pos; have := cZero_pos; positivity

section PaperScales

variable (L : ℕ) [NeZero L]

theorem ellHat_real_pos (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < ellHat L (t : ℂ) :=
  lt_of_lt_of_le (by norm_num) (half_le_ellHat_real L hL ht0 ht1)

/-- `ℓ_sη_s/(ℓ_tη_t) ≥ 1`. -/
theorem one_le_ratio (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    1 ≤ (1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ)) := by
  have hD : 0 < (1 - t) * ellHat L (t : ℂ) :=
    mul_pos (by linarith) (ellHat_real_pos L hL (hs0.trans hst) ht1)
  rw [one_le_div hD]
  exact one_sub_mul_ellHat_anti L hst ht1

/-- `ℓ_t/ℓ_s ≥ 1`. -/
theorem one_le_ellHat_ratio (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    1 ≤ ellHat L (t : ℂ) / ellHat L (s : ℂ) := by
  rw [one_le_div (ellHat_real_pos L hL hs0 (hst.trans_lt ht1))]
  exact ellHat_real_mono L hst ht1

theorem one_add_row_eq {s t : ℝ} (ht1 : t < 1) :
    1 + (t - s) * (1 - t)⁻¹ = (1 - s) / (1 - t) := by
  have : (1 : ℝ) - t ≠ 0 := by linarith
  field_simp; ring

/-- `η_s/η_t = (ℓ_t/ℓ_s) · ℓ_sη_s/(ℓ_tη_t)`, so the row bound `(t-s)/(1-t)` of `Ξ` is at
most `(ℓ_t/ℓ_s) · ℓ_sη_s/(ℓ_tη_t)`. -/
theorem row_le_ratio (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    (t - s) * (1 - t)⁻¹ ≤ ellHat L (t : ℂ) / ellHat L (s : ℂ)
      * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) := by
  have hs := ellHat_real_pos L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL (hs0.trans hst) ht1
  have h1t : (1 : ℝ) - t ≠ 0 := by linarith
  have e : ellHat L (t : ℂ) / ellHat L (s : ℂ)
      * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) = (1 - s) * (1 - t)⁻¹ := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 (by linarith))

/-- Window size × entry bound of `Ξ`: `e · N ≤ c₁ K ℓ_sη_s/(ℓ_tη_t)` for the window
`ℓ_s K`, `K ≥ 1` (the paper's `K = W^τ`). -/
theorem entry_mul_win_le (hL : 3 ≤ L) {s t K : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (hK : 1 ≤ K) :
    (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) * (2 * exp 1 * (ellHat L (s : ℂ) * K + 1))
      ≤ cWin * K * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) := by
  have hs := half_le_ellHat_real L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL (hs0.trans hst) ht1
  have hD : 0 < (1 - t) * ellHat L (t : ℂ) := mul_pos (by linarith) ht
  have h3 : ellHat L (s : ℂ) * K + 1 ≤ 3 * (ellHat L (s : ℂ) * K) := by nlinarith
  have hC := cTwo52_pos
  calc (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)))
        * (2 * exp 1 * (ellHat L (s : ℂ) * K + 1))
      ≤ (1 - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)))
        * (2 * exp 1 * (3 * (ellHat L (s : ℂ) * K))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hC.le hD.le))
          (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
          (mul_nonneg (by linarith) (div_nonneg hC.le hD.le))
    _ = cWin * K * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) := by
        unfold cWin; ring

end PaperScales

section Lemma73

variable (L : ℕ) [NeZero L]

/-- **Lemma 7.3, (7.14)**, with explicit constants.  Let `0 ≤ s ≤ t < 1`, `|ξᵢ| ≤ 1`,
`K ≥ 1` (the paper's `W^τ`), and let `A` be `(ℓ_s K, δ)`-fast-decaying ((7.13)) with
`‖A‖_max ≤ M`.  Then, with `ℓ_u = ℓ̂(u)` and `η_u = 1 - u`,
`|(U_{s,t,σ} ∘ A)_a| ≤ C_n K^n (ℓ_t/ℓ_s) (ℓ_sη_s/(ℓ_tη_t))^n M + (η_s/η_t)^n δ`. -/
theorem norm_Uker_fastDecay_le {n : ℕ} (hn : 1 ≤ n) (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {K M δ : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (a : LoopArg L n) :
    ‖Uker L ξ s t A a‖ ≤
      cKer n * K ^ n * (ellHat L (t : ℂ) / ellHat L (s : ℂ))
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + ((1 - s) / (1 - t)) ^ n * δ := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hs := ellHat_real_pos L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL ht0 ht1
  have hℓ : 0 < ellHat L (s : ℂ) * K := mul_pos hs (by linarith)
  set R := (1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ)) with hRdef
  set ρ := ellHat L (t : ℂ) / ellHat L (s : ℂ) with hρdef
  set e := (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) with hedef
  have he0 : 0 ≤ e := mul_nonneg (by linarith)
    (div_nonneg cTwo52_pos.le (mul_pos (by linarith) ht).le)
  have hR := one_le_ratio L hL hs0 hst ht1
  have hρ := one_le_ellHat_ratio L hL hs0 hst ht1
  rw [Uker_eq_kerOp]
  have key := norm_kerOp_fastDecay_le L (X := fun i => edgeKer L (ξ i) s t - 1) hℓ hM hδ hAM hA
    he0 (fun i x c => norm_edgeKer_sub_one_apply_le L hL hst ht0 ht1 (hξ i) x c)
    (fun i x => sum_norm_edgeKer_sub_one_le L hL hst ht0 ht1 (hξ i) x) ⟨0, hn⟩
    (fun x => sum_norm_edgeKer_sub_one_le L hL hst ht0 ht1 (hξ ⟨0, hn⟩) x) a
  refine key.trans ?_
  rw [one_add_row_eq ht1]
  refine add_le_add ?_ (le_of_eq (mul_comm _ _))
  have hX0 : 0 ≤ e * (2 * exp 1 * (ellHat L (s : ℂ) * K + 1)) := by positivity
  have alg := kerDecay_alg_one hn hM hX0 (entry_mul_win_le L hL hs0 hst ht1 hK)
    (row_le_ratio L hL hs0 hst ht1) cWin_nonneg hK hR (by linarith)
  refine alg.trans ?_
  have hc : 0 ≤ 2 ^ n * (1 + cWin) ^ n := by have := cWin_nonneg; positivity
  have hcoef : 2 ^ n * (1 + cWin) ^ n + ρ * cWin ^ (n - 1) ≤ cKer n * ρ := by
    unfold cKer; nlinarith [pow_nonneg cWin_nonneg (n - 1)]
  have hKR : 0 ≤ K ^ n * R ^ n * M := by
    have : 0 ≤ R := by linarith
    positivity
  calc (2 ^ n * (1 + cWin) ^ n + ρ * cWin ^ (n - 1)) * K ^ n * R ^ n * M
      = (2 ^ n * (1 + cWin) ^ n + ρ * cWin ^ (n - 1)) * (K ^ n * R ^ n * M) := by ring
    _ ≤ cKer n * ρ * (K ^ n * R ^ n * M) := mul_le_mul_of_nonneg_right hcoef hKR
    _ = cKer n * K ^ n * ρ * R ^ n * M := by ring

/-- **Lemma 7.3, Case 1 of (7.16)**: if one edge `i₀` is short, `|1 - tξ_{i₀}| ≥ κ > 0`
(for the paper's `σ_k = σ_{k-1}`, `ξ = m²` or `m̄²`; see `norm_Uker_fastDecay_le_of_eq`),
then the factor `ℓ_t/ℓ_s` of (7.14) disappears:
`|(U_{s,t,σ} ∘ A)_a| ≤ C_{n,κ} K^n (ℓ_sη_s/(ℓ_tη_t))^n M + (η_s/η_t)^n δ`. -/
theorem norm_Uker_fastDecay_le_short {n : ℕ} (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1) {κ : ℝ} (hκ : 0 < κ)
    (i₀ : Fin n) (hκt : κ ≤ ‖1 - (t : ℂ) * ξ i₀‖) {K M δ : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (a : LoopArg L n) :
    ‖Uker L ξ s t A a‖ ≤
      cKerShort n κ * K ^ n
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + ((1 - s) / (1 - t)) ^ n * δ := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (fun h => (h ▸ i₀).elim0)
  have ht0 : 0 ≤ t := hs0.trans hst
  have hs := ellHat_real_pos L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL ht0 ht1
  have hℓ : 0 < ellHat L (s : ℂ) * K := mul_pos hs (by linarith)
  set R := (1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ)) with hRdef
  set e := (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) with hedef
  have he0 : 0 ≤ e := mul_nonneg (by linarith)
    (div_nonneg cTwo52_pos.le (mul_pos (by linarith) ht).le)
  have hR := one_le_ratio L hL hs0 hst ht1
  rw [Uker_eq_kerOp]
  have key := norm_kerOp_fastDecay_le L (X := fun i => edgeKer L (ξ i) s t - 1) hℓ hM hδ hAM hA
    he0 (fun i x c => norm_edgeKer_sub_one_apply_le L hL hst ht0 ht1 (hξ i) x c)
    (fun i x => sum_norm_edgeKer_sub_one_le L hL hst ht0 ht1 (hξ i) x) i₀
    (fun x => sum_norm_edgeKer_sub_one_le_short L hL hst ht0 ht1 (hξ i₀) hκ hκt x) a
  refine key.trans ?_
  rw [one_add_row_eq ht1]
  refine add_le_add ?_ (le_of_eq (mul_comm _ _))
  have hX0 : 0 ≤ e * (2 * exp 1 * (ellHat L (s : ℂ) * K + 1)) := by positivity
  have hr₀ : (t - s) * (2 * cTwo52 * (1 / cZero + 2) / κ) ≤ cShort / κ * R := by
    have h0 : 0 ≤ cShort / κ := div_nonneg cShort_nonneg hκ.le
    calc (t - s) * (2 * cTwo52 * (1 / cZero + 2) / κ) ≤ 1 * (cShort / κ) := by
          unfold cShort; exact mul_le_mul_of_nonneg_right (by linarith) h0
      _ ≤ cShort / κ * R := by nlinarith
  have alg := kerDecay_alg_one hn hM hX0 (entry_mul_win_le L hL hs0 hst ht1 hK) hr₀
    cWin_nonneg hK hR (div_nonneg cShort_nonneg hκ.le)
  refine alg.trans (le_of_eq ?_)
  unfold cKerShort; ring

end Lemma73

section PaperScales2

variable (L : ℕ) [NeZero L]

/-- Window size × window radius × Lipschitz constant of `Ξ`:
`e' ℓ N ≤ c₃ K² (ℓ_sη_s/(ℓ_tη_t)) (ℓ_s/ℓ_t)`.  The last factor is the sum-zero gain. -/
theorem lip_mul_win_le (hL : 3 ≤ L) {s t K : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (hK : 1 ≤ K) :
    (t - s) * (144 / (ellHat L (t : ℂ) * √(1 - t))) * (ellHat L (s : ℂ) * K)
        * (2 * exp 1 * (ellHat L (s : ℂ) * K + 1))
      ≤ cLip * K ^ 2 * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))
          * (ellHat L (s : ℂ) / ellHat L (t : ℂ))) := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hs := half_le_ellHat_real L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  have hsq : 0 < √(1 - t) := Real.sqrt_pos.2 h1t
  have hsq2 : √(1 - t) * √(1 - t) = 1 - t := Real.mul_self_sqrt h1t.le
  have hlt : ellHat L (t : ℂ) * √(1 - t) ≤ 1 := by
    have := ellHat_real_le_inv_sqrt L ht1
    rw [le_div_iff₀ hsq] at this; linarith
  have h3 : ellHat L (s : ℂ) * K + 1 ≤ 3 * (ellHat L (s : ℂ) * K) := by nlinarith
  have hD : 0 < ellHat L (t : ℂ) * √(1 - t) := mul_pos ht hsq
  -- `144/(ℓ_t √η_t) ≤ 144/(ℓ_t² η_t)`
  have hkey : 144 / (ellHat L (t : ℂ) * √(1 - t))
      ≤ 144 / ((1 - t) * ellHat L (t : ℂ) * ellHat L (t : ℂ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have e : (1 - t) * ellHat L (t : ℂ) * ellHat L (t : ℂ)
        = (ellHat L (t : ℂ) * √(1 - t)) * (ellHat L (t : ℂ) * √(1 - t)) := by
      linear_combination (-(ellHat L (t : ℂ) ^ 2)) * hsq2
    rw [e]
    exact mul_le_of_le_one_right hD.le hlt
  have hℓK : 0 ≤ ellHat L (s : ℂ) * K := by nlinarith
  calc (t - s) * (144 / (ellHat L (t : ℂ) * √(1 - t))) * (ellHat L (s : ℂ) * K)
        * (2 * exp 1 * (ellHat L (s : ℂ) * K + 1))
      ≤ (1 - s) * (144 / ((1 - t) * ellHat L (t : ℂ) * ellHat L (t : ℂ)))
          * (ellHat L (s : ℂ) * K) * (2 * exp 1 * (3 * (ellHat L (s : ℂ) * K))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hkey
          (by positivity) (by linarith)) hℓK)
          (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity) ?_
        refine mul_nonneg (mul_nonneg (by linarith) (by positivity)) hℓK
    _ = cLip * K ^ 2 * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))
          * (ellHat L (s : ℂ) / ellHat L (t : ℂ))) := by
        unfold cLip; field_simp; ring

/-- The error factor of Case 2: `(1 + r)ⁿ + r e^{n-1} Lⁿ ≤ C Lⁿ (η_s/η_t)ⁿ`. -/
theorem sumZero_err_le {n : ℕ} (hn : 1 ≤ n) (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht1 : t < 1) :
    (1 + (t - s) * (1 - t)⁻¹) ^ n
        + (t - s) * (1 - t)⁻¹ * ((t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)))) ^ (n - 1)
          * (L : ℝ) ^ n
      ≤ cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - s) / (1 - t)) ^ n := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have ht := half_le_ellHat_real L hL ht0 ht1
  have h1t : 0 < 1 - t := by linarith
  set η := (1 - s) / (1 - t) with hη
  have hη0 : 0 ≤ η := div_nonneg (by linarith) h1t.le
  have hr : (t - s) * (1 - t)⁻¹ ≤ η := by
    rw [hη, div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hr0 : 0 ≤ (t - s) * (1 - t)⁻¹ := mul_nonneg (by linarith) (by positivity)
  have hC := cTwo52_pos
  have he : (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) ≤ 2 * cTwo52 * η := by
    have : cTwo52 / ((1 - t) * ellHat L (t : ℂ)) ≤ cTwo52 / ((1 - t) * (1 / 2)) :=
      div_le_div_of_nonneg_left hC.le (by positivity) (mul_le_mul_of_nonneg_left ht h1t.le)
    calc (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)))
        ≤ (1 - s) * (cTwo52 / ((1 - t) * (1 / 2))) :=
          mul_le_mul (by linarith) this (by positivity) (by linarith)
      _ = 2 * cTwo52 * η := by rw [hη]; field_simp
  have he0 : 0 ≤ (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) :=
    mul_nonneg (by linarith) (div_nonneg hC.le (by positivity))
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
  rw [one_add_row_eq ht1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have h2 : (t - s) * (1 - t)⁻¹ * ((t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)))) ^ m
      ≤ η * (2 * cTwo52 * η) ^ m :=
    mul_le_mul hr (pow_le_pow_left₀ he0 he m) (by positivity) hη0
  have hηp : 0 ≤ η ^ (m + 1) := pow_nonneg hη0 _
  unfold cKerSumZeroErr
  simp only [Nat.add_sub_cancel]
  calc η ^ (m + 1) + (t - s) * (1 - t)⁻¹
        * ((t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ)))) ^ m * (L : ℝ) ^ (m + 1)
      ≤ η ^ (m + 1) * (L : ℝ) ^ (m + 1) + η * (2 * cTwo52 * η) ^ m * (L : ℝ) ^ (m + 1) := by
        gcongr
        nlinarith
    _ = (1 + (2 * cTwo52) ^ m) * (L : ℝ) ^ (m + 1) * η ^ (m + 1) := by
        simp only [mul_pow]; ring

end PaperScales2

section Lemma73SumZero

variable (L : ℕ) [NeZero L]

/-- **Lemma 7.3, Case 2 of (7.16)**: if `A` has the sum-zero property (7.15) (at any
coordinate `j`; the paper's is `j = 0`), then for `n ≥ 2`, `0 ≤ s ≤ t < 1`, `t > 0`,
`0 < |ξᵢ| ≤ 1`,
`|(U_{s,t,σ} ∘ A)_a| ≤ C_n K^{2n} (ℓ_sη_s/(ℓ_tη_t))^n M + C'_n Lⁿ (η_s/η_t)^n δ`.
The paper's `W^{-D + C_n}` is our `C'_n Lⁿ (η_s/η_t)ⁿ δ` with `δ = W^{-D}`. -/
theorem norm_Uker_fastDecay_le_sumZero {n : ℕ} (hn : 2 ≤ n) (hL : 3 ≤ L) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht0 : 0 < t) (ht1 : t < 1) {ξ : Fin n → ℂ}
    (hξ0 : ∀ i, ξ i ≠ 0) (hξ : ∀ i, ‖ξ i‖ ≤ 1) {K M δ : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) {j : Fin n} (hz : SumZeroAt L j A)
    (a : LoopArg L n) :
    ‖Uker L ξ s t A a‖ ≤
      cKerSumZero n * K ^ (2 * n)
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - s) / (1 - t)) ^ n * δ := by
  have hs := ellHat_real_pos L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL ht0.le ht1
  have hℓ : 0 < ellHat L (s : ℂ) * K := mul_pos hs (by linarith)
  set R := (1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ)) with hRdef
  set e := (t - s) * (cTwo52 / ((1 - t) * ellHat L (t : ℂ))) with hedef
  set e' := (t - s) * (144 / (ellHat L (t : ℂ) * √(1 - t))) with he'def
  set r := (t - s) * (1 - t)⁻¹ with hrdef
  set N := 2 * exp 1 * (ellHat L (s : ℂ) * K + 1) with hNdef
  have h1t : 0 < 1 - t := by linarith
  have he0 : 0 ≤ e := mul_nonneg (by linarith) (div_nonneg cTwo52_pos.le (by positivity))
  have he'0 : 0 ≤ e' := mul_nonneg (by linarith)
    (div_nonneg (by norm_num) (mul_pos ht (Real.sqrt_pos.2 h1t)).le)
  have hR := one_le_ratio L hL hs0 hst ht1
  have hN0 : 0 ≤ N := by positivity
  rw [Uker_eq_kerOp]
  have key := norm_kerOp_sumZero_le L (X := fun i => edgeKer L (ξ i) s t - 1) hℓ hM hδ hAM hA hz
    he0 he'0 (fun i x c => norm_edgeKer_sub_one_apply_le L hL hst ht0.le ht1 (hξ i) x c)
    (fun i x => sum_norm_edgeKer_sub_one_le L hL hst ht0.le ht1 (hξ i) x)
    (fun i y c c' => norm_edgeKer_sub_one_sub_le L hL hst ht0 ht1 (hξ0 i) (hξ i) y c c') a
  refine key.trans (add_le_add ?_ ?_)
  · -- the main term
    have hX := entry_mul_win_le L hL hs0 hst ht1 hK
    have hY := lip_mul_win_le L hL hs0 hst ht1 hK
    have hrow := row_le_ratio L hL hs0 hst ht1
    have hσ1 : ellHat L (s : ℂ) / ellHat L (t : ℂ) ≤ 1 :=
      (div_le_one ht).2 (ellHat_real_mono L hst ht1)
    have hσ0 : 0 ≤ ellHat L (s : ℂ) / ellHat L (t : ℂ) := div_nonneg hs.le ht.le
    have hρσ : ellHat L (t : ℂ) / ellHat L (s : ℂ) * (ellHat L (s : ℂ) / ellHat L (t : ℂ)) = 1 := by
      field_simp
    have hR0 : 0 ≤ R := by linarith
    have hX0 : 0 ≤ e * N := mul_nonneg he0 hN0
    have hY0 : 0 ≤ e' * (ellHat L (s : ℂ) * K) * N := by positivity
    have hr0 : 0 ≤ r := mul_nonneg (by linarith) (inv_nonneg.2 h1t.le)
    have hK2 : K ≤ K ^ 2 := by nlinarith
    have hc₃ := cLip_nonneg
    have hc₁ := cWin_nonneg
    have hrY : r * (e' * (ellHat L (s : ℂ) * K) * N) ≤ cLip * K ^ 2 * R ^ 2 := by
      calc r * (e' * (ellHat L (s : ℂ) * K) * N)
          ≤ (ellHat L (t : ℂ) / ellHat L (s : ℂ) * R)
              * (cLip * K ^ 2 * (R * (ellHat L (s : ℂ) / ellHat L (t : ℂ)))) :=
            mul_le_mul hrow hY hY0 (by positivity)
        _ = cLip * K ^ 2 * R ^ 2 *
              (ellHat L (t : ℂ) / ellHat L (s : ℂ) * (ellHat L (s : ℂ) / ellHat L (t : ℂ))) := by
            ring
        _ = cLip * K ^ 2 * R ^ 2 := by rw [hρσ, mul_one]
    have hXY : e * N + e' * (ellHat L (s : ℂ) * K) * N ≤ (cWin + cLip) * K ^ 2 * R := by
      have h1 : cWin * K * R ≤ cWin * K ^ 2 * R := by gcongr
      have h2 : cLip * K ^ 2 * (R * (ellHat L (s : ℂ) / ellHat L (t : ℂ)))
          ≤ cLip * K ^ 2 * R := by
        gcongr; exact mul_le_of_le_one_right hR0 hσ1
      have := add_le_add (hX.trans h1) (hY.trans h2)
      linarith
    have alg := kerDecay_alg_two hn hM hX0 hY0 hX hrY hXY hc₁ hc₃ hK hR
    refine le_trans (le_of_eq ?_) (alg.trans (le_of_eq ?_))
    · ring
    · unfold cKerSumZero; ring
  · -- the error term
    have h := sumZero_err_le L (by omega : 1 ≤ n) hL hs0 hst ht1
    calc δ * ((1 + r) ^ n + r * e ^ (n - 1) * (L : ℝ) ^ n)
        ≤ δ * (cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - s) / (1 - t)) ^ n) :=
          mul_le_mul_of_nonneg_left h hδ
      _ = cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - s) / (1 - t)) ^ n * δ := by ring

end Lemma73SumZero

/-! ### The paper's edge parameters `ξᵢ = m(σᵢ) m(σᵢ₊₁)` -/

section Sigma

variable (L : ℕ) [NeZero L]

theorem norm_xiOf_mSigma {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| ≤ 2) (σ : Fin n → Bool)
    (i : Fin n) : ‖xiOf (mSigma E) σ i‖ = 1 := by
  rw [xiOf, norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]

theorem xiOf_mSigma_ne_zero {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| ≤ 2) (σ : Fin n → Bool)
    (i : Fin n) : xiOf (mSigma E) σ i ≠ 0 := by
  intro h
  have := norm_xiOf_mSigma hE σ i
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- A repeated sign `σ_k = σ_{k+1}` makes the edge `k` short: `ξ_k ∈ {m², m̄²}` and
`|1 - tξ_k| ≥ √κ` in the bulk `|E| ≤ 2 - κ`. -/
theorem sqrt_le_norm_one_sub_xiOf {n : ℕ} [NeZero n] {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {σ : Fin n → Bool} {k : Fin n}
    (hk : σ k = σ (k + 1)) : √κ ≤ ‖1 - (t : ℂ) * xiOf (mSigma E) σ k‖ := by
  have hshort := sqrt_le_norm_one_sub_short hκ0 hκ1 hE ht0 ht1
  rw [xiOf, ← hk]
  cases σ k
  · have e : (1 : ℂ) - (t : ℂ) * (mSigma E false * mSigma E false)
        = (starRingEnd ℂ) (1 - (t : ℂ) * (mE E) ^ 2) := by
      simp [mSigma, map_sub, map_mul, Complex.conj_ofReal, sq]
    rw [e, Complex.norm_conj]; exact hshort
  · have e : (1 : ℂ) - (t : ℂ) * (mSigma E true * mSigma E true) = 1 - (t : ℂ) * (mE E) ^ 2 := by
      simp [mSigma, sq]
    rw [e]; exact hshort

/-- **Lemma 7.3, Case 1 of (7.16)**, in the paper's form: `ξ = (m(σᵢ)m(σᵢ₊₁))ᵢ` with a
repeated sign `σ_k = σ_{k+1}` and `|E| ≤ 2 - κ`. -/
theorem norm_Uker_fastDecay_le_of_eq {n : ℕ} [NeZero n] (hL : 3 ≤ L) {E κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) {σ : Fin n → Bool} {k : Fin n} (hk : σ k = σ (k + 1))
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) {K M δ : ℝ}
    (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ) {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (a : LoopArg L n) :
    ‖Uker L (xiOf (mSigma E) σ) s t A a‖ ≤
      cKerShort n √κ * K ^ n
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + ((1 - s) / (1 - t)) ^ n * δ := by
  have hE2 : |E| ≤ 2 := hE.trans (by linarith)
  exact norm_Uker_fastDecay_le_short L hL hs0 hst ht1
    (fun i => (norm_xiOf_mSigma hE2 σ i).le) (Real.sqrt_pos.2 hκ0) k
    (sqrt_le_norm_one_sub_xiOf hκ0 hκ1 hE (hs0.trans hst) ht1.le hk) hK hM hδ hAM hA a

/-- **Lemma 7.3, Case 2 of (7.16)**, in the paper's form `ξ = (m(σᵢ)m(σᵢ₊₁))ᵢ`.  (No
alternation assumption on `σ` is needed: the proof only uses `0 < |ξᵢ| ≤ 1`.) -/
theorem norm_Uker_fastDecay_le_sumZero_sigma {n : ℕ} [NeZero n] (hn : 2 ≤ n) (hL : 3 ≤ L)
    {E : ℝ} (hE : |E| ≤ 2) (σ : Fin n → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht0 : 0 < t) (ht1 : t < 1) {K M δ : ℝ} (hK : 1 ≤ K) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    {A : LoopArg L n → ℂ} (hAM : ∀ b, ‖A b‖ ≤ M)
    (hA : FastDecay L (ellHat L (s : ℂ) * K) δ A) (hz : SumZeroAt L 0 A) (a : LoopArg L n) :
    ‖Uker L (xiOf (mSigma E) σ) s t A a‖ ≤
      cKerSumZero n * K ^ (2 * n)
        * ((1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ))) ^ n * M
        + cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - s) / (1 - t)) ^ n * δ :=
  norm_Uker_fastDecay_le_sumZero L hn hL hs0 hst ht0 ht1 (xiOf_mSigma_ne_zero hE σ)
    (fun i => (norm_xiOf_mSigma hE σ i).le) hK hM hδ hAM hA hz a

end Sigma

/-! ### Lemma 7.2: pointwise stretched-exponential inequalities -/

section Pointwise

/-- `√(u + v) ≤ u/2 + 1/2 + √v` turned into exponentials:
`e^{-u} e^{-√v} ≤ e^{1/2} e^{-√w} e^{-u/2}` whenever `w ≤ u + v`. -/
theorem exp_neg_mul_exp_neg_sqrt_le {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : w ≤ u + v) :
    exp (-u) * exp (-√v) ≤ exp (1 / 2) * exp (-√w) * exp (-(u / 2)) := by
  have h1 : √w ≤ √u + √v := (Real.sqrt_le_sqrt hw).trans (by
    have := sqrt_add_le_add_sqrt u hv; exact this)
  have h2 : √u ≤ u / 2 + 1 / 2 := by
    nlinarith [Real.sq_sqrt hu, sq_nonneg (√u - 1)]
  rw [← exp_add, ← exp_add, ← exp_add, exp_le_exp]
  linarith

theorem sqrt_le_half_add_half {u : ℝ} (hu : 0 ≤ u) : √u ≤ u / 2 + 1 / 2 := by
  nlinarith [Real.sq_sqrt hu, sq_nonneg (√u - 1)]

theorem exp_neg_quarter_le {x : ℝ} (hx : 0 ≤ x) :
    exp (-(x / 4)) ≤ exp 2 * exp (-(x / 8)) * exp (-√x) := by
  rw [← exp_add, ← exp_add, exp_le_exp]
  nlinarith [Real.sq_sqrt hx, sq_nonneg (√x - 4)]

/-- `e^{-a} ≤ 2/a²`, in the form `e^{-z/4} ≤ 64 σ` for `z² ≥ 1/(2σ)`. -/
theorem exp_neg_quarter_le_of_sq {z σ : ℝ} (hz : 0 ≤ z) (hσ : 0 < σ) (h : 1 ≤ 2 * σ * z ^ 2) :
    exp (-(z / 4)) ≤ 64 * σ := by
  have hq := Real.quadratic_le_exp_of_nonneg (x := z / 4) (by positivity)
  have hpos : 0 < exp (z / 4) := exp_pos _
  rw [exp_neg, inv_le_iff_one_le_mul₀ hpos]
  have h1 : 1 ≤ 64 * σ * ((z / 4) ^ 2 / 2) := by
    have : 64 * σ * ((z / 4) ^ 2 / 2) = 2 * σ * z ^ 2 := by ring
    rw [this]; exact h
  have h2 : (z / 4) ^ 2 / 2 ≤ exp (z / 4) := by nlinarith [sq_nonneg (z / 4)]
  calc (1 : ℝ) ≤ 64 * σ * ((z / 4) ^ 2 / 2) := h1
    _ ≤ 64 * σ * exp (z / 4) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- `√(y/σ) ≥ 4 √y` for `σ ≤ 1/16`. -/
theorem four_sqrt_le_sqrt_div {y σ : ℝ} (hσ : 0 < σ) (hσ16 : σ ≤ 1 / 16) :
    4 * √y ≤ √(y / σ) := by
  rw [Real.sqrt_div' _ hσ.le]
  have hsσ : 0 < √σ := Real.sqrt_pos.2 hσ
  have hsσ4 : √σ ≤ 1 / 4 := by
    rw [show (1 / 4 : ℝ) = √(1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hσ16
  rw [le_div_iff₀ hsσ]
  have := Real.sqrt_nonneg y
  nlinarith

/-- Unit-free core of `exp_three_le_short`. -/
theorem exp_three_le_short_aux {x y₁ y₂ y₃ σ : ℝ} (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) (hy₃ : 0 ≤ y₃)
    (hσ0 : 0 < σ) (hσ16 : σ ≤ 1 / 16) (hx1 : 1 ≤ x) (hxy : x ≤ y₁ + y₂ + y₃) :
    exp (-(y₁ / 2) - y₂ - 1 / 2 * √(y₃ / σ))
      ≤ (64 * exp (1 / 2) * σ + exp 2 * exp (-(x / 8))) * exp (-√x) := by
  have hz0 : 0 ≤ √(y₃ / σ) := Real.sqrt_nonneg _
  have hA : 0 ≤ 64 * exp (1 / 2) * σ * exp (-√x) := by positivity
  have hB : 0 ≤ exp 2 * exp (-(x / 8)) * exp (-√x) := by positivity
  rcases le_or_gt (x / 2) (y₁ + y₂) with hu | hu
  · have h1 : exp (-(y₁ / 2) - y₂ - 1 / 2 * √(y₃ / σ)) ≤ exp (-(x / 4)) := by
      rw [exp_le_exp]; linarith
    have h2 := exp_neg_quarter_le (x := x) (by linarith)
    rw [add_mul]
    linarith
  · have hu0 : 0 ≤ y₁ + y₂ := by linarith
    have hsx : √x ≤ √(y₁ + y₂) + √y₃ :=
      (Real.sqrt_le_sqrt (by linarith)).trans (sqrt_add_le_add_sqrt _ hy₃)
    have hsu := sqrt_le_half_add_half hu0
    have hz4 := four_sqrt_le_sqrt_div (y := y₃) hσ0 hσ16
    have hzsq : √(y₃ / σ) ^ 2 = y₃ / σ := Real.sq_sqrt (div_nonneg hy₃ hσ0.le)
    have hz2 : 1 ≤ 2 * σ * √(y₃ / σ) ^ 2 := by
      rw [hzsq, mul_assoc, mul_div_cancel₀ _ hσ0.ne']; linarith
    have hez := exp_neg_quarter_le_of_sq hz0 hσ0 hz2
    have hkey : exp (-(y₁ / 2) - y₂ - 1 / 2 * √(y₃ / σ))
        ≤ exp (1 / 2) * exp (-(√(y₃ / σ) / 4)) * exp (-√x) := by
      rw [← exp_add, ← exp_add, exp_le_exp]; linarith
    calc exp (-(y₁ / 2) - y₂ - 1 / 2 * √(y₃ / σ))
        ≤ exp (1 / 2) * exp (-(√(y₃ / σ) / 4)) * exp (-√x) := hkey
      _ ≤ exp (1 / 2) * (64 * σ) * exp (-√x) := by gcongr
      _ = 64 * exp (1 / 2) * σ * exp (-√x) := by ring
      _ ≤ (64 * exp (1 / 2) * σ + exp 2 * exp (-(x / 8))) * exp (-√x) := by
          rw [add_mul]; linarith

/-- The long-range regime of (7.4)–(7.5): if the window `ℓ'` of `A` is much shorter than the
decay length `ℓ` of `Θ_t` (`16 ℓ' ≤ ℓ`) and `d ≥ ℓ`, then
`e^{-d₁/ℓ} e^{-d₂/ℓ} e^{-√(d₃/ℓ')}
  ≤ (64 e^{1/2} ℓ'/ℓ + e² e^{-d/(8ℓ)}) e^{-√(d/ℓ)} · e^{-d₁/(2ℓ)} e^{-√(d₃/ℓ')/2}`
for `d ≤ d₁ + d₂ + d₃`. -/
theorem exp_three_le_short {d d₁ d₂ d₃ ℓ ℓ' : ℝ} (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (hℓ' : 0 < ℓ') (hσ : 16 * ℓ' ≤ ℓ) (hdℓ : ℓ ≤ d) (hd : d ≤ d₁ + d₂ + d₃) :
    exp (-(d₁ / ℓ)) * exp (-(d₂ / ℓ)) * exp (-√(d₃ / ℓ'))
      ≤ (64 * exp (1 / 2) * (ℓ' / ℓ) + exp 2 * exp (-(d / ℓ / 8))) * exp (-√(d / ℓ))
        * (exp (-(d₁ / ℓ / 2)) * exp (-(1 / 2 * √(d₃ / ℓ')))) := by
  have hℓ : 0 < ℓ := by linarith
  have hx1 : 1 ≤ d / ℓ := by rw [le_div_iff₀ hℓ]; linarith
  have hxy : d / ℓ ≤ d₁ / ℓ + d₂ / ℓ + d₃ / ℓ := by
    rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right hd hℓ.le
  have hσ0 : 0 < ℓ' / ℓ := div_pos hℓ' hℓ
  have hσ16 : ℓ' / ℓ ≤ 1 / 16 := by rw [div_le_iff₀ hℓ]; linarith
  have hd₃' : d₃ / ℓ' = d₃ / ℓ / (ℓ' / ℓ) := by field_simp
  have h := exp_three_le_short_aux (div_nonneg hd₁ hℓ.le) (div_nonneg hd₂ hℓ.le)
    (div_nonneg hd₃ hℓ.le) hσ0 hσ16 hx1 hxy
  rw [← hd₃'] at h
  have hsplit : exp (-(d₁ / ℓ)) * exp (-(d₂ / ℓ)) * exp (-√(d₃ / ℓ'))
      = exp (-(d₁ / ℓ / 2) - d₂ / ℓ - 1 / 2 * √(d₃ / ℓ'))
        * (exp (-(d₁ / ℓ / 2)) * exp (-(1 / 2 * √(d₃ / ℓ')))) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add]; ring_nf
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right h (by positivity)

end Pointwise

/-! ### Lemma 7.2: lattice sums and the kernel of the long edge -/

section TailSums

variable (L : ℕ) [NeZero L]

theorem sum_fin_two_fun (F : ZMod L → ZMod L → ℝ) :
    ∑ b : LoopArg L 2, F (b 0) (b 1) = ∑ x : ZMod L, ∑ y : ZMod L, F x y := by
  rw [← (piFinTwoEquiv fun _ => ZMod L).symm.sum_comp, Fintype.sum_prod_type]
  simp

/-- `∑_c e^{-‖a - c‖/(2ℓ)} ≤ 8ℓ` for `ℓ ≥ 1/2`. -/
theorem sum_exp_neg_zdist_half_le {ℓ : ℝ} (hℓ : 1 / 2 ≤ ℓ) (a : ZMod L) :
    ∑ c : ZMod L, exp (-((zdist L (a - c) : ℝ) / ℓ / 2)) ≤ 8 * ℓ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hlam : 0 < 1 / (2 * ℓ) := by positivity
  have e : ∀ c : ZMod L, exp (-((zdist L (a - c) : ℝ) / ℓ / 2))
      = exp (-(1 / (2 * ℓ) * (zdist L (c - a) : ℝ))) := by
    intro c
    rw [← zdist_neg L (a - c), neg_sub]
    congr 1; field_simp
  simp_rw [e]
  refine (sum_exp_zdist_le L hlam a).trans ?_
  have h3 := one_sub_exp_neg_ge hlam
  have hpos : 0 < 1 / (2 * ℓ) / (1 + 1 / (2 * ℓ)) := by positivity
  have e2 : 1 / (2 * ℓ) / (1 + 1 / (2 * ℓ)) = 1 / (2 * ℓ + 1) := by field_simp
  rw [e2] at h3 hpos
  rw [div_le_iff₀ (hpos.trans_le h3)]
  rw [div_le_iff₀ (by linarith)] at h3
  nlinarith

/-- `∑_x e^{-√(‖c - x‖/ℓ')/2} ≤ 36 ℓ'` for `ℓ' ≥ 1/2`. -/
theorem sum_exp_neg_half_sqrt_le {ℓ' : ℝ} (hℓ' : 1 / 2 ≤ ℓ') (c : ZMod L) :
    ∑ x : ZMod L, exp (-(1 / 2 * √((zdist L (c - x) : ℝ) / ℓ'))) ≤ 36 * ℓ' := by
  refine (sum_exp_neg_mul_sqrt_zdist_div_le L (by norm_num) (by linarith) c).trans ?_
  have : 2 * (1 + 2 * ℓ' / (1 / 2 : ℝ) ^ 2) = 2 + 16 * ℓ' := by ring
  rw [this]; linarith

/-- The kernel of the long edge `ξ = 1` ((7.7), (7.10)):
`|(Θ_t Θ_s^{-1} - 1)_{xc}| ≤ 8e³ (t-s)/((1-t)ℓ_t) · e^{-‖x - c‖/ℓ_t}`. -/
theorem norm_edgeKer_one_sub_one_le (hL : 3 ≤ L) {s t : ℝ} (hst : s ≤ t) (ht0 : 0 < t)
    (ht1 : t < 1) (x c : ZMod L) :
    ‖(edgeKer L 1 s t - 1) x c‖
      ≤ 8 * exp 3 * (t - s) / ((1 - t) * ellHat L (t : ℂ))
        * exp (-((zdist L (x - c) : ℝ) / ellHat L (t : ℂ))) := by
  have hξ : ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hζ := norm_ofReal_mul_lt_one ht0.le ht1 hξ
  have hℓ := half_le_ellHat_real L hL ht0.le ht1
  have hℓ0 : 0 < ellHat L (t : ℂ) := by linarith
  have h1t : 0 < 1 - t := by linarith
  set ℓ := ellHat L (t : ℂ) with hℓdef
  set B := 8 * exp 3 * exp (-((zdist L (x - c) : ℝ) / ℓ)) / ((1 - t) * ℓ) with hB
  have hΘ : ∀ w, SB L x w ≠ 0 → ‖Theta L ((t : ℂ) * 1) w c‖ ≤ B := by
    intro w hw
    have hxw : zdist L (x - w) ≤ 1 := by
      by_contra h; exact hw (SB_apply_eq_zero L hL (by omega))
    have htri : (zdist L (x - c) : ℝ) ≤ 1 + zdist L (w - c) := by
      have := zdist_add_le L (x - w) (w - c)
      rw [sub_add_sub_cancel] at this
      have : (zdist L (x - c) : ℝ) ≤ zdist L (x - w) + zdist L (w - c) := by exact_mod_cast this
      have h1 : (zdist L (x - w) : ℝ) ≤ 1 := by exact_mod_cast hxw
      linarith
    rw [mul_one]
    refine (norm_Theta_apply_le_of_real hL ht0 ht1 w c).trans ?_
    rw [hB]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have hexp : exp (-(zdist L (w - c) : ℝ) / ℓ) ≤ exp 2 * exp (-((zdist L (x - c) : ℝ) / ℓ)) := by
      rw [← exp_add, exp_le_exp]
      have h2 : 1 / ℓ ≤ 2 := by rw [div_le_iff₀ hℓ0]; linarith
      have : ((zdist L (x - c) : ℝ) - zdist L (w - c)) / ℓ ≤ 1 / ℓ :=
        div_le_div_of_nonneg_right (by linarith) hℓ0.le
      rw [neg_div]
      have e : -((zdist L (w - c) : ℝ) / ℓ) = ((zdist L (x - c) : ℝ) - zdist L (w - c)) / ℓ
          - (zdist L (x - c) : ℝ) / ℓ := by ring
      rw [e]; linarith
    have e3 : exp 3 = exp 1 * exp 2 := by rw [← exp_add]; norm_num
    rw [e3]
    calc 8 * exp 1 * exp (-(zdist L (w - c) : ℝ) / ℓ)
        ≤ 8 * exp 1 * (exp 2 * exp (-((zdist L (x - c) : ℝ) / ℓ))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 8 * (exp 1 * exp 2) * exp (-((zdist L (x - c) : ℝ) / ℓ)) := by ring
  have hSB : ‖(SB L * Theta L ((t : ℂ) * 1)) x c‖ ≤ B := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w : ZMod L, ‖SB L x w * Theta L ((t : ℂ) * 1) w c‖
        ≤ ∑ w : ZMod L, ‖SB L x w‖ * B := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [norm_mul]
          by_cases hw : SB L x w = 0
          · rw [hw, norm_zero, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (hΘ w hw) (norm_nonneg _)
      _ = B := by rw [← Finset.sum_mul, sum_norm_SB_apply_row L hL, one_mul]
  rw [edgeKer_sub_one_apply L hL hζ, norm_mul, norm_neg]
  calc ‖((s : ℂ) - t) * 1‖ * ‖(SB L * Theta L ((t : ℂ) * 1)) x c‖ ≤ (t - s) * B :=
        mul_le_mul (norm_sub_ofReal_mul_le hst hξ) hSB (norm_nonneg _) (by linarith)
    _ = 8 * exp 3 * (t - s) / ((1 - t) * ℓ) * exp (-((zdist L (x - c) : ℝ) / ℓ)) := by
        rw [hB]; ring

end TailSums

section TailCore

variable (L : ℕ) [NeZero L]

/-- The constant of the `ΘΘ`-term of (7.10). -/
noncomputable def cTailFour : ℝ := 2 ^ 15 * exp 2

theorem exp_half_le_exp_two : exp (1 / 2) ≤ exp 2 := exp_le_exp.2 (by norm_num)

theorem zdist_triangle_three (a₁ a₂ x y : ZMod L) :
    (zdist L (a₁ - a₂) : ℝ) ≤ zdist L (a₁ - x) + zdist L (a₂ - y) + zdist L (x - y) := by
  have h1 := zdist_add_le L (a₁ - x) (x - a₂)
  have h2 := zdist_add_le L (x - y) (y - a₂)
  have h3 : zdist L (y - a₂) = zdist L (a₂ - y) := by rw [← zdist_neg L, neg_sub]
  rw [sub_add_sub_cancel] at h1 h2
  rw [h3] at h2
  have : zdist L (a₁ - a₂) ≤ zdist L (a₁ - x) + zdist L (a₂ - y) + zdist L (x - y) := by omega
  exact_mod_cast this

theorem exp_neg_sqrt_div_anti {z ℓ ℓ' : ℝ} (hz : 0 ≤ z) (hℓ' : 0 < ℓ') (hℓℓ' : ℓ' ≤ ℓ) :
    exp (-√(z / ℓ')) ≤ exp (-√(z / ℓ)) := by
  rw [exp_le_exp, neg_le_neg_iff]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hz hℓ' hℓℓ')

/-- The `ΘΘ`-term of (7.10): `∑_{x,y} e^{-‖a₁-x‖/ℓ} e^{-‖a₂-y‖/ℓ} e^{-√(‖x-y‖/ℓ')}
≤ C ℓ² ((ℓ'/ℓ)² + (ℓ'/ℓ) e^{-d/(8ℓ)}) e^{-√(d/ℓ)}` for `d = ‖a₁ - a₂‖ ≥ ℓ`. -/
theorem sum_tail_qq_le {ℓ ℓ' : ℝ} (hℓ' : 1 / 2 ≤ ℓ') (hℓℓ' : ℓ' ≤ ℓ) (a₁ a₂ : ZMod L)
    (hd : ℓ ≤ zdist L (a₁ - a₂)) :
    ∑ x : ZMod L, ∑ y : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ))
        * exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
      ≤ cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-((zdist L (a₁ - a₂) : ℝ) / ℓ / 8)))
        * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ)) := by
  set d : ℝ := (zdist L (a₁ - a₂) : ℝ) with hdd
  have hℓ'0 : 0 < ℓ' := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hℓh : 1 / 2 ≤ ℓ := by linarith
  set E := exp (-√(d / ℓ)) with hE
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hσ0 : 0 < ℓ' / ℓ := div_pos hℓ'0 hℓ0
  have hC4 : 0 ≤ cTailFour := by unfold cTailFour; positivity
  have hex := exp_half_le_exp_two
  have hex0 : 0 ≤ exp (1 / 2 : ℝ) := (exp_pos _).le
  have hS1 := sum_exp_neg_zdist_half_le L hℓh
  rcases le_or_gt (16 * ℓ') ℓ with hσ | hσ
  · -- `ℓ' ≪ ℓ`
    set F := 64 * exp (1 / 2) * (ℓ' / ℓ) + exp 2 * exp (-(d / ℓ / 8)) with hF
    have hF0 : 0 ≤ F := by positivity
    have hpt : ∀ x y : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ))
        * exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
        ≤ F * E * (exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))
            * exp (-(1 / 2 * √((zdist L (x - y) : ℝ) / ℓ')))) := fun x y =>
      exp_three_le_short (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hℓ'0 hσ hd
        (zdist_triangle_three L a₁ a₂ x y)
    calc ∑ x : ZMod L, ∑ y : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ))
          * exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
        ≤ ∑ x : ZMod L, ∑ y : ZMod L, F * E * (exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))
            * exp (-(1 / 2 * √((zdist L (x - y) : ℝ) / ℓ')))) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
      _ = ∑ x : ZMod L, (F * E * exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2)))
            * ∑ y : ZMod L, exp (-(1 / 2 * √((zdist L (x - y) : ℝ) / ℓ'))) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ ≤ ∑ x : ZMod L, (F * E * exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))) * (36 * ℓ') := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (sum_exp_neg_half_sqrt_le L hℓ' x) (by positivity)
      _ = F * E * (36 * ℓ') * ∑ x : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ ≤ F * E * (36 * ℓ') * (8 * ℓ) :=
          mul_le_mul_of_nonneg_left (hS1 a₁) (by positivity)
      _ = 288 * ℓ ^ 2 * (ℓ' / ℓ) * F * E := by field_simp; ring
      _ ≤ cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8))) * E := by
          rw [hF]
          have h1 : 288 * (64 * exp (1 / 2)) ≤ cTailFour := by
            unfold cTailFour; nlinarith [exp_pos (2 : ℝ)]
          have h2 : 288 * exp 2 ≤ cTailFour := by
            unfold cTailFour; nlinarith [exp_pos (2 : ℝ)]
          have hA : 0 ≤ ℓ ^ 2 * (ℓ' / ℓ) ^ 2 * E := by positivity
          have hB : 0 ≤ ℓ ^ 2 * (ℓ' / ℓ) * exp (-(d / ℓ / 8)) * E := by positivity
          have e1 : 288 * ℓ ^ 2 * (ℓ' / ℓ) * (64 * exp (1 / 2) * (ℓ' / ℓ)
                + exp 2 * exp (-(d / ℓ / 8))) * E
              = 288 * (64 * exp (1 / 2)) * (ℓ ^ 2 * (ℓ' / ℓ) ^ 2 * E)
                + 288 * exp 2 * (ℓ ^ 2 * (ℓ' / ℓ) * exp (-(d / ℓ / 8)) * E) := by ring
          have e2 : cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8))) * E
              = cTailFour * (ℓ ^ 2 * (ℓ' / ℓ) ^ 2 * E)
                + cTailFour * (ℓ ^ 2 * (ℓ' / ℓ) * exp (-(d / ℓ / 8)) * E) := by ring
          rw [e1, e2]
          exact add_le_add (mul_le_mul_of_nonneg_right h1 hA) (mul_le_mul_of_nonneg_right h2 hB)
  · -- `ℓ' ≍ ℓ`
    have hpt : ∀ x y : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ))
        * exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
        ≤ exp (1 / 2) * E * (exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))
            * exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2))) := by
      intro x y
      have h0 := exp_neg_sqrt_div_anti (z := (zdist L (x - y) : ℝ)) (Nat.cast_nonneg _) hℓ'0 hℓℓ'
      have htri := zdist_triangle_three L a₁ a₂ x y
      have hk := exp_neg_mul_exp_neg_sqrt_le
        (u := (zdist L (a₁ - x) : ℝ) / ℓ + (zdist L (a₂ - y) : ℝ) / ℓ)
        (v := (zdist L (x - y) : ℝ) / ℓ) (w := d / ℓ) (by positivity) (by positivity)
        (by rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right htri hℓ0.le)
      calc exp (-((zdist L (a₁ - x) : ℝ) / ℓ)) * exp (-((zdist L (a₂ - y) : ℝ) / ℓ))
            * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
          ≤ exp (-((zdist L (a₁ - x) : ℝ) / ℓ)) * exp (-((zdist L (a₂ - y) : ℝ) / ℓ))
            * exp (-√((zdist L (x - y) : ℝ) / ℓ)) := by gcongr
        _ = exp (-((zdist L (a₁ - x) : ℝ) / ℓ + (zdist L (a₂ - y) : ℝ) / ℓ))
            * exp (-√((zdist L (x - y) : ℝ) / ℓ)) := by
              rw [← exp_add (-((zdist L (a₁ - x) : ℝ) / ℓ))]; congr 2; ring
        _ ≤ exp (1 / 2) * E * exp (-(((zdist L (a₁ - x) : ℝ) / ℓ
            + (zdist L (a₂ - y) : ℝ) / ℓ) / 2)) := hk
        _ = exp (1 / 2) * E * (exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))
            * exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2))) := by
              rw [← exp_add (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))]; congr 2; ring
    calc ∑ x : ZMod L, ∑ y : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ))
          * exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
        ≤ ∑ x : ZMod L, ∑ y : ZMod L, exp (1 / 2) * E * (exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2))
            * exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2))) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpt x y
      _ = exp (1 / 2) * E * ((∑ x : ZMod L, exp (-((zdist L (a₁ - x) : ℝ) / ℓ / 2)))
            * ∑ y : ZMod L, exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2))) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ ≤ exp (1 / 2) * E * ((8 * ℓ) * (8 * ℓ)) := by
          gcongr
          · exact hS1 a₁
          · exact hS1 a₂
      _ ≤ cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8))) * E := by
          have hσ16 : 1 / 16 < ℓ' / ℓ := by rw [lt_div_iff₀ hℓ0]; linarith
          have hσ2 : 1 ≤ 256 * (ℓ' / ℓ) ^ 2 := by nlinarith
          have h1 : 64 * exp (1 / 2) * 256 ≤ cTailFour := by
            unfold cTailFour; nlinarith [exp_pos (2 : ℝ)]
          have hB : 0 ≤ ℓ ^ 2 * (ℓ' / ℓ) * exp (-(d / ℓ / 8)) * E := by positivity
          have e1 : exp (1 / 2) * E * ((8 * ℓ) * (8 * ℓ)) = 64 * exp (1 / 2) * (ℓ ^ 2 * E) := by
            ring
          have e2 : cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8))) * E
              = cTailFour * (ℓ' / ℓ) ^ 2 * (ℓ ^ 2 * E)
                + cTailFour * (ℓ ^ 2 * (ℓ' / ℓ) * exp (-(d / ℓ / 8)) * E) := by ring
          rw [e1, e2]
          have hlE : 0 ≤ ℓ ^ 2 * E := by positivity
          have : 64 * exp (1 / 2) ≤ cTailFour * (ℓ' / ℓ) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right this hlE, mul_nonneg hC4 hB]

theorem sum_norm_one_mul (a : ZMod L) (f : ZMod L → ℝ) :
    ∑ x : ZMod L, ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) a x‖ * f x = f a := by
  simp [Matrix.one_apply, apply_ite]

/-- The single-`Θ` terms `V^{(2)}, V^{(4)}` of (7.10): `∑_y e^{-‖a₂-y‖/ℓ} e^{-√(‖a₁-y‖/ℓ')}
≤ 8 e^{1/2} ℓ e^{-√(‖a₁-a₂‖/ℓ)}`. -/
theorem sum_tail_pq_le {ℓ ℓ' : ℝ} (hℓ' : 1 / 2 ≤ ℓ') (hℓℓ' : ℓ' ≤ ℓ) (a₁ a₂ : ZMod L) :
    ∑ y : ZMod L, exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (a₁ - y) : ℝ) / ℓ'))
      ≤ 8 * exp (1 / 2) * ℓ * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ)) := by
  have hℓ'0 : 0 < ℓ' := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hpt : ∀ y : ZMod L, exp (-((zdist L (a₂ - y) : ℝ) / ℓ))
      * exp (-√((zdist L (a₁ - y) : ℝ) / ℓ'))
      ≤ exp (1 / 2) * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ))
        * exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2)) := by
    intro y
    have h0 := exp_neg_sqrt_div_anti (z := (zdist L (a₁ - y) : ℝ)) (Nat.cast_nonneg _) hℓ'0 hℓℓ'
    have htri := zdist_sub_le_add L a₁ a₂ y
    have hk := exp_neg_mul_exp_neg_sqrt_le (u := (zdist L (a₂ - y) : ℝ) / ℓ)
      (v := (zdist L (a₁ - y) : ℝ) / ℓ) (w := (zdist L (a₁ - a₂) : ℝ) / ℓ) (by positivity)
      (by positivity)
      (by rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hℓ0.le)
    calc exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (a₁ - y) : ℝ) / ℓ'))
        ≤ exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (a₁ - y) : ℝ) / ℓ)) := by
          gcongr
      _ ≤ _ := hk
  calc ∑ y : ZMod L, exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) * exp (-√((zdist L (a₁ - y) : ℝ) / ℓ'))
      ≤ ∑ y : ZMod L, exp (1 / 2) * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ))
        * exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2)) := Finset.sum_le_sum fun y _ => hpt y
    _ = exp (1 / 2) * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ))
        * ∑ y : ZMod L, exp (-((zdist L (a₂ - y) : ℝ) / ℓ / 2)) := by rw [Finset.mul_sum]
    _ ≤ exp (1 / 2) * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ)) * (8 * ℓ) :=
        mul_le_mul_of_nonneg_left (sum_exp_neg_zdist_half_le L (by linarith) a₂) (by positivity)
    _ = 8 * exp (1 / 2) * ℓ * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ)) := by ring

/-- **The kernel estimate behind Lemma 7.2**: with `|K_{xc}| ≤ δ_{xc} + κ e^{-‖x-c‖/ℓ}` on
both edges, and `d = ‖a₁ - a₂‖ ≥ ℓ ≥ ℓ' ≥ 1/2`,
`∑_{x,y} |K_{a₁x}| |K_{a₂y}| e^{-√(‖x-y‖/ℓ')}
  ≤ (1 + 16e^{1/2} κℓ + C (κℓ)² ((ℓ'/ℓ)² + (ℓ'/ℓ) e^{-d/(8ℓ)})) e^{-√(d/ℓ)}`. -/
theorem sum_tail_core_le {ℓ ℓ' κ : ℝ} (hℓ' : 1 / 2 ≤ ℓ') (hℓℓ' : ℓ' ≤ ℓ) (hκ : 0 ≤ κ)
    (a₁ a₂ : ZMod L) (hd : ℓ ≤ zdist L (a₁ - a₂)) :
    ∑ x : ZMod L, ∑ y : ZMod L,
        (‖(1 : Matrix (ZMod L) (ZMod L) ℂ) a₁ x‖ + κ * exp (-((zdist L (a₁ - x) : ℝ) / ℓ)))
        * (‖(1 : Matrix (ZMod L) (ZMod L) ℂ) a₂ y‖ + κ * exp (-((zdist L (a₂ - y) : ℝ) / ℓ)))
        * exp (-√((zdist L (x - y) : ℝ) / ℓ'))
      ≤ (1 + 16 * exp (1 / 2) * (κ * ℓ) + cTailFour * (κ * ℓ) ^ 2
          * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-((zdist L (a₁ - a₂) : ℝ) / ℓ / 8))))
        * exp (-√((zdist L (a₁ - a₂) : ℝ) / ℓ)) := by
  set O : ZMod L → ZMod L → ℝ := fun a x => ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) a x‖ with hO
  set e₁ : ZMod L → ℝ := fun x => exp (-((zdist L (a₁ - x) : ℝ) / ℓ)) with he₁
  set e₂ : ZMod L → ℝ := fun y => exp (-((zdist L (a₂ - y) : ℝ) / ℓ)) with he₂
  set F : ZMod L → ZMod L → ℝ := fun x y => exp (-√((zdist L (x - y) : ℝ) / ℓ')) with hF
  have hℓ'0 : 0 < ℓ' := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hexp : ∀ x y, (O a₁ x + κ * e₁ x) * (O a₂ y + κ * e₂ y) * F x y
      = O a₁ x * (O a₂ y * F x y) + O a₁ x * (κ * e₂ y * F x y)
        + κ * (e₁ x * (O a₂ y * F x y)) + κ ^ 2 * (e₁ x * e₂ y * F x y) := by
    intro x y; ring
  change ∑ x : ZMod L, ∑ y : ZMod L, (O a₁ x + κ * e₁ x) * (O a₂ y + κ * e₂ y) * F x y ≤ _
  simp_rw [hexp, Finset.sum_add_distrib]
  have h1 : ∑ x : ZMod L, ∑ y : ZMod L, O a₁ x * (O a₂ y * F x y) = F a₁ a₂ := by
    simp_rw [← Finset.mul_sum, hO, sum_norm_one_mul L a₂ (F _)]
    exact sum_norm_one_mul L a₁ (fun x => F x a₂)
  have h2 : ∑ x : ZMod L, ∑ y : ZMod L, O a₁ x * (κ * e₂ y * F x y)
      = κ * ∑ y : ZMod L, e₂ y * F a₁ y := by
    simp_rw [← Finset.mul_sum, hO]
    rw [sum_norm_one_mul L a₁ (fun x => ∑ y : ZMod L, κ * e₂ y * F x y), Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h3 : ∑ x : ZMod L, ∑ y : ZMod L, κ * (e₁ x * (O a₂ y * F x y))
      = κ * ∑ x : ZMod L, e₁ x * F x a₂ := by
    simp_rw [← Finset.mul_sum, hO, sum_norm_one_mul L a₂ (F _)]
  have h4 : ∑ x : ZMod L, ∑ y : ZMod L, κ ^ 2 * (e₁ x * e₂ y * F x y)
      = κ ^ 2 * ∑ x : ZMod L, ∑ y : ZMod L, e₁ x * e₂ y * F x y := by
    simp_rw [← Finset.mul_sum]
  rw [h1, h2, h3, h4]
  set d : ℝ := (zdist L (a₁ - a₂) : ℝ) with hdd
  set E := exp (-√(d / ℓ)) with hE
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hT1 : F a₁ a₂ ≤ E := exp_neg_sqrt_div_anti (Nat.cast_nonneg _) hℓ'0 hℓℓ'
  have hT2 : ∑ y : ZMod L, e₂ y * F a₁ y ≤ 8 * exp (1 / 2) * ℓ * E :=
    sum_tail_pq_le L hℓ' hℓℓ' a₁ a₂
  have hT3 : ∑ x : ZMod L, e₁ x * F x a₂ ≤ 8 * exp (1 / 2) * ℓ * E := by
    have h := sum_tail_pq_le L hℓ' hℓℓ' a₂ a₁
    have e : (zdist L (a₂ - a₁) : ℝ) = d := by rw [hdd, ← zdist_neg L (a₁ - a₂), neg_sub]
    rw [e] at h
    refine le_of_eq_of_le (Finset.sum_congr rfl fun x _ => ?_) h
    simp only [he₁, hF]
    rw [← zdist_neg L (x - a₂), neg_sub]
  have hT4 : ∑ x : ZMod L, ∑ y : ZMod L, e₁ x * e₂ y * F x y
      ≤ cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8))) * E :=
    sum_tail_qq_le L hℓ' hℓℓ' a₁ a₂ hd
  have hκ2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  calc F a₁ a₂ + κ * ∑ y : ZMod L, e₂ y * F a₁ y + κ * ∑ x : ZMod L, e₁ x * F x a₂
        + κ ^ 2 * ∑ x : ZMod L, ∑ y : ZMod L, e₁ x * e₂ y * F x y
      ≤ E + κ * (8 * exp (1 / 2) * ℓ * E) + κ * (8 * exp (1 / 2) * ℓ * E)
        + κ ^ 2 * (cTailFour * ℓ ^ 2 * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8))) * E) := by
        gcongr
    _ = (1 + 16 * exp (1 / 2) * (κ * ℓ) + cTailFour * (κ * ℓ) ^ 2
          * ((ℓ' / ℓ) ^ 2 + ℓ' / ℓ * exp (-(d / ℓ / 8)))) * E := by ring

end TailCore

/-! ### Lemma 7.2 -/

/-- The constant of Lemma 7.2 (with `c₇ = 8e³` the constant of the long-edge kernel). -/
noncomputable def cTail : ℝ :=
  1 + 16 * exp (1 / 2) * (8 * exp 3) + cTailFour * (8 * exp 3) ^ 2

section Lemma72

variable (L : ℕ) [NeZero L]

/-- `ℓ_t/ℓ_s ≤ ℓ_sη_s/(ℓ_tη_t)`, i.e. `ℓ_t² η_t ≤ ℓ_s² η_s`. -/
theorem ellHat_ratio_le_ratio (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    ellHat L (t : ℂ) / ellHat L (s : ℂ)
      ≤ (1 - s) * ellHat L (s : ℂ) / ((1 - t) * ellHat L (t : ℂ)) := by
  have hs := ellHat_real_pos L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL (hs0.trans hst) ht1
  have h1t : 0 < 1 - t := by linarith
  have h := sqrt_one_sub_mul_ellHat_le L ht1 (ζ := (s : ℂ))
    (by rw [norm_one_sub_ofReal (by linarith)]; linarith)
  rw [norm_one_sub_ofReal (by linarith)] at h
  have h2 := mul_self_le_mul_self (by positivity) h
  have e1 : √(1 - t) * ellHat L (t : ℂ) * (√(1 - t) * ellHat L (t : ℂ))
      = (1 - t) * ellHat L (t : ℂ) ^ 2 := by
    rw [show √(1 - t) * ellHat L (t : ℂ) * (√(1 - t) * ellHat L (t : ℂ))
      = (√(1 - t) * √(1 - t)) * ellHat L (t : ℂ) ^ 2 by ring, Real.mul_self_sqrt h1t.le]
  have e2 : √(1 - s) * ellHat L (s : ℂ) * (√(1 - s) * ellHat L (s : ℂ))
      = (1 - s) * ellHat L (s : ℂ) ^ 2 := by
    rw [show √(1 - s) * ellHat L (s : ℂ) * (√(1 - s) * ellHat L (s : ℂ))
      = (√(1 - s) * √(1 - s)) * ellHat L (s : ℂ) ^ 2 by ring,
      Real.mul_self_sqrt (by linarith)]
  rw [e1, e2] at h2
  rw [div_le_div_iff₀ hs (mul_pos h1t ht)]
  nlinarith

/-- **Lemma 7.2 (7.2)**, explicit form.  Let `n = 2`, `σ = (+,-)` (so `ξ = (1, 1)`, see
`xiOf_mSigma_true_false`), `0 ≤ s ≤ t < 1`, `t > 0`, and let
`|A_b| ≤ T_{s,D}(‖b₁ - b₂‖)` ((5.27), the paper's `T_s(b₁ - b₂) + W^{-D}`).  Then for
`d = ‖a₁ - a₂‖ ≥ ℓ_t`
`|(U_{s,t,σ} ∘ A)_a| ≤ C (1 + (ℓ_t/ℓ_s) e^{-d/(8ℓ_t)}) T_t(d) + (η_s/η_t)² W^{-D}`,
with `T_t(d) = (W ℓ_t η_t)^{-2} e^{-√(d/ℓ_t)}` as in (7.3). -/
theorem norm_Uker_tail_le (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht0 : 0 < t)
    (ht1 : t < 1) {W D : ℝ} (hW : 0 < W) {A : LoopArg L 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ tailT W (ellHat L (s : ℂ)) (1 - s) D (zdist L (b 0 - b 1)))
    (a : LoopArg L 2) (hd : ellHat L (t : ℂ) ≤ zdist L (a 0 - a 1)) :
    ‖Uker L (fun _ => 1) s t A a‖ ≤
      cTail * (1 + ellHat L (t : ℂ) / ellHat L (s : ℂ)
          * exp (-((zdist L (a 0 - a 1) : ℝ) / ellHat L (t : ℂ) / 8)))
        * (((W * ellHat L (t : ℂ) * (1 - t)) ^ 2)⁻¹
          * exp (-√((zdist L (a 0 - a 1) : ℝ) / ellHat L (t : ℂ))))
      + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D) := by
  set ℓs := ellHat L (s : ℂ) with hℓs
  set ℓt := ellHat L (t : ℂ) with hℓt
  set d : ℝ := (zdist L (a 0 - a 1) : ℝ) with hdd
  set K := edgeKer L 1 s t with hK
  set q := (t - s) * (1 - t)⁻¹ with hq
  set κ := 8 * exp 3 * (t - s) / ((1 - t) * ℓt) with hκ
  set F : ZMod L → ZMod L → ℝ := fun x y => exp (-√((zdist L (x - y) : ℝ) / ℓs)) with hF
  set Ps := ((W * ℓs * (1 - s)) ^ 2)⁻¹ with hPs
  have hsh := half_le_ellHat_real L hL hs0 (hst.trans_lt ht1)
  have hth := half_le_ellHat_real L hL ht0.le ht1
  have hs := ellHat_real_pos L hL hs0 (hst.trans_lt ht1)
  have ht := ellHat_real_pos L hL ht0.le ht1
  have h1t : 0 < 1 - t := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hsl : ℓs ≤ ℓt := ellHat_real_mono L hst ht1
  have hsne : ℓs ≠ 0 := ne_of_gt hs
  have htne : ℓt ≠ 0 := ne_of_gt ht
  have h1tne : (1 : ℝ) - t ≠ 0 := ne_of_gt h1t
  have h1sne : (1 : ℝ) - s ≠ 0 := ne_of_gt h1s
  have hκ0 : 0 ≤ κ :=
    div_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_pos h1t ht).le
  have hPs0 : 0 ≤ Ps := by positivity
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  -- entrywise bound on the edge kernel
  have hKe : ∀ x c, ‖K x c‖ ≤ ‖(1 : Matrix (ZMod L) (ZMod L) ℂ) x c‖
      + κ * exp (-((zdist L (x - c) : ℝ) / ℓt)) := by
    intro x c
    have e : K x c = (1 : Matrix (ZMod L) (ZMod L) ℂ) x c + (K - 1) x c := by
      rw [Matrix.sub_apply]; ring
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      (norm_edgeKer_one_sub_one_le L hL hst ht0 ht1 x c))
  -- row sums of the edge kernel
  have hrow : ∀ x, ∑ c : ZMod L, ‖K x c‖ ≤ (1 - s) / (1 - t) := by
    intro x
    have h := sum_norm_edgeKer_row_le L hL (ξ := 1) (s := s) (t := t)
      (norm_ofReal_mul_lt_one ht0.le ht1 (by simp)) x
    have e1 : ‖((s : ℂ) - t) * 1‖ = t - s := by
      rw [mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]; ring
    have e2 : ‖(t : ℂ) * 1‖ = t := by
      rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    rw [e1, e2, one_add_row_eq ht1] at h
    exact h
  -- the sum over `b`
  have hstart : ‖Uker L (fun _ => 1) s t A a‖
      ≤ Ps * ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ * F x y
        + W ^ (-D) * ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ := by
    rw [Uker_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b : LoopArg L 2, ‖(∏ i, edgeKer L ((fun _ => (1 : ℂ)) i) s t (a i) (b i)) * A b‖
        ≤ ∑ b : LoopArg L 2, (Ps * (‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ * F (b 0) (b 1))
            + W ^ (-D) * (‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖)) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, Fin.prod_univ_two, norm_mul]
          have hAb := hA b
          rw [tailT] at hAb
          have hkk : 0 ≤ ‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ := by positivity
          calc ‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ * ‖A b‖
              ≤ ‖K (a 0) (b 0)‖ * ‖K (a 1) (b 1)‖ * (Ps * F (b 0) (b 1) + W ^ (-D)) :=
                mul_le_mul_of_nonneg_left hAb hkk
            _ = _ := by ring
      _ = Ps * ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ * F x y
            + W ^ (-D) * ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_fin_two_fun L (fun x y => ‖K (a 0) x‖ * ‖K (a 1) y‖ * F x y),
            sum_fin_two_fun L (fun x y => ‖K (a 0) x‖ * ‖K (a 1) y‖)]
  refine hstart.trans (add_le_add ?_ ?_)
  · -- the tail part
    have hcore := sum_tail_core_le L hsh hsl hκ0 (a 0) (a 1) hd
    have hmono : ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖ * F x y
        ≤ ∑ x : ZMod L, ∑ y : ZMod L,
          (‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x‖ + κ * exp (-((zdist L (a 0 - x) : ℝ) / ℓt)))
          * (‖(1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y‖
            + κ * exp (-((zdist L (a 1 - y) : ℝ) / ℓt)))
          * exp (-√((zdist L (x - y) : ℝ) / ℓs)) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hKe _ _) (hKe _ _) (norm_nonneg _)
        (by positivity)) (exp_pos _).le
    refine (mul_le_mul_of_nonneg_left (hmono.trans hcore) hPs0).trans ?_
    -- algebra with the scales
    set R := (1 - s) * ℓs / ((1 - t) * ℓt) with hR
    set σ := ℓs / ℓt with hσ
    set ee := exp (-(d / ℓt / 8)) with hee
    set E := exp (-√(d / ℓt)) with hE
    have hR1 : 1 ≤ R := one_le_ratio L hL hs0 hst ht1
    have hρR : ℓt / ℓs ≤ R := ellHat_ratio_le_ratio L hL hs0 hst ht1
    have hqR : q ≤ ℓt / ℓs * R := row_le_ratio L hL hs0 hst ht1
    have hq0 : 0 ≤ q := mul_nonneg (by linarith) (inv_nonneg.2 h1t.le)
    have hσ0 : 0 < σ := div_pos hs ht
    have hρσ : ℓt / ℓs * σ = 1 := by rw [hσ]; field_simp
    have hqσ : q * σ ≤ R := by
      calc q * σ ≤ ℓt / ℓs * R * σ := mul_le_mul_of_nonneg_right hqR hσ0.le
        _ = R := by rw [mul_right_comm, hρσ, one_mul]
    have hqR2 : q ≤ R ^ 2 := by
      calc q ≤ ℓt / ℓs * R := hqR
        _ ≤ R * R := mul_le_mul_of_nonneg_right hρR (by linarith)
        _ = R ^ 2 := by ring
    have hκℓ : κ * ℓt = 8 * exp 3 * q := by rw [hκ, hq]; field_simp
    have hPsR : Ps * R ^ 2 = ((W * ℓt * (1 - t)) ^ 2)⁻¹ := by
      rw [hPs, hR]; field_simp
    have hee0 : 0 ≤ ee := (exp_pos _).le
    have hE0 : 0 ≤ E := (exp_pos _).le
    have hC4 : 0 ≤ cTailFour := by unfold cTailFour; positivity
    set c₇ := 8 * exp 3 with hc₇
    have hc₇0 : 0 ≤ c₇ := by positivity
    rw [hκℓ]
    -- bound the bracket by `R² cTail (1 + σ⁻¹ ee)`
    have hbr : 1 + 16 * exp (1 / 2) * (c₇ * q) + cTailFour * (c₇ * q) ^ 2 * (σ ^ 2 + σ * ee)
        ≤ R ^ 2 * (cTail * (1 + ℓt / ℓs * ee)) := by
      have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
      have ht1' : 16 * exp (1 / 2) * (c₇ * q) ≤ 16 * exp (1 / 2) * c₇ * R ^ 2 := by
        have : 0 ≤ 16 * exp (1 / 2) * c₇ := by positivity
        have e : 16 * exp (1 / 2) * (c₇ * q) = (16 * exp (1 / 2) * c₇) * q := by ring
        rw [e]; exact mul_le_mul_of_nonneg_left hqR2 this
      have hqσ0 : 0 ≤ q * σ := mul_nonneg hq0 hσ0.le
      have hqσ2 : (q * σ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hqσ0 hqσ 2
      have ht2 : cTailFour * (c₇ * q) ^ 2 * σ ^ 2 ≤ cTailFour * c₇ ^ 2 * R ^ 2 := by
        have e : cTailFour * (c₇ * q) ^ 2 * σ ^ 2 = cTailFour * c₇ ^ 2 * (q * σ) ^ 2 := by ring
        rw [e]; exact mul_le_mul_of_nonneg_left hqσ2 (by positivity)
      have ht3 : cTailFour * (c₇ * q) ^ 2 * (σ * ee)
          ≤ cTailFour * c₇ ^ 2 * R ^ 2 * (ℓt / ℓs * ee) := by
        have e : cTailFour * (c₇ * q) ^ 2 * (σ * ee)
            = cTailFour * c₇ ^ 2 * (q * σ) ^ 2 * (ℓt / ℓs * ee) := by
          have hsq : σ ^ 2 * (ℓt / ℓs) = σ := by
            rw [sq, mul_assoc, mul_comm σ (ℓt / ℓs), hρσ, mul_one]
          calc cTailFour * (c₇ * q) ^ 2 * (σ * ee)
              = cTailFour * c₇ ^ 2 * q ^ 2 * (σ ^ 2 * (ℓt / ℓs)) * ee := by rw [hsq]; ring
            _ = cTailFour * c₇ ^ 2 * (q * σ) ^ 2 * (ℓt / ℓs * ee) := by ring
        rw [e]
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqσ2 (by positivity)) ?_
        exact mul_nonneg (div_nonneg ht.le hs.le) hee0
      have hsplit : R ^ 2 * (cTail * (1 + ℓt / ℓs * ee))
          = R ^ 2 + 16 * exp (1 / 2) * c₇ * R ^ 2 + cTailFour * c₇ ^ 2 * R ^ 2
            + R ^ 2 * cTail * (ℓt / ℓs * ee) := by
        rw [cTail]; ring
      have hlast : cTailFour * c₇ ^ 2 * R ^ 2 * (ℓt / ℓs * ee)
          ≤ R ^ 2 * cTail * (ℓt / ℓs * ee) := by
        have hc : cTailFour * c₇ ^ 2 ≤ cTail := by
          unfold cTail; have : 0 ≤ 16 * exp (1 / 2) * (8 * exp 3) := by positivity
          rw [hc₇]; linarith
        have h0 : 0 ≤ R ^ 2 * (ℓt / ℓs * ee) :=
          mul_nonneg (by positivity) (mul_nonneg (div_nonneg ht.le hs.le) hee0)
        have e1 : cTailFour * c₇ ^ 2 * R ^ 2 * (ℓt / ℓs * ee)
            = (cTailFour * c₇ ^ 2) * (R ^ 2 * (ℓt / ℓs * ee)) := by ring
        have e2 : R ^ 2 * cTail * (ℓt / ℓs * ee) = cTail * (R ^ 2 * (ℓt / ℓs * ee)) := by ring
        rw [e1, e2]; exact mul_le_mul_of_nonneg_right hc h0
      have e3 : cTailFour * (c₇ * q) ^ 2 * (σ ^ 2 + σ * ee)
          = cTailFour * (c₇ * q) ^ 2 * σ ^ 2 + cTailFour * (c₇ * q) ^ 2 * (σ * ee) := by ring
      rw [hsplit, e3]
      linarith
    calc Ps * ((1 + 16 * exp (1 / 2) * (c₇ * q) + cTailFour * (c₇ * q) ^ 2
          * ((ℓs / ℓt) ^ 2 + ℓs / ℓt * exp (-(d / ℓt / 8)))) * exp (-√(d / ℓt)))
        = Ps * (1 + 16 * exp (1 / 2) * (c₇ * q) + cTailFour * (c₇ * q) ^ 2 * (σ ^ 2 + σ * ee))
            * E := by rw [hσ, hee, hE]; ring
      _ ≤ Ps * (R ^ 2 * (cTail * (1 + ℓt / ℓs * ee))) * E := by gcongr
      _ = cTail * (1 + ℓt / ℓs * ee) * ((Ps * R ^ 2) * E) := by ring
      _ = cTail * (1 + ℓt / ℓs * ee) * (((W * ℓt * (1 - t)) ^ 2)⁻¹ * E) := by rw [hPsR]
  · -- the `W^{-D}` part
    have hprod : ∑ x : ZMod L, ∑ y : ZMod L, ‖K (a 0) x‖ * ‖K (a 1) y‖
        = (∑ x : ZMod L, ‖K (a 0) x‖) * ∑ y : ZMod L, ‖K (a 1) y‖ := by
      rw [Finset.sum_mul_sum]
    rw [hprod]
    have h0 : 0 ≤ ∑ x : ZMod L, ‖K (a 0) x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    calc W ^ (-D) * ((∑ x : ZMod L, ‖K (a 0) x‖) * ∑ y : ZMod L, ‖K (a 1) y‖)
        ≤ W ^ (-D) * ((1 - s) / (1 - t) * ((1 - s) / (1 - t))) := by
          gcongr
          · exact hrow _
          · exact hrow _
      _ = ((1 - s) / (1 - t)) ^ 2 * W ^ (-D) := by ring

theorem cTail_nonneg : 0 ≤ cTail := by
  unfold cTail cTailFour; positivity

/-- **Lemma 7.2 (7.2)** in the paper's form: for `‖a₁ - a₂‖ ≥ ℓ*_t = (log W)^{3/2} ℓ_t`
(`W ≥ e`), `|(U_{s,t,(+,-)} ∘ A)_a| ≤ C (1 + 2L e^{-(log W)^{3/2}/8}) T_t(a₁ - a₂)
+ (η_s/η_t)² W^{-D}`.  The factor `2L e^{-(log W)^{3/2}/8}` is `O(1)` (indeed `→ 0`) as soon
as `L ≤ W^C`, so this is the paper's `≺ T_t(a₁ - a₂) + W^{-D}(η_s/η_t)²` with an explicit
constant. -/
theorem norm_Uker_tail_le_ellStar (hL : 3 ≤ L) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht0 : 0 < t) (ht1 : t < 1) {W D : ℝ} (hW : exp 1 ≤ W) {A : LoopArg L 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ tailT W (ellHat L (s : ℂ)) (1 - s) D (zdist L (b 0 - b 1)))
    (a : LoopArg L 2) (hd : ellStar W (ellHat L (t : ℂ)) ≤ zdist L (a 0 - a 1)) :
    ‖Uker L (fun _ => 1) s t A a‖ ≤
      cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8)))
        * (((W * ellHat L (t : ℂ) * (1 - t)) ^ 2)⁻¹
          * exp (-√((zdist L (a 0 - a 1) : ℝ) / ellHat L (t : ℂ))))
      + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D) := by
  have hW0 : 0 < W := lt_of_lt_of_le (exp_pos 1) hW
  have hlog : 1 ≤ log W := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hW
  have hlog32 : 1 ≤ log W ^ (3 / 2 : ℝ) := Real.one_le_rpow hlog (by norm_num)
  have ht := ellHat_real_pos L hL ht0.le ht1
  have hsh := half_le_ellHat_real L hL hs0 (hst.trans_lt ht1)
  have hstar : ellHat L (t : ℂ) ≤ ellStar W (ellHat L (t : ℂ)) := by
    unfold ellStar; nlinarith
  have h := norm_Uker_tail_le L hL hs0 hst ht0 ht1 hW0 hA a (hstar.trans hd)
  refine h.trans (add_le_add ?_ le_rfl)
  have hT : 0 ≤ ((W * ellHat L (t : ℂ) * (1 - t)) ^ 2)⁻¹
      * exp (-√((zdist L (a 0 - a 1) : ℝ) / ellHat L (t : ℂ))) := by positivity
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ cTail_nonneg) hT
  have hratio : ellHat L (t : ℂ) / ellHat L (s : ℂ) ≤ 2 * L := by
    rw [div_le_iff₀ (by linarith)]
    have : ellHat L (t : ℂ) ≤ L := by unfold ellHat; exact min_le_right _ _
    nlinarith
  have hexp : exp (-((zdist L (a 0 - a 1) : ℝ) / ellHat L (t : ℂ) / 8))
      ≤ exp (-(log W ^ (3 / 2 : ℝ) / 8)) := by
    rw [exp_le_exp, neg_le_neg_iff]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    rw [le_div_iff₀ ht]; unfold ellStar at hd; linarith
  have h0 : 0 ≤ ellHat L (t : ℂ) / ellHat L (s : ℂ) := div_nonneg ht.le (by linarith)
  have := mul_le_mul hratio hexp (exp_pos _).le (by positivity)
  linarith

/-- `σ = (+, -)` gives the edge parameters `ξ = (m m̄, m̄ m) = (1, 1)`. -/
theorem xiOf_mSigma_true_false {E : ℝ} (hE : |E| ≤ 2) :
    xiOf (n := 2) (mSigma E) ![true, false] = fun _ => 1 := by
  have h1 : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj', norm_mE hE]; simp
  funext i
  fin_cases i
  · simp [xiOf, mSigma, h1]
  · simp [xiOf, mSigma]; rw [mul_comm]; exact h1

/-- **Lemma 7.2 (7.2)** with the paper's `U_{s,t,σ}`, `σ = (+,-)`, `|E| ≤ 2`. -/
theorem norm_Uker_tail_le_sigma (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {s t : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht0 : 0 < t) (ht1 : t < 1) {W D : ℝ} (hW : exp 1 ≤ W)
    {A : LoopArg L 2 → ℂ}
    (hA : ∀ b, ‖A b‖ ≤ tailT W (ellHat L (s : ℂ)) (1 - s) D (zdist L (b 0 - b 1)))
    (a : LoopArg L 2) (hd : ellStar W (ellHat L (t : ℂ)) ≤ zdist L (a 0 - a 1)) :
    ‖Uker L (xiOf (mSigma E) ![true, false]) s t A a‖ ≤
      cTail * (1 + 2 * L * exp (-(log W ^ (3 / 2 : ℝ) / 8)))
        * (((W * ellHat L (t : ℂ) * (1 - t)) ^ 2)⁻¹
          * exp (-√((zdist L (a 0 - a 1) : ℝ) / ellHat L (t : ℂ))))
      + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D) := by
  rw [xiOf_mSigma_true_false hE]
  exact norm_Uker_tail_le_ellStar L hL hs0 hst ht0 ht1 hW hA a hd

end Lemma72

end RBM
