/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.DimsExample
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The loop-level modulus from the resolvent increment, and the deterministic moduli

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.43)/(5.46)/(5.48); (5.27) for `T_{u,D}`.

## Main results

### §1 Telescoping a loop product

* `RBM.norm_gloopProd_sub_le` — a loop product of `n` resolvents moves by at most `n K^n` times
  the largest move of a single resolvent (`A₁B₁ - A₂B₂ = (A₁-A₂)B₁ + A₂(B₁-B₂)`, by induction
  on the charge/label lists).  **Both** `H` and `z` are allowed to move, which is what the flow
  `H_u = √u X`, `z = z_u` does — `RBM.gchain_eq_add_sum_gchainMixed` only moves `z`.

### §2 `resolvent → loop`

* `RBM.norm_Gsig_sub_le_norm_green_sub` — both charges move by the same amount, since
  `G(-) = G(+)†` and `‖·ᴴ‖ = ‖·‖` for the `ℓ²` operator norm.
* `RBM.norm_gloop_sub_le` — `|L_{σ,a}(H₁,z₁) - L_{σ,a}(H₂,z₂)| ≤ LW·n·K^n·‖G₁-G₂‖`.

### §9 The two purely deterministic moduli

* `RBM.abs_inv_ellHat_sub_le` (`|(ℓ̂_v)⁻¹ - (ℓ̂_w)⁻¹| ≤ |v-w|/(2√(1-t₀))`, via
  `RBM.inv_ellHat_ofReal`: `(ℓ̂_u)⁻¹ = max(√(1-u), L⁻¹)`) and `RBM.abs_inv_etaT_sub_le`
  (`|η_v⁻¹ - η_w⁻¹| ≤ |v-w| η_{t₀}⁻²`).  Both `γ = 1`, both `ω`-free, both allow `s = 0`.

### §10 The modulus of `u ↦ T_{u,D}(ℓ)`

* `RBM.abs_tailT_sub_le`: the modulus of `u ↦ T_{u,D}(ℓ)`, uniform in `ℓ ∈ [0, L]`, with
  constant `RBM.tailLip`.

## Deviations

**Crude combinatorial constants.**  `RBM.norm_gloop_sub_le` pays a factor `L·W` for the trace
(`|⟨M⟩| ≤ (LW)‖M‖_op`) where the paper's (5.2)-style bookkeeping would give `W^{-n+1}`, and
`RBM.norm_gloopProd_sub_le` bounds `‖E_a‖ ≤ 1` rather than `W⁻¹`.  Both only inflate the
constant by a bounded power of `N`; the constants are not optimized.
-/

namespace RBM

open Matrix Filter
open scoped Matrix.Norms.L2Operator

section SqrtFlowLip

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

end SqrtFlowLip

/-! ### 1. Telescoping a loop product -/

section Telescope

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `|⟨M⟩| ≤ (LW) ‖M‖_op`. -/
theorem norm_trace_le_card_mul {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) : ‖Matrix.trace M‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : n, ‖M.diag i‖ ≤ ∑ _i : n, ‖M‖ :=
        Finset.sum_le_sum fun i _ => norm_apply_le_l2_opNorm M i i
    _ = (Fintype.card n : ℝ) * ‖M‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem norm_Eblk_le_one'' (b : ZMod L) : ‖Eblk L W b‖ ≤ 1 := by
  refine (norm_Eblk_le (W := W) b).trans ?_
  have hW : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  rw [inv_le_one_iff₀]
  right; exact hW

variable {H₁ H₂ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z₁ z₂ : ℂ}

/-- `‖∏ G(σ_i) E_{a_i}‖ ≤ K^n` when every `‖G(σ)‖ ≤ K` and `‖E_a‖ ≤ 1`. -/
theorem norm_gloopProd_le_pow {K : ℝ} (hK : 0 ≤ K)
    (hG : ∀ s, ‖Gsig H₁ z₁ s‖ ≤ K) :
    ∀ (σ : List Bool) (a : List (ZMod L)), σ.length = a.length →
      ‖gloopProd L W H₁ z₁ ⟨σ, a⟩‖ ≤ K ^ σ.length := by
  intro σ
  induction σ with
  | nil =>
    intro a h
    obtain rfl : a = [] := List.eq_nil_of_length_eq_zero h.symm
    simp
  | cons s σ ih =>
    intro a h
    cases a with
    | nil => simp at h
    | cons b a =>
      have h' : σ.length = a.length := by simpa using h
      rw [gloopProd_cons, List.length_cons, pow_succ']
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      have hE : ‖Eblk L W b‖ ≤ 1 := norm_Eblk_le_one'' b
      have hQ := ih a h'
      have hpow : (0 : ℝ) ≤ K ^ σ.length := pow_nonneg hK _
      have h1 : ‖Gsig H₁ z₁ s‖ * ‖Eblk L W b‖ ≤ K * 1 :=
        mul_le_mul (hG s) hE (norm_nonneg _) hK
      calc ‖Gsig H₁ z₁ s‖ * ‖Eblk L W b‖ * ‖gloopProd L W H₁ z₁ ⟨σ, a⟩‖
          ≤ K * 1 * K ^ σ.length :=
            mul_le_mul h1 hQ (norm_nonneg _) (by positivity)
        _ = K * K ^ σ.length := by ring

/-- **The telescoping estimate.**  A loop product of `n` resolvents moves by at most
`n K^n` times the largest move of a single resolvent. -/
theorem norm_gloopProd_sub_le {K Δ : ℝ} (hK : 1 ≤ K) (hΔ : 0 ≤ Δ)
    (hG₁ : ∀ s, ‖Gsig H₁ z₁ s‖ ≤ K) (hG₂ : ∀ s, ‖Gsig H₂ z₂ s‖ ≤ K)
    (hsub : ∀ s, ‖Gsig H₁ z₁ s - Gsig H₂ z₂ s‖ ≤ Δ) :
    ∀ (σ : List Bool) (a : List (ZMod L)), σ.length = a.length →
      ‖gloopProd L W H₁ z₁ ⟨σ, a⟩ - gloopProd L W H₂ z₂ ⟨σ, a⟩‖
        ≤ (σ.length : ℝ) * K ^ σ.length * Δ := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  intro σ
  induction σ with
  | nil =>
    intro a h
    obtain rfl : a = [] := List.eq_nil_of_length_eq_zero h.symm
    simp
  | cons s σ ih =>
    intro a h
    cases a with
    | nil => simp at h
    | cons b a =>
      have h' : σ.length = a.length := by simpa using h
      have hE : ‖Eblk L W b‖ ≤ 1 := norm_Eblk_le_one'' b
      have hQ₁ := norm_gloopProd_le_pow (H₁ := H₁) (z₁ := z₁) hK0 hG₁ σ a h'
      have hD := ih a h'
      have hsplit : gloopProd L W H₁ z₁ ⟨s :: σ, b :: a⟩
            - gloopProd L W H₂ z₂ ⟨s :: σ, b :: a⟩
          = (Gsig H₁ z₁ s - Gsig H₂ z₂ s) * Eblk L W b * gloopProd L W H₁ z₁ ⟨σ, a⟩
            + Gsig H₂ z₂ s * Eblk L W b
              * (gloopProd L W H₁ z₁ ⟨σ, a⟩ - gloopProd L W H₂ z₂ ⟨σ, a⟩) := by
        rw [gloopProd_cons, gloopProd_cons]
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
        abel
      rw [hsplit, List.length_cons]
      refine (norm_add_le _ _).trans ?_
      have hA : ‖(Gsig H₁ z₁ s - Gsig H₂ z₂ s) * Eblk L W b * gloopProd L W H₁ z₁ ⟨σ, a⟩‖
          ≤ Δ * K ^ σ.length := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        have h1 : ‖Gsig H₁ z₁ s - Gsig H₂ z₂ s‖ * ‖Eblk L W b‖ ≤ Δ * 1 :=
          mul_le_mul (hsub s) hE (norm_nonneg _) hΔ
        calc ‖Gsig H₁ z₁ s - Gsig H₂ z₂ s‖ * ‖Eblk L W b‖ * ‖gloopProd L W H₁ z₁ ⟨σ, a⟩‖
            ≤ Δ * 1 * K ^ σ.length :=
              mul_le_mul h1 hQ₁ (norm_nonneg _) (by positivity)
          _ = Δ * K ^ σ.length := by ring
      have hB : ‖Gsig H₂ z₂ s * Eblk L W b
            * (gloopProd L W H₁ z₁ ⟨σ, a⟩ - gloopProd L W H₂ z₂ ⟨σ, a⟩)‖
          ≤ K * ((σ.length : ℝ) * K ^ σ.length * Δ) := by
        refine (norm_mul_le _ _).trans ?_
        refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
        have h1 : ‖Gsig H₂ z₂ s‖ * ‖Eblk L W b‖ ≤ K * 1 :=
          mul_le_mul (hG₂ s) hE (norm_nonneg _) hK0
        calc ‖Gsig H₂ z₂ s‖ * ‖Eblk L W b‖
              * ‖gloopProd L W H₁ z₁ ⟨σ, a⟩ - gloopProd L W H₂ z₂ ⟨σ, a⟩‖
            ≤ K * 1 * ((σ.length : ℝ) * K ^ σ.length * Δ) :=
              mul_le_mul h1 hD (norm_nonneg _) (by positivity)
          _ = K * ((σ.length : ℝ) * K ^ σ.length * Δ) := by ring
      have hpow : (0 : ℝ) ≤ K ^ σ.length := pow_nonneg hK0 _
      have hkey : Δ * K ^ σ.length + K * ((σ.length : ℝ) * K ^ σ.length * Δ)
          ≤ ((σ.length : ℝ) + 1) * K ^ (σ.length + 1) * Δ := by
        rw [pow_succ']
        have h1 : K ^ σ.length ≤ K * K ^ σ.length := by nlinarith
        nlinarith [Nat.cast_nonneg (α := ℝ) σ.length]
      push_cast
      linarith

end Telescope

/-! ### 2. From the resolvent increment to the loop increment -/

section LoopFromGreen

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {H H₁ H₂ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z z₁ z₂ : ℂ}

/-- `‖G(σ)‖ = ‖G‖` for both charges, since `G(-) = G(+)†`. -/
theorem norm_Gsig_le_of_green (hH : H.IsHermitian) {K : ℝ} (h : ‖green H z‖ ≤ K) (s : Bool) :
    ‖Gsig H z s‖ ≤ K := by
  cases s
  · have hc : Gsig H z false = (green H z)ᴴ := (Gsig_conjTranspose hH z true).symm
    rw [hc, Matrix.l2_opNorm_conjTranspose]
    exact h
  · exact h

/-- **Both charges move by the same amount**: `G(-)_1 - G(-)_2 = (G(+)_1 - G(+)_2)†`. -/
theorem norm_Gsig_sub_le_norm_green_sub (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (s : Bool) :
    ‖Gsig H₁ z₁ s - Gsig H₂ z₂ s‖ ≤ ‖green H₁ z₁ - green H₂ z₂‖ := by
  cases s
  · have hc₁ : Gsig H₁ z₁ false = (green H₁ z₁)ᴴ := (Gsig_conjTranspose h₁ z₁ true).symm
    have hc₂ : Gsig H₂ z₂ false = (green H₂ z₂)ᴴ := (Gsig_conjTranspose h₂ z₂ true).symm
    rw [hc₁, hc₂, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
  · exact le_rfl

/-- **The loop increment.**  `|L_{σ,a}(H₁, z₁) - L_{σ,a}(H₂, z₂)| ≤ LW·n·K^n·‖G₁ - G₂‖`.
Both `H` and `z` are allowed to move, which is what the flow `H_u = √u X`, `z = z_u` does;
the `LW` is the crude `|⟨M⟩| ≤ (LW)‖M‖_op`. -/
theorem norm_gloop_sub_le {K Δ : ℝ} (hK : 1 ≤ K) (hΔ : 0 ≤ Δ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (hG₁ : ‖green H₁ z₁‖ ≤ K) (hG₂ : ‖green H₂ z₂‖ ≤ K)
    (hsub : ‖green H₁ z₁ - green H₂ z₂‖ ≤ Δ)
    (I : LoopIdx (ZMod L)) (hwf : I.WF) :
    ‖gloop L W H₁ z₁ I - gloop L W H₂ z₂ I‖
      ≤ (L : ℝ) * (W : ℝ) * (I.σ.length : ℝ) * K ^ I.σ.length * Δ := by
  obtain ⟨σ, a⟩ := I
  have hcard : (Fintype.card (ZMod L × Fin W) : ℝ) = (L : ℝ) * (W : ℝ) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  have htel := norm_gloopProd_sub_le hK hΔ
    (fun s => norm_Gsig_le_of_green h₁ hG₁ s) (fun s => norm_Gsig_le_of_green h₂ hG₂ s)
    (fun s => (norm_Gsig_sub_le_norm_green_sub h₁ h₂ s).trans hsub) σ a hwf
  have htr : gloop L W H₁ z₁ ⟨σ, a⟩ - gloop L W H₂ z₂ ⟨σ, a⟩
      = Matrix.trace (gloopProd L W H₁ z₁ ⟨σ, a⟩ - gloopProd L W H₂ z₂ ⟨σ, a⟩) := by
    rw [Matrix.trace_sub]; rfl
  rw [htr]
  refine (norm_trace_le_card_mul _).trans ?_
  rw [hcard]
  have hLW : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) := by positivity
  calc (L : ℝ) * (W : ℝ)
          * ‖gloopProd L W H₁ z₁ ⟨σ, a⟩ - gloopProd L W H₂ z₂ ⟨σ, a⟩‖
      ≤ (L : ℝ) * (W : ℝ) * ((σ.length : ℝ) * K ^ σ.length * Δ) :=
        mul_le_mul_of_nonneg_left htel hLW
    _ = (L : ℝ) * (W : ℝ) * (σ.length : ℝ) * K ^ σ.length * Δ := by ring

end LoopFromGreen

section GaussFlow

open Gauss

end GaussFlow

section PrimitiveLip

variable {L : ℕ} [NeZero L]

variable {W : ℕ}

end PrimitiveLip

section LkLip

open Gauss

end LkLip

section Envelope

open Gauss

end Envelope


section SepWitness

open Gauss

end SepWitness

section Witness

open Gauss

end Witness



/-! ### 9. The two purely deterministic moduli

`u ↦ (ℓ̂_u)⁻¹ = max(√(1-u), L⁻¹)` and `u ↦ η_u⁻¹` are Lipschitz on `(-∞, t₀]`, `t₀ < 1`, and
every deterministic factor of the far-field weight and of the ratio `‖(L-K)_u‖/T_{u,D}` is built
from those two: `(ℓ*_u)⁻¹ = (log W)^{-3/2}(ℓ̂_u)⁻¹`, and
`T_{u,D}(ℓ) = W^{-2}(ℓ̂_u^{-1})^{2}(η_u^{-1})^{2}exp(-√ℓ·√(ℓ̂_u)⁻¹) + W^{-D}`.
**No `ω` occurs here, and `s = 0` is allowed**. -/

section DetModulus

open Real Gauss

/-- `|√x - √y| ≤ |x-y|/(2√c)` on `[c, ∞)`, `c > 0`: `√` is Lipschitz away from the origin.
(`RBM.Gauss.abs_sqrt_sub_sqrt_le` is the `γ = 1/2` statement, valid down to `0`.) -/
theorem abs_sqrt_sub_sqrt_le_div {c x y : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |√x - √y| ≤ |x - y| / (2 * √c) := by
  have hx0 : (0:ℝ) ≤ x := hc.le.trans hx
  have hy0 : (0:ℝ) ≤ y := hc.le.trans hy
  have hsc : 0 < √c := Real.sqrt_pos.2 hc
  have hsx : √c ≤ √x := Real.sqrt_le_sqrt hx
  have hsy : √c ≤ √y := Real.sqrt_le_sqrt hy
  have hxx : √x * √x = x := Real.mul_self_sqrt hx0
  have hyy : √y * √y = y := Real.mul_self_sqrt hy0
  rw [le_div_iff₀ (by positivity)]
  have key : |√x - √y| * (√x + √y) = |x - y| := by
    rw [← abs_of_nonneg (by positivity : (0:ℝ) ≤ √x + √y), ← abs_mul]
    congr 1
    nlinarith [hxx, hyy]
  calc |√x - √y| * (2 * √c) ≤ |√x - √y| * (√x + √y) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    _ = |x - y| := key

/-- `|e^{-a} - e^{-b}| ≤ |a - b|` for `a, b ≥ 0`. -/
theorem abs_exp_neg_sub_exp_neg_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |exp (-a) - exp (-b)| ≤ |a - b| := by
  wlog h : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge h)
  have hexp : exp (-a) = exp (-b) * exp (-(a - b)) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : (0:ℝ) < exp (-b) := Real.exp_pos _
  have h3 : 1 - exp (-(a - b)) ≤ a - b := by
    have := Real.add_one_le_exp (-(a - b)); linarith
  have h4 : exp (-(a - b)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 : (0:ℝ) < exp (-(a - b)) := Real.exp_pos _
  rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by linarith)]
  nlinarith

/-- `(ℓ̂_t)⁻¹ = max(√(1-t), L⁻¹)`. -/
theorem inv_ellHat_ofReal (L : ℕ) (hL : 1 ≤ L) {t : ℝ} (ht1 : t < 1) :
    (ellHat L (t : ℂ))⁻¹ = max (√(1 - t)) ((L : ℝ)⁻¹) := by
  have h1t : (0:ℝ) < 1 - t := by linarith
  have hs : 0 < √(1 - t) := Real.sqrt_pos.2 h1t
  have hL0 : (0:ℝ) < L := by exact_mod_cast hL
  rw [ellHat_ofReal L ht1]
  rcases le_total (1 / √(1 - t)) ((L : ℝ)) with h | h
  · rw [min_eq_left h, one_div, inv_inv, max_eq_left]
    rw [div_le_iff₀ hs] at h
    rw [inv_eq_one_div, div_le_iff₀ hL0]
    nlinarith
  · rw [min_eq_right h, max_eq_right]
    rw [le_div_iff₀ hs] at h
    rw [inv_eq_one_div, le_div_iff₀ hL0]
    nlinarith

theorem inv_L_le_inv_ellHat (L : ℕ) (hL : 1 ≤ L) {t : ℝ} (ht1 : t < 1) :
    ((L : ℝ))⁻¹ ≤ (ellHat L (t : ℂ))⁻¹ := by
  rw [inv_ellHat_ofReal L hL ht1]; exact le_max_right _ _

theorem inv_ellHat_le_one (L : ℕ) (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (ellHat L (t : ℂ))⁻¹ ≤ 1 := by
  haveI : NeZero L := ⟨by omega⟩
  have h := one_le_ellHat L hL ht0 ht1
  rw [inv_le_one_iff₀]; exact Or.inr h

/-- **Deterministic modulus 1**: `u ↦ (ℓ̂_u)⁻¹` is Lipschitz with constant `1/(2√(1-t₀))`
on `(-∞, t₀]`, `t₀ < 1`. -/
theorem abs_inv_ellHat_sub_le (L : ℕ) (hL : 1 ≤ L) {t₀ v w : ℝ} (hv : v ≤ t₀) (hw : w ≤ t₀)
    (ht₀ : t₀ < 1) :
    |(ellHat L (v : ℂ))⁻¹ - (ellHat L (w : ℂ))⁻¹| ≤ |v - w| * (2 * √(1 - t₀))⁻¹ := by
  rw [inv_ellHat_ofReal L hL (lt_of_le_of_lt hv ht₀),
    inv_ellHat_ofReal L hL (lt_of_le_of_lt hw ht₀)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have h := abs_sqrt_sub_sqrt_le_div (c := 1 - t₀) (x := 1 - v) (y := 1 - w)
    (by linarith) (by linarith) (by linarith)
  have heq : |(1 - v) - (1 - w)| = |v - w| := by
    rw [show (1 - v) - (1 - w) = -(v - w) by ring, abs_neg]
  rw [heq, div_eq_mul_inv] at h
  exact h

/-- **Deterministic modulus for `u ↦ η_u⁻¹`**, with constant `η_{t₀}⁻²` (using `Im m ≤ 1`). -/
theorem abs_inv_etaT_sub_le {E : ℝ} (hE : |E| < 2) {t₀ v w : ℝ} (hv : v ≤ t₀) (hw : w ≤ t₀)
    (ht₀ : t₀ < 1) :
    |(etaT E v)⁻¹ - (etaT E w)⁻¹| ≤ |v - w| * ((etaT E t₀)⁻¹ * (etaT E t₀)⁻¹) := by
  have hm := mE_im_pos hE
  have hm1 := mE_im_le_one hE
  have hpv : 0 < etaT E v := etaT_pos_of_lt_one' hE (lt_of_le_of_lt hv ht₀)
  have hpw : 0 < etaT E w := etaT_pos_of_lt_one' hE (lt_of_le_of_lt hw ht₀)
  have hpt : 0 < etaT E t₀ := etaT_pos_of_lt_one' hE ht₀
  have hvne : etaT E v ≠ 0 := hpv.ne'
  have hwne : etaT E w ≠ 0 := hpw.ne'
  have hd : etaT E w - etaT E v = (v - w) * (mE E).im := by
    show (1 - w) * (mE E).im - (1 - v) * (mE E).im = (v - w) * (mE E).im
    ring
  have hgen : (etaT E v)⁻¹ - (etaT E w)⁻¹
      = (etaT E w - etaT E v) * ((etaT E v)⁻¹ * (etaT E w)⁻¹) := by
    field_simp
  have key : (etaT E v)⁻¹ - (etaT E w)⁻¹
      = (v - w) * (mE E).im * ((etaT E v)⁻¹ * (etaT E w)⁻¹) := by rw [hgen, hd]
  have h1 : (etaT E v)⁻¹ ≤ (etaT E t₀)⁻¹ := inv_anti₀ hpt (etaT_le_of_le hE hv)
  have h2 : (etaT E w)⁻¹ ≤ (etaT E t₀)⁻¹ := inv_anti₀ hpt (etaT_le_of_le hE hw)
  rw [key, abs_mul, abs_mul, abs_of_nonneg hm.le,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (etaT E v)⁻¹ * (etaT E w)⁻¹)]
  calc |v - w| * (mE E).im * ((etaT E v)⁻¹ * (etaT E w)⁻¹)
      ≤ |v - w| * 1 * ((etaT E t₀)⁻¹ * (etaT E t₀)⁻¹) := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact mul_le_mul_of_nonneg_left hm1 (abs_nonneg _)
        · exact mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = |v - w| * ((etaT E t₀)⁻¹ * (etaT E t₀)⁻¹) := by ring

end DetModulus

/-! ### 10. The modulus of `u ↦ T_{u,D}(ℓ)` and of `u ↦ (T_{u,D}(ℓ))⁻¹` -/

section TailModulus

open Real Gauss

/-- `|ac - be| ≤ |a-b|·|c| + |b|·|c-e|`, in the bounded form used below. -/
theorem abs_mul_sub_mul_le' {a b c e Da Ca Db Cb : ℝ}
    (hda : |a - b| ≤ Da) (hdb : |c - e| ≤ Db) (hc : |c| ≤ Cb) (hb : |b| ≤ Ca)
    (hDa : 0 ≤ Da) (hCa : 0 ≤ Ca) :
    |a * c - b * e| ≤ Da * Cb + Ca * Db := by
  have hrw : a * c - b * e = (a - b) * c + b * (c - e) := by ring
  rw [hrw]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul hda hc (abs_nonneg _) hDa)
    (mul_le_mul hb hdb (abs_nonneg _) hCa)

theorem abs_sq_sub_sq_le {a b M S : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : |a - b| ≤ M)
    (hs : a + b ≤ S) (hM : 0 ≤ M) : |a ^ 2 - b ^ 2| ≤ M * S := by
  have hrw : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [hrw, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ a + b)]
  exact mul_le_mul hd hs (by linarith) hM

/-- `T_{u,D}` written through the inverses `ℓ̂_u⁻¹`, `η_u⁻¹` — the two Lipschitz quantities
of §9. -/
theorem tailT_eq_inv {W ℓu ηu D ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) :
    tailT W ℓu ηu D ℓ
      = W⁻¹ ^ 2 * ℓu⁻¹ ^ 2 * ηu⁻¹ ^ 2 * exp (-(√ℓ * √ℓu⁻¹)) + W ^ (-D) := by
  have h1 : ℓ / ℓu = ℓ * ℓu⁻¹ := div_eq_mul_inv _ _
  have h2 : √(ℓ * ℓu⁻¹) = √ℓ * √ℓu⁻¹ := Real.sqrt_mul hℓ0 _
  have h3 : ((W * ℓu * ηu) ^ 2)⁻¹ = W⁻¹ ^ 2 * ℓu⁻¹ ^ 2 * ηu⁻¹ ^ 2 := by
    simp only [inv_pow, ← mul_inv, ← mul_pow]
  rw [tailT, h1, h2, h3]

/-- **The Lipschitz constant of `u ↦ T_{u,D}(ℓ)`** on `[0, t₀] ⊆ [0,1)`, uniform in
`ℓ ∈ [0, L]`. -/
noncomputable def tailLip (d : Dims) (N : ℕ) (E t₀ : ℝ) : ℝ :=
  2 * (2 * √(1 - t₀))⁻¹ * ((etaT E t₀)⁻¹) ^ 2 + 2 * ((etaT E t₀)⁻¹) ^ 3
    + ((etaT E t₀)⁻¹) ^ 2 * ((d.L N : ℝ) / 2) * (2 * √(1 - t₀))⁻¹

theorem tailLip_nonneg (d : Dims) (N : ℕ) {E t₀ : ℝ} (hE : |E| < 2) (ht₀ : t₀ < 1) :
    0 ≤ tailLip d N E t₀ := by
  have h := etaT_pos_of_lt_one' hE ht₀
  have h1 : (0:ℝ) < 1 - t₀ := by linarith
  have hs : 0 < √(1 - t₀) := Real.sqrt_pos.2 h1
  have hL : (0:ℝ) ≤ (d.L N : ℝ) := Nat.cast_nonneg _
  unfold tailLip
  positivity

/-- **Deterministic modulus 2**: `u ↦ T_{u,D}(ℓ)` is Lipschitz on `[0, t₀]`, `t₀ < 1`,
uniformly in `ℓ ∈ [0, L]`.  `γ = 1`, no `ω`. -/
theorem abs_tailT_sub_le (d : Dims) (N : ℕ) {E D t₀ v w ℓ : ℝ} (hE : |E| < 2)
    (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1)
    (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ (d.L N : ℝ)) :
    |tailT (d.W N : ℝ) (ellHat (d.L N) (v : ℂ)) (etaT E v) D ℓ
        - tailT (d.W N : ℝ) (ellHat (d.L N) (w : ℂ)) (etaT E w) D ℓ|
      ≤ |v - w| * tailLip d N E t₀ := by
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hL1 : 1 ≤ d.L N := by omega
  have hLr : (1:ℝ) ≤ (d.L N : ℝ) := by exact_mod_cast hL1
  have hWr : (1:ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hv1 : v < 1 := lt_of_le_of_lt hv ht₀
  have hw1 : w < 1 := lt_of_le_of_lt hw ht₀
  have h1t : (0:ℝ) < 1 - t₀ := by linarith
  have hst : 0 < √(1 - t₀) := Real.sqrt_pos.2 h1t
  have hCp0 : (0:ℝ) < (2 * √(1 - t₀))⁻¹ := by positivity
  have hq0 : (0:ℝ) < (etaT E t₀)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE ht₀)
  have hW0 : (0:ℝ) < (d.W N : ℝ) := by linarith
  have hWinv0 : (0:ℝ) < ((d.W N : ℝ))⁻¹ := inv_pos.2 hW0
  have hWinv1 : ((d.W N : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; exact Or.inr hWr
  have hLr0 : (0:ℝ) < (d.L N : ℝ) := by linarith
  have hsqL : √(d.L N : ℝ) * √(d.L N : ℝ) = (d.L N : ℝ) := Real.mul_self_sqrt hLr0.le
  have hsqLpos : 0 < √(d.L N : ℝ) := Real.sqrt_pos.2 hLr0
  -- the two moduli of §9, in explicit form
  have hpvL : ((d.L N : ℝ))⁻¹ ≤ (ellHat (d.L N) (v : ℂ))⁻¹ := inv_L_le_inv_ellHat _ hL1 hv1
  have hpwL : ((d.L N : ℝ))⁻¹ ≤ (ellHat (d.L N) (w : ℂ))⁻¹ := inv_L_le_inv_ellHat _ hL1 hw1
  have hpv0 : (0:ℝ) < (ellHat (d.L N) (v : ℂ))⁻¹ := lt_of_lt_of_le (inv_pos.2 hLr0) hpvL
  have hpw0 : (0:ℝ) < (ellHat (d.L N) (w : ℂ))⁻¹ := lt_of_lt_of_le (inv_pos.2 hLr0) hpwL
  have hpv1 : (ellHat (d.L N) (v : ℂ))⁻¹ ≤ 1 := inv_ellHat_le_one _ hL3 hv0 hv1
  have hpw1 : (ellHat (d.L N) (w : ℂ))⁻¹ ≤ 1 := inv_ellHat_le_one _ hL3 hw0 hw1
  have hdp : |(ellHat (d.L N) (v : ℂ))⁻¹ - (ellHat (d.L N) (w : ℂ))⁻¹|
      ≤ |v - w| * (2 * √(1 - t₀))⁻¹ := abs_inv_ellHat_sub_le _ hL1 hv hw ht₀
  have hqv0 : (0:ℝ) < (etaT E v)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE hv1)
  have hqw0 : (0:ℝ) < (etaT E w)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE hw1)
  have hqvq : (etaT E v)⁻¹ ≤ (etaT E t₀)⁻¹ :=
    inv_anti₀ (etaT_pos_of_lt_one' hE ht₀) (etaT_le_of_le hE hv)
  have hqwq : (etaT E w)⁻¹ ≤ (etaT E t₀)⁻¹ :=
    inv_anti₀ (etaT_pos_of_lt_one' hE ht₀) (etaT_le_of_le hE hw)
  have hdq : |(etaT E v)⁻¹ - (etaT E w)⁻¹| ≤ |v - w| * ((etaT E t₀)⁻¹ * (etaT E t₀)⁻¹) :=
    abs_inv_etaT_sub_le hE hv hw ht₀
  have hsqle : √ℓ ≤ √(d.L N : ℝ) := Real.sqrt_le_sqrt hℓL
  rw [tailT_eq_inv hℓ0, tailT_eq_inv hℓ0]
  simp only [tailLip]
  -- abbreviations
  set Cp : ℝ := (2 * √(1 - t₀))⁻¹ with hCp
  set q : ℝ := (etaT E t₀)⁻¹ with hqdef
  set Lr : ℝ := (d.L N : ℝ) with hLdef
  set pv : ℝ := (ellHat (d.L N) (v : ℂ))⁻¹ with hpv
  set pw : ℝ := (ellHat (d.L N) (w : ℂ))⁻¹ with hpw
  set qv : ℝ := (etaT E v)⁻¹ with hqv
  set qw : ℝ := (etaT E w)⁻¹ with hqw
  set Av : ℝ := ((d.W N : ℝ))⁻¹ ^ 2 * pv ^ 2 * qv ^ 2 with hAv
  set Aw : ℝ := ((d.W N : ℝ))⁻¹ ^ 2 * pw ^ 2 * qw ^ 2 with hAw
  set Ev : ℝ := exp (-(√ℓ * √pv)) with hEv
  set Ew : ℝ := exp (-(√ℓ * √pw)) with hEw
  have hcancel : Av * Ev + (d.W N : ℝ) ^ (-D) - (Aw * Ew + (d.W N : ℝ) ^ (-D))
      = Av * Ev - Aw * Ew := by ring
  rw [hcancel]
  -- (i) |Ev| ≤ 1
  have hEv1 : |Ev| ≤ 1 := by
    have hnn : (0:ℝ) ≤ √ℓ * √pv := by positivity
    rw [hEv, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  -- (ii) |Aw| ≤ q^2
  have hAw2 : |Aw| ≤ q ^ 2 := by
    rw [hAw, abs_of_nonneg (by positivity)]
    have h1 : ((d.W N : ℝ))⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hWinv0.le hWinv1
    have h2 : pw ^ 2 ≤ 1 := pow_le_one₀ hpw0.le hpw1
    have h3 : qw ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hqw0.le hqwq 2
    have h4 : ((d.W N : ℝ))⁻¹ ^ 2 * pw ^ 2 * qw ^ 2 ≤ 1 * 1 * q ^ 2 :=
      mul_le_mul (mul_le_mul h1 h2 (by positivity) (by norm_num)) h3 (by positivity)
        (by norm_num)
    linarith
  -- (iii) |Ev - Ew| ≤ (L/2)·|v-w|·Cp
  have hdE : |Ev - Ew| ≤ Lr / 2 * (|v - w| * Cp) := by
    have h1 : |Ev - Ew| ≤ |√ℓ * √pv - √ℓ * √pw| :=
      abs_exp_neg_sub_exp_neg_le (by positivity) (by positivity)
    have h2 : |√ℓ * √pv - √ℓ * √pw| = √ℓ * |√pv - √pw| := by
      rw [show √ℓ * √pv - √ℓ * √pw = √ℓ * (√pv - √pw) by ring, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    have h3 : |√pv - √pw| ≤ |pv - pw| / (2 * √(Lr⁻¹)) :=
      abs_sqrt_sub_sqrt_le_div (by positivity) hpvL hpwL
    have h4 : |pv - pw| / (2 * √(Lr⁻¹)) = |pv - pw| * √Lr / 2 := by
      rw [Real.sqrt_inv, div_eq_mul_inv, mul_inv, inv_inv]; ring
    rw [h4] at h3
    rw [h2] at h1
    have h7 : |Ev - Ew| ≤ √Lr * (|pv - pw| * √Lr / 2) :=
      h1.trans (mul_le_mul hsqle h3 (abs_nonneg _) (Real.sqrt_nonneg _))
    have h8 : √Lr * (|pv - pw| * √Lr / 2) = Lr / 2 * |pv - pw| := by
      rw [show √Lr * (|pv - pw| * √Lr / 2) = (√Lr * √Lr) * (|pv - pw| / 2) by ring, hsqL]
      ring
    rw [h8] at h7
    exact h7.trans (mul_le_mul_of_nonneg_left hdp (by positivity))
  -- (iv) |Av - Aw| ≤ (2·Cp·q² + 2q³)·|v-w|
  have hdA : |Av - Aw| ≤ (2 * Cp * q ^ 2 + 2 * q ^ 3) * |v - w| := by
    have hrw : Av - Aw = ((d.W N : ℝ))⁻¹ ^ 2 * (pv ^ 2 * qv ^ 2 - pw ^ 2 * qw ^ 2) := by
      rw [hAv, hAw]; ring
    have hp2 : |pv ^ 2 - pw ^ 2| ≤ (|v - w| * Cp) * 2 :=
      abs_sq_sub_sq_le hpv0.le hpw0.le hdp (by linarith) (by positivity)
    have hq2 : |qv ^ 2 - qw ^ 2| ≤ (|v - w| * (q * q)) * (2 * q) :=
      abs_sq_sub_sq_le hqv0.le hqw0.le hdq (by linarith) (by positivity)
    have hqv2 : |qv ^ 2| ≤ q ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ hqv0.le hqvq 2
    have hpw2 : |pw ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_one₀ hpw0.le hpw1
    have hinner : |pv ^ 2 * qv ^ 2 - pw ^ 2 * qw ^ 2|
        ≤ (|v - w| * Cp * 2) * q ^ 2 + 1 * ((|v - w| * (q * q)) * (2 * q)) :=
      abs_mul_sub_mul_le' hp2 hq2 hqv2 hpw2 (by positivity) (by norm_num)
    have hWsq : ((d.W N : ℝ))⁻¹ ^ 2 ≤ 1 := pow_le_one₀ hWinv0.le hWinv1
    rw [hrw, abs_mul, abs_of_nonneg (sq_nonneg ((d.W N : ℝ))⁻¹)]
    calc ((d.W N : ℝ))⁻¹ ^ 2 * |pv ^ 2 * qv ^ 2 - pw ^ 2 * qw ^ 2|
        ≤ 1 * ((|v - w| * Cp * 2) * q ^ 2 + 1 * ((|v - w| * (q * q)) * (2 * q))) :=
          mul_le_mul hWsq hinner (abs_nonneg _) (by norm_num)
      _ = (2 * Cp * q ^ 2 + 2 * q ^ 3) * |v - w| := by ring
  have hmain : |Av * Ev - Aw * Ew|
      ≤ (2 * Cp * q ^ 2 + 2 * q ^ 3) * |v - w| * 1 + q ^ 2 * (Lr / 2 * (|v - w| * Cp)) :=
    abs_mul_sub_mul_le' hdA hdE hEv1 hAw2 (by positivity) (by positivity)
  refine hmain.trans (le_of_eq ?_)
  ring

end TailModulus

section JModulus

open Real Gauss Step2FarMart

end JModulus

section Producer

open Real Gauss Step2FarMart Filter

end Producer

section Field

open Real Gauss Step2FarMart Filter MeasureTheory

end Field

end RBM
