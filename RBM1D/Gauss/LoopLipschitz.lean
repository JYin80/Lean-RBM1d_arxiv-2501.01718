/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Gauss.FlowHolder
import RBM1D.Gauss.DimsExample

/-!
# T252 — the loop-level Lipschitz modulus, from the `‖X‖`-free resolvent increment

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.43)/(5.46)/(5.48).

## §0 The sunk resolvent lemmas (T249 part B, moved here by T252)

`RBM.isHermitian_real_smul`, `RBM.mul_green_smul`, `RBM.norm_green_sqrt_sub_le` and
`RBM.norm_green_sqrt_sub_le_lip` used to live in `RBM1D/Flow/Eq548Producer.lean`.  They are
pure resolvent identities — nothing from `RBM1D/Flow/` enters them — and `RBM1D/Gauss/` needs
them, so they were sunk here **verbatim, signatures unchanged**; `Flow/Eq548Producer.lean`
imports this file and keeps `rfl` probes in place of the old section.

The identity `X G_v = v^{-1/2}(1 + z_v G_v)` (`RBM.mul_green_smul`) removes `X` from the
resolvent identity altogether: no bound on `‖X‖` is used, and the estimate holds for **every**
`ω`.  On a window whose left endpoint is `s > 0` the resulting constant is `O(1/s)`
(`RBM.norm_green_sqrt_sub_le_lip`), so on `s_N ≥ N^{-C}` it is `N^{C}` times the `η`-factors —
a Lipschitz (`γ = 1`) modulus, not a Hölder one.  **`s > 0` is essential**: T249's
`RBM.not_entryModulusEv_swapSample_of_far` shows the `s ≡ 0` statement is false.

## Main results

### §1 Telescoping a loop product

* `RBM.norm_gloopProd_sub_le` — a loop product of `n` resolvents moves by at most `n K^n` times
  the largest move of a single resolvent (`A₁B₁ - A₂B₂ = (A₁-A₂)B₁ + A₂(B₁-B₂)`, by induction
  on the charge/label lists).  **Both** `H` and `z` are allowed to move, which is what the flow
  `H_u = √u X`, `z = z_u` does — the existing `RBM.gchain_eq_add_sum_gchainMixed` only moves
  `z`.

### §2 `resolvent → loop`

* `RBM.norm_Gsig_sub_le_norm_green_sub` — both charges move by the same amount, since
  `G(-) = G(+)†` and `‖·ᴴ‖ = ‖·‖` for the `ℓ²` operator norm.
* `RBM.norm_gloop_sub_le` — `|L_{σ,a}(H₁,z₁) - L_{σ,a}(H₂,z₂)| ≤ LW·n·K^n·‖G₁-G₂‖`.

### §3 The flow

* `RBM.greenLip` — the time-Lipschitz constant `η_{t₀}⁻¹(1+3η_{t₀}⁻¹)/(2s) + η_{t₀}⁻²` of the
  resolvent on `[s, t₀] ⊆ (0,1)`; `RBM.norm_green_flow_sub_le`, `RBM.norm_Lval_sub_le_lip`.

### §4 The primitive `K`

* `RBM.Theta_sub_eq` — `Θ_ξ - Θ_ζ = (ξ-ζ) Θ_ξ S^{(B)} Θ_ζ`;
  `RBM.norm_Theta_apply_sub_le` — the **entrywise** bound `|ξ-ζ|(1-r)⁻²`, no `L`-factor;
  `RBM.norm_kTwo_sub_le` — (2.57) is Lipschitz with constant `W⁻¹(1-t₀)⁻²`.

### §5 `(L-K)`, i.e. the transcription asked for

* `RBM.lkLip`, `RBM.norm_lk_sub_le_lip` —
  `‖(L-K)_{v,(+,-),x} - (L-K)_{w,(+,-),x}‖ ≤ |v-w| · lkLip`, **for every `ω`**, with
  `lkLip = L·W·2·η_{t₀}⁻² · greenLip E t₀ s + W⁻¹(1-t₀)⁻²`.  Exponent `γ = 1`; on
  `s_N ≥ N^{-C}` and `W L ≤ N` the constant is `N^{1+C}` times a constant of `(E, t₀)`, i.e.
  `Kmod = 1 + C`.

### §7 The crude envelope

* `RBM.norm_lk_le_crude` — `‖(L-K)_u‖ ≤ W⁻¹(η_{t₀}⁻² + (1-t₀)⁻¹)` on `[0,t₀]`, for every `ω`.

### §6 T252(乙): `hsep` on a concrete `Dims`

* `RBM.log_pow_eight_le_sqrt`, `RBM.lt_sixteen_mul_growL_pow`,
  `RBM.twelve_ellStar_le_half_exampleGrow`, `RBM.hsep_exampleGrow`.

## What the last mile still needs

`RBM.MomentDuhamelCut.CutHypEvOn.modulus` for `J = RBM.Step2FarMart.jSfarSm` factors through
`RBM.Step2FarMart.abs_jSfarSm_sub_le` and `RBM.Step2FarMart.abs_lkFarSm_ratio_sub_le` into

1. the weight term `15/8 |d/(6ℓ*_v) - d/(6ℓ*_w)| · (‖(L-K)_v‖/T_{v,D})`, and
2. the ratio term `|‖(L-K)_v‖/T_{v,D} - ‖(L-K)_w‖/T_{w,D}|`.

Everything **random** in both is supplied here: §5 bounds `|‖(L-K)_v‖ - ‖(L-K)_w‖|` and §7
bounds `‖(L-K)_v‖`, and `T_{u,D} ≥ W^{-D}` (`RBM.rpow_neg_le_tailT`) converts a division into a
factor `W^{D}`.  What is missing is **purely deterministic** (`ω`-free): a Lipschitz modulus in
`u` for `u ↦ (ℓ*_u)⁻¹` and for `u ↦ (T_{u,D}(ℓ))⁻¹` on `[s, t₀]`, which reduces to one for
`u ↦ (ℓ̂_u)⁻¹ = max(√(1-u), L⁻¹)` and `u ↦ η_u⁻¹`.  Both are elementary and both are `γ = 1`;
neither is started here.
-/

namespace RBM

open Matrix Filter
open scoped Matrix.Norms.L2Operator

/-! ### 0. The sunk resolvent lemmas (T249 part B) -/

section SqrtFlowLip

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem isHermitian_real_smul {Y : Matrix n n ℂ} (hY : Y.IsHermitian) (r : ℝ) :
    ((r : ℂ) • Y).IsHermitian := by
  ext i j
  show (starRingEnd ℂ) ((r : ℂ) * Y j i) = (r : ℂ) * Y i j
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  simpa using hY.apply i j

theorem mul_green_smul {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    {r : ℝ} (hr : r ≠ 0) :
    Y * green ((r : ℂ) • Y) z
      = ((r : ℂ))⁻¹ • ((1 : Matrix n n ℂ) + z • green ((r : ℂ) • Y) z) := by
  have hYr : ((r : ℂ) • Y).IsHermitian := isHermitian_real_smul hY r
  have hdet : IsUnit (((r : ℂ) • Y) - z • (1 : Matrix n n ℂ)).det :=
    isUnit_det_sub_smul_one hYr hz
  have hinv : (((r : ℂ) • Y) - z • (1 : Matrix n n ℂ)) * green ((r : ℂ) • Y) z = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have hrC : ((r : ℂ)) ≠ 0 := by exact_mod_cast hr
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul] at hinv
  have : (r : ℂ) • (Y * green ((r : ℂ) • Y) z)
      = (1 : Matrix n n ℂ) + z • green ((r : ℂ) • Y) z := by
    rw [← hinv]; abel
  rw [← this, smul_smul, inv_mul_cancel₀ hrC, one_smul]

/-- **The `‖X‖`-free resolvent increment of the `√u` flow.** -/
theorem norm_green_sqrt_sub_le {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {E : ℝ} (hE : |E| < 2)
    {u v : ℝ} (hv0 : 0 < v) (_hu0 : 0 ≤ u) (hu1 : u < 1) (hv1 : v < 1) :
    ‖green ((Real.sqrt u : ℂ) • Y) (zt E u) - green ((Real.sqrt v : ℂ) • Y) (zt E v)‖
      ≤ |Real.sqrt v - Real.sqrt u| / Real.sqrt v *
          ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹))
        + |u - v| * ((etaT E u)⁻¹ * (etaT E v)⁻¹) := by
  have hηu : 0 < etaT E u := by
    show 0 < (1 - u) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hηv : 0 < etaT E v := by
    show 0 < (1 - v) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hzu : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hηu.ne'
  have hzv : (zt E v).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hηv.ne'
  have hYu : ((Real.sqrt u : ℂ) • Y).IsHermitian := isHermitian_real_smul hY _
  have hYv : ((Real.sqrt v : ℂ) • Y).IsHermitian := isHermitian_real_smul hY _
  set Gu := green ((Real.sqrt u : ℂ) • Y) (zt E u) with hGu
  set Gv := green ((Real.sqrt v : ℂ) • Y) (zt E v) with hGv
  have hnu : ‖Gu‖ ≤ (etaT E u)⁻¹ :=
    Gauss.norm_green_le hYu hηu (by rw [← etaT_eq_zt_im, abs_of_pos hηu])
  have hnv : ‖Gv‖ ≤ (etaT E v)⁻¹ :=
    Gauss.norm_green_le hYv hηv (by rw [← etaT_eq_zt_im, abs_of_pos hηv])
  have hsv : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 hv0).ne'
  have hid := green_sub_eq (isUnit_det_sub_smul_one hYu hzu) (isUnit_det_sub_smul_one hYv hzv)
  have hYG : Y * Gv = ((Real.sqrt v : ℂ))⁻¹ • ((1 : Matrix n n ℂ) + (zt E v) • Gv) :=
    mul_green_smul hY hzv hsv
  have hsplit : Gu - Gv
      = ((((Real.sqrt v : ℂ) - (Real.sqrt u : ℂ)) / (Real.sqrt v : ℂ)) •
            (Gu + (zt E v) • (Gu * Gv)))
        - ((zt E v) - (zt E u)) • (Gu * Gv) := by
    rw [hid]
    rw [show ((Real.sqrt v : ℂ) • Y - (zt E v) • (1 : Matrix n n ℂ))
          - ((Real.sqrt u : ℂ) • Y - (zt E u) • (1 : Matrix n n ℂ))
        = (((Real.sqrt v : ℂ) - (Real.sqrt u : ℂ)) • Y)
          - ((zt E v) - (zt E u)) • (1 : Matrix n n ℂ) by
      rw [sub_smul, sub_smul]; abel]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one]
    rw [Matrix.mul_assoc, hYG, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.mul_one,
      Matrix.mul_smul]
    rw [div_eq_mul_inv]
  have hGuv : ‖Gu * Gv‖ ≤ (etaT E u)⁻¹ * (etaT E v)⁻¹ :=
    (norm_mul_le _ _).trans (mul_le_mul hnu hnv (norm_nonneg _) (by positivity))
  have hscal : ‖(((Real.sqrt v : ℂ) - (Real.sqrt u : ℂ)) / (Real.sqrt v : ℂ))‖
      = |Real.sqrt v - Real.sqrt u| / Real.sqrt v := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_of_nonneg (Real.sqrt_nonneg v)]
  have h1 : ‖((((Real.sqrt v : ℂ) - (Real.sqrt u : ℂ)) / (Real.sqrt v : ℂ)) •
        (Gu + (zt E v) • (Gu * Gv)))‖
      ≤ |Real.sqrt v - Real.sqrt u| / Real.sqrt v *
          ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹)) := by
    rw [norm_smul, hscal]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have : ‖zt E v‖ * ‖Gu * Gv‖ ≤ ‖zt E v‖ * ((etaT E u)⁻¹ * (etaT E v)⁻¹) :=
      mul_le_mul_of_nonneg_left hGuv (norm_nonneg _)
    nlinarith [hnu, norm_nonneg (zt E v)]
  have h2 : ‖((zt E v) - (zt E u)) • (Gu * Gv)‖
      ≤ |u - v| * ((etaT E u)⁻¹ * (etaT E v)⁻¹) := by
    rw [norm_smul, norm_zt_sub hE.le, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hGuv (abs_nonneg _)
  rw [hsplit]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)


/-- **The Lipschitz form on a window with a positive left endpoint.**  `|√v - √u|/√v ≤
|u - v|/(2s)` for `u, v ≥ s > 0`, so the increment is `O(|u-v|/s)` — Lipschitz (`γ = 1`), and
**no bound on `‖Y‖` is used**.  On `s_N ≥ N^{-C}` and `t_N ≤ t₀ < 1` the bracket is at most
`(η_{t₀})⁻¹(1 + 3(η_{t₀})⁻¹) N^C / 2 + (η_{t₀})⁻²`, i.e. `N^C` times a constant of `E` and
`t₀` (use `‖z_v‖ ≤ |E| + 1 ≤ 3` and `η_v ≥ η_{t₀}`). -/
theorem norm_green_sqrt_sub_le_lip {Y : Matrix n n ℂ} (hY : Y.IsHermitian) {E : ℝ}
    (hE : |E| < 2) {s u v : ℝ} (hs : 0 < s) (hsu : s ≤ u) (hsv : s ≤ v) (hu1 : u < 1)
    (hv1 : v < 1) :
    ‖green ((Real.sqrt u : ℂ) • Y) (zt E u) - green ((Real.sqrt v : ℂ) • Y) (zt E v)‖
      ≤ |u - v| * ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹) / (2 * s)
          + (etaT E u)⁻¹ * (etaT E v)⁻¹) := by
  have hv0 : 0 < v := lt_of_lt_of_le hs hsv
  have hu0 : (0 : ℝ) ≤ u := le_trans hs.le hsu
  have hsqu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
  have hsqv : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
  have hs2u : Real.sqrt s ≤ Real.sqrt u := Real.sqrt_le_sqrt hsu
  have hs2v : Real.sqrt s ≤ Real.sqrt v := Real.sqrt_le_sqrt hsv
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hv0' : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hu0' : (0 : ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
  have habs : |Real.sqrt v - Real.sqrt u| * (Real.sqrt u + Real.sqrt v) = |u - v| := by
    rw [← abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt u + Real.sqrt v), ← abs_mul]
    rw [show (Real.sqrt v - Real.sqrt u) * (Real.sqrt u + Real.sqrt v) = v - u by nlinarith]
    exact abs_sub_comm v u
  have hnn : (0 : ℝ) ≤ |Real.sqrt v - Real.sqrt u| := abs_nonneg _
  have hden : 2 * s ≤ (Real.sqrt u + Real.sqrt v) * Real.sqrt v := by nlinarith
  have hkey : |Real.sqrt v - Real.sqrt u| / Real.sqrt v ≤ |u - v| / (2 * s) := by
    rw [div_le_div_iff₀ hv0' (by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hden hnn
    nlinarith [habs, hmul]
  have hηu : 0 < etaT E u := by
    show 0 < (1 - u) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hηv : 0 < etaT E v := by
    show 0 < (1 - v) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  refine (norm_green_sqrt_sub_le hY hE hv0 hu0 hu1 hv1).trans ?_
  have hfac : (0 : ℝ) ≤ (etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹) := by positivity
  have h1 : |Real.sqrt v - Real.sqrt u| / Real.sqrt v *
        ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹))
      ≤ |u - v| / (2 * s) * ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹)) :=
    mul_le_mul_of_nonneg_right hkey hfac
  have hd : |u - v| / (2 * s) * ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹))
      = |u - v| * ((etaT E u)⁻¹ * (1 + ‖zt E v‖ * (etaT E v)⁻¹) / (2 * s)) := by
    field_simp
  rw [hd] at h1
  linarith

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

/-! ### 3. The flow `H_u = √u X`: the loop modulus, for **every** `ω`

The constant is `K = η_{t₀}^{-1}` per resolvent and `Lip E t₀ s` per unit of time; both are
free of `‖X‖`, which is exactly what `RBM.mul_green_smul` bought.  **`0 < s` is essential**:
at `s = 0` the statement is false (T249, `RBM.not_entryModulusEv_swapSample_of_far`). -/

section GaussFlow

open Gauss

/-- `|z_u| ≤ 3` on `[0,1]` (local copy; `RBM.Gauss.XiLow` is not on this import path). -/
theorem norm_zt_le_three' {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖zt E u‖ ≤ 3 := by
  have hz : zt E u = ((E : ℝ) : ℂ) + (((1 - u : ℝ)) : ℂ) * mE E := by
    rw [zt]; push_cast; ring
  rw [hz]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    norm_mE hE.le, mul_one]
  have h2 : |1 - u| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  linarith [hE.le]

/-- **The time-Lipschitz constant of the resolvent on `[s, t₀] ⊆ (0, 1)`.**  `N^{C}` times a
constant of `(E, t₀)` once `s ≥ N^{-C}`; no `‖X‖`. -/
noncomputable def greenLip (E t₀ s : ℝ) : ℝ :=
  (etaT E t₀)⁻¹ * (1 + 3 * (etaT E t₀)⁻¹) / (2 * s) + (etaT E t₀)⁻¹ * (etaT E t₀)⁻¹

theorem greenLip_nonneg {E t₀ s : ℝ} (hE : |E| < 2) (ht₀ : t₀ < 1) (hs : 0 < s) :
    0 ≤ greenLip E t₀ s := by
  have h := etaT_pos_of_lt_one' hE ht₀
  unfold greenLip
  positivity

/-- `1 ≤ η_{t₀}^{-1}`. -/
theorem one_le_inv_etaT {E t₀ : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t₀) (ht₀ : t₀ < 1) :
    1 ≤ (etaT E t₀)⁻¹ := by
  have hpos := etaT_pos_of_lt_one' hE ht₀
  have hle : etaT E t₀ ≤ 1 := by
    show (1 - t₀) * (mE E).im ≤ 1
    have h1 := mE_im_le_one hE
    have h2 := (mE_im_pos hE).le
    nlinarith
  rw [le_inv_comm₀ one_pos hpos, inv_one]
  exact hle

/-- **The `‖X‖`-free resolvent modulus along the flow, uniform on the window `[s, t₀]`.** -/
theorem norm_green_flow_sub_le (d : Dims) (N : ℕ) (ω : Ω d) {E t₀ s v w : ℝ} (hE : |E| < 2)
    (hs : 0 < s) (hsv : s ≤ v) (hsw : s ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1) :
    ‖(sample d).G E N v ω - (sample d).G E N w ω‖ ≤ |v - w| * greenLip E t₀ s := by
  have hv1 : v < 1 := lt_of_le_of_lt hv ht₀
  have hw1 : w < 1 := lt_of_le_of_lt hw ht₀
  have hv0 : (0 : ℝ) ≤ v := le_trans hs.le hsv
  have hw0 : (0 : ℝ) ≤ w := le_trans hs.le hsw
  have hGeq : ∀ u : ℝ, (sample d).G E N u ω
      = green ((Real.sqrt u : ℂ) • Xmat d N ω) (zt E u) := fun u => rfl
  rw [hGeq, hGeq]
  refine (norm_green_sqrt_sub_le_lip (Xmat_isHermitian d N ω) hE hs hsv hsw hv1 hw1).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  have hηw : 0 < etaT E w := etaT_pos_of_lt_one' hE hw1
  have hηt : 0 < etaT E t₀ := etaT_pos_of_lt_one' hE ht₀
  have hiv : (etaT E v)⁻¹ ≤ (etaT E t₀)⁻¹ := by
    exact inv_anti₀ hηt (etaT_le_of_le hE hv)
  have hiw : (etaT E w)⁻¹ ≤ (etaT E t₀)⁻¹ := by
    exact inv_anti₀ hηt (etaT_le_of_le hE hw)
  have hz : ‖zt E w‖ ≤ 3 := norm_zt_le_three' hE hw0 hw1.le
  have hivp : (0 : ℝ) < (etaT E v)⁻¹ := inv_pos.2 hηv
  have hiwp : (0 : ℝ) < (etaT E w)⁻¹ := inv_pos.2 hηw
  have hz0 : (0 : ℝ) ≤ ‖zt E w‖ := norm_nonneg _
  unfold greenLip
  have hnum : (etaT E v)⁻¹ * (1 + ‖zt E w‖ * (etaT E w)⁻¹)
      ≤ (etaT E t₀)⁻¹ * (1 + 3 * (etaT E t₀)⁻¹) := by
    have h1 : ‖zt E w‖ * (etaT E w)⁻¹ ≤ 3 * (etaT E t₀)⁻¹ :=
      mul_le_mul hz hiw hiwp.le (by norm_num)
    have h2 : (0 : ℝ) ≤ 1 + ‖zt E w‖ * (etaT E w)⁻¹ := by positivity
    exact mul_le_mul hiv (by linarith) h2 (by positivity)
  have hfirst : (etaT E v)⁻¹ * (1 + ‖zt E w‖ * (etaT E w)⁻¹) / (2 * s)
      ≤ (etaT E t₀)⁻¹ * (1 + 3 * (etaT E t₀)⁻¹) / (2 * s) := by
    apply div_le_div_of_nonneg_right hnum
    · positivity
  have hsecond : (etaT E v)⁻¹ * (etaT E w)⁻¹ ≤ (etaT E t₀)⁻¹ * (etaT E t₀)⁻¹ :=
    mul_le_mul hiv hiw hiwp.le (by positivity)
  linarith

/-- **The loop-level Lipschitz bound, for every `ω`.**  `n = |σ|` resolvents, `K = η_{t₀}^{-1}`
each, crude trace factor `LW`. -/
theorem norm_Lval_sub_le_lip (d : Dims) (N : ℕ) (ω : Ω d) {E t₀ s v w : ℝ} (hE : |E| < 2)
    (hs : 0 < s) (hsv : s ≤ v) (hsw : s ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.WF) :
    ‖(sample d).Lval E N v ω I - (sample d).Lval E N w ω I‖
      ≤ (d.L N : ℝ) * (d.W N : ℝ) * (I.σ.length : ℝ) * ((etaT E t₀)⁻¹) ^ I.σ.length
        * (|v - w| * greenLip E t₀ s) := by
  have ht0 : (0 : ℝ) ≤ t₀ := le_trans (le_trans hs.le hsv) hv
  have hv1 : v < 1 := lt_of_le_of_lt hv ht₀
  have hw1 : w < 1 := lt_of_le_of_lt hw ht₀
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  have hηw : 0 < etaT E w := etaT_pos_of_lt_one' hE hw1
  have hηt : 0 < etaT E t₀ := etaT_pos_of_lt_one' hE ht₀
  have hK : (1 : ℝ) ≤ (etaT E t₀)⁻¹ := one_le_inv_etaT hE ht0 ht₀
  have hGv : ‖green ((sample d).H N v ω) (zt E v)‖ ≤ (etaT E t₀)⁻¹ := by
    refine (Gauss.norm_green_le ((sample d).hermitian N v ω) hηv
      (by rw [← etaT_eq_zt_im, abs_of_pos hηv])).trans ?_
    exact inv_anti₀ hηt (etaT_le_of_le hE hv)
  have hGw : ‖green ((sample d).H N w ω) (zt E w)‖ ≤ (etaT E t₀)⁻¹ := by
    refine (Gauss.norm_green_le ((sample d).hermitian N w ω) hηw
      (by rw [← etaT_eq_zt_im, abs_of_pos hηw])).trans ?_
    exact inv_anti₀ hηt (etaT_le_of_le hE hw)
  exact norm_gloop_sub_le hK
    (mul_nonneg (abs_nonneg _) (greenLip_nonneg hE ht₀ hs)) ((sample d).hermitian N v ω) ((sample d).hermitian N w ω) hGv hGw
    (norm_green_flow_sub_le d N ω hE hs hsv hsw hv hw ht₀) I hwf

end GaussFlow

/-! ### 4. The primitive `K` moves Lipschitz-ly too

For the `2`-loop of Step 2, `K_{u,σ,(a₁,a₂)} = W⁻¹ m₁m₂ (Θ_{u m₁m₂})_{a₁a₂}` (2.57), and `Θ`
obeys its own resolvent identity `Θ_ξ - Θ_ζ = (ξ-ζ) Θ_ξ S^{(B)} Θ_ζ`.  Two row-sum bounds
(`RBM.sum_norm_Theta_row_le`, `RBM.sum_nnnorm_SB_row`) turn that into an **entrywise**
Lipschitz bound with no `L`-factor. -/

section PrimitiveLip

variable {L : ℕ} [NeZero L]

/-- **The resolvent identity for the propagator.** -/
theorem Theta_sub_eq (hL : 3 ≤ L) {ξ ζ : ℂ} (hξ : ‖ξ‖ < 1) (hζ : ‖ζ‖ < 1) :
    Theta L ξ - Theta L ζ = (ξ - ζ) • (Theta L ξ * SB L * Theta L ζ) := by
  have h1 : Theta L ξ * ((1 - ζ • SB L) * Theta L ζ) = Theta L ξ := by
    rw [mul_Theta L hL hζ, mul_one]
  have h2 : (Theta L ξ * (1 - ξ • SB L)) * Theta L ζ = Theta L ζ := by
    rw [Theta_mul L hL hξ, one_mul]
  calc Theta L ξ - Theta L ζ
      = Theta L ξ * ((1 - ζ • SB L) * Theta L ζ)
        - (Theta L ξ * (1 - ξ • SB L)) * Theta L ζ := by rw [h1, h2]
    _ = Theta L ξ * ((1 - ζ • SB L) - (1 - ξ • SB L)) * Theta L ζ := by noncomm_ring
    _ = Theta L ξ * ((ξ - ζ) • SB L) * Theta L ζ := by
        congr 2
        rw [sub_smul]
        abel
    _ = (ξ - ζ) • (Theta L ξ * SB L * Theta L ζ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]

/-- **The entrywise Lipschitz bound for `Θ`.**  No `L`-factor: the middle `S^{(B)}` is
stochastic and `Θ` has row sums `≤ (1-r)⁻¹`. -/
theorem norm_Theta_apply_sub_le (hL : 3 ≤ L) {ξ ζ : ℂ} {r : ℝ} (hr : r < 1)
    (hξ : ‖ξ‖ ≤ r) (hζ : ‖ζ‖ ≤ r) (a b : ZMod L) :
    ‖Theta L ξ a b - Theta L ζ a b‖ ≤ ‖ξ - ζ‖ * ((1 - r)⁻¹ * (1 - r)⁻¹) := by
  have hξ1 : ‖ξ‖ < 1 := lt_of_le_of_lt hξ hr
  have hζ1 : ‖ζ‖ < 1 := lt_of_le_of_lt hζ hr
  have hr0 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) hξ
  have hinv : (0 : ℝ) < (1 - r)⁻¹ := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  have hmono : ∀ {x : ℂ}, ‖x‖ ≤ r → (1 - ‖x‖)⁻¹ ≤ (1 - r)⁻¹ := by
    intro x hx
    have h1 : (0 : ℝ) < 1 - r := by linarith
    have h2 : (0 : ℝ) < 1 - ‖x‖ := by linarith [hx, hr]
    exact inv_anti₀ h1 (by linarith)
  -- row sums of `Θ_ξ S`
  have hrow : ∑ p : ZMod L, ‖(Theta L ξ * SB L) a p‖ ≤ (1 - r)⁻¹ := by
    have hstep : ∀ p : ZMod L, ‖(Theta L ξ * SB L) a p‖
        ≤ ∑ q : ZMod L, ‖Theta L ξ a q‖ * ‖SB L q p‖ := by
      intro p
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun q _ => norm_mul _ _
    calc ∑ p : ZMod L, ‖(Theta L ξ * SB L) a p‖
        ≤ ∑ p : ZMod L, ∑ q : ZMod L, ‖Theta L ξ a q‖ * ‖SB L q p‖ :=
          Finset.sum_le_sum fun p _ => hstep p
      _ = ∑ q : ZMod L, ‖Theta L ξ a q‖ * ∑ p : ZMod L, ‖SB L q p‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ q : ZMod L, ‖Theta L ξ a q‖ := by
          exact Finset.sum_congr rfl fun q _ => by rw [sum_norm_SB_row hL q, mul_one]
      _ ≤ (1 - ‖ξ‖)⁻¹ := sum_norm_Theta_row_le L hL hξ1 a
      _ ≤ (1 - r)⁻¹ := hmono hξ
  have hmid : ‖(Theta L ξ * SB L * Theta L ζ) a b‖ ≤ (1 - r)⁻¹ * (1 - r)⁻¹ := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p : ZMod L, ‖(Theta L ξ * SB L) a p * Theta L ζ p b‖
        ≤ ∑ p : ZMod L, ‖(Theta L ξ * SB L) a p‖ * (1 - r)⁻¹ := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            ((norm_Theta_apply_le L hL hζ1 p b).trans (hmono hζ)) (norm_nonneg _)
      _ = (∑ p : ZMod L, ‖(Theta L ξ * SB L) a p‖) * (1 - r)⁻¹ := by
          rw [Finset.sum_mul]
      _ ≤ (1 - r)⁻¹ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right hrow hinv.le
  have hsub := congrFun (congrFun (Theta_sub_eq (L := L) hL hξ1 hζ1) a) b
  rw [Matrix.sub_apply] at hsub
  rw [hsub, Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left hmid (norm_nonneg _)

variable {W : ℕ}

/-- **`K` for the `2`-loop is Lipschitz in the time**, with constant `W⁻¹(1-t₀)⁻²`. -/
theorem norm_kTwo_sub_le (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {t₀ v w : ℝ}
    (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1)
    (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    ‖kTwo L W (mSigma E) v σ₁ σ₂ a₁ a₂ - kTwo L W (mSigma E) w σ₁ σ₂ a₁ a₂‖
      ≤ (W : ℝ)⁻¹ * (|v - w| * ((1 - t₀)⁻¹ * (1 - t₀)⁻¹)) := by
  set μ : ℂ := mSigma E σ₁ * mSigma E σ₂ with hμ
  have hμn : ‖μ‖ = 1 := by
    rw [hμ, norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]
  have hnorm : ∀ u : ℝ, ‖((u : ℂ)) * μ‖ = |u| := by
    intro u; rw [norm_mul, hμn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hv' : ‖((v : ℂ)) * μ‖ ≤ t₀ := by rw [hnorm]; rwa [abs_of_nonneg hv0]
  have hw' : ‖((w : ℂ)) * μ‖ ≤ t₀ := by rw [hnorm]; rwa [abs_of_nonneg hw0]
  have hdiff : ((v : ℂ)) * μ - ((w : ℂ)) * μ = (((v - w : ℝ)) : ℂ) * μ := by
    push_cast; ring
  have hdn : ‖((v : ℂ)) * μ - ((w : ℂ)) * μ‖ = |v - w| := by
    rw [hdiff, norm_mul, hμn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hΘ := norm_Theta_apply_sub_le (L := L) hL (r := t₀) ht₀ hv' hw' a₁ a₂
  rw [hdn] at hΘ
  have hk : kTwo L W (mSigma E) v σ₁ σ₂ a₁ a₂ - kTwo L W (mSigma E) w σ₁ σ₂ a₁ a₂
      = ((W : ℂ)⁻¹ * μ) * (Theta L ((v : ℂ) * μ) a₁ a₂ - Theta L ((w : ℂ) * μ) a₁ a₂) := by
    simp only [kTwo, ← hμ]
    ring
  rw [hk, norm_mul, norm_mul, hμn, mul_one, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hΘ (by positivity)

end PrimitiveLip

/-! ### 5. `(L - K)` for the Step-2 loop: the transcription `resolvent → loop`

`RBM.Step2.lk = L - K` at `σ = (+,-)`, so §3 and §4 add up.  The constant is
`Kmod`-polynomial and the exponent is `γ = 1`. -/

section LkLip

open Gauss

/-- **The Lipschitz constant of `(L-K)_{u,(+,-),x}` on `[s, t₀] ⊆ (0,1)`**, for every `ω`. -/
noncomputable def lkLip (d : Dims) (N : ℕ) (E t₀ s : ℝ) : ℝ :=
  (d.L N : ℝ) * (d.W N : ℝ) * 2 * ((etaT E t₀)⁻¹) ^ 2 * greenLip E t₀ s
    + (d.W N : ℝ)⁻¹ * ((1 - t₀)⁻¹ * (1 - t₀)⁻¹)

theorem lkLip_nonneg (d : Dims) (N : ℕ) {E t₀ s : ℝ} (hE : |E| < 2) (ht₀ : t₀ < 1)
    (hs : 0 < s) : 0 ≤ lkLip d N E t₀ s := by
  have h := etaT_pos_of_lt_one' hE ht₀
  have h2 := greenLip_nonneg hE ht₀ hs
  have h3 : (0 : ℝ) < 1 - t₀ := by linarith
  unfold lkLip
  have : (0 : ℝ) ≤ (d.L N : ℝ) * (d.W N : ℝ) * 2 * ((etaT E t₀)⁻¹) ^ 2 := by positivity
  have h4 : (0 : ℝ) ≤ (d.W N : ℝ)⁻¹ * ((1 - t₀)⁻¹ * (1 - t₀)⁻¹) := by positivity
  nlinarith

/-- The Step-2 loop index, written out. -/
theorem idx_sigPM (d : Dims) (N : ℕ) (x : LoopArg (d.L N) 2) :
    LoopData.idx ((Step2.sigPM, x) : LoopData (d.L N) 2)
      = (⟨[true, false], [x 0, x 1]⟩ : LoopIdx (ZMod (d.L N))) := by
  simp [LoopData.idx, List.ofFn_succ, Step2.sigPM]

/-- **The transcription: `‖G_v - G_w‖ ⟹ |(L-K)_v - (L-K)_w|`.**  Lipschitz (`γ = 1`), for
**every** `ω` — `‖X‖` never enters, by `RBM.mul_green_smul`.  `0 < s` is essential. -/
theorem norm_lk_sub_le_lip (d : Dims) (N : ℕ) (ω : Ω d) {E t₀ s v w : ℝ} (hE : |E| < 2)
    (hs : 0 < s) (hsv : s ≤ v) (hsw : s ≤ w) (hv : v ≤ t₀) (hw : w ≤ t₀) (ht₀ : t₀ < 1)
    (x : LoopArg (d.L N) 2) :
    ‖Step2.lk (sample d) E N v ω x - Step2.lk (sample d) E N w ω x‖
      ≤ |v - w| * lkLip d N E t₀ s := by
  have hv0 : (0 : ℝ) ≤ v := le_trans hs.le hsv
  have hw0 : (0 : ℝ) ≤ w := le_trans hs.le hsw
  set I : LoopIdx (ZMod (d.L N)) := LoopData.idx ((Step2.sigPM, x) : LoopData (d.L N) 2) with hI
  have hwf : I.WF := LoopData.idx_wf _
  have hlen : I.σ.length = 2 := by rw [hI, idx_sigPM]; rfl
  have hsplit : Step2.lk (sample d) E N v ω x - Step2.lk (sample d) E N w ω x
      = ((sample d).Lval E N v ω I - (sample d).Lval E N w ω I)
        - ((band d).Kval E N v I - (band d).Kval E N w I) := by
    show ((sample d).Lval E N v ω I - (band d).Kval E N v I)
        - ((sample d).Lval E N w ω I - (band d).Kval E N w I) = _
    ring
  have hL := norm_Lval_sub_le_lip d N ω hE hs hsv hsw hv hw ht₀ I hwf
  rw [hlen] at hL
  have hKeq : ∀ u : ℝ, (band d).Kval E N u I
      = kTwo (d.L N) (d.W N) (mSigma E) u true false (x 0) (x 1) := by
    intro u
    show Kgen (d.L N) (d.W N) (mSigma E) u I = _
    rw [hI, idx_sigPM, Kgen_two]
  have hK := norm_kTwo_sub_le (L := d.L N) (W := d.W N) (d.three_le_L N) hE.le
    hv0 hw0 hv hw ht₀ true false (x 0) (x 1)
  rw [← hKeq v, ← hKeq w] at hK
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  unfold lkLip
  have harr : (d.L N : ℝ) * (d.W N : ℝ) * (2 : ℝ) * ((etaT E t₀)⁻¹) ^ 2
        * (|v - w| * greenLip E t₀ s)
      = |v - w| * ((d.L N : ℝ) * (d.W N : ℝ) * 2 * ((etaT E t₀)⁻¹) ^ 2 * greenLip E t₀ s) := by
    ring
  have hL' : ‖(sample d).Lval E N v ω I - (sample d).Lval E N w ω I‖
      ≤ |v - w| * ((d.L N : ℝ) * (d.W N : ℝ) * 2 * ((etaT E t₀)⁻¹) ^ 2 * greenLip E t₀ s) := by
    refine hL.trans (le_of_eq ?_)
    rw [← harr]
    push_cast
    ring
  have hK' : ‖(band d).Kval E N v I - (band d).Kval E N w I‖
      ≤ |v - w| * ((d.W N : ℝ)⁻¹ * ((1 - t₀)⁻¹ * (1 - t₀)⁻¹)) := by
    refine hK.trans (le_of_eq ?_); ring
  linarith [hL', hK']

end LkLip

/-! ### 7. The crude envelope of `(L-K)`, and what the last mile still needs

`RBM.norm_lk_le_crude` is the companion of §5: the *size* of `(L-K)` on the window, needed
wherever the modulus is divided by `T_{u,D}` (which is `≥ W^{-D}`).  Together, §5 and §7 give
every **random** ingredient of `RBM.MomentDuhamelCut.CutHypEvOn.modulus` for
`J = RBM.Step2FarMart.jSfarSm`; see the module docstring for the two purely deterministic
lemmas that are still missing. -/

section Envelope

open Gauss

/-- `‖(L-K)_{u,(+,-),x}‖ ≤ W⁻¹(η_{t₀}⁻² + (1-t₀)⁻¹)` on `[0, t₀]`, for every `ω`. -/
theorem norm_lk_le_crude (d : Dims) (N : ℕ) (ω : Ω d) {E t₀ u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu : u ≤ t₀) (ht₀ : t₀ < 1) (x : LoopArg (d.L N) 2) :
    ‖Step2.lk (sample d) E N u ω x‖
      ≤ (d.W N : ℝ)⁻¹ * ((etaT E t₀)⁻¹ * (etaT E t₀)⁻¹ + (1 - t₀)⁻¹) := by
  have hu1 : u < 1 := lt_of_le_of_lt hu ht₀
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hηt : 0 < etaT E t₀ := etaT_pos_of_lt_one' hE ht₀
  have hst : (0 : ℝ) < 1 - t₀ := by linarith
  set I : LoopIdx (ZMod (d.L N)) := LoopData.idx ((Step2.sigPM, x) : LoopData (d.L N) 2) with hI
  have hIeq : I = (⟨[true, false], [x 0, x 1]⟩ : LoopIdx (ZMod (d.L N))) := by
    rw [hI, idx_sigPM]
  have hwf : I.σ.length = I.a.length := LoopData.idx_wf _
  have hlen : I.a.length = 2 := by rw [hIeq]; rfl
  have hW0 : (0 : ℝ) < (d.W N : ℝ) := by
    have : 0 < d.W N := d.W_pos N
    exact_mod_cast this
  -- the loop
  have hL : ‖(sample d).Lval E N u ω I‖ ≤ (etaT E t₀)⁻¹ * (etaT E t₀)⁻¹ * (d.W N : ℝ)⁻¹ := by
    have h := norm_gloop_le_of_le_abs_im (L := d.L N) (W := d.W N)
      ((sample d).hermitian N u ω) hηu (by rw [← etaT_eq_zt_im, abs_of_pos hηu]) I hwf
      (by omega)
    rw [hlen] at h
    have hsimp : (etaT E u)⁻¹ ^ 2 * ((d.W N : ℝ))⁻¹ ^ (2 - 1)
        = (etaT E u)⁻¹ * (etaT E u)⁻¹ * ((d.W N : ℝ))⁻¹ := by
      norm_num [pow_two]
    rw [hsimp] at h
    refine h.trans ?_
    · have hiu : (etaT E u)⁻¹ ≤ (etaT E t₀)⁻¹ := inv_anti₀ hηt (etaT_le_of_le hE hu)
      have h0 : (0 : ℝ) ≤ (etaT E u)⁻¹ := (inv_pos.2 hηu).le
      have : (etaT E u)⁻¹ * (etaT E u)⁻¹ ≤ (etaT E t₀)⁻¹ * (etaT E t₀)⁻¹ :=
        mul_le_mul hiu hiu h0 (inv_pos.2 hηt).le
      exact mul_le_mul_of_nonneg_right this (by positivity)
  -- the primitive
  have hKeq : (band d).Kval E N u I
      = kTwo (d.L N) (d.W N) (mSigma E) u true false (x 0) (x 1) := by
    show Kgen (d.L N) (d.W N) (mSigma E) u I = _
    rw [hIeq, Kgen_two]
  have hK : ‖(band d).Kval E N u I‖ ≤ (1 - t₀)⁻¹ * (d.W N : ℝ)⁻¹ := by
    rw [hKeq]
    set μ : ℂ := mSigma E true * mSigma E false with hμ
    have hμn : ‖μ‖ = 1 := by
      rw [hμ, norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, one_mul]
    have hun : ‖((u : ℂ)) * μ‖ = u := by
      rw [norm_mul, hμn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
    have hu1' : ‖((u : ℂ)) * μ‖ < 1 := by rw [hun]; exact hu1
    have hΘ := norm_Theta_apply_le (d.L N) (d.three_le_L N) hu1' (x 0) (x 1)
    rw [hun] at hΘ
    have hmono : (1 - u)⁻¹ ≤ (1 - t₀)⁻¹ := inv_anti₀ hst (by linarith)
    have : kTwo (d.L N) (d.W N) (mSigma E) u true false (x 0) (x 1)
        = ((d.W N : ℂ)⁻¹ * μ) * Theta (d.L N) ((u : ℂ) * μ) (x 0) (x 1) := by
      simp only [kTwo, ← hμ]
    rw [this, norm_mul, norm_mul, hμn, mul_one, norm_inv, Complex.norm_natCast]
    have h1 : ‖Theta (d.L N) ((u : ℂ) * μ) (x 0) (x 1)‖ ≤ (1 - t₀)⁻¹ := hΘ.trans hmono
    calc (d.W N : ℝ)⁻¹ * ‖Theta (d.L N) ((u : ℂ) * μ) (x 0) (x 1)‖
        ≤ (d.W N : ℝ)⁻¹ * (1 - t₀)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 - t₀)⁻¹ * (d.W N : ℝ)⁻¹ := by ring
  have hsplit : Step2.lk (sample d) E N u ω x
      = (sample d).Lval E N u ω I - (band d).Kval E N u I := rfl
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have : (d.W N : ℝ)⁻¹ * ((etaT E t₀)⁻¹ * (etaT E t₀)⁻¹ + (1 - t₀)⁻¹)
      = (etaT E t₀)⁻¹ * (etaT E t₀)⁻¹ * (d.W N : ℝ)⁻¹ + (1 - t₀)⁻¹ * (d.W N : ℝ)⁻¹ := by ring
  rw [this]
  linarith

end Envelope


/-! ### 6. T252(乙): `hsep` on a concrete `Dims`

T249's counterexample carries the geometric hypothesis `hsep`: the two blocks are far enough
apart that `RBM.Step2FarMart.farChi = 1`, i.e. `12 ℓ*_v ≤ ‖a₁ - a₂‖` with
`ℓ*_v = (log W)^{3/2} ℓ̂(v)`.  At `RBM.Gauss.Dims.exampleGrow` (`L ∼ N^{1/4}`, `W ∼ N^{3/4}`)
this holds for large `N` at the antipodal pair `(⌊L/2⌋, 0)`: `(log W)^{3/2}` is `log`-sized and
`L/2` is a positive power of `N`.  So T249's verdict applies to a **real model**, not only
"if the hypothesis can be met". -/

section SepWitness

open Gauss

/-- `(log x)^8 ≤ 16^8 √x` for `1 ≤ x` — the `log`-versus-power estimate, by applying
`log y ≤ y - 1` to `y = x^{1/16}` (four nested square roots). -/
theorem log_pow_eight_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 8 ≤ 16 ^ 8 * Real.sqrt x := by
  have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
  set a := Real.sqrt x with ha
  set b := Real.sqrt a with hb
  set c := Real.sqrt b with hc
  set y := Real.sqrt c with hy
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = a := Real.sq_sqrt ha0
  have hc2 : c ^ 2 = b := Real.sq_sqrt hb0
  have hy2 : y ^ 2 = c := Real.sq_sqrt hc0
  have hy8 : y ^ 8 = a := by
    have : y ^ 8 = ((y ^ 2) ^ 2) ^ 2 := by ring
    rw [this, hy2, hc2, hb2]
  have hlogy : Real.log y = Real.log x / 16 := by
    rw [hy, Real.log_sqrt hc0, hc, Real.log_sqrt hb0, hb, Real.log_sqrt ha0, ha,
      Real.log_sqrt hx0]
    ring
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hylt : Real.log y ≤ y := by
    rcases eq_or_lt_of_le hy0 with h | h
    · rw [← h, Real.log_zero]
    · linarith [Real.log_le_sub_one_of_pos h]
  have hkey : Real.log x ≤ 16 * y := by rw [hlogy] at hylt; linarith
  calc Real.log x ^ 8 ≤ (16 * y) ^ 8 := pow_le_pow_left₀ hlogx0 hkey 8
    _ = 16 ^ 8 * y ^ 8 := by ring
    _ = 16 ^ 8 * Real.sqrt x := by rw [hy8]

/-- `N < 16 (L_N)^4` for the witness `RBM.Gauss.Dims.exampleGrow`: `L_N ≳ (N/16)^{1/4}`. -/
theorem lt_sixteen_mul_growL_pow (N : ℕ) : N < 16 * Dims.growL N ^ 4 := by
  have h1 : N < (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have h2 : Nat.sqrt N < (Nat.sqrt (Nat.sqrt N) + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have h3 : Nat.sqrt N + 1 ≤ (Nat.sqrt (Nat.sqrt N) + 1) ^ 2 := h2
  have hgM : Nat.sqrt (Nat.sqrt N) ≤ Dims.growL N := le_max_right _ _
  have h3M : 3 ≤ Dims.growL N := Dims.three_le_growL N
  calc N < (Nat.sqrt N + 1) ^ 2 := h1
    _ ≤ ((Nat.sqrt (Nat.sqrt N) + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = (Nat.sqrt (Nat.sqrt N) + 1) ^ 4 := by ring
    _ ≤ (2 * Dims.growL N) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    _ = 16 * Dims.growL N ^ 4 := by ring

/-- **The `log`-versus-power estimate, at `exampleGrow`**: `12 ℓ*_v ≤ ⌊L_N/2⌋` for large `N`,
uniformly over the window `(0, t₀]`. -/
theorem twelve_ellStar_le_half_exampleGrow {t₀ : ℝ} (ht₀ : t₀ < 1) (ht₀0 : 0 ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ v : ℝ, 0 < v → v ≤ t₀ →
      12 * ellStar ((Dims.growW N : ℝ)) (ellHat (Dims.growL N) (v : ℂ))
        ≤ ((Dims.growL N / 2 : ℕ) : ℝ) := by
  have hst : (0 : ℝ) < 1 - t₀ := by linarith
  set Cl : ℝ := 1 / Real.sqrt (1 - t₀) with hCl
  have hCl0 : 0 < Cl := by
    rw [hCl]; positivity
  set A : ℝ := 36 * Cl with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  have hlogW : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (Dims.growW N) := by
    have h := Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp Dims.tendsto_growW)
    exact h.eventually_ge_atTop 1
  have hbig : ∀ᶠ N : ℕ in atTop, (16 : ℝ) ^ 9 * A ^ 4 ≤ Real.sqrt N := by
    have h : Filter.Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop _
  filter_upwards [hlogW, hbig, eventually_ge_atTop 81] with N hlogWN hbigN hN81 v hv0 hvt
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht₀
  have hM3 : 3 ≤ Dims.growL N := Dims.three_le_growL N
  have hM0 : (0 : ℝ) < (Dims.growL N : ℝ) := by
    have : (0 : ℕ) < Dims.growL N := by omega
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  -- (a) `ℓ̂(v) ≤ Cl`
  have hell : ellHat (Dims.growL N) (v : ℂ) ≤ Cl := by
    refine (min_le_left _ _).trans ?_
    have hnorm : ‖(1 : ℂ) - (v : ℂ)‖ = 1 - v := by
      have : (1 : ℂ) - (v : ℂ) = ((1 - v : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hnorm, hCl]
    have hs1 : Real.sqrt (1 - t₀) ≤ Real.sqrt (1 - v) := Real.sqrt_le_sqrt (by linarith)
    have hs0 : 0 < Real.sqrt (1 - t₀) := Real.sqrt_pos.2 hst
    exact one_div_le_one_div_of_le hs0 hs1
  have hell0 : 0 < ellHat (Dims.growL N) (v : ℂ) := Step3.ellHat_pos_of_lt_one (by omega) hv1
  -- (b) `ℓ*_v ≤ (log N)^2 Cl`
  have hWN : (Dims.growW N : ℝ) ≤ (N : ℝ) := by
    have : Dims.growW N ≤ N := by
      rw [Dims.growW_eq N hN81]
      exact Nat.div_le_self _ _
    exact_mod_cast this
  have hlogWle : Real.log (Dims.growW N) ≤ Real.log N := by
    have hpos : (0 : ℝ) < (Dims.growW N : ℝ) := by
      have h1 : (1 : ℕ) ≤ Dims.growW N := le_max_left _ _
      have : (1 : ℝ) ≤ (Dims.growW N : ℝ) := by exact_mod_cast h1
      linarith
    exact Real.log_le_log hpos hWN
  have hstar : ellStar ((Dims.growW N : ℝ)) (ellHat (Dims.growL N) (v : ℂ))
      ≤ Real.log N ^ 2 * Cl := by
    unfold ellStar
    have h1 : Real.log (Dims.growW N) ^ (3 / 2 : ℝ) ≤ Real.log (Dims.growW N) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogWN (by norm_num)
    have h2 : Real.log (Dims.growW N) ^ (2 : ℝ) = Real.log (Dims.growW N) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h3 : Real.log (Dims.growW N) ^ 2 ≤ Real.log N ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlogWle 2
    have h4 : Real.log (Dims.growW N) ^ (3 / 2 : ℝ) ≤ Real.log N ^ 2 := by
      rw [h2] at h1; linarith
    have h5 : (0 : ℝ) ≤ Real.log (Dims.growW N) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    exact mul_le_mul h4 hell hell0.le (by positivity)
  -- (c) `36 Cl (log N)^2 ≤ L_N`
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hAlog : A * Real.log N ^ 2 ≤ (Dims.growL N : ℝ) := by
    have h4 : (A * Real.log N ^ 2) ^ 4 ≤ (Dims.growL N : ℝ) ^ 4 := by
      have hlog8 : Real.log N ^ 8 ≤ 16 ^ 8 * Real.sqrt N := log_pow_eight_le_sqrt hN1
      have hsq : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (by linarith)
      have hsq0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      have hNlt : (N : ℝ) < 16 * (Dims.growL N : ℝ) ^ 4 := by
        have := lt_sixteen_mul_growL_pow N
        exact_mod_cast this
      have hexp : (A * Real.log N ^ 2) ^ 4 = A ^ 4 * Real.log N ^ 8 := by ring
      have hstep : A ^ 4 * Real.log N ^ 8 ≤ A ^ 4 * (16 ^ 8 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hlog8 (by positivity)
      have hfin : A ^ 4 * (16 ^ 8 * Real.sqrt N) ≤ (N : ℝ) / 16 := by
        have h6 : (16 : ℝ) ^ 9 * A ^ 4 * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right hbigN hsq0
        rw [hsq] at h6
        nlinarith [h6]
      rw [hexp]
      nlinarith [hstep, hfin, hNlt]
    have hleft : 0 ≤ A * Real.log N ^ 2 := by positivity
    by_contra hcon
    push_neg at hcon
    have := pow_lt_pow_left₀ hcon (le_of_lt hM0) (n := 4) (by norm_num)
    linarith
  have hhalf : (Dims.growL N : ℝ) / 3 ≤ ((Dims.growL N / 2 : ℕ) : ℝ) := by
    have hnat : Dims.growL N ≤ 3 * (Dims.growL N / 2) := by omega
    have : (Dims.growL N : ℝ) ≤ 3 * ((Dims.growL N / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hfinal : 12 * (Real.log N ^ 2 * Cl) ≤ (Dims.growL N : ℝ) / 3 := by
    rw [hA] at hAlog
    nlinarith [hAlog]
  have h12 : 12 * ellStar ((Dims.growW N : ℝ)) (ellHat (Dims.growL N) (v : ℂ))
      ≤ 12 * (Real.log N ^ 2 * Cl) := by linarith
  linarith

/-- The antipodal pair `(⌊L/2⌋, 0)` of blocks. -/
def bHalf {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ) :
    ZMod (B.L N) × ZMod (B.L N) := ((((B.L N / 2 : ℕ)) : ZMod (B.L N)), 0)

theorem zdist_bHalf {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ) :
    (zdist (B.L N) ((bHalf B N).1 - (bHalf B N).2) : ℝ) = ((B.L N / 2 : ℕ) : ℝ) := by
  have hL : 3 ≤ B.L N := B.three_le_L N
  have hlt : B.L N / 2 < B.L N := Nat.div_lt_self (by omega) (by norm_num)
  have hval : (((B.L N / 2 : ℕ) : ZMod (B.L N))).val = B.L N / 2 := ZMod.val_cast_of_lt hlt
  have h0 : (bHalf B N).1 - (bHalf B N).2 = (((B.L N / 2 : ℕ)) : ZMod (B.L N)) := by
    simp [bHalf]
  rw [h0, zdist, hval]
  have : B.L N / 2 ≤ B.L N - B.L N / 2 := by omega
  rw [min_eq_left this]

theorem bHalf_fst_ne_snd {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (N : ℕ) :
    (bHalf B N).1 ≠ (bHalf B N).2 := by
  have hL : 3 ≤ B.L N := B.three_le_L N
  have hlt : B.L N / 2 < B.L N := Nat.div_lt_self (by omega) (by norm_num)
  have hval : (((B.L N / 2 : ℕ) : ZMod (B.L N))).val = B.L N / 2 := ZMod.val_cast_of_lt hlt
  intro hcon
  have : (((B.L N / 2 : ℕ) : ZMod (B.L N))) = 0 := hcon
  rw [this] at hval
  have hz : ((0 : ZMod (B.L N))).val = 0 := by
    haveI : NeZero (B.L N) := ⟨by omega⟩
    simp
  omega

/-- **T252(乙): `hsep` holds for a real model.**  At `RBM.Gauss.Dims.exampleGrow`, the pair
`(⌊L_N/2⌋, 0)` meets T249's geometric hypothesis for large `N`, uniformly over `(0, t_N]` with
`t_N ≤ t₀ < 1`.  Feeding this to `RBM.not_cutHypEv_swapSample_of_far` /
`RBM.not_entryModulusEv_swapSample_of_far` turns T249's verdict into an unconditional
statement about the witness model. -/
theorem hsep_exampleGrow {t : ℕ → ℝ} {t₀ : ℝ} (ht₀ : t₀ < 1) (ht₀0 : 0 ≤ t₀)
    (htt : ∀ᶠ N : ℕ in atTop, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop,
      (bHalf (band Dims.exampleGrow) N).1 ≠ (bHalf (band Dims.exampleGrow) N).2 ∧
      ∀ v ∈ Set.Ioc (0 : ℝ) (t N),
        Step2FarMart.farChi (((band Dims.exampleGrow).W N : ℕ) : ℝ)
          ((band Dims.exampleGrow).ell N v)
          (zdist ((band Dims.exampleGrow).L N)
            ((bHalf (band Dims.exampleGrow) N).1
              - (bHalf (band Dims.exampleGrow) N).2)) = 1 := by
  have hW2 : ∀ᶠ N : ℕ in atTop, 2 ≤ Dims.growW N :=
    Dims.tendsto_growW.eventually_ge_atTop 2
  filter_upwards [htt, twelve_ellStar_le_half_exampleGrow ht₀ ht₀0, hW2] with N htN harith hW2N
  refine ⟨bHalf_fst_ne_snd _ _, fun v hv => ?_⟩
  have hv0 : 0 < v := hv.1
  have hvt : v ≤ t₀ := le_trans hv.2 htN
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht₀
  have hLeq : (band Dims.exampleGrow).L N = Dims.growL N := rfl
  have hWeq : (band Dims.exampleGrow).W N = Dims.growW N := rfl
  have helleq : (band Dims.exampleGrow).ell N v = ellHat (Dims.growL N) (v : ℂ) := rfl
  have hell0 : 0 < ellHat (Dims.growL N) (v : ℂ) :=
    Step3.ellHat_pos_of_lt_one (by have := Dims.three_le_growL N; omega) hv1
  have hW2r : (2 : ℝ) ≤ ((Dims.growW N : ℕ) : ℝ) := by exact_mod_cast hW2N
  have hstar : 0 < ellStar ((Dims.growW N : ℕ) : ℝ) (ellHat (Dims.growL N) (v : ℂ)) :=
    Step2FarMart.ellStar_pos_of_two_le hW2r hell0
  rw [hWeq, helleq]
  refine Step2FarMart.farChi_eq_one hstar ?_
  rw [zdist_bHalf, hLeq]
  exact harith v hv0 hvt


end SepWitness

/-! ### 8. Satisfiability witnesses

Every hypothesis above is met simultaneously by a concrete model, on a **non-degenerate**
window whose left endpoint is positive (`s = 1/4`), so none of §3–§7 is vacuous.  The Lipschitz
constant is a positive real, not `0` and not `∞`. -/

section Witness

open Gauss

/-- The window `[1/4, 1/2]` at `E = 0` on `RBM.Gauss.Dims.exampleGrow`: `§5` instantiates. -/
example (N : ℕ) (ω : Ω Dims.exampleGrow) (x : LoopArg (Dims.exampleGrow.L N) 2)
    {v w : ℝ} (hv : v ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) (hw : w ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    ‖Step2.lk (sample Dims.exampleGrow) 0 N v ω x
        - Step2.lk (sample Dims.exampleGrow) 0 N w ω x‖
      ≤ |v - w| * lkLip Dims.exampleGrow N 0 (1 / 2) (1 / 4) :=
  norm_lk_sub_le_lip Dims.exampleGrow N ω (by norm_num) (by norm_num) hv.1 hw.1 hv.2 hw.2
    (by norm_num) x

/-- The constant is **strictly positive** (so the bound is not the degenerate `≤ 0`). -/
example (N : ℕ) : 0 < lkLip Dims.exampleGrow N 0 (1 / 2) (1 / 4) := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hη := etaT_pos_of_lt_one' hE (show (1 : ℝ) / 2 < 1 by norm_num)
  have hg : 0 ≤ greenLip 0 (1 / 2) (1 / 4) :=
    greenLip_nonneg hE (by norm_num) (by norm_num)
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
    have : 0 < Dims.exampleGrow.W N := Dims.exampleGrow.W_pos N
    exact_mod_cast this
  have hL : (0 : ℝ) < (Dims.exampleGrow.L N : ℝ) := by
    have : 0 < Dims.exampleGrow.L N := by have := Dims.exampleGrow.three_le_L N; omega
    exact_mod_cast this
  have key : lkLip Dims.exampleGrow N 0 (1 / 2) (1 / 4)
      = (Dims.exampleGrow.L N : ℝ) * (Dims.exampleGrow.W N : ℝ) * 2
          * ((etaT 0 (1 / 2))⁻¹) ^ 2 * greenLip 0 (1 / 2) (1 / 4)
        + (Dims.exampleGrow.W N : ℝ)⁻¹ * ((1 - 1 / 2 : ℝ)⁻¹ * (1 - 1 / 2 : ℝ)⁻¹) := rfl
  rw [key]
  have h1 : (0 : ℝ) ≤ (Dims.exampleGrow.L N : ℝ) * (Dims.exampleGrow.W N : ℝ) * 2
      * ((etaT 0 (1 / 2))⁻¹) ^ 2 * greenLip 0 (1 / 2) (1 / 4) := by positivity
  have h2 : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ)⁻¹
      * ((1 - 1 / 2 : ℝ)⁻¹ * (1 - 1 / 2 : ℝ)⁻¹) := by positivity
  linarith

/-- **`hsep` at a concrete window**: `t_N ≡ 1/4`, `t₀ = 1/2`. -/
theorem hsep_exampleGrow_quarter :
    ∀ᶠ N : ℕ in atTop,
      (bHalf (band Dims.exampleGrow) N).1 ≠ (bHalf (band Dims.exampleGrow) N).2 ∧
      ∀ v ∈ Set.Ioc (0 : ℝ) ((fun _ : ℕ => (1 : ℝ) / 4) N),
        Step2FarMart.farChi (((band Dims.exampleGrow).W N : ℕ) : ℝ)
          ((band Dims.exampleGrow).ell N v)
          (zdist ((band Dims.exampleGrow).L N)
            ((bHalf (band Dims.exampleGrow) N).1
              - (bHalf (band Dims.exampleGrow) N).2)) = 1 :=
  hsep_exampleGrow (t₀ := 1 / 2) (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall fun _ => by norm_num)

end Witness

end RBM



/-!
## Deviations (T252a)

**Paper location**: §5.3, (5.43)/(5.46)/(5.48); (2.57) for the primitive; (5.27) for `T_{u,D}`.

1. **`0 < s` is an explicit hypothesis of every Lipschitz statement here**
   (`RBM.norm_green_flow_sub_le`, `RBM.norm_Lval_sub_le_lip`, `RBM.norm_lk_sub_le_lip`).  The
   paper runs (5.43)–(5.48) on `[s, t]` without ever saying `s > 0`, and the grid of
   Theorem 2.21 really does start at `s ≡ 0`.  T249's `RBM.not_entryModulusEv_swapSample_of_far`
   shows the `s = 0` statement is **false**, so this is not a convenience: it is a repair.
   *Change the paper?* Yes — §5.3 should state `s_N ≥ N^{-C}` (or restrict the modulus to an
   event).  *Lines*: one sentence at the start of §5.3.  *Renumbering*: no.
2. **Crude combinatorial constants.**  `RBM.norm_gloop_sub_le` pays a factor `L·W` for the
   trace (`|⟨M⟩| ≤ (LW)‖M‖_op`) where the paper's (5.2)-style bookkeeping would give `W^{-n+1}`,
   and `RBM.norm_gloopProd_sub_le` bounds `‖E_a‖ ≤ 1` rather than `W⁻¹`.  Both only inflate
   `Kmod` by a bounded power of `N`; the project rule "常数不求最优" covers this.
   *Change the paper?* No.  *Renumbering*: no.
3. **`γ = 1`, not `1/2`.**  The paper's modulus in (5.46) is used only through "the net is fine
   enough"; on `s > 0` the flow is genuinely Lipschitz (`RBM.mul_green_smul` removes `X`), which
   is strictly stronger than the Hölder-`1/2` form `RBM.Gauss.abs_llErr_sub_le` gives via
   `‖X‖`.  *Change the paper?* Optional (a strengthening).  *Renumbering*: no.
4. **File move, not a mathematical deviation.**  `RBM.isHermitian_real_smul`,
   `RBM.mul_green_smul`, `RBM.norm_green_sqrt_sub_le`, `RBM.norm_green_sqrt_sub_le_lip` were
   moved here verbatim from `RBM1D/Flow/Eq548Producer.lean` (§0) so that `RBM1D/Gauss/` can use
   them without importing `RBM1D/Flow/`.  Signatures unchanged; `rfl` probes left at the old
   site.
-/
