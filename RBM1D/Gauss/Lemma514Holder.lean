/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step1Hyp
import RBM1D.Gauss.Lemma514Moment

/-!
# A Hölder modulus in the time for the moment route to Lemma 5.14

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2.

The moment route to Lemma 5.14 (`RBM.Step3.Lemma514`) needs a **deterministic modulus of
continuity in the time** of

`ξ_N(u, q, ω) = (W ℓ_u η_u)^m ‖(L - K)_{u,σ,a}‖`,

on a high-probability event, with a polynomially large constant:
`|ξ_N(u) - ξ_N(v)| ≤ N^K |u - v|^γ`.  This file proves its ingredients with explicit
constants: the modulus itself (`RBM.Gauss.abs_scaleLK_sub_le`) and a polynomial bound on its
constant (`RBM.Gauss.scaleLK_const_le`).

## The three pieces

It has three pieces.  The first is in `RBM1D/Gauss/Step1Hyp.lean`:

1. *the product of `m` resolvents* — `RBM.Gauss.norm_gloop_sub_le` (the telescoping estimate for
   `RBM.gloop`) and its Gaussian instance `RBM.Gauss.norm_Lval_sub_le_sqrt` are proved
   in `RBM1D/Gauss/Step1Hyp.lean`.  They are used below as they stand.
2. *the modulus of `RBM.Band.Kval = RBM.Kgen` in `u`* — this file.  `RBM.hasDerivAt_Kgen_all`
   says `u ↦ K_{u,σ,a}` is differentiable with derivative `RBM.primRhs`, and `primRhs` is a
   finite sum of *products of two `K`'s* against one row of `S^{(B)}`; `RBM.norm_primRhs_le`
   below bounds it by `W n² L B²` when `B` bounds the `K`'s of length `≤ n`, and the mean value
   inequality turns that into a **Lipschitz** modulus.
3. *the modulus of `(W ℓ_u η_u)^m` in `u`* — this file, `RBM.abs_ellHat_sub_le` and
   `RBM.Gauss.abs_scale_pow_sub_le`.  `ℓ̂` is `min((1-u)^{-1/2}, L)`; it is **only** `1/2`-Hölder
   near `u = 1`, with constant `(1-T)^{-1}`, which is why `γ = 1/2` here as well — the same
   exponent the `√u` of the flow already forces.

## Main statements

### 1. The modulus

* `RBM.abs_ellHat_sub_le`          — `|ℓ̂(u) - ℓ̂(v)| ≤ (1-T)^{-1}|u-v|^{1/2}` on `[0,T]`, `T < 1`
* `RBM.Gauss.abs_scale_sub_le`,
  `RBM.Gauss.abs_scale_pow_sub_le`  — the same for `W ℓ_u η_u` and for its `m`-th power
* `RBM.norm_primRhs_le`             — `‖(2.48)‖ ≤ W n² L B²`
* `RBM.norm_Kgen_sub_le`,
  `RBM.norm_Kgen_sub_le'`           — `|K_{u,σ,a} - K_{v,σ,a}| ≤ W n² L B² |u-v|`
* `RBM.Gauss.norm_lkT_flow_sub_le`,
  `RBM.Gauss.norm_lkT_flow_le`      — the modulus and the envelope of `(L-K)_{u,σ,a}`
* `RBM.Gauss.abs_scaleLK_sub_le`    — the modulus of `(W ℓ_u η_u)^m ‖(L-K)_{u,σ,a}‖`, explicit
* `RBM.Gauss.scaleLK_const_le`      — and that constant is `≤ (m²+5m) R^{3m+4}`
* `RBM.Gauss.exists_highProb_normX` — a nonempty high-probability event on which
  `‖X_N‖ + 1 ≤ N^c`

### 2. The envelope of `K`, on every ring length

The modulus uses a polynomial envelope on `K` over the loop lengths `2 … m`.  That envelope
is (2.59)–(2.60):

* `RBM.Gauss.exists_norm_Kval_le_upto` — one constant for all lengths `2 … m`, from
  `RBM.Band.norm_Kval_le` ((2.59) for `n ≥ 3`, Example 2.15 for `n = 2`, (2.60) for `n = 1`)
* `RBM.Gauss.eventually_le_rpow_mono` — a polynomial envelope `≤ N^c` stays true for a larger
  exponent

## What the constant really is

Everything is explicit; nothing is asymptotic.  Writing `η = η_{t_N}`, `X = ‖X_N‖`, `S = W ℓ η`
for the scale and `B` for the envelope of the `K`'s, `RBM.Gauss.abs_scaleLK_sub_le` reads

`|S_u^m‖(L-K)_u‖ - S_v^m‖(L-K)_v‖|`
`  ≤ [ m (WL)^{m-1} W((1-T)^{-1}+L) · (η^{-m} + B)`
`      + (WL)^m ( m η^{-(m+1)}(X+1) + W m² L B² ) ] · |u-v|^{1/2}`.

`RBM.Gauss.scaleLK_const_le` collapses that to `(m² + 5m) R^{3m+4}` once one `R ≥ 1` dominates
`W`, `L`, `(1-T)^{-1}`, `η^{-1}`, `B` and `‖X‖+1`.  **`0 < s N` is never used.**

## One loop length at a time

The constant cannot be chosen uniformly in the loop length `m`: the modulus of a product of `m`
resolvents carries `η^{-(m+1)}`, and `η^{-1}` is a positive power of `N` in the regime, so the
constant grows geometrically in `m`.  The estimates here are therefore stated for one `m` at a
time, with a per-`m` constant.
-/

namespace RBM

open scoped Matrix.Norms.L2Operator

/-! ### The decay length `ℓ̂` is `1/2`-Hölder in the time -/

/-- `|min a c - min b c| ≤ |a - b|`: taking a minimum against a fixed constant is a
contraction. -/
theorem abs_min_sub_min_right_le (a b c : ℝ) : |min a c - min b c| ≤ |a - b| := by
  refine (abs_min_sub_min_le_max a c b c).trans ?_
  simp

/-- **`ℓ̂` is `1/2`-Hölder on `[0, T]`, `T < 1`, with constant `(1-T)^{-1}`.**

`ℓ̂(u) = min((1-u)^{-1/2}, L)`, and taking the minimum against `L` only helps, so it suffices to
bound `|(1-u)^{-1/2} - (1-v)^{-1/2}|`.  Writing it as
`|√(1-v) - √(1-u)| / (√(1-u)√(1-v))`, the numerator is `≤ √|u-v|` (`RBM.abs_sqrt_sub_sqrt_le`)
and the denominator is `≥ 1 - T`.

The exponent `1/2` is sharp: near `u = 1` the function `ℓ̂` is genuinely only Hölder. -/
theorem abs_ellHat_sub_le (L : ℕ) {T u v : ℝ} (hT : T < 1) (hu : u ∈ Set.Icc (0 : ℝ) T)
    (hv : v ∈ Set.Icc (0 : ℝ) T) :
    |ellHat L (u : ℂ) - ellHat L (v : ℂ)| ≤ (1 - T)⁻¹ * Real.sqrt |u - v| := by
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 hT
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 hT
  have hT0 : (0 : ℝ) < 1 - T := by linarith
  have hau : (0 : ℝ) < 1 - u := by linarith [hu.2]
  have hav : (0 : ℝ) < 1 - v := by linarith [hv.2]
  have hsu : Real.sqrt (1 - T) ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt (by linarith [hu.2])
  have hsv : Real.sqrt (1 - T) ≤ Real.sqrt (1 - v) := Real.sqrt_le_sqrt (by linarith [hv.2])
  have hsT : (0 : ℝ) < Real.sqrt (1 - T) := Real.sqrt_pos.2 hT0
  have hsu0 : (0 : ℝ) < Real.sqrt (1 - u) := lt_of_lt_of_le hsT hsu
  have hsv0 : (0 : ℝ) < Real.sqrt (1 - v) := lt_of_lt_of_le hsT hsv
  rw [ellHat_ofReal L hu1, ellHat_ofReal L hv1]
  refine (abs_min_sub_min_right_le _ _ _).trans ?_
  -- `1/√(1-u) - 1/√(1-v) = (√(1-v) - √(1-u)) / (√(1-u)√(1-v))`
  have hid : 1 / Real.sqrt (1 - u) - 1 / Real.sqrt (1 - v)
      = (Real.sqrt (1 - v) - Real.sqrt (1 - u)) / (Real.sqrt (1 - u) * Real.sqrt (1 - v)) := by
    field_simp
  have hnum : |Real.sqrt (1 - v) - Real.sqrt (1 - u)| ≤ Real.sqrt |u - v| := by
    have h := abs_sqrt_sub_sqrt_le hav.le hau.le
    have he : |(1 - v) - (1 - u)| = |u - v| := by
      rw [show (1 - v) - (1 - u) = u - v from by ring]
    rwa [he] at h
  have hden : (1 - T) ≤ Real.sqrt (1 - u) * Real.sqrt (1 - v) := by
    calc (1 - T) = Real.sqrt (1 - T) * Real.sqrt (1 - T) := (Real.mul_self_sqrt hT0.le).symm
      _ ≤ Real.sqrt (1 - u) * Real.sqrt (1 - v) := mul_le_mul hsu hsv hsT.le hsu0.le
  rw [hid, abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.sqrt (1-u) * Real.sqrt (1-v))]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (1-u) * Real.sqrt (1-v))]
  calc |Real.sqrt (1 - v) - Real.sqrt (1 - u)| ≤ Real.sqrt |u - v| := hnum
    _ = (1 - T)⁻¹ * Real.sqrt |u - v| * (1 - T) := by field_simp
    _ ≤ (1 - T)⁻¹ * Real.sqrt |u - v| * (Real.sqrt (1 - u) * Real.sqrt (1 - v)) := by
        have h0 : (0 : ℝ) ≤ (1 - T)⁻¹ * Real.sqrt |u - v| := by positivity
        exact mul_le_mul_of_nonneg_left hden h0

/-- `x ≤ √x` for `0 ≤ x ≤ 1`.  This is what lets a Lipschitz modulus be read as a
`1/2`-Hölder one on a window of length `≤ 1`. -/
theorem self_le_sqrt {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.sqrt x := by
  have h := Real.sqrt_le_sqrt (show x ^ 2 ≤ x by nlinarith)
  rwa [Real.sqrt_sq hx0] at h

/-- `|η_u - η_v| ≤ |u - v|`: `η_t = (1-t)\,\mathrm{Im}\,m^{(E)}` is Lipschitz with constant
`Im m ≤ 1`. -/
theorem abs_etaT_sub_le {E : ℝ} (hE : |E| ≤ 2) (u v : ℝ) :
    |etaT E u - etaT E v| ≤ |u - v| := by
  have h : etaT E u - etaT E v = (v - u) * (mE E).im := by
    show (1 - u) * (mE E).im - (1 - v) * (mE E).im = _
    ring
  have him : |(mE E).im| ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (mE E)
    rwa [norm_mE hE] at h1
  rw [h, abs_mul, abs_sub_comm v u]
  calc |u - v| * |(mE E).im| ≤ |u - v| * 1 :=
        mul_le_mul_of_nonneg_left him (abs_nonneg _)
    _ = |u - v| := mul_one _

/-! ### The primitive loop `K` is Lipschitz in the time -/

open Finset in
/-- **The right-hand side of the primitive equation (2.48) is bounded by `W n² L B²`.**

`RBM.primRhs` is a sum over the `≤ n²` pairs `1 ≤ k < l ≤ n` of
`∑_{a,b} K(G^{L}_{k,l,a})\,S^{(B)}_{ab}\,K(G^{R}_{k,l,b})`, and both cut-and-glued loops have
length between `2` and `n` (`RBM.LoopIdx.two_le_length_cutGlueL`,
`RBM.LoopIdx.length_cutGlueL_le`), so each is bounded by `B`.  The `b`-sum is then a single row
sum of `S^{(B)}`, which is `1` (`RBM.sum_norm_SB_row`), and the `a`-sum contributes the factor
`L`.

This is the analogue for the genuine `S^{(B)}` of `RBM.GUEPhase.norm_primRhsGUE_le` (7.34),
which is stated only for the GUE variance profile `S_{ab} = L^{-1}`. -/
theorem norm_primRhs_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) (K : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hI : I.WF) {Bk : ℝ} (hB0 : 0 ≤ Bk)
    (hB : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ Bk) :
    ‖primRhs L W K I‖ ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2 := by
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖∑ a : ZMod L, ∑ b : ZMod L,
          K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)‖ ≤ (L : ℝ) * Bk ^ 2 := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hBL : ∀ a : ZMod L, ‖K (I.cutGlueL k l a)‖ ≤ Bk := fun a =>
      hB _ (LoopIdx.WF.cutGlueL a hI hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
    have hBR : ∀ b : ZMod L, ‖K (I.cutGlueR k l b)‖ ≤ Bk := fun b =>
      hB _ (LoopIdx.WF.cutGlueR b hI hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
    calc ‖∑ a : ZMod L, ∑ b : ZMod L,
            K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)‖
        ≤ ∑ a : ZMod L, ∑ b : ZMod L,
            ‖K (I.cutGlueL k l a) * SB L a b * K (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : ZMod L, ∑ b : ZMod L, Bk ^ 2 * ‖SB L a b‖ := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul]
          calc ‖K (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖K (I.cutGlueR k l b)‖
              ≤ Bk * ‖SB L a b‖ * Bk :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hBL a) (norm_nonneg _)) (hBR b)
                  (norm_nonneg _) (by positivity)
            _ = Bk ^ 2 * ‖SB L a b‖ := by ring
      _ = ∑ _a : ZMod L, Bk ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum, sum_norm_SB_row hL a, mul_one]
      _ = (L : ℝ) * Bk ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  calc ‖primRhs L W K I‖
      ≤ (W : ℝ) * ∑ _k ∈ Icc 1 I.length, ∑ _l ∈ Ioc _k I.length, (L : ℝ) * Bk ^ 2 := by
        rw [primRhs, norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) * ∑ _k ∈ Icc 1 I.length, (I.length : ℝ) * ((L : ℝ) * Bk ^ 2) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have hle : ((I.length - k : ℕ) : ℝ) ≤ (I.length : ℝ) := by
          exact_mod_cast Nat.sub_le I.length k
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

/-- **The primitive loop `K_{u,σ,a}` is Lipschitz in `u` on `[0, T]`, `T < 1`.**

`RBM.hasDerivAt_Kgen_all` gives `d/du\,K_{u,σ,a} = `(2.48)`, and `RBM.norm_primRhs_le` bounds
that derivative by `W n² L B²` uniformly on the window, where `B` is any envelope for the `K`'s
of length between `2` and `n`.  The mean value inequality on the convex set `[0, T]` finishes.

Note the modulus is **Lipschitz**, not merely Hölder: the `1/2` of the final estimate comes
entirely from `√u` in the flow and from `ℓ̂` near `u = 1`
(`RBM.abs_ellHat_sub_le`), never from `K`. -/
theorem norm_Kgen_sub_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] {m : Bool → ℂ}
    (hm1 : ∀ s, ‖m s‖ ≤ 1) {T : ℝ} (hT : T < 1) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (h2 : 2 ≤ I.length) {Bk : ℝ} (hB0 : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) T, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      J.length ≤ I.length → ‖Kgen L W m w J‖ ≤ Bk)
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) :
    ‖Kgen L W m u I - Kgen L W m v I‖
      ≤ ((W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2) * |u - v| := by
  have hderiv : ∀ w ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r : ℝ => Kgen L W m r I)
        (primRhs L W (Kgen L W m w) I) (Set.Icc (0 : ℝ) T) w := by
    intro w hw
    exact (hasDerivAt_Kgen_all W m hL
      (fun s s' => lt_of_le_of_lt (norm_mul_le_of_mem_Icc m hm1 hw s s') hT) I hI
      h2).hasDerivWithinAt
  have hbnd : ∀ w ∈ Set.Icc (0 : ℝ) T, ‖primRhs L W (Kgen L W m w) I‖
      ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2 := fun w hw =>
    norm_primRhs_le hL W _ I hI hB0 (hB w hw)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) hderiv hbnd
    (convex_Icc (0 : ℝ) T) hv hu
  rwa [Real.norm_eq_abs] at h

/-- `RBM.norm_Kgen_sub_le` **without** the restriction `2 ≤ n`: on loops of length `0` and `1`
the tree representation is `0` and `m(σ₁)`, both constant in the time, so the same bound holds
trivially there. -/
theorem norm_Kgen_sub_le' {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] {m : Bool → ℂ}
    (hm1 : ∀ s, ‖m s‖ ≤ 1) {T : ℝ} (hT : T < 1) (I : LoopIdx (ZMod L)) (hI : I.WF)
    {Bk : ℝ} (hB0 : 0 ≤ Bk)
    (hB : ∀ w ∈ Set.Icc (0 : ℝ) T, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      J.length ≤ I.length → ‖Kgen L W m w J‖ ≤ Bk)
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) :
    ‖Kgen L W m u I - Kgen L W m v I‖
      ≤ ((W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2) * |u - v| := by
  rcases le_or_gt 2 I.length with h2 | h2
  · exact norm_Kgen_sub_le hL W hm1 hT I hI h2 hB0 hB hu hv
  · have hconst : Kgen L W m u I = Kgen L W m v I := by
      interval_cases h : I.length <;> simp [Kgen, h]
    rw [hconst, sub_self, norm_zero]
    positivity

end RBM

namespace RBM.Gauss

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

section BandScale

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The scale `W ℓ_u η_u` is `1/2`-Hölder in the time -/

/-- `W ℓ_u η_u ≤ W L`, since `ℓ_u ≤ L` and `η_u ≤ 1`. -/
theorem scale_le_mul {B : Band Ω} {E : ℝ} (hE : |E| < 2) (N : ℕ) {w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) : B.scale E N w ≤ (B.W N : ℝ) * (B.L N : ℝ) := by
  have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have hℓ : B.ell N w ≤ (B.L N : ℝ) := min_le_right _ _
  have hℓ0 : 0 ≤ B.ell N w := le_min (by positivity) (Nat.cast_nonneg _)
  have hη : etaT E w ≤ 1 := etaT_le_one hE hw0
  have hη0 : 0 ≤ etaT E w := (etaT_pos_of_lt_one' hE hw1).le
  show (B.W N : ℝ) * B.ell N w * etaT E w ≤ _
  calc (B.W N : ℝ) * B.ell N w * etaT E w ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 := by
        gcongr
    _ = (B.W N : ℝ) * (B.L N : ℝ) := mul_one _

/-- **The `1/2`-Hölder modulus of the scale `W ℓ_u η_u` on `[0, T]`, `T < 1`.**

The two factors move for different reasons: `ℓ̂` is only `1/2`-Hölder, with constant
`(1-T)^{-1}` (`RBM.abs_ellHat_sub_le`), while `η` is Lipschitz with constant `≤ 1`
(`RBM.abs_etaT_sub_le`) and `ℓ̂ ≤ L`. -/
theorem abs_scale_sub_le {B : Band Ω} {E : ℝ} (hE : |E| < 2) (N : ℕ) {T u v : ℝ}
    (hT : T < 1) (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) :
    |B.scale E N u - B.scale E N v|
      ≤ (B.W N : ℝ) * ((1 - T)⁻¹ + (B.L N : ℝ)) * Real.sqrt |u - v| := by
  have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) < 1 - T := by linarith
  have hηu : etaT E u ≤ 1 := etaT_le_one hE hu.1
  have hηu0 : 0 ≤ etaT E u := (etaT_pos_of_lt_one' hE (lt_of_le_of_lt hu.2 hT)).le
  have hℓv : B.ell N v ≤ (B.L N : ℝ) := min_le_right _ _
  have hℓv0 : 0 ≤ B.ell N v := le_min (by positivity) (Nat.cast_nonneg _)
  -- the window is shorter than `1`, so a Lipschitz modulus is a `1/2`-Hölder one
  have hlen : |u - v| ≤ 1 := by
    rw [abs_le]; constructor <;> [linarith [hu.1, hv.2]; linarith [hv.1, hu.2]]
  have hsq : |u - v| ≤ Real.sqrt |u - v| := self_le_sqrt (abs_nonneg _) hlen
  have hsq0 : (0 : ℝ) ≤ Real.sqrt |u - v| := Real.sqrt_nonneg _
  have hsplit : B.scale E N u - B.scale E N v
      = (B.W N : ℝ) * ((B.ell N u - B.ell N v) * etaT E u
          + B.ell N v * (etaT E u - etaT E v)) := by
    show (B.W N : ℝ) * B.ell N u * etaT E u - (B.W N : ℝ) * B.ell N v * etaT E v = _
    ring
  have hinner : |(B.ell N u - B.ell N v) * etaT E u + B.ell N v * (etaT E u - etaT E v)|
      ≤ ((1 - T)⁻¹ + (B.L N : ℝ)) * Real.sqrt |u - v| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |B.ell N u - B.ell N v| * |etaT E u|
        ≤ ((1 - T)⁻¹ * Real.sqrt |u - v|) * 1 := by
      refine mul_le_mul (abs_ellHat_sub_le _ hT hu hv) ?_ (abs_nonneg _) (by positivity)
      rw [abs_of_nonneg hηu0]; exact hηu
    have h2 : |B.ell N v| * |etaT E u - etaT E v|
        ≤ (B.L N : ℝ) * Real.sqrt |u - v| := by
      refine mul_le_mul ?_ ((abs_etaT_sub_le hE.le u v).trans hsq) (abs_nonneg _)
        (Nat.cast_nonneg _)
      rw [abs_of_nonneg hℓv0]; exact hℓv
    nlinarith [h1, h2]
  rw [hsplit, abs_mul, abs_of_nonneg hW]
  calc (B.W N : ℝ) * |(B.ell N u - B.ell N v) * etaT E u + B.ell N v * (etaT E u - etaT E v)|
      ≤ (B.W N : ℝ) * (((1 - T)⁻¹ + (B.L N : ℝ)) * Real.sqrt |u - v|) :=
        mul_le_mul_of_nonneg_left hinner hW
    _ = (B.W N : ℝ) * ((1 - T)⁻¹ + (B.L N : ℝ)) * Real.sqrt |u - v| := by ring

/-- **The `1/2`-Hölder modulus of `(W ℓ_u η_u)^m`.**  `|a^m - b^m| ≤ m\,|a-b|\max(a,b)^{m-1}`
(`abs_pow_sub_pow_le`) with `RBM.Gauss.abs_scale_sub_le` and `RBM.Gauss.scale_le_mul`. -/
theorem abs_scale_pow_sub_le {B : Band Ω} {E : ℝ} (hE : |E| < 2) (N m : ℕ) {T u v : ℝ}
    (hT : T < 1) (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) :
    |B.scale E N u ^ m - B.scale E N v ^ m|
      ≤ (m : ℝ) * ((B.W N : ℝ) * (B.L N : ℝ)) ^ (m - 1)
          * ((B.W N : ℝ) * ((1 - T)⁻¹ + (B.L N : ℝ))) * Real.sqrt |u - v| := by
  have hWL : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := by positivity
  have hsu : 0 < B.scale E N u := B.scale_pos' hE N hu.1 (lt_of_le_of_lt hu.2 hT)
  have hsv : 0 < B.scale E N v := B.scale_pos' hE N hv.1 (lt_of_le_of_lt hv.2 hT)
  have hmax : max |B.scale E N u| |B.scale E N v| ≤ (B.W N : ℝ) * (B.L N : ℝ) := by
    rw [abs_of_pos hsu, abs_of_pos hsv, max_le_iff]
    exact ⟨scale_le_mul hE N hu.1 (lt_of_le_of_lt hu.2 hT),
      scale_le_mul hE N hv.1 (lt_of_le_of_lt hv.2 hT)⟩
  refine (_root_.abs_pow_sub_pow_le _ _ m).trans ?_
  have hkey : |B.scale E N u - B.scale E N v| * (m : ℝ)
      ≤ ((B.W N : ℝ) * ((1 - T)⁻¹ + (B.L N : ℝ))) * Real.sqrt |u - v| * (m : ℝ) :=
    mul_le_mul_of_nonneg_right (abs_scale_sub_le hE N hT hu hv) (Nat.cast_nonneg _)
  have hpow : max |B.scale E N u| |B.scale E N v| ^ (m - 1)
      ≤ ((B.W N : ℝ) * (B.L N : ℝ)) ^ (m - 1) :=
    pow_le_pow_left₀ (le_trans (abs_nonneg _) (le_max_left _ _)) hmax _
  calc |B.scale E N u - B.scale E N v| * (m : ℝ) * max |B.scale E N u| |B.scale E N v| ^ (m - 1)
      ≤ ((B.W N : ℝ) * ((1 - T)⁻¹ + (B.L N : ℝ))) * Real.sqrt |u - v| * (m : ℝ)
          * ((B.W N : ℝ) * (B.L N : ℝ)) ^ (m - 1) := by
        refine mul_le_mul hkey hpow (pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _) ?_
        positivity
    _ = _ := by ring

end BandScale

/-! ### The modulus of `(L - K)_{u,σ,a}` along the Gaussian flow -/

/-- **The product rule for moduli.**  `a_u f_u - a_v f_v = (a_u - a_v) f_u + a_v (f_u - f_v)`,
so a modulus for `a` and one for `f`, together with envelopes for `f_u` and `a_v`, give one for
the product.  This is the shape in which the scale `(W ℓ_u η_u)^m` and the loop difference
`‖(L-K)_{u,σ,a}‖` are put together. -/
theorem abs_mul_sub_mul_le {au av fu fv Ba Bf Ca Cf δ : ℝ}
    (hfu0 : 0 ≤ fu) (hav0 : 0 ≤ av) (hδ0 : 0 ≤ δ) (hCa0 : 0 ≤ Ca)
    (hBf : fu ≤ Bf) (hBa : av ≤ Ba)
    (ha : |au - av| ≤ Ca * δ) (hf : |fu - fv| ≤ Cf * δ) :
    |au * fu - av * fv| ≤ (Ca * Bf + Ba * Cf) * δ := by
  rw [show au * fu - av * fv = (au - av) * fu + av * (fu - fv) from by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hfu0, abs_of_nonneg hav0]
  have h1 : |au - av| * fu ≤ (Ca * δ) * Bf :=
    mul_le_mul ha hBf hfu0 (by positivity)
  have h2 : av * |fu - fv| ≤ Ba * (Cf * δ) :=
    mul_le_mul hBa hf (abs_nonneg _) (le_trans hav0 hBa)
  calc |au - av| * fu + av * |fu - fv| ≤ (Ca * δ) * Bf + Ba * (Cf * δ) := add_le_add h1 h2
    _ = (Ca * Bf + Ba * Cf) * δ := by ring

variable (d : Dims)

/-- `‖K_{w,σ,a}‖ ≤ B` on loops of length exactly `n ≥ 1`: for `n ≥ 2` this is the envelope
hypothesis, and for `n = 1` the tree representation is `m(σ₁)`, of norm `≤ 1 ≤ B`. -/
theorem norm_Kval_le_of_envelope (N : ℕ) {E : ℝ} (hE : |E| < 2) (w : ℝ) {n : ℕ} (hn : 1 ≤ n)
    {Bk : ℝ} (hBk1 : 1 ≤ Bk) (I : LoopIdx (ZMod ((band d).L N))) (hIwf : I.WF)
    (hlen : I.length = n)
    (hKb : ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(band d).Kval E N w J‖ ≤ Bk) :
    ‖(band d).Kval E N w I‖ ≤ Bk := by
  rcases le_or_gt 2 n with h2 | h2
  · exact hKb I hIwf (by omega) (by omega)
  · have hlen1 : I.length = 1 := by omega
    have hK : (band d).Kval E N w I = mSigma E (I.σ.getD 0 false) := by
      show Kgen ((band d).L N) ((band d).W N) (mSigma E) w I = _
      rw [Kgen]
      exact ite_eq_left_of_eq_true _ _ (eq_true hlen1)
    rw [hK]
    exact (norm_mSigma_le_one hE _).trans hBk1

/-- **The modulus of `(L - K)_{u,σ,a}` in the time, along the Gaussian flow.**

`L - K` moves for two reasons, and this is the sum of the two:

* the `m` resolvents of `L_{u,σ,a}` move, and their product moves by `m` times as much
  (`RBM.Gauss.norm_Lval_sub_le_sqrt`, on top of `RBM.Gauss.norm_green_flow_sub_le`);
  this half is only `1/2`-Hölder, because `H_u = √u X`;
* `K_{u,σ,a}` moves, and this half is **Lipschitz** (`RBM.norm_Kgen_sub_le'`); a Lipschitz
  modulus is also a `1/2`-Hölder one on a window of length `≤ 1`. -/
theorem norm_lkT_flow_sub_le (N : ℕ) {E : ℝ} (hE : |E| < 2) {T : ℝ} (hT : T < 1)
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) (ω : Ω d) {n : ℕ}
    (hn : 1 ≤ n) (q : LoopData ((band d).L N) n) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hKb : ∀ w ∈ Set.Icc (0 : ℝ) T, ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk) :
    ‖SumZeroDyn.lkT (sample d) E N u ω q.1 q.2 - SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖
      ≤ ((n : ℝ) * ((etaT E T)⁻¹ * (etaT E T)⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E T)⁻¹ ^ (n - 1))
          + ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
        * Real.sqrt |u - v| := by
  have hlen : (LoopData.idx (q.1, q.2)).length = n := LoopData.idx_length _
  have hwf : (LoopData.idx (q.1, q.2)).WF := LoopData.idx_wf _
  have hlenwin : |u - v| ≤ 1 := by
    rw [abs_le]; constructor <;> [linarith [hu.1, hv.2]; linarith [hv.1, hu.2]]
  have hsq : |u - v| ≤ Real.sqrt |u - v| := self_le_sqrt (abs_nonneg _) hlenwin
  have hsplit : SumZeroDyn.lkT (sample d) E N u ω q.1 q.2
        - SumZeroDyn.lkT (sample d) E N v ω q.1 q.2
      = ((sample d).Lval E N u ω (LoopData.idx (q.1, q.2))
          - (sample d).Lval E N v ω (LoopData.idx (q.1, q.2)))
        - ((band d).Kval E N u (LoopData.idx (q.1, q.2))
          - (band d).Kval E N v (LoopData.idx (q.1, q.2))) := by
    show ((sample d).Lval E N u ω _ - (band d).Kval E N u _)
      - ((sample d).Lval E N v ω _ - (band d).Kval E N v _) = _
    ring
  -- the `L`-half
  have hLval : ‖(sample d).Lval E N u ω (LoopData.idx (q.1, q.2))
        - (sample d).Lval E N v ω (LoopData.idx (q.1, q.2))‖
      ≤ ((n : ℝ) * ((etaT E T)⁻¹ * (etaT E T)⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E T)⁻¹ ^ (n - 1)))
        * Real.sqrt |u - v| := by
    refine (norm_Lval_sub_le_sqrt d N hE le_rfl hT ω hu hv hn q).trans (le_of_eq ?_)
    ring
  -- the `K`-half
  have hKval : ‖(band d).Kval E N u (LoopData.idx (q.1, q.2))
        - (band d).Kval E N v (LoopData.idx (q.1, q.2))‖
      ≤ (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
        * Real.sqrt |u - v| := by
    have h := norm_Kgen_sub_le' (L := (band d).L N) ((band d).three_le_L N) ((band d).W N)
      (norm_mSigma_le_one hE) hT (LoopData.idx (q.1, q.2)) hwf hBk0
      (fun w hw J hJ h2 hle => hKb w hw J hJ h2 (by rwa [hlen] at hle)) hu hv
    rw [hlen] at h
    refine h.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  calc ‖(sample d).Lval E N u ω (LoopData.idx (q.1, q.2))
          - (sample d).Lval E N v ω (LoopData.idx (q.1, q.2))‖
        + ‖(band d).Kval E N u (LoopData.idx (q.1, q.2))
          - (band d).Kval E N v (LoopData.idx (q.1, q.2))‖
      ≤ ((n : ℝ) * ((etaT E T)⁻¹ * (etaT E T)⁻¹ * (‖Xmat d N ω‖ + 1) * (etaT E T)⁻¹ ^ (n - 1)))
            * Real.sqrt |u - v|
          + (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
            * Real.sqrt |u - v| := add_le_add hLval hKval
    _ = _ := by ring

/-- **The envelope of `(L - K)_{u,σ,a}`**: `‖L‖ ≤ η_T^{-n}` from
`RBM.norm_gloop_le_of_le_abs_im` (each resolvent has norm `≤ η_u^{-1} ≤ η_T^{-1}`, and the
`E_a`'s contribute `W^{-(n-1)} ≤ 1`), and `‖K‖ ≤ B` by hypothesis. -/
theorem norm_lkT_flow_le (N : ℕ) {E : ℝ} (hE : |E| < 2) {T : ℝ} (hT : T < 1)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (ω : Ω d) {n : ℕ} (hn : 1 ≤ n)
    (q : LoopData ((band d).L N) n) {Bk : ℝ} (hBk1 : 1 ≤ Bk)
    (hKb : ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(band d).Kval E N u J‖ ≤ Bk) :
    ‖SumZeroDyn.lkT (sample d) E N u ω q.1 q.2‖ ≤ (etaT E T)⁻¹ ^ n + Bk := by
  have hlen : (LoopData.idx (q.1, q.2)).length = n := LoopData.idx_length _
  have hwf : (LoopData.idx (q.1, q.2)).WF := LoopData.idx_wf _
  have hηT : 0 < etaT E T := etaT_pos_of_lt_one' hE hT
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 hT
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hzim : etaT E T ≤ |(zt E u).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hηu]
    exact etaT_le_of_le hE hu.2
  have halen : (LoopData.idx (q.1, q.2)).a.length = n := hlen
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne ((band d).W N))
  have hgl : ‖(sample d).Lval E N u ω (LoopData.idx (q.1, q.2))‖ ≤ (etaT E T)⁻¹ ^ n := by
    have h := norm_gloop_le_of_le_abs_im (L := (band d).L N) (W := (band d).W N)
      (Hflow_isHermitian d N u ω) hηT hzim (LoopData.idx (q.1, q.2)) hwf
      (by rw [halen]; omega)
    rw [halen] at h
    refine h.trans ?_
    have hinv : ((band d).W N : ℝ)⁻¹ ^ (n - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) (by rw [inv_le_one_iff₀]; right; exact hW1)
    calc (etaT E T)⁻¹ ^ n * ((band d).W N : ℝ)⁻¹ ^ (n - 1)
        ≤ (etaT E T)⁻¹ ^ n * 1 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (etaT E T)⁻¹ ^ n := mul_one _
  have hKv : ‖(band d).Kval E N u (LoopData.idx (q.1, q.2))‖ ≤ Bk :=
    norm_Kval_le_of_envelope d N hE u hn hBk1 _ hwf hlen hKb
  show ‖(sample d).Lval E N u ω (LoopData.idx (q.1, q.2))
    - (band d).Kval E N u (LoopData.idx (q.1, q.2))‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hgl hKv)

/-- **The modulus of `(W ℓ_u η_u)^m ‖(L-K)_{u,σ,a}‖` in the time** — the quantity the time net
of `RBM.Gauss.stochDom_timeIcc_of_unifDom_const` has to be Hölder in.

`RBM.Gauss.abs_mul_sub_mul_le` glues the scale's modulus
(`RBM.Gauss.abs_scale_pow_sub_le`) to the loop difference's
(`RBM.Gauss.norm_lkT_flow_sub_le`), using `RBM.Gauss.scale_le_mul` and
`RBM.Gauss.norm_lkT_flow_le` as the two envelopes.  Every constant is explicit, and the
exponent is `γ = 1/2`. -/
theorem abs_scaleLK_sub_le (N : ℕ) {E : ℝ} (hE : |E| < 2) {T : ℝ} (hT : T < 1)
    {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (hv : v ∈ Set.Icc (0 : ℝ) T) (ω : Ω d) {n : ℕ}
    (hn : 1 ≤ n) (q : LoopData ((band d).L N) n) {Bk : ℝ} (hBk1 : 1 ≤ Bk)
    (hKb : ∀ w ∈ Set.Icc (0 : ℝ) T, ∀ J : LoopIdx (ZMod ((band d).L N)), J.WF →
      2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk) :
    |(band d).scale E N u ^ n * ‖SumZeroDyn.lkT (sample d) E N u ω q.1 q.2‖
        - (band d).scale E N v ^ n * ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖|
      ≤ (((n : ℝ) * (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ (n - 1)
              * (((band d).W N : ℝ) * ((1 - T)⁻¹ + ((band d).L N : ℝ))))
            * ((etaT E T)⁻¹ ^ n + Bk)
          + (((band d).W N : ℝ) * ((band d).L N : ℝ)) ^ n
            * ((n : ℝ) * ((etaT E T)⁻¹ * (etaT E T)⁻¹ * (‖Xmat d N ω‖ + 1)
                  * (etaT E T)⁻¹ ^ (n - 1))
                + ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2))
        * Real.sqrt |u - v| := by
  have hsv : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv.1 (lt_of_le_of_lt hv.2 hT)
  refine abs_mul_sub_mul_le (norm_nonneg _) (pow_nonneg hsv.le n) (Real.sqrt_nonneg _)
    (by positivity)
    (norm_lkT_flow_le d N hE hT hu ω hn q hBk1 (fun J hJ h2 hle => hKb u hu J hJ h2 hle))
    (pow_le_pow_left₀ hsv.le (scale_le_mul hE N hv.1 (lt_of_le_of_lt hv.2 hT)) n)
    (abs_scale_pow_sub_le hE N n hT hu hv)
    ((abs_norm_sub_norm_le _ _).trans
      (norm_lkT_flow_sub_le d N hE hT hu hv ω hn q (by linarith) hKb))

/-! ### The constant is polynomial -/

/-- **The explicit constant of `RBM.Gauss.abs_scaleLK_sub_le` is at most `(n² + 5n) R^{3n+4}`**
whenever a single `R ≥ 1` dominates `W`, `L`, `(1-T)^{-1}`, `η_T^{-1}`, the envelope `B` of the
`K`'s and `‖X‖ + 1`.

Pure arithmetic; it is what turns the estimate into the `N^K |u-v|^γ` shape the time net asks
for, with `K = c(3n+4) + 1` when every ingredient is `≤ N^c`. -/
theorem scaleLK_const_le {R W L Tinv eta Bk X : ℝ} {n : ℕ} (hn : 1 ≤ n) (hR1 : 1 ≤ R)
    (hW0 : 0 ≤ W) (hW : W ≤ R) (hL0 : 0 ≤ L) (hL : L ≤ R)
    (hTinv0 : 0 ≤ Tinv) (hTinv : Tinv ≤ R) (heta0 : 0 ≤ eta) (heta : eta ≤ R)
    (hBk0 : 0 ≤ Bk) (hBk : Bk ≤ R) (hX0 : 0 ≤ X) (hX : X ≤ R) :
    ((n : ℝ) * (W * L) ^ (n - 1) * (W * (Tinv + L))) * (eta ^ n + Bk)
        + (W * L) ^ n * ((n : ℝ) * (eta * eta * X * eta ^ (n - 1))
            + W * (n : ℝ) ^ 2 * L * Bk ^ 2)
      ≤ ((n : ℝ) ^ 2 + 5 * (n : ℝ)) * R ^ (3 * n + 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR1
  have hmono : ∀ i j : ℕ, i ≤ j → R ^ i ≤ R ^ j := fun i j h => pow_le_pow_right₀ hR1 h
  have hRpow : ∀ i : ℕ, (0 : ℝ) ≤ R ^ i := fun i => pow_nonneg hR0 i
  have hWL0 : (0 : ℝ) ≤ W * L := mul_nonneg hW0 hL0
  have hWL : W * L ≤ R ^ 2 := by nlinarith
  have hWLk : ∀ i : ℕ, (W * L) ^ i ≤ R ^ (2 * i) := by
    intro i
    calc (W * L) ^ i ≤ (R ^ 2) ^ i := pow_le_pow_left₀ hWL0 hWL i
      _ = R ^ (2 * i) := by rw [← pow_mul]
  have hk : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [Nat.add_sub_cancel]
  -- the four factors
  have hA : ((k + 1 : ℕ) : ℝ) * (W * L) ^ k * (W * (Tinv + L))
      ≤ (2 * ((k + 1 : ℕ) : ℝ)) * R ^ (2 * k + 2) := by
    have h1 : W * (Tinv + L) ≤ 2 * R ^ 2 := by nlinarith
    have h1' : (0 : ℝ) ≤ W * (Tinv + L) := mul_nonneg hW0 (by linarith)
    have hc0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((k + 1 : ℕ) : ℝ) * (W * L) ^ k * (W * (Tinv + L))
        ≤ ((k + 1 : ℕ) : ℝ) * R ^ (2 * k) * (2 * R ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hWLk k) hc0) h1 h1'
            (mul_nonneg hc0 (hRpow _))
      _ = (2 * ((k + 1 : ℕ) : ℝ)) * R ^ (2 * k + 2) := by rw [pow_add]; ring
  have hB : eta ^ (k + 1) + Bk ≤ 2 * R ^ (k + 1) := by
    have h1 : eta ^ (k + 1) ≤ R ^ (k + 1) := pow_le_pow_left₀ heta0 heta _
    have h2 : Bk ≤ R ^ (k + 1) := le_trans hBk (by simpa using hmono 1 (k + 1) (by omega))
    linarith
  have hC : (W * L) ^ (k + 1) ≤ R ^ (2 * k + 2) := by
    have := hWLk (k + 1)
    rwa [show 2 * (k + 1) = 2 * k + 2 from by ring] at this
  have hD : ((k + 1 : ℕ) : ℝ) * (eta * eta * X * eta ^ k) + W * ((k + 1 : ℕ) : ℝ) ^ 2 * L * Bk ^ 2
      ≤ ((k + 1 : ℕ) : ℝ) * R ^ (k + 3) + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ 4 := by
    have hc0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hek : eta ^ k ≤ R ^ k := pow_le_pow_left₀ heta0 heta k
    have hek0 : (0 : ℝ) ≤ eta ^ k := pow_nonneg heta0 k
    have h1 : eta * eta * X * eta ^ k ≤ R ^ (k + 3) := by
      have ha : eta * eta ≤ R * R := mul_le_mul heta heta heta0 hR0
      have hb : eta * eta * X ≤ R * R * R := mul_le_mul ha hX hX0 (mul_nonneg hR0 hR0)
      have hstep : eta * eta * X * eta ^ k ≤ R * R * R * R ^ k :=
        mul_le_mul hb hek hek0 (mul_nonneg (mul_nonneg hR0 hR0) hR0)
      calc eta * eta * X * eta ^ k ≤ R * R * R * R ^ k := hstep
        _ = R ^ (k + 3) := by rw [pow_add]; ring
    have h2 : W * ((k + 1 : ℕ) : ℝ) ^ 2 * L * Bk ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ 4 := by
      have hBk2 : Bk ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hBk0 hBk 2
      have hprod : W * L * Bk ^ 2 ≤ R ^ 2 * R ^ 2 :=
        mul_le_mul hWL hBk2 (sq_nonneg _) (hRpow 2)
      rw [show W * ((k + 1 : ℕ) : ℝ) ^ 2 * L * Bk ^ 2
            = ((k + 1 : ℕ) : ℝ) ^ 2 * (W * L * Bk ^ 2) from by ring,
        show R ^ 4 = R ^ 2 * R ^ 2 from by ring]
      exact mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    have := mul_le_mul_of_nonneg_left h1 hc0
    linarith
  -- put them together
  have hAB : (((k + 1 : ℕ) : ℝ) * (W * L) ^ k * (W * (Tinv + L))) * (eta ^ (k + 1) + Bk)
      ≤ (2 * ((k + 1 : ℕ) : ℝ)) * R ^ (2 * k + 2) * (2 * R ^ (k + 1)) := by
    refine mul_le_mul hA hB (add_nonneg (pow_nonneg heta0 _) hBk0) ?_
    exact mul_nonneg (by positivity) (hRpow _)
  have hCD : (W * L) ^ (k + 1) * (((k + 1 : ℕ) : ℝ) * (eta * eta * X * eta ^ k)
        + W * ((k + 1 : ℕ) : ℝ) ^ 2 * L * Bk ^ 2)
      ≤ R ^ (2 * k + 2) * (((k + 1 : ℕ) : ℝ) * R ^ (k + 3) + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ 4) := by
    refine mul_le_mul hC hD ?_ (hRpow _)
    have h01 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (eta * eta * X * eta ^ k) := by
      have : (0 : ℝ) ≤ eta * eta * X * eta ^ k :=
        mul_nonneg (mul_nonneg (mul_nonneg heta0 heta0) hX0) (pow_nonneg heta0 k)
      exact mul_nonneg (Nat.cast_nonneg _) this
    have h02 : (0 : ℝ) ≤ W * ((k + 1 : ℕ) : ℝ) ^ 2 * L * Bk ^ 2 := by
      have : (0 : ℝ) ≤ W * ((k + 1 : ℕ) : ℝ) ^ 2 := mul_nonneg hW0 (sq_nonneg _)
      exact mul_nonneg (mul_nonneg this hL0) (sq_nonneg _)
    linarith
  -- and read the powers off
  have e1 : (2 * ((k + 1 : ℕ) : ℝ)) * R ^ (2 * k + 2) * (2 * R ^ (k + 1))
      = 4 * ((k + 1 : ℕ) : ℝ) * R ^ (3 * k + 3) := by
    rw [show (3 * k + 3) = (2 * k + 2) + (k + 1) from by ring, pow_add]; ring
  have e2 : R ^ (2 * k + 2) * (((k + 1 : ℕ) : ℝ) * R ^ (k + 3) + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ 4)
      = ((k + 1 : ℕ) : ℝ) * R ^ (3 * k + 5) + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ (2 * k + 6) := by
    rw [show (3 * k + 5) = (2 * k + 2) + (k + 3) from by ring,
      show (2 * k + 6) = (2 * k + 2) + 4 from by ring, pow_add, pow_add]; ring
  have hc0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have f1 : R ^ (3 * k + 3) ≤ R ^ (3 * (k + 1) + 4) := hmono _ _ (by omega)
  have f2 : R ^ (3 * k + 5) ≤ R ^ (3 * (k + 1) + 4) := hmono _ _ (by omega)
  have f3 : R ^ (2 * k + 6) ≤ R ^ (3 * (k + 1) + 4) := hmono _ _ (by omega)
  have hfin : 4 * ((k + 1 : ℕ) : ℝ) * R ^ (3 * k + 3)
        + (((k + 1 : ℕ) : ℝ) * R ^ (3 * k + 5) + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ (2 * k + 6))
      ≤ (((k + 1 : ℕ) : ℝ) ^ 2 + 5 * ((k + 1 : ℕ) : ℝ)) * R ^ (3 * (k + 1) + 4) := by
    nlinarith [mul_le_mul_of_nonneg_left f1 (by positivity : (0:ℝ) ≤ 4 * ((k + 1 : ℕ) : ℝ)),
      mul_le_mul_of_nonneg_left f2 hc0,
      mul_le_mul_of_nonneg_left f3 (sq_nonneg ((k + 1 : ℕ) : ℝ))]
  calc ((k + 1 : ℕ) : ℝ) * (W * L) ^ k * (W * (Tinv + L)) * (eta ^ (k + 1) + Bk)
        + (W * L) ^ (k + 1) * (((k + 1 : ℕ) : ℝ) * (eta * eta * X * eta ^ k)
            + W * ((k + 1 : ℕ) : ℝ) ^ 2 * L * Bk ^ 2)
      ≤ (2 * ((k + 1 : ℕ) : ℝ)) * R ^ (2 * k + 2) * (2 * R ^ (k + 1))
          + R ^ (2 * k + 2) * (((k + 1 : ℕ) : ℝ) * R ^ (k + 3)
              + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ 4) := add_le_add hAB hCD
    _ = 4 * ((k + 1 : ℕ) : ℝ) * R ^ (3 * k + 3)
          + (((k + 1 : ℕ) : ℝ) * R ^ (3 * k + 5)
              + ((k + 1 : ℕ) : ℝ) ^ 2 * R ^ (2 * k + 6)) := by rw [e1, e2]
    _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2 + 5 * ((k + 1 : ℕ) : ℝ)) * R ^ (3 * (k + 1) + 4) := hfin

open Filter

/-! ### The envelope of `K` on **every** ring length — (2.59) assembled

The modulus of `(L - K)_{u,σ,a}` takes the envelope `‖K_{w,σ,a}‖ ≤ B` on the loops of length
`2 … m` as a hypothesis.  It is (2.59)–(2.60), proved for every length: this section gives one
constant for all lengths `2 … m`.

The chain is

`‖K_{w,σ,a}‖ ≤ C_n (W ℓ_w η_w)^{-n+1}`   (2.59) for `n ≥ 3`, (2.60) for `n = 1`, Example 2.15
                                          for `n = 2` — all three are `RBM.Band.norm_Kval_le`
`(W ℓ_w η_w)^{-1} ≤ η_w^{-1}`             because `W ≥ 1` and `ℓ̂_w ≥ 1` (`RBM.one_le_ellHat`)
`η_w^{-1} ≤ η_{t_N}^{-1} ≤ N^c`           because `η_u = (1-u) Im m` is antitone, and
                                          `η_{t_N}^{-1} ≤ N^c`.

**The normalization**: the exponent that comes out is `c·m + 1`, not `c` — one factor of
`N^c` per edge of the loop (`c(m-1)`, rounded up), plus one to swallow `C_n`.  That is harmless,
because a polynomial bound `≤ N^c` only gets *easier* as `c` grows
(`RBM.Gauss.eventually_le_rpow_mono`).  Nothing is assumed about the window beyond `t_N < 1`:
in particular **no short-window condition** `t_N - s_N ≤ κ(1-t_N)` (which fails on the grid, see
the last section), and `s` does not occur at all. -/

section Kenvelope

variable {Ωb : Type*} [MeasurableSpace Ωb]

/-- A spectral gap `k` out of `|E| < 2`: `RBM.Band.norm_Kval_le` is stated with the bulk
parameter `k` of (2.4), and every consumer here carries only `|E| < 2`. -/
theorem exists_gap_of_abs_lt_two {E : ℝ} (hE : |E| < 2) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ |E| ≤ 2 - k := by
  refine ⟨min 1 (2 - |E|), lt_min one_pos (by linarith), min_le_left _ _, ?_⟩
  have := min_le_right (1 : ℝ) (2 - |E|)
  linarith

/-- **(2.59)/(2.60) with a single constant for all loop lengths `2 … m`.**

`RBM.Band.norm_Kval_le` gives one constant `C_n` per length `n`; the envelope hypothesis of
`RBM.Gauss.norm_lkT_flow_sub_le` ranges over a *set* of lengths, so the constants have to be
maximized.  Induction on `m`, taking `max` at each step; the exponent of the scale stays the sharp
`J.length - 1`. -/
theorem exists_norm_Kval_le_upto (B : Band Ωb) {E : ℝ} (hE : |E| < 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (w : ℝ), 0 ≤ w → w < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ m →
        ‖B.Kval E N w J‖ ≤ C * (B.scale E N w)⁻¹ ^ (J.length - 1) := by
  obtain ⟨k, hk0, hk1, hEk⟩ := exists_gap_of_abs_lt_two hE
  induction m with
  | zero => exact ⟨0, le_rfl, fun _ _ _ _ _ _ h2 hle => absurd hle (by omega)⟩
  | succ m ih =>
      obtain ⟨C, hC0, hC⟩ := ih
      obtain ⟨C', hC'0, hC'⟩ := B.norm_Kval_le hk0 hk1 hEk (n := m + 1) (by omega)
      refine ⟨max C C', le_max_of_le_left hC0, fun N w hw0 hw1 J hJ h2 hle => ?_⟩
      have hs0 : (0 : ℝ) ≤ (B.scale E N w)⁻¹ :=
        inv_nonneg.2 (B.scale_pos' hE N hw0 hw1).le
      rcases le_or_gt J.length m with h | h
      · exact (hC N w hw0 hw1 J hJ h2 h).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hs0 _))
      · have hlen : J.length = m + 1 := by omega
        have h' := hC' N w hw0 hw1 J hJ hlen
        rw [hlen]
        exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hs0 _))

/-- A polynomial envelope only gets weaker as its exponent grows: a bound `f N ≤ N^c` that holds
eventually also holds with any larger exponent `c'`. -/
theorem eventually_le_rpow_mono {f : ℕ → ℝ} {c c' : ℝ} (hcc : c ≤ c')
    (h : ∀ᶠ N : ℕ in atTop, f N ≤ (N : ℝ) ^ c) :
    ∀ᶠ N : ℕ in atTop, f N ≤ (N : ℝ) ^ c' := by
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  exact hN.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hcc)

end Kenvelope

/-! ### A nonempty event for `‖X‖`

A bound on `‖X_N‖` that is asked on an event `Ξ` is vacuous when `Ξ = ∅`.  The event below
really exists, really has high probability, and comes from `‖X‖ ≺ 1` with nothing added. -/

/-- **A high-probability event for `‖X_N‖ + 1 ≤ N^c`.**  `‖X‖ ≺ 1`
(`RBM.Gauss.stochDom_norm_Xmat`) produces an event of high probability on which
`‖X_N‖ + 1 ≤ N^c`, for every `c ≥ 2`.  The event is **nonempty** — `HighProb` on a probability
space forces `P(Ξ_N) > 0` eventually. -/
theorem exists_highProb_normX (d : Dims) (h : TraceMomentBound d) {c : ℝ} (hc : 2 ≤ c) :
    ∃ Ξ : ℕ → Set (Ω d), HighProb (band d).P Ξ ∧
      ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ c := by
  refine ⟨fun N => {ω | ∀ _u : Unit, ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (1 : ℝ) * 1},
    (stochDom_norm_Xmat h).highProb one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with N hN ω hω
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h1 : ‖Xmat d N ω‖ ≤ (N : ℝ) := by
    have := hω ()
    rwa [Real.rpow_one, mul_one] at this
  have h2 : (N : ℝ) + 1 ≤ (N : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    nlinarith
  have h3 : (N : ℝ) ^ (2 : ℝ) ≤ (N : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hc
  linarith

/-! ### The edge-kernel ratio on the grid

The edge parameters `ξ_i = m(σ_i)m(σ_{i+1})` of Definition 5.2 have norm **exactly** `1` in the
bulk (`RBM.norm_xiOf_mSigma`).  So a bound `1 + (w-u)(1-w)^{-1} ≤ C_k` with `w < 1` has a
constant `C_k` **iff** the window is short compared with the distance to the edge of the flow,
`t_N - s_N ≤ κ (1 - t_N)`, and then `C_k = 1 + κ`.

The short window fails on the six-step grid of the proof of Lemmas 2.18–2.20,
`1 - s_j = W^{-jτ'}`: the ratio is an *equality* `(t-s)/(1-t) = W^{τ'} - 1`, which grows with
`N`, so no `N`-independent `C_k` exists.  The left-hand side is exactly that of Lemma 7.1, while
(5.92) says Lemma 5.14 holds with **no** prefactor depending on `η_s/η_t`; the route that does
hold is the (7.16) one. -/

/-! ### `hnum`: (5.92)'s numerical closing -/

section Hnum

variable {Ω : Type*} [MeasurableSpace Ω]

end Hnum

end RBM.Gauss
