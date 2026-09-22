/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Eq548Producer
import RBM1D.Gauss.FlowHolder

/-!
# The first cell `u_0 = 0 → u_1` of the grid of p. 24 — T256

T249 compiled a refutation of the `modulus` field of `RBM.MomentDuhamelCut.CutHypEv` (and of
`RBM.EntryModulusEv`) on a window that starts at `0`, and T251 concluded from it that the first
cell of the grid of p. 24 is outside the reach of the (5.48) chain, weakening the merged
assembly's conclusion from `RBM.Thm221NoEL` to `RBM.Thm221NoELFrom`.

D17 rules that the first cell is **not** a mathematical gap: T249's witness is the sample point
`ω = v^{-1/2}`, whose matrix norm blows up as `v → 0`, so it leaves every event of the form
`{‖X‖ ≤ N}`; on such an event the second resolvent identity gives a Hölder-`1/2` modulus in
the time variable that is valid **including at `u = 0`**.

This file records, all compiled:

1. §1 — the Hölder-`1/2` resolvent modulus of the paper's own flow on `{‖X‖ ≤ N}`, on the
   window `[0, t]` with `t < 1`, **with `0` in the window**
   (`RBM.Gauss.norm_green_flow_sub_le_event`).  It is a corollary of T106's
   `RBM.Gauss.norm_green_flow_sub_le`, which never needed `0 < u`: the `‖X‖`-free route of
   T249乙 (`RBM.norm_green_sqrt_sub_le_lip`) is the only one that does.
2. §2 — the compiled reason why T249's published refutation stops at the event boundary
   (`RBM.t249_witness_norm_gt`): with the exponents `Kmod = 1`, `γ = 1/2` that
   `RBM.EntryModulusEv` hard-codes, the time `v` that `RBM.not_modulusEv_zero_start` selects
   forces `‖X(ω)‖ = v^{-1/2} > N`.  This is acceptance item 4 of D17.
3. §3 — ⚠ **the caveat**, also compiled.  The event alone is not enough for the *literal*
   `RBM.EntryModulusEv` / `RBM.EntryModulusEvOn`, because those hard-code `Kmod = 1`:
   at the time `v = N^{-2}` — the smallest time at which the witness `ω = v^{-1/2}` is still
   inside `{‖X‖ ≤ N}` — a modulus with `Kmod = 1`, `γ = 1/2` allows a jump of at most `1`
   (`RBM.jump_le_one_of_kmod_one`), while `RBM.gap_lower_W` of §3 says T249's jump is at least
   `W/(200((η_{t₀})^{-2}+1))`, which diverges.  So D17's repair needs `Kmod` to grow with `D`
   (`RBM.kmod_ge_of_jump`); `Kmod = 1` is refuted.  See the "Deviations" section.

## Main statements

* `RBM.Gauss.norm_green_flow_sub_le_event`  — §1, the `u = 0`-inclusive Hölder-`1/2` modulus
* `RBM.t249_witness_norm_gt`                — §2, T249's witness leaves `{‖X‖ ≤ N}`
* `RBM.gap_lower_W`                         — §3, T249's jump is `≳ W`, not `≳ 1`
* `RBM.jump_le_one_of_kmod_one`             — §3, what `Kmod = 1` allows at `v = N^{-2}`
* `RBM.kmod_ge_of_jump`                     — §3, the exponent `Kmod` a jump `g` forces
-/

namespace RBM

open MeasureTheory Matrix Filter

open scoped Matrix.Norms.L2Operator

/-! ### 1. The Hölder-`1/2` resolvent modulus on `{‖X‖ ≤ N}`, with `0` in the window

T106 (`RBM.Gauss.norm_green_flow_sub_le`) already proves

`‖G_u - G_{u'}‖ ≤ η_u^{-1}(|√u - √u'| ‖X‖ + |u - u'|) η_{u'}^{-1}`

with **no positivity hypothesis on `u` or `u'`** — the resolvent identity does not divide by
`√u`.  Dividing by `√v` is what forces `0 < s` in T249乙's `‖X‖`-free variant
`RBM.norm_green_sqrt_sub_le_lip`; the price of keeping `0` in the window is the factor `‖X‖`,
which on the event `{‖X‖ ≤ N}` of `RBM.Gauss.exists_highProb_normX` is at most `N`.
-/

namespace Gauss

/-- **The flow's resolvent is Hölder-`1/2` in time on `{‖X‖ ≤ N}`, uniformly on `[0, t]`.**

`u = 0` and `u' = 0` are allowed: the estimate never divides by `√u`.  On the event
`‖X‖ ≤ N` the constant is `(N + 1)(η_t)^{-2}`, a polynomial in `N`, which is exactly the shape
`RBM.MomentDuhamelCut.CutHypEv.Kmod` asks for (with `γ = 1/2`).

This is the deterministic core of D17's ruling on the first cell of the grid of p. 24. -/
theorem norm_green_flow_sub_le_event (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht1 : t < 1) {u u' : ℝ} (hu0 : 0 ≤ u) (hu'0 : 0 ≤ u') (hut : u ≤ t) (hu't : u' ≤ t)
    (hlen : |u - u'| ≤ 1) {ω : Ω d} (hX : ‖Xmat d N ω‖ ≤ (N : ℝ)) :
    ‖green (Hflow d N u ω) (zt E u) - green (Hflow d N u' ω) (zt E u')‖
      ≤ ((N : ℝ) + 1) * ((etaT E t)⁻¹ * (etaT E t)⁻¹) * |u - u'| ^ ((1 : ℝ) / 2) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht1
  have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht1
  have hηt : 0 < etaT E t := etaT_pos_of_lt_one' hE ht1
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hηu' : 0 < etaT E u' := etaT_pos_of_lt_one' hE hu'1
  have hiu : (etaT E u)⁻¹ ≤ (etaT E t)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hηt (etaT_le_of_le hE hut)
  have hiu' : (etaT E u')⁻¹ ≤ (etaT E t)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hηt (etaT_le_of_le hE hu't)
  have hX0 : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hp0 : (0 : ℝ) ≤ |u - u'| ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
  have h1 : |Real.sqrt u - Real.sqrt u'| ≤ |u - u'| ^ ((1 : ℝ) / 2) := by
    have h := RBM.abs_sqrt_sub_sqrt_le hu0 hu'0
    rwa [show Real.sqrt |u - u'| = |u - u'| ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow _] at h
  have h2 : |u - u'| ≤ |u - u'| ^ ((1 : ℝ) / 2) := self_le_rpow_half (abs_nonneg _) hlen
  have hmid : |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|
      ≤ ((N : ℝ) + 1) * |u - u'| ^ ((1 : ℝ) / 2) := by
    have hmul : |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖
        ≤ |u - u'| ^ ((1 : ℝ) / 2) * (N : ℝ) :=
      mul_le_mul h1 hX (norm_nonneg _) hp0
    nlinarith [hmul, h2, hp0, hN0]
  have hm0 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'| := by
    have : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ := by positivity
    linarith [abs_nonneg (u - u')]
  refine (norm_green_flow_sub_le d N hE hu1 hu'1 ω).trans ?_
  calc (etaT E u)⁻¹ * (|Real.sqrt u - Real.sqrt u'| * ‖Xmat d N ω‖ + |u - u'|) * (etaT E u')⁻¹
      ≤ (etaT E t)⁻¹ * (((N : ℝ) + 1) * |u - u'| ^ ((1 : ℝ) / 2)) * (etaT E t)⁻¹ := by gcongr
    _ = ((N : ℝ) + 1) * ((etaT E t)⁻¹ * (etaT E t)⁻¹) * |u - u'| ^ ((1 : ℝ) / 2) := by ring

end Gauss

/-! ### 2. Why T249's published refutation stops at the event boundary (D17, item 4)

`RBM.not_modulusEv_zero_start` refutes a modulus with exponents `(Kmod, γ)` by evaluating it at
the time `v = min(t_N, (c/(N^{Kmod}+1))^{1/γ})`, where `c` is the *constant* gap
`RBM.gap_lower` supplies.  The sample point it needs there is `ω = v^{-1/2}`
(`RBM.exists_jSfarSm_ge_swapSample`), whose matrix norm is `v^{-1/2}`.

With the exponents that `RBM.EntryModulusEv` hard-codes — `Kmod = 1`, `γ = 1/2` — that time is
at most `(c/(N+1))^2`, so the witness has `‖X‖ ≥ (N+1)/c > N` as soon as `c ≤ 1`.  It is
therefore **outside** `{‖X‖ ≤ N}`, and T249's refutation says nothing about the
event-restricted `RBM.EntryModulusEvOn`.  (`RBM.gap_lower`'s `c` is
`1/(200((η_{t₀})^{-2}+1)) < 1`.) -/

section Witness

/-- **T249's witness leaves the event `{‖X‖ ≤ N}`.**  At any time `v` no larger than the
threshold `(c/(N+1))^2` that `RBM.not_modulusEv_zero_start` uses for `Kmod = 1`, `γ = 1/2`, the
sample point `ω = v^{-1/2}` of `RBM.exists_jSfarSm_ge_swapSample` has matrix norm `> N`. -/
theorem t249_witness_norm_gt {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (N : ℕ) {v : ℝ}
    (hv0 : 0 < v) (hv : v ≤ (c / ((N : ℝ) + 1)) ^ 2) : (N : ℝ) < 1 / Real.sqrt v := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hr0 : 0 < c / ((N : ℝ) + 1) := by positivity
  have hsv : Real.sqrt v ≤ c / ((N : ℝ) + 1) := by
    have := Real.sqrt_le_sqrt hv
    rwa [Real.sqrt_sq hr0.le] at this
  have hsv0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hstep : ((N : ℝ) + 1) / c ≤ 1 / Real.sqrt v := by
    rw [div_le_div_iff₀ hc0 hsv0]
    calc ((N : ℝ) + 1) * Real.sqrt v ≤ ((N : ℝ) + 1) * (c / ((N : ℝ) + 1)) := by
          exact mul_le_mul_of_nonneg_left hsv (by linarith)
      _ = c := by field_simp
      _ = 1 * c := (one_mul c).symm
  have hgt : (N : ℝ) < ((N : ℝ) + 1) / c := by
    rw [lt_div_iff₀ hc0]
    nlinarith
  linarith

end Witness

/-! ### 3. ⚠ The caveat: `Kmod = 1` is refuted even on the event

D17's arithmetic is right *provided* the modulus exponent `Kmod` is allowed to grow with `D`.
The repo's `RBM.EntryModulusEv` and `RBM.EntryModulusEvOn` do **not** allow it: both hard-code
the right-hand side `N^1 |v - w|^{1/2}`.  Against that fixed exponent the event does **not**
save the day, and the three lemmas of this section say so quantitatively.

* `RBM.gap_lower_W` — the jump T249 exhibits is not a constant: it is at least
  `W/(200((η_{t₀})^{-2} + 1))`.  This is `RBM.gap_lower` with the factor `W` kept instead of
  discarded (`gap_lower` only needed a positive constant).
* `RBM.jump_le_one_of_kmod_one` — at the time `v = N^{-2}`, which is the *smallest* time at
  which `ω = v^{-1/2}` is still inside `{‖X‖ ≤ N}`, a modulus with `Kmod = 1`, `γ = 1/2` allows
  a jump of at most `1`.
* `RBM.kmod_ge_of_jump` — the exponent a jump of size `g` forces at that time is
  `N^{Kmod - 1} ≥ g`, i.e. `Kmod ≥ 1 + log_N g`.  With `g ≍ W ≥ N^{1/2}` this already rules out
  `Kmod = 1`; with the `W^{-D}` term of `RBM.tailT` used in place of the crude bound of
  `RBM.gap_lower_W` it forces `Kmod` to grow linearly in `D`.
-/

section Caveat

variable {E D : ℝ}

/-- **T249's far-field jump is of order `W`, not of order `1`.**

Verbatim `RBM.gap_lower` except that the factor `(W)` coming from
`num ≥ 1/(100 W)` and `T_{v,D} ≤ W^{-2}((η_{t₀})^{-2}+1)` is kept rather than thrown away by
`W ≥ 1`.  Fed into `RBM.exists_jSfarSm_ge_swapSample` it gives
`J*^{sm}_{v,D} ≥ 1 + W/(200((η_{t₀})^{-2}+1))` at **every** `v ∈ (0, t₀]`. -/
theorem gap_lower_W (hE : |E| < 2) {W L : ℕ} (hW : 1 ≤ W) (hL : 3 ≤ L) {v : ℝ}
    (hv0 : 0 < v) {t₀ : ℝ} (hvt : v ≤ t₀) (ht₀ : t₀ < 1) (hD : 2 ≤ D) (dd : ℝ) :
    (W : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
        / (2 * tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D dd) := by
  have : NeZero L := ⟨by omega⟩
  have hv1 : v < 1 := lt_of_le_of_lt hvt ht₀
  have hWR : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < (W : ℝ) := by linarith
  have hηv : 0 < etaT E v := by
    show 0 < (1 - v) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hηt : 0 < etaT E t₀ := by
    show 0 < (1 - t₀) * (mE E).im; exact mul_pos (by linarith) (mE_im_pos hE)
  have hηle : etaT E t₀ ≤ etaT E v := Gauss.etaT_le_of_le hE hvt
  have hℓ : (1 : ℝ) ≤ ellHat L (v : ℂ) := one_le_ellHat L hL hv0.le hv1
  obtain ⟨hz0, hz, hz'⟩ := zt_ne_zero_and_sq (E := E) (v := v) hE hv1
  have hcj : ‖1 - ((starRingEnd ℂ) (zt E v)) ^ 2‖ = ‖1 - (zt E v) ^ 2‖ := by
    rw [show (1 : ℂ) - ((starRingEnd ℂ) (zt E v)) ^ 2
        = (starRingEnd ℂ) (1 - (zt E v) ^ 2) by simp]
    exact RCLike.norm_conj _
  have hnsq := norm_one_sub_sq_le (E := E) (v := v) hE hv0.le hv1.le
  have hnsq0 : 0 < ‖1 - (zt E v) ^ 2‖ := norm_pos_iff.2 hz
  have hnumeq : ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
      = ((W : ℝ) * (‖1 - (zt E v) ^ 2‖ * ‖1 - (zt E v) ^ 2‖))⁻¹ := by
    rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_inv, hcj, Complex.norm_natCast]
    field_simp
  have hnum : 1 / (100 * (W : ℝ))
      ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖ := by
    rw [hnumeq, ← one_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hsq : ‖1 - (zt E v) ^ 2‖ * ‖1 - (zt E v) ^ 2‖ ≤ 100 := by nlinarith
    nlinarith [hsq, hWR, hnsq0]
  have hexp : Real.exp (-Real.sqrt (dd / ellHat L (v : ℂ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simp [Real.sqrt_nonneg]
  have hWD : (W : ℝ) ^ (-D) ≤ ((W : ℝ) ^ 2)⁻¹ := by
    have h2 : ((W : ℝ) ^ 2)⁻¹ = (W : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hW0.le, ← Real.rpow_natCast (W : ℝ) 2]
      norm_num
    rw [h2]
    exact Real.rpow_le_rpow_of_exponent_le hWR (by linarith)
  have hfirst : (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ *
        Real.exp (-Real.sqrt (dd / ellHat L (v : ℂ)))
      ≤ ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 := by
    have hℓη : etaT E t₀ ≤ ellHat L (v : ℂ) * etaT E v := by
      nlinarith [mul_le_mul_of_nonneg_right hℓ hηv.le]
    have hx : (W : ℝ) * etaT E t₀ ≤ (W : ℝ) * ellHat L (v : ℂ) * etaT E v := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hℓη hW0.le
    have hb : ((W : ℝ) ^ 2) * (etaT E t₀) ^ 2
        ≤ ((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (W : ℝ) * etaT E t₀ := by positivity
      have hp := pow_le_pow_left₀ h0 hx 2
      nlinarith [hp]
    have h1 : (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹
        ≤ (((W : ℝ) ^ 2) * (etaT E t₀) ^ 2)⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) hb
    have h2 : (((W : ℝ) ^ 2) * (etaT E t₀) ^ 2)⁻¹ = ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 := by
      field_simp
    calc (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ *
          Real.exp (-Real.sqrt (dd / ellHat L (v : ℂ)))
        ≤ (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (((W : ℝ) * ellHat L (v : ℂ) * etaT E v) ^ 2)⁻¹ := mul_one _
      _ ≤ (((W : ℝ) ^ 2) * (etaT E t₀) ^ 2)⁻¹ := h1
      _ = ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 := h2
  have hden : tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D dd
      ≤ ((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1) := by
    rw [tailT]
    have heq : ((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1)
        = ((W : ℝ) ^ 2)⁻¹ * (etaT E t₀)⁻¹ ^ 2 + ((W : ℝ) ^ 2)⁻¹ := by ring
    rw [heq]
    exact add_le_add hfirst hWD
  have hTpos : 0 < tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D dd := tailT_pos hW0 _
  have hc1 : (0 : ℝ) < (etaT E t₀)⁻¹ ^ 2 + 1 := by positivity
  calc (W : ℝ) / (200 * ((etaT E t₀)⁻¹ ^ 2 + 1))
      = (1 / (100 * (W : ℝ))) / (2 * (((W : ℝ) ^ 2)⁻¹ * ((etaT E t₀)⁻¹ ^ 2 + 1))) := by
        field_simp
        ring
    _ ≤ ‖((W : ℂ))⁻¹ * ((1 - (zt E v) ^ 2)⁻¹ * (1 - ((starRingEnd ℂ) (zt E v)) ^ 2)⁻¹)‖
        / (2 * tailT (W : ℝ) (ellHat L (v : ℂ)) (etaT E v) D dd) := by
        gcongr

/-- **The exponent a jump of size `g` forces**, at the time `v = N^{-2}` — the smallest time at
which T249's witness `ω = v^{-1/2}` is still inside `{‖X‖ ≤ N}`.  A modulus
`|J_v - J_0| ≤ N^{Kmod} |v|^{1/2}` there reads `g ≤ N^{Kmod - 1}`. -/
theorem kmod_ge_of_jump {Kmod g : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hmod : g ≤ (N : ℝ) ^ Kmod * (((N : ℝ) ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 2))) :
    g ≤ (N : ℝ) ^ (Kmod - 1) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hrw : ((N : ℝ) ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_mul hN0.le]
    norm_num
  rw [hrw, ← Real.rpow_add hN0] at hmod
  rwa [show Kmod + -(1 : ℝ) = Kmod - 1 by ring] at hmod

/-- **What `Kmod = 1` allows**, which is the exponent `RBM.EntryModulusEv` hard-codes: at
`v = N^{-2}` the jump can be at most `1`.  Together with `RBM.gap_lower_W` — whose jump is
`≥ W/(200((η_{t₀})^{-2}+1)) → ∞` — this refutes `Kmod = 1` **on the event as well**, so D17's
repair needs the exponent to grow with `D`. -/
theorem jump_le_one_of_kmod_one {g : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hmod : g ≤ (N : ℝ) ^ (1 : ℝ) * (((N : ℝ) ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 2))) : g ≤ 1 := by
  have h := kmod_ge_of_jump hN hmod
  rwa [show (1 : ℝ) - 1 = 0 by ring, Real.rpow_zero] at h

end Caveat

/-!
## Deviations from the paper

`T256a` — §5.3, the grid of p. 24, and (5.46).  **No change to the paper is proposed here**;
T251's proposed change (`T251a`: about four lines near (5.46) and one line on p. 24) is *not*
adopted, per D17.  What §3 of this file records is a deviation inside the *formalization*, not
in the paper: `RBM.EntryModulusEv` and `RBM.EntryModulusEvOn` write the paper's
high-probability continuity of (5.46) with the exponent pair `(Kmod, γ) = (1, 1/2)` **fixed**,
whereas the paper's argument only asks for *some* polynomial modulus, with the exponent allowed
to depend on `D`.  §3 shows the fixed choice `Kmod = 1` is too small.  Lines: 0 in the paper;
in Lean, the two definitions need `(N : ℝ) ^ (1 : ℝ)` replaced by `(N : ℝ) ^ Kmod` with `Kmod`
carried alongside `D`.  No renumbering.
-/

end RBM
