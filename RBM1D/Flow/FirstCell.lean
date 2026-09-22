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
* `RBM.Gauss.measurableSet_normX_le`        — §4, `good_meas` for `Good N = {‖X‖ ≤ N}`
* `RBM.Gauss.highProb_normX_le`             — §4, that event is `HighProb` (T100)
* `RBM.Gauss.eventually_nonempty_normX_le`  — §4, hence eventually nonempty (anti-vacuity)
* `RBM.exists_const_jTotEv`                 — §4, the event-route constant is `≤ K·N^{1+2D}`
* `RBM.eventually_modulus_jSfarSm_event`    — §4, the `modulus` field, `Kmod = 2+2D`, `γ = 1/2`
* `RBM.cutHypEvOn_jSfarSm_event`            — §4, ⭐ the complete `CutHypEvOn` **instance**
* `RBM.cutHypEvOn_jSfarSm_event_Kmod`       — §4, its own fields *are* `(2+2D, 1/2)` (`rfl`)
* `RBM.not_kmod_le_two_gamma_cutHypEvOn_jSfarSm_event` — §4, ⭐ the `Kmod > 2γ` gate for it
* `RBM.stochDom_jSfarSm_event`              — §4, the bundle + `HighProb` ⟹ `J*^{sm} ≺ Θ`
* `RBM.modulus_event_exampleGrow_zero`      — §5, the witness, window `[0, 1/2]`
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

/-- **The other side of the same arithmetic: what D17's pair allows** (T261).  At the same
time `v = N^{-2}`, a modulus with `Kmod = D - 1`, `γ = 1/2` has budget `N^{D-2}`, so for
`D ≥ 3` every jump of size at most `N` fits inside it.  `RBM.gap_lower_W`'s jump is
`W/(200((η_{t₀})^{-2}+1)) ≤ W/200`, and a band width never exceeds the matrix size, so the
jump that refutes `Kmod = 1` (`RBM.jump_le_one_of_kmod_one`) is comfortably inside D17's
budget.  Together the two lemmas say: the exponent must grow with `D`, and `D - 1` is
enough. -/
theorem jump_fits_kmod_d17 {D g : ℝ} {N : ℕ} (hN : 1 ≤ N) (hD : 3 ≤ D) (hg : g ≤ (N : ℝ)) :
    g ≤ (N : ℝ) ^ (D - 1) * (((N : ℝ) ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 2)) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hrw : ((N : ℝ) ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_mul hN0.le]
    norm_num
  rw [hrw, ← Real.rpow_add hN0, show D - 1 + -(1 : ℝ) = D - 2 by ring]
  have h1 : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ (D - 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_one] at h1
  linarith

end Caveat

/-! ### 4. T266: the event `{‖X‖ ≤ N}`, and the `CutHypEvOn` bundle it carries

§1–§3 settled the *deterministic* side of D17: on the event `{‖X‖ ≤ N}` the flow's resolvent
is Hölder-`1/2` in time **including at `u = 0`**, and the exponent `Kmod` has to grow.  T257
carried that all the way to the loop functional (`RBM.abs_jSfarSm_sub_le_event`, `γ = 1/2`,
`v = w = 0` allowed).  What was still missing for a `RBM.MomentDuhamelCut.CutHypEvOn` bundle
was the *probabilistic* side of the event itself:

* `RBM.Gauss.measurableSet_normX_le` — the `good_meas` field, from T100's
  `RBM.Gauss.measurable_norm_Xmat`;
* `RBM.Gauss.highProb_normX_le` — the `HighProb` the slot needs so that `Good = ∅` cannot make
  the modulus vacuously true, from T100's `RBM.Gauss.stochDom_norm_Xmat`.

With both in hand `RBM.cutHypEvOn_jSfarSm_event` is a **complete structure instance** with
`Good N = {ω | ‖X_N(ω)‖ ≤ N}`, `Kmod = 2 + 2D`, `γ = 1/2`, and — this is the point of §3 and
of T258 — it sits strictly on the `Kmod > 2γ` side of `RBM.not_cutHypEvOn_of_jump`.
-/

section T266

open Real Gauss Step2FarMart Filter MeasureTheory

namespace Gauss

/-- **The event of D17 is measurable** — the `good_meas` field of
`RBM.MomentDuhamelCut.CutHypEvOn` at `Good N = {ω | ‖X_N(ω)‖ ≤ N}`.  `ω ↦ ‖X_N(ω)‖` is
measurable by T100's `RBM.Gauss.measurable_norm_Xmat` (the entries are measurable and the
operator norm is continuous), so the sublevel set is measurable. -/
theorem measurableSet_normX_le (d : Dims) (N : ℕ) :
    MeasurableSet {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)} :=
  measurableSet_le (measurable_norm_Xmat d N) measurable_const

/-- **The event of D17 has high probability**, granted the trace moments.  This is T100's
`‖X‖ ≺ 1` (`RBM.Gauss.stochDom_norm_Xmat`) read at `τ = 1`.  It is what keeps the bundle from
being vacuous: on a probability space `HighProb` forces `Good N` to be eventually nonempty
(`RBM.HighProb.nonempty`), so the modulus of `RBM.cutHypEvOn_jSfarSm_event` is not a statement
about the empty set. -/
theorem highProb_normX_le (d : Dims) (h : TraceMomentBound d) :
    HighProb (band d).P (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}) := by
  refine ((stochDom_norm_Xmat h).highProb (τ := 1) one_pos).mono
    (Filter.Eventually.of_forall fun N ω hω => ?_)
  have h1 := hω ()
  rw [Real.rpow_one, mul_one] at h1
  exact h1

/-- **The event is eventually nonempty** — the anti-vacuity certificate for
`RBM.cutHypEvOn_jSfarSm_event`. -/
theorem eventually_nonempty_normX_le (d : Dims) (h : TraceMomentBound d) :
    ∀ᶠ N : ℕ in atTop, {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}.Nonempty :=
  (highProb_normX_le d h).nonempty (band d).isProbabilityMeasure.measure_univ

end Gauss

/-! The size of the event-route modulus constant.  `RBM.jTot_le_const_mul_rpow` does this for
the `‖X‖`-free route (`N^{1+C+2D}`, where `N^C` pays for `s_N^{-1/2}`); here the `s`-dependence
is gone and the factor `(N+1)` of `RBM.lkLipEv` takes its place, so the honest exponent is
`N^{1+2D}` — provided `D ≥ 1`, which is what makes `N^{2+D} ≤ N^{1+2D}`. -/

/-- **The whole event-route modulus constant is `N^{1+2D}` times an `(E, t₀)`-constant.**

`RBM.jSfarSmLip` contributes `N^{1+D}` and `N^{1+2D}` (through `L ≤ N`, `W^{D} ≤ N^{D}`), and
`RBM.lkLipEv · W^D` contributes `N^{2+D}` (through `L·W ≤ N` and the factor `N + 1` the event
leaves behind).  `D ≥ 1` is exactly what puts `N^{2+D}` under `N^{1+2D}`. -/
theorem exists_const_jTotEv (d : Dims) {E D t₀ : ℝ} (hE : |E| < 2) (hD : 1 ≤ D)
    (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1) :
    ∃ K > (0 : ℝ), ∀ N : ℕ, (1 : ℝ) ≤ (N : ℝ) → (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) →
      jSfarSmLip d N E D t₀ + lkLipEv d N E t₀ * (d.W N : ℝ) ^ D
        ≤ K * (N : ℝ) ^ (1 + 2 * D) := by
  have h1t : (0 : ℝ) < 1 - t₀ := by linarith
  have hst : 0 < √(1 - t₀) := Real.sqrt_pos.2 h1t
  have hq0 : (0 : ℝ) < (etaT E t₀)⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE ht₀)
  have hq1 : (1 : ℝ) ≤ (etaT E t₀)⁻¹ := one_le_inv_etaT hE ht₀0 ht₀
  have hr0 : (0 : ℝ) < (1 - t₀)⁻¹ := inv_pos.2 h1t
  have hCp0 : (0 : ℝ) < (2 * √(1 - t₀))⁻¹ := by positivity
  set q : ℝ := (etaT E t₀)⁻¹ with hqdef
  set r : ℝ := (1 - t₀)⁻¹ with hrdef
  set Cp : ℝ := (2 * √(1 - t₀))⁻¹ with hCpdef
  set Kt : ℝ := 2 * Cp * q ^ 2 + 2 * q ^ 3 + q ^ 2 * Cp / 2 with hKtdef
  refine ⟨15 / 96 * Cp * (q * q + r) + (q * q + r) * Kt + 4 * (q ^ 2 * q ^ 2) + r * r, ?_, ?_⟩
  · have hKt0 : 0 < Kt := by rw [hKtdef]; positivity
    positivity
  intro N hN1 hWL
  have hWr1 : (1 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hLr1 : (1 : ℝ) ≤ (d.L N : ℝ) := by
    have := d.three_le_L N; exact_mod_cast (by omega : 1 ≤ d.L N)
  have hWr0 : (0 : ℝ) < (d.W N : ℝ) := by linarith
  have hWinv0 : (0 : ℝ) < ((d.W N : ℝ))⁻¹ := inv_pos.2 hWr0
  have hWinv1 : ((d.W N : ℝ))⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; exact Or.inr hWr1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hWN : (d.W N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hLN : (d.L N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hWD : (d.W N : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow (by linarith) hWN hD0
  have hW2D : (d.W N : ℝ) ^ (2 * D) ≤ (N : ℝ) ^ (2 * D) :=
    Real.rpow_le_rpow (by linarith) hWN (by linarith)
  have hWD0 : (0 : ℝ) < (d.W N : ℝ) ^ D := Real.rpow_pos_of_pos hWr0 _
  have hW2D0 : (0 : ℝ) < (d.W N : ℝ) ^ (2 * D) := Real.rpow_pos_of_pos hWr0 _
  have hND0 : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 _
  have hA0 : (0 : ℝ) < (N : ℝ) ^ (1 + 2 * D) := Real.rpow_pos_of_pos hN0 _
  -- the four `N`-power products
  have hfac1 : (d.L N : ℝ) * ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D ≤ (N : ℝ) ^ (1 + 2 * D) := by
    calc (d.L N : ℝ) * ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D
        ≤ (N : ℝ) * 1 * (N : ℝ) ^ D :=
          mul_le_mul (mul_le_mul hLN hWinv1 hWinv0.le hN0.le) hWD hWD0.le (by linarith)
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ D := by rw [Real.rpow_one]; ring
      _ ≤ (N : ℝ) ^ (1 + 2 * D) := rpow_mul_rpow_le hN1 (by linarith)
  have hfac2 : ((d.W N : ℝ))⁻¹ * ((N : ℝ) * (d.W N : ℝ) ^ (2 * D))
      ≤ (N : ℝ) ^ (1 + 2 * D) := by
    calc ((d.W N : ℝ))⁻¹ * ((N : ℝ) * (d.W N : ℝ) ^ (2 * D))
        ≤ 1 * ((N : ℝ) * (N : ℝ) ^ (2 * D)) :=
          mul_le_mul hWinv1 (mul_le_mul_of_nonneg_left hW2D hN0.le) (by positivity) (by norm_num)
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (2 * D) := by rw [Real.rpow_one]; ring
      _ ≤ (N : ℝ) ^ (1 + 2 * D) := rpow_mul_rpow_le hN1 (by linarith)
  have hfac3 : (d.L N : ℝ) * (d.W N : ℝ) * (((N : ℝ) + 1) * (d.W N : ℝ) ^ D)
      ≤ 2 * (N : ℝ) ^ (1 + 2 * D) := by
    have hstep1 : (d.L N : ℝ) * (d.W N : ℝ) ≤ (N : ℝ) := by nlinarith
    have hstep2 : ((N : ℝ) + 1) * (d.W N : ℝ) ^ D ≤ 2 * ((N : ℝ) * (N : ℝ) ^ D) := by
      have h1 : ((N : ℝ) + 1) ≤ 2 * (N : ℝ) := by linarith
      calc ((N : ℝ) + 1) * (d.W N : ℝ) ^ D ≤ (2 * (N : ℝ)) * (N : ℝ) ^ D :=
            mul_le_mul h1 hWD hWD0.le (by linarith)
        _ = 2 * ((N : ℝ) * (N : ℝ) ^ D) := by ring
    have hprod : (d.L N : ℝ) * (d.W N : ℝ) * (((N : ℝ) + 1) * (d.W N : ℝ) ^ D)
        ≤ (N : ℝ) * (2 * ((N : ℝ) * (N : ℝ) ^ D)) := by
      refine mul_le_mul hstep1 hstep2 (by positivity) hN0.le
    refine hprod.trans ?_
    have hpow : (N : ℝ) * (N : ℝ) * (N : ℝ) ^ D ≤ (N : ℝ) ^ (1 + 2 * D) := by
      calc (N : ℝ) * (N : ℝ) * (N : ℝ) ^ D
          = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ D := by
            rw [Real.rpow_one]
        _ ≤ (N : ℝ) ^ (1 + 2 * D) := rpow_mul_rpow_mul_rpow_le hN1 (by linarith)
    nlinarith
  have hfac4 : ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D ≤ (N : ℝ) ^ (1 + 2 * D) := by
    calc ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D ≤ 1 * (N : ℝ) ^ D :=
          mul_le_mul hWinv1 hWD hWD0.le (by norm_num)
      _ = (N : ℝ) ^ D := by ring
      _ ≤ (N : ℝ) ^ (1 + 2 * D) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- the three summands
  have hb1 : 15 / 8 * ((d.L N : ℝ) / 12 * Cp) * (crudeLk d N E t₀ * (d.W N : ℝ) ^ D)
      ≤ 15 / 96 * Cp * (q * q + r) * (N : ℝ) ^ (1 + 2 * D) := by
    have hrw : 15 / 8 * ((d.L N : ℝ) / 12 * Cp) * (crudeLk d N E t₀ * (d.W N : ℝ) ^ D)
        = 15 / 96 * Cp * (q * q + r)
          * ((d.L N : ℝ) * ((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D) := by
      rw [crudeLk, hqdef, hrdef]; ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hfac1 (by positivity)
  have htl : tailLip d N E t₀ ≤ Kt * (N : ℝ) := by
    rw [tailLip, hKtdef, ← hqdef, ← hCpdef]
    have e1 : 2 * Cp * q ^ 2 ≤ 2 * Cp * q ^ 2 * (N : ℝ) :=
      le_mul_of_one_le_right (by positivity) hN1
    have e2 : 2 * q ^ 3 ≤ 2 * q ^ 3 * (N : ℝ) := le_mul_of_one_le_right (by positivity) hN1
    have e3 : q ^ 2 * ((d.L N : ℝ) / 2) * Cp ≤ q ^ 2 * Cp / 2 * (N : ℝ) := by
      calc q ^ 2 * ((d.L N : ℝ) / 2) * Cp = q ^ 2 * Cp / 2 * (d.L N : ℝ) := by ring
        _ ≤ q ^ 2 * Cp / 2 * (N : ℝ) := mul_le_mul_of_nonneg_left hLN (by positivity)
    linarith
  have hb2 : crudeLk d N E t₀ * (tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D))
      ≤ (q * q + r) * Kt * (N : ℝ) ^ (1 + 2 * D) := by
    have hKt0 : 0 < Kt := by rw [hKtdef]; positivity
    have hcr : crudeLk d N E t₀ = ((d.W N : ℝ))⁻¹ * (q * q + r) := rfl
    have hstep : tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D)
        ≤ Kt * ((N : ℝ) * (d.W N : ℝ) ^ (2 * D)) := by
      have := mul_le_mul_of_nonneg_right htl hW2D0.le
      calc tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D)
          ≤ Kt * (N : ℝ) * (d.W N : ℝ) ^ (2 * D) := this
        _ = Kt * ((N : ℝ) * (d.W N : ℝ) ^ (2 * D)) := by ring
    calc crudeLk d N E t₀ * (tailLip d N E t₀ * (d.W N : ℝ) ^ (2 * D))
        ≤ ((d.W N : ℝ))⁻¹ * (q * q + r) * (Kt * ((N : ℝ) * (d.W N : ℝ) ^ (2 * D))) := by
          rw [hcr]
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (q * q + r) * Kt * (((d.W N : ℝ))⁻¹ * ((N : ℝ) * (d.W N : ℝ) ^ (2 * D))) := by ring
      _ ≤ (q * q + r) * Kt * (N : ℝ) ^ (1 + 2 * D) :=
          mul_le_mul_of_nonneg_left hfac2 (by positivity)
  have hb3 : lkLipEv d N E t₀ * (d.W N : ℝ) ^ D
      ≤ (4 * (q ^ 2 * q ^ 2) + r * r) * (N : ℝ) ^ (1 + 2 * D) := by
    have hrw : lkLipEv d N E t₀ * (d.W N : ℝ) ^ D
        = 2 * (q ^ 2 * (q * q))
            * ((d.L N : ℝ) * (d.W N : ℝ) * (((N : ℝ) + 1) * (d.W N : ℝ) ^ D))
          + r * r * (((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D) := by
      rw [lkLipEv, hqdef, hrdef]; ring
    rw [hrw]
    have h1 : 2 * (q ^ 2 * (q * q))
        * ((d.L N : ℝ) * (d.W N : ℝ) * (((N : ℝ) + 1) * (d.W N : ℝ) ^ D))
        ≤ 4 * (q ^ 2 * q ^ 2) * (N : ℝ) ^ (1 + 2 * D) := by
      calc 2 * (q ^ 2 * (q * q))
            * ((d.L N : ℝ) * (d.W N : ℝ) * (((N : ℝ) + 1) * (d.W N : ℝ) ^ D))
          ≤ 2 * (q ^ 2 * (q * q)) * (2 * (N : ℝ) ^ (1 + 2 * D)) :=
            mul_le_mul_of_nonneg_left hfac3 (by positivity)
        _ = 4 * (q ^ 2 * q ^ 2) * (N : ℝ) ^ (1 + 2 * D) := by ring
    have h2 : r * r * (((d.W N : ℝ))⁻¹ * (d.W N : ℝ) ^ D)
        ≤ r * r * (N : ℝ) ^ (1 + 2 * D) :=
      mul_le_mul_of_nonneg_left hfac4 (by positivity)
    linarith
  rw [jSfarSmLip, ← hCpdef]
  linarith

/-- **The `modulus` field of `RBM.MomentDuhamelCut.CutHypEvOn` for `jSfarSm` on the event
`{‖X‖ ≤ N}`**, with `Kmod = 2 + 2D`, `γ = 1/2`.

Complementary to `RBM.eventually_modulus_jSfarSm` (T257, `γ = 1`, `Good ≡ univ`): there the
left endpoint of the window has to satisfy `s_N ≥ N^{-C}`, **here `s_N = 0` is allowed**.  That
is the whole content of D17 for the first cell of the grid of p. 24. -/
theorem eventually_modulus_jSfarSm_event (d : Dims) {E D t₀ : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)},
      ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |jSfarSm (sample d) E D N v ω - jSfarSm (sample d) E D N w ω|
        ≤ (N : ℝ) ^ (2 + 2 * D) * |v - w| ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := exists_const_jTotEv d hE hD ht₀0 ht₀
  have hbig : ∀ᶠ N : ℕ in atTop, max 1 K ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [d.dim, hbig, eventually_one_le_log_W d] with N hdimN hbigN hlogW
  intro ω hX v hv w hw
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (le_max_left _ _) hbigN
  have hKN : K ≤ (N : ℝ) := le_trans (le_max_right _ _) hbigN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
    have := hdimN.1
    exact_mod_cast (by exact_mod_cast this : ((d.W N * d.L N : ℕ) : ℝ) ≤ (N : ℝ))
  have hv0 : (0 : ℝ) ≤ v := le_trans (hs0 N) hv.1
  have hw0 : (0 : ℝ) ≤ w := le_trans (hs0 N) hw.1
  have hvt : v ≤ t₀ := hv.2.trans (htt N)
  have hwt : w ≤ t₀ := hw.2.trans (htt N)
  have hlen : |v - w| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have h1 := abs_jSfarSm_sub_le_event d N ω (D := D) (t₀ := t₀) hE hv0 hw0 hvt hwt ht₀ ht₀0
    hlen hlogW hX
  have h2 := hK N hN1 hWL
  have hp0 : (0 : ℝ) ≤ |v - w| ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hA0 : (0 : ℝ) < (N : ℝ) ^ (1 + 2 * D) := Real.rpow_pos_of_pos hN0 _
  have hpow : (N : ℝ) ^ (2 + 2 * D) = (N : ℝ) * (N : ℝ) ^ (1 + 2 * D) := by
    rw [show (2 : ℝ) + 2 * D = 1 + (1 + 2 * D) by ring, Real.rpow_add hN0, Real.rpow_one]
  calc |jSfarSm (sample d) E D N v ω - jSfarSm (sample d) E D N w ω|
      ≤ |v - w| ^ ((1 : ℝ) / 2)
        * (jSfarSmLip d N E D t₀ + lkLipEv d N E t₀ * (d.W N : ℝ) ^ D) := h1
    _ ≤ |v - w| ^ ((1 : ℝ) / 2) * (K * (N : ℝ) ^ (1 + 2 * D)) :=
        mul_le_mul_of_nonneg_left h2 hp0
    _ ≤ |v - w| ^ ((1 : ℝ) / 2) * ((N : ℝ) * (N : ℝ) ^ (1 + 2 * D)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKN hA0.le) hp0
    _ = (N : ℝ) ^ (2 + 2 * D) * |v - w| ^ ((1 : ℝ) / 2) := by rw [hpow]; ring

/-- ⭐ **The `CutHypEvOn` bundle of D17's first cell** — a *complete structure instance*, not a
`#check`.  `Good N = {ω | ‖X_N(ω)‖ ≤ N}`, `Kmod = 2 + 2D`, `γ = 1/2`, and the window may start
at `0`: only `∀ N, 0 ≤ s N` is asked, never `0 < s N`.

Three fields are the content of this ticket — `good_meas` is
`RBM.Gauss.measurableSet_normX_le`, `modulus` is `RBM.eventually_modulus_jSfarSm_event`, and
`meas` is T244's `RBM.measurable_jSfarSm`; the rest are explicit parameters, exactly as in
T257's `RBM.cutHypEvOn_jSfarSm`.

⚠ The `HighProb` of the event is **not** a field of `CutHypEvOn`; it is the separate hypothesis
of `RBM.MomentDuhamelCut.stochDom_of_cutHypEvOn`, and
`RBM.Gauss.highProb_normX_le` supplies it.  `RBM.Gauss.eventually_nonempty_normX_le` is the
anti-vacuity certificate that goes with it. -/
noncomputable def cutHypEvOn_jSfarSm_event (d : Dims) {E D t₀ : ℝ} {s t Θ : ℕ → ℝ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀)
    (hwindow : ∀ N, s N ≤ t N) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hΘpos : ∀ N, 0 < Θ N)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ Θ N)
    (Ccard : ℝ) (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (hmoment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ K > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t mesh N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N)
            (jSfarSm (sample d) E D N ws ω)| ^ (2 * p) ∂(band d).P
          ≤ K * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p))) :
    MomentDuhamelCut.CutHypEvOn (band d).P (fun N u ω => jSfarSm (sample d) E D N u ω)
      s t Θ (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}) where
  window := hwindow
  δ₀ := δ₀
  δ₀_pos := hδ₀
  Θ_pos := hΘpos
  J_nonneg := fun _ _ _ => le_trans zero_le_one (Step2FarMart.one_le_jSfarSm _)
  meas := fun N u => (measurable_jSfarSm (sample d) E D N u).aestronglyMeasurable
  good_meas := fun N => Gauss.measurableSet_normX_le d N
  mesh := mesh
  mesh_pos := hmesh
  Kmod := 2 + 2 * D
  γ := (1 : ℝ) / 2
  γ_pos := by norm_num
  modulus := eventually_modulus_jSfarSm_event d hE hD ht₀0 ht₀ hs0 htt
  mesh_fine := hfine
  Ccard := Ccard
  card_le := hcard
  moment := hmoment

/-- ⭐ **The bundle's own fields are the pair `(2 + 2D, 1/2)`** — by `rfl`, on the very object
`RBM.cutHypEvOn_jSfarSm_event` produces.  Without this the gate below would be a statement
about numbers nobody built (the lesson T261 records). -/
theorem cutHypEvOn_jSfarSm_event_Kmod (d : Dims) {E D t₀ : ℝ} {s t Θ : ℕ → ℝ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀)
    (hwindow : ∀ N, s N ≤ t N) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hΘpos : ∀ N, 0 < Θ N)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ Θ N)
    (Ccard : ℝ) (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (hmoment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ K > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t mesh N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N)
            (jSfarSm (sample d) E D N ws ω)| ^ (2 * p) ∂(band d).P
          ≤ K * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p))) :
    (cutHypEvOn_jSfarSm_event d hE hD ht₀0 ht₀ hs0 htt hwindow δ₀ hδ₀ hΘpos mesh hmesh hfine
        Ccard hcard hmoment).Kmod = 2 + 2 * D ∧
      (cutHypEvOn_jSfarSm_event d hE hD ht₀0 ht₀ hs0 htt hwindow δ₀ hδ₀ hΘpos mesh hmesh hfine
        Ccard hcard hmoment).γ = (1 : ℝ) / 2 :=
  ⟨rfl, rfl⟩

/-- ⭐⭐ **The gate: T258's refutation does not apply to this bundle.**

`RBM.not_cutHypEvOn_of_jump` kills every `CutHypEvOn` whose own fields satisfy
`Kmod ≤ 2γ`.  The bundle built above has `Kmod = 2 + 2D ≥ 4` and `2γ = 1`, so it is strictly
on the other side — and the statement is about *its* fields, via
`RBM.cutHypEvOn_jSfarSm_event_Kmod`, not about an abstract pair. -/
theorem not_kmod_le_two_gamma_cutHypEvOn_jSfarSm_event (d : Dims) {E D t₀ : ℝ} {s t Θ : ℕ → ℝ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀)
    (hwindow : ∀ N, s N ≤ t N) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hΘpos : ∀ N, 0 < Θ N)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ Θ N)
    (Ccard : ℝ) (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (hmoment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ K > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t mesh N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N)
            (jSfarSm (sample d) E D N ws ω)| ^ (2 * p) ∂(band d).P
          ≤ K * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p))) :
    ¬ ((cutHypEvOn_jSfarSm_event d hE hD ht₀0 ht₀ hs0 htt hwindow δ₀ hδ₀ hΘpos mesh hmesh
          hfine Ccard hcard hmoment).Kmod
        ≤ 2 * (cutHypEvOn_jSfarSm_event d hE hD ht₀0 ht₀ hs0 htt hwindow δ₀ hδ₀ hΘpos mesh
          hmesh hfine Ccard hcard hmoment).γ) := by
  obtain ⟨hK, hγ⟩ := cutHypEvOn_jSfarSm_event_Kmod d hE hD ht₀0 ht₀ hs0 htt hwindow δ₀ hδ₀
    hΘpos mesh hmesh hfine Ccard hcard hmoment
  rw [hK, hγ]
  intro h
  linarith

/-- **The packaging, end to end.**  The bundle of `RBM.cutHypEvOn_jSfarSm_event` together with
the high probability of its own event (`RBM.Gauss.highProb_normX_le`) yields `J*^{sm} ≺ Θ` on
the whole window through `RBM.MomentDuhamelCut.stochDom_of_cutHypEvOn` — window left endpoint
`0` included.

⚠ This is where `HighProb` is consumed, and it is the reason it must be carried alongside the
bundle rather than dropped: at `Good = ∅` the `modulus` field would be vacuously true, and
`RBM.HighProb.nonempty` (via `RBM.Gauss.eventually_nonempty_normX_le`) is what rules that
out. -/
theorem stochDom_jSfarSm_event (d : Dims) (hTM : TraceMomentBound d) {E D t₀ : ℝ}
    {s t Θ : ℕ → ℝ}
    (hE : |E| < 2) (hD : 1 ≤ D) (ht₀0 : 0 ≤ t₀) (ht₀ : t₀ < 1)
    (hs0 : ∀ N, 0 ≤ s N) (htt : ∀ N, t N ≤ t₀)
    (hwindow : ∀ N, s N ≤ t N) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hΘpos : ∀ N, 0 < Θ N)
    (mesh : ℕ → ℝ) (hmesh : ∀ N, 0 < mesh N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / mesh N) ^ ((1 : ℝ) / 2) ≤ Θ N)
    (Ccard : ℝ) (hcard : ∀ᶠ N : ℕ in atTop, (t N - s N) * mesh N + 2 ≤ (N : ℝ) ^ Ccard)
    (hmoment : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ K > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t mesh N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * Θ N)
            (jSfarSm (sample d) E D N ws ω)| ^ (2 * p) ∂(band d).P
          ≤ K * ((N : ℝ) ^ (ε * p) * Θ N ^ (2 * p)))
    (hΘ1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Θ N)
    (hinit : StochDom (band d).P
      (fun N (_ : Unit) ω => jSfarSm (sample d) E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    StochDom (band d).P
      (fun N (u : TimeIcc s t N) ω => jSfarSm (sample d) E D N (u : ℝ) ω)
      (fun N _ _ => Θ N) :=
  letI := (band d).isProbabilityMeasure
  MomentDuhamelCut.stochDom_of_cutHypEvOn
    (cutHypEvOn_jSfarSm_event d hE hD ht₀0 ht₀ hs0 htt hwindow δ₀ hδ₀ hΘpos mesh hmesh hfine
      Ccard hcard hmoment)
    (Gauss.highProb_normX_le d hTM) hΘ1 hinit

end T266

/-! ### 5. T266: satisfiability witnesses

`RBM.Gauss.Dims.exampleGrow`, `E = 0`, `D = 1`, `t₀ = 1/2`, and the **degenerate-free** window
`s ≡ 0`, `t ≡ 1/2` — the first cell of the grid of p. 24, left endpoint exactly `0`, which is
the cell T249 refuted for the `‖X‖`-free route.  `Kmod = 2 + 2·1 = 4`, `γ = 1/2`, so
`Kmod > 2γ = 1`.
-/

section T266Witness

open Real Gauss Step2FarMart Filter

/-- The event-route Lipschitz constant is strictly positive at `exampleGrow`: the modulus of
`RBM.modulus_event_exampleGrow_zero` is not the vacuous `≤ 0`. -/
theorem lkLipEv_pos_exampleGrow (N : ℕ) : 0 < lkLipEv Dims.exampleGrow N 0 (1 / 2) := by
  have hE : |(0 : ℝ)| < 2 := by norm_num
  have hq : (0 : ℝ) < (etaT 0 (1 / 2 : ℝ))⁻¹ := inv_pos.2 (etaT_pos_of_lt_one' hE (by norm_num))
  have hW : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by exact_mod_cast Dims.exampleGrow.W_pos N
  have hL : (0 : ℝ) < (Dims.exampleGrow.L N : ℝ) := by
    have := Dims.exampleGrow.three_le_L N
    exact_mod_cast (by omega : 0 < Dims.exampleGrow.L N)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  unfold lkLipEv
  have h1 : (0 : ℝ) < 1 - (1 / 2 : ℝ) := by norm_num
  positivity

/-- **The compiled witness for the `modulus` field on the event**, at `d = exampleGrow`,
`E = 0`, `D = 1`, window `[0, 1/2]` — **left endpoint `0`**, which is exactly what T257's
`γ = 1` route cannot do.  `Kmod = 2 + 2·1 = 4`, `γ = 1/2`. -/
theorem modulus_event_exampleGrow_zero :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)},
      ∀ v ∈ Set.Icc ((fun _ : ℕ => (0 : ℝ)) N) ((fun _ : ℕ => (1 / 2 : ℝ)) N),
      ∀ w ∈ Set.Icc ((fun _ : ℕ => (0 : ℝ)) N) ((fun _ : ℕ => (1 / 2 : ℝ)) N),
      |jSfarSm (sample Dims.exampleGrow) 0 1 N v ω
          - jSfarSm (sample Dims.exampleGrow) 0 1 N w ω|
        ≤ (N : ℝ) ^ (2 + 2 * (1 : ℝ)) * |v - w| ^ ((1 : ℝ) / 2) :=
  eventually_modulus_jSfarSm_event Dims.exampleGrow (t₀ := 1 / 2) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (fun _ => le_rfl) (fun _ => le_rfl)

/-- **The window `[0, 1/2]` is non-degenerate**: it contains `0` (the cell T249 refuted) and is
not a single point, so `RBM.modulus_event_exampleGrow_zero` really constrains a difference. -/
theorem window_exampleGrow_nondegenerate :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      (0 : ℝ) < 1 / 2 := ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The pair `(Kmod, γ) = (4, 1/2)` of the witness is outside T258's refutation range**
`Kmod ≤ 2γ`. -/
theorem d17_event_pair_outside_refutation : ¬ ((2 + 2 * (1 : ℝ)) ≤ 2 * ((1 : ℝ) / 2)) := by
  norm_num

/-- **The two fields that pull against each other are jointly satisfiable at this bundle's own
exponents.**  T258's `RBM.sat_meshK_pair`, read at `(Kmod, γ) = (2 + 2D, 1/2)`: with
`Θ ≡ 1` the mesh `RBM.meshK (2 + 2D) (1/2)` satisfies `mesh_fine` outright and `card_le` at
`Ccard = (2 + 2D)/(1/2) + 1`.  So `mesh_fine` and `card_le` cannot make
`RBM.cutHypEvOn_jSfarSm_event` unsatisfiable. -/
theorem sat_mesh_pair_event {D : ℝ} (hD : 1 ≤ D) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    (∀ N : ℕ, 0 < meshK (2 + 2 * D) (1 / 2) N) ∧
    (∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (2 + 2 * D) * (1 / meshK (2 + 2 * D) (1 / 2) N) ^ ((1 : ℝ) / 2) ≤ (1 : ℝ)) ∧
    (∀ᶠ N : ℕ in atTop, (t N - s N) * meshK (2 + 2 * D) (1 / 2) N + 2
        ≤ (N : ℝ) ^ ((2 + 2 * D) / ((1 : ℝ) / 2) + 1)) := by
  obtain ⟨h1, h2, h3⟩ := sat_meshK_pair (Kmod := 2 + 2 * D) (γ := (1 : ℝ) / 2) (s := s) (t := t)
    (by linarith) (by norm_num) hs0 ht1
  exact ⟨h1, Filter.Eventually.of_forall h2, h3⟩

/-- The mesh at this bundle's pair, explicitly: `Kmod = 2 + 2D`, `γ = 1/2` gives
`(N+1)^{4+4D}`. -/
theorem meshK_event_eq (D : ℝ) :
    meshK (2 + 2 * D) (1 / 2) = fun N : ℕ => ((N : ℝ) + 1) ^ (4 + 4 * D) := by
  funext N
  rw [meshK]
  ring_nf

/-- ⭐ **A `CutHypEvOn` bundle with every parameter pinned down but `moment`.**

`d = exampleGrow`, `E = 0`, `D = 1`, window `s ≡ 0`, `t ≡ 1/2` (**left endpoint `0`**),
`Θ ≡ 1`, `mesh = RBM.meshK 4 (1/2) = (N+1)^8`, `Ccard = 9`, `Good N = {‖X_N‖ ≤ N}`,
`Kmod = 4`, `γ = 1/2`.  `mesh_fine` and `card_le` are discharged by
`RBM.sat_mesh_pair_event`, so nothing but the `moment` field — which is T230's business, not
this ticket's — is left open.  This is the compiled certificate that the bundle's shape is
inhabitable at a concrete model on the cell the grid of p. 24 starts with. -/
noncomputable def cutHypEvOn_event_exampleGrow
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ K > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ))
          (meshK (2 + 2 * (1 : ℝ)) (1 / 2)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1)
            (jSfarSm (sample Dims.exampleGrow) 0 1 N ws ω)| ^ (2 * p)
              ∂(band Dims.exampleGrow).P
          ≤ K * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    MomentDuhamelCut.CutHypEvOn (band Dims.exampleGrow).P
      (fun N u ω => jSfarSm (sample Dims.exampleGrow) 0 1 N u ω)
      (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => (1 : ℝ))
      (fun N => {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}) :=
  cutHypEvOn_jSfarSm_event Dims.exampleGrow (by norm_num) le_rfl (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by norm_num) 1 one_pos (fun _ => one_pos)
    (meshK (2 + 2 * (1 : ℝ)) (1 / 2)) (meshK_pos _ _)
    ((sat_mesh_pair_event (D := 1) (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
      le_rfl (fun _ => le_rfl) (fun _ => by norm_num)).2.1)
    ((2 + 2 * (1 : ℝ)) / ((1 : ℝ) / 2) + 1)
    ((sat_mesh_pair_event (D := 1) (s := fun _ => (0 : ℝ)) (t := fun _ => (1 / 2 : ℝ))
      le_rfl (fun _ => le_rfl) (fun _ => by norm_num)).2.2)
    hmoment

end T266Witness

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

**T261 (2026-09-21) carried it out**, without touching either old definition: the parametric
fields are `RBM.EntryModulusEvK` / `RBM.EntryModulusEvKOn` (T258, `Flow/Eq548Producer.lean`)
and the parametric (5.48) slot is `RBM.Eq548EntryDataEvOnK'`
(`Flow/Thm221Assembly.lean` §10), feeding `RBM.thm221NoEL_of_inputs_mergedOnAllK` and its
Gaussian twin with the conclusion `RBM.Thm221NoEL` unchanged.  The pair carried is exactly
§3's: `Kmod = D - 1`, `γ = 1/2`, whose budget at `v = N^{-2}` is `RBM.jump_fits_kmod_d17`
above.  The paper-side change is recorded there as `T261a`; this file's "no change to the
paper" reading of `T256a` is superseded by it, since T258 refuted the exponent `1` on a
concrete model (`RBM.not_entryModulusEvKOn_one_half_bandGrow`).

## Deviations (T266a)

**Paper location**: §5.3, (5.46)–(5.48); the grid of p. 24; (5.27) for `T_{u,D}`.

1. **The modulus of (5.46) is asserted only on the event `{‖X_N‖ ≤ N}`.**  The paper states
   its continuity in `u` for every sample point.  T249's
   `RBM.not_entryModulusEv_swapSample_of_far` shows the unrestricted form is **false** on a
   window whose left endpoint is `0`, because the Hölder constant of `u ↦ G_u` along the flow
   `H_u = √u X` is `O(‖X‖)` and `‖X‖` is unbounded.  The repair is the event, which is of high
   probability (`RBM.Gauss.highProb_normX_le`, from T100's `‖X‖ ≺ 1`) and hence eventually
   nonempty (`RBM.Gauss.eventually_nonempty_normX_le`), so nothing is lost and nothing becomes
   vacuous.  *Change the paper?*  One sentence in §5.3 saying the continuity is claimed on
   `{‖X‖ ≤ N}`.  *Lines*: one.  *Renumbering*: no.
2. **`Kmod = 2 + 2D` is not optimal, and `D ≥ 1` is an explicit hypothesis.**  The honest
   exponent is `N^{1+2D}` times an `(E, t₀)`-constant (`RBM.exists_const_jTotEv`); the extra
   `+1` only absorbs that constant into a power of `N`, exactly as in `T257a`(3).  `1 ≤ D` is
   used once, to put the `N^{2+D}` coming from `RBM.lkLipEv · W^D` under `N^{1+2D}`; the paper
   only ever uses `D` large, so this costs nothing.  *Change the paper?*  No.  *Lines*: none.
   *Renumbering*: no.
3. **The high probability of the event rests on `RBM.Gauss.TraceMomentBound`.**  That is the
   combinatorial input `E Tr(X^{2p}) ≤ C_p N` of T100, which the paper uses without comment
   when it writes `‖H‖ ≤ 2 + o(1)`.  It appears here as an explicit hypothesis of
   `RBM.Gauss.highProb_normX_le` and `RBM.stochDom_jSfarSm_event`, not as an axiom.
   *Change the paper?*  No.  *Renumbering*: no.
4. **Two incomparable exponent pairs now live side by side**, continuing `T257a`(4):
   `(2 + C + 2D, 1)` off `{s = 0}` and for every `ω` (T257), and `(2 + 2D, 1/2)` including
   `s = 0` but only on `{‖X‖ ≤ N}` (this file).  Both are strictly inside `Kmod > 2γ`, so
   neither is touched by T258's `RBM.not_cutHypEvOn_of_jump`; the second is the one D17 needs
   for the first cell of the grid.  *Change the paper?*  No.  *Renumbering*: no.
-/

end RBM
