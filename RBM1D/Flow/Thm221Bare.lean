/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221Gain

/-!
# Theorem 2.21 with the **bare** (2.72) (T186)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

`RBM.Cond272` is (2.72) exactly as printed on p. 24; `RBM.Cond272'` (T179) is the same with an
`N^c` gain, which is what the six steps of §2.7 consume (`hregS`).  T174/T132c recomputed the
exponent table along the (2.73)-reduced shape and found every row **strictly** below 30, so the
gain was expected to be removable.  This file settles what the bare (2.72) does and does not
buy.

## Answer

The bare (2.72) is **not** enough by itself, and the obstruction is not an exponent: it is that
(2.72) puts **no polynomial lower bound on `A_t = W ℓ_t η_t`**.  At `s = t` it says exactly
`1 ≤ A_t`, and `A_t = 1` is attained (`RBM.Band.eventually_exists_scale_eq_one`), so
`RBM.exists_cond272_not_rpow_le_scale` produces a time sequence satisfying (2.72) verbatim for
which `N^c ≤ A_t` fails for every `c > 0`.  Every consumer of `hregS` needs a strictly positive
power of `N` to absorb the `N^δ` of `≺`, so this is fatal on its own.

What *is* enough is (2.72) **as printed** together with the regime bound `N^c ≤ W ℓ_t η_t` that
Step 1 already carries as a named hypothesis (`RBM.eventually_scale_facts`,
`RBM.weakLaw_highProb`) and that the grid of p. 24 supplies for free (on the grid
`η_s/η_t = W^{τ'}` is itself a positive power of `W`).  That is `RBM.Cond272Reg`, and

* `RBM.Cond272Reg.margin` turns it into the gained form **at every exponent `b < 30`**, with a
  gain `N^{c(1 - b/30)}`: the arithmetic `R^b ≤ A^{b/30}`, `N^e ≤ A^{e/c}`,
  `A^{e/c + b/30} ≤ A^a`;
* `RBM.Cond272Reg.hA_phi` and `RBM.Cond272Reg.hA_betaStar` are the two side conditions the
  compiled Step 2 arithmetic actually consumes — `x^17 R^10 ≤ A` (`RBM.Step2.phi_arith`,
  `RBM.Step2MomentStep.phi_arith'`, the bottleneck `β* = 10` of (5.40)) and `x^32 R^11 ≤ A^2`
  (`RBM.Step2MomentStep.beta_star_margin`, the far field `β* = 5.5`) — produced from the bare
  (2.72) plus the regime bound, uniformly in `u ∈ [s, t]`.

The price is a factor two in the `δ`-budget: `RBM.Step2MomentStep.beta_star_margin` needs
`4δ ≤ 2c`, the bare route needs `4δ ≤ c`.

## Main results

* `RBM.rpow_mul_rpow_le_of_pow_thirty` — the arithmetic bridge.
* `RBM.Cond272Reg` — (2.72) verbatim, plus `N^c ≤ W ℓ_t η_t`.
* `RBM.Cond272'.toCond272Reg`, `RBM.Cond272Reg.toCond272` — `Cond272' → Cond272Reg → Cond272`.
* `RBM.Cond272Reg.margin`, `RBM.Cond272Reg.hA_phi`, `RBM.Cond272Reg.hA_betaStar`.
* `RBM.Thm221Reg` — Theorem 2.21 with `RBM.Cond272Reg` as its step hypothesis;
  `RBM.Thm221.toThm221Reg`, `RBM.Thm221Reg.toThm221'`, `RBM.Bounds_of_Thm221Reg`.
* `RBM.Band.eventually_exists_scale_eq_one`, `RBM.exists_cond272_not_rpow_le_scale` — the
  counterexample.
* `RBM.cond272Reg_zero` — satisfiability of `RBM.Cond272Reg`, independently of the grid.

See `docs/paper-deltas.md` (T186) and `docs/STATUS.md` (D1).
-/

namespace RBM

open MeasureTheory Filter

/-! ### 1. The arithmetic bridge

`R^30 ≤ A` and `N^c ≤ A` give `N^e R^b ≤ A^a` whenever `e/c + b/30 ≤ a`.  For `b < 30 a` this
leaves a genuine gain `N^e` with `e = c (a - b/30) > 0`, which is all any consumer of `hregS`
uses the `N^c` for. -/

section Arith

/-- **The bridge**: from `R^30 ≤ A` (the bare (2.72)) and `N^c ≤ A` (the regime bound),
`N^e R^b ≤ A^a` as soon as `e/c + b/30 ≤ a`.

`R^b ≤ (R^30)^{b/30} ≤ A^{b/30}`, `N^e = (N^c)^{e/c} ≤ A^{e/c}`, and `A ≥ 1` lets the two
exponents be added. -/
theorem rpow_mul_rpow_le_of_pow_thirty {A R Nr c e b a : ℝ} (hN : 1 ≤ Nr) (hR : 1 ≤ R)
    (hc : 0 < c) (he : 0 ≤ e) (hb : 0 ≤ b) (h30 : R ^ (30 : ℕ) ≤ A) (hreg : Nr ^ c ≤ A)
    (hsum : e / c + b / 30 ≤ a) :
    Nr ^ e * R ^ b ≤ A ^ a := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hA1 : (1 : ℝ) ≤ A := (Real.one_le_rpow hN hc.le).trans hreg
  have hA0 : (0 : ℝ) < A := by linarith
  -- `R ^ b ≤ A ^ (b / 30)`
  have hRb : R ^ b ≤ A ^ (b / 30) := by
    have hpow : R ^ b = (R ^ (30 : ℕ)) ^ (b / 30) := by
      rw [← Real.rpow_natCast R 30, ← Real.rpow_mul hR0.le]
      congr 1
      push_cast
      ring
    rw [hpow]
    exact Real.rpow_le_rpow (by positivity) h30 (by positivity)
  -- `Nr ^ e ≤ A ^ (e / c)`
  have hNe : Nr ^ e ≤ A ^ (e / c) := by
    have hN0 : (0 : ℝ) < Nr := by linarith
    have hpow : Nr ^ e = (Nr ^ c) ^ (e / c) := by
      rw [← Real.rpow_mul hN0.le]
      congr 1
      field_simp
    rw [hpow]
    exact Real.rpow_le_rpow (by positivity) hreg (by positivity)
  calc Nr ^ e * R ^ b ≤ A ^ (e / c) * A ^ (b / 30) :=
        mul_le_mul hNe hRb (by positivity) (by positivity)
    _ = A ^ (e / c + b / 30) := (Real.rpow_add hA0 _ _).symm
    _ ≤ A ^ a := Real.rpow_le_rpow_of_exponent_le hA1 hsum

end Arith

/-! ### 2. (2.72) as printed, plus the regime bound -/

section Cond

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **(2.72) exactly as printed, together with the regime bound `N^c ≤ W ℓ_t η_t`.**

The first component is `RBM.Cond272`, verbatim the paper's (2.72).  The second is the
hypothesis `hreg` that `RBM.eventually_scale_facts` and `RBM.weakLaw_highProb` already take
(Step 1, p. 52); on the grid of p. 24 it is free, because there `η_s/η_t = W^{τ'}` is itself a
positive power of `W` and (2.72) then forces `W ℓ_t η_t ≥ W^{30τ'}`.

This is strictly weaker than `RBM.Cond272'` (`RBM.Cond272'.toCond272Reg`) and strictly stronger
than `RBM.Cond272` (`RBM.Cond272Reg.toCond272`; the converse fails,
`RBM.exists_cond272_not_rpow_le_scale`). -/
def Cond272Reg (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (c : ℝ) : Prop :=
  Cond272 B E s t ∧ ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)

theorem Cond272Reg.toCond272 {c : ℝ} (h : Cond272Reg B E s t c) : Cond272 B E s t := h.1

/-- The gained (2.72) gives (2.72) plus the regime bound: `(η_s/η_t)^30 ≥ 1` is thrown away. -/
theorem Cond272'.toCond272Reg (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c) (h : Cond272' B E s t c) : Cond272Reg B E s t c := by
  refine ⟨h.toCond272 hE hst ht1 hc0, ?_⟩
  filter_upwards [h] with N hN
  rw [etaT_div_etaT hE] at hN
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith [hst N]
  have hR1 : (1 : ℝ) ≤ (1 - s N) / (1 - t N) := by
    rw [le_div_iff₀ h1t]; linarith [hst N]
  have hRp : (1 : ℝ) ≤ ((1 - s N) / (1 - t N)) ^ 30 := one_le_pow₀ hR1
  nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) c]

end Cond

/-! ### 3. What the bare (2.72) plus the regime bound buys -/

section Margin

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **`(η_s/η_u)^30 ≤ W ℓ_u η_u` for every `u ∈ [s, t]`**, from the bare (2.72) at `t`: the
ratio `η_s/η_u` only grows with `u` while `W ℓ_u η_u` only shrinks
(`RBM.flowScale_antitoneOn`). -/
theorem Cond272.pow_thirty_le (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (h : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u := by
  filter_upwards [h] with N hN u
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 0 < 1 - s N := by linarith [hst N, ht1 N]
  have hAt : 0 < B.scale E N (t N) :=
    B.scale_eq_flowScale E N (t N) ▸ flowScale_pos hW hL hE (ht1 N)
  -- (2.72), inverted
  have hAt' : ((1 - s N) / (1 - t N)) ^ 30 ≤ B.scale E N (t N) := by
    have hinv := inv_anti₀ (inv_pos.2 hAt) hN
    rw [inv_inv] at hinv
    have heq : ((1 - s N) / (1 - t N)) ^ 30 = (((1 - t N) / (1 - s N)) ^ 30)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [heq]; exact hinv
  -- the scale is antitone, the ratio is monotone
  have hanti : B.scale E N (t N) ≤ B.scale E N u := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW.le (B.L N) E (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have hratio : etaT E (s N) / etaT E u ≤ (1 - s N) / (1 - t N) := by
    rw [etaT_div_etaT hE]
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [u.2.2])
  have hr0 : (0 : ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [etaT_div_etaT hE]; positivity
  calc (etaT E (s N) / etaT E u) ^ 30 ≤ ((1 - s N) / (1 - t N)) ^ 30 :=
        pow_le_pow_left₀ hr0 hratio 30
    _ ≤ B.scale E N (t N) := hAt'
    _ ≤ B.scale E N u := hanti

/-- **The gained (2.72) at every exponent `b` with `e/c + b/30 ≤ a`**, uniformly in
`u ∈ [s, t]`, from the bare (2.72) plus the regime bound.

For `b < 30 a` one may take `e = c (a - b/30) > 0`: every row of T174's table whose `β*` is
strictly below 30 keeps a genuine polynomial gain, and only the rows *at* 30 need
`RBM.Cond272'`. -/
theorem Cond272Reg.margin (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hc : 0 < c) (h : Cond272Reg B E s t c) {e b a : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b)
    (hsum : e / c + b / 30 ≤ a) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (N : ℝ) ^ e * (etaT E (s N) / etaT E u) ^ b ≤ B.scale E N u ^ a := by
  filter_upwards [h.1.pow_thirty_le hE hst ht1, h.2, eventually_ge_atTop 1] with N h30 hreg hN1 u
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hL := B.one_le_L N
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 0 < 1 - s N := by linarith [u.2.1]
  have hR1 : (1 : ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [etaT_div_etaT hE, le_div_iff₀ h1u]; linarith [u.2.1]
  have hanti : B.scale E N (t N) ≤ B.scale E N u := by
    rw [B.scale_eq_flowScale, B.scale_eq_flowScale]
    exact flowScale_antitoneOn hW.le (B.L N) E (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) u.2.2
  exact rpow_mul_rpow_le_of_pow_thirty hN1' hR1 hc he hb (h30 u) (hreg.trans hanti) hsum

/-- **The bottleneck side condition of Step 2, from the bare (2.72)**: `x^17 R^10 ≤ A_u` with
`x = N^{δ/8}` — the hypothesis `hA` of `RBM.Step2.phi_arith` and
`RBM.Step2MomentStep.phi_arith'`, i.e. the `β* = 10` row of (5.40), which T132c's table makes
the bottleneck.

`(17δ/8)/c + 10/30 ≤ 1` needs `δ ≤ 16c/51`, and `4δ ≤ c` is enough. -/
theorem Cond272Reg.hA_phi (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hc : 0 < c) (h : Cond272Reg B E s t c) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ c) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      ((N : ℝ) ^ (δ / 8)) ^ 17 * (etaT E (s N) / etaT E u) ^ 10 ≤ B.scale E N u := by
  have hsum : 17 * δ / 8 / c + (10 : ℝ) / 30 ≤ 1 := by
    have hcc : 17 * δ / 8 / c ≤ 17 / 32 := by
      rw [div_le_iff₀ hc]; linarith
    linarith
  filter_upwards [h.margin hE hst ht1 hc (by positivity : (0 : ℝ) ≤ 17 * δ / 8)
    (by norm_num : (0 : ℝ) ≤ 10) hsum, eventually_ge_atTop 1] with N hN hN1 u
  have hN0 : (0 : ℝ) < N := by
    have : (1 : ℕ) ≤ N := hN1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hx : ((N : ℝ) ^ (δ / 8)) ^ 17 = (N : ℝ) ^ (17 * δ / 8) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (δ / 8)) 17, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  have hr : (etaT E (s N) / etaT E u) ^ (10 : ℕ) = (etaT E (s N) / etaT E u) ^ (10 : ℝ) := by
    rw [← Real.rpow_natCast (etaT E (s N) / etaT E u) 10]
    norm_num
  rw [hx, hr]
  simpa using hN u

/-- **The far-field side conditions of Step 2, from the bare (2.72)**: `x^32 R^11 ≤ A_u^2`,
verbatim the conclusion of `RBM.Step2MomentStep.beta_star_margin` (`β* = 5.5`), from which
`RBM.Step2MomentStep.hbeta_of_reg` and `RBM.Step2MomentStep.hgamma_of_reg` follow.

`4δ/c + 11/30 ≤ 2` needs `δ ≤ 49c/120`; `4δ ≤ c` is enough.  The gained route
(`RBM.Step2MomentStep.beta_star_margin`) asks only `4δ ≤ 2c`, so the bare route costs a factor
two in the `δ`-budget. -/
theorem Cond272Reg.hA_betaStar (hE : |E| < 2) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc : 0 < c) (h : Cond272Reg B E s t c) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ c) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      ((N : ℝ) ^ (δ / 8)) ^ 32 * (etaT E (s N) / etaT E u) ^ 11 ≤ B.scale E N u ^ 2 := by
  have hsum : 4 * δ / c + (11 : ℝ) / 30 ≤ 2 := by
    have hcc : 4 * δ / c ≤ 1 := by rw [div_le_one hc]; linarith
    linarith
  filter_upwards [h.margin hE hst ht1 hc (by positivity : (0 : ℝ) ≤ 4 * δ)
    (by norm_num : (0 : ℝ) ≤ 11) hsum, eventually_ge_atTop 1] with N hN hN1 u
  have hN0 : (0 : ℝ) < N := by
    have : (1 : ℕ) ≤ N := hN1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hx : ((N : ℝ) ^ (δ / 8)) ^ 32 = (N : ℝ) ^ (4 * δ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (δ / 8)) 32, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  have hr : (etaT E (s N) / etaT E u) ^ (11 : ℕ) = (etaT E (s N) / etaT E u) ^ (11 : ℝ) := by
    rw [← Real.rpow_natCast (etaT E (s N) / etaT E u) 11]
    norm_num
  have hA : B.scale E N u ^ (2 : ℕ) = B.scale E N u ^ (2 : ℝ) := by
    rw [← Real.rpow_natCast (B.scale E N u) 2]
    norm_num
  rw [hx, hr, hA]
  exact hN u

end Margin

/-! ### 4. Theorem 2.21 with the bare (2.72) plus the regime bound -/

section Thm

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **Theorem 2.21 with (2.72) exactly as printed**, plus the regime bound `N^c ≤ W ℓ_t η_t`
that Step 1 already carries (`RBM.Cond272Reg`).

This is the strongest form of Theorem 2.21 the six steps of §2.7 can reach: `RBM.Thm221` itself
is out of reach, because the bare (2.72) alone leaves `W ℓ_t η_t` as small as `1`
(`RBM.exists_cond272_not_rpow_le_scale`), and every consumer of `hregS` needs a positive power
of `N` to absorb the `N^δ` of `≺`.

The `c` is quantified inside the field, as in `RBM.Thm221'`: the grid of p. 24 caps the gain it
supplies at roughly `τ/16` (T179), so a producer must handle every small `c > 0`. -/
structure Thm221Reg (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
    (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272Reg B E s t c → Bounds X E s → Bounds X E t

/-- The paper's Theorem 2.21 implies the regime form. -/
theorem Thm221.toThm221Reg {κ : ℝ} (hT : Thm221 X κ) : Thm221Reg X κ where
  step E hE _ _ s t hs0 hst ht1 hcond hB := hT.step E hE s t hs0 hst ht1 hcond.1 hB

/-- The regime form implies the gained form of T179, so everything already proved from
`RBM.Thm221'` (`Flow/Thm221Gain.lean`) holds from `RBM.Thm221Reg`. -/
theorem Thm221Reg.toThm221' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221Reg X κ) : Thm221' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    hT.step E hE c hc0 s t hs0 hst ht1
      (hcond.toCond272Reg (by linarith [abs_nonneg E]) hst ht1 hc0.le) hB

/-- **Lemmas 2.18–2.20 from `RBM.Thm221Reg`**: verbatim `RBM.Bounds_of_Thm221`, with
`RBM.Thm221Reg` in place of `RBM.Thm221`.  The grid of p. 24 supplies the regime bound by
itself. -/
theorem Bounds_of_Thm221Reg {κ : ℝ} (hκ : 0 < κ) (hT : Thm221Reg X κ) (hE : |E| ≤ 2 - κ) {τ : ℝ}
    (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : Bounds X E t :=
  Bounds_of_Thm221' X hκ (hT.toThm221' hκ) hE hτ ht0 ht

/-- `Bounds_of_Thm221Reg` really is `Bounds_of_Thm221` with the hypothesis moved: `Eq` forces
the two conclusions to be the same statement (T107's technique). -/
example {κ : ℝ} (hκ : 0 < κ) (hT : Thm221 X κ) (hE : |E| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ)
    {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) :
    Bounds_of_Thm221 X hκ hT hE hτ ht0 ht =
      Bounds_of_Thm221Reg hκ hT.toThm221Reg hE hτ ht0 ht := rfl

end Thm

/-! ### 5. The bare (2.72) does **not** supply the regime bound

`RBM.Cond272 B E s t` at `s = t` says exactly `1 ≤ W ℓ_t η_t`, and the value `1` is attained. -/

section Counterexample

variable {Ω : Type*} [MeasurableSpace Ω] {E : ℝ}

/-- **`W ℓ_τ η_τ = 1` is attained.**

By `RBM.flowScale_eq` the scale is `W (Im m) min(√(1-τ), L(1-τ))`.  If `L ≤ W Im m`, take
`1 - τ = (W L Im m)⁻¹`, where the minimum is the second entry; otherwise take
`1 - τ = (W Im m)^{-2}`, where it is the first. -/
theorem flowScale_one_sub (W : ℝ) (L : ℕ) (E : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    flowScale W L E (1 - y) = W * (mE E).im * min (Real.sqrt y) ((L : ℝ) * y) := by
  rw [flowScale_eq W L E (by linarith : (1 : ℝ) - y ≤ 1), sub_sub_cancel]

theorem exists_flowScale_eq_one {W : ℝ} (hW : 0 < W) {L : ℕ} (hL : 3 ≤ L) (hE : |E| < 2)
    (hWm : 1 ≤ W * (mE E).im) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ flowScale W L E τ = 1 := by
  have hm := mE_im_pos hE
  have hL3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  by_cases hcase : (L : ℝ) ≤ W * (mE E).im
  · -- `1 - τ = (W L Im m)⁻¹`; the minimum is `L (1 - τ)`
    have hwlm0 : (0 : ℝ) < W * (L : ℝ) * (mE E).im := by positivity
    have hwlm : (1 : ℝ) ≤ W * (L : ℝ) * (mE E).im := by nlinarith
    have hy0 : (0 : ℝ) < (W * (L : ℝ) * (mE E).im)⁻¹ := by positivity
    have hprod : (W * (L : ℝ) * (mE E).im)⁻¹ * (W * (L : ℝ) * (mE E).im) = 1 :=
      inv_mul_cancel₀ hwlm0.ne'
    have hy1 : (W * (L : ℝ) * (mE E).im)⁻¹ ≤ 1 := by nlinarith
    refine ⟨1 - (W * (L : ℝ) * (mE E).im)⁻¹, by linarith, by linarith, ?_⟩
    rw [flowScale_one_sub W L E hy0.le]
    have hsq : ((L : ℝ) * (W * (L : ℝ) * (mE E).im)⁻¹) ^ 2 ≤
        (W * (L : ℝ) * (mE E).im)⁻¹ := by
      have hLy : (L : ℝ) * (W * (L : ℝ) * (mE E).im)⁻¹ * (L : ℝ) ≤ 1 := by
        have : (L : ℝ) * (L : ℝ) ≤ W * (L : ℝ) * (mE E).im := by nlinarith
        nlinarith
      nlinarith
    have hmin : min (Real.sqrt ((W * (L : ℝ) * (mE E).im)⁻¹))
        ((L : ℝ) * (W * (L : ℝ) * (mE E).im)⁻¹)
        = (L : ℝ) * (W * (L : ℝ) * (mE E).im)⁻¹ := by
      refine min_eq_right ?_
      calc (L : ℝ) * (W * (L : ℝ) * (mE E).im)⁻¹
          = Real.sqrt (((L : ℝ) * (W * (L : ℝ) * (mE E).im)⁻¹) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt ((W * (L : ℝ) * (mE E).im)⁻¹) := Real.sqrt_le_sqrt hsq
    rw [hmin]
    field_simp
  · -- `1 - τ = (W Im m)^{-2}`; the minimum is `√(1 - τ)`
    have hcase' : W * (mE E).im ≤ (L : ℝ) := le_of_not_ge hcase
    have hwm0 : (0 : ℝ) < W * (mE E).im := by positivity
    have hv0 : (0 : ℝ) < (W * (mE E).im)⁻¹ := by positivity
    have hvv : (W * (mE E).im)⁻¹ * (W * (mE E).im) = 1 := inv_mul_cancel₀ hwm0.ne'
    have hv1 : (W * (mE E).im)⁻¹ ≤ 1 := by nlinarith
    have hy1 : ((W * (mE E).im)⁻¹) ^ 2 ≤ 1 := by nlinarith
    have hsqrt : Real.sqrt (((W * (mE E).im)⁻¹) ^ 2) = (W * (mE E).im)⁻¹ :=
      Real.sqrt_sq hv0.le
    refine ⟨1 - ((W * (mE E).im)⁻¹) ^ 2, by linarith, by nlinarith, ?_⟩
    rw [flowScale_one_sub W L E (by positivity : (0:ℝ) ≤ ((W * (mE E).im)⁻¹) ^ 2), hsqrt]
    have hmin : min ((W * (mE E).im)⁻¹) ((L : ℝ) * ((W * (mE E).im)⁻¹) ^ 2)
        = (W * (mE E).im)⁻¹ := by
      refine min_eq_left ?_
      nlinarith
    rw [hmin]
    field_simp

/-- **`W ℓ_τ η_τ = 1` is attained for every large `N`**: the only input is `1 ≤ W Im m`, which
(2.2) gives. -/
theorem Band.eventually_exists_scale_eq_one (B : Band Ω) (hE : |E| < 2) :
    ∀ᶠ N : ℕ in atTop, ∃ τ : ℝ, 0 ≤ τ ∧ τ < 1 ∧ B.scale E N τ = 1 := by
  have hm := mE_im_pos hE
  have hWm : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (B.W N : ℝ) * (mE E).im := by
    filter_upwards [B.bandwidth, eventually_le_rpow ((mE E).im)⁻¹
      (show (0 : ℝ) < 1 / 2 + B.c by linarith [B.c_pos])] with N hW hC
    have h1 : ((mE E).im)⁻¹ ≤ (B.W N : ℝ) := hC.trans hW
    have h2 := mul_le_mul_of_nonneg_right h1 hm.le
    rwa [inv_mul_cancel₀ hm.ne'] at h2
  filter_upwards [hWm] with N hWm
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  obtain ⟨τ, hτ0, hτ1, hτ⟩ := exists_flowScale_eq_one hW (B.three_le_L N) hE hWm
  exact ⟨τ, hτ0, hτ1, by rw [B.scale_eq_flowScale]; exact hτ⟩

/-- **The bare (2.72) does not supply the regime bound.**  There is a time sequence satisfying
(2.72) verbatim — with `s = t`, where (2.72) reads exactly `1 ≤ W ℓ_t η_t` — along which
`W ℓ_t η_t = 1`, so `N^c ≤ W ℓ_t η_t` fails for every `c > 0`.

Consequence: `RBM.Thm221` cannot be reached by the route of §2.7, which absorbs the `N^δ` of
`≺` into a positive power of `W ℓ_u η_u` at every step.  `RBM.Thm221Reg` is the form that can
(`RBM.Cond272Reg.hA_phi`, `RBM.Cond272Reg.hA_betaStar`). -/
theorem exists_cond272_not_rpow_le_scale (B : Band Ω) (hE : |E| < 2) {c : ℝ} (hc : 0 < c) :
    ∃ t : ℕ → ℝ, (∀ N, 0 ≤ t N) ∧ (∀ N, t N < 1) ∧ Cond272 B E t t ∧
      ¬ ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N) := by
  classical
  have hgood := B.eventually_exists_scale_eq_one hE
  have hchoice : ∀ N : ℕ, ∃ x : ℝ, 0 ≤ x ∧ x < 1 ∧
      ((∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ B.scale E N y = 1) → B.scale E N x = 1) := by
    intro N
    by_cases h : ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ B.scale E N y = 1
    · exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, fun _ => h.choose_spec.2.2⟩
    · exact ⟨0, le_refl 0, by norm_num, fun h' => absurd h' h⟩
  choose t ht using hchoice
  refine ⟨t, fun N => (ht N).1, fun N => (ht N).2.1, ?_, ?_⟩
  · filter_upwards [hgood] with N hN
    have h1 : B.scale E N (t N) = 1 := (ht N).2.2 hN
    have h2 : (0 : ℝ) < 1 - t N := by linarith [(ht N).2.1]
    rw [h1, inv_one, div_self h2.ne', one_pow]
  · intro hcon
    obtain ⟨N, hN, hcN, hN1⟩ := (hgood.and (hcon.and (eventually_gt_atTop 1))).exists
    rw [(ht N).2.2 hN] at hcN
    have hN1' : (1 : ℝ) < N := by exact_mod_cast hN1
    have hgt : (1 : ℝ) < (N : ℝ) ^ c :=
      (Real.one_lt_rpow_iff_of_pos (by linarith)).2 (Or.inl ⟨hN1', hc⟩)
    linarith

end Counterexample

/-! ### 6. Satisfiability

`RBM.Cond272Reg` is not vacuous.  The grid of p. 24 supplies it through
`RBM.Band.eventually_flow_grid'` and `RBM.Cond272'.toCond272Reg`; independently of the grid,
here is a closed witness at `s = t = 0`, where `W ℓ_0 η_0 = W Im m^{(E)} ≥ N^{1/2 + c}`. -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω] {E : ℝ}

/-- `W ℓ_0 η_0 = W Im m^{(E)}`. -/
theorem Band.scale_zero (B : Band Ω) (E : ℝ) (N : ℕ) :
    B.scale E N 0 = (B.W N : ℝ) * (mE E).im := by
  have h : B.scale E N 0 = (B.W N : ℝ) * ellHat (B.L N) ((0 : ℝ) : ℂ) * etaT E 0 := rfl
  rw [h, Complex.ofReal_zero, ellHat_zero _ (B.three_le_L N), etaT]
  ring

/-- **`RBM.Cond272Reg` is satisfiable**, for every `0 < c ≤ 1/2`, at `s = t = 0`: (2.72) there
reads `1 ≤ W Im m^{(E)}` and the regime bound reads `N^c ≤ W Im m^{(E)}`, both of which (2.2)
gives. -/
theorem cond272Reg_zero (B : Band Ω) (hE : |E| < 2) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1 / 2) :
    Cond272Reg B E (fun _ => 0) (fun _ => 0) c := by
  have hm := mE_im_pos hE
  have key : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (B.W N : ℝ) * (mE E).im := by
    filter_upwards [B.bandwidth, eventually_le_rpow ((mE E).im)⁻¹ B.c_pos,
      eventually_ge_atTop 1] with N hW hC hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ B.c * (mE E).im := by
      have h := mul_le_mul_of_nonneg_right hC hm.le
      rwa [inv_mul_cancel₀ hm.ne'] at h
    have h3 : (N : ℝ) ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ B.c * (mE E).im) ≤ (B.W N : ℝ) * (mE E).im := by
      rw [← mul_assoc, ← Real.rpow_add hN0]
      exact mul_le_mul_of_nonneg_right hW hm.le
    calc (N : ℝ) ^ c ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1' hc
      _ = (N : ℝ) ^ ((1 : ℝ) / 2) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ B.c * (mE E).im) :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)
      _ ≤ (B.W N : ℝ) * (mE E).im := h3
  constructor
  · filter_upwards [key, eventually_ge_atTop 1] with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (B.W N : ℝ) * (mE E).im :=
      le_trans (Real.one_le_rpow hN1' hc0.le) hN
    have hinv := inv_anti₀ (show (0 : ℝ) < 1 by norm_num) h1
    rw [inv_one] at hinv
    have h2 : (B.scale E N 0)⁻¹ ≤ 1 := by rw [B.scale_zero E N]; exact hinv
    simpa using h2
  · filter_upwards [key] with N hN
    simpa [B.scale_zero E N] using hN

end Satisfiable

end RBM
