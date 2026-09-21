/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MinorDiffCond

/-!
# The smallness of the tower, from (4.1) alone

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the last hypothesis of the budgeted route from (4.1) to (4.5).

T177 rebuilt the whole chain `(4.12) → RBM.StepGlue.Eq45Flow` on the *budgeted* gain interfaces
`RBM.Gauss.FlucGainUpTo'` / `RBM.Gauss.MinorDiffGainUpTo'` and closed it with
`RBM.Gauss.eq45Flow_of_goodSetFlow_budget`, but left one numeric hypothesis standing:

```
hsmall : condEnv ^ n * P(badTower …) ≤ B₀ ^ n * (2Ψ) ^ (n M)
```

This file **derives it** from `RBM.HighProb (P d) (RBM.Gauss.goodSetFlow …)` — i.e. from (4.1)
itself — and nothing else probabilistic.

## The accounting

`RBM.Gauss.meas_badTower_le` costs one factor `(ε + #rows)/ε` per letter, so

```
P(badTower ε Bad₀ (M+1)) ≤ ((ε + #rows)/ε) ^ (M+1) · P(Ω(t,c)ᶜ).
```

Every factor in front of `P(Ω(t,c)ᶜ)` is polynomially bounded in `N` for a **fixed** pair of
budgets `M = n = 2p`, and every factor of the right-hand side is polynomially bounded *below*:

| factor | regime bound | source |
| --- | --- | --- |
| `#rows = #(Idx d N)` | `≤ N` | `RBM.Gauss.card_Idx_le` (from `Dims.dim`) |
| `condEnv E u M = 2^{2M+1}(η_u⁻¹+1)` | `≤ 2^{2M+1} N^{Kenv}` | `hEnv`, plus `η` antitone in `u` |
| `condEps E u M Ψ = Ψ(2Ψ)^M/((M+1)condEnv)` | `≥ N^{-C}` | the two above and `Ψ ≥ N^{-c}` |
| `B₀ = 2 minorDiffC(M) Ψ + Ψ` | `≥ Ψ ≥ N^{-c}` | `hδlo` |

`RBM.HighProb` quantifies over *every* `D`, so one choice of `D` beats the whole polynomial.
Since the regime bounds and `RBM.HighProb` are `∀ᶠ N` statements, the derived `hsmall` is one
too — which is why the budgeted chain of `RBM1D/Gauss/MinorDiffCond.lean` was weakened from
`∀ p N` to `∀ p, ∀ᶠ N` in its gain hypothesis (a strictly weaker hypothesis; the conclusions
are unchanged).

## The bookkeeping tool

`RBM.Gauss.PolyLo` / `RBM.Gauss.PolyHi` are the two one-line predicates "eventually at least
`C N^{-D}`" / "eventually at most `C N^{D}`", with the closure lemmas (product, power, inverse,
sum, monotonicity) that the table above needs, and
`RBM.Gauss.measureReal_compl_le_of_polyLo`, which is the only place `RBM.HighProb` is used:
a `RBM.HighProb` event's complement is eventually below **any** `RBM.Gauss.PolyLo` function.

These are general-purpose; if a second consumer appears they belong in `RBM1D/Defs/`.

## Main results

* `RBM.Gauss.hsmall_of_highProb` — the derivation, in the exact shape
  `RBM.Gauss.eq45Flow_of_goodSetFlow_budget` consumes.
* `RBM.Gauss.eq45Flow_of_goodSetFlow_highProb` — (4.1) to `RBM.StepGlue.Eq45Flow` with **no**
  `hsmall` in the hypothesis list.
* `RBM.Gauss.not_forall_mul_le_one` and `RBM.Gauss.eq45Flow_delta_hyps_consistent` — the
  two-directional satisfiability check.  The first is why `hMδ` and `hδC` were moved to
  `∀ p, ∀ᶠ N` as well: in the `∀ p N` shape T177 gave them they are **unsatisfiable** at a
  strictly positive `δ`, which made `RBM.Gauss.eq45Flow_of_goodSetFlow_budget` vacuous.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

/-! ### Polynomial envelopes -/

/-- `f` is eventually at least a fixed negative power of `N`. -/
def PolyLo (f : ℕ → ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ (-D) ≤ f N

/-- `f` is eventually at most a fixed power of `N`. -/
def PolyHi (f : ℕ → ℝ) : Prop :=
  ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ N : ℕ in atTop, f N ≤ C * (N : ℝ) ^ D

theorem polyLo_const {c : ℝ} (hc : 0 < c) : PolyLo (fun _ => c) :=
  ⟨c, hc, 0, Filter.Eventually.of_forall fun N => by rw [neg_zero, Real.rpow_zero, mul_one]⟩

theorem polyHi_const {c : ℝ} (hc : 0 < c) : PolyHi (fun _ => c) :=
  ⟨c, hc, 0, Filter.Eventually.of_forall fun N => by rw [Real.rpow_zero, mul_one]⟩

theorem PolyLo.mono {f g : ℕ → ℝ} (hf : PolyLo f) (h : ∀ᶠ N : ℕ in atTop, f N ≤ g N) :
    PolyLo g := by
  obtain ⟨C, hC, D, hD⟩ := hf
  exact ⟨C, hC, D, by filter_upwards [hD, h] with N h1 h2 using h1.trans h2⟩

theorem PolyHi.mono {f g : ℕ → ℝ} (hg : PolyHi g) (h : ∀ᶠ N : ℕ in atTop, f N ≤ g N) :
    PolyHi f := by
  obtain ⟨C, hC, D, hD⟩ := hg
  exact ⟨C, hC, D, by filter_upwards [hD, h] with N h1 h2 using h2.trans h1⟩

/-- A `RBM.Gauss.PolyLo` function is eventually positive. -/
theorem PolyLo.eventually_pos {f : ℕ → ℝ} (hf : PolyLo f) : ∀ᶠ N : ℕ in atTop, 0 < f N := by
  obtain ⟨C, hC, D, hD⟩ := hf
  filter_upwards [hD, eventually_ge_atTop 1] with N h1 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have : (0 : ℝ) < C * (N : ℝ) ^ (-D) := by positivity
  linarith

theorem PolyLo.mul {f g : ℕ → ℝ} (hf : PolyLo f) (hg : PolyLo g) :
    PolyLo (fun N => f N * g N) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C * C', by positivity, D + D', ?_⟩
  filter_upwards [hD, hD', eventually_ge_atTop 1] with N h1 h2 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hsplit : (N : ℝ) ^ (-(D + D')) = (N : ℝ) ^ (-D) * (N : ℝ) ^ (-D') := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h1' : (0 : ℝ) ≤ C * (N : ℝ) ^ (-D) := by positivity
  have h2' : (0 : ℝ) ≤ C' * (N : ℝ) ^ (-D') := by positivity
  calc C * C' * (N : ℝ) ^ (-(D + D'))
      = (C * (N : ℝ) ^ (-D)) * (C' * (N : ℝ) ^ (-D')) := by rw [hsplit]; ring
    _ ≤ f N * g N := mul_le_mul h1 h2 h2' (h1'.trans h1)

theorem PolyHi.mul {f g : ℕ → ℝ} (hf : PolyHi f) (hg : PolyHi g)
    (hf0 : ∀ᶠ N : ℕ in atTop, 0 ≤ f N) (hg0 : ∀ᶠ N : ℕ in atTop, 0 ≤ g N) :
    PolyHi (fun N => f N * g N) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C * C', by positivity, D + D', ?_⟩
  filter_upwards [hD, hD', hf0, hg0, eventually_ge_atTop 1] with N h1 h2 h3 h4 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hsplit : (N : ℝ) ^ (D + D') = (N : ℝ) ^ D * (N : ℝ) ^ D' := Real.rpow_add hN0 _ _
  calc f N * g N ≤ (C * (N : ℝ) ^ D) * (C' * (N : ℝ) ^ D') :=
        mul_le_mul h1 h2 h4 (h3.trans h1)
    _ = C * C' * (N : ℝ) ^ (D + D') := by rw [hsplit]; ring

theorem PolyHi.add {f g : ℕ → ℝ} (hf : PolyHi f) (hg : PolyHi g) :
    PolyHi (fun N => f N + g N) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  obtain ⟨C', hC', D', hD'⟩ := hg
  refine ⟨C + C', by positivity, max D D', ?_⟩
  filter_upwards [hD, hD', eventually_ge_atTop 1] with N h1 h2 hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hle : (N : ℝ) ^ D ≤ (N : ℝ) ^ (max D D') :=
    Real.rpow_le_rpow_of_exponent_le hN1' (le_max_left _ _)
  have hle' : (N : ℝ) ^ D' ≤ (N : ℝ) ^ (max D D') :=
    Real.rpow_le_rpow_of_exponent_le hN1' (le_max_right _ _)
  calc f N + g N ≤ C * (N : ℝ) ^ D + C' * (N : ℝ) ^ D' := by linarith
    _ ≤ C * (N : ℝ) ^ (max D D') + C' * (N : ℝ) ^ (max D D') := by
        have a1 : C * (N : ℝ) ^ D ≤ C * (N : ℝ) ^ (max D D') :=
          mul_le_mul_of_nonneg_left hle hC.le
        have a2 : C' * (N : ℝ) ^ D' ≤ C' * (N : ℝ) ^ (max D D') :=
          mul_le_mul_of_nonneg_left hle' hC'.le
        linarith
    _ = (C + C') * (N : ℝ) ^ (max D D') := by ring

theorem PolyLo.pow {f : ℕ → ℝ} (hf : PolyLo f) (k : ℕ) : PolyLo (fun N => f N ^ k) := by
  induction k with
  | zero => simpa using polyLo_const (c := (1 : ℝ)) one_pos
  | succ k ih =>
      have := ih.mul hf
      refine this.mono ?_
      exact Filter.Eventually.of_forall fun N => le_of_eq (by rw [pow_succ])

theorem PolyHi.pow {f : ℕ → ℝ} (hf : PolyHi f) (hf0 : ∀ᶠ N : ℕ in atTop, 0 ≤ f N) (k : ℕ) :
    PolyHi (fun N => f N ^ k) := by
  induction k with
  | zero => simpa using polyHi_const (c := (1 : ℝ)) one_pos
  | succ k ih =>
      have hpow0 : ∀ᶠ N : ℕ in atTop, 0 ≤ f N ^ k := by
        filter_upwards [hf0] with N h using pow_nonneg h k
      have := ih.mul hf hpow0 hf0
      refine this.mono ?_
      exact Filter.Eventually.of_forall fun N => le_of_eq (by rw [pow_succ])

/-- The reciprocal of a `RBM.Gauss.PolyHi` function is `RBM.Gauss.PolyLo`. -/
theorem PolyLo.inv {f : ℕ → ℝ} (hf : PolyHi f) (hf0 : ∀ᶠ N : ℕ in atTop, 0 < f N) :
    PolyLo (fun N => (f N)⁻¹) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  refine ⟨C⁻¹, by positivity, D, ?_⟩
  filter_upwards [hD, hf0, eventually_ge_atTop 1] with N h1 h2 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hrp : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 _
  have hCN : (0 : ℝ) < C * (N : ℝ) ^ D := by positivity
  have : (C * (N : ℝ) ^ D)⁻¹ ≤ (f N)⁻¹ := inv_anti₀ h2 h1
  refine le_trans (le_of_eq ?_) this
  rw [mul_inv, ← Real.rpow_neg hN0.le]

/-- The reciprocal of a `RBM.Gauss.PolyLo` function is `RBM.Gauss.PolyHi`. -/
theorem PolyHi.inv {f : ℕ → ℝ} (hf : PolyLo f) : PolyHi (fun N => (f N)⁻¹) := by
  obtain ⟨C, hC, D, hD⟩ := hf
  refine ⟨C⁻¹, by positivity, D, ?_⟩
  filter_upwards [hD, eventually_ge_atTop 1] with N h1 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hrp : (0 : ℝ) < (N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hCN : (0 : ℝ) < C * (N : ℝ) ^ (-D) := by positivity
  have : (f N)⁻¹ ≤ (C * (N : ℝ) ^ (-D))⁻¹ := inv_anti₀ hCN h1
  refine this.trans (le_of_eq ?_)
  rw [mul_inv, ← Real.rpow_neg hN0.le, neg_neg]

/-- A `RBM.Gauss.PolyLo` numerator over a `RBM.Gauss.PolyHi` denominator is
`RBM.Gauss.PolyLo`. -/
theorem PolyLo.div {f g : ℕ → ℝ} (hf : PolyLo f) (hg : PolyHi g)
    (hg0 : ∀ᶠ N : ℕ in atTop, 0 < g N) : PolyLo (fun N => f N / g N) := by
  have := hf.mul (PolyLo.inv hg hg0)
  refine this.mono (Filter.Eventually.of_forall fun N => ?_)
  rw [div_eq_mul_inv]

/-- The shape in which the net condition `1/N^a ≤ δ_N` of the flow hypotheses arrives. -/
theorem polyLo_of_one_div_rpow_le {δ : ℕ → ℝ} {a : ℝ}
    (h : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ a ≤ δ N) : PolyLo δ := by
  refine ⟨1, one_pos, a, ?_⟩
  filter_upwards [h, eventually_ge_atTop 1] with N h1 hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  rw [one_mul, Real.rpow_neg hN0.le, ← one_div]
  exact h1

/-- The shape in which the envelope condition `(η⁻¹+1)^2 ≤ N^{Kenv}` arrives: for a function
bounded below by `1`, a polynomial bound on the square is a polynomial bound. -/
theorem polyHi_of_sq_le {f : ℕ → ℝ} {Kenv : ℝ} (hf1 : ∀ᶠ N : ℕ in atTop, 1 ≤ f N)
    (h : ∀ᶠ N : ℕ in atTop, f N ^ 2 ≤ (N : ℝ) ^ Kenv) : PolyHi f := by
  refine ⟨1, one_pos, Kenv, ?_⟩
  filter_upwards [hf1, h] with N h1 h2
  rw [one_mul]
  nlinarith

/-! ### The only use of `RBM.HighProb` -/

variable {d : Dims}

/-- **A high-probability event's complement is eventually below any `RBM.Gauss.PolyLo`
function.**  This is where the `∀ D` quantifier of `RBM.HighProb` is spent: one `D` beats the
whole polynomial, and the conversion `ℝ≥0∞ → ℝ` is free because `RBM.Gauss.P` is a probability
measure. -/
theorem measureReal_compl_le_of_polyLo {Ξ : ℕ → Set (Ω d)} (hΩ : HighProb (P d) Ξ)
    {f : ℕ → ℝ} (hf : PolyLo f) :
    ∀ᶠ N : ℕ in atTop, (P d).real (Ξ N)ᶜ ≤ f N := by
  obtain ⟨C, hC, D, hD⟩ := hf
  have hD'pos : (0 : ℝ) < max (D + 1) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [hΩ (max (D + 1) 1) hD'pos, hD, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈C⁻¹⌉₊] with N h1 h2 hN1 hNC
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  set D' : ℝ := max (D + 1) 1 with hD'
  -- the measure bound, transported to `ℝ`
  have hstep1 : (P d).real (Ξ N)ᶜ ≤ (N : ℝ) ^ (-D') := by
    rw [measureReal_def]
    calc ((P d) (Ξ N)ᶜ).toReal ≤ (ENNReal.ofReal ((N : ℝ) ^ (-D'))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      _ = (N : ℝ) ^ (-D') := ENNReal.toReal_ofReal (Real.rpow_nonneg hN0.le _)
  -- and the arithmetic `N^{-D'} ≤ C N^{-D}`
  have hCN : (N : ℝ)⁻¹ ≤ C := by
    have : C⁻¹ ≤ (N : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hNC)
    exact (inv_le_comm₀ hC hN0).1 this
  have hDD : (1 : ℝ) ≤ D' - D := by
    have : D + 1 ≤ D' := le_max_left _ _
    linarith
  have hsmallexp : (N : ℝ) ^ (-(D' - D)) ≤ C := by
    calc (N : ℝ) ^ (-(D' - D)) ≤ (N : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      _ = (N : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ C := hCN
  have hstep2 : (N : ℝ) ^ (-D') ≤ C * (N : ℝ) ^ (-D) := by
    have hsplit : (N : ℝ) ^ (-D') = (N : ℝ) ^ (-D) * (N : ℝ) ^ (-(D' - D)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    rw [hsplit]
    have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
    calc (N : ℝ) ^ (-D) * (N : ℝ) ^ (-(D' - D)) ≤ (N : ℝ) ^ (-D) * C :=
          mul_le_mul_of_nonneg_left hsmallexp hnn
      _ = C * (N : ℝ) ^ (-D) := by ring
  exact hstep1.trans (hstep2.trans h2)

/-! ### `hsmall`, derived -/

section Small

variable {E : ℝ} {s t δ : ℕ → ℝ}

/-- **The tower is small enough, at any fixed budget.**

The exceptional set charged by the conditionalization is
`RBM.Gauss.badTower … (M+1)` over the measurable hull of the complement of (4.1).  Its measure
costs one factor `(ε + #rows)/ε` per letter (`RBM.Gauss.meas_badTower_le`); at a **fixed**
budget `M` that whole price, together with the envelope `RBM.Gauss.condEnv ^ M`, is a fixed
power of `N`, while the target `B₀^M (2Ψ)^{M²}` is a fixed *negative* power of `N`.  Since (4.1)
holds with high probability — `P(Ω(t,c)ᶜ) ≤ N^{-D}` for **every** `D` — one choice of `D` beats
both, and the bound holds eventually in `N`.

The two regime bounds are exactly the two `RBM.Gauss.PolyLo`/`RBM.Gauss.PolyHi` hypotheses:
`δ_N` is not super-polynomially small (in the flow hypotheses this is the net condition
`1/N^{2K+6} ≤ δ_N`, see `RBM.Gauss.polyLo_of_one_div_rpow_le`), and `η_{t_N}⁻¹` is
polynomially bounded (this is `hEnv`, see `RBM.Gauss.polyHi_of_sq_le`).  `η` is antitone in the
time (`RBM.Gauss.etaT_le_of_le`), which is what makes the bound uniform over `u ∈ [s_N, t_N]`.

At `M = 0` there is nothing special: the envelope power is `1`, the target is `1`, and the
bound is `P ≤ 1`; the general argument covers it. -/
theorem hsmall_of_highProb_aux (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hδpos : ∀ N, 0 < δ N) (hδlo : PolyLo δ)
    (hηhi : PolyHi fun N => (etaT E (t N))⁻¹ + 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      condEnv E u M ^ M
          * (P d).real (badTower d N (condEps E u M (2 * δ N)) (badBase d E s t δ N) (M + 1))
        ≤ (2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M) := by
  classical
  have hΨpos : ∀ N, (0 : ℝ) < 2 * δ N := fun N => by linarith [hδpos N]
  have hηt : ∀ N, 0 < etaT E (t N) := fun N => etaT_pos_of_lt_one' hE (ht1 N)
  have hEnvt0 : ∀ N, (0 : ℝ) < condEnv E (t N) M := fun N =>
    lt_of_lt_of_le zero_lt_one (one_le_condEnv hE (ht1 N) M)
  have hMEnv0 : ∀ N, (0 : ℝ) < ((M : ℝ) + 1) * condEnv E (t N) M := fun N => by
    have := hEnvt0 N; positivity
  have heT0 : ∀ N, (0 : ℝ) < condEps E (t N) M (2 * δ N) := by
    intro N
    change (0 : ℝ) < (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv E (t N) M)⁻¹
    have h1 := hΨpos N
    have h3 : (0 : ℝ) < (2 * (2 * δ N)) ^ M := by positivity
    exact mul_pos (mul_pos h1 h3) (inv_pos.2 (hMEnv0 N))
  have hR0 : ∀ N, (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := fun N => Nat.cast_nonneg _
  have hq0 : ∀ N, (0 : ℝ) < (condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
      / condEps E (t N) M (2 * δ N) := fun N =>
    div_pos (add_pos_of_pos_of_nonneg (heT0 N) (hR0 N)) (heT0 N)
  have hG0 : ∀ N, (0 : ℝ) < condEnv E (t N) M ^ M
      * ((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
          / condEps E (t N) M (2 * δ N)) ^ (M + 1) := fun N =>
    mul_pos (pow_pos (hEnvt0 N) M) (pow_pos (hq0 N) (M + 1))
  -- the target is bounded below by a fixed negative power of `N`
  have hΨlo : PolyLo fun N => 2 * δ N :=
    hδlo.mono (Filter.Eventually.of_forall fun N => by linarith [(hδpos N).le])
  have hB0lo : PolyLo fun N => 2 * minorDiffC M * (2 * δ N) + 2 * δ N :=
    hΨlo.mono (Filter.Eventually.of_forall fun N => by
      have h1 := minorDiffC_nonneg M
      have h2 := (hδpos N).le
      nlinarith)
  have h2Ψlo : PolyLo fun N => 2 * (2 * δ N) :=
    hΨlo.mono (Filter.Eventually.of_forall fun N => by linarith [(hδpos N).le])
  have hSlo : PolyLo fun N =>
      (2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M) :=
    (hB0lo.pow M).mul (h2Ψlo.pow (M * M))
  -- the price is bounded above by a fixed power of `N`
  have hEnvthi : PolyHi fun N => condEnv E (t N) M := by
    have hc : PolyHi fun _ : ℕ => (2 : ℝ) ^ (2 * M + 1) := polyHi_const (by positivity)
    have hnn : ∀ᶠ N : ℕ in atTop, (0 : ℝ) ≤ (etaT E (t N))⁻¹ + 1 :=
      Filter.Eventually.of_forall fun N => by
        have : (0 : ℝ) ≤ (etaT E (t N))⁻¹ := inv_nonneg.2 (hηt N).le
        linarith
    have h := hc.mul hηhi (Filter.Eventually.of_forall fun _ => by positivity) hnn
    exact h.mono (Filter.Eventually.of_forall fun N => le_of_eq rfl)
  have hMEnvhi : PolyHi fun N => ((M : ℝ) + 1) * condEnv E (t N) M :=
    (polyHi_const (c := (M : ℝ) + 1) (by positivity)).mul hEnvthi
      (Filter.Eventually.of_forall fun _ => by positivity)
      (Filter.Eventually.of_forall fun N => (hEnvt0 N).le)
  have heTlo : PolyLo fun N => condEps E (t N) M (2 * δ N) := by
    have h := (hΨlo.mul (h2Ψlo.pow M)).mul
      (PolyLo.inv hMEnvhi (Filter.Eventually.of_forall hMEnv0))
    exact h.mono (Filter.Eventually.of_forall fun N => le_of_eq rfl)
  have hRhi : PolyHi fun N => (Fintype.card (d.Idx N) : ℝ) := by
    refine ⟨1, one_pos, 1, ?_⟩
    filter_upwards [card_Idx_le d] with N h
    rw [one_mul]; exact h
  have hquothi : PolyHi fun N =>
      (condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
        / condEps E (t N) M (2 * δ N) := by
    have hprod : PolyHi fun N =>
        (Fintype.card (d.Idx N) : ℝ) * (condEps E (t N) M (2 * δ N))⁻¹ :=
      hRhi.mul (PolyHi.inv heTlo) (Filter.Eventually.of_forall hR0)
        (Filter.Eventually.of_forall fun N => (inv_pos.2 (heT0 N)).le)
    refine ((polyHi_const (c := (1 : ℝ)) one_pos).add hprod).mono
      (Filter.Eventually.of_forall fun N => le_of_eq ?_)
    rw [add_div, div_self (heT0 N).ne', div_eq_mul_inv]
  have hGhi : PolyHi fun N => condEnv E (t N) M ^ M
      * ((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
          / condEps E (t N) M (2 * δ N)) ^ (M + 1) :=
    (hEnvthi.pow (Filter.Eventually.of_forall fun N => (hEnvt0 N).le) M).mul
      (hquothi.pow (Filter.Eventually.of_forall fun N => (hq0 N).le) (M + 1))
      (Filter.Eventually.of_forall fun N => pow_nonneg (hEnvt0 N).le M)
      (Filter.Eventually.of_forall fun N => pow_nonneg (hq0 N).le (M + 1))
  -- and (4.1) beats the quotient
  have hkey := measureReal_compl_le_of_polyLo hΩ
    (hSlo.div hGhi (Filter.Eventually.of_forall hG0))
  filter_upwards [hkey] with N hN u hu
  -- uniformity in `u`: `η` is antitone, hence `condEnv` is monotone and `condEps` antitone
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hEnvu0 : (0 : ℝ) < condEnv E u M :=
    lt_of_lt_of_le zero_lt_one (one_le_condEnv hE hu1 M)
  have hEnvle : condEnv E u M ≤ condEnv E (t N) M := by
    have hinv : (etaT E u)⁻¹ ≤ (etaT E (t N))⁻¹ := inv_anti₀ (hηt N) (etaT_le_of_le hE hu.2)
    change (2 : ℝ) ^ (2 * M + 1) * ((etaT E u)⁻¹ + 1)
      ≤ (2 : ℝ) ^ (2 * M + 1) * ((etaT E (t N))⁻¹ + 1)
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * M + 1) := by positivity
    nlinarith
  have hMEnvu0 : (0 : ℝ) < ((M : ℝ) + 1) * condEnv E u M := by positivity
  have heu0 : (0 : ℝ) < condEps E u M (2 * δ N) := by
    change (0 : ℝ) < (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv E u M)⁻¹
    have h1 := hΨpos N
    have h3 : (0 : ℝ) < (2 * (2 * δ N)) ^ M := by positivity
    exact mul_pos (mul_pos (hΨpos N) h3) (inv_pos.2 hMEnvu0)
  have hege : condEps E (t N) M (2 * δ N) ≤ condEps E u M (2 * δ N) := by
    change (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv E (t N) M)⁻¹
      ≤ (2 * δ N) * (2 * (2 * δ N)) ^ M * (((M : ℝ) + 1) * condEnv E u M)⁻¹
    have hmono : (((M : ℝ) + 1) * condEnv E (t N) M)⁻¹
        ≤ (((M : ℝ) + 1) * condEnv E u M)⁻¹ :=
      inv_anti₀ hMEnvu0 (by nlinarith [hEnvle, (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))])
    have h1 := hΨpos N
    have hnn : (0 : ℝ) ≤ (2 * δ N) * (2 * (2 * δ N)) ^ M := by positivity
    exact mul_le_mul_of_nonneg_left hmono hnn
  -- the tower's measure
  have hε0 : (0 : ℝ) ≤ condEps E u M (2 * δ N) := heu0.le
  have htow := meas_badTower_le d N (ε := condEps E u M (2 * δ N))
    (measurableSet_badBase d E s t δ N) (M + 1)
  have hfin : ((ENNReal.ofReal (condEps E u M (2 * δ N))
      + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ (M + 1) * (P d) (badBase d E s t δ N)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.natCast_ne_top _⟩)) (measure_ne_top _ _)
  have hL : (ENNReal.ofReal (condEps E u M (2 * δ N)) ^ (M + 1)
        * (P d) (badTower d N (condEps E u M (2 * δ N)) (badBase d E s t δ N) (M + 1))).toReal
      = condEps E u M (2 * δ N) ^ (M + 1)
        * (P d).real (badTower d N (condEps E u M (2 * δ N))
            (badBase d E s t δ N) (M + 1)) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε0, measureReal_def]
  have hRr : ((ENNReal.ofReal (condEps E u M (2 * δ N))
        + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ (M + 1) * (P d) (badBase d E s t δ N)).toReal
      = (condEps E u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ)) ^ (M + 1)
        * (P d).real (badBase d E s t δ N) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _),
      ENNReal.toReal_ofReal hε0, ENNReal.toReal_natCast, measureReal_def]
  have hreal := ENNReal.toReal_mono hfin htow
  rw [hL, hRr] at hreal
  have hp0 : (P d).real (badBase d E s t δ N) = (P d).real (goodSetFlow d E s t δ N)ᶜ := by
    rw [measureReal_def, measureReal_def, meas_badBase]
  have hp0nn : (0 : ℝ) ≤ (P d).real (badBase d E s t δ N) := measureReal_nonneg
  -- divide by `ε^{M+1}`
  have hA : (P d).real (badTower d N (condEps E u M (2 * δ N)) (badBase d E s t δ N) (M + 1))
      ≤ ((condEps E u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
          / condEps E u M (2 * δ N)) ^ (M + 1) * (P d).real (badBase d E s t δ N) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos heu0 (M + 1)), mul_comm]
    exact hreal
  -- pass from `u` to `t N`
  have hquot : (condEps E u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
        / condEps E u M (2 * δ N)
      ≤ (condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
        / condEps E (t N) M (2 * δ N) := by
    rw [add_div, div_self heu0.ne', add_div, div_self (heT0 N).ne']
    have h := div_le_div_of_nonneg_left (hR0 N) (heT0 N) hege
    linarith
  have hqu0 : (0 : ℝ) ≤ (condEps E u M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
      / condEps E u M (2 * δ N) :=
    (div_pos (add_pos_of_pos_of_nonneg heu0 (hR0 N)) heu0).le
  calc condEnv E u M ^ M
        * (P d).real (badTower d N (condEps E u M (2 * δ N)) (badBase d E s t δ N) (M + 1))
      ≤ condEnv E (t N) M ^ M
          * (((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
              / condEps E (t N) M (2 * δ N)) ^ (M + 1)
            * (P d).real (badBase d E s t δ N)) := by
        refine mul_le_mul (pow_le_pow_left₀ hEnvu0.le hEnvle M) (hA.trans ?_)
          measureReal_nonneg (pow_nonneg (hEnvt0 N).le M)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hqu0 hquot (M + 1)) hp0nn
    _ = (condEnv E (t N) M ^ M
          * ((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
              / condEps E (t N) M (2 * δ N)) ^ (M + 1))
        * (P d).real (badBase d E s t δ N) := by ring
    _ ≤ (condEnv E (t N) M ^ M
          * ((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
              / condEps E (t N) M (2 * δ N)) ^ (M + 1))
        * (((2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M))
          / (condEnv E (t N) M ^ M
            * ((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
                / condEps E (t N) M (2 * δ N)) ^ (M + 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (hG0 N).le
        rw [hp0]; exact hN
    _ = (2 * minorDiffC M * (2 * δ N) + 2 * δ N) ^ M * (2 * (2 * δ N)) ^ (M * M) := by
        have hGne : condEnv E (t N) M ^ M
            * ((condEps E (t N) M (2 * δ N) + (Fintype.card (d.Idx N) : ℝ))
                / condEps E (t N) M (2 * δ N)) ^ (M + 1) ≠ 0 := (hG0 N).ne'
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hGne]

/-- **`hsmall` of `RBM.Gauss.eq45Flow_of_goodSetFlow_budget`, derived from (4.1)**, at the two
budgets `M = n = 2p` the `2p`-th moment expansion provides. -/
theorem hsmall_of_highProb (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    (hδpos : ∀ N, 0 < δ N) (hδlo : PolyLo δ)
    (hηhi : PolyHi fun N => (etaT E (t N))⁻¹ + 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ)) (p : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      condEnv E u (2 * p) ^ (2 * p)
          * (P d).real (badTower d N (condEps E u (2 * p) (2 * δ N))
              (badBase d E s t δ N) (2 * p + 1))
        ≤ (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N) ^ (2 * p)
            * (2 * (2 * δ N)) ^ (2 * p * (2 * p)) :=
  hsmall_of_highProb_aux d hE ht1 hδpos hδlo hηhi hΩ (2 * p)

/-! ### (4.1) to (4.5), with nothing left over -/

/-- **(4.5) along the flow, from the flow good event (4.1) alone** — T188.

Word for word `RBM.Gauss.eq45Flow_of_goodSetFlow_budget` with `hsmall` **removed**: it is now
produced on the spot by `RBM.Gauss.hsmall_of_highProb` from `hΩ` (= (4.1)), the net condition
`hδnet` and the envelope condition `hEnv`, which are hypotheses the theorem already carried.

The hypothesis list therefore contains **no** statement quantified over all sample points and
**no** statement about the measure of the exceptional tower: the only probabilistic input is
`RBM.HighProb (P d) (RBM.Gauss.goodSetFlow …)`.  `RBM.Gauss.minorDiffGain_budget_hyps_consistent`
exhibits explicit parameters at which the numeric side conditions hold simultaneously, at
`B ≍ Ψ`. -/
theorem eq45Flow_of_goodSetFlow_highProb (d : Dims) {K Kenv Bx κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hδpos : ∀ N, 0 < δ N) (hδ4 : ∀ N, δ N ≤ 1 / 4)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hKenv : 0 ≤ Kenv) (hBx : 0 ≤ Bx)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-Bx) ≤ (2 * δ N) * (2 * δ N))
    (hΨ1 : ∀ᶠ N : ℕ in atTop, (2 * δ N) * (2 * δ N) ≤ 1)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * ((2 * δ N) * (2 * δ N)) ≤ (N : ℝ) ^ τ)
    (hll : LocalLawUnifIcc d E s t (fun N => 2 * δ N))
    (hMδ : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, 8 * (2 * p) * δ N ≤ 1)
    (hδC : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
      2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N ≤ 1)
    (hWδ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * (2 * δ N) ^ 2)
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖condExpDiag d N u (zt E u) (mE E) i ω
              - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖condExpDiag d N v (zt E v) (mE E) i ω
              - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    StepGlue.Eq45Flow (sample d) E s t := by
  have hηhi : PolyHi fun N => (etaT E (t N))⁻¹ + 1 :=
    polyHi_of_sq_le (Filter.Eventually.of_forall fun N => by
      have h0 : (0 : ℝ) ≤ (etaT E (t N))⁻¹ :=
        inv_nonneg.2 (etaT_pos_of_lt_one' hE (ht1 N)).le
      linarith) hEnv
  exact eq45Flow_of_goodSetFlow_budget d hκ0 hκ1 hEκ hE hs0 ht1 hst hK hδpos hδ4 hδnet hfine
    hΩ hKenv hBx hEnv hΨlow hΨ1 hΨW hll hMδ hδC hWδ
    (hsmall_of_highProb d hE ht1 hδpos (polyLo_of_one_div_rpow_le hδnet) hηhi hΩ)
    hHolIBP hHolRow hHolBlk

/-! ### Satisfiability, in both directions

T177 verified its budgeted interface in both directions; the same check applied to the
`p`-indexed numeric conditions of the end-to-end theorem turns up a real defect, repaired here.

**Negative.** `hMδ` in the shape T177 gave it — `∀ p N, 8 (2p) δ_N ≤ 1`, one quantifier over
*all* moment orders and *all* `N` — is **unsatisfiable** together with `hδpos : ∀ N, 0 < δ N`:
at a fixed `N` the left side is unbounded in `p` (`RBM.Gauss.not_forall_mul_le_one`).  The same
is true of `hδC`, whose constant `minorDiffC (2p) = 4^{2p} atomC(2p)^3` grows in `p`.  The
paper's order of quantifiers is the other one: `p` is fixed and `N → ∞`, with `δ_N → 0`.  Both
hypotheses are therefore stated as `∀ p, ∀ᶠ N in atTop, …`, here and in
`RBM.Gauss.eq45Flow_of_goodSetFlow_budget`.

**Positive.** `RBM.Gauss.eq45Flow_delta_hyps_consistent` exhibits explicit `K, s, t, δ` at which
every condition of the `δ`-cluster holds at once — including the two that pull against each
other: the net condition `1/N^{2K+6} ≤ δ_N` (a *lower* bound) and the fineness condition
`4 η⁻³ N³ √δ_N ≤ 1` (an *upper* bound, forcing `δ_N ≤ η⁶/(16 N⁶)`).  They are compatible
because `K` is free — `δ_N = (N+4)^{-28}` with `K = 12` works — and incompatible at `K = 0`,
where the net condition would need `η⁶ ≥ 16`. -/

/-- **The `∀ p N` form of `hMδ` is unsatisfiable at a strictly positive `δ`.**  This is why
`RBM.Gauss.eq45Flow_of_goodSetFlow_budget` takes `hMδ` and `hδC` in their eventual form. -/
theorem not_forall_mul_le_one {δ : ℕ → ℝ} {N : ℕ} (hδ : 0 < δ N) :
    ¬ ∀ p : ℕ, 8 * (2 * (p : ℝ)) * δ N ≤ 1 := by
  intro h
  obtain ⟨p, hp⟩ := exists_nat_gt (1 / (16 * δ N))
  have h16 : (0 : ℝ) < 16 * δ N := by linarith
  have hpk := h p
  rw [div_lt_iff₀ h16] at hp
  nlinarith

/-- **The `δ`-cluster of `RBM.Gauss.eq45Flow_of_goodSetFlow_highProb` is satisfiable.**

Explicit witness: `s = t = 0`, `δ_N = (N+4)^{-28}`, `K = 12` (so the net exponent
`(K+2+1)/(1/2)` is `30`).  The `p`-indexed conditions hold in their eventual form — and, by
`RBM.Gauss.not_forall_mul_le_one`, in no other. -/
theorem eq45Flow_delta_hyps_consistent {E : ℝ} (hE : |E| < 2) :
    ∃ (K : ℝ) (s t δ : ℕ → ℝ), 0 ≤ K ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, t N < 1) ∧
      (∀ N, s N ≤ t N) ∧ (∀ N, 0 < δ N) ∧ (∀ N, δ N ≤ 1 / 4) ∧
      (∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N) ∧
      (∀ᶠ N : ℕ in atTop,
        4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1) ∧
      (∀ p : ℕ, ∀ᶠ N : ℕ in atTop, 8 * (2 * (p : ℝ)) * δ N ≤ 1) ∧
      (∀ p : ℕ, ∀ᶠ N : ℕ in atTop,
        2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N ≤ 1) := by
  classical
  have hη : 0 < etaT E 0 := etaT_pos_of_lt_one' hE (by norm_num)
  have hone : ∀ N : ℕ, (1 : ℝ) ≤ (N : ℝ) + 4 := fun N => by
    have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hδpos : ∀ N : ℕ, (0 : ℝ) < (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 := fun N => by
    have := hone N; positivity
  have hδ4 : ∀ N : ℕ, (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 ≤ 1 / 4 := by
    intro N
    have h4 : (4 : ℝ) ≤ (N : ℝ) + 4 := by
      have := Nat.cast_nonneg (α := ℝ) N; linarith
    have hb : (2 : ℝ) ≤ ((N : ℝ) + 4) ^ (14 : ℕ) := by
      calc (2 : ℝ) ≤ (4 : ℝ) ^ (14 : ℕ) := by norm_num
        _ ≤ ((N : ℝ) + 4) ^ (14 : ℕ) := pow_le_pow_left₀ (by norm_num) h4 14
    have h2 : 1 / ((N : ℝ) + 4) ^ (14 : ℕ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hb
    have h3 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 4) ^ (14 : ℕ) := by positivity
    nlinarith
  have hpow28 : ∀ N : ℕ, (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2
      = 1 / ((N : ℝ) + 4) ^ (28 : ℕ) := by
    intro N; rw [div_pow, one_pow, ← pow_mul]
  have hδsmall : ∀ N : ℕ, (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 ≤ 1 / ((N : ℝ) + 4) := by
    intro N
    rw [hpow28 N]
    refine one_div_le_one_div_of_le (by linarith [hone N]) ?_
    calc ((N : ℝ) + 4) = ((N : ℝ) + 4) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ ((N : ℝ) + 4) ^ (28 : ℕ) := pow_le_pow_right₀ (hone N) (by norm_num)
  have hsqrt : ∀ N : ℕ, ((1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2) ^ ((1 : ℝ) / 2)
      = 1 / ((N : ℝ) + 4) ^ (14 : ℕ) := by
    intro N
    have h0 : (0 : ℝ) ≤ 1 / ((N : ℝ) + 4) ^ (14 : ℕ) := by
      have := hone N; positivity
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq h0]
  -- any fixed constant is eventually beaten by `δ⁻¹`
  have hkey : ∀ c : ℝ, 0 ≤ c →
      ∀ᶠ N : ℕ in atTop, c * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 ≤ 1 := by
    intro c hc
    filter_upwards [eventually_ge_atTop ⌈c⌉₊] with N hN
    have hcN : c ≤ (N : ℝ) := le_trans (Nat.le_ceil c) (by exact_mod_cast hN)
    have h4N : (0 : ℝ) < (N : ℝ) + 4 := by linarith [hone N]
    calc c * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 ≤ c * (1 / ((N : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_left (hδsmall N) hc
      _ ≤ 1 := by rw [mul_one_div, div_le_one h4N]; linarith
  -- the net condition, at `K = 12`
  have hnet : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (((12 : ℝ) + 2 + 1) / ((1 : ℝ) / 2))
        ≤ (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 := by
    filter_upwards [eventually_ge_atTop 16384] with N hN
    have hN16 : (16384 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp : ((12 : ℝ) + 2 + 1) / ((1 : ℝ) / 2) = ((30 : ℕ) : ℝ) := by norm_num
    rw [hexp, Real.rpow_natCast, hpow28 N]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h2N : ((N : ℝ) + 4) ≤ 2 * (N : ℝ) := by linarith
    have hNsq : (2 : ℝ) ^ (28 : ℕ) ≤ (N : ℝ) ^ (2 : ℕ) := by
      calc (2 : ℝ) ^ (28 : ℕ) = (16384 : ℝ) ^ (2 : ℕ) := by norm_num
        _ ≤ (N : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hN16 2
    calc ((N : ℝ) + 4) ^ (28 : ℕ) ≤ (2 * (N : ℝ)) ^ (28 : ℕ) :=
          pow_le_pow_left₀ (by linarith [hone N]) h2N 28
      _ = 2 ^ (28 : ℕ) * (N : ℝ) ^ (28 : ℕ) := mul_pow _ _ _
      _ ≤ (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (28 : ℕ) :=
          mul_le_mul_of_nonneg_right hNsq (by positivity)
      _ = (N : ℝ) ^ (30 : ℕ) := by rw [← pow_add]
  -- the fineness condition
  have hfineW : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E 0)⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ)
        * ((1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2) ^ ((1 : ℝ) / 2) ≤ 1 := by
    have hinv : (0 : ℝ) < (etaT E 0)⁻¹ := inv_pos.2 hη
    have hA0 : (0 : ℝ) < 4 * ((etaT E 0)⁻¹) ^ 3 := by positivity
    filter_upwards [eventually_ge_atTop ⌈4 * ((etaT E 0)⁻¹) ^ 3⌉₊, eventually_ge_atTop 1]
      with N hNA hN1
    have hAN : 4 * ((etaT E 0)⁻¹) ^ 3 ≤ (N : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hNA)
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hpow : (0 : ℝ) < ((N : ℝ) + 4) ^ (14 : ℕ) := by positivity
    rw [hsqrt N, mul_one_div, div_le_one hpow]
    calc 4 * ((etaT E 0)⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ)
        ≤ (N : ℝ) * (N : ℝ) ^ (3 : ℕ) := mul_le_mul_of_nonneg_right hAN (by positivity)
      _ = (N : ℝ) ^ (4 : ℕ) := by ring
      _ ≤ ((N : ℝ) + 4) ^ (4 : ℕ) := pow_le_pow_left₀ (by linarith) (by linarith) 4
      _ ≤ ((N : ℝ) + 4) ^ (14 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
  exact ⟨12, fun _ => 0, fun _ => 0, fun N => (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2,
    by norm_num, fun _ => le_rfl, fun _ => by norm_num, fun _ => le_rfl, hδpos, hδ4,
    hnet, hfineW,
    fun p => by
      filter_upwards [hkey (16 * (p : ℝ)) (by positivity)] with N h
      calc 8 * (2 * (p : ℝ)) * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2
          = 16 * (p : ℝ) * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 := by ring
        _ ≤ 1 := h,
    fun p => by
      filter_upwards [hkey (4 * minorDiffC (2 * p) + 2)
        (by linarith [minorDiffC_nonneg (2 * p)])] with N h
      calc 2 * minorDiffC (2 * p) * (2 * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2)
            + 2 * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2
          = (4 * minorDiffC (2 * p) + 2) * (1 / ((N : ℝ) + 4) ^ (14 : ℕ)) ^ 2 := by ring
        _ ≤ 1 := h⟩

end Small

end RBM.Gauss
