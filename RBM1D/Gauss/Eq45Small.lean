/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MinorDiffCond

/-!
# Polynomial envelopes, and the complement of a high-probability event

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the bookkeeping that turns (4.1) into the smallness of an exceptional set on the
route from (4.1) to (4.5).

`RBM.Gauss.PolyLo` / `RBM.Gauss.PolyHi` are the two one-line predicates "eventually at least
`C N^{-D}`" / "eventually at most `C N^{D}`", with the closure lemmas (product, power, inverse,
sum, monotonicity), and `RBM.Gauss.measureReal_compl_le_of_polyLo`, which is the only place
`RBM.HighProb` is used: a `RBM.HighProb` event's complement is eventually below **any**
`RBM.Gauss.PolyLo` function.  `RBM.HighProb` quantifies over *every* `D`, so one choice of `D`
beats a whole polynomial.
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

section Small

variable {E : ℝ} {s t δ : ℕ → ℝ}

/-! ### (4.1) to (4.5), with nothing left over -/

end Small

end RBM.Gauss
