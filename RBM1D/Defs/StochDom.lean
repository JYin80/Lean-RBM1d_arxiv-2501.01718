/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Domination
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Stochastic domination `≺` and high-probability events

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.1 (i), (iii), (iv).

**Convention (a design choice for the whole random layer).**  The probability space `(Ω, P)` is
fixed, and the dependence on `N` is carried by the random variables: a family is
`ξ : ∀ N, U N → Ω → ℝ`, with `U N` the (possibly `N`-dependent) parameter set.  The paper's
`N`-dependent probability spaces are recovered by taking the product space.

* (i) `StochDom P ξ ζ` (`ξ ≺ ζ` uniformly in `u`): for all `τ > 0`, `D > 0`, eventually in `N`,
  `P(∃ u ∈ U(N), ξ(N,u) > N^τ ζ(N,u)) ≤ N^{-D}`.  The union over `u` sits inside the probability,
  as in the paper.
* (iii) `NormStochDom P A ζ`: `‖A‖ ≺ ζ`, for any normed values (complex numbers, matrices with a
  chosen operator norm).
* (iv) `HighProb P Ξ` (`Ξ` holds w.h.p.): `P(Ξᶜ) ≤ N^{-D}` eventually, for every `D > 0`;
  `HighProbIn P Ξ Ω'` (`Ω'` holds w.h.p. in `Ξ`): `P(Ξ \ Ω') ≤ N^{-D}`.

## Main results

* `StochDom.refl`, `trans`, `add`, `mul`, `const_mul_left`, `const_mul_right`: the closure
  properties; `StochDom.of_unifDetDom`: deterministic domination implies stochastic domination.
* `StochDom.of_forall_le`: **the union bound** — a bound for each `u` separately, uniform in `u`,
  gives the uniform statement if `#U(N) ≤ N^C`.
* `HighProb.inter`, `HighProb.biInter`: finitely many, resp. polynomially many, w.h.p. events
  hold simultaneously w.h.p.; `StochDom.highProb`: `ξ ≤ N^τ ζ` holds w.h.p.
-/

namespace RBM

open Filter MeasureTheory

section Arith

/-- `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`. -/
theorem eventually_two_mul_rpow_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 2 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (2 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN2
    _ = _ := mul_one _

/-- `N^C N^{-(D+C)} = N^{-D}`. -/
theorem rpow_mul_rpow_neg_add {N : ℕ} (hN : 1 ≤ N) (C D : ℝ) :
    (N : ℝ) ^ C * (N : ℝ) ^ (-(D + C)) = (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add hN0]; congr 1; ring

end Arith

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

section Defs

variable {U : ℕ → Type*}

/-- The failure event `{∃ u, ξ(N,u) > N^τ ζ(N,u)}`. -/
def badSet (ξ ζ : ∀ N, U N → Ω → ℝ) (τ : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∃ u, (N : ℝ) ^ τ * ζ N u ω < ξ N u ω}

/-- **Definition 2.1 (i)**: `ξ ≺ ζ`, uniformly in `u ∈ U(N)`. -/
def StochDom (ξ ζ : ∀ N, U N → Ω → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    P (badSet ξ ζ τ N) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- **Definition 2.1 (iii)** (and the complex case of (i)): `A = O≺(ζ)`, i.e. `‖A‖ ≺ ζ`. -/
def NormStochDom {E : Type*} [Norm E] (A : ∀ N, U N → Ω → E) (ζ : ∀ N, U N → Ω → ℝ) : Prop :=
  StochDom P (fun N u ω => ‖A N u ω‖) ζ

/-- **Definition 2.1 (iv)**: `Ξ` holds with high probability. -/
def HighProb (Ξ : ℕ → Set Ω) : Prop :=
  ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, P (Ξ N)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- **Definition 2.1 (iv)**: `Ω'` holds with high probability in `Ξ`. -/
def HighProbIn (Ξ Ω' : ℕ → Set Ω) : Prop :=
  ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, P (Ξ N \ Ω' N) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))

end Defs

namespace StochDom

variable {P} {U : ℕ → Type*} {ξ ζ χ ξ₁ ξ₂ ζ₁ ζ₂ : ∀ N, U N → Ω → ℝ}

/-- A failure event eventually contained in the failure event of a single domination. -/
theorem of_subset (h : StochDom P ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      badSet ξ ζ τ N ⊆ badSet ξ₁ ζ₁ τ' N) : StochDom P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with N h1 h2
  exact (measure_mono h1).trans h2

/-- A failure event eventually contained in the union of two failure events. -/
theorem of_subset_union {U₁ U₂ : ℕ → Type*} {f₁ g₁ : ∀ N, U₁ N → Ω → ℝ}
    {f₂ g₂ : ∀ N, U₂ N → Ω → ℝ} (h₁ : StochDom P f₁ g₁) (h₂ : StochDom P f₂ g₂)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      badSet ξ ζ τ N ⊆ badSet f₁ g₁ τ' N ∪ badSet f₂ g₂ τ' N) : StochDom P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith),
    eventually_two_mul_rpow_le D] with N h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P (badSet ξ ζ τ N) ≤ P (badSet f₁ g₁ τ' N ∪ badSet f₂ g₂ τ' N) := measure_mono h0
    _ ≤ P (badSet f₁ g₁ τ' N) + P (badSet f₂ g₂ τ' N) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- A failure event that is eventually empty. -/
theorem of_eventually_empty (h : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, badSet ξ ζ τ N = ∅) :
    StochDom P ξ ζ := by
  intro τ hτ D _
  filter_upwards [h τ hτ] with N hN
  rw [hN, measure_empty]; exact zero_le

/-- **Deterministic domination implies stochastic domination** (Definition 2.1 (ii) ⇒ (i)). -/
theorem of_unifDetDom {f g : ∀ N, U N → ℝ} (h : UnifDetDom f g) :
    StochDom P (fun N u _ => f N u) (fun N u _ => g N u) :=
  of_eventually_empty fun τ hτ => by
    filter_upwards [h τ hτ] with N hN
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    exact hN

/-- `ζ ≺ ζ` for a non-negative family. -/
theorem refl (hζ : ∀ N u ω, 0 ≤ ζ N u ω) : StochDom P ζ ζ :=
  of_eventually_empty fun τ hτ => by
    filter_upwards [eventually_ge_atTop 1] with N hN
    ext ω
    simp only [badSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow (by exact_mod_cast hN) hτ.le
    nlinarith [hζ N u ω]

/-- `≺` is transitive. -/
theorem trans (h₁ : StochDom P ξ ζ) (h₂ : StochDom P ζ χ) : StochDom P ξ χ := by
  refine of_subset_union h₁ h₂ fun τ hτ => ⟨τ / 2, half_pos hτ, Eventually.of_forall fun N => ?_⟩
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have := calc ξ N u ω ≤ (N : ℝ) ^ (τ / 2) * ζ N u ω := hno.1 u
    _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * χ N u ω) :=
        mul_le_mul_of_nonneg_left (hno.2 u) hpos
    _ = (N : ℝ) ^ τ * χ N u ω := by rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]
  linarith

/-- `≺` is closed under addition. -/
theorem add (h₁ : StochDom P ξ₁ ζ₁) (h₂ : StochDom P ξ₂ ζ₂) :
    StochDom P (ξ₁ + ξ₂) (ζ₁ + ζ₂) := by
  refine of_subset_union h₁ h₂ fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  simp only [Pi.add_apply, mul_add] at hu
  linarith [hno.1 u, hno.2 u]

/-- `≺` is closed under multiplication of non-negative quantities. -/
theorem mul (hξ₂ : ∀ N u ω, 0 ≤ ξ₂ N u ω) (hζ₁ : ∀ N u ω, 0 ≤ ζ₁ N u ω)
    (h₁ : StochDom P ξ₁ ζ₁) (h₂ : StochDom P ξ₂ ζ₂) : StochDom P (ξ₁ * ξ₂) (ζ₁ * ζ₂) := by
  refine of_subset_union h₁ h₂ fun τ hτ => ⟨τ / 2, half_pos hτ, Eventually.of_forall fun N => ?_⟩
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have := calc ξ₁ N u ω * ξ₂ N u ω ≤ ((N : ℝ) ^ (τ / 2) * ζ₁ N u ω) * ξ₂ N u ω :=
        mul_le_mul_of_nonneg_right (hno.1 u) (hξ₂ N u ω)
    _ ≤ ((N : ℝ) ^ (τ / 2) * ζ₁ N u ω) * ((N : ℝ) ^ (τ / 2) * ζ₂ N u ω) :=
        mul_le_mul_of_nonneg_left (hno.2 u) (mul_nonneg hpos (hζ₁ N u ω))
    _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2)) * (ζ₁ N u ω * ζ₂ N u ω) := by ring
    _ = (N : ℝ) ^ τ * (ζ₁ N u ω * ζ₂ N u ω) := by
        rw [UnifDetDom.rpow_half_mul_rpow_half N hτ]
  simp only [Pi.mul_apply] at hu
  linarith

/-- Constant factors on the left are absorbed: `ξ ≺ ζ` implies `c ξ ≺ ζ`. -/
theorem const_mul_left {c : ℝ} (hc : 0 ≤ c) (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom P ξ ζ) :
    StochDom P (fun N u ω => c * ξ N u ω) ζ := by
  refine of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [eventually_le_rpow c (half_pos hτ)] with N hcN
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h1 := hno u
  have h2 : 0 ≤ (N : ℝ) ^ (τ / 2) * ζ N u ω := mul_nonneg hpos (hζ N u ω)
  have := calc c * ξ N u ω ≤ c * ((N : ℝ) ^ (τ / 2) * ζ N u ω) := mul_le_mul_of_nonneg_left h1 hc
    _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ζ N u ω) := mul_le_mul_of_nonneg_right hcN h2
    _ = (N : ℝ) ^ τ * ζ N u ω := by rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]
  exact absurd hu (not_lt.2 this)

/-- Constant factors on the right are absorbed: `ξ ≺ ζ` implies `ξ ≺ c ζ` for `c > 0`. -/
theorem const_mul_right {c : ℝ} (hc : 0 < c) (hζ : ∀ N u ω, 0 ≤ ζ N u ω) (h : StochDom P ξ ζ) :
    StochDom P ξ (fun N u ω => c * ζ N u ω) := by
  refine of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [eventually_le_rpow c⁻¹ (half_pos hτ)] with N hcN
  intro ω ⟨u, hu⟩
  by_contra hno
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hpos : 0 ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h1 := hno u
  have hζ' := hζ N u ω
  have := calc ξ N u ω ≤ (N : ℝ) ^ (τ / 2) * ζ N u ω := h1
    _ = (N : ℝ) ^ (τ / 2) * (c⁻¹ * (c * ζ N u ω)) := by field_simp
    _ ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * (c * ζ N u ω)) := by
        gcongr
    _ = (N : ℝ) ^ τ * (c * ζ N u ω) := by rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]
  exact absurd hu (not_lt.2 this)

/-- **The union bound** (the content of "uniformly in `u`"): if each event
`{ξ(N,u) > N^τ ζ(N,u)}` has probability `≤ N^{-D}` for `N ≥ N₀(τ, D)` uniformly in `u`, and
`#U(N) ≤ N^C`, then `ξ ≺ ζ` uniformly in `u`. -/
theorem of_forall_le [∀ N, Fintype (U N)] {C : ℝ} (hC : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ C)
    (h : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u,
      P {ω | (N : ℝ) ^ τ * ζ N u ω < ξ N u ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  by_cases hC0 : 0 ≤ C
  · filter_upwards [hC, h τ hτ (D + C) (by linarith), eventually_ge_atTop 1] with N hcard hN hN1
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + C)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hset : badSet ξ ζ τ N = ⋃ u, {ω | (N : ℝ) ^ τ * ζ N u ω < ξ N u ω} := by
      ext ω; simp [badSet]
    calc P (badSet ξ ζ τ N) ≤ ∑ u, P {ω | (N : ℝ) ^ τ * ζ N u ω < ξ N u ω} := by
          rw [hset]; exact measure_iUnion_fintype_le P _
      _ ≤ ∑ _u : U N, ENNReal.ofReal ((N : ℝ) ^ (-(D + C))) := Finset.sum_le_sum fun u _ => hN u
      _ = ENNReal.ofReal (Fintype.card (U N) * (N : ℝ) ^ (-(D + C))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ C * (N : ℝ) ^ (-(D + C))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
      _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by rw [rpow_mul_rpow_neg_add hN1]
  · -- `C < 0`: then `#U(N) < 1`, so `U(N)` is empty and so is the failure event
    push Not at hC0
    filter_upwards [hC, eventually_ge_atTop 2] with N hcard hN2
    have hlt : (Fintype.card (U N) : ℝ) < 1 := by
      refine hcard.trans_lt ?_
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN2) hC0
    have h0 : Fintype.card (U N) = 0 := by exact_mod_cast (show (Fintype.card (U N) : ℝ) = 0 by
      have := Nat.cast_nonneg (α := ℝ) (Fintype.card (U N))
      rcases Nat.eq_zero_or_pos (Fintype.card (U N)) with h | h
      · exact_mod_cast h
      · exact absurd hlt (not_lt.2 (by exact_mod_cast h)))
    have hE : IsEmpty (U N) := Fintype.card_eq_zero_iff.1 h0
    have : badSet ξ ζ τ N = ∅ := by
      ext ω; simp only [badSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, -⟩; exact hE.false u
    rw [this, measure_empty]; exact zero_le

/-- **The good event holds with high probability**: `ξ ≺ ζ` means that for every `τ > 0`,
`{∀ u, ξ(N,u) ≤ N^τ ζ(N,u)}` holds w.h.p. -/
theorem highProb (h : StochDom P ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProb P (fun N => {ω | ∀ u, ξ N u ω ≤ (N : ℝ) ^ τ * ζ N u ω}) := by
  intro D hD
  filter_upwards [h τ hτ D hD] with N hN
  convert hN using 2
  ext ω; simp [badSet]

end StochDom

namespace HighProb

variable {P}

/-- Monotonicity. -/
theorem mono {Ξ Ξ' : ℕ → Set Ω} (h : HighProb P Ξ) (hsub : ∀ᶠ N : ℕ in atTop, Ξ N ⊆ Ξ' N) :
    HighProb P Ξ' := by
  intro D hD
  filter_upwards [h D hD, hsub] with N hN hs
  exact (measure_mono (Set.compl_subset_compl.2 hs)).trans hN

/-- Two w.h.p. events hold simultaneously w.h.p. -/
theorem inter {Ξ₁ Ξ₂ : ℕ → Set Ω} (h₁ : HighProb P Ξ₁) (h₂ : HighProb P Ξ₂) :
    HighProb P (fun N => Ξ₁ N ∩ Ξ₂ N) := by
  intro D hD
  filter_upwards [h₁ (D + 1) (by linarith), h₂ (D + 1) (by linarith),
    eventually_two_mul_rpow_le D] with N hN1 hN2 h3
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P (Ξ₁ N ∩ Ξ₂ N)ᶜ = P ((Ξ₁ N)ᶜ ∪ (Ξ₂ N)ᶜ) := by rw [Set.compl_inter]
    _ ≤ P (Ξ₁ N)ᶜ + P (Ξ₂ N)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add hN1 hN2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- **Polynomially many w.h.p. events hold simultaneously w.h.p.**: if each `Ξ(N,k)`,
`k ∈ K(N)`, holds w.h.p. uniformly in `k`, and `#K(N) ≤ N^C`, then `⋂_k Ξ(N,k)` holds w.h.p. -/
theorem biInter {K : ℕ → Type*} [∀ N, Fintype (K N)] {Ξ : ∀ N, K N → Set Ω} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᶠ N : ℕ in atTop, (Fintype.card (K N) : ℝ) ≤ (N : ℝ) ^ C)
    (h : ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k, P (Ξ N k)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) :
    HighProb P (fun N => ⋂ k, Ξ N k) := by
  intro D hD
  filter_upwards [hC, h (D + C) (by linarith), eventually_ge_atTop 1] with N hcard hN hN1
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + C)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P (⋂ k, Ξ N k)ᶜ = P (⋃ k, (Ξ N k)ᶜ) := by rw [Set.compl_iInter]
    _ ≤ ∑ k, P (Ξ N k)ᶜ := measure_iUnion_fintype_le P _
    _ ≤ ∑ _k : K N, ENNReal.ofReal ((N : ℝ) ^ (-(D + C))) := Finset.sum_le_sum fun k _ => hN k
    _ = ENNReal.ofReal (Fintype.card (K N) * (N : ℝ) ^ (-(D + C))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ C * (N : ℝ) ^ (-(D + C))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ = ENNReal.ofReal ((N : ℝ) ^ (-D)) := by rw [rpow_mul_rpow_neg_add hN1]

/-- A w.h.p. event holds w.h.p. in any `Ξ`. -/
theorem highProbIn {Ω' : ℕ → Set Ω} (h : HighProb P Ω') (Ξ : ℕ → Set Ω) :
    HighProbIn P Ξ Ω' := by
  intro D hD
  filter_upwards [h D hD] with N hN
  exact (measure_mono fun ω hω => hω.2).trans hN

end HighProb

end RBM
