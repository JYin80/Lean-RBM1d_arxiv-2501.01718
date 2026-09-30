/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBoundFloor
import RBM1D.Hierarchy.Decay
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Defs.StochDomHighProb

/-!
# Quantitative estimates for Lemma 5.9 along the flow

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, §5.4, Lemma 5.9 (5.75).

Along the flow, Lemma 5.9 reduces to three conditions:

1. the radius `2m(ℓ + 2)` of the deterministic Lemma 5.9 of `RBM1D/Hierarchy/Decay.lean` must
   beat the target radius `ℓ_u N^τ`;
2. its error, `27Φ√δ₂ max(1, |Im z_u|⁻¹)^m + C_m(1-u) e^{-c(1-u) · 2m(ℓ+2)}`, must beat
   `N^{-D}`;
3. the event of Lemma 4.1 together with the decay (2.76) must hold with high probability,
   *uniformly in* `u ∈ [s_N, t_N]`.

This file proves the deterministic estimates behind (1) and (2), and states the decay clause
of (3) as the event `RBM.LKDecayQuant.FlowDec`: at *every* `u ∈ [s_N, t_N]` the two-point
function `Lre` is at most `ε_N` beyond the (2.76) radius.

## The two quantitative mechanisms

**The radius.**  The (2.76) radius is taken to be `ℓ = ℓ_u N^{τ/2}` — the geometric mean
of `ℓ_u` and the target `ℓ_u N^τ`.  Then `2m(ℓ + 2) ≤ 6m ℓ_u N^{τ/2} ≤ ℓ_u N^τ` as soon as
`6m ≤ N^{τ/2}`, which is eventual for fixed `m` and `τ > 0`.

**The error.**  The `K`-side term is `C_m(1-u) e^{-c(1-u) · 2m(ℓ+2)}` with
`c(δ) = c₀√δ/4` (`RBM.cor35Rate`).  Since `ℓ̂(u) = min((1-u)^{-1/2}, L)`, there are two
regimes, and *both* are favourable:

* if `L √(1-u) < 1` the cut-off is active, `ℓ_u = L`, and the target radius `ℓ_u N^τ`
  already exceeds the diameter `L/2` of the ring — the decay statement is **vacuous**
  (`RBM.LKDecayQuant.loopDecay_of_half_lt`);
* if `1 ≤ L √(1-u)` the cut-off is inactive and `ℓ_u √(1-u) = 1` exactly
  (`RBM.LKDecayQuant.ellHat_mul_sqrt_eq_one`), so the exponent is
  `≥ (c₀/4)·2m·N^{τ/2}` — *independently of `u`* — while `1 - u ≥ N^{-2}`, so the prefactor
  `C_m(1-u)` is polynomially bounded (`RBM.LKDecayQuant.cKdecay_le_bound`).  A stretched
  exponential beats a power (`RBM.SumZeroDyn.eventually_exp_small`).

The `L`-side term `27Φ√δ₂ max(1,|Im z_u|⁻¹)^m` is handled by asking `Φ√ε ≤ N^{-D'}` with
`D' = D + 2m + 1`, which absorbs the polynomial factor `max(1, η_u⁻¹)^m ≤ (C_E N^2)^m`.

## Main results

* `RBM.LKDecayQuant.cKdecay_le_bound` — an explicit polynomial-in-`δ⁻¹` majorant for
  `RBM.Decay.cKdecay`.
* `RBM.LKDecayQuant.loopDecay_of_half_lt`, `RBM.LKDecayQuant.ellHat_mul_sqrt_eq_one`,
  `RBM.LKDecayQuant.ellHat_eq_L` — the two regimes of `ℓ̂(u)`.
* `RBM.LKDecayQuant.term2_le` — the `K`-side error of condition (2) is `≤ N^{-D}/2`.
* `RBM.LKDecayQuant.FlowDec`, `RBM.LKDecayQuant.prefactor_le` — the decay clause of condition
  (3), and the polynomial bound on the prefactor of (2.76) in the regime `1 ≤ L √(1-u)`.

## Deviations

* The decay clause asks for `Φ_N √(ε_N) ≤ N^{-D'}` for every `D' > 0`.  This is what (2.76)
  supplies at the radius `ℓ_u N^{τ/2}`: the profile `exp(-(|a-b|/ℓ_u)^{1/2}) + W^{-D''}`
  is `≤ exp(-N^{τ/4}) + W^{-D''}` there, and `Φ` is a power of `N`.
* The radius convention is `ℓ_u N^τ` rather than the paper's `ℓ_u W^τ`.
-/

namespace RBM

namespace LKDecayQuant

open Real Filter MeasureTheory

/-! ### A polynomial majorant for the constant of Corollary 3.5 -/

section Constants

/-- `c₀ = (16π²)⁻¹ ≤ 1`. -/
theorem cZero_le_one : cZero ≤ 1 := by
  unfold cZero
  have h : (3 : ℝ) < π := pi_gt_three
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- `2 / (1 - e^{-λ}) ≤ 4 / λ` for `0 < λ ≤ 1`: the elementary bound behind the polynomial
majorant of `RBM.cor35Const`. -/
theorem two_div_one_sub_exp_le {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    2 / (1 - exp (-lam)) ≤ 4 / lam := by
  have hexp : exp (-lam) ≤ 1 / (1 + lam) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp lam])
  have hlow : lam / 2 ≤ 1 - exp (-lam) := by
    have he : 1 - 1 / (1 + lam) = lam / (1 + lam) := by field_simp; ring
    have h2 : lam / 2 ≤ lam / (1 + lam) := by gcongr; linarith
    linarith
  have hpos : 0 < lam / 2 := half_pos h0
  calc 2 / (1 - exp (-lam)) ≤ 2 / (lam / 2) := by gcongr
    _ = 4 / lam := by field_simp; ring

/-- An explicit polynomial-in-`δ⁻¹` majorant for the constant `C_n(δ)` of Corollary 3.5. -/
noncomputable def cor35ConstBound (n : ℕ) : ℝ :=
  ((TSP n).card : ℝ) * (2 * cTwo52 + 1) ^ (n + n * n) * (8 * (n * n : ℕ) / cZero) ^ (n * n)

theorem cor35ConstBound_nonneg (n : ℕ) : 0 ≤ cor35ConstBound n := by
  unfold cor35ConstBound
  have := cTwo52_pos
  have := cZero_pos
  positivity

/-- **`C_n(δ) ≤ B_n δ^{-(n + 2n²)}`** for `0 < δ ≤ 1`. -/
theorem cor35Const_le_bound (n : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    cor35Const n δ ≤ cor35ConstBound n * (1 / δ) ^ (n + 2 * (n * n)) := by
  have hc2 := cTwo52_pos
  have hc0 := cZero_pos
  have hinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cor35Const, cor35ConstBound]
  have hA : 2 * cTwo52 / δ + 1 ≤ (2 * cTwo52 + 1) * (1 / δ) := by
    rw [add_mul, one_mul]
    have h : 2 * cTwo52 / δ = 2 * cTwo52 * (1 / δ) := by ring
    rw [h]
    linarith
  have hnn : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by positivity
  set lam : ℝ := cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)) with hlamdef
  have hsq0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ0
  have hsq1 : Real.sqrt δ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hδ1
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith [cZero_le_one, hsq1, hsq0.le, hc0.le]
  have hB : 2 / (1 - exp (-lam)) ≤ 8 * ((n * n : ℕ) : ℝ) / cZero * (1 / δ) := by
    refine (two_div_one_sub_exp_le hlam0 hlam1).trans ?_
    rw [hlamdef]
    have e : 4 / (cZero * Real.sqrt δ / (2 * ((n * n : ℕ) : ℝ)))
        = 8 * ((n * n : ℕ) : ℝ) / cZero * (1 / Real.sqrt δ) := by
      field_simp; ring
    rw [e]
    have hs : 1 / Real.sqrt δ ≤ 1 / δ := by
      refine one_div_le_one_div_of_le hδ0 ?_
      calc δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ0.le).symm
        _ ≤ 1 * Real.sqrt δ := by nlinarith
        _ = Real.sqrt δ := one_mul _
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have hB0 : (0 : ℝ) ≤ 2 / (1 - exp (-lam)) := by
    have h : exp (-lam) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    positivity
  have hA0 : (0 : ℝ) ≤ 2 * cTwo52 / δ + 1 := by positivity
  unfold cor35Const cor35ConstBound
  rw [← hlamdef]
  have h1 : (2 * cTwo52 / δ + 1) ^ (n + n * n)
      ≤ (2 * cTwo52 + 1) ^ (n + n * n) * (1 / δ) ^ (n + n * n) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hA0 hA _
  have h2 : (2 / (1 - exp (-lam))) ^ (n * n)
      ≤ (8 * ((n * n : ℕ) : ℝ) / cZero) ^ (n * n) * (1 / δ) ^ (n * n) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hB0 hB _
  have hcard : (0 : ℝ) ≤ ((TSP n).card : ℝ) := Nat.cast_nonneg _
  have hexp : (1 / δ) ^ (n + n * n) * (1 / δ) ^ (n * n) = (1 / δ) ^ (n + 2 * (n * n)) := by
    rw [← pow_add]; ring_nf
  calc ((TSP n).card : ℝ) * ((2 * cTwo52 / δ + 1) ^ (n + n * n) * (2 / (1 - exp (-lam))) ^ (n * n))
      ≤ ((TSP n).card : ℝ) * (((2 * cTwo52 + 1) ^ (n + n * n) * (1 / δ) ^ (n + n * n))
          * ((8 * ((n * n : ℕ) : ℝ) / cZero) ^ (n * n) * (1 / δ) ^ (n * n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity)) hcard
    _ = ((TSP n).card : ℝ) * (2 * cTwo52 + 1) ^ (n + n * n)
          * (8 * ((n * n : ℕ) : ℝ) / cZero) ^ (n * n)
          * ((1 / δ) ^ (n + n * n) * (1 / δ) ^ (n * n)) := by ring
    _ = _ := by rw [hexp]

/-- The constant of the polynomial majorant of `RBM.Decay.cKdecay`. -/
noncomputable def cKbound (m : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (m + 1), cor35ConstBound n) + 2 * cTwo52

/-- The exponent of the polynomial majorant of `RBM.Decay.cKdecay`. -/
def cKexp (m : ℕ) : ℕ := m + 2 * (m * m) + 1

theorem cKbound_nonneg (m : ℕ) : 0 ≤ cKbound m := by
  unfold cKbound
  have h : (0 : ℝ) ≤ ∑ n ∈ Finset.range (m + 1), cor35ConstBound n :=
    Finset.sum_nonneg fun n _ => cor35ConstBound_nonneg n
  linarith [cTwo52_pos]

/-- **`C_m(δ) ≤ cKbound m · δ^{-cKexp m}`** for `0 < δ ≤ 1`: the constant of Lemma 5.9's
`K`-side is polynomially bounded in `(1-u)^{-1}`. -/
theorem cKdecay_le_bound (m : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Decay.cKdecay m δ ≤ cKbound m * (1 / δ) ^ cKexp m := by
  have hinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hsum : ∑ n ∈ Finset.range (m + 1), cor35Const n δ
      ≤ (∑ n ∈ Finset.range (m + 1), cor35ConstBound n) * (1 / δ) ^ cKexp m := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnm : n ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    refine (cor35Const_le_bound n hδ0 hδ1).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv ?_) (cor35ConstBound_nonneg n)
    have : n * n ≤ m * m := Nat.mul_le_mul hnm hnm
    unfold cKexp; omega
  have htail : 2 * cTwo52 / δ ≤ 2 * cTwo52 * (1 / δ) ^ cKexp m := by
    have h1 : (1 / δ) ^ 1 ≤ (1 / δ) ^ cKexp m := by
      refine pow_le_pow_right₀ hinv ?_
      unfold cKexp; omega
    rw [pow_one] at h1
    have h : 2 * cTwo52 / δ = 2 * cTwo52 * (1 / δ) := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_left h1 (by linarith [cTwo52_pos])
  unfold Decay.cKdecay cKbound
  rw [add_mul]
  linarith

end Constants

/-! ### The two regimes of `ℓ̂(u) = min((1-u)^{-1/2}, L)` -/

section Regimes

variable {L : ℕ} [NeZero L]

/-- A decay statement whose radius exceeds the diameter `L/2` of the ring is vacuous. -/
theorem loopDecay_of_half_lt {m : ℕ} {R δ : ℝ} (hR : (L : ℝ) / 2 < R)
    (F : LoopIdx (ZMod L) → ℂ) : Decay.LoopDecay L m R δ F := by
  intro J _ _ x _ y _ hxy
  exact absurd (lt_of_lt_of_le (lt_of_le_of_lt (zdist_le_half (x - y)) hR) hxy) (lt_irrefl _)

end Regimes

/-- In the regime `1 ≤ L √(1-u)` the cut-off in `ℓ̂` is inactive: `ℓ̂(u) √(1-u) = 1`. -/
theorem ellHat_mul_sqrt_eq_one (L : ℕ) {u : ℝ} (hu1 : u < 1)
    (h : 1 ≤ (L : ℝ) * Real.sqrt (1 - u)) : ellHat L (u : ℂ) * Real.sqrt (1 - u) = 1 := by
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 (by linarith)
  have hle : 1 / Real.sqrt (1 - u) ≤ (L : ℝ) := by rw [div_le_iff₀ hs]; linarith
  rw [ellHat_ofReal L hu1, min_eq_left hle]
  field_simp

/-- In the regime `L √(1-u) < 1` the cut-off in `ℓ̂` is active: `ℓ̂(u) = L`. -/
theorem ellHat_eq_L (L : ℕ) {u : ℝ} (hu1 : u < 1)
    (h : (L : ℝ) * Real.sqrt (1 - u) < 1) : ellHat L (u : ℂ) = (L : ℝ) := by
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.2 (by linarith)
  have hle : (L : ℝ) ≤ 1 / Real.sqrt (1 - u) := by rw [le_div_iff₀ hs]; linarith
  rw [ellHat_ofReal L hu1, min_eq_right hle]

/-! ### Obligation (1): the radius -/

/-! ### Obligation (2): the error -/

theorem term2_le {m N : ℕ} {D τ v R : ℝ}
    (hN0 : (0 : ℝ) < (N : ℝ)) (hv0 : 0 < v) (hv1 : v ≤ 1) (hvN : 1 / v ≤ (N : ℝ) ^ 2)
    (hexpo : cZero / 2 * (N : ℝ) ^ (τ / 2) ≤ cor35Rate v * R)
    (hbig : 2 * cKbound m * (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ) + D)
        * exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2))) ≤ 1) :
    Decay.cKdecay m v * exp (-(cor35Rate v * R)) ≤ 1 / 2 * (N : ℝ) ^ (-D) := by
  have hinv0 : (0 : ℝ) ≤ 1 / v := by positivity
  have hC : Decay.cKdecay m v ≤ cKbound m * ((N : ℝ) ^ 2) ^ cKexp m := by
    refine (cKdecay_le_bound m hv0 hv1).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hinv0 hvN _) (cKbound_nonneg m)
  have hpow : ((N : ℝ) ^ 2) ^ cKexp m = (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast (N : ℝ) (2 * cKexp m)]
  have hE : exp (-(cor35Rate v * R)) ≤ exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2))) :=
    Real.exp_le_exp.2 (by linarith)
  have hD0 : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ) + D)
      = (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ)) * (N : ℝ) ^ D := Real.rpow_add hN0 _ _
  have hle : Decay.cKdecay m v * exp (-(cor35Rate v * R))
      ≤ cKbound m * (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ)) * exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2))) := by
    rw [← hpow]
    refine mul_le_mul hC hE (Real.exp_pos _).le ?_
    have := cKbound_nonneg m
    positivity
  have hfin : cKbound m * (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ))
      * exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2))) ≤ 1 / 2 * (N : ℝ) ^ (-D) := by
    rw [hsplit] at hbig
    have hneg : (N : ℝ) ^ (-D) = ((N : ℝ) ^ D)⁻¹ := Real.rpow_neg hN0.le D
    set A : ℝ := cKbound m * (N : ℝ) ^ (((2 * cKexp m : ℕ) : ℝ))
      * exp (-(cZero / 2 * (N : ℝ) ^ (τ / 2))) with hA
    have hAP : A * (N : ℝ) ^ D ≤ 1 / 2 := by rw [hA]; nlinarith [hbig]
    have hPinv : (N : ℝ) ^ D * ((N : ℝ) ^ D)⁻¹ = 1 := mul_inv_cancel₀ hD0.ne'
    rw [hneg]
    calc A = A * ((N : ℝ) ^ D * ((N : ℝ) ^ D)⁻¹) := by rw [hPinv]; ring
      _ = A * (N : ℝ) ^ D * ((N : ℝ) ^ D)⁻¹ := by ring
      _ ≤ 1 / 2 * ((N : ℝ) ^ D)⁻¹ := mul_le_mul_of_nonneg_right hAP (by positivity)
  linarith [hle, hfin]


/-! ### Obligation (3): the Lemma 4.1 event and (2.76), uniformly in `u ∈ [s, t]` -/

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- `L_N ≤ N` eventually (from `W L ≤ N` and `W ≥ 1`). -/
theorem eventually_L_le : ∀ᶠ N : ℕ in atTop, (B.L N : ℝ) ≤ (N : ℝ) := by
  filter_upwards [B.dim] with N hN
  have h : B.L N ≤ B.W N * B.L N := Nat.le_mul_of_pos_left _ (B.W_pos N)
  exact_mod_cast h.trans hN.1

end Flow

/-! ### The two conclusions -/

section Conclusions

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end Conclusions

section Plug

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end Plug

/-! ### The decay clause of condition (3) -/

section Produce

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **The decay clause of condition (3)**: the decay (2.76) of the `(+,-)` two-point function
beyond the radius `ℓ_u N^{τ/2}`, at every `u ∈ [s_N, t_N]`. -/
def FlowDec (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (eps : ℕ → ℝ) (τ : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N, ∀ a b : ZMod (B.L N),
      B.ell N (u : ℝ) * (N : ℝ) ^ (τ / 2) ≤ (zdist (B.L N) (a - b) : ℝ) →
        Lre (X.H N (u : ℝ) ω) (zt E (u : ℝ)) a b ≤ eps N}

/-! #### Clauses (ii)–(iii): the large deviation bounds -/

/-! #### Clause (iv): the decay (2.76) at the radius `ℓ_u N^{τ/2}` -/

/-- Moving a factor `N^c` to the other side of a bound. -/
theorem le_rpow_neg_of_mul_le {N : ℕ} (hN0 : (0 : ℝ) < (N : ℝ)) {x y c : ℝ}
    (h : x * (N : ℝ) ^ c ≤ y) : x ≤ y * (N : ℝ) ^ (-c) :=
  calc x = x * (N : ℝ) ^ c * (N : ℝ) ^ (-c) := by
        rw [mul_assoc, ← Real.rpow_add hN0]; simp
    _ ≤ y * (N : ℝ) ^ (-c) := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hN0.le _)

/-- **The prefactor of (2.76) is polynomially bounded in the regime `1 ≤ L √(1-u)`.**

`(η_s/η_u)^4 (W ℓ_u η_u)^{-2} ≤ N^{13}`.  The two `Im m^{(E)}` in `η_s/η_u = (1-s)/(1-u)`
cancel, and `1 - u ≥ N^{-2}` is what the regime `1 ≤ L √(1-u)` gives (with `L ≤ N`); the
remaining `(Im m^{(E)})^{-2}` is an `N`-independent constant, absorbed by `hCE`. -/
theorem prefactor_le (hE : |E| < 2) {N : ℕ} {sv uv : ℝ} (hs0 : 0 ≤ sv) (hsu : sv ≤ uv)
    (hu1 : uv < 1) (hvN : 1 / (1 - uv) ≤ (N : ℝ) ^ 2) (hN1 : (1 : ℝ) ≤ (N : ℝ))
    (hell : (1 : ℝ) ≤ B.ell N uv)
    (hCE : (max 1 ((mE E).im)⁻¹) ^ 2 ≤ (N : ℝ)) :
    (etaT E sv / etaT E uv) ^ 4 * (B.scale E N uv)⁻¹ ^ 2 ≤ (N : ℝ) ^ (13 : ℝ) := by
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hv0 : (0 : ℝ) < 1 - uv := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hηu : etaT E uv = (1 - uv) * (mE E).im := rfl
  have hηs : etaT E sv = (1 - sv) * (mE E).im := rfl
  have hηu0 : 0 < etaT E uv := by rw [hηu]; positivity
  have hinv : (1 - uv)⁻¹ ≤ (N : ℝ) ^ 2 := by rwa [← one_div]
  have hratio : etaT E sv / etaT E uv = (1 - sv) / (1 - uv) := by
    rw [hηu, hηs]; field_simp
  have hr0 : 0 ≤ etaT E sv / etaT E uv := by
    rw [hratio]; exact div_nonneg (by linarith) hv0.le
  have hr1 : etaT E sv / etaT E uv ≤ (N : ℝ) ^ 2 := by
    rw [hratio]
    calc (1 - sv) / (1 - uv) ≤ 1 / (1 - uv) := by gcongr; linarith
      _ ≤ (N : ℝ) ^ 2 := hvN
  have hp4 : (etaT E sv / etaT E uv) ^ 4 ≤ ((N : ℝ) ^ 2) ^ 4 := pow_le_pow_left₀ hr0 hr1 4
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hWl : (1 : ℝ) ≤ (B.W N : ℝ) * B.ell N uv := by nlinarith
  have hsc : etaT E uv ≤ B.scale E N uv := by
    show etaT E uv ≤ (B.W N : ℝ) * B.ell N uv * etaT E uv
    nlinarith
  have hsc0 : (0 : ℝ) < B.scale E N uv := lt_of_lt_of_le hηu0 hsc
  have hCE1 : (1 : ℝ) ≤ max 1 ((mE E).im)⁻¹ := le_max_left _ _
  have hscinv : (B.scale E N uv)⁻¹ ≤ (N : ℝ) ^ 2 * max 1 ((mE E).im)⁻¹ := by
    have h1 : (B.scale E N uv)⁻¹ ≤ (etaT E uv)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hηu0 hsc
    refine h1.trans ?_
    rw [hηu, mul_inv]
    exact mul_le_mul hinv (le_max_right _ _) (by positivity) (by positivity)
  have hp2 : ((B.scale E N uv)⁻¹) ^ 2 ≤ ((N : ℝ) ^ 2 * max 1 ((mE E).im)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hscinv 2
  have hmul : (etaT E sv / etaT E uv) ^ 4 * (B.scale E N uv)⁻¹ ^ 2
      ≤ ((N : ℝ) ^ 2) ^ 4 * ((N : ℝ) ^ 2 * max 1 ((mE E).im)⁻¹) ^ 2 :=
    mul_le_mul hp4 hp2 (by positivity) (by positivity)
  refine hmul.trans ?_
  have hnat : (N : ℝ) ^ (13 : ℝ) = (N : ℝ) ^ (13 : ℕ) := by
    rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hnat]
  have hexp : ((N : ℝ) ^ 2) ^ 4 * ((N : ℝ) ^ 2 * max 1 ((mE E).im)⁻¹) ^ 2
      = (N : ℝ) ^ (12 : ℕ) * (max 1 ((mE E).im)⁻¹) ^ 2 := by ring
  rw [hexp, pow_succ]
  exact mul_le_mul_of_nonneg_left hCE (by positivity)

/-! #### The assembly -/

end Produce

/-! ### The Definition-5.8 decay of the flow's `G`-loops -/

section GLoopDecay

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end GLoopDecay

/-! ### The large deviation bounds (4.2) with an additive floor

A floor `f` in the large deviation bounds (4.2) enters the entry bound (4.10)/(4.11) exactly the
way the (2.76) error `δ₂` does — additively, inside the same bracket — so Lemma 5.9's error
`27 Φ √δ₂ max(1,|Im z|⁻¹)^m` becomes `27 Φ √(δ₂ + f)`.  With the floor taken equal to the
(2.76) error `ε_N`, a small enough power of `N`, nothing is lost: the downstream decay target
always carries a `W^{-D}` floor of its own.

The declarations of this section are `export`s of `RBM1D/Green/EntryBoundFloor.lean`, which
this file imports; the names denote the same constants.
-/

/-! #### The floored entry-bound lemmas, exported from `RBM1D/Green/EntryBoundFloor.lean`

The names below denote the **same constants** as `RBM.LDERowFloor`, `RBM.LDEColFloor`,
`RBM.norm_sq_green_le_row_floor`, `RBM.norm_sq_green_le_col_floor` and
`RBM.norm_sq_green_le_two_sided_floor`.  `RBM.LDEQuadFloor` is the (4.7) analogue. -/

export _root_.RBM (LDERowFloor LDEColFloor norm_sq_green_le_row_floor
  norm_sq_green_le_col_floor norm_sq_green_le_two_sided_floor)

namespace LDERowFloor

end LDERowFloor

namespace LDEColFloor

end LDEColFloor

section BlkFloor

open Finset

variable (L : ℕ) [NeZero L] {W : ℕ} [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-! #### `RBM.norm_sq_green_le_blk_floor`, exported from `RBM1D/Green/EntryBoundFloor.lean`

`RBM.norm_sq_green_le_blk_floor`, (4.2) in the block model with a floor, is exported into this
namespace. -/

export _root_.RBM (norm_sq_green_le_blk_floor)

end BlkFloor

section Flow'

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end Flow'

end LKDecayQuant

end RBM
