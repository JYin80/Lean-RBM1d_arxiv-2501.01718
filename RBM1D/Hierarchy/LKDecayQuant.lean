/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.DecayBridge

/-!
# T126: the quantitative closure of `RBM.SumZeroDyn.LKDecay`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, §5.4, Lemma 5.9 (5.75).

T118 (`RBM1D/Hierarchy/DecayBridge.lean`) reduced `RBM.SumZeroDyn.LKDecay` to
`RBM.DecayBridge.lkDecay_of_highProb`, i.e. to three obligations:

1. the radius of `RBM.Decay.lemma59`, `2m(ℓ + 2)`, must beat the target radius `ℓ_u N^τ`;
2. its error, `27Φ√δ₂ max(1, |Im z_u|⁻¹)^m + C_m(1-u) e^{-c(1-u) · 2m(ℓ+2)}`, must beat
   `N^{-D}`;
3. the event of Lemma 4.1 together with the decay (2.76) must hold with high probability,
   *uniformly in* `u ∈ [s_N, t_N]`.

This file closes (1) and (2) and takes (3) as the named hypothesis
`RBM.LKDecayQuant.FlowInputs`, in the shape that T130 (`RBM1D/Gauss/GoodSetFlow.lean`)
produces: a high-probability event on which, at *every* `u ∈ [s_N, t_N]`, the Lemma 4.1
data (`GoodEvent`, `LDERow`, `LDECol`) holds with parameters `δ_N, Φ_N` and the two-point
function `Lre` is at most `ε_N` beyond the (2.76) radius.

## The two quantitative mechanisms

**The radius.**  The (2.76) radius is taken to be `ℓ = ℓ_u N^{τ/2}` — the geometric mean
of `ℓ_u` and the target `ℓ_u N^τ`.  Then `2m(ℓ + 2) ≤ 6m ℓ_u N^{τ/2} ≤ ℓ_u N^τ` as soon as
`6m ≤ N^{τ/2}`, which is eventual for fixed `m` and `τ > 0`
(`RBM.LKDecayQuant.radius_le`).

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
  `RBM.Decay.cKdecay`, the only genuinely new analytic input.
* `RBM.LKDecayQuant.FlowGoodSet`, `RBM.LKDecayQuant.FlowInputs` — obligation (3), assumed.
* `RBM.LKDecayQuant.highProb_loopDecay_pair` — the pathwise conclusion of Lemma 5.9 at the
  parameters `(m, τ, D)`, for *both* `L` and `L - K`, with high probability.
* `RBM.LKDecayQuant.lkDecay_of_flowInputs` — `RBM.SumZeroDyn.LKDecay`, unconditional modulo
  `FlowInputs`.
* `RBM.LKDecayQuant.LDecay`, `RBM.LKDecayQuant.lDecay_of_flowInputs` — the `|L|` half of
  (5.75) that `RBM.SumZeroDyn.LKDecay` drops (`docs/paper-deltas.md` #78), by the same
  proof.  It is deliberately a *separate* statement: the signature of
  `RBM.SumZeroDyn.LKDecay` is frozen (19 declarations depend on it).
* `RBM.LKDecayQuant.lemma514_flow_of_flowInputs` — the check that the result really fills
  the `hdec` slot of `RBM.SumZeroDyn.lemma514_flow'`.

## Deviations

* Obligation (3) is a hypothesis, not a theorem (T130).
* `FlowInputs` asks for `Φ_N √(ε_N) ≤ N^{-D'}` for every `D' > 0`.  This is what (2.76)
  supplies at the radius `ℓ_u N^{τ/2}`: the profile `exp(-(|a-b|/ℓ_u)^{1/2}) + W^{-D''}`
  is `≤ exp(-N^{τ/4}) + W^{-D''}` there, and `Φ` is a power of `N`.
* The radius convention is the repository's `ℓ_u N^τ` rather than the paper's `ℓ_u W^τ`
  (already recorded in `docs/paper-deltas.md` #78).
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

/-- **The radius of Lemma 5.9 beats the target radius.**  With the (2.76) radius
`ℓ = ℓ_u N^{τ/2}`, the radius `2m(ℓ + 2)` of `RBM.Decay.lemma59` is at most `ℓ_u N^τ` as
soon as `6m ≤ N^{τ/2}`. -/
theorem radius_le {ell A T : ℝ} {m : ℕ} (hell : 1 ≤ ell) (hA : 1 ≤ A)
    (hT : T = A * A) (hm : 6 * (m : ℝ) ≤ A) :
    2 * (m : ℝ) * (ell * A + 2) ≤ ell * T := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [mul_le_mul hell hA (by linarith : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ ell)]

/-! ### Obligation (2): the error -/

theorem term1_le {Φ ε M C : ℝ} {m N : ℕ} {D : ℝ}
    (hΦ0 : 0 ≤ Φ) (hM0 : 0 ≤ M) (hC0 : 0 ≤ C)
    (hN0 : (0 : ℝ) < (N : ℝ))
    (hMC : M ≤ C * (N : ℝ) ^ (2 : ℝ))
    (hΦε : Φ * Real.sqrt ε ≤ (N : ℝ) ^ (-(D + 2 * (m : ℝ) + 1)))
    (hbig : 54 * C ^ m ≤ (N : ℝ)) :
    27 * Φ * Real.sqrt ε * M ^ m ≤ 1 / 2 * (N : ℝ) ^ (-D) := by
  have hpow : M ^ m ≤ C ^ m * (N : ℝ) ^ (2 * (m : ℝ)) := by
    calc M ^ m ≤ (C * (N : ℝ) ^ (2 : ℝ)) ^ m := pow_le_pow_left₀ hM0 hMC m
      _ = C ^ m * ((N : ℝ) ^ (2 : ℝ)) ^ m := mul_pow _ _ _
      _ = C ^ m * (N : ℝ) ^ (2 * (m : ℝ)) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (2 : ℝ)) m, ← Real.rpow_mul hN0.le]
  have hΦε0 : 0 ≤ Φ * Real.sqrt ε := by positivity
  have key : 27 * (Φ * Real.sqrt ε) * M ^ m
      ≤ 27 * ((N : ℝ) ^ (-(D + 2 * (m : ℝ) + 1))) * (C ^ m * (N : ℝ) ^ (2 * (m : ℝ))) := by
    have h1 : (0 : ℝ) ≤ 27 := by norm_num
    refine mul_le_mul (by linarith) hpow (by positivity) (by positivity)
  have hcomb : (N : ℝ) ^ (-(D + 2 * (m : ℝ) + 1)) * (N : ℝ) ^ (2 * (m : ℝ))
      = (N : ℝ) ^ (-D) * (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    ring_nf
  have hinv : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := by
    rw [Real.rpow_neg_one]
  have hCm : (0 : ℝ) ≤ C ^ m := by positivity
  have hfin : 27 * C ^ m * (N : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [mul_inv_le_iff₀ hN0]
    linarith
  calc 27 * Φ * Real.sqrt ε * M ^ m = 27 * (Φ * Real.sqrt ε) * M ^ m := by ring
    _ ≤ 27 * ((N : ℝ) ^ (-(D + 2 * (m : ℝ) + 1))) * (C ^ m * (N : ℝ) ^ (2 * (m : ℝ))) := key
    _ = 27 * C ^ m * ((N : ℝ) ^ (-(D + 2 * (m : ℝ) + 1)) * (N : ℝ) ^ (2 * (m : ℝ))) := by ring
    _ = 27 * C ^ m * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) := by rw [hcomb, hinv]
    _ = (27 * C ^ m * (N : ℝ)⁻¹) * (N : ℝ) ^ (-D) := by ring
    _ ≤ (1 / 2) * (N : ℝ) ^ (-D) :=
        mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hN0.le _)

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

/-- **The event of Lemma 4.1 together with the decay (2.76), at every `u ∈ [s_N, t_N]`.**

This is the shape that T130 (`RBM1D/Gauss/GoodSetFlow.lean`) produces: a single event, not
one per time, carrying at *every* `u ∈ [s_N, t_N]`
* the weak local law `‖G_u - m‖_max ≤ δ_N` (`RBM.GoodEvent`, (4.4)),
* the two large-deviation bounds with constant `Φ_N` (`RBM.LDERow`, `RBM.LDECol`, (4.2)),
* the decay (2.76) of the `(+,-)` two-point function beyond the radius `ℓ_u N^{τ/2}`.

The radius `ℓ_u N^{τ/2}` is the geometric mean of `ℓ_u` and the target radius `ℓ_u N^τ`. -/
def FlowGoodSet (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (gdel Phi eps : ℕ → ℝ) (τ : ℝ)
    (N : ℕ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N,
      GoodEvent (X.G E N (u : ℝ) ω) (mE E) (gdel N)
    ∧ LDERow (X.H N (u : ℝ) ω) (X.G E N (u : ℝ) ω) (Sblk (B.L N) (B.W N)) (Phi N)
    ∧ LDECol (X.H N (u : ℝ) ω) (X.G E N (u : ℝ) ω) (Sblk (B.L N) (B.W N)) (Phi N)
    ∧ ∀ a b : ZMod (B.L N), B.ell N (u : ℝ) * (N : ℝ) ^ (τ / 2) ≤ (zdist (B.L N) (a - b) : ℝ) →
        Lre (X.H N (u : ℝ) ω) (zt E (u : ℝ)) a b ≤ eps N}

/-- **Obligation (3) of `RBM.DecayBridge.lkDecay_of_highProb`, as a hypothesis.**

For every radius exponent `τ > 0` and every error exponent `D' > 0` there are parameters
`δ_N, Φ_N, ε_N` meeting the numerical requirements of `RBM.Decay.lemma59`
(`δ ≤ 1/2`, `Φ ≥ 1`, `36 Φ δ² ≤ 1`) with `Φ_N √(ε_N) ≤ N^{-D'}`, such that
`RBM.LKDecayQuant.FlowGoodSet` holds with high probability.

The smallness `Φ_N √(ε_N) ≤ N^{-D'}` is what (2.76) supplies at the radius `ℓ_u N^{τ/2}`:
there the decay profile `exp(-(|a-b|/ℓ_u)^{1/2}) + W^{-D''}` is at most
`exp(-N^{τ/4}) + W^{-D''}`, super-polynomially small for `D''` large, while `Φ` is a power
of `N`. -/
def FlowInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D' > (0 : ℝ), ∃ gdel Phi eps : ℕ → ℝ,
    (∀ᶠ N : ℕ in atTop, gdel N ≤ 1 / 2 ∧ 1 ≤ Phi N ∧ 36 * Phi N * gdel N ^ 2 ≤ 1
        ∧ 0 ≤ eps N ∧ Phi N * Real.sqrt (eps N) ≤ (N : ℝ) ^ (-D'))
      ∧ HighProb B.P (FlowGoodSet X E s t gdel Phi eps τ)

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- `L_N ≤ N` eventually (from `W L ≤ N` and `W ≥ 1`). -/
theorem eventually_L_le : ∀ᶠ N : ℕ in atTop, (B.L N : ℝ) ≤ (N : ℝ) := by
  filter_upwards [B.dim] with N hN
  have h : B.L N ≤ B.W N * B.L N := Nat.le_mul_of_pos_left _ (B.W_pos N)
  exact_mod_cast h.trans hN.1

/-- **The pathwise conclusion of Lemma 5.9 at `(m, τ, D)`, with high probability**, for
*both* `L` and `L - K`.  This is obligations (1) and (2) discharged; (3) is `FlowInputs`. -/
theorem highProb_loopDecay_pair (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : FlowInputs X E s t) {m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D) :
    HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
        Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
            (fun I => X.Lval E N (u : ℝ) ω I)
      ∧ Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
            (fun I => X.Lval E N (u : ℝ) ω I - B.Kval E N (u : ℝ) I)}) := by
  classical
  set CE : ℝ := max 1 ((mE E).im)⁻¹ with hCEdef
  have hCE1 : (1 : ℝ) ≤ CE := le_max_left _ _
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨gdel, Phi, eps, hnum, hhp⟩ := h τ hτ (D + 2 * (m : ℝ) + 1) (by positivity)
  refine hhp.mono ?_
  have h6m : ∀ᶠ N : ℕ in atTop, 6 * (m : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by
    filter_upwards [SumZeroDyn.eventually_const_mul_rpow_le (6 * (m : ℝ))
      (show (0 : ℝ) < τ / 2 by linarith)] with N hN
    simpa using hN
  have hCEb : ∀ᶠ N : ℕ in atTop, 54 * CE ^ m ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hexp := SumZeroDyn.eventually_exp_small (2 * cKbound m)
    (((2 * cKexp m : ℕ) : ℝ) + D) (cZero / 2) (by have := cZero_pos; linarith)
    (show (0 : ℝ) < τ / 2 by linarith)
  filter_upwards [hnum, eventually_L_le (B := B), h6m, hCEb, hexp, eventually_ge_atTop 1]
    with N hnumN hLN h6mN hCEbN hexpN hN1
  obtain ⟨hgd, hPhi1, hPhid, heps0, hPhieps⟩ := hnumN
  intro ω hω u
  obtain ⟨hΩ, hLrow, hLcol, hdec⟩ := hω u
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hA1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := by
    calc (1 : ℝ) = (N : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
  set uu : ℝ := (u : ℝ) with huu
  have hu0 : 0 ≤ uu := le_trans (hs0 N) u.2.1
  have hu1 : uu < 1 := lt_of_le_of_lt u.2.2 (ht1 N)
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hL0 : (0 : ℝ) < (B.L N : ℝ) := by exact_mod_cast (by omega : 0 < B.L N)
  by_cases hcut : 1 ≤ (B.L N : ℝ) * Real.sqrt (1 - uu)
  · -- the cut-off in `ℓ̂` is inactive: `ℓ_u √(1-u) = 1`
    have hell : B.ell N uu * Real.sqrt (1 - uu) = 1 :=
      ellHat_mul_sqrt_eq_one _ hu1 hcut
    have hsqrt0 : 0 < Real.sqrt (1 - uu) := Real.sqrt_pos.2 (by linarith)
    have hell1 : (1 : ℝ) ≤ B.ell N uu :=
      one_le_ellHat_of_nonneg (by omega : 1 ≤ B.L N) hu0 hu1
    have hell0 : 0 < B.ell N uu := lt_of_lt_of_le one_pos hell1
    -- `1 - u ≥ N^{-2}`
    have hsqN : 1 / (N : ℝ) ≤ Real.sqrt (1 - uu) := by
      rw [div_le_iff₀ hNr]
      nlinarith
    have hv0 : (0 : ℝ) < 1 - uu := by linarith
    have hv1 : (1 : ℝ) - uu ≤ 1 := by linarith
    have hvN : 1 / (1 - uu) ≤ (N : ℝ) ^ 2 := by
      have hsq : Real.sqrt (1 - uu) * Real.sqrt (1 - uu) = 1 - uu :=
        Real.mul_self_sqrt (by linarith)
      have hm2 : 1 / (N : ℝ) * (1 / (N : ℝ)) ≤ 1 - uu := by
        rw [← hsq]
        exact mul_le_mul hsqN hsqN (by positivity) (Real.sqrt_nonneg _)
      rw [div_le_iff₀ hv0]
      calc (1 : ℝ) = (N : ℝ) ^ 2 * (1 / (N : ℝ) * (1 / (N : ℝ))) := by field_simp
        _ ≤ (N : ℝ) ^ 2 * (1 - uu) := mul_le_mul_of_nonneg_left hm2 (by positivity)
    -- the spectral parameter
    have hzim : (zt E uu).im = (1 - uu) * (mE E).im := zt_im E uu
    have hmim : 0 < (mE E).im := mE_im_pos hE
    have hz : (zt E uu).im ≠ 0 := by rw [hzim]; positivity
    -- apply Lemma 5.9
    have h59 := Decay.lemma59 (B.L N) hL3 (X.hermitian N uu ω) hz (norm_mE hE.le) hΩ hgd
      hPhi1 hPhid hLrow hLcol (by positivity) heps0 hdec
      (fun σ => (norm_mSigma hE.le σ).le) hu0 hu1 hm
    -- obligation (1)
    have hT : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
      rw [← Real.rpow_add hNr]; ring_nf
    have hR : 2 * (m : ℝ) * (B.ell N uu * (N : ℝ) ^ (τ / 2) + 2)
        ≤ B.ell N uu * (N : ℝ) ^ τ := radius_le hell1 hA1 hT h6mN
    -- obligation (2), the `L` term
    have hMC : max 1 |(zt E uu).im|⁻¹ ≤ CE * (N : ℝ) ^ (2 : ℝ) := by
      have hr2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hr2]
      refine max_le ?_ ?_
      · nlinarith [sq_nonneg ((N : ℝ) - 1)]
      · have habs : |(zt E uu).im| = (1 - uu) * (mE E).im := by
          rw [hzim, abs_of_pos (by positivity)]
        rw [habs, mul_inv]
        have h1 : (1 - uu)⁻¹ ≤ (N : ℝ) ^ 2 := by rw [← one_div]; exact hvN
        have h2 : ((mE E).im)⁻¹ ≤ CE := le_max_right _ _
        have h3 : (0 : ℝ) ≤ (1 - uu)⁻¹ := by positivity
        have h4 : (0 : ℝ) ≤ ((mE E).im)⁻¹ := by positivity
        calc (1 - uu)⁻¹ * ((mE E).im)⁻¹ ≤ (N : ℝ) ^ 2 * CE :=
              mul_le_mul h1 h2 h4 (by positivity)
          _ = CE * (N : ℝ) ^ 2 := by ring
    have hterm1 : 27 * Phi N * Real.sqrt (eps N) * max 1 |(zt E uu).im|⁻¹ ^ m
        ≤ 1 / 2 * (N : ℝ) ^ (-D) :=
      term1_le (by linarith) (le_trans zero_le_one (le_max_left _ _))
        (by linarith) hNr hMC hPhieps hCEbN
    -- obligation (2), the `K` term
    have hexpo : cZero / 2 * (N : ℝ) ^ (τ / 2)
        ≤ cor35Rate (1 - uu) * (2 * (m : ℝ) * (B.ell N uu * (N : ℝ) ^ (τ / 2) + 2)) := by
      have hid : cor35Rate (1 - uu) * (2 * (m : ℝ) * (B.ell N uu * (N : ℝ) ^ (τ / 2) + 2))
          = cZero * (m : ℝ) * (N : ℝ) ^ (τ / 2) * (B.ell N uu * Real.sqrt (1 - uu)) / 2
            + cZero * (m : ℝ) * Real.sqrt (1 - uu) := by
        unfold cor35Rate; ring
      rw [hid, hell]
      have hc0 := cZero_pos
      nlinarith [mul_nonneg (mul_nonneg hc0.le (sub_nonneg.2 hmr))
          (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2)),
        mul_nonneg (mul_nonneg hc0.le (by linarith : (0 : ℝ) ≤ (m : ℝ))) hsqrt0.le]
    have hterm2 : Decay.cKdecay m (1 - uu)
        * exp (-(cor35Rate (1 - uu) * (2 * (m : ℝ) * (B.ell N uu * (N : ℝ) ^ (τ / 2) + 2))))
        ≤ 1 / 2 * (N : ℝ) ^ (-D) :=
      term2_le hNr hv0 hv1 hvN hexpo hexpN
    have hrp : (0 : ℝ) ≤ (N : ℝ) ^ (-D) := Real.rpow_nonneg hNr.le _
    refine ⟨h59.1.mono (B.L N) le_rfl hR (by linarith), h59.2.mono (B.L N) le_rfl hR ?_⟩
    linarith
  · -- the cut-off is active: `ℓ_u = L`, and the target radius already exceeds `L/2`
    push Not at hcut
    have hellL : B.ell N uu = (B.L N : ℝ) := ellHat_eq_L _ hu1 hcut
    have hhalf : (B.L N : ℝ) / 2 < B.ell N uu * (N : ℝ) ^ τ := by
      have hNt : (1 : ℝ) ≤ (N : ℝ) ^ τ := by
        calc (1 : ℝ) = (N : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
          _ ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hNr1 hτ.le
      rw [hellL]
      nlinarith
    exact ⟨loopDecay_of_half_lt hhalf _, loopDecay_of_half_lt hhalf _⟩

end Flow

/-! ### The two conclusions -/

section Conclusions

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.SumZeroDyn.LKDecay`, unconditional modulo `RBM.LKDecayQuant.FlowInputs`.**

The `(u, τ, D)` decay of `L - K` at every loop length, uniformly in `u ∈ [s_N, t_N]`: the
`|L - K|` half of the paper's (5.75). -/
theorem lkDecay_of_flowInputs (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : FlowInputs X E s t) : SumZeroDyn.LKDecay X E s t :=
  DecayBridge.lkDecay_of_highProb fun _m hm _τ hτ _D hD =>
    (highProb_loopDecay_pair hE hs0 ht1 h hm hτ hD).mono
      (Filter.Eventually.of_forall fun _ _ hω u => (hω u).2)

/-- **The `|L|` half of (5.75)**, which `RBM.SumZeroDyn.LKDecay` drops
(`docs/paper-deltas.md` #78): `|L_{u,σ,a}| ≺ N^{-D}` once two of the labels are at distance
`≥ ℓ_u N^τ`, uniformly in `u ∈ [s_N, t_N]`.

This is a *separate* statement, not a strengthening of `RBM.SumZeroDyn.LKDecay`, whose
signature is frozen (19 declarations depend on it). -/
def LDecay (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ m, 1 ≤ m → ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω =>
      ‖X.Lval E N p.1 ω p.2.idx‖
        * SumZeroDyn.farInd (B.L N) (B.ell N p.1 * (N : ℝ) ^ τ) p.2.2)
    (fun N _ _ => (N : ℝ) ^ (-D))

/-- The pathwise content of the `|L|` half at the parameters `(m, τ, D)`; the analogue of
`RBM.DecayBridge.LKDecayEvent`. -/
def LDecayEvent (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (m : ℕ) (τ D : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N, Decay.LoopDecay (B.L N) m (B.ell N (u : ℝ) * (N : ℝ) ^ τ)
        ((N : ℝ) ^ (-D)) (fun I => X.Lval E N (u : ℝ) ω I)}

/-- The lift "pathwise `|L|` decay w.h.p. ⟹ `LDecay`"; the analogue of
`RBM.DecayBridge.lkDecay_of_highProb`, by the same proof. -/
theorem lDecay_of_highProb
    (h : ∀ m, 1 ≤ m → ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ),
      HighProb B.P (LDecayEvent X E s t m τ D)) :
    LDecay X E s t := by
  intro m hm τ hτ D hD
  refine Step1.stochDom_of_highProb (fun N _ _ => Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_
  refine (h m hm τ hτ D hD).mono (Filter.Eventually.of_forall fun N ω hω => ?_)
  intro p
  exact DecayBridge.farInd_mul_le_of_loopDecay
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hω p.1) p.2

/-- **The `|L|` half of (5.75), unconditional modulo `RBM.LKDecayQuant.FlowInputs`** — the
same proof as `RBM.LKDecayQuant.lkDecay_of_flowInputs`, reading off the other component of
`RBM.Decay.lemma59`. -/
theorem lDecay_of_flowInputs (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h : FlowInputs X E s t) : LDecay X E s t :=
  lDecay_of_highProb fun _m hm _τ hτ _D hD =>
    (highProb_loopDecay_pair hE hs0 ht1 h hm hτ hD).mono
      (Filter.Eventually.of_forall fun _ _ hω u => (hω u).1)

end Conclusions

section Plug

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.LKDecayQuant.lkDecay_of_flowInputs` fills the `hdec` slot of Lemma 5.14.**  The
placeholder for Lemma 5.9 in `RBM.SumZeroDyn.lemma514_flow'` is discharged verbatim — no
`convert`, no coercion — so every consumer of `RBM.SumZeroDyn.LKDecay` now runs off
`FlowInputs` alone. -/
theorem lemma514_flow_of_flowInputs {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hLmK : ∀ m : ℕ, 1 ≤ m → StochDom B.P
      (fun N (w : LoopData (B.L N) m) ω => X.lkErr E N (s N) ω w.idx)
      (fun N _ _ => (B.scale E N (s N))⁻¹ ^ m))
    (H : ∀ n, SumZeroDyn.Hierarchy X E s t n)
    (h510 : ∀ n, SumZeroDyn.Lemma510 X E s t (H n))
    (hfi : FlowInputs X E s t) :
    ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n :=
  SumZeroDyn.lemma514_flow' X hκ0 hκ1 hEκ hs0 hst ht1 hc hLmK H h510
    (lkDecay_of_flowInputs (by linarith) (fun N => (hs0 N).le) ht1 hfi)

end Plug

end LKDecayQuant

end RBM
