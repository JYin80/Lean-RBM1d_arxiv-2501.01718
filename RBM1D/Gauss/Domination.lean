/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.StochDom
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# From moment bounds to stochastic domination, and the time net

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.1 (i) and the time net
used at (5.46).

This file is the bridge between the **moment route** for the random layer (the flow is
`H_u := √u • X` and all bounds are proved for moments, never for paths) and the paper's
stochastic domination `≺` (`RBM.StochDom`, `RBM1D/Defs/StochDom.lean`).

## The two steps

1. **Moments ⟹ `≺`** (Markov / Chebyshev).  `RBM.Gauss.MomentDom P Y Φ` is the moment input
   ```
   ∀ ε > 0, ∀ p : ℕ, ∃ C > 0, eventually in N, ∀ u,   E |Y(N,u)|^{2p} ≤ C N^{εp} Φ(N,u)^{2p}.
   ```
   The order of the quantifiers matters: `ε` is **outside** `p`, so `ε` may be taken arbitrarily
   small for each fixed `p`; this is exactly what is needed to beat the `N^τ` of Definition
   2.1 (i).  `RBM.Gauss.stochDom_of_momentDom` turns this, together with a polynomial bound on
   `#U(N)`, into `RBM.StochDom P Y Φ`; `RBM.Gauss.stochDom_one_of_momentDom` is the case `Φ = 1`.

2. **The time net of (5.46).**  Definition 2.1 (i) puts an *uncountable* union over
   `u ∈ [0, T]` inside the probability; the net of (5.46) reduces it to a union over the
   `⌈N^A⌉₊ + 1` subintervals of `[0, T]`.  Every point of `[0, T]` is within `T / netSize A N`
   of a net point (`RBM.Gauss.exists_netPt_close`), and for `A ≥ 0` the net has at most
   `N^{A+1}` points eventually (`RBM.Gauss.card_net_le`), so the union bound
   `RBM.StochDom.of_forall_le` applies on it.

## Main definitions

* `RBM.Gauss.MomentDom P Y Φ` — the moment input of step 1.
* `RBM.Gauss.netSize`, `RBM.Gauss.netPt` — the uniform net on `[0, T]` of step 2.

## Main results

* `RBM.Gauss.meas_gt_le_of_moment` — Markov/Chebyshev at a single scale.
* `RBM.Gauss.stochDom_of_momentDom` — moments `⟹ ≺`, relative to a deterministic control `Φ`.
* `RBM.Gauss.stochDom_one_of_momentDom` — the case `Φ = 1`, i.e. `Y ≺ 1`.
* `RBM.Gauss.exists_netPt_close`, `RBM.Gauss.card_net_le` — the mesh and the cardinality of
  the time net.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Step 1: Markov's inequality -/

section Markov

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- **Markov / Chebyshev at a single scale.**  A bound `M` on the `2p`-th moment of `Y` gives
`P(Y > t) ≤ M / t^{2p}` for every threshold `t > 0`. -/
theorem meas_gt_le_of_moment {Y : Ω → ℝ} {p : ℕ} {t M : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * p)) P)
    (hM : ∫ ω, |Y ω| ^ (2 * p) ∂P ≤ M) :
    P {ω | t < Y ω} ≤ ENNReal.ofReal (M / t ^ (2 * p)) := by
  have hnn : 0 ≤ᵐ[P] fun ω => |Y ω| ^ (2 * p) :=
    Filter.Eventually.of_forall fun ω => by positivity
  have htp : (0 : ℝ) < t ^ (2 * p) := by positivity
  -- the failure event sits inside the level set of the `2p`-th power
  have hsub : {ω | t < Y ω} ⊆ {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact pow_le_pow_left₀ ht.le ((le_abs_self (Y ω)).trans' hω.le) _
  -- Markov
  have hmark := mul_meas_ge_le_integral_of_nonneg hnn hint (t ^ (2 * p))
  have hreal : P.real {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} ≤ M / t ^ (2 * p) := by
    rw [le_div_iff₀ htp, mul_comm]
    exact hmark.trans hM
  calc P {ω | t < Y ω} ≤ P {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
    _ ≤ ENNReal.ofReal (M / t ^ (2 * p)) := ENNReal.ofReal_le_ofReal hreal

/-- **The moment input.**  For every `ε > 0` and every `p`, the `2p`-th moment of `Y(N,u)` is
bounded by `C_{ε,p} · N^{εp} · Φ(N,u)^{2p}`, eventually in `N` and uniformly in `u ∈ U(N)`.

`ε` is quantified *outside* `p`, so it may be taken arbitrarily small for each fixed `p`; this is
what makes `RBM.Gauss.stochDom_of_momentDom` work for every `τ > 0`. -/
def MomentDom {U : ℕ → Type*} (Y : ∀ N, U N → Ω → ℝ) (Φ : ∀ N, U N → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u,
    ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))

variable {P}

/-- **Moments imply stochastic domination.**  If all moments of `Y` are bounded relative to a
positive deterministic control `Φ` in the sense of `MomentDom`, and `#U(N)` is polynomially
bounded, then `Y ≺ Φ` in the sense of Definition 2.1 (i). -/
theorem stochDom_of_momentDom {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {Y : ∀ N, U N → Ω → ℝ} {Φ : ∀ N, U N → ℝ} (hΦ : ∀ N u, 0 < Φ N u)
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P Y Φ) :
    StochDom P Y (fun N u _ => Φ N u) := by
  refine StochDom.of_forall_le hcard ?_
  intro τ hτ D hD
  obtain ⟨p, hp⟩ := exists_nat_ge ((D + 1) / τ)
  have hDp : D + 1 ≤ τ * (p : ℝ) := by
    rw [div_le_iff₀ hτ] at hp; linarith
  obtain ⟨C, hC0, hCN⟩ := hmom τ hτ p
  have hexp : 0 < τ * (p : ℝ) - D := by linarith
  filter_upwards [hCN, eventually_ge_atTop 1, eventually_le_rpow C hexp] with N hN hN1 hCle u
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hΦu := hΦ N u
  have hrp : (0 : ℝ) < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hNpos τ
  have ht : 0 < (N : ℝ) ^ τ * Φ N u := mul_pos hrp hΦu
  refine (meas_gt_le_of_moment P ht (hint p N u) (hN u)).trans (ENNReal.ofReal_le_ofReal ?_)
  set a : ℝ := (N : ℝ) ^ (τ * (p : ℝ)) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hb : (0 : ℝ) < Φ N u ^ (2 * p) := by positivity
  have h1 : ((N : ℝ) ^ τ * Φ N u) ^ (2 * p) = a * a * Φ N u ^ (2 * p) := by
    rw [mul_pow, ha_def, ← Real.rpow_natCast ((N : ℝ) ^ τ) (2 * p), ← Real.rpow_mul hNpos.le,
      ← Real.rpow_add hNpos]
    push_cast
    ring_nf
  have h2 : C * (a * Φ N u ^ (2 * p)) / (a * a * Φ N u ^ (2 * p)) = C * a⁻¹ := by
    field_simp
  have h3 : a⁻¹ = (N : ℝ) ^ (-(τ * (p : ℝ))) := by
    rw [ha_def, Real.rpow_neg hNpos.le]
  rw [h1, h2]
  calc C * a⁻¹ ≤ (N : ℝ) ^ (τ * (p : ℝ) - D) * a⁻¹ :=
        mul_le_mul_of_nonneg_right hCle (inv_nonneg.2 ha.le)
    _ = (N : ℝ) ^ (-D) := by
        rw [h3, ← Real.rpow_add hNpos]
        congr 1
        ring

/-- **Moments imply `Y ≺ 1`**: the case `Φ = 1` of `stochDom_of_momentDom`. -/
theorem stochDom_one_of_momentDom {U : ℕ → Type*} [∀ N, Fintype (U N)] {Ccard : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (U N) : ℝ) ≤ (N : ℝ) ^ Ccard)
    {Y : ∀ N, U N → Ω → ℝ}
    (hint : ∀ (p N : ℕ) (u : U N), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u,
      ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * (N : ℝ) ^ (ε * p)) :
    StochDom P Y (fun _ _ _ => (1 : ℝ)) := by
  refine stochDom_of_momentDom hcard (Φ := fun _ _ => (1 : ℝ)) (fun _ _ => one_pos) hint ?_
  intro ε hε p
  obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hCN] with N hN u
  simpa using hN u

end Markov

/-! ### Step 2: the time net -/

section Net

/-- The number of subintervals of the time net on `[0, T]`: `⌈N^A⌉₊ + 1` (the `+1` keeps it
positive for every `N` and every `A`). -/
noncomputable def netSize (A : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) ^ A⌉₊ + 1

theorem netSize_pos (A : ℝ) (N : ℕ) : 0 < netSize A N := Nat.succ_pos _

theorem rpow_le_netSize (A : ℝ) (N : ℕ) : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := by
  have := Nat.le_ceil ((N : ℝ) ^ A)
  have h : ((⌈(N : ℝ) ^ A⌉₊ : ℝ)) ≤ (netSize A N : ℝ) := by
    unfold netSize; push_cast; linarith
  linarith

/-- The `k`-th point `k T / m` of the uniform net with `m = netSize A N` subintervals
on `[0, T]`. -/
noncomputable def netPt (T A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  (k : ℝ) * T / (netSize A N : ℝ)

theorem netPt_mem_Icc {T : ℝ} (hT : 0 ≤ T) (A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) :
    netPt T A N k ∈ Set.Icc (0 : ℝ) T := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hk : (k : ℝ) ≤ (netSize A N : ℝ) := by
    have : (k : ℕ) ≤ netSize A N := Nat.lt_succ_iff.1 k.isLt
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  constructor
  · simp only [netPt]
    exact div_nonneg (mul_nonneg hk0 hT) hm.le
  · simp only [netPt]
    rw [div_le_iff₀ hm]
    nlinarith

/-- Every point of `[0, T]` is within `T / netSize A N` of a net point. -/
theorem exists_netPt_close {T : ℝ} (hT : 0 < T) (A : ℝ) (N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) T) :
    ∃ k : Fin (netSize A N + 1), |u - netPt T A N k| ≤ T / (netSize A N : ℝ) := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hx0 : 0 ≤ u * (netSize A N : ℝ) / T := div_nonneg (mul_nonneg hu.1 hm.le) hT.le
  have hxm : u * (netSize A N : ℝ) / T ≤ (netSize A N : ℝ) := by
    rw [div_le_iff₀ hT]
    nlinarith [hu.2, hm.le]
  have hkm : ⌊u * (netSize A N : ℝ) / T⌋₊ ≤ netSize A N := Nat.floor_le_of_le hxm
  have hfl : ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) ≤ u * (netSize A N : ℝ) / T :=
    Nat.floor_le hx0
  have hfu : u * (netSize A N : ℝ) / T < ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨⟨⌊u * (netSize A N : ℝ) / T⌋₊, Nat.lt_succ_of_le hkm⟩, ?_⟩
  have hnet : netPt T A N ⟨⌊u * (netSize A N : ℝ) / T⌋₊, Nat.lt_succ_of_le hkm⟩
      = ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := rfl
  have hkey : (u * (netSize A N : ℝ) / T - ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ))
      * (T / (netSize A N : ℝ))
      = u - ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := by
    field_simp
  rw [hnet, ← hkey,
    abs_of_nonneg (mul_nonneg (by linarith) (div_pos hT hm).le)]
  exact mul_le_of_le_one_left (div_pos hT hm).le (by linarith)

theorem card_net_le {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (Fin (netSize A N + 1)) : ℝ) ≤ (N : ℝ) ^ (A + 1) := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ A := Real.one_le_rpow hN1 hA
  have hceil : ((⌈(N : ℝ) ^ A⌉₊ : ℝ)) < (N : ℝ) ^ A + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcard : (Fintype.card (Fin (netSize A N + 1)) : ℝ) = (⌈(N : ℝ) ^ A⌉₊ : ℝ) + 2 := by
    rw [Fintype.card_fin, netSize]; push_cast; ring
  have hrpow : (N : ℝ) ^ (A + 1) = (N : ℝ) ^ A * (N : ℝ) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  rw [hcard, hrpow]
  nlinarith

end Net

/-! ### Step 2: `≺` uniformly in a continuous time parameter -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

end Uniform

end RBM.Gauss


