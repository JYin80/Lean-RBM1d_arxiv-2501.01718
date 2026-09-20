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

2. **`≺` uniformly in a continuous time parameter `u ∈ [0, T]`.**  Definition 2.1 (i) puts an
   *uncountable* union inside the probability.  `RBM.Gauss.stochDom_Icc_of_holder` removes it
   by the net of (5.46): the `⌈N^A⌉₊ + 1` subintervals of `[0, T]` with `A := (K + B + 1)/γ`,
   where `N^K |u − u'|^γ` is a **deterministic** modulus of continuity of `u ↦ Y(N,u,ω)` and
   `N^{-B}` a lower bound for the control `Φ(N)`.  On the net one uses step 1 and the union
   bound `RBM.StochDom.of_forall_le`; between net points the modulus moves the failure event by
   at most `N^{τ/2} Φ(N)`, which is absorbed in the `N^τ` of Definition 2.1 (i).

The modulus of continuity is an explicit hypothesis (`hHol` below), in the shape
`|Y(N,u,ω) − Y(N,u',ω)| ≤ N^K |u − u'|^γ` for `u, u' ∈ [0,T]`, valid for **every** `ω`
(no exceptional set): that is what the flow `H_u = √u • X` provides.  The exponent `γ` is kept
general because `‖H_u − H_{u'}‖ = |√u − √u'| ‖X‖` is only `1/2`-Hölder at `u = 0`, not Lipschitz;
`RBM.Gauss.stochDom_Icc_of_lipschitz` is the special case `γ = 1`.

## Main definitions

* `RBM.Gauss.MomentDom P Y Φ` — the moment input of step 1.
* `RBM.Gauss.netSize`, `RBM.Gauss.netPt` — the uniform net on `[0, T]` of step 2.

## Main results

* `RBM.Gauss.meas_gt_le_of_moment` — Markov/Chebyshev at a single scale.
* `RBM.Gauss.stochDom_of_momentDom` — moments `⟹ ≺`, relative to a deterministic control `Φ`.
* `RBM.Gauss.stochDom_one_of_momentDom` — the case `Φ = 1`, i.e. `Y ≺ 1`.
* `RBM.Gauss.stochDom_Icc_of_holder` — `≺` uniformly in `u ∈ [0, T]`, with the uncountable
  union of Definition 2.1 (i) intact; `RBM.Gauss.stochDom_Icc_of_lipschitz` is the case `γ = 1`.
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

/-- **Definition 2.1 (i) with the uncountable union intact.**

Let `Y(N, u, ω)` be defined for `u` in the interval `[0, T]`, let `Φ(N) > 0` be a deterministic
control that is not super-polynomially small (`N^{-B} ≤ Φ(N)` eventually), and assume

* a **deterministic** modulus of continuity
  `|Y(N,u,ω) − Y(N,u',ω)| ≤ N^K |u − u'|^γ`, valid for every `ω` (no exceptional set) and all
  `u, u' ∈ [0, T]`;
* the moment bound `MomentDom` relative to `Φ`, uniformly in `u ∈ [0, T]`.

Then `Y ≺ Φ` in the sense of Definition 2.1 (i), i.e. the *union over all* `u ∈ [0, T]` of the
failure events has probability `≤ N^{-D}`.

The proof is the net of (5.46): `⌈N^{(K+B+1)/γ}⌉₊ + 1` subintervals, `stochDom_of_momentDom` plus
the union bound `RBM.StochDom.of_forall_le` on the net, and the modulus of continuity in between.

The Hölder exponent `γ` is kept general (rather than fixing `γ = 1`) because the flow
`H_u = √u • X` gives `‖H_u − H_{u'}‖ = |√u − √u'| ‖X‖`, which is Lipschitz only away from
`u = 0`; on `[0, T]` it is `1/2`-Hölder.  See `stochDom_Icc_of_lipschitz` for `γ = 1`. -/
theorem stochDom_Icc_of_holder {T : ℝ} (hT : 0 < T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hγ : 0 < γ) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    (hHol : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1 on the net
  have hnet : StochDom P (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω => Y N (netPt T A N k) ω)
      (fun N _ _ => Φ N) := by
    refine stochDom_of_momentDom (card_net_le hA) (Φ := fun N _ => Φ N) (fun N _ => hΦ N)
      (fun p N k => hint p N _) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hCN] with N hN k
    exact hN ⟨netPt T A N k, netPt_mem_Icc hT.le A N k⟩
  -- step 2: transfer from the net to the whole interval
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  have hsub : ∀ᶠ N : ℕ in atTop,
      badSet (U := fun _ => ↥(Set.Icc (0 : ℝ) T)) (fun N u ω => Y N (u : ℝ) ω)
        (fun N _ _ => Φ N) τ N ⊆
      badSet (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω => Y N (netPt T A N k) ω)
        (fun N _ _ => Φ N) (τ / 2) N := by
    filter_upwards [hΦlow, eventually_ge_atTop 1, eventually_le_rpow 2 hτ2,
      eventually_le_rpow (T ^ γ) one_pos] with N hΦN hN1 hN2 hNT
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hTN : T ^ γ ≤ (N : ℝ) := by rwa [Real.rpow_one] at hNT
    have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
    have hmge : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := rpow_le_netSize A N
    have hNA : (0 : ℝ) < (N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
    have hr2 : (0 : ℝ) < (N : ℝ) ^ (τ / 2) := Real.rpow_pos_of_pos hNpos _
    -- the net error is at most `N^{τ/2} Φ(N)`
    have herr : (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
      have hstep1 : T / (netSize A N : ℝ) ≤ T / (N : ℝ) ^ A :=
        div_le_div_of_nonneg_left hT.le hNA hmge
      have hstep1' : (T / (netSize A N : ℝ)) ^ γ ≤ (T / (N : ℝ) ^ A) ^ γ :=
        Real.rpow_le_rpow (div_pos hT hm).le hstep1 hγ.le
      have hKpos : (0 : ℝ) < (N : ℝ) ^ K := Real.rpow_pos_of_pos hNpos K
      have hstep2 : (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ
          ≤ (N : ℝ) ^ K * (T / (N : ℝ) ^ A) ^ γ :=
        mul_le_mul_of_nonneg_left hstep1' hKpos.le
      have hpowA : ((N : ℝ) ^ A) ^ γ = (N : ℝ) ^ (K + B + 1) := by
        rw [← Real.rpow_mul hNpos.le, hAγ]
      have hdiv : (T / (N : ℝ) ^ A) ^ γ = T ^ γ / (N : ℝ) ^ (K + B + 1) := by
        rw [Real.div_rpow hT.le hNA.le, hpowA]
      have hexp : K - (K + B + 1) = -B + -1 := by ring
      have hKA : (N : ℝ) ^ K / (N : ℝ) ^ (K + B + 1) = (N : ℝ) ^ (-B) * (N : ℝ)⁻¹ := by
        rw [← Real.rpow_sub hNpos, ← Real.rpow_neg_one (N : ℝ), ← Real.rpow_add hNpos, hexp]
      have hstep3 : (N : ℝ) ^ K * (T / (N : ℝ) ^ A) ^ γ
          = T ^ γ * ((N : ℝ) ^ (-B) * (N : ℝ)⁻¹) := by
        rw [hdiv, ← hKA]; ring
      have hinvn : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
      have hstep4 : T ^ γ * ((N : ℝ) ^ (-B) * (N : ℝ)⁻¹) ≤ T ^ γ * (Φ N * (N : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦN hinvn) hTγ.le
      have hstep5 : T ^ γ * (Φ N * (N : ℝ)⁻¹) ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
        have hTinv : T ^ γ * (N : ℝ)⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ hNpos, one_mul]; exact hTN
        have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hNge1 hτ2.le
        have heq : T ^ γ * (Φ N * (N : ℝ)⁻¹) = (T ^ γ * (N : ℝ)⁻¹) * Φ N := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (hTinv.trans h1) (hΦ N).le
      linarith
    -- and `N^τ ≥ 2 N^{τ/2}`
    have hdouble : 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by
      have heq := UnifDetDom.rpow_half_mul_rpow_half N hτ
      nlinarith [hr2.le]
    rintro ω ⟨u, hu⟩
    obtain ⟨k, hk⟩ := exists_netPt_close hT A N u.2
    refine ⟨k, ?_⟩
    have hhol := hHol N ω u.1 u.2 (netPt T A N k) (netPt_mem_Icc hT.le A N k)
    have hle : |Y N u.1 ω - Y N (netPt T A N k) ω| ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
      refine hhol.trans (le_trans ?_ herr)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
        (Real.rpow_pos_of_pos hNpos K).le
    have hdiff : Y N u.1 ω - Y N (netPt T A N k) ω ≤ (N : ℝ) ^ (τ / 2) * Φ N :=
      (le_abs_self _).trans hle
    have hmul : 2 * (N : ℝ) ^ (τ / 2) * Φ N ≤ (N : ℝ) ^ τ * Φ N :=
      mul_le_mul_of_nonneg_right hdouble (hΦ N).le
    simp only
    linarith
  filter_upwards [hsub, hnet (τ / 2) hτ2 D hD] with N h1 h2
  exact (measure_mono h1).trans h2

/-- **Definition 2.1 (i) with the uncountable union intact**, Lipschitz case: `γ = 1` of
`stochDom_Icc_of_holder`. -/
theorem stochDom_Icc_of_lipschitz {T : ℝ} (hT : 0 < T) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    (hLip : ∀ (N : ℕ) (ω : Ω), ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'|)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) :=
  stochDom_Icc_of_holder hT hK hB one_pos hΦ hΦlow
    (fun N ω u hu u' hu' => by simpa [Real.rpow_one] using hLip N ω u hu u' hu') hint hmom

end Uniform

end RBM.Gauss


