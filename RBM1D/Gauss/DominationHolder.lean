/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Domination
import RBM1D.Flow.Hypotheses

/-!
# The time net with a modulus of continuity that is only valid with high probability

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 2.1 (i) and the time net
of (5.46).

`RBM.Gauss.stochDom_Icc_of_holder` (T73, `RBM1D/Gauss/Domination.lean`) and
`RBM.Step2Moment.stochDom_timeIcc_of_holder` (T75, `RBM1D/Hierarchy/Step2Moment.lean`) both
remove the *uncountable* union over the time `u` of Definition 2.1 (i) by an `N^{-C}` net, and
both demand a **pointwise** Hölder-`γ` modulus of continuity
```
|Y(N,u,ω) − Y(N,u',ω)| ≤ N^K |u − u'|^γ    for every ω, with no exceptional set.
```
That hypothesis is too strong for the Gaussian flow.  The modulus that `RBM1D/Gauss/Model.lean`
supplies is
```
‖H_u − H_{u'}‖ = |√u − √u'| ‖X‖        (`RBM.Gauss.norm_Hflow_sub`),
```
so for a resolvent functional the Hölder constant carries a factor `‖X‖`, which is **not**
bounded pointwise in `ω`: all that is available is `‖X‖ ≺ 1`
(`RBM.Gauss.OpNormBound.norm_X`, the open gap of `docs/paper-deltas.md` #49).

This file proves the variants of the net theorem in which the modulus is allowed to fail on a
null-ish set of `ω`:

* **the high-probability form** — the modulus holds only for `ω ∈ Ξ N`, with `Ξ` a family of
  events of high probability in the sense of Definition 2.1 (iv) (`RBM.HighProb`);
* **the `≺`-controlled-constant form** — the modulus reads
  `|Y(N,u,ω) − Y(N,u',ω)| ≤ N^K · R(N,ω) · |u − u'|^γ` with a *random* constant `R` satisfying
  `R ≺ 1`.

The second reduces to the first: `R ≺ 1` makes `{ω | R(N,ω) ≤ N}` a high-probability event
(`RBM.StochDom.highProb` at `τ = 1`), and on that event `N^K R` is at most `N^{K+1}`, i.e. one
pays a single extra power of `N` in the Hölder constant — which the net absorbs, since the net
size `⌈N^{(K+B+1)/γ}⌉₊ + 1` is polynomial in `N` for every `K`.

Why the weakening is free: the failure event of Definition 2.1 (i) is covered by
```
badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ,
```
the first piece is handled by the net exactly as in T73, and `P(Ξᶜ) ≤ N^{-(D+1)}` by definition
of `HighProb`.  This is `stochDom_of_subset_highProb`, the high-probability analogue of
`RBM.StochDom.of_subset`.

## Generality

The main theorem `stochDom_timeIcc_of_holder_hp` is stated for an **`N`-dependent** time
interval `[s_N, t_N]` of length at most `T`, i.e. at the generality of T75 (T73's fixed `[0,T]`
is the case `s ≡ 0`, `t ≡ T`), with the deterministic control `Φ(N) > 0` of T73 (T75's case
`Φ ≡ 1`).  The four corollaries specialize back:

| | pointwise modulus | modulus w.h.p. | random constant `R ≺ 1` |
|---|---|---|---|
| `[0, T]`, control `Φ` | `stochDom_Icc_of_holder` (T73) | `stochDom_Icc_of_holder_hp` | — |
| `[s_N, t_N]`, control `Φ` | — | `stochDom_timeIcc_of_holder_hp` | `stochDom_timeIcc_of_holder_dom` |
| `[s_N, t_N]`, control `1` | `stochDom_timeIcc_of_holder` (T75) | `stochDom_timeIcc_one_of_holder_hp` | `stochDom_timeIcc_one_of_holder_dom` |

`stochDom_timeIcc_one_of_holder_hp` and `stochDom_timeIcc_one_of_holder_dom` have exactly the
signature of T75's `stochDom_timeIcc_of_holder` apart from the modulus hypothesis, so they are
drop-in replacements for it once the file that hosts it may be edited.

## Main definitions

* `RBM.Gauss.netTime` — the net of (5.46) on the `N`-dependent interval `[s_N, t_N]`: the net
  of `RBM1D/Gauss/Domination.lean` shifted by `s_N` and clipped at `t_N`.  (T75 defines the
  same net inside `RBM1D/Hierarchy/Step2Moment.lean`, where `Gauss/` cannot reach it; this is
  the copy that belongs downstairs.)

## Main results

* `RBM.Gauss.stochDom_of_subset_highProb` — the union bound `badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ`.
* `RBM.Gauss.stochDom_timeIcc_of_holder_hp` — the net theorem with the modulus only on `Ξ`.
* `RBM.Gauss.stochDom_timeIcc_of_holder_dom` — the net theorem with a `≺`-controlled Hölder
  constant.
* `RBM.Gauss.stochDom_Icc_of_holder_hp`, `RBM.Gauss.stochDom_timeIcc_one_of_holder_hp`,
  `RBM.Gauss.stochDom_timeIcc_one_of_holder_dom` — the three specializations.

## What is *not* weakened

The moment hypothesis `hmom` and the integrability hypothesis `hint` remain unconditional (they
are integrals over all of `Ω`, so an exceptional set cannot be discarded there), and the control
`Φ` remains deterministic and independent of `u`, exactly as in T73.  See
`docs/paper-deltas.md` #48.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The union bound with an exceptional event -/

section Core

variable {P : Measure Ω} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
/-- **`RBM.StochDom.of_subset` with an exceptional event.**  If the failure event of `ξ ≺ ζ`
is, *on a high-probability event* `Ξ`, eventually contained in the failure event of a
domination that is already known, then `ξ ≺ ζ`.

The cover is `badSet ⊆ (badSet ∩ Ξ) ∪ Ξᶜ`: the first piece is controlled by the known
domination at the level `D + 1`, the second by `HighProb` at the level `D + 1`, and
`2 N^{-(D+1)} ≤ N^{-D}` (`RBM.eventually_two_mul_rpow_le`). -/
theorem stochDom_of_subset_highProb {U V : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    {ξ' ζ' : ∀ N, V N → Ω → ℝ} {Ξ : ℕ → Set Ω} (h : StochDom P ξ' ζ') (hΞ : HighProb P Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      badSet ξ ζ τ N ∩ Ξ N ⊆ badSet ξ' ζ' τ' N) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    eventually_two_mul_rpow_le D] with N h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcover : badSet ξ ζ τ N ⊆ (badSet ξ ζ τ N ∩ Ξ N) ∪ (Ξ N)ᶜ := by
    intro ω hω
    by_cases hΞω : ω ∈ Ξ N
    · exact Or.inl ⟨hω, hΞω⟩
    · exact Or.inr hΞω
  calc P (badSet ξ ζ τ N) ≤ P ((badSet ξ ζ τ N ∩ Ξ N) ∪ (Ξ N)ᶜ) := measure_mono hcover
    _ ≤ P (badSet ξ ζ τ N ∩ Ξ N) + P (Ξ N)ᶜ := measure_union_le _ _
    _ ≤ P (badSet ξ' ζ' τ' N) + P (Ξ N)ᶜ := add_le_add (measure_mono h0) le_rfl
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

end Core

/-! ### The net of (5.46) on an `N`-dependent interval -/

section Net

/-- The `k`-th point of the uniform net of (5.46) on the **`N`-dependent** interval
`[s_N, t_N]`, whose length is at most `T`.  The net of `RBM1D/Gauss/Domination.lean` lives on a
fixed `[0, T]`; shifting it by `s_N` and clipping at `t_N` keeps it inside `[s_N, t_N]` without
assuming `s_N < t_N`. -/
noncomputable def netTime (s t : ℕ → ℝ) (T A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  min (t N) (s N + netPt T A N k)

theorem netTime_mem {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 ≤ T) (A : ℝ) (N : ℕ)
    (k : Fin (netSize A N + 1)) : netTime s t T A N k ∈ Set.Icc (s N) (t N) := by
  refine ⟨le_min (hst N) ?_, min_le_left _ _⟩
  have := (netPt_mem_Icc hT A N k).1
  linarith

/-- Every time of `[s_N, t_N]` is within `T / m` of a net point, `m = netSize A N`. -/
theorem exists_netTime_close {s t : ℕ → ℝ} {T : ℝ} (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T)
    (A : ℝ) (N : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (s N) (t N)) :
    ∃ k, |u - netTime s t T A N k| ≤ T / (netSize A N : ℝ) := by
  have hmem : u - s N ∈ Set.Icc (0 : ℝ) T :=
    ⟨by linarith [hu.1], by linarith [hu.2, hlen N]⟩
  obtain ⟨k, hk⟩ := exists_netPt_close hT A N hmem
  refine ⟨k, ?_⟩
  have hkq : |u - (s N + netPt T A N k)| ≤ T / (netSize A N : ℝ) := by
    have h : u - (s N + netPt T A N k) = u - s N - netPt T A N k := by ring
    rw [h]; exact hk
  unfold netTime
  rcases le_or_gt (s N + netPt T A N k) (t N) with h | h
  · rwa [min_eq_right h]
  · rw [min_eq_left h.le]
    refine le_trans ?_ hkq
    rw [abs_of_nonpos (by linarith [hu.2]), abs_of_nonpos (by linarith [hu.2])]
    linarith

end Net

/-! ### The net theorem with a modulus valid only with high probability -/

section Uniform

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- **Definition 2.1 (i) with the uncountable union intact, modulus only with high
probability.**

This is `RBM.Gauss.stochDom_Icc_of_holder` (T73) — equivalently
`RBM.Step2Moment.stochDom_timeIcc_of_holder` (T75) — with its *pointwise* Hölder modulus
```
∀ ω, ∀ u u' ∈ [s_N, t_N],  |Y(N,u,ω) − Y(N,u',ω)| ≤ N^K |u − u'|^γ
```
weakened to hold only for `ω` in a family `Ξ` of high-probability events (Definition 2.1 (iv)),
and only eventually in `N`.  Everything else is unchanged: the control `Φ(N) > 0` is
deterministic, independent of `u`, and not super-polynomially small (`N^{-B} ≤ Φ(N)`
eventually), and the moment input is the same unconditional one.

The interval is the `N`-dependent `[s_N, t_N]` of the flow, of length at most `T`; take
`s ≡ 0`, `t ≡ T` for T73's fixed interval (`stochDom_Icc_of_holder_hp`) and `Φ ≡ 1`, `T = 1`
for T75's (`stochDom_timeIcc_one_of_holder_hp`).

The proof is the net of (5.46) — `⌈N^{(K+B+1)/γ}⌉₊ + 1` subintervals, `stochDom_of_momentDom`
on the net — together with `stochDom_of_subset_highProb` in place of `RBM.StochDom.of_subset`:
off `Ξ N` the net argument is simply abandoned, at the cost of `P(Ξᶜ) ≤ N^{-(D+1)}`. -/
theorem stochDom_timeIcc_of_holder_hp {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 < T)
    (hlen : ∀ N, t N - s N ≤ T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ)
    {Y : ℕ → ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ u' ∈ Set.Icc (s N) (t N), |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N),
        ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N ^ (2 * p))) :
    StochDom P (U := fun N => RBM.TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun N _ _ => Φ N) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1 on the net (unconditional: the moment input is unconditional)
  have hnet : StochDom P (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω =>
      Y N (netTime s t T A N k) ω) (fun N _ _ => Φ N) := by
    refine stochDom_of_momentDom (card_net_le hA) (Φ := fun N _ => Φ N) (fun N _ => hΦ N)
      (fun p N k => hint p N _ (netTime_mem hst hT.le A N k)) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    exact ⟨C, hC0, by
      filter_upwards [hCN] with N hN k using hN _ (netTime_mem hst hT.le A N k)⟩
  -- step 2: transfer from the net to the whole interval, on `Ξ`
  refine stochDom_of_subset_highProb hnet hΞ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  filter_upwards [hHol, hΦlow, eventually_ge_atTop 1, eventually_le_rpow 2 hτ2,
    eventually_le_rpow (T ^ γ) one_pos] with N hHolN hΦN hN1 hN2 hNT
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
  rintro ω ⟨⟨u, hu⟩, hωΞ⟩
  obtain ⟨k, hk⟩ := exists_netTime_close hT hlen A N u.2
  refine ⟨k, ?_⟩
  have hhol := hHolN ω hωΞ u.1 u.2 (netTime s t T A N k) (netTime_mem hst hT.le A N k)
  have hle : |Y N u.1 ω - Y N (netTime s t T A N k) ω| ≤ (N : ℝ) ^ (τ / 2) * Φ N := by
    refine hhol.trans (le_trans ?_ herr)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
      (Real.rpow_pos_of_pos hNpos K).le
  have hdiff : Y N u.1 ω - Y N (netTime s t T A N k) ω ≤ (N : ℝ) ^ (τ / 2) * Φ N :=
    (le_abs_self _).trans hle
  have hmul : 2 * (N : ℝ) ^ (τ / 2) * Φ N ≤ (N : ℝ) ^ τ * Φ N :=
    mul_le_mul_of_nonneg_right hdouble (hΦ N).le
  simp only
  linarith

/-- **Definition 2.1 (i) with the uncountable union intact, modulus only with high
probability**, on the fixed interval `[0, T]`.

This is exactly `RBM.Gauss.stochDom_Icc_of_holder` (T73) with `hHol` weakened from "for every
`ω`" to "for `ω` in a high-probability event, eventually in `N`". -/
theorem stochDom_Icc_of_holder_hp {T : ℝ} (hT : 0 < T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hγ : 0 < γ) {Y : ∀ _ : ℕ, ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ u' ∈ Set.Icc (0 : ℝ) T,
      |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ) (u : ℝ), Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : MomentDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ => Φ N)) :
    StochDom P (U := fun _ => ↥(Set.Icc (0 : ℝ) T))
      (fun N u ω => Y N (u : ℝ) ω) (fun N _ _ => Φ N) := by
  refine stochDom_timeIcc_of_holder_hp (s := fun _ => 0) (t := fun _ => T)
    (fun _ => hT.le) hT (fun _ => by linarith) hK hB hγ hΦ hΦlow hΞ hHol
    (fun p N u _ => hint p N u) ?_
  intro ε hε p
  obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
  exact ⟨C, hC0, by filter_upwards [hCN] with N hN u hu using hN ⟨u, hu⟩⟩

/-- The case `Φ ≡ 1`, `T = 1`: this has exactly the signature of T75's
`RBM.Step2Moment.stochDom_timeIcc_of_holder` except that the Hölder modulus is only assumed on
a high-probability event, so it is a drop-in replacement for it. -/
theorem stochDom_timeIcc_one_of_holder_hp {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N)
    (hlen : ∀ N, t N - s N ≤ 1) {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) {Y : ℕ → ℝ → Ω → ℝ}
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ u' ∈ Set.Icc (s N) (t N), |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N), ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * (N : ℝ) ^ (ε * p)) :
    StochDom P (U := fun N => RBM.TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine stochDom_timeIcc_of_holder_hp hst one_pos hlen hK le_rfl hγ
    (Φ := fun _ => (1 : ℝ)) (fun _ => one_pos) ?_ hΞ hHol hint ?_
  · filter_upwards with N
    rw [neg_zero, Real.rpow_zero]
  · intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    exact ⟨C, hC0, by filter_upwards [hCN] with N hN u hu using by simpa using hN u hu⟩

end Uniform

/-! ### The net theorem with a `≺`-controlled Hölder constant -/

section RandomConstant

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- **The Hölder constant is itself only `≺`-controlled.**

The modulus is `|Y(N,u,ω) − Y(N,u',ω)| ≤ N^K · R(N,ω) · |u − u'|^γ` with a **random** constant
`R` subject only to `R ≺ 1` (Definition 2.1 (i) with a one-point parameter set — literally the
shape of `RBM.Gauss.OpNormBound.norm_X`, `R(N,ω) = ‖X‖`).

This is the form the Gaussian flow produces: from `‖H_u − H_{u'}‖ = |√u − √u'| ‖X‖`
(`RBM.Gauss.norm_Hflow_sub`) and the resolvent identity, a Green's function functional obeys
`‖G_u − G_{u'}‖ ≤ η^{-2} |√u − √u'| ‖X‖ ≤ η^{-2} ‖X‖ · |u − u'|^{1/2}`
(`RBM.Gauss.abs_sqrt_sub_sqrt_le`), i.e. `γ = 1/2`, `N^K` the deterministic `η^{-2}`, and
`R = ‖X‖`, which is *not* bounded pointwise in `ω`.

Reduction to `stochDom_timeIcc_of_holder_hp`: `R ≺ 1` makes `{ω | R(N,ω) ≤ N}` a
high-probability event (`RBM.StochDom.highProb` at `τ = 1`), and on it the modulus becomes the
deterministic `N^{K+1} |u − u'|^γ`.  The single extra power of `N` only enlarges the net from
`N^{(K+B+1)/γ}` to `N^{(K+B+2)/γ}` points, which is still polynomial. -/
theorem stochDom_timeIcc_of_holder_dom {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ} (hT : 0 < T)
    (hlen : ∀ N, t N - s N ≤ T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ)
    {Y : ℕ → ℝ → Ω → ℝ} {Φ : ℕ → ℝ} (hΦ : ∀ N, 0 < Φ N)
    (hΦlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Φ N)
    {R : ℕ → Ω → ℝ}
    (hR : StochDom P (fun N (_ : Unit) ω => R N ω) (fun _ _ _ => (1 : ℝ)))
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ (ω : Ω), ∀ u ∈ Set.Icc (s N) (t N),
      ∀ u' ∈ Set.Icc (s N) (t N), |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * R N ω * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N),
        ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N ^ (2 * p))) :
    StochDom P (U := fun N => RBM.TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun N _ _ => Φ N) := by
  -- the good event: the random Hölder constant is at most `N`
  have hΞ : HighProb P (fun N => {ω | R N ω ≤ (N : ℝ)}) := by
    refine (hR.highProb one_pos).mono (Eventually.of_forall fun N ω hω => ?_)
    have h := hω ()
    simpa [Real.rpow_one] using h
  refine stochDom_timeIcc_of_holder_hp hst hT hlen (K := K + 1) (by linarith) hB hγ hΦ hΦlow
    hΞ ?_ hint hmom
  filter_upwards [hHol, eventually_ge_atTop 1] with N hHolN hN1 ω hωΞ u hu u' hu'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hd : (0 : ℝ) ≤ |u - u'| ^ γ := Real.rpow_nonneg (abs_nonneg _) _
  have hKnn : (0 : ℝ) ≤ (N : ℝ) ^ K := Real.rpow_nonneg hNpos.le _
  have hRle : R N ω ≤ (N : ℝ) := hωΞ
  refine (hHolN ω u hu u' hu').trans ?_
  have hc : (N : ℝ) ^ K * R N ω ≤ (N : ℝ) ^ (K + 1) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hRle hKnn
  exact mul_le_mul_of_nonneg_right hc hd

/-- The case `Φ ≡ 1`, `T = 1` of `stochDom_timeIcc_of_holder_dom`: T75's
`RBM.Step2Moment.stochDom_timeIcc_of_holder` with the pointwise Hölder constant replaced by a
`≺`-controlled random one. -/
theorem stochDom_timeIcc_one_of_holder_dom {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N)
    (hlen : ∀ N, t N - s N ≤ 1) {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) {Y : ℕ → ℝ → Ω → ℝ}
    {R : ℕ → Ω → ℝ}
    (hR : StochDom P (fun N (_ : Unit) ω => R N ω) (fun _ _ _ => (1 : ℝ)))
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ (ω : Ω), ∀ u ∈ Set.Icc (s N) (t N),
      ∀ u' ∈ Set.Icc (s N) (t N), |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * R N ω * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N), ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * (N : ℝ) ^ (ε * p)) :
    StochDom P (U := fun N => RBM.TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine stochDom_timeIcc_of_holder_dom hst one_pos hlen hK le_rfl hγ
    (Φ := fun _ => (1 : ℝ)) (fun _ => one_pos) ?_ hR hHol hint ?_
  · filter_upwards with N
    rw [neg_zero, Real.rpow_zero]
  · intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    exact ⟨C, hC0, by filter_upwards [hCN] with N hN u hu using by simpa using hN u hu⟩

end RandomConstant

/-! ### The net theorem with a **time-dependent** control

All five statements above take a control `Φ : ℕ → ℝ` that does not depend on the time.  The
controls that the flow produces do: `RBM.Step1.Lemma41Flow` is quantified over
`Φ : ∀ N, RBM.TimeIcc s t N → ℝ`, and the `Φ` that `RBM1D/Hierarchy/Step1.lean` actually
supplies is `Φ(N,u) = (ℓ_u/ℓ_s)(W ℓ_u η_u)⁻¹`.

The net argument transports a bound from a net point `v` to a nearby `u`, so with a
`u`-dependent control it needs `Φ(N,v) ≤ N^ε Φ(N,u)` for `v` close to `u`.  That is **false**
for an arbitrary nonnegative `Φ`, so it has to be assumed; the two theorems below are the
variants of `stochDom_timeIcc_of_holder_hp` and `stochDom_timeIcc_of_holder_dom` carrying it.

To make the hypothesis dischargeable, the separation at which slow variation is required is
*exposed*: the caller supplies its own scale `δ : ℕ → ℝ` together with `hδ`, which says that
`δ` dominates the spacing `T·N^{-(K+B+1)/γ}` of the net that the proof builds — the net has
`⌈N^{(K+B+1)/γ}⌉₊ + 1` points on an interval of length at most `T`
(`RBM.Gauss.netSize`, `RBM.Gauss.rpow_le_netSize`), so its spacing is at most that.  The
exponent `(K+B+1)/γ` is determined by the explicit inputs `K`, `B`, `γ`, so both hypotheses
are statements the caller can check.

The `N^{-B} ≤ Φ` hypothesis is likewise relativized to the interval.  Nothing above is
changed: these are new declarations. -/

section SlowControl

variable {P : Measure Ω} [IsFiniteMeasure P]

/-- **Definition 2.1 (i) with the uncountable union intact, for a time-dependent control.**

`stochDom_timeIcc_of_holder_hp` with the deterministic control `Φ(N)` replaced by `Φ(N,u)`,
at the price of the slow-variation hypothesis `hslow`: at any polynomially small `ε > 0`, times
at distance at most `δ N` have controls within a factor `N^ε` of each other.  `hδ` says that
`δ N` is at least the spacing `T·N^{-(K+B+1)/γ}` of the net used in the proof, so `hslow` is in
force at every net point.

The three-way split of the budget `τ`: `τ/3` for the net error (as before), `τ/3` for the
slow-variation loss, and `τ/3` to absorb `x² + x ≤ x³` at `x = N^{τ/3} ≥ 2`. -/
theorem stochDom_timeIcc_of_holder_slow_hp {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ}
    (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ)
    {Y : ℕ → ℝ → Ω → ℝ} {Φ : ℕ → ℝ → ℝ} (hΦ : ∀ N u, 0 < Φ N u)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N), (N : ℝ) ^ (-B) ≤ Φ N u)
    {δ : ℕ → ℝ} (hδ : ∀ᶠ N : ℕ in atTop, T / (N : ℝ) ^ ((K + B + 1) / γ) ≤ δ N)
    (hslow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ v ∈ Set.Icc (s N) (t N), |u - v| ≤ δ N → Φ N v ≤ (N : ℝ) ^ ε * Φ N u)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ u' ∈ Set.Icc (s N) (t N), |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N),
        ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))) :
    StochDom P (U := fun N => RBM.TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun N u _ => Φ N (u : ℝ)) := by
  set A : ℝ := (K + B + 1) / γ with hA_def
  have hA : 0 ≤ A := div_nonneg (by linarith) hγ.le
  have hAγ : A * γ = K + B + 1 := by rw [hA_def]; field_simp
  -- step 1 on the net (unconditional: the moment input is unconditional)
  have hnet : StochDom P (fun (N : ℕ) (k : Fin (netSize A N + 1)) ω =>
      Y N (netTime s t T A N k) ω) (fun N k _ => Φ N (netTime s t T A N k)) := by
    refine stochDom_of_momentDom (card_net_le hA) (Φ := fun N k => Φ N (netTime s t T A N k))
      (fun N k => hΦ N _) (fun p N k => hint p N _ (netTime_mem hst hT.le A N k)) ?_
    intro ε hε p
    obtain ⟨C, hC0, hCN⟩ := hmom ε hε p
    exact ⟨C, hC0, by
      filter_upwards [hCN] with N hN k using hN _ (netTime_mem hst hT.le A N k)⟩
  -- step 2: transfer from the net to the whole interval, on `Ξ`
  refine stochDom_of_subset_highProb hnet hΞ fun τ hτ => ⟨τ / 3, by linarith, ?_⟩
  have hτ3 : (0 : ℝ) < τ / 3 := by linarith
  have hTγ : (0 : ℝ) < T ^ γ := Real.rpow_pos_of_pos hT γ
  filter_upwards [hHol, hΦlow, hδ, hslow (τ / 3) hτ3, eventually_ge_atTop 1,
    eventually_le_rpow 2 hτ3, eventually_le_rpow (T ^ γ) one_pos]
    with N hHolN hΦN hδN hslowN hN1 hN2 hNT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hTN : T ^ γ ≤ (N : ℝ) := by rwa [Real.rpow_one] at hNT
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hmge : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := rpow_le_netSize A N
  have hNA : (0 : ℝ) < (N : ℝ) ^ A := Real.rpow_pos_of_pos hNpos A
  rintro ω ⟨⟨u, hub⟩, hωΞ⟩
  obtain ⟨k, hk⟩ := exists_netTime_close hT hlen A N u.2
  refine ⟨k, ?_⟩
  set v : ℝ := netTime s t T A N k with hv_def
  have hvmem : v ∈ Set.Icc (s N) (t N) := netTime_mem hst hT.le A N k
  set x : ℝ := (N : ℝ) ^ (τ / 3) with hx_def
  have hx2 : (2 : ℝ) ≤ x := hN2
  have hxpos : (0 : ℝ) < x := by linarith
  -- the net spacing is at most `δ N`, so slow variation applies between `u` and `v`
  have hspace : T / (netSize A N : ℝ) ≤ δ N :=
    (div_le_div_of_nonneg_left hT.le hNA hmge).trans hδN
  have hslow' : Φ N v ≤ x * Φ N u.1 := hslowN u.1 u.2 v hvmem (hk.trans hspace)
  -- the net error is at most `x · Φ(N,u)`
  have herr : (N : ℝ) ^ K * (T / (netSize A N : ℝ)) ^ γ ≤ x * Φ N u.1 := by
    have hΦu : (N : ℝ) ^ (-B) ≤ Φ N u.1 := hΦN u.1 u.2
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
    have hstep4 : T ^ γ * ((N : ℝ) ^ (-B) * (N : ℝ)⁻¹) ≤ T ^ γ * (Φ N u.1 * (N : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦu hinvn) hTγ.le
    have hstep5 : T ^ γ * (Φ N u.1 * (N : ℝ)⁻¹) ≤ x * Φ N u.1 := by
      have hTinv : T ^ γ * (N : ℝ)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hNpos, one_mul]; exact hTN
      have h1 : (1 : ℝ) ≤ x := by linarith
      have heq : T ^ γ * (Φ N u.1 * (N : ℝ)⁻¹) = (T ^ γ * (N : ℝ)⁻¹) * Φ N u.1 := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right (hTinv.trans h1) (hΦ N u.1).le
    linarith
  -- the modulus of continuity between `u` and the net point `v`
  have hhol := hHolN ω hωΞ u.1 u.2 v hvmem
  have hle : |Y N u.1 ω - Y N v ω| ≤ x * Φ N u.1 := by
    refine hhol.trans (le_trans ?_ herr)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hk hγ.le)
      (Real.rpow_pos_of_pos hNpos K).le
  have hdiff : Y N u.1 ω - Y N v ω ≤ x * Φ N u.1 := (le_abs_self _).trans hle
  -- `N^τ = x³` and `x³ ≥ x² + x` for `x ≥ 2`
  have hx3 : (N : ℝ) ^ τ = x * (x * x) := by
    rw [hx_def, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hΦu0 : (0 : ℝ) < Φ N u.1 := hΦ N u.1
  have hcube : 0 ≤ x * x * x - x * x - x := by nlinarith [hx2]
  have hgap : x * (x * Φ N u.1) + x * Φ N u.1 ≤ (x * (x * x)) * Φ N u.1 := by
    nlinarith [hcube, hΦu0.le]
  have hstep : x * Φ N v ≤ x * (x * Φ N u.1) :=
    mul_le_mul_of_nonneg_left hslow' hxpos.le
  have hub' : (x * (x * x)) * Φ N u.1 < Y N u.1 ω := by
    have : (N : ℝ) ^ τ * Φ N u.1 < Y N u.1 ω := hub
    rwa [hx3] at this
  show x * Φ N v < Y N v ω
  linarith

/-- **The time-dependent control together with a `≺`-controlled Hölder constant.**

`stochDom_timeIcc_of_holder_dom` with `Φ(N)` replaced by `Φ(N,u)`, under the same
slow-variation hypothesis as `stochDom_timeIcc_of_holder_slow_hp`.  This is the form that
composes with `RBM.Gauss.OpNormBound.norm_X` (T100) with no glue: `hR` has literally its
type. -/
theorem stochDom_timeIcc_of_holder_slow_dom {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) {T : ℝ}
    (hT : 0 < T) (hlen : ∀ N, t N - s N ≤ T) {K B γ : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) (hγ : 0 < γ)
    {Y : ℕ → ℝ → Ω → ℝ} {Φ : ℕ → ℝ → ℝ} (hΦ : ∀ N u, 0 < Φ N u)
    (hΦlow : ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N), (N : ℝ) ^ (-B) ≤ Φ N u)
    {δ : ℕ → ℝ} (hδ : ∀ᶠ N : ℕ in atTop, T / (N : ℝ) ^ ((K + 1 + B + 1) / γ) ≤ δ N)
    (hslow : ∀ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ v ∈ Set.Icc (s N) (t N), |u - v| ≤ δ N → Φ N v ≤ (N : ℝ) ^ ε * Φ N u)
    {R : ℕ → Ω → ℝ}
    (hR : StochDom P (fun N (_ : Unit) ω => R N ω) (fun _ _ _ => (1 : ℝ)))
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ (ω : Ω), ∀ u ∈ Set.Icc (s N) (t N),
      ∀ u' ∈ Set.Icc (s N) (t N), |Y N u ω - Y N u' ω| ≤ (N : ℝ) ^ K * R N ω * |u - u'| ^ γ)
    (hint : ∀ (p N : ℕ), ∀ u ∈ Set.Icc (s N) (t N),
      Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (s N) (t N),
        ∫ ω, |Y N u ω| ^ (2 * p) ∂P ≤ C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p))) :
    StochDom P (U := fun N => RBM.TimeIcc s t N) (fun N u ω => Y N (u : ℝ) ω)
      (fun N u _ => Φ N (u : ℝ)) := by
  -- the good event: the random Hölder constant is at most `N`
  have hΞ : HighProb P (fun N => {ω | R N ω ≤ (N : ℝ)}) := by
    refine (hR.highProb one_pos).mono (Eventually.of_forall fun N ω hω => ?_)
    have h := hω ()
    simpa [Real.rpow_one] using h
  refine stochDom_timeIcc_of_holder_slow_hp hst hT hlen (K := K + 1) (by linarith) hB hγ hΦ
    hΦlow hδ hslow hΞ ?_ hint hmom
  filter_upwards [hHol, eventually_ge_atTop 1] with N hHolN hN1 ω hωΞ u hu u' hu'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hd : (0 : ℝ) ≤ |u - u'| ^ γ := Real.rpow_nonneg (abs_nonneg _) _
  have hKnn : (0 : ℝ) ≤ (N : ℝ) ^ K := Real.rpow_nonneg hNpos.le _
  have hRle : R N ω ≤ (N : ℝ) := hωΞ
  refine (hHolN ω u hu u' hu').trans ?_
  have hc : (N : ℝ) ^ K * R N ω ≤ (N : ℝ) ^ (K + 1) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
    exact mul_le_mul_of_nonneg_left hRle hKnn
  exact mul_le_mul_of_nonneg_right hc hd

end SlowControl

end RBM.Gauss

