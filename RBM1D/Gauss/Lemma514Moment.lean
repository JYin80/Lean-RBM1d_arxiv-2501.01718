/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.Eq45FlowInputs

/-!
# Lemma 5.14 on the moment route, uniformly in the time

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: the passage from a **fixed-terminal-time** stochastic domination of the loop
difference `(L - K)_{v,σ,a}` to the **time-uniform** form in which `RBM.Step3.Lemma514` states
it.

The moment route has no martingale at all.  Its steps are

```
    `≺` at one fixed terminal time `v`
 →  unifDomIcc_of_forall_stochDom        (this file: every terminal time at once)
 →  unifDomIcc_mul_scale                 (this file: put back the scale `(W ℓ_u η_u)^m`)
 →  stochDom_timeIcc_of_unifDom_const    (this file; the net engine, constant control)
 →  Step3.Lemma514
```

## Main results

* `RBM.Gauss.unifDomIcc_of_forall_stochDom` — **the quantifier exchange.**  `≺` at every
  terminal-time *sequence* `v` gives `RBM.Gauss.UnifDomIcc`, i.e. the fixed-time domination
  uniform in `u ∈ [s_N, t_N]`.  This is the step that lets a domination which only ever speaks
  about one sequence `v : ℕ → ℝ` be used as a black box.  It is a classical choice argument:
  were the uniform statement to fail, the bad times would assemble into a sequence at which the
  hypothesis fails.  Note that the thresholds `τ`, `D` are fixed **before** the `∀ᶠ N`, which
  is what makes the exchange legitimate; the same argument is *not* available for a statement
  whose constant `C` is existentially quantified in front (see the warning below).
* `RBM.Gauss.unifDomIcc_mul_scale` — multiplying both sides of a `UnifDomIcc` by a positive
  deterministic factor `k(N,u)`.  Used with `k = (W ℓ_u η_u)^m`, which turns
  `‖(L-K)_{u,σ,a}‖ ≺ c_N (W ℓ_u η_u)^{-m}` into `Ξ`-shape.
* `RBM.Gauss.stochDom_timeIcc_of_unifDom_const` — the net engine
  (`RBM.Gauss.stochDom_timeIcc_of_unifDom`) at a control that is **constant in the time, in
  the index and in `ω`**.  Then `hζlow` and `hslow` are free, and the only real input left is
  the Hölder modulus of the loop difference in the time.
* `RBM.Gauss.card_loopData_le` — `#(LoopData L m) ≤ N^{m+1}` eventually, so an index-count
  hypothesis is a theorem.

## The quantifier that must stay where it is

`RBM.Gauss.unifDomIcc_of_forall_stochDom` exchanges `∀ v, ∀ᶠ N` into `∀ᶠ N, ∀ v` because the
statement being exchanged, `P(bad) ≤ N^{-D}`, has **no** constant in front of it: `τ` and `D`
are chosen first.  The exchange is *false* in general for a statement of the shape
`∃ C, ∀ᶠ N, …`, such as a moment bound on the right-hand side of (5.20).  That is why the
exchange is applied to the *output* of the fixed-time domination and not to such a bound: at
the point of application the `C` has already been consumed by Markov's inequality.

## What this file does **not** do

* Everything here is stated *from* a fixed-time domination; the moment bounds that produce it
  ((5.20) and (5.24) in moment form) are not proved here.
* The Hölder modulus of the loop difference along the flow is a *named hypothesis* here, with
  the exact shape the net engine consumes; its ingredients are proved in
  `RBM1D/Gauss/Lemma514Holder.lean`.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The quantifier exchange: every terminal-time sequence ⟹ uniformly in the time -/

section Exchange

variable {P : Measure Ω}

/-- **`RBM.Gauss.UnifDomIcc` from `≺` at every terminal-time sequence.**

The moment route produces, for each sequence `v : ℕ → ℝ` with `s_N ≤ v_N ≤ t_N`, a `≺` for
the loop difference **at the time `v_N`**.  What the time net
needs is the domination at *every* `u ∈ [s_N, t_N]` at once, eventually in `N`.  The two are
equivalent, because the thresholds `τ` and `D` of Definition 2.1 (i) are fixed before the
`∀ᶠ N`: if the uniform statement failed, the times at which it fails would assemble (by
choice) into a sequence violating the hypothesis.

Only `s N ≤ t N` is used, and only to have a default point in the window. -/
theorem unifDomIcc_of_forall_stochDom {V : ℕ → Type*} {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N)
    {ξ ζ : ∀ N, ℝ → V N → Ω → ℝ}
    (h : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom P (fun N a ω => ξ N (v N) a ω) (fun N a ω => ζ N (v N) a ω)) :
    UnifDomIcc P s t ξ ζ := by
  classical
  intro τ hτ D hD
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- at each `N`, a time of the window that witnesses the failure whenever there is one
  have hwit : ∀ N : ℕ, ∃ u : ℝ, u ∈ Set.Icc (s N) (t N) ∧
      (¬ (∀ u' ∈ Set.Icc (s N) (t N), ∀ a : V N,
            P {ω | (N : ℝ) ^ τ * ζ N u' a ω < ξ N u' a ω}
              ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) →
        ∃ a : V N, ¬ (P {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ N u a ω}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)))) := by
    intro N
    by_cases hb : ∀ u' ∈ Set.Icc (s N) (t N), ∀ a : V N,
        P {ω | (N : ℝ) ^ τ * ζ N u' a ω < ξ N u' a ω} ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))
    · exact ⟨s N, ⟨le_rfl, hst N⟩, fun hc => absurd hb hc⟩
    · have hex : ∃ u ∈ Set.Icc (s N) (t N), ∃ a : V N,
          ¬ (P {ω | (N : ℝ) ^ τ * ζ N u a ω < ξ N u a ω}
            ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) := by
        by_contra hc
        push Not at hc
        exact hb fun u hu a => hc u hu a
      obtain ⟨u, hu, ha⟩ := hex
      exact ⟨u, hu, fun _ => ha⟩
  choose v hvmem hvbad using hwit
  obtain ⟨N, hbadN, hgoodN⟩ := (hcon.and_eventually (h v hvmem τ hτ D hD)).exists
  obtain ⟨a, ha⟩ := hvbad N hbadN
  refine ha (le_trans (measure_mono ?_) hgoodN)
  intro ω hω
  exact ⟨a, hω⟩

end Exchange

/-! ### The index bound `hcard` is a theorem, not an assumption -/

section Card

/-- **`#(LoopData L m) ≤ N^{m+1}` eventually**, so the hypothesis `hcard` of every theorem
below is satisfiable — with the explicit exponent `Cv = m + 1` — for *every* `RBM.Band`.

`#(LoopData L m) = 2^m L^m`, and `L_N ≤ W_N L_N ≤ N` by `RBM.Band.dim` while `2^m ≤ N`
eventually.  This is the satisfiability witness for the one hypothesis of this file that is
purely combinatorial. -/
theorem card_loopData_le {B : Band Ω} (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (LoopData (B.L N) m) : ℝ) ≤ (N : ℝ) ^ ((m : ℝ) + 1) := by
  filter_upwards [B.dim, eventually_ge_atTop (2 ^ m), eventually_ge_atTop 1] with N hdim h2 h1
  have hL : B.L N ≤ N := le_trans (Nat.le_mul_of_pos_left _ (B.W_pos N)) hdim.1
  have hcard : Fintype.card (LoopData (B.L N) m) = 2 ^ m * B.L N ^ m := by
    simp [LoopData, ZMod.card]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h1
  have hLr : (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hL
  have h2r : (2 : ℝ) ^ m ≤ (N : ℝ) := by exact_mod_cast h2
  have hstep : ((2 ^ m * B.L N ^ m : ℕ) : ℝ) ≤ (N : ℝ) ^ (m + 1) := by
    push_cast
    rw [pow_succ]
    calc (2 : ℝ) ^ m * (B.L N : ℝ) ^ m ≤ (N : ℝ) * (N : ℝ) ^ m := by gcongr
      _ = (N : ℝ) ^ m * (N : ℝ) := by ring
  rw [hcard]
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.rpow_natCast (N : ℝ) (m + 1)]
  push_cast
  ring_nf

end Card

/-! ### Putting the scale back -/

section Scale

variable {P : Measure Ω}

/-- **A positive deterministic factor passes through `RBM.Gauss.UnifDomIcc`.**

With `k(N,u) = (W ℓ_u η_u)^m` this converts a bound on `‖(L-K)_{u,σ,a}‖` with control
`c_N (W ℓ_u η_u)^{-m}` — the shape in which the moment route delivers it — into a bound on
`(W ℓ_u η_u)^m ‖(L-K)_{u,σ,a}‖` with the control `c_N` **constant in the time**, which is what
makes the net engine cheap. -/
theorem unifDomIcc_mul_scale {V : ℕ → Type*} {s t : ℕ → ℝ} {k : ℕ → ℝ → ℝ} {c : ℕ → ℝ}
    (hk : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), 0 < k N u) {ξ : ∀ N, ℝ → V N → Ω → ℝ}
    (h : UnifDomIcc P s t ξ (fun N u _ _ => c N * (k N u)⁻¹)) :
    UnifDomIcc P s t (fun N u a ω => k N u * ξ N u a ω) (fun N _ _ _ => c N) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN u hu a
  refine le_trans (le_of_eq ?_) (hN u hu a)
  congr 1
  have hkey : (N : ℝ) ^ τ * (c N * (k N u)⁻¹) = ((N : ℝ) ^ τ * c N) / k N u := by
    field_simp
  ext ω
  simp only [Set.mem_ofPred_eq, hkey, div_lt_iff₀ (hk N u hu),
    mul_comm (k N u) (ξ N u a ω)]

end Scale

/-! ### The net engine at a control constant in the time -/

section Net

variable {P : Measure Ω}

/-- **The net engine (`RBM.Gauss.stochDom_timeIcc_of_unifDom`) at a control that does not
depend on the time, on the index, or on `ω`.**

Two of that theorem's five side conditions become free:

* `hζlow` (`N^{-B} ≤ ζ`) holds with `B = 0` as soon as `1 ≤ c_N` eventually — and in the
  application `c_N = Λ_N^{1/2} + Φ_N` with `1 ≤ Λ_N` eventually, which is a *hypothesis of
  `RBM.Step3.Lemma514` itself*;
* `hslow` (slow variation of the control at the net spacing) is trivial, the control being
  constant in `u`.

What is left is the Hölder modulus `hHol`, valid on a high-probability event — exactly the
shape `RBM1D/Gauss/DominationHolder.lean` was built for, so a random Hölder constant
`≺ 1` may be moved onto `Ξ` by `RBM.StochDom.highProb` before this theorem is applied. -/
theorem stochDom_timeIcc_of_unifDom_const {V : ℕ → Type*} [∀ N, Fintype (V N)] {Cv : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ Cv)
    {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N) (hlen : ∀ N, t N - s N ≤ 1)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {ξ : ∀ N, ℝ → V N → Ω → ℝ} {c : ℕ → ℝ} (hc0 : ∀ N, 0 ≤ c N)
    (hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ c N)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ a : V N, ∀ u ∈ Set.Icc (s N) (t N),
      ∀ v ∈ Set.Icc (s N) (t N), |ξ N u a ω - ξ N v a ω| ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hfix : UnifDomIcc P s t ξ (fun N _ _ _ => c N)) :
    StochDom P (U := fun N => RBM.TimeIcc s t N × V N)
      (fun N p ω => ξ N (p.1 : ℝ) p.2 ω) (fun N _ _ => c N) := by
  refine stochDom_timeIcc_of_unifDom hcard hst one_pos hlen hK le_rfl hγ
    (fun N _ _ _ => hc0 N) (δ := fun N => 1 / (N : ℝ) ^ ((K + 0 + 1) / γ))
    (Filter.Eventually.of_forall fun N => le_rfl) hΞ hHol ?_ ?_ hfix
  · filter_upwards [hc1] with N hN _ _ _ _ _
    simpa using hN
  · intro ε hε
    filter_upwards [eventually_ge_atTop 1] with N hN1 _ _ _ _ _ _ _ _
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ ε :=
      Real.one_le_rpow (by exact_mod_cast hN1) hε.le
    nlinarith [hc0 N]

end Net

section XiLK

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end XiLK

section Compose

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Compose

section Lemma514

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Lemma514

section FromHyp

variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

end FromHyp

end RBM.Gauss
