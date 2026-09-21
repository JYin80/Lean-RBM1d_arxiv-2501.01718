/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamelRhs
import RBM1D.Gauss.Eq45FlowInputs

/-!
# Lemma 5.14 on the moment route, uniformly in the time (T181)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2: the passage from the **fixed-terminal-time** conclusion of
`RBM.MomentDuhamel.stochDom_of_momentDuhamel` (T132a) to the **time-uniform** statement
`RBM.Step3.Lemma514` that Step 3, Steps 4–5 and `RBM.StepGlue` consume.

## Why this file exists

`RBM.Step3.Lemma514` has one producer today, `RBM.SumZeroDyn.lemma514_flow'`, and it takes
`H : ∀ n, RBM.SumZeroDyn.Hierarchy X E s t n`, whose fields `F`, `EE`, `mart`, `martQ` are
**free data**.  Instantiating it is forbidden (T118/T74): a `mart` chosen as the residual of
`duhamel` makes that field true by definition, and every theorem downstream of it vacuous.
`lemma514_flow'` moreover needs `0 < s N`, which would reopen the seam T161 closed.

The moment route has no martingale at all.  This file assembles it:

```
    stochDom_of_momentDuhamel   (T132a; one fixed terminal time `v`)
 →  unifDomIcc_of_forall_stochDom        (this file: every terminal time at once)
 →  unifDomIcc_mul_scale                 (this file: put back the scale `(W ℓ_u η_u)^m`)
 →  stochDom_timeIcc_of_unifDom_const    (this file; T124's net engine, constant control)
 →  stochDom_xiLK_of_nonneg              (this file: T53's step, at `0 ≤ s` instead of `0 < s`)
 →  Step3.Lemma514                       (`lemma514_of_seq`)
```

## Main results

* `RBM.Gauss.unifDomIcc_of_forall_stochDom` — **the quantifier exchange.**  `≺` at every
  terminal-time *sequence* `v` gives `RBM.Gauss.UnifDomIcc`, i.e. the fixed-time domination
  uniform in `u ∈ [s_N, t_N]`.  This is the step that lets
  `RBM.MomentDuhamel.stochDom_of_momentDuhamel` — which only ever speaks about one sequence
  `v : ℕ → ℝ` — be used as a black box.  It is a classical choice argument: were the uniform
  statement to fail, the bad times would assemble into a sequence at which the hypothesis
  fails.  Note that the thresholds `τ`, `D` are fixed **before** the `∀ᶠ N`, which is what
  makes the exchange legitimate; the same argument is *not* available for a statement whose
  constant `C` is existentially quantified in front (see the module docstring's warning
  below).
* `RBM.Gauss.unifDomIcc_mul_scale` — multiplying both sides of a `UnifDomIcc` by a positive
  deterministic factor `k(N,u)`.  Used with `k = (W ℓ_u η_u)^m`, which turns
  `‖(L-K)_{u,σ,a}‖ ≺ c_N (W ℓ_u η_u)^{-m}` into `Ξ`-shape.
* `RBM.Gauss.stochDom_timeIcc_of_unifDom_const` — T124's net engine
  (`RBM.Gauss.stochDom_timeIcc_of_unifDom`) at a control that is **constant in the time, in
  the index and in `ω`**.  Then `hζlow` and `hslow` are free, and the only real input left is
  the Hölder modulus `hHol`.
* `RBM.Gauss.stochDom_xiLK_of_nonneg` — `RBM.SumZeroDyn.stochDom_xiLK_of` with `0 < s N`
  weakened to `0 ≤ s N`.  The strict positivity is used there only through
  `RBM.Band.scale_pos`, and `RBM.Band.scale_pos'` is the `0 ≤ t` form of the same fact
  (`ℓ_0 = 1`).  **This is the point of T176's warning**: the moment route must not reopen the
  `0 ≤ s` seam that T161 closed, and it does not.
* `RBM.Gauss.stochDom_flowXiLK_of_seq` — the four steps composed.
* `RBM.Gauss.lemma514_of_seq` — **`RBM.Step3.Lemma514` itself**, from the per-sequence `≺`
  with control `Λ^{1/2} + Φ` divided by the scale.  No `RBM.SumZeroDyn.Hierarchy`, no
  `RBM.SumZeroDyn.Lemma510` field, and only `0 ≤ s`.
* `RBM.Gauss.lemma514_of_momentDuhamel` — the same, with the per-sequence `≺` replaced by
  `RBM.MomentDuhamel.Hyp` together with the right-hand-side bound `RBM.Gauss.Rhs514At`, which
  is verbatim the `hrhs` slot of `RBM.MomentDuhamel.stochDom_of_momentDuhamel`.
* `RBM.Gauss.hrhs514_of_moment_inputs` — **compile-time check**: that slot is filled by a
  *bare application* of `RBM.Gauss.hrhs_of_moment_inputs` (T146/T157).
* `RBM.Gauss.rhs514At_forall_of_moment_inputs` — and the `∀ v` in front of it costs nothing:
  each hypothesis at the terminal time `v` is the restriction of the same hypothesis at `t`,
  with the same constants.  So the terminal-time quantifier is not an obstruction and
  `RBM1D/Gauss/MomentDuhamelRhs.lean` does not have to change.
* `RBM.Gauss.lemma514_forall_of_momentDuhamel` — the `∀ n, 2 ≤ n →` form the consumers write,
  with `hcard` discharged by `RBM.Gauss.card_loopData_le`.
* `RBM.Gauss.flow_sharpLmK_of_momentDuhamel` — **end-to-end acceptance probe**: the result is
  fed to `RBM.Step45.flow_sharpLmK`'s `h514` argument, applied, with no coercion.
* `RBM.Gauss.card_loopData_le`, `RBM.Gauss.rhs514At_self`,
  `RBM.Gauss.hHol_of_window_degenerate`, `RBM.Gauss.forall_stochDom_of_unifDomIcc` — the
  satisfiability and degeneracy checks; see the last section.

## The quantifier that must stay where it is

`RBM.Gauss.unifDomIcc_of_forall_stochDom` exchanges `∀ v, ∀ᶠ N` into `∀ᶠ N, ∀ v` because the
statement being exchanged, `P(bad) ≤ N^{-D}`, has **no** constant in front of it: `τ` and `D`
are chosen first.  The exchange is *false* in general for a statement of the shape
`∃ C, ∀ᶠ N, …` — and `RBM.Gauss.hrhs_of_moment_inputs`'s conclusion is exactly of that shape.
That is why this file applies the exchange to the *output* of
`RBM.MomentDuhamel.stochDom_of_momentDuhamel` and not to `hrhs`: at the point of application
the `C` has already been consumed by Markov's inequality.

## What this file does **not** do

* It does not instantiate `RBM.SumZeroDyn.Hierarchy` and it uses no `RBM.SumZeroDyn.Lemma510`
  field.  Neither name occurs below.
* It does not close `RBM.MomentDuhamel.Hyp`'s fields `momentDuhamel` / `momentDuhamelQ`; those
  are T180's remainder and T187 reports precisely what they are still short of (time-dependent
  admissibility and the drift-and-Hölder chain).  Everything here is stated *from* a `Hyp`, so
  it composes with that instance the moment it exists.
* It does not prove the Hölder modulus `hHol` of the loop difference along the flow.  The
  deterministic half of that estimate is T106 (`RBM1D/Gauss/FlowHolder.lean`,
  `RBM.Gauss.norm_green_flow_sub_le`) at loop length one; the extension to a product of
  `m` resolvents, and the `u`-modulus of `RBM.Band.Kval`, are not in the repository.  It is a
  *named hypothesis* here, with the exact shape the net engine consumes.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The quantifier exchange: every terminal-time sequence ⟹ uniformly in the time -/

section Exchange

variable {P : Measure Ω}

/-- **`RBM.Gauss.UnifDomIcc` from `≺` at every terminal-time sequence.**

`RBM.MomentDuhamel.stochDom_of_momentDuhamel` produces, for each sequence `v : ℕ → ℝ` with
`s_N ≤ v_N ≤ t_N`, a `≺` for the loop difference **at the time `v_N`**.  What the time net
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

/-- **The converse of `unifDomIcc_of_forall_stochDom`**, as soon as the index is polynomially
large.  Together the two say that the two formulations are *equivalent*, which is the
non-vacuity check for the exchange: it cannot have silently strengthened the hypothesis, since
the strengthened form gives the original one back. -/
theorem forall_stochDom_of_unifDomIcc {V : ℕ → Type*} [∀ N, Fintype (V N)] {Cv : ℝ}
    (hcard : ∀ᶠ N : ℕ in atTop, (Fintype.card (V N) : ℝ) ≤ (N : ℝ) ^ Cv)
    {s t : ℕ → ℝ} {ξ ζ : ∀ N, ℝ → V N → Ω → ℝ} (h : UnifDomIcc P s t ξ ζ)
    (v : ℕ → ℝ) (hv : ∀ N, v N ∈ Set.Icc (s N) (t N)) :
    StochDom P (fun N a ω => ξ N (v N) a ω) (fun N a ω => ζ N (v N) a ω) := by
  refine StochDom.of_forall_le hcard fun τ hτ D hD => ?_
  filter_upwards [h τ hτ D hD] with N hN a
  exact hN (v N) (hv N) a

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
`c_N (W ℓ_u η_u)^{-m}` — the shape in which
`RBM.MomentDuhamel.stochDom_of_momentDuhamel` delivers it — into a bound on
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

/-- **T124's net engine (`RBM.Gauss.stochDom_timeIcc_of_unifDom`) at a control that does not
depend on the time, on the index, or on `ω`.**

Two of that theorem's five side conditions become free:

* `hζlow` (`N^{-B} ≤ ζ`) holds with `B = 0` as soon as `1 ≤ c_N` eventually — and in the
  application `c_N = Λ_N^{1/2} + Φ_N` with `1 ≤ Λ_N` eventually, which is a *hypothesis of
  `RBM.Step3.Lemma514` itself*;
* `hslow` (slow variation of the control at the net spacing) is trivial, the control being
  constant in `u`.

What is left is the Hölder modulus `hHol`, valid on a high-probability event — exactly the
shape `RBM1D/Gauss/DominationHolder.lean` (T101) was built for, so a random Hölder constant
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

/-! ### `Ξ^{(L-K)}` from the loop difference, at `0 ≤ s` -/

section XiLK

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.SumZeroDyn.stochDom_xiLK_of` with `0 < s N` weakened to `0 ≤ s N`.**

Strict positivity of `s` enters that proof at one place only, `RBM.Band.scale_pos`, and
`RBM.Band.scale_pos'` is the same statement at `0 ≤ t` (it holds because `ℓ_0 = 1`).  The
weakening matters: T176 records that `RBM.SumZeroDyn.lemma514_flow'` needs `0 < s N`, so a
route to `RBM.Step3.Lemma514` through it would reopen the `0 ≤ s` seam that T161 closed and
that `RBM.Thm221.step` depends on.  The moment route assembled below therefore does not go
through this lemma's primed original. -/
theorem stochDom_xiLK_of_nonneg (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {m : ℕ} {ζ : ∀ N, RBM.TimeIcc s t N → ℝ}
    (h : StochDom B.P (fun N (p : RBM.TimeIcc s t N × LoopData (B.L N) m) ω =>
      B.scale E N p.1 ^ m * ‖SumZeroDyn.lkT X E N p.1 ω p.2.1 p.2.2‖) (fun N p _ => ζ N p.1)) :
    StochDom B.P (Step3.flowXiLK X E s t m) (fun N u _ => ζ N u) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono fun ω hω => ?_).trans hN
  obtain ⟨u, hu⟩ := hω
  have hA : 0 < B.scale E N u ^ m :=
    pow_pos (B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))) m
  have hu' : (N : ℝ) ^ τ * ζ N u / B.scale E N u ^ m < X.lkMax E N u ω m := by
    rw [div_lt_iff₀ hA]
    have : Step3.flowXiLK X E s t m N u ω = X.lkMax E N u ω m * B.scale E N u ^ m := rfl
    linarith
  obtain ⟨ld, hld⟩ := exists_lt_of_lt_ciSup hu'
  refine ⟨(u, ld), ?_⟩
  show (N : ℝ) ^ τ * ζ N u < B.scale E N u ^ m * ‖SumZeroDyn.lkT X E N u ω ld.1 ld.2‖
  rw [div_lt_iff₀ hA] at hld
  rw [SumZeroDyn.norm_lkT]
  linarith

end XiLK

/-! ### The four steps composed -/

section Compose

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **From `≺` for the loop difference at every terminal-time sequence to `Ξ^{(L-K)}_{·,m} ≺ c`,
uniformly in `u ∈ [s_N, t_N]`.**

This is the whole of the time-uniform passage the moment route needs, and the only hypothesis
in it that is not already a theorem of the repository is the Hölder modulus `hHol`.

* `hseq` is the conclusion of `RBM.MomentDuhamel.stochDom_of_momentDuhamel`, read at an
  arbitrary terminal-time sequence, with the control divided by the scale `(W ℓ_v η_v)^m`;
* `hHol` is the deterministic modulus of continuity of `(W ℓ_u η_u)^m ‖(L-K)_{u,σ,a}‖`, valid
  on a high-probability event `Ξ` (T101's weakening: the constant may be random as long as
  it is `≺ 1`, which is where `‖X‖ ≺ 1` enters);
* `hc1` (`1 ≤ c_N` eventually) is what makes the control admissible for the net.

`0 < s` is **not** used. -/
theorem stochDom_flowXiLK_of_seq (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {m : ℕ}
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) m) : ℝ) ≤ (N : ℝ) ^ Cv)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    {c : ℕ → ℝ} (hc0 : ∀ N, 0 ≤ c N) (hc1 : ∀ᶠ N : ℕ in atTop, 1 ≤ c N)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ m * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ m * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hseq : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) m) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
        (fun N _ _ => c N * (B.scale E N (v N) ^ m)⁻¹)) :
    StochDom B.P (Step3.flowXiLK X E s t m) (fun N _ _ => c N) := by
  have hkpos : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), 0 < B.scale E N u ^ m := fun N u hu =>
    pow_pos (B.scale_pos' hE N ((hs0 N).trans hu.1) (hu.2.trans_lt (ht1 N))) m
  have h1 : UnifDomIcc B.P s t
      (fun N u (q : LoopData (B.L N) m) ω => ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖)
      (fun N u _ _ => c N * (B.scale E N u ^ m)⁻¹) :=
    unifDomIcc_of_forall_stochDom hst hseq
  exact stochDom_xiLK_of_nonneg X hE hs0 ht1 (ζ := fun N _ => c N)
    (stochDom_timeIcc_of_unifDom_const hcard hst
      (fun N => by have h1 := hs0 N; have h2 := ht1 N; linarith) hK hγ hc0 hc1 hΞ hHol
      (unifDomIcc_mul_scale hkpos h1))

end Compose

/-! ### `RBM.Step3.Lemma514`, on the moment route -/

section Lemma514

variable {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The four `≺` premises of `RBM.Step3.Lemma514`**, bundled so that they can be named once
and passed on.  Unbundling them is `Lemma514Premises` ↔ the four conjuncts, by `rfl`; the
bundle exists only to keep the statements below readable.

Keeping them is *not* optional.  Dropping them and quantifying the moment bound over all
`(Λ, Φ)` would make the hypothesis unsatisfiable — at `Λ = Φ = 0` the control collapses to
`(W ℓ_v η_v)^{-(n+2)}`, which does not bound the right-hand side of (5.24) — and the
resulting theorem vacuous.  `Λ` is what controls the `E ⊗ E` term (whence the `Λ^{1/2}` in the
conclusion) and `Φ` the drift and the initial datum. -/
def Lemma514Premises (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) (Λ Φ : ℕ → ℝ) : Prop :=
  StochDom B.P (Step3.flowXiL X E s t (2 * n + 2)) (fun N _ _ => Λ N) ∧
  (∀ m, 1 ≤ m → m < n → StochDom B.P (Step3.flowXiLK X E s t m) fun N _ _ => Φ N) ∧
  (∀ m, 2 ≤ m → m ≤ n → StochDom B.P
    (fun N u ω => Step3.flowXiLK X E s t m N u ω
      * Step3.flowXiLK X E s t (n - m + 2) N u ω * (Step3.flowA B E s t N u)⁻¹)
    fun N _ _ => Φ N) ∧
  StochDom B.P (Step3.flowXiL X E s t (n + 1)) (fun N _ _ => Φ N)

/-- **Lemma 5.14 (5.92) in the form `RBM.Step3.Lemma514`, from the moment route.**

The hypothesis `hseq` is the conclusion of `RBM.MomentDuhamel.stochDom_of_momentDuhamel` at an
arbitrary terminal time, with the control `Λ^{1/2} + Φ` divided by the scale.  The `Λ`-half
comes from the `E ⊗ E` term of (5.24) — whose square root is why the conclusion carries
`Λ^{1/2}` — and the `Φ`-half from the initial datum and the drift; that bookkeeping is `hrhs`
(T146/T157) and `RBM.Hierarchy.DriftBound` (T165), and it is *not* redone here.

What this statement is worth is what it does **not** contain: no `RBM.SumZeroDyn.Hierarchy`,
no `RBM.SumZeroDyn.Lemma510` field, no martingale, no quadratic variation, and no `0 < s N`.
Those are exactly the four defects T176 records of the only pre-existing producer. -/
theorem lemma514_of_seq (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {n : ℕ}
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) n) : ℝ) ≤ (N : ℝ) ^ Cv)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) n,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ n * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ n * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hseq : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514Premises X E s t n Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        StochDom B.P
          (fun N (q : LoopData (B.L N) n) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
          (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * (B.scale E N (v N) ^ n)⁻¹)) :
    Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1
  refine stochDom_flowXiLK_of_seq X hE hs0 hst ht1 hcard hK hγ hΞ
    (c := fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) (fun N => ?_) ?_ hHol
    (hseq Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩)
  · have h1 : (0 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 N) _
    have := hΦ0 N
    linarith
  · filter_upwards [hΛ1] with N hN
    have h1 : (1 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have := hΦ0 N
    linarith

end Lemma514

/-! ### The same, starting from `RBM.MomentDuhamel.Hyp` -/

section FromHyp

variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The `hrhs` slot of `RBM.MomentDuhamel.stochDom_of_momentDuhamel`, at the terminal time
`v` and the control `c_N (W ℓ_v η_v)^{-(n+2)}`.**

Written out once, as a `def`, so that the acceptance probe below and the two theorems that
consume it cannot drift apart.  The three summands are, in order, the initial datum of (5.20),
the drift, and the `E ⊗ E` term of (5.24) under its square root. -/
def Rhs514At (H : MomentDuhamel.Hyp X E s t n) (c v : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ q : LoopData (B.L N) (n + 2),
      momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖)
        + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (H.F N u (X.H N u ω) q.1) q.2‖))
        + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (eeFun B E N u (X.H N u ω) q.1) (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
        ≤ C * ((N : ℝ) ^ (ε / 2) * (c N * (B.scale E N (v N) ^ (n + 2))⁻¹))

/-- **Acceptance probe: `RBM.Gauss.hrhs_of_moment_inputs` (T146/T157) fills the `hrhs` slot of
`lemma514_of_momentDuhamel` at each terminal time, by a bare application.**

The proof term is the application itself — no `convert`, no coercion, no `simp only` — so it is
a compile-time check that the shape of the hypothesis `hrhs` below is *exactly* the shape
T146/T157 deliver.  The only specialization made here is the control: T146 leaves it as
an arbitrary `Φ : ∀ N, LoopData (B.L N) (n+2) → ℝ`, and the moment route wants it in the form
`c_N · (W ℓ_v η_v)^{-(n+2)}` so that the scale can be put back by
`RBM.Gauss.unifDomIcc_mul_scale`.  Instantiating `c := Λ^{1/2} + Φ` gives `hrhs` verbatim. -/
theorem hrhs514_of_moment_inputs (H : MomentDuhamel.Hyp X E s t n)
    (v : ℕ → ℝ) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    {Ck Ck2 : ℝ} (hCk0 : 0 ≤ Ck) (hCk20 : 0 ≤ Ck2)
    (hkerlt : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (i : Fin (n + 2)),
      ‖((v N : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (hkerC : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ i, 1 + ‖(((u : ℝ) : ℂ) - ((v N : ℝ) : ℂ)) * xiOf (mSigma E) σ i‖
        * (1 - ‖((v N : ℝ) : ℂ) * xiOf (mSigma E) σ i‖)⁻¹ ≤ Ck)
    (hker2lt : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))),
      ‖((v N : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ < 1)
    (hker2C : ∀ᶠ N : ℕ in atTop, ∀ (σ : Fin (n + 2) → Bool) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ i, 1 + ‖(((u : ℝ) : ℂ) - ((v N : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i‖
        * (1 - ‖((v N : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤ Ck2)
    (hintF : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
      Integrable (fun ω => ‖H.F N u (X.H N u ω) σ b‖ ^ r) B.P)
    (hintEE : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool)
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
      Integrable (fun ω => ‖eeFun B E N u (X.H N u ω) σ c‖ ^ r) B.P)
    {Φ1 ΦF ΦE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hΦ10 : ∀ N q, 0 ≤ Φ1 N q) (hΦF0 : ∀ N q, 0 ≤ ΦF N q) (hΦE0 : ∀ N q, 0 ≤ ΦE N q)
    (hinit : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (q : LoopData (B.L N) (n + 2)) (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ1 N q))
    (hFmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖H.F N u (X.H N u ω) q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦF N q))
    (hEEmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
        momNorm B.P p (fun ω => ‖eeFun B E N u (X.H N u ω) q.1 c‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦE N q))
    {c : ℕ → ℝ}
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
      Ck ^ (n + 2) * Φ1 N q
        + 2 * ((v N - s N) * (Ck ^ (n + 2) * ΦF N q))
        + ((v N - s N) * (Ck2 ^ ((n + 2) + (n + 2)) * ΦE N q)) ^ ((1 : ℝ) / 2)
      ≤ c N * (B.scale E N (v N) ^ (n + 2))⁻¹) :
    Rhs514At H c v :=
  hrhs_of_moment_inputs H v hsv hvt hCk0 hCk20 hkerlt hkerC hker2lt hker2C hintF hintEE
    hΦ10 hΦF0 hΦE0 hinit hFmom hEEmom hnum

/-- **`RBM.Step3.Lemma514` from `RBM.MomentDuhamel.Hyp` and `hrhs`.**

This is the moment route end to end.  The hypothesis `hrhs` is *verbatim* the `hrhs` slot of
`RBM.MomentDuhamel.stochDom_of_momentDuhamel`, at the control
`(Λ^{1/2} + Φ) (W ℓ_v η_v)^{-(n+2)}` and quantified over the terminal time `v`; the three
terms it bounds are the initial datum, the drift and the `E ⊗ E` term of (5.20) + (5.24), and
the producer of that bound is `RBM.Gauss.hrhs_of_moment_inputs` (T146/T157), whose own three
inputs are discharged by `RBM.Gauss.hinit_of_stochDom`, `RBM.Gauss.hFmom_of_stochDom`
(fed by T165's `RBM.hdom_of_driftInputs`, which contains no `RBM.SumZeroDyn.Hierarchy`) and
`RBM.Gauss.hEEmom_of_stochDom`.

The control is raised to `max (Λ^{1/2} + Φ) 1` inside the proof, because
`stochDom_of_momentDuhamel` asks for a *strictly positive* control at every `N` while
`RBM.Step3.Lemma514` only offers `1 ≤ Λ_N` eventually; the two agree eventually, which is all
`≺` sees (`RBM.Step3.stochDom_mono`). -/
theorem lemma514_of_momentDuhamel (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (H : MomentDuhamel.Hyp X E s t n)
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Cv)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) (n + 2),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ (n + 2) * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ (n + 2) * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hrhs : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514At H (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v) :
    Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) (n + 2) := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1
  have hc1 : ∀ N : ℕ, (1 : ℝ) ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := fun N => le_max_right _ _
  have hc0 : ∀ N : ℕ, (0 : ℝ) ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := fun N =>
    le_trans zero_le_one (hc1 N)
  have hscale : ∀ (N : ℕ) (w : ℝ), w ∈ Set.Icc (s N) (t N) →
      0 < B.scale E N w ^ (n + 2) := fun N w hw =>
    pow_pos (B.scale_pos' hE N ((hs0 N).trans hw.1) (hw.2.trans_lt (ht1 N))) _
  have hseq : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
        (fun N _ _ => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
          * (B.scale E N (v N) ^ (n + 2))⁻¹) := by
    intro v hv
    refine MomentDuhamel.stochDom_of_momentDuhamel H v (fun N => (hv N).1) (fun N => (hv N).2)
      hcard (Φ := fun N _ => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
        * (B.scale E N (v N) ^ (n + 2))⁻¹) (fun N q => ?_) ?_
    · have h1 := hscale N (v N) (hv N)
      have h2 : (0 : ℝ) < max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := lt_of_lt_of_le one_pos (hc1 N)
      positivity
    · intro ε hε p hp
      obtain ⟨C, hC0, hCN⟩ := hrhs Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩ v hv ε hε p hp
      refine ⟨C, hC0, ?_⟩
      filter_upwards [hCN] with N hN q
      refine (hN q).trans ?_
      have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
      have hinv : (0 : ℝ) ≤ (B.scale E N (v N) ^ (n + 2))⁻¹ := (inv_pos.2 hsc).le
      have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hle : Λ N ^ ((1 : ℝ) / 2) + Φ N ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 :=
        le_max_left _ _
      gcongr
  have hmain := stochDom_flowXiLK_of_seq X hE hs0 hst ht1 hcard hK hγ hΞ hc0
    (Filter.Eventually.of_forall hc1) hHol hseq
  refine Step3.stochDom_mono (fun N _ _ => ?_) 1 ?_ hmain
  · have h1 : (0 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 N) _
    have := hΦ0 N
    linarith
  · filter_upwards [hΛ1] with N hN _ _
    have h1 : (1 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have := hΦ0 N
    rw [one_mul, max_le_iff]
    exact ⟨le_rfl, by linarith⟩

/-- **The `∀ v` of `lemma514_of_momentDuhamel`'s `hrhs` is free**, given the inputs of
`RBM.Gauss.hrhs_of_moment_inputs` stated over the whole window `[s_N, t_N]` instead of over
`[s_N, v_N]`.

This matters because the exchange `unifDomIcc_of_forall_stochDom` is *not* available here: the
conclusion of `hrhs_of_moment_inputs` has `∃ C` in front of `∀ᶠ N`, so the classical argument
that works for `P(bad) ≤ N^{-D}` does not apply (see the module docstring).  What this theorem
shows is that no argument is needed: `hrhs_of_moment_inputs` already takes the terminal time
`v` as an *argument*, and each of its hypotheses at `v` is the restriction to `v` of the same
hypothesis at `t`, with the same constants.  So the `∀ v` quantifier is not an obstruction, and
the moment route's remaining obligations are exactly the window-uniform inputs below.

Nothing in `RBM1D/Gauss/MomentDuhamelRhs.lean` has to change for this. -/
theorem rhs514At_forall_of_moment_inputs (H : MomentDuhamel.Hyp X E s t n)
    {Ck Ck2 : ℝ} (hCk0 : 0 ≤ Ck) (hCk20 : 0 ≤ Ck2)
    (hkerlt : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (s N) (t N),
      ∀ (σ : Fin (n + 2) → Bool) (i : Fin (n + 2)), ‖((w : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1)
    (hkerC : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (s N) (t N),
      ∀ (σ : Fin (n + 2) → Bool) (u : ℝ), s N ≤ u → u ≤ w →
      ∀ i, 1 + ‖(((u : ℝ) : ℂ) - ((w : ℝ) : ℂ)) * xiOf (mSigma E) σ i‖
        * (1 - ‖((w : ℝ) : ℂ) * xiOf (mSigma E) σ i‖)⁻¹ ≤ Ck)
    (hker2lt : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (s N) (t N),
      ∀ (σ : Fin (n + 2) → Bool) (i : Fin ((n + 2) + (n + 2))),
        ‖((w : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖ < 1)
    (hker2C : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (s N) (t N),
      ∀ (σ : Fin (n + 2) → Bool) (u : ℝ), s N ≤ u → u ≤ w →
      ∀ i, 1 + ‖(((u : ℝ) : ℂ) - ((w : ℝ) : ℂ)) * SumZeroDyn.xi2 E σ i‖
        * (1 - ‖((w : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤ Ck2)
    (hintF : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
      Integrable (fun ω => ‖H.F N u (X.H N u ω) σ b‖ ^ r) B.P)
    (hintEE : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool)
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
      Integrable (fun ω => ‖eeFun B E N u (X.H N u ω) σ c‖ ^ r) B.P)
    {Φ1 ΦF ΦE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hΦ10 : ∀ N q, 0 ≤ Φ1 N q) (hΦF0 : ∀ N q, 0 ≤ ΦF N q) (hΦE0 : ∀ N q, 0 ≤ ΦE N q)
    (hinit : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (q : LoopData (B.L N) (n + 2)) (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ1 N q))
    (hFmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ t N → ∀ (q : LoopData (B.L N) (n + 2))
        (b : LoopArg (B.L N) (n + 2)),
        momNorm B.P (2 * p) (fun ω => ‖H.F N u (X.H N u ω) q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦF N q))
    (hEEmom : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ t N → ∀ (q : LoopData (B.L N) (n + 2))
        (c : LoopArg (B.L N) ((n + 2) + (n + 2))),
        momNorm B.P p (fun ω => ‖eeFun B E N u (X.H N u ω) q.1 c‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * ΦE N q))
    {c : ℕ → ℝ}
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (s N) (t N),
      ∀ q : LoopData (B.L N) (n + 2),
        Ck ^ (n + 2) * Φ1 N q
          + 2 * ((w - s N) * (Ck ^ (n + 2) * ΦF N q))
          + ((w - s N) * (Ck2 ^ ((n + 2) + (n + 2)) * ΦE N q)) ^ ((1 : ℝ) / 2)
        ≤ c N * (B.scale E N w ^ (n + 2))⁻¹) :
    ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) → Rhs514At H c v := by
  intro v hv
  refine hrhs514_of_moment_inputs H v (fun N => (hv N).1) (fun N => (hv N).2) hCk0 hCk20
    ?_ ?_ ?_ ?_ hintF hintEE hΦ10 hΦF0 hΦE0 hinit ?_ ?_ ?_
  · filter_upwards [hkerlt] with N hN using hN (v N) (hv N)
  · filter_upwards [hkerC] with N hN using hN (v N) (hv N)
  · filter_upwards [hker2lt] with N hN using hN (v N) (hv N)
  · filter_upwards [hker2C] with N hN using hN (v N) (hv N)
  · intro ε hε p hp
    obtain ⟨C, hC0, hCN⟩ := hFmom ε hε p hp
    exact ⟨C, hC0, by
      filter_upwards [hCN] with N hN u hu1 hu2 using hN u hu1 (hu2.trans (hv N).2)⟩
  · intro ε hε p hp
    obtain ⟨C, hC0, hCN⟩ := hEEmom ε hε p hp
    exact ⟨C, hC0, by
      filter_upwards [hCN] with N hN u hu1 hu2 using hN u hu1 (hu2.trans (hv N).2)⟩
  · filter_upwards [hnum] with N hN using hN (v N) (hv N)

/-- **The `h514` slot of Steps 3–5, in the `∀ n, 2 ≤ n` form the consumers write.**

`hcard` has disappeared: it is discharged by `RBM.Gauss.card_loopData_le`.  What is left is
`H` (T180's instance, whose last two fields are T187's remainder), the Hölder modulus `hHol`
(T106's estimate extended from one resolvent to a loop; not in the repository) and `hrhs`
(T146/T157 for the three terms, T165 for the drift's control), the last of which is filled by
`RBM.Gauss.hrhs514_of_moment_inputs` above. -/
theorem lemma514_forall_of_momentDuhamel (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (H : ∀ n, MomentDuhamel.Hyp X E s t n)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ m * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ m * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hrhs : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514At (H n) (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v) :
    ∀ m, 2 ≤ m → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) m := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact lemma514_of_momentDuhamel hE hs0 hst ht1 (H n) (card_loopData_le (n + 2))
    hK hγ hΞ (hHol (n + 2)) (hrhs n)

/-- **Acceptance probe: the moment route fills the `h514` slot of Step 4 end to end.**

`RBM.Step45.flow_sharpLmK` is (2.78) for the flow, and its `h514` argument is *the* slot T176
records as unowned.  Here it is filled by `lemma514_forall_of_momentDuhamel`, applied — no
`convert`, no coercion.  Note what this theorem's hypotheses do **not** contain:
`RBM.SumZeroDyn.Hierarchy`, any `RBM.SumZeroDyn.Lemma510` field, and `0 < s N`.  The four
remaining Step 3 inputs `h0`, `h12`, `h1`, `h2` are exactly the ones `flow_sharpLmK` already
asks for and are not this file's business. -/
theorem flow_sharpLmK_of_momentDuhamel {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (H : ∀ n, MomentDuhamel.Hyp X E s t n)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ m * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ m * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hrhs : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514At (H n) (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v)
    (h0 : ∀ m, 1 ≤ m → Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s)
      (Step3.flowR B s t) (Step3.flowA B E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s)
      (Step3.flowR B s t) (Step3.flowA B E s t) m l)
    (h1 : StochDom B.P (Step3.flowXiLK X E s t 1) fun _ _ _ => 1)
    (h2 : StochDom B.P (Step3.flowXiLK X E s t 2)
      fun N u _ => Step3.flowA B E s t N u ^ ((1 : ℝ) / 4)) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : RBM.TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n) :=
  Step45.flow_sharpLmK X hκ0 hκ1 hEκ hs0 hst ht1 hc
    (lemma514_forall_of_momentDuhamel (by linarith : |E| < 2) hs0 hst ht1 H hK hγ hΞ
      hHol hrhs)
    h0 h12 h1 h2

end FromHyp

/-! ### Satisfiability and degeneracy checks -/

section Checks

variable {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **Degeneracy check for `Rhs514At`.**  At the terminal time `v = s` the two time integrals
vanish and the hypothesis reduces *exactly* to a bound on the initial datum — i.e. to (2.68) at
the time `s`, the `LmK` field of `RBM.BoundsCore`, which is an input the six-step loop already
has.  So `Rhs514At` is not identically false, and the window's left endpoint is not a point at
which the interface silently asks for something unavailable.

The converse degeneracy — a window with `t < s` — cannot arise here: every theorem above takes
`hst : ∀ N, s N ≤ t N`, and the *conclusion* `RBM.Step3.Lemma514` then still quantifies over a
nonempty `RBM.TimeIcc`. -/
theorem rhs514At_self (H : MomentDuhamel.Hyp X E s t n) (c : ℕ → ℝ) :
    Rhs514At H c s ↔ ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((s N : ℝ) : ℂ)
              (SumZeroDyn.lkT X E N (s N) ω q.1) q.2‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * (c N * (B.scale E N (s N) ^ (n + 2))⁻¹)) := by
  have hz : ((0 : ℝ)) ^ ((1 : ℝ) / 2) = 0 := Real.zero_rpow (by norm_num)
  simp only [Rhs514At, intervalIntegral.integral_same, mul_zero, hz, add_zero]

/-- **Consistency check for `hHol`.**  At a degenerate window the Hölder hypothesis is
automatic, so the hypothesis set of `lemma514_of_seq` / `lemma514_of_momentDuhamel` is
consistent: `hHol` is not a hidden `False`.

This is a *consistency* statement and nothing more.  The estimate that the hypothesis actually
asks for on a genuine window is `‖G_u - G_{u'}‖ ≤ η^{-2}(‖X‖+1)|u-u'|^{1/2}`
(`RBM.Gauss.norm_green_flow_sub_le`, T106) propagated through a product of `m` resolvents and
through the `u`-dependence of `RBM.Band.Kval`; neither propagation is in the repository, and
neither is proved here. -/
theorem hHol_of_window_degenerate (hts : ∀ N, t N = s N) {Ξ : ℕ → Set Ω} {K γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ m * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ m * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ := by
  refine Filter.Eventually.of_forall fun N ω _ q u hu v hv => ?_
  have hu' : u = s N := le_antisymm (by rw [← hts N]; exact hu.2) hu.1
  have hv' : v = s N := le_antisymm (by rw [← hts N]; exact hv.2) hv.1
  subst hu'
  subst hv'
  simp [Real.zero_rpow hγ.ne']

end Checks

end RBM.Gauss
