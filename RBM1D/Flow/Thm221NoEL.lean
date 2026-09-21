/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221Bare
import RBM1D.Hierarchy.Step2PP
import RBM1D.Gauss.MomentDuhamelCut
import RBM1D.Gauss.DimsExample

/-!
# Theorem 2.21 **without (2.71)** — the first induction (T204)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7.

The paper remarks on p. 25, right after Step 6, that

> "(2.71) will not be needed for Steps 1–5, i.e., Theorem 2.21 holds if (2.71) were removed from
> both the assumption and statement".

This file is that variant.  It runs the whole of §2.7 — Theorem 2.21, the induction of p. 24
that proves Lemmas 2.18–2.20, and the consequences of §2.5 — on `RBM.BoundsCore`, i.e. on
(2.68)–(2.70) **with the expectation bound (2.71) deleted from both sides**.  Nothing here
mentions (2.71) or any Step 6 datum; the second induction, which puts (2.71) back on top of this
one and yields (2.8)/(2.9) of Theorem 2.4 and Theorem 2.5, is T205.

`RBM.BoundsCore` (`Flow/Hypotheses.lean`) is already exactly the "(2.71) removed" bundle, and
`RBM.BoundsCore_of_Steps` is already the "without Step 6" half of `RBM.Bounds_of_Steps`; this
file adds what was missing, namely the *theorem* and the *induction* in that shape.

## The (2.72) side (D13)

Jun's ruling D13 (2026-09-21) fixes the step condition to `RBM.Cond272Reg` of
`Flow/Thm221Bare.lean` — (2.72) verbatim plus the regime bound `N^c ≤ W ℓ_t η_t` that Step 1
already carries and that the grid `1 - s_k = W^{-kτ'}` of p. 24 supplies for free.  T186 proved
that the bare `RBM.Cond272` alone is *not* enough (`RBM.exists_cond272_not_rpow_le_scale`), so
`RBM.Thm221NoEL` below is the strongest form available.

`RBM.Thm221NoEL'` is the same with the gained `RBM.Cond272'` (T179);
`RBM.Thm221NoEL.toThm221NoEL'` goes one way and the converse is not available, for the same
reason as in T186.  The induction is proved from the weaker `RBM.Thm221NoEL'`, so both forms
reach Lemmas 2.18–2.20.

**T209**: the six-step assembly now produces the `RBM.Cond272Reg` form directly
(`RBM.thm221NoEL_of_inputs`), so `RBM.Thm221NoEL` — D13's shape — has a producer and
`RBM.Cond272'` no longer occurs anywhere in the chain.  §5b below records where each of the
three `hregS`-consumers went.

## Main results

* `RBM.BoundsCore_zero`, `RBM.BoundsCore.congr` — (2.67) without (2.71), and stability under
  changing the time sequence for small `N`.
* `RBM.Thm221NoEL`, `RBM.Thm221NoEL'`, `RBM.Thm221NoEL.toThm221NoEL'` — Theorem 2.21 with
  (2.71) removed from hypothesis *and* conclusion.  `RBM.Thm221NoEL.step_boundsCore` is the
  one-step acceptance probe: `RBM.BoundsCore` at `s` in, `RBM.BoundsCore` at `t` out.
* `RBM.BoundsCore_of_Thm221NoEL'`, `RBM.BoundsCore_of_Thm221NoEL` — **Lemmas 2.18 (2.60),
  2.19 (2.63), 2.20 (2.64)** — everything except (2.62) — for every time sequence
  `0 ≤ t ≤ 1 - N^{-1+τ}`.  `RBM.stochDom_norm_Lval_of_Thm221NoEL'` is (2.61).
* `RBM.Band.cond272Reg_grid`, `RBM.Band.eventually_rpow_le_scale`,
  `RBM.Band.scale_zero_ge_rpow`, `RBM.boundsCore_hyp_consistent`,
  `RBM.boundsCore_gauss_witness` — the satisfiability checks of §4: the step condition
  `RBM.Cond272Reg` and the grid of p. 24 are jointly satisfiable inside the window
  `t ≤ 1 - N^{-1+τ}` that D13 added, and the remaining fields of `RBM.BoundsCore` have a
  forward witness on T202's explicit band model, at a non-degenerate scale.
* `RBM.BoundsCore_of_flow`, `RBM.boundsCore_step_of_flow`, `RBM.boundsCore_step_of_inputs`,
  `RBM.thm221NoEL'_of_inputs` — Steps 1–5 chained into the step of `RBM.Thm221NoEL'`, with no
  Step 6 datum anywhere.
* `RBM.boundsCore_step_of_flow_reg`, `RBM.boundsCore_step_of_inputs_reg`,
  `RBM.thm221NoEL_of_inputs`, `RBM.Thm221NoEL.step_boundsCore_reg`,
  `RBM.cond272Reg_grid_step_domain` — **T209**: the same chain with D13's step condition
  `RBM.Cond272Reg`, i.e. **`RBM.Thm221NoEL` itself**, plus the joint-satisfiability check of a
  whole step on the grid of p. 24.
* `RBM.SpecSeq.boundsCore`, `RBM.localLaw_of_boundsCore`, `RBM.loop1_of_boundsCore`,
  `RBM.partialTrace_of_boundsCore`, `RBM.trace_of_boundsCore`, `RBM.loop2_of_boundsCore`,
  `RBM.quantumDiffusion_pm_of_boundsCore`, `RBM.quantumDiffusion_pp_of_boundsCore`,
  `RBM.localSemicircleLaw_of_Thm221NoEL'`, `RBM.quantumDiffusion_pm_pp_of_Thm221NoEL'` —
  **Theorem 2.3** and **(2.6)/(2.7) of Theorem 2.4** on `RBM.BoundsCore`.  (2.8)/(2.9) and
  Theorem 2.5 genuinely need (2.71) and are deliberately *not* here; they are T205.

## What this file does **not** close

* **Closed by T209** (kept for the record): `RBM.Thm221NoEL` — the `RBM.Cond272Reg` shape D13
  fixes — used to have no producer, because Steps 2–5 consumed `hregS = RBM.Cond272'` verbatim
  and no route from `RBM.Cond272Reg` to `RBM.Cond272'` is available (in
  `RBM.rpow_mul_rpow_le_of_pow_thirty` the exponents `a = 1`, `b = 30` force `e ≤ 0`).  The fix
  was to restate the three consumers rather than to bridge: see §5b and
  `RBM.thm221NoEL_of_inputs`.  Note that `RBM.Cond272Reg.hA_phi` and
  `RBM.Cond272Reg.hA_betaStar` were **not** needed on this path — they are the side conditions
  of the *moment* route, i.e. of the hypothesis `RBM.MomentDuhamelCut.MomentHypCut`, and the
  chain below consumes that as a black box.
* Theorem 2.2 is not assembled anywhere in the tree yet (`RBM.sq_norm_eigenvector_le_of_norm_
  green_le` is its deterministic core, `RBM.localSemicircleLaw_of_Thm221N_of_z` the local law
  it needs), so there is nothing here to convert; the `RBM.BoundsCoreN` version of the latter
  belongs in `Flow/EnergyUniform.lean`.
* The six named inputs of Steps 1–5 are still hypotheses.

## Deviations from the paper

The variant itself is the paper's own remark on p. 25, so it is not a deviation.  The (2.72)
side is `RBM.Cond272Reg`, recorded by T186 (`docs/paper-deltas.md` #132) and ruled on in D13.
-/

namespace RBM

open MeasureTheory Filter

/-! ### 1. (2.67) and stability, without (2.71) -/

section Initial

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- **(2.67) with (2.71) removed**: (2.68)–(2.70) hold at `t = 0` with no error.  The
expectation bound (2.62) = (2.71) is simply not part of the bundle. -/
theorem BoundsCore_zero (hE : |E| ≤ 2) : BoundsCore X E (fun _ => 0) :=
  (Bounds_zero X hE).toBoundsCore

/-- (2.68)–(2.70) at a time sequence only depend on it for large `N`.  Verbatim
`RBM.Bounds.congr` with the `expect` line deleted. -/
theorem BoundsCore.congr {s t : ℕ → ℝ} (h : BoundsCore X E s)
    (hst : ∀ᶠ N : ℕ in atTop, s N = t N) : BoundsCore X E t where
  LmK n hn := (h.LmK n hn).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  decay D hD := (h.decay D hD).congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])
  localLaw := h.localLaw.congr_eventually (by filter_upwards [hst] with N hN; rw [hN])
    (by filter_upwards [hst] with N hN; rw [hN])

end Initial

/-! ### 2. Theorem 2.21 with (2.71) removed from both sides -/

section Thm

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **Theorem 2.21, p. 25 variant**: (2.71) removed from both the assumption and the statement.
The step condition is `RBM.Cond272Reg` (D13): (2.72) verbatim plus the regime bound
`N^c ≤ W ℓ_t η_t` of Step 1.

Compare `RBM.Thm221`: the hypothesis and the conclusion are `RBM.BoundsCore` instead of
`RBM.Bounds`, so neither `RBM.Bounds.expect` nor any conclusion of Step 6 occurs.  The two
statements are incomparable — `RBM.Thm221` gives (2.71) at `t` but demands it at `s`. -/
structure Thm221NoEL (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
    (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272Reg B E s t c →
    BoundsCore X E s → BoundsCore X E t

/-- **Theorem 2.21 without (2.71), with the gained (2.72)** (T179): the form the six steps of
§2.7 currently produce, since Steps 2–5 consume `hregS = RBM.Cond272'`.  Weaker than
`RBM.Thm221NoEL` (`RBM.Thm221NoEL.toThm221NoEL'`), and still enough for the induction of p. 24
(`RBM.BoundsCore_of_Thm221NoEL'`). -/
structure Thm221NoEL' (X : Sample B) (κ : ℝ) : Prop where
  step : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ c : ℝ, 0 < c → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) →
    (∀ N, s N ≤ t N) → (∀ N, t N < 1) → Cond272' B E s t c →
    BoundsCore X E s → BoundsCore X E t

/-- The gained (2.72) implies the regime form (T186), so `RBM.Thm221NoEL` is the stronger
statement. -/
theorem Thm221NoEL.toThm221NoEL' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoEL X κ) :
    Thm221NoEL' X κ where
  step E hE c hc0 s t hs0 hst ht1 hcond hB :=
    hT.step E hE c hc0 s t hs0 hst ht1
      (hcond.toCond272Reg (by linarith [abs_nonneg E]) hst ht1 hc0.le) hB

/-- **The acceptance probe of T204, one step**: `RBM.BoundsCore X E s` in, `RBM.BoundsCore X E t`
out, through `RBM.Thm221NoEL`.  The hypothesis list contains no `RBM.Bounds.expect`, no
`RBM.Steps.sharpExpect` and no other Step 6 datum; the (2.72) side is `RBM.Cond272Reg` (D13).

Note that `RBM.Thm221` does **not** give this: its `step` demands (2.71) at `s`, which
`RBM.BoundsCore` does not carry.  The p. 25 remark is a statement about the *proof* — Steps 1–5
never use (2.71) — not a formal consequence of the printed Theorem 2.21, which is why this file
restates it rather than deriving it. -/
theorem Thm221NoEL.step_boundsCore {κ : ℝ} (hT : Thm221NoEL X κ) {E : ℝ} (hE : |E| ≤ 2 - κ)
    {c : ℝ} (hc0 : 0 < c) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272Reg B E s t c) (hB : BoundsCore X E s) :
    BoundsCore X E t :=
  hT.step E hE c hc0 s t hs0 hst ht1 hcond hB

end Thm

/-! ### 3. The induction of p. 24, without (2.71) -/

section Induction

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}

/-- **Lemmas 2.18 (2.60), 2.19 (2.63) and 2.20 (2.64) — everything except (2.62) — from the
(2.71)-free Theorem 2.21.**

Verbatim the statement of `RBM.Bounds_of_Thm221'` with `RBM.BoundsCore` in place of
`RBM.Bounds`; the proof is the same induction along the truncated grid
`u_k = min(1 - W^{-kτ'}, t)` of p. 24, started at (2.67) (`RBM.BoundsCore_zero`).  No step of
the induction sees (2.71). -/
theorem BoundsCore_of_Thm221NoEL' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoEL' X κ)
    (hE : |E| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsCore X E t := by
  obtain ⟨τ', hτ', c, hc0, n₀, hgrid⟩ := B.eventually_flow_grid' hκ hτ
  have hg := hgrid E hE t ht0 ht
  have hE2 : |E| ≤ 2 := by linarith
  have hE2' : |E| < 2 := by linarith
  let u : ℕ → ℕ → ℝ := fun k N => gridT (B.W N) τ' (t N) k
  have key : ∀ k, BoundsCore X E (u k) := by
    intro k
    induction k with
    | zero =>
      have h0 : u 0 = fun _ => 0 := funext fun N => gridT_zero (ht0 N)
      rw [h0]
      exact BoundsCore_zero X hE2
    | succ k ih =>
      refine hT.step E hE c hc0 (u k) (u (k + 1)) (fun N => ?_) (fun N => ?_) (fun N => ?_) ?_ ih
      · exact le_min (gridS_nonneg (B.one_le_W N) hτ'.le k) (ht0 N)
      · exact gridT_mono (B.one_le_W N) hτ'.le (t N) (Nat.le_succ k)
      · exact (min_le_left _ _).trans_lt (gridS_lt_one (by linarith [B.one_le_W N]) _)
      · filter_upwards [hg] with N hN
        rw [etaT_div_etaT hE2']
        exact hN.2.2.2 k
  exact (key n₀).congr X (by filter_upwards [hg] with N hN; exact hN.1)

/-- **Lemmas 2.18–2.20 without (2.62), from `RBM.Thm221NoEL`** — the corollary of
`RBM.BoundsCore_of_Thm221NoEL'` along `RBM.Thm221NoEL.toThm221NoEL'`. -/
theorem BoundsCore_of_Thm221NoEL {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoEL X κ) (hE : |E| ≤ 2 - κ)
    {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) : BoundsCore X E t :=
  BoundsCore_of_Thm221NoEL' X hκ (hT.toThm221NoEL' hκ) hE hτ ht0 ht

/-- **(2.61) without (2.71)**: verbatim `RBM.stochDom_norm_Lval_of_Thm221'` with
`RBM.Thm221NoEL'` in place of `RBM.Thm221'`. -/
theorem stochDom_norm_Lval_of_Thm221NoEL' {κ : ℝ} (hκ : 0 < κ) (hT : Thm221NoEL' X κ)
    (hE : |E| ≤ 2 - κ) {τ : ℝ} (hτ : 0 < τ) {t : ℕ → ℝ} (ht0 : ∀ N, 0 ≤ t N)
    (ht : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N (u : LoopData (B.L N) n) ω => ‖X.Lval E N (t N) ω u.idx‖)
      (fun N _ _ => (B.scale E N (t N))⁻¹ ^ (n - 1)) := by
  obtain ⟨τ', -, c, -, n₀, hgrid⟩ := B.eventually_flow_grid' hκ hτ
  set t' : ℕ → ℝ := fun N => if t N < 1 then t N else 0 with ht'
  have ht'0 : ∀ N, 0 ≤ t' N := fun N => by
    simp only [ht']; split_ifs
    · exact ht0 N
    · exact le_rfl
  have ht'1 : ∀ N, t' N < 1 := fun N => by
    simp only [ht']; split_ifs with h
    · exact h
    · exact zero_lt_one
  have hg := hgrid E hE t ht0 ht
  have htt' : ∀ᶠ N : ℕ in atTop, t N = t' N := by
    filter_upwards [hg] with N hN
    simp only [ht', ite_eq_left hN.2.2.1]
  have ht'' : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t' N := by
    filter_upwards [ht, htt'] with N h1 h2; rwa [← h2]
  have hk0 : 0 < min κ 1 := lt_min hκ one_pos
  have hEk : |E| ≤ 2 - min κ 1 := hE.trans (by linarith [min_le_left κ 1])
  have hA : ∀ᶠ N : ℕ in atTop, 1 ≤ B.scale E N (t' N) := by
    filter_upwards [hg, htt'] with N h1 h2; rw [← h2]; exact h1.2.1
  have hB := BoundsCore_of_Thm221NoEL' X hκ hT hE hτ ht'0 ht''
  have h := stochDom_norm_Lval_of_LmK X hk0 (min_le_right κ 1) hEk ht'0 ht'1 hA hn
    (hB.LmK n (by omega))
  exact h.congr_eventually (by filter_upwards [htt'] with N hN; rw [hN])
    (by filter_upwards [htt'] with N hN; rw [hN])

end Induction


/-! ### 4. Satisfiability

The ticket's own warning: deleting a field can make the remaining ones jointly unsatisfiable,
and the compiler never says so.  Four compiled checks.

* **(2.67) survives the deletion.**  `RBM.BoundsCore_zero` is a *forward* witness: `BoundsCore`
  holds at `s ≡ 0`, for every sample, with no hypothesis beyond `|E| ≤ 2`.
* **The witness is at the critical scale, not at a collapsed one.**  At `s ≡ 0` the dominating
  side of every field of `RBM.BoundsCore` is `(W Im m^{(E)})^{-n} ≤ N^{-n/2}`
  (`RBM.Band.scale_zero_ge_rpow`), so the three `≺` statements are genuine decaying bounds, not
  `≺ 1`.  More generally `RBM.Band.eventually_rpow_le_scale` gives `W ℓ_t η_t ≥ N^c` with
  `c = min(τ,1)/32 > 0` at **every** time of the window `0 ≤ t ≤ 1 - N^{-1+τ}`, so the
  conclusion of `RBM.BoundsCore_of_Thm221NoEL'` is never vacuous either.
* **The step condition and the grid are jointly satisfiable** — `RBM.Band.cond272Reg_grid`:
  the truncated grid `u_k = min(1 - W^{-kτ'}, t)` of p. 24 satisfies `RBM.Cond272Reg` at every
  one of its steps with one and the same `c > 0`, inside the window `t ≤ 1 - N^{-1+τ}` that
  D13 added to Theorem 2.21.  This is the check T195 failed elsewhere.
* **Quantifier order.**  Every asymptotic condition here is `∀ᶠ N in atTop` *inside* the
  statement (`RBM.Cond272`, `RBM.Cond272'`, `RBM.StochDom`), with `c`, `τ`, `n` fixed first;
  `RBM.Band.cond272Reg_grid` exhibits `τ'`, `c`, `n₀` chosen **before** `E` and `t`, which is
  the order the induction needs and the one the paper uses on p. 24. -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- At `t = 0` the scale is `W Im m^{(E)} ≥ N^{1/2}·N^{c_B} Im m ≥ N^{1/2}`: the right-hand
sides of `RBM.BoundsCore_zero` are genuine decaying bounds.  (Same computation as
`RBM.cond272Reg_zero`, isolated.) -/
theorem Band.scale_zero_ge_rpow (B : Band Ω) {E : ℝ} (hE : |E| < 2) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((1 : ℝ) / 2) ≤ B.scale E N 0 := by
  have hm := mE_im_pos hE
  filter_upwards [B.bandwidth, eventually_le_rpow ((mE E).im)⁻¹ B.c_pos,
    eventually_ge_atTop 1] with N hW hC hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have h2 : (1 : ℝ) ≤ (N : ℝ) ^ B.c * (mE E).im := by
    have h := mul_le_mul_of_nonneg_right hC hm.le
    rwa [inv_mul_cancel₀ hm.ne'] at h
  have h3 : (N : ℝ) ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ B.c * (mE E).im) ≤ (B.W N : ℝ) * (mE E).im := by
    rw [← mul_assoc, ← Real.rpow_add hN0]
    exact mul_le_mul_of_nonneg_right hW hm.le
  rw [B.scale_zero E N]
  calc (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ ((1 : ℝ) / 2) * 1 := (mul_one _).symm
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ B.c * (mE E).im) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hN0.le _)
    _ ≤ _ := h3

/-- **The grid of p. 24 satisfies `RBM.Cond272Reg` at every step**, with `τ'`, `c > 0` and `n₀`
chosen from `κ, τ` alone and *before* `E` and `t`.

This is the joint satisfiability check D13 calls for: the window `t ≤ 1 - N^{-1+τ}` that
Theorem 2.21 now carries and the grid `1 - s_k = W^{-kτ'}` that the induction runs on are
compatible, and the step condition holds on the grid with a single `c`.  The witness for
`RBM.Cond272Reg` is produced by the grid itself (`RBM.Band.eventually_flow_grid'` followed by
`RBM.Cond272'.toCond272Reg`), not assumed. -/
theorem Band.cond272Reg_grid (B : Band Ω) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ,
      (∀ N, 0 ≤ t N) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      (∀ᶠ N : ℕ in atTop, gridT (B.W N) τ' (t N) n₀ = t N) ∧
      ∀ k : ℕ, Cond272Reg B E (fun N => gridT (B.W N) τ' (t N) k)
        (fun N => gridT (B.W N) τ' (t N) (k + 1)) c := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ := B.eventually_flow_grid' hκ hτ
  refine ⟨τ', hτ'0, c, hc0, n₀, fun E hE t ht0 ht => ?_⟩
  have hE2 : |E| < 2 := by linarith
  have hg := hgrid E hE t ht0 ht
  refine ⟨by filter_upwards [hg] with N hN; exact hN.1, fun k => ?_⟩
  have hst : ∀ N, gridT (B.W N) τ' (t N) k ≤ gridT (B.W N) τ' (t N) (k + 1) := fun N =>
    gridT_mono (B.one_le_W N) hτ'0.le (t N) (Nat.le_succ k)
  have ht1 : ∀ N, gridT (B.W N) τ' (t N) (k + 1) < 1 := fun N =>
    (min_le_left _ _).trans_lt (gridS_lt_one (by linarith [B.one_le_W N]) _)
  refine Cond272'.toCond272Reg hE2 hst ht1 hc0.le ?_
  filter_upwards [hg] with N hN
  rw [etaT_div_etaT hE2]
  exact hN.2.2.2 k

/-- **`W ℓ_t η_t ≥ N^c` everywhere in the window of Theorem 2.21**, with `c = min(τ,1)/32 > 0`
depending on `τ` only.  Two uses: it is the regime bound of `RBM.Cond272Reg` at the endpoint,
and it certifies that the conclusion of `RBM.BoundsCore_of_Thm221NoEL'` is not vacuous — the
dominating sides `(W ℓ_t η_t)^{-n}` really do go to zero like `N^{-nc}`. -/
theorem Band.eventually_rpow_le_scale (B : Band Ω) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ, (∀ N, 0 ≤ t N) →
      (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N) := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ := B.cond272Reg_grid hκ hτ
  refine ⟨c, hc0, fun E hE t ht0 ht => ?_⟩
  obtain ⟨hlast, hstep⟩ := hgrid E hE t ht0 ht
  -- the grid stays at `t` once it reaches it, so the step `n₀ → n₀ + 1` ends at `t`
  filter_upwards [hlast, (hstep n₀).2] with N h0 hc
  have hle : t N ≤ gridS (B.W N : ℝ) τ' n₀ :=
    min_eq_right_iff.1 (show min (gridS (B.W N : ℝ) τ' n₀) (t N) = t N from h0)
  have hle2 : t N ≤ gridS (B.W N : ℝ) τ' (n₀ + 1) :=
    hle.trans (gridS_mono (B.one_le_W N) hτ'0.le (Nat.le_succ n₀))
  rwa [gridT_of_le hle2] at hc

/-- **The hypotheses of `RBM.BoundsCore_of_Thm221NoEL'` other than Theorem 2.21 are jointly
satisfiable, at the critical end of the window.**  Explicit parameters: `κ = 1`, `E = 0`,
`τ` anything in `(0,1)`, and the boundary time `t = max(0, 1 - N^{-1+τ})`, for which
`1 - t = N^{-1+τ}` exactly for large `N` — the worst time Theorem 2.21 is asked about, not a
collapsed one.  The last conjunct records that the conclusion has content there. -/
theorem boundsCore_hyp_consistent (B : Band Ω) {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ t : ℕ → ℝ, (∀ N, 0 ≤ t N) ∧ (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) ∧
      (∀ᶠ N : ℕ in atTop, 1 - t N = (N : ℝ) ^ (-1 + τ)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale (0 : ℝ) N (t N) := by
  refine ⟨fun N => max 0 (1 - (N : ℝ) ^ (-1 + τ)), fun N => le_max_left _ _, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h1 : (N : ℝ) ^ (-1 + τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
    rcases max_cases (0 : ℝ) (1 - (N : ℝ) ^ (-1 + τ)) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h1 : (N : ℝ) ^ (-1 + τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
    rw [max_eq_right (by linarith)]
    ring
  · obtain ⟨c, hc0, hc⟩ := B.eventually_rpow_le_scale (κ := 1) one_pos hτ0
    refine ⟨c, hc0, hc 0 (by norm_num) _ (fun N => le_max_left _ _) ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h1 : (N : ℝ) ^ (-1 + τ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith)
    rw [max_eq_right (by linarith)]
    linarith

/-- **A fully explicit forward witness for `RBM.BoundsCore`.**

T202's non-degenerate dimensions (`RBM.Gauss.Dims.exampleGrow`: `L N ≍ N^{1/4} → ∞`,
`W N ≍ N^{3/4} → ∞`, `c = 1/8`) give an actual `RBM.Band`, and the Gaussian flow an actual
`RBM.Sample` on it.  On that model (2.68)–(2.70) hold at `s ≡ 0` **and** the dominating side is
genuinely small: `W ℓ_0 η_0 ≥ N^{1/2}`, so the three `≺` statements read `≺ N^{-n/2}`,
`≺ N^{-1}·decay` and `≺ N^{-1/4}`.  So the first induction is not vacuous at its starting
point, and the starting point is not a collapsed scale. -/
theorem boundsCore_gauss_witness :
    BoundsCore (Gauss.sample Gauss.Dims.exampleGrow) 0 (fun _ => 0) ∧
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (Gauss.band Gauss.Dims.exampleGrow).scale 0 N 0 :=
  ⟨BoundsCore_zero _ (by norm_num),
    (Gauss.band Gauss.Dims.exampleGrow).scale_zero_ge_rpow (E := 0) (by norm_num)⟩

end Satisfiable


/-! ### 5. Steps 1–5, chained — with no Step 6 datum anywhere

The five statements (2.73), (2.75), (2.76), (2.77), (2.78)/(2.79) of §2.7 are exactly what
`RBM.BoundsCore` needs at `t`, and every producer already in the tree takes `RBM.BoundsCore` (not
`RBM.Bounds`) as its input: `RBM.Step1.step1`, `RBM.MomentDuhamelCut.step2_cut`,
`RBM.Step2PP.flow_sharpLoop_glue_flowAs'`, `RBM.Step2PP.flow_steps45_glue_flowAs'`.  So the
chain below never mentions (2.71) or (2.80).

**The (2.72) shape in this section is `RBM.Cond272'`**, the form T204 could reach.  §5b
repeats the chain with D13's `RBM.Cond272Reg` (T209) and produces `RBM.Thm221NoEL` itself; this
section is kept because `RBM.BoundsCore_of_Thm221NoEL'` — the induction of p. 24 — runs on the
weaker `RBM.Thm221NoEL'`, which the grid supplies directly. -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **(2.68)–(2.70) at `t` from (2.75), (2.78) and (2.79)** — `RBM.BoundsCore_of_Steps` with the
bundle `RBM.Steps` replaced by the three fields it actually projects.  Taking the bundle would
make "(2.80) is available" a hypothesis of the (2.71)-free route, which is the packaging
circularity of T147 §0a. -/
theorem BoundsCore_of_flow (hst : ∀ N, s N ≤ t N) (hll : LocalLawFlow X E s t)
    (hLmK : SharpLmKFlow X E s t)
    (hdec : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) :
    BoundsCore X E t where
  LmK n hn := (hLmK n hn).precomp_param fun N u => (TimeIcc.last hst N, u)
  decay D hD := (hdec D hD).precomp_param fun N a => (TimeIcc.last hst N, a)
  localLaw := hll.precomp_param fun N ij => (TimeIcc.last hst N, ij)

/-- **Steps 3, 4 and 5 chained into (2.68)–(2.70) at `t`.**  Input: the conclusions (2.73) of
Step 1 and (2.75), (2.76) of Step 2, plus the four named hypotheses the `(+,+)` bootstrap and
the (5.48) reduction still take.  Output: `RBM.BoundsCore X E t`, i.e. the conclusion of the
(2.71)-free Theorem 2.21. -/
theorem boundsCore_step_of_flow (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hregS : Cond272' B E s t c)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (h548 : Step45.FlowEq548 X E s t) :
    BoundsCore X E t := by
  have hsharp : SharpLoopFlow X E s t := fun n hn =>
    Step2PP.flow_sharpLoop_glue_flowAs' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hΘ
      (fun m hm => h514 m (by omega)) hn
  obtain ⟨hLmK, hdec⟩ :=
    Step2PP.flow_steps45_glue_flowAs' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hsharp
      h45 hΘ h514 h548
  exact BoundsCore_of_flow hst hll hLmK hdec

/-- **Steps 1–5 chained: the step of the (2.71)-free Theorem 2.21.**

`RBM.BoundsCore X E s` in, `RBM.BoundsCore X E t` out, along
`RBM.Step1.step1 → RBM.MomentDuhamelCut.step2_cut → RBM.Step2PP.flow_sharpLoop_glue_flowAs' →
RBM.Step2PP.flow_steps45_glue_flowAs'`.  The remaining named hypotheses are the six that T176's
probe P1 left open on the Steps 1–5 half of the chain: `RBM.Step1.Hyp`,
`RBM.MomentDuhamelCut.MomentHypCut` (T197's truncated moment route, which replaces the
`RBM.MomentHyp.step` that T132c proved unprovable in its frozen shape), the `(+,+)` bootstrap
target `hΘ`, Lemma 5.14, (4.5) and (5.48).  **`hH`, `hFD`, `h5133` and every other Step 6 datum
are absent**, which is the point of the p. 25 variant. -/
theorem boundsCore_step_of_inputs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hregS : Cond272' B E s t c) (hB : BoundsCore X E s)
    (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (h548 : Step45.FlowEq548 X E s t) :
    BoundsCore X E t := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 B E s t := Step2.cond272_of_strict hE hst ht1 hc0 hregS
  have hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N) := by
    filter_upwards [Step2.eventually_R4_le_scale (B := B) hE hst ht1 hc0 hregS] with N hN
    exact (hN ⟨t N, hst N, le_rfl⟩).2
  have hapriori : AprioriFlow X E s t :=
    (Step1.step1 X hκ0 hEκ hB hs0 hst ht1 hcond hc0 hreg h1).1
  have hll : LocalLawFlow X E s t :=
    (MomentDuhamelCut.step2_cut X hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hregS).1
  exact boundsCore_step_of_flow X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hΘ h514 h45 h548

/-- **The (2.71)-free Theorem 2.21 from the inputs Steps 1–5 still take.**

The six inputs are demanded **only on the domain of a step of §2.7** — `|E| ≤ 2 - κ`,
`0 ≤ s ≤ t < 1`, and (2.72) with the gain — and not for arbitrary `E`, `s`, `t`: outside that
domain `RBM.Step1.Hyp` and `RBM.MomentDuhamelCut.MomentHypCut` are not expected to hold (at
`t ≥ 1` the Green function is singular), and quantifying over all of them would be an
unsatisfiable hypothesis of exactly the kind T164/T188 produced.

`RBM.BoundsCore_of_Thm221NoEL'` then runs the induction of p. 24 on the result. -/
theorem thm221NoEL'_of_inputs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272' B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272' B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272' B E s t c →
      StochDom B.P (Step3.flowXiLK X E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272' B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272' B E s t c → StepGlue.Eq45Flow X E s t)
    (h548 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272' B E s t c → Step45.FlowEq548 X E s t) :
    Thm221NoEL' X κ where
  step E hE c hc0 s t hs0 hst ht1 hregS hB :=
    boundsCore_step_of_inputs X hκ0 hκ1 hE hs0 hst ht1 hc0 hregS hB
      (h1 E hE s t hs0 hst ht1 c hc0 hregS) (Hy E hE s t hs0 hst ht1 c hc0 hregS)
      (hΘ E hE s t hs0 hst ht1 c hc0 hregS) (h514 E hE s t hs0 hst ht1 c hc0 hregS)
      (h45 E hE s t hs0 hst ht1 c hc0 hregS) (h548 E hE s t hs0 hst ht1 c hc0 hregS)

end Assembly

/-! ### 5b. The same chain with the **D13** step condition `RBM.Cond272Reg` (T209)

T204 left exactly one gap: `RBM.thm221NoEL'_of_inputs` produces `RBM.Thm221NoEL'`, the
`RBM.Cond272'` form, because Steps 2–5 consumed `hregS` verbatim while D13 fixes the step
condition to `RBM.Cond272Reg`.  T186 had shown that no bridge `RBM.Cond272Reg → RBM.Cond272'`
can be built from the arithmetic of `RBM.rpow_mul_rpow_le_of_pow_thirty` (at `a = 1`, `b = 30`
the gain `e` is forced to `≤ 0`).

T209 closes it by restating the three consumers instead.  Where `hregS` actually went:

* **Step 1** — `RBM.Step1.step1` already takes `RBM.Cond272` plus `N^c ≤ W ℓ_t η_t`, i.e.
  `RBM.Cond272Reg` on the nose.  Nothing to do.
* **Step 2** — `RBM.MomentDuhamelCut.step2_cut_of_reg`.  Of its three uses of `hregS`, (2.76)
  only ever wanted `RBM.Cond272`, the weak law already wanted `RBM.Cond272Reg`, and (2.75)
  wanted only the two scale facts `(η_s/η_u)^4 ≤ W ℓ_u η_u`, `N^c ≤ W ℓ_u η_u`
  (`RBM.StepGlue.eventually_R4_le_scale_of_cond272`) — the exponent `4` is far below `30`.
* **Steps 3–5** — `RBM.Step2PP.flow_sharpLoop_glue_flowAs_of_cond272'` and
  `RBM.Step2PP.flow_steps45_glue_flowAs_of_reg'`.  The glue used `hregS` only through
  `RBM.Step2.cond272_of_strict`; the one genuine consumer is
  `RBM.Step2PP.harith_flowAs_of_reg`, which wants `((1-s)/(1-t))^{30} ≤ W ℓ_t η_t` — the bare
  (2.72) inverted — together with `4 ≤ (W ℓ_t η_t)^{1/12}`, supplied by the regime bound.

No exponent anywhere in Steps 1–5 needed a gain, so the `δ`-budget is untouched: the `4δ ≤ c`
of `RBM.Cond272Reg.hA_phi` / `RBM.Cond272Reg.hA_betaStar` is not consumed on this path at all
(those two are the side conditions of the *moment* route, i.e. of the hypothesis
`RBM.MomentDuhamelCut.MomentHypCut`, not of the chain below).

**`RBM.Thm221NoEL` now has a producer**, and `RBM.Cond272'` does not occur in its hypothesis
list. -/

section AssemblyReg

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **Steps 3, 4 and 5 chained into (2.68)–(2.70) at `t`, from `RBM.Cond272Reg`.**  Verbatim
`RBM.boundsCore_step_of_flow` with the (2.72) side moved to D13's shape. -/
theorem boundsCore_step_of_flow_reg (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (h548 : Step45.FlowEq548 X E s t) :
    BoundsCore X E t := by
  have hsharp : SharpLoopFlow X E s t := fun n hn =>
    Step2PP.flow_sharpLoop_glue_flowAs_of_cond272' X hκ0 hκ1 hEκ hs0 hst ht1 hreg.1 hapriori hll
      hΘ (fun m hm => h514 m (by omega)) hn
  obtain ⟨hLmK, hdec⟩ :=
    Step2PP.flow_steps45_glue_flowAs_of_reg' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg.1 hreg.2
      hapriori hll hsharp h45 hΘ h514 h548
  exact BoundsCore_of_flow hst hll hLmK hdec

/-- **Steps 1–5 chained: the step of the (2.71)-free Theorem 2.21, in D13's shape.**

`RBM.BoundsCore X E s` in, `RBM.BoundsCore X E t` out, along
`RBM.Step1.step1 → RBM.MomentDuhamelCut.step2_cut_of_reg →
RBM.Step2PP.flow_sharpLoop_glue_flowAs_of_cond272' →
RBM.Step2PP.flow_steps45_glue_flowAs_of_reg'`.  The remaining named hypotheses are the same six
as in `RBM.boundsCore_step_of_inputs`; the only change is that the (2.72) side is
`RBM.Cond272Reg`, i.e. (2.72) **exactly as printed** plus the regime bound. -/
theorem boundsCore_step_of_inputs_reg (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s)
    (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (h548 : Step45.FlowEq548 X E s t) :
    BoundsCore X E t := by
  have hapriori : AprioriFlow X E s t :=
    (Step1.step1 X hκ0 hEκ hB hs0 hst ht1 hreg.1 hc0 hreg.2 h1).1
  have hll : LocalLawFlow X E s t :=
    (MomentDuhamelCut.step2_cut_of_reg X hκ0 hκ1 hEκ Hy h1 hB hs0 hst ht1 hc0 hreg.1 hreg.2).1
  exact boundsCore_step_of_flow_reg X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hapriori hll hΘ h514
    h45 h548

/-- **The (2.71)-free Theorem 2.21 in D13's shape, from the inputs Steps 1–5 still take.**

This is `RBM.thm221NoEL'_of_inputs` with `RBM.Cond272'` replaced by `RBM.Cond272Reg`
everywhere — in the conclusion *and* in the domain on which the six inputs are demanded, so
the inputs are asked for on a **larger** domain than before (`RBM.Cond272'` implies
`RBM.Cond272Reg`, `RBM.Cond272'.toCond272Reg`, and the converse fails,
`RBM.exists_cond272_not_rpow_le_scale`).

Together with `RBM.Thm221NoEL.toThm221NoEL'` this makes `RBM.Thm221NoEL'` a corollary of what
is produced here, so nothing downstream of T204 loses a producer. -/
theorem thm221NoEL_of_inputs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut X E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      StochDom B.P (Step3.flowXiLK X E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → StepGlue.Eq45Flow X E s t)
    (h548 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step45.FlowEq548 X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_reg X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg) (Hy E hE s t hs0 hst ht1 c hc0 hreg)
      (hΘ E hE s t hs0 hst ht1 c hc0 hreg) (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45 E hE s t hs0 hst ht1 c hc0 hreg) (h548 E hE s t hs0 hst ht1 c hc0 hreg)

/-- **The acceptance probe of T209**: `RBM.BoundsCore X E s` in, `RBM.BoundsCore X E t` out,
with the (2.72) side `RBM.Cond272Reg` and **no `RBM.Cond272'` anywhere** in the hypothesis
list.  Compare `RBM.Thm221NoEL'.step`, which is the same statement with `RBM.Cond272'`. -/
theorem Thm221NoEL.step_boundsCore_reg {κ : ℝ} (hT : Thm221NoEL X κ) (hE : |E| ≤ 2 - κ)
    {c : ℝ} (hc0 : 0 < c) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hreg : Cond272Reg B E s t c) (hB : BoundsCore X E s) : BoundsCore X E t :=
  hT.step E hE c hc0 s t hs0 hst ht1 hreg hB

/-- The two routes end at the *same* statement: `Eq` forces the conclusions of the
`RBM.Cond272'` chain and of the `RBM.Cond272Reg` chain to be one and the same
`RBM.BoundsCore X E t` (T107's technique).  Only the (2.72) hypothesis differs. -/
example (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c) (hregS : Cond272' B E s t c)
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hΘ : StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowAs B E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45 : StepGlue.Eq45Flow X E s t) (h548 : Step45.FlowEq548 X E s t) :
    boundsCore_step_of_flow X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hΘ h514 h45 h548 =
      boundsCore_step_of_flow_reg X hκ0 hκ1 hEκ hs0 hst ht1 hc0
        (hregS.toCond272Reg (by linarith [abs_nonneg E]) hst ht1 hc0.le)
        hapriori hll hΘ h514 h45 h548 := rfl

/-- **Joint satisfiability of a whole step, on the paper's own grid** (T209).

The check the ticket asks for: on the truncated grid `u_k = min(1 - W^{-kτ'}, t)` of p. 24,
with `τ'`, `c` and `n₀` chosen from `κ, τ` alone and **before** `E` and `t`, *all four* domain
conditions of `RBM.Thm221NoEL.step` — `0 ≤ u_k`, `u_k ≤ u_{k+1}`, `u_{k+1} < 1` and
`RBM.Cond272Reg … c` — hold simultaneously at every `k`, inside the window
`t ≤ 1 - N^{-1+τ}` that D13 added.  So the step condition consumed by
`RBM.boundsCore_step_of_inputs_reg` is not vacuous, and it is not satisfied only by a
degenerate (collapsed) window: `RBM.Band.cond272Reg_grid`'s last conjunct also pins the grid to
`t` at `k = n₀`.

The quantifier order is the paper's: `c` is chosen before `E` and `t` but the step of
`RBM.Thm221NoEL` quantifies `c` *inside*, because the grid caps the `c` it supplies at roughly
`τ/16` (paper-deltas #125). -/
theorem cond272Reg_grid_step_domain (B : Band Ω) {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ,
      (∀ N, 0 ≤ t N) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      (∀ᶠ N : ℕ in atTop, gridT (B.W N) τ' (t N) n₀ = t N) ∧
      ∀ k : ℕ, (∀ N, 0 ≤ gridT (B.W N) τ' (t N) k) ∧
        (∀ N, gridT (B.W N) τ' (t N) k ≤ gridT (B.W N) τ' (t N) (k + 1)) ∧
        (∀ N, gridT (B.W N) τ' (t N) (k + 1) < 1) ∧
        Cond272Reg B E (fun N => gridT (B.W N) τ' (t N) k)
          (fun N => gridT (B.W N) τ' (t N) (k + 1)) c := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ := B.cond272Reg_grid hκ hτ
  refine ⟨τ', hτ'0, c, hc0, n₀, fun E hE t ht0 ht => ?_⟩
  obtain ⟨hlast, hstep⟩ := hgrid E hE t ht0 ht
  refine ⟨hlast, fun k => ⟨fun N => ?_, fun N => ?_, fun N => ?_, hstep k⟩⟩
  · exact le_min (gridS_nonneg (B.one_le_W N) hτ'0.le k) (ht0 N)
  · exact gridT_mono (B.one_le_W N) hτ'0.le (t N) (Nat.le_succ k)
  · exact (min_le_left _ _).trans_lt (gridS_lt_one (by linarith [B.one_le_W N]) _)

end AssemblyReg


/-! ### 6. Downstream: Theorem 2.3 and (2.6)/(2.7) of Theorem 2.4 on `RBM.BoundsCore`

Every consumer in `Flow/Consequences.lean` except three uses only `RBM.Bounds.LmK`,
`RBM.Bounds.decay`, `RBM.Bounds.localLaw`, i.e. only the `RBM.BoundsCore` part; the statements
below are those consumers with `RBM.Bounds` weakened to `RBM.BoundsCore`, and the proof scripts
are copied unchanged (each is checked against its `RBM.Bounds` original by a `rfl`-probe, the
technique of T107).

The three exceptions are `RBM.expect_loop2_of_bounds` and
`RBM.expect_quantumDiffusion_pm/pp_of_bounds`, which are **(2.8) and (2.9) of Theorem 2.4** and
really do need (2.71) — the paper derives them from (2.62), and Theorem 2.5 (QUE) then uses
(2.8)/(2.9).  They are deliberately not restated here; that is T205's second induction.  Hanging
them on `RBM.BoundsCore` would make them vacuous or false, not merely weaker. -/

section Downstream

open scoped Matrix

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {κ τ E : ℝ} {z : ℕ → ℂ}

/-- **Lemmas 2.18–2.20 without (2.62), at the time `t = lemT z` of Lemma 2.8.**  Verbatim
`RBM.SpecSeq.bounds'` with `RBM.Thm221NoEL'` in place of `RBM.Thm221'`.  This is the only place
the (2.71)-free Theorem 2.21 enters the assembly below. -/
theorem SpecSeq.boundsCore (hz : SpecSeq κ τ E z) (X : Sample B) (hκ : 0 < κ)
    (hT : Thm221NoEL' X κ) (hτ : 0 < τ) : BoundsCore X E (fun N => lemT (z N)) :=
  BoundsCore_of_Thm221NoEL' X hκ hT (hz.abs_E_le hκ) (half_pos hτ) hz.lemT_nonneg
    (hz.eventually_rpow_le_one_sub hκ hτ)

/-- **Theorem 2.3, (2.3)** from (2.64) and (2.65), on `RBM.BoundsCore`. -/
theorem localLaw_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ij : B.Idx N × B.Idx N) ω =>
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2)) := by
  have h1 := hB.localLaw.trans
    (StochDom.of_unifDetDom (hz.unifDetDom_rpow hκ (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  refine T.green_sub_msc z hz.im_pos _ (StochDom.of_le_left (fun N ij ω => ?_) h1)
  rw [hz.lemE_eq N, Matrix.smul_apply, norm_smul, Sample.llErr]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (hz.lemT_lt_one' N).le

/-- **Theorem 2.3, (2.4)** in loop form, on `RBM.BoundsCore`. -/
theorem loop1_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true], [a]⟩ - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  have h1 := ((hB.LmK 1 le_rfl).trans
    (StochDom.of_unifDetDom (hz.unifDetDom_pow hκ 1))).precomp_param
    (fun N (a : ZMod (B.L N)) => ((fun _ => true, fun _ => a) : LoopData (B.L N) 1))
  have h2 := T1.loop1 z hz.im_pos (fun N _ => msc (z N)) (fun N _ => (B.zScale N (z N))⁻¹ ^ 1)
    (StochDom.of_le_left (fun N a ω => ?_) h1)
  · simpa only [pow_one] using h2
  have hidx : LoopData.idx ((fun _ => true, fun _ => a) : LoopData (B.L N) 1) =
      ⟨[true], [a]⟩ := by simp [LoopData.idx]
  rw [hidx, Sample.lkErr, Band.Kval, Kgen_one, msc_eq_sqrt_mul_mE (hz.im_pos N), hz.lemE_eq N,
    ← mul_sub, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.2 (hz.lemT_lt_one' N).le

/-- **Theorem 2.3, (2.4)** (partial tracial local law), on `RBM.BoundsCore`. -/
theorem partialTrace_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (a : ZMod (B.L N)) ω =>
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  refine StochDom.of_le_left (fun N a ω => le_of_eq ?_) (loop1_of_boundsCore T T1 hκ hz hB)
  rw [gloop_one_eq]

/-- **Theorem 2.4, (2.6)/(2.7)** in loop form, on `RBM.BoundsCore`. -/
theorem loop2_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) (σ₂ : Bool) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖gloop (B.L N) (B.W N) (T.Hband N ω) (z N) ⟨[true, σ₂], [ab.1, ab.2]⟩ -
          (lemT (z N) : ℂ) * B.Kval E N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  have h1 := ((hB.LmK 2 (by norm_num)).trans
    (StochDom.of_unifDetDom (hz.unifDetDom_pow hκ 2))).precomp_param
    (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) =>
      ((![true, σ₂], ![ab.1, ab.2]) : LoopData (B.L N) 2))
  refine T.loop2 z hz.im_pos σ₂
    (fun N ab => (lemT (z N) : ℂ) * B.Kval E N (lemT (z N)) ⟨[true, σ₂], [ab.1, ab.2]⟩) _
    (StochDom.of_le_left (fun N ab ω => ?_) h1)
  rw [LoopData.idx_two, hz.lemE_eq N, Sample.lkErr, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (hz.lemT_nonneg N)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hz.lemT_lt_one' N).le

/-- **Theorem 2.4, (2.6)**, on `RBM.BoundsCore`. -/
theorem quantumDiffusion_pm_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  refine StochDom.of_le_left (fun N ab ω => le_of_eq ?_) (loop2_of_boundsCore T hκ hz hB false)
  rw [gloop_pm_eq (T.hermitian N ω), ← hz.lemE_eq N, B.lemT_mul_Kval_pm N (hz.im_pos N)]

/-- **Theorem 2.4, (2.7)**, on `RBM.BoundsCore`. -/
theorem quantumDiffusion_pp_of_boundsCore (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (ab : ZMod (B.L N) × ZMod (B.L N)) ω =>
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹ ^ 2) := by
  refine StochDom.of_le_left (fun N ab ω => le_of_eq ?_) (loop2_of_boundsCore T hκ hz hB true)
  rw [gloop_pp_eq, ← hz.lemE_eq N, B.lemT_mul_Kval_pp N (hz.im_pos N)]

/-- **Theorem 2.3, the tracial local law**, on `RBM.BoundsCore`. -/
theorem trace_of_boundsCore (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hz : SpecSeq κ τ E z) (hB : BoundsCore X E (fun N => lemT (z N))) :
    StochDom B.P (fun N (_ : Unit) ω =>
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖)
      (fun N _ _ => (B.zScale N (z N))⁻¹) := by
  have h := StochDom.average (V := fun N => ZMod (B.L N)) (c := fun N => msc (z N))
    (ζ := fun N => (B.zScale N (z N))⁻¹) (partialTrace_of_boundsCore T T1 hκ hz hB)
  refine StochDom.of_le_left (fun N _ ω => le_of_eq ?_) h
  have hW : (B.W N : ℂ) ≠ 0 := by exact_mod_cast (B.W_pos N).ne'
  have hL : (B.L N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne (B.L N))
  simp only [ZMod.card, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, ← Finset.mul_sum]
  push_cast
  field_simp

/-- **Theorem 2.3 (local semicircle law) from the (2.71)-free Theorem 2.21.**  Verbatim the
conclusion of `RBM.localSemicircleLaw_of_Thm221'`, with `RBM.Thm221NoEL'` in place of
`RBM.Thm221'`. -/
theorem localSemicircleLaw_of_Thm221NoEL' (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ)
    (hT : Thm221NoEL' X κ) (hτ : 0 < τ) (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ij : B.Idx N × B.Idx N,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ ((1 : ℝ) / 2) <
        ‖(green (T.Hband N ω) (z N) - msc (z N) • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ij.1 ij.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ a : ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖(B.W N : ℂ)⁻¹ * ∑ x : Fin (B.W N), green (T.Hband N ω) (z N) (a, x) (a, x) - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ _u : Unit,
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ <
        ‖((B.L N * B.W N : ℕ) : ℂ)⁻¹ * (green (T.Hband N ω) (z N)).trace - msc (z N)‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) := by
  have hB := hz.boundsCore X hκ hT hτ
  exact ⟨B.prob_le_of_stochDom (fun N _ _ => Real.rpow_nonneg (hz.zScale_inv_nonneg N) _)
      (localLaw_of_boundsCore T hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (partialTrace_of_boundsCore T T1 hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => hz.zScale_inv_nonneg N)
      (trace_of_boundsCore T T1 hκ hz hB) hτ' hD⟩

/-- **(2.6) and (2.7) of Theorem 2.4 from the (2.71)-free Theorem 2.21.**  Verbatim the first
two conjuncts of `RBM.quantumDiffusion_of_Thm221'`.  The last two conjuncts of that theorem are
(2.8) and (2.9); they need (2.71) and are T205. -/
theorem quantumDiffusion_pm_pp_of_Thm221NoEL' (T : Transfer X) (hκ : 0 < κ)
    (hT : Thm221NoEL' X κ) (hτ : 0 < τ) (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            (green (T.Hband N ω) (z N))ᴴ * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) *
            Theta (B.L N) ((‖msc (z N)‖ ^ 2 : ℝ) : ℂ) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
    (∀ᶠ N : ℕ in atTop, B.P {ω | ∃ ab : ZMod (B.L N) × ZMod (B.L N),
      (B.W N : ℝ) ^ τ' * (B.zScale N (z N))⁻¹ ^ 2 <
        ‖(green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.1 *
            green (T.Hband N ω) (z N) * Eblk (B.L N) (B.W N) ab.2).trace -
          (B.W N : ℂ)⁻¹ * msc (z N) ^ 2 * Theta (B.L N) (msc (z N) ^ 2) ab.1 ab.2‖}
      ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) := by
  have hB := hz.boundsCore X hκ hT hτ
  exact ⟨B.prob_le_of_stochDom (fun N _ _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
      (quantumDiffusion_pm_of_boundsCore T hκ hz hB) hτ' hD,
    B.prob_le_of_stochDom (fun N _ _ => pow_nonneg (hz.zScale_inv_nonneg N) _)
      (quantumDiffusion_pp_of_boundsCore T hκ hz hB) hτ' hD⟩

/-! #### `rfl`-probes: the (2.71)-free statements are the old ones

`Eq` forces both sides to have the same type, so each of these type-checks only if the two
conclusions are definitionally equal (T107's technique).  Nothing has been weakened; only the
hypothesis moved from `RBM.Bounds` to `RBM.BoundsCore`. -/

example (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    localLaw_of_bounds T hκ hz hB = localLaw_of_boundsCore T hκ hz hB.toBoundsCore := rfl

example (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    partialTrace_of_bounds T T1 hκ hz hB =
      partialTrace_of_boundsCore T T1 hκ hz hB.toBoundsCore := rfl

example (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    quantumDiffusion_pm_of_bounds T hκ hz hB =
      quantumDiffusion_pm_of_boundsCore T hκ hz hB.toBoundsCore := rfl

example (T : Transfer X) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    quantumDiffusion_pp_of_bounds T hκ hz hB =
      quantumDiffusion_pp_of_boundsCore T hκ hz hB.toBoundsCore := rfl

example (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hz : SpecSeq κ τ E z)
    (hB : Bounds X E (fun N => lemT (z N))) :
    trace_of_bounds T T1 hκ hz hB = trace_of_boundsCore T T1 hκ hz hB.toBoundsCore := rfl

example (T : Transfer X) (T1 : TransferLoop1 T) (hκ : 0 < κ) (hT : Thm221' X κ)
    (hTn : Thm221NoEL' X κ) (hτ : 0 < τ) (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ')
    (hD : 0 < D) :
    localSemicircleLaw_of_Thm221' T T1 hκ hT hτ hz hτ' hD =
      localSemicircleLaw_of_Thm221NoEL' T T1 hκ hTn hτ hz hτ' hD := rfl

example (T : Transfer X) (hκ : 0 < κ) (hT : Thm221' X κ) (hTn : Thm221NoEL' X κ) (hτ : 0 < τ)
    (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    (quantumDiffusion_of_Thm221' T hκ hT hτ hz hτ' hD).1 =
      (quantumDiffusion_pm_pp_of_Thm221NoEL' T hκ hTn hτ hz hτ' hD).1 := rfl

example (T : Transfer X) (hκ : 0 < κ) (hT : Thm221' X κ) (hTn : Thm221NoEL' X κ) (hτ : 0 < τ)
    (hz : SpecSeq κ τ E z) {τ' D : ℝ} (hτ' : 0 < τ') (hD : 0 < D) :
    (quantumDiffusion_of_Thm221' T hκ hT hτ hz hτ' hD).2.1 =
      (quantumDiffusion_pm_pp_of_Thm221NoEL' T hκ hTn hτ hz hτ' hD).2 := rfl

end Downstream

end RBM
