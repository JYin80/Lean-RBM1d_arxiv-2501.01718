/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarInputs
import RBM1D.Gauss.MomentDuhamelCut

/-!
# (5.45) in the far field: `M_m` is the conclusion, not an input (T216)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.20)–(5.21), (5.42), (5.44)–(5.48).

`RBM1D/Hierarchy/Step2FarInputs.lean` (T208) pinned the far-field drift and left exactly one
input open: the fourth field of `RBM.Step2FarInputs.FarInputs'`, a bound

`‖farMart‖ ≤ M_m · T_{v,D}` at the far arguments, with `M_m ≺ 1`,

where `RBM.Step2FarInputs.farMart` is *defined* as the defect of the Duhamel identity (5.21).
In the paper that bound is (5.45), proved from the quadratic variation (5.44) by BDG (5.24).
This file settles what the moment route can do with it.

## The answer, in one line

`M_m ≺ 1` is **equivalent** to the far half of (5.48) that it is used to prove
(`farMart_far_equiv`: `norm_farMart_le_tT` and `far_bound_of_farMart_tT`, with the *same*
additive constant), so it is not an input that can be supplied from weaker data.  The defect
is `(L-K)_v` minus two terms that the *other* three fields of `FarInputs'` already control, so
bounding it **is** bounding `(L-K)_v` in the far field.  In particular the a priori (5.47),
`J*_{v,D} ≺ (η_s/η_v)²`, gives only `M_m ≺ (η_s/η_v)²`, and that is *not* `≺ 1` on the grid
`1 - s_k = W^{-kτ'}` of Lemmas 2.18–2.20 (`etaRatio_sq_not_detDom`,
`cFarStep'_apriori_not_detDom`, packaged as `Mm_slot_decides`).

So (5.45) in the far field is not wiring; it is the far half of (5.48) under another name, and
on the moment route it has to come from the second-order term of the generator identity — the
`E ⊗ E` of (5.42) integrated as in (5.44) — applied to the **defect**, which is a path
functional of `{H_u : u ∈ [s,v]}` and not a function of the current matrix.  See *What is
missing* below.

## What is built

* `RBM.Step2FarMart.lkFar`, `jSfar` — the far-restricted loop error and the far-restricted
  `J*_{u,D}` of (5.29), i.e. `RBM.Step2.jStar` of the loop error truncated to
  `‖a₁ - a₂‖ > 6ℓ*_u`.  `jSfar ≥ 1` always (`one_le_jSfar`), so asking for `jSfar ≺ 1` is
  asking for the **critical** value, never for `0`.
* `RBM.Step2FarMart.stochDom_far_of_jSfar`, `flowEq548_of_jSfar` — `jSfar ≺ 1` *is* the far
  half of (5.48): it produces the `hfar` of `RBM.Step2MomentStep.flowEq548_of_near_far`, hence
  `RBM.Step45.FlowEq548`, **with no `M_m`, no martingale and no drift bundle in the hypothesis
  list**.  This is the shape any producer of the far half should target.
* `RBM.Step2FarMart.ellStar_mono_time`, `far_mono_time`, `lkFar_crossing` — **the compiled
  satisfiability audit of the obvious next move.**  The far family *shrinks* with `u`, so
  `jSfar` jumps downwards whenever `6ℓ*_u` crosses an achieved distance; a
  `RBM.MomentDuhamelCut.CutHyp` for `jSfar` would need the two-sided `modulus` (and
  `stochDom_of_net` the `ContinuousOn`), which is therefore **not** available.  No such bundle
  is defined here on purpose — it would be an unsatisfiable hypothesis of the kind this
  project keeps producing.
* `RBM.Step2FarMart.norm_init_add_drift_le` — the two known terms of (5.21) in the far field,
  i.e. `RBM.Step2FarInputs.step_bound_far'` with the loop error and the defect removed.
* `RBM.Step2FarMart.norm_farMart_le`, `norm_farMart_le_tT` — the defect bound, pathwise:
  `‖farMart‖ ≤ (J_f + Ξ(M_i + M_f·len) + 1) T_{v,D}` at far arguments, for any far a priori
  bound `J_f` on `(L-K)_v`.
* `RBM.Step2FarMart.far_bound_of_farMart`, `far_bound_of_farMart_tT`, `farMart_far_equiv` —
  the converse and the two-directional package.
* `RBM.Step2FarMart.farInputs'_of_far_apriori` — **the fourth field of `FarInputs'`, supplied
  by a theorem**: all four fields of `RBM.Step2FarInputs.FarInputs'` from (2.69), (5.35) and a
  far a priori bound, with `M_m = RBM.Step2FarInputs.cFarStep' B E s M_i M_f J_f`.
* `RBM.Step2FarMart.detDom_Mm_of_far` — `M_m ≺ 1` from `J_f ≺ 1`, `M_i ≺ 1`, `M_f(1-s) ≺ 1`,
  through `RBM.Step2FarInputs.detDom_cFarStep'` (whose only non-hypothesis ingredient is the
  theorem `Ξ ≺ 1`).

## The negative half, compiled

* `RBM.Step2FarMart.etaRatio_sq_not_detDom` — `(η_s/η_t)²` is not `≺ 1` on a grid with
  `1 - t = (1 - s)²`, which is the shape of the grid of Lemmas 2.18–2.20.
* `RBM.Step2FarMart.cFarStep'_detDom_far_critical` and `cFarStep'_apriori_not_detDom`, packaged
  as `Mm_slot_decides` — on the **same** grid and the **same** critical drift
  `M_f = (1-s)^{-1}` (not the degenerate `M_f = 0`, which by
  `RBM.Step2FarInputs.farDrift_eq_zero_of_farInputs'_zero` would force the model's drift to
  vanish), the far-field constant is `≺ 1` with `J_f ≡ 1` and is *not* `≺ 1` with
  `J_f = (η_s/η_v)²`.  The two witnesses differ only in the `M_m` slot, so the gap is located
  exactly at (5.45).

## What is missing, and where

The moment-route substitute for BDG is the generator identity applied to `|Φ_u|^{2p}` with
`Φ_u = (U_{u,v}∘(L-K)_u)_a - (U_{s,v}∘(L-K)_s)_a - ∫_s^u (U_{w,v}∘F_w)_a dw`, for which the
first-order term cancels by `RBM.Gauss.hasDerivAt_ukerObsT_drift` and only the
`E ⊗ E` term survives.  Two ingredients for that are **not** in the repository:

1. `Φ_u` involves `(L-K)_s`, an `H_s`-measurable random constant, so the identity has to be
   read under the law conditioned on `H_s`; `RBM.Sample` carries no filtration and no Markov
   property, and `RBM.MomentDuhamel.Hyp` is an interface for *deterministic* test functions of
   `(u, H_u)`.
2. `Φ_u` carries the additive functional `∫_s^u (U_{w,v}∘F_w)_a dw`, so the state has to be
   extended by it and the generator by `(U_{u,v}∘F_u)_a ∂_A`.

Both are decisions about the `RBM.MomentDuhamel` interface, not lemmas; they are recorded for
Cowork rather than guessed at here.

## Degeneracy checks

* `RBM.Step2FarMart.farMart_self` — at the collapsed window `v = s` the defect is `0`, so the
  fourth field of `FarInputs'` is then trivially true and carries no information.  (This is
  the `s = v` check the project's satisfiability discipline asks for: the hypothesis is *not*
  false at the degenerate point, it is empty there, and the content lives at `s < v`.)
* `one_le_jSfar` — the far functional is `≥ 1` identically, so `jSfar ≺ 1` is critical, not
  vacuous.
* Every hypothesis here is a bound *at a given `(N, ω)`*, never a bound quantified over all
  `ω`; the `ω = 0` accident of T164 cannot occur.

## What T228 adds: D15 → option 3, and `M_m` deleted

Cowork's ruling on D15 (2026-09-21 18:10) is option 3 of §3: widen the far threshold to
`12ℓ*_u` and smooth the indicator on `[6ℓ*_u, 12ℓ*_u]`.  Then the far functional is continuous
in `u`, the bootstrap applies, and the `M_m` line is no longer needed at all.

* `RBM.Step2FarMart.nearChi`, `farChi` — the smooth weights, built from T175's quintic Hermite
  profile `RBM.Cutoff.cutChi` (no new cutoff; `|χ'| ≤ 15/8` is T175's *sharp* constant).
  `nearChi_eq_one`, `nearChi_eq_zero`, `indicator_le_nearChi`, `abs_nearChi_sub_le`.
* `RBM.Step2FarMart.lkFarSm`, `jSfarSm` — the far-restricted loop error and `J*` with the
  smooth weight.  `one_le_jSfarSm` (`≥ 1` identically, so `≺ 1` is critical),
  `norm_lk_le_jSfarSm_mul` (past `12ℓ*_u` the weight is `1`, so nothing is given away there).
* `RBM.Step2FarMart.stochDom_eq548W_of_near_of_jSfarSm`, `flowEq548W_of_jSfarSm`,
  `flow_sharpDecay_of_jSfarSm` — the sharp near half (5.47) and `jSfarSm ≺ 1` give
  `RBM.Step45.FlowEq548W` and then **(2.79) verbatim**.  The mechanism is the splitting
  identity `norm_lk_eq_near_add_far`, not a triangle inequality through the Duhamel defect, so
  **`M_m`, the martingale, `FarInputs'` and the drift bundle are all absent**.
* `RBM.Step2FarMart.continuousOn_jSfarSm` — the key structural point: the smoothed functional
  inherits the time-continuity of the loop error, whereas `jSfar` jumps whatever the loop error
  does (`lkFar_crossing`).  `abs_jSfarSm_sub_le` + `abs_lkFarSm_ratio_sub_le` reduce
  `RBM.MomentDuhamelCut.CutHyp.modulus` to a modulus for `|(L-K)_u|/T_{u,D}` plus a `15/8`
  Lipschitz term.  `sharp_vs_smooth_at_crossing` is the contrast in one statement.
* `RBM.Step2FarMart.stochDom_jSfarSm_of_cutHyp`, `flowEq548W_of_cutHyp`,
  `flow_sharpDecay_of_cutHyp` — the hook-up to `RBM.MomentDuhamelCut.stochDom_of_cutHyp` at the
  threshold `Θ ≡ 1`.
* §12 `nearChi_nine_ellStar`, `exists_farChi_eq_one`, `jSfarSm_ge_of_farChi_eq_one`,
  `sat_mesh_card_at_one`, `pref_grid_critical`, `smooth_route_nondegenerate` — the
  satisfiability audit (not fiat, not vacuous, critical scale, net conditions jointly solvable
  with `mesh_fine` at equality).

⚠ §3's negative results stand as stated: they are about the **sharp** `jSfar`, and T228 does
not contradict them — it changes the functional.

## Deviations from the paper (paper-deltas `T216a`, `T228a`, `T228b`)

The paper's (5.45) bounds the stopped martingale `∫_s^{T∧t'}(U_{u,t'}∘E^{(M)})_a` and its
right-hand side is `[(η_s/η_{t'})²·1(‖a₁-a₂‖ ≤ 6ℓ*_{t'}) + 1]`.  Here the left-hand side is
the Duhamel **defect** `RBM.Step2FarInputs.farMart` (T208's choice: it makes (5.20) a `rfl`
and removes the free tensor), there is no stopping time (the truncation is
`RBM.MomentDuhamelCut.cutTrunc`, already recorded for T158/T175), and only the far half of the
right-hand side — the summand `1`, at `‖a₁-a₂‖ > 6ℓ*_v` — is ever asserted.  The near half
`(η_s/η_{t'})²` is *not* assumed anywhere, which is what T208b requires: asserting the far
value `M_m ≺ 1` at the near arguments as well would be unsatisfiable.

**`T228a`** — the far threshold of (5.48) is `12ℓ*_u`, not `6ℓ*_u`, and the indicator is
smoothed on `[6ℓ*_u, 12ℓ*_u]` by `RBM.Cutoff.cutChi`.  The paper's (5.48) is a statement at a
fixed time with the endpoint threshold, so it is unaffected; the Lean statement
`RBM.Step45.FlowEq548` is uniform in `u ∈ [s,t]`, and there the sharp indicator is
discontinuous in `u` (§3).  Everything downstream of (5.48) is unchanged
(`RBM.Step45.decay_of_split_W` has the same conclusion as `decay_of_split`).

**`T228b`** — the far half of (5.48) is obtained by a **bootstrap in `u`** over the window
`[s,t]` (`RBM.MomentDuhamelCut.stochDom_of_cutHyp` at `Θ ≡ 1`), whereas the paper obtains it at
each fixed time from (5.45) by BDG.  The Lean route therefore needs a modulus of continuity in
`u` and an initial bound at `u = s_N`, neither of which appears in the paper's argument; in
exchange it needs no martingale inequality, which is what the repository cannot state
(no filtration on `RBM.Sample`, see §*What is missing*).
-/

namespace RBM
namespace Step2FarMart

open Real Filter MeasureTheory

/-! ### 1. The far-restricted `J*` of (5.29) -/

section FarJ

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The loop error restricted to the far field**, `|(L-K)_{u,(+,-),a}|·1(‖a₁-a₂‖ > 6ℓ*_u)`.
This is the left-hand side of the far half of (5.48). -/
noncomputable def lkFar (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℝ :=
  fun a => if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N u)
           then 0 else ‖Step2.lk X E N u ω a‖

/-- **(5.29) in the far field**: `J*_{u,D}` of the far-restricted loop error.  Exactly
`RBM.Step2.jS` with the near-diagonal arguments zeroed out. -/
noncomputable def jSfar (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  Step2.jStar (B.L N) (lkFar X E N u ω) (B.W N) (B.ell N u) (etaT E u) D

variable (X : Sample B) {E D : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}

theorem lkFar_nonneg (a : LoopArg (B.L N) 2) : 0 ≤ lkFar X E N u ω a := by
  unfold lkFar; split_ifs
  · exact le_rfl
  · exact norm_nonneg _

theorem lkFar_eq_of_far {a : LoopArg (B.L N) 2}
    (ha : ¬ ((zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N u))) :
    lkFar X E N u ω a = ‖Step2.lk X E N u ω a‖ := by
  unfold lkFar; simp [ha]

theorem lkFar_le (a : LoopArg (B.L N) 2) :
    lkFar X E N u ω a ≤ ‖Step2.lk X E N u ω a‖ := by
  unfold lkFar; split_ifs
  · exact norm_nonneg _
  · exact le_rfl

/-- **The far functional is `≥ 1` identically.**  So `jSfar ≺ 1` is the *critical* request:
it cannot be satisfied by the degenerate `jSfar ≡ 0`, exactly as the threshold `Θ ≡ 1` of
`RBM.MomentDuhamelCut.MomentHypCut` is critical for the near half. -/
theorem one_le_jSfar : 1 ≤ jSfar X E D N u ω := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  exact Step2.one_le_jStar hW0 (lkFar_nonneg X)

theorem jSfar_nonneg : 0 ≤ jSfar X E D N u ω := le_trans zero_le_one (one_le_jSfar X)

/-- `|(L-K)_{v,a}| ≤ J*^{far}_{v,D} · T_{v,D}(‖a₁-a₂‖)` at the far arguments. -/
theorem norm_lk_le_jSfar_mul {a : LoopArg (B.L N) 2}
    (ha : ¬ ((zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N u))) :
    ‖Step2.lk X E N u ω a‖
      ≤ jSfar X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have h := Step2.le_jStar_mul (f := lkFar X E N u ω) (ℓu := B.ell N u) (ηu := etaT E u)
    (D := D) hW0 a
  rwa [lkFar_eq_of_far X ha] at h

/-- Conversely, a far-field bound `|(L-K)_v| ≤ c T_{v,D}` gives `J*^{far}_{v,D} ≤ c + 1`. -/
theorem jSfar_le {c : ℝ}
    (hc : ∀ a : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖Step2.lk X E N u ω a‖
          ≤ c * Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1))) (hc0 : 0 ≤ c) :
    jSfar X E D N u ω ≤ c + 1 := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  refine Step2.jStar_le hW0 fun a => ?_
  unfold lkFar
  split_ifs with hb
  · have : (0 : ℝ) ≤ Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) := tailT_nonneg hW0.le _
    positivity
  · exact hc a hb

end FarJ

/-! ### 2. `jSfar ≺ 1` **is** the far half of (5.48)

`RBM.Step2MomentStep.flowEq548_of_near_far` splits (5.48) into the near half — the sharp
(5.47), `J*_{u,D} ≺ (η_s/η_u)²`, which T207 delivers — and the far half, the same bound with
no prefactor beyond `6ℓ*_u`.  That far half is *literally* `jSfar ≺ 1`. -/

section Far548

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **`jSfar ≺ 1` gives `hfar`.**  The far-restricted `J*` dominates the far-restricted loop
error pointwise (`norm_lk_le_jSfar_mul`), and the near arguments contribute nothing because the
left-hand side is `0` there. -/
theorem stochDom_far_of_jSfar {D : ℝ}
    (hj : StochDom B.P (fun N (u : TimeIcc s t N) ω => jSfar X E D N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
          then 0 else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
        (zdist (B.L N) (p.2.1 - p.2.2))) := by
  refine StochDom.of_subset_union hj hj fun τ hτ =>
    ⟨τ, hτ, Filter.Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  refine Or.inl ?_
  dsimp only at hp
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hT0 : (0 : ℝ) < tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
      (zdist (B.L N) (p.2.1 - p.2.2)) := tailT_pos hW0 _
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  split_ifs at hp with hnear
  · exact absurd hp (by nlinarith)
  · refine ⟨p.1, ?_⟩
    dsimp only
    set a : LoopArg (B.L N) 2 := ![p.2.1, p.2.2] with hadef
    have ha0 : a 0 = p.2.1 := rfl
    have ha1 : a 1 = p.2.2 := rfl
    have hnear' : ¬ ((zdist (B.L N) (a 0 - a 1) : ℝ)
        ≤ 6 * ellStar (B.W N : ℝ) (B.ell N (p.1 : ℝ))) := by rw [ha0, ha1]; exact hnear
    have heq : X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) = ‖Step2.lk X E N (p.1 : ℝ) ω a‖ := by
      rw [Step2.norm_lk_eq, ha0, ha1]
    have hle := norm_lk_le_jSfar_mul (E := E) (D := D) (ω := ω) X hnear'
    rw [ha0, ha1] at hle
    rw [heq] at hp
    rw [mul_one]
    unfold Step2.tT at hle
    nlinarith

/-- **(5.48) from the far-restricted `J*`.**  `RBM.Step45.FlowEq548` with the far half read as
`jSfar ≺ 1`: no `FarInputs'`, no drift bundle, and in particular **no `M_m`**. -/
theorem flowEq548_of_jSfar
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (hj : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => jSfar X E D N (u : ℝ) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548 X E s t :=
  Step2MomentStep.flowEq548_of_near_far X hnear fun D hD => stochDom_far_of_jSfar X (hj D hD)

end Far548

/-! ### 3. Why the far half is **not** a bootstrap

`RBM.MomentDuhamelCut.CutHyp` is generic in the functional, so the obvious next move is to
bootstrap `jSfar` by the machinery the near half uses.  It does not work, and this section
compiles the reason: the far family shrinks with `u`, so `jSfar` has downward jumps and
neither `CutHyp.modulus` nor the `ContinuousOn` of
`RBM.MomentDuhamelCut.stochDom_of_net` is available for it.  No `CutHyp` for `jSfar` is
defined here; it would be an unsatisfiable bundle. -/

section FarCut

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- `ℓ*_u = (log W)^{3/2} ℓ̂_u` is non-decreasing in `u`, because `ℓ̂` is
(`RBM.Step3.ellHat_mono`). -/
theorem ellStar_mono_time {N : ℕ} (hW1 : (1 : ℝ) ≤ (B.W N : ℝ)) {w v : ℝ} (hwv : w ≤ v)
    (hv1 : v < 1) :
    ellStar (B.W N : ℝ) (B.ell N w) ≤ ellStar (B.W N : ℝ) (B.ell N v) := by
  have hlogW : 0 ≤ log (B.W N : ℝ) := Real.log_nonneg hW1
  have hp : (0 : ℝ) ≤ log (B.W N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogW _
  have h : B.ell N w ≤ B.ell N v := Step3.ellHat_mono (L := B.L N) hwv hv1
  unfold ellStar
  nlinarith

/-- **The far index set shrinks with time.**  `6ℓ*_u` grows, so an argument that is far at a
later time was far at every earlier time — never the other way round. -/
theorem far_mono_time {N : ℕ} (hW1 : (1 : ℝ) ≤ (B.W N : ℝ)) {w v : ℝ} (hwv : w ≤ v)
    (hv1 : v < 1) {d : ℝ} (h : ¬ (d ≤ 6 * ellStar (B.W N : ℝ) (B.ell N v))) :
    ¬ (d ≤ 6 * ellStar (B.W N : ℝ) (B.ell N w)) := by
  have hmono := ellStar_mono_time (B := B) hW1 hwv hv1
  intro hc
  exact h (by linarith)

/-- **⚠ Why `jSfar` cannot be bootstrapped by the machinery of
`RBM.MomentDuhamelCut.CutHyp`.**

An argument `a` at distance `d` is *removed* from the far family at the time `u₀` where
`6ℓ*_{u₀}` first reaches `d`: just before, `lkFar` at `a` is `|(L-K)_u(a)|`; at `u₀` and after,
it is `0`.  The far functional therefore jumps **downwards** at each such crossing, by the full
contribution of the crossing argument, and the size of the jump does not go to `0` with the
time increment.

`RBM.MomentDuhamelCut.CutHyp.modulus` demands a *two-sided* modulus of continuity
`|J v ω - J w ω| ≤ N^{Kmod}|v-w|^γ` valid for **every** `ω`, and
`RBM.MomentDuhamelCut.stochDom_of_net` demands `ContinuousOn`; neither holds for `jSfar`.  So
a `CutHyp` for `jSfar` at threshold `Θ ≡ 1` is **not** a weaker input to be handed to the
producer of `RBM.MomentDuhamelCut.CutHyp.moment` — it is an unsatisfiable bundle, and this
file deliberately does not define one.  Smoothing the cut-off in `d` restores continuity but
moves the far threshold from `6ℓ*_u` to `12ℓ*_u`, which
`RBM.Step2MomentStep.flowEq548_of_near_far` does not accept.

Read positively: the far half of (5.48) is a statement at each **fixed** `v`, obtained from
the one-step bound — which is how the paper proves it (via (5.45)) and why the martingale
enters there and nowhere else. -/
theorem lkFar_crossing {N : ℕ} {ω : Ω} {w v : ℝ} (a : LoopArg (B.L N) 2)
    (hw : ¬ ((zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N w)))
    (hv : (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N v)) :
    lkFar X E N w ω a = ‖Step2.lk X E N w ω a‖ ∧ lkFar X E N v ω a = 0 :=
  ⟨lkFar_eq_of_far X hw, by unfold lkFar; simp [hv]⟩

end FarCut

/-! ### 4. The Duhamel defect, and why `M_m` is the conclusion

`RBM.Step2FarInputs.farMart` is `(L-K)_v` minus the two terms of (5.21) that the *other* three
fields of `RBM.Step2FarInputs.FarInputs'` already bound.  So the triangle inequality turns any
far a priori bound on `(L-K)_v` into a bound on the defect, and conversely.  Both directions
are proved here; together they say that the fourth field is **equivalent** to the far half of
(5.48), not an independent input. -/

section Defect

open Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

/-- **The two known terms of (5.21), in the far field.**  This is
`RBM.Step2FarInputs.step_bound_far'` with the loop error and the defect removed: it bounds the
initial term `U_{s,v}∘(L-K)_s` and the drift integral `∫_s^v U_{u,v}∘F_u`, the two summands of
the Duhamel identity that the drift inputs of `FarInputs'` control.  The proof is that of
`step_bound_far'` up to its last line, where the triangle inequality is applied in the other
direction. -/
theorem norm_init_add_drift_le (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D' Mi Mn Mf len : ℝ} (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn) (hMf : 0 ≤ Mf)
    (hlen : v - s N ≤ len)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn)
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (a : LoopArg (B.L N) 2)
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ)) :
    ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Step2.lk X E N (s N) ω) a‖
      + ‖∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
          ((v : ℝ) : ℂ) (farDrift X E N u ω) a‖
      ≤ Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len)
            * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
        + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
            * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := by
  have hL1 : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hm0 := mE_im_pos hE
  have hlogW : 0 ≤ log (B.W N : ℝ) :=
    Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hW)
  have hlen0 : 0 ≤ len := le_trans (by linarith) hlen
  have hTv0 : (0 : ℝ) ≤ Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1)) :=
    tailT_nonneg hW0.le _
  have hR0 : (0 : ℝ) ≤ etaT E (s N) / etaT E v := by
    rw [Step2.etaT_ratio hE]
    have : (0 : ℝ) < 1 - v := by linarith
    have : (0 : ℝ) ≤ 1 - s N := by linarith
    positivity
  have hellv : 1 ≤ B.ell N v := one_le_ellHat_of_nonneg hL1 hv0 hv1
  have hstv : 0 ≤ ellStar (B.W N : ℝ) (B.ell N v) := by
    unfold ellStar
    have hp : (0 : ℝ) ≤ log (B.W N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogW _
    nlinarith
  have hd1 : ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by linarith
  -- the split of the drift into its near and far parts, as in `far_le_of_farInputs'`
  have hFnb : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ‖farDriftNear X E N u ω b‖
        ≤ Mn * (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
                then 1 else 0) := by
    intro u hu b
    unfold farDriftNear
    split_ifs with hb
    · rw [mul_one]; exact hFn u hu b hb
    · simp
  have hFrb : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ‖farDrift X E N u ω b - farDriftNear X E N u ω b‖
        ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := by
    intro u hu b
    unfold farDriftNear
    split_ifs with hb
    · rw [sub_self, norm_zero]
      have : (0 : ℝ) ≤ Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := tailT_nonneg hW0.le _
      positivity
    · rw [sub_zero]; exact hFr u hu b hb
  -- (5.39): the initial term
  have hI := Step2MomentStep.norm_Uker_far_flow hE hs0 hsv hv0 hv1 hW hMi hinit a hd1
  -- (5.41): the drift, pointwise in `u ∈ [s, v)`
  have hdrift : ∀ u ∈ Set.Ico (s N) v,
      ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (farDrift X E N u ω) a‖
        ≤ 128 * exp 3 * Mn * (etaT E (s N) / etaT E v) ^ 2
              * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
          + Mf * (Step2.xiK (B.L N) (B.W N) (mE E).im
              * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
            + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (B.W N : ℝ) ^ (-D')) := by
    intro u hu
    have hu0 : 0 ≤ u := hs0.trans hu.1
    have huv : u ≤ v := hu.2.le
    have hu1 : u < 1 := hu.2.trans hv1
    have hru : etaT E u / etaT E v ≤ etaT E (s N) / etaT E v := by
      rw [Step2.etaT_ratio hE, Step2.etaT_ratio hE]
      gcongr
      linarith [hu.1]
    have hru0 : (0 : ℝ) ≤ etaT E u / etaT E v := by
      rw [Step2.etaT_ratio hE]
      have : (0 : ℝ) < 1 - v := by linarith
      have : (0 : ℝ) ≤ 1 - u := by linarith
      positivity
    have hsplit : farDrift X E N u ω
        = farDriftNear X E N u ω + fun b => farDrift X E N u ω b - farDriftNear X E N u ω b := by
      funext b; simp
    rw [hsplit, Uker_add, Pi.add_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Step2MomentStep.norm_Uker_supp_flow hE hu0 huv hv1 hW hMn (hFnb u hu) a
        hfar).trans ?_
      have he3 : (0 : ℝ) ≤ exp 3 := (exp_pos _).le
      gcongr
    · refine (Step2MomentStep.norm_Uker_far_flow hE hu0 huv hv0 hv1 hW hMf (hFrb u hu) a
        hd1).trans ?_
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hMf
      gcongr
  set C : ℝ := 128 * exp 3 * Mn * (etaT E (s N) / etaT E v) ^ 2
        * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
      + Mf * (Step2.xiK (B.L N) (B.W N) (mE E).im
          * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
        + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (B.W N : ℝ) ^ (-D')) with hCdef
  have hΞ0 : (0 : ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hWD : (0 : ℝ) ≤ (B.W N : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hmi : (0 : ℝ) ≤ ((mE E).im ^ 2)⁻¹ := by positivity
  have hE5 : (0 : ℝ) ≤ exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := (exp_pos _).le
  have hC0 : (0 : ℝ) ≤ C := by rw [hCdef]; positivity
  have hint : ‖∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
      ((v : ℝ) : ℂ) (farDrift X E N u ω) a‖ ≤ C * |v - s N| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume v] with u hne hu
    rw [Set.uIoc_of_le hsv] at hu
    exact hdrift u ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩
  have hvs : |v - s N| ≤ len := by rw [abs_of_nonneg (by linarith)]; linarith
  have hint' : ‖∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
      ((v : ℝ) : ℂ) (farDrift X E N u ω) a‖ ≤ C * len :=
    hint.trans (mul_le_mul_of_nonneg_left hvs hC0)
  rw [hCdef] at hint'
  nlinarith [hI, hint']

/-- **The defect bound from a far a priori bound.**  `farMart` is `(L-K)_v` minus the two
terms bounded by `norm_init_add_drift_le`, so any far-field bound `|(L-K)_v| ≤ J_f T_{v,D'}`
gives `‖farMart‖ ≤ (J_f + Ξ(M_i + M_f·len)) T_{v,D'} + residues`. -/
theorem norm_farMart_le (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D' Jf Mi Mn Mf len : ℝ} (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn) (hMf : 0 ≤ Mf)
    (hlen : v - s N ≤ len)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn)
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (a : LoopArg (B.L N) 2)
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ))
    (hJ : ‖Step2.lk X E N v ω a‖
      ≤ Jf * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))) :
    ‖farMart X E s N v ω a‖
      ≤ (Jf + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len))
            * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
        + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
            * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := by
  have hkey := norm_init_add_drift_le X hE hs0 hsv hv1 hW hMi hMn hMf hlen hinit hFn hFr a hfar
  have hdef : farMart X E s N v ω a
      = Step2.lk X E N v ω a
        - Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
            (Step2.lk X E N (s N) ω) a
        - ∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
            ((v : ℝ) : ℂ) (farDrift X E N u ω) a := rfl
  have htri : ‖farMart X E s N v ω a‖
      ≤ ‖Step2.lk X E N v ω a‖
        + (‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Step2.lk X E N (s N) ω) a‖
          + ‖∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
              ((v : ℝ) : ℂ) (farDrift X E N u ω) a‖) := by
    rw [hdef]
    refine (norm_sub_le _ _).trans ?_
    have := norm_sub_le (Step2.lk X E N v ω a)
      (Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Step2.lk X E N (s N) ω) a)
    linarith
  have hTv0 : (0 : ℝ) ≤ Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1)) := by
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    exact tailT_nonneg hW0.le _
  nlinarith [htri, hkey, hJ]

/-- **The converse.**  The Duhamel identity is an identity, so a bound on the defect gives back
a far-field bound on `(L-K)_v`.  This is `RBM.Step2FarInputs.step_bound_far'` again; it is
restated here so that the equivalence "`M_m` small ⟺ (5.48) far" is compiled in both
directions in one place. -/
theorem far_bound_of_farMart (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D' Mm Mi Mn Mf len : ℝ} (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn) (hMf : 0 ≤ Mf)
    (hlen : v - s N ≤ len)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn)
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (a : LoopArg (B.L N) 2)
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ))
    (hmart : ‖farMart X E s N v ω a‖
      ≤ Mm * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))) :
    ‖Step2.lk X E N v ω a‖
      ≤ (Mm + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len))
            * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
        + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
            * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := by
  have hkey := norm_init_add_drift_le X hE hs0 hsv hv1 hW hMi hMn hMf hlen hinit hFn hFr a hfar
  have htri : ‖Step2.lk X E N v ω a‖
      ≤ (‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (Step2.lk X E N (s N) ω) a‖
          + ‖∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
              ((v : ℝ) : ℂ) (farDrift X E N u ω) a‖)
        + ‖farMart X E s N v ω a‖ := by
    rw [farDrift_duhamel X (s := s) N v ω a]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hTv0 : (0 : ℝ) ≤ Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1)) := by
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    exact tailT_nonneg hW0.le _
  nlinarith [htri, hkey, hmart]

/-- The tail function is non-increasing in the decay exponent. -/
theorem tT_mono {N : ℕ} {D D' v ℓ : ℝ} (hW : (1 : ℝ) ≤ (B.W N : ℝ)) (hDD : D ≤ D') :
    Step2.tT B E N D' v ℓ ≤ Step2.tT B E N D v ℓ := by
  have hDW : (B.W N : ℝ) ^ (-D') ≤ (B.W N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW (by linarith)
  unfold Step2.tT tailT
  have : (0 : ℝ) ≤ (((B.W N : ℝ) * B.ell N v * etaT E v) ^ 2)⁻¹
      * exp (-√(ℓ / B.ell N v)) := by positivity
  linarith

/-- **The fourth field of `RBM.Step2FarInputs.FarInputs'`, supplied by a theorem.**  The
residues are absorbed into `W^{-D} ≤ T_{v,D}` exactly as in
`RBM.Step2FarInputs.lkErr_far_le'`, so the constant is

`M_m = J_f + Ξ (M_i + M_f · len) + 1`,

which is `RBM.Step2FarInputs.cFarStep'` with the far a priori constant `J_f` in the slot where
`M_m` used to sit.  **That is the point**: the martingale constant and the far-field constant
are the same object. -/
theorem norm_farMart_le_tT (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D D' Jf Mi Mn Mf len : ℝ} (hDD : D ≤ D') (hJf : 0 ≤ Jf) (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn)
    (hMf : 0 ≤ Mf) (hlen : v - s N ≤ len)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn)
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hres : ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
          * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
        ≤ (B.W N : ℝ) ^ (-D))
    (a : LoopArg (B.L N) 2)
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ))
    (hJ : ‖Step2.lk X E N v ω a‖
      ≤ Jf * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))) :
    ‖farMart X E s N v ω a‖
      ≤ (Jf + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + 1)
          * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hW
  have hkey := norm_farMart_le X hE hs0 hsv hv1 hW hMi hMn hMf hlen hinit hFn hFr a hfar hJ
  have hmono : Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
      ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := tT_mono hW1 hDD
  have hWT : (B.W N : ℝ) ^ (-D) ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) :=
    rpow_neg_le_tailT _
  have hΞ0 : (0 : ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hlen0 : 0 ≤ len := le_trans (by linarith) hlen
  have hcoef : (0 : ℝ) ≤ Jf + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) := by
    have : (0 : ℝ) ≤ Mi + Mf * len := by positivity
    nlinarith
  nlinarith [hkey, mul_le_mul_of_nonneg_left hmono hcoef, hres, hWT]

/-- The converse of `norm_farMart_le_tT`, with the residues absorbed in the same way. -/
theorem far_bound_of_farMart_tT (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D D' Mm Mi Mn Mf len : ℝ} (hDD : D ≤ D') (hMm : 0 ≤ Mm) (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn)
    (hMf : 0 ≤ Mf) (hlen : v - s N ≤ len)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn)
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hres : ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
          * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
        ≤ (B.W N : ℝ) ^ (-D))
    (a : LoopArg (B.L N) 2)
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ))
    (hmart : ‖farMart X E s N v ω a‖
      ≤ Mm * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))) :
    ‖Step2.lk X E N v ω a‖
      ≤ (Mm + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + 1)
          * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hW
  have hkey := far_bound_of_farMart X hE hs0 hsv hv1 hW hMi hMn hMf hlen hinit hFn hFr a hfar
    hmart
  have hmono : Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1))
      ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := tT_mono hW1 hDD
  have hWT : (B.W N : ℝ) ^ (-D) ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) :=
    rpow_neg_le_tailT _
  have hΞ0 : (0 : ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hlen0 : 0 ≤ len := le_trans (by linarith) hlen
  have hcoef : (0 : ℝ) ≤ Mm + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) := by
    have : (0 : ℝ) ≤ Mi + Mf * len := by positivity
    nlinarith
  nlinarith [hkey, mul_le_mul_of_nonneg_left hmono hcoef, hres, hWT]

/-- **`M_m ≺ 1` and the far half of (5.48) are the same statement**, up to the additive
constant `Ξ(M_i + M_f·len) + 1` — which is `≺ 1` by
`RBM.Step2FarInputs.eventually_xiK_le` together with (2.69) and (5.35) integrated.  Both
implications hold with the *same* constant, so neither is a weaker input than the other, and
the fourth field of `RBM.Step2FarInputs.FarInputs'` cannot be discharged from the other three
plus (5.47). -/
theorem farMart_far_equiv (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D D' c Mi Mn Mf len : ℝ} (hDD : D ≤ D') (hc : 0 ≤ c) (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn)
    (hMf : 0 ≤ Mf) (hlen : v - s N ≤ len)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn)
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hres : ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
          * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
        ≤ (B.W N : ℝ) ^ (-D))
    (a : LoopArg (B.L N) 2)
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ)) :
    (‖Step2.lk X E N v ω a‖ ≤ c * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1)) →
        ‖farMart X E s N v ω a‖
          ≤ (c + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + 1)
            * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))
      ∧ (‖farMart X E s N v ω a‖ ≤ c * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1)) →
        ‖Step2.lk X E N v ω a‖
          ≤ (c + Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + 1)
            * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) :=
  ⟨fun h => norm_farMart_le_tT X hE hs0 hsv hv1 hW hDD hc hMi hMn hMf hlen hinit hFn hFr hres
      a hfar h,
   fun h => far_bound_of_farMart_tT X hE hs0 hsv hv1 hW hDD hc hMi hMn hMf hlen hinit hFn hFr
      hres a hfar h⟩

/-- **The defect vanishes on the collapsed window.**  At `v = s` the Duhamel identity is
`(L-K)_s = (L-K)_s`, so `farMart = 0` and the fourth field of
`RBM.Step2FarInputs.FarInputs'` is *empty* there rather than false: the degenerate point is on
the right side of the satisfiability discipline, and all the content is at `s < v`. -/
theorem farMart_self (hE : |E| ≤ 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) (hs1 : s N < 1)
    (a : LoopArg (B.L N) 2) : farMart X E s N (s N) ω a = 0 := by
  have hL : 3 ≤ B.L N := B.three_le_L N
  have hξ : xiOf (mSigma E) Step2.sigPM = fun _ => (1 : ℂ) := Step2.sigPM_xi hE
  have ht : ∀ i : Fin 2, ‖(((s N : ℝ) : ℂ)) * xiOf (mSigma E) Step2.sigPM i‖ < 1 := by
    intro i
    rw [hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs1
  have hU := congrFun (Uker_self (B.L N) hL ht (Step2.lk X E N (s N) ω)) a
  change Step2.lk X E N (s N) ω a
      - Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((s N : ℝ) : ℂ)
          (Step2.lk X E N (s N) ω) a
      - (∫ u in (s N)..(s N), Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ)
          ((s N : ℝ) : ℂ) (farDrift X E N u ω) a) = 0
  rw [intervalIntegral.integral_same, hU]
  ring

end Defect

/-! ### 5. The fourth field of `FarInputs'`, and `M_m ≺ 1` -/

section Supply

open Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.Step2FarInputs.FarInputs'`, all four fields, from a far a priori bound.**  The
martingale constant produced is `RBM.Step2FarInputs.cFarStep' B E s M_i M_f J_f`, i.e. the
far-field constant with the far a priori bound `J_f` in the slot where `M_m` sat.  Nothing
about a martingale is used: the fourth field is the first three plus the far bound, by the
triangle inequality. -/
theorem farInputs'_of_far_apriori (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {N : ℕ} (hW : exp 1 ≤ (B.W N : ℝ)) {D D' : ℝ} (hDD : D ≤ D')
    {Mi Mn Mf Jf : ℕ → ℝ} (hJf : 0 ≤ Jf N) (hMi : 0 ≤ Mi N) (hMn : 0 ≤ Mn N)
    (hMf : 0 ≤ Mf N) (hres : FarResidue' B E s t D D' Mi Mn Mf N) {ω : Ω}
    (hinit : ∀ b : LoopArg (B.L N) 2, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi N * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hnear : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn N)
    (hfarD : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hJ : ∀ v : TimeIcc s t N, ∀ b : LoopArg (B.L N) 2,
      6 * ellStar (B.W N : ℝ) (B.ell N (v : ℝ)) ≤ (zdist (B.L N) (b 0 - b 1) : ℝ) →
        ‖Step2.lk X E N (v : ℝ) ω b‖
          ≤ Jf N * Step2.tT B E N D' (v : ℝ) (zdist (B.L N) (b 0 - b 1))) :
    FarInputs' X E s t D Mi Mn Mf (cFarStep' B E s Mi Mf Jf) N ω := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := lt_of_lt_of_le (exp_pos 1) hW
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hW
  have hs1 : s N < 1 := lt_of_le_of_lt (hst N) (ht1 N)
  have hlen0 : (0 : ℝ) ≤ 1 - s N := by linarith
  refine ⟨fun b => (hinit b).trans (mul_le_mul_of_nonneg_left (tT_mono hW1 hDD) hMi),
    fun u hu b hb => hnear u hu b hb,
    fun u hu b hb => (hfarD u hu b hb).trans (mul_le_mul_of_nonneg_left (tT_mono hW1 hDD) hMf),
    fun v x y hxy => ?_⟩
  set a : LoopArg (B.L N) 2 := ![x, y] with hadef
  have ha0 : a 0 = x := rfl
  have ha1 : a 1 = y := rfl
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_lt v.2.2 (ht1 N)
  have hsv : s N ≤ (v : ℝ) := v.2.1
  have hvlen : (v : ℝ) - s N ≤ 1 - s N := by linarith
  have hfar' : 6 * ellStar (B.W N : ℝ) (B.ell N (v : ℝ))
      ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by rw [ha0, ha1]; exact hxy
  have hJa := hJ v a hfar'
  -- the residue, transported from `t N` to `v`
  have hvt : (v : ℝ) ≤ t N := v.2.2
  have h1t : (0 : ℝ) < 1 - t N := by linarith [ht1 N]
  have hRv : etaT E (s N) / etaT E (v : ℝ) ≤ etaT E (s N) / etaT E (t N) := by
    rw [Step2.etaT_ratio hE, Step2.etaT_ratio hE]
    gcongr
  have hRv0 : (0 : ℝ) ≤ etaT E (s N) / etaT E (v : ℝ) := by
    rw [Step2.etaT_ratio hE]
    have : (0 : ℝ) < 1 - (v : ℝ) := by linarith
    positivity
  have hmi : (0 : ℝ) ≤ ((mE E).im ^ 2)⁻¹ := by positivity
  have hWD : (0 : ℝ) ≤ (B.W N : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hE5 : (0 : ℝ) ≤ exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := (exp_pos _).le
  have hresv : ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E (v : ℝ)) ^ 2
          * (Mi N + Mf N * (1 - s N)) * (B.W N : ℝ) ^ (-D')
      + 128 * exp 3 * (Mn N * (1 - s N)) * (etaT E (s N) / etaT E (v : ℝ)) ^ 2
          * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
      ≤ (B.W N : ℝ) ^ (-D) := by
    refine le_trans ?_ hres
    have hsq : (etaT E (s N) / etaT E (v : ℝ)) ^ 2
        ≤ (etaT E (s N) / etaT E (t N)) ^ 2 := by gcongr
    have he3 : (0 : ℝ) ≤ exp 3 := (exp_pos _).le
    have h1 : (0 : ℝ) ≤ Mi N + Mf N * (1 - s N) := by positivity
    have h2 : (0 : ℝ) ≤ Mn N * (1 - s N) := by positivity
    gcongr
  have hkey := norm_farMart_le_tT X hE (hs0 N) hsv hv1 hW hDD hJf hMi hMn hMf hvlen hinit
    (fun u hu b hb => hnear u ⟨hu.1, lt_of_lt_of_le hu.2 v.2.2⟩ b hb)
    (fun u hu b hb => hfarD u ⟨hu.1, lt_of_lt_of_le hu.2 v.2.2⟩ b hb) hresv a hfar' hJa
  rw [ha0, ha1] at hkey
  refine hkey.trans (le_of_eq ?_)
  rw [cFarStep']
  ring

/-- **`M_m ≺ 1` from `J_f ≺ 1`.**  The constant produced by `farInputs'_of_far_apriori` is
`RBM.Step2FarInputs.cFarStep'`, so `RBM.Step2FarInputs.detDom_cFarStep'` — whose only
non-hypothesis ingredient is the theorem `Ξ ≺ 1` — discharges it from `M_i ≺ 1`,
`M_f(1-s) ≺ 1` and the far a priori `J_f ≺ 1`. -/
theorem detDom_Mm_of_far (B : Band Ω) (E : ℝ) {s : ℕ → ℝ} {Mi Mf Jf : ℕ → ℝ}
    (hs1 : ∀ N, s N ≤ 1) (hMi : ∀ N, 0 ≤ Mi N) (hMf : ∀ N, 0 ≤ Mf N)
    (hMi' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mi N ≤ (N : ℝ) ^ τ)
    (hMf' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mf N * (1 - s N) ≤ (N : ℝ) ^ τ)
    (hJf' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Jf N ≤ (N : ℝ) ^ τ) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      cFarStep' B E s Mi Mf Jf N ≤ (N : ℝ) ^ τ :=
  detDom_cFarStep' B E hs1 hMi hMf hMi' hMf' hJf'

end Supply

/-! ### 6. Why (5.47) is not enough: the `M_m` slot decides

The a priori bound the moment route delivers without the far-field argument is (5.47),
`J*_{v,D} ≺ (η_s/η_v)²`.  Feeding *that* into `farInputs'_of_far_apriori` gives
`M_m ≍ (η_s/η_v)²`, and the resulting far-field constant is **not** `≺ 1`.  The two witnesses
below sit on the same grid and the same critical drift `M_f = (1-s)^{-1}`, and differ only in
the `M_m` slot — so the gap is located exactly at (5.45), and nowhere else. -/

section Sharp

open Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A grid step of the shape of Lemmas 2.18–2.20: `1 - t = (1 - s)²`, i.e. `η_s/η_t` a genuine
power of `N`.  (On the paper's grid `1 - s_k = W^{-kτ'}`, so `η_{s_k}/η_{s_{k+1}} = W^{τ'}`;
the square is the same phenomenon with `τ'` at its largest.) -/
noncomputable def sGrid (N : ℕ) : ℝ := 1 - 1 / ((N : ℝ) + 1)

/-- The right endpoint of the grid step, `1 - t = (1 - s)²`. -/
noncomputable def tGrid (N : ℕ) : ℝ := 1 - 1 / (((N : ℝ) + 1) ^ 2)

theorem one_sub_sGrid (N : ℕ) : 1 - sGrid N = 1 / ((N : ℝ) + 1) := by rw [sGrid]; ring

theorem one_sub_tGrid (N : ℕ) : 1 - tGrid N = 1 / (((N : ℝ) + 1) ^ 2) := by rw [tGrid]; ring

theorem sGrid_nonneg (N : ℕ) : 0 ≤ sGrid N := by
  have h : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : 1 / ((N : ℝ) + 1) ≤ 1 := by rw [div_le_one h]; linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [sGrid]; linarith

theorem sGrid_le_one (N : ℕ) : sGrid N ≤ 1 := by
  have h : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  rw [sGrid]; linarith

theorem sGrid_le_tGrid (N : ℕ) : sGrid N ≤ tGrid N := by
  have h : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h2 : 1 / (((N : ℝ) + 1) ^ 2) ≤ 1 / ((N : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by positivity) h]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [sGrid, tGrid]; linarith

theorem tGrid_lt_one (N : ℕ) : tGrid N < 1 := by
  have h : (0 : ℝ) < 1 / (((N : ℝ) + 1) ^ 2) := by positivity
  rw [tGrid]; linarith

/-- On that grid `η_s/η_t = N + 1`, so `(η_s/η_t)²` is a genuine power of `N`. -/
theorem etaRatio_grid {E : ℝ} (hE : |E| < 2) (N : ℕ) :
    etaT E (sGrid N) / etaT E (tGrid N) = (N : ℝ) + 1 := by
  have h : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [Step2.etaT_ratio hE, one_sub_sGrid, one_sub_tGrid]
  field_simp

/-- **`(η_s/η_t)²` is not `≺ 1`.**  So (5.47) alone cannot produce the martingale constant of
(5.45): the triangle inequality of `norm_farMart_le_tT` is short by exactly this factor. -/
theorem etaRatio_sq_not_detDom {E : ℝ} (hE : |E| < 2) :
    ¬ (∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
        (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2 ≤ (N : ℝ) ^ τ) := by
  intro h
  obtain ⟨N, hN, hN1⟩ := ((h (1 / 2) (by norm_num)).and (Filter.eventually_ge_atTop 1)).exists
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [etaRatio_grid hE] at hN
  have hup : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) := by
    calc (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  nlinarith

/-- **The positive witness**, at the critical scaling: `M_i = 1`, `M_f = (1-s)^{-1}` — the size
(5.35) gives, and *not* the degenerate `M_f = 0`, which by
`RBM.Step2FarInputs.farDrift_eq_zero_of_farInputs'_zero` would force the model's drift to
vanish — and the far a priori `J_f = 1`, i.e. the far half of (5.48).  Then `M_m ≺ 1`. -/
theorem cFarStep'_detDom_far_critical (B : Band Ω) (E : ℝ) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      cFarStep' B E sGrid (fun _ => 1) (fun N => (N : ℝ) + 1) (fun _ => 1) N ≤ (N : ℝ) ^ τ := by
  refine detDom_cFarStep' B E sGrid_le_one (fun _ => zero_le_one)
    (fun N => by positivity) ?_ ?_ ?_
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN using hN
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have heq : ((N : ℝ) + 1) * (1 - sGrid N) = 1 := by
      rw [one_sub_sGrid]; field_simp
    rw [heq]; exact hN
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN using hN

/-- **The negative witness**, on the *same* data with only the `M_m` slot changed to what
(5.47) supplies, `J_f = (η_s/η_v)²`: the far-field constant is then not `≺ 1`, so (5.48) gives
nothing beyond (5.47) in the far field.  This is the precise sense in which `M_m ≺ 1` cannot be
obtained from the a priori bound by rearranging the pathwise inputs. -/
theorem cFarStep'_apriori_not_detDom (B : Band Ω) {E : ℝ} (hE : |E| < 2) :
    ¬ (∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
        cFarStep' B E sGrid (fun _ => 1) (fun N => (N : ℝ) + 1)
          (fun N => (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2) N ≤ (N : ℝ) ^ τ) := by
  intro h
  refine etaRatio_sq_not_detDom hE fun τ hτ => ?_
  filter_upwards [h τ hτ] with N hN
  have hΞ0 : (0 : ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hs1 : sGrid N ≤ 1 := sGrid_le_one N
  have hpos : (0 : ℝ) ≤ (1 : ℝ) + ((N : ℝ) + 1) * (1 - sGrid N) := by
    have h1 : (0 : ℝ) ≤ 1 - sGrid N := by linarith
    positivity
  have hle : (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2
      ≤ cFarStep' B E sGrid (fun _ => 1) (fun N => (N : ℝ) + 1)
          (fun N => (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2) N := by
    rw [cFarStep']
    nlinarith
  linarith

/-- **The two-sided check in one statement.**  Same grid, same critical drift, same `M_i`: the
far-field constant is `≺ 1` when the `M_m` slot carries the far-field conclusion `J_f ≡ 1`, and
is *not* `≺ 1` when it carries what (5.47) gives.  So the whole content of (5.45) in the far
field is the far half of (5.48) itself. -/
theorem Mm_slot_decides (B : Band Ω) {E : ℝ} (hE : |E| < 2) :
    (∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
        cFarStep' B E sGrid (fun _ => 1) (fun N => (N : ℝ) + 1) (fun _ => 1) N ≤ (N : ℝ) ^ τ)
      ∧ ¬ (∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
        cFarStep' B E sGrid (fun _ => 1) (fun N => (N : ℝ) + 1)
          (fun N => (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2) N ≤ (N : ℝ) ^ τ) :=
  ⟨cFarStep'_detDom_far_critical B E, cFarStep'_apriori_not_detDom B hE⟩

end Sharp

/-! ### 7. The smoothed threshold (T228; D15 → option 3)

§3 located the obstruction exactly: the *sharp* indicator `1(d ≤ 6ℓ*_u)` makes the far-field
functional jump in `u`.  Cowork's ruling on D15 is to widen the threshold to `12ℓ*_u` and
interpolate smoothly in `[6ℓ*_u, 12ℓ*_u]`.  The profile is T175's quintic Hermite cutoff
`RBM.Cutoff.cutChi` — `1` on `(-∞,1]`, `0` on `[2,∞)`, `C²`, with the *sharp* derivative bound
`|χ'| ≤ 15/8` — so no new cutoff is built here, and the Lipschitz constant is a rational
number rather than an invented one.

`RBM.Step45.decay_of_split_W` shows the widening is free downstream: Step 5 uses the weight
only through "`w = 0` beyond `12ℓ*_u`", and (5.32) (`RBM.inv_sq_le_tailT`) holds at every
constant `C ≥ 0`, so the whole cost is `e^{√12(log W)^{3/4}}` in place of
`e^{√6(log W)^{3/4}}` — both `W^{o(1)}`. -/

section SmoothThreshold

open Cutoff

/-- **The smooth near-field weight** `χ(d / 6ℓ*_u)`: `1` for `d ≤ 6ℓ*_u`, `0` for `d ≥ 12ℓ*_u`,
`C²` in between. -/
noncomputable def nearChi (W ℓu d : ℝ) : ℝ := cutChi (d / (6 * ellStar W ℓu))

/-- **The smooth far-field weight** `1 - χ(d / 6ℓ*_u)`: `0` for `d ≤ 6ℓ*_u`, `1` for
`d ≥ 12ℓ*_u`.  This is the multiplier that replaces the indicator of `RBM.Step2FarMart.lkFar`
and removes its jump. -/
noncomputable def farChi (W ℓu d : ℝ) : ℝ := 1 - nearChi W ℓu d

/-- `ℓ*_u = (log W)^{3/2}ℓ_u > 0` as soon as `W ≥ 2` and `ℓ_u > 0`.  This is the side condition
of `RBM.Step2FarMart.nearChi_eq_zero`, and it is why the far vanishing of the weight is stated
*eventually* in `N`: at `W = 1` the scale `ℓ*` degenerates to `0`. -/
theorem ellStar_pos_of_two_le {W ℓu : ℝ} (hW : 2 ≤ W) (hℓ : 0 < ℓu) : 0 < ellStar W ℓu := by
  have hlog : 0 < Real.log W := Real.log_pos (by linarith)
  have : 0 < Real.log W ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hlog _
  unfold ellStar
  positivity

/-- `ℓ*_u ≥ 0` whenever `W ≥ 1` — the side condition of `nearChi_eq_one` and hence of
`indicator_le_nearChi`.  (`RBM.ellStar` is `(log W)^{3/2}ℓ_u`, and the `rpow` of the negative
`log W` at `W < 1` need not be nonnegative, so `W ≥ 1` is not decoration.) -/
theorem ellStar_nonneg_of_one_le {W ℓu : ℝ} (hW : 1 ≤ W) (hℓ : 0 ≤ ℓu) : 0 ≤ ellStar W ℓu := by
  have hlog : 0 ≤ Real.log W := Real.log_nonneg hW
  unfold ellStar
  positivity

theorem nearChi_nonneg (W ℓu d : ℝ) : 0 ≤ nearChi W ℓu d := cutChi_nonneg _

theorem nearChi_le_one (W ℓu d : ℝ) : nearChi W ℓu d ≤ 1 := cutChi_le_one _

theorem farChi_nonneg (W ℓu d : ℝ) : 0 ≤ farChi W ℓu d := by
  have := nearChi_le_one W ℓu d; unfold farChi; linarith

theorem farChi_le_one (W ℓu d : ℝ) : farChi W ℓu d ≤ 1 := by
  have := nearChi_nonneg W ℓu d; unfold farChi; linarith

theorem nearChi_add_farChi (W ℓu d : ℝ) : nearChi W ℓu d + farChi W ℓu d = 1 := by
  unfold farChi; ring

/-- On the near field `d ≤ 6ℓ*_u` the weight is `1`, so the smoothed (5.48) is *exactly* the
sharp one there: no information is given away where the prefactor `(η_s/η_u)²` lives. -/
theorem nearChi_eq_one {W ℓu d : ℝ} (hstar : 0 ≤ ellStar W ℓu) (hd : d ≤ 6 * ellStar W ℓu) :
    nearChi W ℓu d = 1 := by
  refine cutChi_eq_one ?_
  rcases eq_or_lt_of_le hstar with h | h
  · rw [← h]; norm_num
  · rw [div_le_one (by linarith)]; exact hd

theorem farChi_eq_zero {W ℓu d : ℝ} (hstar : 0 ≤ ellStar W ℓu) (hd : d ≤ 6 * ellStar W ℓu) :
    farChi W ℓu d = 0 := by
  unfold farChi; rw [nearChi_eq_one hstar hd]; ring

/-- Beyond `12ℓ*_u` the near weight vanishes: this is the field `hwfar` that
`RBM.Step45.decay_of_split_W` consumes, and the reason the threshold had to move from `6` to
`12`. -/
theorem nearChi_eq_zero {W ℓu d : ℝ} (hstar : 0 < ellStar W ℓu) (hd : 12 * ellStar W ℓu ≤ d) :
    nearChi W ℓu d = 0 := by
  refine cutChi_eq_zero ?_
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- Beyond `12ℓ*_u` the far weight is `1`, so `RBM.Step2FarMart.jSfarSm` really does control
`(L-K)` there: the smoothing does **not** make the far request vacuous. -/
theorem farChi_eq_one {W ℓu d : ℝ} (hstar : 0 < ellStar W ℓu) (hd : 12 * ellStar W ℓu ≤ d) :
    farChi W ℓu d = 1 := by
  unfold farChi; rw [nearChi_eq_zero hstar hd]; ring

/-- **The sharp indicator is below the smooth weight**, so `RBM.Step45.Eq548` implies
`RBM.Step45.Eq548W` at this weight (`RBM.Step45.eq548W_of_eq548`). -/
theorem indicator_le_nearChi {W ℓu d : ℝ} (hstar : 0 ≤ ellStar W ℓu) :
    (if d ≤ 6 * ellStar W ℓu then (1 : ℝ) else 0) ≤ nearChi W ℓu d := by
  split_ifs with h
  · exact le_of_eq (nearChi_eq_one hstar h).symm
  · exact nearChi_nonneg _ _ _

/-- **`χ` is `15/8`-Lipschitz**, from the sharp derivative bound `RBM.Cutoff.abs_cutChiD_le`
through the mean value inequality.  This is the quantitative replacement for the jump of
`RBM.Step2FarMart.lkFar_crossing`. -/
theorem abs_cutChi_sub_le (x y : ℝ) : |cutChi x - cutChi y| ≤ 15 / 8 * |x - y| := by
  have h := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := cutChi) (f' := cutChiD) (C := 15 / 8)
    (fun z _ => (hasDerivAt_cutChi z).hasDerivWithinAt)
    (fun z _ => by simpa [Real.norm_eq_abs] using abs_cutChiD_le z)
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- **The smooth weight is Lipschitz in the threshold.**  At a fixed distance `d ≥ 0`, moving
the scale from `ℓ*_w` to `ℓ*_v` moves the weight by at most `(15/8)·d·|1/6ℓ*_v - 1/6ℓ*_w|`.
For the sharp indicator the same quantity is `1` however close `v` and `w` are
(`RBM.Step2FarMart.lkFar_crossing`); *this* is what the smoothing buys. -/
theorem abs_nearChi_sub_le (W ℓ₁ ℓ₂ d : ℝ) :
    |nearChi W ℓ₁ d - nearChi W ℓ₂ d|
      ≤ 15 / 8 * |d / (6 * ellStar W ℓ₁) - d / (6 * ellStar W ℓ₂)| :=
  abs_cutChi_sub_le _ _

theorem abs_farChi_sub_le (W ℓ₁ ℓ₂ d : ℝ) :
    |farChi W ℓ₁ d - farChi W ℓ₂ d|
      ≤ 15 / 8 * |d / (6 * ellStar W ℓ₁) - d / (6 * ellStar W ℓ₂)| := by
  have h := abs_nearChi_sub_le W ℓ₁ ℓ₂ d
  have : farChi W ℓ₁ d - farChi W ℓ₂ d = -(nearChi W ℓ₁ d - nearChi W ℓ₂ d) := by
    unfold farChi; ring
  rw [this, abs_neg]; exact h

end SmoothThreshold

/-! ### 8. The smoothed far functional

`RBM.Step2FarMart.lkFar` multiplies the loop error by the sharp indicator of `‖a₁-a₂‖ > 6ℓ*_u`;
`lkFarSm` multiplies it by `RBM.Step2FarMart.farChi` instead.  Everything §1 proves about
`jSfar` survives with the same proofs, and the crossing of §3 does not. -/

section SmoothFar

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The loop error with the smooth far-field weight**,
`(1 - χ(‖a₁-a₂‖/6ℓ*_u))·|(L-K)_{u,(+,-),a}|`. -/
noncomputable def lkFarSm (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℝ :=
  fun a => farChi (B.W N : ℝ) (B.ell N u) (zdist (B.L N) (a 0 - a 1)) *
    ‖Step2.lk X E N u ω a‖

/-- **(5.29) with the smooth far weight**: `J*_{u,D}` of `lkFarSm`. -/
noncomputable def jSfarSm (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  Step2.jStar (B.L N) (lkFarSm X E N u ω) (B.W N) (B.ell N u) (etaT E u) D

variable (X : Sample B) {E D : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}

theorem lkFarSm_nonneg (a : LoopArg (B.L N) 2) : 0 ≤ lkFarSm X E N u ω a :=
  mul_nonneg (farChi_nonneg _ _ _) (norm_nonneg _)

theorem lkFarSm_le (a : LoopArg (B.L N) 2) :
    lkFarSm X E N u ω a ≤ ‖Step2.lk X E N u ω a‖ := by
  have h := farChi_le_one (B.W N : ℝ) (B.ell N u) (zdist (B.L N) (a 0 - a 1))
  have h0 : (0 : ℝ) ≤ ‖Step2.lk X E N u ω a‖ := norm_nonneg _
  unfold lkFarSm
  nlinarith

/-- **The splitting identity** the producer of (5.48) runs on: the two weights add to `1`. -/
theorem norm_lk_eq_near_add_far (a : LoopArg (B.L N) 2) :
    ‖Step2.lk X E N u ω a‖
      = nearChi (B.W N : ℝ) (B.ell N u) (zdist (B.L N) (a 0 - a 1)) *
          ‖Step2.lk X E N u ω a‖ + lkFarSm X E N u ω a := by
  unfold lkFarSm
  rw [← add_mul, nearChi_add_farChi, one_mul]

/-- **The smooth far functional is `≥ 1` identically**, so `jSfarSm ≺ 1` is the *critical*
request — it cannot be met by a degenerate `jSfarSm ≡ 0`, exactly as for `jSfar`
(`RBM.Step2FarMart.one_le_jSfar`).  Smoothing does not make the far half cheap. -/
theorem one_le_jSfarSm : 1 ≤ jSfarSm X E D N u ω := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  exact Step2.one_le_jStar hW0 fun a => lkFarSm_nonneg X a

theorem jSfarSm_nonneg : 0 ≤ jSfarSm X E D N u ω := le_trans zero_le_one (one_le_jSfarSm X)

/-- `lkFarSm ≤ J*^{sm}_{u,D}·T_{u,D}` pointwise — the definitional content of (5.31). -/
theorem lkFarSm_le_jSfarSm_mul (a : LoopArg (B.L N) 2) :
    lkFarSm X E N u ω a
      ≤ jSfarSm X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  exact Step2.le_jStar_mul (f := lkFarSm X E N u ω) (ℓu := B.ell N u) (ηu := etaT E u)
    (D := D) hW0 a

/-- **Beyond `12ℓ*_u` the smooth weight is `1`**, so `jSfarSm` controls `(L-K)` there exactly as
`jSfar` does beyond `6ℓ*_u`.  This is the check that the smoothing has not emptied the far
request: outside the transition window the two functionals ask for the same thing. -/
theorem norm_lk_le_jSfarSm_mul {a : LoopArg (B.L N) 2}
    (hstar : 0 < ellStar (B.W N : ℝ) (B.ell N u))
    (ha : 12 * ellStar (B.W N : ℝ) (B.ell N u) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ)) :
    ‖Step2.lk X E N u ω a‖
      ≤ jSfarSm X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) := by
  have h := lkFarSm_le_jSfarSm_mul (E := E) (D := D) (u := u) (ω := ω) X a
  rwa [lkFarSm, farChi_eq_one hstar ha, one_mul] at h

end SmoothFar

/-! ### 9. The producer: (5.48) with the smoothed threshold, **no `M_m` and no martingale**

The splitting identity `RBM.Step2FarMart.norm_lk_eq_near_add_far` turns the near half (the
sharp (5.47), which T207 delivers) and `jSfarSm ≺ 1` into `RBM.Step45.Eq548W` directly:

`|(L-K)_v| = χ·|(L-K)_v| + (1-χ)·|(L-K)_v| ≤ χ·(η_s/η_v)²T + J*^{sm}·T`,

and `J*^{sm} ≺ 1` absorbs into the `N^τ` of `≺`.  No triangle inequality through the Duhamel
defect, no `M_m`, no drift bundle: the hypothesis list is `hnear` and `jSfarSm ≺ 1`. -/

section Produce548

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The near half plus `jSfarSm ≺ 1` give the smoothed (5.48)**, at one `D`. -/
theorem stochDom_eq548W_of_near_of_jSfarSm {D : ℝ}
    (hnear : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (hj : StochDom B.P (fun N (u : TimeIcc s t N) ω => jSfarSm X E D N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2)) *
        ((etaT E (s N) / etaT E p.1) ^ 2 *
          nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2)) + 1)) := by
  refine StochDom.of_subset_union hnear hj fun τ hτ =>
    ⟨τ, hτ, Filter.Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨hA, hB⟩ := hno
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  set a : LoopArg (B.L N) 2 := ![p.2.1, p.2.2] with hadef
  have ha0 : a 0 = p.2.1 := rfl
  have ha1 : a 1 = p.2.2 := rfl
  set T := tailT (B.W N : ℝ) (B.ell N (p.1 : ℝ)) (etaT E (p.1 : ℝ)) D
    (zdist (B.L N) (p.2.1 - p.2.2)) with hTdef
  have hT0 : 0 < T := tailT_pos hW0 _
  set pref := (etaT E (s N) / etaT E (p.1 : ℝ)) ^ 2 with hprefdef
  set χ := nearChi (B.W N : ℝ) (B.ell N (p.1 : ℝ))
    ((zdist (B.L N) (p.2.1 - p.2.2) : ℕ) : ℝ) with hχdef
  have hχ0 : 0 ≤ χ := nearChi_nonneg _ _ _
  have heq : X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) = ‖Step2.lk X E N (p.1 : ℝ) ω a‖ := by
    rw [Step2.norm_lk_eq, ha0, ha1]
  -- the far half, pointwise
  have hfarb : lkFarSm X E N (p.1 : ℝ) ω a ≤ (N : ℝ) ^ τ * T := by
    refine (lkFarSm_le_jSfarSm_mul (E := E) (D := D) (u := (p.1 : ℝ)) (ω := ω) X a).trans ?_
    have hj' := hB p.1
    rw [mul_one] at hj'
    have hTT : Step2.tT B E N D (p.1 : ℝ) (zdist (B.L N) (a 0 - a 1)) = T := by
      rw [ha0, ha1]; rfl
    rw [hTT]
    exact mul_le_mul_of_nonneg_right hj' hT0.le
  -- the near half
  have hnearb : X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) ≤ (N : ℝ) ^ τ * (pref * T) := hA p
  -- put them together
  have hsplit := norm_lk_eq_near_add_far (E := E) (u := (p.1 : ℝ)) (ω := ω) X a
  rw [ha0, ha1, ← heq, ← hχdef] at hsplit
  nlinarith [hp, hsplit, hfarb, hnearb, hχ0, hT0, hτ0]

/-- **(5.48) with the smoothed threshold** — `RBM.Step45.FlowEq548W` at the weight
`χ(‖a₁-a₂‖/6ℓ*_u)`.  Hypothesis list: the sharp near half (5.47) and `jSfarSm ≺ 1`.
**No `M_m`, no martingale bound, no `FarInputs'`, no drift bundle.** -/
theorem flowEq548W_of_jSfarSm
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (hj : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => jSfarSm X E D N (u : ℝ) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548W X E s t
      (fun N p => nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2))) :=
  fun D hD => stochDom_eq548W_of_near_of_jSfarSm X (hnear D hD) (hj D hD)

/-- **No regression: every existing producer of the sharp (5.48) also produces the smoothed
one, at the concrete weight.**  `RBM.Step45.flowEq548W_of_flowEq548` at
`w = RBM.Step2FarMart.nearChi`, whose side condition is `indicator_le_nearChi`.  So
`RBM.Step2MomentStep.flowEq548_of_near_far`, `RBM.Step2Near47.flowEq548_of_sharp_farInputs`
and `RBM.Step2FarInputs.flowEq548_of_egData` all feed the primed Step 5 unchanged — the
threshold move `6 → 12` costs nothing on the producer side either. -/
theorem flowEq548W_of_flowEq548_nearChi (ht1 : ∀ N, t N < 1) (h : Step45.FlowEq548 X E s t) :
    Step45.FlowEq548W X E s t
      (fun N p => nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2))) :=
  Step45.flowEq548W_of_flowEq548 X
    (fun N p => indicator_le_nearChi (ellStar_nonneg_of_one_le (B.one_le_W N)
      (Step3.ellHat_pos_of_lt_one (B.one_le_L N)
        (lt_of_le_of_lt p.1.2.2 (ht1 N))).le)) h

/-- **`hwfar` for the concrete weight**: past `12ℓ*_u` the smooth near weight vanishes.  This is
what `RBM.Step45.decay_of_split_W` consumes; it needs `W ≥ 2` (so that `ℓ*_u > 0`), which holds
eventually because `W → ∞`. -/
theorem eventually_nearChi_eq_zero (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N)),
      12 * ellStar (B.W N : ℝ) (B.ell N p.1) < (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) →
        nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2)) = 0 := by
  filter_upwards [B.eventually_le_W 2] with N hW2 p hd
  exact nearChi_eq_zero (ellStar_pos_of_two_le hW2
    (Step3.ellHat_pos_of_lt_one (B.one_le_L N) (lt_of_le_of_lt p.1.2.2 (ht1 N)))) hd.le

/-- **(2.79) for the flow, from the smoothed (5.48)**: `RBM.Step45.flow_sharpDecay` with the
threshold at `12ℓ*_u`.  The conclusion is the *unprimed* one verbatim — the shape of the field
`RBM.Steps.sharpDecay` — so Step 5's consumers are served with `M_m` nowhere in sight. -/
theorem flow_sharpDecay_of_jSfarSm (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h4 : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2))
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (hj : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => jSfarSm X E D N (u : ℝ) ω) (fun _ _ _ => (1 : ℝ))) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2) :=
  Step45.flow_sharpDecay_W X hE hs0 ht1 (eventually_nearChi_eq_zero (s := s) ht1) h4
    (flowEq548W_of_jSfarSm X hnear hj)

end Produce548

/-! ### 10. Why the bootstrap is **available** for `jSfarSm`

§3 ruled out a `RBM.MomentDuhamelCut.CutHyp` for `jSfar` because that functional jumps in `u`:
`CutHyp.modulus` is a two-sided modulus valid for every `ω`, and
`RBM.MomentDuhamelCut.stochDom_of_net` needs `ContinuousOn`.  Both objections disappear for
`jSfarSm`, and this section compiles the reason:

* `continuousOn_jSfarSm` — the smoothed functional inherits the time-continuity of the loop
  error itself (for `jSfar` the same implication is **false**: `lkFar_crossing` produces a jump
  even when the loop error is constant in `u`);
* `abs_jSfarSm_sub_le` + `abs_lkFarSm_ratio_sub_le` — the modulus transfer: a modulus for
  `|(L-K)_u|/T_{u,D}` gives one for `jSfarSm`, with the extra term controlled by the `15/8`
  Lipschitz constant of `RBM.Cutoff.cutChi`;
* `sharp_vs_smooth_at_crossing` — the contrast in one statement: at a crossing the sharp
  indicator moves by `1`, the smooth weight by `(15/8)|d/6ℓ*_v - d/6ℓ*_w|`. -/

section SmoothCut

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E D : ℝ}

/-- `u ↦ 1 - χ(d/6ℓ*_u)` is continuous on a window `[a,b]` with `b < 1`, once `W ≥ 2` makes
`ℓ*_u` positive. -/
theorem continuousOn_farChi {N : ℕ} (hW2 : (2 : ℝ) ≤ (B.W N : ℝ)) {a b : ℝ} (hb : b < 1)
    (d : ℝ) : ContinuousOn (fun u => farChi (B.W N : ℝ) (B.ell N u) d) (Set.Icc a b) := by
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hℓ := Step2.continuousOn_ell B N (a := a) hb
  have hℓpos : ∀ u ∈ Set.Icc a b, 0 < B.ell N u := fun u hu =>
    Step3.ellHat_pos_of_lt_one hL1 (hu.2.trans_lt hb)
  refine ContinuousOn.sub continuousOn_const ?_
  refine Cutoff.differentiable_cutChi.continuous.comp_continuousOn ?_
  refine ContinuousOn.div continuousOn_const ?_ fun u hu => ?_
  · simp only [ellStar]
    exact continuousOn_const.mul (continuousOn_const.mul hℓ)
  · have := ellStar_pos_of_two_le hW2 (hℓpos u hu)
    positivity

/-- **The smoothed far functional is continuous in the time.**  Compare `lkFar_crossing`: the
sharp far functional jumps even for a loop error that does not move at all. -/
theorem continuousOn_jSfarSm {N : ℕ} {ω : Ω} (hE : |E| < 2) (hW2 : (2 : ℝ) ≤ (B.W N : ℝ))
    {a b : ℝ} (hb : b < 1)
    (hc : ∀ x : LoopArg (B.L N) 2, ContinuousOn (fun u => Step2.lk X E N u ω x) (Set.Icc a b)) :
    ContinuousOn (fun u => jSfarSm X E D N u ω) (Set.Icc a b) := by
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hW : (0 : ℝ) < (B.W N : ℝ) := by linarith
  refine ContinuousOn.add ?_ continuousOn_const
  refine ContinuousOn.finset_sup'_apply _ fun x _ => ?_
  have hℓ := Step2.continuousOn_ell B N (a := a) hb
  have hℓpos : ∀ u ∈ Set.Icc a b, 0 < B.ell N u := fun u hu =>
    Step3.ellHat_pos_of_lt_one hL1 (hu.2.trans_lt hb)
  have hT : ContinuousOn
      (fun u => tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x 0 - x 1)))
      (Set.Icc a b) := by
    unfold tailT
    refine ContinuousOn.add (ContinuousOn.mul ?_ ?_) continuousOn_const
    · refine ContinuousOn.inv₀ ?_ fun u hu => ?_
      · refine ContinuousOn.pow (ContinuousOn.mul (ContinuousOn.mul continuousOn_const hℓ) ?_) 2
        unfold etaT; fun_prop
      · have := hℓpos u hu
        have := Step2.etaT_pos' hE (hu.2.trans_lt hb)
        positivity
    · refine ContinuousOn.rexp (ContinuousOn.neg (ContinuousOn.sqrt ?_))
      exact ContinuousOn.div continuousOn_const hℓ fun u hu => (hℓpos u hu).ne'
  refine ContinuousOn.div ?_ hT fun u _ => (tailT_pos hW _).ne'
  simp only [lkFarSm]
  exact ContinuousOn.mul (continuousOn_farChi (B := B) hW2 hb _) (ContinuousOn.norm (hc x))

/-- **Modulus transfer.**  `J*` is a max over a finite index set plus `1`, so a uniform bound on
the pointwise differences is a bound on the difference of the maxima.  This is the reduction
that makes `RBM.MomentDuhamelCut.CutHyp.modulus` a statement about the *entries* of `L - K`
again. -/
theorem abs_jSfarSm_sub_le {N : ℕ} {ω : Ω} {v w M : ℝ}
    (h : ∀ x : LoopArg (B.L N) 2,
      |lkFarSm X E N v ω x / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
            (zdist (B.L N) (x 0 - x 1))
        - lkFarSm X E N w ω x / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
            (zdist (B.L N) (x 0 - x 1))| ≤ M) :
    |jSfarSm X E D N v ω - jSfarSm X E D N w ω| ≤ M := by
  set F : LoopArg (B.L N) 2 → ℝ := fun x =>
    lkFarSm X E N v ω x / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
      (zdist (B.L N) (x 0 - x 1)) with hF
  set G : LoopArg (B.L N) 2 → ℝ := fun x =>
    lkFarSm X E N w ω x / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
      (zdist (B.L N) (x 0 - x 1)) with hG
  have key : ∀ (F G : LoopArg (B.L N) 2 → ℝ), (∀ x, F x ≤ G x + M) →
      Finset.univ.sup' Finset.univ_nonempty F
        ≤ Finset.univ.sup' Finset.univ_nonempty G + M := by
    intro F G hFG
    refine Finset.sup'_le _ _ fun x _ => (hFG x).trans ?_
    have := Finset.le_sup' G (Finset.mem_univ x)
    linarith
  have h1 : Finset.univ.sup' Finset.univ_nonempty F
      ≤ Finset.univ.sup' Finset.univ_nonempty G + M :=
    key F G fun x => by have := abs_le.1 (h x); linarith [this.2]
  have h2 : Finset.univ.sup' Finset.univ_nonempty G
      ≤ Finset.univ.sup' Finset.univ_nonempty F + M :=
    key G F fun x => by have := abs_le.1 (h x); linarith [this.1]
  simp only [jSfarSm, Step2.jStar, ← hF, ← hG]
  rw [abs_le]
  constructor <;> linarith

/-- **The pointwise modulus splits** into a weight term — bounded by the `15/8` Lipschitz
constant of `RBM.Cutoff.cutChi` — and the modulus of the *unweighted* ratio `|(L-K)_u|/T_{u,D}`.
The first term is the one that does not exist for the sharp indicator. -/
theorem abs_lkFarSm_ratio_sub_le {N : ℕ} {ω : Ω} {v w : ℝ} (x : LoopArg (B.L N) 2) :
    |lkFarSm X E N v ω x / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
          (zdist (B.L N) (x 0 - x 1))
      - lkFarSm X E N w ω x / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
          (zdist (B.L N) (x 0 - x 1))|
      ≤ 15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
            - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
          * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))|
        + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
              (zdist (B.L N) (x 0 - x 1))
            - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
              (zdist (B.L N) (x 0 - x 1))| := by
  set d : ℝ := ((zdist (B.L N) (x 0 - x 1) : ℕ) : ℝ) with hd
  set cv := farChi (B.W N : ℝ) (B.ell N v) d with hcv
  set cw := farChi (B.W N : ℝ) (B.ell N w) d with hcw
  set Y := ‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D d with hY
  set Z := ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D d with hZ
  have hrw : lkFarSm X E N v ω x / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D d
      - lkFarSm X E N w ω x / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D d
      = (cv - cw) * Y + cw * (Y - Z) := by
    simp only [lkFarSm, hY, hZ, hcv, hcw, hd]
    ring
  rw [hrw]
  refine (abs_add_le _ _).trans ?_
  have hcw0 : 0 ≤ cw := farChi_nonneg _ _ _
  have hcw1 : cw ≤ 1 := farChi_le_one _ _ _
  have h1 : |(cv - cw) * Y| ≤ 15 / 8 * |d / (6 * ellStar (B.W N : ℝ) (B.ell N v))
      - d / (6 * ellStar (B.W N : ℝ) (B.ell N w))| * |Y| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_farChi_sub_le _ _ _ _) (abs_nonneg _)
  have h2 : |cw * (Y - Z)| ≤ |Y - Z| := by
    rw [abs_mul, abs_of_nonneg hcw0]
    nlinarith [abs_nonneg (Y - Z)]
  linarith

/-- **The contrast, in one statement.**  At a time `v` where `6ℓ*_v` has just passed a distance
`d` that was still far at `w`, the sharp indicator of `RBM.Step45.Eq548` has moved by exactly
`1` — no matter how close `v` and `w` are — while the smooth weight has moved by at most
`(15/8)|d/6ℓ*_v - d/6ℓ*_w|`, which goes to `0` with `|v-w|`.  This is the whole content of
D15 → option 3. -/
theorem sharp_vs_smooth_at_crossing {W ℓv ℓw d : ℝ}
    (hv : d ≤ 6 * ellStar W ℓv) (hw : ¬ (d ≤ 6 * ellStar W ℓw)) :
    |(if d ≤ 6 * ellStar W ℓv then (1 : ℝ) else 0)
        - (if d ≤ 6 * ellStar W ℓw then (1 : ℝ) else 0)| = 1
      ∧ |nearChi W ℓv d - nearChi W ℓw d|
          ≤ 15 / 8 * |d / (6 * ellStar W ℓv) - d / (6 * ellStar W ℓw)| := by
  refine ⟨?_, abs_nearChi_sub_le W ℓv ℓw d⟩
  have e1 : (if d ≤ 6 * ellStar W ℓv then (1 : ℝ) else 0) = 1 := by simp [hv]
  have e2 : (if d ≤ 6 * ellStar W ℓw then (1 : ℝ) else 0) = 0 := by simp [hw]
  rw [e1, e2]
  norm_num

end SmoothCut

/-! ### 11. The bootstrap hook-up: `CutHyp` for `jSfarSm` at `Θ ≡ 1`

With continuity and the modulus available, `RBM.MomentDuhamelCut.stochDom_of_cutHyp` applies to
`jSfarSm` at the threshold `Θ ≡ 1` and delivers `jSfarSm ≺ 1`, i.e. the far half of (5.48).
Chaining it with §9 gives (5.48) — and Step 5 — with **no `M_m`, no martingale bound, no
`FarInputs'` and no drift bundle** anywhere in the hypothesis list. -/

section Hookup

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **`jSfarSm ≺ 1` from the bootstrap interface.**  `Θ ≡ 1` is the critical threshold:
`one_le_jSfarSm` says the functional is `≥ 1` identically, so this is not a request that a
degenerate functional could meet. -/
theorem stochDom_jSfarSm_of_cutHyp {D : ℝ}
    (H : MomentDuhamelCut.CutHyp B.P (fun N u ω => jSfarSm X E D N u ω) s t (fun _ => 1))
    (hinit : StochDom B.P (fun N (_ : Unit) ω => jSfarSm X E D N (s N) ω)
      (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P (fun N (u : TimeIcc s t N) ω => jSfarSm X E D N (u : ℝ) ω)
      (fun _ _ _ => (1 : ℝ)) :=
  letI := B.isProbabilityMeasure
  MomentDuhamelCut.stochDom_of_cutHyp H (Filter.Eventually.of_forall fun _ => le_rfl) hinit

/-- **(5.48) with the smoothed threshold, from the bootstrap interface.**  The complete
hypothesis list: the sharp near half (5.47), a `CutHyp` for `jSfarSm` at `Θ ≡ 1`, and the
initial bound at `u = s_N` ((2.68)/(2.69)).  **`M_m` does not occur, and neither does any
martingale.** -/
theorem flowEq548W_of_cutHyp
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (H : ∀ D : ℝ, 0 < D →
      MomentDuhamelCut.CutHyp B.P (fun N u ω => jSfarSm X E D N u ω) s t (fun _ => 1))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548W X E s t
      (fun N p => nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2))) :=
  flowEq548W_of_jSfarSm X hnear fun D hD =>
    stochDom_jSfarSm_of_cutHyp X (H D hD) (hinit D hD)

/-- **(2.79) for the flow with `M_m` deleted.**  Step 4's uniform bound, the sharp near half
(5.47), a `CutHyp` for `jSfarSm` at `Θ ≡ 1` and the initial bound produce the field
`RBM.Steps.sharpDecay` verbatim.  This is the landing point of D15 → option 3. -/
theorem flow_sharpDecay_of_cutHyp (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h4 : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2))
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (H : ∀ D : ℝ, 0 < D →
      MomentDuhamelCut.CutHyp B.P (fun N u ω => jSfarSm X E D N u ω) s t (fun _ => 1))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2) :=
  Step45.flow_sharpDecay_W X hE hs0 ht1 (eventually_nearChi_eq_zero (s := s) ht1) h4
    (flowEq548W_of_cutHyp X hnear H hinit)

end Hookup

/-! ### 12. Satisfiability of the smoothed route

The project's two failure modes are *fiat* (a hypothesis so weak it is free) and *vacuity* (a
hypothesis so strong nothing satisfies it).  Both are checked here for the smoothed far half.

**Not fiat.**  `one_le_jSfarSm` — the functional is `≥ 1` identically, so `jSfarSm ≺ 1` is the
critical request, not one that `0` would meet; `exists_farChi_eq_one` — as soon as the ring is
longer than `24ℓ*_u` there are arguments at which the smooth weight is exactly `1`, so the
request really does bind on `(L-K)` there, `jSfarSm_ge_of_farChi_eq_one` making that explicit.
Smoothing loses nothing outside the transition window `[6ℓ*_u, 12ℓ*_u]`.

**Not vacuous.**  The net conditions `RBM.MomentDuhamelCut.CutHyp.mesh_fine` and `card_le` pull
against each other; at our threshold `Θ ≡ 1` they are jointly satisfiable with `mesh_fine` at
*equality* (`sat_mesh_card_at_one`, T197's witness at exactly our parameters).  `modulus` and
`ContinuousOn` — the two fields that are **false** for the sharp `jSfar` (§3) — are supplied by
§10 for `jSfarSm`.

**Critical scale.**  On the grid of Lemmas 2.18–2.20 the near prefactor is
`(η_s/η_t)² = (N+1)²` (`pref_grid_critical`), i.e. genuinely large: the smoothed (5.48) is not
the trivial `≺ T_{u,D}`.  This is the same grid point at which T208 showed `cFarStep` fails and
T215 placed its witness.

**Profile pin.**  `nearChi_nine_ellStar` fixes the weight at the middle of the transition band
to exactly `1/2`; a mis-copied threshold would fail to compile here rather than silently change
the statement. -/

section Satisfiable

variable {Ω : Type*} [MeasurableSpace Ω]

/-- At the middle of the transition band `d = 9ℓ*_u` the weight is exactly `χ(3/2) = 1/2`.
Numerical pin for the threshold pair `(6, 12)`. -/
theorem nearChi_nine_ellStar {W ℓu : ℝ} (hstar : 0 < ellStar W ℓu) :
    nearChi W ℓu (9 * ellStar W ℓu) = 1 / 2 := by
  have h : 9 * ellStar W ℓu / (6 * ellStar W ℓu) = 3 / 2 := by
    field_simp
    ring
  rw [nearChi, h, Cutoff.cutChi_three_halves]

/-- The weight decreases with the distance: further arguments are *more* far-field.  (A sign
slip in the definition would be caught here.) -/
theorem nearChi_antitone {W ℓu : ℝ} (hstar : 0 < ellStar W ℓu) {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) :
    nearChi W ℓu d₂ ≤ nearChi W ℓu d₁ := by
  refine Cutoff.cutChi_antitone ?_
  exact div_le_div_of_nonneg_right h (by linarith)

/-- On the diagonal the weight is `1`: the near field is where the prefactor `(η_s/η_u)²` is
allowed, exactly as in the unprimed (5.48). -/
theorem nearChi_zero {W ℓu : ℝ} (hstar : 0 ≤ ellStar W ℓu) : nearChi W ℓu 0 = 1 :=
  nearChi_eq_one hstar (by linarith)

/-- **The far family is non-empty** once the ring is longer than `24ℓ*_u`: there is a pair of
indices at distance `⌊L/2⌋`. -/
theorem exists_zdist_half (L : ℕ) [NeZero L] (hL : 3 ≤ L) :
    ∃ a : LoopArg L 2, (zdist L (a 0 - a 1) : ℝ) = ((L / 2 : ℕ) : ℝ) := by
  refine ⟨![((L / 2 : ℕ) : ZMod L), 0], ?_⟩
  have hlt : L / 2 < L := Nat.div_lt_self (by omega) (by norm_num)
  have hval : (((L / 2 : ℕ) : ZMod L)).val = L / 2 := ZMod.val_cast_of_lt hlt
  have h0 : (![((L / 2 : ℕ) : ZMod L), (0 : ZMod L)] 0 - ![((L / 2 : ℕ) : ZMod L),
      (0 : ZMod L)] 1) = ((L / 2 : ℕ) : ZMod L) := by simp
  rw [h0, zdist, hval]
  have : L / 2 ≤ L - L / 2 := by omega
  rw [min_eq_left this]

/-- **The far request really binds.**  If the ring is long enough that some distance exceeds
`12ℓ*_u`, the smooth weight is `1` there, so `jSfarSm ≺ 1` is a bound on `(L-K)` itself and not
an artefact of the transition window. -/
theorem exists_farChi_eq_one {B : Band Ω} {N : ℕ} {u : ℝ}
    (hL : 12 * ellStar (B.W N : ℝ) (B.ell N u) ≤ ((B.L N / 2 : ℕ) : ℝ))
    (hstar : 0 < ellStar (B.W N : ℝ) (B.ell N u)) :
    ∃ a : LoopArg (B.L N) 2,
      farChi (B.W N : ℝ) (B.ell N u) (zdist (B.L N) (a 0 - a 1)) = 1 := by
  have : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  obtain ⟨a, ha⟩ := exists_zdist_half (B.L N) (B.three_le_L N)
  exact ⟨a, farChi_eq_one hstar (by rw [ha]; exact hL)⟩

/-- At such an argument `J*^{sm}_{u,D}` dominates the *unweighted* ratio, so `jSfarSm ≺ 1` is
exactly the far half of (5.48) there. -/
theorem jSfarSm_ge_of_farChi_eq_one {B : Band Ω} (X : Sample B) {E D : ℝ} {N : ℕ} {u : ℝ}
    {ω : Ω} {a : LoopArg (B.L N) 2}
    (ha : farChi (B.W N : ℝ) (B.ell N u) (zdist (B.L N) (a 0 - a 1)) = 1) :
    ‖Step2.lk X E N u ω a‖ / Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) + 1
      ≤ jSfarSm X E D N u ω := by
  have h := Step2.div_le_jStar_sub_one (f := lkFarSm X E N u ω) (W := (B.W N : ℝ))
    (ℓu := B.ell N u) (ηu := etaT E u) (D := D) a
  rw [lkFarSm, ha, one_mul] at h
  have : jSfarSm X E D N u ω
      = Step2.jStar (B.L N) (lkFarSm X E N u ω) (B.W N) (B.ell N u) (etaT E u) D := rfl
  rw [this, Step2.tT]
  linarith

/-- **The two net conditions at our threshold `Θ ≡ 1`**, jointly satisfiable with `mesh_fine`
at *equality*: `Kmod = 1`, `γ = 1/2` (the flow's Hölder exponent), mesh `m_N = N²`,
`t - s = 1`, `Ccard = 3`.  These are exactly the parameters of
`RBM.MomentDuhamelCut.satCutHyp`, and `Θ ≡ 1` is the threshold
`stochDom_jSfarSm_of_cutHyp` uses. -/
theorem sat_mesh_card_at_one {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ (1 : ℝ) * (1 / (N : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 1 ∧
      ((1 : ℝ) - 0) * (N : ℝ) ^ (2 : ℝ) + 2 ≤ (N : ℝ) ^ (3 : ℝ) :=
  MomentDuhamelCut.sat_mesh_card hN

/-- **The near prefactor at the critical scale.**  On the grid `1 - s = 1/(N+1)`,
`1 - t = (1-s)²` — T208's failure point and T215's witness point — the prefactor of the
smoothed (5.48) is `(N+1)²`, so the near half is not the trivial `≺ T_{u,D}`. -/
theorem pref_grid_critical {E : ℝ} (hE : |E| < 2) (N : ℕ) :
    (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2 = ((N : ℝ) + 1) ^ 2 := by
  rw [etaRatio_grid hE]

/-- **The non-degeneracy package for the smoothed route**, at the critical grid point: the far
functional sits at its critical value `≥ 1`, the near prefactor is the genuinely large
`(N+1)²`, and the two net conditions of the bootstrap hold simultaneously with `mesh_fine` at
equality. -/
theorem smooth_route_nondegenerate {B : Band Ω} (X : Sample B) {E : ℝ} (hE : |E| < 2)
    {D : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} (hN : 2 ≤ N) :
    1 ≤ jSfarSm X E D N u ω ∧
      (etaT E (sGrid N) / etaT E (tGrid N)) ^ 2 = ((N : ℝ) + 1) ^ 2 ∧
      ((N : ℝ) ^ (1 : ℝ) * (1 / (N : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) = 1 ∧
        ((1 : ℝ) - 0) * (N : ℝ) ^ (2 : ℝ) + 2 ≤ (N : ℝ) ^ (3 : ℝ)) :=
  ⟨one_le_jSfarSm X, pref_grid_critical hE N, sat_mesh_card_at_one hN⟩

end Satisfiable

/-! ### 13. The `CutHyp` bundle, assembled from the entries (T228)

§10 reduced the two-sided modulus of `jSfarSm` to the entries of `L - K`, and §11 still took
the whole `RBM.MomentDuhamelCut.CutHyp` as a hypothesis — so §10 had no consumer.  This section
closes that gap.  At the parameters of `RBM.MomentDuhamelCut.satCutHyp` — `Kmod = 1`,
`γ = 1/2` (the flow's Hölder exponent, `RBM.Gauss.abs_sqrt_sub_sqrt_le`), mesh
`m_N = (N+1)²`, `Ccard = 3`, `Θ ≡ 1` — **every field of the bundle except the entrywise
modulus, the measurability and `moment` is discharged by a theorem**.

That matters for the *vacuity* side of the audit.  `mesh_fine` wants the net fine and `card_le`
wants it coarse, which is the shape in which a pair of hypotheses can be jointly
unsatisfiable; §12's `sat_mesh_card_at_one` only exhibited a solution.  Here the two are
**proved** at one and the same mesh (`mesh_fine_one_at_sq`, `card_le_one_at_sq`), so they
cannot be jointly unsatisfiable at all — the risk is removed rather than witnessed.

`moment` stays a hypothesis.  That is not a gap opened by the smoothing: it is the same field
the near half of the bootstrap has always taken, and T210 located its obstruction exactly (the
truncation constrains only the endpoint, while (5.39)–(5.44) need a priori control at the
intermediate times, so the first pass has to bootstrap the prefix event). -/

section Assemble

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E D : ℝ} {s t : ℕ → ℝ}

/-- **The modulus of `jSfarSm`, from the entries of `L - K`** — the field
`RBM.MomentDuhamelCut.CutHyp.modulus`.  Composition of `abs_jSfarSm_sub_le` (the `sup'`
transfer) with `abs_lkFarSm_ratio_sub_le` (the pointwise split into the `15/8`-Lipschitz weight
term and the modulus of the unweighted ratio `|(L-K)_u|/T_{u,D}`).  The continuity that
`continuousOn_jSfarSm` exhibits directly is then free, by
`RBM.MomentDuhamelCut.CutHyp.continuousOn`.

For the *sharp* functional there is no such reduction: `lkFar_crossing` produces a jump of a
whole `‖lk‖/T` however small `|v - w|` is. -/
theorem modulus_jSfarSm_of_entries {Kmod γ : ℝ}
    (h : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      ∀ x : LoopArg (B.L N) 2,
        15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
              - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
            * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))|
          + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))
              - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
                (zdist (B.L N) (x 0 - x 1))|
            ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ) :
    ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |jSfarSm X E D N v ω - jSfarSm X E D N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ :=
  fun N ω v hv w hw =>
    abs_jSfarSm_sub_le X fun x => (abs_lkFarSm_ratio_sub_le X x).trans (h N ω v hv w hw x)

/-- **`mesh_fine` at `Kmod = 1`, `γ = 1/2`, `Θ ≡ 1` and the mesh `m_N = (N+1)²`**: it reduces to
`N/(N+1) ≤ 1`.  `RBM.MomentDuhamelCut.sat_mesh_card` is the same computation at `m_N = N²`,
where it holds with *equality*; the shift to `(N+1)²` is only so that
`RBM.MomentDuhamelCut.CutHyp.mesh_pos` also holds at `N = 0`, and it is not separately named
there (it sits inside a field of `satCutHyp`). -/
theorem mesh_fine_one_at_sq (N : ℕ) :
    (N : ℝ) ^ (1 : ℝ) * (1 / ((N : ℝ) + 1) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤ 1 := by
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : (1 / ((N : ℝ) + 1) ^ (2 : ℝ)) = ((N : ℝ) + 1) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg ha.le, one_div]
  have h2 : (-(2 : ℝ)) * ((1 : ℝ) / 2) = -1 := by norm_num
  rw [h1, ← Real.rpow_mul ha.le, h2, Real.rpow_neg ha.le, Real.rpow_one, Real.rpow_one,
    ← div_eq_mul_inv, div_le_one ha]
  linarith

/-- **`card_le` at the same mesh**, with `Ccard = 3`: the window has length `< 1` because
`0 ≤ s_N` and `t_N < 1`, so the net has at most `(N+1)² + 2 ≤ N³` points.  Together with
`mesh_fine_one_at_sq` this settles the pair that pulls in opposite directions — at *one* mesh,
by theorems, not by a witness. -/
theorem card_le_one_at_sq (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, (t N - s N) * ((N : ℝ) + 1) ^ (2 : ℝ) + 2 ≤ (N : ℝ) ^ (3 : ℝ) := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : ((N : ℝ) + 1) ^ (2 : ℝ) = ((N : ℝ) + 1) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast ((N : ℝ) + 1) 2]; norm_num
  have h3 : (N : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast (N : ℝ) 3]; norm_num
  have hts : t N - s N ≤ 1 := by linarith [hs0 N, ht1 N]
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ (2 : ℕ) := by positivity
  rw [h2, h3]
  nlinarith [hpos, hts, hNR]

/-- **The `CutHyp` for `jSfarSm`, assembled.**  Hypotheses: the window, the entrywise modulus
at `Kmod = 1` and `γ = 1/2`, measurability, and `moment`.  `window`, `Θ_pos`, `J_nonneg`,
`mesh_pos`, `mesh_fine` and `card_le` are all discharged here, so the bundle cannot be
unsatisfiable through the `mesh_fine`/`card_le` pair.

This is the missing consumer of §10: `flowEq548W_of_cutHyp` took the bundle on faith, and now
`flowEq548W_of_entries` builds it. -/
noncomputable def cutHyp_jSfarSm_of_entries
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hmeas : ∀ (N : ℕ) (u : ℝ), AEStronglyMeasurable (fun ω => jSfarSm X E D N u ω) B.P)
    (hmod : ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      ∀ x : LoopArg (B.L N) 2,
        15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
              - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
            * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))|
          + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))
              - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
                (zdist (B.L N) (x 0 - x 1))|
            ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2))
    (hmoment : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (jSfarSm X E D N ws ω)|
              ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p))) :
    MomentDuhamelCut.CutHyp B.P (fun N u ω => jSfarSm X E D N u ω) s t (fun _ => 1) where
  window := hst
  δ₀ := 1
  δ₀_pos := one_pos
  Θ_pos := fun _ => one_pos
  J_nonneg := fun _ _ _ => jSfarSm_nonneg X
  meas := hmeas
  mesh := fun N => ((N : ℝ) + 1) ^ (2 : ℝ)
  mesh_pos := fun N => Real.rpow_pos_of_pos (by positivity) _
  Kmod := 1
  γ := 1 / 2
  γ_pos := by norm_num
  modulus := modulus_jSfarSm_of_entries X hmod
  mesh_fine := mesh_fine_one_at_sq
  Ccard := 3
  card_le := card_le_one_at_sq hs0 ht1
  moment := hmoment

/-- **(5.48) with the smoothed threshold, from entrywise data.**  `flowEq548W_of_cutHyp` with
its `CutHyp` slot filled by `cutHyp_jSfarSm_of_entries`: the hypothesis list is the sharp near
half (5.47), the entrywise modulus, measurability, `moment`, and the initial bound at `u = s_N`
((2.68)/(2.69)).  **`M_m`, the martingale, `FarInputs'` and the drift bundle are all absent.** -/
theorem flowEq548W_of_entries
    (hst : ∀ N, s N ≤ t N) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2))))
    (hmeas : ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (u : ℝ),
      AEStronglyMeasurable (fun ω => jSfarSm X E D N u ω) B.P)
    (hmod : ∀ D : ℝ, 0 < D → ∀ (N : ℕ) (ω : Ω), ∀ v ∈ Set.Icc (s N) (t N),
      ∀ w ∈ Set.Icc (s N) (t N), ∀ x : LoopArg (B.L N) 2,
        15 / 8 * |(zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N v))
              - (zdist (B.L N) (x 0 - x 1) : ℝ) / (6 * ellStar (B.W N : ℝ) (B.ell N w))|
            * |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))|
          + |‖Step2.lk X E N v ω x‖ / tailT (B.W N : ℝ) (B.ell N v) (etaT E v) D
                (zdist (B.L N) (x 0 - x 1))
              - ‖Step2.lk X E N w ω x‖ / tailT (B.W N : ℝ) (B.ell N w) (etaT E w) D
                (zdist (B.L N) (x 0 - x 1))|
            ≤ (N : ℝ) ^ (1 : ℝ) * |v - w| ^ ((1 : ℝ) / 2))
    (hmoment : ∀ D : ℝ, 0 < D → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ),
      ∀ᶠ N : ℕ in atTop,
      ∀ ws ∈ MomentDuhamelCut.netFinset s t (fun N => ((N : ℝ) + 1) ^ (2 : ℝ)) N,
        ∫ ω, |MomentDuhamelCut.cutTrunc ((N : ℝ) ^ (2 * δ) * 1) (jSfarSm X E D N ws ω)|
              ^ (2 * p) ∂B.P
          ≤ C * ((N : ℝ) ^ (ε * p) * (1 : ℝ) ^ (2 * p)))
    (hinit : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (_ : Unit) ω => jSfarSm X E D N (s N) ω) (fun _ _ _ => (1 : ℝ))) :
    Step45.FlowEq548W X E s t
      (fun N p => nearChi (B.W N : ℝ) (B.ell N p.1) (zdist (B.L N) (p.2.1 - p.2.2))) :=
  flowEq548W_of_cutHyp X hnear
    (fun D hD => cutHyp_jSfarSm_of_entries X hst hs0 ht1 (hmeas D hD) (hmod D hD)
      (hmoment D hD)) hinit

end Assemble

end Step2FarMart
end RBM
