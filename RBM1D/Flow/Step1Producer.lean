/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Thm221Assembly
import RBM1D.Gauss.EntryBoundTime

/-!
# The Step-1 slot of the Theorem 2.21 assembly, discharged — T242

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §2.7, §5.1.

T239's assembly `RBM.thm221NoEL_of_inputs_entries` (`Flow/Thm221Assembly.lean`) lists six
named inputs; its first slot is **(2.73), Step 1**, in the shape

```
∀ E, |E| ≤ 2 - κ → ∀ s t, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) → (∀ N, t N < 1) →
  ∀ c, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t
```

and T239 recorded it as "Step 1 line, no producer".  That reading is one premise off.  A
complete Gaussian producer of `RBM.Step1.Hyp` **does** exist — `RBM.Gauss.step1Hyp_gauss_of_scale''`
(T183, itself the end of the chain T111 → T108 → T116 → T125 → T107 → T183) — under word for
word the hypotheses of `RBM.Step1.step1`, i.e. the four domain conditions, `RBM.Cond272Reg`
**and `RBM.BoundsCore X E s`**.  The slot as T239 spelled it out carries no `RBM.BoundsCore`
premise, which is precisely the structural surplus T239 flagged for `Eq548EntryData.init`.

`RBM.BoundsCore X E s` is not missing, though: it is the *fifth* argument of
`RBM.Thm221NoEL.step` itself, hence in scope at every point where the assembly actually feeds
the Step-1 slot.  So the slot can be filled without any new mathematics and without touching
the assembly file, by restating the assembly one level down, at
`RBM.boundsCore_step_of_inputs_reg_W`, where `hB` and `h1` sit side by side.

## Field inventory of `RBM.Step1.Hyp` (the read-only step 0 of T242)

| field | producer on the Gaussian model |
| --- | --- |
| `scaling` (6.1, input of Lemma 5.1) | `RBM.Gauss.loopScaling_gauss` (T111) |
| `lift` (`N^{-C}` net of (5.46) + Lemma 5.1) | `RBM.Gauss.netLift_gauss` (T125), fed by |
| | `RBM.Gauss.eq58_seq_thr` at threshold `3` |
| `lemma41` (Lemma 4.1 = (4.2)+(4.3), flow) | `RBM.Gauss.lemma41Flow_gauss` (T107 + T183), |
| | from `RBM.Gauss.entryBoundFlow_floor` and |
| | `RBM.Gauss.diagBoundFlow_floor` |
| `cont` (time continuity behind (5.1)) | `RBM.Gauss.cont_gauss` (T116), unconditional |

Nothing is left over: the four are assembled by `RBM.Gauss.step1Hyp_gauss_of_scale''`, whose
extra regime inputs (`N^{-1} ≤ η_{t_N}`, `δ_N ≤ N^{-c/6}`, `0 < κ ≤ 1` for (4.3)'s kernel) are
all consequences of the slot's own `N^c ≤ W ℓ_t η_t`, so they cost no hypothesis.

## Main results

* `RBM.Gauss.step1Hyp_slot` — the Step-1 slot of T239's table, verbatim, with one extra
  premise `RBM.BoundsCore (sample d) E s`.
* `RBM.Gauss.thm221NoEL_of_inputs_entries_gauss` — **the deliverable**:
  `RBM.Thm221NoEL (Gauss.sample d) κ` from the *four* remaining named inputs of Steps 2–5 plus
  `RBM.Eq548EntryData`.  `RBM.Step1.Hyp` does not occur in its hypothesis list.
* `RBM.Gauss.thm221NoEL_of_inputs_cutHyp_gauss` — the same, stopping at a
  `RBM.MomentDuhamelCut.CutHyp` for `RBM.Step2FarMart.jSfarSm`, matching
  `RBM.thm221NoEL_of_inputs_cutHyp`.
* `RBM.Gauss.eventually_gridT_zero_lt_gridT_one` — the grid's first window does not collapse.
* `RBM.Gauss.step1Hyp_gauss_grid_first` — an **unconditional** `RBM.Step1.Hyp` on the paper's
  grid (p. 24) at the first step `(u_0, u_1) = (0, min(1 - W^{-τ'}, t))`, with the
  non-degeneracy certificates `N^c ≤ W ℓ_{u_1} η_{u_1}` and `u_0 < u_1`.
* `RBM.Gauss.step1Hyp_gauss_witness` — the same with every parameter pinned down
  (`Dims.exampleGrow`, `E = 0`, `κ = 1`, `t_N = 1 - N^{-1/2}`): a closed statement with no
  hypothesis left to satisfy.
* `RBM.Gauss.step1Hyp_gauss_grid_pos` — `RBM.Step1.Hyp` at **every** later grid window
  `(u_{k+1}, u_{k+2})`, where the start time is positive (`0 < u_{k+1}` eventually), under the
  four remaining inputs of Steps 2–5.  This is the `s > 0` instance: the `RBM.BoundsCore` it
  needs is produced by the induction of p. 24 (`RBM.BoundsCore_of_Thm221NoEL`) run on
  `thm221NoEL_of_inputs_entries_gauss`, not assumed.

## Satisfiability

`step1Hyp_gauss_grid_first` is a *theorem*, not a hypothesis bundle, so `RBM.Step1.Hyp` is
satisfiable outright on the Gaussian model.  It is not satisfied degenerately:

* the window is not collapsed — `eventually_gridT_zero_lt_gridT_one` gives `u_0 < u_1`
  whenever `0 < t_N` eventually (`u_1 = min(1 - W^{-τ'}, t_N)` and `W → ∞`);
* the scale is not collapsed — the second conjunct is `N^c ≤ W ℓ_{u_1} η_{u_1}` with `c > 0`
  chosen *before* `E` and `t`, so every `≺` inside `RBM.Step1.Hyp` is a genuine polynomial
  decay request, not a bound by a constant;
* `t_N < 1` throughout, so the time quantifier never leaves the window where the Green
  function is regular (the failure mode of T240);
* every random-layer field of `RBM.Step1.Hyp` is a `RBM.StochDom` / `RBM.HighProb`
  statement, i.e. already event-restricted; none of them is a pointwise inequality quantified
  over all `ω`, so the `ω = 0` (`H = 0`) and "large multiple of the identity" checks are not
  applicable — the one field that *is* pointwise for every `ω`, `cont`, is continuity of
  `u ↦ ‖G_u - m‖_max`, which is true at `ω = 0` (the map is then constant in the entries).

## Deviations from the paper

None.  Every statement here is a specialization or a rewiring of statements already in the
tree; no hypothesis was weakened and no conclusion changed.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-! ### 1. The Step-1 slot -/

section Slot

/-- **The Step-1 slot of T239's hypothesis table, with the `RBM.BoundsCore` premise restored.**

Verbatim the first hypothesis of `RBM.thm221NoEL_of_inputs_entries`, except for the extra
premise `RBM.BoundsCore (Gauss.sample d) E s` — which is the fifth argument of
`RBM.Thm221NoEL.step` and therefore free at every place the assembly uses this slot.  The
proof is `RBM.Gauss.step1Hyp_gauss_of_scale''`: the two components of `RBM.Cond272Reg` are
exactly the `RBM.Cond272` and the `N^c ≤ W ℓ_t η_t` it asks for. -/
theorem step1Hyp_slot (d : Dims) {κ : ℝ} (hκ : 0 < κ) :
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      BoundsCore (sample d) E s → Step1.Hyp (sample d) E s t :=
  fun _E hE _s _t hs0 hst ht1 _c hc0 hreg hB =>
    step1Hyp_gauss_of_scale'' d hκ hE hB hs0 hst ht1 hreg.1 hc0 hreg.2

end Slot

/-! ### 2. Theorem 2.21 (first pass) with the Step-1 slot gone -/

section Assembly

/-- **Theorem 2.21 without (2.71), in D13's shape, on the Gaussian model, with the Step-1 slot
discharged.**

Verbatim `RBM.thm221NoEL_of_inputs_entries` at `X = Gauss.sample d`, `B = Gauss.band d`,
**minus its first hypothesis** `RBM.Step1.Hyp`.  The conclusion `RBM.Thm221NoEL (sample d) κ`
is unchanged; what fills the slot is `RBM.Gauss.step1Hyp_gauss_of_scale''`, a *producer* of
`RBM.Step1.Hyp`, applied inside the `step` field where `RBM.BoundsCore (sample d) E s` is one
of the arguments.

So the four remaining named inputs are Steps 2–5's: the truncated moment hypothesis, the
`(+,+)` bootstrap target, Lemma 5.14 and (4.5); plus the entrywise (5.48) data of T228. -/
theorem thm221NoEL_of_inputs_entries_gauss (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω d) => Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      StepGlue.Eq45Flow (sample d) E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq548EntryData (sample d) E s t) :
    Thm221NoEL (sample d) κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_reg_W (sample d) hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (step1Hyp_slot d hκ0 E hE s t hs0 hst ht1 c hc0 hreg hB)
      (Hy E hE s t hs0 hst ht1 c hc0 hreg) (hΘ E hE s t hs0 hst ht1 c hc0 hreg)
      (h514 E hE s t hs0 hst ht1 c hc0 hreg) (h45 E hE s t hs0 hst ht1 c hc0 hreg)
      (flowEq548Sm_of_entryData (sample d) hst hs0 ht1
        (h548e E hE s t hs0 hst ht1 c hc0 hreg))

/-- The same assembly one level down, at a `RBM.MomentDuhamelCut.CutHyp` for
`RBM.Step2FarMart.jSfarSm` — the Gaussian counterpart of
`RBM.thm221NoEL_of_inputs_cutHyp`, again with no `RBM.Step1.Hyp` in the hypothesis list. -/
theorem thm221NoEL_of_inputs_cutHyp_gauss (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω d) => Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      StepGlue.Eq45Flow (sample d) E s t)
    (hnear : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 0 < D → StochDom (band d).P
        (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
          (sample d).lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
        (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
          tailT ((band d).W N : ℝ) ((band d).ell N p.1) (etaT E p.1) D
            (zdist ((band d).L N) (p.2.1 - p.2.2))))
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ D : ℝ, 0 < D →
      MomentDuhamelCut.CutHyp (band d).P
        (fun N u ω => Step2FarMart.jSfarSm (sample d) E D N u ω) s t (fun _ => 1))
    (hinit : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ D : ℝ, 0 < D →
      StochDom (band d).P
        (fun N (_ : Unit) ω => Step2FarMart.jSfarSm (sample d) E D N (s N) ω)
        (fun _ _ _ => (1 : ℝ))) :
    Thm221NoEL (sample d) κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_reg_W (sample d) hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (step1Hyp_slot d hκ0 E hE s t hs0 hst ht1 c hc0 hreg hB)
      (Hy E hE s t hs0 hst ht1 c hc0 hreg) (hΘ E hE s t hs0 hst ht1 c hc0 hreg)
      (h514 E hE s t hs0 hst ht1 c hc0 hreg) (h45 E hE s t hs0 hst ht1 c hc0 hreg)
      (flowEq548Sm_of_cutHyp (sample d) ht1 (hnear E hE s t hs0 hst ht1 c hc0 hreg)
        (hcut E hE s t hs0 hst ht1 c hc0 hreg) (hinit E hE s t hs0 hst ht1 c hc0 hreg))

end Assembly

/-! ### 3. The grid of p. 24 does not collapse at its first step -/

section Grid

variable {Ωb : Type*} [MeasurableSpace Ωb]

/-- **`u_0 < u_1` on the truncated grid `u_k = min(1 - W^{-kτ'}, t)`**, eventually in `N`.
`u_0 = 0` (`RBM.gridT_zero`) and `u_1 = min(1 - W^{-τ'}, t_N)`, so the only two things to
check are `W^{-τ'} < 1` — true as soon as `2 ≤ W`, and `W → ∞` by (2.2)
(`RBM.Step2.tendsto_W`) — and `0 < t_N`. -/
theorem eventually_gridT_zero_lt_gridT_one (B : Band Ωb) {τ' : ℝ} (hτ' : 0 < τ')
    {t : ℕ → ℝ} (ht : ∀ᶠ N : ℕ in atTop, 0 < t N) :
    ∀ᶠ N : ℕ in atTop,
      gridT ((B.W N : ℝ)) τ' (t N) 0 < gridT ((B.W N : ℝ)) τ' (t N) 1 := by
  filter_upwards [ht, (Step2.tendsto_W B).eventually_ge_atTop 2] with N htN hWN
  have hW1 : (1 : ℝ) < (B.W N : ℝ) := by linarith
  have hlt : ((B.W N : ℝ)) ^ (-(((1 : ℕ) : ℝ) * τ')) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hW1 (by push_cast; linarith)
  rw [gridT_zero htN.le, gridT]
  refine lt_min ?_ htN
  rw [gridS]
  linarith

end Grid

/-! ### 4. An unconditional, non-degenerate `RBM.Step1.Hyp` on the paper's grid -/

section Witness

/-- **`RBM.Step1.Hyp` holds, on the Gaussian model, at the first step of the grid of p. 24.**

`RBM.cond272Reg_grid_step_domain` supplies `τ' > 0` and `c > 0` — chosen from `κ, τ` alone and
*before* `E` and `t` — such that the window `(u_0, u_1)` of the truncated grid
`u_k = min(1 - W^{-kτ'}, t)` satisfies all four domain conditions and `RBM.Cond272Reg … c`.
The remaining input of `RBM.Gauss.step1Hyp_gauss_of_scale''` is `RBM.BoundsCore` at `u_0`, and
`u_0 = 0` (`RBM.gridT_zero`), where it is (2.67) — `RBM.BoundsCore_zero`.

The two extra conjuncts are the non-degeneracy certificates: the scale at the right end is at
least `N^c` with `c > 0` (so every `≺` inside `RBM.Step1.Hyp` is a genuine polynomial decay
request), and the window is not the collapsed `u_0 = u_1` as soon as `0 < t_N` eventually. -/
theorem step1Hyp_gauss_grid_first (d : Dims) {κ τ : ℝ} (hκ0 : 0 < κ) (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ,
      (∀ N, 0 ≤ t N) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      Step1.Hyp (sample d) E
          (fun N => gridT (((band d).W N : ℝ)) τ' (t N) 0)
          (fun N => gridT (((band d).W N : ℝ)) τ' (t N) 1) ∧
        (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤
          (band d).scale E N (gridT (((band d).W N : ℝ)) τ' (t N) 1)) ∧
        ((∀ᶠ N : ℕ in atTop, 0 < t N) → ∀ᶠ N : ℕ in atTop,
          gridT (((band d).W N : ℝ)) τ' (t N) 0 < gridT (((band d).W N : ℝ)) τ' (t N) 1) := by
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ := cond272Reg_grid_step_domain (band d) hκ0 hτ
  refine ⟨τ', hτ'0, c, hc0, fun E hE t ht0 ht => ?_⟩
  obtain ⟨-, hstep⟩ := hgrid E hE t ht0 ht
  obtain ⟨hu0, huv, hv1, hcond⟩ := hstep 0
  have hB : BoundsCore (sample d) E (fun N => gridT (((band d).W N : ℝ)) τ' (t N) 0) :=
    (BoundsCore_zero (sample d) (by linarith : |E| ≤ 2)).congr (sample d)
      (Eventually.of_forall fun N => (gridT_zero (ht0 N)).symm)
  refine ⟨step1Hyp_gauss_of_scale'' d hκ0 hE hB hu0 huv hv1 hcond.1 hc0 hcond.2, hcond.2,
    fun htpos => eventually_gridT_zero_lt_gridT_one (band d) hτ'0 htpos⟩

/-- **A fully explicit, quantifier-free witness for `RBM.Step1.Hyp`.**

`step1Hyp_gauss_grid_first` with every remaining parameter pinned down: T202's non-degenerate
dimensions `RBM.Gauss.Dims.exampleGrow` (`L ≍ N^{1/4} → ∞`, `W ≍ N^{3/4} → ∞`), the energy
`E = 0` at the centre of the spectrum (`κ = 1`), and the right end of the flow at the paper's
own `t_N = 1 - N^{-1/2}` (i.e. `τ = 1/2` in `t ≤ 1 - N^{-1+τ}`).  All three conjuncts are
closed statements: `RBM.Step1.Hyp` on the first grid window, the scale certificate
`N^c ≤ W ℓ_{u_1} η_{u_1}` with `c > 0`, and `u_0 < u_1` — no hypothesis is left to satisfy. -/
theorem step1Hyp_gauss_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧
      Step1.Hyp (sample Dims.exampleGrow) 0
          (fun N => gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
            (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) 0)
          (fun N => gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
            (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) 1) ∧
        (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band Dims.exampleGrow).scale 0 N
          (gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
            (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) 1)) ∧
        (∀ᶠ N : ℕ in atTop,
          gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
              (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) 0 <
            gridT (((band Dims.exampleGrow).W N : ℝ)) τ'
              (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) 1) := by
  obtain ⟨τ', hτ'0, c, hc0, h⟩ :=
    step1Hyp_gauss_grid_first Dims.exampleGrow (κ := 1) (τ := 1 / 2) one_pos (by norm_num)
  have ht0 : ∀ N : ℕ, 0 ≤ 1 - (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
      norm_num
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h0
      have := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num : -(1 : ℝ) / 2 ≤ 0)
      linarith
  have ht : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 : ℝ) / 2) ≤ 1 - (1 - (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
    refine Eventually.of_forall fun N => ?_
    rw [show (-1 + (1 : ℝ) / 2) = -(1 : ℝ) / 2 by norm_num]
    linarith
  have htpos : ∀ᶠ N : ℕ in atTop, 0 < 1 - (N : ℝ) ^ (-(1 : ℝ) / 2) := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
    have := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by norm_num : -(1 : ℝ) / 2 < 0)
    linarith
  obtain ⟨h1, h2, h3⟩ := h 0 (by norm_num) _ ht0 ht
  exact ⟨τ', hτ'0, c, hc0, h1, h2, h3 htpos⟩

/-- **`RBM.Step1.Hyp` at every *later* grid window, where the start time is positive.**

The `s > 0` instance.  `RBM.BoundsCore` at `u_{k+1}` is not assumed: it is produced by the
induction of p. 24, `RBM.BoundsCore_of_Thm221NoEL`, run on
`RBM.Gauss.thm221NoEL_of_inputs_entries_gauss` — i.e. on the four named inputs of Steps 2–5
that remain open after T242, and on nothing else.  Its time hypothesis
`N^{-1+τ} ≤ 1 - u_{k+1}` follows from the one for `t`, since `u_{k+1} ≤ t`
(`RBM.gridT_le`).

The second conjunct is the certificate that the start time really is positive:
`0 < u_1 ≤ u_{k+1}` eventually, by `RBM.Gauss.eventually_gridT_zero_lt_gridT_one` and
`RBM.gridT_mono`. -/
theorem step1Hyp_gauss_grid_pos (d : Dims) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      ∀ D : ℝ, 60 ≤ D → MomentDuhamelCut.MomentHypCut (sample d) E s t D)
    (hΘ : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2)
        (fun N (_ : TimeIcc s t N) (_ : Ω d) => Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2)))
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
        (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) n)
    (h45 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      StepGlue.Eq45Flow (sample d) E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg (band d) E s t c →
      Eq548EntryData (sample d) E s t)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∀ E : ℝ, |E| ≤ 2 - κ → ∀ t : ℕ → ℝ,
      (∀ N, 0 ≤ t N) → (∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-1 + τ) ≤ 1 - t N) →
      (∀ᶠ N : ℕ in atTop, 0 < t N) → ∀ k : ℕ,
        Step1.Hyp (sample d) E
            (fun N => gridT (((band d).W N : ℝ)) τ' (t N) (k + 1))
            (fun N => gridT (((band d).W N : ℝ)) τ' (t N) (k + 1 + 1)) ∧
          (∀ᶠ N : ℕ in atTop, 0 < gridT (((band d).W N : ℝ)) τ' (t N) (k + 1)) := by
  have hT : Thm221NoEL (sample d) κ :=
    thm221NoEL_of_inputs_entries_gauss d hκ0 hκ1 Hy hΘ h514 h45 h548e
  obtain ⟨τ', hτ'0, c, hc0, n₀, hgrid⟩ := cond272Reg_grid_step_domain (band d) hκ0 hτ
  refine ⟨τ', hτ'0, c, hc0, fun E hE t ht0 ht htpos k => ?_⟩
  obtain ⟨-, hstep⟩ := hgrid E hE t ht0 ht
  obtain ⟨hu0, huv, hv1, hcond⟩ := hstep (k + 1)
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < gridT (((band d).W N : ℝ)) τ' (t N) (k + 1) := by
    filter_upwards [eventually_gridT_zero_lt_gridT_one (band d) hτ'0 htpos, htpos]
      with N h1 h2
    have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have h3 : gridT (((band d).W N : ℝ)) τ' (t N) 1 ≤
        gridT (((band d).W N : ℝ)) τ' (t N) (k + 1) :=
      gridT_mono hW1 hτ'0.le (t N) (by omega)
    have h0 : gridT (((band d).W N : ℝ)) τ' (t N) 0 = 0 := gridT_zero h2.le
    rw [h0] at h1
    linarith
  have hB : BoundsCore (sample d) E
      (fun N => gridT (((band d).W N : ℝ)) τ' (t N) (k + 1)) := by
    refine BoundsCore_of_Thm221NoEL (sample d) hκ0 hT hE hτ hu0 ?_
    filter_upwards [ht] with N hN
    have := gridT_le (W := ((band d).W N : ℝ)) (τ' := τ') (t N) (k + 1)
    linarith
  exact ⟨step1Hyp_gauss_of_scale'' d hκ0 hE hB hu0 huv hv1 hcond.1 hc0 hcond.2, hpos⟩

end Witness

end RBM.Gauss
