/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Hierarchy.DriftDef

/-!
# (5.48) with the drift pinned, and `cFarStep ≺ 1` (T208)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.21), (5.34)–(5.36), (5.39)–(5.41), (5.45), (5.48) and §7, (7.2).

`RBM1D/Hierarchy/Step2MomentStep.lean` §11 (T198) closed the far-field slot of (5.48): its
`RBM.Step2MomentStep.flowEq548_of_near_farInputs` produces `RBM.Step45.FlowEq548` from a
bundle `RBM.Step2MomentStep.FarInputs` instead of from an opaque `hfar`.  But that bundle

```
∀ v, ∃ F Fn : ℝ → LoopArg (B.L N) 2 → ℂ, ∃ Mrt : LoopArg (B.L N) 2 → ℂ, …
```

**existentially quantifies the drift and the martingale**, and its satisfiability witness
`RBM.Step2MomentStep.farInputs_of_remainder` takes `F = Fn = 0`.  That is the fiat shape: if
the drift is free data of the hypothesis, (5.48) says nothing about the model.  This file
removes the freedom.

## What is pinned here

* `RBM.Step2FarInputs.farDrift` — the drift of (5.15)/(5.21) at `σ = (+,-)` along the flow,
  i.e. `RBM.DriftDef.driftF` at `n = 0`.  It is a **definition** in the Green function of
  `H_u = √u X`: by `RBM.Step2FarInputs.farDrift_eq_eGpm_add_quadGlue` it is
  `E^{(G̃)}_{u,(+,-),a} + E^{((L-K)×(L-K))}_{u,(+,-),a}` — T163's `RBM.EGDef.eGpm` plus the
  quadratic gluing term of (5.34)/(5.49) — and `RBM.DriftDef.F_eq_driftF` says that the `F`
  of `RBM.MomentDuhamel.Hyp` *equals* it.  Nothing can be chosen.
* `RBM.Step2FarInputs.farDriftNear` — its restriction to the diagonal band `‖b₁-b₂‖ ≤ ℓ*_u`,
  the near-field term of (5.35).  A definition, not a second drift: the splitting
  `F = Fn + (F - Fn)` that `RBM.Step2MomentStep.step_bound_far` needs is now the literal
  restriction/co-restriction, so `RBM.Step2FarInputs.FarInputs'` constrains `farDrift` itself
  on the two regions.
* `RBM.Step2FarInputs.farMart` — the **defect** of the Duhamel identity (5.20) for `farDrift`.
  Defining it as the defect makes the identity a `rfl`-level fact
  (`RBM.Step2FarInputs.farDrift_duhamel`) and turns the one remaining input into a bound on a
  pinned object: the hypothesis "`farMart` is small" is (5.20) **and** (5.45) together, which
  is strictly weaker than assuming the two separately.  (5.20) is Itô; (5.45) is BDG; neither
  is available, and this is the only place where the stochastic layer enters the far field.

So `RBM.Step2FarInputs.FarInputs'` has **no free tensor at all**: it is four inequalities
about `RBM.Step2.lk`, `farDrift` and `farMart`, every one of which unfolds to the Green
function of `H_u`.  `RBM.Step2FarInputs.farInputs_of_farInputs'` maps it into T198's bundle.

## `cFarStep ≺ 1`: the constant of T198 is **not** `≺ 1`, and why

`RBM.Step2MomentStep.cFarStep = Ξ(M_i + M_f) + M_m + 1`, where `M_f` is the far-field constant
of the drift, *uniformly in `u ∈ [s,v)`*.  The drift's far bound is (5.35), shape 2
(`RBM.EGDef.eGpm_le_reduced`), whose prefactor is

`η_u^{-1} ( c_far (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} J*  +  169 (ℓ_u/ℓ_s) A_u^{-1} (J*)^{3/2} )`,

and `η_u^{-1}` is **not** `N^{o(1)}` — at `u = s` it is `η_s^{-1}`, up to `N^{1-τ}`.  What is
`≺ 1` is the *time integral*: `RBM.Step2MomentStep.step_bound_far` bounds
`∫_s^v … du` by `sup_u … × |v - s|` and then throws `|v-s| ≤ 1` away, while `|v - s| ≤ 1 - s
= η_s / Im m` is exactly the factor that cancels the `η_s^{-1}`.  Keeping it is the whole
content of `RBM.Step2FarInputs.step_bound_far'` and of the constant

`RBM.Step2FarInputs.cFarStep' = Ξ (M_i + M_f (1 - s)) + M_m + 1`,

for which `RBM.Step2FarInputs.detDom_cFarStep'` proves `≺ 1` from `Ξ ≺ 1` (a theorem here,
`RBM.Step2FarInputs.eventually_xiK_le`) and from `M_i ≺ 1`, `M_f (1-s) ≺ 1`, `M_m ≺ 1` — the
three one-step inputs (2.69), (5.35) and (5.45).

**This is a correction to T198**, and a precise one: `RBM.Step2MomentStep.cFarStep ≺ 1` is
false on data that (5.35) does produce (`RBM.Step2FarInputs.cFarStep_not_detDom`, at the
critical scaling `M_f = (1-s)^{-1}`), while `cFarStep' ≺ 1` holds there
(`RBM.Step2FarInputs.cFarStep'_detDom_critical`).  At `s = 0` the two constants are literally
equal (`RBM.Step2FarInputs.cFarStep'_eq_cFarStep`), so T198's §11 is usable exactly when `s`
is bounded away from `1` — which the grid of Lemmas 2.18–2.20 is not.

## Main results

* `RBM.Step2FarInputs.farDrift_eq_eGpm_add_quadGlue`, `farDrift_duhamel` — the drift is pinned
  and the Duhamel identity holds for it.
* `RBM.Step2FarInputs.FarInputs'`, `farInputs_of_farInputs'` — the free-tensor-free bundle.
* `RBM.Step2FarInputs.step_bound_far'`, `lkErr_far_le'`, `far_le_of_farInputs'`,
  `stochDom_far_of_farInputs'` — (5.39)/(5.41)/(5.44) with the indicators kept **and** the
  length of the time interval kept.
* `RBM.Step2FarInputs.flowEq548_of_farInputs'` — **(5.48)**, `RBM.Step45.FlowEq548`, with no
  free drift anywhere in the hypothesis list.
* `RBM.Step2FarInputs.eventually_xiK_le`, `detDom_cFarStep'` — **`cFarStep' ≺ 1`**.
* `RBM.Step2FarInputs.farInputs'_of_eG_of_quad` — the two drift inputs produced from (5.35)
  (`RBM.EGDef.eGpm_le_reduced`, T163) and (5.34) (the quadratic gluing term), i.e. from the
  two summands `farDrift` actually has.
* `RBM.Step2FarInputs.farDrift_eq_zero_of_farInputs'_zero` — the anti-fiat certificate:
  `M_n = M_f = 0` forces the *model's* drift to vanish.  T198's bundle has no such property —
  `RBM.Step2MomentStep.farInputs_of_remainder` takes `M_n = M_f = 0` for every sample.
* `RBM.Step2FarInputs.cFarStep'_detDom_critical`, `cFarStep_not_detDom` — the satisfiability
  witness at the **critical** scaling `M_f = (1-s)^{-1}`, which is the size (5.35) gives, and
  the proof that T198's constant is not `≺ 1` there.

## Deviations from the paper (paper-delta `T208a`)

`RBM.Step2FarInputs.cFarStep'` carries the factor `1 - s`, which the paper's (5.48) does not
display.  The paper integrates the drift over `[s,t]` and the factor is produced by that
integration; keeping `sup_u` and the length separately is the only way to say it without an
`L¹` hypothesis on the drift, and at `s = 0` — the case Step 5 uses — the two agree.
-/

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 1. The pinned one-step data -/

section Pinned

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The drift of (5.15)/(5.21) at `σ = (+,-)`, along the flow** — `RBM.DriftDef.driftF` at
loop length `2`.  A definition in the Green function of `H_u`; no structure field occurs. -/
noncomputable def farDrift (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℂ :=
  fun a => DriftDef.driftF B E N u (X.H N u ω) (n := 0) Step2.sigPM a

/-- **The near-diagonal part of the pinned drift**: its restriction to `‖b₁-b₂‖ ≤ ℓ*_u`, the
region carrying the indicator of (5.35)/(5.41). -/
noncomputable def farDriftNear (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℂ :=
  fun b => if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
           then farDrift X E N u ω b else 0

/-- **The martingale term of (5.20)**, defined as the defect of the Duhamel identity for the
pinned drift.  Definition 5.3's `E^{(M)}` integrated; the only thing assumed about it below is
a size bound, which is (5.20) and (5.45) in one. -/
noncomputable def farMart (X : Sample B) (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (v : ℝ) (ω : Ω) :
    LoopArg (B.L N) 2 → ℂ :=
  fun a => Step2.lk X E N v ω a
    - Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Step2.lk X E N (s N) ω) a
    - ∫ u in (s N)..v, Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (farDrift X E N u ω) a

variable (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

/-- **(5.21)/(5.20) for the pinned drift**, by construction of `RBM.Step2FarInputs.farMart`. -/
theorem farDrift_duhamel (N : ℕ) (v : ℝ) (ω : Ω) (a : LoopArg (B.L N) 2) :
    Step2.lk X E N v ω a
      = Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((s N : ℝ) : ℂ) ((v : ℝ) : ℂ)
          (Step2.lk X E N (s N) ω) a
        + (∫ u in (s N)..v,
            Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
              (farDrift X E N u ω) a)
        + farMart X E s N v ω a := by
  unfold farMart; ring

theorem etaExpand_two {L : ℕ} (a : LoopArg L 2) : ![a 0, a 1] = a := by
  funext i; fin_cases i <;> rfl

/-- **The pinned drift, unfolded**: at loop length `2` it is T163's `E^{(G̃)}` of (5.51) plus
the quadratic gluing term `E^{((L-K)×(L-K))}` of (5.34)/(5.49), and nothing else
(`RBM.DriftDef.driftF_zero_eq_eGpm_add_quadGlue`).  Both summands are definitions in the Green
function of `H_u = √u X`; this is the fiat audit of the left-hand side of (5.35)/(5.34). -/
theorem farDrift_eq_eGpm_add_quadGlue (N : ℕ) (u : ℝ) (ω : Ω) (a : LoopArg (B.L N) 2) :
    farDrift X E N u ω a
      = EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (a 0) (a 1)
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            ⟨[true, false], [a 0, a 1]⟩ := by
  rw [farDrift, show (Step2.sigPM : Fin 2 → Bool) = ![true, false] from rfl, ← etaExpand_two a]
  exact DriftDef.driftF_zero_eq_eGpm_add_quadGlue B E N u (X.H N u ω) (a 0) (a 1)

/-- **The pinned drift is the `F` of `RBM.MomentDuhamel.Hyp`** — read along the flow, at the
charges `(+,-)`, in the regime `|E| < 2`, `0 ≤ u < 1`.  `RBM.MomentDuhamel.Hyp.F` is itself
pinned by the field `drift` (`RBM.MomentDuhamel.Hyp.F_unique`); this says that the object this
file bounds is that one. -/
theorem Fpath_eq_farDrift {t : ℕ → ℝ} (H : MomentDuhamel.Hyp X E s t 0) {N : ℕ} {u : ℝ}
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N) (ω : Ω)
    (a : LoopArg (B.L N) 2) :
    H.Fpath N u ω Step2.sigPM a = farDrift X E N u ω a :=
  DriftDef.Fpath_eq_driftF_of_lt_one H hE hu0 hu1 hsu hut ω Step2.sigPM a

end Pinned

/-! ### 2. One step of (5.21) in the far field, with the length of `[s,v]` kept

`RBM.Step2MomentStep.step_bound_far` bounds the drift integral by `sup_u × |v - s|` and then
uses `|v - s| ≤ 1`.  That last step is what makes `RBM.Step2MomentStep.cFarStep ≺ 1`
unprovable: the far-field constant of (5.35) is `η_u^{-1}(…)`, whose supremum over `u ∈ [s,v)`
is of order `η_s^{-1}`, and `|v - s| ≤ 1 - s = η_s / Im m` is exactly the factor that cancels
it.  Everything else in this section is `RBM.Step2MomentStep.step_bound_far` verbatim.

The martingale bound is also asked for **only at the far argument `a`** — which is the only
place the proof uses it.  Near the diagonal the martingale really does carry `(η_s/η_v)²`
((5.45)), so demanding `‖E^{(M)}_a‖ ≤ M_m T` at *every* `a` with `M_m ≺ 1` would be an
unsatisfiable hypothesis. -/

section FarStep

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

/-- **(5.39)/(5.41)/(5.44) in the far field, with the time-interval length kept.**
`RBM.Step2MomentStep.step_bound_far` with `|v - s| ≤ 1` replaced by `|v - s| ≤ len`, and with
the martingale bound asked only at the argument `a` at which it is used. -/
theorem step_bound_far' (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D Mi Mn Mf Mm len : ℝ} (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn) (hMf : 0 ≤ Mf)
    (hlen : v - s N ≤ len)
    {F Fn : ℝ → LoopArg (B.L N) 2 → ℂ} {Mrt : LoopArg (B.L N) 2 → ℂ}
    (hdu : ∀ a, Step2.lk X E N v ω a
      = Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (s N : ℂ) (v : ℂ)
            (Step2.lk X E N (s N) ω) a
        + (∫ u in (s N)..v,
            Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (u : ℂ) (v : ℂ) (F u) a)
        + Mrt a)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b, ‖Fn u b‖
      ≤ Mn * (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
              then 1 else 0))
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b, ‖F u b - Fn u b‖
      ≤ Mf * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)))
    (a : LoopArg (B.L N) 2)
    (hmart : ‖Mrt a‖ ≤ Mm * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ)) :
    ‖Step2.lk X E N v ω a‖
      ≤ (Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + Mm)
          * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))
        + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
            * (B.W N : ℝ) ^ (-D)
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := by
  have hL1 : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hm0 := mE_im_pos hE
  have hlogW : 0 ≤ log (B.W N : ℝ) :=
    Real.log_nonneg (le_trans (Real.one_le_exp (by norm_num)) hW)
  have h1v : 0 < 1 - v := by linarith
  have h1s : 0 < 1 - s N := by linarith
  have hlen0 : 0 ≤ len := le_trans (by linarith) hlen
  have hTv0 : (0:ℝ) ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) :=
    tailT_nonneg hW0.le _
  have hΞ0 : (0:ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hWD : (0:ℝ) ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  have hmi : (0:ℝ) ≤ ((mE E).im ^ 2)⁻¹ := by positivity
  have hE5 : (0:ℝ) ≤ exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := (exp_pos _).le
  have hR0 : (0:ℝ) ≤ etaT E (s N) / etaT E v := by
    rw [Step2.etaT_ratio hE]; positivity
  have hellv : 1 ≤ B.ell N v := one_le_ellHat_of_nonneg hL1 hv0 hv1
  have hstv : 0 ≤ ellStar (B.W N : ℝ) (B.ell N v) := by
    unfold ellStar
    have hp : (0:ℝ) ≤ log (B.W N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlogW _
    nlinarith
  have hd1 : ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by linarith
  -- the initial term (5.39)
  have hI := Step2MomentStep.norm_Uker_far_flow hE hs0 hsv hv0 hv1 hW hMi hinit a hd1
  -- the drift, pointwise in `u ∈ [s, v)`
  have hdrift : ∀ u ∈ Set.Ico (s N) v,
      ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (u : ℂ) (v : ℂ) (F u) a‖
        ≤ 128 * exp 3 * Mn * (etaT E (s N) / etaT E v) ^ 2
              * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
          + Mf * (Step2.xiK (B.L N) (B.W N) (mE E).im
              * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))
            + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (B.W N : ℝ) ^ (-D)) := by
    intro u hu
    have hu0 : 0 ≤ u := hs0.trans hu.1
    have huv : u ≤ v := hu.2.le
    have hu1 : u < 1 := hu.2.trans hv1
    have hru : etaT E u / etaT E v ≤ etaT E (s N) / etaT E v := by
      rw [Step2.etaT_ratio hE, Step2.etaT_ratio hE]
      gcongr
      linarith [hu.1]
    have hru0 : (0:ℝ) ≤ etaT E u / etaT E v := by rw [Step2.etaT_ratio hE]; positivity
    have hsplit : F u = Fn u + (fun b => F u b - Fn u b) := by funext b; simp
    rw [hsplit, Uker_add, Pi.add_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (Step2MomentStep.norm_Uker_supp_flow hE hu0 huv hv1 hW hMn (hFn u hu) a
        hfar).trans ?_
      have he3 : (0:ℝ) ≤ exp 3 := (exp_pos _).le
      gcongr
    · refine (Step2MomentStep.norm_Uker_far_flow hE hu0 huv hv0 hv1 hW hMf (hFr u hu) a
        hd1).trans ?_
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hMf
      gcongr
  set C : ℝ := 128 * exp 3 * Mn * (etaT E (s N) / etaT E v) ^ 2
        * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
      + Mf * (Step2.xiK (B.L N) (B.W N) (mE E).im
          * Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))
        + ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (B.W N : ℝ) ^ (-D)) with hCdef
  have hC0 : (0:ℝ) ≤ C := by rw [hCdef]; positivity
  have hint : ‖∫ u in (s N)..v,
      Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (u : ℂ) (v : ℂ) (F u) a‖ ≤ C * |v - s N| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume v] with u hne hu
    rw [Set.uIoc_of_le hsv] at hu
    exact hdrift u ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩
  have hvs : |v - s N| ≤ len := by rw [abs_of_nonneg (by linarith)]; linarith
  have hint' : ‖∫ u in (s N)..v,
      Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (u : ℂ) (v : ℂ) (F u) a‖ ≤ C * len :=
    hint.trans (mul_le_mul_of_nonneg_left hvs hC0)
  have htri : ‖Step2.lk X E N v ω a‖
      ≤ ‖Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (s N : ℂ) (v : ℂ)
            (Step2.lk X E N (s N) ω) a‖
        + ‖∫ u in (s N)..v,
            Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (u : ℂ) (v : ℂ) (F u) a‖
        + ‖Mrt a‖ := by
    rw [hdu a]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [hCdef] at hint'
  nlinarith [htri, hI, hint', hmart]

/-- **(5.48)'s far half, pathwise, with the length kept.**  `RBM.Step2FarInputs.step_bound_far'`
at the loop-error level, the two residues absorbed into `W^{-D} ≤ T_{v,D}`. -/
theorem lkErr_far_le' (hE : |E| < 2) {N : ℕ} {ω : Ω} (hs0 : 0 ≤ s N) {v : ℝ}
    (hsv : s N ≤ v) (hv1 : v < 1) (hW : exp 1 ≤ (B.W N : ℝ))
    {D D' Mi Mn Mf Mm len : ℝ} (hDD : D ≤ D') (hMi : 0 ≤ Mi) (hMn : 0 ≤ Mn) (hMf : 0 ≤ Mf)
    (hMm : 0 ≤ Mm) (hlen : v - s N ≤ len)
    {F Fn : ℝ → LoopArg (B.L N) 2 → ℂ} {Mrt : LoopArg (B.L N) 2 → ℂ}
    (hdu : ∀ a, Step2.lk X E N v ω a
      = Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (s N : ℂ) (v : ℂ)
            (Step2.lk X E N (s N) ω) a
        + (∫ u in (s N)..v,
            Uker (B.L N) (xiOf (mSigma E) Step2.sigPM) (u : ℂ) (v : ℂ) (F u) a)
        + Mrt a)
    (hinit : ∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (hFn : ∀ u ∈ Set.Ico (s N) v, ∀ b, ‖Fn u b‖
      ≤ Mn * (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
              then 1 else 0))
    (hFr : ∀ u ∈ Set.Ico (s N) v, ∀ b, ‖F u b - Fn u b‖
      ≤ Mf * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hres : ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E v) ^ 2 * (Mi + Mf * len)
          * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn * len) * (etaT E (s N) / etaT E v) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
        ≤ (B.W N : ℝ) ^ (-D))
    (x y : ZMod (B.L N))
    (hmart : ‖Mrt ![x, y]‖ ≤ Mm * Step2.tT B E N D' v (zdist (B.L N) (x - y)))
    (hfar : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (x - y) : ℝ)) :
    X.lkErr E N v ω (pmLoop x y)
      ≤ (Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + Mm + 1)
          * Step2.tT B E N D v (zdist (B.L N) (x - y)) := by
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := le_trans (Real.one_le_exp (by norm_num)) hW
  have hW0 : (0:ℝ) < (B.W N : ℝ) := by linarith
  set a : LoopArg (B.L N) 2 := ![x, y] with hadef
  have ha0 : a 0 = x := rfl
  have ha1 : a 1 = y := rfl
  have hfar' : 6 * ellStar (B.W N : ℝ) (B.ell N v) ≤ (zdist (B.L N) (a 0 - a 1) : ℝ) := by
    rw [ha0, ha1]; exact hfar
  have hmart' : ‖Mrt a‖ ≤ Mm * Step2.tT B E N D' v (zdist (B.L N) (a 0 - a 1)) := by
    rw [ha0, ha1]; exact hmart
  have key := step_bound_far' X hE hs0 hsv hv1 hW hMi hMn hMf hlen hdu hinit hFn hFr a
    hmart' hfar'
  rw [ha0, ha1] at key
  have heq : X.lkErr E N v ω (pmLoop x y) = ‖Step2.lk X E N v ω a‖ := by
    rw [Step2.norm_lk_eq, ha0, ha1]
  rw [heq]
  refine key.trans ?_
  have hDW : (B.W N : ℝ) ^ (-D') ≤ (B.W N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hTmono : Step2.tT B E N D' v (zdist (B.L N) (x - y))
      ≤ Step2.tT B E N D v (zdist (B.L N) (x - y)) := by
    unfold Step2.tT tailT
    have : (0:ℝ) ≤ (((B.W N : ℝ) * B.ell N v * etaT E v) ^ 2)⁻¹
        * exp (-√((zdist (B.L N) (x - y) : ℝ) / B.ell N v)) := by positivity
    linarith
  have hWT : (B.W N : ℝ) ^ (-D) ≤ Step2.tT B E N D v (zdist (B.L N) (x - y)) :=
    rpow_neg_le_tailT _
  have hΞ0 : (0:ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hlen0 : 0 ≤ len := le_trans (by linarith) hlen
  have hcoef : (0:ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi + Mf * len) + Mm := by
    have : (0:ℝ) ≤ Mi + Mf * len := by positivity
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hTmono hcoef
  nlinarith

end FarStep

/-! ### 3. The one-step inputs, with no free tensor -/

section Inputs

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The pathwise one-step inputs of the far half of (5.48), with the drift pinned.**

Compare `RBM.Step2MomentStep.FarInputs`, which reads
`∀ v, ∃ F Fn Mrt, (Duhamel identity) ∧ …`: there `F`, `Fn` and `Mrt` are free data, and its
witness takes `F = Fn = 0`.  Here there is **no existential**: the four conditions are

* (2.69) — the initial loop error at `s`;
* (5.35) near — `‖F_u‖ ≤ M_n` on the diagonal band `‖b₁-b₂‖ ≤ ℓ*_u`;
* (5.35) far — `‖F_u‖ ≤ M_f T_{u,D'}` off it;
* (5.45) — the Duhamel defect at the *far* arguments,

and `F_u` is `RBM.Step2FarInputs.farDrift`, the defined drift, while the defect is
`RBM.Step2FarInputs.farMart`, a definition too.  Every left-hand side unfolds to the Green
function of `H_u = √u X`. -/
def FarInputs' (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D' : ℝ) (Mi Mn Mf Mm : ℕ → ℝ)
    (N : ℕ) (ω : Ω) : Prop :=
  (∀ b, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi N * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
  ∧ (∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖farDrift X E N u ω b‖ ≤ Mn N)
  ∧ (∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖farDrift X E N u ω b‖ ≤ Mf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
  ∧ (∀ v : TimeIcc s t N, ∀ x y : ZMod (B.L N),
      6 * ellStar (B.W N : ℝ) (B.ell N (v : ℝ)) ≤ (zdist (B.L N) (x - y) : ℝ) →
        ‖farMart X E s N (v : ℝ) ω ![x, y]‖
          ≤ Mm N * Step2.tT B E N D' (v : ℝ) (zdist (B.L N) (x - y)))

/-- The far-field constant, **with the length of the time interval**:
`Ξ (M_i + M_f (1-s)) + M_m + 1`.  See the module docstring for why
`RBM.Step2MomentStep.cFarStep`, which has `M_f` alone, is not `≺ 1`. -/
noncomputable def cFarStep' (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (Mi Mf Mm : ℕ → ℝ) (N : ℕ) : ℝ :=
  Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi N + Mf N * (1 - s N)) + Mm N + 1

/-- At `s = 0` — the time Step 5 runs the argument from — `cFarStep'` is
`RBM.Step2MomentStep.cFarStep` verbatim. -/
theorem cFarStep'_eq_cFarStep (B : Band Ω) (E : ℝ) {s : ℕ → ℝ} (hs : ∀ N, s N = 0)
    (Mi Mf Mm : ℕ → ℝ) (N : ℕ) :
    cFarStep' B E s Mi Mf Mm N = Step2MomentStep.cFarStep B E Mi Mf Mm N := by
  rw [cFarStep', Step2MomentStep.cFarStep, hs N]; ring

/-- The residue condition of the far half, with the length kept. -/
def FarResidue' (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (D D' : ℝ) (Mi Mn Mf : ℕ → ℝ)
    (N : ℕ) : Prop :=
  ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E (t N)) ^ 2 * (Mi N + Mf N * (1 - s N))
      * (B.W N : ℝ) ^ (-D')
    + 128 * exp 3 * (Mn N * (1 - s N)) * (etaT E (s N) / etaT E (t N)) ^ 2
        * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
    ≤ (B.W N : ℝ) ^ (-D)

/-- **The far half of (5.48), uniformly in `(v, a₁, a₂)`, at a fixed `(N, ω)`**, from the
pinned inputs. -/
theorem far_le_of_farInputs' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {N : ℕ} (hW : exp 1 ≤ (B.W N : ℝ)) {D D' : ℝ} (hDD : D ≤ D')
    {Mi Mn Mf Mm : ℕ → ℝ} (hMi : 0 ≤ Mi N) (hMn : 0 ≤ Mn N) (hMf : 0 ≤ Mf N)
    (hMm : 0 ≤ Mm N) (hres : FarResidue' B E s t D D' Mi Mn Mf N)
    {ω : Ω} (hin : FarInputs' X E s t D' Mi Mn Mf Mm N ω)
    (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) :
    (if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
        then 0 else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      ≤ cFarStep' B E s Mi Mf Mm N *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2)) := by
  obtain ⟨hinit, hnear, hfarD, hmart⟩ := hin
  have hW0 : (0:ℝ) < (B.W N : ℝ) := lt_of_lt_of_le (exp_pos 1) hW
  have hT0 : (0:ℝ) ≤ tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
      (zdist (B.L N) (p.2.1 - p.2.2)) := tailT_nonneg hW0.le _
  have hΞ0 : (0:ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hs1 : s N < 1 := lt_of_le_of_lt (hst N) (ht1 N)
  have hlen0 : (0:ℝ) ≤ 1 - s N := by linarith
  have hC0 : (0:ℝ) ≤ cFarStep' B E s Mi Mf Mm N := by
    have h1 : (0:ℝ) ≤ Mi N + Mf N * (1 - s N) := by positivity
    unfold cFarStep'; nlinarith
  by_cases hnearcase : (zdist (B.L N) (p.2.1 - p.2.2) : ℝ)
      ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
  · rw [show (if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ)
        ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1) then (0:ℝ)
        else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2)) = 0 by simp [hnearcase]]
    positivity
  · rw [show (if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ)
        ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1) then (0:ℝ)
        else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
        = X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2) by simp [hnearcase]]
    push Not at hnearcase
    have hv1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 N)
    have hsv : s N ≤ (p.1 : ℝ) := p.1.2.1
    have hvlen : (p.1 : ℝ) - s N ≤ 1 - s N := by linarith
    -- the drift split, from the two pointwise bounds
    have hFn : ∀ u ∈ Set.Ico (s N) (p.1 : ℝ), ∀ b : LoopArg (B.L N) 2,
        ‖farDriftNear X E N u ω b‖
          ≤ Mn N * (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
                    then 1 else 0) := by
      intro u hu b
      have hu' : u ∈ Set.Ico (s N) (t N) := ⟨hu.1, lt_of_lt_of_le hu.2 p.1.2.2⟩
      unfold farDriftNear
      split_ifs with hb
      · rw [mul_one]; exact hnear u hu' b hb
      · simp
    have hFr : ∀ u ∈ Set.Ico (s N) (p.1 : ℝ), ∀ b : LoopArg (B.L N) 2,
        ‖farDrift X E N u ω b - farDriftNear X E N u ω b‖
          ≤ Mf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := by
      intro u hu b
      have hu' : u ∈ Set.Ico (s N) (t N) := ⟨hu.1, lt_of_lt_of_le hu.2 p.1.2.2⟩
      unfold farDriftNear
      split_ifs with hb
      · rw [sub_self, norm_zero]
        have : (0:ℝ) ≤ Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) :=
          tailT_nonneg hW0.le _
        positivity
      · rw [sub_zero]
        exact hfarD u hu' b hb
    -- the residue, transported from `t N` to `v`
    have h1t : (0:ℝ) < 1 - t N := by linarith [ht1 N]
    have hRv : etaT E (s N) / etaT E p.1 ≤ etaT E (s N) / etaT E (t N) := by
      rw [Step2.etaT_ratio hE, Step2.etaT_ratio hE]
      gcongr
      linarith [hs0 N, p.1.2.2, ht1 N]
    have hRv0 : (0:ℝ) ≤ etaT E (s N) / etaT E p.1 := by
      rw [Step2.etaT_ratio hE]
      have h1s : (0:ℝ) < 1 - s N := by linarith
      positivity
    have hmi : (0:ℝ) ≤ ((mE E).im ^ 2)⁻¹ := by positivity
    have hWD : (0:ℝ) ≤ (B.W N : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
    have hE5 : (0:ℝ) ≤ exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2))) := (exp_pos _).le
    have hresv : ((mE E).im ^ 2)⁻¹ * (etaT E (s N) / etaT E p.1) ^ 2
            * (Mi N + Mf N * (1 - s N)) * (B.W N : ℝ) ^ (-D')
        + 128 * exp 3 * (Mn N * (1 - s N)) * (etaT E (s N) / etaT E p.1) ^ 2
            * exp (-(5 / 4 * log (B.W N : ℝ) ^ ((3 : ℝ) / 2)))
        ≤ (B.W N : ℝ) ^ (-D) := by
      refine le_trans ?_ hres
      have hsq : (etaT E (s N) / etaT E p.1) ^ 2 ≤ (etaT E (s N) / etaT E (t N)) ^ 2 := by
        gcongr
      have he3 : (0:ℝ) ≤ exp 3 := (exp_pos _).le
      have h1 : (0:ℝ) ≤ Mi N + Mf N * (1 - s N) := by positivity
      have h2 : (0:ℝ) ≤ Mn N * (1 - s N) := by positivity
      gcongr
    have key := lkErr_far_le' X hE (hs0 N) hsv hv1 hW hDD hMi hMn hMf hMm hvlen
      (fun a => farDrift_duhamel X N (p.1 : ℝ) ω a) hinit hFn hFr hresv p.2.1 p.2.2
      (hmart p.1 p.2.1 p.2.2 hnearcase.le) hnearcase.le
    exact key

/-- **(5.48)'s far half, `≺`**, from the pinned inputs. -/
theorem stochDom_far_of_farInputs' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {D D' : ℝ} (hDD : D ≤ D') {Mi Mn Mf Mm : ℕ → ℝ}
    (hMi : ∀ N, 0 ≤ Mi N) (hMn : ∀ N, 0 ≤ Mn N) (hMf : ∀ N, 0 ≤ Mf N) (hMm : ∀ N, 0 ≤ Mm N)
    (hfacts : ∀ᶠ N : ℕ in Filter.atTop,
      exp 1 ≤ (B.W N : ℝ) ∧ FarResidue' B E s t D D' Mi Mn Mf N)
    (hpoly : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, cFarStep' B E s Mi Mf Mm N ≤ (N : ℝ) ^ τ)
    (hHP : HighProb B.P (fun N => {ω | FarInputs' X E s t D' Mi Mn Mf Mm N ω})) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
          then 0 else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
        (zdist (B.L N) (p.2.1 - p.2.2))) := by
  have hC0 : ∀ N, 0 ≤ cFarStep' B E s Mi Mf Mm N := by
    intro N
    have h1 := Step2.xiK_nonneg (B.L N) (B.W N) (mE E).im
    have hs1 : s N < 1 := lt_of_le_of_lt (hst N) (ht1 N)
    have h5 : (0:ℝ) ≤ Mi N + Mf N * (1 - s N) := by
      have := hMi N; have := hMf N; nlinarith
    have := hMm N
    unfold cFarStep'; nlinarith
  have hstep : HighProb B.P (fun N => {ω | ∀ p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N)),
      (if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
        then 0 else X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
        ≤ cFarStep' B E s Mi Mf Mm N *
          tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
            (zdist (B.L N) (p.2.1 - p.2.2))}) := by
    refine hHP.mono ?_
    filter_upwards [hfacts] with N hN ω hω p
    exact far_le_of_farInputs' X hE hs0 hst ht1 hN.1 hDD (hMi N) (hMn N) (hMf N) (hMm N)
      hN.2 hω p
  have hmain := Step1.stochDom_of_highProb (P := B.P) (fun N p ω => by
    have := hC0 N
    have hW0 : (0:ℝ) ≤ (B.W N : ℝ) := by positivity
    exact mul_nonneg this (tailT_nonneg hW0 _)) hstep
  refine hmain.trans (StochDom.of_unifDetDom ?_)
  intro τ hτ
  filter_upwards [hpoly τ hτ, hfacts] with N hp hN p
  have hW0 : (0:ℝ) < (B.W N : ℝ) := lt_of_lt_of_le (exp_pos 1) hN.1
  exact mul_le_mul_of_nonneg_right hp (tailT_nonneg hW0.le _)

/-- **(5.48) with the drift pinned.**  `RBM.Step45.FlowEq548` from the sharp (5.47) on the
near side and, on the far side, the four pinned one-step inputs — no free drift, no free
martingale, no `hfar`. -/
theorem flowEq548_of_farInputs' (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {Mi Mn Mf Mm : ℝ → ℕ → ℝ}
    (hMi : ∀ D' N, 0 ≤ Mi D' N) (hMn : ∀ D' N, 0 ≤ Mn D' N) (hMf : ∀ D' N, 0 ≤ Mf D' N)
    (hMm : ∀ D' N, 0 ≤ Mm D' N)
    (hpoly : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      cFarStep' B E s (Mi D') (Mf D') (Mm D') N ≤ (N : ℝ) ^ τ)
    (hHP : ∀ D' : ℝ, HighProb B.P
      (fun N => {ω | FarInputs' X E s t D' (Mi D') (Mn D') (Mf D') (Mm D') N ω}))
    (hres : ∀ D : ℝ, 0 < D → ∃ D' : ℝ, D ≤ D' ∧ ∀ᶠ N : ℕ in Filter.atTop,
      exp 1 ≤ (B.W N : ℝ) ∧ FarResidue' B E s t D D' (Mi D') (Mn D') (Mf D') N)
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2)))) :
    Step45.FlowEq548 X E s t := by
  refine Step2MomentStep.flowEq548_of_near_far X hnear fun D hD => ?_
  obtain ⟨D', hDD, hfacts⟩ := hres D hD
  exact stochDom_far_of_farInputs' X hE hs0 hst ht1 hDD (hMi D') (hMn D') (hMf D') (hMm D')
    hfacts (hpoly D') (hHP D')

/-- **T198's bundle, produced with the drift pinned.**  `RBM.Step2MomentStep.FarInputs` still
existentially quantifies `F`, `Fn`, `Mrt`; this supplies the witnesses from
`RBM.Step2FarInputs.farDrift`, `farDriftNear` and `farMart`, so that any consumer of the
T198 interface is, after this lemma, consuming a statement about the pinned objects.  The
extra hypothesis `hmartAll` is the price of T198's bundle asking the martingale bound at
*every* argument rather than only the far ones. -/
theorem farInputs_of_farInputs' {D' : ℝ} {Mi Mn Mf Mm Mm' : ℕ → ℝ} {N : ℕ} {ω : Ω}
    (hMf : 0 ≤ Mf N)
    (hin : FarInputs' X E s t D' Mi Mn Mf Mm N ω)
    (hmartAll : ∀ (v : TimeIcc s t N) (a : LoopArg (B.L N) 2),
      ‖farMart X E s N (v : ℝ) ω a‖
        ≤ Mm' N * Step2.tT B E N D' (v : ℝ) (zdist (B.L N) (a 0 - a 1))) :
    Step2MomentStep.FarInputs X E s t D' Mi Mn Mf Mm' N ω := by
  obtain ⟨hinit, hnear, hfarD, -⟩ := hin
  intro v
  have hW0 : (0:ℝ) ≤ (B.W N : ℝ) := by positivity
  have hFnb : ∀ u ∈ Set.Ico (s N) (v : ℝ), ∀ b : LoopArg (B.L N) 2,
      ‖farDriftNear X E N u ω b‖
        ≤ Mn N * (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
                  then 1 else 0) := by
    intro u hu b
    have hu' : u ∈ Set.Ico (s N) (t N) := ⟨hu.1, lt_of_lt_of_le hu.2 v.2.2⟩
    unfold farDriftNear
    split_ifs with hb
    · rw [mul_one]; exact hnear u hu' b hb
    · simp
  have hFrb : ∀ u ∈ Set.Ico (s N) (v : ℝ), ∀ b : LoopArg (B.L N) 2,
      ‖farDrift X E N u ω b - farDriftNear X E N u ω b‖
        ≤ Mf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := by
    intro u hu b
    have hu' : u ∈ Set.Ico (s N) (t N) := ⟨hu.1, lt_of_lt_of_le hu.2 v.2.2⟩
    unfold farDriftNear
    split_ifs with hb
    · rw [sub_self, norm_zero]
      have : (0:ℝ) ≤ Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := tailT_nonneg hW0 _
      positivity
    · rw [sub_zero]
      exact hfarD u hu' b hb
  exact ⟨fun u => farDrift X E N u ω, fun u => farDriftNear X E N u ω,
    farMart X E s N (v : ℝ) ω, fun a => farDrift_duhamel X N (v : ℝ) ω a, hinit, hFnb, hFrb,
    hmartAll v⟩

end Inputs

/-! ### 4. `cFarStep' ≺ 1`

`Ξ = RBM.Step2.xiK` is `N^{o(1)}` unconditionally on the band (`eventually_xiK_le`), so the
whole far-field constant is `≺ 1` as soon as the three one-step constants are: `M_i` from
(2.69), `M_f (1-s)` from (5.35) integrated over `[s,v]`, and `M_m` from (5.45). -/

section Poly

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `1 ≤ Ξ`: the stretched-exponential summand of `RBM.Step2.xiK` is already `≥ 1`. -/
theorem one_le_xiK {L : ℕ} {W m : ℝ} (hW : 1 ≤ W) : 1 ≤ Step2.xiK L W m := by
  have hlog : 0 ≤ log W := Real.log_nonneg hW
  have h34 : (0:ℝ) ≤ log W ^ (3 / 4 : ℝ) := Real.rpow_nonneg hlog _
  have he : (1:ℝ) ≤ exp (log W ^ (3 / 4 : ℝ)) := Real.one_le_exp h34
  have hct := cTail_nonneg
  have h1 : (0:ℝ) ≤ 1 + 2 * (L : ℝ) * exp (-(log W ^ (3 / 2 : ℝ) / 8)) := by positivity
  have h2 : (0:ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  unfold Step2.xiK
  nlinarith

/-- **`Ξ ≺ 1`.**  The kernel constant of (7.2),
`Ξ = C(1 + 2L e^{-(log W)^{3/2}/8}) + (Im m)^{-2} + e^{(log W)^{3/4}}`, is `N^{o(1)}`: the
middle term is a constant, the first is `≤ 2C` once `L ≤ W²` and `W ≥ e^{400}`, and the last
is `≤ W^{τ/2} ≤ N^{τ/2}`.  Nothing about the flow enters — only `W L ≤ N` and (2.2). -/
theorem eventually_xiK_le (B : Band Ω) (m : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, Step2.xiK (B.L N) (B.W N) m ≤ (N : ℝ) ^ τ := by
  have hτ2 : 0 < τ / 2 := by linarith
  filter_upwards [B.dim, Step2.eventually_le_W_sq B,
    (Step2.tendsto_W B).eventually_ge_atTop (exp 400),
    (Step2.tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 1 hτ2),
    eventually_le_rpow (2 * cTail + (m ^ 2)⁻¹) hτ2, eventually_le_rpow 2 hτ2,
    Filter.eventually_ge_atTop 1] with
    N hdim hW2 hWe hWexp hC hC2 hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
  have hL1 : (1 : ℝ) ≤ B.L N := by exact_mod_cast (by omega : 1 ≤ B.L N)
  have hLN : (B.L N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hWN : (B.W N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hLW : (B.L N : ℝ) ≤ (B.W N : ℝ) ^ 2 := hLN.trans hW2
  have hexpL : 2 * (B.L N : ℝ) * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8)) ≤ 1 := by
    have := Step2.two_mul_sq_mul_exp_le hWe
    have h0 := exp_pos (-(log (B.W N : ℝ) ^ (3 / 2 : ℝ) / 8))
    nlinarith
  have hct := cTail_nonneg
  have h1 : cTail * (1 + 2 * (B.L N : ℝ) * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8)))
      ≤ 2 * cTail := by nlinarith
  have h2 : exp (log (B.W N : ℝ) ^ (3 / 4 : ℝ)) ≤ (N : ℝ) ^ (τ / 2) := by
    have h := hWexp
    rw [one_mul] at h
    exact h.trans (Real.rpow_le_rpow hW0.le hWN hτ2.le)
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h3 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN hτ2.le
  have h4 : 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by nlinarith [hsplit, hC2, h3]
  unfold Step2.xiK
  linarith

/-- **`cFarStep' ≺ 1`.**  From `Ξ ≺ 1` and the three one-step constants being `≺ 1`. -/
theorem detDom_cFarStep' (B : Band Ω) (E : ℝ) {s : ℕ → ℝ} {Mi Mf Mm : ℕ → ℝ}
    (hs1 : ∀ N, s N ≤ 1) (hMi : ∀ N, 0 ≤ Mi N) (hMf : ∀ N, 0 ≤ Mf N)
    (hMi' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mi N ≤ (N : ℝ) ^ τ)
    (hMf' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mf N * (1 - s N) ≤ (N : ℝ) ^ τ)
    (hMm' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mm N ≤ (N : ℝ) ^ τ) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, cFarStep' B E s Mi Mf Mm N ≤ (N : ℝ) ^ τ := by
  intro τ hτ
  have hτ4 : 0 < τ / 4 := by linarith
  filter_upwards [eventually_xiK_le B (mE E).im hτ4, hMi' _ hτ4, hMf' _ hτ4, hMm' _ hτ4,
    eventually_le_rpow 2 hτ4, Filter.eventually_ge_atTop 1] with N hΞ hi hf hm h2 hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  set x : ℝ := (N : ℝ) ^ (τ / 4) with hxdef
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hN hτ4.le
  have hx4 : x ^ 4 = (N : ℝ) ^ τ := by
    rw [hxdef, Step2.natCast_rpow_pow]; norm_num
  have hΞ0 : (0:ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := Step2.xiK_nonneg _ _ _
  have hlen : (0:ℝ) ≤ 1 - s N := by linarith [hs1 N]
  have hfl : (0:ℝ) ≤ Mf N * (1 - s N) := mul_nonneg (hMf N) hlen
  have hkey : cFarStep' B E s Mi Mf Mm N ≤ 4 * x ^ 2 := by
    unfold cFarStep'
    have hsum : Mi N + Mf N * (1 - s N) ≤ 2 * x := by linarith
    have hmul : Step2.xiK (B.L N) (B.W N) (mE E).im * (Mi N + Mf N * (1 - s N)) ≤ x * (2 * x) :=
      mul_le_mul hΞ (hsum) (by linarith [hMi N]) (by linarith)
    nlinarith
  have h4x : (4:ℝ) ≤ x ^ 2 := by nlinarith
  calc cFarStep' B E s Mi Mf Mm N ≤ 4 * x ^ 2 := hkey
    _ ≤ x ^ 2 * x ^ 2 := by nlinarith [sq_nonneg x]
    _ = x ^ 4 := by ring
    _ = (N : ℝ) ^ τ := hx4

end Poly

/-! ### 4b. (5.48) end to end -/

section EndToEnd

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **(5.48) with nothing free in the hypothesis list.**  The far half is
`RBM.Step2FarInputs.FarInputs'` — four inequalities about `RBM.Step2.lk`,
`RBM.Step2FarInputs.farDrift` and `RBM.Step2FarInputs.farMart`, all three of which unfold to
the Green function of `H_u` — together with `M_i ≺ 1` ((2.69)), `M_f (1-s) ≺ 1` ((5.35)
integrated over `[s,v]`) and `M_m ≺ 1` ((5.45) in the far field).  `Ξ ≺ 1` is not a hypothesis
but a theorem (`RBM.Step2FarInputs.eventually_xiK_le`), so **`cFarStep' ≺ 1` is proved here,
not assumed**. -/
theorem flowEq548_of_farInputs'_detDom (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {Mi Mn Mf Mm : ℝ → ℕ → ℝ}
    (hMi : ∀ D' N, 0 ≤ Mi D' N) (hMn : ∀ D' N, 0 ≤ Mn D' N) (hMf : ∀ D' N, 0 ≤ Mf D' N)
    (hMm : ∀ D' N, 0 ≤ Mm D' N)
    (hMi' : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mi D' N ≤ (N : ℝ) ^ τ)
    (hMf' : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      Mf D' N * (1 - s N) ≤ (N : ℝ) ^ τ)
    (hMm' : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop, Mm D' N ≤ (N : ℝ) ^ τ)
    (hHP : ∀ D' : ℝ, HighProb B.P
      (fun N => {ω | FarInputs' X E s t D' (Mi D') (Mn D') (Mf D') (Mm D') N ω}))
    (hres : ∀ D : ℝ, 0 < D → ∃ D' : ℝ, D ≤ D' ∧ ∀ᶠ N : ℕ in Filter.atTop,
      exp 1 ≤ (B.W N : ℝ) ∧ FarResidue' B E s t D D' (Mi D') (Mn D') (Mf D') N)
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2)))) :
    Step45.FlowEq548 X E s t :=
  flowEq548_of_farInputs' X hE hs0 hst ht1 hMi hMn hMf hMm
    (fun D' => detDom_cFarStep' B E (fun N => le_of_lt (lt_of_le_of_lt (hst N) (ht1 N)))
      (hMi D') (hMf D') (hMi' D') (hMf' D') (hMm' D')) hHP hres hnear

end EndToEnd

/-! ### 5. The two drift inputs, produced from (5.35) and (5.34)

`farDrift` has exactly two summands (`farDrift_eq_eGpm_add_quadGlue`): T163's `E^{(G̃)}`, which
(5.35) bounds (`RBM.EGDef.eGpm_le_reduced`, shape 2), and the quadratic gluing term
`E^{((L-K)×(L-K))}` of (5.34)/(5.49).  So the two drift fields of `FarInputs'` are the sum of
the two bounds, near the diagonal and off it. -/

section Produce

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The one-step inputs from (2.69), (5.35), (5.34) and (5.45).**  There is nothing else in
the drift, so these are all the inputs there are. -/
theorem farInputs'_of_eG_of_quad {D' : ℝ} {Mi Mg Mq Mgf Mqf Mm : ℕ → ℝ} {N : ℕ} {ω : Ω}
    (hinit : ∀ b : LoopArg (B.L N) 2, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi N * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
    (heGnear : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖ ≤ Mg N)
    (hQnear : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            ⟨[true, false], [b 0, b 1]⟩‖ ≤ Mq N)
    (heGfar : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
          ≤ Mgf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hQfar : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            ⟨[true, false], [b 0, b 1]⟩‖
          ≤ Mqf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
    (hmart : ∀ v : TimeIcc s t N, ∀ x y : ZMod (B.L N),
      6 * ellStar (B.W N : ℝ) (B.ell N (v : ℝ)) ≤ (zdist (B.L N) (x - y) : ℝ) →
        ‖farMart X E s N (v : ℝ) ω ![x, y]‖
          ≤ Mm N * Step2.tT B E N D' (v : ℝ) (zdist (B.L N) (x - y))) :
    FarInputs' X E s t D' Mi (fun N => Mg N + Mq N) (fun N => Mgf N + Mqf N) Mm N ω := by
  refine ⟨hinit, ?_, ?_, hmart⟩
  · intro u hu b hb
    rw [farDrift_eq_eGpm_add_quadGlue]
    exact (norm_add_le _ _).trans (add_le_add (heGnear u hu b hb) (hQnear u hu b hb))
  · intro u hu b hb
    rw [farDrift_eq_eGpm_add_quadGlue]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add (heGfar u hu b hb) (hQfar u hu b hb)
    calc ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
          + ‖primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
              ⟨[true, false], [b 0, b 1]⟩‖
        ≤ Mgf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1))
          + Mqf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := this
      _ = (Mgf N + Mqf N) * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := by ring

end Produce

/-! ### 6. Satisfiability, and the sharpness of the correction to T198 -/

section Sat

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The anti-fiat certificate.**  In `RBM.Step2MomentStep.FarInputs` the two drift constants
can always be taken to be `0` — that is literally what
`RBM.Step2MomentStep.farInputs_of_remainder` does, for *every* sample, by choosing `F = 0`.
Here `M_n = M_f = 0` forces the model's own drift to vanish on `[s,t)`.  So the two drift
fields of `FarInputs'` are statements about `H_u`, not free parameters. -/
theorem farDrift_eq_zero_of_farInputs'_zero {D' : ℝ} {Mi Mm : ℕ → ℝ} {N : ℕ} {ω : Ω}
    (h : FarInputs' X E s t D' Mi (fun _ => 0) (fun _ => 0) Mm N ω)
    {u : ℝ} (hu : u ∈ Set.Ico (s N) (t N)) (b : LoopArg (B.L N) 2) :
    farDrift X E N u ω b = 0 := by
  obtain ⟨-, hnear, hfar, -⟩ := h
  by_cases hb : (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
  · have := hnear u hu b hb
    simpa using norm_le_zero_iff.1 (by simpa using this)
  · have := hfar u hu b hb
    rw [zero_mul] at this
    simpa using norm_le_zero_iff.1 this

/-- **Why the factor `1-s` is exactly the right normalization.**  (5.35), shape 2
(`RBM.EGDef.eGpm_le_reduced`), has the prefactor `η_u^{-1}(…)`; at `u = s` that is
`η_s^{-1}(…)`, and `η_s^{-1}(1-s) = (Im m_E)^{-1}`, a constant.  So `M_f (1-s) ≺ 1` is the
statement (5.35) supports, and `M_f ≺ 1` is not. -/
theorem etaT_inv_mul_one_sub {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) :
    (etaT E u)⁻¹ * (1 - u) = ((mE E).im)⁻¹ := by
  have hm := mE_im_pos hE
  have h1u : (0:ℝ) < 1 - u := by linarith
  rw [Step2.etaT_eq]
  field_simp

/-- **The critical scaling.**  `M_f = (1-s)^{-1}` — the size (5.35) really gives, since its
prefactor is `η_u^{-1}` and `η_s^{-1} = ((1-s) Im m)^{-1}` — together with `M_i = M_m = 1`
satisfies the hypotheses of `RBM.Step2FarInputs.detDom_cFarStep'`, so `cFarStep' ≺ 1`. -/
theorem cFarStep'_detDom_critical (B : Band Ω) (E : ℝ) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      cFarStep' B E (fun N => 1 - 1 / ((N : ℝ) + 1)) (fun _ => 1) (fun N => (N : ℝ) + 1)
          (fun _ => 1) N ≤ (N : ℝ) ^ τ := by
  refine detDom_cFarStep' B E (fun N => by
    have : (0:ℝ) < (N : ℝ) + 1 := by positivity
    have : (0:ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    linarith) (fun _ => zero_le_one) (fun N => by positivity) ?_ ?_ ?_
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN using hN
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN
    have hpos : (0:ℝ) < (N : ℝ) + 1 := by positivity
    have : ((N : ℝ) + 1) * (1 - (1 - 1 / ((N : ℝ) + 1))) = 1 := by field_simp; ring
    rw [this]; exact hN
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN using hN

/-- **And `RBM.Step2MomentStep.cFarStep` is *not* `≺ 1` on that same data.**  This is the
correction to T198, compiled: the far-field constant without the factor `1-s` is at least
`M_f = N + 1`, because `1 ≤ Ξ`.  The content of (5.48)'s far half is `cFarStep' ≺ 1`. -/
theorem cFarStep_not_detDom (B : Band Ω) (E : ℝ) :
    ¬ (∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
        Step2MomentStep.cFarStep B E (fun _ => 1) (fun N => (N : ℝ) + 1) (fun _ => 1) N
          ≤ (N : ℝ) ^ τ) := by
  intro h
  have h2 := h (1/2) (by norm_num)
  obtain ⟨N, hN, hN1⟩ := ((h2.and (Filter.eventually_ge_atTop 1)).exists)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hΞ : (1:ℝ) ≤ Step2.xiK (B.L N) (B.W N) (mE E).im := one_le_xiK hW1
  have hlow : (N : ℝ) + 2
      ≤ Step2MomentStep.cFarStep B E (fun _ => 1) (fun N => (N : ℝ) + 1) (fun _ => 1) N := by
    unfold Step2MomentStep.cFarStep
    nlinarith
  have hup : (N : ℝ) ^ ((1:ℝ)/2) ≤ (N : ℝ) := by
    calc (N : ℝ) ^ ((1:ℝ)/2) ≤ (N : ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hNr (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  linarith [hN, hlow, hup]

end Sat

end Step2FarInputs
end RBM

/-! ## T215: the far-field constant `M_gf` of (5.35), and its exponent account

`RBM.Step2FarInputs.farInputs'_of_eG_of_quad` (T208) reduced the two drift inputs of
`RBM.Step2FarInputs.FarInputs'` to bounds on the two summands of `RBM.Step2FarInputs.farDrift`:
`RBM.EGDef.eGpm`, governed by (5.35), and the quadratic gluing term of (5.34).  This part of
the file carries out the first half: it puts the right-hand side of (5.35), shape 2
(`RBM.EGDef.eGpm_le_reduced`), into the shape `M_gf · T_{u,D}` that `FarInputs'` asks for, and
checks the exponent budget of `M_gf (1-s) ≺ 1`.

The factor `1 - s` is not cosmetic: (5.35)'s prefactor carries `η_u^{-1}`, which is as large as
`η_t^{-1}`, i.e. `N^{1-τ}`, while `η_u^{-1}(1-s) = (Im m_E)^{-1}(η_s/η_u)` — a constant times
the window ratio `R_u` (`RBM.Step2FarInputs.etaT_inv_mul_one_sub_ratio`).  That one power of
`R_u`, together with the **two** powers of `T207`'s sharp (5.47) `J*_{u,D} ≺ (η_s/η_u)²`, is
the whole exponent account:

| term of (5.35) | coefficient | budget needed | `β*` |
| --- | --- | --- | --- |
| `c_far r^{3/2} A^{-1/2} J` | `β = r^{3/2}A^{-1/2}` | `β x⁸ R³ ≤ 1` | `7.5` |
| `169 r A^{-1} J^{3/2}` | `γ = r A^{-1}` | `γ x^{12} R⁴ ≤ 1` | `4.5` |

Both are strictly below (2.72)'s exponent `30`, so **(2.72) is not touched**; with the older
`J* ≺ (η_s/η_u)⁴` the same two rows would read `β x⁸ R⁵ ≤ 1` (`β* = 11.5`) and
`γ x^{12} R⁷ ≤ 1` (`β* = 7.5`) — still inside the budget, but the sharp (5.47) is what makes
the `γ` row *literally* `RBM.Step2MomentStep.hgamma_of_reg`, with no new arithmetic at all.

### Deviations from the paper

* **`T215a`** — (5.35)'s additive residue.  `RBM.EGDef.eGpm_le_reduced` ends in
  `+ r (ℓ_u η_u)^{-1} L ρ`, with `ρ` the (5.54) tail of the `3`-loop; the paper displays
  (5.35) purely as `(prefactor) · T_{u,D}`.  To reach the `M · T` shape that
  `RBM.Step2FarInputs.FarInputs'` asks for, this file assumes the residue is at most **one**
  unit of `W^{-D'} ≤ T_{u,D'}` (the hypothesis `hrem` of
  `RBM.Step2FarInputs.rhs535_far_le`), and the constant becomes `M_gf + 1`.  (5.54) makes `ρ`
  stretched-exponentially small, so this is free, but it is an added hypothesis and not a
  step the paper writes.
* **`T215b`** — the near-field constant.  `FarInputs'` asks for a **plain constant** on the
  diagonal band (T198's shape, not the paper's), so
  `RBM.Step2FarInputs.rhs535_le_const` evaluates the tail at its maximum
  `T_{u,D}(0) = A_u^{-2} + W^{-D} ≤ 2`, which needs `1 ≤ A_u` and `0 ≤ D'`.  The paper never
  states a near-field constant in this form.
-/

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 7. (5.35), shape 2, split into `M_gn` (near) and `M_gf` (far) -/

section Shape

/-- **`β = r^{3/2} A^{-1/2}`**, the leading far-field coefficient of (5.35), shape 2, with
`r = ℓ_u/ℓ_s` and `A = W ℓ_u η_u`.  Written exactly as it occurs in
`RBM.EGDef.eGpm_le_reduced` and in `RBM.Step2MomentStep.hbeta_of_reg`. -/
noncomputable def mgfBeta (Wr ℓu ℓs ηu : ℝ) : ℝ :=
  ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹

/-- **`γ = r A^{-1}`**, the subleading far-field coefficient of (5.35), shape 2. -/
noncomputable def mgfGamma (Wr ℓu ℓs ηu : ℝ) : ℝ := ℓu / ℓs * (Wr * ℓu * ηu)⁻¹

/-- **`M_gf`: the far-field constant of (5.35), shape 2** —
`η_u^{-1}(c_far β J + 169 γ J^{3/2})`.  It is exactly the prefactor of
`RBM.EGDef.eGpm_le_reduced` off the diagonal band, where the indicator vanishes. -/
noncomputable def mGF (Wr ℓu ℓs ηu J : ℝ) : ℝ :=
  ηu⁻¹ * (Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * J)
    + 169 * (mgfGamma Wr ℓu ℓs ηu * (J * √J)))

/-- **`M_gn`: the near-field constant of (5.35), shape 2** — `M_gf` plus the indicator term
`η_u^{-1} c_near r³` that (5.35) carries on the diagonal band `‖a₁-a₂‖ ≤ ℓ*_u`. -/
noncomputable def mGN (Wr ℓu ℓs ηu J : ℝ) : ℝ :=
  ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3) + mGF Wr ℓu ℓs ηu J

/-- **The right-hand side of (5.35), shape 2** — the conclusion of
`RBM.EGDef.eGpm_le_reduced`, as a function of the scales.  `Wr`, `Lr` are the real casts of
`W`, `L`, and `d` is `‖a₁ - a₂‖`. -/
noncomputable def rhs535 (Wr Lr ℓu ℓs ηu D J ρ d : ℝ) : ℝ :=
  ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * (if d ≤ ellStar Wr ℓu then 1 else 0)
      + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
      + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
    * tailT Wr ℓu ηu D d
  + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ

theorem mgfBeta_nonneg {Wr ℓu ℓs ηu : ℝ} (hr0 : 0 ≤ ℓu / ℓs) : 0 ≤ mgfBeta Wr ℓu ℓs ηu := by
  unfold mgfBeta; positivity

theorem mgfGamma_nonneg {Wr ℓu ℓs ηu : ℝ} (hr0 : 0 ≤ ℓu / ℓs) (hA0 : 0 ≤ Wr * ℓu * ηu) :
    0 ≤ mgfGamma Wr ℓu ℓs ηu := by
  unfold mgfGamma; positivity

theorem mGF_nonneg {Wr ℓu ℓs ηu J : ℝ} (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hr0 : 0 ≤ ℓu / ℓs) (hJ0 : 0 ≤ J) : 0 ≤ mGF Wr ℓu ℓs ηu J := by
  have hcF : 0 ≤ Lemma57.cFar Wr ℓu := Lemma57.cFar_nonneg hW hℓu
  have hA0 : (0:ℝ) ≤ Wr * ℓu * ηu := by positivity
  have hb := mgfBeta_nonneg (Wr := Wr) (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) hr0
  have hg := mgfGamma_nonneg (Wr := Wr) (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) hr0 hA0
  have hsJ : (0:ℝ) ≤ √J := Real.sqrt_nonneg _
  have hηi : (0:ℝ) ≤ ηu⁻¹ := by positivity
  unfold mGF
  have h1 : 0 ≤ Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * J) := by positivity
  have h2 : (0:ℝ) ≤ 169 * (mgfGamma Wr ℓu ℓs ηu * (J * √J)) := by positivity
  positivity

theorem mGN_nonneg {Wr ℓu ℓs ηu J : ℝ} (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hηu : 0 < ηu)
    (hr0 : 0 ≤ ℓu / ℓs) (hJ0 : 0 ≤ J) : 0 ≤ mGN Wr ℓu ℓs ηu J := by
  have hcN : 0 ≤ Lemma57.cNear Wr ℓu := Lemma57.cNear_nonneg hW hℓu
  have h1 : (0:ℝ) ≤ ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3) := by positivity
  have := mGF_nonneg (Wr := Wr) (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) (J := J) hW hℓu hηu hr0 hJ0
  unfold mGN
  linarith

/-- **(5.35) in the shape `FarInputs'` asks for, off the diagonal band.**  The indicator of
(5.35) vanishes there, and the residue `r (ℓ_u η_u)^{-1} L ρ` — the contribution of the (5.54)
tail `ρ` — is absorbed into one unit of `W^{-D} ≤ T_{u,D}`. -/
theorem rhs535_far_le {Wr Lr ℓu ℓs ηu D J ρ d : ℝ} (hfar : ¬ d ≤ ellStar Wr ℓu)
    (hrem : ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ ≤ Wr ^ (-D)) :
    rhs535 Wr Lr ℓu ℓs ηu D J ρ d ≤ (mGF Wr ℓu ℓs ηu J + 1) * tailT Wr ℓu ηu D d := by
  have h1 : Wr ^ (-D) ≤ tailT Wr ℓu ηu D d := rpow_neg_le_tailT d
  have hind : (if d ≤ ellStar Wr ℓu then (1:ℝ) else 0) = 0 := by simp [hfar]
  have hkey : ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * 0
      + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
      + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J))) * tailT Wr ℓu ηu D d
      = mGF Wr ℓu ℓs ηu J * tailT Wr ℓu ηu D d := by
    unfold mGF mgfBeta mgfGamma; ring
  rw [rhs535, hind, hkey,
    show (mGF Wr ℓu ℓs ηu J + 1) * tailT Wr ℓu ηu D d
      = mGF Wr ℓu ℓs ηu J * tailT Wr ℓu ηu D d + tailT Wr ℓu ηu D d from by ring]
  linarith

/-- **(5.35) as a plain constant, on the diagonal band.**  `FarInputs'` asks for a constant
there, so the tail is thrown away at its maximum `T_{u,D}(0) = A_u^{-2} + W^{-D}`. -/
theorem rhs535_le_const {Wr Lr ℓu ℓs ηu D J ρ d : ℝ} (hW : 1 ≤ Wr) (hℓu : 0 < ℓu)
    (hηu : 0 < ηu) (hr0 : 0 ≤ ℓu / ℓs) (hJ0 : 0 ≤ J) (hd : 0 ≤ d)
    (hrem : ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ ≤ Wr ^ (-D)) :
    rhs535 Wr Lr ℓu ℓs ηu D J ρ d
      ≤ (mGN Wr ℓu ℓs ηu J + 1) * (((Wr * ℓu * ηu) ^ 2)⁻¹ + Wr ^ (-D)) := by
  have hW0 : (0:ℝ) < Wr := by linarith
  have hcN : 0 ≤ Lemma57.cNear Wr ℓu := Lemma57.cNear_nonneg hW hℓu
  have hηi : (0:ℝ) ≤ ηu⁻¹ := by positivity
  have hWD : (0:ℝ) ≤ Wr ^ (-D) := Real.rpow_nonneg hW0.le _
  have hAi2 : (0:ℝ) ≤ ((Wr * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hT0 : tailT Wr ℓu ηu D 0 = ((Wr * ℓu * ηu) ^ 2)⁻¹ + Wr ^ (-D) := by
    rw [tailT]; simp
  have hTd : tailT Wr ℓu ηu D d ≤ ((Wr * ℓu * ηu) ^ 2)⁻¹ + Wr ^ (-D) := by
    rw [← hT0]; exact tailT_antitone hℓu hd
  have hTd0 : (0:ℝ) ≤ tailT Wr ℓu ηu D d := tailT_nonneg hW0.le _
  have hbr : ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * (if d ≤ ellStar Wr ℓu then 1 else 0)
      + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
      + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
      ≤ mGN Wr ℓu ℓs ηu J := by
    have hind : (if d ≤ ellStar Wr ℓu then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have hind0 : (0:ℝ) ≤ if d ≤ ellStar Wr ℓu then (1:ℝ) else 0 := by split_ifs <;> norm_num
    have hnn : (0:ℝ) ≤ Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 := by positivity
    have hmul : Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3
        * (if d ≤ ellStar Wr ℓu then (1:ℝ) else 0)
        ≤ Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 := by nlinarith
    have hrw : mGN Wr ℓu ℓs ηu J
        = ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3
          + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
          + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J))) := by
      unfold mGN mGF mgfBeta mgfGamma; ring
    rw [hrw]
    have := mul_le_mul_of_nonneg_left hmul hηi
    nlinarith
  have hbr0 : (0:ℝ) ≤ mGN Wr ℓu ℓs ηu J := mGN_nonneg hW hℓu hηu hr0 hJ0
  have hmul : ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3
      * (if d ≤ ellStar Wr ℓu then 1 else 0)
      + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
      + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J))) * tailT Wr ℓu ηu D d
      ≤ mGN Wr ℓu ℓs ηu J * (((Wr * ℓu * ηu) ^ 2)⁻¹ + Wr ^ (-D)) := by
    calc _ ≤ mGN Wr ℓu ℓs ηu J * tailT Wr ℓu ηu D d :=
          mul_le_mul_of_nonneg_right hbr hTd0
      _ ≤ mGN Wr ℓu ℓs ηu J * (((Wr * ℓu * ηu) ^ 2)⁻¹ + Wr ^ (-D)) :=
          mul_le_mul_of_nonneg_left hTd hbr0
  rw [rhs535]
  nlinarith [hmul, hrem, hWD, hAi2]

end Shape

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 7b. (5.35) itself, folded into `rhs535` -/

section Link

variable {L W : ℕ} [NeZero L] [NeZero W]
  {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- **(5.35), shape 2, with the right-hand side folded.**  `RBM.EGDef.eGpm_le_reduced`
verbatim, with its conclusion read through `RBM.Step2FarInputs.rhs535` and at
`d = ‖a₁ - a₂‖` (`RBM.zdist` is symmetric).  Nothing is assumed here that
`RBM.EGDef.eGpm_le_reduced` does not assume. -/
theorem eGpm_le_rhs535 {ℓu ℓs ηu D J : ℝ} (hM : M.IsHermitian) (hL : 3 ≤ L)
    (hW : 1 ≤ (W : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (W : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * Real.sqrt ((W : ℝ) ^ (-D)) ≤ ℓu * ((W : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((W : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (W : ℝ) ℓu < (zdist L (a₂ - b) : ℝ) →
      ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L W M z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (W : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ Real.sqrt J * Real.sqrt (tailT (W : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin W), p.1 = y →
      ∑ r : ZMod L × Fin W, Lemma57.blkW L W r x * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin W), r.1 = x →
      ∑ p : ZMod L × Fin W, Lemma57.blkW L W p y * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h560 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      Gm a₂ b * Gm a₁ b * Gm a₂ a₁)
    (m : Bool → ℂ)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M z σ
        - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)‖
      ≤ κ * ((W : ℝ) * ℓu * ηu)⁻¹)
    (hκ : 2 * κ ≤ ℓu / ℓs) :
    ‖EGDef.eGpm L W m M z a₁ a₂‖
      ≤ rhs535 (W : ℝ) (L : ℝ) ℓu ℓs ηu D J ρ (zdist L (a₁ - a₂)) := by
  rw [rhs535, Lemma57.zdist_sub_comm L a₁ a₂]
  exact EGDef.eGpm_le_reduced hM hL hW hℓu hℓs hηu hJ hA hr hD a₁ a₂ hρ hGm h273 h554 h531
    h42 h557C h557R h560 m hone hκ

end Link

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 8. The exponent account of `M_gf (1-s)` -/

section Account

/-- **`η_u^{-1}(1-s) = (Im m_E)^{-1}(η_s/η_u)`.**  The generalization of
`RBM.Step2FarInputs.etaT_inv_mul_one_sub` (which is the case `s = u`) that the far-field
account needs: the length of `[s,v]` cancels `η_u^{-1}` up to **one** power of the window
ratio `R_u = η_s/η_u`. -/
theorem etaT_inv_mul_one_sub_ratio {E : ℝ} (hE : |E| < 2) {s u : ℝ} (hu : u < 1) :
    (etaT E u)⁻¹ * (1 - s) = ((mE E).im)⁻¹ * (etaT E s / etaT E u) := by
  have hm := mE_im_pos hE
  have h1u : (0:ℝ) < 1 - u := by linarith
  rw [Step2.etaT_ratio hE s u, Step2.etaT_eq]
  field_simp

/-- **`β* = 7.5`.**  The leading far-field coefficient of (5.35), shape 2, is
`β = r^{3/2}A^{-1/2}`, and `M_gf(1-s) ≺ 1` needs `β x⁸ R³ ≤ 1` — one power of `R` from
`η_u^{-1}(1-s)`, two from the sharp (5.47) `J*_{u,D} ≺ R²` (T207).  Squaring, this is
`r³ x^{16} R⁶ ≤ A`; with `r⁶ ≤ R³` it follows from `A² ≥ x^{32} R^{15}`.

Compare `RBM.Step2MomentStep.hbeta_of_reg` (`β x⁸ R² ≤ 1`, `β* = 5.5`): the extra power of `R`
costs exactly `2` in `β*`, and `7.5 < 30`, so (2.72)'s exponent is untouched. -/
theorem hbeta_far_of_reg {x R r A : ℝ} (hR : 1 ≤ R) (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ R)
    (hA0 : 0 < A) (hA : x ^ 32 * R ^ 15 ≤ A ^ 2) :
    (r * √r * (√A)⁻¹) * (x ^ 8 * R ^ 3) ≤ 1 := by
  have hR0 : (0:ℝ) < R := by linarith
  have hsA : (0:ℝ) < √A := Real.sqrt_pos.2 hA0
  have hR3 : (0:ℝ) ≤ R ^ 3 := pow_nonneg hR0.le 3
  have hx8R3 : (0:ℝ) ≤ x ^ 8 * R ^ 3 := by
    have : (0:ℝ) ≤ x ^ 8 := by positivity
    exact mul_nonneg this hR3
  set β : ℝ := r * √r * (√A)⁻¹ with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hβsq : β ^ 2 = r ^ 3 * A⁻¹ := by
    rw [hβdef, mul_pow, mul_pow, Real.sq_sqrt hr0, ← Real.sqrt_inv,
      Real.sq_sqrt (by positivity)]
    ring
  have h6 : (r ^ 3) ^ 2 ≤ R ^ 3 := by
    calc (r ^ 3) ^ 2 = (r ^ 2) ^ 3 := by ring
      _ ≤ R ^ 3 := by gcongr
  have hkey : r ^ 3 * (x ^ 16 * R ^ 6) ≤ A := by
    have hR6 : (0:ℝ) ≤ R ^ 6 := pow_nonneg hR0.le 6
    have hlhs0 : (0:ℝ) ≤ r ^ 3 * (x ^ 16 * R ^ 6) := by
      have h1 : (0:ℝ) ≤ x ^ 16 := by positivity
      exact mul_nonneg (pow_nonneg hr0 3) (mul_nonneg h1 hR6)
    have hsqle : (r ^ 3 * (x ^ 16 * R ^ 6)) ^ 2 ≤ A ^ 2 := by
      have hR12 : (0:ℝ) ≤ R ^ 12 := pow_nonneg hR0.le 12
      have hx32 : (0:ℝ) ≤ x ^ 32 := by positivity
      calc (r ^ 3 * (x ^ 16 * R ^ 6)) ^ 2 = (r ^ 3) ^ 2 * (x ^ 32 * R ^ 12) := by ring
        _ ≤ R ^ 3 * (x ^ 32 * R ^ 12) := by
            exact mul_le_mul_of_nonneg_right h6 (mul_nonneg hx32 hR12)
        _ = x ^ 32 * R ^ 15 := by ring
        _ ≤ A ^ 2 := hA
    nlinarith [hA0.le, hlhs0]
  have hsq : (β * (x ^ 8 * R ^ 3)) ^ 2 ≤ 1 := by
    have heq : (β * (x ^ 8 * R ^ 3)) ^ 2 = (r ^ 3 * A⁻¹) * (x ^ 16 * R ^ 6) := by
      rw [mul_pow, hβsq]; ring
    rw [heq, mul_comm (r ^ 3) A⁻¹, mul_assoc, ← div_eq_inv_mul, div_le_one hA0]
    exact hkey
  nlinarith [mul_nonneg hβ0 hx8R3]

/-- **(2.72) with a gain, at every monomial `x^j R^k` with `j ≤ 32`, `k ≤ 60`.**

This is `RBM.Step2Near47.margin_of_reg`; `RBM1D/Hierarchy/Step2Near47.lean` is **not** in this
file's import chain (it sits on the `MomentDuhamelCut` branch), so the six-line argument is
repeated here rather than imported.  Nothing new is claimed. -/
theorem margin_pow_le {x R A N c δ : ℝ} (hN : 1 ≤ N) (hR : 1 ≤ R) (hδ0 : 0 ≤ δ)
    (hδ : 4 * δ ≤ 2 * c) (hx : x = N ^ (δ / 8)) (hA0 : 0 < A) (hA : N ^ c * R ^ 30 ≤ A)
    {j k : ℕ} (hj : j ≤ 32) (hk : k ≤ 60) : x ^ j * R ^ k ≤ A ^ 2 := by
  have hN0 : (0:ℝ) < N := by linarith
  have hR0 : (0:ℝ) < R := by linarith
  have hx1 : (1:ℝ) ≤ x := by rw [hx]; exact Real.one_le_rpow hN (by linarith)
  have h1 : x ^ j * R ^ k ≤ x ^ 32 * R ^ 60 :=
    mul_le_mul (pow_le_pow_right₀ hx1 hj) (pow_le_pow_right₀ hR hk)
      (pow_nonneg hR0.le k) (pow_nonneg (by linarith) 32)
  have hx32 : x ^ 32 = N ^ (4 * δ) := by
    rw [hx, ← Real.rpow_natCast (N ^ (δ / 8)) 32, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hNc2 : (N ^ c) ^ 2 = N ^ (2 * c) := by
    rw [← Real.rpow_natCast (N ^ c) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have h2c : N ^ (4 * δ) ≤ N ^ (2 * c) := Real.rpow_le_rpow_of_exponent_le hN hδ
  have hAsq : (N ^ c * R ^ 30) ^ 2 ≤ A ^ 2 := by
    have h0 : (0:ℝ) ≤ N ^ c * R ^ 30 := by positivity
    nlinarith
  refine h1.trans ?_
  have hR60 : (0:ℝ) ≤ R ^ 60 := pow_nonneg hR0.le 60
  calc x ^ 32 * R ^ 60 = N ^ (4 * δ) * R ^ 60 := by rw [hx32]
    _ ≤ N ^ (2 * c) * R ^ 60 := mul_le_mul_of_nonneg_right h2c hR60
    _ = (N ^ c * R ^ 30) ^ 2 := by rw [mul_pow, hNc2]; ring
    _ ≤ A ^ 2 := hAsq

/-- **The exponent account of `M_gf (1-s)`, at a fixed time.**

`M_gf · d = (η_u^{-1} d)(c_far β J + 169 γ J^{3/2})`, and with `η_u^{-1} d = m^{-1} R`
(`etaT_inv_mul_one_sub_ratio`) and `J ≤ x⁸ R²` (the sharp (5.47)) the two summands are
`c_far · β x⁸ R³` and `169 · γ x^{12} R⁴` — exactly the two side conditions. -/
theorem mGF_mul_le {Wr ℓu ℓs ηu J x R mm dd : ℝ} (hmm : 0 < mm) (hx : 1 ≤ x) (hR : 1 ≤ R)
    (hJ : J ≤ x ^ 8 * R ^ 2) (hcF : 0 ≤ Lemma57.cFar Wr ℓu)
    (hr0 : 0 ≤ ℓu / ℓs) (hA0 : 0 ≤ Wr * ℓu * ηu)
    (hd : ηu⁻¹ * dd = mm⁻¹ * R)
    (hbeta : mgfBeta Wr ℓu ℓs ηu * (x ^ 8 * R ^ 3) ≤ 1)
    (hgamma : mgfGamma Wr ℓu ℓs ηu * (x ^ 12 * R ^ 4) ≤ 1) :
    mGF Wr ℓu ℓs ηu J * dd ≤ mm⁻¹ * (Lemma57.cFar Wr ℓu + 169) := by
  have hb0 := mgfBeta_nonneg (Wr := Wr) (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) hr0
  have hg0 := mgfGamma_nonneg (Wr := Wr) (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) hr0 hA0
  have hx0 : (0:ℝ) < x := by linarith
  have hR0 : (0:ℝ) < R := by linarith
  have hsJ : √J ≤ x ^ 4 * R := by
    have h2 : (0:ℝ) ≤ x ^ 4 * R := by positivity
    have h1 : J ≤ (x ^ 4 * R) ^ 2 := by nlinarith
    calc √J ≤ √((x ^ 4 * R) ^ 2) := Real.sqrt_le_sqrt h1
      _ = x ^ 4 * R := Real.sqrt_sq h2
  have hsJ0 : (0:ℝ) ≤ √J := Real.sqrt_nonneg _
  have hJJ : J * √J ≤ x ^ 12 * R ^ 3 := by
    have h := mul_le_mul hJ hsJ hsJ0 (by positivity : (0:ℝ) ≤ x ^ 8 * R ^ 2)
    calc J * √J ≤ (x ^ 8 * R ^ 2) * (x ^ 4 * R) := h
      _ = x ^ 12 * R ^ 3 := by ring
  have hterm1 : mgfBeta Wr ℓu ℓs ηu * (R * J) ≤ 1 := by
    have hRJ : R * J ≤ x ^ 8 * R ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hJ hR0.le]
    nlinarith [mul_le_mul_of_nonneg_left hRJ hb0]
  have hterm2 : mgfGamma Wr ℓu ℓs ηu * (R * (J * √J)) ≤ 1 := by
    have hRJ : R * (J * √J) ≤ x ^ 12 * R ^ 4 := by
      nlinarith [mul_le_mul_of_nonneg_left hJJ hR0.le]
    nlinarith [mul_le_mul_of_nonneg_left hRJ hg0]
  have hexp : mGF Wr ℓu ℓs ηu J * dd
      = (ηu⁻¹ * dd) * (Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * J)
        + 169 * (mgfGamma Wr ℓu ℓs ηu * (J * √J))) := by unfold mGF; ring
  rw [hexp, hd,
    show mm⁻¹ * R * (Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * J)
        + 169 * (mgfGamma Wr ℓu ℓs ηu * (J * √J)))
      = mm⁻¹ * (Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * (R * J))
        + 169 * (mgfGamma Wr ℓu ℓs ηu * (R * (J * √J)))) from by ring]
  have hmm0 : (0:ℝ) ≤ mm⁻¹ := by positivity
  have h1 : Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * (R * J)) ≤ Lemma57.cFar Wr ℓu := by
    nlinarith
  have h2 : (169:ℝ) * (mgfGamma Wr ℓu ℓs ηu * (R * (J * √J))) ≤ 169 := by nlinarith
  exact mul_le_mul_of_nonneg_left (by linarith) hmm0

end Account

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 9. The account on the flow, and the `u`-free far-field constant -/

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **`M_gf(1-s) ≤ (Im m)^{-1}(c_far + 169)` at every `u ∈ [s,1)`.**

The two side conditions are discharged from (2.72) with a gain exactly as T132c's are
(`RBM.Step2MomentStep.side_conditions_of_reg`): `β* = 7.5` for the leading term
(`RBM.Step2FarInputs.hbeta_far_of_reg`) and `β* = 4.5` for the subleading one — the latter is
*literally* `RBM.Step2MomentStep.hgamma_of_reg`, unchanged.  The hypothesis `hJ` is the sharp
(5.47) of T207, `J*_{u,D} ≤ N^δ (η_s/η_u)²`. -/
theorem mGF_flow_mul_one_sub_le (hE : |E| < 2) {N : ℕ} {u : ℝ} (hs0 : 0 ≤ s N) (hsu : s N ≤ u)
    (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c) (hN1 : 1 ≤ (N : ℝ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u)
    {J : ℝ} (hJ : J ≤ (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 2) :
    mGF (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) J * (1 - s N)
      ≤ ((mE E).im)⁻¹ * (Lemma57.cFar (B.W N : ℝ) (B.ell N u) + 169) := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL hu1
  have hr0 : (0:ℝ) ≤ B.ell N u / B.ell N (s N) := by positivity
  have hr := Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hsu hu1
  have hm := mE_im_pos hE
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hR1 : (1:ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith), one_mul]; linarith
  have hA0 : 0 < B.scale E N u := B.scale_pos' hE N (hs0.trans hsu) hu1
  have hscale : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  have hx1 : (1:ℝ) ≤ (N : ℝ) ^ (δ / 8) := Real.one_le_rpow hN1 (by linarith)
  have hx8 : ((N : ℝ) ^ (δ / 8)) ^ 8 = (N : ℝ) ^ δ := by
    rw [Step2.natCast_rpow_pow]; norm_num
  have h15 := margin_pow_le (x := (N : ℝ) ^ (δ / 8)) (R := etaT E (s N) / etaT E u)
    (A := B.scale E N u) hN1 hR1 hδ0 hδ rfl hA0 hA (j := 32) (k := 15)
    (by norm_num) (by norm_num)
  have h9 := margin_pow_le (x := (N : ℝ) ^ (δ / 8)) (R := etaT E (s N) / etaT E u)
    (A := B.scale E N u) hN1 hR1 hδ0 hδ rfl hA0 hA (j := 24) (k := 9)
    (by norm_num) (by norm_num)
  have hbeta := hbeta_far_of_reg hR1 hr0 hr hA0 h15
  have hgamma := Step2MomentStep.hgamma_of_reg hx1 hR1 hr0 hr hA0 h9
  refine mGF_mul_le (x := (N : ℝ) ^ (δ / 8)) (R := etaT E (s N) / etaT E u) hm hx1 hR1 ?_
    (Lemma57.cFar_nonneg hW1 hℓu) hr0 ?_ (etaT_inv_mul_one_sub_ratio hE hu1) ?_ ?_
  · rw [hx8]; exact hJ
  · rw [← hscale]; exact hA0.le
  · unfold mgfBeta; rw [← hscale]; exact hbeta
  · unfold mgfGamma; rw [← hscale]; exact hgamma

/-- **`c_far(W,ℓ) ≤ c_far(W,1)` for `ℓ ≥ 1`.**  The only `ℓ`-dependence of
`RBM.Lemma57.cFar` is the summand `8/ℓ`, so the supremum over `u` is at `ℓ_u = 1`. -/
theorem cFar_le_cFar_one {Wr ℓu : ℝ} (hW : 1 ≤ Wr) (hℓu : 1 ≤ ℓu) :
    Lemma57.cFar Wr ℓu ≤ Lemma57.cFar Wr 1 := by
  have hlog : (0:ℝ) ≤ log Wr := Real.log_nonneg hW
  have hloss : (0:ℝ) < Lemma57.loss32 Wr := Lemma57.loss32_pos Wr
  have hℓ0 : (0:ℝ) < ℓu := by linarith
  have h8 : (8:ℝ) / ℓu ≤ 8 / 1 := by
    rw [div_one, div_le_iff₀ hℓ0]; nlinarith
  have h34 : (0:ℝ) ≤ 4 * log Wr ^ (3 / 2 : ℝ) := by positivity
  unfold Lemma57.cFar
  nlinarith

/-- **`c_near(W,ℓ) ≤ c_near(W,1)` for `ℓ ≥ 1`.**  As for `RBM.Lemma57.cFar`, the only
`ℓ`-dependence is the summand `2/ℓ`. -/
theorem cNear_le_cNear_one {Wr ℓu : ℝ} (hW : 1 ≤ Wr) (hℓu : 1 ≤ ℓu) :
    Lemma57.cNear Wr ℓu ≤ Lemma57.cNear Wr 1 := by
  have hlog : (0:ℝ) ≤ log Wr := Real.log_nonneg hW
  have hexp : (0:ℝ) < exp (log Wr ^ (3 / 4 : ℝ)) := exp_pos _
  have hℓ0 : (0:ℝ) < ℓu := by linarith
  have h2 : (2:ℝ) / ℓu ≤ 2 / 1 := by
    rw [div_one, div_le_iff₀ hℓ0]; nlinarith
  have h3 : (0:ℝ) ≤ 2 * log Wr ^ (3 : ℝ) := by positivity
  unfold Lemma57.cNear
  nlinarith

/-- **`c_far(W,1) ≺ 1`.**  `c_far(W,1) = (4(log W)^{3/2} + 8) e^{√(1/2)(log W)^{3/4}}`, and
`(log W)^{3/2} = ((log W)^{3/4})² ≤ e^{2(log W)^{3/4}}`, so the whole thing is at most
`12 e^{(2+√(1/2))(log W)^{3/4}} ≤ 12 W^{τ/2} ≤ N^τ`. -/
theorem eventually_cFar_one_le (B : Band Ω) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, Lemma57.cFar (B.W N : ℝ) 1 ≤ (N : ℝ) ^ τ := by
  have hτ2 : 0 < τ / 2 := by linarith
  filter_upwards [B.dim, (Step2.tendsto_W B).eventually_ge_atTop 1,
    (Step2.tendsto_W B).eventually (eventually_exp_mul_log_rpow_le (2 + √(1 / 2 : ℝ)) hτ2),
    eventually_le_rpow 12 hτ2, Filter.eventually_ge_atTop 1] with
    N hdim hW1 hWexp h12 hN1
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0:ℝ) < N := by linarith
  have hL1 : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
  have hL1' : (1:ℝ) ≤ (B.L N : ℝ) := by exact_mod_cast hL1
  have hW0 : (0:ℝ) < (B.W N : ℝ) := by linarith
  have hWN : (B.W N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hlogW : (0:ℝ) ≤ log (B.W N : ℝ) := Real.log_nonneg hW1
  set T : ℝ := log (B.W N : ℝ) ^ (3 / 4 : ℝ) with hTdef
  have hT0 : (0:ℝ) ≤ T := Real.rpow_nonneg hlogW _
  have hlog32 : log (B.W N : ℝ) ^ (3 / 2 : ℝ) = T ^ 2 := by
    rw [hTdef, ← Real.rpow_natCast (log (B.W N : ℝ) ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hlogW]
    norm_num
  have hte : T ≤ exp T := by linarith [Real.add_one_le_exp T]
  have hexp2 : exp T * exp T = exp (2 * T) := by rw [← Real.exp_add]; ring_nf
  have hT2 : T ^ 2 ≤ exp (2 * T) := by nlinarith [exp_pos T]
  have he1 : (1:ℝ) ≤ exp (2 * T) := Real.one_le_exp (by linarith)
  have hnum : 4 * log (B.W N : ℝ) ^ (3 / 2 : ℝ) + 8 / 1 ≤ 12 * exp (2 * T) := by
    rw [hlog32]; nlinarith
  have hloss : Lemma57.loss32 (B.W N : ℝ) = exp (√(1 / 2 : ℝ) * T) := rfl
  have hprod : exp (2 * T) * exp (√(1 / 2 : ℝ) * T) = exp ((2 + √(1 / 2 : ℝ)) * T) := by
    rw [← Real.exp_add]; ring_nf
  have hlossp : (0:ℝ) < exp (√(1 / 2 : ℝ) * T) := exp_pos _
  have hkey : Lemma57.cFar (B.W N : ℝ) 1 ≤ 12 * exp ((2 + √(1 / 2 : ℝ)) * T) := by
    unfold Lemma57.cFar
    rw [hloss, ← hprod]
    nlinarith
  have hWexp' : exp ((2 + √(1 / 2 : ℝ)) * T) ≤ (N : ℝ) ^ (τ / 2) := by
    refine hWexp.trans ?_
    exact Real.rpow_le_rpow hW0.le hWN hτ2.le
  have h3 : (1:ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN hτ2.le
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; ring_nf
  calc Lemma57.cFar (B.W N : ℝ) 1 ≤ 12 * exp ((2 + √(1 / 2 : ℝ)) * T) := hkey
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        exact mul_le_mul h12 hWexp' (exp_pos _).le (by linarith)
    _ = (N : ℝ) ^ τ := hsplit

/-- **The `u`-free far-field constant of (5.35)**: `(Im m_E)^{-1}(c_far(W,1) + 169)`.  By
`RBM.Step2FarInputs.mGF_flow_mul_one_sub_le` and `RBM.Step2FarInputs.cFar_le_cFar_one` it
dominates `M_gf(u)(1-s)` for **every** `u ∈ [s, 1)`, which is what `FarInputs'` needs. -/
noncomputable def mgfBar (B : Band Ω) (E : ℝ) (N : ℕ) : ℝ :=
  ((mE E).im)⁻¹ * (Lemma57.cFar (B.W N : ℝ) 1 + 169)

theorem mgfBar_pos (B : Band Ω) {E : ℝ} (hE : |E| < 2) (N : ℕ) : 0 < mgfBar B E N := by
  have hm := mE_im_pos hE
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have := Lemma57.cFar_nonneg hW1 (by norm_num : (0:ℝ) < 1)
  unfold mgfBar
  positivity

/-- **`M_gf(u)(1-s) ≤ mgfBar`, uniformly in `u ∈ [s,1)`.** -/
theorem mGF_flow_mul_one_sub_le_bar (hE : |E| < 2) {N : ℕ} {u : ℝ} (hs0 : 0 ≤ s N)
    (hsu : s N ≤ u) (hu1 : u < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    (hN1 : 1 ≤ (N : ℝ))
    (hA : (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u)
    {J : ℝ} (hJ : J ≤ (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 2) :
    mGF (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) J * (1 - s N) ≤ mgfBar B E N := by
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL (hs0.trans hsu) hu1
  have hm := mE_im_pos hE
  have hstep := mGF_flow_mul_one_sub_le (B := B) (s := s) hE hs0 hsu hu1 hδ0 hδ hN1 hA hJ
  have hc := cFar_le_cFar_one hW1 hℓu1
  have hmi : (0:ℝ) ≤ ((mE E).im)⁻¹ := by positivity
  unfold mgfBar
  nlinarith

/-- **`mgfBar ≺ 1`.** -/
theorem detDom_mgfBar (B : Band Ω) {E : ℝ} (hE : |E| < 2) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, mgfBar B E N ≤ (N : ℝ) ^ τ := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by linarith
  have hm := mE_im_pos hE
  filter_upwards [eventually_cFar_one_le B hτ2,
    eventually_le_rpow (((mE E).im)⁻¹ * 170) hτ2, Filter.eventually_ge_atTop 1] with
    N hcF hconst hN1
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hx1 : (1:ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN hτ2.le
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hcF0 := Lemma57.cFar_nonneg hW1 (by norm_num : (0:ℝ) < 1)
  have hmi : (0:ℝ) ≤ ((mE E).im)⁻¹ := by positivity
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < N)]; ring_nf
  have hle : mgfBar B E N ≤ (((mE E).im)⁻¹ * 170) * (N : ℝ) ^ (τ / 2) := by
    unfold mgfBar
    nlinarith
  calc mgfBar B E N ≤ (((mE E).im)⁻¹ * 170) * (N : ℝ) ^ (τ / 2) := hle
    _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
        exact mul_le_mul_of_nonneg_right hconst (by linarith)
    _ = (N : ℝ) ^ τ := hsplit

end Flow

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 10. The two drift constants of `FarInputs'`, produced from (5.35) -/

section Produce535

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **`M_f` for the `E^{(G̃)}` half of the drift.**  `M_gf(u) ≤ mgfBar/(1-s)` uniformly in
`u ∈ [s,t)` (`RBM.Step2FarInputs.mGF_flow_mul_one_sub_le_bar`), and the `+1` is the one unit of
`W^{-D}` that absorbs the (5.54) residue of (5.35). -/
noncomputable def mfEG (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (N : ℕ) : ℝ :=
  mgfBar B E N * (1 - s N)⁻¹ + 1

/-- **`M_n` for the `E^{(G̃)}` half of the drift.**  On the diagonal band `FarInputs'` asks for
a plain constant, so the tail is thrown away at its maximum
`T_{u,D'}(0) = A_u^{-2} + W^{-D'} ≤ 1 + W^{-D'}`.  `M_n` is *not* required to be `≺ 1`: it
enters only `RBM.Step2FarInputs.FarResidue'`, against `e^{-(5/4)(log W)^{3/2}}`. -/
noncomputable def mnEG (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (D' : ℝ) (N : ℕ) : ℝ :=
  (1 + (B.W N : ℝ) ^ (-D'))
    * (((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1 * (etaT E (s N) / etaT E (t N)) ^ 3
      + Lemma57.cFar (B.W N : ℝ) 1 + 169) * (1 - s N)⁻¹ + 1)

/-- **`M_f (1-s) ≺ 1` for the `E^{(G̃)}` half** — the conclusion T208 asked for. -/
theorem detDom_mfEG_mul_one_sub (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hs1 : ∀ N, s N < 1) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, mfEG B E s N * (1 - s N) ≤ (N : ℝ) ^ τ := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by linarith
  filter_upwards [detDom_mgfBar B hE (τ / 2) hτ2, eventually_le_rpow 2 hτ2,
    Filter.eventually_ge_atTop 1] with N hbar h2 hN1
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have h1s : (0:ℝ) < 1 - s N := by linarith [hs1 N]
  have h1s' : (1 - s N) ≤ 1 := by linarith [hs0 N]
  have hx1 : (1:ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN hτ2.le
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < N)]; ring_nf
  have heq : mfEG B E s N * (1 - s N) = mgfBar B E N + (1 - s N) := by
    unfold mfEG
    field_simp
  rw [heq]
  nlinarith

/-- **The far drift input of `FarInputs'`, for the `E^{(G̃)}` half**, from (5.35), shape 2, the
sharp (5.47) (`hJ`) and (2.72) with a gain (`hA`).  The constant is the `u`-free
`RBM.Step2FarInputs.mfEG`. -/
theorem eGfar_le_of_rhs535 (hE : |E| < 2) {N : ℕ} {ω : Ω} {D' c δ : ℝ}
    (hs0 : 0 ≤ s N) (hs1 : s N < 1) (hN1 : 1 ≤ (N : ℝ)) (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    {Jf ρf : ℝ → ℝ}
    (h535 : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
        ≤ rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) D'
            (Jf u) (ρf u) (zdist (B.L N) (b 0 - b 1)))
    (ht1 : t N < 1)
    (hA : ∀ u ∈ Set.Ico (s N) (t N),
      (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u)
    (hJ : ∀ u ∈ Set.Ico (s N) (t N), Jf u ≤ (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 2)
    (hrem : ∀ u ∈ Set.Ico (s N) (t N),
      B.ell N u / B.ell N (s N) * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρf u
        ≤ (B.W N : ℝ) ^ (-D')) :
    ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
          ≤ mfEG B E s N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)) := by
  intro u hu b hb
  have hu1 : u < 1 := hu.2.trans ht1
  have hW0 : (0:ℝ) < (B.W N : ℝ) := by
    have : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    linarith
  have h1s : (0:ℝ) < 1 - s N := by linarith
  have hT0 : (0:ℝ) ≤ tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D'
      (zdist (B.L N) (b 0 - b 1)) := tailT_nonneg hW0.le _
  have hstep := (h535 u hu b).trans (rhs535_far_le hb (hrem u hu))
  have hbar := mGF_flow_mul_one_sub_le_bar (B := B) (s := s) hE hs0 hu.1 hu1 hδ0 hδ hN1
    (hA u hu) (hJ u hu)
  have hmg : mGF (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u)
      ≤ mgfBar B E N * (1 - s N)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hbar (inv_nonneg.2 h1s.le)
    rwa [mul_assoc, mul_inv_cancel₀ h1s.ne', mul_one] at h
  have hle : mGF (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) + 1
      ≤ mfEG B E s N := by unfold mfEG; linarith
  refine hstep.trans ?_
  exact mul_le_mul_of_nonneg_right hle hT0

/-- **The near drift input of `FarInputs'`, for the `E^{(G̃)}` half.**  Same data; the
constant is the `u`-free `RBM.Step2FarInputs.mnEG`.  `M_n` is *not* required to be `≺ 1` —
it enters only `RBM.Step2FarInputs.FarResidue'`, against `e^{-(5/4)(log W)^{3/2}}`. -/
theorem eGnear_le_of_rhs535 (hE : |E| < 2) {N : ℕ} {ω : Ω} {D' c δ : ℝ}
    (hs0 : 0 ≤ s N) (hs1 : s N < 1) (ht1 : t N < 1) (hN1 : 1 ≤ (N : ℝ))
    (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    {Jf ρf : ℝ → ℝ}
    (h535 : ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
        ≤ rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) D'
            (Jf u) (ρf u) (zdist (B.L N) (b 0 - b 1)))
    (hscale1 : ∀ u ∈ Set.Ico (s N) (t N), 1 ≤ B.scale E N u)
    (hA : ∀ u ∈ Set.Ico (s N) (t N),
      (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u)
    (hJ0 : ∀ u ∈ Set.Ico (s N) (t N), 0 ≤ Jf u)
    (hJ : ∀ u ∈ Set.Ico (s N) (t N), Jf u ≤ (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 2)
    (hrem : ∀ u ∈ Set.Ico (s N) (t N),
      B.ell N u / B.ell N (s N) * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρf u
        ≤ (B.W N : ℝ) ^ (-D')) :
    ∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
          ≤ mnEG B E s t D' N := by
  intro u hu b _
  have hsu : s N ≤ u := hu.1
  have hut : u < t N := hu.2
  have hu1 : u < 1 := hut.trans ht1
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hW0 : (0:ℝ) < (B.W N : ℝ) := by linarith
  have h1s : (0:ℝ) < 1 - s N := by linarith
  have hℓs : 0 < B.ell N (s N) := Step3.ellHat_pos_of_lt_one hL hs1
  have hℓu : 0 < B.ell N u := Step3.ellHat_pos_of_lt_one hL hu1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg hL (hs0.trans hsu) hu1
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hm := mE_im_pos hE
  have hmi : (0:ℝ) ≤ ((mE E).im)⁻¹ := by positivity
  have hr0 : (0:ℝ) ≤ B.ell N u / B.ell N (s N) := by positivity
  have hscale : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  have hstep := (h535 u hu b).trans (rhs535_le_const (Lr := (B.L N : ℝ)) (ρ := ρf u)
    hW1 hℓu hηu hr0 (hJ0 u hu) (by positivity) (hrem u hu))
  -- `T_{u,D}(0) = A_u^{-2} + W^{-D} ≤ 2`
  have hA1 : (1:ℝ) ≤ (B.W N : ℝ) * B.ell N u * etaT E u := by
    rw [← hscale]; exact hscale1 u hu
  have hAi : (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith)
  have hWD0 : (0:ℝ) ≤ (B.W N : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  have hsum : (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ + (B.W N : ℝ) ^ (-D')
      ≤ 1 + (B.W N : ℝ) ^ (-D') := by linarith
  -- the window ratios
  have hR0 : (0:ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE]; positivity
  have hR1 : (1:ℝ) ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith), one_mul]; linarith
  have hRt : etaT E (s N) / etaT E u ≤ etaT E (s N) / etaT E (t N) := by
    rw [Step2.etaT_ratio hE, Step2.etaT_ratio hE]
    have h1t : (0:ℝ) < 1 - t N := by linarith
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith)
  have h3 : (etaT E (s N) / etaT E u) ^ 3 ≤ (etaT E (s N) / etaT E (t N)) ^ 3 :=
    pow_le_pow_left₀ hR0 hRt 3
  have hq := Step2MomentStep.hq_of_ratio hR1 hr0
    (Step2MomentStep.ratio_sq_le (B := B) (s := s) hE hsu hu1)
  have hcN := cNear_le_cNear_one hW1 hℓu1
  have hcN0 : (0:ℝ) ≤ Lemma57.cNear (B.W N : ℝ) 1 := Lemma57.cNear_nonneg hW1 (by norm_num)
  have hr3 : (0:ℝ) ≤ (B.ell N u / B.ell N (s N)) ^ 3 := by positivity
  have hbar := mGF_flow_mul_one_sub_le_bar (B := B) (s := s) hE hs0 hsu hu1 hδ0 hδ hN1
    (hA u hu) (hJ u hu)
  -- the near summand of `M_gn`, times `1 - s`
  have hnearterm : (etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u)
      * (B.ell N u / B.ell N (s N)) ^ 3) * (1 - s N)
      ≤ ((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1
        * (etaT E (s N) / etaT E (t N)) ^ 3) := by
    have hid := etaT_inv_mul_one_sub_ratio (E := E) (s := s N) hE hu1
    have hrw : (etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u)
        * (B.ell N u / B.ell N (s N)) ^ 3) * (1 - s N)
        = ((etaT E u)⁻¹ * (1 - s N)) * (Lemma57.cNear (B.W N : ℝ) (B.ell N u)
          * (B.ell N u / B.ell N (s N)) ^ 3) := by ring
    rw [hrw, hid, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hmi
    calc (etaT E (s N) / etaT E u) * (Lemma57.cNear (B.W N : ℝ) (B.ell N u)
          * (B.ell N u / B.ell N (s N)) ^ 3)
        ≤ (etaT E (s N) / etaT E u) * (Lemma57.cNear (B.W N : ℝ) 1
            * (etaT E (s N) / etaT E u) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hcN hq hr3 hcN0) hR0
      _ = Lemma57.cNear (B.W N : ℝ) 1 * (etaT E (s N) / etaT E u) ^ 3 := by ring
      _ ≤ Lemma57.cNear (B.W N : ℝ) 1 * (etaT E (s N) / etaT E (t N)) ^ 3 :=
          mul_le_mul_of_nonneg_left h3 hcN0
  -- `M_gn(u)(1-s) ≤ C`
  have hgn : mGN (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) * (1 - s N)
      ≤ ((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1 * (etaT E (s N) / etaT E (t N)) ^ 3
        + Lemma57.cFar (B.W N : ℝ) 1 + 169) := by
    have hexp : mGN (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) * (1 - s N)
        = (etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u)
            * (B.ell N u / B.ell N (s N)) ^ 3) * (1 - s N)
          + mGF (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) * (1 - s N) := by
      unfold mGN; ring
    have hbar' : mGF (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) * (1 - s N)
        ≤ ((mE E).im)⁻¹ * (Lemma57.cFar (B.W N : ℝ) 1 + 169) := hbar
    have hring : ((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1
          * (etaT E (s N) / etaT E (t N)) ^ 3)
        + ((mE E).im)⁻¹ * (Lemma57.cFar (B.W N : ℝ) 1 + 169)
        = ((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1
          * (etaT E (s N) / etaT E (t N)) ^ 3 + Lemma57.cFar (B.W N : ℝ) 1 + 169) := by ring
    rw [hexp, ← hring]
    linarith
  have hgn' : mGN (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u)
      ≤ ((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1 * (etaT E (s N) / etaT E (t N)) ^ 3
        + Lemma57.cFar (B.W N : ℝ) 1 + 169) * (1 - s N)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hgn (inv_nonneg.2 h1s.le)
    rwa [mul_assoc, mul_inv_cancel₀ h1s.ne', mul_one] at h
  have hgn0 : (0:ℝ) ≤ mGN (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) :=
    mGN_nonneg hW1 hℓu hηu hr0 (hJ0 u hu)
  refine hstep.trans ?_
  unfold mnEG
  calc (mGN (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) + 1)
        * ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ + (B.W N : ℝ) ^ (-D'))
      ≤ (mGN (B.W N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) (Jf u) + 1)
          * (1 + (B.W N : ℝ) ^ (-D')) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ (((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1
          * (etaT E (s N) / etaT E (t N)) ^ 3 + Lemma57.cFar (B.W N : ℝ) 1 + 169)
          * (1 - s N)⁻¹ + 1) * (1 + (B.W N : ℝ) ^ (-D')) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ = (1 + (B.W N : ℝ) ^ (-D')) * (((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1
          * (etaT E (s N) / etaT E (t N)) ^ 3 + Lemma57.cFar (B.W N : ℝ) 1 + 169)
          * (1 - s N)⁻¹ + 1) := by ring

end Produce535

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 11. `FarInputs'` with the `E^{(G̃)}` half of the drift produced -/

section Assemble

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **The per-sample data of (5.35), (5.34) and (5.45) at `(N, ω)`.**

`Jf` and `ρf` are *given* functions, not existentials: the caller instantiates `Jf` by
`RBM.Step2.jS` (5.29) and `ρf` by the (5.54) tail, so nothing about the model can be chosen
after the fact.  The left-hand sides are `RBM.EGDef.eGpm`, `RBM.primBil` of `L - K` and
`RBM.Step2FarInputs.farMart` — all three definitions in the Green function of `H_u`. -/
def EGData (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (D' δ : ℝ) (Mi Mq Mqf Mm : ℕ → ℝ)
    (Jf ρf : ℕ → Ω → ℝ → ℝ) (N : ℕ) (ω : Ω) : Prop :=
  (∀ b : LoopArg (B.L N) 2, ‖Step2.lk X E N (s N) ω b‖
      ≤ Mi N * Step2.tT B E N D' (s N) (zdist (B.L N) (b 0 - b 1)))
  ∧ (∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) (b 0) (b 1)‖
        ≤ rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (B.ell N (s N)) (etaT E u) D'
            (Jf N ω u) (ρf N ω u) (zdist (B.L N) (b 0 - b 1)))
  ∧ (∀ u ∈ Set.Ico (s N) (t N), 0 ≤ Jf N ω u)
  ∧ (∀ u ∈ Set.Ico (s N) (t N), Jf N ω u ≤ (N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 2)
  ∧ (∀ u ∈ Set.Ico (s N) (t N),
      B.ell N u / B.ell N (s N) * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρf N ω u
        ≤ (B.W N : ℝ) ^ (-D'))
  ∧ (∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) →
        ‖primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            ⟨[true, false], [b 0, b 1]⟩‖ ≤ Mq N)
  ∧ (∀ u ∈ Set.Ico (s N) (t N), ∀ b : LoopArg (B.L N) 2,
      ¬ ((zdist (B.L N) (b 0 - b 1) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)) →
        ‖primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
            ⟨[true, false], [b 0, b 1]⟩‖
          ≤ Mqf N * Step2.tT B E N D' u (zdist (B.L N) (b 0 - b 1)))
  ∧ (∀ v : TimeIcc s t N, ∀ x y : ZMod (B.L N),
      6 * ellStar (B.W N : ℝ) (B.ell N (v : ℝ)) ≤ (zdist (B.L N) (x - y) : ℝ) →
        ‖farMart X E s N (v : ℝ) ω ![x, y]‖
          ≤ Mm N * Step2.tT B E N D' (v : ℝ) (zdist (B.L N) (x - y)))

/-- **The two drift inputs of `FarInputs'` are now theorems.**  Compare
`RBM.Step2FarInputs.farInputs'_of_eG_of_quad`, whose `heGnear`/`heGfar` were *hypotheses* with
unexplained constants: here they are produced from (5.35), shape 2, with the explicit constants
`RBM.Step2FarInputs.mnEG` and `RBM.Step2FarInputs.mfEG`. -/
theorem farInputs'_of_egData (hE : |E| < 2) {N : ℕ} {ω : Ω} {D' c δ : ℝ}
    {Mi Mq Mqf Mm : ℕ → ℝ} {Jf ρf : ℕ → Ω → ℝ → ℝ}
    (hs0 : 0 ≤ s N) (hs1 : s N < 1) (ht1 : t N < 1) (hN1 : 1 ≤ (N : ℝ))
    (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    (hscale1 : ∀ u ∈ Set.Ico (s N) (t N), 1 ≤ B.scale E N u)
    (hA : ∀ u ∈ Set.Ico (s N) (t N),
      (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u)
    (h : EGData X E s t D' δ Mi Mq Mqf Mm Jf ρf N ω) :
    FarInputs' X E s t D' Mi (fun N => mnEG B E s t D' N + Mq N)
      (fun N => mfEG B E s N + Mqf N) Mm N ω := by
  obtain ⟨hinit, h535, hJ0, hJ, hrem, hQnear, hQfar, hmart⟩ := h
  exact farInputs'_of_eG_of_quad X hinit
    (eGnear_le_of_rhs535 X hE hs0 hs1 ht1 hN1 hδ0 hδ h535 hscale1 hA hJ0 hJ hrem)
    hQnear
    (eGfar_le_of_rhs535 X hE hs0 hs1 hN1 hδ0 hδ h535 ht1 hA hJ hrem)
    hQfar hmart

/-- **The same, at the level of `HighProb`.** -/
theorem highProb_farInputs'_of_egData (hE : |E| < 2) {D' c δ : ℝ}
    {Mi Mq Mqf Mm : ℕ → ℝ} {Jf ρf : ℕ → Ω → ℝ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hs1 : ∀ N, s N < 1) (ht1 : ∀ N, t N < 1)
    (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    (hdet : ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ)
      ∧ (∀ u ∈ Set.Ico (s N) (t N), 1 ≤ B.scale E N u)
      ∧ (∀ u ∈ Set.Ico (s N) (t N),
          (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u))
    (hHP : HighProb B.P (fun N => {ω | EGData X E s t D' δ Mi Mq Mqf Mm Jf ρf N ω})) :
    HighProb B.P (fun N => {ω | FarInputs' X E s t D' Mi (fun N => mnEG B E s t D' N + Mq N)
      (fun N => mfEG B E s N + Mqf N) Mm N ω}) := by
  refine hHP.mono ?_
  filter_upwards [hdet] with N hN ω hω
  exact farInputs'_of_egData X hE (hs0 N) (hs1 N) (ht1 N) hN.1 hδ0 hδ hN.2.1 hN.2.2 hω

/-- **`M_f (1-s) ≺ 1` for the produced far constant**, given the (5.34) half.  The `E^{(G̃)}`
half is `RBM.Step2FarInputs.detDom_mfEG_mul_one_sub`, a theorem; only the quadratic gluing
term's constant is still an input. -/
theorem detDom_mf_mul_one_sub (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hs1 : ∀ N, s N < 1) {Mqf : ℕ → ℝ}
    (hq : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Mqf N * (1 - s N) ≤ (N : ℝ) ^ τ) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (mfEG B E s N + Mqf N) * (1 - s N) ≤ (N : ℝ) ^ τ := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := by linarith
  filter_upwards [detDom_mfEG_mul_one_sub B hE hs0 hs1 (τ / 2) hτ2, hq (τ / 2) hτ2,
    eventually_le_rpow 2 hτ2, Filter.eventually_ge_atTop 1] with N h1 h2 h3 hN1
  have hN : (1:ℝ) ≤ N := by exact_mod_cast hN1
  have hx1 : (1:ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN hτ2.le
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < N)]; ring_nf
  have hexp : (mfEG B E s N + Mqf N) * (1 - s N)
      = mfEG B E s N * (1 - s N) + Mqf N * (1 - s N) := by ring
  rw [hexp]
  nlinarith

end Assemble

/-! ### 12. The produced constants are non-degenerate -/

section NonDegenerate

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **`1 ≤ M_f`.**  `RBM.Step2FarInputs.farDrift_eq_zero_of_farInputs'_zero` says that
`M_n = M_f = 0` forces the model's own drift to vanish; what (5.35) actually produces is at
least `1`, so the witnesses below are **not** the fiat witness of T198
(`RBM.Step2MomentStep.farInputs_of_remainder`, which takes `F = 0`). -/
theorem one_le_mfEG (B : Band Ω) {E : ℝ} (hE : |E| < 2) (s : ℕ → ℝ) {N : ℕ}
    (hs1 : s N < 1) : 1 ≤ mfEG B E s N := by
  have h1s : (0:ℝ) < 1 - s N := by linarith
  have hbar := (mgfBar_pos B hE N).le
  have : (0:ℝ) ≤ mgfBar B E N * (1 - s N)⁻¹ := by positivity
  unfold mfEG; linarith

/-- **`1 ≤ M_n`.** -/
theorem one_le_mnEG (B : Band Ω) {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (D' : ℝ) {N : ℕ}
    (hs1 : s N < 1) (ht1 : t N < 1) : 1 ≤ mnEG B E s t D' N := by
  have h1s : (0:ℝ) < 1 - s N := by linarith
  have hm := mE_im_pos hE
  have hW1 : (1:ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hcN := Lemma57.cNear_nonneg hW1 (by norm_num : (0:ℝ) < 1)
  have hcF := Lemma57.cFar_nonneg hW1 (by norm_num : (0:ℝ) < 1)
  have hR0 : (0:ℝ) ≤ etaT E (s N) / etaT E (t N) := by
    rw [Step2.etaT_ratio hE]; positivity
  have hR3 : (0:ℝ) ≤ (etaT E (s N) / etaT E (t N)) ^ 3 := by positivity
  have hmi : (0:ℝ) ≤ ((mE E).im)⁻¹ := by positivity
  have hinv : (0:ℝ) ≤ (1 - s N)⁻¹ := by positivity
  have hterm : (0:ℝ) ≤ ((mE E).im)⁻¹ * (Lemma57.cNear (B.W N : ℝ) 1
      * (etaT E (s N) / etaT E (t N)) ^ 3 + Lemma57.cFar (B.W N : ℝ) 1 + 169)
      * (1 - s N)⁻¹ := by positivity
  have hW0 : (0:ℝ) < (B.W N : ℝ) := by linarith
  have hWD0 : (0:ℝ) ≤ (B.W N : ℝ) ^ (-D') := Real.rpow_nonneg hW0.le _
  unfold mnEG; nlinarith

/-- **The satisfiability witness, at the critical scaling, with the produced far constant.**

`1 - s_N = 1/(N+1)` — the regime `η_s^{-1} ≍ N`, where T198's `RBM.Step2MomentStep.cFarStep`
is *not* `≺ 1` (`RBM.Step2FarInputs.cFarStep_not_detDom`) — and `M_f` is the constant (5.35)
really produces, `RBM.Step2FarInputs.mfEG`, which is `≥ 1` by
`RBM.Step2FarInputs.one_le_mfEG`: the drift is **not** taken to be `0`. -/
theorem cFarStep'_detDom_mfEG (B : Band Ω) {E : ℝ} (hE : |E| < 2) :
    ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      cFarStep' B E (fun N => 1 - 1 / ((N : ℝ) + 1)) (fun _ => 1)
          (mfEG B E (fun N => 1 - 1 / ((N : ℝ) + 1))) (fun _ => 1) N ≤ (N : ℝ) ^ τ := by
  set s : ℕ → ℝ := fun N => 1 - 1 / ((N : ℝ) + 1) with hs
  have hpos : ∀ N : ℕ, (0:ℝ) < (N : ℝ) + 1 := fun N => by positivity
  have hs0 : ∀ N, 0 ≤ s N := by
    intro N
    have h1 : (1:ℝ) / ((N : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (hpos N)]
      have : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    rw [hs]; simp only []; linarith
  have hs1 : ∀ N, s N < 1 := by
    intro N
    have : (0:ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    rw [hs]; simp only []; linarith
  refine detDom_cFarStep' B E (fun N => (hs1 N).le) (fun _ => zero_le_one)
    (fun N => le_trans zero_le_one (one_le_mfEG B hE s (hs1 N))) ?_ ?_ ?_
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN using hN
  · exact detDom_mfEG_mul_one_sub B hE hs0 hs1
  · intro τ hτ
    filter_upwards [eventually_le_rpow 1 hτ] with N hN using hN

end NonDegenerate

/-! ### 13. (5.48) end to end, with the `E^{(G̃)}` half of the drift produced -/

section EndToEnd535

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **(5.48) with the drift's `E^{(G̃)}` half produced from (5.35).**

`RBM.Step2FarInputs.flowEq548_of_farInputs'_detDom` with its `FarInputs'` slot filled by
`RBM.Step2FarInputs.highProb_farInputs'_of_egData` and its `M_f (1-s) ≺ 1` slot by
`RBM.Step2FarInputs.detDom_mf_mul_one_sub`.  What is left of the far-field drift is exactly
the **quadratic gluing term** of (5.34) — the constants `Mq`, `Mqf` — and the martingale
`Mm` of (5.45); the `E^{(G̃)}` half of (5.35) is no longer a hypothesis. -/
theorem flowEq548_of_egData (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 4 * δ ≤ 2 * c)
    {Mi Mq Mqf Mm : ℝ → ℕ → ℝ} {Jf ρf : ℝ → ℕ → Ω → ℝ → ℝ}
    (hMi : ∀ D' N, 0 ≤ Mi D' N) (hMq : ∀ D' N, 0 ≤ Mq D' N) (hMqf : ∀ D' N, 0 ≤ Mqf D' N)
    (hMm : ∀ D' N, 0 ≤ Mm D' N)
    (hMi' : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Mi D' N ≤ (N : ℝ) ^ τ)
    (hMqf' : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Mqf D' N * (1 - s N) ≤ (N : ℝ) ^ τ)
    (hMm' : ∀ D' : ℝ, ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, Mm D' N ≤ (N : ℝ) ^ τ)
    (hdet : ∀ᶠ N : ℕ in atTop, 1 ≤ (N : ℝ)
      ∧ (∀ u ∈ Set.Ico (s N) (t N), 1 ≤ B.scale E N u)
      ∧ (∀ u ∈ Set.Ico (s N) (t N),
          (N : ℝ) ^ c * (etaT E (s N) / etaT E u) ^ 30 ≤ B.scale E N u))
    (hHP : ∀ D' : ℝ, HighProb B.P (fun N => {ω |
      EGData X E s t D' δ (Mi D') (Mq D') (Mqf D') (Mm D') (Jf D') (ρf D') N ω}))
    (hres : ∀ D : ℝ, 0 < D → ∃ D' : ℝ, D ≤ D' ∧ ∀ᶠ N : ℕ in atTop,
      exp 1 ≤ (B.W N : ℝ) ∧ FarResidue' B E s t D D' (Mi D')
        (fun N => mnEG B E s t D' N + Mq D' N) (fun N => mfEG B E s N + Mqf D' N) N)
    (hnear : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 2 *
        tailT (B.W N : ℝ) (B.ell N p.1) (etaT E p.1) D
          (zdist (B.L N) (p.2.1 - p.2.2)))) :
    Step45.FlowEq548 X E s t := by
  have hs1 : ∀ N, s N < 1 := fun N => lt_of_le_of_lt (hst N) (ht1 N)
  refine flowEq548_of_farInputs'_detDom X hE hs0 hst ht1
    (Mn := fun D' N => mnEG B E s t D' N + Mq D' N)
    (Mf := fun D' N => mfEG B E s N + Mqf D' N)
    hMi (fun D' N => ?_) (fun D' N => ?_) hMm hMi' (fun D' => ?_) hMm'
    (fun D' => highProb_farInputs'_of_egData X hE hs0 hs1 ht1 hδ0 hδ hdet (hHP D'))
    hres hnear
  · have := one_le_mnEG B hE s t D' (hs1 N) (ht1 N)
    have := hMq D' N
    linarith
  · have := one_le_mfEG B hE s (hs1 N)
    have := hMqf D' N
    linarith
  · exact detDom_mf_mul_one_sub B hE hs0 hs1 (hMqf' D')

end EndToEnd535

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 14. The constants are not vacuously zero -/

section NonVacuous

/-- **`M_gf > 0` whenever `J > 0`.**  (5.35)'s far-field constant is a genuine positive
quantity — the `169 r A^{-1} J^{3/2}` term alone is positive — so
`RBM.Step2FarInputs.mGF_mul_le` and the bound it feeds are not statements about `0`. -/
theorem mGF_pos {Wr ℓu ℓs ηu J : ℝ} (hW : 1 ≤ Wr) (hℓs : 0 < ℓs) (hℓu : 0 < ℓu)
    (hηu : 0 < ηu) (hJ : 0 < J) : 0 < mGF Wr ℓu ℓs ηu J := by
  have hW0 : (0:ℝ) < Wr := by linarith
  have hr0 : (0:ℝ) < ℓu / ℓs := by positivity
  have hcF : 0 ≤ Lemma57.cFar Wr ℓu := Lemma57.cFar_nonneg hW hℓu
  have hb0 := mgfBeta_nonneg (Wr := Wr) (ℓu := ℓu) (ℓs := ℓs) (ηu := ηu) hr0.le
  have hsJ : (0:ℝ) < √J := Real.sqrt_pos.2 hJ
  have hg0 : 0 < mgfGamma Wr ℓu ℓs ηu := by
    unfold mgfGamma; positivity
  have h1 : (0:ℝ) ≤ Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * J) := by positivity
  have h2 : (0:ℝ) < 169 * (mgfGamma Wr ℓu ℓs ηu * (J * √J)) := by positivity
  have hηi : (0:ℝ) < ηu⁻¹ := by positivity
  unfold mGF
  have : (0:ℝ) < Lemma57.cFar Wr ℓu * (mgfBeta Wr ℓu ℓs ηu * J)
      + 169 * (mgfGamma Wr ℓu ℓs ηu * (J * √J)) := by linarith
  positivity

end NonVacuous

end Step2FarInputs
end RBM
