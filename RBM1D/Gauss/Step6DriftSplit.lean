/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6HierarchyGauss
import RBM1D.Hierarchy.DriftBound

/-!
# T182: the size obligations of Step 6's pinned drift

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8: (5.129)–(5.133) and the fast decay of p. 73, for the drift tensor that
`RBM1D/Gauss/Step6HierarchyGauss.lean` (T173) pinned.

T173 left `RBM.sharpExpect_step6_driftE` with three obligations that are still statements
*about the drift*: `hH`, `hFD` and `h5133`.  This file discharges all three, for the paper's
**two** tensors rather than T173's single one.

## Why the split is necessary and not cosmetic

T152's `RBM.Step6.sharpExpect_step6_single` collapses the paper's `E E^{((L-K)×(L-K))}` and
`E E^{(G)}` into one tensor, on the ground that `RBM.Step6.driftBound_of_5133` and
`RBM.Step6.driftBound_of_5134` produce the *same* bound `η_v^{-1}(W ℓ_v η_v)^{-3}`.  That is
true of the bounds but not of their proofs, and (5.133) cannot be reached through the single
tensor:

* the quadratic half obeys (5.133) **pathwise**.  At loop length `2` the `Ξ`-factor of the
  second line of (5.77) is `Φ = Ξ^{(L-K)}_{u,2} Ξ^{(L-K)}_{u,2} A^{-1}`, whose `A^{-1}` is
  exactly the extra power (5.133) needs beyond `A^{-2}`.  This is `RBM.norm_primBil_lkPath_le`.
* the `E^{(G)}` half does **not**.  The third line of (5.77) gives
  `Ξ^{(L-K)}_{u,1} Ξ^{(L)}_{u,3} · η_u^{-1} A^{-2}`, which is one factor `A = W ℓ_u η_u`
  weaker than (5.133)'s `η_u^{-1} A^{-3}`, and the factor is *not* recoverable pathwise: it is
  the cancellation inside the expectation `E[⟨(G-m)E_{a₁}⟩ L_3]` that produces it, i.e. the
  paper's (5.134)/(5.135) route, which needs `RBM.Step6.quad13 ≺ A^{-4}`.

So the two halves need different arguments, and `RBM.Step6.sharpExpect_step6` — which already
asks for (5.134) as `hG` — is the right consumer.  Consequently the size hypothesis that
remains after this file is `hG` on `RBM.driftEG`, and it is one Step 6 always had.

## Main results

* `RBM.driftELK`, `RBM.driftEG` — the two tensors, **as definitions**:
  `E[primBil (L-K) (L-K)]` and `E[E^{(G)}]`.  `RBM.driftE_eq_driftELK_add_driftEG` says their
  sum is T173's `RBM.driftE`; `RBM.driftF_path_eq_add` is the pathwise identity behind it (the
  coupling sum of `RBM.DriftDef.driftF` is empty at loop length `2`).
* `RBM.norm_integral_le_add_measure_compl` — the first-moment bookkeeping outside a good set,
  `‖E f‖ ≤ c + Env · P(Gᶜ)`, with **no measurability hypothesis on the good set** (the good
  sets of Lemma 5.9 are quantified over the uncountable time window).
* `RBM.norm_primBil_lkPath_le` — **(5.77), second line, at `n = 0`, in (5.133)'s own shape**
  `W ℓ_u (W ℓ_u η_u)^{-4}`.  The single identity spent is
  `RBM.Decay.mul_add_one_div_le`, `W(ℓ+1)/A ≤ (Krad+2)/η_u`.
* `RBM.unifDetDom_driftELK` — **(5.133)** for `RBM.driftELK`.
* `RBM.eventually_rpow_neg_three_le_drift_target` — the `hlow` side condition of
  `RBM.DriftBound.stochDom_norm_driftF` (the target of (5.133) is `≥ N^{-3}`), here proved
  rather than assumed, so that it is discharged in the assembly below.
* `RBM.fastDecay_integral_of_highProb` — fast decay survives `E` on a good set; this replaces
  T173's `RBM.fastDecay_integral`, which needed the pathwise decay at *every* `ω`.
* `RBM.fastDecayHyp_driftSplit` — **`RBM.Step6.FastDecayHyp` for the pair**, from Lemma 5.9's
  decay (`RBM.FDInputs`) and a crude envelope.  The radius arithmetic
  `2 ℓ_v W^{τ/2} + 1 ≤ ℓ_v W^τ` uses `3 ≤ W^{τ/2}`, i.e. (2.2).
* `RBM.hierarchy_driftSplit` — **(5.129)–(5.131)** for the pair, on the **open** interval
  (T152), from T173's expectation drift identity.
* `RBM.sharpExpect_step6_driftSplit` — **(2.80)** with `hH`, `hFD` and (5.133) discharged.

## The fiat audit

`RBM.driftELK` and `RBM.driftEG` are `def`s whose integrands unfold to the Green function of
the flow; there is no structure field and nothing an instance could choose.  Every hypothesis
of `RBM.sharpExpect_step6_driftSplit` is either about the *sample* (`RBM.FDInputs`,
`RBM.QuadInputs`, the envelope, the measurability, the integrability, `hEL`) or one of the
five inputs `RBM.Step6.sharpExpect_step6` already had and which do not mention the drift
((5.132), (5.127), `quad11`, `quad13`, the one-loop integrability) — with the single exception
of `hG`, (5.134), whose status is discussed above.  Nothing here is an `axiom` and nothing is
`sorry`.
-/

namespace RBM

open MeasureTheory Filter

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The pathwise `L - K` of the flow at time `v`. -/
noncomputable def lkPath (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω) :
    LoopIdx (ZMod (B.L N)) → ℂ :=
  gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) - B.Kval E N v

/-- The `E^{(G)}` half of the pinned drift, `E E^{(G)}` of (5.131). -/
noncomputable def driftEG (X : Sample B) (E : ℝ) : Step6.DriftTensor B :=
  fun N v σ a => ∫ ω, Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
    (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a)) ∂B.P

/-- The quadratic half of the pinned drift, `E E^{((L-K)×(L-K))}` of (5.130). -/
noncomputable def driftELK (X : Sample B) (E : ℝ) : Step6.DriftTensor B :=
  fun N v σ a => ∫ ω, primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
    (LoopData.idx (σ, a)) ∂B.P

/-- **At loop length `2` the drift is `E^{(G)} + E^{((L-K)×(L-K))}`**: the coupling sum of
`RBM.DriftDef.driftF` is empty. -/
theorem driftF_zero_eq_eG_add (B : Band Ω) (E : ℝ) (N : ℕ) (v : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) :
    DriftDef.driftF B E N v M (n := 0) σ a
      = Decay.eG (B.L N) (B.W N)
          (gloop (B.L N) (B.W N) M (zt E v) - B.Kval E N v)
          (gloop (B.L N) (B.W N) M (zt E v)) (LoopData.idx (σ, a))
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E v) - B.Kval E N v)
            (gloop (B.L N) (B.W N) M (zt E v) - B.Kval E N v) (LoopData.idx (σ, a)) := by
  have hempty : Finset.Icc 3 (0 + 2) = (∅ : Finset ℕ) := rfl
  rw [DriftDef.driftF_eq_eG_add, hempty, Finset.sum_empty, add_zero]

/-- The pathwise form of the same split, along the flow. -/
theorem driftF_path_eq_add (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) :
    DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a
      = primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω) (LoopData.idx (σ, a))
        + Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
            (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a)) := by
  rw [driftF_zero_eq_eG_add]
  rw [show lkPath X E N v ω
      = gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) - B.Kval E N v from rfl]
  ring

/-- **`RBM.driftE` is `RBM.driftELK + RBM.driftEG`.**  The paper's split of the drift of
(5.15) into `E E^{((L-K)×(L-K))}` and `E E^{(G)}`, for the *pinned* drift of T173. -/
theorem driftE_eq_driftELK_add_driftEG (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ)
    (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2)
    (hG : Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
      (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) B.P)
    (hQ : Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
      (LoopData.idx (σ, a))) B.P) :
    driftE X E N v σ a = driftELK X E N v σ a + driftEG X E N v σ a := by
  have hpt : ∀ ω : Ω, DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a
      = primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω) (LoopData.idx (σ, a))
        + Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
            (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a)) :=
    fun ω => driftF_path_eq_add X E N v ω σ a
  show (∫ ω, DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a ∂B.P) = _
  rw [show (fun ω : Ω => DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ a)
      = (fun ω : Ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
            (LoopData.idx (σ, a))
          + Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
              (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a)))
      from funext hpt,
    integral_add hQ hG]
  rfl

end Split

/-! ### First moments from a good set and a deterministic envelope -/

section Moment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The first-moment bookkeeping outside the good set.**  If `‖f‖ ≤ c` on `G` and `‖f‖ ≤ Env`
everywhere, then `‖E f‖ ≤ c + Env · P(Gᶜ)`.  This is the only step of Step 6's size estimates
that is not deterministic: the bounds of Lemma 5.10 hold with high probability, and the
expectation sees the complement through a crude envelope. -/
theorem norm_integral_le_add_measure_compl_of_measurable {P : Measure Ω}
    [IsProbabilityMeasure P]
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f P) {G : Set Ω} (hG : MeasurableSet G)
    {c Env : ℝ} (hc : 0 ≤ c)
    (hgood : ∀ ω ∈ G, ‖f ω‖ ≤ c) (henv : ∀ ω, ‖f ω‖ ≤ Env) :
    ‖∫ ω, f ω ∂P‖ ≤ c + Env * (P Gᶜ).toReal := by
  classical
  have hint : Integrable f P :=
    Integrable.mono' (integrable_const Env) hf (Filter.Eventually.of_forall henv)
  have hbound : ∀ ω, ‖f ω‖ ≤ c + Env * Set.indicator Gᶜ (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      simpa using hgood ω hω
    · rw [Set.indicator_of_mem (by simpa using hω)]
      have := henv ω
      simp only [mul_one]
      linarith
  have hint2 : Integrable (fun ω => c + Env * Set.indicator Gᶜ (fun _ => (1 : ℝ)) ω) P := by
    refine (integrable_const c).add (Integrable.const_mul ?_ Env)
    exact (integrable_const (1 : ℝ)).indicator hG.compl
  calc ‖∫ ω, f ω ∂P‖ ≤ ∫ ω, ‖f ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (c + Env * Set.indicator Gᶜ (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono hint.norm hint2 hbound
    _ = c + Env * (P Gᶜ).toReal := by
        rw [integral_add (integrable_const c) (Integrable.const_mul
          ((integrable_const (1 : ℝ)).indicator hG.compl) Env), integral_const,
          integral_const_mul, integral_indicator hG.compl]
        simp [MeasureTheory.measureReal_def]

/-- The same with **no measurability hypothesis on the good set**: the good sets of Lemma 5.9
and of the power counts (5.76) are quantified over the uncountable time window, so their
measurability is not free, and `RBM.HighProb` does not ask for it either.  Replacing `G` by
the complement of a measurable hull of `Gᶜ` changes neither side. -/
theorem norm_integral_le_add_measure_compl {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f P) {G : Set Ω}
    {c Env : ℝ} (hc : 0 ≤ c)
    (hgood : ∀ ω ∈ G, ‖f ω‖ ≤ c) (henv : ∀ ω, ‖f ω‖ ≤ Env) :
    ‖∫ ω, f ω ∂P‖ ≤ c + Env * (P Gᶜ).toReal := by
  classical
  set G' : Set Ω := (toMeasurable P Gᶜ)ᶜ with hG'
  have hsub : G' ⊆ G := by
    intro ω hω
    by_contra hωG
    exact hω (subset_toMeasurable P Gᶜ hωG)
  have hmeas : MeasurableSet G' := (measurableSet_toMeasurable P Gᶜ).compl
  have hcompl : P G'ᶜ = P Gᶜ := by
    rw [hG', compl_compl]
    exact measure_toMeasurable Gᶜ
  have := norm_integral_le_add_measure_compl_of_measurable (P := P) hf hmeas hc
    (fun ω hω => hgood ω (hsub hω)) henv
  rwa [hcompl] at this

end Moment

/-! ### (5.133) for the quadratic half, pointwise -/

section Quad

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.77), second line, at loop length `2`, in (5.133)'s shape.**

`RBM.DriftBound.norm_driftF_le` collects the three lines of (5.77) into one constant
`RBM.DriftBound.cDrift` and one power `A^{-(n+2)} η^{-1}`; that shape is *one factor `A` too
weak* for (5.133).  The quadratic line alone is not: its `Ξ`-factor
`Φ = Ξ^{(L-K)}_{u,2} Ξ^{(L-K)}_{u,2} A^{-1}` carries the extra `A^{-1}`, and after
`RBM.Decay.mul_add_one_div_le` (`W(ℓ+1)/A ≤ (Krad+2)/η_u`) the main term is exactly
`W ℓ_u (W ℓ_u η_u)^{-4}`, i.e. `η_u^{-1}(W ℓ_u η_u)^{-3}`. -/
theorem norm_primBil_lkPath_le (X : Sample B) {E : ℝ} (N : ℕ) {u : ℝ} (ω : Ω)
    (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) {Krad δ : ℝ}
    (hE : |E| < 2) (hu1 : u < 1)
    (hA : 1 ≤ B.scale E N u) (hell : 1 / 2 ≤ B.ell N u) (hKrad : 1 ≤ Krad) (hδ : 0 ≤ δ)
    (hDd : Decay.LoopDecay (B.L N) 2 (B.ell N u * Krad) δ (lkPath X E N u ω)) :
    ‖primBil (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω) (LoopData.idx (σ, a))‖
      ≤ 8 * Real.exp 1 * (Krad + 2) * X.xiLK E N u ω 2 ^ 2
          * ((B.W N : ℝ) * B.ell N u * (B.scale E N u)⁻¹ ^ 4)
        + 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * X.xiLK E N u ω 2 := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hℓ0 : (0 : ℝ) < B.ell N u * Krad := by nlinarith
  set A := B.scale E N u with hAdef
  have hxi2 : 0 ≤ X.xiLK E N u ω 2 := X.xiLK_nonneg hA0.le
  have hD : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ 2 →
      ‖lkPath X E N u ω J‖ ≤ X.xiLK E N u ω J.length * A⁻¹ ^ J.length := fun J hJ _ _ =>
    DriftBound.norm_lk_le X E N u ω hA0.ne' J hJ rfl
  have hX : ∀ m, 2 ≤ m → m ≤ 2 →
      X.xiLK E N u ω m * X.xiLK E N u ω (2 - m + 2) * A⁻¹
        ≤ X.xiLK E N u ω 2 * X.xiLK E N u ω 2 * A⁻¹ := by
    intro m h1 h2
    have : m = 2 := le_antisymm h2 h1
    subst this
    exact le_rfl
  have hXB : ∀ m, 2 ≤ m → m ≤ 2 → X.xiLK E N u ω m ≤ X.xiLK E N u ω 2 := by
    intro m h1 h2
    have : m = 2 := le_antisymm h2 h1
    subst this
    exact le_rfl
  have hbase := Decay.norm_loopTensor_primBil_le (B.L N) hL3 (B.W N) (n := 2)
    (D := lkPath X E N u ω) σ (fun k => X.xiLK E N u ω k) hA hℓ0 hδ
    (by positivity) hxi2 hD hX hXB hDd a
  have hfrac : (B.W N : ℝ) * (B.ell N u * Krad + 1) / A ≤ (Krad + 2) * (etaT E u)⁻¹ := by
    rw [hAdef, show B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u from rfl,
      ← div_eq_mul_inv]
    exact Decay.mul_add_one_div_le hW hell hη
  have hid : (B.W N : ℝ) * B.ell N u * A⁻¹ ^ 4 = (etaT E u)⁻¹ * A⁻¹ ^ 3 :=
    Step6.W_mul_ell_mul_scale_inv_pow_four hE N hu1
  have hmain : 2 * Real.exp 1 * (2 : ℝ) ^ 2 * (X.xiLK E N u ω 2 * X.xiLK E N u ω 2 * A⁻¹)
        * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ 2
      ≤ 8 * Real.exp 1 * (Krad + 2) * X.xiLK E N u ω 2 ^ 2
          * ((B.W N : ℝ) * B.ell N u * A⁻¹ ^ 4) := by
    rw [hid]
    have hc0 : (0 : ℝ) ≤ 2 * Real.exp 1 * (2 : ℝ) ^ 2
        * (X.xiLK E N u ω 2 * X.xiLK E N u ω 2 * A⁻¹) * A⁻¹ ^ 2 := by
      have : (0 : ℝ) ≤ A⁻¹ := inv_nonneg.2 hA0.le
      positivity
    have hstep := mul_le_mul_of_nonneg_left hfrac hc0
    calc 2 * Real.exp 1 * (2 : ℝ) ^ 2 * (X.xiLK E N u ω 2 * X.xiLK E N u ω 2 * A⁻¹)
            * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ 2
        = 2 * Real.exp 1 * (2 : ℝ) ^ 2 * (X.xiLK E N u ω 2 * X.xiLK E N u ω 2 * A⁻¹) * A⁻¹ ^ 2
            * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) := by ring
      _ ≤ 2 * Real.exp 1 * (2 : ℝ) ^ 2 * (X.xiLK E N u ω 2 * X.xiLK E N u ω 2 * A⁻¹) * A⁻¹ ^ 2
            * ((Krad + 2) * (etaT E u)⁻¹) := hstep
      _ = 8 * Real.exp 1 * (Krad + 2) * X.xiLK E N u ω 2 ^ 2 * ((etaT E u)⁻¹ * A⁻¹ ^ 3) := by
          rw [pow_succ, pow_succ]; ring
  have herr : (2 : ℝ) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * X.xiLK E N u ω 2
      = 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * X.xiLK E N u ω 2 := by ring
  have hLT : ‖primBil (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
      (LoopData.idx (σ, a))‖
      = ‖Decay.loopTensor (B.L N) (primBil (B.L N) (B.W N) (lkPath X E N u ω)
          (lkPath X E N u ω)) σ a‖ := rfl
  rw [hLT]
  push_cast at hbase
  linarith [hbase]

end Quad

/-! ### (5.133) for the quadratic half of the pinned drift -/

section QuadDom

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The inputs of (5.133) at one `N`.**  Lemma 5.9's `(Krad, δ)` decay of `L - K` at the
`2`-loops and the power count (5.76) at length `2`, uniformly in `u ∈ [s_N, t_N]`.  Neither
mentions the drift; both are produced elsewhere (`RBM.Decay.lemma59`, Step 3).  This is the
`n = 0` fragment of `RBM.DriftBound.DriftInputs`. -/
def QuadInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (Krad δ Ψ : ℝ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 2 (B.ell N (u : ℝ) * Krad) δ (lkPath X E N (u : ℝ) ω)
    ∧ X.xiLK E N (u : ℝ) ω 2 ≤ Ψ}

open Real in
set_option maxHeartbeats 1000000 in
/-- **(5.133) for `RBM.driftELK`.**

`E E^{((L-K)×(L-K))} ≺ W ℓ_u (W ℓ_u η_u)^{-4}`, for the tensor pinned in
`RBM.driftELK`.  Three things go into it and nothing else:

* the pointwise second line of (5.77) in (5.133)'s own shape
  (`RBM.norm_primBil_lkPath_le` — this is where `W(ℓ+1)/A ≤ (Krad+2)/η_u` is spent);
* the high-probability inputs `RBM.QuadInputs` (Lemma 5.9's decay and the count (5.76)),
  with `Krad = N^τ`, `δ = N^{-D}`, `Ψ = N^τ`;
* the first-moment bookkeeping outside the good set
  (`RBM.norm_integral_le_add_measure_compl`), which is why a deterministic polynomial
  envelope `Env` is needed: the bound of Lemma 5.10 is not pathwise.

`hlow` is the statement that the target of (5.133) is not super-polynomially small; it is the
same side condition as `hlow` of `RBM.DriftBound.stochDom_norm_driftF`. -/
@[deprecated "RETIRED (T205/T227): the envelope/measurability/integrability hypotheses here quantify the TIME v over all of the reals, while the proof only ever uses v in TimeIcc s t N. At E = 0, omega = 0, v = 1 - w the (5.131) integrand has the closed form 2(1/w - 1)/w^3/W, unbounded as w tends to 0 with no cancellation, so NO Env satisfies henvG - RBM.Gauss.not_exists_env_eG proves it. Filling these slots makes (2.71) vacuous. Use the primed version in RBM1D/Gauss/Step6EnvWindow.lean, whose only change is the time quantifier (verified verbatim otherwise), together with RBM.exists_env_window and RBM.Gauss.env_window_vs_not_exists_env_eG." (since := "2026-09-21")]
theorem unifDetDom_driftELK (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv Blow : ℝ}
    (hmeas : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (henv : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N)
    (hKenv : 0 ≤ Kenv) (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hB : 0 ≤ Blow)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-Blow)
      ≤ (B.W N : ℝ) * B.ell N (u : ℝ) * (B.scale E N (u : ℝ))⁻¹ ^ 4)
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
        ‖driftELK X E N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4) := by
  have hP := B.isProbabilityMeasure
  intro τ hτ
  set τ₁ : ℝ := τ / 8 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set D₁ : ℝ := Blow + Kenv + τ₁ + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hin τ₁ hτ₁ D₁ hD₁ D₁ hD₁,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc, hEnvpoly, hlow,
    SumZeroDyn.eventually_const_mul_rpow_le (24 * exp 1)
      (show 3 * τ₁ < τ / 2 by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 4
      (show 2 + τ₁ - D₁ < -Blow - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -Blow - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith),
    eventually_ge_atTop 2] with N hgood hcr hEnvN hlowN hmainN herr1N herr2N hfinN hN2
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  rintro ⟨v, q⟩
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := (v : ℝ) with hudef
  have hu0 : 0 ≤ u := (hs0 N).trans v.2.1
  have hu1 : u < 1 := v.2.2.trans_lt (ht1 N)
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hA : 1 ≤ B.scale E N u := (hu v).1
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  set Gt : ℝ := (B.W N : ℝ) * B.ell N u * (B.scale E N u)⁻¹ ^ 4 with hGtdef
  have hGt0 : 0 ≤ Gt := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (B.scale E N u)⁻¹ ^ 4 := by positivity
    have hℓ0 : (0 : ℝ) ≤ B.ell N u := by linarith
    rw [hGtdef]; positivity
  have hGtlow : (N : ℝ) ^ (-Blow) ≤ Gt := hlowN v
  set Krad : ℝ := (N : ℝ) ^ τ₁ with hKraddef
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  have hKrad1 : (1 : ℝ) ≤ Krad := Real.one_le_rpow hN1' hτ₁.le
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  -- the pointwise bound on the good set
  set c : ℝ := 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt + 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
    with hcdef
  have hc0 : 0 ≤ c := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ Krad := by linarith
    rw [hcdef]
    have h1 : (0 : ℝ) ≤ 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt := by positivity
    have h2 : (0 : ℝ) ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad := by positivity
    linarith
  have hpt : ∀ ω ∈ QuadInputs X E s t N Krad δ Krad,
      ‖primBil (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2))‖ ≤ c := by
    intro ω hω
    obtain ⟨hDd, hΨ⟩ := hω v
    have hxi0 : 0 ≤ X.xiLK E N u ω 2 := X.xiLK_nonneg hA0.le
    have hbase := norm_primBil_lkPath_le X N ω q.1 q.2 hE hu1 hA hell hKrad1 hδ0 hDd
    refine hbase.trans ?_
    rw [hcdef, ← hGtdef]
    have h1 : X.xiLK E N u ω 2 ^ 2 ≤ Krad ^ 2 := by
      have : X.xiLK E N u ω 2 ≤ Krad := hΨ
      nlinarith
    have hcoef : (0 : ℝ) ≤ 8 * exp 1 * (Krad + 2) := by
      have : (0 : ℝ) ≤ Krad := by linarith
      positivity
    have hWLd : (0 : ℝ) ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) := by
      have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hA' : 8 * exp 1 * (Krad + 2) * X.xiLK E N u ω 2 ^ 2 * Gt
        ≤ 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt := by
      have := mul_le_mul_of_nonneg_left h1 hcoef
      exact mul_le_mul_of_nonneg_right this hGt0
    have hB' : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * X.xiLK E N u ω 2
        ≤ 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad :=
      mul_le_mul_of_nonneg_left hΨ hWLd
    linarith
  -- the first moment
  have hbad : (B.P (QuadInputs X E s t N Krad δ Krad)ᶜ).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ0 hgood
  have hstep : ‖driftELK X E N v q.1 q.2‖ ≤ c + Env N * δ := by
    have := norm_integral_le_add_measure_compl (P := B.P)
      (f := fun ω => primBil (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2)))
      (hmeas N u q.1 q.2) (G := QuadInputs X E s t N Krad δ Krad) hc0 hpt
      (fun ω => henv N u q.1 q.2 ω)
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbad (hEnv0 N)
    linarith
  refine hstep.trans ?_
  -- the `Ξ`-bookkeeping: main term, two errors
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]; nlinarith
  have hmain : 8 * exp 1 * (Krad + 2) * Krad ^ 2 * Gt ≤ (N : ℝ) ^ (τ / 2) * Gt := by
    have h3 : Krad + 2 ≤ 3 * Krad := by linarith
    have hK0 : (0 : ℝ) ≤ Krad := by linarith
    have hstep2 : 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 24 * exp 1 * (N : ℝ) ^ (3 * τ₁) := by
      have hk3 : Krad ^ 3 = (N : ℝ) ^ (3 * τ₁) := by
        rw [hKraddef, ← Real.rpow_natCast ((N : ℝ) ^ τ₁) 3, ← Real.rpow_mul hN0.le]
        norm_num [mul_comm]
      have : 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 8 * exp 1 * (3 * Krad) * Krad ^ 2 := by
        have : (0 : ℝ) ≤ 8 * exp 1 * Krad ^ 2 := by positivity
        nlinarith [exp_nonneg (1 : ℝ)]
      calc 8 * exp 1 * (Krad + 2) * Krad ^ 2 ≤ 8 * exp 1 * (3 * Krad) * Krad ^ 2 := this
        _ = 24 * exp 1 * Krad ^ 3 := by ring
        _ = 24 * exp 1 * (N : ℝ) ^ (3 * τ₁) := by rw [hk3]
    exact mul_le_mul_of_nonneg_right (hstep2.trans hmainN) hGt0
  have herr1 : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ (N : ℝ) ^ (-Blow - 1) := by
    have he : (N : ℝ) ^ (2 : ℝ) * δ * Krad = (N : ℝ) ^ (2 + τ₁ - D₁) := by
      rw [hδdef, hKraddef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hmono : 4 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
        ≤ 4 * ((N : ℝ) ^ (2 : ℝ) * δ) * Krad := by
      have hK0 : (0 : ℝ) ≤ Krad := by linarith
      have : (B.W N : ℝ) * (B.L N : ℝ) * δ ≤ (N : ℝ) ^ (2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hWL hδ0
      nlinarith
    refine hmono.trans ?_
    calc 4 * ((N : ℝ) ^ (2 : ℝ) * δ) * Krad = 4 * ((N : ℝ) ^ (2 : ℝ) * δ * Krad) := by ring
      _ = 4 * (N : ℝ) ^ (2 + τ₁ - D₁) := by rw [he]
      _ ≤ (N : ℝ) ^ (-Blow - 1) := herr1N
  have herr2 : Env N * δ ≤ (N : ℝ) ^ (-Blow - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-Blow - 1) := herr2N
  have hsumerr : (N : ℝ) ^ (-Blow - 1) + (N : ℝ) ^ (-Blow - 1) ≤ Gt := by
    have hmul : (N : ℝ) ^ (-Blow - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-Blow) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-Blow - 1) := Real.rpow_nonneg hN0.le _
    have h2 : (N : ℝ) ^ (-Blow - 1) + (N : ℝ) ^ (-Blow - 1) ≤ (N : ℝ) ^ (-Blow) := by
      rw [← hmul, Real.rpow_one]
      nlinarith
    exact h2.trans hGtlow
  have hfin : (N : ℝ) ^ (τ / 2) * Gt + Gt ≤ (N : ℝ) ^ τ * Gt := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
    have h2 : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by
      have := hfinN
      linarith
    have := mul_le_mul_of_nonneg_right h2 hGt0
    linarith [this]
  rw [hcdef]
  linarith [hmain, herr1, herr2, hsumerr, hfin]

/-- **The target of (5.133) is not super-polynomially small**, with `Blow = 3`:
`W ℓ_u (W ℓ_u η_u)^{-4} = η_u^{-1}(W ℓ_u η_u)^{-3} ≥ N^{-3}`, from `1 ≤ A_u ≤ N`
(`RBM.SumZeroDyn.flow_crude`) and `η_u ≤ 1`.  This is the `hlow` side condition of
`RBM.DriftBound.stochDom_norm_driftF`, here a theorem; in particular `hlow` of
`RBM.unifDetDom_driftELK` is satisfiable. -/
theorem eventually_rpow_neg_three_le_drift_target (B : Band Ω) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-(3 : ℝ))
      ≤ (B.W N : ℝ) * B.ell N (u : ℝ) * (B.scale E N (u : ℝ))⁻¹ ^ 4 := by
  filter_upwards [SumZeroDyn.flow_crude hE hs0 hst ht1 hc, eventually_ge_atTop 1]
    with N hcr hN1
  obtain ⟨_, _, _, hu⟩ := hcr
  intro u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hA1 : 1 ≤ B.scale E N (u : ℝ) := (hu u).1
  have hA0 : (0 : ℝ) < B.scale E N (u : ℝ) := lt_of_lt_of_le zero_lt_one hA1
  have hAN : B.scale E N (u : ℝ) ≤ (N : ℝ) := (hu u).2.1
  have hη : 0 < etaT E (u : ℝ) := etaT_pos hE hu1
  have hη1 : etaT E (u : ℝ) ≤ 1 := etaT_le_one hE hu0
  have hinv1 : (1 : ℝ) ≤ (etaT E (u : ℝ))⁻¹ := by
    have := one_div_le_one_div_of_le hη hη1
    simpa [one_div] using this
  have hrp : (N : ℝ) ^ (-(3 : ℝ)) = ((N : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hN0.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcube : (B.scale E N (u : ℝ)) ^ (3 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hA0.le hAN 3
  have h2 : ((N : ℝ) ^ (3 : ℕ))⁻¹ ≤ (B.scale E N (u : ℝ))⁻¹ ^ 3 := by
    rw [← inv_pow]
    have hpos : (0 : ℝ) < (B.scale E N (u : ℝ)) ^ (3 : ℕ) := by positivity
    have := one_div_le_one_div_of_le hpos hcube
    simpa [one_div] using this
  rw [Step6.W_mul_ell_mul_scale_inv_pow_four hE N hu1]
  calc (N : ℝ) ^ (-(3 : ℝ)) = ((N : ℝ) ^ (3 : ℕ))⁻¹ := hrp
    _ ≤ (B.scale E N (u : ℝ))⁻¹ ^ 3 := h2
    _ = 1 * (B.scale E N (u : ℝ))⁻¹ ^ 3 := (one_mul _).symm
    _ ≤ (etaT E (u : ℝ))⁻¹ * (B.scale E N (u : ℝ))⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_right hinv1 (by positivity)

end QuadDom

/-! ### The fast decay of both halves -/

section FDecay

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Fast decay survives taking expectations, with a good set.**  `RBM.fastDecay_integral`
(T173) asks for the pathwise decay at *every* `ω`; Lemma 5.9 gives it only with high
probability, and the expectation sees the complement through a crude envelope.  The price is
the additive `Env · P(Gᶜ)`, which is super-polynomially small. -/
theorem fastDecay_integral_of_highProb {L : ℕ} [NeZero L] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} {ℓ δ Env : ℝ} {A : Ω → LoopArg L n → ℂ} {G : Set Ω}
    (hδ : 0 ≤ δ) (hmeas : ∀ b, AEStronglyMeasurable (fun ω => A ω b) P)
    (hgood : ∀ ω ∈ G, FastDecay L ℓ δ (A ω)) (henv : ∀ ω b, ‖A ω b‖ ≤ Env) :
    FastDecay L ℓ (δ + Env * (P Gᶜ).toReal) (fun b => ∫ ω, A ω b ∂P) := fun b hb =>
  norm_integral_le_add_measure_compl (hmeas b) hδ
    (fun ω hω => hgood ω hω b hb) (fun ω => henv ω b)

/-- **The pathwise inputs of Lemma 5.9** for the decay of the two halves of the drift at loop
length `2`: the `(ℓ_v Krad, δ)` decay of `L - K` and of `L`, and the sup bound `M` on `L - K`
at lengths `≤ 2`.  Nothing here mentions the drift. -/
def FDInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (Krad δ M : ℝ) : Set Ω :=
  {ω | ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 2 (B.ell N (v : ℝ) * Krad) δ (lkPath X E N (v : ℝ) ω)
    ∧ Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * Krad) δ
        (gloop (B.L N) (B.W N) (X.H N (v : ℝ) ω) (zt E (v : ℝ)))
    ∧ (∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ 2 → ‖lkPath X E N (v : ℝ) ω J‖ ≤ M)}

/-- The quadratic half decays, pathwise: `RBM.Decay.fastDecay_primBil` at `n = 2`. -/
theorem fastDecay_primBil_lkPath (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) {ℓ δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hDd : Decay.LoopDecay (B.L N) 2 ℓ δ (lkPath X E N v ω))
    (hD : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ 2 →
      ‖lkPath X E N v ω J‖ ≤ M) :
    FastDecay (B.L N) (2 * ℓ + 1) (8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)
      (fun a : LoopArg (B.L N) 2 => primBil (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) := by
  have h := Decay.fastDecay_primBil (B.L N) (B.three_le_L N) (B.W N)
    (D := lkPath X E N v ω) (n := 2) (σ := List.ofFn σ) (List.length_ofFn) hδ hM hDd hD
  refine SumZeroDyn.FastDecay.mono (B.L N) h le_rfl ?_
  push_cast
  ring_nf
  exact le_rfl

/-- The `E^{(G)}` half decays, pathwise: `RBM.Decay.fastDecay_eG` at `n = 2`. -/
theorem fastDecay_eG_lkPath (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) {ℓ δ M : ℝ}
    (hLd : Decay.LoopDecay (B.L N) 3 ℓ δ (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)))
    (hD : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ 2 →
      ‖lkPath X E N v ω J‖ ≤ M) :
    FastDecay (B.L N) ℓ (2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ)
      (fun a : LoopArg (B.L N) 2 => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) := by
  have hX : ∀ (b : Bool) (c : ZMod (B.L N)),
      ‖lkPath X E N v ω ⟨[b], [c]⟩‖ ≤ M := fun b c =>
    hD ⟨[b], [c]⟩ rfl (by show (1 : ℕ) ≤ 2; omega)
  have h := Decay.fastDecay_eG (B.L N) (B.W N) (B.three_le_L N)
    (X := lkPath X E N v ω) (n := 2) (σ := List.ofFn σ) (List.length_ofFn) hX hLd
  refine SumZeroDyn.FastDecay.mono (B.L N) h le_rfl ?_
  push_cast
  ring_nf
  exact le_rfl

/-- `W → ∞` in the `W^τ` scale: `C ≤ W^τ` for large `N`, from (2.2). -/
theorem Band.eventually_le_W_rpow (B : Band Ω) (C : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, C ≤ (B.W N : ℝ) ^ τ := by
  have hW : Filter.Tendsto (fun N : ℕ => (B.W N : ℝ)) atTop atTop :=
    Filter.tendsto_atTop.2 fun W₀ => B.eventually_le_W W₀
  exact ((tendsto_rpow_atTop hτ).comp hW).eventually_ge_atTop C

set_option maxHeartbeats 1000000 in
/-- **The fast decay of the two halves of the pinned drift** (`RBM.Step6.FastDecayHyp`).

The `E(L-K)_s` half is `hlk`, which is (5.132)'s companion and belongs to Steps 1–5.  The two
drift halves are proved here: pathwise from `RBM.Decay.fastDecay_primBil` and
`RBM.Decay.fastDecay_eG` (Definition 5.8, no stochastic step), and then in expectation by
`RBM.fastDecay_integral_of_highProb`.  The radius arithmetic is
`2 ℓ_v W^{τ/2} + 1 ≤ ℓ_v W^τ`, which uses `3 ≤ W^{τ/2}`, i.e. (2.2). -/
@[deprecated "RETIRED (T205/T227): the envelope/measurability/integrability hypotheses here quantify the TIME v over all of the reals, while the proof only ever uses v in TimeIcc s t N. At E = 0, omega = 0, v = 1 - w the (5.131) integrand has the closed form 2(1/w - 1)/w^3/W, unbounded as w tends to 0 with no cancellation, so NO Env satisfies henvG - RBM.Gauss.not_exists_env_eG proves it. Filling these slots makes (2.71) vacuous. Use the primed version in RBM1D/Gauss/Step6EnvWindow.lean, whose only change is the time quantifier (verified verbatim otherwise), together with RBM.exists_env_window and RBM.Gauss.env_window_vs_not_exists_env_eG." (since := "2026-09-21")]
theorem fastDecayHyp_driftSplit (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv) (hKM : 0 ≤ KM)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D)) :
    Step6.FastDecayHyp X E s t (driftELK X E) (driftEG X E) := by
  have hP := B.isProbabilityMeasure
  intro τ hτ D hD
  set τ' : ℝ := τ / 2 with hτ'def
  have hτ' : 0 < τ' := by rw [hτ'def]; linarith
  set D₁ : ℝ := D + KM + Kenv + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hlk τ hτ D hD, hin τ' hτ' D₁ hD₁, hEnvpoly,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc, B.eventually_le_W_rpow 3 hτ',
    SumZeroDyn.eventually_const_mul_rpow_le 8
      (show 2 + KM - D₁ < -D - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -D - 1 by rw [hD₁def]; linarith),
    eventually_ge_atTop 2] with N hlkN hinN hEnvN hcr hW3 herr1N herr2N hN2
  obtain ⟨hLN, hWN, _, _⟩ := hcr
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  set M : ℝ := (N : ℝ) ^ KM with hMdef
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  have hM0 : (0 : ℝ) ≤ M := Real.rpow_nonneg hN0.le _
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]; nlinarith
  -- `N^{-D} ≤ W^{-D}`
  have hWD : (N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-D) := by
    have h1 : (0 : ℝ) < (B.W N : ℝ) ^ D := Real.rpow_pos_of_pos hW0 D
    have h2 : (B.W N : ℝ) ^ D ≤ (N : ℝ) ^ D := Real.rpow_le_rpow hW0.le hWN hD.le
    rw [Real.rpow_neg hW0.le, Real.rpow_neg hN0.le, ← one_div, ← one_div]
    exact one_div_le_one_div_of_le h1 h2
  have hsum2 : (N : ℝ) ^ (-D - 1) + (N : ℝ) ^ (-D - 1) ≤ (B.W N : ℝ) ^ (-D) := by
    have hmul : (N : ℝ) ^ (-D - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-D) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-D - 1) := Real.rpow_nonneg hN0.le _
    have : (N : ℝ) ^ (-D - 1) + (N : ℝ) ^ (-D - 1) ≤ (N : ℝ) ^ (-D) := by
      rw [← hmul, Real.rpow_one]; nlinarith
    exact this.trans hWD
  -- the two error budgets
  have herrEnv : Env N * δ ≤ (N : ℝ) ^ (-D - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-D - 1) := herr2N
  have hcoefErr : ∀ cc : ℝ, 0 ≤ cc → cc ≤ 8 →
      cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ (N : ℝ) ^ (-D - 1) := by
    intro cc hcc0 hcc8
    have he : (N : ℝ) ^ (2 : ℝ) * δ * M = (N : ℝ) ^ (2 + KM - D₁) := by
      rw [hδdef, hMdef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hδM : (0 : ℝ) ≤ δ * M := mul_nonneg hδ0 hM0
    have hW0' : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0' : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := mul_nonneg hW0' hL0'
    have hstep : cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ 8 * ((N : ℝ) ^ (2 : ℝ) * δ * M) := by
      have hcc : cc * ((B.W N : ℝ) * (B.L N : ℝ)) ≤ 8 * ((B.W N : ℝ) * (B.L N : ℝ)) :=
        mul_le_mul_of_nonneg_right hcc8 hWL0
      calc cc * (B.W N : ℝ) * (B.L N : ℝ) * δ * M
          = cc * ((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M) := by ring
        _ ≤ 8 * ((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M) :=
            mul_le_mul_of_nonneg_right hcc hδM
        _ = 8 * (((B.W N : ℝ) * (B.L N : ℝ)) * (δ * M)) := by ring
        _ ≤ 8 * ((N : ℝ) ^ (2 : ℝ) * (δ * M)) := by
            have := mul_le_mul_of_nonneg_right hWL hδM
            linarith
        _ = 8 * ((N : ℝ) ^ (2 : ℝ) * δ * M) := by ring
    refine hstep.trans ?_
    rw [he]
    exact herr1N
  refine fun σ => ⟨hlkN σ, ?_⟩
  intro v hv
  set vv : TimeIcc s t N := ⟨v, hv⟩ with hvvdef
  have hv0 : 0 ≤ v := (hs0 N).trans hv.1
  have hv1 : v < 1 := hv.2.trans_lt (ht1 N)
  have hℓ1 : (1 : ℝ) ≤ B.ell N v := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hv0 hv1
    rw [Band.ell]; exact this
  have hWt1 : (1 : ℝ) ≤ (B.W N : ℝ) ^ τ' := by linarith
  -- the radius arithmetic `2 ℓ_v W^{τ'} + 1 ≤ ℓ_v W^τ`
  have hWW : (B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ' = (B.W N : ℝ) ^ τ := by
    rw [← Real.rpow_add hW0]; congr 1; rw [hτ'def]; ring
  have hrad : 2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1 ≤ B.ell N v * (B.W N : ℝ) ^ τ := by
    have h1 : 2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1
        ≤ B.ell N v * (3 * (B.W N : ℝ) ^ τ') := by nlinarith
    have h2 : B.ell N v * (3 * (B.W N : ℝ) ^ τ')
        ≤ B.ell N v * ((B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ') := by
      have : (3 : ℝ) * (B.W N : ℝ) ^ τ' ≤ (B.W N : ℝ) ^ τ' * (B.W N : ℝ) ^ τ' := by nlinarith
      nlinarith
    rw [← hWW]; linarith
  have hradG : B.ell N v * (B.W N : ℝ) ^ τ' ≤ B.ell N v * (B.W N : ℝ) ^ τ := by
    nlinarith [hrad, hWt1]
  constructor
  · -- the quadratic half
    have hgood : ∀ ω ∈ FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M,
        FastDecay (B.L N) (2 * (B.ell N v * (B.W N : ℝ) ^ τ') + 1)
          (8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)
          (fun a : LoopArg (B.L N) 2 => primBil (B.L N) (B.W N) (lkPath X E N v ω)
            (lkPath X E N v ω) (LoopData.idx (σ, a))) := by
      intro ω hω
      obtain ⟨hDd, _, hDb⟩ := hω vv
      exact fastDecay_primBil_lkPath X E N v ω σ hδ0 hM0 hDd hDb
    have hE8 : (0 : ℝ) ≤ 8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M := by
      have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hres := fastDecay_integral_of_highProb (P := B.P)
      (G := FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M) hE8 (hmeasQ N v σ) hgood
      (fun ω a => henvQ N v σ a ω)
    refine SumZeroDyn.FastDecay.mono (B.L N) hres hrad ?_
    have h1 : 8 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M ≤ (N : ℝ) ^ (-D - 1) :=
      hcoefErr 8 (by norm_num) le_rfl
    have h2 : Env N * (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M)ᶜ).toReal
        ≤ (N : ℝ) ^ (-D - 1) := by
      refine le_trans (mul_le_mul_of_nonneg_left hinN (hEnv0 N)) herrEnv
    linarith [hsum2]
  · -- the `E^{(G)}` half
    have hgood : ∀ ω ∈ FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M,
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ')
          (2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ)
          (fun a : LoopArg (B.L N) 2 => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
            (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) := by
      intro ω hω
      obtain ⟨_, hLd, hDb⟩ := hω vv
      exact fastDecay_eG_lkPath X E N v ω σ hLd hDb
    have hE2 : (0 : ℝ) ≤ 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ := by
      have hW0' : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0' : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    have hres := fastDecay_integral_of_highProb (P := B.P)
      (G := FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M) hE2 (hmeasG N v σ) hgood
      (fun ω a => henvG N v σ a ω)
    refine SumZeroDyn.FastDecay.mono (B.L N) hres hradG ?_
    have h1 : 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ ≤ (N : ℝ) ^ (-D - 1) := by
      have := hcoefErr 2 (by norm_num) (by norm_num)
      linarith [this, (by ring : 2 * (B.W N : ℝ) * (B.L N : ℝ) * M * δ
        = 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * M)]
    have h2 : Env N * (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ') δ M)ᶜ).toReal
        ≤ (N : ℝ) ^ (-D - 1) :=
      le_trans (mul_le_mul_of_nonneg_left hinN (hEnv0 N)) herrEnv
    linarith [hsum2]

end FDecay

/-! ### The hierarchy for the split pair -/

section Hier

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.129)–(5.131) with the paper's two tensors, both pinned.**

`RBM.hierarchy_driftE` (T173) carries the whole non-`Θ` drift in one tensor and takes `0` for
the second; that is legitimate for the *identity*, but it is the wrong vehicle for the size
estimates, because (5.133) and (5.135) are proved by different arguments (see
`RBM.norm_primBil_lkPath_le`).  Here the two tensors are `RBM.driftELK = E E^{((L-K)×(L-K))}`
and `RBM.driftEG = E E^{(G)}`, both definitions; the identity is the same one, split by
`RBM.driftE_eq_driftELK_add_driftEG`.  The derivative is again required only on the **open**
interval (T152). -/
theorem hierarchy_driftSplit (X : Sample B) {E : ℝ} (hE : |E| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X E N v σ) a) volume (s N) (u : ℝ)) :
    Step6.Hierarchy X E s t (driftELK X E) (driftEG X E) := by
  refine Step6.hierarchy_of_hasDerivAt_Ioo X hE hs0 ht1 hcont ?_ hintU1 hintU2
  intro N u σ v hv b
  have hv0 : 0 < v := lt_of_le_of_lt (hs0 N) hv.1
  have hv1 : v < 1 := hv.2.trans (u.2.2.trans_lt (ht1 N))
  have hm := norm_time_mul_mSigma_lt_one hE hv0.le hv1
  have hQ := hintQ N v hv0 hv1 σ b
  have hG := hintG N v hv0 hv1 σ b
  have hF : Integrable (fun ω => DriftDef.driftF B E N v (X.H N v ω) (n := 0) σ b) B.P :=
    (hQ.add hG).congr
      (Filter.Eventually.of_forall fun ω => (driftF_path_eq_add X E N v ω σ b).symm)
  refine (hasDerivAt_lkT_thetaOp_driftE X E σ b hm (hintL N v hv0 hv1 σ) hF
    (hEL N v hv0 hv1 σ b)).congr_deriv ?_
  rw [driftE_eq_driftELK_add_driftEG X E N v σ b hG hQ]

end Hier

/-! ### Step 6 with both drift tensors pinned and their size obligations discharged -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

set_option maxHeartbeats 1000000 in
/-- **(2.80) for the pinned drift pair, with `hH`, `hFD` and (5.133) discharged.**

Compared with `RBM.sharpExpect_step6_driftE` (T173), the three obligations that were still
statements *about the drift* are gone:

* `hH` is `RBM.hierarchy_driftSplit`, whose inputs are the analytic ones of T140/T141/T70
  (`hcont`, `hintL`, `hEL`) plus integrability;
* `hFD` is `RBM.fastDecayHyp_driftSplit`, whose inputs are Lemma 5.9's decay (`hin59`) and the
  crude envelope;
* (5.133) is `RBM.unifDetDom_driftELK`, whose inputs are Lemma 5.9's decay and the count
  (5.76) at length `2` (`hinQ`) and the same envelope.

What remains is exactly what `RBM.Step6.sharpExpect_step6` already asked of the random layer
and which never mentions the drift: (5.132), (5.127), the two quadratic counts `hq11`/`hq13`,
the integrability of the one-loops, and the structural bound (5.134) `hG` — which is the only
place `E E^{(G)}` is still constrained by hypothesis, and which cannot be replaced by the
pathwise (5.77): pathwise the third line of (5.77) is one factor `W ℓ_u η_u` weaker than
(5.133), and the missing factor is recovered only by the cancellation inside
`E[(L-K)_1 L_3]`. -/
@[deprecated "RETIRED (T205/T227): the envelope/measurability/integrability hypotheses here quantify the TIME v over all of the reals, while the proof only ever uses v in TimeIcc s t N. At E = 0, omega = 0, v = 1 - w the (5.131) integrand has the closed form 2(1/w - 1)/w^3/W, unbounded as w tends to 0 with no cancellation, so NO Env satisfies henvG - RBM.Gauss.not_exists_env_eG proves it. Filling these slots makes (2.71) vacuous. Use the primed version in RBM1D/Gauss/Step6EnvWindow.lean, whose only change is the time quantifier (verified verbatim otherwise), together with RBM.exists_env_window and RBM.Gauss.env_window_vs_not_exists_env_eG." (since := "2026-09-21")]
theorem sharpExpect_step6_driftSplit (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    -- the analytic inputs of the hierarchy (T140/T141/T70)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X E N v σ) a) volume (s N) (u : ℝ))
    -- measurability and the crude envelope
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    -- Lemma 5.9 and the counts (5.76)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    -- what `RBM.Step6.sharpExpect_step6` asks of the random layer and never of the drift
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h527 : Step6.Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hG : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ N (v : TimeIcc s t N) (σ : Fin 2 → Bool)
      (a : LoopArg (B.L N) 2) (Λ : ℝ),
      (∀ a₁ (w : LoopData (B.L N) 3), ‖Step6.mix13 X E N v a₁ w‖ ≤ Λ) →
        ‖driftEG X E N v σ a‖ ≤ Cg * ((B.W N : ℝ) * B.ell N (v : ℝ) * Λ))
    (hint1 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω (Step6.oneLoop a₁)) B.P)
    (hint2 : ∀ N (v : TimeIcc s t N) (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3),
      Integrable (fun ω => (X.Lval E N v ω (Step6.oneLoop a₁) - B.Kval E N v (Step6.oneLoop a₁)) *
        (X.Lval E N v ω w.idx - B.Kval E N v w.idx)) B.P)
    (hq13 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖Step6.quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4)) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := by linarith
  exact Step6.sharpExpect_step6 X hκ0 hκ1 hEκ hs0 hst ht1 hc
    (hierarchy_driftSplit X hE2 hs0 ht1 hcont hintL hintQ hintG hEL hintU1 hintU2)
    (fastDecayHyp_driftSplit X hE hs0 hst ht1 hc hmeasQ hmeasG henvQ henvG hEnv0 hKenv
      hEnvpoly hKM hlk hin59)
    h5132
    (unifDetDom_driftELK X hE hs0 hst ht1 hc hmeasQ henvQ hEnv0 hKenv hEnvpoly
      (by norm_num) (eventually_rpow_neg_three_le_drift_target B hE hs0 hst ht1 hc) hinQ)
    h527 hq11 hG hint1 hint2 hq13

end Assembly

end RBM
