/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6HierarchyGauss
import RBM1D.Hierarchy.DriftBound

/-!
# The size obligations of Step 6's pinned drift

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8: (5.129)–(5.133) and the fast decay used in §5.8, for the drift tensor that
`RBM1D/Gauss/Step6HierarchyGauss.lean` pins.

Step 6's drift obligations — the hierarchy identity (5.129)–(5.131), the fast decay, and the
size bound (5.133) — are statements *about the drift*.  This file treats them for the paper's
**two** tensors rather than a single one.

## Why the split is necessary and not cosmetic

The paper's `E E^{((L-K)×(L-K))}` and `E E^{(G)}` obey the *same* bound
`η_v^{-1}(W ℓ_v η_v)^{-3}`.  That is true of the bounds but not of their proofs, and (5.133)
cannot be reached through a single tensor:

* the quadratic half obeys (5.133) **pathwise**.  At loop length `2` the `Ξ`-factor of the
  second line of (5.77) is `Φ = Ξ^{(L-K)}_{u,2} Ξ^{(L-K)}_{u,2} A^{-1}`, whose `A^{-1}` is
  exactly the extra power (5.133) needs beyond `A^{-2}`.  This is `RBM.norm_primBil_lkPath_le`.
* the `E^{(G)}` half does **not**.  The third line of (5.77) gives
  `Ξ^{(L-K)}_{u,1} Ξ^{(L)}_{u,3} · η_u^{-1} A^{-2}`, which is one factor `A = W ℓ_u η_u`
  weaker than (5.133)'s `η_u^{-1} A^{-3}`, and the factor is *not* recoverable pathwise: it is
  the cancellation inside the expectation `E[⟨(G-m)E_{a₁}⟩ L_3]` that produces it, i.e. the
  paper's (5.134)/(5.135) route (`RBM1D/Gauss/Step6DriftEG.lean`).

So the two halves need different arguments.

## Main results

* `RBM.driftELK`, `RBM.driftEG` — the two tensors, **as definitions**:
  `E[primBil (L-K) (L-K)]` and `E[E^{(G)}]`.  `RBM.driftE_eq_driftELK_add_driftEG` says their
  sum is `RBM.driftE`; `RBM.driftF_path_eq_add` is the pathwise identity behind it (the
  coupling sum of `RBM.DriftDef.driftF` is empty at loop length `2`).
* `RBM.norm_integral_le_add_measure_compl` — the first-moment bookkeeping outside a good set,
  `‖E f‖ ≤ c + Env · P(Gᶜ)`, with **no measurability hypothesis on the good set** (the good
  sets of Lemma 5.9 are quantified over the uncountable time window).
* `RBM.norm_primBil_lkPath_le` — **(5.77), second line, at `n = 0`, in (5.133)'s own shape**
  `W ℓ_u (W ℓ_u η_u)^{-4}`.  The single identity spent is
  `RBM.Decay.mul_add_one_div_le`, `W(ℓ+1)/A ≤ (Krad+2)/η_u`.
* `RBM.fastDecay_integral_of_highProb` — fast decay survives `E` on a good set, with the
  pathwise decay needed only with high probability.
* `RBM.fastDecay_primBil_lkPath`, `RBM.fastDecay_eG_lkPath` — both halves decay, pathwise.
* `RBM.hierarchy_driftSplit` — **(5.129)–(5.131)** for the pair, on the **open** interval,
  from the expectation drift identity.

## No free data

`RBM.driftELK` and `RBM.driftEG` are `def`s whose integrands unfold to the Green function of
the flow; there is no structure field and nothing an instance could choose.  The inputs
`RBM.FDInputs` and `RBM.QuadInputs` are about the *sample*, not the drift.  Nothing here is an
`axiom` and nothing is `sorry`.
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
(5.15) into `E E^{((L-K)×(L-K))}` and `E E^{(G)}`, for the *pinned* drift. -/
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

Collecting the three lines of (5.77) into one constant and one power `A^{-(n+2)} η^{-1}` gives
a shape *one factor `A` too weak* for (5.133).  The quadratic line alone is not: its `Ξ`-factor
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
mentions the drift; both are produced elsewhere (Lemma 5.9, Step 3). -/
def QuadInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (Krad δ Ψ : ℝ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 2 (B.ell N (u : ℝ) * Krad) δ (lkPath X E N (u : ℝ) ω)
    ∧ X.xiLK E N (u : ℝ) ω 2 ≤ Ψ}

end QuadDom

/-! ### The fast decay of both halves -/

section FDecay

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Fast decay survives taking expectations, with a good set.** The pathwise decay at *every* `ω`
is not available; Lemma 5.9 gives it only with high probability, and the expectation sees the
complement through a crude envelope.  The price is the additive `Env · P(Gᶜ)`, which is
super-polynomially small. -/
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

end FDecay

/-! ### The hierarchy for the split pair -/

section Hier

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.129)–(5.131) with the paper's two tensors, both pinned.**

Carrying the whole non-`Θ` drift in one tensor, with `0` for the second, is legitimate for the
*identity*, but it is the wrong vehicle for the size estimates, because (5.133) and (5.135) are
proved by different arguments (see `RBM.norm_primBil_lkPath_le`).  Here the two tensors are
`RBM.driftELK = E E^{((L-K)×(L-K))}` and `RBM.driftEG = E E^{(G)}`, both definitions; the identity
is the same one, split by `RBM.driftE_eq_driftELK_add_driftEG`.  The derivative is again required
only on the **open** interval. -/
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

end Assembly

end RBM
