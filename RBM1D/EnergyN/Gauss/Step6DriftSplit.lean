/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6DriftSplit
import RBM1D.EnergyN.Hierarchy.SumZeroDyn
import RBM1D.EnergyN.Hierarchy.Step6

/-!
# The drift-target bound and the pinned-pair hierarchy at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.8 ((5.129)–(5.133)).

At an `N`-dependent energy `E : ℕ → ℝ`: the lower bound on the target of (5.133)
(`RBM.eventually_rpow_neg_three_le_drift_targetN`) and, by diagonal specialisation of
`RBM.hierarchy_driftSplit`, the hierarchy (5.129)–(5.131) (`RBM.hierarchyN_driftSplit`).

No energy-dependent constant is fixed here: `RBM.eventually_rpow_neg_three_le_drift_targetN`
uses `RBM.SumZeroDyn.flow_crudeN` (`EnergyN/Hierarchy/SumZeroDyn.lean`) and the `E`-parametric
`RBM.Step6.W_mul_ell_mul_scale_inv_pow_four`, neither of which fixes an `E`-dependent constant
before `∀ᶠ N`.

## `RBM.hierarchyN_driftSplit`: diagonal specialisation

The hypotheses of `RBM.hierarchy_driftSplit` (`hcont`, `hintL`, `hintQ`, `hintG`, `hEL`, `hintU1`,
`hintU2`) are `∀ N` at one fixed energy, and its conclusion
`RBM.Step6.Hierarchy X E s t (driftELK X E) (driftEG X E)` is `∀ N` at that same fixed `E`. To
build `RBM.Step6.HierarchyN X E s t (driftELKN X E) (driftEGN X E)` — one equation per outer index
`N₀`, at the moving energy `E N₀` — the diagonal pattern needs, for every `N₀`, the whole
fixed-energy hypothesis family at `E N₀` (not only its `N₀`-th row): the hypotheses of
`RBM.hierarchyN_driftSplit` carry the outer binder `∀ N₀`, with `E N₀` in place of `E`, and its
`N₀`-th equation is `RBM.hierarchy_driftSplit` at `E := E N₀` (fed with the `N₀`-slice of the
hypotheses), specialized at its own internal binder `N := N₀`.

## Main declarations

* `RBM.eventually_rpow_neg_three_le_drift_targetN` — the lower bound on the target of (5.133).
* `RBM.driftELKN`, `RBM.driftEGN` — the diagonalised drift tensors `fun N v σ a =>
  driftELK X (E N) N v σ a` / `driftEG X (E N) N v σ a`.
* `RBM.hierarchyN_driftSplit` — the diagonal specialisation into `RBM.Step6.HierarchyN`.
-/

namespace RBM

open MeasureTheory Filter

section DriftTargetN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The target of (5.133) is not super-polynomially small**, at an `N`-dependent energy:
`N^{-3} ≤ W ℓ_u (W ℓ_u η_u)^{-4}` eventually, for all `u ∈ [s, t]`, using
`RBM.SumZeroDyn.flow_crudeN`. No energy-dependent constant is fixed here (module docstring). -/
theorem eventually_rpow_neg_three_le_drift_targetN (B : Band Ω) {E : ℕ → ℝ} {s t : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272N B E s t) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-(3 : ℝ))
      ≤ (B.W N : ℝ) * B.ell N (u : ℝ) * (B.scale (E N) N (u : ℝ))⁻¹ ^ 4 := by
  filter_upwards [SumZeroDyn.flow_crudeN hE hs0 hst ht1 hc, eventually_ge_atTop 1]
    with N hcr hN1
  obtain ⟨_, _, _, hu⟩ := hcr
  intro u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hA1 : 1 ≤ B.scale (E N) N (u : ℝ) := (hu u).1
  have hA0 : (0 : ℝ) < B.scale (E N) N (u : ℝ) := lt_of_lt_of_le zero_lt_one hA1
  have hAN : B.scale (E N) N (u : ℝ) ≤ (N : ℝ) := (hu u).2.1
  have hη : 0 < etaT (E N) (u : ℝ) := etaT_pos (hE N) hu1
  have hη1 : etaT (E N) (u : ℝ) ≤ 1 := etaT_le_one (hE N) hu0
  have hinv1 : (1 : ℝ) ≤ (etaT (E N) (u : ℝ))⁻¹ := by
    have := one_div_le_one_div_of_le hη hη1
    simpa [one_div] using this
  have hrp : (N : ℝ) ^ (-(3 : ℝ)) = ((N : ℝ) ^ (3 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hN0.le, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcube : (B.scale (E N) N (u : ℝ)) ^ (3 : ℕ) ≤ (N : ℝ) ^ (3 : ℕ) :=
    pow_le_pow_left₀ hA0.le hAN 3
  have h2 : ((N : ℝ) ^ (3 : ℕ))⁻¹ ≤ (B.scale (E N) N (u : ℝ))⁻¹ ^ 3 := by
    rw [← inv_pow]
    have hpos : (0 : ℝ) < (B.scale (E N) N (u : ℝ)) ^ (3 : ℕ) := by positivity
    have := one_div_le_one_div_of_le hpos hcube
    simpa [one_div] using this
  rw [Step6.W_mul_ell_mul_scale_inv_pow_four (hE N) N hu1]
  calc (N : ℝ) ^ (-(3 : ℝ)) = ((N : ℝ) ^ (3 : ℕ))⁻¹ := hrp
    _ ≤ (B.scale (E N) N (u : ℝ))⁻¹ ^ 3 := h2
    _ = 1 * (B.scale (E N) N (u : ℝ))⁻¹ ^ 3 := (one_mul _).symm
    _ ≤ (etaT (E N) (u : ℝ))⁻¹ * (B.scale (E N) N (u : ℝ))⁻¹ ^ 3 :=
        mul_le_mul_of_nonneg_right hinv1 (by positivity)

end DriftTargetN

/-! ### `RBM.hierarchyN_driftSplit`: the diagonal specialisation -/

section HierN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The pinned drift tensors, diagonalised at an `N`-dependent energy: `driftELK X (E N) N`,
`driftEG X (E N) N`. -/
noncomputable def driftELKN (X : Sample B) (E : ℕ → ℝ) : Step6.DriftTensor B :=
  fun N v σ a => driftELK X (E N) N v σ a

noncomputable def driftEGN (X : Sample B) (E : ℕ → ℝ) : Step6.DriftTensor B :=
  fun N v σ a => driftEG X (E N) N v σ a

/-- **(5.129)–(5.131) with the paper's two tensors, both pinned, at an `N`-dependent energy.**
Diagonal specialisation of `RBM.hierarchy_driftSplit` (module docstring): for each `N₀`, apply
the fixed-energy theorem at `E := E N₀` (fed with the hypotheses' `N₀`-slice, which supplies the
whole fixed-energy family, as `RBM.hierarchy_driftSplit`'s own hypotheses demand), then extract
the `N₀`-th equation. -/
theorem hierarchyN_driftSplit (X : Sample B) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hcont : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X (E N₀) N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval (E N₀) N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X (E N₀) N v ω)
        (lkPath X (E N₀) N v ω) (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X (E N₀) N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt (E N₀) v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N₀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval (E N₀) N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma (E N₀)) (X.H N v ω) (zt (E N₀) v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval (E N₀) N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X (E N₀) N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N₀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma (E N₀)) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X (E N₀) N v σ) a) volume (s N) (u : ℝ)) :
    Step6.HierarchyN X E s t (driftELKN X E) (driftEGN X E) :=
  fun N u σ a =>
    hierarchy_driftSplit X (hE N) hs0 ht1 (hcont N) (hintL N) (hintQ N) (hintG N) (hEL N)
      (hintU1 N) (hintU2 N) N u σ a

end HierN

end RBM
