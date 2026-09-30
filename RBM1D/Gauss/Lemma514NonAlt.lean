/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.MomentDuhamelHypGauss
import Mathlib.Probability.Distributions.Geometric
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Gauss.GridAssemblyKerClass
import RBM1D.Gauss.Lemma510Fixed
import RBM1D.Gauss.EETensorBound
import RBM1D.Gauss.GridStepDecompC
import RBM1D.Gauss.GridDuhamel
import RBM1D.Gauss.GridHierarchyN
import RBM1D.Gauss.FastDecayFlow
import RBM1D.Gauss.Step2Plain

/-!
# Lemma 5.14, the non-alternating charges: (5.20) + (7.16) Case 1

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5 — (5.20), (5.82)–(5.85), (5.93) — and §7, Lemma 7.3, **Case 1** of (7.16).

On non-alternating charges (`RBM.SumZeroDyn.NonAlt`, a repeated sign `σ_k = σ_{k+1}`) §5.5 runs
(5.20) — the **unprojected** Duhamel formula — through **Case 1** of (7.16), where the short
edge `|1 - v ξ_k| ≥ √κ` supplies the contraction that sum-zero supplies in Case 2.  Neither
`Q_u`, nor Ward's identity, nor the sum-zero property is used.  This file carries that argument
out on the grid of the time interval, for a general loop length `n`; the second module docstring
below lists its parts.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel

section Short716

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end Short716

section Consumer

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

end Consumer

section Producer

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

end Producer

section Split

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} {X : Sample B} {E : ℝ}

end Split

section Satisfiability

section WitnessModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

end WitnessModel

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end GridWitness

section EventRowsWitness

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

end EventRowsWitness

end Satisfiability

end RBM.Gauss

/-!
# The general-`n` non-alternating endpoint (Lemma 5.14, grid-assembly route)

Route: the class-restricted, gap-free grid-assembly interface `RBM.Gauss.Grid.GridAssemblyHypPW`
(`RBM.Gauss.Grid.grid_assembly_stopped_pathwise`) with `τ` the `goodSet514` exit, expansion via
`discrete_hierarchy_step_n` + `stepDecompC`, kernel via `uker_decay_le_nonAlt`
(`hker_of_Q716_nonAlt` wrapper), drift via the (5.78)-(5.80), QV via
`qv_contraction_le_nonAlt` (`step_mul_vC_AbC_le_nonAlt` wrapper), Y via the fourth-moment tail
of `GridAssemblyKerClass.lean`, and R via the coarse row-sum bound.

The general-`n` capped Duhamel telescope is built here from the general-`n` glue
`RBM.Gauss.Grid.Uker_grid_semigroup` / `RBM.Gauss.Grid.duhamel_telescope`.

## Main declarations

* §1 `AtrueN`/`DgridN`/`RgridN`/`hierarchy_step_ae_n`/`gridYC`/`step_summand_identity_ae` — the
  true `(L-K)_{u,σ}` grid process, general loop length `n ≥ 2`, general `σ`, and its exact
  one-step recombination `Δ·D_j + Z_{j+1} + Y_{j+1} + R_j`.
* §2 `goodExitTau514`/`lt_goodExitTau514_measurableSet`/`goodExitTau514_eq_of_forall_mem` — the
  `goodSet514`-exit stopping time (no threshold bootstrap).
* §3 `grid_duhamel_telescope_n`/`grid_expansion_stopped_n` — the general-`n`, general-`ξ` capped
  Duhamel telescope and the resulting four-term expansion of `A_k`, matching
  `GridAssemblyHypPW.hexp`.
* §4 `hexp514`, `hqv514`, `kerClass_A0`, `kerClass_drift`, … — the assembly inputs, and
  `budget514`, the (5.93) budget at a fixed `N`.
* §5 the asymptotic helpers of the endpoint.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal

section OddNonAlt

end OddNonAlt

/-! ## §1 : the true grid process, general loop length `n`, general `σ`

`discrete_hierarchy_step_n` bridged to the `Dims`-based grid, and `stepXiC = stepZC + stepYC`
collapsed to the label level via the identity kernel `gridDeltaC`. -/

section TrueProcess

/-- `(band d').toDims = d'`, needed to align `discrete_hierarchy_step_n`'s generic `Band Ω'`
output with the `Dims`-indexed grid machinery (`Ωg d`, `H d s t K N`, `goodSet514 d`). -/
private theorem band_toDims_eq'' (d' : Dims) : (band d').toDims = d' := by
  cases d'; rfl

variable (d : Dims)

/-- **`AtrueN`**: the true `(L−K)_{u_j,σ}` grid process, general loop length `n`. -/
noncomputable def AtrueN (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {n : ℕ} (σ : Fin n → Bool)
    (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) n → ℂ :=
  fun a => LvalN (band d) E N (time s t K N j) (H d s t K N j ω) σ a
    - KvN (band d) E N (time s t K N j) σ a

/-- **`DgridN`**: the deterministic `Δ`-drift bracket of `discrete_hierarchy_step_n`
(`eGterm + [K∼(L−K)]_{l_K≥3} + primBil(L−K,L−K)`), general loop length `n`. -/
noncomputable def DgridN (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {n : ℕ} (σ : Fin n → Bool)
    (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) n → ℂ :=
  fun a => eGterm (d.L N) (d.W N) (mSigma E) (H d s t K N j ω) (zt E (time s t K N j))
        ⟨List.ofFn σ, List.ofFn a⟩
      + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (d.L N) (d.W N) lK
          (fun I => (band d).Kval E N (time s t K N j) I)
          (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) I
            - (band d).Kval E N (time s t K N j) I)
          (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))))
      + primBil (d.L N) (d.W N)
          (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) I
            - (band d).Kval E N (time s t K N j) I)
          (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) I
            - (band d).Kval E N (time s t K N j) I)
          (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N)))

/-- **`RgridN`**: the exact remainder, named by subtraction. -/
noncomputable def RgridN (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {n : ℕ} [NeZero n]
    (σ : Fin n → Bool) (j : ℕ) (ω : Ωg d) (a : LoopArg (d.L N) n) : ℂ :=
  (Pg d)[fun ω' => AtrueN d E s t K N σ (j + 1) ω' a | filt d j] ω
    - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
        (AtrueN d E s t K N σ j ω) a
    - (step s t K N : ℂ) * DgridN d E s t K N σ j ω a

/-- **The exact per-step identity + the remainder bound.** -/
theorem hierarchy_step_ae_n (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hst : s N < t N) (hj : k < K N) (hu0 : 0 ≤ time s t K N k)
    (hu1 : time s t K N (k + 1) < 1) {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) (σ : Fin n → Bool)
    {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (k + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (d.L N) n, ‖(time s t K N k : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (n - 1)‖ < 1) :
    ∀ᵐ ω ∂ (Pg d), ∀ a : LoopArg (d.L N) n,
      (Pg d)[fun ω' => AtrueN d E s t K N σ (k + 1) ω' a | filt d k] ω
          = Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N k : ℂ) (time s t K N (k + 1) : ℂ)
              (AtrueN d E s t K N σ k ω) a
            + (step s t K N : ℂ) * DgridN d E s t K N σ k ω a + RgridN d E s t K N σ k ω a
        ∧ ‖RgridN d E s t K N σ k ω a‖
            ≤ stepErrN (band d) E N n (time s t K N k) (time s t K N (k + 1)) (step s t K N) Bk := by
  have hdet : ∀ᵐ ω ∂ (Pg d), ∀ a : LoopArg (d.L N) n,
      ‖(Pg d)[fun ω' => AtrueN d E s t K N σ (k + 1) ω' a | filt d k] ω
          - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N k : ℂ) (time s t K N (k + 1) : ℂ)
              (AtrueN d E s t K N σ k ω) a
          - (step s t K N : ℂ) * DgridN d E s t K N σ k ω a‖
        ≤ stepErrN (band d) E N n (time s t K N k) (time s t K N (k + 1)) (step s t K N) Bk :=
    band_toDims_eq'' d ▸
      discrete_hierarchy_step_n (band d) s t K N k E hEb hst hj hu0 hu1 hn2 σ hBk0 hBk hξ
  filter_upwards [hdet] with ω hω
  intro a
  have hR : RgridN d E s t K N σ k ω a
      = (Pg d)[fun ω' => AtrueN d E s t K N σ (k + 1) ω' a | filt d k] ω
          - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N k : ℂ) (time s t K N (k + 1) : ℂ)
              (AtrueN d E s t K N σ k ω) a
          - (step s t K N : ℂ) * DgridN d E s t K N σ k ω a := rfl
  refine ⟨by rw [hR]; ring, ?_⟩
  rw [hR]; exact hω a

/-- **`gridYC`**: the second-order remainder `stepYC`, cut to the grid range exactly as
`gridZC` cuts `stepZC`. -/
def gridYC (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N n : ℕ)
    (Φ : ℕ → LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (i : ℕ) (ω : Ωg d) :
    LoopArg (d.L N) n → ℂ :=
  fun a => if 1 ≤ i ∧ i ≤ Kf N then
    stepYC d s t Kf N (i - 1) n (Φ i) (gridDeltaC (d.L N) n) a ω else 0

/-- **`gridΦG` at `H_i` is literally `AtrueN`.** -/
theorem gridΦG_eq_AtrueN (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ) {n : ℕ} (σ : Fin n → Bool)
    (a : LoopArg (d.L N) n) (ω : Ωg d) :
    gridΦG d E s t K N σ i a (H d s t K N i ω) = AtrueN d E s t K N σ i ω a := by
  show ΦgridG (band d) E N (time s t K N i) σ a (H d s t K N i ω) = _
  rw [ΦgridG_band_eq]
  show loopObs d N (zt E (time s t K N i)) (toIdx σ a) (H d s t K N i ω)
      - (band d).Kval E N (time s t K N i) (toIdx σ a) = _
  unfold AtrueN LvalN KvN
  rw [loopObs_of_isHermitian (H_isHermitian d s t K N i ω)]
  rfl

/-- **The `gridDeltaC`-collapse of `stepXiC`.** -/
theorem stepXiC_gridDeltaC_eq (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    (Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (b : LoopArg (d.L N) n)
    (ω : Ωg d) :
    stepXiC d s t K N j n Φ (gridDeltaC (d.L N) n) b ω
      = Φ b (H d s t K N (j + 1) ω)
        - (Pg d)[fun ω' => Φ b (H d s t K N (j + 1) ω') | filt d j] ω := by
  have hcollapse : ∀ ω' : Ωg d, (∑ a : LoopArg (d.L N) n,
      gridDeltaC (d.L N) n b a * Φ a (H d s t K N (j + 1) ω')) = Φ b (H d s t K N (j + 1) ω') := by
    intro ω'
    rw [Finset.sum_eq_single b]
    · simp [gridDeltaC]
    · intro c _ hc; simp [gridDeltaC, Ne.symm hc]
    · simp
  have hfun : (fun ω' => ∑ a : LoopArg (d.L N) n,
        gridDeltaC (d.L N) n b a * Φ a (H d s t K N (j + 1) ω'))
      = fun ω' => Φ b (H d s t K N (j + 1) ω') := funext hcollapse
  unfold stepXiC
  rw [hcollapse ω, hfun]

/-- **The exact per-step identity**: `Δ·D_j + Z_{j+1} + Y_{j+1} + R_j` recombines exactly into
the true one-step increment, general `n`, general `σ`. -/
theorem step_summand_identity_ae (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) {n : ℕ} [NeZero n]
    (σ : Fin n → Bool) (hEb : |E| < 2) (hj : j < K N) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N (j + 1) < 1) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (d.L N) n, ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (n - 1)‖ < 1)
    (hst : s N < t N) (hn2 : 2 ≤ n) :
    ∀ᵐ ω ∂ (Pg d), ∀ a : LoopArg (d.L N) n,
      AtrueN d E s t K N σ (j + 1) ω a
          - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
              (AtrueN d E s t K N σ j ω) a
        = (step s t K N : ℂ) * DgridN d E s t K N σ j ω a
          + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω a
          + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω a
          + RgridN d E s t K N σ j ω a := by
  have hstep := hierarchy_step_ae_n d s t K N j E hEb hst hj hu0 hu1 hn2 σ hBk0 hBk hξ
  filter_upwards [hstep] with ω hω
  intro a
  have h1 := (hω a).1
  have hj1 : (1 : ℕ) ≤ j + 1 ∧ j + 1 ≤ K N := ⟨by omega, by omega⟩
  have hZeq : gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω a
      = stepZC d s t K N j n (gridΦG d E s t K N σ (j + 1)) (gridDeltaC (d.L N) n) a ω := by
    unfold gridZC
    simp only [hj1, and_self, ↓reduceIte, Nat.add_sub_cancel]
  have hYeq : gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω a
      = stepYC d s t K N j n (gridΦG d E s t K N σ (j + 1)) (gridDeltaC (d.L N) n) a ω := by
    unfold gridYC
    simp only [hj1, and_self, ↓reduceIte, Nat.add_sub_cancel]
  have hXY : stepZC d s t K N j n (gridΦG d E s t K N σ (j + 1)) (gridDeltaC (d.L N) n) a ω
        + stepYC d s t K N j n (gridΦG d E s t K N σ (j + 1)) (gridDeltaC (d.L N) n) a ω
      = stepXiC d s t K N j n (gridΦG d E s t K N σ (j + 1)) (gridDeltaC (d.L N) n) a ω := by
    unfold stepYC; ring
  have hcollapse := stepXiC_gridDeltaC_eq d s t K N j n (gridΦG d E s t K N σ (j + 1)) a ω
  have hΦeq : ∀ ω' : Ωg d, gridΦG d E s t K N σ (j + 1) a (H d s t K N (j + 1) ω')
      = AtrueN d E s t K N σ (j + 1) ω' a := gridΦG_eq_AtrueN d E s t K N (j + 1) σ a
  have hCEeq : (Pg d)[fun ω' => gridΦG d E s t K N σ (j + 1) a (H d s t K N (j + 1) ω') | filt d j] ω
      = (Pg d)[fun ω' => AtrueN d E s t K N σ (j + 1) ω' a | filt d j] ω := by
    have : (fun ω' => gridΦG d E s t K N σ (j + 1) a (H d s t K N (j + 1) ω'))
        = (fun ω' => AtrueN d E s t K N σ (j + 1) ω' a) := funext hΦeq
    rw [this]
  rw [hΦeq ω, hCEeq] at hcollapse
  linear_combination h1 - hZeq - hYeq - hXY - hcollapse

end TrueProcess

/-! ## §2 : the `goodSet514`-exit stopping time

A **good-set-exit-only** stopping time: no threshold bootstrap.  It is the first grid index at
which `H_j` leaves the fixed-time good set `goodSet514`. -/

section GoodExit

/-- The good-set-exit stopping time: the first grid index at which `H_j` leaves the good set
`goodSet514 d E N u_j n ε Λ Φ τ D ℓs`, `Kf N` if it never does. -/
def goodExitTau514 (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (n : ℕ)
    (ε Λ Φ τ D ℓs : ℝ) (N : ℕ) : Ωg d → ℕ :=
  firstHit (fun j (ω : Ωg d) =>
    (goodSet514 d E N (time s t Kf N j) n ε Λ Φ τ D ℓs)ᶜ.indicator (fun _ => (1 : ℝ))
      (H d s t Kf N j ω)) (1 / 2) (Kf N)

theorem lt_goodExitTau514_measurableSet (d : Dims) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) {E : ℝ} (n : ℕ)
    (ε Λ Φ τ D ℓs : ℝ) (N j : ℕ) :
    MeasurableSet[filt d j] {ω | j < goodExitTau514 d E s t Kf n ε Λ Φ τ D ℓs N ω} :=
  lt_firstHit_grid_measurableSet d s t Kf N
    (F := fun j M => (goodSet514 d E N (time s t Kf N j) n ε Λ Φ τ D ℓs)ᶜ.indicator
      (fun _ => (1 : ℝ)) M)
    (fun _ => measurable_const.indicator (measurableSet_goodSet514 d E N _ n ε Λ Φ τ D ℓs).compl)
    (1 / 2) (Kf N) j

/-- **The union bound for the good-set-exit stopping time**: on the event where
`H_jω ∈ goodSet514(u_j)` for every `j ≤ Kf N`, the good-set-exit stopping time does not fire
early: `goodExitTau514 = Kf N`. -/
theorem goodExitTau514_eq_of_forall_mem (d : Dims) (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (n : ℕ)
    (ε Λ Φ τ D ℓs : ℝ) (N : ℕ) {ω : Ωg d}
    (hgood : ∀ k : Fin (Kf N + 1),
      H d s t Kf N k ω ∈ goodSet514 d E N (time s t Kf N k) n ε Λ Φ τ D ℓs) :
    goodExitTau514 d E s t Kf n ε Λ Φ τ D ℓs N ω = Kf N := by
  unfold goodExitTau514 firstHit
  rw [MeasureTheory.hittingBtwn_eq_end_iff]
  rintro ⟨j, hj, hmem⟩
  exfalso
  obtain ⟨-, hjK⟩ := hj
  have hgoodk := hgood ⟨j, by omega⟩
  simp only [Fin.val_mk] at hgoodk
  have hnotmem : H d s t Kf N j ω
      ∉ (goodSet514 d E N (time s t Kf N j) n ε Λ Φ τ D ℓs)ᶜ := fun h => h hgoodk
  rw [Set.indicator_of_notMem hnotmem] at hmem
  norm_num [Set.mem_Ici] at hmem

end GoodExit

/-! ## §3 : the general-`n`, general-`ξ` capped Duhamel telescope

The `n = 2`, `ξ ≡ 1` telescope `grid_duhamel_telescope` of `GridExpansion.lean` is private; the
general-`n`, general-`ξ` version is built here from the glue
`Uker_grid_semigroup`/`duhamel_telescope` (`GridDuhamel.lean`), by the same "clamp the grid
time at `K N`" device (so `Uker_grid_semigroup`'s `∀ k : ℕ` hypothesis holds), then reading the
clamped identity back at the raw grid times on `k ≤ K N`. -/

section DuhamelN

variable (d : Dims)

/-- **The general-`n`, general-`ξ` clamped grid Duhamel telescope.** `Uker_grid_semigroup`'s
hypothesis needs the semigroup law for *every* `k : ℕ`, but the raw grid times `time s t K N k`
leave `[0,1)` once `k > K N`; clamping the index at `K N` keeps the times in `[s N, t N] ⊆ [0,1)`
for every `k : ℕ` and agrees with the raw grid times on `k ≤ K N`, which is all
`duhamel_telescope`'s conclusion at `k ≤ K N` ever reads. -/
theorem grid_duhamel_telescope_n {n : ℕ} {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0)
    (A' : ℕ → LoopArg (d.L N) n → ℂ) (m : ℕ) (hm : m ≤ K N) :
    A' m - Uker (d.L N) ξ (time s t K N 0 : ℂ) (time s t K N m : ℂ) (A' 0)
      = ∑ j ∈ Finset.range m, Uker (d.L N) ξ
          (time s t K N (j + 1) : ℂ) (time s t K N m : ℂ)
          (A' (j + 1) - Uker (d.L N) ξ (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (A' j)) := by
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hstep0 : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have huC_mem : ∀ i : ℕ,
      s N ≤ time s t K N (min i (K N)) ∧ time s t K N (min i (K N)) ≤ t N := by
    intro i
    refine ⟨?_, ?_⟩
    · have h0 : 0 ≤ ((min i (K N) : ℕ) : ℝ) * step s t K N := by positivity
      unfold time; linarith
    · have hle : ((min i (K N) : ℕ) : ℝ) ≤ (K N : ℝ) := by exact_mod_cast min_le_right i (K N)
      have hmul := mul_le_mul_of_nonneg_right hle hstep0
      have heq : time s t K N (K N) = t N := time_last s t K N hK0
      unfold time at heq ⊢
      linarith [hmul]
  have huC_lt1 : ∀ (i : ℕ) (l : Fin n),
      ‖(time s t K N (min i (K N)) : ℂ) * ξ l‖ < 1 := by
    intro i l
    obtain ⟨hlo, hhi⟩ := huC_mem i
    have hb : ‖(time s t K N (min i (K N)) : ℂ) * ξ l‖ ≤ time s t K N (min i (K N)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hs0.trans hlo)]
      nlinarith [hξ l, norm_nonneg (ξ l)]
    exact lt_of_le_of_lt (hb.trans hhi) ht1
  have hsg := Uker_grid_semigroup (L := d.L N) (ξ := ξ) hL3
    (fun i => time s t K N (min i (K N))) huC_lt1
  obtain ⟨hself, hcomp⟩ := hsg
  have htele := duhamel_telescope
    (fun i j => UkerHom (d.L N) ξ
      (time s t K N (min i (K N)) : ℂ) (time s t K N (min j (K N)) : ℂ)) hself hcomp A' m
  simp only [UkerHom_apply] at htele
  have hclamp : ∀ i : ℕ, i ≤ K N → time s t K N (min i (K N)) = time s t K N i := by
    intro i hi; rw [min_eq_left hi]
  have h0K : (0 : ℕ) ≤ K N := Nat.zero_le _
  rw [hclamp 0 h0K, hclamp m hm] at htele
  rw [htele]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j < m := Finset.mem_range.mp hj
  have hj1 : j + 1 ≤ K N := by omega
  have hj0 : j ≤ K N := by omega
  rw [hclamp (j + 1) hj1, hclamp j hj0]

set_option maxHeartbeats 4000000 in
-- the nested `Uker`/`gridZC`/`gridYC`/`RgridN` terms make the final `Uker_comp`/`ring` steps slow
-- to elaborate against the default heartbeat budget.
/-- **`GridAssemblyHypPW.hexp`, general `n`, for the "kernel-frozen-after-exit" process.**
Combines `grid_duhamel_telescope_n` (the raw, unstopped algebra) with
`step_summand_identity_ae` (the per-step probabilistic content) and the kernel's composability
(`Uker_comp`) to push every summand through to the common target time `u_k`, with the sum cut at
`min k (τ ω)`.  This is exactly `GridAssemblyHypPW.hexp`'s shape, general `n` and general `σ`,
built once from the `n`-generic glue (not re-derived per `n`). -/
theorem grid_expansion_stopped_n {n : ℕ} [NeZero n] (E : ℝ) (hEb : |E| < 2) (σ : Fin n → Bool)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1)
    (hK0 : K N ≠ 0) (hn2 : 2 ≤ n)
    (hξb : ∀ j ≤ K N, ∀ a : LoopArg (d.L N) n, ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (n - 1)‖ < 1)
    {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ j < K N, ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk)
    (τ : Ωg d → ℕ) (hτ : ∀ ω, τ ω ≤ K N) (k : ℕ) (hk : k ≤ K N) :
    ∀ᵐ ω ∂ (Pg d),
      Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)
          (AtrueN d E s t K N σ (min k (τ ω)) ω)
        = Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
            (AtrueN d E s t K N σ 0 ω)
          + ∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) (xiOf (mSigma E) σ)
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
              ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
                + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
                + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
                + RgridN d E s t K N σ j ω) := by
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  set ξ := xiOf (mSigma E) σ with hξdef
  have hξnorm : ∀ l, ‖ξ l‖ ≤ 1 := fun l => (norm_xiOf_mSigma hEb.le σ l).le
  have hubound : ∀ i, i ≤ K N → ∀ l, ‖(time s t K N i : ℂ) * ξ l‖ < 1 := by
    intro i hi l
    have hmem := mem_Icc_time s t K N i hs0 hst.le hi
    have hnn : 0 ≤ time s t K N i := hs0.trans hmem.1
    have hb : ‖(time s t K N i : ℂ) * ξ l‖ ≤ time s t K N i := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      nlinarith [hξnorm l, norm_nonneg (ξ l), hnn]
    exact lt_of_le_of_lt (hb.trans hmem.2) ht1
  have hstepAll : ∀ᵐ ω ∂ (Pg d), ∀ j : Fin (K N), ∀ a : LoopArg (d.L N) n,
      AtrueN d E s t K N σ ((j : ℕ) + 1) ω a
          - Uker (d.L N) ξ (time s t K N (j : ℕ) : ℂ) (time s t K N ((j : ℕ) + 1) : ℂ)
              (AtrueN d E s t K N σ (j : ℕ) ω) a
        = (step s t K N : ℂ) * DgridN d E s t K N σ (j : ℕ) ω a
          + gridZC d s t K N n (gridΦG d E s t K N σ) ((j : ℕ) + 1) ω a
          + gridYC d s t K N n (gridΦG d E s t K N σ) ((j : ℕ) + 1) ω a
          + RgridN d E s t K N σ (j : ℕ) ω a := by
    refine ae_all_iff.mpr fun j : Fin (K N) => ?_
    have hjKN : (j : ℕ) < K N := j.isLt
    have hmemj1 := mem_Icc_time s t K N ((j : ℕ) + 1) hs0 hst.le (by omega)
    have hmemj := mem_Icc_time s t K N (j : ℕ) hs0 hst.le (by omega)
    exact step_summand_identity_ae d E s t K N (j : ℕ) σ hEb hjKN (hs0.trans hmemj.1)
      (lt_of_le_of_lt hmemj1.2 ht1) hBk0 (hBk (j : ℕ) hjKN) (hξb (j : ℕ) (by omega)) hst hn2
  filter_upwards [hstepAll] with ω hω
  have hmKN : min k (τ ω) ≤ K N := (min_le_right _ _).trans (hτ ω)
  have htele := grid_duhamel_telescope_n d hξnorm s t K N hs0 hst.le ht1 hK0
    (fun j => AtrueN d E s t K N σ j ω) (min k (τ ω)) hmKN
  have hsub : ∀ j ∈ Finset.range (min k (τ ω)),
      Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ)
          (AtrueN d E s t K N σ (j + 1) ω - Uker (d.L N) ξ (time s t K N j : ℂ)
              (time s t K N (j + 1) : ℂ) (AtrueN d E s t K N σ j ω))
        = Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ)
            ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
              + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
              + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
              + RgridN d E s t K N σ j ω) := by
    intro j hj
    have hjm : j < min k (τ ω) := Finset.mem_range.mp hj
    have hjKN : j < K N := lt_of_lt_of_le hjm hmKN
    apply congrArg (Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ))
    funext a
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hω ⟨j, hjKN⟩ a
  rw [Finset.sum_congr rfl hsub] at htele
  have htele' : AtrueN d E s t K N σ (min k (τ ω)) ω
      = (∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) ξ (time s t K N (j + 1) : ℂ)
            (time s t K N (min k (τ ω)) : ℂ)
            ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
              + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
              + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
              + RgridN d E s t K N σ j ω))
        + Uker (d.L N) ξ (time s t K N 0 : ℂ) (time s t K N (min k (τ ω)) : ℂ)
            (AtrueN d E s t K N σ 0 ω) :=
    sub_eq_iff_eq_add.mp htele
  have hmU := hubound (min k (τ ω)) hmKN
  have hkU := hubound k hk
  have hpush := congrArg
    (Uker (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)) htele'
  rw [Uker_add] at hpush
  rw [Uker_comp (d.L N) hL3 hmU hkU (AtrueN d E s t K N σ 0 ω)] at hpush
  have hsumpush : Uker (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)
      (∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) ξ (time s t K N (j + 1) : ℂ)
          (time s t K N (min k (τ ω)) : ℂ)
          ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
            + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
            + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
            + RgridN d E s t K N σ j ω))
      = ∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) ξ (time s t K N (j + 1) : ℂ)
          (time s t K N k : ℂ)
          ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
            + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
            + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
            + RgridN d E s t K N σ j ω) := by
    have hmap := map_sum
      (UkerHom (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ))
      (fun j => Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ)
        ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
          + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
          + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
          + RgridN d E s t K N σ j ω))
      (Finset.range (min k (τ ω)))
    simp only [UkerHom_apply] at hmap
    rw [hmap]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < min k (τ ω) := Finset.mem_range.mp hj
    have hj1 : j + 1 ≤ K N := by omega
    exact Uker_comp (d.L N) hL3 hmU hkU _
  rw [hsumpush] at hpush
  rw [hpush]
  ring

end DuhamelN

/-! ## §4 : the assembly inputs

Everything `GridAssemblyHypPW` needs for the non-alternating endpoint, general `n`: the sharp
(7.16) kernel weight and its (5.93) scale identity (`kappa514_*`, **no `η_s/η_t` prefactor**), the
frozen process and the truncated remainder, the time shift `u_j → u_{j+1}` of the QV input, the
kernel classes of `A_0` and of the drift, the drift size ((5.78)–(5.80)), the sub-Gaussian
constants, the conditional `Y` moments and the
`Δ^{3/2}` bound on the remainder. -/

open scoped Matrix.Norms.L2Operator

section Kappa514

variable (d : Dims)

/-- `A_u = W ℓ_u η_u` is nonincreasing in `u` on `[0,1)`. -/
theorem scale_anti514 {E : ℝ} (hE : |E| < 2) (N : ℕ) {u u' : ℝ} (hu : u ≤ u') (hu' : u' < 1) :
    (band d).scale E N u' ≤ (band d).scale E N u := by
  have h := one_sub_mul_ellHat_anti (d.L N) hu hu'
  have hm := (mE_im_pos hE).le
  have hW : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  show (d.W N : ℝ) * ellHat (d.L N) (u' : ℂ) * etaT E u'
      ≤ (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) * etaT E u
  unfold etaT
  calc (d.W N : ℝ) * ellHat (d.L N) (u' : ℂ) * ((1 - u') * (mE E).im)
      = (d.W N : ℝ) * ((1 - u') * ellHat (d.L N) (u' : ℂ)) * (mE E).im := by ring
    _ ≤ (d.W N : ℝ) * ((1 - u) * ellHat (d.L N) (u : ℂ)) * (mE E).im := by gcongr
    _ = (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) * ((1 - u) * (mE E).im) := by ring

/-- The sharp (7.16) Case 1 kernel weight of `hker_of_Q716_nonAlt`,
`κ_{i,k} = cKerShort·Kd^n·((1-u_i)ℓ_{u_i}/((1-u_k)ℓ_{u_k}))^n`. -/
def kappa514 (L n : ℕ) (E Kd : ℝ) (u : ℕ → ℝ) (i k : ℕ) : ℝ :=
  cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n
    * ((1 - u i) * ellHat L ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat L ((u k : ℝ) : ℂ))) ^ n

/-- The additive decay-error weight of (7.16), `ε_{i,k} = ((1-u_i)/(1-u_k))^n`. -/
def eps514 (n : ℕ) (u : ℕ → ℝ) (i k : ℕ) : ℝ := ((1 - u i) / (1 - u k)) ^ n

/-- **(5.93), the sharp kernel on the initial datum**: `κ_{i,k} A_{u_i}^{-n} = cKerShort Kd^n A_{u_k}^{-n}`
exactly — no `η_s/η_t` prefactor. -/
theorem kappa514_mul_scale_pow_eq {E : ℝ} (hE : |E| < 2) (N n : ℕ) (Kd : ℝ) (u : ℕ → ℝ)
    (i k : ℕ) (hi0 : 0 ≤ u i) (hi1 : u i < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1) :
    kappa514 (d.L N) n E Kd u i k * ((band d).scale E N (u i))⁻¹ ^ n
      = cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n * ((band d).scale E N (u k))⁻¹ ^ n := by
  unfold kappa514
  rw [mul_assoc, scale_ratio_pow (d := d) hE hi0 hi1 hk0 hk1 n]

/-- **(5.93), the sharp kernel on the drift**: for grid times
`0 ≤ u_j ≤ u_{j+1} ≤ u_k < 1`, `κ_{j+1,k} A_{u_j}^{-n} ≤ cKerShort Kd^n A_{u_k}^{-n}` — the kernel
weight from `u_{j+1}` against the drift's own scale at `u_j` carries **no** `η_s/η_t` factor. -/
theorem kappa514_succ_mul_scale_pow_le {E : ℝ} (hE : |E| < 2) (N n : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd)
    (u : ℕ → ℝ) (j k : ℕ) (hj0 : 0 ≤ u j) (hjj : u j ≤ u (j + 1)) (hj1k : u (j + 1) ≤ u k)
    (hk1 : u k < 1) :
    kappa514 (d.L N) n E Kd u (j + 1) k * ((band d).scale E N (u j))⁻¹ ^ n
      ≤ cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n * ((band d).scale E N (u k))⁻¹ ^ n := by
  have hj1 : u (j + 1) < 1 := hj1k.trans_lt hk1
  have hk0 : 0 ≤ u k := hj0.trans (hjj.trans hj1k)
  have hA1 : 0 < (band d).scale E N (u (j + 1)) :=
    (band d).scale_pos' hE N (hj0.trans hjj) hj1
  have hle : (band d).scale E N (u (j + 1)) ≤ (band d).scale E N (u j) :=
    scale_anti514 d hE N hjj hj1
  have hinv : ((band d).scale E N (u j))⁻¹ ^ n ≤ ((band d).scale E N (u (j + 1)))⁻¹ ^ n :=
    pow_le_pow_left₀ (inv_nonneg.mpr (hA1.le.trans hle)) (inv_anti₀ hA1 hle) n
  have hκ0 : 0 ≤ kappa514 (d.L N) n E Kd u (j + 1) k := by
    unfold kappa514
    have hc := cKerShort_nonneg n (Real.sqrt_nonneg (min (2 - |E|) 1))
    have hl1 : 0 < ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) :=
      Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hj1
    have hl2 : 0 < ellHat (d.L N) ((u k : ℝ) : ℂ) :=
      Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hk1
    have h1 : 0 < 1 - u (j + 1) := by linarith
    have h2 : 0 < 1 - u k := by linarith
    positivity
  calc kappa514 (d.L N) n E Kd u (j + 1) k * ((band d).scale E N (u j))⁻¹ ^ n
      ≤ kappa514 (d.L N) n E Kd u (j + 1) k * ((band d).scale E N (u (j + 1)))⁻¹ ^ n :=
        mul_le_mul_of_nonneg_left hinv hκ0
    _ = _ := kappa514_mul_scale_pow_eq d hE N n Kd u (j + 1) k (hj0.trans hjj) hj1 hk0 hk1

end Kappa514


section Frozen514

variable (d : Dims)

/-- Strictly before the good-set exit, the grid state is in `goodSet514`. -/
theorem mem_goodSet514_of_lt_goodExitTau514 {E : ℝ} {s t : ℕ → ℝ} {Kf : ℕ → ℕ} {n : ℕ}
    {ε Λ Φ τ D ℓs : ℝ} {N j : ℕ} {ω : Ωg d}
    (h : j < goodExitTau514 d E s t Kf n ε Λ Φ τ D ℓs N ω) :
    H d s t Kf N j ω ∈ goodSet514 d E N (time s t Kf N j) n ε Λ Φ τ D ℓs := by
  have h1 := lt_firstHit_imp _ _ _ h
  by_contra hc
  have hm : H d s t Kf N j ω ∈ (goodSet514 d E N (time s t Kf N j) n ε Λ Φ τ D ℓs)ᶜ := hc
  rw [Set.indicator_of_mem hm] at h1
  norm_num at h1

theorem goodExitTau514_le (E : ℝ) (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (n : ℕ) (ε Λ Φ τ D ℓs : ℝ)
    (N : ℕ) (ω : Ωg d) : goodExitTau514 d E s t Kf n ε Λ Φ τ D ℓs N ω ≤ Kf N :=
  firstHit_le _ _ _ ω

/-- `‖u · xiLoop‖ < 1` for `u ∈ [0,1)`: the edge parameters have modulus one. -/
theorem norm_time_mul_xiLoop_lt {E : ℝ} (hE : |E| < 2) {L : ℕ} (I : LoopIdx (ZMod L)) (i : ℕ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    ‖(u : ℂ) * xiLoop (mSigma E) I i‖ < 1 := by
  unfold xiLoop
  rw [norm_mul, norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, Complex.norm_real,
    Real.norm_of_nonneg hu0]
  linarith

theorem norm_time_mul_xiOf_lt {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| < 2) (σ : Fin n → Bool)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (i : Fin n) :
    ‖(u : ℂ) * xiOf (mSigma E) σ i‖ < 1 := by
  rw [norm_mul, norm_xiOf_mSigma hE.le, Complex.norm_real, Real.norm_of_nonneg hu0]
  linarith

/-- **The kernel-frozen-after-exit process** `A_k := U_{u_{k∧τ}, u_k}(A_true(k∧τ))`. -/
def Afroz514 {n : ℕ} [NeZero n] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (σ : Fin n → Bool)
    (τ : Ωg d → ℕ) (k : ℕ) (ω : Ωg d) : LoopArg (d.L N) n → ℂ :=
  Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)
    (AtrueN d E s t K N σ (min k (τ ω)) ω)

/-- At `k = τ = K` the frozen process is the true process `(L-K)_{u_K}(H_K)`. -/
theorem Afroz514_eq_of_eq {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    {K : ℕ → ℕ} {N : ℕ} (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (σ : Fin n → Bool)
    {τ : Ωg d → ℕ} {ω : Ωg d} (hτ : τ ω = K N) :
    Afroz514 d E s t K N σ τ (K N) ω = AtrueN d E s t K N σ (K N) ω := by
  unfold Afroz514
  rw [hτ, min_self]
  have hmem := mem_Icc_time s t K N (K N) hs0 hst le_rfl
  exact Uker_self (d.L N) (d.three_le_L N)
    (fun i => norm_time_mul_xiOf_lt hE σ (hs0.trans hmem.1) (hmem.2.trans_lt ht1) i) _

open Classical in
/-- **The remainder, truncated off the null set where the bound fails**: pathwise bounded by
`stepErrN`, and a.e. equal to `RgridN` (so the expansion is unchanged a.e.). -/
def RgridT {n : ℕ} [NeZero n] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (σ : Fin n → Bool)
    (Bk : ℝ) (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) n → ℂ :=
  if ∀ a, ‖RgridN d E s t K N σ j ω a‖
      ≤ stepErrN (band d) E N n (time s t K N j) (time s t K N (j + 1)) (step s t K N) Bk
  then RgridN d E s t K N σ j ω else 0

theorem norm_RgridT_le {n : ℕ} [NeZero n] (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin n → Bool) (Bk : ℝ) (j : ℕ)
    (h0 : 0 ≤ stepErrN (band d) E N n (time s t K N j) (time s t K N (j + 1)) (step s t K N) Bk)
    (ω : Ωg d) (a : LoopArg (d.L N) n) :
    ‖RgridT d E s t K N σ Bk j ω a‖
      ≤ stepErrN (band d) E N n (time s t K N j) (time s t K N (j + 1)) (step s t K N) Bk := by
  unfold RgridT
  split_ifs with h
  · exact h a
  · simpa using h0

/-- Under the hypotheses of `hierarchy_step_ae_n`: `stepErrN ≥ 0` and `RgridT = RgridN` a.e. -/
theorem RgridT_ae {n : ℕ} [NeZero n] (E : ℝ) (hEb : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (N j : ℕ) (hst : s N < t N) (hj : j < K N) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N (j + 1) < 1) (hn2 : 2 ≤ n) (σ : Fin n → Bool) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (d.L N) n, ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (n - 1)‖ < 1) :
    0 ≤ stepErrN (band d) E N n (time s t K N j) (time s t K N (j + 1)) (step s t K N) Bk
      ∧ ∀ᵐ ω ∂(Pg d), RgridT d E s t K N σ Bk j ω = RgridN d E s t K N σ j ω := by
  have hst' := hierarchy_step_ae_n d s t K N j E hEb hst hj hu0 hu1 hn2 σ hBk0 hBk hξ
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, hω⟩ := hst'.exists
    obtain ⟨a⟩ := (inferInstance : Nonempty (LoopArg (d.L N) n))
    exact (norm_nonneg _).trans (hω a).2
  · filter_upwards [hst'] with ω hω
    unfold RgridT
    split_ifs with h
    · rfl
    · exact absurd (fun a => (hω a).2) h

set_option maxHeartbeats 1600000 in
/-- **`GridAssemblyHypPW.hexp` for the frozen process, with the truncated remainder.** -/
theorem hexp514 {n : ℕ} [NeZero n] (E : ℝ) (hEb : |E| < 2) (σ : Fin n → Bool)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1)
    (hK0 : K N ≠ 0) (hn2 : 2 ≤ n) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ j < K N, ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n → ‖(band d).Kval E N w J‖ ≤ Bk)
    (τ : Ωg d → ℕ) (hτ : ∀ ω, τ ω ≤ K N) :
    ∀ k ≤ K N, ∀ᵐ ω ∂(Pg d),
      Afroz514 d E s t K N σ τ k ω
        = Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
            (AtrueN d E s t K N σ 0 ω)
          + ∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) (xiOf (mSigma E) σ)
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
              ((step s t K N : ℂ) • DgridN d E s t K N σ j ω
                + gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
                + gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω
                + RgridT d E s t K N σ Bk j ω) := by
  intro k hk
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst.le hi
  have hξb : ∀ j ≤ K N, ∀ a : LoopArg (d.L N) n, ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
      (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (n - 1)‖ < 1 :=
    fun j hj a => norm_time_mul_xiLoop_lt hEb _ _ (hs0.trans (hmem j hj).1)
      ((hmem j hj).2.trans_lt ht1)
  have hexp := grid_expansion_stopped_n d E hEb σ s t K N hs0 hst ht1 hK0 hn2 hξb hBk0 hBk τ hτ
    k hk
  have hR : ∀ᵐ ω ∂(Pg d), ∀ j : Fin (K N),
      RgridT d E s t K N σ Bk (j : ℕ) ω = RgridN d E s t K N σ (j : ℕ) ω := by
    refine ae_all_iff.mpr fun j => ?_
    have hj := j.isLt
    exact (RgridT_ae d E hEb s t K N (j : ℕ) hst hj (hs0.trans (hmem _ hj.le).1)
      ((hmem _ (by omega)).2.trans_lt ht1) hn2 σ hBk0 (hBk _ hj)
      (hξb _ hj.le)).2
  filter_upwards [hexp, hR] with ω hω hRω
  unfold Afroz514
  rw [hω]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK : j < K N :=
    lt_of_lt_of_le (Finset.mem_range.mp hj) ((min_le_right _ _).trans (hτ ω))
  rw [hRω ⟨j, hjK⟩]

end Frozen514


section Shift514

variable (d : Dims)

/-- **Spectral-parameter shift of one loop** at a fixed Hermitian matrix:
`|L(M,z') - L(M,z)| ≤ ℓ η^{-(ℓ+1)} |z'-z|` for `|Im z|, |Im z'| ≥ η`, `η ≤ 1`. -/
theorem norm_gloop_zshift_le {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    (I : LoopIdx (ZMod (d.L N))) (hwf : I.σ.length = I.a.length) (hlen : 1 ≤ I.a.length) :
    ‖gloop (d.L N) (d.W N) M z' I - gloop (d.L N) (d.W N) M z I‖
      ≤ (I.a.length : ℝ) * (η⁻¹ ^ (I.a.length + 1) * ‖z' - z‖) := by
  have hzn : z.im ≠ 0 := abs_pos.mp (hη.trans_le hz)
  have hzn' : z'.im ≠ 0 := abs_pos.mp (hη.trans_le hz')
  have hG : ‖green M z‖ ≤ η⁻¹ := Gauss.norm_green_le hM hη hz
  have hG' : ‖green M z'‖ ≤ η⁻¹ := Gauss.norm_green_le hM hη hz'
  have hη1' : 1 ≤ η⁻¹ := one_le_inv₀ hη |>.mpr hη1
  have hsub : ‖green M z' - green M z‖ ≤ η⁻¹ * ‖z' - z‖ * η⁻¹ := by
    have h := RBM.norm_green_sub_le hM hM hzn' hzn
    rw [sub_self, norm_zero, zero_add] at h
    refine h.trans ?_
    have h0 : 0 ≤ ‖z' - z‖ := norm_nonneg _
    have hi : 0 ≤ η⁻¹ := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_right hG' h0) hG (norm_nonneg _) (mul_nonneg hi h0)
  have hloop := Gauss.norm_gloop_sub_le (H := M) (H' := M) (z := z') (z' := z) hη1'
    (fun s => norm_Gsig_le_of_green hM hG' s) (fun s => norm_Gsig_le_of_green hM hG s)
    (fun s => (Gauss.norm_Gsig_sub_le_green_sub hM hM z' z s).trans hsub) I hwf hlen
  refine hloop.trans (le_of_eq ?_)
  obtain ⟨k, hk⟩ : ∃ k, I.a.length = k + 1 := ⟨I.a.length - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  ring

/-- `loopMax` shift: `loopMax(M,z',m) ≤ loopMax(M,z,m) + m η^{-(m+1)} |z'-z|`. -/
theorem loopMax_zshift_le {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {z z' : ℂ} {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|)
    {m : ℕ} (hm : 1 ≤ m) :
    loopMax (d.L N) (d.W N) M z' m
      ≤ loopMax (d.L N) (d.W N) M z m + (m : ℝ) * (η⁻¹ ^ (m + 1) * ‖z' - z‖) := by
  unfold loopMax
  refine ciSup_le fun x => ?_
  have hwf : (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N))).σ.length
      = (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N))).a.length := by simp
  have hlen : (⟨List.ofFn x.1, List.ofFn x.2⟩ : LoopIdx (ZMod (d.L N))).a.length = m := by simp
  have h1 := norm_gloop_zshift_le d hM hη hη1 hz hz' _ hwf (by rw [hlen]; exact hm)
  rw [hlen] at h1
  have h2 : ‖gloop (d.L N) (d.W N) M z ⟨List.ofFn x.1, List.ofFn x.2⟩‖
      ≤ ⨆ x : (Fin m → Bool) × (Fin m → ZMod (d.L N)),
          ‖gloop (d.L N) (d.W N) M z ⟨List.ofFn x.1, List.ofFn x.2⟩‖ :=
    le_ciSup (f := fun x : (Fin m → Bool) × (Fin m → ZMod (d.L N)) =>
      ‖gloop (d.L N) (d.W N) M z ⟨List.ofFn x.1, List.ofFn x.2⟩‖) (Set.finite_range _).bddAbove x
  have h3 := norm_sub_norm_le (gloop (d.L N) (d.W N) M z' ⟨List.ofFn x.1, List.ofFn x.2⟩)
    (gloop (d.L N) (d.W N) M z ⟨List.ofFn x.1, List.ofFn x.2⟩)
  linarith

theorem norm_zt_sub {E : ℝ} (hE : |E| < 2) (u u' : ℝ) : ‖zt E u' - zt E u‖ = |u' - u| := by
  have h : zt E u' - zt E u = ((u - u' : ℝ) : ℂ) * mE E := by
    simp only [zt]; push_cast; ring
  rw [h, norm_mul, norm_mE hE.le, Complex.norm_real, Real.norm_eq_abs, mul_one, abs_sub_comm]

theorem abs_zt_im {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu : u < 1) : |(zt E u).im| = etaT E u := by
  have h : (zt E u).im = etaT E u := by simp [zt, etaT]
  rw [h, abs_of_pos (etaT_pos hE hu)]

theorem etaT_le_one {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) : etaT E u ≤ 1 := by
  unfold etaT
  have hm : (mE E).im ≤ 1 := by
    have := Complex.abs_im_le_norm (mE E)
    rw [norm_mE hE.le] at this
    exact (le_abs_self _).trans this
  have hm0 := (mE_im_pos hE).le
  nlinarith

theorem etaT_anti {E : ℝ} (hE : |E| < 2) {u u' : ℝ} (hu : u ≤ u') : etaT E u' ≤ etaT E u := by
  unfold etaT
  have := (mE_im_pos hE).le
  nlinarith

/-- **The QV time shift, `Ξ^{(L)}` part**: at a fixed Hermitian `M`, for `0 ≤ u ≤ u' < 1`,
`Ξ^{(L)}_m(M; u') ≤ Ξ^{(L)}_m(M; u) + m η_{u'}^{-(m+1)} (u'-u) A_u^{m-1}`. -/
theorem xiLM_shift_le {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {u u' : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'1 : u' < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    xiLM d E N u' M m ≤ xiLM d E N u M m
      + (m : ℝ) * ((etaT E u')⁻¹ ^ (m + 1) * (u' - u)) * ((band d).scale E N u) ^ (m - 1) := by
  have hη := etaT_pos hE hu'1
  have hη1 := etaT_le_one hE (hu0.trans huu')
  have hz : etaT E u' ≤ |(zt E u).im| := by
    rw [abs_zt_im hE (huu'.trans_lt hu'1)]; exact etaT_anti hE huu'
  have hz' : etaT E u' ≤ |(zt E u').im| := by rw [abs_zt_im hE hu'1]
  have hmax := loopMax_zshift_le d hM hη hη1 hz hz' hm
  rw [norm_zt_sub hE, abs_of_nonneg (by linarith)] at hmax
  have hA' : 0 < (band d).scale E N u' := (band d).scale_pos' hE N (hu0.trans huu') hu'1
  have hA0 : 0 ≤ (band d).scale E N u := (hA'.le.trans (scale_anti514 d hE N huu' hu'1))
  have hAle : (band d).scale E N u' ≤ (band d).scale E N u := scale_anti514 d hE N huu' hu'1
  have hApow : (band d).scale E N u' ^ (m - 1) ≤ (band d).scale E N u ^ (m - 1) :=
    pow_le_pow_left₀ hA'.le hAle _
  unfold xiLM loopXi
  have hL0 := loopMax_nonneg (L := d.L N) (W := d.W N) (H := M) (z := zt E u') m
  have hL1 := loopMax_nonneg (L := d.L N) (W := d.W N) (H := M) (z := zt E u) m
  have hδ0 : 0 ≤ (m : ℝ) * ((etaT E u')⁻¹ ^ (m + 1) * (u' - u)) := by
    have : 0 ≤ u' - u := by linarith
    positivity
  calc loopMax (d.L N) (d.W N) M (zt E u') m * (band d).scale E N u' ^ (m - 1)
      ≤ loopMax (d.L N) (d.W N) M (zt E u') m * (band d).scale E N u ^ (m - 1) :=
        mul_le_mul_of_nonneg_left hApow hL0
    _ ≤ (loopMax (d.L N) (d.W N) M (zt E u) m
          + (m : ℝ) * ((etaT E u')⁻¹ ^ (m + 1) * (u' - u))) * (band d).scale E N u ^ (m - 1) :=
        mul_le_mul_of_nonneg_right hmax (by positivity)
    _ = _ := by ring

/-- **The QV time shift, decay part**: `decaySet` at `u` with error `W^{-D}` gives
`decaySet` at `u' ≥ u` with error `W^{-D'}` once `W^{-D} + ℓ η_{u'}^{-(ℓ+1)}(u'-u) ≤ W^{-D'}` for every
loop length `1 ≤ ℓ ≤ m₀` (the radius `ℓ_u W^τ` only grows). -/
theorem decaySet_shift {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {m₀ : ℕ} {u u' τ D D' : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'1 : u' < 1)
    (hmem : M ∈ decaySet d E N m₀ u τ D)
    (hδ : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ m₀ →
      (d.W N : ℝ) ^ (-D) + (ℓ : ℝ) * ((etaT E u')⁻¹ ^ (ℓ + 1) * (u' - u)) ≤ (d.W N : ℝ) ^ (-D')) :
    M ∈ decaySet d E N m₀ u' τ D' := by
  have hη := etaT_pos hE hu'1
  have hη1 := etaT_le_one hE (hu0.trans huu')
  have hz : etaT E u' ≤ |(zt E u).im| := by
    rw [abs_zt_im hE (huu'.trans_lt hu'1)]; exact etaT_anti hE huu'
  have hz' : etaT E u' ≤ |(zt E u').im| := by rw [abs_zt_im hE hu'1]
  have hrad : (band d).ell N u * (d.W N : ℝ) ^ τ ≤ (band d).ell N u' * (d.W N : ℝ) ^ τ :=
    mul_le_mul_of_nonneg_right (Step3.ellHat_mono huu' hu'1) (Real.rpow_nonneg (by positivity) _)
  intro J hJ hJlen x hx y hy hxy
  have hlen1 : 1 ≤ J.a.length := by
    rcases J with ⟨σ, a⟩
    cases a with
    | nil => simp at hx
    | cons b a => simp
  have hJ0 := hmem J hJ hJlen x hx y hy (hrad.trans hxy)
  have hsh := norm_gloop_zshift_le d hM hη hη1 hz hz' J hJ hlen1
  rw [norm_zt_sub hE, abs_of_nonneg (by linarith)] at hsh
  have hJl : J.a.length ≤ m₀ := hJlen
  have hb := hδ J.a.length hlen1 hJl
  have h3 := norm_sub_norm_le (gloop (d.L N) (d.W N) M (zt E u') J)
    (gloop (d.L N) (d.W N) M (zt E u) J)
  show ‖gloop (d.L N) (d.W N) M (zt E u') J‖ ≤ (d.W N : ℝ) ^ (-D')
  linarith

end Shift514


section Crude514

variable (d : Dims)

/-- Crude loop bound: `|L_{σ,a}(M, z_u)| ≤ η_u^{-ℓ}` for Hermitian `M`, `1 ≤ ℓ`. -/
theorem norm_gloop_crude {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu1 : u < 1) (J : LoopIdx (ZMod (d.L N))) (hJ : J.WF)
    (hlen : 1 ≤ J.a.length) :
    ‖gloop (d.L N) (d.W N) M (zt E u) J‖ ≤ (etaT E u)⁻¹ ^ J.a.length := by
  have hη := etaT_pos hE hu1
  have h := norm_gloop_le_of_le_abs_im hM hη (le_of_eq (abs_zt_im hE hu1).symm) J hJ hlen
  refine h.trans ?_
  have hW : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
  have hWi : (d.W N : ℝ)⁻¹ ^ (J.a.length - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW)
  have h0 : 0 ≤ (etaT E u)⁻¹ ^ J.a.length := by positivity
  calc (etaT E u)⁻¹ ^ J.a.length * (d.W N : ℝ)⁻¹ ^ (J.a.length - 1)
      ≤ (etaT E u)⁻¹ ^ J.a.length * 1 := mul_le_mul_of_nonneg_left hWi h0
    _ = _ := mul_one _

/-- The crude `(L-K)` envelope for all lengths `ℓ ≤ n`. -/
theorem norm_lk_env {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {n : ℕ} {MK : ℝ}
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ n → ‖(band d).Kval E N u J‖ ≤ MK)
    (J : LoopIdx (ZMod (d.L N))) (hJ : J.WF) (hln : J.length ≤ n) :
    ‖gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J‖
      ≤ (d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n + MK := by
  have hη := etaT_pos hE hu1
  have hη1 : 1 ≤ (etaT E u)⁻¹ := (one_le_inv₀ hη).mpr (etaT_le_one hE hu0)
  have hG : ‖gloop (d.L N) (d.W N) M (zt E u) J‖
      ≤ (d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n := by
    rcases J with ⟨σ, a⟩
    cases a with
    | nil =>
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero (by simpa [LoopIdx.WF] using hJ)
      subst hσ
      have h0 : gloop (d.L N) (d.W N) M (zt E u) ⟨[], []⟩ = ((d.L N : ℂ) * (d.W N : ℂ)) := by
        simp [gloop, gloopProd, Matrix.trace_one]
      rw [h0]
      have : ‖((d.L N : ℂ) * (d.W N : ℂ))‖ = (d.L N : ℝ) * (d.W N : ℝ) := by
        rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
      rw [this]
      have : (0 : ℝ) ≤ (etaT E u)⁻¹ ^ n := by positivity
      linarith
    | cons b a =>
      have h1 := norm_gloop_crude d hE hM hu1 ⟨σ, b :: a⟩ hJ (by simp)
      have hle : (b :: a).length ≤ n := hln
      have h2 : (etaT E u)⁻¹ ^ (b :: a).length ≤ (etaT E u)⁻¹ ^ n := pow_le_pow_right₀ hη1 hle
      have : (0 : ℝ) ≤ (d.L N : ℝ) * (d.W N : ℝ) := by positivity
      simp only at h1
      linarith
  have hKJ := hK J hJ hln
  calc ‖gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J‖
      ≤ ‖gloop (d.L N) (d.W N) M (zt E u) J‖ + ‖(band d).Kval E N u J‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- Crude bound on `Ξ^{(L-K)}_m(M)` for `2 ≤ m ≤ n` (the `hΞm` row of (5.79)): it multiplies only
the `W^{-D}` tail. -/
theorem xiLKM_crude {E : ℝ} (hE : |E| < 2) {N : ℕ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hA1 : 1 ≤ (band d).scale E N u)
    {n : ℕ} {MK : ℝ}
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ n → ‖(band d).Kval E N u J‖ ≤ MK)
    {m : ℕ} (hmn : m ≤ n) :
    xiLKM d E N u M m ≤ ((d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n + MK)
      * (band d).scale E N u ^ n := by
  have hA0 : 0 ≤ (band d).scale E N u := le_trans zero_le_one hA1
  have hmax : lkMaxM d E N u M m ≤ (d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n + MK := by
    unfold lkMaxM
    refine ciSup_le fun q => ?_
    have hwf : (LoopData.idx q : LoopIdx (ZMod (d.L N))).WF := LoopData.idx_wf q
    have hlen : (LoopData.idx q : LoopIdx (ZMod (d.L N))).length ≤ n := by
      show (List.ofFn q.2).length ≤ n
      simp [hmn]
    exact norm_lk_env d hE hM hu0 hu1 hK _ hwf hlen
  have hpow : (band d).scale E N u ^ m ≤ (band d).scale E N u ^ n := pow_le_pow_right₀ hA1 hmn
  have h0 : 0 ≤ (d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n + MK :=
    le_trans (lkMaxM_nonneg d E N u M m) hmax
  unfold xiLKM
  calc lkMaxM d E N u M m * (band d).scale E N u ^ m
      ≤ ((d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n + MK) * (band d).scale E N u ^ m :=
        mul_le_mul_of_nonneg_right hmax (pow_nonneg hA0 _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow h0

end Crude514


section Classes514

variable (d : Dims)

/-- **`A_0` is in the kernel class on `{0 < τ}`**: `lkDecaySet` of `goodSet514(u_0)`, read as
(7.13) of the tensor `a ↦ (L-K)_{u_0,σ,a}`, at radius `ℓ_{u_0} W^{τ'} ≤ ℓ_{u_0} Kd`. -/
theorem kerClass_A0 {n : ℕ} [NeZero n] {E : ℝ} (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin n → Bool) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs Kd : ℝ}
    (hmem : H d s t K N 0 ω ∈ goodSet514 d E N (time s t K N 0) n ε₁ Λ Φ τ' D' ℓs)
    (hKd : (d.W N : ℝ) ^ τ' ≤ Kd) :
    KerClass (d.L N) (time s t K N) Kd false ((d.W N : ℝ) ^ (-D')) 0
      (AtrueN d E s t K N σ 0 ω) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hlk⟩, _⟩, _⟩ := hmem
  have hlk' : Decay.LoopDecay (d.L N) n ((band d).ell N (time s t K N 0) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N 0 ω)
        (zt E (time s t K N 0)) I - (band d).Kval E N (time s t K N 0) I) :=
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl
  have hfd := Decay.LoopDecay.fastDecay (d.L N) hlk' (List.ofFn σ) (by simp)
  refine ⟨?_, fun h => absurd h (by decide)⟩
  have hℓ0 : 0 ≤ ellHat (d.L N) ((time s t K N 0 : ℝ) : ℂ) := by
    unfold ellHat; exact le_min (by positivity) (Nat.cast_nonneg _)
  exact SumZeroDyn.FastDecay.mono (d.L N) hfd (mul_le_mul_of_nonneg_left hKd hℓ0) le_rfl

/-- The decay error of the drift tensor produced by `fastDecay_driftF_window` (with `δ = W^{-D'}`). -/
def driftErr514 (d : Dims) (N m : ℕ) (MK MD D' : ℝ) : ℝ :=
  (d.W N : ℝ) * ((m : ℝ) + 2) * ((d.L N : ℝ) * (MD * (d.W N : ℝ) ^ (-D')))
    + (m : ℝ) * (2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (MK + MD))
    + 2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * MD

/-- **The drift is in the kernel class at `u_{j+1}` on `{j < τ}`**: `fastDecay_driftF_window`
fed Lemma 5.9's decay of `K` (`K_decay_rpow`), of `L - K` and of `L` (`goodSet514(u_j)`), at radius
`ℓ_{u_j}·4W^{τ'} ≤ ℓ_{u_{j+1}}·4W^{τ'}`. -/
theorem kerClass_drift {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (j : ℕ) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ} (hτ' : 0 < τ')
    (hD' : 0 ≤ D') (hu0 : 0 ≤ time s t K N j) (hjj : time s t K N j ≤ time s t K N (j + 1))
    (hu1 : time s t K N (j + 1) < 1) (hreg : KDecayRegime d N (m + 2) τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    {MK MD : ℝ} (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hKb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖ ≤ MK)
    (hDb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) J
        - (band d).Kval E N (time s t K N j) J‖ ≤ MD) :
    KerClass (d.L N) (time s t K N) (4 * (d.W N : ℝ) ^ τ') false (driftErr514 d N m MK MD D')
      (j + 1) (DgridN d E s t K N σ j ω) := by
  have huj1 : time s t K N j < 1 := hjj.trans_lt hu1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hdec⟩, hlk⟩, _⟩, _⟩ := hmem
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hKd := K_decay_rpow d hE (m + 2) hτ' hD' hu0 huj1 hreg
  have hDd : Decay.LoopDecay (d.L N) (m + 2) ((band d).ell N (time s t K N j) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω)
        (zt E (time s t K N j)) I - (band d).Kval E N (time s t K N j) I) :=
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl
  have hLd : Decay.LoopDecay (d.L N) (m + 3) ((band d).ell N (time s t K N j) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω)
        (zt E (time s t K N j)) I) :=
    Decay.LoopDecay.mono (d.L N) hdec (by omega) le_rfl le_rfl
  have hfd := FastDecayFlow.fastDecay_driftF_window (band d) E N (time s t K N j)
    (d.three_le_L N) hu0 huj1 (H d s t K N j ω) σ (K := (d.W N : ℝ) ^ τ')
    (δ := (d.W N : ℝ) ^ (-D')) (δF := driftErr514 d N m MK MD D') hW1
    (Real.rpow_nonneg (by positivity) _) hMK hMD hKd hDd hLd hKb hDb le_rfl
  refine ⟨?_, fun h => absurd h (by decide)⟩
  have hℓ : ellHat (d.L N) ((time s t K N j : ℝ) : ℂ) ≤ ellHat (d.L N) ((time s t K N (j + 1) : ℝ) : ℂ) :=
    Step3.ellHat_mono hjj hu1
  exact SumZeroDyn.FastDecay.mono (d.L N) hfd
    (mul_le_mul_of_nonneg_right hℓ (by positivity)) le_rfl

/-- The pathwise drift bound of (5.78)–(5.80) at `u = u_j` on `{j < τ}`. -/
def dDr514 (d : Dims) (E : ℝ) (N n : ℕ) (u ε₁ τ' D' Φ CK B : ℝ) : ℝ :=
  (4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * (N : ℝ) ^ ε₁ * ((N : ℝ) ^ ε₁ * Φ)
      * ((band d).scale E N u)⁻¹ ^ n
    + (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁)
  + ∑ _lK ∈ Finset.Icc 3 n,
      (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * ((N : ℝ) ^ ε₁ * Φ)
          * ((band d).scale E N u)⁻¹ ^ n
        + 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * ((N : ℝ) ^ ε₁ * Φ))
  + (4 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * ((N : ℝ) ^ ε₁ * Φ)
      * ((band d).scale E N u)⁻¹ ^ n
    + (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * B)

/-- **h-drift (size)**: (5.78)–(5.80) on `H_j ∈ goodSet514(u_j)`. -/
theorem norm_DgridN_le {n : ℕ} [NeZero n] (hn3 : 3 ≤ n) {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ)
    (K : ℕ → ℕ) (N : ℕ) (σ : Fin n → Bool) (j : ℕ) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ}
    (hτ' : 0 < τ') (hD' : 0 ≤ D') (hΦ0 : 0 ≤ Φ) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N j < 1) (hA1 : 1 ≤ (band d).scale E N (time s t K N j))
    (hreg : KDecayRegime d N n τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) n ε₁ Λ Φ τ' D' ℓs)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(band d).Kval E N (time s t K N j) J‖
        ≤ CK * ((band d).scale E N (time s t K N j))⁻¹ ^ (J.length - 1))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m, 2 ≤ m → m ≤ n → xiLKM d E N (time s t K N j) (H d s t K N j ω) m ≤ B)
    (b : LoopArg (d.L N) n) :
    ‖DgridN d E s t K N σ j ω b‖ ≤ dDr514 d E N n (time s t K N j) ε₁ τ' D' Φ CK B := by
  set u := time s t K N j with hu
  set M := H d s t K N j ω with hM
  have hmem' := hmem
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩ := hmem
  obtain ⟨hdec, hlk⟩ := goodSet514_decay d E N u n ε₁ Λ Φ τ' D' ℓs hmem'
  have hNe : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set I : LoopIdx (ZMod (d.L N)) := ⟨List.ofFn σ, List.ofFn b⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hIlen : I.length = n := by simp [hI, LoopIdx.length]
  -- the three pieces
  have heG := norm_eGterm_le d hE N hu0 hu1 hτ' hA1 M hdec (Ξ1 := (N : ℝ) ^ ε₁)
    (Φ := (N : ℝ) ^ ε₁ * Φ) hNe (mul_nonneg hNe hΦ0) h5 h4 I hIwf hIlen
  have hprod : ∀ m, 2 ≤ m → m ≤ n →
      xiLKM d E N u M m * xiLKM d E N u M (n - m + 2) * ((band d).scale E N u)⁻¹
        ≤ (N : ℝ) ^ ε₁ * Φ := by
    intro m hm1 hm2
    have := h3 m hm1 hm2
    rwa [div_eq_mul_inv] at this
  have hpB := norm_primBil_le514 d hE N hu0 hu1 hτ' hA1 (n := n) (by omega) M hlk
    (Φ := (N : ℝ) ^ ε₁ * Φ) (mul_nonneg hNe hΦ0) hB0 hprod hB I hIwf hIlen
  have hcoup : ∀ lK ∈ Finset.Icc 3 n,
      ‖Decay.couplingLen (d.L N) (d.W N) lK ((band d).Kval E N u)
          (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J) I‖
        ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹
              * ((N : ℝ) ^ ε₁ * Φ) * ((band d).scale E N u)⁻¹ ^ n
          + 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D')
              * ((N : ℝ) ^ ε₁ * Φ) := by
    intro lK hlK
    rw [Finset.mem_Icc] at hlK
    have h := norm_KsimLK_le d hE N hu0 hu1 hτ' hD' hA1 hlK.1 hlK.2 hreg hCK0 hK M I hIwf hIlen
    have hX := h2 (n - lK + 2) (by omega) (by omega)
    have hX0 : 0 ≤ xiLKM d E N u M (n - lK + 2) :=
      xiLKM_nonneg d E N u (le_trans zero_le_one hA1) M _
    have hc1 : 0 ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ := by
      have := etaT_pos hE hu1
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
      positivity
    have hc2 : 0 ≤ ((band d).scale E N u)⁻¹ ^ n := by
      have : 0 ≤ (band d).scale E N u := le_trans zero_le_one hA1
      positivity
    have hc3 : 0 ≤ 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
      positivity
    refine h.trans ?_
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hc1) hc2
    have e2 := mul_le_mul_of_nonneg_left hX hc3
    linarith
  have hsum := (norm_sum_le (Finset.Icc 3 n) (fun lK => Decay.couplingLen (d.L N) (d.W N) lK
      (fun I => (band d).Kval E N u I)
      (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) I)).trans
    (Finset.sum_le_sum hcoup)
  have hsplit : DgridN d E s t K N σ j ω b
      = eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
        + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (d.L N) (d.W N) lK
            (fun I => (band d).Kval E N u I)
            (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) I)
        + primBil (d.L N) (d.W N)
            (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J)
            (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J) I := rfl
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  unfold dDr514
  have heG' : ‖eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I‖
      ≤ 4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * (N : ℝ) ^ ε₁
            * ((N : ℝ) ^ ε₁ * Φ) * ((band d).scale E N u)⁻¹ ^ n
        + (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁ := heG
  exact add_le_add (add_le_add heG' hsum) hpB

end Classes514


section QV514

variable (d : Dims)

/-- The sub-Gaussian constant of the `j`-th propagated increment towards the target `u_k`:
`Δ · qvBdNonAlt(u_{j+1}, u_k)` ((5.105) at the shifted time). -/
def cQV514 (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N n : ℕ) (τ' D'' Φq : ℝ) (k : ℕ)
    (_a : LoopArg (d.L N) n) (j : ℕ) : ℝ≥0 :=
  (step s t K N * qvBdNonAlt d N E n (time s t K N (j + 1)) (time s t K N k) τ' D'' Φq).toNNReal

theorem qvBdNonAlt_pos {E : ℝ} (hE : |E| < 2) {N n : ℕ} (hn : 1 ≤ n) {v w τ D Φ : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) (hΦ : 0 ≤ Φ) :
    0 < qvBdNonAlt d N E n v w τ D Φ := by
  unfold qvBdNonAlt
  have hv1 : v < 1 := hvw.trans_lt hw1
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hL : (0 : ℝ) < d.L N := by have := d.three_le_L N; exact_mod_cast (by omega : 0 < d.L N)
  have hWD : (0 : ℝ) < (d.W N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW _
  have hWτ : (0 : ℝ) < (d.W N : ℝ) ^ τ := Real.rpow_pos_of_pos hW _
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hEE : 0 < eeHermErr d N n D := by
    unfold eeHermErr
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hr : 0 < (1 - v) / (1 - w) := div_pos (by linarith) (by linarith)
  have hc := cKerShort_nonneg (n + n) (Real.sqrt_nonneg (min (2 - |E|) 1))
  have hℓv : 0 < ellHat (d.L N) ((v : ℝ) : ℂ) :=
    Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hv1
  have hℓw : 0 < ellHat (d.L N) ((w : ℝ) : ℂ) :=
    Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hw1
  have hAt : 0 ≤ ((band d).scale E N w)⁻¹ ^ (2 * n) := by
    have := (band d).scale_pos' hE N (hv0.trans hvw) hw1
    positivity
  have h1v : 0 < 1 - v := by linarith
  have h1w : 0 < 1 - w := by linarith
  have hfirst : 0 ≤ cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ) ^ (n + n)
      * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * Φ * (etaT E v)⁻¹
          * ((band d).scale E N w)⁻¹ ^ (2 * n)
        + ((1 - v) * ellHat (d.L N) (v : ℂ) / ((1 - w) * ellHat (d.L N) (w : ℂ))) ^ (n + n)
          * eeHermErr d N n D) := by positivity
  have hsecond : 0 < ((1 - v) / (1 - w)) ^ (n + n) * eeHermErr d N n D := by positivity
  linarith

/-- **h-qv, sharp** (`hqv_of_vC` + `step_mul_vC_AbC_le_nonAlt`), with the
time shift `u_j → u_{j+1}` discharged by `xiLM_shift_le`/`decaySet_shift`. -/
theorem hqv514 {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin n → Bool) {k0 : Fin n} (hk0 : σ k0 = σ (k0 + 1)) (hs0 : 0 ≤ s N)
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0) (τ : Ωg d → ℕ)
    (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    {ε₁ Λ Φ τ' D' D'' ℓs Φq : ℝ} (hτ' : 0 ≤ τ')
    (hmemτ : ∀ ω j, j < τ ω →
      H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) n ε₁ Λ Φ τ' D' ℓs)
    (hA1 : ∀ j ≤ K N, 1 ≤ (band d).scale E N (time s t K N j))
    (hshiftΞ : ∀ j < K N, (N : ℝ) ^ ε₁ * Λ
      + ((2 * n + 2 : ℕ) : ℝ) * ((etaT E (time s t K N (j + 1)))⁻¹ ^ (2 * n + 2 + 1)
          * (time s t K N (j + 1) - time s t K N j))
        * ((band d).scale E N (time s t K N j)) ^ (2 * n + 2 - 1) ≤ Φq)
    (hshiftD : ∀ j < K N, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * n + 2 →
      (d.W N : ℝ) ^ (-D') + (ℓ : ℝ) * ((etaT E (time s t K N (j + 1)))⁻¹ ^ (ℓ + 1)
          * (time s t K N (j + 1) - time s t K N j)) ≤ (d.W N : ℝ) ^ (-D'')) :
    ∀ k ≤ K N, ∀ (a : LoopArg (d.L N) n) (j : ℕ), j < k →
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (j + 1) : ℂ)
            (time s t K N k : ℂ) (gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω') a) ω).re)
        (cQV514 d E s t K N n τ' D'' Φq k a j) (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (j + 1) : ℂ)
            (time s t K N k : ℂ) (gridZC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω') a) ω).im)
        (cQV514 d E s t K N n τ' D'' Φq k a j) (Pg d) := by
  have hΔ : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst hi
  refine hqv_of_vC s t K N n (xiOf (mSigma E) σ) τ hτmeas (gridΦG d E s t K N σ)
    (gridΦG_testFun d hE hst ht1 hK0 (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) σ) hΔ
    (cQV514 d E s t K N n τ' D'' Φq) ?_
  intro k hk a j hj ω hjτ
  have hjK : j < K N := lt_of_lt_of_le hj hk
  have hj1 := hmem (j + 1) (by omega)
  have hj0 := hmem j hjK.le
  have hkk := hmem k hk
  have hjj : time s t K N j ≤ time s t K N (j + 1) := by
    unfold time; push_cast; nlinarith [hΔ]
  have hj1k : time s t K N (j + 1) ≤ time s t K N k := by
    unfold time
    have : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    nlinarith [hΔ]
  have hgood := hmemτ ω j hjτ
  have hgood' := hgood
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hΞ0, _⟩, _⟩, _⟩, _⟩, hdec0⟩, _⟩, _⟩, _⟩ := hgood
  have hHerm := H_isHermitian d s t K N j ω
  have hsh := xiLM_shift_le d hE hHerm (hs0.trans hj0.1) hjj (hj1.2.trans_lt ht1)
    (m := 2 * n + 2) (by omega)
  have hΞ : loopXi (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N (j + 1)))
      ((band d).scale E N (time s t K N (j + 1))) (2 * n + 2) ≤ Φq := by
    show xiLM d E N (time s t K N (j + 1)) (H d s t K N j ω) (2 * n + 2) ≤ Φq
    have h0 : xiLM d E N (time s t K N j) (H d s t K N j ω) (2 * n + 2) ≤ (N : ℝ) ^ ε₁ * Λ := hΞ0
    have := hshiftΞ j hjK
    linarith
  have hdec := decaySet_shift d hE hHerm (hs0.trans hj0.1) hjj (hj1.2.trans_lt ht1) hdec0
    (hshiftD j hjK)
  have h := step_mul_vC_AbC_le_nonAlt s t K j hΔ hE hk0 (hs0.trans hj1.1) hj1k
    (hkk.2.trans_lt ht1) hτ'
    (fun b => (band d).Kval E N (time s t K N (j + 1)) (toIdx σ b)) ω (hA1 (j + 1) (by omega))
    hΞ hdec a
  refine h.trans ?_
  exact Real.le_coe_toNNReal _

/-- `hc_pos` for `cQV514`: strictly positive for `Δ > 0`. -/
theorem cQV514_sum_pos {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) {τ' D'' Φq : ℝ} (hΦq : 0 ≤ Φq) :
    ∀ k, 1 ≤ k → k ≤ K N → ∀ a : LoopArg (d.L N) n,
      0 < ∑ j ∈ Finset.range k, (cQV514 d E s t K N n τ' D'' Φq k a j : ℝ) := by
  intro k hk1 hk a
  have hK : 0 < K N := lt_of_lt_of_le hk1 hk
  have hΔ : 0 < step s t K N := div_pos (by linarith) (by exact_mod_cast hK)
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst.le hi
  have hterm : ∀ j ∈ Finset.range k, 0 ≤ (cQV514 d E s t K N n τ' D'' Φq k a j : ℝ) :=
    fun j _ => NNReal.coe_nonneg _
  have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm h0)
  unfold cQV514
  rw [Real.coe_toNNReal _ (le_of_lt ?_)]
  all_goals
    have h1 := hmem 1 (by omega)
    have hk' := hmem k hk
    have h1k : time s t K N (0 + 1) ≤ time s t K N k := by
      unfold time
      have : ((0 + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      nlinarith [hΔ.le]
    exact mul_pos hΔ (qvBdNonAlt_pos d hE (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
      (hs0.trans h1.1) h1k (hk'.2.trans_lt ht1) hΦq)

end QV514


section Y514

variable (d : Dims)

theorem integrable_incr_comp (j : ℕ) {f : Ω d → ℝ} (hint : Integrable f (P d)) :
    Integrable (fun ω : Ωg d => f (ω (j + 1))) (Pg d) := by
  have h : Integrable f ((Pg d).map (fun ω : Ωg d => ω (j + 1))) := by rw [map_incr d j]; exact hint
  exact h.comp_measurable (measurable_pi_apply (j + 1))

theorem integral_incr_comp (j : ℕ) {f : Ω d → ℝ} (hf : Measurable f) :
    ∫ ω, f (ω (j + 1)) ∂(Pg d) = ∫ x, f x ∂(P d) := by
  rw [← map_incr d j, integral_map (measurable_pi_apply (j + 1)).aemeasurable
    hf.aestronglyMeasurable]

/-- `E[f(X_{j+1}) | F_j] = E f(X)`: the increment is independent of `F_j` (freezing with a constant). -/
theorem condExp_incr_comp (j : ℕ) {f : Ω d → ℝ} (hf : Measurable f) (hint : Integrable f (P d)) :
    (Pg d)[fun ω => f (ω (j + 1)) | filt d j] =ᵐ[Pg d] fun _ => ∫ x, f x ∂(P d) := by
  have h := condExp_freeze (d := d) (β := ℝ) j (Y := fun _ => (0 : ℝ)) measurable_const
    (F := fun _ x => f x) (hf.comp measurable_snd) (integrable_incr_comp d j hint)
  simpa using h

/-- `(‖X‖² + m)^2` is integrable. -/
theorem integrable_sq_normSq_add (N : ℕ) (m : ℝ) :
    Integrable (fun x : Ω d => (‖Xmat d N x‖ ^ 2 + m) ^ 2) (P d) := by
  have h4 : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ (2 * 2)) (P d) :=
    integrable_norm_Xmat_pow d N 2
  have h2 : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ (2 * 1)) (P d) :=
    integrable_norm_Xmat_pow d N 1
  have heq : (fun x : Ω d => (‖Xmat d N x‖ ^ 2 + m) ^ 2)
      = fun x => ‖Xmat d N x‖ ^ (2 * 2) + 2 * m * ‖Xmat d N x‖ ^ (2 * 1) + m ^ 2 := by
    funext x; ring
  rw [heq]
  exact (h4.add (h2.const_mul (2 * m))).add (integrable_const _)

/-- `(‖X‖² + m)^4` is integrable. -/
theorem integrable_pow4_normSq_add (N : ℕ) (m : ℝ) :
    Integrable (fun x : Ω d => (‖Xmat d N x‖ ^ 2 + m) ^ 4) (P d) := by
  have heq : (fun x : Ω d => (‖Xmat d N x‖ ^ 2 + m) ^ 4)
      = fun x => ‖Xmat d N x‖ ^ (2 * 4) + 4 * m * ‖Xmat d N x‖ ^ (2 * 3)
          + 6 * m ^ 2 * ‖Xmat d N x‖ ^ (2 * 2) + 4 * m ^ 3 * ‖Xmat d N x‖ ^ (2 * 1) + m ^ 4 := by
    funext x; ring
  rw [heq]
  exact ((((integrable_norm_Xmat_pow d N 4).add ((integrable_norm_Xmat_pow d N 3).const_mul _)).add
    ((integrable_norm_Xmat_pow d N 2).const_mul _)).add
    ((integrable_norm_Xmat_pow d N 1).const_mul _)).add (integrable_const _)

theorem measurable_normSq_add_pow (N : ℕ) (m : ℝ) (p : ℕ) :
    Measurable (fun x : Ω d => (‖Xmat d N x‖ ^ 2 + m) ^ p) :=
  (((measurable_norm_Xmat d N).pow_const 2).add_const m).pow_const p

/-- `stepYC` is `filt (j+1)`-measurable. -/
theorem measurable_stepYC_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) :
    Measurable[filt d (j + 1)] (fun ω => stepYC d s t K N j n Φ U b ω) := by
  have hH : Measurable[filt d (j + 1)] (fun ω => H d s t K N (j + 1) ω) :=
    H_measurable_filt d s t K N (j + 1)
  have h1 : Measurable[filt d (j + 1)] (fun ω =>
      ∑ a : LoopArg (d.L N) n, U b a * Φ a (H d s t K N (j + 1) ω)) :=
    Finset.measurable_sum _ fun a _ =>
      ((hΦ a).contDiff.continuous.measurable.comp hH).const_mul _
  have h2 : Measurable[filt d (j + 1)] ((Pg d)[fun ω' => ∑ a : LoopArg (d.L N) n,
      U b a * Φ a (H d s t K N (j + 1) ω') | filt d j]) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have h3 := measurable_stepZC_filt s t K N j n hΦ U b
  unfold stepYC stepXiC
  exact (h1.sub h2).sub h3

/-- **The pathwise `Y` bound with the frozen conditional moment**:
`‖Y‖ ≤ R (C₂/2) Δ (‖X_{j+1}‖² + E‖X‖²)` a.e., for any row bound `Σ_a ‖U(b,a)‖ ≤ R`. -/
theorem norm_stepYC_le_incr (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n) {R : ℝ}
    (hR : ∑ a, ‖U b a‖ ≤ R) :
    ∀ᵐ ω ∂(Pg d), ‖stepYC d s t K N j n Φ U b ω‖
      ≤ R * (C₂ / 2 * step s t K N)
          * (‖Xmat d N (ω (j + 1))‖ ^ 2 + ∫ x, ‖Xmat d N x‖ ^ 2 ∂(P d)) := by
  have hC0 : 0 ≤ C₂ := (norm_nonneg (fderiv ℝ (fderiv ℝ (Φ b)) 0)).trans (hC₂ b 0)
  have hY := stepYC_norm_le_ae d s t K N j n hΦ hC₂ hΔ U b
    (integrable_stepZC_re_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
    (integrable_stepZC_im_of_testFun d s t K N j n hΦ hC₂ hΔ U b)
  set c0 : ℝ := (∑ a, ‖U b a‖) * (C₂ / 2 * step s t K N) with hc0
  have hfm : Measurable (fun x : Ω d => c0 * ‖Xmat d N x‖ ^ 2) :=
    ((measurable_norm_Xmat d N).pow_const 2).const_mul _
  have hfi : Integrable (fun x : Ω d => c0 * ‖Xmat d N x‖ ^ 2) (P d) :=
    (by simpa using integrable_norm_Xmat_pow d N 1 : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ 2) (P d)).const_mul _
  have hcond := condExp_incr_comp d j hfm hfi
  have hc0R : c0 ≤ R * (C₂ / 2 * step s t K N) :=
    mul_le_mul_of_nonneg_right hR (by positivity)
  have hc00 : 0 ≤ c0 := by rw [hc0]; exact mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
  filter_upwards [hY, hcond] with ω h1 h2
  rw [h2, integral_const_mul] at h1
  have hX0 : 0 ≤ ‖Xmat d N (ω (j + 1))‖ ^ 2 + ∫ x, ‖Xmat d N x‖ ^ 2 ∂(P d) :=
    add_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  calc ‖stepYC d s t K N j n Φ U b ω‖
      ≤ c0 * ‖Xmat d N (ω (j + 1))‖ ^ 2 + c0 * ∫ x, ‖Xmat d N x‖ ^ 2 ∂(P d) := h1
    _ = c0 * (‖Xmat d N (ω (j + 1))‖ ^ 2 + ∫ x, ‖Xmat d N x‖ ^ 2 ∂(P d)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc0R hX0

/-- Real/imaginary parts of the stopped `stepYC` have conditional mean zero. -/
theorem condExp_indicator_stepYC_reim (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j n : ℕ)
    {Φ : LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    {C₂ : ℝ} (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
    (U : LoopArg (d.L N) n → LoopArg (d.L N) n → ℂ) (b : LoopArg (d.L N) n)
    {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S) :
    (Pg d)[fun ω => (S.indicator (fun ω => stepYC d s t K N j n Φ U b ω) ω).re | filt d j]
        =ᵐ[Pg d] 0
      ∧ (Pg d)[fun ω => (S.indicator (fun ω => stepYC d s t K N j n Φ U b ω) ω).im | filt d j]
        =ᵐ[Pg d] 0 := by
  have hZre := integrable_stepZC_re_of_testFun d s t K N j n hΦ hC₂ hΔ U b
  have hZim := integrable_stepZC_im_of_testFun d s t K N j n hΦ hC₂ hΔ U b
  have hdec := stepDecompC d s t K N j n hΦ hC₂ hΔ U b hZre hZim
  have hmean := hdec.2.2.2
  have hint : Integrable (fun ω => stepYC d s t K N j n Φ U b ω) (Pg d) := by
    have hZ := integrable_stepZC_of_testFun d s t K N j n hΦ hC₂ hΔ U b
    have hXi : Integrable (fun ω => stepXiC d s t K N j n Φ U b ω) (Pg d) := by
      have hg : Integrable (fun ω : Ωg d => ∑ a : LoopArg (d.L N) n,
          U b a * Φ a (H d s t K N (j + 1) ω)) (Pg d) :=
        integrable_finsetSum _ fun a _ =>
          (integrable_Phi_H d s t K N (j + 1) (hΦ a)).const_mul (U b a)
      exact hg.sub integrable_condExp
    have heq : (fun ω => stepYC d s t K N j n Φ U b ω)
        = fun ω => stepXiC d s t K N j n Φ U b ω - stepZC d s t K N j n Φ U b ω := rfl
    rw [heq]; exact hXi.sub hZ
  constructor
  · have hfun : (fun ω => (S.indicator (fun ω => stepYC d s t K N j n Φ U b ω) ω).re)
        = S.indicator (fun ω => (stepYC d s t K N j n Φ U b ω).re) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have h1 := condExp_indicator (m := filt d j)
      (f := fun ω => (stepYC d s t K N j n Φ U b ω).re) hint.re hS
    have h2 : (Pg d)[fun ω => (stepYC d s t K N j n Φ U b ω).re | filt d j] =ᵐ[Pg d] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint
        Complex.reCLM).symm
      have hc' : (Pg d)[fun ω => (stepYC d s t K N j n Φ U b ω).re | filt d j]
          =ᵐ[Pg d] fun ω => ((Pg d)[fun ω => stepYC d s t K N j n Φ U b ω | filt d j] ω).re := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', hmean] with ω h1 h2
      rw [h1]
      have : (Pg d)[fun ω => stepYC d s t K N j n Φ U b ω | filt d j] ω = 0 := h2
      rw [this]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl
  · have hfun : (fun ω => (S.indicator (fun ω => stepYC d s t K N j n Φ U b ω) ω).im)
        = S.indicator (fun ω => (stepYC d s t K N j n Φ U b ω).im) := by
      funext ω; by_cases h : ω ∈ S
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hfun]
    have h1 := condExp_indicator (m := filt d j)
      (f := fun ω => (stepYC d s t K N j n Φ U b ω).im) hint.im hS
    have h2 : (Pg d)[fun ω => (stepYC d s t K N j n Φ U b ω).im | filt d j] =ᵐ[Pg d] 0 := by
      have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint
        Complex.imCLM).symm
      have hc' : (Pg d)[fun ω => (stepYC d s t K N j n Φ U b ω).im | filt d j]
          =ᵐ[Pg d] fun ω => ((Pg d)[fun ω => stepYC d s t K N j n Φ U b ω | filt d j] ω).im := by
        simpa [Function.comp_def] using hc
      filter_upwards [hc', hmean] with ω h1 h2
      rw [h1]
      have : (Pg d)[fun ω => stepYC d s t K N j n Φ U b ω | filt d j] ω = 0 := h2
      rw [this]; simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1]
    by_cases h : ω ∈ S
    · rw [Set.indicator_of_mem h, hω2]
    · rw [Set.indicator_of_notMem h]; rfl

end Y514


section Y514b

variable (d : Dims)

/-- **Moments of a real process dominated by `c(‖X_{j+1}‖² + m)`**: fourth power integrable,
conditional second moment `≤ c² E(‖X‖²+m)²`, fourth moment `≤ c⁴ E(‖X‖²+m)⁴`. -/
theorem moments_of_dom_incr {N j : ℕ} {W : Ωg d → ℝ} (hWm : Measurable W) {c m : ℝ}
    (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hdom : ∀ᵐ ω ∂(Pg d), |W ω| ≤ c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m)) :
    Integrable (fun ω => W ω ^ 4) (Pg d)
      ∧ (Pg d)[fun ω => W ω ^ 2 | filt d j]
          ≤ᵐ[Pg d] (fun _ => c ^ 2 * (∫ x, (‖Xmat d N x‖ ^ 2 + m) ^ 2 ∂(P d)))
      ∧ (∫ ω, W ω ^ 4 ∂(Pg d)) ≤ c ^ 4 * (∫ x, (‖Xmat d N x‖ ^ 2 + m) ^ 4 ∂(P d)) := by
  set f2 : Ω d → ℝ := fun x => c ^ 2 * (‖Xmat d N x‖ ^ 2 + m) ^ 2 with hf2
  set f4 : Ω d → ℝ := fun x => c ^ 4 * (‖Xmat d N x‖ ^ 2 + m) ^ 4 with hf4
  have hf2m : Measurable f2 := (measurable_normSq_add_pow d N m 2).const_mul _
  have hf4m : Measurable f4 := (measurable_normSq_add_pow d N m 4).const_mul _
  have hf2i : Integrable f2 (P d) := (integrable_sq_normSq_add d N m).const_mul _
  have hf4i : Integrable f4 (P d) := (integrable_pow4_normSq_add d N m).const_mul _
  have hg2i := integrable_incr_comp d j hf2i
  have hg4i := integrable_incr_comp d j hf4i
  have hW2 : ∀ᵐ ω ∂(Pg d), W ω ^ 2 ≤ f2 (ω (j + 1)) := by
    filter_upwards [hdom] with ω hω
    have h0 : 0 ≤ c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m) := by positivity
    have := pow_le_pow_left₀ (abs_nonneg _) hω 2
    rw [sq_abs] at this
    simp only [hf2]
    nlinarith
  have hW4 : ∀ᵐ ω ∂(Pg d), W ω ^ 4 ≤ f4 (ω (j + 1)) := by
    filter_upwards [hdom] with ω hω
    have h0 : 0 ≤ c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m) := by positivity
    have := pow_le_pow_left₀ (abs_nonneg _) hω 4
    rw [show |W ω| ^ 4 = W ω ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
      at this
    simp only [hf4]
    calc W ω ^ 4 ≤ (c * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m)) ^ 4 := this
      _ = c ^ 4 * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m) ^ 4 := by ring
  have hW2i : Integrable (fun ω => W ω ^ 2) (Pg d) :=
    hg2i.mono' (hWm.pow_const 2).aestronglyMeasurable (by
      filter_upwards [hW2] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hω)
  have hW4i : Integrable (fun ω => W ω ^ 4) (Pg d) :=
    hg4i.mono' (hWm.pow_const 4).aestronglyMeasurable (by
      filter_upwards [hW4] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hω)
  refine ⟨hW4i, ?_, ?_⟩
  · have hmono := condExp_mono (m := filt d j) hW2i hg2i hW2
    have hfr := condExp_incr_comp d j hf2m hf2i
    filter_upwards [hmono, hfr] with ω h1 h2
    rw [h2] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hf2, integral_const_mul]
  · have hmono := integral_mono_ae hW4i hg4i hW4
    rw [integral_incr_comp d j hf4m, hf4, integral_const_mul] at hmono
    exact hmono

/-- **Row sum of the complex kernel matrix**: `Σ_a ‖U_{v,w}(b,a)‖ ≤ (1+(1-w)⁻¹)^n`. -/
theorem sum_norm_ukerMatC_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {n : ℕ} {ξ : Fin n → ℂ}
    (hξ : ∀ i, ‖ξ i‖ ≤ 1) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (b : LoopArg L n) :
    ∑ a : LoopArg L n, ‖ukerMatC ξ v w b a‖ ≤ (1 + (1 - w)⁻¹) ^ n := by
  have hpos : 0 < 1 - w := by linarith
  have hb : ∀ p, ‖((w : ℝ) : ℂ) * ξ p‖ ≤ w := by
    intro p
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    nlinarith [hξ p, norm_nonneg (ξ p)]
  have ht : ∀ p, ‖((w : ℝ) : ℂ) * ξ p‖ < 1 := fun p => (hb p).trans_lt hw1
  have hC : ∀ p, 1 + ‖(((v : ℝ) : ℂ) - ((w : ℝ) : ℂ)) * ξ p‖
      * (1 - ‖((w : ℝ) : ℂ) * ξ p‖)⁻¹ ≤ 1 + (1 - w)⁻¹ := by
    intro p
    have hst : |v - w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have ha : ‖(((v : ℝ) : ℂ) - ((w : ℝ) : ℂ)) * ξ p‖ ≤ 1 := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [hξ p, norm_nonneg (ξ p), abs_nonneg (v - w)]
    have hinv : (1 - ‖((w : ℝ) : ℂ) * ξ p‖)⁻¹ ≤ (1 - w)⁻¹ :=
      inv_anti₀ hpos (by linarith [hb p])
    have hinv0 : 0 ≤ (1 - ‖((w : ℝ) : ℂ) * ξ p‖)⁻¹ := inv_nonneg.mpr (by linarith [hb p])
    have := mul_le_mul ha hinv hinv0 zero_le_one
    linarith
  have heq : (∑ a : LoopArg L n, ‖ukerMatC ξ v w b a‖)
      = ∏ i : Fin n, ∑ c : ZMod L, ‖edgeKer L (ξ i) (v : ℂ) (w : ℂ) (b i) c‖ := by
    rw [← sum_prod_pi L (fun i c => ‖edgeKer L (ξ i) (v : ℂ) (w : ℂ) (b i) c‖)]
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold ukerMatC
    rw [norm_prod]
  rw [heq]
  calc (∏ i : Fin n, ∑ c : ZMod L, ‖edgeKer L (ξ i) (v : ℂ) (w : ℂ) (b i) c‖)
      ≤ ∏ _i : Fin n, (1 + (1 - w)⁻¹) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (fun i _ => (sum_norm_edgeKer_row_le L hL (ht i) (b i)).trans (hC i))
    _ = (1 + (1 - w)⁻¹) ^ n := by simp

end Y514b


section Y514c

variable (d : Dims)

/-- `gridYC i` is `filt d i`-strongly measurable (`hYmeas`). -/
theorem stronglyMeasurable_gridYC (s t : ℕ → ℝ) (Kf : ℕ → ℕ) (N n : ℕ)
    (Φ : ℕ → LoopArg (d.L N) n → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (hΦ : ∀ i, 1 ≤ i → i ≤ Kf N → ∀ a, TestFun d N (Φ i a)) (i : ℕ) :
    StronglyMeasurable[filt d i] (gridYC d s t Kf N n Φ i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ Kf N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hfun : gridYC d s t Kf N n Φ (j + 1)
        = fun ω a => stepYC d s t Kf N j n (Φ (j + 1)) (gridDeltaC (d.L N) n) a ω := by
      funext ω a
      unfold gridYC
      simp only [hi, and_self, ↓reduceIte, Nat.add_sub_cancel]
    rw [hfun]
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact measurable_stepYC_filt d s t Kf N j n (hΦ (j + 1) hi.1 hi.2) _ a
  · have : gridYC d s t Kf N n Φ i = fun _ _ => 0 := by
      funext ω a
      unfold gridYC
      simp only [hi, ↓reduceIte]
    rw [this]
    exact stronglyMeasurable_const

/-- The uniform second-derivative constant of the label family at `η` (`ΦgridG_bdd2`). -/
def C2g (d : Dims) (N n : ℕ) (η : ℝ) : ℝ :=
  (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n)

/-- `c/Δ` in the pathwise `Y` bound: coarse row sum times `C₂/2`. -/
def yConst (d : Dims) (N n : ℕ) (T η : ℝ) : ℝ := (1 + (1 - T)⁻¹) ^ n * (C2g d N n η / 2)

/-- The conditional second-moment bound `v_j` of the propagated, stopped `Y`. -/
def vY514 (d : Dims) (N n : ℕ) (T η Δ : ℝ) : ℝ :=
  (yConst d N n T η * Δ) ^ 2
    * ∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 2 ∂(P d)

/-- The fourth-moment bound `w_j` of the propagated, stopped `Y`. -/
def wY514 (d : Dims) (N n : ℕ) (T η Δ : ℝ) : ℝ :=
  (yConst d N n T η * Δ) ^ 4
    * ∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 4 ∂(P d)

set_option maxHeartbeats 1600000 in
/-- **h-Y′**: the eight moment hypotheses of `GridAssemblyHypPW` for the stopped,
propagated second-order increments `Y = gridYC`, with the explicit `v = vY514`, `w = wY514`. -/
theorem Y_fields514 {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0)
    (σ : Fin n → Bool) (τ : Ωg d → ℕ) (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    (k : ℕ) (hk : k ≤ K N) (b : LoopArg (d.L N) n) (j : ℕ) (hj : j < k) :
    let Y := gridYC d s t K N n (gridΦG d E s t K N σ)
    let u := time s t K N
    let ξ := xiOf (mSigma E) σ
    let V := vY514 d N n (t N) (etaT E (t N)) (step s t K N)
    let W := wY514 d N n (t N) (etaT E (t N)) (step s t K N)
    (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re | filt d j] =ᵐ[Pg d] 0
    ∧ (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im | filt d j] =ᵐ[Pg d] 0
    ∧ Integrable (fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re ^ 4) (Pg d)
    ∧ Integrable (fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im ^ 4) (Pg d)
    ∧ (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re ^ 2 | filt d j]
        ≤ᵐ[Pg d] (fun _ => V)
    ∧ (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im ^ 2 | filt d j]
        ≤ᵐ[Pg d] (fun _ => V)
    ∧ (∫ ω, (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re ^ 4 ∂(Pg d)) ≤ W
    ∧ (∫ ω, (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im ^ 4 ∂(Pg d)) ≤ W := by
  intro Y u ξ V W
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hΔ : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hjK : j < K N := lt_of_lt_of_le hj hk
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst hi
  have hj1 := hmem (j + 1) (by omega)
  have hkk := hmem k hk
  set Φ := gridΦG d E s t K N σ (j + 1) with hΦdef
  have hΦ : ∀ a, TestFun d N (Φ a) :=
    gridΦG_testFun d hE hst ht1 hK0 hn1 σ (j + 1) (by omega) (by omega)
  have hη : 0 < etaT E (t N) := etaT_pos hE ht1
  have hzη : etaT E (t N) ≤ |(zt E (time s t K N (j + 1))).im| := by
    rw [abs_zt_im hE (hj1.2.trans_lt ht1)]; exact etaT_anti hE hj1.2
  have hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C2g d N n (etaT E (t N)) :=
    fun a A => ΦgridG_bdd2 (band d) hE N (hj1.2.trans_lt ht1) hη hzη σ a A
  set U := ukerMatC (L := d.L N) ξ (time s t K N (j + 1)) (time s t K N k) with hUdef
  have hR : ∑ a, ‖U b a‖ ≤ (1 + (1 - t N)⁻¹) ^ n := by
    refine (sum_norm_ukerMatC_le (d.three_le_L N) (fun i => (norm_xiOf_mSigma hE.le σ i).le)
      (hs0.trans hj1.1) (hj1.2.trans_lt ht1) (hs0.trans hkk.1) (hkk.2.trans_lt ht1) b).trans ?_
    have h1 : 0 < 1 - time s t K N k := by linarith [hkk.2]
    have h2 : (1 - time s t K N k)⁻¹ ≤ (1 - t N)⁻¹ := inv_anti₀ (by linarith) (by linarith [hkk.2])
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  have hS : MeasurableSet[filt d j] {ω | j < τ ω} := hτmeas j
  -- the stopped edge is a.e. the stopped `stepYC` with the kernel folded in
  have hYeq : ∀ ω, Y (j + 1) ω
      = fun a => stepYC d s t K N j n Φ (gridDeltaC (d.L N) n) a ω := by
    intro ω; funext a
    show gridYC d s t K N n (gridΦG d E s t K N σ) (j + 1) ω a = _
    unfold gridYC
    have hc : 1 ≤ j + 1 ∧ j + 1 ≤ K N := ⟨by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte, Nat.add_sub_cancel]
    rfl
  have hae := stepYC_ukerMatC_eq_Uker_ae d s t K N j n hΦ ξ (time s t K N (j + 1))
    (time s t K N k)
  have hSE : ∀ᵐ ω ∂(Pg d), stoppedEdge (d.L N) ξ u (u k) τ Y b j ω
      = {ω | j < τ ω}.indicator (fun ω => stepYC d s t K N j n Φ U b ω) ω := by
    filter_upwards [hae] with ω hω
    rw [stoppedEdge_apply]
    by_cases h : j < τ ω
    · have hm : ω ∈ {ω' | j < τ ω'} := h
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, hω b, hYeq ω]
    · have hm : ω ∉ {ω' | j < τ ω'} := h
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
  -- measurability of the stopped edge
  have hYm : ∀ i, StronglyMeasurable[filt d i] (Y i) :=
    stronglyMeasurable_gridYC d s t K N n (gridΦG d E s t K N σ)
      (gridΦG_testFun d hE hst ht1 hK0 hn1 σ)
  have hSEm : Measurable (stoppedEdge (d.L N) ξ u (u k) τ Y b j) :=
    ((stronglyMeasurable_stoppedEdge_succ (ℱ := filt d) (d.L N) ξ u (u k) hYm hτmeas b j).mono
      ((filt d).le (j + 1))).measurable
  -- the pathwise domination
  set m2 : ℝ := ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hc : yConst d N n (t N) (etaT E (t N)) * step s t K N
      = (1 + (1 - t N)⁻¹) ^ n * (C2g d N n (etaT E (t N)) / 2 * step s t K N) := by
    unfold yConst; ring
  have hC0 : 0 ≤ C2g d N n (etaT E (t N)) := by unfold C2g; positivity
  have hc0 : 0 ≤ yConst d N n (t N) (etaT E (t N)) * step s t K N := by
    rw [hc]
    have : 0 < 1 - t N := by linarith
    positivity
  have hdomY := norm_stepYC_le_incr d s t K N j n hΦ hC₂ hΔ U b hR
  have hdomN : ∀ᵐ ω ∂(Pg d), ‖stoppedEdge (d.L N) ξ u (u k) τ Y b j ω‖
      ≤ yConst d N n (t N) (etaT E (t N)) * step s t K N * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hSE, hdomY] with ω h1 h2
    rw [h1, hc]
    exact (norm_indicator_le_norm_self _ _).trans h2
  have hdomRe : ∀ᵐ ω ∂(Pg d), |(stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re|
      ≤ yConst d N n (t N) (etaT E (t N)) * step s t K N * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomN] with ω h
    exact (Complex.abs_re_le_norm _).trans h
  have hdomIm : ∀ᵐ ω ∂(Pg d), |(stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im|
      ≤ yConst d N n (t N) (etaT E (t N)) * step s t K N * (‖Xmat d N (ω (j + 1))‖ ^ 2 + m2) := by
    filter_upwards [hdomN] with ω h
    exact (Complex.abs_im_le_norm _).trans h
  obtain ⟨hRe4, hRe2, hRe4'⟩ := moments_of_dom_incr d (Complex.measurable_re.comp hSEm) hc0 hm20
    hdomRe
  obtain ⟨hIm4, hIm2, hIm4'⟩ := moments_of_dom_incr d (Complex.measurable_im.comp hSEm) hc0 hm20
    hdomIm
  -- conditional mean zero
  obtain ⟨hmRe, hmIm⟩ := condExp_indicator_stepYC_reim d s t K N j n hΦ hC₂ hΔ U b hS
  have hmRe' : (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re | filt d j]
      =ᵐ[Pg d] 0 := by
    refine (condExp_congr_ae ?_).trans hmRe
    filter_upwards [hSE] with ω h
    simp only [h]
  have hmIm' : (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im | filt d j]
      =ᵐ[Pg d] 0 := by
    refine (condExp_congr_ae ?_).trans hmIm
    filter_upwards [hSE] with ω h
    simp only [h]
  exact ⟨hmRe', hmIm', hRe4, hIm4, hRe2, hIm2, hRe4', hIm4'⟩

/-- `v_j ≤ Δ² P`, `w_j ≤ Δ⁴ P²` with `P = yConst²(I₂ + I₄ + 1)`. -/
theorem vY_wY_le (N n : ℕ) (T η Δ : ℝ) :
    vY514 d N n T η Δ ≤ Δ ^ 2 * (yConst d N n T η ^ 2
        * ((∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 2 ∂(P d))
          + (∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 4 ∂(P d)) + 1))
    ∧ wY514 d N n T η Δ ≤ Δ ^ 4 * (yConst d N n T η ^ 2
        * ((∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 2 ∂(P d))
          + (∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 4 ∂(P d)) + 1)) ^ 2 := by
  set I2 := ∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 2 ∂(P d) with hI2
  set I4 := ∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 4 ∂(P d) with hI4
  set c := yConst d N n T η with hcdef
  have hI20 : 0 ≤ I2 := integral_nonneg fun _ => by positivity
  have hI40 : 0 ≤ I4 := integral_nonneg fun _ => by positivity
  constructor
  · show (c * Δ) ^ 2 * I2 ≤ Δ ^ 2 * (c ^ 2 * (I2 + I4 + 1))
    have : (c * Δ) ^ 2 * I2 = Δ ^ 2 * (c ^ 2 * I2) := by ring
    rw [this]
    have h1 : c ^ 2 * I2 ≤ c ^ 2 * (I2 + I4 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · show (c * Δ) ^ 4 * I4 ≤ Δ ^ 4 * (c ^ 2 * (I2 + I4 + 1)) ^ 2
    have hsq : I4 ≤ (I2 + I4 + 1) ^ 2 := by nlinarith
    have : (c * Δ) ^ 4 * I4 = Δ ^ 4 * (c ^ 4 * I4) := by ring
    rw [this]
    have h1 : c ^ 4 * I4 ≤ (c ^ 2 * (I2 + I4 + 1)) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    exact mul_le_mul_of_nonneg_left h1 (by positivity)

end Y514c


section StepErr514

variable (d : Dims)

theorem max_norm_mSigma_eq {E : ℝ} (hE : |E| < 2) : max ‖mSigma E true‖ ‖mSigma E false‖ = 1 := by
  rw [norm_mSigma hE.le, norm_mSigma hE.le, max_self]

theorem zMotionZLip_le514 {L W n : ℕ} {η Y : ℝ} {E : ℝ} (hE : |E| < 2) (hη : 0 < η)
    (hW : (W : ℝ) ≤ Y) (hL : (L : ℝ) ≤ Y) (hηY : 1 + η⁻¹ ≤ Y) :
    zMotionZLip L W n η (mSigma E) ≤ (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7) := by
  unfold zMotionZLip
  rw [max_norm_mSigma_eq hE]
  have h1 : 0 ≤ 1 + η⁻¹ := by positivity
  have hY0 : 0 ≤ Y := h1.trans hηY
  calc (n : ℝ) * (1 * (W : ℝ) * (L : ℝ) * ((L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (1 + η⁻¹) ^ (n + 1)))
        * (1 + η⁻¹) ^ 2
      ≤ (n : ℝ) * (1 * Y * Y * (Y * Y * ((n : ℝ) + 1) * Y ^ (n + 1))) * Y ^ 2 := by gcongr
    _ = (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7) := by ring

theorem zMotionLip_le514 {L W n : ℕ} {η Y : ℝ} {E : ℝ} (hE : |E| < 2) (hη : 0 < η)
    (hW : (W : ℝ) ≤ Y) (hL : (L : ℝ) ≤ Y) (hηY : 1 + η⁻¹ ≤ Y) :
    zMotionLip L W n η (mSigma E) ≤ (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7) := by
  unfold zMotionLip
  rw [max_norm_mSigma_eq hE]
  have hi : η⁻¹ ≤ Y := by have : 0 ≤ η⁻¹ := by positivity
                          linarith
  have hY0 : 0 ≤ Y := (by positivity : (0:ℝ) ≤ η⁻¹).trans hi
  calc (n : ℝ) * (1 * (W : ℝ) * (L : ℝ) * ((L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (1 + η⁻¹) ^ (n + 1)))
        * η⁻¹ ^ 2
      ≤ (n : ℝ) * (1 * Y * Y * (Y * Y * ((n : ℝ) + 1) * Y ^ (n + 1))) * Y ^ 2 := by gcongr
    _ = (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7) := by ring

theorem driftLip_le514 {L W n : ℕ} {η Y : ℝ} {E : ℝ} (hE : |E| < 2) (hη : 0 < η)
    (hW : (W : ℝ) ≤ Y) (hL : (L : ℝ) ≤ Y) (hηY : 1 + η⁻¹ ≤ Y) (hY1 : 1 ≤ Y) :
    driftLip L W n η (mSigma E) ≤ 16 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13) := by
  unfold driftLip
  rw [max_norm_mSigma_eq hE]
  have hi : η⁻¹ ≤ Y := by have : 0 ≤ η⁻¹ := by positivity
                          linarith
  have h2 : (1 + η⁻¹) + 1 ≤ 2 * Y := by linarith
  calc 4 * (L : ℝ) ^ 4 * (W : ℝ) ^ 3 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * ((1 + η⁻¹) + 1) ^ 2
        * (1 + η⁻¹) ^ (2 * (n + 1)) * η⁻¹ ^ 2
      ≤ 4 * Y ^ 4 * Y ^ 3 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * (2 * Y) ^ 2
        * Y ^ (2 * (n + 1)) * Y ^ 2 := by gcongr
    _ = 16 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13) := by ring

/-- `(1+x)^n - 1 - n x ≤ 4^n x²` for `0 ≤ x ≤ 1`. -/
theorem one_add_pow_sub_le (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ n - 1 - (n : ℝ) * x ≤ 4 ^ n * x ^ 2 := by
  induction n with
  | zero => simp; positivity
  | succ k ih =>
    have hk4 : (k : ℝ) ≤ 4 ^ k := by
      have : (k : ℝ) < 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      have h2 : (2 : ℝ) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      linarith
    have h1 : (1 + x) ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℝ) * x
        = (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) + (k : ℝ) * x ^ 2 := by
      push_cast; ring
    rw [h1, pow_succ]
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
    have h5 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ 1 + x)
    have h6 : (1 + x) * (4 ^ k * x ^ 2) ≤ 2 * (4 ^ k * x ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h7 : (k : ℝ) * x ^ 2 ≤ 4 ^ k * x ^ 2 := mul_le_mul_of_nonneg_right hk4 hx2
    have h8 : (4 : ℝ) ^ k * 4 = 4 ^ k * 4 := rfl
    calc (1 + x) * ((1 + x) ^ k - 1 - (k : ℝ) * x) + (k : ℝ) * x ^ 2
        ≤ 2 * (4 ^ k * x ^ 2) + 4 ^ k * x ^ 2 := by linarith
      _ ≤ 4 ^ k * 4 * x ^ 2 := by nlinarith
      _ = 4 ^ k * 4 * x ^ 2 := rfl

/-- `∫‖X‖² ≤ #Idx` (`traceConst 1 = 1`). -/
theorem integral_normSq_Xmat_le514 (N : ℕ) :
    ∫ ω, ‖Xmat d N ω‖ ^ 2 ∂(P d) ≤ (Fintype.card (d.Idx N) : ℝ) := by
  have h1 := integral_norm_Xmat_pow_le (d := d) N 0
  norm_num at h1
  have hfrob : ∀ ω : Ω d, frobSq (Xmat d N ω) = ∑ i, colSq (Xmat d N ω) 1 i := by
    intro ω; unfold frobSq colSq; simp only [pow_one]; exact Finset.sum_comm
  simp only [hfrob] at h1
  rw [integral_finsetSum _ fun i _ => integrable_colSq d N 1 i] at h1
  have h2 : ∑ i : d.Idx N, ∫ ω, colSq (Xmat d N ω) 1 i ∂(P d)
      ≤ ∑ _i : d.Idx N, traceConst 1 := Finset.sum_le_sum fun i _ => integral_colSq_le d N 1 i
  have h3 : traceConst 1 = 1 := by norm_num [traceConst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h3, mul_one] at h2
  linarith

theorem integral_norm_Xmat_le514 (N : ℕ) :
    ∫ ω, ‖Xmat d N ω‖ ∂(P d) ≤ 1 + (Fintype.card (d.Idx N) : ℝ) := by
  have hi2 : Integrable (fun ω : Ω d => ‖Xmat d N ω‖ ^ 2) (P d) := by
    simpa using integrable_norm_Xmat_pow d N 1
  have hi1 : Integrable (fun ω : Ω d => ‖Xmat d N ω‖) (P d) := by
    refine ((integrable_const 1).add hi2).mono' (measurable_norm_Xmat d N).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    show ‖Xmat d N ω‖ ≤ 1 + ‖Xmat d N ω‖ ^ 2
    nlinarith [sq_nonneg (‖Xmat d N ω‖ - 1), norm_nonneg (Xmat d N ω)]
  calc ∫ ω, ‖Xmat d N ω‖ ∂(P d) ≤ ∫ ω, (1 + ‖Xmat d N ω‖ ^ 2) ∂(P d) := by
        refine integral_mono hi1 ((integrable_const 1).add hi2) fun ω => ?_
        nlinarith [sq_nonneg (‖Xmat d N ω‖ - 1), norm_nonneg (Xmat d N ω)]
    _ = 1 + ∫ ω, ‖Xmat d N ω‖ ^ 2 ∂(P d) := by
        rw [integral_add (integrable_const 1) hi2]; simp
    _ ≤ 1 + (Fintype.card (d.Idx N) : ℝ) := by linarith [integral_normSq_Xmat_le514 d N]

set_option maxHeartbeats 4000000 in
/-- **The remainder `stepErrN` is `O(Δ^{3/2})` with a polynomial constant**: with `Y ≥ 1` bounding
`W, L, 1 + η^{-1}, #Idx, Bk` (`η = η_{u_{k+1}} ≤ η_{u_k}`) and `ΔY ≤ 1`,
`stepErrN ≤ Δ^{3/2}·(100 (n+1)^6 4^n) Y^{2n+16}`. -/
theorem stepErrN_le {E : ℝ} (hE : |E| < 2) (N n : ℕ) {uk uk1 Δ Bk Y : ℝ} (hu0 : 0 ≤ uk)
    (huk : uk ≤ uk1) (hu1 : uk1 < 1) (hΔ0 : 0 ≤ Δ) (hBk0 : 0 ≤ Bk) (hY1 : 1 ≤ Y)
    (hW : (d.W N : ℝ) ≤ Y) (hL : (d.L N : ℝ) ≤ Y) (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ Y)
    (hηY : 1 + (etaT E uk1)⁻¹ ≤ Y) (hBk : Bk ≤ Y) (hΔY : Δ * Y ≤ 1) :
    stepErrN (band d) E N n uk uk1 Δ Bk
      ≤ Δ ^ (3 / 2 : ℝ) * (100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * Y ^ (2 * n + 16)) := by
  have hη1 : 0 < etaT E uk1 := etaT_pos hE hu1
  have hηk : 0 < etaT E uk := etaT_pos hE (huk.trans_lt hu1)
  have hηk_le : etaT E uk1 ≤ etaT E uk := etaT_anti hE huk
  have hηk' : 1 + (etaT E uk)⁻¹ ≤ Y := by
    have := inv_anti₀ hη1 hηk_le
    linarith
  have habsk : |(zt E uk).im| = etaT E uk := abs_zt_im hE (huk.trans_lt hu1)
  have hηeq : (1 - uk1) * (mE E).im = etaT E uk1 := rfl
  have hmE : ‖mE E‖ = 1 := norm_mE hE.le
  have hΔ1 : Δ ≤ 1 := by nlinarith
  have hΔ32 : Δ ^ 2 ≤ Δ ^ (3 / 2 : ℝ) := by
    rcases hΔ0.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge h hΔ1 (by norm_num)
  have hΔ32' : 0 ≤ Δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hΔ0 _
  have hmim1 : (mE E).im ≤ 1 := by
    have := Complex.abs_im_le_norm (mE E); rw [hmE] at this; exact (le_abs_self _).trans this
  have hmim0 : 0 < (mE E).im := mE_im_pos hE
  have h1u : (1 - uk1)⁻¹ ≤ Y := by
    have : (1 - uk1)⁻¹ = (mE E).im * (etaT E uk1)⁻¹ := by
      unfold etaT; field_simp
    rw [this]
    have : (mE E).im * (etaT E uk1)⁻¹ ≤ 1 * (etaT E uk1)⁻¹ :=
      mul_le_mul_of_nonneg_right hmim1 (by positivity)
    linarith
  have h1u0 : 0 ≤ (1 - uk1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hY0 : 0 ≤ Y := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the pieces
  have hZZ := zMotionZLip_le514 (L := d.L N) (W := d.W N) (n := n) hE hη1 hW hL hηY
  rw [← hηeq] at hZZ
  have hpos : 0 < |(zt E uk).im| := by rw [habsk]; exact hηk
  have hZ := zMotionLip_le514 (L := d.L N) (W := d.W N) (n := n) hE hpos hW hL
    (by rw [habsk]; exact hηk')
  have hD := driftLip_le514 (L := d.L N) (W := d.W N) (n := n) hE hpos hW hL
    (by rw [habsk]; exact hηk') hY1
  have hX := integral_norm_Xmat_le514 d N
  have hXY : ∫ x, ‖Xmat d N x‖ ∂ (P d) ≤ 2 * Y := by linarith
  have hX0 : 0 ≤ ∫ x, ‖Xmat d N x‖ ∂ (P d) := integral_nonneg fun _ => norm_nonneg _
  have hx : Δ * (1 - uk1)⁻¹ ≤ 1 := by nlinarith
  have hx0 : 0 ≤ Δ * (1 - uk1)⁻¹ := by positivity
  have hf := one_add_pow_sub_le n hx0 hx
  have hηn : |(zt E uk).im|⁻¹ ^ n * (d.W N : ℝ)⁻¹ ^ (n - 1) ≤ Y ^ n := by
    rw [habsk]
    have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
    have h1 : (d.W N : ℝ)⁻¹ ^ (n - 1) ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
    have h2 : (etaT E uk)⁻¹ ^ n ≤ Y ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    calc (etaT E uk)⁻¹ ^ n * (d.W N : ℝ)⁻¹ ^ (n - 1) ≤ Y ^ n * 1 :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = Y ^ n := mul_one _
  have hint : ∫ x, ‖Xmat (band d).toDims N x‖ ∂ (P (band d).toDims)
      = ∫ x, ‖Xmat d N x‖ ∂ (P d) := rfl
  unfold stepErrN
  rw [hint, hmE]
  set I1 := ∫ x, ‖Xmat d N x‖ ∂ (P d) with hI1
  set ZZ := zMotionZLip ((band d).L N) ((band d).W N) n ((1 - uk1) * (mE E).im) (mSigma E)
    with hZZdef
  set ZL := zMotionLip ((band d).L N) ((band d).W N) n |(zt E uk).im| (mSigma E) with hZLdef
  set GLp := genPtLip ((band d).L N) ((band d).W N) n |(zt E uk).im| (mSigma E) with hGLpdef
  have hGLp : GLp ≤ 16 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13)
      + (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7) := by
    rw [hGLpdef, genPtLip]; exact add_le_add hD hZ
  have hZL0 : 0 ≤ ZL := by
    rw [hZLdef]; unfold zMotionLip; positivity
  have hGLp0 : 0 ≤ GLp := by
    rw [hGLpdef]; unfold genPtLip driftLip zMotionLip; positivity
  have hZZ0 : 0 ≤ ZZ := by
    rw [hZZdef]; unfold zMotionZLip; positivity
  set P := Y ^ (2 * n + 16) with hPdef
  have hYp : ∀ a : ℕ, a ≤ 2 * n + 16 → Y ^ a ≤ P := fun a ha => pow_le_pow_right₀ hY1 ha
  have hP0 : 0 ≤ P := by positivity
  -- term 1
  have e1 : ZZ * 1 * Δ ^ 2 / 2 ≤ Δ ^ (3 / 2 : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) * P) := by
    have h1 : ZZ ≤ (n : ℝ) * ((n : ℝ) + 1) * P :=
      hZZ.trans (mul_le_mul_of_nonneg_left (hYp _ (by omega)) (by positivity))
    have h2 : ZZ * 1 * Δ ^ 2 / 2 ≤ ZZ * Δ ^ 2 := by nlinarith [sq_nonneg Δ]
    calc ZZ * 1 * Δ ^ 2 / 2 ≤ ZZ * Δ ^ 2 := h2
      _ ≤ ((n : ℝ) * ((n : ℝ) + 1) * P) * Δ ^ (3 / 2 : ℝ) :=
          mul_le_mul h1 hΔ32 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  -- term 2
  have e2 : (ZL + 2 / 3 * GLp) * Δ ^ (3 / 2 : ℝ) * I1
      ≤ Δ ^ (3 / 2 : ℝ) * (2 * (2 * (n : ℝ) * ((n : ℝ) + 1)
          + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) * P) := by
    have hZLp : ZL ≤ (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7) := hZ
    have hsum : ZL + 2 / 3 * GLp ≤ (2 * (n : ℝ) * ((n : ℝ) + 1)
        + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) * Y ^ (2 * n + 13) := by
      have ha : Y ^ (n + 7) ≤ Y ^ (2 * n + 13) := pow_le_pow_right₀ hY1 (by omega)
      have hb : (n : ℝ) * ((n : ℝ) + 1) * Y ^ (n + 7)
          ≤ (n : ℝ) * ((n : ℝ) + 1) * Y ^ (2 * n + 13) :=
        mul_le_mul_of_nonneg_left ha (by positivity)
      have hA0 : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) * Y ^ (2 * n + 13) := by positivity
      have hB0 : 0 ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13) := by positivity
      have e1 : 16 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13)
          = 16 * ((n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13)) := by ring
      have e2 : (2 * (n : ℝ) * ((n : ℝ) + 1) + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1))
          * Y ^ (2 * n + 13) = 2 * ((n : ℝ) * ((n : ℝ) + 1) * Y ^ (2 * n + 13))
            + 11 * ((n : ℝ) ^ 2 * ((n : ℝ) + 1) * Y ^ (2 * n + 13)) := by ring
      rw [e2]
      rw [e1] at hGLp
      linarith
    have hYY : Y ^ (2 * n + 13) * (2 * Y) ≤ 2 * P := by
      have e : Y ^ (2 * n + 13) * (2 * Y) = 2 * Y ^ (2 * n + 14) := by ring
      have h14 := hYp (2 * n + 14) (by omega)
      rw [e]; linarith
    have hc0 : 0 ≤ 2 * (n : ℝ) * ((n : ℝ) + 1) + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) := by positivity
    calc (ZL + 2 / 3 * GLp) * Δ ^ (3 / 2 : ℝ) * I1
        = Δ ^ (3 / 2 : ℝ) * ((ZL + 2 / 3 * GLp) * I1) := by ring
      _ ≤ Δ ^ (3 / 2 : ℝ) * (((2 * (n : ℝ) * ((n : ℝ) + 1)
            + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) * Y ^ (2 * n + 13)) * (2 * Y)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hsum hXY hX0 (by positivity)) hΔ32'
      _ ≤ Δ ^ (3 / 2 : ℝ) * (2 * (2 * (n : ℝ) * ((n : ℝ) + 1)
            + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) * P) := by
          refine mul_le_mul_of_nonneg_left ?_ hΔ32'
          calc ((2 * (n : ℝ) * ((n : ℝ) + 1) + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1))
                * Y ^ (2 * n + 13)) * (2 * Y)
              = (2 * (n : ℝ) * ((n : ℝ) + 1) + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1))
                * (Y ^ (2 * n + 13) * (2 * Y)) := by ring
            _ ≤ (2 * (n : ℝ) * ((n : ℝ) + 1) + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) * (2 * P) :=
                mul_le_mul_of_nonneg_left hYY hc0
            _ = _ := by ring
  -- term 3
  have e3 : (2 * ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk
        * (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
      + ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ)
        * (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2) ^ 2) * Δ ^ 2
      ≤ Δ ^ (3 / 2 : ℝ) * ((2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6) * P) := by
    have hW' : ((band d).W N : ℝ) ≤ Y := hW
    have hL' : ((band d).L N : ℝ) ≤ Y := hL
    have hW0 : (0 : ℝ) ≤ ((band d).W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ ((band d).L N : ℝ) := Nat.cast_nonneg _
    have hbd : 2 * ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk
        * (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
      + ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ)
        * (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2) ^ 2
        ≤ 2 * Y * (n : ℝ) ^ 2 * Y * Y * (Y * (n : ℝ) ^ 2 * Y * Y ^ 2)
          + Y * (n : ℝ) ^ 2 * Y * (Y * (n : ℝ) ^ 2 * Y * Y ^ 2) ^ 2 := by gcongr
    have heq : 2 * Y * (n : ℝ) ^ 2 * Y * Y * (Y * (n : ℝ) ^ 2 * Y * Y ^ 2)
          + Y * (n : ℝ) ^ 2 * Y * (Y * (n : ℝ) ^ 2 * Y * Y ^ 2) ^ 2
        = 2 * (n : ℝ) ^ 4 * Y ^ 7 + (n : ℝ) ^ 6 * Y ^ 10 := by ring
    have h7 := hYp 7 (by omega)
    have h10 := hYp 10 (by omega)
    have hbd' : 2 * (n : ℝ) ^ 4 * Y ^ 7 + (n : ℝ) ^ 6 * Y ^ 10 ≤ (2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6) * P := by
      have := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ) ^ 4)
      have := mul_le_mul_of_nonneg_left h10 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 6)
      nlinarith
    have htot := hbd.trans (heq ▸ hbd')
    have h0 : 0 ≤ 2 * ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk
        * (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2)
      + ((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ)
        * (((band d).W N : ℝ) * (n : ℝ) ^ 2 * ((band d).L N : ℝ) * Bk ^ 2) ^ 2 := by positivity
    calc _ ≤ ((2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6) * P) * Δ ^ (3 / 2 : ℝ) :=
          mul_le_mul htot hΔ32 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  -- term 4
  have e4 : ((n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹))
        * (|(zt E uk).im|⁻¹ ^ n * ((band d).W N : ℝ)⁻¹ ^ (n - 1) + Bk)
      ≤ Δ ^ (3 / 2 : ℝ) * (2 * ((n : ℝ) + 4 ^ n) * P) := by
    have hf' : (1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹
        ≤ 4 ^ n * (Δ * (1 - uk1)⁻¹) ^ 2 := by
      rw [show (n : ℝ) * Δ * (1 - uk1)⁻¹ = (n : ℝ) * (Δ * (1 - uk1)⁻¹) by ring]; exact hf
    have hf0 : 0 ≤ (1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹ := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - uk1)⁻¹ by linarith) n
      linarith
    have hA : (n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹)
        ≤ ((n : ℝ) + 4 ^ n) * Δ ^ 2 * Y ^ 2 := by
      have h1 : (1 - uk1)⁻¹ ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ h1u0 h1u 2
      have h2 : (n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2 ≤ (n : ℝ) * Δ ^ 2 * Y ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : 4 ^ n * (Δ * (1 - uk1)⁻¹) ^ 2 ≤ 4 ^ n * (Δ ^ 2 * Y ^ 2) := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) (by positivity)
      nlinarith
    have hB : |(zt E uk).im|⁻¹ ^ n * ((band d).W N : ℝ)⁻¹ ^ (n - 1) + Bk ≤ 2 * Y ^ (n + 1) := by
      have h1 : Y ^ n ≤ Y ^ (n + 1) := pow_le_pow_right₀ hY1 (by omega)
      have h2 : Y ≤ Y ^ (n + 1) := by
        calc Y = Y ^ 1 := (pow_one Y).symm
          _ ≤ Y ^ (n + 1) := pow_le_pow_right₀ hY1 (by omega)
      have : |(zt E uk).im|⁻¹ ^ n * ((band d).W N : ℝ)⁻¹ ^ (n - 1) ≤ Y ^ n := hηn
      linarith
    have hB0 : 0 ≤ |(zt E uk).im|⁻¹ ^ n * ((band d).W N : ℝ)⁻¹ ^ (n - 1) + Bk := by positivity
    have hA0 : 0 ≤ (n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹) := by positivity
    have hY3 : Y ^ 2 * Y ^ (n + 1) ≤ P := by
      rw [← pow_add]; exact hYp _ (by omega)
    calc _ ≤ (((n : ℝ) + 4 ^ n) * Δ ^ 2 * Y ^ 2) * (2 * Y ^ (n + 1)) :=
          mul_le_mul hA hB hB0 (by positivity)
      _ = 2 * ((n : ℝ) + 4 ^ n) * (Y ^ 2 * Y ^ (n + 1)) * Δ ^ 2 := by ring
      _ ≤ 2 * ((n : ℝ) + 4 ^ n) * P * Δ ^ (3 / 2 : ℝ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hY3 (by positivity)) hΔ32 (sq_nonneg _)
            (by positivity)
      _ = _ := by ring
  -- total
  have hcoef : (n : ℝ) * ((n : ℝ) + 1) + 2 * (2 * (n : ℝ) * ((n : ℝ) + 1)
        + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) + (2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6)
        + 2 * ((n : ℝ) + 4 ^ n) ≤ 100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n := by
    set q : ℝ := (n : ℝ) + 1 with hq
    have hq1 : (1 : ℝ) ≤ q := by rw [hq]; linarith
    have hnq : (n : ℝ) ≤ q := by rw [hq]; linarith
    have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    have hq2 : q ^ 2 ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by norm_num)
    have hq3 : q ^ 3 ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by norm_num)
    have hq1' : q ≤ q ^ 6 := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ 6 := pow_le_pow_right₀ hq1 (by norm_num)
    have hn1 : (n : ℝ) * ((n : ℝ) + 1) ≤ q ^ 2 := by
      rw [← hq, sq]; exact mul_le_mul_of_nonneg_right hnq (by linarith)
    have hn2 : (n : ℝ) ^ 2 * ((n : ℝ) + 1) ≤ q ^ 3 := by
      rw [← hq, pow_succ]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn0 hnq 2) (by linarith)
    have hn4 : (n : ℝ) ^ 4 ≤ q ^ 6 := (pow_le_pow_left₀ hn0 hnq 4).trans
      (pow_le_pow_right₀ hq1 (by norm_num))
    have hn6 : (n : ℝ) ^ 6 ≤ q ^ 6 := pow_le_pow_left₀ hn0 hnq 6
    have hX6 : q ^ 6 ≤ q ^ 6 * 4 ^ n := le_mul_of_one_le_right (by positivity) h4
    have hX4 : (4 : ℝ) ^ n ≤ q ^ 6 * 4 ^ n :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq1)
    have e : 100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n = 100 * (q ^ 6 * 4 ^ n) := by rw [← hq]; ring
    rw [e]
    have e2 : 2 * (2 * (n : ℝ) * ((n : ℝ) + 1) + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1))
        = 4 * ((n : ℝ) * ((n : ℝ) + 1)) + 22 * ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by ring
    rw [e2]
    linarith
  have htot := add_le_add (add_le_add (add_le_add e1 e2) e3) e4
  refine htot.trans ?_
  have hPc : ((n : ℝ) * ((n : ℝ) + 1) + 2 * (2 * (n : ℝ) * ((n : ℝ) + 1)
        + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) + (2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6)
        + 2 * ((n : ℝ) + 4 ^ n)) * P ≤ 100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * P :=
    mul_le_mul_of_nonneg_right hcoef hP0
  have h2 := mul_le_mul_of_nonneg_left hPc hΔ32'
  have e : Δ ^ (3 / 2 : ℝ) * ((n : ℝ) * ((n : ℝ) + 1) * P)
      + Δ ^ (3 / 2 : ℝ) * (2 * (2 * (n : ℝ) * ((n : ℝ) + 1)
          + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) * P)
      + Δ ^ (3 / 2 : ℝ) * ((2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6) * P)
      + Δ ^ (3 / 2 : ℝ) * (2 * ((n : ℝ) + 4 ^ n) * P)
      = Δ ^ (3 / 2 : ℝ) * (((n : ℝ) * ((n : ℝ) + 1) + 2 * (2 * (n : ℝ) * ((n : ℝ) + 1)
        + 11 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)) + (2 * (n : ℝ) ^ 4 + (n : ℝ) ^ 6)
        + 2 * ((n : ℝ) + 4 ^ n)) * P) := by ring
  rw [e]
  refine h2.trans (le_of_eq ?_)
  ring

end StepErr514



section Assembly514

variable (d : Dims)

/-- The `(L-K)` envelope `MD_u = LW + η_u^{-n} + MK`. -/
def MD514 (d : Dims) (E : ℝ) (N n : ℕ) (MK u : ℝ) : ℝ :=
  (d.L N : ℝ) * (d.W N : ℝ) + (etaT E u)⁻¹ ^ n + MK

/-- The `Y` scale `P = yConst²(I₂ + I₄ + 1)`. -/
def PY514 (d : Dims) (N n : ℕ) (T η : ℝ) : ℝ :=
  yConst d N n T η ^ 2
    * ((∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 2 ∂(P d))
      + (∫ x, (‖Xmat d N x‖ ^ 2 + ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d)) ^ 4 ∂(P d)) + 1)

/-- `κ_{i,k} ≥ 0` on the grid. -/
theorem kappa514_nonneg {L n : ℕ} [NeZero L] (hL : 3 ≤ L) {E Kd : ℝ} (hKd : 0 ≤ Kd) (u : ℕ → ℝ)
    {i k : ℕ} (hi0 : 0 ≤ u i) (hi1 : u i < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1) :
    0 ≤ kappa514 L n E Kd u i k := by
  unfold kappa514
  have hc := cKerShort_nonneg n (Real.sqrt_nonneg (min (2 - |E|) 1))
  have hl1 : 0 < ellHat L ((u i : ℝ) : ℂ) := Step3.ellHat_pos_of_lt_one (by omega) hi1
  have hl2 : 0 < ellHat L ((u k : ℝ) : ℂ) := Step3.ellHat_pos_of_lt_one (by omega) hk1
  have h1 : 0 < 1 - u i := by linarith
  have h2 : 0 < 1 - u k := by linarith
  positivity

theorem eps514_nonneg (n : ℕ) (u : ℕ → ℝ) {i k : ℕ} (hi1 : u i < 1) (hk1 : u k < 1) :
    0 ≤ eps514 n u i k := by
  unfold eps514
  have h1 : 0 < 1 - u i := by linarith
  have h2 : 0 < 1 - u k := by linarith
  positivity

theorem dDr514_nonneg {E : ℝ} (hE : |E| < 2) (N n : ℕ) {u ε₁ τ' D' Φ CK B : ℝ} (hu1 : u < 1)
    (hA : 0 < (band d).scale E N u) (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK) (hB : 0 ≤ B) :
    0 ≤ dDr514 d E N n u ε₁ τ' D' Φ CK B := by
  unfold dDr514
  have := etaT_pos hE hu1
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
  have hs : 0 ≤ ∑ _lK ∈ Finset.Icc 3 n,
      (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * ((N : ℝ) ^ ε₁ * Φ)
          * ((band d).scale E N u)⁻¹ ^ n
        + 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * ((N : ℝ) ^ ε₁ * Φ)) :=
    Finset.sum_nonneg fun _ _ => by positivity
  positivity

theorem driftErr514_nonneg (N m : ℕ) {MK MD D' : ℝ} (hMK : 0 ≤ MK) (hMD : 0 ≤ MD) :
    0 ≤ driftErr514 d N m MK MD D' := by
  unfold driftErr514
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  positivity

end Assembly514



section Budget514

variable (d : Dims)

theorem mE_im_le_one {E : ℝ} (hE : |E| < 2) : (mE E).im ≤ 1 := by
  have := Complex.abs_im_le_norm (mE E)
  rw [norm_mE hE.le] at this
  exact (le_abs_self _).trans this

/-- On the grid window, `η_u^{-1} ≤ N` and `(1-u)^{-1} ≤ N` once `η_v^{-1} ≤ N`. -/
theorem inv_eta_le_of {E : ℝ} (hE : |E| < 2) {N : ℕ} {v u : ℝ} (hv1 : v < 1)
    (hη : (etaT E v)⁻¹ ≤ N) (huv : u ≤ v) :
    (etaT E u)⁻¹ ≤ N ∧ (1 - u)⁻¹ ≤ N := by
  have hηv := etaT_pos hE hv1
  have hηu := etaT_pos hE (huv.trans_lt hv1)
  have h1 : (etaT E u)⁻¹ ≤ (etaT E v)⁻¹ := inv_anti₀ hηv (etaT_anti hE huv)
  refine ⟨h1.trans hη, ?_⟩
  have heq : (1 - u)⁻¹ = (mE E).im * (etaT E u)⁻¹ := by
    unfold etaT
    have : (mE E).im ≠ 0 := (mE_im_pos hE).ne'
    have : 1 - u ≠ 0 := by linarith
    field_simp
  rw [heq]
  have := mE_im_le_one hE
  have h0 : 0 ≤ (etaT E u)⁻¹ := by positivity
  nlinarith [mE_im_pos hE]

/-- `A_u = W ℓ_u η_u ≤ L W`. -/
theorem scale_le_LW {E : ℝ} (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (band d).scale E N u ≤ (d.L N : ℝ) * (d.W N : ℝ) := by
  show (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) * etaT E u ≤ (d.L N : ℝ) * (d.W N : ℝ)
  have hℓ : ellHat (d.L N) (u : ℂ) ≤ d.L N := by unfold ellHat; exact min_le_right _ _
  have hℓ0 : 0 ≤ ellHat (d.L N) (u : ℂ) := by
    unfold ellHat; exact le_min (by positivity) (Nat.cast_nonneg _)
  have hη := etaT_le_one hE hu0
  have hη0 := (etaT_pos hE hu1).le
  have hW : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  calc (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) * etaT E u ≤ (d.W N : ℝ) * (d.L N : ℝ) * 1 := by
        gcongr
    _ = _ := by ring

/-- The drift bound split into its sharp main part and its `W^{-D'}` tail. -/
theorem dDr514_eq (E : ℝ) (N n : ℕ) (u ε₁ τ' D' Φ CK B : ℝ) :
    dDr514 d E N n u ε₁ τ' D' Φ CK B
      = (4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁
          + ((Finset.Icc 3 n).card : ℝ) * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ'
              * (N : ℝ) ^ ε₁)
          + 4 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁)
          * Φ * (etaT E u)⁻¹ * ((band d).scale E N u)⁻¹ ^ n
        + ((n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁
          + ((Finset.Icc 3 n).card : ℝ) * (2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ)
              * (d.W N : ℝ) ^ (-D') * ((N : ℝ) ^ ε₁ * Φ))
          + (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * B) := by
  unfold dDr514
  rw [Finset.sum_const, nsmul_eq_mul]
  ring


/-- `κ_{i,k} ≤ cKerShort·Kd^n·A_{u_i}^n` when `A_{u_k} ≥ 1` (for the `W^{-D'}` tails only). -/
theorem kappa514_le_max {E : ℝ} (hE : |E| < 2) (N n : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd) (u : ℕ → ℝ)
    (i k : ℕ) (hi0 : 0 ≤ u i) (hi1 : u i < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1)
    (hAk : 1 ≤ (band d).scale E N (u k)) :
    kappa514 (d.L N) n E Kd u i k
      ≤ cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n * (band d).scale E N (u i) ^ n := by
  have hAi : 0 < (band d).scale E N (u i) := (band d).scale_pos' hE N hi0 hi1
  have hr := scale_ratio_pow (d := d) (N := N) hE hi0 hi1 hk0 hk1 n
  set R := (1 - u i) * ellHat (d.L N) ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat (d.L N) ((u k : ℝ) : ℂ))
    with hR
  have hRn : R ^ n = ((band d).scale E N (u k))⁻¹ ^ n * (band d).scale E N (u i) ^ n := by
    have hai : ((band d).scale E N (u i))⁻¹ ^ n * (band d).scale E N (u i) ^ n = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hAi.ne', one_pow]
    calc R ^ n = R ^ n * (((band d).scale E N (u i))⁻¹ ^ n * (band d).scale E N (u i) ^ n) := by
          rw [hai, mul_one]
      _ = (R ^ n * ((band d).scale E N (u i))⁻¹ ^ n) * (band d).scale E N (u i) ^ n := by ring
      _ = _ := by rw [hr]
  have hk : ((band d).scale E N (u k))⁻¹ ^ n ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hAk)
  unfold kappa514
  rw [← hR, hRn]
  have hc := cKerShort_nonneg n (Real.sqrt_nonneg (min (2 - |E|) 1))
  have h0 : 0 ≤ cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n := by positivity
  have h1 : ((band d).scale E N (u k))⁻¹ ^ n * (band d).scale E N (u i) ^ n
      ≤ (band d).scale E N (u i) ^ n := by
    have : 0 ≤ (band d).scale E N (u i) ^ n := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_left h1 h0

theorem eps514_le {n : ℕ} (u : ℕ → ℝ) {i k : ℕ} {X : ℝ} (hi0 : 0 ≤ u i) (hi1 : u i < 1)
    (hk1 : u k < 1) (hX : (1 - u k)⁻¹ ≤ X) : eps514 n u i k ≤ X ^ n := by
  unfold eps514
  have h1 : 0 < 1 - u k := by linarith
  have h2 : (1 - u i) / (1 - u k) ≤ (1 - u k)⁻¹ := by
    rw [div_eq_mul_inv]
    have : 1 - u i ≤ 1 := by linarith
    have h0 : 0 ≤ (1 - u k)⁻¹ := by positivity
    nlinarith
  have h3 : 0 ≤ (1 - u i) / (1 - u k) := div_nonneg (by linarith) h1.le
  exact pow_le_pow_left₀ h3 (h2.trans hX) n

/-- The main coefficient of the drift bound. -/
def Mc514 (d : Dims) (N n : ℕ) (ε₁ τ' CK : ℝ) : ℝ :=
  4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁
    + ((Finset.Icc 3 n).card : ℝ) * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ'
        * (N : ℝ) ^ ε₁)
    + 4 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁

/-- The tail coefficient of the drift bound with the crude envelope `B`. -/
def Ec514 (d : Dims) (N n : ℕ) (ε₁ D' Φ B : ℝ) : ℝ :=
  (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁
    + ((Finset.Icc 3 n).card : ℝ) * (2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ)
        * (d.W N : ℝ) ^ (-D') * ((N : ℝ) ^ ε₁ * Φ))
    + (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * B

set_option maxHeartbeats 1600000 in
/-- **(5.93) for the drift, with the sharp kernel**: the drift term of the assembly bound at the
target `u_K = v` is at most `cKerShort Kd^n · Mc · Φ · A_v^{-n} · Σ_j Δ/η_{u_j}` (no `η_s/η_t`
prefactor) plus `W^{-D'}` tails. -/
theorem tb_drift {m : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hA : ∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale E N u)
    (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hN1 : (1 : ℝ) ≤ N)
    {ε₁ τ' D' Φ CK Kd : ℝ} (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK) (hKd : 0 ≤ Kd) :
    step s v K N * ∑ j ∈ Finset.range (K N),
        (kappa514 (d.L N) (m + 2) E Kd (time s v K N) (j + 1) (K N)
            * dDr514 d E N (m + 2) (time s v K N j) ε₁ τ' D' Φ CK
                (MD514 d E N (m + 2) (CK + 1) (time s v K N j)
                  * (band d).scale E N (time s v K N j) ^ (m + 2))
          + eps514 (m + 2) (time s v K N) (j + 1) (K N)
            * driftErr514 d N m (CK + 1) (MD514 d E N (m + 2) (CK + 1) (time s v K N j)) D')
      ≤ cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * Kd ^ (m + 2) * Mc514 d N (m + 2) ε₁ τ' CK
            * Φ * ((band d).scale E N (v N))⁻¹ ^ (m + 2)
            * ∑ j ∈ Finset.range (K N), step s v K N / etaT E (time s v K N j)
        + (cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * Kd ^ (m + 2) * (N : ℝ) ^ (m + 2)
            * Ec514 d N (m + 2) ε₁ D' Φ (((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) * (N : ℝ) ^ (m + 2))
          + (N : ℝ) ^ (m + 2) * driftErr514 d N m (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) D')
        := by
  set n := m + 2 with hn
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have huK : u (K N) = v N := time_last s v K N hK0
  have hKΔ : (K N : ℝ) * Δ = v N - s N := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step; field_simp
  have hsumΔ : ∑ _j ∈ Finset.range (K N), Δ ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKΔ]; linarith
  set cK := cKerShort n (Real.sqrt (min (2 - |E|) 1)) with hcK
  have hcK0 : 0 ≤ cK := cKerShort_nonneg n (Real.sqrt_nonneg _)
  set Mbig : ℝ := (N : ℝ) + (N : ℝ) ^ n + CK + 1 with hMbig
  set Mc := Mc514 d N n ε₁ τ' CK with hMc
  have hMc0 : 0 ≤ Mc := by
    rw [hMc]; unfold Mc514
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
    have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    positivity
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hNe : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hAv : 1 ≤ (band d).scale E N (v N) := hA (v N) (hs0.trans hsv.le) le_rfl
  -- per-step bounds
  have hstep : ∀ j ∈ Finset.range (K N),
      Δ * (kappa514 (d.L N) n E Kd u (j + 1) (K N)
            * dDr514 d E N n (u j) ε₁ τ' D' Φ CK
                (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
          + eps514 n u (j + 1) (K N)
            * driftErr514 d N m (CK + 1) (MD514 d E N n (CK + 1) (u j)) D')
        ≤ cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (Δ / etaT E (u j))
          + Δ * (cK * Kd ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n)
            + (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mbig D') := by
    intro j hj
    have hjK : j < K N := Finset.mem_range.mp hj
    have hj0 := hu0 j hjK.le
    have hj1 := hu1 j hjK.le
    have hjj : u j ≤ u (j + 1) := by
      rw [hu]; unfold time; push_cast; nlinarith
    have hj1K : u (j + 1) ≤ u (K N) := by
      rw [hu]; unfold time
      have : ((j + 1 : ℕ) : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hjK
      nlinarith
    have hAj : 1 ≤ (band d).scale E N (u j) := hA (u j) hj0 (hmem j hjK.le).2
    have hAj0 : 0 < (band d).scale E N (u j) := lt_of_lt_of_le one_pos hAj
    have hηj := inv_eta_le_of hE hv1 hη (hmem j hjK.le).2
    have hηj0 : 0 < etaT E (u j) := etaT_pos hE hj1
    -- `MD_j ≤ Mbig`, `B_j ≤ Mbig N^n`
    have hMD : MD514 d E N n (CK + 1) (u j) ≤ Mbig := by
      unfold MD514
      have : (etaT E (u j))⁻¹ ^ n ≤ (N : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hηj.1 n
      rw [hMbig]; linarith
    have hMD0 : 0 ≤ MD514 d E N n (CK + 1) (u j) := by unfold MD514; positivity
    have hAjN : (band d).scale E N (u j) ≤ N := (scale_le_LW d hE N hj0 hj1).trans hLW
    have hB : MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n ≤ Mbig * (N : ℝ) ^ n :=
      mul_le_mul hMD (pow_le_pow_left₀ hAj0.le hAjN n) (by positivity) (by rw [hMbig]; positivity)
    -- the sharp main part
    have hsharp := kappa514_succ_mul_scale_pow_le d hE N n hKd u j (K N) hj0 hjj hj1K
      (by rw [huK]; exact hv1)
    rw [huK] at hsharp
    have hκ0 : 0 ≤ kappa514 (d.L N) n E Kd u (j + 1) (K N) :=
      kappa514_nonneg (d.three_le_L N) hKd u (hj0.trans hjj) (hu1 (j + 1) (by omega))
        (hu0 (K N) le_rfl) (hu1 (K N) le_rfl)
    have hκmax : kappa514 (d.L N) n E Kd u (j + 1) (K N) ≤ cK * Kd ^ n * (N : ℝ) ^ n := by
      have h := kappa514_le_max d hE N n hKd u (j + 1) (K N) (hj0.trans hjj)
        (hu1 (j + 1) (by omega)) (hu0 (K N) le_rfl) (hu1 (K N) le_rfl) (by rw [huK]; exact hAv)
      have hA1N : (band d).scale E N (u (j + 1)) ≤ N :=
        (scale_le_LW d hE N (hj0.trans hjj) (hu1 (j + 1) (by omega))).trans hLW
      have hA10 : 0 < (band d).scale E N (u (j + 1)) :=
        (band d).scale_pos' hE N (hj0.trans hjj) (hu1 (j + 1) (by omega))
      refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA10.le hA1N n) (by positivity))
    have hEc : Ec514 d N n ε₁ D' Φ (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
        ≤ Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n) := by
      unfold Ec514
      have : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by positivity
      nlinarith
    have hEc0 : 0 ≤ Ec514 d N n ε₁ D' Φ (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) := by
      unfold Ec514; positivity
    have hsplit := dDr514_eq d E N n (u j) ε₁ τ' D' Φ CK
      (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
    have hmain : kappa514 (d.L N) n E Kd u (j + 1) (K N)
          * dDr514 d E N n (u j) ε₁ τ' D' Φ CK
              (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
        ≤ cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (etaT E (u j))⁻¹
          + cK * Kd ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n) := by
      rw [hsplit]
      have e1 : kappa514 (d.L N) n E Kd u (j + 1) (K N)
          * (Mc514 d N n ε₁ τ' CK * Φ * (etaT E (u j))⁻¹ * ((band d).scale E N (u j))⁻¹ ^ n
            + Ec514 d N n ε₁ D' Φ (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n))
          = Mc * Φ * (etaT E (u j))⁻¹
              * (kappa514 (d.L N) n E Kd u (j + 1) (K N) * ((band d).scale E N (u j))⁻¹ ^ n)
            + kappa514 (d.L N) n E Kd u (j + 1) (K N)
              * Ec514 d N n ε₁ D' Φ (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) := by
        rw [hMc]; ring
      have e0 : dDr514 d E N n (u j) ε₁ τ' D' Φ CK
            (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
          = Mc514 d N n ε₁ τ' CK * Φ * (etaT E (u j))⁻¹ * ((band d).scale E N (u j))⁻¹ ^ n
            + Ec514 d N n ε₁ D' Φ (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) := by
        rw [hsplit]; unfold Mc514 Ec514; ring
      rw [← hsplit, e0, e1]
      have hq : 0 ≤ Mc * Φ * (etaT E (u j))⁻¹ := by positivity
      have t1 := mul_le_mul_of_nonneg_left hsharp hq
      have t2 := mul_le_mul hκmax hEc hEc0 (by positivity)
      have e2 : Mc * Φ * (etaT E (u j))⁻¹ * (cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n
            * ((band d).scale E N (v N))⁻¹ ^ n)
          = cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (etaT E (u j))⁻¹ := by
        rw [hcK]; ring
      linarith
    have heps : eps514 n u (j + 1) (K N) * driftErr514 d N m (CK + 1) (MD514 d E N n (CK + 1) (u j)) D'
        ≤ (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mbig D' := by
      have he := eps514_le (n := n) u (hj0.trans hjj) (hu1 (j + 1) (by omega)) (hu1 (K N) le_rfl)
        (by simpa only [huK] using (inv_eta_le_of hE hv1 hη le_rfl).2)
      have hdE : driftErr514 d N m (CK + 1) (MD514 d E N n (CK + 1) (u j)) D'
          ≤ driftErr514 d N m (CK + 1) Mbig D' := by
        unfold driftErr514
        have : (0 : ℝ) ≤ (d.W N : ℝ) * ((m : ℝ) + 2) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
          positivity
        have : (0 : ℝ) ≤ (m : ℝ) * (2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ)
            * (d.W N : ℝ) ^ (-D')) := by positivity
        have : (0 : ℝ) ≤ 2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
          positivity
        nlinarith
      have hd0 := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) hMD0
      exact mul_le_mul he hdE hd0 (by positivity)
    have hΔdiv : Δ * (cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (etaT E (u j))⁻¹)
        = cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (Δ / etaT E (u j)) := by
      rw [div_eq_mul_inv]; ring
    have key := mul_le_mul_of_nonneg_left (add_le_add hmain heps) hΔ0
    have e : Δ * ((cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (etaT E (u j))⁻¹
          + cK * Kd ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n))
          + (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mbig D')
        = cK * Kd ^ n * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (Δ / etaT E (u j))
          + Δ * (cK * Kd ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n)
            + (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mbig D') := by
      rw [div_eq_mul_inv]; ring
    rw [e] at key
    exact key
  have htot := Finset.sum_le_sum hstep
  rw [Finset.mul_sum]
  refine htot.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hE0 : 0 ≤ cK * Kd ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n)
      + (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mbig D' := by
    have : 0 ≤ Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n) := by
      unfold Ec514; rw [hMbig]; positivity
    have := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) (by rw [hMbig]; positivity :
      (0 : ℝ) ≤ Mbig)
    positivity
  have := mul_le_mul_of_nonneg_right hsumΔ hE0
  linarith


/-- `R^m ≤ A_{u_i}^m` for the (7.14) ratio `R = (1-u_i)ℓ_i/((1-u_k)ℓ_k)` when `A_{u_k} ≥ 1`. -/
theorem ratio514_pow_le {E : ℝ} (hE : |E| < 2) (N m : ℕ) (u : ℕ → ℝ) (i k : ℕ)
    (hi0 : 0 ≤ u i) (hi1 : u i < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1)
    (hAk : 1 ≤ (band d).scale E N (u k)) :
    ((1 - u i) * ellHat (d.L N) ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat (d.L N) ((u k : ℝ) : ℂ))) ^ m
      ≤ (band d).scale E N (u i) ^ m := by
  have hAi : 0 < (band d).scale E N (u i) := (band d).scale_pos' hE N hi0 hi1
  have hr := scale_ratio_pow (d := d) (N := N) hE hi0 hi1 hk0 hk1 m
  set R := (1 - u i) * ellHat (d.L N) ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat (d.L N) ((u k : ℝ) : ℂ))
    with hR
  have hai : ((band d).scale E N (u i))⁻¹ ^ m * (band d).scale E N (u i) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hAi.ne', one_pow]
  have hRn : R ^ m = ((band d).scale E N (u k))⁻¹ ^ m * (band d).scale E N (u i) ^ m := by
    calc R ^ m = R ^ m * (((band d).scale E N (u i))⁻¹ ^ m * (band d).scale E N (u i) ^ m) := by
          rw [hai, mul_one]
      _ = (R ^ m * ((band d).scale E N (u i))⁻¹ ^ m) * (band d).scale E N (u i) ^ m := by ring
      _ = _ := by rw [hr]
  rw [hRn]
  have hk : ((band d).scale E N (u k))⁻¹ ^ m ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hAk)
  have : 0 ≤ (band d).scale E N (u i) ^ m := by positivity
  nlinarith

/-- Reindexing the time sum: `Σ_{j<K} Δ/η_{u_{j+1}} ≤ Σ_{j<K} Δ/η_{u_j} + Δ/η_{u_K}`. -/
theorem sum_succ_le {K : ℕ} (f : ℕ → ℝ) (hf0 : 0 ≤ f 0) :
    ∑ j ∈ Finset.range K, f (j + 1) ≤ ∑ j ∈ Finset.range K, f j + f K := by
  have h := Finset.sum_range_succ' f K
  have h2 := Finset.sum_range_succ f K
  linarith

set_option maxHeartbeats 1600000 in
/-- **(5.93) for the martingale part, sharp (5.105)**: the QV sum at the target `u_K = v` is at
most `C·Φq·A_v^{-2n}·(Σ_j Δ/η_{u_j} + Δ/η_v)` plus `W^{-D''}` tails. -/
theorem tb_qv {n : ℕ} [NeZero n] {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hA : ∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale E N u)
    (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) {τ' D'' Φq : ℝ} (hΦq : 0 ≤ Φq)
    (a : LoopArg (d.L N) n) :
    ∑ j ∈ Finset.range (K N), (cQV514 d E s v K N n τ' D'' Φq (K N) a j : ℝ)
      ≤ cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ (n + n)
          * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * Φq)
          * ((band d).scale E N (v N))⁻¹ ^ (2 * n)
          * (∑ j ∈ Finset.range (K N), step s v K N / etaT E (time s v K N j)
              + step s v K N / etaT E (v N))
        + (cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ (n + n)
            * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n)) * eeHermErr d N n D'' := by
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have huK : u (K N) = v N := time_last s v K N hK0
  have hKΔ : (K N : ℝ) * Δ = v N - s N := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step; field_simp
  set cK2 := cKerShort (n + n) (Real.sqrt (min (2 - |E|) 1)) with hcK2
  have hcK20 : 0 ≤ cK2 := cKerShort_nonneg _ (Real.sqrt_nonneg _)
  set Wτ := ((d.W N : ℝ) ^ τ') with hWτ
  have hWτ0 : 0 ≤ Wτ := Real.rpow_nonneg (by positivity) _
  set Cm := cK2 * Wτ ^ (n + n) * (6 * Real.exp 1 * (n : ℝ) ^ 2 * Wτ * Φq) with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set ee := eeHermErr d N n D'' with hee
  have hee0 : 0 ≤ ee := eeHermErr_nonneg d N n D''
  have hAv : 1 ≤ (band d).scale E N (v N) := hA (v N) (hs0.trans hsv.le) le_rfl
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hstep : ∀ j ∈ Finset.range (K N), (cQV514 d E s v K N n τ' D'' Φq (K N) a j : ℝ)
      ≤ Cm * ((band d).scale E N (v N))⁻¹ ^ (2 * n) * (Δ / etaT E (u (j + 1)))
        + Δ * ((cK2 * Wτ ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n)) * ee) := by
    intro j hj
    have hjK : j < K N := Finset.mem_range.mp hj
    have hj10 := hu0 (j + 1) (by omega)
    have hj11 := hu1 (j + 1) (by omega)
    have hj1K : u (j + 1) ≤ u (K N) := by
      rw [hu]; unfold time
      have : ((j + 1 : ℕ) : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hjK
      have : 0 ≤ step s v K N := hΔ0
      nlinarith
    have hpos := qvBdNonAlt_pos d hE (N := N) (n := n) (τ := τ') (D := D'')
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) hj10 hj1K (hu1 (K N) le_rfl) hΦq
    unfold cQV514
    rw [Real.coe_toNNReal _ (mul_nonneg hΔ0 hpos.le)]
    unfold qvBdNonAlt
    rw [huK]
    have hR := ratio514_pow_le d hE N (n + n) u (j + 1) (K N) hj10 hj11 (hu0 (K N) le_rfl)
      (hu1 (K N) le_rfl) (by rw [huK]; exact hAv)
    rw [huK] at hR
    have hA1N : (band d).scale E N (u (j + 1)) ≤ N :=
      (scale_le_LW d hE N hj10 hj11).trans hLW
    have hA10 : 0 < (band d).scale E N (u (j + 1)) := (band d).scale_pos' hE N hj10 hj11
    have hR' := hR.trans (pow_le_pow_left₀ hA10.le hA1N _)
    have hr := eps514_le (n := n + n) u hj10 hj11 (hu1 (K N) le_rfl)
      (by simpa only [huK] using (inv_eta_le_of hE hv1 hη le_rfl).2)
    unfold eps514 at hr
    rw [huK] at hr
    have hR0 : 0 ≤ ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
        / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ (n + n) := by
      have h1 : 0 < 1 - u (j + 1) := by linarith
      have h2 : 0 < 1 - v N := by linarith
      have h3 : 0 < ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) :=
        Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hj11
      have h4 : 0 < ellHat (d.L N) ((v N : ℝ) : ℂ) :=
        Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hv1
      positivity
    have e : Δ * (cK2 * Wτ ^ (n + n)
          * (6 * Real.exp 1 * (n : ℝ) ^ 2 * Wτ * Φq * (etaT E (u (j + 1)))⁻¹
              * ((band d).scale E N (v N))⁻¹ ^ (2 * n)
            + ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
                / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ (n + n) * ee)
          + ((1 - u (j + 1)) / (1 - v N)) ^ (n + n) * ee)
        = Cm * ((band d).scale E N (v N))⁻¹ ^ (2 * n) * (Δ / etaT E (u (j + 1)))
          + Δ * ((cK2 * Wτ ^ (n + n)
            * ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
                / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ (n + n)
            + ((1 - u (j + 1)) / (1 - v N)) ^ (n + n)) * ee) := by
      rw [hCm, div_eq_mul_inv]; ring
    rw [e]
    have hc0 : 0 ≤ cK2 * Wτ ^ (n + n) := by positivity
    have t1 : cK2 * Wτ ^ (n + n)
            * ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
                / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ (n + n)
            + ((1 - u (j + 1)) / (1 - v N)) ^ (n + n)
          ≤ cK2 * Wτ ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n) :=
      add_le_add (mul_le_mul_of_nonneg_left hR' hc0) hr
    have t2 := mul_le_mul_of_nonneg_right t1 hee0
    have t3 := mul_le_mul_of_nonneg_left t2 hΔ0
    linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hsucc := sum_succ_le (K := K N) (fun j => Δ / etaT E (u j))
    (div_nonneg hΔ0 (etaT_pos hE (hu1 0 (Nat.zero_le _))).le)
  simp only [huK] at hsucc
  have hsumΔ : ∑ _j ∈ Finset.range (K N), Δ ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKΔ]; linarith
  have hX0 : 0 ≤ (cK2 * Wτ ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n)) * ee := by positivity
  have hA0 : 0 ≤ Cm * ((band d).scale E N (v N))⁻¹ ^ (2 * n) := by
    have := (band d).scale_pos' hE N (hs0.trans hsv.le) hv1
    positivity
  have t1 := mul_le_mul_of_nonneg_left hsucc hA0
  have t2 := mul_le_mul_of_nonneg_right hsumΔ hX0
  rw [hCm] at t1 hA0
  linarith


/-- **(5.93) for the initial datum, sharp**: `κ_{0,k}·‖A_0‖ ≤ cKerShort Kd^n N^{ε₁} A_{u_k}^{-n}` when
`‖A_0‖ ≤ N^{ε₁} A_{u_0}^{-n}`. -/
theorem tb_init {E : ℝ} (hE : |E| < 2) (N n : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd) (u : ℕ → ℝ) (k : ℕ)
    (h00 : 0 ≤ u 0) (h01 : u 0 < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1) {X0 ε₁ : ℝ}
    (hX : X0 ≤ (N : ℝ) ^ ε₁ * ((band d).scale E N (u 0))⁻¹ ^ n) :
    kappa514 (d.L N) n E Kd u 0 k * X0
      ≤ cKerShort n (Real.sqrt (min (2 - |E|) 1)) * Kd ^ n * (N : ℝ) ^ ε₁
          * ((band d).scale E N (u k))⁻¹ ^ n := by
  have hκ0 := kappa514_nonneg (n := n) (E := E) (d.three_le_L N) hKd u h00 h01 hk0 hk1
  have h := kappa514_mul_scale_pow_eq d hE N n Kd u 0 k h00 h01 hk0 hk1
  calc kappa514 (d.L N) n E Kd u 0 k * X0
      ≤ kappa514 (d.L N) n E Kd u 0 k * ((N : ℝ) ^ ε₁ * ((band d).scale E N (u 0))⁻¹ ^ n) :=
        mul_le_mul_of_nonneg_left hX hκ0
    _ = (N : ℝ) ^ ε₁ * (kappa514 (d.L N) n E Kd u 0 k * ((band d).scale E N (u 0))⁻¹ ^ n) := by
        ring
    _ = _ := by rw [h]; ring

theorem stepErrN_nonneg {E : ℝ} (hE : |E| < 2) (N n : ℕ) {uk uk1 Δ Bk : ℝ} (huk : uk ≤ uk1)
    (hu1 : uk1 < 1) (hΔ0 : 0 ≤ Δ) (hBk0 : 0 ≤ Bk) :
    0 ≤ stepErrN (band d) E N n uk uk1 Δ Bk := by
  have h1u : 0 < 1 - uk1 := by linarith
  have hm := mE_im_pos hE
  have hx0 : 0 ≤ Δ * (1 - uk1)⁻¹ := by positivity
  have hb : 0 ≤ (1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹ := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * (1 - uk1)⁻¹ by linarith) n
    have e : (n : ℝ) * Δ * (1 - uk1)⁻¹ = (n : ℝ) * (Δ * (1 - uk1)⁻¹) := by ring
    rw [e]; linarith
  have hI : 0 ≤ ∫ x, ‖Xmat (band d).toDims N x‖ ∂ (P (band d).toDims) :=
    integral_nonneg fun _ => norm_nonneg _
  unfold stepErrN
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · unfold zMotionZLip; positivity
  · have : 0 ≤ zMotionLip ((band d).L N) ((band d).W N) n |(zt E uk).im| (mSigma E) := by
      unfold zMotionLip; positivity
    have : 0 ≤ genPtLip ((band d).L N) ((band d).W N) n |(zt E uk).im| (mSigma E) := by
      unfold genPtLip driftLip zMotionLip; positivity
    have : 0 ≤ Δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hΔ0 _
    positivity
  · positivity
  · have : 0 ≤ (n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2 := by positivity
    have : 0 ≤ |(zt E uk).im|⁻¹ ^ n * ((band d).W N : ℝ)⁻¹ ^ (n - 1) + Bk := by positivity
    have : 0 ≤ (n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹) := by linarith
    positivity

set_option maxHeartbeats 1600000 in
/-- **The remainder term**: `Σ_{j<K} (1+(1-u_K)^{-1})^n stepErr_j ≤ (1+N)^n·C_R (2N)^{2n+16}·Δ^{1/2}`. -/
theorem tb_R {n : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hW : (d.W N : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hN1 : (1 : ℝ) ≤ N) {CK : ℝ} (hCK : 0 ≤ CK)
    (hCKN : CK + 1 ≤ 2 * (N : ℝ)) (hΔN : step s v K N * (2 * (N : ℝ)) ≤ 1) :
    ∑ j ∈ Finset.range (K N), (1 + (1 - time s v K N (K N))⁻¹) ^ n
        * stepErrN (band d) E N n (time s v K N j) (time s v K N (j + 1)) (step s v K N) (CK + 1)
      ≤ (1 + (N : ℝ)) ^ n * (100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * (2 * (N : ℝ)) ^ (2 * n + 16))
          * step s v K N ^ ((1 : ℝ) / 2) := by
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have huK : u (K N) = v N := time_last s v K N hK0
  have hKΔ : (K N : ℝ) * Δ = v N - s N := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step; field_simp
  set CR := 100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * (2 * (N : ℝ)) ^ (2 * n + 16) with hCR
  have hCR0 : 0 ≤ CR := by positivity
  have hcoarse : (1 + (1 - u (K N))⁻¹) ^ n ≤ (1 + (N : ℝ)) ^ n := by
    rw [huK]
    have h := (inv_eta_le_of hE hv1 hη le_rfl).2
    have h0 : 0 ≤ (1 - v N)⁻¹ := inv_nonneg.mpr (by linarith)
    exact pow_le_pow_left₀ (by positivity) (by linarith) n
  have hstep : ∀ j ∈ Finset.range (K N), (1 + (1 - u (K N))⁻¹) ^ n
      * stepErrN (band d) E N n (u j) (u (j + 1)) Δ (CK + 1)
        ≤ (1 + (N : ℝ)) ^ n * CR * Δ ^ ((3 : ℝ) / 2) := by
    intro j hj
    have hjK : j < K N := Finset.mem_range.mp hj
    have hjj : u j ≤ u (j + 1) := by rw [hu]; unfold time; push_cast; nlinarith
    have hη1 := (inv_eta_le_of hE hv1 hη (hmem (j + 1) (by omega)).2).1
    have hSE := stepErrN_le d hE N n (hu0 j hjK.le) hjj (hu1 (j + 1) (by omega)) hΔ0
      (by linarith : (0 : ℝ) ≤ CK + 1) (by linarith : (1 : ℝ) ≤ 2 * N) (by linarith) (by linarith)
      (by linarith) (by linarith) hCKN hΔN
    have hSE0 := stepErrN_nonneg d hE N n hjj (hu1 (j + 1) (by omega)) hΔ0
      (by linarith : (0 : ℝ) ≤ CK + 1)
    have hc0 : 0 ≤ (1 + (1 - u (K N))⁻¹) ^ n := by
      have : 0 ≤ (1 - u (K N))⁻¹ := inv_nonneg.mpr (by linarith [hu1 (K N) le_rfl])
      positivity
    calc (1 + (1 - u (K N))⁻¹) ^ n * stepErrN (band d) E N n (u j) (u (j + 1)) Δ (CK + 1)
        ≤ (1 + (N : ℝ)) ^ n * (Δ ^ (3 / 2 : ℝ) * CR) :=
          mul_le_mul hcoarse hSE hSE0 (by positivity)
      _ = (1 + (N : ℝ)) ^ n * CR * Δ ^ ((3 : ℝ) / 2) := by ring
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h32 : Δ ^ ((3 : ℝ) / 2) = Δ * Δ ^ ((1 : ℝ) / 2) := by
    rcases hΔ0.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one]
  rw [h32]
  have hKΔ1 : (K N : ℝ) * Δ ≤ 1 := by rw [hKΔ]; linarith
  have hX0 : 0 ≤ (1 + (N : ℝ)) ^ n * CR * Δ ^ ((1 : ℝ) / 2) := by
    have := Real.rpow_nonneg hΔ0 ((1 : ℝ) / 2)
    positivity
  have e : (K N : ℝ) * ((1 + (N : ℝ)) ^ n * CR * (Δ * Δ ^ ((1 : ℝ) / 2)))
      = ((K N : ℝ) * Δ) * ((1 + (N : ℝ)) ^ n * CR * Δ ^ ((1 : ℝ) / 2)) := by ring
  rw [e]
  calc ((K N : ℝ) * Δ) * ((1 + (N : ℝ)) ^ n * CR * Δ ^ ((1 : ℝ) / 2))
      ≤ 1 * ((1 + (N : ℝ)) ^ n * CR * Δ ^ ((1 : ℝ) / 2)) := mul_le_mul_of_nonneg_right hKΔ1 hX0
    _ = _ := one_mul _


theorem sqrt_add_le514 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    have h3 : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y :=
        Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

set_option maxHeartbeats 4000000 in
/-- **The (5.93) budget** at a fixed `N`: on the good event (`τ = K`, `‖A_0‖ ≤ N^{ε₁}A_s^{-n}`),
the assembly bound is `≤ N^ε (Λ^{1/2} + Φ) A_v^{-n}`, given the regime facts and the absorption
inequalities (each of which holds for all large `N`, see §5). The sharp kernel
enters only through `tb_init`/`tb_drift`/`tb_qv`: **no `η_s/η_t` prefactor** on any main term. -/
theorem budget514 {m : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    {ε ε₁ τ' D' D_Y Λ Φ CK X0 : ℝ} (a : LoopArg (d.L N) (m + 2))
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hN1 : (1 : ℝ) ≤ N) (hW : (d.W N : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hA : ∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale E N u)
    (hΛ : 1 ≤ Λ) (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK) (hCKN : CK + 1 ≤ 2 * (N : ℝ))
    (hΔN : step s v K N * (2 * (N : ℝ)) ≤ 1)
    (hlog : ∑ j ∈ Finset.range (K N), step s v K N / etaT E (time s v K N j)
      ≤ (mE E).im⁻¹ * Real.log N)
    (hX0 : X0 ≤ (N : ℝ) ^ ε₁ * ((band d).scale E N (s N))⁻¹ ^ (m + 2))
    (ha1 : cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
      * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε / 8)
    (ha2 : cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
      * Mc514 d N (m + 2) ε₁ τ' CK * ((mE E).im⁻¹ * Real.log N) ≤ (N : ℝ) ^ ε / 8)
    (ha3 : (N : ℝ) ^ ε₁ * Real.sqrt (cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1))
      * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
      * (6 * Real.exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
      * ((mE E).im⁻¹ * Real.log N + 1)) ≤ (N : ℝ) ^ ε / 8)
    (he1 : (N : ℝ) ^ (m + 2) * (d.W N : ℝ) ^ (-D') ≤ (N : ℝ) ^ ε / 16 * (N : ℝ)⁻¹ ^ (m + 2))
    (he2 : cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
        * (N : ℝ) ^ (m + 2)
        * Ec514 d N (m + 2) ε₁ D' Φ (((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) * (N : ℝ) ^ (m + 2))
      + (N : ℝ) ^ (m + 2) * driftErr514 d N m (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) D'
      ≤ (N : ℝ) ^ ε / 16 * (1 + Φ) * (N : ℝ)⁻¹ ^ (m + 2))
    (he3 : (N : ℝ) ^ ε₁ * Real.sqrt ((cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1))
        * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2)) * (N : ℝ) ^ ((m + 2) + (m + 2))
        + (N : ℝ) ^ ((m + 2) + (m + 2))) * eeHermErr d N (m + 2) (D' - 1))
      ≤ (N : ℝ) ^ ε / 16 * (N : ℝ)⁻¹ ^ (m + 2))
    (he4 : (N : ℝ) ^ (-D_Y) ≤ (N : ℝ) ^ ε / 16 * (N : ℝ)⁻¹ ^ (m + 2))
    (he5 : (1 + (N : ℝ)) ^ (m + 2) * (100 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2)
        * (2 * (N : ℝ)) ^ (2 * (m + 2) + 16)) * step s v K N ^ ((1 : ℝ) / 2)
      ≤ (N : ℝ) ^ ε / 16 * (N : ℝ)⁻¹ ^ (m + 2)) :
    kappa514 (d.L N) (m + 2) E (4 * (d.W N : ℝ) ^ τ') (time s v K N) 0 (K N) * X0
      + eps514 (m + 2) (time s v K N) 0 (K N) * (d.W N : ℝ) ^ (-D')
      + step s v K N * ∑ j ∈ Finset.range (K N),
          (kappa514 (d.L N) (m + 2) E (4 * (d.W N : ℝ) ^ τ') (time s v K N) (j + 1) (K N)
              * dDr514 d E N (m + 2) (time s v K N j) ε₁ τ' D' Φ CK
                  (MD514 d E N (m + 2) (CK + 1) (time s v K N j)
                    * (band d).scale E N (time s v K N j) ^ (m + 2))
            + eps514 (m + 2) (time s v K N) (j + 1) (K N)
              * driftErr514 d N m (CK + 1) (MD514 d E N (m + 2) (CK + 1) (time s v K N j)) D')
      + (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range (K N),
          (cQV514 d E s v K N (m + 2) τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ))
      + (N : ℝ) ^ (-D_Y)
      + ∑ j ∈ Finset.range (K N), (1 + (1 - time s v K N (K N))⁻¹) ^ (m + 2)
          * stepErrN (band d) E N (m + 2) (time s v K N j) (time s v K N (j + 1))
              (step s v K N) (CK + 1)
      ≤ (N : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) * ((band d).scale E N (v N) ^ (m + 2))⁻¹ := by
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hu00 : u 0 = s N := time_zero s v K N
  have huK : u (K N) = v N := time_last s v K N hK0
  have hAv : 1 ≤ (band d).scale E N (v N) := hA (v N) (hs0.trans hsv.le) le_rfl
  have hAv0 : 0 < (band d).scale E N (v N) := lt_of_lt_of_le one_pos hAv
  have hAvN : (band d).scale E N (v N) ≤ N := (scale_le_LW d hE N (hs0.trans hsv.le) hv1).trans hLW
  set X := ((band d).scale E N (v N))⁻¹ ^ (m + 2) with hX
  have hX0' : 0 ≤ X := by positivity
  have hXN : (N : ℝ)⁻¹ ^ (m + 2) ≤ X :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ hAv0 hAvN) (m + 2)
  have hNe : (0 : ℝ) ≤ (N : ℝ) ^ ε := Real.rpow_nonneg (by positivity) _
  have hsqΛ : 1 ≤ Λ ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  have hgoalX : (N : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) * ((band d).scale E N (v N) ^ (m + 2))⁻¹
      = (N : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) * X := by rw [hX, inv_pow]
  rw [hgoalX]
  have hKd0 : (0 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by
    have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) τ'; positivity
  -- T1
  have t1 := tb_init d hE N (m + 2) hKd0 u (K N) (by rw [hu00]; exact hs0) (by rw [hu00]; linarith)
    (by rw [huK]; linarith) (by rw [huK]; exact hv1) (X0 := X0) (ε₁ := ε₁) (by rw [hu00]; exact hX0)
  rw [huK] at t1
  have T1 : kappa514 (d.L N) (m + 2) E (4 * (d.W N : ℝ) ^ τ') u 0 (K N) * X0
      ≤ (N : ℝ) ^ ε / 8 * X := by
    refine t1.trans ?_
    exact mul_le_mul_of_nonneg_right ha1 hX0'
  -- T2
  have T2 : eps514 (m + 2) u 0 (K N) * (d.W N : ℝ) ^ (-D') ≤ (N : ℝ) ^ ε / 16 * X := by
    have he := eps514_le (n := m + 2) u (by rw [hu00]; exact hs0) (by rw [hu00]; linarith)
      (by rw [huK]; exact hv1) (by simpa only [huK] using (inv_eta_le_of hE hv1 hη le_rfl).2)
    have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
    calc eps514 (m + 2) u 0 (K N) * (d.W N : ℝ) ^ (-D') ≤ (N : ℝ) ^ (m + 2) * (d.W N : ℝ) ^ (-D') :=
          mul_le_mul_of_nonneg_right he hWD
      _ ≤ (N : ℝ) ^ ε / 16 * (N : ℝ)⁻¹ ^ (m + 2) := he1
      _ ≤ (N : ℝ) ^ ε / 16 * X := mul_le_mul_of_nonneg_left hXN (by positivity)
  -- T3
  have t3 := tb_drift d (m := m) hE s v K N hs0 hsv hv1 hK1 hη hA hLW hN1 (ε₁ := ε₁) (τ' := τ')
    (D' := D') hΦ hCK hKd0
  have hMc0 : 0 ≤ Mc514 d N (m + 2) ε₁ τ' CK := by
    unfold Mc514
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
    have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    positivity
  have hcK0 : 0 ≤ cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) := cKerShort_nonneg _ (Real.sqrt_nonneg _)
  have T3 : Δ * ∑ j ∈ Finset.range (K N),
          (kappa514 (d.L N) (m + 2) E (4 * (d.W N : ℝ) ^ τ') u (j + 1) (K N)
              * dDr514 d E N (m + 2) (u j) ε₁ τ' D' Φ CK
                  (MD514 d E N (m + 2) (CK + 1) (u j) * (band d).scale E N (u j) ^ (m + 2))
            + eps514 (m + 2) u (j + 1) (K N)
              * driftErr514 d N m (CK + 1) (MD514 d E N (m + 2) (CK + 1) (u j)) D')
      ≤ (N : ℝ) ^ ε / 8 * Φ * X + (N : ℝ) ^ ε / 16 * (1 + Φ) * X := by
    refine t3.trans ?_
    have h1 : cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
          * Mc514 d N (m + 2) ε₁ τ' CK * Φ * X * ∑ j ∈ Finset.range (K N), Δ / etaT E (u j)
        ≤ (N : ℝ) ^ ε / 8 * Φ * X := by
      have h0 : 0 ≤ cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
          * Mc514 d N (m + 2) ε₁ τ' CK := by positivity
      have := mul_le_mul_of_nonneg_left hlog h0
      have e : cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
            * Mc514 d N (m + 2) ε₁ τ' CK * Φ * X * ∑ j ∈ Finset.range (K N), Δ / etaT E (u j)
          = (cKerShort (m + 2) (Real.sqrt (min (2 - |E|) 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2)
            * Mc514 d N (m + 2) ε₁ τ' CK * ∑ j ∈ Finset.range (K N), Δ / etaT E (u j)) * (Φ * X) := by
        ring
      rw [e]
      have h2 := this.trans ha2
      calc _ ≤ (N : ℝ) ^ ε / 8 * (Φ * X) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring
    have h2 : (1 + Φ) * (N : ℝ)⁻¹ ^ (m + 2) ≤ (1 + Φ) * X := mul_le_mul_of_nonneg_left hXN (by linarith)
    have he2' := he2.trans (by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ ε / 16)
      calc (N : ℝ) ^ ε / 16 * (1 + Φ) * (N : ℝ)⁻¹ ^ (m + 2)
          = (N : ℝ) ^ ε / 16 * ((1 + Φ) * (N : ℝ)⁻¹ ^ (m + 2)) := by ring
        _ ≤ (N : ℝ) ^ ε / 16 * ((1 + Φ) * X) := this
        _ = (N : ℝ) ^ ε / 16 * (1 + Φ) * X := by ring)
    linarith
  -- T4
  have t4 := tb_qv d (n := m + 2) hE s v K N hs0 hsv hv1 hK1 hη hA hLW (τ' := τ') (D'' := D' - 1)
    (Φq := 2 * (N : ℝ) ^ ε₁ * Λ) (by positivity) a
  have hSv : ∑ j ∈ Finset.range (K N), Δ / etaT E (u j) + Δ / etaT E (v N)
      ≤ (mE E).im⁻¹ * Real.log N + 1 := by
    have hv := etaT_pos hE hv1
    have : Δ / etaT E (v N) ≤ 1 := by
      rw [div_eq_mul_inv]
      have h1 : Δ * (etaT E (v N))⁻¹ ≤ Δ * N := mul_le_mul_of_nonneg_left hη hΔ0
      nlinarith
    linarith
  set Z := cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
      * (6 * Real.exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
      * ((mE E).im⁻¹ * Real.log N + 1) with hZ
  set Qe := (cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
      * (N : ℝ) ^ ((m + 2) + (m + 2)) + (N : ℝ) ^ ((m + 2) + (m + 2))) * eeHermErr d N (m + 2) (D' - 1) with hQe
  have hZ0 : 0 ≤ Z := by
    have hc := cKerShort_nonneg ((m + 2) + (m + 2)) (Real.sqrt_nonneg (min (2 - |E|) 1))
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
    have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    have hl : 0 ≤ (mE E).im⁻¹ * Real.log N + 1 := by
      have := Real.log_nonneg hN1
      have := (mE_im_pos hE).le
      positivity
    positivity
  have hQe0 : 0 ≤ Qe := by
    have hc := cKerShort_nonneg ((m + 2) + (m + 2)) (Real.sqrt_nonneg (min (2 - |E|) 1))
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
    have := eeHermErr_nonneg d N (m + 2) (D' - 1)
    positivity
  have hsum : ∑ j ∈ Finset.range (K N),
        (cQV514 d E s v K N (m + 2) τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ)
      ≤ Z * Λ * X ^ 2 + Qe := by
    refine t4.trans ?_
    have hX2 : ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 2)) = X ^ 2 := by rw [hX, ← pow_mul, mul_comm]
    rw [hX2]
    have hcoef0 : 0 ≤ cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
        * (6 * Real.exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁ * Λ)) * X ^ 2 := by
      have hc := cKerShort_nonneg ((m + 2) + (m + 2)) (Real.sqrt_nonneg (min (2 - |E|) 1))
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ Λ := by linarith
      positivity
    have := mul_le_mul_of_nonneg_left hSv hcoef0
    have e : Z * Λ * X ^ 2 = cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1))
        * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
        * (6 * Real.exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁ * Λ)) * X ^ 2
        * ((mE E).im⁻¹ * Real.log N + 1) := by rw [hZ]; ring
    rw [e]
    have e2 : cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
          * (6 * Real.exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁ * Λ)) * X ^ 2
          * (∑ j ∈ Finset.range (K N), Δ / etaT E (u j) + Δ / etaT E (v N))
        = cKerShort ((m + 2) + (m + 2)) (Real.sqrt (min (2 - |E|) 1)) * ((d.W N : ℝ) ^ τ') ^ ((m + 2) + (m + 2))
          * (6 * Real.exp 1 * ((m + 2 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁ * Λ))
          * X ^ 2 * (∑ j ∈ Finset.range (K N), Δ / etaT E (u j) + Δ / etaT E (v N)) := rfl
    linarith
  have T4 : (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range (K N),
        (cQV514 d E s v K N (m + 2) τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ))
      ≤ (N : ℝ) ^ ε / 8 * Λ ^ ((1 : ℝ) / 2) * X + (N : ℝ) ^ ε / 16 * X := by
    have hNe1 : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt (Z * Λ * X ^ 2 + Qe) ≤ Real.sqrt Z * Real.sqrt Λ * X + Real.sqrt Qe := by
      have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
      have hZΛ : 0 ≤ Z * Λ * X ^ 2 := by positivity
      refine (sqrt_add_le514 hZΛ hQe0).trans ?_
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Z * Λ), Real.sqrt_mul hZ0,
        Real.sqrt_sq hX0']
    have hsΛ : Real.sqrt Λ = Λ ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Λ
    have k1 : (N : ℝ) ^ ε₁ * (Real.sqrt Z * Real.sqrt Λ * X)
        ≤ (N : ℝ) ^ ε / 8 * Λ ^ ((1 : ℝ) / 2) * X := by
      have e : (N : ℝ) ^ ε₁ * (Real.sqrt Z * Real.sqrt Λ * X)
          = ((N : ℝ) ^ ε₁ * Real.sqrt Z) * (Λ ^ ((1 : ℝ) / 2) * X) := by rw [hsΛ]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_right ha3 (by positivity : (0 : ℝ) ≤ Λ ^ ((1 : ℝ) / 2) * X)
      calc _ ≤ (N : ℝ) ^ ε / 8 * (Λ ^ ((1 : ℝ) / 2) * X) := this
        _ = _ := by ring
    have k2 : (N : ℝ) ^ ε₁ * Real.sqrt Qe ≤ (N : ℝ) ^ ε / 16 * X :=
      he3.trans (mul_le_mul_of_nonneg_left hXN (by positivity))
    calc (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range (K N),
          (cQV514 d E s v K N (m + 2) τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ))
        ≤ (N : ℝ) ^ ε₁ * (Real.sqrt Z * Real.sqrt Λ * X + Real.sqrt Qe) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe1
      _ = (N : ℝ) ^ ε₁ * (Real.sqrt Z * Real.sqrt Λ * X) + (N : ℝ) ^ ε₁ * Real.sqrt Qe := by ring
      _ ≤ _ := add_le_add k1 k2
  -- `T5`, `T6`
  have T5 : (N : ℝ) ^ (-D_Y) ≤ (N : ℝ) ^ ε / 16 * X :=
    he4.trans (mul_le_mul_of_nonneg_left hXN (by positivity))
  have t6 := tb_R d (n := m + 2) hE s v K N hs0 hsv hv1 hK1 hη hW hL hcard hN1 hCK hCKN hΔN
  have T6 : ∑ j ∈ Finset.range (K N), (1 + (1 - u (K N))⁻¹) ^ (m + 2)
        * stepErrN (band d) E N (m + 2) (u j) (u (j + 1)) Δ (CK + 1) ≤ (N : ℝ) ^ ε / 16 * X := by
    refine t6.trans ?_
    refine le_trans ?_ (he5.trans (mul_le_mul_of_nonneg_left hXN (by positivity)))
    exact le_of_eq rfl
  -- total
  have hΦX : 0 ≤ Φ * X := by positivity
  have hX1 : X ≤ Λ ^ ((1 : ℝ) / 2) * X := le_mul_of_one_le_left hX0' hsqΛ
  nlinarith [T1, T2, T3, T4, T5, T6, hX1, hΦX, hNe]


end Budget514


end RBM.Gauss.Grid


/-! ## §5 : the endpoint

* asymptotic helpers `ev_rpow_le`/`ev_rpow_log_le`; the flow → grid transfer of stochastic
  domination (`stochDom_grid_of_flow514`, via `highProb_grid_of_flow`/`map_H_eq`);
* the Gaussian `Y` scale `PY514_le` (from `integral_norm_Xmat_pow_le514`);
* the eventual absorption of every regime inequality of `budget514`
  (`ev_ha1`–`ev_ha3`, `ev_he1`–`ev_he5`, `shXi_le`, `shD_le`, `step_Kc_le`, `ev_Kcard`). -/


namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Asymp

/-- `C·N^a ≤ N^b` for all large `N` when `a < b`. -/
theorem ev_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop C, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have h1 : (N : ℝ) ^ b = (N : ℝ) ^ (b - a) * (N : ℝ) ^ a := by
    rw [← Real.rpow_add hN0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hN0.le _)

/-- `C·N^a·(log N + 1) ≤ N^b` for all large `N` when `a < b`. -/
theorem ev_rpow_log_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a * (Real.log N + 1) ≤ (N : ℝ) ^ b := by
  set δ := (b - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  filter_upwards [ev_rpow_le (a := a + δ) (b := b) (by rw [hδ]; linarith)
    (max C 0 * (1 / δ + 1)), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1'
  have hlog : Real.log N ≤ (N : ℝ) ^ δ / δ := Real.log_le_rpow_div hN0.le hδ0
  have hNδ : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1' hδ0.le
  have hl : Real.log N + 1 ≤ (1 / δ + 1) * (N : ℝ) ^ δ := by
    have : (N : ℝ) ^ δ / δ = 1 / δ * (N : ℝ) ^ δ := by ring
    nlinarith
  have hCa : C * (N : ℝ) ^ a ≤ max C 0 * (N : ℝ) ^ a :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hN0.le _)
  have hM0 : 0 ≤ max C 0 * (N : ℝ) ^ a :=
    mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hN0.le _)
  calc C * (N : ℝ) ^ a * (Real.log N + 1)
      ≤ max C 0 * (N : ℝ) ^ a * (Real.log N + 1) :=
        mul_le_mul_of_nonneg_right hCa (by linarith)
    _ ≤ max C 0 * (N : ℝ) ^ a * ((1 / δ + 1) * (N : ℝ) ^ δ) :=
        mul_le_mul_of_nonneg_left hl hM0
    _ = max C 0 * (1 / δ + 1) * (N : ℝ) ^ (a + δ) := by
        rw [Real.rpow_add hN0]; ring
    _ ≤ (N : ℝ) ^ b := hN

/-- `W^x ≤ N^x` for `1 ≤ W ≤ N`, `x ≥ 0`, natural powers. -/
theorem rpow_pow_le_of_le {W N x : ℝ} (hW : 0 ≤ W) (hWN : W ≤ N) (hx : 0 ≤ x) (k : ℕ) :
    (W ^ x) ^ k ≤ N ^ ((k : ℝ) * x) := by
  have hN : 0 ≤ N := hW.trans hWN
  rw [mul_comm, Real.rpow_mul hN, Real.rpow_natCast]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hW _) (Real.rpow_le_rpow hW hWN hx) k

/-- `W^{-D} ≤ N^{-D/2}` for `N^{1/2} ≤ W`, `D ≥ 0`. -/
theorem rpow_neg_le_of_sqrt_le {W N D : ℝ} (hN0 : 0 < N) (hW : N ^ ((1 : ℝ) / 2) ≤ W)
    (hD : 0 ≤ D) : W ^ (-D) ≤ N ^ (-(D / 2)) := by
  have h1 : 0 < N ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hN0 _
  have h := Real.rpow_le_rpow_of_nonpos h1 hW (by linarith : -D ≤ 0)
  rw [← Real.rpow_mul hN0.le] at h
  convert h using 2; ring

theorem natpow_eq_rpow (N : ℝ) (k : ℕ) : N ^ k = N ^ (k : ℝ) := (Real.rpow_natCast N k).symm

end Asymp

section Transfer

variable (d : Dims)

/-- **Flow → grid transfer of a `StochDom` premise** on a sub-window `[s, v] ⊆ [s, t]`:
`map_H_eq` at every grid point (`highProb_grid_of_flow`) plus the union bound over the
polynomially many grid points. -/
theorem stochDom_grid_of_flow514 {s t v : ℕ → ℝ} (K : ℕ → ℕ) (hs0 : ∀ N, 0 ≤ s N)
    (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N) (hK0 : ∀ N, K N ≠ 0) {C : ℝ} (hC0 : 0 ≤ C)
    (hKcard : ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C)
    (F : ∀ N : ℕ, ℝ → Matrix (d.Idx N) (d.Idx N) ℂ → ℝ) (hF : ∀ N u, Measurable (F N u))
    (ζ : ℕ → ℝ)
    (h : StochDom (P d) (fun N (u : TimeIcc s t N) ω => F N u (Hflow d N u ω)) (fun N _ _ => ζ N)) :
    StochDom (Pg d) (fun N (k : Fin (K N + 1)) ω => F N (time s v K N k) (H d s v K N k ω))
      (fun N _ _ => ζ N) := by
  intro τ hτ D hD
  have hHP := h.highProb hτ
  have hflow : HighProb (P d) (fun N => {ω | ∀ u : TimeIcc s v N,
      Hflow d N (u : ℝ) ω ∈ {M | F N (u : ℝ) M ≤ (N : ℝ) ^ τ * ζ N}}) := by
    refine hHP.mono (Filter.Eventually.of_forall fun N ω hω u => ?_)
    exact hω ⟨u, u.2.1, u.2.2.trans (hvt N)⟩
  have hgrid := highProb_grid_of_flow d s v K hs0 hsv hK0 hC0 hKcard
    (fun N u => {M | F N u M ≤ (N : ℝ) ^ τ * ζ N})
    (fun N u => measurableSet_le (hF N u) measurable_const) hflow
  filter_upwards [hgrid D hD] with N hN
  refine (measure_mono ?_).trans hN
  intro ω hω hall
  obtain ⟨k, hk⟩ := hω
  exact absurd (hall k) (not_le.mpr hk)

/-- **Single grid time ↔ flow**: `Pg{H_k ∈ S} = P{H_{u_k} ∈ S}` (`map_H_eq`). -/
theorem prob_grid_eq_flow {s v : ℕ → ℝ} (K : ℕ → ℕ) (N k : ℕ) (hs0 : 0 ≤ s N) (hsv : s N ≤ v N)
    (hK0 : K N ≠ 0) {S : Set (Matrix (d.Idx N) (d.Idx N) ℂ)} (hS : MeasurableSet S) :
    (Pg d) (H d s v K N k ⁻¹' S) = (P d) (Hflow d N (time s v K N k) ⁻¹' S) := by
  have hHmeas : Measurable (H d s v K N k) :=
    (H_measurable_filt d s v K N k).mono ((filt d).le k) le_rfl
  have hHflowmeas : Measurable (Hflow d N (time s v K N k)) :=
    RBM.measurable_H (sample d) N _
  rw [← Measure.map_apply hHmeas hS, ← Measure.map_apply hHflowmeas hS,
    map_H_eq s v K N k hs0 hsv hK0]

end Transfer

section Window

variable (d : Dims)

end Window

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Moments

variable (d : Dims)

/-- `E‖X‖^{2·2^m} ≤ #Idx · traceConst(2^m)`. -/
theorem integral_norm_Xmat_pow_le514 (N m : ℕ) :
    ∫ ω, ‖Xmat d N ω‖ ^ (2 * 2 ^ m) ∂(P d)
      ≤ (Fintype.card (d.Idx N) : ℝ) * traceConst (2 ^ m) := by
  have h1 := integral_norm_Xmat_pow_le (d := d) N m
  have hfrob : ∀ ω : Ω d, frobSq (Xmat d N ω ^ 2 ^ m) = ∑ i, colSq (Xmat d N ω) (2 ^ m) i := by
    intro ω; unfold frobSq colSq; exact Finset.sum_comm
  simp only [hfrob] at h1
  rw [integral_finsetSum _ fun i _ => integrable_colSq d N (2 ^ m) i] at h1
  have h2 : ∑ i : d.Idx N, ∫ ω, colSq (Xmat d N ω) (2 ^ m) i ∂(P d)
      ≤ ∑ _i : d.Idx N, traceConst (2 ^ m) :=
    Finset.sum_le_sum fun i _ => integral_colSq_le d N (2 ^ m) i
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  linarith

theorem card_idx_eq (N : ℕ) : (Fintype.card (d.Idx N) : ℝ) = (d.L N : ℝ) * (d.W N : ℝ) := by
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]; push_cast; ring

/-- **The `Y` scale is polynomial**: `PY514 ≤ 857·1024^n n^4 N^{8n+6}` under
`#Idx ≤ N`, `(1-T)^{-1} ≤ N`, `η^{-1} ≤ N`. -/
theorem PY514_le (N n : ℕ) {T η : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hT : T < 1) (hT' : (1 - T)⁻¹ ≤ N)
    (hη : 0 < η) (hη' : η⁻¹ ≤ N) :
    PY514 d N n T η ≤ 857 * 1024 ^ n * (n : ℝ) ^ 4 * (N : ℝ) ^ (8 * n + 6) := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hT0 : 0 ≤ (1 - T)⁻¹ := inv_nonneg.mpr (by linarith)
  have hη0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hc0 : (0 : ℝ) ≤ Fintype.card (d.Idx N) := Nat.cast_nonneg _
  -- yConst
  have hy0 : 0 ≤ yConst d N n T η := by unfold yConst C2g; positivity
  have hy : yConst d N n T η ≤ 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (4 * n + 1) := by
    unfold yConst C2g
    have h1 : (1 + (1 - T)⁻¹) ^ n ≤ (2 * (N : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    have h2 : (2 * (1 + η⁻¹) ^ 3) ^ n ≤ (16 * (N : ℝ) ^ 3) ^ n := by
      refine pow_le_pow_left₀ (by positivity) ?_ n
      have : (1 + η⁻¹) ^ 3 ≤ (2 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      nlinarith
    have h3 : (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) / 2
        ≤ (N : ℝ) * ((n : ℝ) ^ 2 * (16 * (N : ℝ) ^ 3) ^ n) := by
      have : (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n)
          ≤ (N : ℝ) * ((n : ℝ) ^ 2 * (16 * (N : ℝ) ^ 3) ^ n) :=
        mul_le_mul hcard (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity) hN0
      have h0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) := by
        positivity
      linarith
    calc (1 + (1 - T)⁻¹) ^ n * ((Fintype.card (d.Idx N) : ℝ)
          * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) / 2)
        ≤ (2 * (N : ℝ)) ^ n * ((N : ℝ) * ((n : ℝ) ^ 2 * (16 * (N : ℝ) ^ 3) ^ n)) :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
      _ = 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (4 * n + 1) := by
          rw [mul_pow, mul_pow, ← pow_mul, show (32 : ℝ) = 2 * 16 by norm_num, mul_pow]
          ring
  have hy2 : yConst d N n T η ^ 2 ≤ 1024 ^ n * (n : ℝ) ^ 4 * (N : ℝ) ^ (8 * n + 2) := by
    calc yConst d N n T η ^ 2 ≤ (32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (4 * n + 1)) ^ 2 :=
          pow_le_pow_left₀ hy0 hy 2
      _ = 1024 ^ n * (n : ℝ) ^ 4 * (N : ℝ) ^ (8 * n + 2) := by
          rw [show (1024 : ℝ) = 32 ^ 2 by norm_num, ← pow_mul, mul_pow, mul_pow, ← pow_mul,
            ← pow_mul, ← pow_mul]
          ring_nf
  -- moments
  set m2 := ∫ y, ‖Xmat d N y‖ ^ 2 ∂(P d) with hm2
  have hm20 : 0 ≤ m2 := integral_nonneg fun _ => by positivity
  have hm2N : m2 ≤ N := (integral_normSq_Xmat_le514 d N).trans hcard
  have hX4 : ∫ ω, ‖Xmat d N ω‖ ^ 4 ∂(P d) ≤ 3 * N := by
    have h := integral_norm_Xmat_pow_le514 d N 1
    rw [show traceConst (2 ^ 1) = 3 by norm_num [traceConst], show 2 * 2 ^ 1 = 4 by norm_num] at h
    linarith
  have hX8 : ∫ ω, ‖Xmat d N ω‖ ^ 8 ∂(P d) ≤ 105 * N := by
    have h := integral_norm_Xmat_pow_le514 d N 2
    rw [show traceConst (2 ^ 2) = 105 by norm_num [traceConst], show 2 * 2 ^ 2 = 8 by norm_num] at h
    linarith
  have hi4 : Integrable (fun ω : Ω d => ‖Xmat d N ω‖ ^ 4) (P d) := by
    simpa using integrable_norm_Xmat_pow d N 2
  have hi8 : Integrable (fun ω : Ω d => ‖Xmat d N ω‖ ^ 8) (P d) := by
    simpa using integrable_norm_Xmat_pow d N 4
  have hI2 : ∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 2 ∂(P d) ≤ 8 * (N : ℝ) ^ 2 := by
    have hle : ∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 2 ∂(P d)
        ≤ ∫ x, (2 * ‖Xmat d N x‖ ^ 4 + 2 * m2 ^ 2) ∂(P d) := by
      refine integral_mono (integrable_sq_normSq_add d N m2)
        ((hi4.const_mul 2).add (integrable_const _)) fun x => ?_
      nlinarith [sq_nonneg (‖Xmat d N x‖ ^ 2 - m2)]
    rw [integral_add (hi4.const_mul 2) (integrable_const _), integral_const_mul] at hle
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
    nlinarith
  have hI4 : ∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 4 ∂(P d) ≤ 848 * (N : ℝ) ^ 4 := by
    have hle : ∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 4 ∂(P d)
        ≤ ∫ x, (8 * ‖Xmat d N x‖ ^ 8 + 8 * m2 ^ 4) ∂(P d) := by
      refine integral_mono (integrable_pow4_normSq_add d N m2)
        ((hi8.const_mul 8).add (integrable_const _)) fun x => ?_
      have ha : 0 ≤ ‖Xmat d N x‖ ^ 2 := by positivity
      set a := ‖Xmat d N x‖ ^ 2
      have e : ‖Xmat d N x‖ ^ 8 = a ^ 4 := by rw [← pow_mul]
      rw [e]
      nlinarith [sq_nonneg (a - m2), sq_nonneg (a + m2), sq_nonneg (a ^ 2 - m2 ^ 2),
        mul_nonneg ha hm20, sq_nonneg (a * m2)]
    rw [integral_add (hi8.const_mul 8) (integrable_const _), integral_const_mul] at hle
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
    have : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have : m2 ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hm20 hm2N 4
    nlinarith
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN4 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
  have hsum : (∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 2 ∂(P d))
      + (∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 4 ∂(P d)) + 1 ≤ 857 * (N : ℝ) ^ 4 := by linarith
  have hs0 : 0 ≤ (∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 2 ∂(P d))
      + (∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 4 ∂(P d)) + 1 := by
    have h2 : 0 ≤ ∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 2 ∂(P d) := integral_nonneg fun x => by positivity
    have h4 : 0 ≤ ∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 4 ∂(P d) := integral_nonneg fun x => by positivity
    linarith
  unfold PY514
  rw [← hm2]
  calc yConst d N n T η ^ 2 * ((∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 2 ∂(P d))
        + (∫ x, (‖Xmat d N x‖ ^ 2 + m2) ^ 4 ∂(P d)) + 1)
      ≤ (1024 ^ n * (n : ℝ) ^ 4 * (N : ℝ) ^ (8 * n + 2)) * (857 * (N : ℝ) ^ 4) :=
        mul_le_mul hy2 hsum hs0 (by positivity)
    _ = 857 * 1024 ^ n * (n : ℝ) ^ 4 * (N : ℝ) ^ (8 * n + 6) := by ring

end Moments

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Absorb

variable (d : Dims)

/-- The dimension facts used by the absorption: `1 ≤ N`, `2 ≤ W ≤ N`, `L ≤ N`, `LW ≤ N`,
`#Idx ≤ N`, `N^{1/2} ≤ W` (all from `Dims`, eventually). -/
theorem ev_dims514 :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ N ∧ (2 : ℝ) ≤ d.W N ∧ (d.W N : ℝ) ≤ N ∧ (d.L N : ℝ) ≤ N ∧
      (d.L N : ℝ) * (d.W N : ℝ) ≤ N ∧ (Fintype.card (d.Idx N) : ℝ) ≤ N ∧
      (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N := by
  have h2 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    filter_upwards [ev_rpow_le (a := 0) (b := (1 : ℝ) / 2) (by norm_num) 2,
      eventually_ge_atTop 1] with N hN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    simpa [Real.rpow_zero] using hN
  filter_upwards [d.dim, d.bandwidth, eventually_ge_atTop 1, h2] with N hdim hbw hN1 h2N
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hW1 : 1 ≤ d.W N := d.W_pos N
  have hsq : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ d.W N :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [d.c_pos])) hbw
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hW0 : (1 : ℝ) ≤ d.W N := by exact_mod_cast hW1
  have hL0 : (3 : ℝ) ≤ d.L N := by exact_mod_cast hL3
  refine ⟨hN1', h2N.trans hsq, by nlinarith, by nlinarith, by linarith, ?_, hsq⟩
  rw [card_idx_eq]; linarith

theorem four_Wtau_pow_le {W N τ' : ℝ} (hW : 0 ≤ W) (hWN : W ≤ N) (hτ' : 0 ≤ τ') (k : ℕ) :
    (4 * W ^ τ') ^ k ≤ 4 ^ k * N ^ ((k : ℝ) * τ') := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (rpow_pow_le_of_le hW hWN hτ' k) (by positivity)

/-- (ha1) The initial-datum main term. -/
theorem ev_ha1 (n : ℕ) {ε₀ ε₁ τ' cK : ℝ} (hτ' : 0 ≤ τ') (hε : (n : ℝ) * τ' + ε₁ < ε₀)
    (hcK : 0 ≤ cK) :
    ∀ᶠ N : ℕ in atTop, cK * (4 * (d.W N : ℝ) ^ τ') ^ n * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ε₀ / 8 := by
  filter_upwards [ev_dims514 d, ev_rpow_le hε (8 * (cK * 4 ^ n))] with N hd hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 := four_Wtau_pow_le (Nat.cast_nonneg (d.W N)) hWN hτ' n
  have hε1 : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  calc cK * (4 * (d.W N : ℝ) ^ τ') ^ n * (N : ℝ) ^ ε₁
      ≤ cK * (4 ^ n * (N : ℝ) ^ ((n : ℝ) * τ')) * (N : ℝ) ^ ε₁ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hcK) hε1
    _ = (8 * (cK * 4 ^ n) * (N : ℝ) ^ ((n : ℝ) * τ' + ε₁)) / 8 := by
        rw [Real.rpow_add hN0]; ring
    _ ≤ (N : ℝ) ^ ε₀ / 8 := by linarith

theorem Mc514_le {N n : ℕ} {ε₁ τ' CK : ℝ} (hN1 : (1 : ℝ) ≤ N) (hWN : (d.W N : ℝ) ≤ N)
    (hτ' : 0 ≤ τ') (hε₁ : 0 ≤ ε₁) (hCK : 0 ≤ CK) :
    Mc514 d N n ε₁ τ' CK ≤ (4 * Real.exp 1 * n + ((Finset.Icc 3 n).card : ℝ)
        * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK) + 4 * Real.exp 1 * (n : ℝ) ^ 2)
      * (N : ℝ) ^ (τ' + 2 * ε₁) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hWτ : (d.W N : ℝ) ^ τ' ≤ (N : ℝ) ^ τ' := Real.rpow_le_rpow (Nat.cast_nonneg _) hWN hτ'
  have hWτ0 : 0 ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hN1e : 1 ≤ (N : ℝ) ^ ε₁ := Real.one_le_rpow hN1 hε₁
  have he : (N : ℝ) ^ (τ' + 2 * ε₁) = (N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁ := by
    rw [Real.rpow_add hN0, show 2 * ε₁ = ε₁ + ε₁ by ring, Real.rpow_add hN0]; ring
  have hA : (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (τ' + 2 * ε₁) := by
    rw [he]; gcongr
  have hB : (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (τ' + 2 * ε₁) := by
    rw [he]
    calc (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ = (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * 1 := by ring
      _ ≤ (N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁ := by gcongr
  unfold Mc514
  have hc3 : (0 : ℝ) ≤ ((Finset.Icc 3 n).card : ℝ) := Nat.cast_nonneg _
  have hk1 : 0 ≤ 4 * Real.exp 1 * (n : ℝ) := by positivity
  have hk2 : 0 ≤ ((Finset.Icc 3 n).card : ℝ) * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK) := by positivity
  have hk3 : 0 ≤ 4 * Real.exp 1 * (n : ℝ) ^ 2 := by positivity
  have e1 : 4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁
      = 4 * Real.exp 1 * (n : ℝ) * ((d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ * (N : ℝ) ^ ε₁) := by ring
  have e2 : ((Finset.Icc 3 n).card : ℝ) * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ'
        * (N : ℝ) ^ ε₁)
      = ((Finset.Icc 3 n).card : ℝ) * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK)
        * ((d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁) := by ring
  have e3 : 4 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁
      = 4 * Real.exp 1 * (n : ℝ) ^ 2 * ((d.W N : ℝ) ^ τ' * (N : ℝ) ^ ε₁) := by ring
  rw [e1, e2, e3]
  have := mul_le_mul_of_nonneg_left hA hk1
  have := mul_le_mul_of_nonneg_left hB hk2
  have := mul_le_mul_of_nonneg_left hB hk3
  nlinarith

/-- (ha2) The drift main term, with the `log N` of `Σ Δ/η`. -/
theorem ev_ha2 (n : ℕ) {ε₀ ε₁ τ' cK CK mi : ℝ} (hτ' : 0 ≤ τ') (hε₁ : 0 ≤ ε₁)
    (hε : ((n : ℝ) + 1) * τ' + 2 * ε₁ < ε₀) (hcK : 0 ≤ cK) (hCK : 0 ≤ CK) (hmi : 0 < mi) :
    ∀ᶠ N : ℕ in atTop, cK * (4 * (d.W N : ℝ) ^ τ') ^ n * Mc514 d N n ε₁ τ' CK
      * (mi⁻¹ * Real.log N) ≤ (N : ℝ) ^ ε₀ / 8 := by
  set M0 := 4 * Real.exp 1 * n + ((Finset.Icc 3 n).card : ℝ) * (8 * Real.exp 1 * (n : ℝ) ^ 2 * CK)
      + 4 * Real.exp 1 * (n : ℝ) ^ 2 with hM0
  have hM00 : 0 ≤ M0 := by rw [hM0]; positivity
  filter_upwards [ev_dims514 d, ev_rpow_log_le (a := ((n : ℝ) + 1) * τ' + 2 * ε₁) hε
    (8 * (cK * 4 ^ n * M0 * mi⁻¹))] with N hd hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h1 := four_Wtau_pow_le (Nat.cast_nonneg (d.W N)) hWN hτ' n
  have h2 := Mc514_le d (n := n) (CK := CK) hN1 hWN hτ' hε₁ hCK
  have hMc0 : 0 ≤ Mc514 d N n ε₁ τ' CK := by
    unfold Mc514
    have := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) τ'
    have := Real.rpow_nonneg hN0.le ε₁
    positivity
  have hmil : 0 ≤ mi⁻¹ * Real.log N := by positivity
  calc cK * (4 * (d.W N : ℝ) ^ τ') ^ n * Mc514 d N n ε₁ τ' CK * (mi⁻¹ * Real.log N)
      ≤ cK * (4 ^ n * (N : ℝ) ^ ((n : ℝ) * τ')) * (M0 * (N : ℝ) ^ (τ' + 2 * ε₁))
          * (mi⁻¹ * Real.log N) := by
        gcongr
    _ = (cK * 4 ^ n * M0 * mi⁻¹) * (N : ℝ) ^ (((n : ℝ) + 1) * τ' + 2 * ε₁) * Real.log N := by
        rw [show ((n : ℝ) + 1) * τ' + 2 * ε₁ = (n : ℝ) * τ' + (τ' + 2 * ε₁) by ring,
          Real.rpow_add hN0 ((n : ℝ) * τ') (τ' + 2 * ε₁)]; ring
    _ ≤ (8 * (cK * 4 ^ n * M0 * mi⁻¹) * (N : ℝ) ^ (((n : ℝ) + 1) * τ' + 2 * ε₁)
          * (Real.log N + 1)) / 8 := by
        have h0 : 0 ≤ cK * 4 ^ n * M0 * mi⁻¹ * (N : ℝ) ^ (((n : ℝ) + 1) * τ' + 2 * ε₁) := by
          have := Real.rpow_nonneg hN0.le (((n : ℝ) + 1) * τ' + 2 * ε₁)
          positivity
        nlinarith
    _ ≤ (N : ℝ) ^ ε₀ / 8 := by linarith

/-- (ha3) The QV main term. -/
theorem ev_ha3 (n : ℕ) {ε₀ ε₁ τ' cK2 mi : ℝ} (hτ' : 0 ≤ τ')
    (hε : (2 * (n : ℝ) + 1) * τ' + ε₁ < 2 * ε₀ - 2 * ε₁) (hcK2 : 0 ≤ cK2) (hmi : 0 < mi) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ε₁ * Real.sqrt (cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
      * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
      * (mi⁻¹ * Real.log N + 1)) ≤ (N : ℝ) ^ ε₀ / 8 := by
  set C := cK2 * (12 * Real.exp 1 * (n : ℝ) ^ 2) * (mi⁻¹ + 1) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  filter_upwards [ev_dims514 d, ev_rpow_log_le (a := (2 * (n : ℝ) + 1) * τ' + ε₁) hε
    (64 * C)] with N hd hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  have h1 := rpow_pow_le_of_le hW0 hWN hτ' (n + n)
  have h2 : (d.W N : ℝ) ^ τ' ≤ (N : ℝ) ^ τ' := Real.rpow_le_rpow hW0 hWN hτ'
  have hl : mi⁻¹ * Real.log N + 1 ≤ (mi⁻¹ + 1) * (Real.log N + 1) := by
    have : 0 ≤ mi⁻¹ := by positivity
    nlinarith
  have hZ : cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
      * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
      * (mi⁻¹ * Real.log N + 1)
      ≤ C * (N : ℝ) ^ ((2 * (n : ℝ) + 1) * τ' + ε₁) * (Real.log N + 1) := by
    have hNe : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
    have hWt : 0 ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg hW0 _
    have e : (N : ℝ) ^ ((2 * (n : ℝ) + 1) * τ' + ε₁)
        = (N : ℝ) ^ (((n + n : ℕ) : ℝ) * τ') * (N : ℝ) ^ τ' * (N : ℝ) ^ ε₁ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; push_cast; ring_nf
    rw [e, hC]
    calc cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
          * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
          * (mi⁻¹ * Real.log N + 1)
        ≤ cK2 * (N : ℝ) ^ (((n + n : ℕ) : ℝ) * τ')
          * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
          * ((mi⁻¹ + 1) * (Real.log N + 1)) := by gcongr
      _ = _ := by ring
  have hsq : Real.sqrt (cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
      * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
      * (mi⁻¹ * Real.log N + 1)) ≤ (N : ℝ) ^ (ε₀ - ε₁) / 8 := by
    rw [Real.sqrt_le_left (by positivity)]
    have e : ((N : ℝ) ^ (ε₀ - ε₁) / 8) ^ 2 = (N : ℝ) ^ (2 * ε₀ - 2 * ε₁) / 64 := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
    rw [e]
    have : C * (N : ℝ) ^ ((2 * (n : ℝ) + 1) * τ' + ε₁) * (Real.log N + 1)
        ≤ (N : ℝ) ^ (2 * ε₀ - 2 * ε₁) / 64 := by nlinarith
    linarith
  calc (N : ℝ) ^ ε₁ * Real.sqrt (cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
        * (6 * Real.exp 1 * (n : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
        * (mi⁻¹ * Real.log N + 1))
      ≤ (N : ℝ) ^ ε₁ * ((N : ℝ) ^ (ε₀ - ε₁) / 8) :=
        mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ ε₀ / 8 := by
        rw [mul_div_assoc', ← Real.rpow_add hN0]; ring_nf

end Absorb

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Absorb2

variable (d : Dims)

theorem inv_pow_eq_rpow {N : ℝ} (hN : 0 < N) (k : ℕ) : N⁻¹ ^ k = N ^ (-(k : ℝ)) := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN.le]

theorem natpow_mul_rpow {N : ℝ} (hN : 0 < N) (k : ℕ) (a : ℝ) :
    N ^ k * N ^ a = N ^ ((k : ℝ) + a) := by
  rw [Real.rpow_add hN, Real.rpow_natCast]

/-- (he1) the `W^{-D'}` tail of the initial datum. -/
theorem ev_he1 (n : ℕ) {ε₀ D' : ℝ} (hε₀ : 0 ≤ ε₀) (hD' : 4 * (n : ℝ) < D') :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ n * (d.W N : ℝ) ^ (-D') ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ)⁻¹ ^ n := by
  filter_upwards [ev_dims514 d, ev_rpow_le (a := (n : ℝ) - D' / 2) (b := -(n : ℝ))
    (by linarith) 16] with N hd hA
  obtain ⟨hN1, -, -, -, -, -, hsq⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hW := rpow_neg_le_of_sqrt_le hN0 hsq (by linarith : 0 ≤ D')
  have hε : 1 ≤ (N : ℝ) ^ ε₀ := Real.one_le_rpow hN1 hε₀
  rw [inv_pow_eq_rpow hN0]
  have hn0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ)) := Real.rpow_nonneg hN0.le _
  calc (N : ℝ) ^ n * (d.W N : ℝ) ^ (-D') ≤ (N : ℝ) ^ n * (N : ℝ) ^ (-(D' / 2)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = (N : ℝ) ^ ((n : ℝ) - D' / 2) := by rw [natpow_mul_rpow hN0]; ring_nf
    _ ≤ (N : ℝ) ^ (-(n : ℝ)) / 16 := by linarith
    _ ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ) ^ (-(n : ℝ)) := by nlinarith

/-- (he4) the `Y` threshold. -/
theorem ev_he4 (n : ℕ) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-((n : ℝ) + 1)) ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ)⁻¹ ^ n := by
  filter_upwards [eventually_ge_atTop 1, ev_rpow_le (a := -((n : ℝ) + 1)) (b := -(n : ℝ))
    (by linarith) 16] with N hN1 hA
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hε : 1 ≤ (N : ℝ) ^ ε₀ := Real.one_le_rpow hN1' hε₀
  rw [inv_pow_eq_rpow hN0]
  have hn0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ)) := Real.rpow_nonneg hN0.le _
  nlinarith

/-- (he5) the `Δ^{1/2}` remainder. -/
theorem ev_he5 (n : ℕ) {ε₀ C_K : ℝ} (hε₀ : 0 ≤ ε₀) (hCK : 8 * (n : ℝ) + 32 < C_K) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ (N : ℝ) ^ (-C_K) →
      (1 + (N : ℝ)) ^ n * (100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * (2 * (N : ℝ)) ^ (2 * n + 16))
        * Δ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ)⁻¹ ^ n := by
  set C := 100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * 2 ^ (3 * n + 16) with hC
  filter_upwards [eventually_ge_atTop 1, ev_rpow_le (a := ((3 * n + 16 : ℕ) : ℝ) - C_K / 2)
    (b := -(n : ℝ)) (by push_cast; linarith) (16 * C)] with N hN1 hA Δ hΔ0 hΔ
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hε : 1 ≤ (N : ℝ) ^ ε₀ := Real.one_le_rpow hN1' hε₀
  have hsq : Δ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(C_K / 2)) := by
    have := Real.rpow_le_rpow hΔ0 hΔ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul hN0.le] at this
    convert this using 2; ring
  have h1N : (1 + (N : ℝ)) ^ n ≤ (2 * (N : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
  rw [inv_pow_eq_rpow hN0]
  have hn0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ)) := Real.rpow_nonneg hN0.le _
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  calc (1 + (N : ℝ)) ^ n * (100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * (2 * (N : ℝ)) ^ (2 * n + 16))
        * Δ ^ ((1 : ℝ) / 2)
      ≤ (2 * (N : ℝ)) ^ n * (100 * ((n : ℝ) + 1) ^ 6 * 4 ^ n * (2 * (N : ℝ)) ^ (2 * n + 16))
        * (N : ℝ) ^ (-(C_K / 2)) := by
        gcongr
    _ = C * ((N : ℝ) ^ (3 * n + 16) * (N : ℝ) ^ (-(C_K / 2))) := by
        rw [hC, mul_pow, mul_pow]; ring
    _ = C * (N : ℝ) ^ (((3 * n + 16 : ℕ) : ℝ) - C_K / 2) := by
        rw [natpow_mul_rpow hN0]; ring_nf
    _ ≤ (N : ℝ) ^ (-(n : ℝ)) / 16 := by linarith
    _ ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ) ^ (-(n : ℝ)) := by nlinarith

/-- (he3) the `W^{-(D'-1)}` tail of the QV sum. -/
theorem ev_he3 (n : ℕ) {ε₀ ε₁ τ' D' cK2 : ℝ} (hε₀ : 0 ≤ ε₀) (hε₁ : ε₁ ≤ 1 / 2)
    (hτ' : 0 ≤ τ') (hnτ : ((n + n : ℕ) : ℝ) * τ' ≤ 1) (hD' : 8 * (n : ℝ) + 7 < D')
    (hcK2 : 0 ≤ cK2) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ε₁ * Real.sqrt ((cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
        * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n)) * eeHermErr d N n (D' - 1))
      ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ)⁻¹ ^ n := by
  set C := (cK2 + 1) * (n : ℝ) ^ 2 with hC
  filter_upwards [ev_dims514 d, ev_rpow_le (a := ((2 * n + 2 : ℕ) : ℝ) - (D' - 1) / 2)
    (b := -(2 * (n : ℝ) + 1)) (by push_cast; linarith) (256 * C)] with N hd hA
  obtain ⟨hN1, -, hWN, -, hLW, -, hsq⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hε : 1 ≤ (N : ℝ) ^ ε₀ := Real.one_le_rpow hN1 hε₀
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  have hWD := rpow_neg_le_of_sqrt_le hN0 hsq (by linarith : 0 ≤ D' - 1)
  have hWt : ((d.W N : ℝ) ^ τ') ^ (n + n) ≤ N := by
    refine (rpow_pow_le_of_le hW0 hWN hτ' (n + n)).trans ?_
    calc (N : ℝ) ^ (((n + n : ℕ) : ℝ) * τ') ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 hnτ
      _ = N := Real.rpow_one _
  have hee : eeHermErr d N n (D' - 1) ≤ (n : ℝ) ^ 2 * N * (N : ℝ) ^ (-((D' - 1) / 2)) := by
    unfold eeHermErr
    have : (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) = (n : ℝ) ^ 2 * ((d.L N : ℝ) * (d.W N : ℝ)) := by
      ring
    rw [this]
    gcongr
  have hee0 : 0 ≤ eeHermErr d N n (D' - 1) := eeHermErr_nonneg d N n (D' - 1)
  have hQ : (cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n))
      * eeHermErr d N n (D' - 1)
      ≤ C * (N : ℝ) ^ (((2 * n + 2 : ℕ) : ℝ) - (D' - 1) / 2) := by
    have h1 : cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n)
        ≤ (cK2 + 1) * (N : ℝ) ^ (n + n + 1) := by
      have hN' : (N : ℝ) ^ (n + n) ≤ (N : ℝ) ^ (n + n + 1) := pow_le_pow_right₀ hN1 (by omega)
      have : cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n) * (N : ℝ) ^ (n + n)
          ≤ cK2 * N * (N : ℝ) ^ (n + n) := by gcongr
      rw [pow_succ] at hN' ⊢
      nlinarith [pow_nonneg hN0.le (n + n)]
    calc (cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n))
          * eeHermErr d N n (D' - 1)
        ≤ ((cK2 + 1) * (N : ℝ) ^ (n + n + 1)) * ((n : ℝ) ^ 2 * N * (N : ℝ) ^ (-((D' - 1) / 2))) :=
          mul_le_mul h1 hee hee0 (by positivity)
      _ = C * ((N : ℝ) ^ (2 * n + 2) * (N : ℝ) ^ (-((D' - 1) / 2))) := by
          rw [hC, show 2 * n + 2 = (n + n + 1) + 1 by ring, pow_succ]; ring
      _ = C * (N : ℝ) ^ (((2 * n + 2 : ℕ) : ℝ) - (D' - 1) / 2) := by
          rw [natpow_mul_rpow hN0]; ring_nf
  have hQ' : (cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n) * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n))
      * eeHermErr d N n (D' - 1) ≤ ((N : ℝ) ^ (-((n : ℝ) + 1 / 2)) / 16) ^ 2 := by
    have e : ((N : ℝ) ^ (-((n : ℝ) + 1 / 2)) / 16) ^ 2 = (N : ℝ) ^ (-(2 * (n : ℝ) + 1)) / 256 := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
    rw [e]; linarith
  have hs := Real.sqrt_le_sqrt hQ'
  rw [Real.sqrt_sq (by positivity)] at hs
  have hN12 : (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 hε₁
  rw [inv_pow_eq_rpow hN0]
  have hn0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ)) := Real.rpow_nonneg hN0.le _
  calc (N : ℝ) ^ ε₁ * Real.sqrt ((cK2 * ((d.W N : ℝ) ^ τ') ^ (n + n)
        * (N : ℝ) ^ (n + n) + (N : ℝ) ^ (n + n)) * eeHermErr d N n (D' - 1))
      ≤ (N : ℝ) ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ (-((n : ℝ) + 1 / 2)) / 16) :=
        mul_le_mul hN12 hs (Real.sqrt_nonneg _) (by positivity)
    _ = (N : ℝ) ^ (-(n : ℝ)) / 16 := by
        rw [mul_div_assoc', ← Real.rpow_add hN0]; ring_nf
    _ ≤ (N : ℝ) ^ ε₀ / 16 * (N : ℝ) ^ (-(n : ℝ)) := by nlinarith

end Absorb2

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Absorb3

variable (d : Dims)

set_option maxHeartbeats 1600000 in
/-- (he2) the `W^{-D'}` tails of the drift. -/
theorem ev_he2 (m : ℕ) {ε₀ ε₁ τ' D' cK CK : ℝ} (hε₀ : 0 ≤ ε₀) (hε₁ : ε₁ ≤ 1)
    (hτ' : 0 ≤ τ') (hnτ : ((m + 2 : ℕ) : ℝ) * τ' ≤ 1) (hD' : 8 * ((m + 2 : ℕ) : ℝ) + 6 < D')
    (hcK : 0 ≤ cK) (hCK : 0 ≤ CK) :
    ∀ᶠ N : ℕ in atTop, ∀ Φ : ℝ, 0 ≤ Φ →
      cK * (4 * (d.W N : ℝ) ^ τ') ^ (m + 2) * (N : ℝ) ^ (m + 2)
          * Ec514 d N (m + 2) ε₁ D' Φ (((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) * (N : ℝ) ^ (m + 2))
        + (N : ℝ) ^ (m + 2) * driftErr514 d N m (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) D'
      ≤ (N : ℝ) ^ ε₀ / 16 * (1 + Φ) * (N : ℝ)⁻¹ ^ (m + 2) := by
  set n := m + 2 with hn
  set c3 : ℝ := ((Finset.Icc 3 n).card : ℝ) with hc3
  set E0 : ℝ := (n : ℝ) + 2 * c3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) ^ 2 with hE0
  set D0 : ℝ := 3 * (n : ℝ) + 8 * (m : ℝ) * (n : ℝ) ^ 2 + 6 * (n : ℝ) ^ 2 with hD0
  set C : ℝ := cK * 4 ^ n * E0 + D0 with hC
  filter_upwards [ev_dims514 d, eventually_ge_atTop ⌈CK + 1⌉₊,
    ev_rpow_le (a := ((3 * n + 3 : ℕ) : ℝ) - D' / 2) (b := -(n : ℝ)) (by push_cast; linarith)
      (16 * C)] with N hd hCKN hA Φ hΦ
  obtain ⟨hN1, -, hWN, -, hLW, -, hsq⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hCKN' : CK + 1 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hCKN)
  have hε : 1 ≤ (N : ℝ) ^ ε₀ := Real.one_le_rpow hN1 hε₀
  have hn1 : 1 ≤ n := by omega
  have hNn : (N : ℝ) ≤ (N : ℝ) ^ n := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (N : ℝ) ^ n := pow_le_pow_right₀ hN1 hn1
  set X := (d.W N : ℝ) ^ (-D') with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hXY := rpow_neg_le_of_sqrt_le hN0 hsq (by linarith : 0 ≤ D')
  have hNe1 : (N : ℝ) ^ ε₁ ≤ N := by
    calc (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hε₁
      _ = N := Real.rpow_one _
  have hNe0 : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  set Mb := (N : ℝ) + (N : ℝ) ^ n + CK + 1 with hMbdef
  have hMb : Mb ≤ 3 * (N : ℝ) ^ n := by rw [hMbdef]; linarith
  have hMb0 : 0 ≤ Mb := by rw [hMbdef]; positivity
  have hWL0 : 0 ≤ (d.W N : ℝ) * (d.L N : ℝ) := by positivity
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by linarith
  have hc30 : 0 ≤ c3 := Nat.cast_nonneg _
  have hNsq : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * n + 2) := pow_le_pow_right₀ hN1 (by omega)
  have hN2n : (N : ℝ) ^ (2 * n + 1) ≤ (N : ℝ) ^ (2 * n + 2) := pow_le_pow_right₀ hN1 (by omega)
  -- Ec514
  have hEc : Ec514 d N n ε₁ D' Φ (Mb * (N : ℝ) ^ n) ≤ E0 * (N : ℝ) ^ (2 * n + 2) * X * (1 + Φ) := by
    unfold Ec514
    rw [← hX, ← hc3]
    have t1 : (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * X * (N : ℝ) ^ ε₁ ≤ (n : ℝ) * (N : ℝ) ^ 2 * X := by
      have : (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) * N := mul_le_mul hWL hNe1 hNe0 hN0.le
      calc (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * X * (N : ℝ) ^ ε₁
          = (n : ℝ) * X * ((d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁) := by ring
        _ ≤ (n : ℝ) * X * ((N : ℝ) * N) := by gcongr
        _ = (n : ℝ) * (N : ℝ) ^ 2 * X := by ring
    have t2 : c3 * (2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * X * ((N : ℝ) ^ ε₁ * Φ))
        ≤ 2 * c3 * (n : ℝ) ^ 2 * (N : ℝ) ^ 2 * X * Φ := by
      have : (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) * N := mul_le_mul hWL hNe1 hNe0 hN0.le
      calc c3 * (2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * X * ((N : ℝ) ^ ε₁ * Φ))
          = 2 * c3 * (n : ℝ) ^ 2 * X * Φ * ((d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁) := by ring
        _ ≤ 2 * c3 * (n : ℝ) ^ 2 * X * Φ * ((N : ℝ) * N) := by gcongr
        _ = 2 * c3 * (n : ℝ) ^ 2 * (N : ℝ) ^ 2 * X * Φ := by ring
    have t3 : (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * X * (Mb * (N : ℝ) ^ n)
        ≤ 3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 1) * X := by
      have : (d.W N : ℝ) * (d.L N : ℝ) * (Mb * (N : ℝ) ^ n) ≤ (N : ℝ) * (3 * (N : ℝ) ^ n * (N : ℝ) ^ n) :=
        mul_le_mul hWL (mul_le_mul_of_nonneg_right hMb (by positivity)) (by positivity) hN0.le
      calc (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * X * (Mb * (N : ℝ) ^ n)
          = (n : ℝ) ^ 2 * X * ((d.W N : ℝ) * (d.L N : ℝ) * (Mb * (N : ℝ) ^ n)) := by ring
        _ ≤ (n : ℝ) ^ 2 * X * ((N : ℝ) * (3 * (N : ℝ) ^ n * (N : ℝ) ^ n)) := by gcongr
        _ = 3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 1) * X := by ring
    have hnX : 0 ≤ (n : ℝ) ^ 2 * X := by positivity
    have u1 := mul_le_mul_of_nonneg_left hNsq (mul_nonneg (Nat.cast_nonneg n) hX0)
    have u2 := mul_le_mul_of_nonneg_left hNsq (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0 : ℝ) ≤ 2) hc30) (sq_nonneg (n : ℝ))) (mul_nonneg hX0 hΦ))
    have u3 := mul_le_mul_of_nonneg_left hN2n (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hnX)
    have ex : 0 ≤ ((n : ℝ) + 3 * (n : ℝ) ^ 2) * (N : ℝ) ^ (2 * n + 2) * X * Φ
        + 2 * c3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 2) * X := by positivity
    have eE : E0 * (N : ℝ) ^ (2 * n + 2) * X * (1 + Φ)
        = (n : ℝ) * X * (N : ℝ) ^ (2 * n + 2)
          + 2 * c3 * (n : ℝ) ^ 2 * (X * Φ) * (N : ℝ) ^ (2 * n + 2)
          + 3 * ((n : ℝ) ^ 2 * X) * (N : ℝ) ^ (2 * n + 2)
          + (((n : ℝ) + 3 * (n : ℝ) ^ 2) * (N : ℝ) ^ (2 * n + 2) * X * Φ
            + 2 * c3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 2) * X) := by
      rw [hE0]; ring
    rw [eE]
    have f1 : (n : ℝ) * (N : ℝ) ^ 2 * X = (n : ℝ) * X * (N : ℝ) ^ 2 := by ring
    have f2 : 2 * c3 * (n : ℝ) ^ 2 * (N : ℝ) ^ 2 * X * Φ = 2 * c3 * (n : ℝ) ^ 2 * (X * Φ) * (N : ℝ) ^ 2 := by
      ring
    have f3 : 3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 1) * X = 3 * ((n : ℝ) ^ 2 * X) * (N : ℝ) ^ (2 * n + 1) := by
      ring
    rw [f1] at t1; rw [f2] at t2; rw [f3] at t3
    linarith
  -- driftErr514
  have hdE : driftErr514 d N m (CK + 1) Mb D' ≤ D0 * (N : ℝ) ^ (n + 1) * X := by
    unfold driftErr514
    rw [← hX]
    have hMK : CK + 1 ≤ (N : ℝ) ^ n := hCKN'.trans hNn
    have hm2 : ((m : ℝ) + 2) = (n : ℝ) := by rw [hn]; push_cast; ring
    rw [hm2]
    have t1 : (d.W N : ℝ) * (n : ℝ) * (d.L N : ℝ) * (Mb * X) ≤ 3 * (n : ℝ) * (N : ℝ) ^ (n + 1) * X := by
      calc (d.W N : ℝ) * (n : ℝ) * (d.L N : ℝ) * (Mb * X)
          = (n : ℝ) * X * ((d.W N : ℝ) * (d.L N : ℝ) * Mb) := by ring
        _ ≤ (n : ℝ) * X * ((N : ℝ) * (3 * (N : ℝ) ^ n)) := by gcongr
        _ = 3 * (n : ℝ) * (N : ℝ) ^ (n + 1) * X := by ring
    have t2 : (m : ℝ) * (2 * (d.W N : ℝ) * (n : ℝ) ^ 2 * (d.L N : ℝ) * X * (CK + 1 + Mb))
        ≤ 8 * (m : ℝ) * (n : ℝ) ^ 2 * (N : ℝ) ^ (n + 1) * X := by
      have hs : CK + 1 + Mb ≤ 4 * (N : ℝ) ^ n := by linarith
      calc (m : ℝ) * (2 * (d.W N : ℝ) * (n : ℝ) ^ 2 * (d.L N : ℝ) * X * (CK + 1 + Mb))
          = 2 * (m : ℝ) * (n : ℝ) ^ 2 * X * ((d.W N : ℝ) * (d.L N : ℝ) * (CK + 1 + Mb)) := by ring
        _ ≤ 2 * (m : ℝ) * (n : ℝ) ^ 2 * X * ((N : ℝ) * (4 * (N : ℝ) ^ n)) := by
            gcongr
        _ = 8 * (m : ℝ) * (n : ℝ) ^ 2 * (N : ℝ) ^ (n + 1) * X := by ring
    have t3 : 2 * (d.W N : ℝ) * (n : ℝ) ^ 2 * (d.L N : ℝ) * X * Mb
        ≤ 6 * (n : ℝ) ^ 2 * (N : ℝ) ^ (n + 1) * X := by
      calc 2 * (d.W N : ℝ) * (n : ℝ) ^ 2 * (d.L N : ℝ) * X * Mb
          = 2 * (n : ℝ) ^ 2 * X * ((d.W N : ℝ) * (d.L N : ℝ) * Mb) := by ring
        _ ≤ 2 * (n : ℝ) ^ 2 * X * ((N : ℝ) * (3 * (N : ℝ) ^ n)) := by gcongr
        _ = 6 * (n : ℝ) ^ 2 * (N : ℝ) ^ (n + 1) * X := by ring
    have eD : D0 * (N : ℝ) ^ (n + 1) * X = 3 * (n : ℝ) * (N : ℝ) ^ (n + 1) * X
        + 8 * (m : ℝ) * (n : ℝ) ^ 2 * (N : ℝ) ^ (n + 1) * X + 6 * (n : ℝ) ^ 2 * (N : ℝ) ^ (n + 1) * X := by
      rw [hD0]; ring
    rw [eD]
    linarith
  -- combine
  have hWτ := four_Wtau_pow_le (Nat.cast_nonneg (d.W N)) hWN hτ' n
  have hNτ : (N : ℝ) ^ ((n : ℝ) * τ') ≤ N := by
    calc (N : ℝ) ^ ((n : ℝ) * τ') ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hnτ
      _ = N := Real.rpow_one _
  have hKτ : cK * (4 * (d.W N : ℝ) ^ τ') ^ n ≤ cK * 4 ^ n * N := by
    calc cK * (4 * (d.W N : ℝ) ^ τ') ^ n ≤ cK * (4 ^ n * (N : ℝ) ^ ((n : ℝ) * τ')) :=
          mul_le_mul_of_nonneg_left hWτ hcK
      _ ≤ cK * (4 ^ n * N) := by gcongr
      _ = cK * 4 ^ n * N := by ring
  have hEc0 : 0 ≤ Ec514 d N n ε₁ D' Φ (Mb * (N : ℝ) ^ n) := by unfold Ec514; positivity
  have hE00 : 0 ≤ E0 := by rw [hE0]; positivity
  have hD00 : 0 ≤ D0 := by rw [hD0]; positivity
  have hP : (N : ℝ) ^ (3 * n + 3) * X ≤ (N : ℝ) ^ (((3 * n + 3 : ℕ) : ℝ) - D' / 2) := by
    rw [show ((3 * n + 3 : ℕ) : ℝ) - D' / 2 = ((3 * n + 3 : ℕ) : ℝ) + (-(D' / 2)) by ring,
      ← natpow_mul_rpow hN0]
    exact mul_le_mul_of_nonneg_left hXY (by positivity)
  have term1 : cK * (4 * (d.W N : ℝ) ^ τ') ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mb * (N : ℝ) ^ n)
      ≤ cK * 4 ^ n * E0 * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ) := by
    calc cK * (4 * (d.W N : ℝ) ^ τ') ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mb * (N : ℝ) ^ n)
        ≤ (cK * 4 ^ n * N) * (N : ℝ) ^ n * (E0 * (N : ℝ) ^ (2 * n + 2) * X * (1 + Φ)) := by
          gcongr
      _ = cK * 4 ^ n * E0 * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ) := by ring
  have term2 : (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mb D'
      ≤ D0 * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ) := by
    have hpow : (N : ℝ) ^ (2 * n + 1) ≤ (N : ℝ) ^ (3 * n + 3) := pow_le_pow_right₀ hN1 (by omega)
    calc (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mb D' ≤ (N : ℝ) ^ n * (D0 * (N : ℝ) ^ (n + 1) * X) :=
          mul_le_mul_of_nonneg_left hdE (by positivity)
      _ = D0 * ((N : ℝ) ^ (2 * n + 1) * X) * 1 := by ring
      _ ≤ D0 * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ) := by gcongr; linarith
  rw [inv_pow_eq_rpow hN0]
  have hn0 : 0 ≤ (N : ℝ) ^ (-(n : ℝ)) := Real.rpow_nonneg hN0.le _
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hfin : C * ((N : ℝ) ^ (3 * n + 3) * X) ≤ (N : ℝ) ^ (-(n : ℝ)) / 16 := by
    have := mul_le_mul_of_nonneg_left hP hC0
    linarith
  have h1Φ : 0 ≤ 1 + Φ := by linarith
  calc cK * (4 * (d.W N : ℝ) ^ τ') ^ n * (N : ℝ) ^ n * Ec514 d N n ε₁ D' Φ (Mb * (N : ℝ) ^ n)
        + (N : ℝ) ^ n * driftErr514 d N m (CK + 1) Mb D'
      ≤ C * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ) := by
        have eC : C * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ)
            = cK * 4 ^ n * E0 * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ)
              + D0 * ((N : ℝ) ^ (3 * n + 3) * X) * (1 + Φ) := by rw [hC]; ring
        rw [eC]; linarith
    _ ≤ (N : ℝ) ^ (-(n : ℝ)) / 16 * (1 + Φ) := mul_le_mul_of_nonneg_right hfin h1Φ
    _ ≤ (N : ℝ) ^ ε₀ / 16 * (1 + Φ) * (N : ℝ) ^ (-(n : ℝ)) := by
        have h := mul_le_mul_of_nonneg_right hε (mul_nonneg h1Φ hn0)
        have e1 : (N : ℝ) ^ (-(n : ℝ)) / 16 * (1 + Φ) = (1 * ((1 + Φ) * (N : ℝ) ^ (-(n : ℝ)))) / 16 := by
          ring
        have e2 : (N : ℝ) ^ ε₀ / 16 * (1 + Φ) * (N : ℝ) ^ (-(n : ℝ))
            = ((N : ℝ) ^ ε₀ * ((1 + Φ) * (N : ℝ) ^ (-(n : ℝ)))) / 16 := by ring
        rw [e1, e2]; linarith

/-- (hshΞ) the QV time shift of `Ξ^{(L)}`. -/
theorem shXi_le {N : ℕ} {C_K x A Δ e : ℝ} (k : ℕ) (hN1 : (1 : ℝ) ≤ N) (hx0 : 0 ≤ x) (hx : x ≤ N)
    (hA0 : 0 ≤ A) (hA : A ≤ N) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ (N : ℝ) ^ (-C_K))
    (hev : ((k : ℕ) : ℝ) * (N : ℝ) ^ (((2 * k : ℕ) : ℝ) - C_K) ≤ 1) (h1 : 1 ≤ e) (hk : 1 ≤ k) :
    e + ((k : ℕ) : ℝ) * (x ^ (k + 1) * Δ) * A ^ (k - 1) ≤ 2 * e := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hx' : x ^ (k + 1) ≤ (N : ℝ) ^ (k + 1) := pow_le_pow_left₀ hx0 hx _
  have hA' : A ^ (k - 1) ≤ (N : ℝ) ^ (k - 1) := pow_le_pow_left₀ hA0 hA _
  have hpow : (N : ℝ) ^ (k + 1) * (N : ℝ) ^ (k - 1) = (N : ℝ) ^ (2 * k) := by
    rw [← pow_add]; congr 1; omega
  have hb : ((k : ℕ) : ℝ) * (x ^ (k + 1) * Δ) * A ^ (k - 1)
      ≤ ((k : ℕ) : ℝ) * (N : ℝ) ^ (((2 * k : ℕ) : ℝ) - C_K) := by
    calc ((k : ℕ) : ℝ) * (x ^ (k + 1) * Δ) * A ^ (k - 1)
        ≤ ((k : ℕ) : ℝ) * ((N : ℝ) ^ (k + 1) * (N : ℝ) ^ (-C_K)) * (N : ℝ) ^ (k - 1) := by
          gcongr
      _ = ((k : ℕ) : ℝ) * ((N : ℝ) ^ (2 * k) * (N : ℝ) ^ (-C_K)) := by rw [← hpow]; ring
      _ = ((k : ℕ) : ℝ) * (N : ℝ) ^ (((2 * k : ℕ) : ℝ) - C_K) := by
          rw [natpow_mul_rpow hN0]; ring_nf
  linarith

/-- (hshD) the QV time shift of the decay set. -/
theorem shD_le {N : ℕ} {C_K W x Δ D' : ℝ} {ℓ k : ℕ} (hN1 : (1 : ℝ) ≤ N) (hW2 : 2 ≤ W)
    (hWN : W ≤ N) (hD' : 0 ≤ D') (hx1 : 1 ≤ x) (hx : x ≤ N) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ (N : ℝ) ^ (-C_K)) (hℓ : ℓ ≤ k)
    (hev : (k : ℝ) * (N : ℝ) ^ (((k + 1 : ℕ) : ℝ) - C_K) ≤ (N : ℝ) ^ (-D')) :
    W ^ (-D') + (ℓ : ℝ) * (x ^ (ℓ + 1) * Δ) ≤ W ^ (-(D' - 1)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hW0 : 0 < W := by linarith
  have hx' : x ^ (ℓ + 1) ≤ (N : ℝ) ^ (k + 1) :=
    (pow_le_pow_right₀ hx1 (by omega)).trans (pow_le_pow_left₀ (by linarith) hx _)
  have hb : (ℓ : ℝ) * (x ^ (ℓ + 1) * Δ) ≤ (k : ℝ) * (N : ℝ) ^ (((k + 1 : ℕ) : ℝ) - C_K) := by
    calc (ℓ : ℝ) * (x ^ (ℓ + 1) * Δ) ≤ (k : ℝ) * ((N : ℝ) ^ (k + 1) * (N : ℝ) ^ (-C_K)) := by
          gcongr
      _ = (k : ℝ) * (N : ℝ) ^ (((k + 1 : ℕ) : ℝ) - C_K) := by
          rw [natpow_mul_rpow hN0]; ring_nf
  have hNW : (N : ℝ) ^ (-D') ≤ W ^ (-D') := Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
  have hWW : W ^ (-(D' - 1)) = W ^ (-D') * W := by
    rw [show -(D' - 1) = -D' + 1 by ring, Real.rpow_add hW0, Real.rpow_one]
  have hWD0 : 0 ≤ W ^ (-D') := Real.rpow_nonneg hW0.le _
  rw [hWW]
  nlinarith

end Absorb3

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section GridSize

/-- The grid size `K N = max 1 ⌈N^{C_K}⌉₊` (never zero; `= ⌈N^{C_K}⌉₊` for `N ≥ 1`). -/
def Kc (C_K : ℝ) (N : ℕ) : ℕ := max 1 ⌈(N : ℝ) ^ C_K⌉₊

theorem Kc_ne_zero (C_K : ℝ) (N : ℕ) : Kc C_K N ≠ 0 := by
  unfold Kc; omega

theorem Kc_le_ceil (C_K : ℝ) {N : ℕ} (hN : 1 ≤ N) : Kc C_K N ≤ ⌈(N : ℝ) ^ C_K⌉₊ := by
  unfold Kc
  have : 1 ≤ ⌈(N : ℝ) ^ C_K⌉₊ := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hN0 _)).ne'
  omega

theorem rpow_le_Kc (C_K : ℝ) (N : ℕ) : (N : ℝ) ^ C_K ≤ Kc C_K N := by
  unfold Kc
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)

theorem step_Kc_le {s v : ℕ → ℝ} (C_K : ℝ) {N : ℕ} (hN : 1 ≤ N) (hs0 : 0 ≤ s N)
    (hv1 : v N < 1) : step s v (Kc C_K) N ≤ (N : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hK := rpow_le_Kc C_K N
  have hKpos : (0 : ℝ) < Kc C_K N := hp.trans_le hK
  unfold step
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hKpos]
  have h1 : v N - s N ≤ 1 := by linarith
  have h2 : 1 ≤ ((N : ℝ) ^ C_K)⁻¹ * (Kc C_K N : ℝ) := by
    rw [inv_mul_eq_div, le_div_iff₀ hp, one_mul]; exact hK
  linarith

theorem ev_Kcard (C_K : ℝ) (hC : 0 ≤ C_K) :
    ∀ᶠ N : ℕ in atTop, ((Kc C_K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (C_K + 1) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ C_K := Real.one_le_rpow (by linarith) hC
  have hceil : (⌈(N : ℝ) ^ C_K⌉₊ : ℝ) < (N : ℝ) ^ C_K + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hN0.le _)
  have hK : (Kc C_K N : ℝ) ≤ (N : ℝ) ^ C_K + 1 := by
    unfold Kc
    rcases le_total 1 ⌈(N : ℝ) ^ C_K⌉₊ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; push_cast; linarith
  rw [Real.rpow_add hN0, Real.rpow_one]
  push_cast
  nlinarith

end GridSize

section Init

variable (d : Dims)

end Init

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Endpoint

variable (d : Dims)

end Endpoint

end RBM.Gauss.Grid

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

section Corollaries

variable (d : Dims)

end Corollaries

section Witness

variable (d : Dims)

end Witness

end RBM.Gauss.Grid

