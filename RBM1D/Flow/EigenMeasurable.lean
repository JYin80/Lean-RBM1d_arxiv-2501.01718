/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EigenWeyl
import RBM1D.Flow.DBMInput
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Measurability and law congruence of correlation pairings

Measurability of the (unnormalized) correlation-pairing sum in terms of a measurable
Hermitian-matrix-valued map, congruence of `RBM.corrPairing` under equality of pushforward laws,
monotonicity in the test function, and the energy-shift identity (Theorem 2.6).

## Route to `measurable_corrSum`

Mathlib's `Matrix.IsHermitian.eigenvalues₀` (`Analysis/Matrix/Spectrum.lean`) needs a Hermitian
proof to evaluate, so it is not literally a function on all of `Matrix n n ℂ`.  On the *subtype*
`{A // A.IsHermitian}` (with the subspace topology, inherited from the ambient `Pi` topology on
`Matrix n n ℂ = n → n → ℂ`), it is continuous: the Weyl bound
`RBM.Gauss.eigenvalues₀_abs_sub_le` bounds `|eigenvalues₀ i A - eigenvalues₀ i B|`
by a manifestly continuous (Frobenius-type) function of `A - B` that vanishes at `A = B`, so a
squeeze argument gives continuity, hence measurability (`Continuous.measurable`, using the
standard `OpensMeasurableSpace`/`BorelSpace` instances for finite `Pi` types of `ℂ`). Composing
with `Measurable.subtype_mk` along a measurable `Hm : Ω' → Matrix n n ℂ` that is *always*
Hermitian gives `measurable_corrSum`.

## Route to `corrPairing_congr_law`

The same measurability, applied to the identity map on the Hermitian subtype, gives a *global*
measurable extension `EigenMeasurable.corrSumVal` of the correlation sum to all of
`Matrix n n ℂ` (junk value `0` off the Hermitian locus, via `Measurable.dite`). Pushing the
integral through `H₁`, `H₂` via `MeasureTheory.integral_map` and the hypothesis
`P₁.map H₁ = P₂.map H₂` gives the congruence.

## Route to `corrPairing_shift`

`A - (E₀ : ℂ) • 1` is `hA.cfc (fun x => x - E₀)` (`Matrix.IsHermitian.cfc`,
`Analysis/Matrix/HermitianFunctionalCalculus.lean`), so its characteristic polynomial is
`∏ i, (X - C (hA.eigenvalues i - E₀))` (`Matrix.IsHermitian.charpoly_cfc_eq`). Matching sorted
roots (`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`, using that a constant shift of an
antitone sequence is antitone) identifies the eigenvalues of the shifted matrix.
-/

open MeasureTheory Filter Matrix Polynomial Topology
open scoped ComplexConjugate

namespace RBM.Gauss

/-! ### Measurability of the eigenvalue functions -/

section Measurability

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian matrices form a closed (hence measurable) subset of `Matrix n n ℂ`, for any
index type `n` (generalizing `Gauss/GridGoodSet.lean`'s `measurableSet_isHermitian`, which is
specific to one concrete index type). File-stem-prefixed helper. -/
private theorem EigenMeasurable.measurableSet_isHermitian :
    MeasurableSet {A : Matrix n n ℂ | A.IsHermitian} := by
  have hcont : Continuous (fun A : Matrix n n ℂ => Aᴴ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.conjTranspose_apply]
    exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
  have heq : {A : Matrix n n ℂ | A.IsHermitian} = {A | Aᴴ = A} := rfl
  rw [heq]
  exact (isClosed_eq hcont continuous_id).measurableSet

/-- Continuity of `A.eigenvalues₀ i` on the Hermitian subtype (subspace topology), via the Weyl
bound `RBM.Gauss.eigenvalues₀_abs_sub_le`. File-stem-prefixed helper. -/
private theorem EigenMeasurable.continuous_eigenvalues₀_subtype (i : Fin (Fintype.card n)) :
    Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues₀ i) := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ i)
    (𝓝 x) (𝓝 (x.2.eigenvalues₀ i))
  rw [tendsto_iff_dist_tendsto_zero]
  have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
  have hcont : Continuous (fun A : Matrix n n ℂ =>
      Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
    Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
      continuous_finsetSum Finset.univ fun b _ =>
        (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
  have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
      (𝓝 x.1) (𝓝 0) := by
    have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
    have := hcont.continuousAt (x := x.1)
    rwa [ContinuousAt, hval] at this
  have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
      Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
    h0.comp (continuous_subtype_val.continuousAt (x := x))
  refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
  rw [Real.dist_eq]
  exact eigenvalues₀_abs_sub_le y.2 x.2 i

/-- Measurability of `A.eigenvalues₀ i` on the Hermitian subtype. -/
private theorem EigenMeasurable.measurable_eigenvalues₀_subtype (i : Fin (Fintype.card n)) :
    Measurable (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues₀ i) :=
  (EigenMeasurable.continuous_eigenvalues₀_subtype i).measurable

/-- Measurability of `A.eigenvalues i` on the Hermitian subtype, `n`-indexed. -/
private theorem EigenMeasurable.measurable_eigenvalues_subtype (i : n) :
    Measurable (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues i) := by
  have := EigenMeasurable.measurable_eigenvalues₀_subtype
    (n := n) ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)
  simpa [Matrix.IsHermitian.eigenvalues] using this

/-- Measurability of the correlation-sum integrand, for a measurable and
everywhere-Hermitian matrix-valued map. -/
theorem measurable_corrSum {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*} [Fintype n]
    [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : Continuous O)
    (c E : ℝ) :
    Measurable (fun ω => ∑ f : Fin k ↪ n, O (fun j => c * ((hH ω).eigenvalues (f j) - E))) := by
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have heig : ∀ i : n, Measurable (fun ω => (hH ω).eigenvalues i) := by
    intro i
    have h : Measurable ((fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2.eigenvalues i) ∘
        (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian}))) :=
      (EigenMeasurable.measurable_eigenvalues_subtype i).comp hφ
    exact h
  have heigPi : Measurable (fun ω i => (hH ω).eigenvalues i) := measurable_pi_iff.mpr heig
  refine Finset.measurable_sum _ (fun f _ => ?_)
  refine hO.measurable.comp ?_
  refine measurable_pi_iff.mpr (fun j => ?_)
  have h1 : Measurable (fun ω => (hH ω).eigenvalues (f j)) := (measurable_pi_apply (f j)).comp heigPi
  have h2 : Measurable (fun ω => (hH ω).eigenvalues (f j) - E) := h1.sub_const E
  exact h2.const_mul c

end Measurability

/-! ### `corrPairing_congr_law`: global extension and law congruence -/

section CongrLaw

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The correlation-sum function, extended to all of `Matrix n n ℂ` by the junk value `0` off
the Hermitian locus (needed to push the integral through `Measure.map`). File-stem-prefixed
helper. -/
private noncomputable def EigenMeasurable.corrSumVal (k : ℕ) (O : (Fin k → ℝ) → ℝ) (E : ℝ)
    (A : Matrix n n ℂ) : ℝ :=
  if hA : A.IsHermitian then
    ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * (hA.eigenvalues (f j) - E))
  else 0

private theorem EigenMeasurable.measurable_corrSumVal (k : ℕ) {O : (Fin k → ℝ) → ℝ}
    (hO : Continuous O) (E : ℝ) :
    Measurable (EigenMeasurable.corrSumVal (n := n) k O E) := by
  have hf : Measurable (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * (x.2.eigenvalues (f j) - E))) :=
    measurable_corrSum measurable_subtype_coe (fun x : {A : Matrix n n ℂ // A.IsHermitian} => x.2)
      k hO (Fintype.card n : ℝ) E
  have hg : Measurable (fun _ : {A : Matrix n n ℂ // ¬ A.IsHermitian} => (0 : ℝ)) :=
    measurable_const
  have hdite := Measurable.dite (s := {A : Matrix n n ℂ | A.IsHermitian}) hf hg
    EigenMeasurable.measurableSet_isHermitian
  have heq : EigenMeasurable.corrSumVal (n := n) k O E = fun A =>
      if hA : A ∈ {A : Matrix n n ℂ | A.IsHermitian} then
        ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * (hA.eigenvalues (f j) - E))
      else 0 := rfl
  rw [heq]
  exact hdite

private theorem EigenMeasurable.corrSumVal_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Hm : Ω' → Matrix n n ℂ} (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) (O : (Fin k → ℝ) → ℝ)
    (E : ℝ) (ω : Ω') :
    EigenMeasurable.corrSumVal k O E (Hm ω) =
      ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) := by
  simp only [EigenMeasurable.corrSumVal, dif_pos (hH ω)]

/-- File-local step: `RBM.corrPairing` rewritten as a scalar multiple of the pushforward integral
of `EigenMeasurable.corrSumVal`. -/
private theorem EigenMeasurable.corrPairing_eq_integral_corrSumVal {Ω' : Type*}
    [MeasurableSpace Ω'] (P : Measure Ω') {H : Ω' → Matrix n n ℂ} (hm : Measurable H)
    (hH : ∀ ω, (H ω).IsHermitian) (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) (E : ℝ) :
    RBM.corrPairing P H hH k O E =
      (Fintype.card n : ℝ) ^ k * (((Fintype.card n - k).factorial : ℝ) /
          (Fintype.card n).factorial) *
        ∫ A, EigenMeasurable.corrSumVal k O E A ∂(P.map H) := by
  have hmeas : Measurable (EigenMeasurable.corrSumVal (n := n) k O E) :=
    EigenMeasurable.measurable_corrSumVal k hO E
  unfold RBM.corrPairing
  congr 1
  rw [MeasureTheory.integral_map hm.aemeasurable hmeas.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun ω => (EigenMeasurable.corrSumVal_eq hH k O E ω).symm))

/-- Congruence of `RBM.corrPairing` under equality of the pushforward laws
of the two Hermitian-matrix-valued maps. -/
theorem corrPairing_congr_law {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {n : Type*} [Fintype n] [DecidableEq n] {H₁ : Ω₁ → Matrix n n ℂ} {H₂ : Ω₂ → Matrix n n ℂ}
    (hm₁ : Measurable H₁) (hm₂ : Measurable H₂) (h₁ : ∀ ω, (H₁ ω).IsHermitian)
    (h₂ : ∀ ω, (H₂ ω).IsHermitian) (hlaw : P₁.map H₁ = P₂.map H₂) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) (E : ℝ) :
    RBM.corrPairing P₁ H₁ h₁ k O E = RBM.corrPairing P₂ H₂ h₂ k O E := by
  rw [EigenMeasurable.corrPairing_eq_integral_corrSumVal P₁ hm₁ h₁ k hO E,
    EigenMeasurable.corrPairing_eq_integral_corrSumVal P₂ hm₂ h₂ k hO E, hlaw]

end CongrLaw

/-! ### `corrPairing_mono`: monotonicity in the test function -/

section Mono

/-- Monotonicity of `RBM.corrPairing` in the test function `O`, given
integrability of the two correlation sums (satisfied e.g. whenever `O`, `O'` are bounded and
measurable, since `P` need not even be a probability measure for this direction — any finite
measure suffices; boundedness plus continuity with compact support, as for `RBM.IsTestFun`,
gives integrability against a probability measure directly). -/
theorem corrPairing_mono {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {n : Type*}
    [Fintype n] [DecidableEq n] {H : Ω' → Matrix n n ℂ} (hH : ∀ ω, (H ω).IsHermitian) (k : ℕ)
    {O O' : (Fin k → ℝ) → ℝ} (hOO' : O ≤ O') (E : ℝ)
    (hInt : Integrable (fun ω => ∑ f : Fin k ↪ n, O (fun j => (Fintype.card n : ℝ) *
        ((hH ω).eigenvalues (f j) - E))) P)
    (hInt' : Integrable (fun ω => ∑ f : Fin k ↪ n, O' (fun j => (Fintype.card n : ℝ) *
        ((hH ω).eigenvalues (f j) - E))) P) :
    RBM.corrPairing P H hH k O E ≤ RBM.corrPairing P H hH k O' E := by
  unfold RBM.corrPairing
  have hpref : 0 ≤ (Fintype.card n : ℝ) ^ k * (((Fintype.card n - k).factorial : ℝ) /
      (Fintype.card n).factorial) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpref
  exact integral_mono hInt hInt' (fun ω => Finset.sum_le_sum (fun f _ => hOO' _))

end Mono

/-! ### Acceptance witness for `corrPairing_congr_law` -/

section Witness

end Witness

/-! ### `corrPairing_shift`: the energy-shift identity -/

section Shift

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma EigenMeasurable.scalar_eq_smul_one (c : ℂ) :
    Matrix.scalar n c = c • (1 : Matrix n n ℂ) := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, Matrix.smul_apply]

/-- The energy shift `A - E₀ • 1` of a Hermitian matrix is Hermitian. -/
private lemma EigenMeasurable.isHermitian_sub_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (c : ℝ) : (A - (c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
  hA.sub (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))

/-- The characteristic polynomial of an energy shift, in terms of the unshifted eigenvalues
(`n`-indexed), via `Matrix.charpoly_sub_scalar` (no Weyl bound needed here: this is an *exact*
algebraic identity, not merely a perturbation estimate). -/
private lemma EigenMeasurable.charpoly_sub_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (c : ℝ) :
    (A - (c : ℂ) • (1 : Matrix n n ℂ)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((hA.eigenvalues i - c : ℝ) : ℂ)) := by
  have hscalar : A - (c : ℂ) • (1 : Matrix n n ℂ) = A - Matrix.scalar n (c : ℂ) := by
    rw [EigenMeasurable.scalar_eq_smul_one]
  rw [hscalar, Matrix.charpoly_sub_scalar, hA.charpoly_eq, Polynomial.prod_comp]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hcast : ((hA.eigenvalues i - c : ℝ) : ℂ) = (hA.eigenvalues i : ℂ) - (c : ℂ) := by
    push_cast; ring
  rw [hcast, map_sub]
  ring

/-- The roots of the characteristic polynomial of an energy shift, `n`-indexed. Stated with the
concrete `ℝ → ℂ` coercion `Complex.ofReal` (not the generic `RCLike.ofReal`), matching
`EigenMeasurable.charpoly_sub_smul_one`'s conclusion syntactically. -/
private lemma EigenMeasurable.roots_charpoly_shift {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (c : ℝ) :
    (A - (c : ℂ) • (1 : Matrix n n ℂ)).charpoly.roots =
      Multiset.map (Complex.ofReal ∘ (fun i => hA.eigenvalues i - c))
        (Finset.univ : Finset n).val := by
  rw [EigenMeasurable.charpoly_sub_smul_one hA c,
    Polynomial.roots_prod _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Function.comp_def]

/-- The roots of the characteristic polynomial of an energy shift, `Fin (Fintype.card n)`-indexed
via the (matrix-independent) reindexing bijection used by `Matrix.IsHermitian.eigenvalues`. -/
private lemma EigenMeasurable.roots_charpoly_shift₀ {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (c : ℝ) :
    (A - (c : ℂ) • (1 : Matrix n n ℂ)).charpoly.roots =
      Multiset.map (Complex.ofReal ∘ (fun j => hA.eigenvalues₀ j - c))
        (Finset.univ : Finset (Fin (Fintype.card n))).val := by
  rw [EigenMeasurable.roots_charpoly_shift hA c]
  simp only [← Multiset.map_map, Matrix.IsHermitian.eigenvalues,
    ← Function.comp_apply (f := fun j => hA.eigenvalues₀ j - c)]
  simp

/-- A constant shift of `eigenvalues₀` matches `eigenvalues₀` of the shifted matrix: both are
antitone sequences with the same underlying root multiset, hence (`sort_roots_charpoly_eq_eigenvalues₀`
plus uniqueness of the sorted arrangement of a multiset) they are equal as functions. -/
private lemma EigenMeasurable.eigenvalues₀_sub_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (c : ℝ) (hA' : (A - (c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian) :
    hA'.eigenvalues₀ = fun j => hA.eigenvalues₀ j - c := by
  have h1 := hA'.sort_roots_charpoly_eq_eigenvalues₀
  rw [EigenMeasurable.roots_charpoly_shift₀ hA c, Multiset.map_map] at h1
  simp only [RCLike.re_eq_complex_re, Function.comp_def, Complex.ofReal_re] at h1
  have hv : Antitone (fun j => hA.eigenvalues₀ j - c) :=
    fun _ _ hij => sub_le_sub_right (hA.eigenvalues₀_antitone hij) c
  have h2 : (Multiset.map (fun j => hA.eigenvalues₀ j - c)
      (Finset.univ : Finset (Fin (Fintype.card n))).val).sort (· ≥ ·) =
      List.ofFn (fun j => hA.eigenvalues₀ j - c) := by
    rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hv.sortedGE_ofFn
  rw [h2] at h1
  exact (List.ofFn_injective h1).symm

/-- A constant shift of `eigenvalues` matches `eigenvalues` of the shifted matrix, `n`-indexed. -/
private lemma EigenMeasurable.eigenvalues_sub_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (c : ℝ) (hA' : (A - (c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian) (i : n) :
    hA'.eigenvalues i = hA.eigenvalues i - c := by
  have h := EigenMeasurable.eigenvalues₀_sub_smul_one hA c hA'
  show hA'.eigenvalues₀ _ = hA.eigenvalues₀ _ - c
  rw [h]

/-- The energy-shift identity, `corrPairing (H - E₀ • 1) k O 0 =
corrPairing H k O E₀`. -/
theorem corrPairing_shift {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') {n : Type*}
    [Fintype n] [DecidableEq n] {H : Ω' → Matrix n n ℂ} (hH : ∀ ω, (H ω).IsHermitian) (E₀ : ℝ)
    (k : ℕ) (O : (Fin k → ℝ) → ℝ) :
    RBM.corrPairing P (fun ω => H ω - (E₀ : ℂ) • 1)
        (fun ω => EigenMeasurable.isHermitian_sub_smul_one (hH ω) E₀) k O 0 =
      RBM.corrPairing P H hH k O E₀ := by
  unfold RBM.corrPairing
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  refine Finset.sum_congr rfl (fun f _ => ?_)
  congr 1
  funext j
  rw [EigenMeasurable.eigenvalues_sub_smul_one (hH ω) E₀ _ (f j)]
  ring

end Shift

end RBM.Gauss
