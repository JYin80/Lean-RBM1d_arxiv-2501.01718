/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.EigenMeasurable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rescaling and counting for Step 1 of Theorem 2.6

[51, Theorem 2.2] compares correlation functions in the `ρ_fc`-rescaled pairing
`∫ O(α) p^{(k)}(E + α/(Mρ)) dα` (`scaledPairing`), while (2.21) is stated in the unrescaled
pairing `∫ O(α) p^{(k)}(E + α/M) dα` (`RBM.corrPairing`). This file supplies the deterministic
steps between the two:

* `scaledPairing_lipschitz`: `ρ ↦ scaledPairing … k O E ρ` is Lipschitz on `[ρmin, ρmax]`, with
  the Lipschitz constant a multiple of `corrPairing … k Q E` for a nonnegative test function `Q`;
  `Q` and the constant are fixed before the probability space, the matrix size and `E`.
* `exists_dominating_testFun`: a test function `Q' ≥ 0` with `Q β ≤ Q' (ρ β)` for all
  `ρ ∈ [ρmin, ρmax]`.
* `corrPairing_le_count`: for `0 ≤ Q ≤ 1_{[-R,R]^k}` and `k < M`,
  `corrPairing … k Q E ≤ (M/(M-k))^k · E[#{i : |λ_i - E| ≤ R/M}^k]`.

All rates are explicit parameters: the factor `|ρ - ρ'|` (instantiated in
`Flow/Step1BandNorm.lean` with `ρ = ρ_fc`, rate `step1Rate`) and the window radius `R` with power
`k` (instantiated there at scale `M^{-1+step1CountEps}`).
-/

open MeasureTheory Filter Matrix Topology Metric Set

namespace RBM.Gauss

/-! ### Elementary facts about test functions -/

/-- A test function vanishes outside a closed ball. File-stem-prefixed helper. -/
private theorem Step1Rescale.exists_support_radius {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : RBM.IsTestFun O) : ∃ R0 : ℝ, 0 ≤ R0 ∧ ∀ x, R0 < ‖x‖ → O x = 0 := by
  obtain ⟨R, hR⟩ := hO.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h := hR hmem
  rw [mem_closedBall, dist_zero_right] at h
  linarith [le_max_left R 0]

/-- A smooth bump on `Fin k → ℝ` equal to `1` on `closedBall 0 r`. File-stem-prefixed helper. -/
private theorem Step1Rescale.exists_bump {k : ℕ} (r : ℝ) :
    ∃ Q : (Fin k → ℝ) → ℝ, RBM.IsTestFun Q ∧ 0 ≤ Q ∧ ∀ x, ‖x‖ ≤ r → Q x = 1 := by
  let b : ContDiffBump (0 : Fin k → ℝ) :=
    ⟨max r 0 + 1, max r 0 + 2, by positivity, by linarith⟩
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, fun x => b.nonneg, fun x hx => ?_⟩
  apply b.one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ max r 0 + 1
  linarith [le_max_left r 0]

/-- Integrability of a correlation sum with a bounded continuous test function.
File-stem-prefixed helper. -/
private theorem Step1Rescale.integrable_corrSum {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsFiniteMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    {O : (Fin k → ℝ) → ℝ} (hO : Continuous O) {B : ℝ} (hB : ∀ x, ‖O x‖ ≤ B) (c E : ℝ) :
    Integrable (fun ω => ∑ f : Fin k ↪ n, O (fun j => c * ((hH ω).eigenvalues (f j) - E))) Pm := by
  refine Integrable.of_bound (measurable_corrSum hm hH k hO c E).aestronglyMeasurable
    ((Finset.univ : Finset (Fin k ↪ n)).card * B) (Eventually.of_forall fun ω => ?_)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun f _ => hB _).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ### `scaledPairing_lipschitz` -/

/-- The pointwise Lipschitz bound behind `scaledPairing_lipschitz`. File-stem-prefixed helper. -/
private theorem Step1Rescale.pointwise_lipschitz {k : ℕ} {O : (Fin k → ℝ) → ℝ}
    (hO : RBM.IsTestFun O) {ρmin ρmax : ℝ} (h0 : 0 < ρmin) :
    ∃ Q : (Fin k → ℝ) → ℝ, RBM.IsTestFun Q ∧ 0 ≤ Q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Fin k → ℝ, ∀ ρ ρ' : ℝ, ρ ∈ Icc ρmin ρmax → ρ' ∈ Icc ρmin ρmax →
        |ρ ^ k * O (fun j => ρ * x j) - ρ' ^ k * O (fun j => ρ' * x j)| ≤
          C * |ρ - ρ'| * Q x := by
  obtain ⟨R0, hR0, hsupp⟩ := Step1Rescale.exists_support_radius hO
  obtain ⟨B0, hB0⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  obtain ⟨B1, hB1⟩ := (hO.1.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hO.2.fderiv (𝕜 := ℝ))
  have hdiff : Differentiable ℝ O := hO.1.differentiable (by simp)
  set R1 : ℝ := R0 / ρmin with hR1def
  have hR1 : 0 ≤ R1 := div_nonneg hR0 h0.le
  obtain ⟨Q, hQ, hQ0, hQ1⟩ := Step1Rescale.exists_bump (k := k) R1
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  have hB1' : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  set C : ℝ := k * |ρmax| ^ (k - 1) * B0 + |ρmax| ^ k * B1 * R1 with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨Q, hQ, hQ0, C, hC, fun x ρ ρ' hρ hρ' => ?_⟩
  have hsx : ∀ s : ℝ, (fun j => s * x j) = s • x := fun s => rfl
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖s • x‖ = s * ‖x‖ := fun s hs => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  by_cases hx : ‖x‖ ≤ R1
  · rw [hQ1 x hx, mul_one, hsx ρ, hsx ρ']
    set φ : ℝ → ℝ := fun s => s ^ k * O (s • x) with hφ
    set φ' : ℝ → ℝ := fun s =>
      (k : ℝ) * s ^ (k - 1) * O (s • x) + s ^ k * (fderiv ℝ O (s • x) ((1 : ℝ) • x)) with hφ'
    have hder : ∀ s ∈ Icc ρmin ρmax, HasDerivWithinAt φ (φ' s) (Icc ρmin ρmax) s := by
      intro s _
      have hg : HasDerivAt (fun y : ℝ => y • x) ((1 : ℝ) • x) s := (hasDerivAt_id s).smul_const x
      have hcomp : HasDerivAt (fun y : ℝ => O (y • x)) (fderiv ℝ O (s • x) ((1 : ℝ) • x)) s :=
        (hdiff (s • x)).hasFDerivAt.comp_hasDerivAt s hg
      exact ((hasDerivAt_pow k s).mul hcomp).hasDerivWithinAt
    have hbound : ∀ s ∈ Icc ρmin ρmax, ‖φ' s‖ ≤ C := by
      intro s hs
      have hs0 : 0 ≤ s := h0.le.trans hs.1
      have hsm : s ≤ |ρmax| := hs.2.trans (le_abs_self _)
      have h1 : |s ^ (k - 1)| ≤ |ρmax| ^ (k - 1) := by
        rw [abs_of_nonneg (pow_nonneg hs0 _)]; exact pow_le_pow_left₀ hs0 hsm _
      have h2 : |s ^ k| ≤ |ρmax| ^ k := by
        rw [abs_of_nonneg (pow_nonneg hs0 _)]; exact pow_le_pow_left₀ hs0 hsm _
      have h3 : |O (s • x)| ≤ B0 := by simpa [Real.norm_eq_abs] using hB0 (s • x)
      have h4 : |fderiv ℝ O (s • x) ((1 : ℝ) • x)| ≤ B1 * R1 := by
        rw [← Real.norm_eq_abs, one_smul]
        refine ((fderiv ℝ O (s • x)).le_opNorm x).trans ?_
        exact mul_le_mul (hB1 _) hx (norm_nonneg _) hB1'
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_mul, Nat.abs_cast]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e1 : (k : ℝ) * |s ^ (k - 1)| * |O (s • x)| ≤ k * |ρmax| ^ (k - 1) * B0 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hk) h3 (abs_nonneg _) (by positivity)
      have e2 : |s ^ k| * |fderiv ℝ O (s • x) ((1 : ℝ) • x)| ≤ |ρmax| ^ k * B1 * R1 := by
        rw [mul_assoc]; exact mul_le_mul h2 h4 (abs_nonneg _) (by positivity)
      rw [hCdef]; linarith
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
      (convex_Icc ρmin ρmax) hρ' hρ
    simpa [hφ, Real.norm_eq_abs] using hmvt
  · push Not at hx
    have hzero : ∀ s ∈ Icc ρmin ρmax, O (s • x) = 0 := by
      intro s hs
      apply hsupp
      rw [hnorm s (h0.le.trans hs.1)]
      have hR0eq : ρmin * R1 = R0 := by rw [hR1def]; field_simp
      calc R0 = ρmin * R1 := hR0eq.symm
        _ < ρmin * ‖x‖ := mul_lt_mul_of_pos_left hx h0
        _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right hs.1 (norm_nonneg _)
    rw [hsx ρ, hsx ρ', hzero ρ hρ, hzero ρ' hρ']
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hC (abs_nonneg _)) (hQ0 x)

/-- Lipschitz dependence of the `ρ`-rescaled pairing on `ρ ∈ [ρmin, ρmax]`,
with the Lipschitz factor a fixed multiple of an unrescaled pairing against a nonnegative test
function `Q`. `Q` and `C` depend only on `k, O, ρmin, ρmax` (fixed before the measure). -/
theorem scaledPairing_lipschitz {k : ℕ} {O : (Fin k → ℝ) → ℝ} (hO : RBM.IsTestFun O)
    {ρmin ρmax : ℝ} (h0 : 0 < ρmin) (h1 : ρmin ≤ ρmax) :
    ∃ Q : (Fin k → ℝ) → ℝ, RBM.IsTestFun Q ∧ 0 ≤ Q ∧ ∃ C : ℝ, ∀ {Ω' : Type}
      [MeasurableSpace Ω'] (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type} [Fintype n]
      [DecidableEq n] (Hm : Ω' → Matrix n n ℂ), Measurable Hm → ∀ (hH : ∀ ω, (Hm ω).IsHermitian)
      (E ρ ρ' : ℝ), ρ ∈ Set.Icc ρmin ρmax → ρ' ∈ Set.Icc ρmin ρmax →
        |scaledPairing Pm Hm hH k O E ρ - scaledPairing Pm Hm hH k O E ρ'| ≤
          C * |ρ - ρ'| * RBM.corrPairing Pm Hm hH k Q E := by
  have _hne : ρmin ≤ ρmax := h1
  obtain ⟨Q, hQ, hQ0, C, hC, hpt⟩ := Step1Rescale.pointwise_lipschitz hO (ρmax := ρmax) h0
  refine ⟨Q, hQ, hQ0, C, ?_⟩
  intro Ω' _ Pm _ n _ _ Hm hm hH E ρ ρ' hρ hρ'
  obtain ⟨B0, hB0⟩ := hO.1.continuous.bounded_above_of_compact_support hO.2
  obtain ⟨BQ, hBQ⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hcontρ : ∀ r : ℝ, Continuous (fun β : Fin k → ℝ => O (fun j => r * β j)) := fun r =>
    hO.1.continuous.comp (continuous_pi fun j => continuous_const.mul (continuous_apply j))
  have hboundρ : ∀ r : ℝ, ∀ β : Fin k → ℝ, ‖O (fun j => r * β j)‖ ≤ B0 := fun r β => hB0 _
  have hIρ := Step1Rescale.integrable_corrSum Pm hm hH k (hcontρ ρ) (hboundρ ρ)
    (Fintype.card n : ℝ) E
  have hIρ' := Step1Rescale.integrable_corrSum Pm hm hH k (hcontρ ρ') (hboundρ ρ')
    (Fintype.card n : ℝ) E
  have hIQ := Step1Rescale.integrable_corrSum Pm hm hH k hQ.1.continuous hBQ
    (Fintype.card n : ℝ) E
  set c : ℝ := (Fintype.card n : ℝ) ^ k *
    (((Fintype.card n - k).factorial : ℝ) / (Fintype.card n).factorial) with hcdef
  have hc : 0 ≤ c := by positivity
  set A : Ω' → ℝ := fun ω => ∑ f : Fin k ↪ n,
    O (fun j => ρ * ((Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E))) with hA
  set B : Ω' → ℝ := fun ω => ∑ f : Fin k ↪ n,
    O (fun j => ρ' * ((Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E))) with hB
  set S : Ω' → ℝ := fun ω => ∑ f : Fin k ↪ n,
    Q (fun j => (Fintype.card n : ℝ) * ((hH ω).eigenvalues (f j) - E)) with hS
  change |ρ ^ k * (c * ∫ ω, A ω ∂Pm) - ρ' ^ k * (c * ∫ ω, B ω ∂Pm)| ≤
    C * |ρ - ρ'| * (c * ∫ ω, S ω ∂Pm)
  have hdiff : ρ ^ k * ∫ ω, A ω ∂Pm - ρ' ^ k * ∫ ω, B ω ∂Pm =
      ∫ ω, (ρ ^ k * A ω - ρ' ^ k * B ω) ∂Pm := by
    rw [integral_sub (hIρ.const_mul _) (hIρ'.const_mul _), integral_const_mul, integral_const_mul]
  have hle : |∫ ω, (ρ ^ k * A ω - ρ' ^ k * B ω) ∂Pm| ≤ ∫ ω, C * |ρ - ρ'| * S ω ∂Pm := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hIQ.const_mul _) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    simp only [hA, hB, hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun f _ => hpt _ ρ ρ' hρ hρ')
  have hrw : ρ ^ k * (c * ∫ ω, A ω ∂Pm) - ρ' ^ k * (c * ∫ ω, B ω ∂Pm) =
      c * (ρ ^ k * ∫ ω, A ω ∂Pm - ρ' ^ k * ∫ ω, B ω ∂Pm) := by ring
  rw [hrw, abs_mul, abs_of_nonneg hc, hdiff]
  calc c * |∫ ω, (ρ ^ k * A ω - ρ' ^ k * B ω) ∂Pm| ≤ c * (C * |ρ - ρ'| * ∫ ω, S ω ∂Pm) :=
        mul_le_mul_of_nonneg_left (hle.trans_eq (integral_const_mul _ _)) hc
    _ = C * |ρ - ρ'| * (c * ∫ ω, S ω ∂Pm) := by ring

/-! ### `exists_dominating_testFun` -/

/-- A nonnegative test function `Q'` dominating `Q` after every dilation
`β ↦ ρ β` with `ρ ∈ [ρmin, ρmax]`: `Q β ≤ Q' (ρ β)`. (No sign condition on `ρmin, ρmax` is
needed.) -/
theorem exists_dominating_testFun {k : ℕ} {Q : (Fin k → ℝ) → ℝ} (hQ : RBM.IsTestFun Q)
    (ρmin ρmax : ℝ) :
    ∃ Q' : (Fin k → ℝ) → ℝ, RBM.IsTestFun Q' ∧ 0 ≤ Q' ∧
      ∀ ρ ∈ Set.Icc ρmin ρmax, ∀ β : Fin k → ℝ, Q β ≤ Q' (fun j => ρ * β j) := by
  obtain ⟨R0, hR0, hsupp⟩ := Step1Rescale.exists_support_radius hQ
  obtain ⟨B0, hB0⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  set ρbar : ℝ := max |ρmin| |ρmax|
  obtain ⟨b, hb, hb0, hb1⟩ := Step1Rescale.exists_bump (k := k) (ρbar * R0)
  refine ⟨fun y => B0 * b y, ⟨contDiff_const.mul hb.1, hb.2.mul_left⟩,
    fun y => mul_nonneg hB0' (hb0 y), fun ρ hρ β => ?_⟩
  by_cases hβ : ‖β‖ ≤ R0
  · have hρabs : |ρ| ≤ ρbar := by
      rcases le_or_gt 0 ρ with h | h
      · rw [abs_of_nonneg h]; exact (hρ.2.trans (le_abs_self _)).trans (le_max_right _ _)
      · rw [abs_of_neg h]
        exact (neg_le_neg hρ.1 |>.trans (neg_le_abs _)).trans (le_max_left _ _)
    have hn : ‖(fun j => ρ * β j : Fin k → ℝ)‖ ≤ ρbar * R0 := by
      change ‖ρ • β‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hρabs hβ (norm_nonneg _) ((abs_nonneg _).trans hρabs)
    change Q β ≤ B0 * b (fun j => ρ * β j)
    rw [hb1 _ hn, mul_one]
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hB0 β)
  · push Not at hβ
    rw [hsupp β hβ]
    exact mul_nonneg hB0' (hb0 _)

/-! ### `corrPairing_le_count` -/

/-- Measurability of a single eigenvalue along a measurable, everywhere-Hermitian matrix map
(the same Weyl-bound argument as in `EigenMeasurable.lean`, whose helpers are private).
File-stem-prefixed helper. -/
private theorem Step1Rescale.measurable_eigenvalue {Ω' : Type*} [MeasurableSpace Ω'] {n : Type*}
    [Fintype n] [DecidableEq n] {Hm : Ω' → Matrix n n ℂ} (hm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (i : n) : Measurable (fun ω => (hH ω).eigenvalues i) := by
  have hcont : Continuous (fun x : {A : Matrix n n ℂ // A.IsHermitian} =>
      x.2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)) := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} => y.2.eigenvalues₀ _)
      (𝓝 x) (𝓝 (x.2.eigenvalues₀ _))
    rw [tendsto_iff_dist_tendsto_zero]
    have hsub : Continuous (fun A : Matrix n n ℂ => A - x.1) := continuous_id.sub continuous_const
    have hc : Continuous (fun A : Matrix n n ℂ =>
        Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2)) :=
      Continuous.sqrt (continuous_finsetSum Finset.univ fun a _ =>
        continuous_finsetSum Finset.univ fun b _ =>
          (((continuous_apply b).comp (continuous_apply a)).comp hsub).norm.pow 2)
    have h0 : Tendsto (fun A : Matrix n n ℂ => Real.sqrt (∑ a, ∑ b, ‖(A - x.1) a b‖ ^ 2))
        (𝓝 x.1) (𝓝 0) := by
      have hval : Real.sqrt (∑ a, ∑ b, ‖(x.1 - x.1) a b‖ ^ 2) = 0 := by simp
      have := hc.continuousAt (x := x.1)
      rwa [ContinuousAt, hval] at this
    have hcomp : Tendsto (fun y : {A : Matrix n n ℂ // A.IsHermitian} =>
        Real.sqrt (∑ a, ∑ b, ‖(y.1 - x.1) a b‖ ^ 2)) (𝓝 x) (𝓝 0) :=
      h0.comp (continuous_subtype_val.continuousAt (x := x))
    refine squeeze_zero (fun _ => dist_nonneg) (fun y => ?_) hcomp
    rw [Real.dist_eq]
    exact eigenvalues₀_abs_sub_le y.2 x.2 _
  have hφ : Measurable (fun ω => (⟨Hm ω, hH ω⟩ : {A : Matrix n n ℂ // A.IsHermitian})) :=
    hm.subtype_mk (h := hH)
  have := hcont.measurable.comp hφ
  simpa [Matrix.IsHermitian.eigenvalues, Function.comp_def] using this

/-- The number of injective `k`-tuples with values in a finite set `S` is at most `|S|^k`.
File-stem-prefixed helper. -/
private theorem Step1Rescale.card_embedding_filter_le {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (S : Finset n) :
    ((Finset.univ : Finset (Fin k ↪ n)).filter (fun f => ∀ j, f j ∈ S)).card ≤ S.card ^ k := by
  calc ((Finset.univ : Finset (Fin k ↪ n)).filter (fun f => ∀ j, f j ∈ S)).card
      ≤ (Fintype.piFinset (fun _ : Fin k => S)).card := by
        refine Finset.card_le_card_of_injOn (fun f => ⇑f) (fun f hf => ?_) ?_
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
          simpa [Fintype.mem_piFinset] using hf
        · intro f _ g _ hfg
          exact DFunLike.coe_injective hfg
    _ = S.card ^ k := by simp [Fintype.card_piFinset]

/-- The normalization of `RBM.corrPairing` is at most `(M/(M-k))^k` for `k < M`.
File-stem-prefixed helper. -/
private theorem Step1Rescale.prefactor_le {M k : ℕ} (hk : k < M) :
    (M : ℝ) ^ k * (((M - k).factorial : ℝ) / (M.factorial : ℝ)) ≤
      ((M : ℝ) / ((M : ℝ) - k)) ^ k := by
  have hMk : (0 : ℝ) < (M : ℝ) - k := by
    have : (k : ℝ) < M := by exact_mod_cast hk
    linarith
  have hfac : ((M.factorial : ℕ) : ℝ) = ((M - k).factorial : ℝ) * (M.descFactorial k : ℝ) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial hk.le]
  have hdesc : ((M : ℝ) - k) ^ k ≤ (M.descFactorial k : ℝ) := by
    have h1 : (M - k) ^ k ≤ M.descFactorial k :=
      (Nat.pow_le_pow_left (by omega) k).trans (Nat.pow_sub_le_descFactorial M k)
    have h2 : (((M - k : ℕ) : ℝ)) = (M : ℝ) - k := by rw [Nat.cast_sub hk.le]
    rw [← h2]; exact_mod_cast h1
  have hfpos : (0 : ℝ) < ((M - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hdpos : (0 : ℝ) < ((M : ℝ) - k) ^ k := pow_pos hMk k
  rw [hfac, div_pow, div_mul_cancel_left₀ hfpos.ne', div_eq_mul_inv ((M : ℝ) ^ k)]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hdpos hdesc) (by positivity)

/-- For `0 ≤ Q ≤ 1_{[-R,R]^k}` and `k < M`, the pairing is bounded by the
`k`-th moment of the number of eigenvalues in the window `[E - R/M, E + R/M]`:
`corrPairing … k Q E ≤ (M/(M-k))^k · E[#{i : |λ_i - E| ≤ R/M}^k]`. -/
theorem corrPairing_le_count {Ω' : Type*} [MeasurableSpace Ω'] (Pm : Measure Ω')
    [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n] (Hm : Ω' → Matrix n n ℂ)
    (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) (hk : k < Fintype.card n)
    {Q : (Fin k → ℝ) → ℝ} (hQ0 : 0 ≤ Q) {R : ℝ}
    (hQR : ∀ β, Q β ≤ Set.indicator (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R)
      (fun _ => (1 : ℝ)) β)
    (E : ℝ) :
    RBM.corrPairing Pm Hm hH k Q E ≤
      ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - k)) ^ k *
        ∫ ω, (((Finset.univ : Finset n).filter
          (fun i => |(hH ω).eigenvalues i - E| ≤ R / (Fintype.card n : ℝ))).card : ℝ) ^ k
          ∂Pm := by
  set M : ℕ := Fintype.card n with hMdef
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  set cnt : Ω' → ℝ := fun ω => (((Finset.univ : Finset n).filter
    (fun i => |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ))).card : ℝ) ^ k with hcnt
  -- measurability and integrability of the count
  have hcnt_meas : Measurable cnt := by
    have heq : cnt = fun ω => (∑ i : n,
        if |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ) then (1 : ℝ) else 0) ^ k := by
      funext ω; simp only [hcnt, Finset.natCast_card_filter]
    rw [heq]
    refine Measurable.pow_const (Finset.measurable_sum _ fun i _ => ?_) k
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le
      (continuous_abs.measurable.comp
        ((Step1Rescale.measurable_eigenvalue hm hH i).sub_const E)) measurable_const
  have hcnt_int : Integrable cnt Pm := by
    refine Integrable.of_bound hcnt_meas.aestronglyMeasurable ((M : ℝ) ^ k)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have := Finset.card_filter_le (Finset.univ : Finset n)
      (fun i => |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ))
    rw [Finset.card_univ] at this
    exact_mod_cast this
  have hcnt_nonneg : ∀ ω, 0 ≤ cnt ω := fun ω => by positivity
  -- the pointwise count bound
  have hpt : ∀ ω, (∑ f : Fin k ↪ n,
      Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E))) ≤ cnt ω := by
    intro ω
    set S : Finset n := (Finset.univ : Finset n).filter
      (fun i => |(hH ω).eigenvalues i - E| ≤ R / (M : ℝ)) with hSdef
    have hmem : ∀ i, (M : ℝ) * ((hH ω).eigenvalues i - E) ∈ Set.Icc (-R) R ↔ i ∈ S := by
      intro i
      rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos hMpos, hSdef, Finset.mem_filter,
        le_div_iff₀ hMpos]
      rw [mul_comm]
      simp
    calc (∑ f : Fin k ↪ n, Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E)))
        ≤ ∑ f : Fin k ↪ n, (if ∀ j, f j ∈ S then (1 : ℝ) else 0) := by
          refine Finset.sum_le_sum fun f _ => (hQR _).trans_eq ?_
          by_cases h : ∀ j, f j ∈ S
          · rw [Set.indicator_of_mem
              (Set.mem_univ_pi.mpr fun j => (hmem (f j)).mpr (h j))]
            simp [h]
          · rw [Set.indicator_of_notMem
              (fun hc => h fun j => (hmem (f j)).mp (Set.mem_univ_pi.mp hc j))]
            simp [h]
      _ = (((Finset.univ : Finset (Fin k ↪ n)).filter (fun f => ∀ j, f j ∈ S)).card : ℝ) := by
          rw [Finset.natCast_card_filter]
      _ ≤ ((S.card ^ k : ℕ) : ℝ) := by
          exact_mod_cast Step1Rescale.card_embedding_filter_le k S
      _ = cnt ω := by simp only [hcnt, hSdef, Nat.cast_pow]
  -- integrate
  have hint : ∫ ω, (∑ f : Fin k ↪ n,
      Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E))) ∂Pm ≤ ∫ ω, cnt ω ∂Pm :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun f _ => hQ0 _) hcnt_int
      (Eventually.of_forall hpt)
  have hpre := Step1Rescale.prefactor_le hk
  have hint0 : 0 ≤ ∫ ω, cnt ω ∂Pm := integral_nonneg hcnt_nonneg
  change (M : ℝ) ^ k * (((M - k).factorial : ℝ) / (M.factorial : ℝ)) *
      ∫ ω, (∑ f : Fin k ↪ n, Q (fun j => (M : ℝ) * ((hH ω).eigenvalues (f j) - E))) ∂Pm ≤
    ((M : ℝ) / ((M : ℝ) - k)) ^ k * ∫ ω, cnt ω ∂Pm
  exact mul_le_mul hpre hint (integral_nonneg fun ω => Finset.sum_nonneg fun f _ => hQ0 _)
    (pow_nonneg (div_nonneg hMpos.le (by
      have : (k : ℝ) < M := by exact_mod_cast hk
      linarith)) k)

/-! ### Consumer forms (public, file-stem prefixed) -/

/-- A test function is bounded by a positive multiple of the indicator of a box `[-R,R]^k`.
Public helper for `Flow/Step1BandNorm.lean` (to feed `corrPairing_le_count` /
`Step1Rescale.corrPairing_le_count_smul` with a dominating test function). -/
theorem Step1Rescale.exists_le_indicator {k : ℕ} {Q : (Fin k → ℝ) → ℝ} (hQ : RBM.IsTestFun Q) :
    ∃ B R : ℝ, 0 < B ∧ 0 ≤ R ∧ ∀ β, Q β ≤ B * Set.indicator
      (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R) (fun _ => (1 : ℝ)) β := by
  obtain ⟨R0, hR0, hsupp⟩ := Step1Rescale.exists_support_radius hQ
  obtain ⟨B0, hB0⟩ := hQ.1.continuous.bounded_above_of_compact_support hQ.2
  have hB0' : 0 ≤ B0 := (norm_nonneg _).trans (hB0 0)
  refine ⟨B0 + 1, R0, by linarith, hR0, fun β => ?_⟩
  by_cases hβ : ‖β‖ ≤ R0
  · have hmem : β ∈ Set.univ.pi fun _ : Fin k => Set.Icc (-R0) R0 := by
      refine Set.mem_univ_pi.mpr fun j => ?_
      rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs]
      exact (norm_le_pi_norm β j).trans hβ
    rw [Set.indicator_of_mem hmem, mul_one]
    have := (le_abs_self (Q β)).trans (by simpa [Real.norm_eq_abs] using hB0 β)
    linarith
  · push Not at hβ
    rw [hsupp β hβ]
    exact mul_nonneg (by linarith) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- `corrPairing_le_count` with a general height: for `0 ≤ Q ≤ B · 1_{[-R,R]^k}`, `0 < B`,
`k < M`: `corrPairing … k Q E ≤ B (M/(M-k))^k · E[#{i : |λ_i - E| ≤ R/M}^k]`. -/
theorem Step1Rescale.corrPairing_le_count_smul {Ω' : Type*} [MeasurableSpace Ω']
    (Pm : Measure Ω') [IsProbabilityMeasure Pm] {n : Type*} [Fintype n] [DecidableEq n]
    (Hm : Ω' → Matrix n n ℂ) (hm : Measurable Hm) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ)
    (hk : k < Fintype.card n) {Q : (Fin k → ℝ) → ℝ} (hQ0 : 0 ≤ Q) {B R : ℝ} (hB : 0 < B)
    (hQR : ∀ β, Q β ≤ B * Set.indicator (Set.univ.pi fun _ : Fin k => Set.Icc (-R) R)
      (fun _ => (1 : ℝ)) β)
    (E : ℝ) :
    RBM.corrPairing Pm Hm hH k Q E ≤
      B * ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - k)) ^ k *
        ∫ ω, (((Finset.univ : Finset n).filter
          (fun i => |(hH ω).eigenvalues i - E| ≤ R / (Fintype.card n : ℝ))).card : ℝ) ^ k
          ∂Pm := by
  have h := corrPairing_le_count Pm Hm hm hH k hk (Q := fun β => B⁻¹ * Q β)
    (fun β => mul_nonneg (inv_nonneg.mpr hB.le) (hQ0 β)) (R := R)
    (fun β => by
      rw [inv_mul_le_iff₀ hB]; exact hQR β) E
  have hlin : RBM.corrPairing Pm Hm hH k Q E =
      B * RBM.corrPairing Pm Hm hH k (fun β => B⁻¹ * Q β) E := by
    unfold RBM.corrPairing
    simp_rw [← Finset.mul_sum, integral_const_mul]
    field_simp
  rw [hlin, mul_assoc B]
  exact mul_le_mul_of_nonneg_left h hB.le

/-! ### Satisfiability witnesses (nondegenerate instances at the GUE matrix) -/

end RBM.Gauss
