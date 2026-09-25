/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Pure-probability grid lemmas for the P4 pilot (BDG replacement)

This file collects generic martingale/Azuma facts on an arbitrary probability
space `(Ω', μ)` with a filtration `ℱ : Filtration ℕ _`. Nothing here is
RBM-specific; the results are consumed by the discrete grid-Duhamel argument
described in `docs/claude-team/pilot-P4P5-paper.md` §4, §9.

## Main declarations

* `azuma_two_sided`: two-sided Azuma-Hoeffding tail bound for a sum of
  conditionally sub-Gaussian martingale differences with deterministic
  variance proxies, obtained from Mathlib's one-sided
  `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` applied to the
  process and its negation.
* `azuma_complex`: the complex-valued analogue, obtained by splitting into
  real and imaginary parts via `Complex.norm_le_sqrt_two_mul_max`.
* `doob_L2_max`: Doob's L² maximal inequality for a real martingale started at
  `0`, obtained from `MeasureTheory.maximal_ineq` applied to the nonnegative
  submartingale `(M k)^2`.
* `martingale_sq_eq_sum`: orthogonality of martingale increments,
  `∫ (M K)^2 = ∑_{k<K} ∫ (M (k+1) - M k)^2`.
* `stopped_martingale`: the process stopped at a bounded stopping time is
  again a martingale, obtained from `MeasureTheory.Submartingale.stoppedProcess`
  applied to `M` and `-M`.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped MeasureTheory NNReal ENNReal

namespace RBM.Gauss.Grid

section Azuma

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω']
  {μ : Measure Ω'} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- **Two-sided Azuma-Hoeffding inequality.** If `Y` is strongly adapted to `ℱ`, `Y 0` has a
sub-Gaussian mgf with deterministic parameter `c 0`, and every later increment `Y (i+1)` has a
conditionally sub-Gaussian mgf given `ℱ i` with deterministic parameter `c (i+1)`, then the sum
`∑_{i<n} Y i` concentrates around `0` on both sides at rate governed by `∑_{i<n} c i`. This is
Mathlib's one-sided `measure_sum_ge_le_of_hasCondSubgaussianMGF` applied to `Y` and to `-Y`. -/
theorem azuma_two_sided {Y : ℕ → Ω' → ℝ} {c : ℕ → ℝ≥0} (h_adapted : StronglyAdapted ℱ Y) (n : ℕ)
    (h0 : HasSubgaussianMGF (Y 0) (c 0) μ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (c (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ range n, Y i ω|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i)) := by
  have hUp : μ.real {ω | ε ≤ ∑ i ∈ range n, Y i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i)) :=
    measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted h0 n h_subG hε
  have h_adapted' : StronglyAdapted ℱ (-Y) := h_adapted.neg
  have h0' : HasSubgaussianMGF ((-Y) 0) (c 0) μ := h0.neg
  have h_subG' : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) ((-Y) (i + 1)) (c (i + 1)) μ :=
    fun i hi => Kernel.HasSubgaussianMGF.neg (h_subG i hi)
  have hDown : μ.real {ω | ε ≤ -∑ i ∈ range n, Y i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i)) := by
    have hneg := measure_sum_ge_le_of_hasCondSubgaussianMGF h_adapted' h0' n h_subG' hε
    have hseteq : {ω | ε ≤ ∑ i ∈ range n, (-Y) i ω} = {ω | ε ≤ -∑ i ∈ range n, Y i ω} := by
      ext ω
      simp [Finset.sum_neg_distrib]
    rwa [hseteq] at hneg
  have hset : {ω | ε ≤ |∑ i ∈ range n, Y i ω|} =
      {ω | ε ≤ ∑ i ∈ range n, Y i ω} ∪ {ω | ε ≤ -∑ i ∈ range n, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  calc
    μ.real {ω | ε ≤ |∑ i ∈ range n, Y i ω|}
        = μ.real ({ω | ε ≤ ∑ i ∈ range n, Y i ω} ∪ {ω | ε ≤ -∑ i ∈ range n, Y i ω}) := by
          rw [hset]
    _ ≤ μ.real {ω | ε ≤ ∑ i ∈ range n, Y i ω} + μ.real {ω | ε ≤ -∑ i ∈ range n, Y i ω} :=
          measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i))
        + Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i)) := add_le_add hUp hDown
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ range n, c i)) := by ring

/-- **Complex two-sided Azuma-Hoeffding inequality.** The same statement for `ℂ`-valued
increments `Z`, whose real and imaginary parts each satisfy the hypotheses of
`azuma_two_sided` with the same deterministic variance proxies `c`. -/
theorem azuma_complex {Z : ℕ → Ω' → ℂ} {c : ℕ → ℝ≥0}
    (hZR : StronglyAdapted ℱ (fun i ω => (Z i ω).re))
    (hZI : StronglyAdapted ℱ (fun i ω => (Z i ω).im)) (n : ℕ)
    (h0R : HasSubgaussianMGF (fun ω => (Z 0 ω).re) (c 0) μ)
    (h0I : HasSubgaussianMGF (fun ω => (Z 0 ω).im) (c 0) μ)
    (hCR : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Z (i + 1) ω).re) (c (i + 1)) μ)
    (hCI : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Z (i + 1) ω).im) (c (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ‖∑ i ∈ range n, Z i ω‖} ≤
      4 * Real.exp (-ε ^ 2 / (4 * ∑ i ∈ range n, c i)) := by
  have hεSqrt2 : 0 ≤ ε / Real.sqrt 2 := by positivity
  have hReTail := azuma_two_sided (Y := fun i ω => (Z i ω).re) hZR n h0R hCR hεSqrt2
  have hImTail := azuma_two_sided (Y := fun i ω => (Z i ω).im) hZI n h0I hCI hεSqrt2
  simp only [← Complex.re_sum, ← Complex.im_sum] at hReTail hImTail
  have hexp_eq : Real.exp (-(ε / Real.sqrt 2) ^ 2 / (2 * ∑ i ∈ range n, c i)) =
      Real.exp (-ε ^ 2 / (4 * ∑ i ∈ range n, c i)) := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    congr 1
    rw [div_pow, h2]
    ring
  rw [hexp_eq] at hReTail hImTail
  have hsplit : ∀ ω : Ω', ε ≤ ‖∑ i ∈ range n, Z i ω‖ →
      ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).re| ∨
      ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).im| := by
    intro ω hω
    have h1 : ε ≤ Real.sqrt 2 *
        max |(∑ i ∈ range n, Z i ω).re| |(∑ i ∈ range n, Z i ω).im| :=
      hω.trans (Complex.norm_le_sqrt_two_mul_max _)
    have h2 : ε / Real.sqrt 2 ≤
        max |(∑ i ∈ range n, Z i ω).re| |(∑ i ∈ range n, Z i ω).im| := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
      linarith [h1]
    exact le_max_iff.mp h2
  have hsubset : {ω | ε ≤ ‖∑ i ∈ range n, Z i ω‖} ⊆
      {ω | ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).re|} ∪
        {ω | ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).im|} := by
    intro ω hω
    rcases hsplit ω hω with h | h
    · exact Set.mem_union_left _ h
    · exact Set.mem_union_right _ h
  calc
    μ.real {ω | ε ≤ ‖∑ i ∈ range n, Z i ω‖}
        ≤ μ.real ({ω | ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).re|} ∪
            {ω | ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).im|}) :=
          measureReal_mono hsubset
    _ ≤ μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).re|}
        + μ.real {ω | ε / Real.sqrt 2 ≤ |(∑ i ∈ range n, Z i ω).im|} :=
          measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (4 * ∑ i ∈ range n, c i))
        + 2 * Real.exp (-ε ^ 2 / (4 * ∑ i ∈ range n, c i)) := add_le_add hReTail hImTail
    _ = 4 * Real.exp (-ε ^ 2 / (4 * ∑ i ∈ range n, c i)) := by ring

end Azuma

section Martingale

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'} {M : ℕ → Ω' → ℝ}

/-- Core one-step/one-window identity: for `i ≤ j`, conditioning `(M j)^2` on `ℱ i` splits into
`(M i)^2` plus the conditional second moment of the increment `M j - M i`. This is the standard
"orthogonality of martingale increments" computation, spelled out via Mathlib's conditional
expectation pull-out lemmas. -/
private theorem condExp_sq_eq_add (hM : Martingale M ℱ μ) (hM2 : ∀ k, MemLp (M k) 2 μ)
    {i j : ℕ} (hij : i ≤ j) :
    μ[fun ω => (M j ω) ^ 2 | ℱ i] =ᵐ[μ]
      fun ω => (M i ω) ^ 2 + (μ[fun ω => (M j ω - M i ω) ^ 2 | ℱ i]) ω := by
  have hMi2 : Integrable (M i * M i) μ := (hM2 i).integrable_mul (hM2 i)
  have hDiff : MemLp (M j - M i) 2 μ := (hM2 j).sub (hM2 i)
  have hsq2 : Integrable ((M j - M i) * (M j - M i)) μ := hDiff.integrable_mul hDiff
  have hCr : Integrable (M i * (M j - M i)) μ := (hM2 i).integrable_mul hDiff
  have hmeasMi2 : StronglyMeasurable[ℱ i] (M i * M i) :=
    (hM.stronglyAdapted i).mul (hM.stronglyAdapted i)
  have hcondSelf : μ[M i * M i | ℱ i] = M i * M i :=
    condExp_of_stronglyMeasurable (ℱ.le i) hmeasMi2 hMi2
  have hZeroDiff : μ[M j - M i | ℱ i] =ᵐ[μ] 0 := by
    have hsub := condExp_sub (hM.integrable j) (hM.integrable i) (ℱ i)
    have h2 : μ[M j | ℱ i] =ᵐ[μ] M i := hM.condExp_ae_eq hij
    have h3 : μ[M i | ℱ i] = M i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hM.stronglyAdapted i) (hM.integrable i)
    filter_upwards [hsub, h2] with ω hω1 hω2
    simp only [Pi.sub_apply, Pi.zero_apply] at hω1 ⊢
    rw [hω1, hω2, h3]
    ring
  have hcondCr : μ[M i * (M j - M i) | ℱ i] =ᵐ[μ] 0 := by
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := ℱ i) (f := M i) (g := M j - M i)
      (hM.stronglyAdapted i) hCr (hDiff.integrable (by norm_num))
    filter_upwards [h1, hZeroDiff] with ω hω1 hω2
    simp only [Pi.mul_apply, Pi.zero_apply] at hω1 hω2 ⊢
    rw [hω1, hω2]
    ring
  have hcondCrCr : μ[M i * (M j - M i) + M i * (M j - M i) | ℱ i] =ᵐ[μ] 0 := by
    have h1 := condExp_add hCr hCr (ℱ i)
    have h2 := h1.trans (hcondCr.add hcondCr)
    filter_upwards [h2] with ω hω
    simpa [Pi.add_apply, Pi.zero_apply] using hω
  have hPi : μ[M j * M j | ℱ i] =ᵐ[μ] M i * M i + μ[(M j - M i) * (M j - M i) | ℱ i] := by
    have hexpandDiff : M j * M j =
        M i * M i + (M i * (M j - M i) + M i * (M j - M i)) + (M j - M i) * (M j - M i) := by
      funext ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    have hsplit1 := condExp_add (hMi2.add (hCr.add hCr)) hsq2 (ℱ i)
    have hsplit2 := condExp_add hMi2 (hCr.add hCr) (ℱ i)
    rw [hexpandDiff]
    refine hsplit1.trans ?_
    refine (hsplit2.add (Filter.EventuallyEq.rfl)).trans ?_
    rw [hcondSelf]
    filter_upwards [hcondCrCr] with ω hω
    simp only [Pi.add_apply, Pi.zero_apply] at hω ⊢
    rw [hω]
    ring
  have heqJ : (fun ω => (M j ω) ^ 2) = M j * M j := by
    funext ω; simp only [Pi.mul_apply]; ring
  have heqD : (fun ω => (M j ω - M i ω) ^ 2) = (M j - M i) * (M j - M i) := by
    funext ω; simp only [Pi.mul_apply, Pi.sub_apply]; ring
  rw [heqJ, heqD]
  filter_upwards [hPi] with ω hω
  simp only [Pi.add_apply, Pi.mul_apply] at hω ⊢
  rw [hω]
  ring

/-- **Doob's L² maximal inequality.** For a real martingale `M` started at `0` with every `M k`
square-integrable, the maximum of `|M k|` over `k ≤ K` is controlled by the second moment of the
terminal value `M K`. Obtained from `MeasureTheory.maximal_ineq` applied to the nonnegative
submartingale `k ↦ (M k)^2`. -/
theorem doob_L2_max (hM : Martingale M ℱ μ) (_hM0 : M 0 = 0) (hM2 : ∀ k, MemLp (M k) 2 μ)
    (K : ℕ) {x : ℝ} (hx : 0 < x) :
    μ.real {ω | x ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => |M k ω|} ≤
      (∫ ω, (M K ω) ^ 2 ∂μ) / x ^ 2 := by
  have hSub : Submartingale (fun k ω => (M k ω) ^ 2) ℱ μ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      change StronglyMeasurable[ℱ k] (fun ω => (M k ω) ^ 2)
      have heq : (M k * M k) = fun ω => (M k ω) ^ 2 := by
        funext ω; simp only [Pi.mul_apply]; ring
      rw [← heq]
      exact (hM.stronglyAdapted k).mul (hM.stronglyAdapted k)
    · intro i j hij
      have hc := condExp_sq_eq_add hM hM2 hij
      have hnn : (0 : Ω' → ℝ) ≤ᵐ[μ] fun ω => (M j ω - M i ω) ^ 2 :=
        ae_of_all _ fun ω => sq_nonneg _
      have hcn := condExp_nonneg (m := ℱ i) hnn
      filter_upwards [hc, hcn] with ω hω hωn
      simp only [Pi.zero_apply] at hωn
      rw [hω]
      linarith
    · intro k
      change Integrable (fun ω => (M k ω) ^ 2) μ
      have h : Integrable (M k * M k) μ := (hM2 k).integrable_mul (hM2 k)
      have heq : (M k * M k) = fun ω => (M k ω) ^ 2 := by
        funext ω; simp only [Pi.mul_apply]; ring
      rwa [heq] at h
  have hnonneg : (0 : ℕ → Ω' → ℝ) ≤ fun k ω => (M k ω) ^ 2 := fun k ω => sq_nonneg _
  set εN : ℝ≥0 := ⟨x ^ 2, sq_nonneg x⟩ with hεNdef
  have hcoe : (εN : ℝ) = x ^ 2 := rfl
  have hmax := maximal_ineq hSub hnonneg (ε := εN) K
  set S2 : Set Ω' := {ω | (εN : ℝ) ≤ (range (K + 1)).sup' nonempty_range_add_one
    fun k => (M k ω) ^ 2} with hS2def
  have hset : {ω | x ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => |M k ω|} = S2 := by
    rw [hS2def, hcoe]
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have := (pow_le_pow_iff_left₀ hx.le (abs_nonneg (M k ω)) two_ne_zero).mpr hxk
      rwa [sq_abs] at this
    · rintro ⟨k, hk, hxk⟩
      refine ⟨k, hk, ?_⟩
      have hxk' : x ^ 2 ≤ |M k ω| ^ 2 := by rwa [sq_abs]
      exact (pow_le_pow_iff_left₀ hx.le (abs_nonneg (M k ω)) two_ne_zero).mp hxk'
  rw [hset]
  have hS2meas : MeasurableSet S2 := by
    rw [hS2def]
    exact measurableSet_le measurable_const
      (Finset.measurable_range_sup'' fun n _ => (hSub.stronglyMeasurable n).measurable.le (ℱ.le n))
  have hnnInt : 0 ≤ ∫ ω in S2, (M K ω) ^ 2 ∂μ :=
    setIntegral_nonneg hS2meas fun ω _ => sq_nonneg _
  have hrealBound : x ^ 2 * μ.real S2 ≤ ∫ ω in S2, (M K ω) ^ 2 ∂μ := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hnnInt, hcoe] at hmono
    exact hmono
  have hfull : ∫ ω in S2, (M K ω) ^ 2 ∂μ ≤ ∫ ω, (M K ω) ^ 2 ∂μ := by
    have hInt : Integrable (fun ω => (M K ω) ^ 2) μ := by
      have h : Integrable (M K * M K) μ := (hM2 K).integrable_mul (hM2 K)
      have heq : (M K * M K) = fun ω => (M K ω) ^ 2 := by
        funext ω; simp only [Pi.mul_apply]; ring
      rwa [heq] at h
    exact setIntegral_le_integral hInt (ae_of_all _ fun ω => sq_nonneg _)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < x ^ 2)]
  nlinarith [hrealBound, hfull]

/-- **Orthogonality of martingale increments.** For a real martingale `M` started at `0` with
every `M k` square-integrable, the second moment of the terminal value telescopes into the sum of
the second moments of the successive increments. -/
theorem martingale_sq_eq_sum (hM : Martingale M ℱ μ) (hM0 : M 0 = 0) (hM2 : ∀ k, MemLp (M k) 2 μ)
    (K : ℕ) :
    ∫ ω, (M K ω) ^ 2 ∂μ = ∑ k ∈ range K, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
  induction K with
  | zero => simp [hM0]
  | succ K ih =>
    have hc := condExp_sq_eq_add hM hM2 (Nat.le_succ K)
    have h1 : ∫ ω, (μ[fun ω => (M (K + 1) ω) ^ 2 | ℱ K]) ω ∂μ = ∫ ω, (M (K + 1) ω) ^ 2 ∂μ :=
      integral_condExp (ℱ.le K)
    have h2 : ∫ ω, (μ[fun ω => (M (K + 1) ω - M K ω) ^ 2 | ℱ K]) ω ∂μ
        = ∫ ω, (M (K + 1) ω - M K ω) ^ 2 ∂μ :=
      integral_condExp (ℱ.le K)
    have hInt2 : Integrable (fun ω => (M K ω) ^ 2) μ := by
      have h : Integrable (M K * M K) μ := (hM2 K).integrable_mul (hM2 K)
      have heq : (M K * M K) = fun ω => (M K ω) ^ 2 := by
        funext ω; simp only [Pi.mul_apply]; ring
      rwa [heq] at h
    have hstep : ∫ ω, (M (K + 1) ω) ^ 2 ∂μ =
        ∫ ω, (M K ω) ^ 2 ∂μ + ∫ ω, (M (K + 1) ω - M K ω) ^ 2 ∂μ := by
      rw [← h1, integral_congr_ae hc, integral_add hInt2 integrable_condExp, h2]
    rw [Finset.sum_range_succ, ← ih, hstep]

/-- **Stopped martingale.** If `M` is a martingale and `τ : Ω' → ℕ` is a (bounded, i.e.
`ℕ`-valued) stopping time for `ℱ`, then the process stopped at `τ`, `k ↦ M (min k τ)`, is again a
martingale. Obtained from `MeasureTheory.Submartingale.stoppedProcess` applied to `M` and `-M`. -/
theorem stopped_martingale (hM : Martingale M ℱ μ) {τ : Ω' → ℕ}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ))) :
    Martingale (fun k ω => M (min k (τ ω)) ω) ℱ μ := by
  have hcoeUntopA : ∀ n : ℕ, ((n : WithTop ℕ)).untopA = n := fun n => rfl
  have heq : stoppedProcess M (fun ω => (τ ω : WithTop ℕ)) = fun k ω => M (min k (τ ω)) ω := by
    funext k ω
    change M (min (k : WithTop ℕ) ((τ ω : ℕ) : WithTop ℕ)).untopA ω = M (min k (τ ω)) ω
    have hmin : (min (k : WithTop ℕ) ((τ ω : ℕ) : WithTop ℕ))
        = ((min k (τ ω) : ℕ) : WithTop ℕ) := (WithTop.coe_min k (τ ω)).symm
    rw [hmin, hcoeUntopA]
  rw [← heq]
  have hSubUp : Submartingale (stoppedProcess M (fun ω => (τ ω : WithTop ℕ))) ℱ μ :=
    hM.submartingale.stoppedProcess hτ
  have hSubDown : Submartingale (stoppedProcess (-M) (fun ω => (τ ω : WithTop ℕ))) ℱ μ :=
    hM.neg.submartingale.stoppedProcess hτ
  have heqNeg : stoppedProcess (-M) (fun ω => (τ ω : WithTop ℕ))
      = -(stoppedProcess M (fun ω => (τ ω : WithTop ℕ))) :=
    stoppedProcess_comp Neg.neg
  rw [heqNeg] at hSubDown
  have hSuper : Supermartingale (stoppedProcess M (fun ω => (τ ω : WithTop ℕ))) ℱ μ := by
    have h := hSubDown.neg
    simpa using h
  exact martingale_iff.mpr ⟨hSuper, hSubUp⟩

end Martingale

end RBM.Gauss.Grid

#print axioms RBM.Gauss.Grid.azuma_two_sided
#print axioms RBM.Gauss.Grid.azuma_complex
#print axioms RBM.Gauss.Grid.doob_L2_max
#print axioms RBM.Gauss.Grid.martingale_sq_eq_sum
#print axioms RBM.Gauss.Grid.stopped_martingale
