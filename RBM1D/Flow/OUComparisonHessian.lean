/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.StieltjesEtaMonotone
import RBM1D.Gauss.Generator

/-!
# Pointwise Hessian structure for the centered-variance Green comparison

This file records the deterministic, finite-dimensional second-variation calculation
underlying the `L₁` and `L₂` expressions in (2.25).  It makes no assertion about an OU path,
expectations, or a time integral.
-/

namespace RBM

open Matrix
open scoped ComplexConjugate
open scoped Matrix.Norms.L2Operator

section ResolventVariation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The ordinary second derivative of a finite product separates into the single-factor Hessians
and the ordered cross-factor products. This is the deterministic product expansion needed before
contracting against the centered variance matrix. -/
theorem hasDerivAt_deriv_finset_product_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f fp : ι → ℝ → ℝ) (fpp : ι → ℝ)
    (hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t)
    (hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t)
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, f j 0) * fpp i +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)) 0 := by
  have hfirst (t : ℝ) :
      HasDerivAt (fun u : ℝ => ∏ i ∈ s, f i u)
        (∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t) t := by
    have h := HasDerivAt.fun_finsetProd (u := s) (f := fun i u => f i u)
      (f' := fun i => fp i t) (fun i hi => hf i hi t)
    simpa [smul_eq_mul] using h
  have hderiv :
      (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t) =
        fun t => ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t := by
    funext t
    exact (hfirst t).deriv
  let p : ι → ℝ := fun i => ∏ j ∈ s.erase i, f j 0
  let dp : ι → ℝ := fun i =>
    ∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0
  have hprod (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun t : ℝ => ∏ j ∈ s.erase i, f j t) (dp i) 0 := by
    have h := HasDerivAt.fun_finsetProd (u := s.erase i) (f := fun j t => f j t)
      (f' := fun j => fp j 0) (fun j hj => hf j (Finset.mem_of_mem_erase hj) 0)
    simpa [dp, smul_eq_mul] using h
  have hterm (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun t : ℝ => (∏ j ∈ s.erase i, f j t) * fp i t)
        (dp i * fp i 0 + p i * fpp i) 0 := by
    have h := (hprod i hi).mul (hfp i hi)
    refine h.congr_deriv ?_
    simp [p, dp, add_comm, mul_comm, mul_left_comm, mul_assoc]
  have hsum₀ : HasDerivAt
      (fun t : ℝ => ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t)
      (∑ i ∈ s, (dp i * fp i 0 + p i * fpp i)) 0 := by
    have h := HasDerivAt.sum (u := s)
      (A := fun i t => (∏ j ∈ s.erase i, f j t) * fp i t)
      (A' := fun i => dp i * fp i 0 + p i * fpp i)
      (fun i hi => hterm i hi)
    have heq : (fun t : ℝ => ∑ i ∈ s,
        (∏ j ∈ s.erase i, f j t) * fp i t) =
        ∑ i ∈ s, fun t : ℝ => (∏ j ∈ s.erase i, f j t) * fp i t := by
      funext t
      simp
    rw [heq]
    exact h
  rw [hderiv]
  refine hsum₀.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro i hi
  simp [p, dp, add_comm, mul_comm, mul_left_comm, mul_assoc]

private theorem fderiv_fderiv_eq_lineSecond {H A : Matrix n n ℂ}
    {f : Matrix n n ℂ → ℂ} (hf : ContDiffAt ℝ 2 f H)
    (hline : ∀ t : ℝ, DifferentiableAt ℝ f (H + (t : ℂ) • A)) :
    fderiv ℝ (fderiv ℝ f) H A A =
      deriv (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hf.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline0 := Gauss.hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline0
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    exact (hline t).hasFDerivAt.comp_hasDerivAt t (Gauss.hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]

private theorem deriv_deriv_ofRealCLM {g dg : ℝ → ℝ} {d2g : ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (dg t) t)
    (hdg : HasDerivAt dg d2g 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => (g s : ℂ)) t) 0 = (d2g : ℂ) := by
  have hfirst (t : ℝ) : HasDerivAt (fun s : ℝ => (g s : ℂ)) (dg t : ℂ) t := by
    have h := HasFDerivAt.comp_hasDerivAt t Complex.ofRealCLM.hasFDerivAt (hg t)
    simpa [Function.comp_def] using h
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => (g s : ℂ)) t) =
      fun t => (dg t : ℂ) := by
    funext t
    exact (hfirst t).deriv
  have hsecond := HasFDerivAt.comp_hasDerivAt 0 Complex.ofRealCLM.hasFDerivAt hdg
  rw [hderiv]
  exact hsecond.deriv

private noncomputable def traceCLM : Matrix n n ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap

private def entryMatrix (i j : n) : Matrix n n ℂ := Matrix.single i j 1

private theorem matrix_mul_entryMatrix_apply (X : Matrix n n ℂ) (i j a b : n) :
    (X * entryMatrix i j) a b = if b = j then X a i else 0 := by
  by_cases hb : b = j
  · subst b
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [entryMatrix]
    · intro x hx hxi
      simp [entryMatrix, hxi.symm]
    · simp
  · simp [entryMatrix, Matrix.mul_apply, Matrix.single_apply, hb, Ne.symm hb]

private theorem matrix_mul_entryMatrix_mul_apply (X Y : Matrix n n ℂ) (i j a b : n) :
    (X * entryMatrix i j * Y) a b = X a i * Y j b := by
  rw [Matrix.mul_apply]
  simp_rw [matrix_mul_entryMatrix_apply]
  simp

private theorem trace_green_entryCross (G : Matrix n n ℂ) (i j : n) :
    (G * entryMatrix i j * G * entryMatrix j i * G).trace =
      (G * G) i i * G j j := by
  calc
    (G * entryMatrix i j * G * entryMatrix j i * G).trace =
        ((G * entryMatrix i j * G) * (entryMatrix j i * G)).trace := by simp [mul_assoc]
    _ = ((entryMatrix j i * G) * (G * entryMatrix i j * G)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (entryMatrix j i * (G * G * entryMatrix i j * G)).trace := by simp [mul_assoc]
    _ = (G * G * entryMatrix i j * G) i j := by
      simpa [entryMatrix] using
        (Matrix.trace_single_mul j i (1 : ℂ) (G * G * entryMatrix i j * G))
    _ = (G * G) i i * G j j := matrix_mul_entryMatrix_mul_apply (G * G) G i j i j

private theorem trace_green_singleEntry (G : Matrix n n ℂ) (a b : n) :
    (G * entryMatrix a b * G).trace = (G * G) b a := by
  calc
    (G * entryMatrix a b * G).trace = (G * (entryMatrix a b * G)).trace := by
      congr 1
      simp [Matrix.mul_assoc]
    _ = ((entryMatrix a b * G) * G).trace := Matrix.trace_mul_comm _ _
    _ = (entryMatrix a b * (G * G)).trace := by congr 1 <;> simp [Matrix.mul_assoc]
    _ = (G * G) b a := by
      simpa [entryMatrix] using Matrix.trace_single_mul a b (1 : ℂ) (G * G)

private theorem trace_green_entryPair (G : Matrix n n ℂ) (i j : n) :
    (G * (entryMatrix i j + entryMatrix j i) * G).trace =
      (G * G) j i + (G * G) i j := by
  calc
    (G * (entryMatrix i j + entryMatrix j i) * G).trace =
        (G * entryMatrix i j * G + G * entryMatrix j i * G).trace := by
      congr 1 <;> simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = (G * entryMatrix i j * G).trace + (G * entryMatrix j i * G).trace :=
      Matrix.trace_add _ _
    _ = (G * G) j i + (G * G) i j := by
      rw [trace_green_singleEntry G i j, trace_green_singleEntry G j i]

private theorem trace_green_entryImagPair (G : Matrix n n ℂ) (i j : n) :
    (G * (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) * G).trace =
      Complex.I * ((G * G) j i - (G * G) i j) := by
  have hmul : G * (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) * G =
      Complex.I • (G * entryMatrix i j * G) - Complex.I • (G * entryMatrix j i * G) := by
    calc
      G * (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) * G =
          (Complex.I • (G * entryMatrix i j) - Complex.I • (G * entryMatrix j i)) * G := by
        simp [Matrix.mul_sub, Matrix.mul_smul]
      _ = Complex.I • (G * entryMatrix i j * G) -
          Complex.I • (G * entryMatrix j i * G) := by
        rw [Matrix.sub_mul, smul_mul_assoc, smul_mul_assoc]
  rw [hmul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    trace_green_singleEntry, trace_green_singleEntry]
  simp only [smul_eq_mul]
  ring

private theorem Bmat_real_eq_entryMatrices {d : Gauss.Dims} {N : ℕ}
    {i j : d.Idx N} (hij : i ≠ j) :
    Gauss.Bmat d N i j true = entryMatrix i j + entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, h1, h2, h1', h2', and_comm]

private theorem Bmat_imag_eq_entryMatrices {d : Gauss.Dims} {N : ℕ}
    {i j : d.Idx N} (hij : i ≠ j) :
    Gauss.Bmat d N i j false = Complex.I • entryMatrix i j - Complex.I • entryMatrix j i := by
  ext k l
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩
    simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, hij]
  · by_cases h2 : k = j ∧ l = i
    · rcases h2 with ⟨rfl, rfl⟩
      simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, hij]
    · have h1' : ¬ (i = k ∧ j = l) := by
        rintro ⟨hik, hjl⟩
        exact h1 ⟨hik.symm, hjl.symm⟩
      have h2' : ¬ (i = l ∧ j = k) := by
        rintro ⟨hil, hjk⟩
        exact h2 ⟨hjk.symm, hil.symm⟩
      simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, h1, h2, h1', h2', and_comm]

private theorem trace_green_Bmat_pair_sum {G : Matrix n n ℂ} {i j : n} (hij : i ≠ j) :
    (G * (entryMatrix i j + entryMatrix j i) * G * (entryMatrix i j + entryMatrix j i) * G).trace +
      (G * (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) * G *
        (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) * G).trace =
      2 * ((G * G) i i * G j j + (G * G) j j * G i i) := by
  simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp_rw [trace_green_entryCross]
  simp only [smul_eq_mul, Complex.I_mul_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem Bmat_hermitian_of_ne {d : Gauss.Dims} {N : ℕ} {i j : d.Idx N}
    (hij : i ≠ j) (b : Bool) : (Gauss.Bmat d N i j b).IsHermitian := by
  rcases Gauss.idxKey_lt_or_eq_or_lt d N i j with hlt | heq | hgt
  · exact Gauss.Bmat_isHermitian (p := (i, j, b)) (Gauss.mem_usedCoord.2 (Or.inl hlt))
  · exact (hij heq).elim
  · have hmem : (j, i, b) ∈ Gauss.usedCoord d N :=
      Gauss.mem_usedCoord.2 (Or.inl hgt)
    have hji := Gauss.Bmat_isHermitian (p := (j, i, b)) hmem
    cases b
    · have hswap := Gauss.Bmat_swap_false d N hij
      have hneg : -Gauss.Bmat d N j i false = Gauss.Bmat d N i j false := by
        rw [hswap]
        simp
      rw [← hneg]
      exact hji.neg
    · rw [← Gauss.Bmat_swap_true d N i j]
      exact hji

private theorem Bmat_diag_true_eq_entryMatrix {d : Gauss.Dims} {N : ℕ} (i : d.Idx N) :
    Gauss.Bmat d N i i true = entryMatrix i i := by
  ext k l
  by_cases h : k = i ∧ l = i
  · rcases h with ⟨rfl, rfl⟩
    simp [Gauss.Bmat, entryMatrix, Matrix.single_apply]
  · have h' : ¬ (i = k ∧ i = l) := by
      rintro ⟨hik, hil⟩
      exact h ⟨hik.symm, hil.symm⟩
    simp [Gauss.Bmat, entryMatrix, Matrix.single_apply, h, h']

private theorem analyticAt_green_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => green K z) H := by
  let q : Matrix n n ℂ → Matrix n n ℂ := fun K => K - z • (1 : Matrix n n ℂ)
  have hq : AnalyticAt ℝ q H := by
    exact analyticAt_id.sub analyticAt_const
  have hU : IsUnit (q H) := isUnit_sub_smul_one_of_im_ne_zero hH hz
  let u : (Matrix n n ℂ)ˣ := hU.unit
  have hu : (u : Matrix n n ℂ) = q H := IsUnit.unit_spec _
  have hinv : AnalyticAt ℝ Ring.inverse (q H) := by
    rw [← hu]
    exact analyticAt_inverse u
  have hc := hinv.comp hq
  convert hc using 1
  funext K
  simp [q, green, Matrix.nonsing_inv_eq_ringInverse]

private theorem hasFDerivAt_green_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun K : Matrix n n ℂ => green K z)
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (green H z) (green H z)) H := by
  let q : Matrix n n ℂ → Matrix n n ℂ := fun K => K - z • (1 : Matrix n n ℂ)
  have hq : HasFDerivAt q (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) H := by
    simpa [q] using (hasFDerivAt_id H).sub_const (z • (1 : Matrix n n ℂ))
  have hU : IsUnit (q H) := isUnit_sub_smul_one_of_im_ne_zero hH hz
  let u : (Matrix n n ℂ)ˣ := hU.unit
  have hu : (u : Matrix n n ℂ) = q H := IsUnit.unit_spec _
  have hinv := (hasFDerivAt_ringInverse u).comp H hq
  have hinvval : (↑u⁻¹ : Matrix n n ℂ) = green H z := by
    calc
      (↑u⁻¹ : Matrix n n ℂ) = Ring.inverse (↑u : Matrix n n ℂ) :=
        (Ring.inverse_unit u).symm
      _ = Ring.inverse (q H) := by rw [hu]
      _ = green H z := by simp [q, green, Matrix.nonsing_inv_eq_ringInverse]
  convert hinv using 1
  · funext K
    simp [q, Function.comp_def, green, Matrix.nonsing_inv_eq_ringInverse]
  · rw [← hinvval]
    simp

private theorem analyticAt_stieltjes_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) : AnalyticAt ℝ (fun K : Matrix n n ℂ => stieltjes K z) H := by
  have hg := analyticAt_green_matrix hH z hz
  have ht : AnalyticAt ℝ (fun K : Matrix n n ℂ => traceCLM (n := n) (green K z)) H := by
    have ht0 : AnalyticAt ℝ (fun A : Matrix n n ℂ => traceCLM (n := n) A) (green H z) :=
      (traceCLM (n := n)).analyticAt (green H z)
    have hcomp : AnalyticAt ℝ
        ((fun A : Matrix n n ℂ => traceCLM (n := n) A) ∘
          (fun K : Matrix n n ℂ => green K z)) H :=
      AnalyticAt.comp (g := fun A : Matrix n n ℂ => traceCLM (n := n) A)
        (f := fun K : Matrix n n ℂ => green K z) (x := H) ht0 hg
    simpa [Function.comp_def] using hcomp
  have hc : AnalyticAt ℝ (fun K : Matrix n n ℂ =>
      (Fintype.card n : ℂ)⁻¹ * traceCLM (n := n) (green K z)) H := by
    exact (analyticAt_const (x := H)).mul ht
  convert hc using 1
  funext K
  rfl

private theorem hasFDerivAt_stieltjes_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    HasFDerivAt (fun K : Matrix n n ℂ => stieltjes K z)
      (((Fintype.card n : ℂ)⁻¹) •
        (traceCLM (n := n) ∘L
          (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (green H z) (green H z)))) H := by
  have hgreen := hasFDerivAt_green_matrix hH z hz
  have htrace := (traceCLM (n := n)).hasFDerivAt.comp H hgreen
  have hst := htrace.const_mul ((Fintype.card n : ℂ)⁻¹)
  have hEq : (fun K : Matrix n n ℂ => stieltjes K z)
      = fun K => (Fintype.card n : ℂ)⁻¹ * traceCLM (n := n) (green K z) := by
    rfl
  rw [hEq]
  simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using hst

private theorem fderiv_stieltjes_apply_matrix {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fun K : Matrix n n ℂ => stieltjes K z) H A =
      -((Fintype.card n : ℂ)⁻¹) * (green H z * A * green H z).trace := by
  have h := (hasFDerivAt_stieltjes_matrix hH z hz).fderiv
  have hA := congrArg (fun L : Matrix n n ℂ →L[ℝ] ℂ => L A) h
  simpa [traceCLM, Matrix.traceLinearMap_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply, mul_assoc] using hA

private theorem fderiv_stieltjesIm_apply_matrix {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fun K : Matrix n n ℂ => (stieltjes K z).im) H A =
      (-((Fintype.card n : ℂ)⁻¹) *
        (green H z * A * green H z).trace).im := by
  have h := (Complex.imCLM.hasFDerivAt.comp H
    (hasFDerivAt_stieltjes_matrix hH z hz)).fderiv
  have hA := congrArg (fun L : Matrix n n ℂ →L[ℝ] ℝ => L A) h
  calc
    fderiv ℝ (fun K : Matrix n n ℂ => (stieltjes K z).im) H A =
        (fderiv ℝ (⇑Complex.imCLM ∘ fun K : Matrix n n ℂ => stieltjes K z) H) A := rfl
    _ = (Complex.imCLM ∘SL
        ((Fintype.card n : ℂ)⁻¹ •
          traceCLM (n := n) ∘L
            (-ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (green H z) (green H z)))) A := hA
    _ = (-((Fintype.card n : ℂ)⁻¹) *
        (green H z * A * green H z).trace).im := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
        traceCLM, Matrix.traceLinearMap_apply, Complex.mul_im, mul_assoc]

private theorem analyticAt_stieltjesIm_matrix {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => (stieltjes K z).im) H := by
  have hm := analyticAt_stieltjes_matrix hH z hz
  have hi0 : AnalyticAt ℝ (fun w : ℂ => Complex.imCLM w) (stieltjes H z) :=
    Complex.imCLM.analyticAt (stieltjes H z)
  have hi : AnalyticAt ℝ
      ((fun w : ℂ => Complex.imCLM w) ∘ (fun K : Matrix n n ℂ => stieltjes K z)) H :=
    AnalyticAt.comp (g := fun w : ℂ => Complex.imCLM w)
      (f := fun K : Matrix n n ℂ => stieltjes K z) (x := H) hi0 hm
  simpa [Function.comp_def] using hi

private theorem analyticAt_stieltjesImComplex_matrix {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ => ((stieltjes K z).im : ℂ)) H := by
  have hm := analyticAt_stieltjesIm_matrix hH z hz
  have ho : AnalyticAt ℝ (fun x : ℝ => Complex.ofRealCLM x)
      ((stieltjes H z).im) := Complex.ofRealCLM.analyticAt _
  have hc : AnalyticAt ℝ
      ((fun x : ℝ => Complex.ofRealCLM x) ∘
        (fun K : Matrix n n ℂ => (stieltjes K z).im)) H :=
    AnalyticAt.comp (g := fun x : ℝ => Complex.ofRealCLM x)
      (f := fun K : Matrix n n ℂ => (stieltjes K z).im) (x := H) ho hm
  simpa [Function.comp_def] using hc

private theorem analyticAt_stieltjesImProduct_complex {ι : Type*} [DecidableEq ι]
    (s : Finset ι) {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    AnalyticAt ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)) H := by
  have hR : AnalyticAt ℝ
      (fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjes K (z i)).im) H := by
    exact s.analyticAt_fun_prod
      (fun i hi => analyticAt_stieltjesIm_matrix hH (z i) (hz i hi))
  have hcast : AnalyticAt ℝ (fun x : ℝ => (x : ℂ))
      (∏ i ∈ s, (stieltjes H (z i)).im) := Complex.ofRealCLM.analyticAt _
  have hcomp : AnalyticAt ℝ
      ((fun x : ℝ => (x : ℂ)) ∘
        (fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjes K (z i)).im)) H :=
    AnalyticAt.comp (g := fun x : ℝ => (x : ℂ))
      (f := fun K : Matrix n n ℂ => ∏ i ∈ s, (stieltjes K (z i)).im)
      (x := H) hcast hR
  simpa [Function.comp_def] using hcomp

private theorem fderiv_fderiv_stieltjesImComplex_eq_lineSecond {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => ((stieltjes K z).im : ℂ))) H A A =
      deriv (fun t : ℝ => deriv
        (fun s : ℝ => ((stieltjes (H + (s : ℂ) • A) z).im : ℂ)) t) 0 := by
  let f : Matrix n n ℂ → ℂ := fun K => ((stieltjes K z).im : ℂ)
  have hc : ContDiffAt ℝ 2 f H :=
    (analyticAt_stieltjesImComplex_matrix hH z hz).contDiffAt
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hc.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline := Gauss.hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    have hHt := Gauss.isHermitian_add_realSmul hH hA t
    exact (analyticAt_stieltjesImComplex_matrix hHt z hz).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt t (Gauss.hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  change fderiv ℝ (fderiv ℝ f) H A A = _
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv
        (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]

private theorem fderiv_fderiv_stieltjesIm_eq_lineSecond {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => (stieltjes K z).im)) H A A =
      deriv (fun t : ℝ => deriv
        (fun s : ℝ => (stieltjes (H + (s : ℂ) • A) z).im) t) 0 := by
  let f : Matrix n n ℂ → ℝ := fun K => (stieltjes K z).im
  have hc : ContDiffAt ℝ 2 f H := (analyticAt_stieltjesIm_matrix hH z hz).contDiffAt
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) H := hc.fderiv_right (by norm_num)
  have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) H) H :=
    (hfd.differentiableAt (by norm_num)).hasFDerivAt
  have happly := hfd'.clm_apply (hasFDerivAt_const (𝕜 := ℝ) A H)
  have hline := Gauss.hasDerivAt_line H A 0
  have happly0 : HasFDerivAt (fun K => fderiv ℝ f K A)
      ((fderiv ℝ (fderiv ℝ f) H).flip A) (H + (0 : ℝ) • A) := by
    simpa using happly
  have hcomp := HasFDerivAt.comp_hasDerivAt 0 happly0 hline
  have hcomp' : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A)
      (fderiv ℝ (fderiv ℝ f) H A A) 0 := by
    simpa [Function.comp_def, ContinuousLinearMap.flip_apply] using hcomp
  have hfirst (t : ℝ) : HasDerivAt
      (fun s : ℝ => f (H + (s : ℂ) • A))
      (fderiv ℝ f (H + (t : ℂ) • A) A) t := by
    have hHt := Gauss.isHermitian_add_realSmul hH hA t
    exact (analyticAt_stieltjesIm_matrix hHt z hz).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt t (Gauss.hasDerivAt_line H A t)
  have hderiv : (fun t : ℝ => deriv (fun s : ℝ => f (H + (s : ℂ) • A)) t) =
      fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A := by
    funext t
    exact (hfirst t).deriv
  change fderiv ℝ (fderiv ℝ f) H A A = _
  calc
    fderiv ℝ (fderiv ℝ f) H A A =
        deriv (fun t : ℝ => fderiv ℝ f (H + (t : ℂ) • A) A) 0 := hcomp'.deriv.symm
    _ = deriv (fun t : ℝ => deriv
        (fun s : ℝ => f (H + (s : ℂ) • A)) t) 0 := by rw [← hderiv]


/-- The resolvent along a Hermitian real line has the usual first variation. -/
theorem hasDerivAt_green_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => green (H + (s : ℂ) • A) z)
      (-(green (H + (t : ℂ) • A) z * A * green (H + (t : ℂ) • A) z)) t := by
  have hU : ∀ s : ℝ, IsUnit (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    intro s
    have hsum : H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A
        = (H + (s : ℂ) • A) - z • (1 : Matrix n n ℂ) := by abel
    rw [hsum]
    exact isUnit_sub_smul_one_of_im_ne_zero (Gauss.isHermitian_add_realSmul hH hA s) hz
  have hEq : (fun s : ℝ => green (H + (s : ℂ) • A) z)
      = fun s : ℝ => Ring.inverse (H - z • (1 : Matrix n n ℂ) + (s : ℂ) • A) := by
    funext s
    change (H + (s : ℂ) • A - z • (1 : Matrix n n ℂ))⁻¹ = _
    rw [Matrix.nonsing_inv_eq_ringInverse]
    congr 1
    abel
  have hEq_t := congrFun hEq t
  have hline := Gauss.hasDerivAt_lineInverse hU t
  rw [← hEq_t] at hline
  rw [hEq]
  exact hline

/-- The first derivative of the paper-normalized Stieltjes transform along a Hermitian line. -/
theorem hasDerivAt_stieltjes_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => stieltjes (H + (s : ℂ) • A) z)
      (-((Fintype.card n : ℂ)⁻¹) *
        (green (H + (t : ℂ) • A) z * A * green (H + (t : ℂ) • A) z).trace) t := by
  have hG := hasDerivAt_green_hermitianLine hH hA z hz t
  have htrace := HasFDerivAt.comp_hasDerivAt t
    (traceCLM (n := n)).hasFDerivAt hG
  have hmul := (htrace.const_mul ((Fintype.card n : ℂ)⁻¹))
  have hst : (fun s : ℝ => stieltjes (H + (s : ℂ) • A) z)
      = fun s : ℝ => (Fintype.card n : ℂ)⁻¹ * traceCLM (n := n) (green (H + (s : ℂ) • A) z) := by
    rfl
  rw [hst]
  simpa [traceCLM, Matrix.traceLinearMap_apply] using hmul

/-- Along a Hermitian line, the derivative of the first Stieltjes variation is the usual
resolvent second variation. -/
theorem hasDerivAt_stieltjesFirstVariation {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => -((Fintype.card n : ℂ)⁻¹) *
        (green (H + (s : ℂ) • A) z * A * green (H + (s : ℂ) • A) z).trace)
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (green (H + (t : ℂ) • A) z * A * green (H + (t : ℂ) • A) z * A *
          green (H + (t : ℂ) • A) z).trace) t := by
  have hG := hasDerivAt_green_hermitianLine hH hA z hz t
  set R := green (H + (t : ℂ) • A) z
  have hRA := hG.mul_const A
  have hRARA := hRA.mul hG
  have hfun : ((fun s : ℝ => green (H + (s : ℂ) • A) z * A) *
      (fun s : ℝ => green (H + (s : ℂ) • A) z)) =
      (fun s : ℝ => green (H + (s : ℂ) • A) z *
        (A * green (H + (s : ℂ) • A) z)) := by
    funext s
    simp [Pi.mul_apply, Matrix.mul_assoc]
  have hprod : HasDerivAt
      (fun s : ℝ => green (H + (s : ℂ) • A) z *
        (A * green (H + (s : ℂ) • A) z))
      ((-(R * A * R) * A) * R + (R * A) * (-(R * A * R))) t := by
    rw [← hfun]
    simpa [R, Matrix.mul_assoc] using hRARA
  have htr := HasFDerivAt.comp_hasDerivAt t
    (traceCLM (n := n)).hasFDerivAt hprod
  have hconst := htr.const_mul (-((Fintype.card n : ℂ)⁻¹))
  convert hconst using 1 <;>
    simp [traceCLM, Matrix.traceLinearMap_apply, Matrix.mul_assoc] <;> ring

/-- The real Stieltjes factor along a Hermitian matrix line. -/
noncomputable def stieltjesImAlong (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (stieltjes (H + (t : ℂ) • A) z).im

/-- Its first derivative, written as the imaginary part of the resolvent first variation. -/
noncomputable def stieltjesImLineFirst (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (-((Fintype.card n : ℂ)⁻¹) *
    (green (H + (t : ℂ) • A) z * A * green (H + (t : ℂ) • A) z).trace).im

/-- Its second derivative at the base point, written as the resolvent second variation. -/
noncomputable def stieltjesImLineSecond (H A : Matrix n n ℂ) (z : ℂ) : ℝ :=
  (2 * (Fintype.card n : ℂ)⁻¹ *
    (green H z * A * green H z * A * green H z).trace).im

/-- The finite-product second line variation, including all single and ordered cross terms. -/
noncomputable def stieltjesImProductLineSecond {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (z : ι → ℂ) : ℝ :=
  ∑ i ∈ s,
    ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
        stieltjesImLineSecond H A (z i) +
      (∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
          stieltjesImLineFirst H A (z j) 0) *
        stieltjesImLineFirst H A (z i) 0)

/-- The product rule expansion of the second line derivative of finitely many real Stieltjes
factors. The first sum is the `L₁`-type single-factor contribution; the ordered cross sum is the
`L₂`-type contribution before the centered-variance contraction. -/
theorem deriv_deriv_stieltjesImProduct_hermitianLine {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    deriv (fun t : ℝ => deriv (fun u : ℝ =>
      ∏ i ∈ s, stieltjesImAlong H A (z i) u) t) 0 =
      ∑ i ∈ s,
        ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
            stieltjesImLineSecond H A (z i) +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
              stieltjesImLineFirst H A (z j) 0) *
            stieltjesImLineFirst H A (z i) 0) := by
  let f : ι → ℝ → ℝ := fun i t => stieltjesImAlong H A (z i) t
  let fp : ι → ℝ → ℝ := fun i t => stieltjesImLineFirst H A (z i) t
  let fpp : ι → ℝ := fun i => stieltjesImLineSecond H A (z i)
  have hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t := by
    intro i hi t
    have hst := hasDerivAt_stieltjes_hermitianLine hH hA (z i) (hz i hi) t
    have him := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hst
    simpa [f, fp, stieltjesImAlong, stieltjesImLineFirst, Function.comp_def] using him
  have hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0 := by
    intro i hi
    have hst := hasDerivAt_stieltjesFirstVariation hH hA (z i) (hz i hi) 0
    have him := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hst
    simpa [fp, fpp, stieltjesImLineFirst, stieltjesImLineSecond,
      Function.comp_def] using him
  have hexp := hasDerivAt_deriv_finset_product_expansion s f fp fpp hf hfp
  simpa [f, fp, fpp] using hexp.deriv

/-- The Fréchet Hessian of a finite product of real Stieltjes factors along any Hermitian
direction has the same single-factor and ordered cross-factor expansion. -/
theorem fderiv_fderiv_stieltjesImProduct_hermitianLine {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (hH : H.IsHermitian) (hA : A.IsHermitian)
    (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ =>
      ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ))) H A A =
      ((∑ i ∈ s,
        ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
            stieltjesImLineSecond H A (z i) +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
              stieltjesImLineFirst H A (z j) 0) *
            stieltjesImLineFirst H A (z i) 0) : ℝ) : ℂ) := by
  let F : Matrix n n ℂ → ℂ := fun K =>
    ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)
  let f : ι → ℝ → ℝ := fun i t => stieltjesImAlong H A (z i) t
  let fp : ι → ℝ → ℝ := fun i t => stieltjesImLineFirst H A (z i) t
  let fpp : ι → ℝ := fun i => stieltjesImLineSecond H A (z i)
  let g : ℝ → ℝ := fun t => ∏ i ∈ s, f i t
  let d2g : ℝ := ∑ i ∈ s,
    ((∏ j ∈ s.erase i, f j 0) * fpp i +
      (∑ j ∈ s.erase i, (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)
  have hC2 : ContDiffAt ℝ 2 F H :=
    (analyticAt_stieltjesImProduct_complex s hH z hz).contDiffAt
  have hline : ∀ t : ℝ, DifferentiableAt ℝ F (H + (t : ℂ) • A) := by
    intro t
    have htH := Gauss.isHermitian_add_realSmul hH hA t
    exact (analyticAt_stieltjesImProduct_complex s htH z hz).differentiableAt
  have hbridge := fderiv_fderiv_eq_lineSecond hC2 hline
  have hf : ∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t := by
    intro i hi t
    have hst := hasDerivAt_stieltjes_hermitianLine hH hA (z i) (hz i hi) t
    have him := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hst
    simpa [f, fp, stieltjesImAlong, stieltjesImLineFirst, Function.comp_def] using him
  have hfp : ∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0 := by
    intro i hi
    have hst := hasDerivAt_stieltjesFirstVariation hH hA (z i) (hz i hi) 0
    have him := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hst
    simpa [fp, fpp, stieltjesImLineFirst, stieltjesImLineSecond,
      Function.comp_def] using him
  have hfirst (t : ℝ) : HasDerivAt g
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t) t := by
    have h := HasDerivAt.fun_finsetProd (u := s) (f := fun i u => f i u)
      (f' := fun i => fp i t) (fun i hi => hf i hi t)
    simpa [g, smul_eq_mul] using h
  have hg : ∀ t : ℝ, HasDerivAt g (deriv g t) t := by
    intro t
    have heq : deriv g t =
        ∑ i ∈ s, (∏ j ∈ s.erase i, f j t) * fp i t := (hfirst t).deriv
    exact (hfirst t).congr_deriv heq.symm
  have hsecond := hasDerivAt_deriv_finset_product_expansion s f fp fpp hf hfp
  have hsecond' : HasDerivAt (fun t => deriv g t) d2g 0 := by
    simpa [g, d2g, f, fp, fpp] using hsecond
  have hcast := deriv_deriv_ofRealCLM hg hsecond'
  have hlineEq : (fun t : ℝ => F (H + (t : ℂ) • A)) = fun t => (g t : ℂ) := by
    funext t
    rfl
  rw [hlineEq] at hbridge
  rw [hbridge]
  simpa [d2g, f, fp, fpp] using hcast

/-- The Generator's Wirtinger Hessian of a finite product is the corresponding real-coordinate
combination of the single and cross resolvent variations. -/
theorem wirtSecond_stieltjesImProduct_expansion {d : Gauss.Dims} {N : ℕ}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (H : Matrix (d.Idx N) (d.Idx N) ℂ)
    (hH : H.IsHermitian) (z : ι → ℂ) (hz : ∀ i ∈ s, (z i).im ≠ 0)
    (a b : d.Idx N) :
    Gauss.wirtSecond d N
        (fun K => ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ)) H a b =
      if a = b then
        (stieltjesImProductLineSecond s H (Gauss.Bmat d N a a true) z : ℂ)
      else
        (1 / 4 : ℝ) •
          ((stieltjesImProductLineSecond s H (Gauss.Bmat d N a b true) z : ℂ) +
            (stieltjesImProductLineSecond s H (Gauss.Bmat d N a b false) z : ℂ)) := by
  by_cases hab : a = b
  · subst b
    simp only [Gauss.wirtSecond, if_pos rfl]
    have hA : (Gauss.Bmat d N a a true).IsHermitian :=
      Gauss.Bmat_isHermitian (p := (a, a, true))
        (Gauss.mem_usedCoord.2 (Or.inr ⟨rfl, rfl⟩))
    change fderiv ℝ (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ))) H
        (Gauss.Bmat d N a a true) (Gauss.Bmat d N a a true) = _
    rw [fderiv_fderiv_stieltjesImProduct_hermitianLine s H
      (Gauss.Bmat d N a a true) hH hA z hz]
    simp [stieltjesImProductLineSecond]
  · simp only [Gauss.wirtSecond, if_neg hab]
    have hT : (Gauss.Bmat d N a b true).IsHermitian := Bmat_hermitian_of_ne hab true
    have hF : (Gauss.Bmat d N a b false).IsHermitian := Bmat_hermitian_of_ne hab false
    change (1 / 4 : ℝ) •
      (fderiv ℝ (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ =>
        ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ))) H
          (Gauss.Bmat d N a b true) (Gauss.Bmat d N a b true) +
       fderiv ℝ (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ =>
        ((∏ i ∈ s, (stieltjes K (z i)).im : ℝ) : ℂ))) H
          (Gauss.Bmat d N a b false) (Gauss.Bmat d N a b false)) = _
    rw [fderiv_fderiv_stieltjesImProduct_hermitianLine s H
          (Gauss.Bmat d N a b true) hH hT z hz,
        fderiv_fderiv_stieltjesImProduct_hermitianLine s H
          (Gauss.Bmat d N a b false) hH hF z hz]
    simp [stieltjesImProductLineSecond]

/-- The pointwise second derivative of the real Stieltjes factor along a Hermitian line. -/
theorem deriv_deriv_stieltjes_im_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => (stieltjes (H + (s : ℂ) • A) z).im) t) 0
      = (2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im := by
  let f : ℝ → ℝ := fun s => (stieltjes (H + (s : ℂ) • A) z).im
  let d : ℝ → ℝ := fun s => Complex.imCLM
    (-((Fintype.card n : ℂ)⁻¹) *
      (green (H + (s : ℂ) • A) z * A * green (H + (s : ℂ) • A) z).trace)
  have hfirst (t : ℝ) : HasDerivAt f (d t) t := by
    have hs := hasDerivAt_stieltjes_hermitianLine hH hA z hz t
    have hi := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hs
    simpa [Function.comp_def, f, d] using hi
  have hderiv : (fun t : ℝ => deriv f t) = d := by
    funext t
    exact (hfirst t).deriv
  have hsecond := hasDerivAt_stieltjesFirstVariation hH hA z hz 0
  have hsecondIm := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hsecond
  have hd : d = fun s : ℝ => Complex.imCLM
      (-((Fintype.card n : ℂ)⁻¹) *
        (green (H + (s : ℂ) • A) z * A * green (H + (s : ℂ) • A) z).trace) := by
    funext s
    rfl
  change deriv (fun t : ℝ => deriv f t) 0 = _
  calc
    deriv (fun t : ℝ => deriv f t) 0 = deriv d 0 := by rw [hderiv]
    _ = (2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im := by
      rw [hd]
      convert hsecondIm.deriv using 1
      · rfl
      · rw [Complex.imCLM_apply]
        simp

/-- The Fréchet Hessian of the real Stieltjes factor is the explicit resolvent second variation.
This is the coordinate-free identity used below to specialize to the matrix-entry directions. -/
theorem fderiv_fderiv_stieltjes_im_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => (stieltjes K z).im)) H A A =
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im := by
  rw [fderiv_fderiv_stieltjesIm_eq_lineSecond hH hA z hz]
  exact deriv_deriv_stieltjes_im_hermitianLine hH hA z hz

/-- A concrete finite-Hermitian witness where the Stieltjes Hessian is nonzero. -/
theorem stieltjesIm_hessian_nondegenerate_example :
    fderiv ℝ (fderiv ℝ
      (fun K : Matrix (Fin 1) (Fin 1) ℂ => (stieltjes K Complex.I).im))
      (0 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)
        (1 : Matrix (Fin 1) (Fin 1) ℂ) ≠ 0 := by
  have hH : (0 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := Matrix.isHermitian_zero
  have hA : (1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := Matrix.isHermitian_one
  have h := fderiv_fderiv_stieltjes_im_hermitianLine hH hA Complex.I (by norm_num)
  rw [h]
  norm_num [green, Matrix.nonsing_inv_eq_ringInverse]

private theorem deriv_deriv_stieltjes_im_complex_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    deriv (fun t : ℝ => deriv
      (fun s : ℝ => ((stieltjes (H + (s : ℂ) • A) z).im : ℂ)) t) 0 =
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im : ℂ) := by
  let fR : ℝ → ℝ := fun s => (stieltjes (H + (s : ℂ) • A) z).im
  let fC : ℝ → ℂ := fun s => (fR s : ℂ)
  let dR : ℝ → ℝ := fun s => Complex.imCLM
    (-((Fintype.card n : ℂ)⁻¹) *
      (green (H + (s : ℂ) • A) z * A * green (H + (s : ℂ) • A) z).trace)
  have hfirstR (t : ℝ) : HasDerivAt fR (dR t) t := by
    have hs := hasDerivAt_stieltjes_hermitianLine hH hA z hz t
    have hi := HasFDerivAt.comp_hasDerivAt t Complex.imCLM.hasFDerivAt hs
    simpa [Function.comp_def, fR, dR] using hi
  have hfirstC (t : ℝ) : HasDerivAt fC ((dR t : ℂ)) t := by
    have hc := HasFDerivAt.comp_hasDerivAt t Complex.ofRealCLM.hasFDerivAt (hfirstR t)
    simpa [Function.comp_def, fC] using hc
  have hderiv : (fun t : ℝ => deriv fC t) = fun t => (dR t : ℂ) := by
    funext t
    exact (hfirstC t).deriv
  have hsecond := hasDerivAt_stieltjesFirstVariation hH hA z hz 0
  have hsecondR : HasDerivAt dR
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im 0 := by
    have hi := HasFDerivAt.comp_hasDerivAt 0 Complex.imCLM.hasFDerivAt hsecond
    simpa [Function.comp_def, dR] using hi
  have hsecondC : HasDerivAt (fun s : ℝ => (dR s : ℂ))
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im : ℂ) 0 := by
    have hc := HasFDerivAt.comp_hasDerivAt 0 Complex.ofRealCLM.hasFDerivAt hsecondR
    simpa [Function.comp_def] using hc
  change deriv (fun t : ℝ => deriv fC t) 0 = _
  calc
    deriv (fun t : ℝ => deriv fC t) 0 = deriv (fun t : ℝ => (dR t : ℂ)) 0 := by
      rw [hderiv]
    _ = _ := hsecondC.deriv

private theorem fderiv_fderiv_stieltjes_imComplex_hermitianLine {H A : Matrix n n ℂ}
    (hH : H.IsHermitian) (hA : A.IsHermitian) (z : ℂ) (hz : z.im ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ => ((stieltjes K z).im : ℂ))) H A A =
      ((2 * (Fintype.card n : ℂ)⁻¹ *
        (green H z * A * green H z * A * green H z).trace).im : ℂ) := by
  rw [fderiv_fderiv_stieltjesImComplex_eq_lineSecond hH hA z hz]
  exact deriv_deriv_stieltjes_im_complex_hermitianLine hH hA z hz

/-- The first Wirtinger derivative of a real-valued matrix observable, expressed through the
real-coordinate derivatives used by `Gauss.coordD1`. -/
noncomputable def stieltjesImWirtingerFirst {d : Gauss.Dims} {N : ℕ}
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ℂ) (i j : d.Idx N) : ℂ :=
  if i = j then
    (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ => (stieltjes K z).im) H
      (Gauss.Bmat d N i i true) : ℝ)
  else
    (2⁻¹ : ℂ) *
      ((fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ => (stieltjes K z).im) H
          (Gauss.Bmat d N i j true) : ℝ) -
        Complex.I * (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ => (stieltjes K z).im) H
          (Gauss.Bmat d N i j false) : ℝ))

/-- The first Wirtinger derivative of `Im m` is the difference of the two resolvent-square
entries.  The conjugated entry is the corresponding entry of `G*²` for Hermitian `H`. -/
theorem stieltjesImWirtingerFirst_entry_formula {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : d.Idx N) :
    stieltjesImWirtingerFirst H z i j =
      (Complex.I * (Fintype.card (d.Idx N) : ℂ)⁻¹ / 2) *
        ((green H z * green H z) j i - conj ((green H z * green H z) i j)) := by
  by_cases hij : i = j
  · subst j
    rw [stieltjesImWirtingerFirst, if_pos rfl, Bmat_diag_true_eq_entryMatrix]
    rw [fderiv_stieltjesIm_apply_matrix hH z hz]
    rw [trace_green_singleEntry]
    let c : ℂ := (Fintype.card (d.Idx N) : ℂ)⁻¹
    have hc : c.im = 0 := by simp [c]
    change ((-c * (green H z * green H z) i i).im : ℂ) =
      (Complex.I * c / 2) * ((green H z * green H z) i i -
        conj ((green H z * green H z) i i))
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, hc] <;> ring

  · rw [stieltjesImWirtingerFirst, if_neg hij,
      Bmat_real_eq_entryMatrices hij, Bmat_imag_eq_entryMatrices hij]
    rw [fderiv_stieltjesIm_apply_matrix hH z hz,
      fderiv_stieltjesIm_apply_matrix hH z hz,
      trace_green_entryPair, trace_green_entryImagPair]
    let c : ℂ := (Fintype.card (d.Idx N) : ℂ)⁻¹
    have hc : c.im = 0 := by simp [c]
    change (2⁻¹ : ℂ) *
      (((-c * ((green H z * green H z) j i + (green H z * green H z) i j)).im : ℂ) -
        Complex.I * ((-c * (Complex.I * ((green H z * green H z) j i -
          (green H z * green H z) i j))).im : ℂ)) =
      (Complex.I * c / 2) * ((green H z * green H z) j i -
        conj ((green H z * green H z) i j))
    apply Complex.ext <;> simp [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, hc] <;> ring

private theorem green_square_conj_entry {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian) (z : ℂ)
    (i j : d.Idx N) :
    conj ((green H z * green H z) i j) =
      (green H ((starRingEnd ℂ) z) * green H ((starRingEnd ℂ) z)) j i := by
  have hG : green H ((starRingEnd ℂ) z) = (green H z)ᴴ := by
    simpa [Gsig] using (Gsig_conjTranspose hH z true).symm
  calc
    conj ((green H z * green H z) i j) = ((green H z * green H z)ᴴ) j i := by
      simp [Matrix.conjTranspose_apply, Complex.star_def]
    _ = ((green H z)ᴴ * (green H z)ᴴ) j i := by rw [Matrix.conjTranspose_mul]
    _ = (green H ((starRingEnd ℂ) z) * green H ((starRingEnd ℂ) z)) j i := by rw [← hG]

/-- The centered covariance entry `S°_{ab}=S_{ab}-M^{-1}`, with the matrix dimension
`M = card (d.Idx N)` kept distinct from the sequence parameter `N`. -/
noncomputable def centeredVarianceEntry (d : Gauss.Dims) (N : ℕ)
    (a b : d.Idx N) : ℝ :=
  Sblk (d.L N) (d.W N) a b - (Fintype.card (d.Idx N) : ℝ)⁻¹

theorem centeredVarianceEntry_symm (d : Gauss.Dims) (N : ℕ) (a b : d.Idx N) :
    centeredVarianceEntry d N a b = centeredVarianceEntry d N b a := by
  simp [centeredVarianceEntry, Gauss.Sblk_comm]

/-- The signed resolvent family `{G,G*}` at a Hermitian matrix. -/
noncomputable def signedGreen (H : Matrix (n) (n) ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  if σ then green H z else green H ((starRingEnd ℂ) z)

/-- The deterministic pointwise `L₁` kernel in (2.25), for the model's centered covariance. -/
noncomputable def paperL1Kernel (d : Gauss.Dims) (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (d.Idx N) : ℂ)⁻¹ *
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        ((signedGreen H z σ * signedGreen H z σ) a a) *
          (centeredVarianceEntry d N a b : ℂ) * (signedGreen H z τ) b b‖

/-- The deterministic pointwise `L₂` kernel in (2.25), for two spectral parameters. -/
noncomputable def paperL2Kernel (d : Gauss.Dims) (N : ℕ)
    (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z₁ z₂ : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (d.Idx N) : ℂ)⁻¹ *
      (Fintype.card (d.Idx N) : ℂ)⁻¹ *
      ∑ a : d.Idx N, ∑ b : d.Idx N,
        ((signedGreen H z₁ σ * signedGreen H z₁ σ) a b) *
          (centeredVarianceEntry d N a b : ℂ) *
          ((signedGreen H z₂ τ * signedGreen H z₂ τ) b a)‖

/-- The first derivative formula in the notation of (2.25), with the conjugate entry written as
the corresponding entry of the adjoint resolvent square. -/
theorem stieltjesImWirtingerFirst_adjoint_formula {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : d.Idx N) :
    stieltjesImWirtingerFirst H z i j =
      (Complex.I * (Fintype.card (d.Idx N) : ℂ)⁻¹ / 2) *
        ((green H z * green H z) j i -
          (green H ((starRingEnd ℂ) z) * green H ((starRingEnd ℂ) z)) j i) := by
  rw [stieltjesImWirtingerFirst_entry_formula hH z hz i j,
    green_square_conj_entry hH z i j]

/-- The Generator's Wirtinger Hessian of one real Stieltjes factor has the exact diagonal-entry
formula that underlies the paper's `L₁` contraction. -/
theorem wirtSecond_stieltjesIm_entry_formula {d : Gauss.Dims} {N : ℕ}
    {H : Matrix (d.Idx N) (d.Idx N) ℂ} (hH : H.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) (i j : d.Idx N) :
    Gauss.wirtSecond d N (fun K => (stieltjes K z).im) H i j =
      (((Fintype.card (d.Idx N) : ℂ)⁻¹) *
        ((green H z * green H z) i i * (green H z) j j +
          (green H z * green H z) j j * (green H z) i i)).im := by
  by_cases hij : i = j
  · subst j
    have hdiag : (Gauss.Bmat d N i i true).IsHermitian :=
      Gauss.Bmat_isHermitian (p := (i, i, true))
        (Gauss.mem_usedCoord.2 (Or.inr ⟨rfl, rfl⟩))
    rw [Gauss.wirtSecond, if_pos rfl]
    change fderiv ℝ (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ((stieltjes K z).im : ℂ))) H (Gauss.Bmat d N i i true) (Gauss.Bmat d N i i true) = _
    rw [fderiv_fderiv_stieltjes_imComplex_hermitianLine hH hdiag z hz]
    rw [Bmat_diag_true_eq_entryMatrix, trace_green_entryCross]
    simp [Complex.mul_im, mul_assoc]
    ring
  · rw [Gauss.wirtSecond, if_neg hij]
    change (1 / 4 : ℝ) •
      (fderiv ℝ (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ =>
        ((stieltjes K z).im : ℂ))) H (Gauss.Bmat d N i j true) (Gauss.Bmat d N i j true) +
       fderiv ℝ (fderiv ℝ (fun K : Matrix (d.Idx N) (d.Idx N) ℂ =>
        ((stieltjes K z).im : ℂ))) H (Gauss.Bmat d N i j false) (Gauss.Bmat d N i j false)) = _
    rw [fderiv_fderiv_stieltjes_imComplex_hermitianLine hH
          (Bmat_hermitian_of_ne hij true) z hz,
        fderiv_fderiv_stieltjes_imComplex_hermitianLine hH
          (Bmat_hermitian_of_ne hij false) z hz,
        Bmat_real_eq_entryMatrices hij, Bmat_imag_eq_entryMatrices hij]
    let c : ℂ := (Fintype.card (d.Idx N) : ℂ)⁻¹
    let T₁ := (green H z * (entryMatrix i j + entryMatrix j i) * green H z *
      (entryMatrix i j + entryMatrix j i) * green H z).trace
    let T₂ := (green H z * (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) *
      green H z * (Complex.I • entryMatrix i j - Complex.I • entryMatrix j i) *
      green H z).trace
    have hcIm : c.im = 0 := by simp [c]
    have hIm : (2 * c * T₁).im + (2 * c * T₂).im = (2 * c * (T₁ + T₂)).im := by
      simp [Complex.mul_im, hcIm]
      ring
    have hImC : ((2 * c * T₁).im : ℂ) + ((2 * c * T₂).im : ℂ) =
        ((2 * c * (T₁ + T₂)).im : ℂ) := by
      exact_mod_cast hIm
    change (1 / 4 : ℝ) •
      (((2 * c * T₁).im : ℂ) + ((2 * c * T₂).im : ℂ)) = _
    rw [hImC]
    have hT : T₁ + T₂ = 2 * ((green H z * green H z) i i * (green H z) j j +
        (green H z * green H z) j j * (green H z) i i) := by
      dsimp [T₁, T₂]
      exact trace_green_Bmat_pair_sum hij
    rw [hT]
    simp [Complex.mul_im, hcIm, c]
    ring

end ResolventVariation

end RBM
