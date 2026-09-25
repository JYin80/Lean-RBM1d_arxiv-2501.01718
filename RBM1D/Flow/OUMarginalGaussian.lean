/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DimsExample
import RBM1D.Flow.Universality
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Fixed-time Gaussian OU marginals

This module constructs the fixed-time marginal

`exp (-t / 2) X + sqrt (1 - exp (-t)) G`

on the explicit product of the existing Gaussian band-matrix space and an independent normalized
Hermitian GUE coordinate space.  It proves the finite-coordinate joint Gaussian law and the
covariance profile `(1 - ζ) S + ζ / M` stated in (7.25), where `ζ = 1 - exp (-t)` and
`M = L N * W N = (Gauss.band d).size N`.

This is a fixed-time marginal construction only.  The common-G interpolation is not the Brownian
OU path in (2.19), since it does not have independent increments.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Gauss

/-- The number of rows and columns at the paper's matrix size `M`.  This is definitionally
`(Gauss.band d).size N = L N * W N`; in particular it is positive even at parameter `N = 0`. -/
def ouMatrixSize (d : Dims) (N : ℕ) : ℕ := d.L N * d.W N

theorem ouMatrixSize_pos (d : Dims) (N : ℕ) : 0 < ouMatrixSize d N := by
  exact Nat.mul_pos (by have := d.three_le_L N; omega) (d.W_pos N)

theorem ouMatrixSize_eq_band_size (d : Dims) (N : ℕ) :
    ouMatrixSize d N = (Gauss.band d).size N := rfl

/-- Real-coordinate variance of a normalized Hermitian GUE matrix.  A diagonal entry is real with
variance `1/M`; each off-diagonal real or imaginary component has variance `1/(2M)`. -/
noncomputable def gueCoordVar (d : Dims) (N : ℕ) (c : Coord d) : ℝ≥0 :=
  if c.2.1 = c.2.2.1 then
    (1 : ℝ≥0) / (ouMatrixSize d N : ℝ≥0)
  else
    (1 : ℝ≥0) / (2 * (ouMatrixSize d N : ℝ≥0))

/-- An independent normalized GUE coordinate field at size `M=L N*W N`. -/
noncomputable def gueMeasure (d : Dims) (N : ℕ) : Measure (Ω d) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueCoordVar d N c)

instance gueMeasure_isProbabilityMeasure (d : Dims) (N : ℕ) :
    IsProbabilityMeasure (gueMeasure d N) := by
  unfold gueMeasure
  infer_instance

/-- The explicit common probability space is the product of the actual band Gaussian field `P d`
and an independent normalized GUE coordinate field. -/
noncomputable def ouProductMeasure (d : Dims) (N : ℕ) :
    Measure (Ω d × Ω d) := (P d).prod (gueMeasure d N)

instance ouProductMeasure_isProbabilityMeasure (d : Dims) (N : ℕ) :
    IsProbabilityMeasure (ouProductMeasure d N) := by
  unfold ouProductMeasure
  infer_instance

/-- The matrix `X` from the existing Gaussian band source on the first product coordinate. -/
noncomputable def ouBandMatrix (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ := Xmat d N ω.1

/-- The independent normalized Hermitian GUE matrix on the second product coordinate. -/
noncomputable def ouGueMatrix (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ := Xmat d N ω.2

/-- The OU time fraction used by (7.25). -/
noncomputable def ouZeta (t : ℝ) : ℝ := 1 - Real.exp (-t)

/-- The first fixed-time interpolation coefficient in (2.19). -/
noncomputable def ouBandCoeff (t : ℝ) : ℝ := Real.exp (-t / 2)

/-- The second fixed-time interpolation coefficient in (2.19). -/
noncomputable def ouGueCoeff (t : ℝ) : ℝ := Real.sqrt (ouZeta t)

/-- The product sample carrying the linearly interpolated independent real coordinates. -/
noncomputable def ouInterpolatedSample (d : Dims) (_N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) : Ω d :=
  fun c => ouBandCoeff t * ω.1 c + ouGueCoeff t * ω.2 c

/-- The matrix obtained from the interpolated real coordinates using the actual `Xentry` layout. -/
noncomputable def ouInterpolatedMatrix (d : Dims) (N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  Xmat d N (ouInterpolatedSample d N t ω)

/-- The fixed-time matrix interpolation `e^(-t/2) X + sqrt(1-e^(-t)) G`. -/
noncomputable def ouMatrix (d : Dims) (N : ℕ) (t : ℝ) (ω : Ω d × Ω d) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  (ouBandCoeff t : ℂ) • ouBandMatrix d N ω +
    (ouGueCoeff t : ℂ) • ouGueMatrix d N ω

/-- The real interpolation at a primitive independent coordinate. -/
noncomputable def ouCoordinate (d : Dims) (_N : ℕ) (t : ℝ) (ω : Ω d × Ω d)
    (c : Coord d) : ℝ :=
  ouBandCoeff t * ω.1 c + ouGueCoeff t * ω.2 c

/-- Variance of one interpolated real coordinate. -/
noncomputable def ouCoordinateVar (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) : ℝ≥0 :=
  ⟨(ouBandCoeff t) ^ 2, sq_nonneg _⟩ * gvar d c +
    ⟨(ouGueCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c

/-- The finite vector of primitive interpolated real coordinates indexed by `I`. -/
noncomputable def ouCoordinateVector (d : Dims) (N : ℕ) (t : ℝ)
    (I : Finset (Coord d)) (ω : Ω d × Ω d) : I → ℝ :=
  fun c => ouCoordinate d N t ω c.1

private theorem bandCoordinates_iIndep (d : Dims) :
    iIndepFun (fun c : Coord d => fun ω : Ω d => ω c) (P d) := by
  simpa only [P] using
    (iIndepFun_infinitePi
      (P := fun c : Coord d => gaussianReal 0 (gvar d c))
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id))

private theorem gueCoordinates_iIndep (d : Dims) (N : ℕ) :
    iIndepFun (fun c : Coord d => fun ω : Ω d => ω c) (gueMeasure d N) := by
  simpa only [gueMeasure] using
    (iIndepFun_infinitePi
      (P := fun c : Coord d => gaussianReal 0 (gueCoordVar d N c))
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id))

private theorem bandCoord_hasGaussianLaw (d : Dims) (c : Coord d) :
    HasGaussianLaw (fun ω : Ω d => ω c) (P d) := by
  refine ⟨(measurable_pi_apply c).aemeasurable, ?_⟩
  rw [P_map_eval]
  infer_instance

theorem gueCoord_hasGaussianLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasGaussianLaw (fun ω : Ω d => ω c) (gueMeasure d N) := by
  refine ⟨(measurable_pi_apply c).aemeasurable, ?_⟩
  unfold gueMeasure
  rw [Measure.infinitePi_map_eval]
  infer_instance

private theorem bandCoordinateVector_gaussian (d : Dims) (I : Finset (Coord d)) :
    HasGaussianLaw (fun ω : Ω d => fun c : I => ω c.1) (P d) := by
  have hind : iIndepFun (fun c : I => fun ω : Ω d => ω c.1) (P d) :=
    (bandCoordinates_iIndep d).precomp
      (g := fun c : I => (c : Coord d)) (by intro a b h; exact Subtype.ext h)
  exact hind.hasGaussianLaw (fun c => bandCoord_hasGaussianLaw d c.1)

theorem gueCoordinateVector_jointGaussian (d : Dims) (N : ℕ)
    (I : Finset (Coord d)) :
    HasGaussianLaw (fun ω : Ω d => fun c : I => ω c.1) (gueMeasure d N) := by
  have hind : iIndepFun (fun c : I => fun ω : Ω d => ω c.1) (gueMeasure d N) :=
    (gueCoordinates_iIndep d N).precomp
      (g := fun c : I => (c : Coord d)) (by intro a b h; exact Subtype.ext h)
  exact hind.hasGaussianLaw (fun c => gueCoord_hasGaussianLaw d N c.1)

private theorem bandCoord_hasLaw (d : Dims) (c : Coord d) :
    HasLaw (fun ω : Ω d => ω c) (gaussianReal 0 (gvar d c)) (P d) := by
  exact ⟨(measurable_pi_apply c).aemeasurable, P_map_eval d c⟩

private theorem gueCoord_hasLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasLaw (fun ω : Ω d => ω c) (gaussianReal 0 (gueCoordVar d N c)) (gueMeasure d N) := by
  refine ⟨(measurable_pi_apply c).aemeasurable, ?_⟩
  unfold gueMeasure
  exact Measure.infinitePi_map_eval _ c

private theorem bandCoord_joint_hasLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasLaw (fun ω : Ω d × Ω d => ω.1 c) (gaussianReal 0 (gvar d c))
      (ouProductMeasure d N) := by
  exact (bandCoord_hasLaw d c).fun_comp
    (measurePreserving_fst (μ := P d) (ν := gueMeasure d N)).hasLaw

private theorem gueCoord_joint_hasLaw (d : Dims) (N : ℕ) (c : Coord d) :
    HasLaw (fun ω : Ω d × Ω d => ω.2 c) (gaussianReal 0 (gueCoordVar d N c))
      (ouProductMeasure d N) := by
  exact (gueCoord_hasLaw d N c).fun_comp
    (measurePreserving_snd (μ := P d) (ν := gueMeasure d N)).hasLaw

/-- The fixed-time law of each real interpolation coordinate is the centered Gaussian whose
variance is the corresponding convex combination of the band and GUE coordinate variances. -/
theorem ouCoordinate_hasLaw (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) :
    HasLaw (fun ω : Ω d × Ω d => ouCoordinate d N t ω c)
      (gaussianReal 0 (ouCoordinateVar d N t c)) (ouProductMeasure d N) := by
  have hParts : (fun ω : Ω d × Ω d => ω.1 c) ⟂ᵢ[ouProductMeasure d N]
      (fun ω => ω.2 c) :=
    indepFun_prod (measurable_pi_apply c) (measurable_pi_apply c)
  have hScaled : (fun ω : Ω d × Ω d => ouBandCoeff t * ω.1 c) ⟂ᵢ[ouProductMeasure d N]
      (fun ω => ouGueCoeff t * ω.2 c) :=
    hParts.comp (by fun_prop) (by fun_prop)
  have hX := gaussianReal_const_mul (bandCoord_joint_hasLaw d N c) (ouBandCoeff t)
  have hG := gaussianReal_const_mul (gueCoord_joint_hasLaw d N c) (ouGueCoeff t)
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hScaled hX hG
  have hmeas : Measurable (fun ω : Ω d × Ω d => ouCoordinate d N t ω c) := by
    dsimp [ouCoordinate]
    fun_prop
  refine ⟨hmeas.aemeasurable, ?_⟩
  have hvar :
      (⟨(ouBandCoeff t) ^ 2, sq_nonneg _⟩ * gvar d c +
        ⟨(ouGueCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c) =
        ouCoordinateVar d N t c := by
    apply Subtype.ext
    simp [ouCoordinateVar, NNReal.coe_add]
  have hdist : gaussianReal
      (ouBandCoeff t * 0 + ouGueCoeff t * 0)
      (⟨(ouBandCoeff t) ^ 2, sq_nonneg _⟩ * gvar d c +
        ⟨(ouGueCoeff t) ^ 2, sq_nonneg _⟩ * gueCoordVar d N c) =
      gaussianReal 0 (ouCoordinateVar d N t c) := by
    rw [show ouBandCoeff t * 0 + ouGueCoeff t * 0 = 0 by ring, hvar]
  calc
    (ouProductMeasure d N).map (fun ω => ouCoordinate d N t ω c) =
        (ouProductMeasure d N).map
          ((fun ω => ouBandCoeff t * ω.1 c) + fun ω => ouGueCoeff t * ω.2 c) := by
      congr 1
    _ = gaussianReal 0 (ouCoordinateVar d N t c) :=
      hsum.trans hdist

private theorem ouCoordinate_integrable_sq (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) :
    Integrable (fun ω : Ω d × Ω d => (ouCoordinate d N t ω c) ^ 2)
      (ouProductMeasure d N) := by
  have hLaw := ouCoordinate_hasLaw d N t c
  have hg : Integrable (fun x : ℝ => x ^ 2)
      ((ouProductMeasure d N).map (fun ω => ouCoordinate d N t ω c)) := by
    rw [hLaw.map_eq]
    exact (memLp_id_gaussianReal (μ := 0) (v := ouCoordinateVar d N t c) 2).integrable_sq
  exact (integrable_map_measure hg.aestronglyMeasurable hLaw.aemeasurable).1 hg

/-- The second moment of one real interpolation coordinate equals its Gaussian variance. -/
theorem ouCoordinate_integral_sq (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) :
    ∫ ω, (ouCoordinate d N t ω c) ^ 2 ∂(ouProductMeasure d N) =
      (ouCoordinateVar d N t c : ℝ) := by
  have hLaw := ouCoordinate_hasLaw d N t c
  have hf : AEMeasurable (fun ω : Ω d × Ω d => ouCoordinate d N t ω c)
      (ouProductMeasure d N) := hLaw.aemeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
      ((ouProductMeasure d N).map (fun ω => ouCoordinate d N t ω c)) := by
    fun_prop
  rw [← integral_map hf hg, hLaw.map_eq]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := ouCoordinateVar d N t c)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa using hv

/-- Every finite vector of the actual interpolated real coordinates is jointly Gaussian.  This
records the full Gaussian law, not only the coordinate second moments. -/
theorem ouCoordinateVector_jointGaussian (d : Dims) (N : ℕ) (t : ℝ)
    (I : Finset (Coord d)) :
    HasGaussianLaw (fun ω : Ω d × Ω d => ouCoordinateVector d N t I ω)
      (ouProductMeasure d N) := by
  let Xv : Ω d → I → ℝ := fun ω c => ω c.1
  let Gv : Ω d → I → ℝ := fun ω c => ω c.1
  have hX : HasGaussianLaw Xv (P d) := by
    simpa [Xv] using bandCoordinateVector_gaussian d I
  have hG : HasGaussianLaw Gv (gueMeasure d N) := by
    simpa [Gv] using gueCoordinateVector_jointGaussian d N I
  have hX' : HasGaussianLaw (fun ω : Ω d × Ω d => Xv ω.1) (ouProductMeasure d N) := by
    refine ⟨by fun_prop, ?_⟩
    change IsGaussian (Measure.map (Xv ∘ Prod.fst) ((P d).prod (gueMeasure d N)))
    rw [← Measure.map_map (show Measurable Xv from by fun_prop) measurable_fst,
      (measurePreserving_fst (μ := P d) (ν := gueMeasure d N)).map_eq]
    exact hX.isGaussian_map
  have hG' : HasGaussianLaw (fun ω : Ω d × Ω d => Gv ω.2) (ouProductMeasure d N) := by
    refine ⟨by fun_prop, ?_⟩
    change IsGaussian (Measure.map (Gv ∘ Prod.snd) ((P d).prod (gueMeasure d N)))
    rw [← Measure.map_map (show Measurable Gv from by fun_prop) measurable_snd,
      (measurePreserving_snd (μ := P d) (ν := gueMeasure d N)).map_eq]
    exact hG.isGaussian_map
  have hIndep : (fun ω : Ω d × Ω d => Xv ω.1) ⟂ᵢ[ouProductMeasure d N]
      (fun ω => Gv ω.2) := by
    exact indepFun_prod (by fun_prop) (by fun_prop)
  let T : ((I → ℝ) × (I → ℝ)) →L[ℝ] (I → ℝ) :=
    (ouBandCoeff t) • ContinuousLinearMap.fst ℝ (I → ℝ) (I → ℝ) +
      (ouGueCoeff t) • ContinuousLinearMap.snd ℝ (I → ℝ) (I → ℝ)
  have hPair : HasGaussianLaw (fun ω => (Xv ω.1, Gv ω.2)) (ouProductMeasure d N) :=
    hIndep.hasGaussianLaw hX' hG'
  have hOut := hPair.map_fun T
  convert hOut using 1
  ext c
  simp [T, ouCoordinateVector, ouCoordinate, Xv, Gv]

theorem ouInterpolatedSample_eq_band_at_zero (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    ouInterpolatedSample d N 0 ω = ω.1 := by
  funext c
  simp [ouInterpolatedSample, ouBandCoeff, ouGueCoeff, ouZeta]

theorem ouMatrix_eq_interpolatedMatrix (d : Dims) (N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) :
    ouMatrix d N t ω = ouInterpolatedMatrix d N t ω := by
  ext i j
  simp only [ouMatrix, ouBandMatrix, ouGueMatrix, ouInterpolatedMatrix,
    Matrix.add_apply, Matrix.smul_apply, Xmat_apply, smul_eq_mul]
  unfold Xentry
  split_ifs <;> simp only [ouInterpolatedSample, Complex.ofReal_add, Complex.ofReal_mul] <;>
    ring

theorem ouMatrix_isHermitian (d : Dims) (N : ℕ) (t : ℝ) (ω : Ω d × Ω d) :
    (ouMatrix d N t ω).IsHermitian := by
  rw [ouMatrix_eq_interpolatedMatrix]
  exact Xmat_isHermitian d N (ouInterpolatedSample d N t ω)

theorem ouMatrix_start (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    ouMatrix d N 0 ω = ouBandMatrix d N ω := by
  rw [ouMatrix_eq_interpolatedMatrix, ouInterpolatedMatrix,
    ouInterpolatedSample_eq_band_at_zero]
  rfl

/-- The actual band and normalized GUE matrices are independent on the explicit product space. -/
theorem ouBandMatrix_indep_ouGueMatrix (d : Dims) (N : ℕ) :
    (fun ω => ouBandMatrix d N ω) ⟂ᵢ[ouProductMeasure d N]
      (fun ω => ouGueMatrix d N ω) := by
  apply indepFun_prod
  · apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_Xentry d N i j
  · apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_Xentry d N i j

theorem ouGueMatrix_isHermitian (d : Dims) (N : ℕ) (ω : Ω d × Ω d) :
    (ouGueMatrix d N ω).IsHermitian :=
  Xmat_isHermitian d N ω.2

theorem gueCoordVar_diag (d : Dims) (N : ℕ) (i : d.Idx N) (b : Bool) :
    (gueCoordVar d N ⟨N, i, i, b⟩ : ℝ) = 1 / (ouMatrixSize d N : ℝ) := by
  simp [gueCoordVar, ouMatrixSize]

theorem gueCoordVar_offDiag (d : Dims) (N : ℕ) (i j : d.Idx N) (b : Bool)
    (hij : i ≠ j) :
    (gueCoordVar d N ⟨N, i, j, b⟩ : ℝ) = 1 / (2 * (ouMatrixSize d N : ℝ)) := by
  simp [gueCoordVar, ouMatrixSize, hij]

/-- The squared first coefficient is `1-ζ`, with `ζ=1-exp(-t)`. -/
theorem ouBandCoeff_sq (t : ℝ) : (ouBandCoeff t) ^ 2 = 1 - ouZeta t := by
  rw [ouBandCoeff, ouZeta]
  calc
    Real.exp (-t / 2) ^ 2 = Real.exp ((-t / 2) + (-t / 2)) := by
      rw [pow_two, ← Real.exp_add]
    _ = Real.exp (-t) := by congr 1; ring
    _ = 1 - (1 - Real.exp (-t)) := by ring

/-- The squared GUE coefficient is exactly `ζ`; nonnegativity of the time is what makes the
square-root interpolation real. -/
theorem ouGueCoeff_sq (t : ℝ) (ht : 0 ≤ t) :
    (ouGueCoeff t) ^ 2 = ouZeta t := by
  have he : Real.exp (-t) ≤ 1 :=
    (Real.exp_le_one_iff).2 (by linarith)
  unfold ouGueCoeff
  exact Real.sq_sqrt (sub_nonneg.mpr he)

private theorem ouCoordinateVar_coe (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) :
    (ouCoordinateVar d N t c : ℝ) =
      (ouBandCoeff t) ^ 2 * (gvar d c : ℝ) +
        (ouGueCoeff t) ^ 2 * (gueCoordVar d N c : ℝ) := by
  dsimp [ouCoordinateVar]
  norm_cast

private theorem ouCoordinateVar_diag (d : Dims) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (i : d.Idx N) :
    (ouCoordinateVar d N t ⟨N, i, i, true⟩ : ℝ) =
      (1 - ouZeta t) * Sblk (d.L N) (d.W N) i i +
        ouZeta t / (ouMatrixSize d N : ℝ) := by
  rw [ouCoordinateVar_coe, gvar_diag, ouBandCoeff_sq, ouGueCoeff_sq t ht]
  have hg : (gueCoordVar d N ⟨N, i, i, true⟩ : ℝ) =
      1 / (ouMatrixSize d N : ℝ) := by
    simp [gueCoordVar, ouMatrixSize]
  rw [hg]
  ring

private theorem ouCoordinateVar_offDiag (d : Dims) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (i j : d.Idx N) (b : Bool) (hij : i ≠ j) :
    (ouCoordinateVar d N t ⟨N, i, j, b⟩ : ℝ) =
      (1 - ouZeta t) * (Sblk (d.L N) (d.W N) i j / 2) +
        ouZeta t / (2 * (ouMatrixSize d N : ℝ)) := by
  rw [ouCoordinateVar_coe, gvar_offDiag d N i j b hij,
    ouBandCoeff_sq, ouGueCoeff_sq t ht]
  have hg : (gueCoordVar d N ⟨N, i, j, b⟩ : ℝ) =
      1 / (2 * (ouMatrixSize d N : ℝ)) := by
    simp [gueCoordVar, ouMatrixSize, hij]
  rw [hg]
  ring

theorem ouMatrix_entry_eq_interpolatedSample (d : Dims) (N : ℕ) (t : ℝ)
    (ω : Ω d × Ω d) (i j : d.Idx N) :
    ouMatrix d N t ω i j = Xentry d N (ouInterpolatedSample d N t ω) i j := by
  rw [ouMatrix_eq_interpolatedMatrix, ouInterpolatedMatrix, Xmat_apply]

/-- At every fixed nonnegative time, the matrix entry covariance is the variance profile stated
in (7.25):
`E |H_{t,ij}|² = (1-ζ) S_ij + ζ/M`, with `ζ=1-exp(-t)`. -/
theorem ouMatrix_entry_covariance (d : Dims) (N : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (i j : d.Idx N) :
    ∫ ω, ‖ouMatrix d N t ω i j‖ ^ 2 ∂(ouProductMeasure d N) =
      (1 - ouZeta t) * Sblk (d.L N) (d.W N) i j +
        ouZeta t / (ouMatrixSize d N : ℝ) := by
  rcases idxKey_lt_or_eq_or_lt d N i j with hij | heq | hji
  · have hne : i ≠ j := fun h => by subst h; exact (lt_irrefl _ hij)
    have hpoint : ∀ ω : Ω d × Ω d,
        ‖ouMatrix d N t ω i j‖ ^ 2 =
          (ouCoordinate d N t ω ⟨N, i, j, true⟩) ^ 2 +
            (ouCoordinate d N t ω ⟨N, i, j, false⟩) ^ 2 := by
      intro ω
      rw [ouMatrix_entry_eq_interpolatedSample, Xentry, ite_eq_left hij,
        ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      simp [ouInterpolatedSample, ouCoordinate]
      ring
    calc
      ∫ ω, ‖ouMatrix d N t ω i j‖ ^ 2 ∂(ouProductMeasure d N) =
          ∫ ω, (ouCoordinate d N t ω ⟨N, i, j, true⟩) ^ 2 +
            (ouCoordinate d N t ω ⟨N, i, j, false⟩) ^ 2 ∂(ouProductMeasure d N) := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hpoint ω
      _ = (∫ ω, (ouCoordinate d N t ω ⟨N, i, j, true⟩) ^ 2 ∂(ouProductMeasure d N)) +
          (∫ ω, (ouCoordinate d N t ω ⟨N, i, j, false⟩) ^ 2 ∂(ouProductMeasure d N)) :=
        integral_add (ouCoordinate_integrable_sq d N t ⟨N, i, j, true⟩)
          (ouCoordinate_integrable_sq d N t ⟨N, i, j, false⟩)
      _ = (1 - ouZeta t) * Sblk (d.L N) (d.W N) i j +
          ouZeta t / (ouMatrixSize d N : ℝ) := by
        rw [ouCoordinate_integral_sq, ouCoordinate_integral_sq,
          ouCoordinateVar_offDiag d N t ht i j true hne,
          ouCoordinateVar_offDiag d N t ht i j false hne]
        ring
  · subst heq
    have hpoint : ∀ ω : Ω d × Ω d,
        ‖ouMatrix d N t ω i i‖ ^ 2 =
          (ouCoordinate d N t ω ⟨N, i, i, true⟩) ^ 2 := by
      intro ω
      rw [ouMatrix_entry_eq_interpolatedSample, Xentry,
        ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _),
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp [ouInterpolatedSample, ouCoordinate]
    calc
      ∫ ω, ‖ouMatrix d N t ω i i‖ ^ 2 ∂(ouProductMeasure d N) =
          ∫ ω, (ouCoordinate d N t ω ⟨N, i, i, true⟩) ^ 2 ∂(ouProductMeasure d N) := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hpoint ω
      _ = (1 - ouZeta t) * Sblk (d.L N) (d.W N) i i +
          ouZeta t / (ouMatrixSize d N : ℝ) := by
        rw [ouCoordinate_integral_sq, ouCoordinateVar_diag d N t ht i]
  · have hne : j ≠ i := fun h => by subst h; exact (lt_irrefl _ hji)
    have hpoint : ∀ ω : Ω d × Ω d,
        ‖ouMatrix d N t ω i j‖ ^ 2 =
          (ouCoordinate d N t ω ⟨N, j, i, true⟩) ^ 2 +
            (ouCoordinate d N t ω ⟨N, j, i, false⟩) ^ 2 := by
      intro ω
      rw [ouMatrix_entry_eq_interpolatedSample, Xentry, ite_eq_right (asymm hji),
        ite_eq_left hji,
        ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
      simp [ouInterpolatedSample, ouCoordinate]
      ring
    calc
      ∫ ω, ‖ouMatrix d N t ω i j‖ ^ 2 ∂(ouProductMeasure d N) =
          ∫ ω, (ouCoordinate d N t ω ⟨N, j, i, true⟩) ^ 2 +
            (ouCoordinate d N t ω ⟨N, j, i, false⟩) ^ 2 ∂(ouProductMeasure d N) := by
        apply integral_congr_ae
        filter_upwards with ω
        exact hpoint ω
      _ = (∫ ω, (ouCoordinate d N t ω ⟨N, j, i, true⟩) ^ 2 ∂(ouProductMeasure d N)) +
          (∫ ω, (ouCoordinate d N t ω ⟨N, j, i, false⟩) ^ 2 ∂(ouProductMeasure d N)) :=
        integral_add (ouCoordinate_integrable_sq d N t ⟨N, j, i, true⟩)
          (ouCoordinate_integrable_sq d N t ⟨N, j, i, false⟩)
      _ = (1 - ouZeta t) * Sblk (d.L N) (d.W N) i j +
          ouZeta t / (ouMatrixSize d N : ℝ) := by
        rw [ouCoordinate_integral_sq, ouCoordinate_integral_sq,
          ouCoordinateVar_offDiag d N t ht j i true hne,
          ouCoordinateVar_offDiag d N t ht j i false hne,
          Sblk_comm (d.L N) (d.W N) j i]
        ring

/-- Named fixed-time marginal statement: every finite set of primitive real/imaginary matrix
coordinates of the actual interpolation has a joint Gaussian law. -/
theorem fixedTimeMarginal_jointGaussian (d : Dims) (N : ℕ) (t : ℝ) (_ht : 0 ≤ t)
    (I : Finset (Coord d)) :
    HasGaussianLaw (fun ω : Ω d × Ω d => ouCoordinateVector d N t I ω)
      (ouProductMeasure d N) :=
  ouCoordinateVector_jointGaussian d N t I

/-- A single explicit sample in the shared product space has both `X` and `G` nonzero, including
when the size parameter is zero. -/
theorem ouBandGue_nonzero_witness (d : Dims) (N : ℕ) :
    ∃ (i : d.Idx N) (ω : Ω d × Ω d),
      ouBandMatrix d N ω i i ≠ 0 ∧ ouGueMatrix d N ω i i ≠ 0 := by
  let i : d.Idx N := (0, ⟨0, by have hw := d.W_pos N; omega⟩)
  let c : Coord d := ⟨N, i, i, true⟩
  let s : Ω d := fun c' => if c' = c then 1 else 0
  have hx : ouBandMatrix d N (s, s) i i = 1 := by
    simp [ouBandMatrix, Xmat_apply, Xentry, s, c, i]
  have hg : ouGueMatrix d N (s, s) i i = 1 := by
    simp [ouGueMatrix, Xmat_apply, Xentry, s, c, i]
  exact ⟨i, (s, s), by rw [hx]; norm_num, by rw [hg]; norm_num⟩

/-- The requested nondegenerate sample for the project growth model. -/
theorem exampleGrow_ouBandGue_nonzero_witness (N : ℕ) :
    ∃ (i : Dims.exampleGrow.Idx N)
      (ω : Ω Dims.exampleGrow × Ω Dims.exampleGrow),
      ouBandMatrix Dims.exampleGrow N ω i i ≠ 0 ∧
        ouGueMatrix Dims.exampleGrow N ω i i ≠ 0 :=
  ouBandGue_nonzero_witness Dims.exampleGrow N

end RBM.Gauss
