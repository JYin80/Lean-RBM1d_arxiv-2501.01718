/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUCommonCarrier
import RBM1D.Gauss.OpNorm
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Jensen

/-!
# Fixed-time OU spectral second-moment bound

For deterministic nonnegative time and spectral parameter in the fixed bounded region, the
normalized second spectral moment of the actual common-carrier OU matrix has every fixed moment
uniformly bounded.  The proof uses the accepted Gaussian coordinate laws and the (7.25) row
normalization, at one deterministic time only.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate

namespace RBM.Gauss

noncomputable section

/-- The actual normalized spectral second moment of the common-carrier fixed-time OU matrix. -/
noncomputable def ouFixedTimeR2 (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ω : ouCommonOmega d) : ℝ :=
  let H := ouMatrix d N t (ouCommonProjection d N ω)
  let hH := ouMatrix_isHermitian d N t (ouCommonProjection d N ω)
  (ouMatrixSize d N : ℝ)⁻¹ *
    ∑ i : d.Idx N, ‖((hH.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2

/-- The nonnegative square root of the actual normalized spectral second moment. -/
noncomputable def ouFixedTimeR (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ω : ouCommonOmega d) : ℝ := Real.sqrt (ouFixedTimeR2 d N t z ω)

/-- A positive envelope for one fixed-time entry variance, with total mass two per row. -/
noncomputable def ouVarianceEnvelope (d : Dims) (N : ℕ)
    (i j : d.Idx N) : ℝ :=
  Sblk (d.L N) (d.W N) i j + (ouMatrixSize d N : ℝ)⁻¹

/-- A scalar real coordinate of the fixed-time matrix, pulled to the common carrier. -/
noncomputable def ouCommonCoord (d : Dims) (N : ℕ) (t : ℝ)
    (ω : ouCommonOmega d) (c : Coord d) : ℝ :=
  ouCoordinate d N t (ouCommonProjection d N ω) c

/-- All real coordinates read by the Hermitian matrix at a fixed size and time. -/
noncomputable def ouFixedTimeCoordSqSum (d : Dims) (N : ℕ) (t : ℝ)
    (ω : ouCommonOmega d) : ℝ :=
  ∑ c : d.Idx N × d.Idx N × Bool,
    (ouCommonCoord d N t ω ⟨N, c⟩) ^ 2

private noncomputable def ouFixedTimeCoordWeight (d : Dims) (N : ℕ)
    (c : d.Idx N × d.Idx N × Bool) : ℝ :=
  ouVarianceEnvelope d N c.1 c.2.1

private noncomputable def ouFixedTimeWeightedPowerSum (d : Dims) (N : ℕ) (t : ℝ)
    (p : ℕ) (ω : ouCommonOmega d) : ℝ :=
  ∑ c : d.Idx N × d.Idx N × Bool,
    (ouCommonCoord d N t ω ⟨N, c⟩ ^ 2) ^ p /
      (ouFixedTimeCoordWeight d N c) ^ (p - 1)

private theorem abs_even_pow (x : ℝ) (p : ℕ) : |x| ^ (2 * p) = x ^ (2 * p) := by
  have hx : 0 ≤ x ^ (2 * p) := by
    calc
      x ^ (2 * p) = x ^ (p * 2) := by congr 1 <;> omega
      _ = (x ^ p) ^ 2 := by rw [pow_mul]
      _ ≥ 0 := sq_nonneg _
  rw [← abs_pow, abs_of_nonneg hx]

private theorem ouCommonCoord_hasLaw (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) :
    HasLaw (ouCommonCoord d N t · c) (gaussianReal 0 (ouCoordinateVar d N t c))
      (ouCommonMeasure d) := by
  exact (ouCoordinate_hasLaw d N t c).fun_comp
    (ouCommonProjection_measurePreserving d N).hasLaw

private theorem ouCommonCoord_integrable_abs_pow (d : Dims) (N : ℕ) (t : ℝ)
    (c : Coord d) (p : ℕ) :
    Integrable (fun ω => |ouCommonCoord d N t ω c| ^ (2 * p)) (ouCommonMeasure d) := by
  have hLaw := ouCommonCoord_hasLaw d N t c
  have hgauss : Integrable (fun x : ℝ => |x| ^ (2 * p))
      (gaussianReal 0 (ouCoordinateVar d N t c)) := by
    have h := RBM.integrable_pow_gaussianReal (ouCoordinateVar d N t c) (2 * p)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact (abs_even_pow x p).symm
  simpa [Function.comp_def] using hLaw.integrable_comp hgauss

private theorem ouCommonCoord_integral_abs_pow (d : Dims) (N : ℕ) (t : ℝ)
    (c : Coord d) (p : ℕ) :
    ∫ ω, |ouCommonCoord d N t ω c| ^ (2 * p) ∂(ouCommonMeasure d) =
      RBM.dfac p * (ouCoordinateVar d N t c : ℝ) ^ p := by
  have hLaw := ouCommonCoord_hasLaw d N t c
  have hgauss : AEStronglyMeasurable (fun x : ℝ => |x| ^ (2 * p))
      (gaussianReal 0 (ouCoordinateVar d N t c)) := by fun_prop
  calc
    ∫ ω, |ouCommonCoord d N t ω c| ^ (2 * p) ∂(ouCommonMeasure d) =
        ∫ x, |x| ^ (2 * p) ∂gaussianReal 0 (ouCoordinateVar d N t c) := by
      simpa [Function.comp_def] using hLaw.integral_comp hgauss
    _ = ∫ x, x ^ (2 * p) ∂gaussianReal 0 (ouCoordinateVar d N t c) := by
      apply integral_congr_ae
      filter_upwards with x
      exact abs_even_pow x p
    _ = RBM.dfac p * (ouCoordinateVar d N t c : ℝ) ^ p :=
      RBM.integral_pow_gaussianReal (ouCoordinateVar d N t c) p

private theorem ouCommonCoord_square_pow_integrable (d : Dims) (N : ℕ) (t : ℝ)
    (c : Coord d) (p : ℕ) :
    Integrable (fun ω => (ouCommonCoord d N t ω c ^ 2) ^ p) (ouCommonMeasure d) := by
  have h := ouCommonCoord_integrable_abs_pow d N t c p
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  calc
    |ouCommonCoord d N t ω c| ^ (2 * p) = ouCommonCoord d N t ω c ^ (2 * p) :=
      abs_even_pow _ p
    _ = (ouCommonCoord d N t ω c ^ 2) ^ p := by rw [pow_mul]

private theorem ouCommonCoord_square_pow_integral (d : Dims) (N : ℕ) (t : ℝ)
    (c : Coord d) (p : ℕ) :
    ∫ ω, (ouCommonCoord d N t ω c ^ 2) ^ p ∂(ouCommonMeasure d) =
      RBM.dfac p * (ouCoordinateVar d N t c : ℝ) ^ p := by
  calc
    ∫ ω, (ouCommonCoord d N t ω c ^ 2) ^ p ∂(ouCommonMeasure d) =
        ∫ ω, |ouCommonCoord d N t ω c| ^ (2 * p) ∂(ouCommonMeasure d) := by
          apply integral_congr_ae
          filter_upwards with ω
          calc
            (ouCommonCoord d N t ω c ^ 2) ^ p =
                ouCommonCoord d N t ω c ^ (2 * p) := by rw [pow_mul]
            _ = |ouCommonCoord d N t ω c| ^ (2 * p) := (abs_even_pow _ p).symm
    _ = RBM.dfac p * (ouCoordinateVar d N t c : ℝ) ^ p :=
      ouCommonCoord_integral_abs_pow d N t c p

private theorem dfac_nonneg (p : ℕ) : 0 ≤ RBM.dfac p := by
  unfold RBM.dfac
  exact Finset.prod_nonneg fun i hi => by positivity

private theorem sum_bool_pow_le (x : Bool → ℝ) (p : ℕ) (hp : 0 < p)
    (hx : ∀ b, 0 ≤ x b) :
    (∑ b : Bool, x b) ^ p ≤ 2 ^ (p - 1) * ∑ b : Bool, x b ^ p := by
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
    (f := x) (fun b _ => hx b) (p - 1)
  simpa [Fintype.card_bool, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne')] using h

/-- Weighted Jensen inequality, written to retain the natural variance weights in the sum. -/
private theorem weighted_pow_sum_le {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (x w : α → ℝ) (p : ℕ) (hp : 0 < p)
    (hx : ∀ i, 0 ≤ x i) (hw : ∀ i, 0 < w i) :
    (∑ i, x i) ^ p ≤ (∑ i, w i) ^ (p - 1) *
      ∑ i, x i ^ p / w i ^ (p - 1) := by
  classical
  let W := ∑ i, w i
  let a : α → ℝ := fun i => w i / W
  have hW : 0 < W := by
    unfold W
    exact Finset.sum_pos (fun i _ => hw i) (Finset.univ_nonempty)
  have ha (i : α) : 0 < a i := by
    dsimp [a]
    exact div_pos (hw i) hW
  have hasum : ∑ i, a i = 1 := by
    dsimp [a, W]
    rw [← Finset.sum_div]
    exact div_self hW.ne'
  have hweights (i : α) : 0 ≤ a i := (ha i).le
  have hpoints (i : α) : 0 ≤ x i / a i := div_nonneg (hx i) (ha i).le
  have hJ : (∑ i, a i * (x i / a i)) ^ p ≤
      ∑ i, a i * (x i / a i) ^ p := by
    have hconv := (convexOn_pow p).map_sum_le
      (t := Finset.univ) (w := a) (p := fun i => x i / a i)
      (fun i _ => hweights i) hasum (fun i _ => Set.mem_Ici.mpr (hpoints i))
    simpa only [smul_eq_mul] using hconv
  have hleft : (∑ i, a i * (x i / a i)) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (ha i)]
  have hright : (∑ i, a i * (x i / a i) ^ p) =
      W ^ (p - 1) * ∑ i, x i ^ p / w i ^ (p - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [a]
    field_simp [ne_of_gt (hw i), ne_of_gt hW]
    have hsub : 1 + (p - 1) - 1 = p - 1 := by omega
    rw [div_pow, mul_pow]
    field_simp [ne_of_gt (hw i)]
    have hpNat : p = p - 1 + 1 := by omega
    rw [hpNat, pow_succ]
    have hsub2 : p - 1 + 1 - 1 = p - 1 := by omega
    rw [hsub2]
    ring
  rw [hleft, hright] at hJ
  simpa [W] using hJ

private theorem ouMatrixSize_eq_card (d : Dims) (N : ℕ) :
    ouMatrixSize d N = Fintype.card (d.Idx N) := by
  simp [ouMatrixSize, Dims.Idx]

private theorem ouMatrixSize_cast_pos (d : Dims) (N : ℕ) :
    (0 : ℝ) < ouMatrixSize d N := by
  exact_mod_cast ouMatrixSize_pos d N

private theorem ouCoordinateVar_coe' (d : Dims) (N : ℕ) (t : ℝ) (c : Coord d) :
    (ouCoordinateVar d N t c : ℝ) =
      (ouBandCoeff t) ^ 2 * (gvar d c : ℝ) +
        (ouGueCoeff t) ^ 2 * (gueCoordVar d N c : ℝ) := by
  dsimp [ouCoordinateVar]
  norm_cast

private theorem ouZeta_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ouZeta t ∧ ouZeta t ≤ 1 := by
  constructor
  · rw [ouZeta]
    exact sub_nonneg.mpr ((Real.exp_le_one_iff).2 (by linarith))
  · rw [ouZeta]
    linarith [Real.exp_pos (-t)]

private theorem ouVarianceEnvelope_pos (d : Dims) (N : ℕ) (i j : d.Idx N) :
    0 < ouVarianceEnvelope d N i j := by
  unfold ouVarianceEnvelope
  have hS := RBM.Sblk_nonneg i j
  have hM := ouMatrixSize_cast_pos d N
  positivity

private theorem ouVarianceEnvelope_symm (d : Dims) (N : ℕ) (i j : d.Idx N) :
    ouVarianceEnvelope d N i j = ouVarianceEnvelope d N j i := by
  unfold ouVarianceEnvelope
  rw [Sblk_comm (d.L N) (d.W N) i j]

private theorem ouVarianceEnvelope_row_sum (d : Dims) (N : ℕ) (i : d.Idx N) :
    ∑ j, ouVarianceEnvelope d N i j = 2 := by
  unfold ouVarianceEnvelope
  rw [Finset.sum_add_distrib, RBM.sum_Sblk_row (d.three_le_L N) i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  have hL : (d.L N : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) (d.three_le_L N)))
  have hW : (d.W N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (d.W_pos N))
  simp only [nsmul_eq_mul, ouMatrixSize, Nat.cast_mul]
  field_simp [hL, hW]
  ring

private theorem ouCoordinateVar_le_envelope (d : Dims) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (i j : d.Idx N) (b : Bool) :
    (ouCoordinateVar d N t ⟨N, i, j, b⟩ : ℝ) ≤ ouVarianceEnvelope d N i j := by
  have hvar := ouCoordinateVar_coe' d N t ⟨N, i, j, b⟩
  have hζ := ouZeta_bounds ht
  have hcoeffX := ouBandCoeff_sq t
  have hcoeffG := ouGueCoeff_sq t ht
  have hS : 0 ≤ Sblk (d.L N) (d.W N) i j := RBM.Sblk_nonneg i j
  have hM := ouMatrixSize_cast_pos d N
  by_cases hij : i = j
  · subst j
    rw [hvar, hcoeffX, hcoeffG, gvar_diag, gueCoordVar_diag]
    unfold ouVarianceEnvelope
    have h1 : 0 ≤ 1 - ouZeta t := by linarith [hζ.2]
    have h1le : 1 - ouZeta t ≤ 1 := by linarith [hζ.1]
    have hterm1 : (1 - ouZeta t) * Sblk (d.L N) (d.W N) i i ≤
        Sblk (d.L N) (d.W N) i i := by
      simpa using mul_le_mul_of_nonneg_right h1le hS
    have hterm2 : ouZeta t / (ouMatrixSize d N : ℝ) ≤
        (ouMatrixSize d N : ℝ)⁻¹ := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hζ.2 (inv_nonneg.mpr hM.le)
    have hterm2' : ouZeta t * (ouMatrixSize d N : ℝ)⁻¹ ≤
        (ouMatrixSize d N : ℝ)⁻¹ := by
      simpa using mul_le_mul_of_nonneg_right hζ.2 (inv_nonneg.mpr hM.le)
    have hterm2'' : ouZeta t * (1 / (ouMatrixSize d N : ℝ)) ≤
        1 / (ouMatrixSize d N : ℝ) := by
      simpa [one_div] using hterm2'
    simp only [one_div] at hterm2''
    simp only [one_div]
    nlinarith

  · rw [hvar, hcoeffX, hcoeffG, gvar_offDiag d N i j b hij,
      gueCoordVar_offDiag d N i j b hij]
    unfold ouVarianceEnvelope
    have h1 : 0 ≤ 1 - ouZeta t := by linarith [hζ.2]
    have h1le : 1 - ouZeta t ≤ 1 := by linarith [hζ.1]
    have hterm1 : (1 - ouZeta t) * Sblk (d.L N) (d.W N) i j ≤
        Sblk (d.L N) (d.W N) i j := by
      simpa using mul_le_mul_of_nonneg_right h1le hS
    have hterm2 : ouZeta t / (ouMatrixSize d N : ℝ) ≤
        (ouMatrixSize d N : ℝ)⁻¹ := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right hζ.2 (inv_nonneg.mpr hM.le)
    have hterm1half : (1 - ouZeta t) * (Sblk (d.L N) (d.W N) i j / 2) ≤
        Sblk (d.L N) (d.W N) i j := by
      have := mul_le_mul_of_nonneg_right h1le (div_nonneg hS (by norm_num : (0:ℝ) ≤ 2))
      nlinarith
    have hterm2half : ouZeta t / (2 * (ouMatrixSize d N : ℝ)) ≤
        (ouMatrixSize d N : ℝ)⁻¹ := by
      have hhalf : ouZeta t / (2 * (ouMatrixSize d N : ℝ)) ≤
          1 / (2 * (ouMatrixSize d N : ℝ)) :=
        div_le_div_of_nonneg_right hζ.2 (by positivity)
      have hden : 1 / (2 * (ouMatrixSize d N : ℝ)) ≤
          1 / (ouMatrixSize d N : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hM]
        nlinarith
      simpa [one_div] using hhalf.trans hden
    have hterm2half' : ouZeta t * (1 / (2 * (ouMatrixSize d N : ℝ))) ≤
        1 / (ouMatrixSize d N : ℝ) := by
      simpa [div_eq_mul_inv, one_div] using hterm2half
    simp only [one_div] at hterm2half'
    simp only [one_div]
    nlinarith

private theorem ouFixedTimeCoordWeight_sum (d : Dims) (N : ℕ) :
    (∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) =
      4 * (ouMatrixSize d N : ℝ) := by
  classical
  have hrow (i : d.Idx N) : ∑ j : d.Idx N,
      (ouVarianceEnvelope d N i j + ouVarianceEnvelope d N i j) = 4 := by
    calc
      ∑ j : d.Idx N, (ouVarianceEnvelope d N i j + ouVarianceEnvelope d N i j) =
          (∑ j : d.Idx N, ouVarianceEnvelope d N i j) +
            (∑ j : d.Idx N, ouVarianceEnvelope d N i j) := by
        rw [Finset.sum_add_distrib]
      _ = 4 := by simp only [ouVarianceEnvelope_row_sum]; norm_num
  calc
    (∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) =
        ∑ i : d.Idx N, ∑ j : d.Idx N,
          (ouVarianceEnvelope d N i j + ouVarianceEnvelope d N i j) := by
      simp [ouFixedTimeCoordWeight, Fintype.sum_prod_type, Fintype.sum_bool]
      simp_rw [two_mul]
    _ = ∑ i : d.Idx N, (4 : ℝ) := by simp_rw [hrow]
    _ = 4 * (ouMatrixSize d N : ℝ) := by simp [ouMatrixSize_eq_card] <;> ring

private theorem ouFixedTimeWeightedPowerSum_integrable (d : Dims) (N : ℕ)
    (t : ℝ) (p : ℕ) :
    Integrable (ouFixedTimeWeightedPowerSum d N t p) (ouCommonMeasure d) := by
  classical
  unfold ouFixedTimeWeightedPowerSum
  apply integrable_finsetSum Finset.univ
  intro c hc
  simpa only [div_eq_mul_inv] using
    (ouCommonCoord_square_pow_integrable d N t ⟨N, c⟩ p).mul_const
      ((ouFixedTimeCoordWeight d N c ^ (p - 1))⁻¹)

private theorem ouFixedTimeWeightedTerm_integrable (d : Dims) (N : ℕ) (t : ℝ)
    (p : ℕ) (c : d.Idx N × d.Idx N × Bool) :
    Integrable (fun ω => (ouCommonCoord d N t ω ⟨N, c⟩ ^ 2) ^ p /
      (ouFixedTimeCoordWeight d N c) ^ (p - 1)) (ouCommonMeasure d) := by
  simpa only [div_eq_mul_inv] using
    (ouCommonCoord_square_pow_integrable d N t ⟨N, c⟩ p).mul_const
      ((ouFixedTimeCoordWeight d N c ^ (p - 1))⁻¹)

private theorem ouFixedTimeWeightedPowerSum_integral_le (d : Dims) (N : ℕ)
    (t : ℝ) (ht : 0 ≤ t) (p : ℕ) (hp : 0 < p) :
    ∫ ω, ouFixedTimeWeightedPowerSum d N t p ω ∂(ouCommonMeasure d) ≤
      RBM.dfac p * (4 * (ouMatrixSize d N : ℝ)) := by
  classical
  have hInt : Integrable (ouFixedTimeWeightedPowerSum d N t p) (ouCommonMeasure d) :=
    ouFixedTimeWeightedPowerSum_integrable d N t p
  have hsplit :
      ∫ ω, ouFixedTimeWeightedPowerSum d N t p ω ∂(ouCommonMeasure d) =
        ∑ c : d.Idx N × d.Idx N × Bool,
          ∫ ω, (ouCommonCoord d N t ω ⟨N, c⟩ ^ 2) ^ p /
            (ouFixedTimeCoordWeight d N c) ^ (p - 1) ∂(ouCommonMeasure d) := by
    simpa [ouFixedTimeWeightedPowerSum] using
      (integral_finsetSum (s := Finset.univ)
        (f := fun c ω => (ouCommonCoord d N t ω ⟨N, c⟩ ^ 2) ^ p /
          (ouFixedTimeCoordWeight d N c) ^ (p - 1))
        (fun c hc => ouFixedTimeWeightedTerm_integrable d N t p c))
  rw [hsplit]
  calc
    (∑ c : d.Idx N × d.Idx N × Bool,
        ∫ ω, (ouCommonCoord d N t ω ⟨N, c⟩ ^ 2) ^ p /
          (ouFixedTimeCoordWeight d N c) ^ (p - 1) ∂(ouCommonMeasure d)) ≤
        ∑ c : d.Idx N × d.Idx N × Bool,
          RBM.dfac p * ouFixedTimeCoordWeight d N c := by
      apply Finset.sum_le_sum
      intro c hc
      have hw := ouVarianceEnvelope_pos d N c.1 c.2.1
      have hv := ouCoordinateVar_le_envelope d N t ht c.1 c.2.1 c.2.2
      have hpow : (ouCoordinateVar d N t ⟨N, c⟩ : ℝ) ^ p ≤
          (ouFixedTimeCoordWeight d N c) ^ p := by
        apply pow_le_pow_left₀ (NNReal.coe_nonneg _) hv p
      have hdf := mul_le_mul_of_nonneg_left hpow (dfac_nonneg p)
      have hden : 0 < (ouFixedTimeCoordWeight d N c) ^ (p - 1) := pow_pos hw _
      have hcancel : (ouFixedTimeCoordWeight d N c) ^ p /
          (ouFixedTimeCoordWeight d N c) ^ (p - 1) = ouFixedTimeCoordWeight d N c := by
        have hpNat : p - 1 + 1 = p := by omega
        have hsub : p - 1 + 1 - 1 = p - 1 := by omega
        calc
          ouFixedTimeCoordWeight d N c ^ p / ouFixedTimeCoordWeight d N c ^ (p - 1) =
              ouFixedTimeCoordWeight d N c ^ (p - 1) * ouFixedTimeCoordWeight d N c /
                ouFixedTimeCoordWeight d N c ^ (p - 1) := by
                  rw [← hpNat, pow_succ, hsub]
          _ = ouFixedTimeCoordWeight d N c := by
            exact mul_div_cancel_left₀ _ (pow_ne_zero _ hw.ne')
      have hbound : RBM.dfac p * (ouCoordinateVar d N t ⟨N, c⟩ : ℝ) ^ p /
          (ouFixedTimeCoordWeight d N c) ^ (p - 1) ≤
            RBM.dfac p * ouFixedTimeCoordWeight d N c := by
        calc
          _ ≤ RBM.dfac p * (ouFixedTimeCoordWeight d N c) ^ p /
                (ouFixedTimeCoordWeight d N c) ^ (p - 1) :=
              div_le_div_of_nonneg_right hdf (pow_nonneg (hw.le) _)
          _ = RBM.dfac p * ouFixedTimeCoordWeight d N c := by
            rw [mul_div_assoc, hcancel]
      calc
        _ = RBM.dfac p * (ouCoordinateVar d N t ⟨N, c⟩ : ℝ) ^ p /
              (ouFixedTimeCoordWeight d N c) ^ (p - 1) := by
            rw [integral_div, ouCommonCoord_square_pow_integral]
        _ ≤ RBM.dfac p * ouFixedTimeCoordWeight d N c := hbound
    _ = RBM.dfac p * (4 * (ouMatrixSize d N : ℝ)) := by
      rw [← Finset.mul_sum, ouFixedTimeCoordWeight_sum]

private theorem ouFixedTimeCoordSqSum_integrable (d : Dims) (N : ℕ) (t : ℝ)
    (p : ℕ) (hp : 0 < p) :
    Integrable (fun ω => ouFixedTimeCoordSqSum d N t ω ^ p) (ouCommonMeasure d) := by
  classical
  haveI : Nonempty (d.Idx N) := ⟨(0, ⟨0, d.W_pos N⟩)⟩
  haveI : Nonempty (d.Idx N × d.Idx N × Bool) := inferInstance
  have hweights := ouFixedTimeCoordWeight_sum d N
  have hsumPos : 0 < ∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c := by
    rw [hweights]
    have hM := ouMatrixSize_cast_pos d N
    nlinarith
  have hJ (ω : ouCommonOmega d) :
      ouFixedTimeCoordSqSum d N t ω ^ p ≤
        (∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) ^ (p - 1) *
          ouFixedTimeWeightedPowerSum d N t p ω := by
    have h := weighted_pow_sum_le
      (fun c : d.Idx N × d.Idx N × Bool =>
        (ouCommonCoord d N t ω ⟨N, c⟩) ^ 2)
      (ouFixedTimeCoordWeight d N) p hp
      (fun c => sq_nonneg _)
      (fun c => by
        have := ouVarianceEnvelope_pos d N c.1 c.2.1
        simpa [ouFixedTimeCoordWeight] using this)
    simpa [ouFixedTimeCoordSqSum, ouFixedTimeWeightedPowerSum] using h
  have hmeas : Measurable (fun ω => ouFixedTimeCoordSqSum d N t ω ^ p) := by
    unfold ouFixedTimeCoordSqSum ouCommonCoord ouCoordinate
    fun_prop
  have hG : Integrable (ouFixedTimeWeightedPowerSum d N t p) (ouCommonMeasure d) :=
    ouFixedTimeWeightedPowerSum_integrable d N t p
  have hGscaled : Integrable
      (fun ω => (∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) ^ (p - 1) *
        ouFixedTimeWeightedPowerSum d N t p ω) (ouCommonMeasure d) :=
    hG.const_mul ((∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) ^ (p - 1))
  refine hGscaled.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hsumNonneg : 0 ≤ ouFixedTimeCoordSqSum d N t ω := by
    unfold ouFixedTimeCoordSqSum
    exact Finset.sum_nonneg fun c _ => sq_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hsumNonneg] using hJ ω

private theorem ouFixedTimeCoordSqSum_moment_le (d : Dims) (N : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (p : ℕ) (hp : 0 < p) :
    ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) ≤
      RBM.dfac p * (4 * (ouMatrixSize d N : ℝ)) ^ p := by
  classical
  haveI : Nonempty (d.Idx N) := ⟨(0, ⟨0, d.W_pos N⟩)⟩
  haveI : Nonempty (d.Idx N × d.Idx N × Bool) := inferInstance
  have hweights := ouFixedTimeCoordWeight_sum d N
  have hleft := ouFixedTimeCoordSqSum_integrable d N t p hp
  have hG := ouFixedTimeWeightedPowerSum_integrable d N t p
  have hscale : 0 ≤ (∑ c : d.Idx N × d.Idx N × Bool,
      ouFixedTimeCoordWeight d N c) ^ (p - 1) := by
    rw [hweights]
    exact pow_nonneg (by positivity) _
  rw [hweights] at hscale
  have hpt : ∀ ω, ouFixedTimeCoordSqSum d N t ω ^ p ≤
      (∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) ^ (p - 1) *
        ouFixedTimeWeightedPowerSum d N t p ω := by
    intro ω
    have h := weighted_pow_sum_le
      (fun c : d.Idx N × d.Idx N × Bool =>
        (ouCommonCoord d N t ω ⟨N, c⟩) ^ 2)
      (ouFixedTimeCoordWeight d N) p hp
      (fun c => sq_nonneg _)
      (fun c => by
        have := ouVarianceEnvelope_pos d N c.1 c.2.1
        simpa [ouFixedTimeCoordWeight] using this)
    simpa [ouFixedTimeCoordSqSum, ouFixedTimeWeightedPowerSum] using h
  have hmono := integral_mono hleft (hG.const_mul
    ((∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) ^ (p - 1))) hpt
  have hGint := ouFixedTimeWeightedPowerSum_integral_le d N t ht p hp
  calc
    ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) ≤
        (∑ c : d.Idx N × d.Idx N × Bool, ouFixedTimeCoordWeight d N c) ^ (p - 1) *
          ∫ ω, ouFixedTimeWeightedPowerSum d N t p ω ∂(ouCommonMeasure d) := by
      simpa only [integral_const_mul] using hmono
    _ ≤ (4 * (ouMatrixSize d N : ℝ)) ^ (p - 1) *
          (RBM.dfac p * (4 * (ouMatrixSize d N : ℝ))) := by
      rw [hweights]
      exact mul_le_mul_of_nonneg_left hGint hscale
    _ = RBM.dfac p * (4 * (ouMatrixSize d N : ℝ)) ^ p := by
      have hpNat : p - 1 + 1 = p := by omega
      have hpow : (4 * (ouMatrixSize d N : ℝ)) ^ (p - 1) *
          (4 * (ouMatrixSize d N : ℝ)) = (4 * (ouMatrixSize d N : ℝ)) ^ p := by
        simpa [hpNat] using (pow_succ (4 * (ouMatrixSize d N : ℝ)) (p - 1)).symm
      calc
        (4 * (ouMatrixSize d N : ℝ)) ^ (p - 1) *
            (RBM.dfac p * (4 * (ouMatrixSize d N : ℝ))) =
              RBM.dfac p * ((4 * (ouMatrixSize d N : ℝ)) ^ (p - 1) *
                (4 * (ouMatrixSize d N : ℝ))) := by ring
        _ = RBM.dfac p * (4 * (ouMatrixSize d N : ℝ)) ^ p := by rw [hpow]

/-- The squared eigenvalues of a Hermitian matrix sum to its Frobenius square. -/
theorem hermitian_eigenvalues_sq_eq_frobSq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (∑ i, hA.eigenvalues i ^ 2) = frobSq A := by
  classical
  let u : Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary
  let U : Matrix n n ℂ := (u : Matrix n n ℂ)
  let D : Matrix n n ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hdiag : A = U * D * star U := by
    dsimp [U, D, Function.comp_def]
    exact hA.spectral_theorem
  have hU : star U * U = 1 := Unitary.coe_star_mul_self u
  have hsq : A ^ 2 = U * (D ^ 2) * star U := by
    rw [hdiag]
    rw [pow_two]
    calc
      (U * D * star U) * (U * D * star U) = U * D * (star U * U) * D * star U := by
        simp [Matrix.mul_assoc]
      _ = U * D * D * star U := by rw [hU]; simp
      _ = U * (D * D) * star U := by simp [Matrix.mul_assoc]
      _ = U * (D ^ 2) * star U := by
        exact congrArg (fun X => U * X * star U) (pow_two D).symm
  have htrace : (A ^ 2).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
    rw [hsq]
    calc
      (U * (D ^ 2) * star U).trace = ((D ^ 2) * (star U * U)).trace := by
        rw [Matrix.trace_mul_cycle]
        exact Matrix.trace_mul_comm _ _
      _ = (D ^ 2).trace := by rw [hU, Matrix.mul_one]
      _ = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
        rw [pow_two, Matrix.diagonal_mul_diagonal]
        simp only [Matrix.trace_diagonal]
        exact Finset.sum_congr rfl fun i _ => by rw [pow_two]
  have hf : (A ^ 2).trace = (frobSq A : ℂ) := by
    simpa using trace_pow_eq_frobSq hA 1
  have hc : (∑ i, ((hA.eigenvalues i : ℂ) ^ 2)) = (frobSq A : ℂ) := htrace.symm.trans hf
  have hcre := congrArg Complex.re hc
  simp_rw [← Complex.ofReal_pow] at hcre
  rw [← Complex.ofReal_sum] at hcre
  simpa only [Complex.ofReal_re] using hcre

private theorem hermitian_eigenvalues_centered_sq {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : ℂ) :
    (∑ i, ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2) =
      frobSq A - 2 * z.re * A.trace.re + (Fintype.card n : ℝ) * ‖z‖ ^ 2 := by
  classical
  have htraceC := Matrix.IsHermitian.trace_eq_sum_eigenvalues hA
  have htraceR : A.trace.re = ∑ i, hA.eigenvalues i := by
    rw [htraceC]
    simp
  have hterm (i : n) :
      ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2 =
        hA.eigenvalues i ^ 2 - 2 * z.re * hA.eigenvalues i + ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_ofReal, Complex.re_ofReal_mul, Complex.conj_re,
      Complex.normSq_eq_norm_sq]
    ring
  calc
    (∑ i, ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2) =
        ∑ i, (hA.eigenvalues i ^ 2 - 2 * z.re * hA.eigenvalues i + ‖z‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i
    _ = (∑ i, hA.eigenvalues i ^ 2) - 2 * z.re * (∑ i, hA.eigenvalues i) +
        (Fintype.card n : ℝ) * ‖z‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = frobSq A - 2 * z.re * A.trace.re + (Fintype.card n : ℝ) * ‖z‖ ^ 2 := by
      rw [hermitian_eigenvalues_sq_eq_frobSq A hA, ← htraceR]

private theorem ouMatrix_common_measurable (d : Dims) (N : ℕ) (t : ℝ) :
    Measurable (fun ω : ouCommonOmega d => ouMatrix d N t (ouCommonProjection d N ω)) := by
  have hsample : Measurable (fun ω : ouCommonOmega d =>
      ouInterpolatedSample d N t (ouCommonProjection d N ω)) := by
    apply measurable_pi_iff.mpr
    intro c
    simp [ouInterpolatedSample, ouCommonProjection, ouCoordinate]
    fun_prop
  convert (measurable_Xmat d N).comp hsample using 1
  funext ω
  simp only [ouMatrix_eq_interpolatedMatrix, ouInterpolatedMatrix, Function.comp_apply]

private theorem ouFixedTimeR2_formula (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ω : ouCommonOmega d) :
    ouFixedTimeR2 d N t z ω =
      (ouMatrixSize d N : ℝ)⁻¹ *
        (frobSq (ouMatrix d N t (ouCommonProjection d N ω)) -
          2 * z.re * (ouMatrix d N t (ouCommonProjection d N ω)).trace.re +
          (ouMatrixSize d N : ℝ) * ‖z‖ ^ 2) := by
  let H := ouMatrix d N t (ouCommonProjection d N ω)
  let hH := ouMatrix_isHermitian d N t (ouCommonProjection d N ω)
  have hcard : Fintype.card (d.Idx N) = ouMatrixSize d N :=
    (ouMatrixSize_eq_card d N).symm
  simpa [ouFixedTimeR2, H, hH, hcard] using
    congrArg (fun x : ℝ => (ouMatrixSize d N : ℝ)⁻¹ * x)
      (hermitian_eigenvalues_centered_sq H hH z)

private theorem ouFixedTimeR2_measurable (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ) :
    Measurable (fun ω : ouCommonOmega d => ouFixedTimeR2 d N t z ω) := by
  have hM := ouMatrix_common_measurable d N t
  have hfrob : Measurable (fun ω : ouCommonOmega d =>
      frobSq (ouMatrix d N t (ouCommonProjection d N ω))) := by
    unfold frobSq
    fun_prop
  have htrace : Measurable (fun ω : ouCommonOmega d =>
      (ouMatrix d N t (ouCommonProjection d N ω)).trace.re) := by
    fun_prop
  have hlinear : Measurable (fun ω : ouCommonOmega d =>
      frobSq (ouMatrix d N t (ouCommonProjection d N ω)) -
        2 * z.re * (ouMatrix d N t (ouCommonProjection d N ω)).trace.re +
        (ouMatrixSize d N : ℝ) * ‖z‖ ^ 2) := by
    exact hfrob.sub (measurable_const.mul htrace) |>.add measurable_const
  have hscaled : Measurable (fun ω : ouCommonOmega d =>
      (ouMatrixSize d N : ℝ)⁻¹ *
        (frobSq (ouMatrix d N t (ouCommonProjection d N ω)) -
          2 * z.re * (ouMatrix d N t (ouCommonProjection d N ω)).trace.re +
          (ouMatrixSize d N : ℝ) * ‖z‖ ^ 2)) := measurable_const.mul hlinear
  convert hscaled using 1
  funext ω
  exact ouFixedTimeR2_formula d N t z ω

private theorem hermitian_centered_sq_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (z : ℂ)
    (hzre : |z.re| ≤ 3) (hzim : 0 < z.im) (hzim' : z.im ≤ 1) :
    (∑ i, ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2) ≤
      2 * frobSq A + 32 * (Fintype.card n : ℝ) := by
  classical
  have hre2 : z.re ^ 2 ≤ 9 := by
    have h := (sq_le_sq₀ (abs_nonneg z.re) (by norm_num : (0 : ℝ) ≤ 3)).mpr hzre
    nlinarith [sq_abs z.re]
  have him2 : z.im ^ 2 ≤ 1 := by nlinarith
  have hzsq : ‖z‖ ^ 2 ≤ 10 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hznorm : ‖z‖ ≤ 4 := by
    nlinarith [sq_nonneg (‖z‖ - 4), norm_nonneg z]
  have hterm (i : n) :
      ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2 ≤
        2 * (hA.eigenvalues i) ^ 2 + 32 := by
    have hnorm : ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ≤ |hA.eigenvalues i| + 4 := by
      calc
        ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ≤
            ‖((hA.eigenvalues i : ℝ) : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ = |hA.eigenvalues i| + ‖z‖ := by simp
        _ ≤ |hA.eigenvalues i| + 4 := by nlinarith [hznorm]
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ |hA.eigenvalues i| + 4)).mpr hnorm
    nlinarith [sq_nonneg (|hA.eigenvalues i| - 4), sq_abs (hA.eigenvalues i)]
  have hsum :
      (∑ i, ‖((hA.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2) ≤
        2 * (∑ i, hA.eigenvalues i ^ 2) + 32 * (Fintype.card n : ℝ) := by
    calc
      _ ≤ ∑ i, (2 * hA.eigenvalues i ^ 2 + 32) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * (∑ i, hA.eigenvalues i ^ 2) + 32 * (Fintype.card n : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  rw [hermitian_eigenvalues_sq_eq_frobSq A hA] at hsum
  exact hsum

private theorem ouFixedTimeR2_le_frob (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (hzre : |z.re| ≤ 3) (hzim : 0 < z.im) (hzim' : z.im ≤ 1)
    (ω : ouCommonOmega d) :
    ouFixedTimeR2 d N t z ω ≤
      2 * frobSq (ouMatrix d N t (ouCommonProjection d N ω)) /
        (ouMatrixSize d N : ℝ) + 32 := by
  let H := ouMatrix d N t (ouCommonProjection d N ω)
  let hH := ouMatrix_isHermitian d N t (ouCommonProjection d N ω)
  have hM : 0 < (ouMatrixSize d N : ℝ) := ouMatrixSize_cast_pos d N
  have hsum := hermitian_centered_sq_le H hH z hzre hzim hzim'
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hM.le)
  have hcard : (Fintype.card (d.Idx N) : ℝ) = (ouMatrixSize d N : ℝ) := by
    exact_mod_cast (ouMatrixSize_eq_card d N).symm
  have hsum' : (∑ i, ‖((hH.eigenvalues i : ℝ) : ℂ) - z‖ ^ 2) ≤
      2 * frobSq H + 32 * (ouMatrixSize d N : ℝ) := by
    rw [hcard] at hsum
    exact hsum
  unfold ouFixedTimeR2
  calc
    _ ≤ (ouMatrixSize d N : ℝ)⁻¹ *
        (2 * frobSq (ouMatrix d N t (ouCommonProjection d N ω)) +
          32 * (ouMatrixSize d N : ℝ)) := by
      simpa [H, hH] using mul_le_mul_of_nonneg_left hsum' (inv_nonneg.mpr hM.le)
    _ = 2 * frobSq (ouMatrix d N t (ouCommonProjection d N ω)) /
        (ouMatrixSize d N : ℝ) + 32 := by
      field_simp [ne_of_gt hM]

private theorem ouMatrix_frobSq_le_coordSqSum (d : Dims) (N : ℕ) (t : ℝ)
    (ω : ouCommonOmega d) :
    frobSq (ouMatrix d N t (ouCommonProjection d N ω)) ≤
      2 * ouFixedTimeCoordSqSum d N t ω := by
  let sample := ouInterpolatedSample d N t (ouCommonProjection d N ω)
  have hcoord : ouFixedTimeCoordSqSum d N t ω = coordSq d N sample := by
    unfold ouFixedTimeCoordSqSum ouCommonCoord coordSq
    apply Finset.sum_congr rfl
    intro c hc
    simp only [ouCoordinate, ouCommonProjection, sample, ouInterpolatedSample]
  have h := frobSq_Xmat_le (d := d) (N := N) sample
  simpa [ouMatrix_eq_interpolatedMatrix, ouInterpolatedMatrix, sample, hcoord] using h

private theorem ouFixedTimeR2_nonneg (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ω : ouCommonOmega d) : 0 ≤ ouFixedTimeR2 d N t z ω := by
  unfold ouFixedTimeR2
  positivity

private theorem ouFixedTimeR2_le_coordSqSum (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ht : 0 ≤ t) (hzre : |z.re| ≤ 3) (hzim : 0 < z.im) (hzim' : z.im ≤ 1)
    (ω : ouCommonOmega d) :
    ouFixedTimeR2 d N t z ω ≤
      4 / (ouMatrixSize d N : ℝ) * ouFixedTimeCoordSqSum d N t ω + 32 := by
  have hspec := ouFixedTimeR2_le_frob d N t z hzre hzim hzim' ω
  have hF := ouMatrix_frobSq_le_coordSqSum d N t ω
  have hscaled :
      2 * frobSq (ouMatrix d N t (ouCommonProjection d N ω)) /
          (ouMatrixSize d N : ℝ) ≤
        4 / (ouMatrixSize d N : ℝ) * ouFixedTimeCoordSqSum d N t ω := by
    have hmul := mul_le_mul_of_nonneg_left hF (by norm_num : (0 : ℝ) ≤ 2)
    have hdiv :
        (2 * frobSq (ouMatrix d N t (ouCommonProjection d N ω))) /
            (ouMatrixSize d N : ℝ) ≤
          (2 * (2 * ouFixedTimeCoordSqSum d N t ω)) /
            (ouMatrixSize d N : ℝ) :=
      div_le_div_of_nonneg_right hmul (by positivity)
    calc
      _ ≤ (2 * (2 * ouFixedTimeCoordSqSum d N t ω)) /
          (ouMatrixSize d N : ℝ) := hdiv
      _ = 4 * ouFixedTimeCoordSqSum d N t ω / (ouMatrixSize d N : ℝ) := by ring
      _ = 4 / (ouMatrixSize d N : ℝ) * ouFixedTimeCoordSqSum d N t ω := by ring
  linarith

private theorem ouFixedTimeR2_pow_integrable (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ht : 0 ≤ t) (hzre : |z.re| ≤ 3) (hzim : 0 < z.im) (hzim' : z.im ≤ 1)
    (p : ℕ) (hp : 0 < p) :
    Integrable (fun ω => ouFixedTimeR2 d N t z ω ^ p) (ouCommonMeasure d) := by
  let c : ℝ := 4 / (ouMatrixSize d N : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcoord := ouFixedTimeCoordSqSum_integrable d N t p hp
  have hcoordScaled : Integrable
      (fun ω => c ^ p * ouFixedTimeCoordSqSum d N t ω ^ p) (ouCommonMeasure d) :=
    hcoord.const_mul (c ^ p)
  have hpowMeas : Measurable (fun ω : ouCommonOmega d =>
      ouFixedTimeR2 d N t z ω ^ p) := (ouFixedTimeR2_measurable d N t z).pow_const p
  have hR2 := ouFixedTimeR2_nonneg d N t z
  have hA (ω : ouCommonOmega d) : 0 ≤ c * ouFixedTimeCoordSqSum d N t ω := by
    have hsum : 0 ≤ ouFixedTimeCoordSqSum d N t ω := by
      unfold ouFixedTimeCoordSqSum
      exact Finset.sum_nonneg fun c _ => sq_nonneg _
    dsimp [c]
    exact mul_nonneg (by positivity) hsum
  have hbound (ω : ouCommonOmega d) :
      ouFixedTimeR2 d N t z ω ^ p ≤
        2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p) := by
    have h1 := pow_le_pow_left₀ (hR2 ω) (ouFixedTimeR2_le_coordSqSum d N t z ht hzre hzim hzim' ω) p
    have h2 := sum_bool_pow_le (fun b : Bool => if b then c * ouFixedTimeCoordSqSum d N t ω else 32)
      p hp (by
        intro b
        by_cases hb : b = true
        · simpa [hb] using hA ω
        · simp [hb])
    have h2' : (c * ouFixedTimeCoordSqSum d N t ω + 32) ^ p ≤
        2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p) := by
      simpa [Fintype.sum_bool] using h2
    exact h1.trans h2'
  have hmajor : Integrable
      (fun ω => 2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p))
      (ouCommonMeasure d) := by
    have hsum : Integrable (fun ω => (c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p)
        (ouCommonMeasure d) := by
      have hfirst : Integrable (fun ω => c ^ p * ouFixedTimeCoordSqSum d N t ω ^ p)
          (ouCommonMeasure d) := hcoordScaled
      have hsum' := hfirst.add (integrable_const ((32 : ℝ) ^ p))
      refine hsum'.congr (Filter.Eventually.of_forall fun ω => ?_)
      change c ^ p * ouFixedTimeCoordSqSum d N t ω ^ p + (32 : ℝ) ^ p =
        (c * ouFixedTimeCoordSqSum d N t ω) ^ p + (32 : ℝ) ^ p
      rw [mul_pow]
    exact hsum.const_mul _
  refine hmajor.mono' hpowMeas.aestronglyMeasurable ?_
  filter_upwards with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg (hR2 ω)] using hbound ω

private theorem ouFixedTimeR2_eq_R_pow (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ω : ouCommonOmega d) (p : ℕ) :
    ouFixedTimeR2 d N t z ω ^ p =
      |ouFixedTimeR d N t z ω| ^ (2 * p) := by
  change ouFixedTimeR2 d N t z ω ^ p =
    |Real.sqrt (ouFixedTimeR2 d N t z ω)| ^ (2 * p)
  rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_mul,
    Real.sq_sqrt (ouFixedTimeR2_nonneg d N t z ω)]

private theorem ouFixedTimeR2_moment_le (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ht : 0 ≤ t) (hzre : |z.re| ≤ 3) (hzim : 0 < z.im) (hzim' : z.im ≤ 1)
    (p : ℕ) (hp : 0 < p) :
    ∫ ω, ouFixedTimeR2 d N t z ω ^ p ∂(ouCommonMeasure d) ≤
      2 ^ (p - 1) * (RBM.dfac p * 16 ^ p + 32 ^ p) := by
  let c : ℝ := 4 / (ouMatrixSize d N : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hM : 0 < (ouMatrixSize d N : ℝ) := ouMatrixSize_cast_pos d N
  have hcoord := ouFixedTimeCoordSqSum_integrable d N t p hp
  have hcoordMoment := ouFixedTimeCoordSqSum_moment_le d N t ht p hp
  have hR2int := ouFixedTimeR2_pow_integrable d N t z ht hzre hzim hzim' p hp
  have hAint : Integrable
      (fun ω => (c * ouFixedTimeCoordSqSum d N t ω) ^ p) (ouCommonMeasure d) := by
    have hscaled := hcoord.const_mul (c ^ p)
    refine hscaled.congr (Filter.Eventually.of_forall fun ω => ?_)
    change c ^ p * ouFixedTimeCoordSqSum d N t ω ^ p =
      (c * ouFixedTimeCoordSqSum d N t ω) ^ p
    rw [← mul_pow]
  have hmajor : Integrable
      (fun ω => 2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p))
      (ouCommonMeasure d) := (hAint.add (integrable_const _)).const_mul _
  have hbound (ω : ouCommonOmega d) :
      ouFixedTimeR2 d N t z ω ^ p ≤
        2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p) := by
    have h1 := pow_le_pow_left₀ (ouFixedTimeR2_nonneg d N t z ω)
      (ouFixedTimeR2_le_coordSqSum d N t z ht hzre hzim hzim' ω) p
    have h2 := sum_bool_pow_le
      (fun b : Bool => if b then c * ouFixedTimeCoordSqSum d N t ω else 32) p hp
      (by
        intro b
        by_cases hb : b = true
        · have hsum : 0 ≤ ouFixedTimeCoordSqSum d N t ω := by
            unfold ouFixedTimeCoordSqSum
            exact Finset.sum_nonneg fun c _ => sq_nonneg _
          dsimp [c]
          simp [hb]
          exact mul_nonneg (by positivity) hsum
        · simp [hb])
    have h2' : (c * ouFixedTimeCoordSqSum d N t ω + 32) ^ p ≤
        2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p) := by
      simpa [Fintype.sum_bool] using h2
    exact h1.trans h2'
  have hAeq :
      ∫ ω, (c * ouFixedTimeCoordSqSum d N t ω) ^ p ∂(ouCommonMeasure d) =
        c ^ p * ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) := by
    calc
      ∫ ω, (c * ouFixedTimeCoordSqSum d N t ω) ^ p ∂(ouCommonMeasure d) =
          ∫ ω, c ^ p * ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [mul_pow]
      _ = c ^ p * ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) :=
        integral_const_mul _ _
  have hsumInt :
      ∫ ω, ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p) ∂(ouCommonMeasure d) =
        c ^ p * ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) + 32 ^ p := by
    calc
      ∫ ω, ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p) ∂(ouCommonMeasure d) =
          ∫ ω, (c * ouFixedTimeCoordSqSum d N t ω) ^ p ∂(ouCommonMeasure d) +
            ∫ ω, (32 : ℝ) ^ p ∂(ouCommonMeasure d) :=
        integral_add hAint (integrable_const _)
      _ = c ^ p * ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) + 32 ^ p := by
        rw [hAeq]
        simp
  have hcoeff : c ^ p * (4 * (ouMatrixSize d N : ℝ)) ^ p = 16 ^ p := by
    have hbase : c * (4 * (ouMatrixSize d N : ℝ)) = 16 := by
      dsimp [c]
      field_simp [ne_of_gt hM]
      ring
    rw [← mul_pow, hbase]
  have hscaledMoment :
      c ^ p * ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) ≤
        RBM.dfac p * 16 ^ p := by
    calc
      _ ≤ c ^ p * (RBM.dfac p * (4 * (ouMatrixSize d N : ℝ)) ^ p) :=
        mul_le_mul_of_nonneg_left hcoordMoment (pow_nonneg hc p)
      _ = RBM.dfac p * (c ^ p * (4 * (ouMatrixSize d N : ℝ)) ^ p) := by ring
      _ = RBM.dfac p * 16 ^ p := by rw [hcoeff]
  calc
    ∫ ω, ouFixedTimeR2 d N t z ω ^ p ∂(ouCommonMeasure d) ≤
        ∫ ω, 2 ^ (p - 1) * ((c * ouFixedTimeCoordSqSum d N t ω) ^ p + 32 ^ p)
          ∂(ouCommonMeasure d) := integral_mono hR2int hmajor hbound
    _ = 2 ^ (p - 1) *
          (c ^ p * ∫ ω, ouFixedTimeCoordSqSum d N t ω ^ p ∂(ouCommonMeasure d) + 32 ^ p) := by
      rw [integral_const_mul, hsumInt]
    _ ≤ 2 ^ (p - 1) * (RBM.dfac p * 16 ^ p + 32 ^ p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [hscaledMoment]
    _ = 2 ^ (p - 1) * (RBM.dfac p * 16 ^ p + 32 ^ p) := rfl

private theorem ouFixedTimeR_pow_integrable (d : Dims) (N : ℕ) (t : ℝ) (z : ℂ)
    (ht : 0 ≤ t) (hzre : |z.re| ≤ 3) (hzim : 0 < z.im) (hzim' : z.im ≤ 1)
    (p : ℕ) :
    Integrable (fun ω => |ouFixedTimeR d N t z ω| ^ (2 * p)) (ouCommonMeasure d) := by
  by_cases hp : 0 < p
  · have h := ouFixedTimeR2_pow_integrable d N t z ht hzre hzim hzim' p hp
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    exact ouFixedTimeR2_eq_R_pow d N t z ω p
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    simp [hp0]

/-- Uniform all-order moments of the actual common-carrier spectral statistic. -/
theorem ouFixedTimeR2_uniform_moment (d : Dims) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (ht : ∀ n, 0 ≤ t n) (hzre : ∀ n, |(z n).re| ≤ 3)
    (hzim : ∀ n, 0 < (z n).im) (hzim' : ∀ n, (z n).im ≤ 1) (p : ℕ) :
    ∃ C > (0 : ℝ), ∀ n,
      ∫ ω, ouFixedTimeR2 d n (t n) (z n) ω ^ p ∂(ouCommonMeasure d) ≤ C := by
  by_cases hp : 0 < p
  · let C := 2 ^ (p - 1) * (RBM.dfac p * 16 ^ p + 32 ^ p)
    have hC : 0 < C := by
      have h32 : 0 < (32 : ℝ) ^ p := pow_pos (by norm_num) p
      have h2 : 0 < (2 : ℝ) ^ (p - 1) := pow_pos (by norm_num) _
      dsimp [C]
      exact mul_pos h2 (add_pos_of_nonneg_of_pos
        (mul_nonneg (dfac_nonneg p) (by positivity)) h32)
    refine ⟨C, hC, ?_⟩
    intro n
    exact ouFixedTimeR2_moment_le d n (t n) (z n) (ht n) (hzre n) (hzim n) (hzim' n) p hp
  · have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    refine ⟨1, by norm_num, ?_⟩
    intro n
    simp [hp0]

/-- All moments of the square-root statistic are integrable on the actual common carrier. -/
theorem ouFixedTimeR_integrable_moments (d : Dims) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (ht : ∀ n, 0 ≤ t n) (hzre : ∀ n, |(z n).re| ≤ 3)
    (hzim : ∀ n, 0 < (z n).im) (hzim' : ∀ n, (z n).im ≤ 1) :
    ∀ (p n : ℕ), Integrable
      (fun ω => |ouFixedTimeR d n (t n) (z n) ω| ^ (2 * p)) (ouCommonMeasure d) := by
  intro p n
  exact ouFixedTimeR_pow_integrable d n (t n) (z n) (ht n) (hzre n) (hzim n) (hzim' n) p

/-- Fixed deterministic times and bounded spectral parameters give `R_n ≺ 1` on the shared
common carrier, with the fixed parameters chosen before the eventual-size quantifier. -/
theorem ouFixedTimeR_stochDom (d : Dims) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (ht : ∀ n, 0 ≤ t n) (hzre : ∀ n, |(z n).re| ≤ 3)
    (hzim : ∀ n, 0 < (z n).im) (hzim' : ∀ n, (z n).im ≤ 1) :
    RBM.StochDom (ouCommonMeasure d)
      (fun n (_ : Unit) ω => ouFixedTimeR d n (t n) (z n) ω)
      (fun _ _ _ => (1 : ℝ)) := by
  refine stochDom_one_of_momentDom (Ccard := 0) ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simp [Real.rpow_zero, hn1]
  · intro p n _
    exact ouFixedTimeR_pow_integrable d n (t n) (z n) (ht n) (hzre n) (hzim n) (hzim' n) p
  · intro ε hε p
    obtain ⟨C, hC, hbound⟩ := ouFixedTimeR2_uniform_moment d t z ht hzre hzim hzim' p
    refine ⟨C, hC, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn u
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (ε * (p : ℝ)) :=
      Real.one_le_rpow hn1 (by positivity)
    have hIntegral :
        ∫ ω, |ouFixedTimeR d n (t n) (z n) ω| ^ (2 * p) ∂(ouCommonMeasure d) =
          ∫ ω, ouFixedTimeR2 d n (t n) (z n) ω ^ p ∂(ouCommonMeasure d) := by
      apply integral_congr_ae
      filter_upwards with ω
      exact (ouFixedTimeR2_eq_R_pow d n (t n) (z n) ω p).symm
    rw [hIntegral]
    calc
      _ ≤ C := hbound n
      _ ≤ C * (n : ℝ) ^ (ε * (p : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_left hnPow hC.le

/-- A same-carrier sample with a positive-variance diagonal coordinate and a bounded, nonzero
fixed-time statistic, including at sequence index zero. -/
theorem ouFixedTimeR2_nonzero_witness (d : Dims) (N : ℕ) :
    ∃ (i : d.Idx N) (ω : ouCommonOmega d),
      0 < (ouCoordinateVar d N 0 ⟨N, i, i, true⟩ : ℝ) ∧
      ouMatrix d N 0 (ouCommonProjection d N ω) i i = (1 / 2 : ℂ) ∧
      0 < ouFixedTimeR2 d N 0 Complex.I ω ∧
      ouFixedTimeR2 d N 0 Complex.I ω ≤ 33 := by
  let i : d.Idx N := (0, ⟨0, by have hw := d.W_pos N; omega⟩)
  let c : Coord d := ⟨N, i, i, true⟩
  let s : Ω d := fun c' => if c' = c then (1 / 2 : ℝ) else 0
  let ω : ouCommonOmega d := (s, fun _ => 0)
  have hvar : (ouCoordinateVar d N 0 c : ℝ) = Sblk (d.L N) (d.W N) i i := by
    calc
      (ouCoordinateVar d N 0 c : ℝ) =
          (ouBandCoeff 0) ^ 2 * (gvar d c : ℝ) +
            (ouGueCoeff 0) ^ 2 * (gueCoordVar d N c : ℝ) := by
        dsimp [ouCoordinateVar]
        norm_cast
      _ = Sblk (d.L N) (d.W N) i i := by
        simp [ouBandCoeff, ouGueCoeff, ouZeta, gvar_diag, c]
  have hvarpos : 0 < (ouCoordinateVar d N 0 c : ℝ) := by
    rw [hvar]
    exact Sblk_diag_pos i
  have hentry : ouMatrix d N 0 (ouCommonProjection d N ω) i i = (1 / 2 : ℂ) := by
    rw [ouMatrix_start]
    simp [ouBandMatrix, Xmat_apply, Xentry, ouCommonProjection, ω, s, c, i]
  have hcoord : ouFixedTimeCoordSqSum d N 0 ω = (1 / 4 : ℝ) := by
    unfold ouFixedTimeCoordSqSum ouCommonCoord
    simp [ouCoordinate, ouCommonProjection, ouBandCoeff, ouGueCoeff, ouZeta, ω, s, c]
    norm_num
  have hupper : ouFixedTimeR2 d N 0 Complex.I ω ≤ 33 := by
    have h := ouFixedTimeR2_le_coordSqSum d N 0 Complex.I (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) ω
    rw [hcoord] at h
    have hM : (1 : ℝ) ≤ (ouMatrixSize d N : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ouMatrixSize_pos d N).ne')
    have hinv : (ouMatrixSize d N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hM
    have hscale : 4 / (ouMatrixSize d N : ℝ) * (1 / 4 : ℝ) ≤ 1 := by
      have heq : 4 / (ouMatrixSize d N : ℝ) * (1 / 4 : ℝ) =
          (ouMatrixSize d N : ℝ)⁻¹ := by
        field_simp [ne_of_gt (ouMatrixSize_cast_pos d N)]
      rw [heq]
      exact hinv
    linarith
  have hlower : 0 < ouFixedTimeR2 d N 0 Complex.I ω := by
    unfold ouFixedTimeR2
    let hH := ouMatrix_isHermitian d N 0 (ouCommonProjection d N ω)
    have hterm (j : d.Idx N) :
        0 < ‖((hH.eigenvalues j : ℝ) : ℂ) - Complex.I‖ ^ 2 := by
      have hne : (((hH.eigenvalues j : ℝ) : ℂ) - Complex.I) ≠ 0 := by
        intro heq
        have him := congrArg Complex.im heq
        norm_num at him
      have hnorm : 0 < ‖((hH.eigenvalues j : ℝ) : ℂ) - Complex.I‖ :=
        norm_pos_iff.mpr hne
      positivity
    have hsum : 0 < ∑ j : d.Idx N,
        ‖((hH.eigenvalues j : ℝ) : ℂ) - Complex.I‖ ^ 2 := by
      apply Finset.sum_pos'
      · intro j hj
        positivity
      · exact ⟨i, Finset.mem_univ _, hterm i⟩
    have hM : 0 < (ouMatrixSize d N : ℝ) := ouMatrixSize_cast_pos d N
    have hmul : 0 < (ouMatrixSize d N : ℝ)⁻¹ *
        ∑ j : d.Idx N, ‖((hH.eigenvalues j : ℝ) : ℂ) - Complex.I‖ ^ 2 :=
      mul_pos (inv_pos.mpr hM) hsum
    simpa [ouFixedTimeR2, hH] using hmul
  exact ⟨i, ω, by simpa [c] using hvarpos, hentry, hlower, hupper⟩

end

end RBM.Gauss
