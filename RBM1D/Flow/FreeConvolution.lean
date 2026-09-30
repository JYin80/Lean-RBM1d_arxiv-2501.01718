/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.DBMInput

/-!
# Existence and uniqueness of the free-convolution subordination equation

This file proves existence and uniqueness of the fixed point `m` of the free-convolution
equation `m = (1/n) ∑ i, (v i - z - t m)⁻¹` (Landon–Sosoe–Yau [51, (2.5)]) among `m` with
`Im m > 0`, for `v : n → ℝ`, `t ≥ 0`, `z` in the upper half-plane. Uses only elementary complex
analysis (Cauchy–Schwarz on finite sums, and a shifted pseudo-hyperbolic-metric contraction to
get existence for `t > 0`; a direct algebraic argument gives uniqueness for all `t ≥ 0`).

* `freeConv_existsUnique`: existence and uniqueness.
* `freeConvST`: the resulting Stieltjes transform of the free convolution, as a function of `z`.
* `isFreeConv51_freeConvST`: `freeConvST` satisfies `IsFreeConv51` (`[51, (2.5)]`).
-/

open Filter Topology

namespace RBM.Gauss

variable {n : Type*} [Fintype n] [Nonempty n]

/-! ### Elementary facts about `stieltjesVec` -/

private lemma freeConv_cardInv_ofReal :
    (((Fintype.card n : ℕ) : ℂ))⁻¹ = ((((Fintype.card n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.ofReal_inv, Complex.ofReal_natCast]

private lemma freeConv_card_ne_zero : ((Fintype.card n : ℕ) : ℝ) ≠ 0 := by
  have := Fintype.card_pos (α := n)
  exact_mod_cast this.ne'

/-- Shift identity: the fixed-point equation for `m` unfolds to `stieltjesVec` at `z + t * m`. -/
private lemma freeConv_stieltjesVec_shift (v : n → ℝ) (z t m : ℂ) :
    stieltjesVec v (z + t * m) =
      ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - t * m)⁻¹ := by
  unfold stieltjesVec
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

private lemma freeConv_sub_ne_zero {a : ℝ} {ω : ℂ} (hω : ω.im ≠ 0) : (a : ℂ) - ω ≠ 0 := by
  intro h
  apply hω
  have him : ((a : ℂ) - ω).im = (0 : ℂ).im := by rw [h]
  simpa using him

private lemma freeConv_stieltjesVec_im (v : n → ℝ) (ω : ℂ) :
    (stieltjesVec v ω).im =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, ω.im / Complex.normSq ((v i : ℂ) - ω) := by
  unfold stieltjesVec
  rw [freeConv_cardInv_ofReal, Complex.im_ofReal_mul]
  congr 1
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inv_im, Complex.sub_im, Complex.ofReal_im]
  ring

private lemma freeConv_stieltjesVec_im_pos (v : n → ℝ) {ω : ℂ} (hω : 0 < ω.im) :
    0 < (stieltjesVec v ω).im := by
  rw [freeConv_stieltjesVec_im]
  refine mul_pos (by positivity) (Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty)
  exact div_pos hω (Complex.normSq_pos.mpr (freeConv_sub_ne_zero hω.ne'))

private lemma freeConv_stieltjesVec_im_le (v : n → ℝ) {ω : ℂ} (hω : 0 < ω.im) :
    (stieltjesVec v ω).im ≤ ω.im⁻¹ := by
  rw [freeConv_stieltjesVec_im]
  have hterm : ∀ i ∈ (Finset.univ : Finset n),
      ω.im / Complex.normSq ((v i : ℂ) - ω) ≤ ω.im⁻¹ := by
    intro i _
    have hne : (v i : ℂ) - ω ≠ 0 := freeConv_sub_ne_zero hω.ne'
    have hpos : 0 < Complex.normSq ((v i : ℂ) - ω) := Complex.normSq_pos.mpr hne
    have hsq : ((v i : ℂ) - ω).im * ((v i : ℂ) - ω).im ≤ Complex.normSq ((v i : ℂ) - ω) :=
      Complex.im_sq_le_normSq _
    have him : ((v i : ℂ) - ω).im = -ω.im := by
      rw [Complex.sub_im, Complex.ofReal_im]; ring
    rw [him] at hsq
    have hsq' : ω.im ^ 2 ≤ Complex.normSq ((v i : ℂ) - ω) := by nlinarith [hsq]
    rw [div_le_iff₀ hpos]
    rw [inv_mul_eq_div, le_div_iff₀ hω]
    nlinarith [hsq']
  calc ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, ω.im / Complex.normSq ((v i : ℂ) - ω)
      ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ _i : n, ω.im⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = ω.im⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [freeConv_card_ne_zero]

private lemma freeConv_stieltjesVec_norm_le (v : n → ℝ) {ω : ℂ} (hω : 0 < ω.im) :
    ‖stieltjesVec v ω‖ ≤ ω.im⁻¹ := by
  have hterm : ∀ i ∈ (Finset.univ : Finset n), ‖((v i : ℂ) - ω)⁻¹‖ ≤ ω.im⁻¹ := by
    intro i _
    have hne : (v i : ℂ) - ω ≠ 0 := freeConv_sub_ne_zero hω.ne'
    rw [norm_inv]
    have habs : |((v i : ℂ) - ω).im| ≤ ‖(v i : ℂ) - ω‖ := Complex.abs_im_le_norm _
    have him : ((v i : ℂ) - ω).im = -ω.im := by
      rw [Complex.sub_im, Complex.ofReal_im]; ring
    rw [him, abs_neg, abs_of_pos hω] at habs
    have hpos : (0:ℝ) < ‖(v i : ℂ) - ω‖ := lt_of_lt_of_le hω habs
    exact (inv_le_inv₀ hpos hω).mpr habs
  have hcard_nonneg : (0:ℝ) ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ := by positivity
  have hnormeq : ‖stieltjesVec v ω‖ =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ * ‖∑ i, ((v i : ℂ) - ω)⁻¹‖ := by
    unfold stieltjesVec
    rw [freeConv_cardInv_ofReal, norm_mul, Complex.norm_of_nonneg hcard_nonneg]
  rw [hnormeq]
  calc ((Fintype.card n : ℕ) : ℝ)⁻¹ * ‖∑ i, ((v i : ℂ) - ω)⁻¹‖
      ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, ‖((v i : ℂ) - ω)⁻¹‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) hcard_nonneg
    _ ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ _i : n, ω.im⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) hcard_nonneg
    _ = ω.im⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [freeConv_card_ne_zero]

/-- Elementary algebraic identity behind the Cauchy–Schwarz bound. -/
private lemma freeConv_inv_sub_inv {a : ℝ} {ω1 ω2 : ℂ} (h1 : (a : ℂ) - ω1 ≠ 0)
    (h2 : (a : ℂ) - ω2 ≠ 0) :
    ((a : ℂ) - ω1)⁻¹ - ((a : ℂ) - ω2)⁻¹ = (ω1 - ω2) * (((a : ℂ) - ω1)⁻¹ * ((a : ℂ) - ω2)⁻¹) := by
  field_simp
  ring

/-- **Key Cauchy–Schwarz bound.** -/
private lemma freeConv_stieltjesVec_sub_le (v : n → ℝ) {ω1 ω2 : ℂ} (h1 : 0 < ω1.im)
    (h2 : 0 < ω2.im) :
    ‖stieltjesVec v ω1 - stieltjesVec v ω2‖ ≤
      ‖ω1 - ω2‖ * Real.sqrt ((stieltjesVec v ω1).im / ω1.im) *
        Real.sqrt ((stieltjesVec v ω2).im / ω2.im) := by
  have hne1 : ∀ i : n, (v i : ℂ) - ω1 ≠ 0 := fun i => freeConv_sub_ne_zero h1.ne'
  have hne2 : ∀ i : n, (v i : ℂ) - ω2 ≠ 0 := fun i => freeConv_sub_ne_zero h2.ne'
  set f : n → ℝ := fun i => ‖((v i : ℂ) - ω1)⁻¹‖ with hf_def
  set g : n → ℝ := fun i => ‖((v i : ℂ) - ω2)⁻¹‖ with hg_def
  have hdiff : stieltjesVec v ω1 - stieltjesVec v ω2 =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ *
        ∑ i, (ω1 - ω2) * (((v i : ℂ) - ω1)⁻¹ * ((v i : ℂ) - ω2)⁻¹) := by
    have e1 : stieltjesVec v ω1 =
        ((Fintype.card n : ℕ) : ℝ)⁻¹ * (∑ i, ((v i : ℂ) - ω1)⁻¹ : ℂ) := by
      unfold stieltjesVec; rw [freeConv_cardInv_ofReal]
    have e2 : stieltjesVec v ω2 =
        ((Fintype.card n : ℕ) : ℝ)⁻¹ * (∑ i, ((v i : ℂ) - ω2)⁻¹ : ℂ) := by
      unfold stieltjesVec; rw [freeConv_cardInv_ofReal]
    rw [e1, e2, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact freeConv_inv_sub_inv (hne1 i) (hne2 i)
  have hnorm1 : ‖stieltjesVec v ω1 - stieltjesVec v ω2‖ =
      ((Fintype.card n : ℕ) : ℝ)⁻¹ *
        ‖∑ i, (ω1 - ω2) * (((v i : ℂ) - ω1)⁻¹ * ((v i : ℂ) - ω2)⁻¹)‖ := by
    rw [hdiff, norm_mul, Complex.norm_of_nonneg (by positivity)]
  have hnorm2 : ‖∑ i, (ω1 - ω2) * (((v i : ℂ) - ω1)⁻¹ * ((v i : ℂ) - ω2)⁻¹)‖ ≤
      ‖ω1 - ω2‖ * ∑ i, f i * g i := by
    calc ‖∑ i, (ω1 - ω2) * (((v i : ℂ) - ω1)⁻¹ * ((v i : ℂ) - ω2)⁻¹)‖
        ≤ ∑ i, ‖(ω1 - ω2) * (((v i : ℂ) - ω1)⁻¹ * ((v i : ℂ) - ω2)⁻¹)‖ := norm_sum_le _ _
      _ = ∑ i, ‖ω1 - ω2‖ * (f i * g i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_mul]
      _ = ‖ω1 - ω2‖ * ∑ i, f i * g i := by rw [Finset.mul_sum]
  have hCS : ∑ i, f i * g i ≤ Real.sqrt (∑ i, (f i) ^ 2) * Real.sqrt (∑ i, (g i) ^ 2) := by
    have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) f g
    have hnn : (0:ℝ) ≤ ∑ i, f i * g i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hnn1 : (0:ℝ) ≤ ∑ i, (f i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc ∑ i, f i * g i = Real.sqrt ((∑ i, f i * g i) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∑ i, (f i) ^ 2) * ∑ i, (g i) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (∑ i, (f i) ^ 2) * Real.sqrt (∑ i, (g i) ^ 2) := Real.sqrt_mul hnn1 _
  have hexpand1 : ∀ i : n, (f i) ^ 2 = (Complex.normSq ((v i : ℂ) - ω1))⁻¹ := by
    intro i
    rw [hf_def]; simp only [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  have hexpand2 : ∀ i : n, (g i) ^ 2 = (Complex.normSq ((v i : ℂ) - ω2))⁻¹ := by
    intro i
    rw [hg_def]; simp only [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  have hf2 : ∑ i, (f i) ^ 2 = ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω1).im / ω1.im := by
    have hsum : ∑ i, ω1.im / Complex.normSq ((v i : ℂ) - ω1) =
        ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω1).im := by
      rw [freeConv_stieltjesVec_im]; field_simp [freeConv_card_ne_zero]
    calc ∑ i, (f i) ^ 2 = ∑ i, ω1.im⁻¹ * (ω1.im / Complex.normSq ((v i : ℂ) - ω1)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexpand1 i]
          have hpos : (0:ℝ) < Complex.normSq ((v i : ℂ) - ω1) :=
            Complex.normSq_pos.mpr (hne1 i)
          field_simp
      _ = ω1.im⁻¹ * ∑ i, ω1.im / Complex.normSq ((v i : ℂ) - ω1) := by rw [Finset.mul_sum]
      _ = ω1.im⁻¹ * (((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω1).im) := by rw [hsum]
      _ = ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω1).im / ω1.im := by ring
  have hg2 : ∑ i, (g i) ^ 2 = ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω2).im / ω2.im := by
    have hsum : ∑ i, ω2.im / Complex.normSq ((v i : ℂ) - ω2) =
        ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω2).im := by
      rw [freeConv_stieltjesVec_im]; field_simp [freeConv_card_ne_zero]
    calc ∑ i, (g i) ^ 2 = ∑ i, ω2.im⁻¹ * (ω2.im / Complex.normSq ((v i : ℂ) - ω2)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hexpand2 i]
          have hpos : (0:ℝ) < Complex.normSq ((v i : ℂ) - ω2) :=
            Complex.normSq_pos.mpr (hne2 i)
          field_simp
      _ = ω2.im⁻¹ * ∑ i, ω2.im / Complex.normSq ((v i : ℂ) - ω2) := by rw [Finset.mul_sum]
      _ = ω2.im⁻¹ * (((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω2).im) := by rw [hsum]
      _ = ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω2).im / ω2.im := by ring
  have hcard0 : (0:ℝ) ≤ ((Fintype.card n : ℕ) : ℝ) := by positivity
  rw [hnorm1]
  calc ((Fintype.card n : ℕ) : ℝ)⁻¹ *
        ‖∑ i, (ω1 - ω2) * (((v i : ℂ) - ω1)⁻¹ * ((v i : ℂ) - ω2)⁻¹)‖
      ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ * (‖ω1 - ω2‖ * ∑ i, f i * g i) :=
        mul_le_mul_of_nonneg_left hnorm2 (by positivity)
    _ ≤ ((Fintype.card n : ℕ) : ℝ)⁻¹ *
          (‖ω1 - ω2‖ * (Real.sqrt (∑ i, (f i) ^ 2) * Real.sqrt (∑ i, (g i) ^ 2))) := by
        gcongr
    _ = ((Fintype.card n : ℕ) : ℝ)⁻¹ *
          (‖ω1 - ω2‖ *
            (Real.sqrt (((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω1).im / ω1.im) *
              Real.sqrt (((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω2).im / ω2.im))) := by
        rw [hf2, hg2]
    _ = ‖ω1 - ω2‖ * Real.sqrt ((stieltjesVec v ω1).im / ω1.im) *
          Real.sqrt ((stieltjesVec v ω2).im / ω2.im) := by
        rw [show ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω1).im / ω1.im =
              ((Fintype.card n : ℕ) : ℝ) * ((stieltjesVec v ω1).im / ω1.im) by ring,
            show ((Fintype.card n : ℕ) : ℝ) * (stieltjesVec v ω2).im / ω2.im =
              ((Fintype.card n : ℕ) : ℝ) * ((stieltjesVec v ω2).im / ω2.im) by ring,
            Real.sqrt_mul hcard0, Real.sqrt_mul hcard0]
        have hc : (0:ℝ) < ((Fintype.card n : ℕ) : ℝ) := by
          have := Fintype.card_pos (α := n); exact_mod_cast this
        have hcs : Real.sqrt (((Fintype.card n : ℕ) : ℝ)) ≠ 0 := by
          positivity
        field_simp
        rw [Real.sq_sqrt hcard0]
        ring

/-! ### Uniqueness (all `t ≥ 0`) -/

private lemma freeConv_uniqueness_pos (v : n → ℝ) {t : ℝ} (ht0 : 0 < t) {z : ℂ} (hz : 0 < z.im)
    {m1 m2 : ℂ} (hm1 : 0 < m1.im) (hm2 : 0 < m2.im)
    (he1 : m1 = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m1)⁻¹)
    (he2 : m2 = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m2)⁻¹) :
    m1 = m2 := by
  by_contra hne
  have hm1eq : m1 = stieltjesVec v (z + (t : ℂ) * m1) := by
    rw [freeConv_stieltjesVec_shift]; exact he1
  have hm2eq : m2 = stieltjesVec v (z + (t : ℂ) * m2) := by
    rw [freeConv_stieltjesVec_shift]; exact he2
  set ω1 : ℂ := z + (t : ℂ) * m1 with hω1_def
  set ω2 : ℂ := z + (t : ℂ) * m2 with hω2_def
  have hω1im : ω1.im = z.im + t * m1.im := by
    rw [hω1_def]; simp [Complex.add_im, Complex.mul_im]
  have hω2im : ω2.im = z.im + t * m2.im := by
    rw [hω2_def]; simp [Complex.add_im, Complex.mul_im]
  have hω1pos : 0 < ω1.im := by rw [hω1im]; nlinarith
  have hω2pos : 0 < ω2.im := by rw [hω2im]; nlinarith
  have hωdiff : ω1 - ω2 = (t : ℂ) * (m1 - m2) := by
    rw [hω1_def, hω2_def]; ring
  have hmdiff : m1 - m2 = stieltjesVec v ω1 - stieltjesVec v ω2 := by rw [← hm1eq, ← hm2eq]
  have hbound := freeConv_stieltjesVec_sub_le v hω1pos hω2pos
  rw [← hmdiff, hωdiff, norm_mul, Complex.norm_of_nonneg ht0.le, ← hm1eq, ← hm2eq] at hbound
  have hm1ne : m1 - m2 ≠ 0 := sub_ne_zero.mpr hne
  have hmnorm_pos : 0 < ‖m1 - m2‖ := norm_pos_iff.mpr hm1ne
  -- Bound `sqrt(m_j.im/ω_j.im) < sqrt(1/t)` strictly, using `ω_j.im > t * m_j.im`.
  have hbound1 : m1.im / ω1.im < t⁻¹ := by
    rw [div_lt_iff₀ hω1pos, hω1im]
    have hstep : z.im + t * m1.im > t * m1.im := by linarith
    calc m1.im = t⁻¹ * (t * m1.im) := by field_simp
      _ < t⁻¹ * (z.im + t * m1.im) := mul_lt_mul_of_pos_left hstep (by positivity)
  have hbound2 : m2.im / ω2.im < t⁻¹ := by
    rw [div_lt_iff₀ hω2pos, hω2im]
    have hstep : z.im + t * m2.im > t * m2.im := by linarith
    calc m2.im = t⁻¹ * (t * m2.im) := by field_simp
      _ < t⁻¹ * (z.im + t * m2.im) := mul_lt_mul_of_pos_left hstep (by positivity)
  have hs1 : Real.sqrt (m1.im / ω1.im) < Real.sqrt (t⁻¹) :=
    Real.sqrt_lt_sqrt (by positivity) hbound1
  have hs2 : Real.sqrt (m2.im / ω2.im) < Real.sqrt (t⁻¹) :=
    Real.sqrt_lt_sqrt (by positivity) hbound2
  have hs1' : 0 ≤ Real.sqrt (m1.im / ω1.im) := Real.sqrt_nonneg _
  have hs2' : 0 ≤ Real.sqrt (m2.im / ω2.im) := Real.sqrt_nonneg _
  have hprod : Real.sqrt (m1.im / ω1.im) * Real.sqrt (m2.im / ω2.im) <
      Real.sqrt (t⁻¹) * Real.sqrt (t⁻¹) :=
    mul_lt_mul'' hs1 hs2 hs1' hs2'
  have hsqrtinv : Real.sqrt (t⁻¹) * Real.sqrt (t⁻¹) = t⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  rw [hsqrtinv] at hprod
  -- From `hbound`: `‖m1-m2‖ ≤ t * ‖m1-m2‖ * sqrt(m1.im/ω1.im) * sqrt(m2.im/ω2.im)`.
  have hfinal : ‖m1 - m2‖ * 1 < ‖m1 - m2‖ * (t * t⁻¹) := by
    have step : ‖m1 - m2‖ ≤
        ‖m1 - m2‖ * (t * (Real.sqrt (m1.im / ω1.im) * Real.sqrt (m2.im / ω2.im))) := by
      calc ‖m1 - m2‖ ≤ t * ‖m1 - m2‖ * Real.sqrt (m1.im / ω1.im) * Real.sqrt (m2.im / ω2.im) :=
            hbound
        _ = ‖m1 - m2‖ * (t * (Real.sqrt (m1.im / ω1.im) * Real.sqrt (m2.im / ω2.im))) := by ring
    have hlt : ‖m1 - m2‖ * (t * (Real.sqrt (m1.im / ω1.im) * Real.sqrt (m2.im / ω2.im))) <
        ‖m1 - m2‖ * (t * t⁻¹) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hprod ht0) hmnorm_pos
    have := lt_of_le_of_lt step hlt
    simpa using this
  rw [mul_inv_cancel₀ ht0.ne'] at hfinal
  simp at hfinal

/-! ### Existence for `t > 0` -/

private lemma freeConv_exists_pos (v : n → ℝ) {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 < z.im) :
    ∃ m : ℂ, 0 < m.im ∧ m = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m)⁻¹ := by
  classical
  set η : ℝ := z.im with hη_def
  have hη : 0 < η := hz
  set R : ℝ := ∑ i, |v i| with hR_def
  have hRnonneg : 0 ≤ R := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hRbound : ∀ i, |v i| ≤ R := by
    intro i
    have heq := Finset.sum_erase_add (Finset.univ : Finset n) (fun j => |v j|) (Finset.mem_univ i)
    have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.univ.erase i, |v j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    rw [hR_def]
    nlinarith [heq, hnn]
  set Λ : ℝ := R + ‖z‖ + t / η with hΛ_def
  have hΛpos : 0 < Λ := by rw [hΛ_def]; positivity
  set ε : ℝ := t * η / Λ ^ 2 with hε_def
  have hεpos : 0 < ε := by rw [hε_def]; positivity
  have hηleΛ : η ≤ Λ := by
    have h1 : η ≤ ‖z‖ := by
      have := Complex.im_le_norm z
      rw [hη_def]; exact this
    rw [hΛ_def]; nlinarith [hRnonneg, div_nonneg ht.le hη.le]
  have hεle : ε ≤ t / η := by
    rw [hε_def, div_le_div_iff₀ (by positivity) hη]
    have h1 : η ^ 2 ≤ Λ ^ 2 := by nlinarith [hηleΛ, hη.le, hΛpos.le]
    nlinarith [h1, ht.le]
  set κ : ℝ := t / (η ^ 2 + t) with hκ_def
  have hκnonneg : 0 ≤ κ := by rw [hκ_def]; positivity
  have hκlt1 : κ < 1 := by
    rw [hκ_def, div_lt_one (by positivity)]
    nlinarith [sq_nonneg η, hη]
  set K : Set ℂ := {ω : ℂ | η + ε ≤ ω.im ∧ ω.im ≤ η + t / η ∧ ‖ω - z‖ ≤ t / η} with hK_def
  set T : ℂ → ℂ := fun ω => z + (t : ℂ) * stieltjesVec v ω with hT_def
  have hTim_all : ∀ ω : ℂ, (T ω).im = η + t * (stieltjesVec v ω).im := by
    intro ω
    rw [hT_def]; simp [Complex.add_im, Complex.mul_im, hη_def]
  have hTdisc_all : ∀ ω : ℂ, T ω - z = (t : ℂ) * stieltjesVec v ω := by
    intro ω; rw [hT_def]; ring
  have hTdiff_all : ∀ ω1 ω2 : ℂ, T ω1 - T ω2 = (t : ℂ) * (stieltjesVec v ω1 - stieltjesVec v ω2) := by
    intro ω1 ω2; rw [hT_def]; ring
  -- self-map
  have hself : ∀ ω ∈ K, T ω ∈ K := by
    intro ω hω
    obtain ⟨hω1, hω2, hω3⟩ := hω
    have hηω : η ≤ ω.im := by linarith [hεpos]
    have hωim : 0 < ω.im := by linarith
    have hTim : (T ω).im = η + t * (stieltjesVec v ω).im := hTim_all ω
    have hTdisc : T ω - z = (t : ℂ) * stieltjesVec v ω := hTdisc_all ω
    refine ⟨?_, ?_, ?_⟩
    · -- lower bound
      rw [hTim]
      have hΛbound : ∀ i, ‖(v i : ℂ) - ω‖ ≤ Λ := by
        intro i
        have h1 : ‖(v i : ℂ) - ω‖ ≤ ‖(v i : ℂ)‖ + ‖ω‖ := norm_sub_le _ _
        have h2 : ‖(v i : ℂ)‖ = |v i| := by rw [Complex.norm_real, Real.norm_eq_abs]
        have h3 : ‖ω‖ ≤ ‖z‖ + t / η := by
          calc ‖ω‖ = ‖z + (ω - z)‖ := by congr 1; ring
            _ ≤ ‖z‖ + ‖ω - z‖ := norm_add_le _ _
            _ ≤ ‖z‖ + t / η := by linarith [hω3]
        rw [h2] at h1
        rw [hΛ_def]
        linarith [hRbound i, h1, h3]
      have hlow : ε ≤ t * (stieltjesVec v ω).im := by
        have hSVim : (stieltjesVec v ω).im ≥ ω.im / Λ ^ 2 := by
          rw [freeConv_stieltjesVec_im]
          have hterm : ∀ i ∈ (Finset.univ : Finset n),
              ω.im / Λ ^ 2 ≤ ω.im / Complex.normSq ((v i : ℂ) - ω) := by
            intro i _
            have hne : (v i : ℂ) - ω ≠ 0 := freeConv_sub_ne_zero hωim.ne'
            have hnormsq_le : Complex.normSq ((v i : ℂ) - ω) ≤ Λ ^ 2 := by
              rw [Complex.normSq_eq_norm_sq]
              exact pow_le_pow_left₀ (norm_nonneg _) (hΛbound i) 2
            have hpos1 : (0:ℝ) < Complex.normSq ((v i : ℂ) - ω) := Complex.normSq_pos.mpr hne
            exact div_le_div_of_nonneg_left hωim.le hpos1 hnormsq_le
          calc ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ i, ω.im / Complex.normSq ((v i : ℂ) - ω)
              ≥ ((Fintype.card n : ℕ) : ℝ)⁻¹ * ∑ _i : n, ω.im / Λ ^ 2 :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
            _ = ω.im / Λ ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                field_simp [freeConv_card_ne_zero]
        have hstep : t * (ω.im / Λ ^ 2) ≤ t * (stieltjesVec v ω).im :=
          mul_le_mul_of_nonneg_left hSVim ht.le
        have hεeq : ε = t * (η / Λ ^ 2) := by rw [hε_def]; ring
        rw [hεeq]
        calc t * (η / Λ ^ 2) ≤ t * (ω.im / Λ ^ 2) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hηω (by positivity)) ht.le
          _ ≤ t * (stieltjesVec v ω).im := hstep
      linarith [hlow]
    · -- upper bound
      rw [hTim]
      have hle : (stieltjesVec v ω).im ≤ ω.im⁻¹ := freeConv_stieltjesVec_im_le v hωim
      have hstep1 : t * (stieltjesVec v ω).im ≤ t * ω.im⁻¹ := mul_le_mul_of_nonneg_left hle ht.le
      have hωinv : ω.im⁻¹ ≤ η⁻¹ := (inv_le_inv₀ hωim hη).mpr hηω
      have hstep2 : t * ω.im⁻¹ ≤ t * η⁻¹ := mul_le_mul_of_nonneg_left hωinv ht.le
      have heq : t * η⁻¹ = t / η := by rw [div_eq_mul_inv]
      linarith [hstep1, hstep2]
    · -- disc bound
      rw [hTdisc, norm_mul, Complex.norm_of_nonneg ht.le]
      have hle : ‖stieltjesVec v ω‖ ≤ ω.im⁻¹ := freeConv_stieltjesVec_norm_le v hωim
      have h1 : t * ‖stieltjesVec v ω‖ ≤ t * ω.im⁻¹ := mul_le_mul_of_nonneg_left hle ht.le
      have hωinv : ω.im⁻¹ ≤ η⁻¹ := (inv_le_inv₀ hωim hη).mpr hηω
      have h2 : t * ω.im⁻¹ ≤ t * η⁻¹ := mul_le_mul_of_nonneg_left hωinv ht.le
      have heq : t * η⁻¹ = t / η := by rw [div_eq_mul_inv]
      linarith [h1, h2]
  -- Cauchy–Schwarz bound for `T`, in terms of plain imaginary parts.
  have hLemA : ∀ ω1 ∈ K, ∀ ω2 ∈ K,
      ‖T ω1 - T ω2‖ * Real.sqrt (ω1.im * ω2.im) ≤
        ‖ω1 - ω2‖ * Real.sqrt (((T ω1).im - η) * ((T ω2).im - η)) := by
    intro ω1 hω1mem ω2 hω2mem
    obtain ⟨hω1a, hω1b, hω1c⟩ := hω1mem
    obtain ⟨hω2a, hω2b, hω2c⟩ := hω2mem
    have hω1pos : 0 < ω1.im := by linarith [hεpos]
    have hω2pos : 0 < ω2.im := by linarith [hεpos]
    have hSV1pos : 0 < (stieltjesVec v ω1).im := freeConv_stieltjesVec_im_pos v hω1pos
    have hSV2pos : 0 < (stieltjesVec v ω2).im := freeConv_stieltjesVec_im_pos v hω2pos
    have hbound := freeConv_stieltjesVec_sub_le v hω1pos hω2pos
    have hY1 : (T ω1).im - η = t * (stieltjesVec v ω1).im := by rw [hTim_all]; ring
    have hY2 : (T ω2).im - η = t * (stieltjesVec v ω2).im := by rw [hTim_all]; ring
    have hTeq : ‖T ω1 - T ω2‖ = t * ‖stieltjesVec v ω1 - stieltjesVec v ω2‖ := by
      rw [hTdiff_all, norm_mul, Complex.norm_of_nonneg ht.le]
    have hABnonneg : (0:ℝ) ≤ ((stieltjesVec v ω1).im / ω1.im) * ((stieltjesVec v ω2).im / ω2.im) :=
      mul_nonneg (div_nonneg hSV1pos.le hω1pos.le) (div_nonneg hSV2pos.le hω2pos.le)
    have expand :
        Real.sqrt (t * (stieltjesVec v ω1).im * (t * (stieltjesVec v ω2).im)) =
          t * (Real.sqrt ((stieltjesVec v ω1).im / ω1.im) * Real.sqrt ((stieltjesVec v ω2).im / ω2.im)) *
            Real.sqrt (ω1.im * ω2.im) := by
      rw [show t * (stieltjesVec v ω1).im * (t * (stieltjesVec v ω2).im) =
          t ^ 2 * (((stieltjesVec v ω1).im / ω1.im) * ((stieltjesVec v ω2).im / ω2.im)) *
            (ω1.im * ω2.im) by field_simp]
      rw [Real.sqrt_mul (mul_nonneg (sq_nonneg t) hABnonneg),
        Real.sqrt_mul (sq_nonneg t),
        Real.sqrt_mul (div_nonneg hSV1pos.le hω1pos.le),
        Real.sqrt_sq ht.le]
    rw [hY1, hY2, hTeq]
    calc t * ‖stieltjesVec v ω1 - stieltjesVec v ω2‖ * Real.sqrt (ω1.im * ω2.im)
        = (t * Real.sqrt (ω1.im * ω2.im)) * ‖stieltjesVec v ω1 - stieltjesVec v ω2‖ := by ring
      _ ≤ (t * Real.sqrt (ω1.im * ω2.im)) *
            (‖ω1 - ω2‖ * Real.sqrt ((stieltjesVec v ω1).im / ω1.im) *
              Real.sqrt ((stieltjesVec v ω2).im / ω2.im)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ‖ω1 - ω2‖ * (t * (Real.sqrt ((stieltjesVec v ω1).im / ω1.im) *
            Real.sqrt ((stieltjesVec v ω2).im / ω2.im)) * Real.sqrt (ω1.im * ω2.im)) := by ring
      _ = ‖ω1 - ω2‖ * Real.sqrt (t * (stieltjesVec v ω1).im * (t * (stieltjesVec v ω2).im)) := by
          rw [← expand]
  -- Contraction of the shifted pseudo-hyperbolic quantity.
  have hLemB : ∀ ω ∈ K, ω.im - η ≤ κ * ω.im := by
    intro ω hωmem
    obtain ⟨hωa, hωb, hωc⟩ := hωmem
    have hy_le : ω.im - η ≤ t / η := by linarith
    have h1mκ_pos : 0 < 1 - κ := by linarith [hκlt1]
    have hmul : (ω.im - η) * (1 - κ) ≤ (t / η) * (1 - κ) :=
      mul_le_mul_of_nonneg_right hy_le h1mκ_pos.le
    have hidentity : (t / η) * (1 - κ) = κ * η := by
      rw [hκ_def]; field_simp; ring
    rw [hidentity] at hmul
    nlinarith [hmul]
  have hcontract : ∀ ω1 ∈ K, ∀ ω2 ∈ K,
      ‖T ω1 - T ω2‖ * Real.sqrt ((ω1.im - η) * (ω2.im - η)) ≤
        κ * ‖ω1 - ω2‖ * Real.sqrt (((T ω1).im - η) * ((T ω2).im - η)) := by
    intro ω1 hω1mem ω2 hω2mem
    obtain ⟨hω1a, hω1b, hω1c⟩ := hω1mem
    obtain ⟨hω2a, hω2b, hω2c⟩ := hω2mem
    have hω1pos : 0 < ω1.im := by linarith [hεpos]
    have hω2pos : 0 < ω2.im := by linarith [hεpos]
    have hy1nonneg : (0:ℝ) ≤ ω1.im - η := by linarith
    have hy2nonneg : (0:ℝ) ≤ ω2.im - η := by linarith
    have hB1 : ω1.im - η ≤ κ * ω1.im := hLemB ω1 ⟨hω1a, hω1b, hω1c⟩
    have hB2 : ω2.im - η ≤ κ * ω2.im := hLemB ω2 ⟨hω2a, hω2b, hω2c⟩
    have hprodle : (ω1.im - η) * (ω2.im - η) ≤ κ ^ 2 * (ω1.im * ω2.im) := by
      have h1 : (ω1.im - η) * (ω2.im - η) ≤ (κ * ω1.im) * (κ * ω2.im) := by
        apply mul_le_mul hB1 hB2 hy2nonneg (by positivity)
      nlinarith [h1]
    have hsqrt_le : Real.sqrt ((ω1.im - η) * (ω2.im - η)) ≤ κ * Real.sqrt (ω1.im * ω2.im) := by
      rw [show κ * Real.sqrt (ω1.im * ω2.im) = Real.sqrt (κ ^ 2 * (ω1.im * ω2.im)) by
        rw [Real.sqrt_mul (sq_nonneg κ), Real.sqrt_sq hκnonneg]]
      exact Real.sqrt_le_sqrt hprodle
    have hTnorm_nonneg : (0:ℝ) ≤ ‖T ω1 - T ω2‖ := norm_nonneg _
    calc ‖T ω1 - T ω2‖ * Real.sqrt ((ω1.im - η) * (ω2.im - η))
        ≤ ‖T ω1 - T ω2‖ * (κ * Real.sqrt (ω1.im * ω2.im)) :=
          mul_le_mul_of_nonneg_left hsqrt_le hTnorm_nonneg
      _ = κ * (‖T ω1 - T ω2‖ * Real.sqrt (ω1.im * ω2.im)) := by ring
      _ ≤ κ * (‖ω1 - ω2‖ * Real.sqrt (((T ω1).im - η) * ((T ω2).im - η))) :=
          mul_le_mul_of_nonneg_left (hLemA ω1 ⟨hω1a, hω1b, hω1c⟩ ω2 ⟨hω2a, hω2b, hω2c⟩) hκnonneg
      _ = κ * ‖ω1 - ω2‖ * Real.sqrt (((T ω1).im - η) * ((T ω2).im - η)) := by ring
  -- Build the iterate sequence in `K` and show its increments decay geometrically.
  have hω0mem : z + Complex.I * ((t / η : ℝ) : ℂ) ∈ K := by
    have him : (z + Complex.I * ((t / η : ℝ) : ℂ)).im = η + t / η := by
      simp [Complex.add_im, Complex.mul_im, hη_def]
    have hnorm : ‖z + Complex.I * ((t / η : ℝ) : ℂ) - z‖ = t / η := by
      have : z + Complex.I * ((t / η : ℝ) : ℂ) - z = Complex.I * ((t / η : ℝ) : ℂ) := by ring
      rw [this, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg (by positivity)]
    refine ⟨?_, ?_, ?_⟩
    · rw [him]; linarith [hεle]
    · rw [him]
    · rw [hnorm]
  set ωseq : ℕ → ℂ := fun k => T^[k] (z + Complex.I * ((t / η : ℝ) : ℂ)) with hωseq_def
  have hωmem : ∀ k, ωseq k ∈ K := by
    intro k
    induction k with
    | zero => simpa [hωseq_def] using hω0mem
    | succ k ih =>
      have hstepeq : ωseq (k + 1) = T (ωseq k) := by
        simp [hωseq_def, Function.iterate_succ_apply']
      rw [hstepeq]
      exact hself (ωseq k) ih
  have hYlo : ∀ k, ε ≤ (ωseq k).im - η := by
    intro k; obtain ⟨h1, _, _⟩ := hωmem k; linarith
  have hYhi : ∀ k, (ωseq k).im - η ≤ t / η := by
    intro k; obtain ⟨_, h2, _⟩ := hωmem k; linarith
  set S : ℕ → ℝ := fun k => Real.sqrt (((ωseq k).im - η) * ((ωseq (k + 1)).im - η)) with hS_def
  set N : ℕ → ℝ := fun k => ‖ωseq (k + 1) - ωseq k‖ with hN_def
  set D : ℕ → ℝ := fun k => N k / S k with hD_def
  have hSpos : ∀ k, 0 < S k := by
    intro k
    rw [hS_def]
    exact Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hεpos (hYlo k))
      (lt_of_lt_of_le hεpos (hYlo (k + 1))))
  have hSle : ∀ k, S k ≤ t / η := by
    intro k
    rw [hS_def]
    have h1 : (0:ℝ) ≤ (ωseq k).im - η := le_trans hεpos.le (hYlo k)
    calc Real.sqrt (((ωseq k).im - η) * ((ωseq (k + 1)).im - η))
        ≤ Real.sqrt ((t / η) * (t / η)) :=
          Real.sqrt_le_sqrt (mul_le_mul (hYhi k) (hYhi (k + 1)) (le_trans hεpos.le (hYlo (k+1))) (by positivity))
      _ = t / η := Real.sqrt_mul_self (by positivity)
  have hstepT : ∀ k, T (ωseq k) = ωseq (k + 1) := by
    intro k; rw [hωseq_def]; simp [Function.iterate_succ_apply']
  have hstepineq : ∀ k, N (k + 1) * S k ≤ κ * N k * S (k + 1) := by
    intro k
    have hc := hcontract (ωseq k) (hωmem k) (ωseq (k + 1)) (hωmem (k + 1))
    rw [hstepT k, hstepT (k + 1), norm_sub_rev (ωseq (k + 1)) (ωseq (k + 2)),
      norm_sub_rev (ωseq k) (ωseq (k + 1))] at hc
    exact hc
  have hDstep : ∀ k, D (k + 1) ≤ κ * D k := by
    intro k
    have hs := hstepineq k
    have h1 : D (k + 1) = N (k + 1) / S (k + 1) := rfl
    have h2 : D k = N k / S k := rfl
    rw [h1, h2, div_le_iff₀ (hSpos (k + 1)), mul_comm κ (N k / S k), mul_assoc,
      div_mul_eq_mul_div, le_div_iff₀ (hSpos k)]
    nlinarith [hs]
  have hDnonneg : ∀ k, 0 ≤ D k := by
    intro k; rw [hD_def]; exact div_nonneg (norm_nonneg _) (hSpos k).le
  have hDdecay : ∀ k, D k ≤ κ ^ k * D 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc D (k + 1) ≤ κ * D k := hDstep k
        _ ≤ κ * (κ ^ k * D 0) := mul_le_mul_of_nonneg_left ih hκnonneg
        _ = κ ^ (k + 1) * D 0 := by ring
  have hNbound : ∀ k, N k ≤ (D 0 * (t / η)) * κ ^ k := by
    intro k
    have h1 : N k = D k * S k := by
      rw [hD_def]; field_simp [(hSpos k).ne']
    rw [h1]
    calc D k * S k ≤ (κ ^ k * D 0) * S k :=
          mul_le_mul_of_nonneg_right (hDdecay k) (hSpos k).le
      _ ≤ (κ ^ k * D 0) * (t / η) :=
          mul_le_mul_of_nonneg_left (hSle k) (by positivity)
      _ = D 0 * (t / η) * κ ^ k := by ring
  -- The iterates form a Cauchy sequence.
  have hCauchy : CauchySeq ωseq := by
    apply cauchySeq_of_le_geometric κ (D 0 * (t / η)) hκlt1
    intro k
    have : dist (ωseq k) (ωseq (k + 1)) = N k := by
      rw [hN_def, dist_eq_norm]; exact norm_sub_rev _ _
    rw [this]
    exact hNbound k
  obtain ⟨ωlim, hTendsto⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hIm_tendsto : Filter.Tendsto (fun k => (ωseq k).im) Filter.atTop (𝓝 ωlim.im) :=
    (Complex.continuous_im.tendsto ωlim).comp hTendsto
  have hIm_lo : η + ε ≤ ωlim.im := ge_of_tendsto' hIm_tendsto (fun k => (hωmem k).1)
  have hIm_hi : ωlim.im ≤ η + t / η := le_of_tendsto' hIm_tendsto (fun k => (hωmem k).2.1)
  have hnorm_tendsto : Filter.Tendsto (fun k => ‖ωseq k - z‖) Filter.atTop (𝓝 ‖ωlim - z‖) := by
    have hsub : Filter.Tendsto (fun k => ωseq k - z) Filter.atTop (𝓝 (ωlim - z)) :=
      (Continuous.tendsto (continuous_id.sub continuous_const) ωlim).comp hTendsto
    exact (continuous_norm.tendsto (ωlim - z)).comp hsub
  have hnorm_le : ‖ωlim - z‖ ≤ t / η := le_of_tendsto' hnorm_tendsto (fun k => (hωmem k).2.2)
  have hωlimK : ωlim ∈ K := ⟨hIm_lo, hIm_hi, hnorm_le⟩
  have hωlim_im_pos : 0 < ωlim.im := by linarith [hεpos]
  have hne_lim : ∀ i : n, (v i : ℂ) - ωlim ≠ 0 := fun i => freeConv_sub_ne_zero hωlim_im_pos.ne'
  have hterm : ∀ i : n, Filter.Tendsto (fun k => ((v i : ℂ) - ωseq k)⁻¹) Filter.atTop
      (𝓝 (((v i : ℂ) - ωlim)⁻¹)) := by
    intro i
    have hsub : Filter.Tendsto (fun k => (v i : ℂ) - ωseq k) Filter.atTop (𝓝 ((v i : ℂ) - ωlim)) :=
      (Continuous.tendsto (continuous_const.sub continuous_id) ωlim).comp hTendsto
    exact hsub.inv₀ (hne_lim i)
  have hSV_tendsto : Filter.Tendsto (fun k => stieltjesVec v (ωseq k)) Filter.atTop
      (𝓝 (stieltjesVec v ωlim)) := by
    have hsum : Filter.Tendsto (fun k => ∑ i, ((v i : ℂ) - ωseq k)⁻¹) Filter.atTop
        (𝓝 (∑ i, ((v i : ℂ) - ωlim)⁻¹)) := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
    have hmul : Filter.Tendsto
        (fun k => ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - ωseq k)⁻¹) Filter.atTop
        (𝓝 (((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - ωlim)⁻¹)) :=
      (Continuous.tendsto (continuous_const.mul continuous_id)
        (∑ i, ((v i : ℂ) - ωlim)⁻¹)).comp hsum
    simpa [stieltjesVec] using hmul
  have hT_tendsto : Filter.Tendsto (fun k => T (ωseq k)) Filter.atTop (𝓝 (T ωlim)) := by
    have hg : Continuous (fun w : ℂ => z + (t : ℂ) * w) :=
      continuous_const.add (continuous_const.mul continuous_id)
    have := (hg.tendsto (stieltjesVec v ωlim)).comp hSV_tendsto
    simpa [hT_def, Function.comp_def] using this
  have hshift_tendsto : Filter.Tendsto (fun k => ωseq (k + 1)) Filter.atTop (𝓝 ωlim) :=
    hTendsto.comp (tendsto_add_atTop_nat 1)
  have hTfix : T ωlim = ωlim := by
    have heq : (fun k => T (ωseq k)) = (fun k => ωseq (k + 1)) := funext hstepT
    rw [heq] at hT_tendsto
    exact tendsto_nhds_unique hT_tendsto hshift_tendsto
  refine ⟨stieltjesVec v ωlim, freeConv_stieltjesVec_im_pos v hωlim_im_pos, ?_⟩
  have hz_eq : z + (t : ℂ) * stieltjesVec v ωlim = ωlim := by
    have hTωlim : T ωlim = z + (t : ℂ) * stieltjesVec v ωlim := by rw [hT_def]
    rw [← hTωlim]; exact hTfix
  have hshift := freeConv_stieltjesVec_shift v z (t : ℂ) (stieltjesVec v ωlim)
  rw [hz_eq] at hshift
  exact hshift

/-! ### Main theorem -/

theorem freeConv_existsUnique {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    ∃! m : ℂ, 0 < m.im ∧
      m = ((Fintype.card n : ℕ) : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m)⁻¹ := by
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · refine ⟨stieltjesVec v z, ⟨freeConv_stieltjesVec_im_pos v hz, ?_⟩, ?_⟩
    · rw [← ht0]; simp [stieltjesVec]
    · rintro m ⟨hm_im, hm_eq⟩
      rw [← ht0] at hm_eq
      simpa [stieltjesVec] using hm_eq
  · obtain ⟨m, hm_im, hm_eq⟩ := freeConv_exists_pos v ht0 hz
    refine ⟨m, ⟨hm_im, hm_eq⟩, ?_⟩
    rintro m' ⟨hm'_im, hm'_eq⟩
    exact freeConv_uniqueness_pos v ht0 hz hm'_im hm_im hm'_eq hm_eq

/-- The Stieltjes transform of the free convolution `v ⊞ sc_t` (the unique root from
`freeConv_existsUnique`), for `t ≥ 0`. Junk (`0`) off `{0 ≤ t} ∩ {0 < z.im}`. -/
noncomputable def freeConvST {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) (t : ℝ) : ℂ → ℂ :=
  fun z => if h : 0 ≤ t ∧ 0 < z.im then (freeConv_existsUnique v h.1 h.2).choose else 0

/-- **[51, (2.5)]** for `freeConvST`. -/
theorem isFreeConv51_freeConvST {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) {t : ℝ}
    (ht : 0 ≤ t) : IsFreeConv51 v t (freeConvST v t) := by
  intro z hz
  unfold freeConvST
  rw [dif_pos (⟨ht, hz⟩ : 0 ≤ t ∧ 0 < z.im)]
  exact (freeConv_existsUnique v ht hz).choose_spec.1

end RBM.Gauss
