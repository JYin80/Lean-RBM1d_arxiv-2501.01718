/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GreenSpectralL1
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Bulk/tail control of the weighted spectral factor

This file proves the finite-Hermitian deterministic beta-factor bound used with the accepted
spectral expansion in `GreenSpectralL1`. Delocalization is assumed only for eigenvalues in the
fixed bulk interval. Eigenvectors in its complement are controlled by completeness and spectral
separation. The second-moment form is also deterministic. No stochastic OU estimate or claim of
(2.29) is made here.
-/

namespace RBM

open Matrix Finset

section GreenSpectralBulkFactor

variable {L W : ℕ} [NeZero L] [NeZero W]
variable {Hm : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
variable (hH : Hm.IsHermitian)

local notation "Idx" => (ZMod L × Fin W)

/-- The fixed half-margin bulk interval `[-2 + κ/2, 2 - κ/2]`. -/
def spectralBulkInterval (κ x : ℝ) : Prop := -2 + κ / 2 ≤ x ∧ x ≤ 2 - κ / 2

/-- Distance from an eigenvalue to the complex spectral parameter. -/
noncomputable def spectralDistance (z : ℂ) (β : Idx) : ℝ :=
  ‖(hH.eigenvalues β : ℂ) - z‖

/-- The full first pole sum `P₁ = ∑β |λβ-z|⁻¹`. -/
noncomputable def spectralP1 (z : ℂ) : ℝ :=
  ∑ β : Idx, ‖spectralPole hH z β‖

/-- The normalized second spectral moment `R_z² = N⁻¹ ∑β |λβ-z|²`. -/
noncomputable def spectralSecondMoment (z : ℂ) : ℝ :=
  Real.sqrt ((L * W : ℝ)⁻¹ *
    ∑ β : Idx, spectralDistance hH z β ^ 2)

private theorem card_idx_real :
    (∑ _ : Idx, (1 : ℝ)) = (L * W : ℝ) := by
  simp [Fintype.card_prod]

private theorem size_pos : 0 < (L * W : ℝ) := by
  exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos W)

private theorem spectralDistance_pos {z : ℂ} (hη : 0 < z.im) (β : Idx) :
    0 < spectralDistance hH z β := by
  have him : |((hH.eigenvalues β : ℂ) - z).im| ≤
      spectralDistance hH z β := by
    simpa [spectralDistance, Complex.sub_im, abs_neg] using
      (Complex.abs_im_le_norm ((hH.eigenvalues β : ℂ) - z))
  have him' : z.im ≤ spectralDistance hH z β := by
    simpa [abs_of_pos hη] using him
  exact lt_of_lt_of_le hη him'

private theorem spectralPole_norm_eq_inv_distance {z : ℂ} (hη : 0 < z.im)
    (β : Idx) :
    ‖spectralPole hH z β‖ = (spectralDistance hH z β)⁻¹ := by
  simp [spectralPole, spectralDistance, norm_inv]

private theorem spectralGsigPole_norm_eq_inv_distance {z : ℂ} (hη : 0 < z.im)
    (σ : Bool) (β : Idx) :
    ‖spectralGsigPole hH z σ β‖ = (spectralDistance hH z β)⁻¹ := by
  cases σ
  · change ‖(((hH.eigenvalues β : ℂ) - (starRingEnd ℂ) z)⁻¹)‖ =
      ‖(hH.eigenvalues β : ℂ) - z‖⁻¹
    rw [norm_inv]
    have hconj : ((hH.eigenvalues β : ℂ) - (starRingEnd ℂ) z) =
        star ((hH.eigenvalues β : ℂ) - z) := by simp
    have hnorm : ‖(hH.eigenvalues β : ℂ) - (starRingEnd ℂ) z‖ =
        ‖(hH.eigenvalues β : ℂ) - z‖ := by
      calc
        _ = ‖star ((hH.eigenvalues β : ℂ) - z)‖ := by rw [hconj]
        _ = _ := norm_star _
    rw [hnorm]
  · exact spectralPole_norm_eq_inv_distance hH hη β

private theorem spectralDistance_re_ge_of_outside {κ E : ℝ} {z : ℂ}
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hz : |z.re - E| ≤ κ / 4)
    (β : Idx) (hout : ¬ spectralBulkInterval κ (hH.eigenvalues β)) :
    κ / 4 ≤ |hH.eigenvalues β - z.re| := by
  have hElo : -2 + κ ≤ E := by
    have := (abs_le.mp hE).1
    linarith
  have hEhi : E ≤ 2 - κ := by
    exact (abs_le.mp hE).2
  have hzlo : E - κ / 4 ≤ z.re := by
    have := (abs_le.mp hz).1
    linarith
  have hzhi : z.re ≤ E + κ / 4 := by
    have := (abs_le.mp hz).2
    linarith
  have hout' : hH.eigenvalues β < -2 + κ / 2 ∨
      2 - κ / 2 < hH.eigenvalues β := by
    by_cases hlo : hH.eigenvalues β < -2 + κ / 2
    · exact Or.inl hlo
    · right
      by_contra hhi
      apply hout
      exact ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩
  rcases hout' with hlo | hhi
  · have hgap : κ / 4 ≤ z.re - hH.eigenvalues β := by linarith
    simpa [abs_of_nonpos (by linarith : hH.eigenvalues β - z.re ≤ 0)] using hgap
  · have hgap : κ / 4 ≤ hH.eigenvalues β - z.re := by linarith
    simpa [abs_of_nonneg (by linarith : 0 ≤ hH.eigenvalues β - z.re)] using hgap

private theorem pole_norm_le_inv_margin {κ E : ℝ} {z : ℂ} (hη : 0 < z.im)
    (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (hz : |z.re - E| ≤ κ / 4)
    (σ : Bool) (β : Idx) (hout :
      ¬ spectralBulkInterval κ (hH.eigenvalues β)) :
    ‖spectralGsigPole hH z σ β‖ ≤ (κ / 4)⁻¹ := by
  have hgap := spectralDistance_re_ge_of_outside hH hκ hE hz β hout
  have hden : κ / 4 ≤ ‖(hH.eigenvalues β : ℂ) -
      (if σ then z else (starRingEnd ℂ) z)‖ := by
    calc
      κ / 4 ≤ |hH.eigenvalues β - z.re| := hgap
      _ = |(((hH.eigenvalues β : ℂ) -
          (if σ then z else (starRingEnd ℂ) z)).re)| := by
            cases σ <;> simp [Complex.sub_re]
      _ ≤ _ := Complex.abs_re_le_norm _
  have hδ : 0 < κ / 4 := by positivity
  have hdenpos : 0 < ‖(hH.eigenvalues β : ℂ) -
      (if σ then z else (starRingEnd ℂ) z)‖ := lt_of_lt_of_le hδ hden
  rw [spectralGsigPole, spectralPole, norm_inv]
  exact (inv_le_inv₀ hdenpos hδ).2 hden

private theorem eigenmass_sum (y : Idx) :
    (∑ β : Idx, (Complex.normSq (hH.eigenvectorBasis β y) : ℝ)) = 1 := by
  simpa [Complex.normSq_eq_norm_sq] using sum_sq_norm_eigenvectorBasis hH y

/-- The paper's fixed `C₀/N` spectral window gives the required half-margin separation once
`N = L W` is large enough that `C₀/N ≤ κ/4`. -/
theorem spectral_parameter_half_margin_of_paper_window
    (E κ C0 : ℝ) {z : ℂ}
    (hwindow : |z.re - E| ≤ C0 / (L * W : ℝ))
    (hlarge : C0 / (L * W : ℝ) ≤ κ / 4) :
    |z.re - E| ≤ κ / 4 := hwindow.trans hlarge

/-- Additive bulk/tail estimate for the weighted beta sum. The bulk eigenvector bound is needed
only on `J`; the complementary eigenvectors enter through sitewise eigenmass completeness. -/
theorem weighted_spectral_beta_additive_bound
    (hL : 3 ≤ L) (κ E D : ℝ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hD : 0 ≤ D) {z : ℂ} (hη : 0 < z.im)
    (hz : |z.re - E| ≤ κ / 4) (σ : Bool) (y : Idx)
    (hbulk : ∀ β : Idx, spectralBulkInterval κ (hH.eigenvalues β) →
      (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) ≤ D / (L * W : ℝ)) :
    (∑ β : Idx, ‖spectralGsigPole hH z σ β‖ *
        (Complex.normSq (hH.eigenvectorBasis β y) : ℝ)) ≤
      D / (L * W : ℝ) * spectralP1 hH z + (κ / 4)⁻¹ := by
  classical
  have hN : 0 < (L * W : ℝ) := size_pos (L := L) (W := W)
  have hNne : (L * W : ℝ) ≠ 0 := ne_of_gt hN
  have hDN : 0 ≤ D / (L * W : ℝ) := div_nonneg hD hN.le
  have hdelta : 0 < κ / 4 := by positivity
  have hmass : ∀ β : Idx, 0 ≤
      (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) := by
    intro β
    exact Complex.normSq_nonneg _
  have hpole : ∀ β : Idx, 0 ≤ ‖spectralGsigPole hH z σ β‖ :=
    fun β => norm_nonneg _
  have hP1 : spectralP1 hH z =
      ∑ β : Idx, (spectralDistance hH z β)⁻¹ := by
    simp [spectralP1, spectralPole_norm_eq_inv_distance hH hη]
  let bulk : Idx → Prop := fun β => spectralBulkInterval κ (hH.eigenvalues β)
  have hbulkterm (β : Idx) :
      (if bulk β then ‖spectralGsigPole hH z σ β‖ *
          (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) else 0) ≤
        D / (L * W : ℝ) * ‖spectralGsigPole hH z σ β‖ := by
    by_cases hb : bulk β
    · simp only [hb, ↓reduceIte]
      calc
        ‖spectralGsigPole hH z σ β‖ *
            (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) ≤
          ‖spectralGsigPole hH z σ β‖ * (D / (L * W : ℝ)) :=
            mul_le_mul_of_nonneg_left (hbulk β hb) (hpole β)
        _ = D / (L * W : ℝ) * ‖spectralGsigPole hH z σ β‖ := by ring
    · simp [hb]
      exact mul_nonneg hDN (hpole β)
  have htailterm (β : Idx) :
      (if bulk β then 0 else ‖spectralGsigPole hH z σ β‖ *
          (Complex.normSq (hH.eigenvectorBasis β y) : ℝ)) ≤
        (κ / 4)⁻¹ * (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) := by
    by_cases hb : bulk β
    · simp [hb]
      exact mul_nonneg (by positivity) (hmass β)
    · simp only [hb, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right
        (pole_norm_le_inv_margin hH hη hκ hE hz σ β hb) (hmass β)
  have hsplit :
      (∑ β : Idx, ‖spectralGsigPole hH z σ β‖ *
          (Complex.normSq (hH.eigenvectorBasis β y) : ℝ)) =
        (∑ β : Idx, if bulk β then ‖spectralGsigPole hH z σ β‖ *
          (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) else 0) +
        (∑ β : Idx, if bulk β then 0 else ‖spectralGsigPole hH z σ β‖ *
          (Complex.normSq (hH.eigenvectorBasis β y) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro β hβ
    by_cases hb : bulk β <;> simp [hb]
  calc
    _ = _ := hsplit
    _ ≤ (∑ β : Idx, D / (L * W : ℝ) *
          ‖spectralGsigPole hH z σ β‖) +
        ∑ β : Idx, (κ / 4)⁻¹ *
          (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) := by
      exact add_le_add
        (Finset.sum_le_sum fun β hβ => hbulkterm β)
        (Finset.sum_le_sum fun β hβ => htailterm β)
    _ = D / (L * W : ℝ) * spectralP1 hH z + (κ / 4)⁻¹ := by
      have hPσ : (∑ β : Idx, ‖spectralGsigPole hH z σ β‖) = spectralP1 hH z := by
        rw [hP1]
        refine Finset.sum_congr rfl fun β _ => ?_
        exact spectralGsigPole_norm_eq_inv_distance hH hη σ β
      rw [← Finset.mul_sum, hPσ, ← Finset.mul_sum, eigenmass_sum hH y]
      ring

/-- The actual second spectral moment is positive whenever `Im z > 0`; in particular the relative
form never divides by a zero moment. -/
theorem spectralSecondMoment_pos {z : ℂ} (hη : 0 < z.im) :
    0 < spectralSecondMoment hH z := by
  have hN : 0 < (L * W : ℝ) := size_pos (L := L) (W := W)
  have hβ : Idx := (0, ⟨0, NeZero.pos W⟩)
  have hSterm : 0 < spectralDistance hH z hβ ^ 2 :=
    sq_pos_of_pos (spectralDistance_pos hH hη hβ)
  have hS : 0 < ∑ β : Idx, spectralDistance hH z β ^ 2 := by
    exact lt_of_lt_of_le hSterm
      (Finset.single_le_sum (fun β hβ => sq_nonneg _) (Finset.mem_univ hβ))
  unfold spectralSecondMoment
  exact Real.sqrt_pos.2 (mul_pos (inv_pos.mpr hN) hS)

private theorem p1_mul_secondMoment_ge_size {z : ℂ} (hη : 0 < z.im) :
    (L * W : ℝ) ≤ spectralP1 hH z * spectralSecondMoment hH z := by
  let d : Idx → ℝ := fun β => spectralDistance hH z β
  let n : ℝ := (L * W : ℝ)
  let s : ℝ := ∑ β : Idx, d β ^ 2
  let t : ℝ := ∑ β : Idx, d β
  let r : ℝ := spectralSecondMoment hH z
  have hn : 0 < n := by dsimp [n]; exact size_pos (L := L) (W := W)
  have hncard : (∑ _ : Idx, (1 : ℝ)) = n := by
    dsimp [n]
    exact card_idx_real (L := L) (W := W)
  have hdpos (β : Idx) : 0 < d β := by
    exact spectralDistance_pos hH hη β
  have hdsum : 0 < t := by
    have hβ : Idx := (0, ⟨0, NeZero.pos W⟩)
    exact lt_of_lt_of_le (hdpos hβ) (Finset.single_le_sum
      (fun β hβ => (hdpos β).le) (Finset.mem_univ hβ))
  have hssum : 0 < s := by
    have hβ : Idx := (0, ⟨0, NeZero.pos W⟩)
    exact lt_of_lt_of_le (sq_pos_of_pos (hdpos hβ)) (Finset.single_le_sum
      (fun β hβ => sq_nonneg _) (Finset.mem_univ hβ))
  have hRpos : 0 < r := by
    have hSpos : 0 < ∑ β : Idx, spectralDistance hH z β ^ 2 := by
      simpa [s, d] using hssum
    dsimp [r, spectralSecondMoment]
    exact Real.sqrt_pos.2 (mul_pos (inv_pos.mpr hn) hSpos)
  have hRdef : r ^ 2 = n⁻¹ * s := by
    dsimp [r, spectralSecondMoment, s, d, n]
    rw [Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr hn.le) (Finset.sum_nonneg fun β _ => sq_nonneg _))]
  have hcs : t ^ 2 ≤ s * n := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
      (f := d) (g := fun _ : Idx => (1 : ℝ))
    simpa [t, s, pow_two, hncard, mul_comm] using this
  have hTle : t ≤ n * r := by
    apply (sq_le_sq₀ hdsum.le (mul_nonneg hn.le hRpos.le)).1
    rw [mul_pow, hRdef]
    calc
      t ^ 2 ≤ s * n := hcs
      _ = n ^ 2 * (n⁻¹ * s) := by field_simp [ne_of_gt hn]
  have hTitu : (∑ β : Idx, (1 : ℝ)) ^ 2 / t ≤
      ∑ β : Idx, (1 : ℝ) ^ 2 / d β := by
    exact Finset.sq_sum_div_le_sum_sq_div Finset.univ
      (f := fun _ : Idx => (1 : ℝ)) (fun β _ => hdpos β)
  have hP1_eq : spectralP1 hH z = ∑ β : Idx, (d β)⁻¹ := by
    simp [spectralP1, spectralPole_norm_eq_inv_distance hH hη, d]
  have hPmul : n ^ 2 ≤ spectralP1 hH z * t := by
    rw [hncard] at hTitu
    have hh := (div_le_iff₀ hdsum).1 hTitu
    calc
      n ^ 2 ≤ t * ∑ β : Idx, (d β)⁻¹ := by
        have hh' : n ^ 2 ≤ (∑ β : Idx, (d β)⁻¹) * t := by
          simpa [d, one_pow, div_eq_mul_inv] using hh
        nlinarith [hh']
      _ = spectralP1 hH z * t := by rw [← hP1_eq]; ring
  calc
    n = (n ^ 2) / n := by field_simp [ne_of_gt hn]
    _ ≤ (spectralP1 hH z * t) / n := by
      exact div_le_div_of_nonneg_right hPmul hn.le
    _ ≤ (spectralP1 hH z * (n * r)) / n := by
      have hPnonneg : 0 ≤ spectralP1 hH z :=
        Finset.sum_nonneg fun β _ => norm_nonneg _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTle hPnonneg) hn.le
    _ = spectralP1 hH z * r := by field_simp [ne_of_gt hn]

/-- Relative second-moment form `Q_y ≤ (D + R_z/δ) P₁/N`. The proof derives
`P₁/N ≥ 1/R_z` by Titu's inequality and Cauchy--Schwarz from the actual finite eigenvalue list. -/
theorem weighted_spectral_beta_relative_bound
    (hL : 3 ≤ L) (κ E D : ℝ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hD : 0 ≤ D) {z : ℂ} (hη : 0 < z.im)
    (hz : |z.re - E| ≤ κ / 4) (σ : Bool) (y : Idx)
    (hbulk : ∀ β : Idx, spectralBulkInterval κ (hH.eigenvalues β) →
      (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) ≤ D / (L * W : ℝ)) :
    (∑ β : Idx, ‖spectralGsigPole hH z σ β‖ *
        (Complex.normSq (hH.eigenvectorBasis β y) : ℝ)) ≤
      (D + spectralSecondMoment hH z / (κ / 4)) *
        (spectralP1 hH z / (L * W : ℝ)) := by
  have hN : 0 < (L * W : ℝ) := size_pos (L := L) (W := W)
  have hδ : 0 < κ / 4 := by positivity
  have hR : 0 < spectralSecondMoment hH z := spectralSecondMoment_pos hH hη
  have hPR := p1_mul_secondMoment_ge_size hH hη
  have hPoverR : 1 / spectralSecondMoment hH z ≤
      spectralP1 hH z / (L * W : ℝ) := by
    apply (div_le_div_iff₀ hR hN).2
    simpa using hPR
  have hadd := weighted_spectral_beta_additive_bound hH hL κ E D hκ hE hD hη hz σ y hbulk
  have htail : (κ / 4)⁻¹ ≤
      (spectralSecondMoment hH z / (κ / 4)) *
        (spectralP1 hH z / (L * W : ℝ)) := by
    calc
      (κ / 4)⁻¹ = (1 / spectralSecondMoment hH z) *
          (spectralSecondMoment hH z / (κ / 4)) := by
            field_simp [ne_of_gt hR, ne_of_gt hδ]
      _ ≤ (spectralP1 hH z / (L * W : ℝ)) *
          (spectralSecondMoment hH z / (κ / 4)) :=
            mul_le_mul_of_nonneg_right hPoverR (div_nonneg hR.le hδ.le)
      _ = _ := by ring
  have hfirst : D / (L * W : ℝ) * spectralP1 hH z =
      D * (spectralP1 hH z / (L * W : ℝ)) := by
    field_simp [ne_of_gt hN]
  calc
    _ ≤ D / (L * W : ℝ) * spectralP1 hH z + (κ / 4)⁻¹ := hadd
    _ = D * (spectralP1 hH z / (L * W : ℝ)) + (κ / 4)⁻¹ := by rw [hfirst]
    _ ≤ D * (spectralP1 hH z / (L * W : ℝ)) +
        (spectralSecondMoment hH z / (κ / 4)) *
          (spectralP1 hH z / (L * W : ℝ)) := by
      simpa [add_comm] using add_le_add_right htail
        (D * (spectralP1 hH z / (L * W : ℝ)))
    _ = _ := by ring

/-- Deterministic composition of the accepted T1397/T1398 expansion with the additive bulk/tail
bound. Both resolvent signs are quantified independently by `σ₁` and `σ₂`. -/
theorem norm_green_spectral_bulk_tail_bound
    (hL : 3 ≤ L) (κ E D : ℝ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hD : 0 ≤ D) {z : ℂ} (hη : 0 < z.im)
    (hz : |z.re - E| ≤ κ / 4) (σ₁ σ₂ : Bool) (y : Idx)
    (hbulk : ∀ β : Idx, spectralBulkInterval κ (hH.eigenvalues β) →
      (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) ≤ D / (L * W : ℝ)) :
    ‖∑ x : Idx, (Gsig Hm z σ₁ ^ 2) x x *
        (Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹) * Gsig Hm z σ₂ y y‖ ≤
      (L * W : ℝ)⁻¹ *
        (∑ α : Idx, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 * ‖blockM hH y.1 α‖) *
        (D / (L * W : ℝ) * spectralP1 hH z + (κ / 4)⁻¹) := by
  have hT1397 := norm_green_spectral_identity_blockM_le hH hL y.1 y.2 z hη σ₁ σ₂
  have hQ := weighted_spectral_beta_additive_bound hH hL κ E D hκ hE hD hη hz σ₂ y hbulk
  exact hT1397.trans (mul_le_mul_of_nonneg_left hQ
    (mul_nonneg (inv_nonneg.mpr (size_pos (L := L) (W := W)).le)
      (Finset.sum_nonneg fun α _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))))

/-- Relative deterministic composition, retaining the full alpha factor from T1397. -/
theorem norm_green_spectral_bulk_tail_relative_bound
    (hL : 3 ≤ L) (κ E D : ℝ) (hκ : 0 < κ) (hE : |E| ≤ 2 - κ)
    (hD : 0 ≤ D) {z : ℂ} (hη : 0 < z.im)
    (hz : |z.re - E| ≤ κ / 4) (σ₁ σ₂ : Bool) (y : Idx)
    (hbulk : ∀ β : Idx, spectralBulkInterval κ (hH.eigenvalues β) →
      (Complex.normSq (hH.eigenvectorBasis β y) : ℝ) ≤ D / (L * W : ℝ)) :
    ‖∑ x : Idx, (Gsig Hm z σ₁ ^ 2) x x *
        (Svar L W x y - ((L * W : ℕ) : ℂ)⁻¹) * Gsig Hm z σ₂ y y‖ ≤
      (L * W : ℝ)⁻¹ *
        (∑ α : Idx, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 * ‖blockM hH y.1 α‖) *
        ((D + spectralSecondMoment hH z / (κ / 4)) *
          (spectralP1 hH z / (L * W : ℝ))) := by
  have hT1397 := norm_green_spectral_identity_blockM_le hH hL y.1 y.2 z hη σ₁ σ₂
  have hQ := weighted_spectral_beta_relative_bound hH hL κ E D hκ hE hD hη hz σ₂ y hbulk
  exact hT1397.trans (mul_le_mul_of_nonneg_left hQ
    (mul_nonneg (inv_nonneg.mpr (size_pos (L := L) (W := W)).le)
      (Finset.sum_nonneg fun α _ => mul_nonneg (sq_nonneg _) (norm_nonneg _))))

end GreenSpectralBulkFactor

end RBM

#print axioms RBM.weighted_spectral_beta_additive_bound
#print axioms RBM.spectral_parameter_half_margin_of_paper_window
#print axioms RBM.spectralSecondMoment_pos
#print axioms RBM.weighted_spectral_beta_relative_bound
#print axioms RBM.norm_green_spectral_bulk_tail_bound
#print axioms RBM.norm_green_spectral_bulk_tail_relative_bound
