/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.WardStep
import RBM1D.Loop.Ward
import RBM1D.Loop.Cyclic

/-!
# Ward's identity for `K` at every length (Lemma 3.6, (3.13))

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.6, (3.13): for any solution
`K` of Definition 2.12 with `m = m^{(E)}` on `[0, T₀]`, `T₀ < 1`, with bounded `2`-loops, and
every loop `(+, μ, -; a', x)`,
`∑_x K_{t,(+,μ,-),(a',x)} = (K_{t,(+,μ),a'} - K_{t,(-,μ),a'}) / (2 W i η_t)`.

The proof is the paper's: the defect `wD` satisfies the linear equation (3.18)
(`RBM.ward_rhs_identity` plus `∂_t κ_t = κ_t/(1-t)`, `W c_t = (1-t)⁻¹`) and vanishes at `t = 0`;
Grönwall and induction on the length.
-/

namespace RBM

open Finset LoopIdx

variable (L : ℕ) [NeZero L]

section Kappa

variable {E : ℝ}

/-- `κ_t = (2 W i η_t)⁻¹`. -/
noncomputable def wardKappa (W : ℕ) (E t : ℝ) : ℂ := (2 * W * Complex.I * etaT E t)⁻¹

theorem wardKappa_mul (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    wardKappa W E t * (mSigma E true - mSigma E false) = wardC W t := by
  rw [wardKappa, mSigma_true, mSigma_false, ← div_eq_inv_mul,
    show mE E - (starRingEnd ℂ) (mE E) = 1 * (mE E - (starRingEnd ℂ) (mE E)) by ring,
    sub_div_two_W_I_etaT W hE ht1, wardC, one_div]

theorem hasDerivAt_wardKappa (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    HasDerivAt (wardKappa W E) (wardKappa W E t / (1 - t)) t := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hIm : ((mE E).im : ℂ) ≠ 0 := by exact_mod_cast (mE_im_pos hE).ne'
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  have hg : HasDerivAt (fun s : ℝ => 2 * (W : ℂ) * Complex.I * (etaT E s : ℂ))
      (-(2 * (W : ℂ) * Complex.I * (mE E).im)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (etaT E s : ℂ)) (-((mE E).im : ℂ)) t := by
      have := (((hasDerivAt_id t).const_sub 1).mul_const (mE E).im).ofReal_comp
      simpa [etaT] using this
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1.const_mul (2 * (W : ℂ) * Complex.I)
  have hne : 2 * (W : ℂ) * Complex.I * (etaT E t : ℂ) ≠ 0 := by
    simp only [etaT]
    push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hW) Complex.I_ne_zero)
      (mul_ne_zero ht hIm)
  refine (hg.inv hne).congr_deriv ?_
  simp only [wardKappa, etaT]
  push_cast
  field_simp

end Kappa

section Init

/-- Summing the "all labels equal" indicator over the last label. -/
theorem sum_allEq_append (a' : List (ZMod L)) (ha : a' ≠ []) :
    ∑ x : ZMod L, (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then (1 : ℂ) else 0)
      = if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0 := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil ha
  have hh : h ∈ h :: t := List.mem_cons_self
  by_cases hall : ∀ y ∈ h :: t, ∀ z ∈ h :: t, y = z
  · rw [ite_eq_left hall]
    have key : ∀ x : ZMod L,
        (∀ y ∈ h :: t ++ [x], ∀ z ∈ h :: t ++ [x], y = z) ↔ x = h := by
      intro x
      constructor
      · intro hx
        exact hx x (List.mem_append_right _ (List.mem_singleton_self x)) h
          (List.mem_append_left _ hh)
      · intro hxh
        have hin : ∀ w ∈ h :: t ++ [x], w ∈ h :: t := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact hw
          · rw [List.mem_singleton.mp hw, hxh]
            exact hh
        exact fun y hy z hz => hall y (hin y hy) z (hin z hz)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [ite_eq_right hall]
    refine Finset.sum_eq_zero fun x _ => ite_eq_right fun hx => hall fun y hy z hz =>
      hx y (List.mem_append_left _ hy) z (List.mem_append_left _ hz)

/-- **The initial value.**  At `t = 0`, (3.13) holds for the initial value of Definition 2.12. -/
theorem wD_primInit (W : ℕ) [NeZero W] {E : ℝ} (hE : |E| < 2) (μ : List Bool)
    (a' : List (ZMod L)) (hμ : μ.length + 1 = a'.length) :
    wD L (primInit L W (mSigma E)) (wardKappa W E 0) μ a' = 0 := by
  have ha : a' ≠ [] := by
    intro h
    rw [h] at hμ
    simp at hμ
  obtain ⟨N, hN⟩ : ∃ N, a'.length = N + 1 := ⟨a'.length - 1, by omega⟩
  have hfull : ∀ x : ZMod L, primInit L W (mSigma E) (fullLoop μ a' x)
      = (W : ℂ)⁻¹ ^ (N + 1) * (mSigma E true * (μ.map (mSigma E)).prod * mSigma E false) *
        (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then 1 else 0) := by
    intro x
    simp only [primInit, fullLoop, LoopIdx.length, List.length_append, List.length_singleton,
      hN, Nat.add_sub_cancel, List.map_cons, List.map_append, List.map_nil, List.prod_cons,
      List.prod_append, List.prod_nil, mul_one, mul_assoc]
    rfl
  have hpm : ∀ s, primInit L W (mSigma E) (pmLoop s μ a')
      = (W : ℂ)⁻¹ ^ N * (mSigma E s * (μ.map (mSigma E)).prod) *
        (if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0) := by
    intro s
    simp only [primInit, pmLoop, LoopIdx.length, hN, Nat.add_sub_cancel, List.map_cons,
      List.prod_cons]
    rfl
  have hk := wardKappa_mul W hE (t := 0) (by norm_num)
  have hmm : mSigma E true * mSigma E false = 1 := mE_mul_conj hE.le
  simp only [wD, wStar, hfull, hpm, ← Finset.mul_sum, sum_allEq_append L a' ha]
  rw [wardC] at hk
  push_cast at hk
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  set P := (μ.map (mSigma E)).prod
  set I := (if ∀ y ∈ a', ∀ z ∈ a', y = z then (1 : ℂ) else 0)
  calc (W : ℂ)⁻¹ ^ (N + 1) * (mSigma E true * P * mSigma E false) * I
        - wardKappa W E 0 * ((W : ℂ)⁻¹ ^ N * (mSigma E true * P) * I
          - (W : ℂ)⁻¹ ^ N * (mSigma E false * P) * I)
      = (W : ℂ)⁻¹ ^ N * P * I * ((W : ℂ)⁻¹ * (mSigma E true * mSigma E false)
          - wardKappa W E 0 * (mSigma E true - mSigma E false)) := by ring
    _ = 0 := by rw [hmm, hk, sub_zero, mul_one, mul_one, sub_self, mul_zero]

end Init

end RBM
