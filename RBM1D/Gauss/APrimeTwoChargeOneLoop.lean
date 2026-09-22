/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EGDef
import RBM1D.Gauss.Model
import RBM1D.Gauss.DimsExample

/-!
# Centered block one-loops at both charges on one Gaussian sample

Conjugation of a Hermitian resolvent identifies the two centered block traces
at exactly the same spectral parameter, time, block, and sample.
-/

namespace RBM.APrimeTwoChargeOneLoop

open Matrix

theorem centered_block_trace_false_eq_conj_true (L W : ℕ) [NeZero L]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (hM : M.IsHermitian)
    (z : ℂ) (m : ℂ) (b : ZMod L) :
    Matrix.trace ((Gsig M z false - (starRingEnd ℂ) m •
        (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)
      = (starRingEnd ℂ) (Matrix.trace ((Gsig M z true - m •
        (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)) := by
  let A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
    Gsig M z true - m • 1
  have hA : Aᴴ = Gsig M z false - (starRingEnd ℂ) m • 1 := by
    simp only [A, Matrix.conjTranspose_sub, Gsig_conjTranspose hM,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rfl
  rw [← hA, ← Complex.star_def, ← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, Eblk_conjTranspose, Matrix.trace_mul_comm]

theorem gaussian_centered_oneLoop_false_norm_eq_true (d : Gauss.Dims)
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) (b : ZMod (d.L N)) :
    ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) false
        - mSigma 0 false • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ =
    ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) true
        - mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ := by
  rw [mSigma_false, mSigma_true]
  rw [centered_block_trace_false_eq_conj_true (d.L N) (d.W N)
    (Gauss.Hflow d N u ω) (Gauss.Hflow_isHermitian d N u ω) (zt 0 u) (mE 0) b,
    Complex.norm_conj]

theorem gaussian_centered_oneLoop_twoCharge_le (d : Gauss.Dims)
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) {c : ℝ}
    (htrue : ∀ b : ZMod (d.L N),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) true
          - mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖ ≤ c) :
    ∀ σ b, ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) σ
        - mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤ c := by
  intro σ b
  cases σ with
  | false =>
      rw [gaussian_centered_oneLoop_false_norm_eq_true]
      exact htrue b
  | true => exact htrue b

/-- The transfer is pointwise inside the *same* event; no second Gaussian
event or independent sample is introduced. -/
theorem gaussian_centered_oneLoop_twoCharge_le_on (d : Gauss.Dims)
    (N : ℕ) (u : ℝ) (Good : Set (Gauss.Ω d)) {c : ℝ}
    (htrue : ∀ ω ∈ Good, ∀ b : ZMod (d.L N),
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) true
          - mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖ ≤ c) :
    ∀ ω ∈ Good, ∀ σ b,
      ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) σ
          - mSigma 0 σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖ ≤ c := by
  intro ω hω
  exact gaussian_centered_oneLoop_twoCharge_le d N u ω (htrue ω hω)

/-- A positive-time actual Gaussian sample with a nonzero matrix and a positive
first-cell scale.  The bound is obtained for both charges on this same sample;
it makes no probabilistic Good-set assertion. -/
theorem positive_time_twoCharge_witness :
    ∃ (N : ℕ) (u : ℝ) (ω : Gauss.Ω Gauss.Dims.exampleGrow) (c : ℝ),
      0 < u ∧ u < 1 ∧ ω ≠ 0 ∧
      Gauss.Hflow Gauss.Dims.exampleGrow N u ω ≠ 0 ∧
      0 < (Gauss.band Gauss.Dims.exampleGrow).scale 0 N u ∧ 0 < c ∧
      (∀ σ (b : ZMod (Gauss.Dims.exampleGrow.L N)),
        ‖Matrix.trace ((Gsig
            (Gauss.Hflow Gauss.Dims.exampleGrow N u ω) (zt 0 u) σ
              - mSigma 0 σ •
                (1 : Matrix (Gauss.Dims.exampleGrow.Idx N)
                  (Gauss.Dims.exampleGrow.Idx N) ℂ)) *
                  Eblk (Gauss.Dims.exampleGrow.L N)
                    (Gauss.Dims.exampleGrow.W N) b)‖ ≤ c) := by
  let d := Gauss.Dims.exampleGrow
  let N : ℕ := 2
  let u : ℝ := 1 / 2
  let ω : Gauss.Ω d := fun _ => 1
  let i : d.Idx N := (0, ⟨0, d.W_pos N⟩)
  let f : ZMod (d.L N) → ℝ := fun b =>
    ‖Matrix.trace ((Gsig (Gauss.Hflow d N u ω) (zt 0 u) true
        - mSigma 0 true • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖
  let c : ℝ := 1 + ∑ b : ZMod (d.L N), f b
  refine ⟨N, u, ω, c, by norm_num [u], by norm_num [u], ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    have hc := congrFun hz (⟨N, (i, i, true)⟩ : Gauss.Coord d)
    norm_num [ω] at hc
  ·
    have hdiag : Gauss.Hflow d N u ω i i = (Real.sqrt u : ℂ) := by
      rw [Gauss.Hflow_apply]
      simp [Gauss.Xentry, ω]
    intro hz
    have hz' := congrArg (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => M i i) hz
    have hz'' : (Real.sqrt u : ℂ) = 0 := hdiag.symm.trans (by simpa using hz')
    have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 (by norm_num [u])
    exact (Complex.ofReal_ne_zero.mpr hsqrt.ne') hz''
  · exact (Gauss.band d).scale_pos (by norm_num : |(0 : ℝ)| < 2) N
      (by norm_num [u]) (by norm_num [u])
  · have hsum : 0 ≤ ∑ b : ZMod (d.L N), f b :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    dsimp [c]
    linarith
  · intro σ b
    apply gaussian_centered_oneLoop_twoCharge_le d N u ω
    intro b'
    have hf0 : ∀ b : ZMod (d.L N), 0 ≤ f b := fun b => norm_nonneg _
    have hb : f b' ≤ ∑ b : ZMod (d.L N), f b :=
      Finset.single_le_sum (s := Finset.univ) (f := f)
        (fun b _ => hf0 b) (Finset.mem_univ b')
    change f b' ≤ c
    change f b' ≤ 1 + ∑ b : ZMod (d.L N), f b
    linarith

#print axioms centered_block_trace_false_eq_conj_true
#print axioms gaussian_centered_oneLoop_false_norm_eq_true
#print axioms gaussian_centered_oneLoop_twoCharge_le
#print axioms gaussian_centered_oneLoop_twoCharge_le_on
#print axioms positive_time_twoCharge_witness

end RBM.APrimeTwoChargeOneLoop
