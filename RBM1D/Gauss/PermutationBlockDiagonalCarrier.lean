/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator
import RBM1D.Gauss.DimsExample

/-!
# Generic Hermitian block-diagonal physical carrier

A finite family of Hermitian `Fin W` blocks embeds into the actual physical
`ZMod L × Fin W` matrix. The embedding is band-supported, and the full-product
sample encoder reads back the exact matrix while respecting all zero-variance
coordinates. This is a deterministic interface, not a construction of the
quantile Fourier blocks or a Gaussian local-law event.
-/

open Matrix
namespace RBM.Gauss

/-- Place one finite matrix on each physical block, with zero cross-block entries. -/
def blockDiagonal (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  fun i j => if i.1 = j.1 then C i.1 i.2 j.2 else 0

theorem blockDiagonal_apply (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (i j : d.Idx N) :
    blockDiagonal d N C i j = if i.1 = j.1 then C i.1 i.2 j.2 else 0 := rfl

/-- Hermiticity is inherited entrywise from every diagonal block. -/
theorem blockDiagonal_isHermitian (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (hC : ∀ a, (C a).IsHermitian) :
    (blockDiagonal d N C).IsHermitian := by
  ext i j
  change star (blockDiagonal d N C j i) = blockDiagonal d N C i j
  simp only [blockDiagonal]
  by_cases h : i.1 = j.1
  · rw [ite_eq_left h.symm, ite_eq_left h]
    rw [← h]
    exact (hC i.1).apply i.2 j.2
  · have h' : j.1 ≠ i.1 := Ne.symm h
    simp [h, h']

/-- A block-diagonal matrix lies inside the physical band support. -/
theorem blockDiagonal_bandSupported (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ) :
    HermitianBandSupported (blockDiagonal d N C) := by
  intro i j hnot
  have hne : i.1 ≠ j.1 := by
    intro h
    apply hnot
    simp [h, sbSupport]
  simp [blockDiagonal, hne]

/-- The full-product encoder reads back every matrix entry exactly. -/
theorem blockDiagonal_readback (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (hC : ∀ a, (C a).IsHermitian) :
    Xmat d N (omegaOfHermitian d N (blockDiagonal d N C)) = blockDiagonal d N C :=
  Xmat_omegaOfHermitian (blockDiagonal d N C) (blockDiagonal_isHermitian d N C hC)

/-- The encoded sample vanishes at every zero-variance coordinate. -/
theorem blockDiagonal_zeroVar (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (c : Coord d) (hg : (gvar d c : ℝ) = 0) :
    omegaOfHermitian d N (blockDiagonal d N C) c = 0 :=
  omegaOfHermitian_eq_zero_of_gvar_eq_zero (blockDiagonal_bandSupported d N C) c hg

theorem exampleGrow_width_six : Dims.exampleGrow.W 6 = 2 := by
  rw [Dims.exampleGrow_W]
  unfold Dims.growW Dims.growL
  have hs6 : Nat.sqrt 6 = 2 := (Nat.eq_sqrt.2 (by norm_num)).symm
  rw [hs6, Nat.sqrt_two]
  norm_num

/-- At the actual size `N = 6`, `W = 2`, there is a nonzero within-block
off-diagonal Hermitian carrier. -/
theorem exampleGrow_nonzero_block :
    ∃ C : ZMod (Dims.exampleGrow.L 6) →
        Matrix (Fin (Dims.exampleGrow.W 6)) (Fin (Dims.exampleGrow.W 6)) ℂ,
      (∀ a, (C a).IsHermitian) ∧
      blockDiagonal Dims.exampleGrow 6 C ≠ 0 := by
  let C : ZMod (Dims.exampleGrow.L 6) →
      Matrix (Fin (Dims.exampleGrow.W 6)) (Fin (Dims.exampleGrow.W 6)) ℂ :=
    fun _ α β => if α = β then 0 else 1
  have hC : ∀ a, (C a).IsHermitian := by
    intro a
    ext α β
    change star (C a β α) = C a α β
    by_cases h : α = β
    · subst β
      simp only [C, ite_true]
      exact star_zero (R := ℂ)
    · have h' : β ≠ α := Ne.symm h
      simp only [C, h, h', ite_false]
      simp
  refine ⟨C, hC, ?_⟩
  intro heq
  let i : Dims.exampleGrow.Idx 6 := (0, ⟨0, by rw [exampleGrow_width_six]; decide⟩)
  let j : Dims.exampleGrow.Idx 6 := (0, ⟨1, by rw [exampleGrow_width_six]; decide⟩)
  have h := congrArg (fun M : Matrix (Dims.exampleGrow.Idx 6) (Dims.exampleGrow.Idx 6) ℂ =>
    M i j) heq
  have hij : i.2 ≠ j.2 := by decide
  change (if i.1 = j.1 then C i.1 i.2 j.2 else 0) = 0 at h
  rw [ite_eq_left rfl] at h
  change (if i.2 = j.2 then (0 : ℂ) else 1) = 0 at h
  rw [ite_eq_right hij] at h
  norm_num at h

/-- The nonzero carrier gives a full-product sample compatible with all
degenerate Gaussian coordinates. -/
theorem exampleGrow_nonzero_compatible_sample :
    ∃ ω : Ω Dims.exampleGrow,
      Xmat Dims.exampleGrow 6 ω ≠ 0 ∧
      ∀ c : Coord Dims.exampleGrow,
        (gvar Dims.exampleGrow c : ℝ) = 0 → ω c = 0 := by
  obtain ⟨C, hC, hnonzero⟩ := exampleGrow_nonzero_block
  refine ⟨omegaOfHermitian Dims.exampleGrow 6
      (blockDiagonal Dims.exampleGrow 6 C), ?_, ?_⟩
  · rw [blockDiagonal_readback Dims.exampleGrow 6 C hC]
    exact hnonzero
  · intro c hg
    exact blockDiagonal_zeroVar Dims.exampleGrow 6 C c hg

#print axioms exampleGrow_width_six
#print axioms exampleGrow_nonzero_block
#print axioms exampleGrow_nonzero_compatible_sample

#print axioms blockDiagonal_isHermitian
#print axioms blockDiagonal_bandSupported
#print axioms blockDiagonal_readback
#print axioms blockDiagonal_zeroVar

end RBM.Gauss
