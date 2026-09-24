/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationBlockDiagonalCarrier
import RBM1D.Gauss.PermutationFourierCirculantResolvent
import RBM1D.Gauss.PermutationFourierExampleGrowEntryMargin
import RBM1D.Gauss.Step6Sample
/-!
# Actual growing-model full-matrix flow-event carrier

A single permutation supplies the same midpoint-quantile Fourier block at every
physical site. Exact block-diagonal inversion identifies all full-matrix
resolvent entries, including zero cross-block entries. The resulting encoded
nonzero sample belongs to the literal `goodSetFlow` throughout `[0, 1/2]`.
This is deterministic existence, with no Gaussian measure assertion.
-/


set_option autoImplicit false
open Matrix RBM Filter
namespace RBM.Gauss


/-- Identify the physical block carrier with Mathlib’s reordered block diagonal. -/
theorem blockDiagonal_eq_reindex (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ) :
    blockDiagonal d N C =
      (Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)).symm
        (Matrix.blockDiagonal C) := by
  ext i j
  cases i with
  | mk a x =>
    cases j with
    | mk b y =>
      simp [blockDiagonal, Matrix.reindex_apply, Matrix.blockDiagonal_apply]

/-- Multiplication is blockwise after physical reindexing. -/
theorem blockDiagonal_mul (d : Dims) (N : ℕ)
    (C D : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ) :
    blockDiagonal d N C * blockDiagonal d N D =
      blockDiagonal d N (fun a => C a * D a) := by
  simp only [blockDiagonal_eq_reindex]
  let e : d.Idx N ≃ Fin (d.W N) × ZMod (d.L N) := Equiv.prodComm _ _
  change (Matrix.reindexRingEquiv ℂ e).symm (Matrix.blockDiagonal C) *
      (Matrix.reindexRingEquiv ℂ e).symm (Matrix.blockDiagonal D) =
        (Matrix.reindexRingEquiv ℂ e).symm (Matrix.blockDiagonal (fun a => C a * D a))
  rw [Matrix.blockDiagonal_mul]
  exact ((Matrix.reindexRingEquiv ℂ e).symm.map_mul _ _).symm

theorem blockDiagonal_one (d : Dims) (N : ℕ) :
    blockDiagonal d N (fun _ => (1 : Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)) = 1 := by
  ext ⟨a, x⟩ ⟨b, y⟩
  by_cases h : a = b <;> simp [blockDiagonal, Matrix.one_apply, h, Prod.mk.injEq]

/-- A blockwise left inverse is the inverse of the physical carrier. -/
theorem blockDiagonal_inv (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (hC : ∀ a, (C a)⁻¹ * C a = 1) :
    (blockDiagonal d N C)⁻¹ = blockDiagonal d N (fun a => (C a)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [blockDiagonal_mul]
  have h : (fun a => (C a)⁻¹ * C a) =
      (fun _ => (1 : Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)) := by
    funext a
    exact hC a
  change blockDiagonal d N (fun a => (C a)⁻¹ * C a) = 1
  rw [h, blockDiagonal_one]


theorem blockDiagonal_flow_sub (d : Dims) (N : ℕ)
    (C : ZMod (d.L N) → Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (c z : ℂ) :
    c • blockDiagonal d N C - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) =
      blockDiagonal d N (fun a => c • C a - z • 1) := by
  ext ⟨a, x⟩ ⟨b, y⟩
  by_cases h : a = b
  · subst b
    simp [blockDiagonal, Matrix.one_apply]
  · simp [blockDiagonal, Matrix.one_apply, h, Prod.mk.injEq]


/-- The full resolvent is the single-block resolvent on matching physical blocks
and is exactly zero between distinct blocks. -/
theorem blockDiagonal_const_resolvent (d : Dims) (N : ℕ)
    (C : Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ)
    (hC : C.IsHermitian) (u : ℝ) (hu : u ≤ 1 / 2)
    (i j : d.Idx N) :
    green ((Real.sqrt u : ℂ) • blockDiagonal d N (fun _ => C))
        (((1-u : ℝ) : ℂ) * Complex.I) i j =
      if i.1 = j.1 then
        green ((Real.sqrt u : ℂ) • C) (((1-u : ℝ) : ℂ) * Complex.I) i.2 j.2
      else 0 := by
  let z : ℂ := ((1-u : ℝ) : ℂ) * Complex.I
  have hz : z.im ≠ 0 := by
    dsimp [z]
    simp
    linarith
  let B : Matrix (Fin (d.W N)) (Fin (d.W N)) ℂ :=
    (Real.sqrt u : ℂ) • C - z • 1
  have hB : B⁻¹ * B = 1 := by
    change green ((Real.sqrt u : ℂ) • C) z * B = 1
    exact green_mul_sub_of_im (hC.smul (by simp [IsSelfAdjoint])) hz
  have hfactor : (Real.sqrt u : ℂ) • blockDiagonal d N (fun _ => C) - z • 1 =
      blockDiagonal d N (fun _ => B) :=
    blockDiagonal_flow_sub d N (fun _ => C) _ _
  change (((Real.sqrt u : ℂ) • blockDiagonal d N (fun _ => C) - z • 1)⁻¹) i j = _
  rw [hfactor, blockDiagonal_inv d N (fun _ => B) (fun _ => hB)]
  rfl

/-- One strict Fourier-entry margin yields the literal weak `GoodEvent` for the
full physical matrix at every time in the closed half-time interval. -/
theorem quantile_block_event (d : Dims) (N : ℕ)
    (π : Equiv.Perm (Fin (d.W N))) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hmargin : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
      ∀ a b : Fin (d.W N),
      ‖permutationFourierSum (d.W N)
        (fun k => semicircleFlowKernel u
          (semicircleLambda (d.W N) (d.W_pos N) k.val k.isLt))
        (permutationFourierCharacter (d.W N) (b-a)) π -
          (if a = b then Complex.I else 0)‖ < δ) :
    omegaOfHermitian d N
      (blockDiagonal d N (fun _ => permutationFourierBlock (d.W N) (d.W_pos N) π)) ∈
      goodSetFlow d 0 (fun _ => 0) (fun _ => 1/2) (fun _ => δ) N := by
  let C := permutationFourierBlock (d.W N) (d.W_pos N) π
  let ω := omegaOfHermitian d N (blockDiagonal d N (fun _ => C))
  change ∀ u ∈ Set.Icc (0 : ℝ) (1/2),
    GoodEvent (green (Hflow d N u ω) (zt 0 u)) (mE 0) δ
  intro u hu i j
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1/2 := hu.2
  have hread : Xmat d N ω = blockDiagonal d N (fun _ => C) :=
    blockDiagonal_readback d N _ (fun _ => permutationFourierBlock_hermitian _ _ π)
  rw [Hflow, hread, zt_zero_energy, mE_zero]
  rw [blockDiagonal_const_resolvent d N C
    (permutationFourierBlock_hermitian _ _ π) u hu1 i j]
  by_cases hb : i.1 = j.1
  · have heq : (i = j) ↔ (i.2 = j.2) := by
      cases i with
      | mk a x =>
        cases j with
        | mk b y =>
          simp only at hb
          simp [Prod.mk.injEq, hb]
    rw [if_pos hb, if_congr heq rfl rfl]
    change ‖green ((Real.sqrt u : ℂ) • C)
      (((1-u : ℝ) : ℂ) * Complex.I) i.2 j.2 -
        (if i.2 = j.2 then Complex.I else 0)‖ ≤ δ
    rw [show green ((Real.sqrt u : ℂ) • C)
        (((1-u : ℝ) : ℂ) * Complex.I) i.2 j.2 =
      permutationFourierSum (d.W N)
        (fun k => semicircleFlowKernel u
          (semicircleLambda (d.W N) (d.W_pos N) k.val k.isLt))
        (permutationFourierCharacter (d.W N) (j.2-i.2)) π from by
      simpa only [green, C, mul_comm] using
        permutationFourierBlock_resolvent_entry (d.W N) (d.W_pos N) π u hu0 hu1 i.2 j.2]
    exact (hmargin u hu0 hu1 i.2 j.2).le
  · have hij : i ≠ j := by intro h; exact hb (congrArg Prod.fst h)
    simp [hb, hij, hδ]

theorem quantileBlock_nonzero (W : ℕ) (hW : 1 ≤ W) (hW2 : 2 ≤ W)
    (π : Equiv.Perm (Fin W)) : permutationFourierBlock W hW π ≠ 0 := by
  let lam : Fin W → ℝ := fun j => semicircleLambda W hW j.val j.isLt
  have hlt : lam ⟨0, by omega⟩ < lam ⟨1, by omega⟩ := by
    have h0 := (semicircleGamma_lt_Lambda_lt_Gamma_succ W hW (j := 0) (by omega)).2
    have h1 := (semicircleGamma_lt_Lambda_lt_Gamma_succ W hW (j := 1) (by omega)).1
    exact lt_trans h0 h1
  let F := permutationFourierMatrix W
  let D : Matrix (Fin W) (Fin W) ℂ := Matrix.diagonal (fun j => (lam (π j) : ℂ))
  have hC : permutationFourierBlock W hW π = Fᴴ * D * F := rfl
  intro hzero
  have hdiag : D = 0 := by
    have h := congrArg (fun M : Matrix (Fin W) (Fin W) ℂ => F * M * Fᴴ) hzero
    rw [hC] at h
    have hFF : F * Fᴴ = 1 := permutationFourierMatrix_mul_conjTranspose W hW
    have hcalc : F * (Fᴴ * D * F) * Fᴴ = D := by
      calc
        F * (Fᴴ * D * F) * Fᴴ = (F * Fᴴ) * D * (F * Fᴴ) := by simp [Matrix.mul_assoc]
        _ = D := by rw [hFF]; simp
    simpa only [hcalc, mul_zero, zero_mul] using h
  have hz (j : Fin W) : lam j = 0 := by
    have h := congrArg (fun M : Matrix (Fin W) (Fin W) ℂ => M (π.symm j) (π.symm j)) hdiag
    simp [D] at h
    exact_mod_cast h
  have h0 := hz ⟨0, by omega⟩
  have h1 := hz ⟨1, by omega⟩
  linarith

#print axioms quantileBlock_nonzero

theorem eventually_quantile_block_goodSetFlow :
    ∀ᶠ N : ℕ in atTop,
      ∃ ω : Ω Dims.exampleGrow,
        ω ∈ goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1/2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1/2)) N := by
  filter_upwards [permutationFourierExampleGrow_eventually_entry_margin] with N hN
  obtain ⟨π, hπ⟩ := hN
  let d := Dims.exampleGrow
  let δ := flowDelta d 0 (fun _ => 1/2) N
  let C := permutationFourierBlock (d.W N) (d.W_pos N) π
  refine ⟨omegaOfHermitian d N (blockDiagonal d N (fun _ => C)), ?_⟩
  have hδ : 0 ≤ δ := by
    dsimp [δ, flowDelta]
    have hscale := PermutationFourierExampleGrowFlowMargin.scale_half_pos N
    change 0 ≤ ((band d).scale 0 N (1/2))⁻¹ ^ ((1 : ℝ) / 6)
    positivity
  exact quantile_block_event d N π δ hδ (by
    intro u hu0 hu1 a b
    exact hπ u hu0 hu1 a b)

/-- For every sufficiently large actual growing dimension, there is a nonzero
zero-variance-compatible physical sample in the literal flow event. -/
theorem eventually_quantile_block_goodSetFlow_nondegenerate :
    ∀ᶠ N : ℕ in atTop,
      ∃ ω : Ω Dims.exampleGrow,
        ω ∈ goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1/2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1/2)) N ∧
        Xmat Dims.exampleGrow N ω ≠ 0 ∧
        (∀ c : Coord Dims.exampleGrow,
          (gvar Dims.exampleGrow c : ℝ) = 0 → ω c = 0) := by
  filter_upwards [permutationFourierExampleGrow_eventually_entry_margin_nonempty]
    with N hN
  obtain ⟨hW2, π, hπ⟩ := hN
  let d := Dims.exampleGrow
  let δ := flowDelta d 0 (fun _ => 1/2) N
  let C := permutationFourierBlock (d.W N) (d.W_pos N) π
  let ω := omegaOfHermitian d N (blockDiagonal d N (fun _ => C))
  refine ⟨ω, ?_, ?_, ?_⟩
  · have hδ : 0 ≤ δ := by
      dsimp [δ, flowDelta]
      have hscale := PermutationFourierExampleGrowFlowMargin.scale_half_pos N
      change 0 ≤ ((band d).scale 0 N (1/2))⁻¹ ^ ((1 : ℝ) / 6)
      positivity
    exact quantile_block_event d N π δ hδ (by
      intro u hu0 hu1 a b
      exact hπ u hu0 hu1 a b)
  · rw [show Xmat d N ω = blockDiagonal d N (fun _ => C) from
      blockDiagonal_readback d N _ (fun _ => permutationFourierBlock_hermitian _ _ π)]
    intro hzero
    apply quantileBlock_nonzero (d.W N) (d.W_pos N) hW2 π
    ext x y
    have h := congrArg (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      M (0, x) (0, y)) hzero
    simpa [blockDiagonal, C] using h
  · intro c hg
    exact blockDiagonal_zeroVar d N (fun _ => C) c hg

#print axioms eventually_quantile_block_goodSetFlow_nondegenerate

#print axioms eventually_quantile_block_goodSetFlow

#print axioms quantile_block_event

#print axioms blockDiagonal_const_resolvent

#print axioms blockDiagonal_mul
#print axioms blockDiagonal_one
#print axioms blockDiagonal_inv
#print axioms blockDiagonal_flow_sub
end RBM.Gauss
