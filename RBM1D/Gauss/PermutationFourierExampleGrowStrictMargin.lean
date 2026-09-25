/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowFlowCarrier

/-! A strict all-time, all-physical-entry resolvent margin for the actual
midpoint-quantile block sample. Within a block this retains T958's strict
Fourier estimate; across blocks the resolvent entry is exactly zero and the
literal flow threshold is positive. -/

set_option autoImplicit false

open RBM RBM.Gauss Filter

namespace RBM.Gauss

private theorem quantile_block_strict_resolvent (d : Dims) (N : ℕ)
    (π : Equiv.Perm (Fin (d.W N))) (δ : ℝ)
    (hδ : 0 < δ)
    (hmargin : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
      ∀ a b : Fin (d.W N),
      ‖permutationFourierSum (d.W N)
        (fun k => semicircleFlowKernel u
          (semicircleLambda (d.W N) (d.W_pos N) k.val k.isLt))
        (permutationFourierCharacter (d.W N) (b-a)) π -
          (if a = b then Complex.I else 0)‖ < δ) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1/2),
      ∀ i j : d.Idx N,
        ‖green (Hflow d N u
          (omegaOfHermitian d N
            (blockDiagonal d N (fun _ => permutationFourierBlock (d.W N) (d.W_pos N) π))))
          (zt 0 u) i j - (if i = j then Complex.I else 0)‖ < δ := by
  let C := permutationFourierBlock (d.W N) (d.W_pos N) π
  let ω := omegaOfHermitian d N (blockDiagonal d N (fun _ => C))
  intro u hu i j
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1/2 := hu.2
  have hread : Xmat d N ω = blockDiagonal d N (fun _ => C) :=
    blockDiagonal_readback d N _ (fun _ => permutationFourierBlock_hermitian _ _ π)
  rw [Hflow, hread, zt_zero_energy]
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
        (if i.2 = j.2 then Complex.I else 0)‖ < δ
    rw [show green ((Real.sqrt u : ℂ) • C)
        (((1-u : ℝ) : ℂ) * Complex.I) i.2 j.2 =
      permutationFourierSum (d.W N)
        (fun k => semicircleFlowKernel u
          (semicircleLambda (d.W N) (d.W_pos N) k.val k.isLt))
        (permutationFourierCharacter (d.W N) (j.2-i.2)) π from by
      simpa only [green, C, mul_comm] using
        permutationFourierBlock_resolvent_entry (d.W N) (d.W_pos N) π u hu0 hu1 i.2 j.2]
    exact hmargin u hu0 hu1 i.2 j.2
  · have hij : i ≠ j := by intro h; exact hb (congrArg Prod.fst h)
    simp [hb, hij, hδ]

/-- One permutation is fixed before all times and physical indices. Its
encoded actual quantile block sample has strict entrywise resolvent margin
throughout the closed half-time interval, as well as literal `goodSetFlow`
membership, a nonzero physical matrix, and compatibility with zero-variance
coordinates. -/
theorem eventually_quantile_block_strict_resolvent_nondegenerate :
    ∀ᶠ N : ℕ in atTop,
      ∃ π : Equiv.Perm (Fin (Dims.exampleGrow.W N)),
      ∃ ω : Ω Dims.exampleGrow,
        2 ≤ Dims.exampleGrow.W N ∧
        ω = omegaOfHermitian Dims.exampleGrow N
          (blockDiagonal Dims.exampleGrow N
            (fun _ => permutationFourierBlock (Dims.exampleGrow.W N)
              (Dims.exampleGrow.W_pos N) π)) ∧
        ω ∈ goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1/2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1/2)) N ∧
        (∀ u ∈ Set.Icc (0 : ℝ) (1/2),
          ∀ i j : Dims.exampleGrow.Idx N,
            ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) i j -
              (if i = j then Complex.I else 0)‖ <
                flowDelta Dims.exampleGrow 0 (fun _ => 1/2) N) ∧
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
  refine ⟨π, ω, hW2, rfl, ?_, ?_, ?_, ?_⟩
  · have hδ : 0 ≤ δ := by
      dsimp [δ, flowDelta]
      have hscale := PermutationFourierExampleGrowFlowMargin.scale_half_pos N
      change 0 ≤ ((band d).scale 0 N (1/2))⁻¹ ^ ((1 : ℝ) / 6)
      positivity
    exact quantile_block_event d N π δ hδ (by
      intro u hu0 hu1 a b
      exact hπ u hu0 hu1 a b)
  · have hδ : 0 < δ := by
      dsimp [δ, flowDelta]
      have hscale := PermutationFourierExampleGrowFlowMargin.scale_half_pos N
      change 0 < ((band d).scale 0 N (1/2))⁻¹ ^ ((1 : ℝ) / 6)
      positivity
    exact quantile_block_strict_resolvent d N π δ hδ (by
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

#print axioms quantile_block_strict_resolvent
#print axioms eventually_quantile_block_strict_resolvent_nondegenerate

end RBM.Gauss
