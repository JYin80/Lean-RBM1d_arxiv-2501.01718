/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowAllTimeProbability
import RBM1D.Gauss.PermutationFourierExampleGrowMeshNorm

/-!
# Finite-permutation probability of the physical quantile-carrier flow event

The T979 all-time centered Fourier event maps, under the same permutation, to
an encoded physical quantile sample in the literal `goodSetFlow`. The same
carrier is nonzero, vanishes on zero-variance coordinates, and belongs to the
fixed norm good-mesh event for sufficiently large actual dimensions. The
probability remains solely on the finite uniform-permutation space.
-/

set_option autoImplicit false

open Filter MeasureTheory RBM RBM.Gauss

namespace RBM.Gauss

/-- The physical sample encoded from the midpoint-quantile Fourier block
arranged by one permutation on every physical block. -/
noncomputable def permutationFourierExampleGrowCarrier (N : ℕ)
    (π : Equiv.Perm (Fin (Dims.exampleGrow.W N))) : Ω Dims.exampleGrow :=
  omegaOfHermitian Dims.exampleGrow N
    (blockDiagonal Dims.exampleGrow N
      (fun _ => permutationFourierBlock (Dims.exampleGrow.W N)
        (Dims.exampleGrow.W_pos N) π))

/-- The preimage, under the physical quantile carrier, of the literal full
flow event together with nonzero, zero-variance, and fixed norm-good-mesh
properties. -/
def permutationFourierExampleGrowCarrierGoodSet (N : ℕ) :
    Set (PermΩ (Dims.exampleGrow.W N)) :=
  {π | permutationFourierExampleGrowCarrier N π ∈
        goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1 / 2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2)) N ∧
      Xmat Dims.exampleGrow N (permutationFourierExampleGrowCarrier N π) ≠ 0 ∧
      (∀ c : Coord Dims.exampleGrow,
        (gvar Dims.exampleGrow c : ℝ) = 0 →
          permutationFourierExampleGrowCarrier N π c = 0) ∧
      permutationFourierExampleGrowCarrier N π ∈
        APrimeGeneralMovingGoodMesh.good N}

/-- The T979 all-time event is contained in the preimage of the physical
carrier event. The one permutation is retained throughout. -/
theorem permutationFourierExampleGrowAllTimeCenteredSet_subset_carrierGoodSet
    (N : ℕ) (hW : 2 ≤ Dims.exampleGrow.W N) (hN : 2 ≤ N) :
    permutationFourierExampleGrowAllTimeCenteredSet N ⊆
      permutationFourierExampleGrowCarrierGoodSet N := by
  intro π hπ
  have hscalar : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 →
      ∀ q : Fin (Dims.exampleGrow.W N),
        ‖permutationFourierSum (Dims.exampleGrow.W N)
          (fun k => semicircleFlowKernel u
            (semicircleLambda (Dims.exampleGrow.W N)
              (Dims.exampleGrow.W_pos N) k.val k.isLt))
          (permutationFourierCharacter (Dims.exampleGrow.W N) q) π -
          (if q = (⟨0, by have h := Dims.exampleGrow.W_pos N; omega⟩ :
            Fin (Dims.exampleGrow.W N)) then Complex.I else 0)‖ <
          flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
    intro u hu0 hu1 q
    exact hπ u ⟨hu0, hu1⟩ q
  have hzero : ‖permutationFourierSum (Dims.exampleGrow.W N)
        (fun k => semicircleFlowKernel 0
          (semicircleLambda (Dims.exampleGrow.W N)
            (Dims.exampleGrow.W_pos N) k.val k.isLt))
        (permutationFourierCharacter (Dims.exampleGrow.W N)
          (⟨0, by have h := Dims.exampleGrow.W_pos N; omega⟩ :
            Fin (Dims.exampleGrow.W N))) π - Complex.I‖ <
        flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N := by
    exact hπ 0 ⟨by norm_num, by norm_num⟩ _
  have hδ : 0 ≤ flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N :=
    le_of_lt (lt_of_le_of_lt (norm_nonneg _) hzero)
  let ω := permutationFourierExampleGrowCarrier N π
  change ω ∈ goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1 / 2)
      (flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2)) N ∧
    Xmat Dims.exampleGrow N ω ≠ 0 ∧
    (∀ c : Coord Dims.exampleGrow,
      (gvar Dims.exampleGrow c : ℝ) = 0 → ω c = 0) ∧
    ω ∈ APrimeGeneralMovingGoodMesh.good N
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact quantile_block_event Dims.exampleGrow N π _ hδ (by
      intro u hu0 hu1 a b
      let : NeZero (Dims.exampleGrow.W N) := ⟨by
        have h := Dims.exampleGrow.W_pos N
        omega⟩
      have hcond : (b - a = (0 : Fin (Dims.exampleGrow.W N))) ↔ a = b := by
        constructor
        · intro hh
          exact (sub_eq_zero.mp hh).symm
        · intro hab
          subst b
          exact sub_self a
      have hs := hscalar u hu0 hu1 (b - a)
      have hite : (if a = b then Complex.I else 0) =
          (if b - a = (0 : Fin (Dims.exampleGrow.W N)) then Complex.I else 0) := by
        apply if_congr
        · exact hcond.symm
        · rfl
        · rfl
      change ‖permutationFourierSum (Dims.exampleGrow.W N)
          (fun k => semicircleFlowKernel u
            (semicircleLambda (Dims.exampleGrow.W N)
              (Dims.exampleGrow.W_pos N) k.val k.isLt))
          (permutationFourierCharacter (Dims.exampleGrow.W N) (b - a)) π -
          (if a = b then Complex.I else 0)‖ < _
      rw [hite]
      exact hs)
  · change Xmat Dims.exampleGrow N
      (permutationFourierExampleGrowCarrier N π) ≠ 0
    rw [show Xmat Dims.exampleGrow N
        (permutationFourierExampleGrowCarrier N π) =
        blockDiagonal Dims.exampleGrow N
          (fun _ => permutationFourierBlock (Dims.exampleGrow.W N)
            (Dims.exampleGrow.W_pos N) π) from by
        exact blockDiagonal_readback _ _ _
          (fun _ => permutationFourierBlock_hermitian _ _ π)]
    intro hz
    apply quantileBlock_nonzero (Dims.exampleGrow.W N)
      (Dims.exampleGrow.W_pos N) hW π
    ext x y
    have h := congrArg (fun M : Matrix (Dims.exampleGrow.Idx N)
      (Dims.exampleGrow.Idx N) ℂ => M (0, x) (0, y)) hz
    have h' : (if (0 : ZMod (Dims.exampleGrow.L N)) = 0 then
        permutationFourierBlock (Dims.exampleGrow.W N)
          (Dims.exampleGrow.W_pos N) π x y else 0) = 0 := by
      simpa [blockDiagonal] using h
    simpa only [ite_true, Matrix.zero_apply] using h'
  · intro c hg
    exact blockDiagonal_zeroVar Dims.exampleGrow N
      (fun _ => permutationFourierBlock (Dims.exampleGrow.W N)
        (Dims.exampleGrow.W_pos N) π) c hg
  · exact quantileCarrier_mem_generalMovingGoodMesh N π hN

/-- The literal physical carrier event, including its deterministic
nondegeneracy and norm conditions, has probability at least `1 - 8 N^(-14)`
eventually under the finite uniform-permutation law. -/
theorem permutationFourierExampleGrow_eventually_carrier_good_probability :
    ∀ᶠ N : ℕ in atTop,
      1 - 8 * (N : ℝ) ^ (-14 : ℝ) ≤
        (uniformPerm (Dims.exampleGrow.W N)).real
          (permutationFourierExampleGrowCarrierGoodSet N) := by
  filter_upwards
    [permutationFourierExampleGrow_eventually_allTime_good_probability,
      permutationFourierExampleGrow_eventually_entry_margin_nonempty,
      eventually_ge_atTop 2] with N hprob hdim hN
  have hsubset : permutationFourierExampleGrowAllTimeCenteredSet N ⊆
      permutationFourierExampleGrowCarrierGoodSet N :=
    permutationFourierExampleGrowAllTimeCenteredSet_subset_carrierGoodSet
      N hdim.1 hN
  exact le_trans hprob (measureReal_mono hsubset)

/-- Every preimage event above is measurable in the finite discrete
uniform-permutation space. -/
theorem permutationFourierExampleGrowCarrierGoodSet_measurable (N : ℕ) :
    MeasurableSet (permutationFourierExampleGrowCarrierGoodSet N) := by
  exact MeasurableSpace.measurableSet_top

#print axioms permutationFourierExampleGrowAllTimeCenteredSet_subset_carrierGoodSet
#print axioms permutationFourierExampleGrow_eventually_carrier_good_probability
#print axioms permutationFourierExampleGrowCarrierGoodSet_measurable

end RBM.Gauss
