/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingEarlyPrefixTransitionExclusion
import RBM1D.Gauss.APrimeGeneralMovingJointRateIntegrable
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget
import RBM1D.Gauss.APrimeGeneralMovingTargetTransitionExists

/-!
# T1149: first-cell early cross rate is supported on the norm-bad set

The strict transition defining the actual cross `jointRate` is disjoint from
the fixed norm-good event on every polynomially early active prefix. Thus the
literal p=1 Gaussian second moment is exactly its integral over the norm-bad
complement. This is only a support identity; it gives no small-probability
bound.
-/

namespace RBM.APrimeGeneralMovingEarlyCrossBadSupport

open Filter MeasureTheory Set Gauss CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60
private noncomputable abbrev firstCellGood (N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ‖Gauss.Xmat d N ω‖ ≤ (N : ℝ)}

/-- The actual cross rate vanishes pointwise on the fixed norm-good event,
uniformly over active prefixes `k ≤ N^10` and every output and closed-cell time.
The same canonical order and T995 loss schedule occur in both factors. -/
theorem eventually_jointRate_eq_zero_on_normGood
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N,
        k ≤ N ^ 10 →
        ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
        ∀ r ∈ Icc (firstCellS τ N)
          (cutNetPt (firstCellS τ) mesh N k),
        ∀ ω ∈ firstCellGood N,
          APrimeCrossJointSplit.jointRate d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (firstCellS τ) mesh N k
            (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
              (firstCellT τ) mesh N)
            σ a (cutNetPt (firstCellS τ) mesh N k) r ω = 0 := by
  filter_upwards [
    _root_.RBM.APrimeGeneralMovingEarlyPrefixTransitionExclusion.eventually_early_prefix_transition_exclusion hτ (by norm_num) hδ hsmall] with
    N hN
  intro k hk hkEarly σ a r hr ω hgood
  have htrans : ω ∉ APrimeCrossJointSplit.transition d 0 60
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (firstCellS τ) mesh N k
      (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
        (firstCellT τ) mesh N) :=
    (hN k hk hkEarly ω hgood).2
  simp [APrimeCrossJointSplit.jointRate, htrans]

/-- At p=1 the actual general-moving integrability producer applies to the
same first-cell schedule and canonical smoothing order as the support result. -/
theorem eventually_integrable_firstCell_jointRate_sq
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N,
      ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (firstCellS τ N)
        (cutNetPt (firstCellS τ) mesh N k),
        Integrable (fun ω => |APrimeCrossJointSplit.jointRate d 0 60
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) mesh N k
          (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
            (firstCellT τ) mesh N)
          σ a (cutNetPt (firstCellS τ) mesh N k) r ω| ^ 2)
          (Gauss.P d) := by
  have hsEq : firstCellS τ = fun _ => 0 := by
    funext N
    unfold firstCellS
    exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hreg0 := APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg hτ
  have hreg0' : Cond272Reg (Gauss.band d) 0 (fun _ => 0) (firstCellT τ) (1 / 2) := by
    change Cond272Reg (Gauss.band d) 0 (fun _ => 0) (firstCellT τ) (1 / 2) at hreg0
    exact hreg0
  have hreg : Cond272Reg (Gauss.band d) 0 (firstCellS τ) (firstCellT τ) (1 / 2) := by
    simpa [hsEq] using hreg0'
  have hs0 : ∀ N, 0 ≤ firstCellS τ N := by
    intro N
    rw [hsEq]
  have hst : ∀ N, firstCellS τ N ≤ firstCellT τ N := by
    intro N
    rw [hsEq]
    have hW : (1 : ℝ) ≤ (Gauss.band d).W N := (Gauss.band d).one_le_W N
    have hm := gridT_mono hW hτ.le (1 / 2 : ℝ)
    have h := hm (show 0 ≤ 1 by norm_num)
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    simpa [firstCellT] using h
  have ht1 : ∀ N, firstCellT τ N < 1 := by
    intro N
    have h := gridT_le (W := (Gauss.band d).W N) (τ' := τ) (1 / 2 : ℝ) 1
    exact lt_of_le_of_lt h (by norm_num)
  have hroom := APrimeGeneralMovingSlotLossSchedule.schedule_room
    (by norm_num : (0 : ℝ) < 1 / 2) hδ hsmall
  have h := APrimeGeneralMovingJointRateIntegrable.eventually_integrable_jointRate_pow
    (E := 0) (D := 60) (c := 1 / 2)
    (s := firstCellS τ) (t := firstCellT τ)
    (by norm_num) (by norm_num) hs0 hst ht1 (by norm_num) hreg
    (deltaWeight := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
    hroom.1.le 1 (by norm_num)
  simpa [mesh, pow_two] using h

/-- Exact p=1 support localization: the second moment of the literal `jointRate`
equals its Gaussian integral over `{‖Xmat‖ > N}`. -/
theorem eventually_second_moment_eq_normBad_integral
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hsmall : δ ≤ min 1 ((1 / 2 : ℝ) / 100)) :
    ∀ᶠ N : ℕ in atTop,
      ∀ k ≤ cutNetTop (firstCellS τ) (firstCellT τ) mesh N,
      k ≤ N ^ 10 →
      ∀ σ : Fin 2 → Bool, ∀ a : LoopArg (d.L N) 2,
      ∀ r ∈ Icc (firstCellS τ N)
        (cutNetPt (firstCellS τ) mesh N k),
        (∫ ω, |APrimeCrossJointSplit.jointRate d 0 60
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          (firstCellS τ) mesh N k
          (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
            (firstCellT τ) mesh N)
          σ a (cutNetPt (firstCellS τ) mesh N k) r ω| ^ 2 ∂Gauss.P d) =
        ∫ ω in (firstCellGood N)ᶜ,
          |APrimeCrossJointSplit.jointRate d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (firstCellS τ) mesh N k
            (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
              (firstCellT τ) mesh N)
            σ a (cutNetPt (firstCellS τ) mesh N k) r ω| ^ 2 ∂Gauss.P d := by
  have hzero := eventually_jointRate_eq_zero_on_normGood
    (τ := τ) (δ := δ) hτ hδ hsmall
  have hint := eventually_integrable_firstCell_jointRate_sq hτ hδ hsmall
  filter_upwards [hzero, hint] with N hzeroN hintN
  intro k hk hkEarly σ a r hr
  have hI : Integrable (fun ω => |APrimeCrossJointSplit.jointRate d 0 60
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      (firstCellS τ) mesh N k
      (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
        (firstCellT τ) mesh N)
      σ a (cutNetPt (firstCellS τ) mesh N k) r ω| ^ 2) (Gauss.P d) :=
    hintN k hk σ a r hr
  have hzeroGood : ∀ ω ∈ firstCellGood N,
      |APrimeCrossJointSplit.jointRate d 0 60
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (firstCellS τ) mesh N k
        (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
          (firstCellT τ) mesh N)
        σ a (cutNetPt (firstCellS τ) mesh N k) r ω| ^ 2 = 0 := by
    intro ω hω
    rw [hzeroN k hk hkEarly σ a r hr ω hω]
    norm_num
  have hGoodMeas : MeasurableSet (firstCellGood N) := by
    exact measurableSet_le (Gauss.measurable_norm_Xmat d N) measurable_const
  have hGoodInt : ∫ ω in firstCellGood N,
      |APrimeCrossJointSplit.jointRate d 0 60
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
        (firstCellS τ) mesh N k
        (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
          (firstCellT τ) mesh N)
        σ a (cutNetPt (firstCellS τ) mesh N k) r ω| ^ 2 ∂Gauss.P d = 0 := by
    rw [← integral_indicator hGoodMeas]
    apply integral_eq_zero_of_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ firstCellGood N
    · have hz := hzeroGood ω hω
      simp only [Set.indicator_of_mem hω]
      exact hz
    · simp [Set.indicator_of_notMem hω]
  rw [← integral_add_compl hGoodMeas hI, hGoodInt, zero_add]

/-- A concrete nondegenerate context: the exact first-cell `Cond272Reg`
assumption is satisfiable, and T1051 supplies a genuine active `k=2` strict-
transition witness for τ=c=1, δ=1/200 on the D=60 target mesh. -/
theorem nondegenerate_firstCell_and_active_two_witness :
    ∃ τ c δ : ℝ, 0 < τ ∧ 0 < c ∧ 0 < δ ∧
      δ ≤ min 1 (c / 100) ∧
      Cond272Reg (Gauss.band d) 0 (firstCellS τ) (firstCellT τ) c ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ x ∈ Set.Ioo 0 (2 / Real.sqrt ((mesh N)⁻¹)),
          let ω := APrimeSmoothTransition.scalarSample d x
          ω ∈ APrimeCrossJointSplit.transition d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
            (firstCellS τ) mesh N 2
            (APrimeSmoothWeightActual.canonicalM d (firstCellS τ)
              (firstCellT τ) mesh N) := by
  refine ⟨1, 1 / 2, 1 / 200, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · have h := APrimeFirstCellInitialMomentBudget.firstCell_cond272Reg
      (τ' := 1) (by norm_num)
    have hs : firstCellS 1 = fun _ => 0 := by
      funext N
      unfold firstCellS
      exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa [hs] using h
  have hw := APrimeGeneralMovingTargetTransitionExists.eventually_exampleGrow_target_transition
    (τ := 1) (c := 1 / 2) (δ := 1 / 200) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  filter_upwards [hw] with N hN
  obtain ⟨_hs, _ht, _hactive, x, hx, htransition, _hlow, _hhigh⟩ := hN
  refine ⟨x, ?_, ?_⟩
  · simpa [mesh] using hx
  · have hs : firstCellS 1 = fun _ => 0 := by
      funext n
      unfold firstCellS
      exact gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)
    simpa [mesh, hs] using htransition

#print axioms eventually_jointRate_eq_zero_on_normGood
#print axioms eventually_integrable_firstCell_jointRate_sq
#print axioms eventually_second_moment_eq_normBad_integral
#print axioms nondegenerate_firstCell_and_active_two_witness

end RBM.APrimeGeneralMovingEarlyCrossBadSupport
