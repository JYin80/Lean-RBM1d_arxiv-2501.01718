/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSingletonLocalLawGeneralDims
import RBM1D.Gauss.APrimeGeneralMovingFixedOneLoop
import RBM1D.Gauss.DetAvgIBPFlow

/-!
# T1373: arbitrary-dimension centered one-loop bound at a fixed selector

The actual Gaussian singleton entry law is converted to the public local-law
interface at the same deterministic selector. Fixed-time averaged IBP then
gives the centered block trace bound at twice the selector scale.
-/

namespace RBM.APrimeFixedOneLoopGeneralDims

open Filter MeasureTheory Set Gauss

noncomputable section

/-- Convert the actual singleton `llErr` domination into the local-law
interface at the singleton time. The model bridge is `Sample.llErr_eq`. -/
theorem localLawUnifIcc_of_selector_llErr (d : Dims) {E : ℝ}
    {s u : ℕ → ℝ}
    (hll : StochDom (P d)
      (fun N (ij : d.Idx N × d.Idx N) ω =>
        (sample d).llErr E N (u N) ω ij)
      (fun N _ _ => APrimeSingletonLocalLawGeneralDims.selectorPsi d E s u N)) :
    LocalLawUnifIcc d E u u
      (APrimeSingletonLocalLawGeneralDims.selectorPsi d E s u) := by
  have hidx := hll.precomp_param
    (fun N (p : TimeIcc u u N × (d.Idx N × d.Idx N)) => p.2)
  have hgreen : StochDom (P d)
      (fun N (p : TimeIcc u u N × (d.Idx N × d.Idx N)) ω =>
        ‖green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)) p.2.1 p.2.2 -
          (if p.2.1 = p.2.2 then mE E else 0)‖)
      (fun N _ _ => APrimeSingletonLocalLawGeneralDims.selectorPsi d E s u N) := by
    refine StochDom.of_le_left (fun N p ω => le_of_eq ?_) hidx
    have hp : (p.1 : ℝ) = u N := le_antisymm p.1.2.2 p.1.2.1
    rw [hp, (sample d).llErr_eq N (u N) ω p.2]
    simp only [Sample.G, sample_H]
    congr 2
  exact Gauss.unifDomIcc_of_stochDom_timeIcc hgreen

set_option maxHeartbeats 1000000 in
-- The dimension-generic producer/IBP composition exceeds the default budget.
/-- The actual plus-charge centered block trace at a deterministic selector
in the moving window is dominated by twice the generic singleton scale. -/
theorem centered_block_trace_stochDom (d : Dims) {E c : ℝ}
    {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band d) E s t c)
    (hB : BoundsCore (sample d) E s)
    (hStep : Step1.Hyp (sample d) E s t) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) ω =>
        ‖Matrix.trace ((green (Hflow d N (u N) ω) (zt E (u N))
          - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
            Eblk (d.L N) (d.W N) b)‖)
      (fun N _ _ =>
        2 * APrimeSingletonLocalLawGeneralDims.selectorQ d E s u N) := by
  let κ : ℝ := (2 - |E|) / 2
  let a : ℝ := 59 * c / 240
  have hκ0 : 0 < κ := by dsimp [κ]; linarith
  have hκ1 : κ ≤ 1 := by
    dsimp [κ]
    have := abs_nonneg E
    linarith
  have hEκ : |E| ≤ 2 - κ := by dsimp [κ]; linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha : a < 59 * c / 120 := by dsimp [a]; linarith
  have hu0 : ∀ N, 0 ≤ u N := fun N => (hs0 N).trans (hu N).1
  have hu1 : ∀ N, u N < 1 := fun N => (hu N).2.trans_lt (ht1 N)
  have hpack :=
    APrimeSingletonLocalLawGeneralDims.general_moving_singleton_localLaw
      d hE hs0 hst ht1 hu hc hreg hB hStep ha0 ha
  have hlocal : LocalLawUnifIcc d E u u
      (APrimeSingletonLocalLawGeneralDims.selectorPsi d E s u) :=
    localLawUnifIcc_of_selector_llErr d hpack.1
  have hone := Gauss.detAvgIBP_stochDom_of_localLaw_complete d
    hκ0 hκ1 hEκ hu0 hu1 ha0 (show (0 : ℝ) ≤ 2 by norm_num)
    hpack.2.2.2 (Eventually.of_forall hpack.2.1) hpack.2.2.1 hlocal
  refine StochDom.control_mono hone ?_
  intro N b ω
  have hq0 := APrimeSingletonLocalLawGeneralDims.selectorQ_nonneg
    d hE hs0 ht1 hu N
  have hwq := APrimeSingletonLocalLawGeneralDims.W_inv_le_selectorQ
    d hE hs0 ht1 hu N
  have hsqrt :
      APrimeSingletonLocalLawGeneralDims.selectorPsi d E s u N ^ 2 =
        APrimeSingletonLocalLawGeneralDims.selectorQ d E s u N +
          (d.W N : ℝ)⁻¹ := by
    unfold APrimeSingletonLocalLawGeneralDims.selectorPsi
    rw [Real.sq_sqrt]
    exact add_nonneg hq0 (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [← pow_two, hsqrt]
  linarith

/-- At `Dims.exampleGrow`, the generic theorem specializes to the existing
fixed-dimension centered one-loop result. -/
theorem centered_block_trace_stochDom_exampleGrow {E c : ℝ}
    {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c)
    (hreg : Cond272Reg (band Dims.exampleGrow) E s t c)
    (hB : BoundsCore (sample Dims.exampleGrow) E s)
    (hStep : Step1.Hyp (sample Dims.exampleGrow) E s t) :
    StochDom (P Dims.exampleGrow)
      (fun N (b : ZMod (Dims.exampleGrow.L N)) ω =>
        ‖Matrix.trace ((green (Hflow Dims.exampleGrow N (u N) ω) (zt E (u N))
          - mE E • (1 : Matrix (Dims.exampleGrow.Idx N)
              (Dims.exampleGrow.Idx N) ℂ)) *
            Eblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b)‖)
      (fun N _ _ =>
        2 * APrimeGeneralMovingSingletonLocalLaw.selectorQ E s u N) := by
  have h := centered_block_trace_stochDom Dims.exampleGrow
    hE hs0 hst ht1 hu hc hreg hB hStep
  simpa only [APrimeSingletonLocalLawGeneralDims.selectorQ_exampleGrow] using h

/-- The established positive first-cell witness also realizes the generic
theorem at its `exampleGrow` specialization and the same endpoint selector. -/
theorem positive_length_same_parameter_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, s N = 0) ∧ (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧
      (∀ N, t N < 1) ∧ Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
      BoundsCore (sample Dims.exampleGrow) 0 s ∧
      Step1.Hyp (sample Dims.exampleGrow) 0 s t ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      StochDom (P Dims.exampleGrow)
        (fun N (b : ZMod (Dims.exampleGrow.L N)) ω =>
          ‖Matrix.trace ((green (Hflow Dims.exampleGrow N (t N) ω) (zt 0 (t N))
            - mE 0 • (1 : Matrix (Dims.exampleGrow.Idx N)
                (Dims.exampleGrow.Idx N) ℂ)) *
              Eblk (Dims.exampleGrow.L N) (Dims.exampleGrow.W N) b)‖)
        (fun N _ _ =>
          2 * APrimeSingletonLocalLawGeneralDims.selectorQ
            Dims.exampleGrow 0 s t N) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, hfixed⟩ :=
    APrimeGeneralMovingFixedOneLoop.positive_length_same_parameter_witness
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg,
    hB, hStep, hpos, by
      simpa only [APrimeSingletonLocalLawGeneralDims.selectorQ_exampleGrow] using
        hfixed⟩

#print axioms localLawUnifIcc_of_selector_llErr
#print axioms centered_block_trace_stochDom
#print axioms centered_block_trace_stochDom_exampleGrow
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeFixedOneLoopGeneralDims
