/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSingletonLocalLaw
import RBM1D.Gauss.DetAvgIBPFlow

/-!
# T507: a centered one-loop bound at a fixed selector in a moving window

The sharp singleton entry law from T495 is converted to the public
`LocalLawUnifIcc` interface at the same singleton time.  Fixed-time averaged
IBP then gives the centered block trace at its sharp squared scale.
-/

namespace RBM.APrimeGeneralMovingFixedOneLoop

open Filter MeasureTheory Set Gauss

noncomputable section

/-- The T495 singleton `llErr` law, expressed in the public local-law
interface.  The only model bridge is the actual identity `Sample.llErr_eq`. -/
theorem localLawUnifIcc_of_selector_llErr {E : ℝ} {s u : ℕ → ℝ}
    (hll : StochDom (P Dims.exampleGrow)
      (fun N (ij : (band Dims.exampleGrow).Idx N ×
          (band Dims.exampleGrow).Idx N) ω =>
        (sample Dims.exampleGrow).llErr E N (u N) ω ij)
      (fun N _ _ =>
        APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N)) :
    LocalLawUnifIcc Dims.exampleGrow E u u
      (APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u) := by
  have hidx := hll.precomp_param
    (fun N (p : TimeIcc u u N ×
        (Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N)) => p.2)
  have hgreen : StochDom (P Dims.exampleGrow)
      (fun N (p : TimeIcc u u N ×
          (Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N)) ω =>
        ‖green (Hflow Dims.exampleGrow N (p.1 : ℝ) ω)
            (zt E (p.1 : ℝ)) p.2.1 p.2.2 -
          (if p.2.1 = p.2.2 then mE E else 0)‖)
      (fun N _ _ =>
        APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N) := by
    refine StochDom.of_le_left (fun N p ω => le_of_eq ?_) hidx
    have hp : (p.1 : ℝ) = u N := le_antisymm p.1.2.2 p.1.2.1
    rw [hp, (sample Dims.exampleGrow).llErr_eq N (u N) ω p.2]
    simp only [Sample.G, sample_H]
    congr 2
  exact Gauss.unifDomIcc_of_stochDom_timeIcc hgreen

/-- The actual plus-charge centered block trace at any deterministic selector
in the moving window is dominated by twice the sharp T495 scale `q`. -/
theorem centered_block_trace_stochDom {E c : ℝ} {s t u : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hu : ∀ N, u N ∈ Icc (s N) (t N))
    (hc : 0 < c) (hreg : Cond272Reg (band Dims.exampleGrow) E s t c)
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
    APrimeGeneralMovingSingletonLocalLaw.general_moving_singleton_localLaw
      hE hs0 hst ht1 hu hc hreg
        hB hStep ha0 ha
  have hlocal : LocalLawUnifIcc Dims.exampleGrow E u u
      (APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u) :=
    localLawUnifIcc_of_selector_llErr hpack.1
  have hone := Gauss.detAvgIBP_stochDom_of_localLaw_complete Dims.exampleGrow
    hκ0 hκ1 hEκ hu0 hu1 ha0 (show (0 : ℝ) ≤ 2 by norm_num)
    hpack.2.2.2 (Eventually.of_forall hpack.2.1) hpack.2.2.1 hlocal
  refine StochDom.control_mono hone ?_
  intro N b ω
  have hq0 := APrimeGeneralMovingSingletonLocalLaw.selectorQ_nonneg
    hE hs0 ht1 hu N
  have hwq := APrimeGeneralMovingSingletonLocalLaw.W_inv_le_selectorQ
    hE hs0 ht1 hu N
  have hsqrt :
      APrimeGeneralMovingSingletonLocalLaw.selectorPsi E s u N ^ 2 =
        APrimeGeneralMovingSingletonLocalLaw.selectorQ E s u N +
          (Dims.exampleGrow.W N : ℝ)⁻¹ := by
    unfold APrimeGeneralMovingSingletonLocalLaw.selectorPsi
    rw [Real.sq_sqrt]
    exact add_nonneg hq0 (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [← pow_two, hsqrt]
  linarith

/-- A genuine positive first cell realizes the same hypotheses and the
centered one-loop conclusion at its right endpoint. -/
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
          2 * APrimeGeneralMovingSingletonLocalLaw.selectorQ 0 s t N) := by
  obtain ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg, hB,
      hStep, hpos, _hll⟩ :=
    APrimeGeneralMovingSingletonLocalLaw.positive_length_same_parameter_witness
  have hu : ∀ N, t N ∈ Icc (s N) (t N) := fun N => ⟨hst N, le_rfl⟩
  have hone := centered_block_trace_stochDom (E := 0) (s := s) (t := t)
    (u := t) (by norm_num) hs0 hst ht1 hu hc hreg hB hStep
  exact ⟨τ', hτ', c, hc, s, t, hsEq, hs0, hst, ht1, hreg,
    hB, hStep, hpos, hone⟩

#print axioms localLawUnifIcc_of_selector_llErr
#print axioms centered_block_trace_stochDom
#print axioms positive_length_same_parameter_witness

end
end RBM.APrimeGeneralMovingFixedOneLoop
