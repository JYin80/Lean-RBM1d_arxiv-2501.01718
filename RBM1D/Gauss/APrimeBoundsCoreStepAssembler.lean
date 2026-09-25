/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSlotFields

/-!
# BoundsCore-dependent assemblers for the primed A′ slot

These assemblers make the dependency already present in the one-step consumer explicit:
the primed slot producer may use the incoming `BoundsCore X E s`. They do not construct
the Gaussian slot producer.
-/

namespace RBM

namespace APrimeBoundsCoreStepAssembler

open MeasureTheory Filter Set Real Gauss Step2FarMart Step2Bootstrap MomentDuhamelCut
  APrimeSlotFields

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- One p. 24 grid step with the primed slot producer explicitly depending on the incoming
`BoundsCore X E s`. All other premises and the conclusion match
`APrimeSlotFields.boundsCore_step_of_inputs_mergedOn_aprime'`. -/
theorem boundsCore_step_of_inputs_mergedOn_aprime_of_boundsCore
    (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c) (hreg : Cond272Reg B E s t c)
    (hB : BoundsCore X E s) (h1 : Step1.Hyp X E s t)
    (Hy : ∀ D : ℝ, 60 ≤ D → BoundsCore X E s → APrimeSlot' X E s t D)
    (hcut : CutHypEvOnSlot X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h45i : Eq45FlowInputs X E s t) (H : Eq548EntryDataEvOn' X E s t) :
    BoundsCore X E t := by
  have hE : |E| < 2 := by linarith
  exact APrimeSlotFields.boundsCore_step_of_inputs_mergedOn_aprime'
    X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hreg hB h1
    (fun D hD => Hy D hD hB)
    hcut h514 h45i H

/-- The merged Theorem 2.21 assembler with the same explicit `BoundsCore` dependency in its
primed slot producer. Every other premise and the conclusion match
`APrimeSlotFields.thm221NoEL_of_inputs_mergedOnAll_aprime'`. -/
theorem thm221NoEL_of_inputs_mergedOnAll_aprime_of_boundsCore
    (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1)
    (h1 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Step1.Hyp X E s t)
    (Hy : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      ∀ D : ℝ, 60 ≤ D → BoundsCore X E s → APrimeSlot' X E s t D)
    (hcut : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      BoundsCore X E s → CutHypEvOnSlot X E s t)
    (h514 : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → ∀ n : ℕ, 2 ≤ n →
      Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
        (Step3.flowA B E s t) n)
    (h45i : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c → Eq45FlowInputs X E s t)
    (h548e : ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s t : ℕ → ℝ, (∀ N, 0 ≤ s N) → (∀ N, s N ≤ t N) →
      (∀ N, t N < 1) → ∀ c : ℝ, 0 < c → Cond272Reg B E s t c →
      Eq548EntryDataEvOn' X E s t) :
    Thm221NoEL X κ where
  step E hE c hc0 s t hs0 hst ht1 hreg hB :=
    boundsCore_step_of_inputs_mergedOn_aprime_of_boundsCore X hκ0 hκ1 hE hs0 hst ht1 hc0 hreg hB
      (h1 E hE s t hs0 hst ht1 c hc0 hreg)
      (fun D hD hB' => Hy E hE s t hs0 hst ht1 c hc0 hreg D hD hB')
      (hcut E hE s t hs0 hst ht1 c hc0 hreg hB)
      (h514 E hE s t hs0 hst ht1 c hc0 hreg)
      (h45i E hE s t hs0 hst ht1 c hc0 hreg)
      (h548e E hE s t hs0 hst ht1 c hc0 hreg)

end APrimeBoundsCoreStepAssembler

end RBM

#print axioms RBM.APrimeBoundsCoreStepAssembler.boundsCore_step_of_inputs_mergedOn_aprime_of_boundsCore
#print axioms RBM.APrimeBoundsCoreStepAssembler.thm221NoEL_of_inputs_mergedOnAll_aprime_of_boundsCore
