/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingDriftNearCombinedSlot
import RBM1D.Gauss.APrimeGeneralMovingDriftQuadraticSlotRepair

/-!
# T1037: combined T615 near-source and quadratic integral slot

This module adds the two already-proved local integral bounds at their shared
T995 schedule, endpoint, and moving normalization. It makes no full N1/A′
claim.
-/

namespace RBM.APrimeGeneralMovingDriftNearQuadraticSlot

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The exact near-source and quadratic T615 summands together fit the same
strict A-prime slot, uniformly on all active cut-net cells including `k=0`.
The coefficient is the explicit sum of the two producer coefficients, and
the terminal `ratR(v)^(-2)` factor is retained. The left side is the sum of
the two interval integrals; T1017 already proves linearity for the near row's
own two summands. -/
theorem eventually_near_plus_quadratic_integral_le_small_slot
    {E D c : Real} {s t : Nat → Real}
    (hE : |E| < 2) (hD : 60 ≤ D)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg B E s t c)
    {δ : Real} (hδ : 0 < δ)
    (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh D) N →
      let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
      (∫ u in (s N)..v,
          APrimeGeneralMovingDriftNearCombinedSlot.normalizedNearSource
            E D s δ N v u) +
        (∫ u in (s N)..v,
          APrimeGeneralMovingDriftQuadraticSlotRepair.normalizedQuadratic
            E D s (APrimeGeneralMovingSlotLossSchedule.deltaCap δ) N v u) ≤
        ((8 / (mE E).im + 1) + 1 / (mE E).im) *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by
  have hnear :=
    APrimeGeneralMovingDriftNearCombinedSlot.eventually_near_source_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  have hquad :=
    APrimeGeneralMovingDriftQuadraticSlotRepair.eventually_quadratic_integral_le_small_slot
      hE hD hs0 hst ht1 hc hreg hδ hδsmall
  filter_upwards [hnear, hquad] with N hnearN hquadN
  intro k hk
  let v := cutNetPt s (APrimeGeneralMovingMesh.targetMesh D) N k
  have hn := hnearN k hk
  have hq := hquadN k hk
  calc
    _ ≤ ((8 / (mE E).im + 1) *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real)) +
        ((1 / (mE E).im) * (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real)) := by
      exact add_le_add hn hq
    _ = ((8 / (mE E).im + 1) + 1 / (mE E).im) *
          (N : Real) ^ (5 * δ / 32) *
          Step2Moment.ratR E s N v ^ (-2 : Real) := by ring

/-- T995's explicit nondegenerate same-resident, positive-cell witness for
the exact scheduled regime used by this combined slot. -/
noncomputable abbrev nondegenerate_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_near_plus_quadratic_integral_le_small_slot
#print axioms nondegenerate_positive_cell_witness

end
end RBM.APrimeGeneralMovingDriftNearQuadraticSlot
