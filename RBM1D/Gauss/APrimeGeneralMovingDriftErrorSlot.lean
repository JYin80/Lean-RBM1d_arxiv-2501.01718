/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSmoothDriftNormBudget
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule

/-!
# T1047: absorb the T615 complement payment into the moving drift slot

This module proves only the scalar absorption for the complement term with
power `N⁻¹`.  Its endpoint and mesh are the exact target mesh used by T615.
-/

namespace RBM.APrimeGeneralMovingDriftErrorSlot

open Filter Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- At every active target-mesh endpoint, the T615 complement payment with
`β = 1` fits the squared small-slot budget.  The bound includes `k = 0`.
-/
theorem eventually_complement_payment_le_small_slot
    {E c δ : Real} {s t : Nat → Real}
    (hE : |E| < 2) (_hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (_hc : 0 < c) (hreg : Cond272Reg B E s t c)
    (hδ : 0 < δ) (_hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop s t (APrimeGeneralMovingMesh.targetMesh 60) N →
      let v := APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k
      (v - s N) * (N : Real) ^ (-1 : Real) ≤
        (N : Real) ^ (5 * δ / 32) *
          (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
  have hmargin := hreg.1.pow_thirty_le hE hst ht1
  filter_upwards [hmargin, B.dim, eventually_ge_atTop 1] with N hmarginN hdim hN
  have hN1 : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := by linarith
  intro k hk
  let v := APrimeGeneralMovingSmoothDriftNormBudget.endpoint s t 60 N k
  have hvIcc : v ∈ Icc (s N) (t N) := by
    simpa only [v, APrimeGeneralMovingSmoothDriftNormBudget.endpoint] using
      MomentDuhamelCut.netFinset_subset_Icc (hst N)
        (APrimeGeneralMovingMesh.targetMesh_pos 60 N) _
        (cutNetPt_mem_netFinset hk)
  let hv : TimeIcc s t N := ⟨v, hvIcc⟩
  have hvval : (hv : Real) = v := rfl
  have hRpos : 0 < Step2Moment.ratR E s N v :=
    Step2Moment.ratR_pos hE (hvIcc.1.trans_lt (hvIcc.2.trans_lt (ht1 N)))
      (hvIcc.2.trans_lt (ht1 N))
  have hR1 : 1 ≤ Step2Moment.ratR E s N v :=
    Step2Moment.one_le_ratR hE hvIcc.1 (hvIcc.2.trans_lt (ht1 N))
  have hR30 : (Step2Moment.ratR E s N v) ^ (30 : Nat) ≤ B.scale E N v := by
    have h := hmarginN hv
    rw [hvval] at h
    simpa only [Step2Moment.ratR] using h
  have hscaleN : B.scale E N v ≤ (N : Real) := by
    obtain ⟨_, _, heta1, _, hellL⟩ := EEBridge.eeFacts B hE
      (fun n => _hs0 n) ht1 N hv
    have hWL : (B.W N : Real) * (B.L N : Real) ≤ (N : Real) := by
      exact_mod_cast hdim.1
    have hscaleNv : B.scale E N (hv : Real) ≤ (N : Real) := by
      change (B.W N : Real) * B.ell N (hv : Real) * etaT E (hv : Real) ≤
        (N : Real)
      calc
        _ ≤ (B.W N : Real) * (B.L N : Real) * 1 := by gcongr
        _ = (B.W N : Real) * (B.L N : Real) := by ring
        _ ≤ (N : Real) := hWL
    rw [hvval] at hscaleNv
    exact hscaleNv
  have hR2 : (Step2Moment.ratR E s N v) ^ (2 : Nat) ≤ (N : Real) := by
    have hR28 : 1 ≤ (Step2Moment.ratR E s N v) ^ (28 : Nat) :=
      one_le_pow₀ hR1
    have hpow : (Step2Moment.ratR E s N v) ^ (2 : Nat) ≤
        (Step2Moment.ratR E s N v) ^ (30 : Nat) := by
      calc
        _ = (Step2Moment.ratR E s N v) ^ 2 * 1 := by simp
        _ ≤ (Step2Moment.ratR E s N v) ^ 2 *
              (Step2Moment.ratR E s N v) ^ (28 : Nat) :=
          mul_le_mul_of_nonneg_left hR28 (sq_nonneg _)
        _ = (Step2Moment.ratR E s N v) ^ (30 : Nat) := by
          rw [← pow_add]
    exact hpow.trans (hR30.trans hscaleN)
  have hR2real : (Step2Moment.ratR E s N v) ^ (2 : Real) ≤ (N : Real) := by
    have heq : (Step2Moment.ratR E s N v) ^ (2 : Real) =
        (Step2Moment.ratR E s N v) ^ (2 : Nat) := by
      simpa only [Nat.cast_ofNat] using
        (Real.rpow_natCast (Step2Moment.ratR E s N v) 2)
    rw [heq]
    exact hR2
  have hlen : v - s N ≤ 1 := by linarith [hvIcc.1, hvIcc.2, _hs0 N, ht1 N]
  have hlenR2real : (v - s N) * (Step2Moment.ratR E s N v) ^ (2 : Real) ≤
      (N : Real) := by
    have hnonneg : 0 ≤ (Step2Moment.ratR E s N v) ^ (2 : Real) :=
      Real.rpow_nonneg hRpos.le _
    calc
      _ ≤ 1 * (Step2Moment.ratR E s N v) ^ (2 : Real) :=
        mul_le_mul_of_nonneg_right hlen hnonneg
      _ = (Step2Moment.ratR E s N v) ^ (2 : Real) := one_mul _
      _ ≤ (N : Real) := hR2real
  have hexp : (N : Real) ≤ (N : Real) ^ (5 * δ / 32) * (N : Real) := by
    have hNeps : 1 ≤ (N : Real) ^ (5 * δ / 32) :=
      Real.one_le_rpow hN1 (by positivity)
    calc
      (N : Real) = 1 * (N : Real) := by ring
      _ ≤ (N : Real) ^ (5 * δ / 32) * (N : Real) :=
        mul_le_mul_of_nonneg_right hNeps hNpos.le
  have hcross : (v - s N) * (Step2Moment.ratR E s N v) ^ (2 : Real) ≤
      (N : Real) ^ (5 * δ / 32) * (N : Real) := hlenR2real.trans hexp
  have hR2pos : 0 < (Step2Moment.ratR E s N v) ^ (2 : Real) :=
    Real.rpow_pos_of_pos hRpos _
  have hresult := (div_le_div_iff₀ hNpos hR2pos).2 hcross
  have hNinv : (N : Real)⁻¹ = (N : Real) ^ (-1 : Real) := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_one]
  have hRinv : ((Step2Moment.ratR E s N v) ^ (2 : Real))⁻¹ =
      (Step2Moment.ratR E s N v) ^ (-2 : Real) := by
    rw [Real.rpow_neg hRpos.le]
  simpa [hNinv, hRinv, v, div_eq_mul_inv, mul_comm] using hresult

/-- T995's nondegenerate, same-sample positive-cell witness, re-exported for
the complement-payment consumer. -/
noncomputable abbrev scheduled_positive_cell_witness :=
  APrimeGeneralMovingSlotLossSchedule.scheduled_positive_cell_witness

#print axioms eventually_complement_payment_le_small_slot
#print axioms scheduled_positive_cell_witness

end
end RBM.APrimeGeneralMovingDriftErrorSlot
