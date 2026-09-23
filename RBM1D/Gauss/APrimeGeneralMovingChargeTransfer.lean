/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingTwoChargeModulus
import RBM1D.Gauss.CondStableFlow

/-!
# T511: exact stochastic-domination transfer between the two charges

T501 proves that the norms of the plus and minus centered one-loop traces
agree on every sample.  This file transfers a supplied plus-charge bound to
the minus charge with the identical control for deterministic selectors,
`UnifDomIcc`, and the public `TimeIcc` stochastic-domination interface.
-/

namespace RBM.APrimeGeneralMovingChargeTransfer

open Filter MeasureTheory Set Gauss

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The real norm of T501's centered block trace. -/
noncomputable def traceNorm (E : Real) (N : Nat) (u : Real)
    (sigma : Bool) (b : ZMod (d.L N)) (omega : Ω d) : Real :=
  ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
    E N u omega sigma b‖

/-- The two real observables coincide pointwise, with no event or scale loss. -/
theorem traceNorm_false_eq_true (E : Real) (N : Nat) (u : Real)
    (b : ZMod (d.L N)) (omega : Ω d) :
    traceNorm E N u false b omega = traceNorm E N u true b omega := by
  exact APrimeGeneralMovingTwoChargeModulus.centeredTrace_false_norm_eq_true
    E N u omega b

/-- At a deterministic selector, the minus and plus failure sets are
literally equal for every exponent and size. -/
theorem selector_badSet_false_eq_true
    (E : Real) (u : Nat -> Real)
    (control : ∀ N, ZMod (d.L N) -> Ω d -> Real)
    (tau : Real) (N : Nat) :
    badSet
        (fun N (b : ZMod (d.L N)) omega =>
          traceNorm E N (u N) false b omega)
        control tau N =
      badSet
        (fun N (b : ZMod (d.L N)) omega =>
          traceNorm E N (u N) true b omega)
        control tau N := by
  ext omega
  simp only [badSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa only [traceNorm_false_eq_true] using hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa only [traceNorm_false_eq_true] using hb⟩

/-- A selector-indexed plus-charge domination transfers exactly to the minus
charge at the same deterministic selector and control. -/
theorem selector_stochDom_false_of_true
    {E : Real} {u : Nat -> Real}
    {control : ∀ N, ZMod (d.L N) -> Ω d -> Real}
    (hplus : StochDom (P d)
      (fun N (b : ZMod (d.L N)) omega =>
        traceNorm E N (u N) true b omega)
      control) :
    StochDom (P d)
      (fun N (b : ZMod (d.L N)) omega =>
        traceNorm E N (u N) false b omega)
      control := by
  exact StochDom.of_le_left
    (fun N b omega => (traceNorm_false_eq_true E N (u N) b omega).le)
    hplus

/-- A fixed-time moving-window domination transfers from plus to minus with
the identical time-dependent control. -/
theorem unifDomIcc_false_of_true
    {E : Real} {s t : Nat -> Real}
    {control : ∀ N, Real -> ZMod (d.L N) -> Ω d -> Real}
    (hplus : UnifDomIcc (P d) s t
      (fun N u (b : ZMod (d.L N)) omega =>
        traceNorm E N u true b omega)
      control) :
    UnifDomIcc (P d) s t
      (fun N u (b : ZMod (d.L N)) omega =>
        traceNorm E N u false b omega)
      control := by
  exact Gauss.UnifDomIcc.of_le_left
    (fun N u b omega => (traceNorm_false_eq_true E N u b omega).le)
    hplus

/-- With time inside the public `TimeIcc` index, the same pointwise identity
transfers stochastic domination without a net or a second event. -/
theorem stochDom_timeIcc_false_of_true
    {E : Real} {s t : Nat -> Real}
    {control : ∀ N,
      (TimeIcc s t N × ZMod (d.L N)) -> Ω d -> Real}
    (hplus : StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N q omega => traceNorm E N (q.1 : Real) true q.2 omega)
      control) :
    StochDom (P d)
      (U := fun N => TimeIcc s t N × ZMod (d.L N))
      (fun N q omega => traceNorm E N (q.1 : Real) false q.2 omega)
      control := by
  exact StochDom.of_le_left
    (fun N q omega =>
      (traceNorm_false_eq_true E N (q.1 : Real) q.2 omega).le)
    hplus

/-- T501's positive-length measurable high-probability nonempty norm event
also witnesses the all-sample pointwise charge identity. -/
theorem positive_length_same_good_charge_transfer_witness :
    ∃ tauPrime : Real, 0 < tauPrime ∧
      ∃ c : Real, 0 < c ∧ ∃ s t : Nat -> Real,
      (∀ N, 0 <= s N) ∧ (∀ N, s N <= t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ (∀ᶠ N : Nat in atTop, s N < t N) ∧
      (∀ N, MeasurableSet (APrimeGeneralMovingGoodMesh.good N)) ∧
      HighProb (P d) APrimeGeneralMovingGoodMesh.good ∧
      (∀ N, (APrimeGeneralMovingGoodMesh.good N).Nonempty) ∧
      (∀ N, ∀ omega ∈ APrimeGeneralMovingGoodMesh.good N,
        ∀ u ∈ Icc (s N) (t N), ∀ b : ZMod (d.L N),
          traceNorm 0 N u false b omega =
            traceNorm 0 N u true b omega) := by
  obtain ⟨tauPrime, hTau, c, hc, s, t, hs0, hst, ht1, hreg, hpos,
      hmeas, hhigh, hnonempty, _hmodulus⟩ :=
    APrimeGeneralMovingTwoChargeModulus.positive_length_same_good_twoCharge_modulus_witness
  refine ⟨tauPrime, hTau, c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    hmeas, hhigh, hnonempty, ?_⟩
  intro N omega _homega u _hu b
  exact traceNorm_false_eq_true 0 N u b omega

end

end RBM.APrimeGeneralMovingChargeTransfer

namespace RBM.APrimeGeneralMovingChargeTransfer

#print axioms traceNorm_false_eq_true
#print axioms selector_badSet_false_eq_true
#print axioms selector_stochDom_false_of_true
#print axioms unifDomIcc_false_of_true
#print axioms stochDom_timeIcc_false_of_true
#print axioms positive_length_same_good_charge_transfer_witness

end RBM.APrimeGeneralMovingChargeTransfer
