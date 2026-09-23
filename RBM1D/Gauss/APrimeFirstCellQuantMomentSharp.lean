/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMoment
import RBM1D.Gauss.APrimeFirstCellExponentAbsorptionSharp

/-!
# T527: the sharper actual first-cell coordinate moment

This preserves the exact T500/T506 ledger proved in T509 and replaces only
its last deterministic absorption by T526's `delta / 5` bound.  The moment
order is fixed before the common eventual threshold for all active indices
and outputs.  The exact zero-index branch and the positive `k = 2` resident
remain on the same literal sharp common event.
-/

namespace RBM.APrimeFirstCellQuantMomentSharp

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellQuantMoment.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellQuantMoment.alpha
noncomputable abbrev beta : ℝ := APrimeFirstCellQuantMoment.beta

/-- The sharper canonical-weight coordinate norm at the actual moving endpoint. -/
def quantMomentAt' (τ' : ℝ) (p N k : ℕ) (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight τ' p N k) p (Y N k a (endpoint N k)) ≤
    (N : ℝ) ^ (delta / 5) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- T509's exact T500/T506 ledger is unchanged before the final absorption. -/
theorem momNormW_le_momentRhs' {τ' : ℝ} {p N k : ℕ}
    (a : LoopArg (d.L N) 2) (hvhalf : endpoint N k ≤ 1 / 2)
    (hpaid : APrimeFirstCellMinkowskiCrossQVPaid.minkowskiCrossQVPaidAt
      τ' alpha beta p N k a)
    (hinit : momNormW (P d) (weight τ' p N k) p (initial N k a) ≤
      (N : ℝ) ^ (5 * delta / 32) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :
    momNormW (P d) (weight τ' p N k) p (Y N k a (endpoint N k)) ≤
      APrimeFirstCellExponentAbsorption.momentRhs p N
        (etaT 0 0 / etaT 0 (endpoint N k)) := by
  exact APrimeFirstCellQuantMoment.momNormW_le_momentRhs
    a hvhalf hpaid hinit

/-- The sharper quantitative bound is uniform over every positive active
index and output after the moment order has been fixed. -/
def actualQuantMoment' (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    ∀ a : LoopArg (d.L N) 2, quantMomentAt' τ' p N k a

/-- T526 replaces only T509's final absorption step. -/
theorem actualQuantMoment_of_paid' {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p)
    (hpaid : APrimeFirstCellMinkowskiCrossQVPaid.actualMinkowskiCrossQVPaid
      τ' alpha beta p) :
    actualQuantMoment' τ' p := by
  filter_upwards [hpaid,
    APrimeFirstCellInitialMomentBudget.eventually_initial_simplified hτ' p hp,
    APrimeFirstCellExponentAbsorptionSharp.eventually_momentRhs_le p hp,
    APrimeFirstCellScaleFloors.eventually_scalePackage hτ']
      with N hpaidN hinitN harithN hscaleN
  intro k hk1 hk a
  have hscale := hscaleN k hk
  have hledger := momNormW_le_momentRhs' a hscale.time_le_half
    (hpaidN k hk1 hk a) (hinitN k hk a)
  exact hledger.trans
    (harithN _ hscale.one_le_ratio hscale.ratio_le_two)

/-- The zero-index branch records the normalized target and its exact
ratio-one simplification separately from the positive active indices. -/
def kZeroQuantMoment' (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧ quantMomentAt' τ' p N 0 a ∧
      momNormW (P d) (weight τ' p N 0) p (Y N 0 a (endpoint N 0)) ≤
        (N : ℝ) ^ (delta / 5)

/-- At zero the flow is the initial term, whose T500 exponent is smaller
than `delta / 5`. -/
theorem eventually_kZeroQuantMoment' {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p) : kZeroQuantMoment' τ' p := by
  filter_upwards [APrimeFirstCellInitialMomentBudget.eventually_initial_k_zero hτ' p hp,
    eventually_ge_atTop 1] with N hinitN hN a
  obtain ⟨hv, _hexact, hsmall⟩ := hinitN a
  have hY := Y_zero_eq_initial a (by rw [hv]) (by rw [hv]; norm_num)
  have hpow : (N : ℝ) ^ (5 * delta / 32) ≤ (N : ℝ) ^ (delta / 5) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      (by nlinarith [APrimeFirstCellQuantMoment.delta_pos])
  have hflow : momNormW (P d) (weight τ' p N 0) p
      (Y N 0 a (endpoint N 0)) ≤ (N : ℝ) ^ (delta / 5) := by
    rw [hv, hY]
    exact hsmall.trans hpow
  refine ⟨hv, ?_, hflow⟩
  simpa [quantMomentAt', hv, etaT, mE_zero] using hflow

/-- A positive `k = 2` resident on T506's literal sharp common event, with
canonical weight one and the sharper bound for every output. -/
def positiveTwoQuantMomentResident' (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    weight τ' p N 2 ω = 1 ∧
    ∀ a : LoopArg (d.L N) 2, quantMomentAt' τ' p N 2 a

/-- The sharper quantitative conclusion is attached to T506's same resident
and canonical plateau. -/
theorem positiveTwoQuantMomentResident_of_paid' {τ' : ℝ} {p : ℕ}
    (hτ' : 0 < τ')
    (hresident :
      APrimeFirstCellMinkowskiCrossQVPaid.positiveTwoMinkowskiCrossQVPaidResident
        τ' alpha beta p)
    (hquant : actualQuantMoment' τ' p) :
    positiveTwoQuantMomentResident' τ' p := by
  filter_upwards [hresident, hquant,
    APrimeFirstCellCanonicalPlateau.eventually_canonicalWeight_one_on_sharpCommonEvent
      hτ' APrimeFirstCellQuantMoment.delta_pos
        APrimeFirstCellQuantMoment.alpha_pos]
      with N hresidentN hquantN hweightN
  obtain ⟨ω, hω, hk, hvpos, hvle, _hpaid⟩ := hresidentN
  exact ⟨ω, hω, hk, hvpos, hvle, hweightN ω hω p,
    fun a => hquantN 2 (by norm_num) hk a⟩

/-- Closed sharper coordinate moment on T506's one literal measurable,
high-probability, eventually nonempty sharp event. -/
theorem exists_quantMoment_with_resident' :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ p : ℕ, 1 ≤ p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
        HighProb (P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
        (∀ᶠ N : ℕ in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N).Nonempty) ∧
        actualQuantMoment' τ' p ∧ kZeroQuantMoment' τ' p ∧
        positiveTwoQuantMomentResident' τ' p := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellMinkowskiCrossQVPaid.exists_minkowskiCrossQVPaid_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro p hp
  obtain ⟨hm, hprob, hpaid, _hzero, hne, hresident⟩ :=
    hall alpha APrimeFirstCellQuantMoment.alpha_pos p hp beta
      APrimeFirstCellQuantMoment.beta_pos
  have hquant := actualQuantMoment_of_paid' hτ' p hp hpaid
  exact ⟨hm, hprob, hne, hquant, eventually_kZeroQuantMoment' hτ' p hp,
    positiveTwoQuantMomentResident_of_paid' hτ' hresident hquant⟩

#print axioms momNormW_le_momentRhs'
#print axioms actualQuantMoment_of_paid'
#print axioms eventually_kZeroQuantMoment'
#print axioms positiveTwoQuantMomentResident_of_paid'
#print axioms exists_quantMoment_with_resident'

end

end RBM.APrimeFirstCellQuantMomentSharp
