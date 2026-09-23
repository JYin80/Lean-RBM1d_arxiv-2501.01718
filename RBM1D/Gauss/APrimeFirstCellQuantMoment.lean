/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellInitialMomentBudget
import RBM1D.Gauss.APrimeFirstCellExponentAbsorption
import RBM1D.Gauss.APrimeFirstCellMinkowskiCrossQVPaid

/-!
# T509: the actual quantitative first-cell coordinate moment

The T500 initial bound and T506 paid integral bounds give the exact T503
numerical ledger, using only the first-cell endpoint cap.  T503 then
absorbs the ledger with coefficient one.  The moment order is fixed before
the common eventual size threshold for all moving endpoints and outputs.
-/

namespace RBM.APrimeFirstCellQuantMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellExponentAbsorption.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellExponentAbsorption.alpha
noncomputable abbrev beta : ℝ := APrimeFirstCellExponentAbsorption.beta

theorem delta_eq_one_over_two_thousand : delta = 1 / 2000 := rfl
theorem alpha_eq : alpha = delta / 16 := rfl
theorem beta_eq_one : beta = 1 := rfl

theorem delta_eq_paid : delta = APrimeFirstCellMinkowskiCrossQVPaid.delta := rfl

theorem delta_pos : 0 < delta := by norm_num [delta_eq_one_over_two_thousand]
theorem alpha_pos : 0 < alpha := by rw [alpha_eq]; exact div_pos delta_pos (by norm_num)
theorem beta_pos : 0 < beta := by rw [beta_eq_one]; norm_num

/-- The actual canonical-weight coordinate norm at the actual moving endpoint. -/
def quantMomentAt (τ' : ℝ) (p N k : ℕ) (a : LoopArg (d.L N) 2) : Prop :=
  momNormW (P d) (weight τ' p N k) p (Y N k a (endpoint N k)) ≤
    (N : ℝ) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- The exact exponent identities in the T506-to-T503 substitution. -/
theorem ledger_exponents :
    2 * alpha = delta / 8 ∧
    alpha - 2 * APrimeFirstCellFullCrossBudget.delta = -31 * delta / 16 ∧
    alpha / 2 = delta / 32 := by
  change 2 * (delta / 16) = delta / 8 ∧
    delta / 16 - 2 * delta = -31 * delta / 16 ∧
    (delta / 16) / 2 = delta / 32
  constructor
  · ring
  constructor <;> ring

/-- After the T500 initial substitution, the only estimate needed to identify
T503's literal ledger is `sqrt(v) ≤ sqrt(1/2)`. -/
theorem momNormW_le_momentRhs {τ' : ℝ} {p N k : ℕ}
    (a : LoopArg (d.L N) 2) (hvhalf : endpoint N k ≤ 1 / 2)
    (hpaid : APrimeFirstCellMinkowskiCrossQVPaid.minkowskiCrossQVPaidAt
      τ' alpha beta p N k a)
    (hinit : momNormW (P d) (weight τ' p N k) p (initial N k a) ≤
      (N : ℝ) ^ (5 * delta / 32) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :
    momNormW (P d) (weight τ' p N k) p (Y N k a (endpoint N k)) ≤
      APrimeFirstCellExponentAbsorption.momentRhs p N
        (etaT 0 0 / etaT 0 (endpoint N k)) := by
  have htail : Real.sqrt (endpoint N k) * (N : ℝ) ^ (-(1 : ℝ) / 2) ≤
      Real.sqrt (1 / 2 : ℝ) * (N : ℝ) ^ (-(1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hvhalf)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hq := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl
      (384 * Real.sqrt 3 * (N : ℝ) ^ (delta / 32) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)))) htail)
    (Real.sqrt_nonneg (2 * (p : ℝ) - 1))
  unfold APrimeFirstCellMinkowskiCrossQVPaid.minkowskiCrossQVPaidAt at hpaid
  rw [ledger_exponents.1, ledger_exponents.2.1, ledger_exponents.2.2,
    beta_eq_one, Real.rpow_neg_one] at hpaid
  unfold APrimeFirstCellExponentAbsorption.momentRhs
    APrimeFirstCellExponentAbsorption.driftConstant
  change _ ≤ _ at hinit
  change momNormW (P d) (weight τ' p N k) p (Y N k a (endpoint N k)) ≤
    momNormW (P d) (weight τ' p N k) p (initial N k a) +
      APrimeFirstCellDriftCoefficient.coefficientConstant * (Real.sqrt 2 + 1) *
        (N : ℝ) ^ (delta / 8) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) +
      (N : ℝ)⁻¹ +
      2 * APrimeFirstCellFullCrossBudget.budgetConstant p *
        (N : ℝ) ^ (-31 * delta / 16) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) +
      Real.sqrt (2 * (p : ℝ) - 1) *
        (384 * Real.sqrt 3 * (N : ℝ) ^ (delta / 32) *
            (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) +
          Real.sqrt (endpoint N k) * (N : ℝ) ^ (-(1 : ℝ) / 2)) at hpaid
  linarith only [hpaid, hinit, hq]

/-- The actual quantitative coordinate bound is uniform over positive active
indices and every output after fixing the moment order. -/
def actualQuantMoment (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N →
    ∀ a : LoopArg (d.L N) 2, quantMomentAt τ' p N k a

/-- Uniform T500 initial bounds, the actual T506 inequality, and numerical
T503 absorption are combined before selecting any mesh index or output. -/
theorem actualQuantMoment_of_paid {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p)
    (hpaid : APrimeFirstCellMinkowskiCrossQVPaid.actualMinkowskiCrossQVPaid
      τ' alpha beta p) :
    actualQuantMoment τ' p := by
  filter_upwards [hpaid,
    APrimeFirstCellInitialMomentBudget.eventually_initial_simplified hτ' p hp,
    APrimeFirstCellExponentAbsorption.eventually_momentRhs_le p hp,
    APrimeFirstCellScaleFloors.eventually_scalePackage hτ']
      with N hpaidN hinitN harithN hscaleN
  intro k hk1 hk a
  have hscale := hscaleN k hk
  have hledger := momNormW_le_momentRhs a hscale.time_le_half
    (hpaidN k hk1 hk a) (hinitN k hk a)
  exact hledger.trans
    (harithN _ hscale.one_le_ratio hscale.ratio_le_two)

/-- The zero-index branch states both the normalized target and its exact
ratio-one simplification. -/
def kZeroQuantMoment (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ a : LoopArg (d.L N) 2,
    endpoint N 0 = 0 ∧ quantMomentAt τ' p N 0 a ∧
      momNormW (P d) (weight τ' p N 0) p (Y N 0 a (endpoint N 0)) ≤
        (N : ℝ) ^ (delta / 4)

/-- At zero the actual flow equals the actual initial term.  The smaller
T500 initial exponent is directly bounded by `delta/4`. -/
theorem eventually_kZeroQuantMoment {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 1 ≤ p) : kZeroQuantMoment τ' p := by
  filter_upwards [APrimeFirstCellInitialMomentBudget.eventually_initial_k_zero hτ' p hp,
    eventually_ge_atTop 1] with N hinitN hN a
  obtain ⟨hv, _hexact, hsmall⟩ := hinitN a
  have hY := Y_zero_eq_initial a (by rw [hv]) (by rw [hv]; norm_num)
  have hpow : (N : ℝ) ^ (5 * delta / 32) ≤ (N : ℝ) ^ (delta / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
      (by nlinarith [delta_pos])
  have hflow : momNormW (P d) (weight τ' p N 0) p
      (Y N 0 a (endpoint N 0)) ≤ (N : ℝ) ^ (delta / 4) := by
    rw [hv, hY]
    exact hsmall.trans hpow
  refine ⟨hv, ?_, hflow⟩
  simpa [quantMomentAt, hv, etaT, mE_zero] using hflow

/-- A positive `k=2` resident in T506's literal sharp event, with the same
canonical weight equal to one and all actual output moment bounds. -/
def positiveTwoQuantMomentResident (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    weight τ' p N 2 ω = 1 ∧
    ∀ a : LoopArg (d.L N) 2, quantMomentAt τ' p N 2 a

/-- Add the canonical plateau and the quantitative bound to T506's very
same resident, without a second existential event or parameter. -/
theorem positiveTwoQuantMomentResident_of_paid {τ' : ℝ} {p : ℕ}
    (hτ' : 0 < τ')
    (hresident :
      APrimeFirstCellMinkowskiCrossQVPaid.positiveTwoMinkowskiCrossQVPaidResident
        τ' alpha beta p)
    (hquant : actualQuantMoment τ' p) :
    positiveTwoQuantMomentResident τ' p := by
  filter_upwards [hresident, hquant,
    APrimeFirstCellCanonicalPlateau.eventually_canonicalWeight_one_on_sharpCommonEvent
      hτ' delta_pos alpha_pos] with N hresidentN hquantN hweightN
  obtain ⟨ω, hω, hk, hvpos, hvle, _hpaid⟩ := hresidentN
  exact ⟨ω, hω, hk, hvpos, hvle, hweightN ω hω p,
    fun a => hquantN 2 (by norm_num) hk a⟩

/-- Closed quantitative coordinate moment on T506's one literal measurable,
high-probability, eventually nonempty sharp event.  The fixed moment order
precedes all eventual thresholds; the zero branch is stated separately. -/
theorem exists_quantMoment_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ p : ℕ, 1 ≤ p →
        (∀ N, MeasurableSet
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
        HighProb (P d) (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
        (∀ᶠ N : ℕ in atTop,
          (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N).Nonempty) ∧
        actualQuantMoment τ' p ∧ kZeroQuantMoment τ' p ∧
        positiveTwoQuantMomentResident τ' p := by
  obtain ⟨τ', hτ', hall⟩ :=
    APrimeFirstCellMinkowskiCrossQVPaid.exists_minkowskiCrossQVPaid_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro p hp
  obtain ⟨hm, hprob, hpaid, _hzero, hne, hresident⟩ :=
    hall alpha alpha_pos p hp beta beta_pos
  have hquant := actualQuantMoment_of_paid hτ' p hp hpaid
  exact ⟨hm, hprob, hne, hquant, eventually_kZeroQuantMoment hτ' p hp,
    positiveTwoQuantMomentResident_of_paid hτ' hresident hquant⟩

#print axioms delta_eq_paid
#print axioms ledger_exponents
#print axioms momNormW_le_momentRhs
#print axioms actualQuantMoment_of_paid
#print axioms eventually_kZeroQuantMoment
#print axioms positiveTwoQuantMomentResident_of_paid
#print axioms exists_quantMoment_with_resident

end

end RBM.APrimeFirstCellQuantMoment
