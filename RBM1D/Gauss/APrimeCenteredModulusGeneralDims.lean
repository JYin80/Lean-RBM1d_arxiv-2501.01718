/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeTwoChargeOneLoop
import RBM1D.Gauss.APrimeGeneralMovingTwoChargeModulus
import RBM1D.Gauss.Lemma514XiPoly
import RBM1D.Gauss.Step1Hyp

/-!
# Generic actual centered-trace time modulus

For every `Dims`, the Gaussian resolvent flow has a pathwise centered block-trace
Hölder modulus on the actual matrix-norm event.  The only event input is
`‖Xmat d N ω‖ ≤ N`; the endpoint spectral floor follows from `Cond272Reg`.
-/

namespace RBM.APrimeCenteredModulusGeneralDims

open Filter MeasureTheory Set Gauss

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The actual Gaussian norm event at dimension `d` and size `N`. -/
def normGood (d : Dims) (N : ℕ) : Set (Ω d) :=
  {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}

/-- The actual centered block trace for either resolvent charge. -/
noncomputable def centeredTrace (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω d) (σ : Bool) (b : ZMod (d.L N)) : ℂ :=
  Matrix.trace ((Gsig (Hflow d N u ω) (zt E u) σ
    - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
      Eblk (d.L N) (d.W N) b)

theorem measurableSet_normGood (d : Dims) (N : ℕ) :
    MeasurableSet (normGood d N) := by
  simpa only [normGood] using Gauss.measurableSet_normX_le d N

theorem highProb_normGood (d : Dims) :
    HighProb (P d) (fun N => normGood d N) := by
  change HighProb (P d)
    (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
  exact Gauss.highProb_norm_Xmat_le d

theorem zero_mem_normGood (d : Dims) (N : ℕ) :
    (0 : Ω d) ∈ normGood d N := by
  simpa only [normGood] using APrimeSlotFields.zero_mem_normX_le d N

theorem normGood_nonempty (d : Dims) (N : ℕ) : (normGood d N).Nonempty :=
  ⟨0, zero_mem_normGood d N⟩

private theorem eventually_endpoint_etaT_inv_le_sq (d : Dims) {E c : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ 2 := by
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_ge
    (band d) hE ht1 hc hreg.2
  have hm := eventually_le_rpow (mE E).im⁻¹
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hfloor, hm, eventually_ge_atTop (1 : ℕ)]
    with N hfloorN hmN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hNfloor : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloorN
  have hImfloor : (N : ℝ)⁻¹ ≤ (mE E).im := by
    exact (inv_le_comm₀ hm0 hN0).mp (by simpa only [Real.rpow_one] using hmN)
  have hprod : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤
      (1 - t N) * (mE E).im :=
    mul_le_mul hNfloor hImfloor (by positivity) (by linarith [ht1 N])
  have hηlower : (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT E (t N) := by
    calc
      (N : ℝ) ^ (-(2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
        rw [Real.rpow_neg hN0.le, Real.rpow_two]
        simpa only [pow_two] using (inv_pow (N : ℝ) 2).symm
      _ ≤ (1 - t N) * (mE E).im := hprod
      _ = etaT E (t N) := by rw [Step2.etaT_eq]
  have hi := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hηlower
  have hrpow : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hN0.le, Real.rpow_two]
  rw [hrpow, inv_inv] at hi
  exact hi

/-- The minus-charge centered trace is the conjugate of the plus-charge trace,
pointwise in the same dimension, time, block, and Gaussian sample. -/
theorem centeredTrace_false_eq_conj_true (d : Dims) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω d) (b : ZMod (d.L N)) :
    centeredTrace d E N u ω false b =
      (starRingEnd ℂ) (centeredTrace d E N u ω true b) := by
  rw [centeredTrace, centeredTrace, mSigma_false, mSigma_true]
  exact APrimeTwoChargeOneLoop.centered_block_trace_false_eq_conj_true
    (d.L N) (d.W N) (Hflow d N u ω) (Hflow_isHermitian d N u ω)
      (zt E u) (mE E) b

/-- On the norm event, the plus-charge block trace inherits the generic
resolvent-flow square-root modulus, with deterministic coefficient `2 N^5`.
The inverse spectral height bound is obtained from `Cond272Reg` via the
generic scale-floor producer. -/
theorem eventually_centeredTrace_true_sub_le (d : Dims) {E c : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (_hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ normGood d N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ b : ZMod (d.L N),
          ‖centeredTrace d E N u ω true b -
              centeredTrace d E N u' ω true b‖ ≤
            2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := by
  have hη := eventually_endpoint_etaT_inv_le_sq d hE ht1 hc hreg
  filter_upwards [hη, eventually_ge_atTop (1 : ℕ)] with N hηN hN
  intro ω hω u hu u' hu' b
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hηt0 : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
  have hηt : (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ 2 := hηN
  have hηinv : 0 ≤ (etaT E (t N))⁻¹ := inv_nonneg.mpr hηt0.le
  have hηsq :
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ 4 := by
    have hsquare := mul_self_le_mul_self hηinv hηt
    calc
      _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
        simpa only [pow_two] using hsquare
      _ = (N : ℝ) ^ 4 := by ring
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ) := by linarith
  have hcoef :
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ *
          (‖Xmat d N ω‖ + 1) ≤ 2 * (N : ℝ) ^ 5 := by
    calc
      _ ≤ (N : ℝ) ^ 4 * (2 * (N : ℝ)) :=
        mul_le_mul hηsq hX1 (by positivity) (by positivity)
      _ = 2 * (N : ℝ) ^ 5 := by ring
  have htrace :
      ‖centeredTrace d E N u ω true b -
          centeredTrace d E N u' ω true b‖ ≤
        ‖green (Hflow d N u ω) (zt E u) -
          green (Hflow d N u' ω) (zt E u')‖ := by
    simp only [centeredTrace, Gsig_true, mSigma_true]
    rw [← Matrix.trace_sub]
    have heq :
        ((green (Hflow d N u ω) (zt E u) -
            mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b -
          (green (Hflow d N u' ω) (zt E u') -
            mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b) =
        (green (Hflow d N u ω) (zt E u) -
          green (Hflow d N u' ω) (zt E u')) *
            Eblk (d.L N) (d.W N) b := by
      noncomm_ring
    rw [heq]
    exact norm_trace_mul_Eblk_le _ b
  refine htrace.trans ((norm_green_flow_sub_le_sqrt d N hE
    (hs0 N) (ht1 N) ω hu hu').trans ?_)
  exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

/-- The actual generic two-charge pathwise centered block-trace modulus on
the common matrix-norm event, uniformly over the original moving window and
all blocks. -/
theorem eventually_centeredTrace_sub_le (d : Dims) {E c : ℝ}
    {s t : ℕ → ℝ} (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ normGood d N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ σ b, ‖centeredTrace d E N u ω σ b -
            centeredTrace d E N u' ω σ b‖ ≤
          2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := by
  filter_upwards [eventually_centeredTrace_true_sub_le d hE hs0 hst ht1 hc hreg]
    with N hN
  intro ω hω u hu u' hu' σ b
  have hplus := hN ω hω u hu u' hu' b
  cases σ with
  | false =>
      rw [centeredTrace_false_eq_conj_true, centeredTrace_false_eq_conj_true,
        ← map_sub, Complex.norm_conj]
      exact hplus
  | true => exact hplus

/-- At `Dims.exampleGrow`, the generic centered trace is definitionally the
existing two-charge trace. -/
theorem centeredTrace_exampleGrow_eq (E : ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω Dims.exampleGrow) (σ : Bool)
    (b : ZMod (Dims.exampleGrow.L N)) :
    centeredTrace Dims.exampleGrow E N u ω σ b =
      APrimeGeneralMovingTwoChargeModulus.centeredTrace E N u ω σ b := rfl

theorem normGood_exampleGrow_eq (N : ℕ) :
    normGood Dims.exampleGrow N = APrimeGeneralMovingGoodMesh.good N := rfl

/-- The accepted positive-length first-cell witness supplies one admissible
window, and its same actual norm event carries the generic conclusion at the
`exampleGrow` specialization.  This asserts no all-dimensions window
nondegeneracy. -/
theorem positive_length_same_good_twoCharge_modulus_witness :
    ∃ τ' : ℝ, 0 < τ' ∧ ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ N, MeasurableSet (normGood Dims.exampleGrow N)) ∧
      HighProb (P Dims.exampleGrow) (normGood Dims.exampleGrow) ∧
      (∀ N, (normGood Dims.exampleGrow N).Nonempty) ∧
      (∀ᶠ N : ℕ in atTop, ∀ ω ∈ normGood Dims.exampleGrow N,
        ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
          ∀ σ b, ‖centeredTrace Dims.exampleGrow 0 N u ω σ b -
              centeredTrace Dims.exampleGrow 0 N u' ω σ b‖ ≤
            2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'|) := by
  obtain ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
      hmeas, hhigh, hnonempty, _hmod⟩ :=
    APrimeGeneralMovingTwoChargeModulus.positive_length_same_good_twoCharge_modulus_witness
  have hmeas' : ∀ N, MeasurableSet (normGood Dims.exampleGrow N) := by
    intro N
    change MeasurableSet (APrimeGeneralMovingGoodMesh.good N)
    exact hmeas N
  have hhigh' : HighProb (P Dims.exampleGrow) (normGood Dims.exampleGrow) := by
    change HighProb (P Dims.exampleGrow) APrimeGeneralMovingGoodMesh.good
    exact hhigh
  have hnonempty' : ∀ N, (normGood Dims.exampleGrow N).Nonempty := by
    intro N
    change (APrimeGeneralMovingGoodMesh.good N).Nonempty
    exact hnonempty N
  have hmod := eventually_centeredTrace_sub_le Dims.exampleGrow
    (by norm_num) hs0 hst ht1 hc hreg
  exact ⟨τ', hτ', c, hc, s, t, hs0, hst, ht1, hreg, hpos,
    hmeas', hhigh', hnonempty', hmod⟩

#print axioms measurableSet_normGood
#print axioms highProb_normGood
#print axioms zero_mem_normGood
#print axioms centeredTrace_false_eq_conj_true
#print axioms eventually_centeredTrace_true_sub_le
#print axioms eventually_centeredTrace_sub_le
#print axioms centeredTrace_exampleGrow_eq
#print axioms positive_length_same_good_twoCharge_modulus_witness

end
end RBM.APrimeCenteredModulusGeneralDims
