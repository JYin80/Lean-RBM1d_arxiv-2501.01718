/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CenteredTraceModulus
import RBM1D.EnergyN.Gauss.Step1Hyp
import RBM1D.Flow.EnergyUniformReg

/-!
# Time modulus of the centered block trace at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: the private
`eventually_endpoint_etaT_inv_le_sqN`,
`RBM.CenteredTraceModulus.eventually_centeredTrace_true_sub_leN` and
`RBM.CenteredTraceModulus.eventually_centeredTrace_sub_leN`.

## The external `κ`

`eventually_endpoint_etaT_inv_le_sqN` needs a bound on `(mE (E N)).im⁻¹` that does not depend on
`N`. It takes an explicit `κ` (`hE : ∀ N, |E N| ≤ 2 - κ`) and uses the uniform `mκ⁻¹`,
`mκ := √(2κ')/2 ≤ (mE (E N)).im` for every `N` (`κ' := min κ 1`, `mE_im_ge`). The other two
theorems use this bound through `eventually_endpoint_etaT_inv_le_sqN` and take the same `κ`.
-/

namespace RBM.CenteredTraceModulus

open Filter MeasureTheory Set Gauss

open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **`η_t⁻¹ ≤ N^2` eventually**, under the regime condition `Cond272NReg`. The constant
`(mE (E N)).im⁻¹` is bounded by the uniform `mκ⁻¹`, `mκ := √(2κ')/2 ≤ (mE (E N)).im` for every
`N` (`mE_im_ge`). -/
private theorem eventually_endpoint_etaT_inv_le_sqN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t : ℕ → ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, t N < 1)
    (hc : 0 < c) (hreg : Cond272NReg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ 2 := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_geN (band d) hE2 ht1 hc hreg.2
  set κ' : ℝ := min κ 1 with hκ'def
  have hκ'0 : 0 < κ' := lt_min hκ0 one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'2 : κ' ≤ 2 := hκ'1.trans (by norm_num)
  have hEκ' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  have hmge : ∀ N, Real.sqrt (2 * κ') / 2 ≤ (mE (E N)).im :=
    fun N => mE_im_ge hκ'0 hκ'2 (hEκ' N)
  have hmpos : 0 < Real.sqrt (2 * κ') / 2 := by positivity
  have hmEN : ∀ N, (mE (E N)).im⁻¹ ≤ (Real.sqrt (2 * κ') / 2)⁻¹ :=
    fun N => inv_anti₀ hmpos (hmge N)
  have hmunif := eventually_le_rpow (Real.sqrt (2 * κ') / 2)⁻¹ (by norm_num : (0 : ℝ) < 1)
  have hm : ∀ᶠ N : ℕ in atTop, (mE (E N)).im⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [hmunif] with N hN
    exact (hmEN N).trans hN
  filter_upwards [hfloor, hm, eventually_ge_atTop (1 : ℕ)]
    with N hfloorN hmN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 < (mE (E N)).im := mE_im_pos (hE2 N)
  have hNfloor : (N : ℝ)⁻¹ ≤ 1 - t N := by
    simpa only [Real.rpow_neg_one] using hfloorN
  have hImfloor : (N : ℝ)⁻¹ ≤ (mE (E N)).im := by
    exact (inv_le_comm₀ hm0 hN0).mp (by simpa only [Real.rpow_one] using hmN)
  have hprod : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ ≤
      (1 - t N) * (mE (E N)).im :=
    mul_le_mul hNfloor hImfloor (by positivity) (by linarith [ht1 N])
  have hηlower : (N : ℝ) ^ (-(2 : ℝ)) ≤ etaT (E N) (t N) := by
    calc
      (N : ℝ) ^ (-(2 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ)⁻¹ := by
        rw [Real.rpow_neg hN0.le, Real.rpow_two]
        simpa only [pow_two] using (inv_pow (N : ℝ) 2).symm
      _ ≤ (1 - t N) * (mE (E N)).im := hprod
      _ = etaT (E N) (t N) := by rw [Step2.etaT_eq]
  have hi := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hηlower
  have hrpow : (N : ℝ) ^ (-(2 : ℝ)) = ((N : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hN0.le, Real.rpow_two]
  rw [hrpow, inv_inv] at hi
  exact hi

/-- **Time modulus of the `true`-charge centered trace**: eventually, on `normGood`,
`‖centeredTrace u - centeredTrace u'‖ ≤ 2 N^5 √|u - u'|` for `u, u' ∈ [s, t]`. It fixes no
energy-dependent constant itself (it takes the external `κ` through
`eventually_endpoint_etaT_inv_le_sqN`). -/
theorem eventually_centeredTrace_true_sub_leN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t : ℕ → ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (_hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ normGood d N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ b : ZMod (d.L N),
          ‖centeredTrace d (E N) N u ω true b -
              centeredTrace d (E N) N u' ω true b‖ ≤
            2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := by
  have hE2 : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hη := eventually_endpoint_etaT_inv_le_sqN d hκ0 hE ht1 hc hreg
  filter_upwards [hη, eventually_ge_atTop (1 : ℕ)] with N hηN hN
  intro ω hω u hu u' hu' b
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hηt0 : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE2 N) (ht1 N)
  have hηt : (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ 2 := hηN
  have hηinv : 0 ≤ (etaT (E N) (t N))⁻¹ := inv_nonneg.mpr hηt0.le
  have hηsq :
      (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ 4 := by
    have hsquare := mul_self_le_mul_self hηinv hηt
    calc
      _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
        simpa only [pow_two] using hsquare
      _ = (N : ℝ) ^ 4 := by ring
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ) := by linarith
  have hcoef :
      (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ *
          (‖Xmat d N ω‖ + 1) ≤ 2 * (N : ℝ) ^ 5 := by
    calc
      _ ≤ (N : ℝ) ^ 4 * (2 * (N : ℝ)) :=
        mul_le_mul hηsq hX1 (by positivity) (by positivity)
      _ = 2 * (N : ℝ) ^ 5 := by ring
  have htrace :
      ‖centeredTrace d (E N) N u ω true b -
          centeredTrace d (E N) N u' ω true b‖ ≤
        ‖green (Hflow d N u ω) (zt (E N) u) -
          green (Hflow d N u' ω) (zt (E N) u')‖ := by
    simp only [centeredTrace, Gsig_true, mSigma_true]
    rw [← Matrix.trace_sub]
    have heq :
        ((green (Hflow d N u ω) (zt (E N) u) -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b -
          (green (Hflow d N u' ω) (zt (E N) u') -
            mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
              Eblk (d.L N) (d.W N) b) =
        (green (Hflow d N u ω) (zt (E N) u) -
          green (Hflow d N u' ω) (zt (E N) u')) *
            Eblk (d.L N) (d.W N) b := by
      noncomm_ring
    rw [heq]
    exact norm_trace_mul_Eblk_le _ b
  refine htrace.trans ((norm_green_flow_sub_le_sqrt d N (hE2 N)
    (hs0 N) (ht1 N) ω hu hu').trans ?_)
  exact mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

/-- **The same time modulus for both charges `σ`.** It takes the external `κ` through
`eventually_centeredTrace_true_sub_leN`. -/
theorem eventually_centeredTrace_sub_leN (d : Dims) {E : ℕ → ℝ} {κ c : ℝ}
    {s t : ℕ → ℝ} (hκ0 : 0 < κ) (hE : ∀ N, |E N| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272NReg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop, ∀ ω ∈ normGood d N,
      ∀ u ∈ Icc (s N) (t N), ∀ u' ∈ Icc (s N) (t N),
        ∀ σ b, ‖centeredTrace d (E N) N u ω σ b -
            centeredTrace d (E N) N u' ω σ b‖ ≤
          2 * (N : ℝ) ^ 5 * Real.sqrt |u - u'| := by
  filter_upwards [eventually_centeredTrace_true_sub_leN d hκ0 hE hs0 hst ht1 hc hreg]
    with N hN
  intro ω hω u hu u' hu' σ b
  have hplus := hN ω hω u hu u' hu' b
  cases σ with
  | false =>
      rw [centeredTrace_false_eq_conj_true, centeredTrace_false_eq_conj_true,
        ← map_sub, Complex.norm_conj]
      exact hplus
  | true => exact hplus

section Compat

end Compat

end
end RBM.CenteredTraceModulus
