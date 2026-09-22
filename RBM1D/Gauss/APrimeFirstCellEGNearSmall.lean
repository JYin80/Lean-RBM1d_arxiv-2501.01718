/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellEGNear
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# First-cut-time near `eGpm` with an arbitrary positive power loss
-/

namespace RBM.APrimeFirstCellEGNearSmall

open Filter Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- The complete near coefficient, including its cubic logarithm, is
subpolynomial at the actual first source time. -/
theorem eventually_cNear_le {τ' : ℝ} (hτ' : 0 < τ')
    {ν : ℝ} (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop,
      Lemma57.cNear (d.W N : ℝ)
        (B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)) ≤
          (N : ℝ) ^ (ν / 4) := by
  have hθ : (0 : ℝ) < ν / 8 := by positivity
  have hlogR : ∀ᶠ W : ℝ in atTop,
      4 * Real.log W ^ (3 : ℝ) ≤ W ^ (ν / 8) := by
    have hsmall := (Asymptotics.isLittleO_iff_nat_mul_le'.1
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hθ)) 4
    filter_upwards [hsmall, eventually_ge_atTop 1] with W hsmall hW1
    have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
    have hp0 : 0 ≤ Real.log W ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
    have hwp0 : 0 ≤ W ^ (ν / 8) := Real.rpow_nonneg (by linarith : 0 ≤ W) _
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg hp0,
      abs_of_nonneg hwp0] using hsmall
  have hlog := (Step2.tendsto_W B).eventually hlogR
  have hExp := (Step2.tendsto_W B).eventually
    (eventually_exp_mul_log_rpow_le 1 hθ)
  have hPow4 : ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) ≤ (d.W N : ℝ) ^ (ν / 8) :=
    ((tendsto_rpow_atTop hθ).comp (Step2.tendsto_W B)).eventually_ge_atTop 4
  filter_upwards [APrimeFirstCellEGNear.eventually_source_scales hτ' 1 1,
    APrimeFirstCellJGCap.eventually_firstTime_T334_scales,
    hlog, hExp, hPow4] with N hs hb hlog hExp hPow4
  dsimp only at hs
  rcases hs with ⟨_, _, hW, _, _, hN, hℓ, _, _, _, _, _, _, _, _, _, _⟩
  rcases hb with ⟨_, _, _, _, _, _, _, hWL, _⟩
  let W : ℝ := d.W N
  let ℓ : ℝ := B.ell N (APrimeFirstCellNearSources.sourceTime τ' N)
  have hWpos : 0 < W := by
    change (0 : ℝ) < (d.W N : ℝ)
    exact_mod_cast d.W_pos N
  have hW1 : 1 ≤ W := (Real.one_le_exp (by norm_num)).trans hW
  have hL1 : (1 : ℝ) ≤ d.L N := by
    have hn : 1 ≤ d.L N := by have := d.three_le_L N; omega
    exact_mod_cast hn
  have hWle : W ≤ (N : ℝ) := by
    have hL0 : 0 ≤ (d.L N : ℝ) - 1 := by linarith
    nlinarith [mul_nonneg hWpos.le hL0]
  have hdiv : 2 / ℓ ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < ℓ)).2
    nlinarith
  change 4 * Real.log W ^ (3 : ℝ) ≤ W ^ (ν / 8) at hlog
  change (4 : ℝ) ≤ W ^ (ν / 8) at hPow4
  have hExp' : Real.exp (Real.log W ^ (3 / 4 : ℝ)) ≤ W ^ (ν / 8) := by
    change Real.exp (1 * Real.log W ^ (3 / 4 : ℝ)) ≤ W ^ (ν / 8) at hExp
    simpa only [one_mul] using hExp
  have hpoly : 2 * Real.log W ^ (3 : ℝ) + 2 / ℓ ≤ W ^ (ν / 8) := by
    nlinarith
  have hc : Lemma57.cNear W ℓ ≤ W ^ (ν / 8) * W ^ (ν / 8) := by
    unfold Lemma57.cNear
    exact mul_le_mul hpoly hExp' (Real.exp_pos _).le
      (Real.rpow_nonneg hWpos.le _)
  calc
    Lemma57.cNear W ℓ ≤ W ^ (ν / 8) * W ^ (ν / 8) := hc
    _ = W ^ (ν / 4) := by
      rw [← Real.rpow_add hWpos]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ (ν / 4) :=
      Real.rpow_le_rpow hWpos.le hWle (by positivity)

/-- Strict exponent slack pays for both the fixed factor `2` and the
already absorbed `W⁻¹` remainder. -/
theorem coefficient_le_rpow {ν W N c : ℝ} (hν : 0 < ν)
    (hN : 1 ≤ N) (hW : 1 ≤ W)
    (hc : c ≤ N ^ (ν / 4))
    (hlarge : 4 ≤ N ^ (ν / 2)) :
    2 * N ^ (min (ν / 8) (1 / 2) + min (ν / 8) (1 / 2)) * c + W⁻¹ ≤
      N ^ ν := by
  let ζ : ℝ := min (ν / 8) (1 / 2)
  have hNpos : 0 < N := by linarith
  have hWpos : 0 < W := by linarith
  have hζ : ζ ≤ ν / 8 := min_le_left _ _
  have hα : ζ + ζ + ν / 4 ≤ ν / 2 := by linarith
  have hWinv : W⁻¹ ≤ (1 : ℝ) := (inv_le_one₀ hWpos).2 hW
  have hpowadd : N ^ (ζ + ζ) * N ^ (ν / 4) = N ^ (ζ + ζ + ν / 4) := by
    rw [← Real.rpow_add hNpos]
  have hsq : (N ^ (ν / 2)) ^ 2 = N ^ ν := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    congr 1
    ring
  calc
    2 * N ^ (ζ + ζ) * c + W⁻¹ ≤
        2 * N ^ (ζ + ζ) * N ^ (ν / 4) + 1 := by
      gcongr
    _ = 2 * N ^ (ζ + ζ + ν / 4) + 1 := by rw [mul_assoc, hpowadd]
    _ ≤ 2 * N ^ (ν / 2) + 1 := by
      gcongr
    _ ≤ N ^ ν := by
      rw [← hsq]
      nlinarith [sq_nonneg (N ^ (ν / 2) - 2)]

/-- The near-output conclusion with the complete first-cut-time loss
absorbed into an arbitrary `N^ν`. -/
def nearBoundSmall (τ' ν : ℝ) (N : ℕ) (ω : Gauss.Ω d) : Prop :=
  ∀ a₁ a₂ : ZMod (d.L N),
    let u := APrimeFirstCellNearSources.sourceTime τ' N
    let ℓu := B.ell N u
    let ℓs := B.ell N (Gauss.firstCellS τ' N)
    let ηu := etaT 0 u
    let r := ℓu / ℓs
    let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
        (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ *
        (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0) ≤
      (N : ℝ) ^ ν * ηu⁻¹ * r ^ 3 *
        tailT (d.W N : ℝ) ℓu ηu 60 dd *
        (if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0)

/-- One source parameter works for every positive loss exponent. At each
exponent the T389 event with its two equal, explicit source losses is high
probability, measurable, eventually inhabited, and located at `N⁻²⁴⁸>0`. -/
theorem exists_highProb_near_small_event :
    ∃ τ' : ℝ, 0 < τ' ∧
      ∀ ν : ℝ, 0 < ν →
        let ζ := min (ν / 8) (1 / 2)
        HighProb (Gauss.P d)
          (APrimeFirstCellNearSources.jointEvent τ' ζ ζ) ∧
        ∀ᶠ N : ℕ in atTop,
          0 < APrimeFirstCellNearSources.sourceTime τ' N ∧
          APrimeFirstCellNearSources.sourceTime τ' N =
            APrimeFirstCellJGCap.firstTime N ∧
          MeasurableSet (APrimeFirstCellNearSources.jointEvent τ' ζ ζ N) ∧
          (∃ ω : Gauss.Ω d,
            ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ ζ N) ∧
          ∀ ω ∈ APrimeFirstCellNearSources.jointEvent τ' ζ ζ N,
            nearBoundSmall τ' ν N ω := by
  obtain ⟨τ', hτ', hsource⟩ :=
    APrimeFirstCellEGNear.exists_highProb_near_event
  refine ⟨τ', hτ', ?_⟩
  intro ν hν
  let ζ : ℝ := min (ν / 8) (1 / 2)
  have hζpos : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζle : ζ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨hp, hbase⟩ := hsource ζ ζ hζpos hζle hζpos
  have hc := eventually_cNear_le hτ' hν
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (ν / 2) :=
    eventually_le_rpow 4 (by positivity)
  refine ⟨hp, ?_⟩
  filter_upwards [hbase, hc, hlarge,
    APrimeFirstCellEGNear.eventually_source_scales hτ' ζ ζ]
    with N hb hc hlarge hsc
  rcases hb with ⟨htime0, htime, hmeas, hne, hnear⟩
  dsimp only at hsc
  rcases hsc with ⟨_, _, hW, _, _, hN, hℓ, _, hr, hη, _, _, _, _, _, _, _⟩
  refine ⟨htime0, htime, hmeas, hne, ?_⟩
  intro ω hω a₁ a₂
  have hb := hnear ω hω a₁ a₂
  dsimp only at hb ⊢
  let u := APrimeFirstCellNearSources.sourceTime τ' N
  let ℓu := B.ell N u
  let ℓs := B.ell N (Gauss.firstCellS τ' N)
  let ηu := etaT 0 u
  let r := ℓu / ℓs
  let dd := (zdist (d.L N) (a₂ - a₁) : ℝ)
  let ind : ℝ := if dd ≤ ellStar (d.W N : ℝ) ℓu then 1 else 0
  let c := 2 * (N : ℝ) ^ (ζ + ζ) * Lemma57.cNear (d.W N : ℝ) ℓu +
    (d.W N : ℝ)⁻¹
  have hW1 : (1 : ℝ) ≤ d.W N :=
    (Real.one_le_exp (by norm_num)).trans hW
  have hcoef : c ≤ (N : ℝ) ^ ν :=
    coefficient_le_rpow hν hN hW1 hc hlarge
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have htail : 0 ≤ tailT (d.W N : ℝ) ℓu ηu 60 dd :=
    (tailT_pos hWpos _).le
  have hind : 0 ≤ ind := ite_nonneg (by norm_num) (by norm_num)
  have hfactor : 0 ≤ ηu⁻¹ * r ^ 3 *
      tailT (d.W N : ℝ) ℓu ηu 60 dd * ind := by
    have hηpos : 0 < ηu := hη
    have hr0 : 0 ≤ r := by linarith
    positivity
  calc
    ‖EGDef.eGpm (d.L N) (d.W N) (mSigma 0)
        (Gauss.Hflow d N u ω) (zt 0 u) a₁ a₂‖ * ind ≤
      c * ηu⁻¹ * r ^ 3 * tailT (d.W N : ℝ) ℓu ηu 60 dd * ind := hb
    _ = c * (ηu⁻¹ * r ^ 3 * tailT (d.W N : ℝ) ℓu ηu 60 dd * ind) := by ring
    _ ≤ (N : ℝ) ^ ν *
        (ηu⁻¹ * r ^ 3 * tailT (d.W N : ℝ) ℓu ηu 60 dd * ind) :=
      mul_le_mul_of_nonneg_right hcoef hfactor
    _ = (N : ℝ) ^ ν * ηu⁻¹ * r ^ 3 *
        tailT (d.W N : ℝ) ℓu ηu 60 dd * ind := by ring

#print axioms eventually_cNear_le
#print axioms coefficient_le_rpow
#print axioms exists_highProb_near_small_event

end RBM.APrimeFirstCellEGNearSmall
