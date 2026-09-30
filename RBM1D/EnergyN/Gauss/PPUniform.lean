/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PPUniform
import RBM1D.EnergyN.Gauss.PPInduction
import RBM1D.EnergyN.Gauss.Step3Charges
import RBM1D.EnergyN.Gauss.Lemma514Holder

/-!
# The uniform `(+,+)` bound at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: the loopwise `(+,+)` bound at each time
(`pp_endpoint_loopwise_plainN`), the same uniformly in time (`stochDom_pp_timeIcc_plainN`), and
the bound on `Ξ^{(L-K)}` for the charges `(+,+)` (`hpp_gauss_plainN`). The five statements of the
`(+,+)` induction are in `RBM1D/EnergyN/Gauss/PPInduction.lean`. No energy-dependent constant is
fixed in this file (the κ-bounds enter through `Grid.pp_endpoint_seq_plainN`/`Grid.ev_Lg_leN` of
`PPInduction.lean`); these three statements use no further `E`-dependent constant and need no
`xiK`-type monotonicity argument.

Energy-dependent dependencies: `Grid.pp_endpoint_seq_plainN` (`PPInduction.lean`),
`Step2.cond272_of_plainN` (`Gauss/Step2Plain.lean`), `Grid.etaT_inv_le_of_plainN`
(`Gauss/Step2Plain.lean`), `hHol_flowN`, `hKb_flowN` (`Gauss/Lemma514Holder.lean`),
`stochDom_flowXiLKSigmaN` (`Gauss/Step3Charges.lean`). Every other callee
(`stochDom_div_factor`, `idx_sigPP_two`, `thetaPP`, `one_le_thetaPP`,
`unifDomIcc_of_forall_stochDom`, `unifDomIcc_mul_scale`, `stochDom_timeIcc_of_unifDom_const`,
`exists_highProb_normX`, `traceMomentBound_gauss`, `Step3.stochDom_mono`, `SumZeroDyn.norm_lkT`)
is energy-free or a generic helper with no `E` binder.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter

variable (d : Dims)

/-! ### The loopwise `(+,+)` bound at each time -/

/-- **`‖lkT_{(+,+)}‖ ≺ thetaPP (W ℓ_v η_v)^{-2}` at each time `v N ∈ [s N, t N]`.** It uses
`Grid.pp_endpoint_seq_plainN` and `Step2.cond272_of_plainN`. -/
theorem pp_endpoint_loopwise_plainN {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (v : ℕ → ℝ) (hv : ∀ N, v N ∈ Set.Icc (s N) (t N)) :
    StochDom (band d).P
      (fun N (a : ZMod ((band d).L N) × ZMod ((band d).L N)) ω =>
        ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω Grid.sigPP ![a.1, a.2]‖)
      (fun N _ _ => thetaPP d s t N * ((band d).scale (E N) N (v N) ^ 2)⁻¹) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hcond : Cond272N (band d) E s t := Step2.cond272_of_plainN hE hst ht1 hreg0
  have h := Grid.pp_endpoint_seq_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hcond hc0 hreg0 hAc v
    (fun N => (hv N).1) (fun N => (hv N).2)
  have hk : ∀ N (_ : ZMod ((band d).L N) × ZMod ((band d).L N)),
      0 < (band d).scale (E N) N (v N) ^ 2 := fun N _ =>
    pow_pos ((band d).scale_pos' (hE N) N ((hs0 N).trans (hv N).1) ((hv N).2.trans_lt (ht1 N))) 2
  refine stochDom_div_factor (k := fun N _ => (band d).scale (E N) N (v N) ^ 2)
    (c := fun N _ => thetaPP d s t N) hk ?_
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono fun ω hω => ?_).trans hN
  obtain ⟨a, ha⟩ := hω
  refine ⟨(), lt_of_lt_of_le ha ?_⟩
  change (band d).scale (E N) N (v N) ^ 2 *
      ‖SumZeroDyn.lkT (sample d) (E N) N (v N) ω Grid.sigPP ![a.1, a.2]‖
    ≤ (band d).scale (E N) N (v N) ^ 2 * Finset.univ.sup' Finset.univ_nonempty
      (fun a' : LoopArg (d.L N) 2 =>
        lkErrMat d (E N) N (v N) (Hflow d N (v N) ω) (LoopData.idx (Grid.sigPP, a')))
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Finset.le_sup' (fun a' : LoopArg (d.L N) 2 =>
    lkErrMat d (E N) N (v N) (Hflow d N (v N) ω) (LoopData.idx (Grid.sigPP, a')))
    (Finset.mem_univ (![a.1, a.2] : LoopArg (d.L N) 2))

/-! ### The `(+,+)` bound uniformly in time -/

/-- **`(W ℓ_u η_u)² |L - K|_{(+,+)} ≺ 1 + R² + R^{5/2}`** uniformly in `u ∈ [s, t]`. It uses
`pp_endpoint_loopwise_plainN`, `Grid.etaT_inv_le_of_plainN`, `hKb_flowN`, `hHol_flowN`. -/
theorem stochDom_pp_timeIcc_plainN {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (band d).scale (E N) N p.1 ^ 2 * (sample d).lkErr (E N) N p.1 ω
          ⟨[true, true], [p.2.1, p.2.2]⟩)
      (fun N _ _ => 1 + Grid.RPP d s t N ^ 2 + Grid.RPP d s t N ^ (5 / 2 : ℝ)) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  -- the quantifier exchange and the scale
  have hkpos : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), 0 < (band d).scale (E N) N u ^ 2 := fun N u hu =>
    pow_pos ((band d).scale_pos' (hE N) N ((hs0 N).trans hu.1) (hu.2.trans_lt (ht1 N))) 2
  have h1 : UnifDomIcc (band d).P s t
      (fun N u (a : ZMod ((band d).L N) × ZMod ((band d).L N)) ω =>
        ‖SumZeroDyn.lkT (sample d) (E N) N u ω Grid.sigPP ![a.1, a.2]‖)
      (fun N u _ _ => thetaPP d s t N * ((band d).scale (E N) N u ^ 2)⁻¹) :=
    unifDomIcc_of_forall_stochDom hst fun v hv =>
      pp_endpoint_loopwise_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc v hv
  have h2 := unifDomIcc_mul_scale hkpos h1
  -- the Hölder modulus at loop length `2`
  obtain ⟨Ξ, hΞ, hXΞ⟩ := exists_highProb_normX d (traceMomentBound_gauss d) (le_refl (2 : ℝ))
  have hη2 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [Grid.etaT_inv_le_of_plainN (band d) hE ht1 hc0 hAc, eventually_ge_atTop 1]
      with N hN hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    refine hN.trans ?_
    have h := Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num : (1 : ℝ) ≤ 2)
    rwa [Real.rpow_one] at h
  have hKb := hKb_flowN (band d) hκ0 hκ1 hEκ ht1 (by norm_num : (0 : ℝ) ≤ 2) 2 hη2
  have h25 : (2 : ℝ) ≤ 2 * ((2 : ℕ) : ℝ) + 1 := by norm_num
  have hHol0 := hHol_flowN d hE hs0 ht1 (c := 2 * ((2 : ℕ) : ℝ) + 1) (by norm_num) (m := 2)
    (by norm_num) (eventually_le_rpow_mono h25 hη2)
    (by
      filter_upwards [hXΞ, eventually_ge_atTop 1] with N hN hN1 ω hω
      exact (hN ω hω).trans
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) h25))
    hKb
  have hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N,
      ∀ a : ZMod ((band d).L N) × ZMod ((band d).L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |(band d).scale (E N) N u ^ 2 *
            ‖SumZeroDyn.lkT (sample d) (E N) N u ω Grid.sigPP ![a.1, a.2]‖
          - (band d).scale (E N) N v ^ 2 *
            ‖SumZeroDyn.lkT (sample d) (E N) N v ω Grid.sigPP ![a.1, a.2]‖|
          ≤ (N : ℝ) ^ ((2 * ((2 : ℕ) : ℝ) + 1) * (3 * ((2 : ℕ) : ℝ) + 4) + 1)
            * |u - v| ^ ((1 : ℝ) / 2) := by
    filter_upwards [hHol0] with N hN ω hω a u hu v hv
    exact hN ω hω (Grid.sigPP, ![a.1, a.2]) u hu v hv
  -- the index set `ZMod L × ZMod L` is polynomial
  have hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (ZMod ((band d).L N) × ZMod ((band d).L N)) : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    filter_upwards [(band d).dim] with N hdim
    have hL : (band d).L N ≤ N :=
      le_trans (Nat.le_mul_of_pos_left _ ((band d).W_pos N)) hdim.1
    have hLr : ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hL
    rw [Fintype.card_prod, ZMod.card, Real.rpow_two]
    push_cast
    have h0 : (0 : ℝ) ≤ (band d).L N := Nat.cast_nonneg _
    nlinarith
  have h3 := stochDom_timeIcc_of_unifDom_const hcard hst
    (fun N => by have h1 := hs0 N; have h2 := ht1 N; linarith)
    (by norm_num : (0 : ℝ) ≤ (2 * ((2 : ℕ) : ℝ) + 1) * (3 * ((2 : ℕ) : ℝ) + 4) + 1)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun N => (zero_le_one.trans (one_le_thetaPP d s t N)))
    (Eventually.of_forall fun N => one_le_thetaPP d s t N) hΞ hHol h2
  have heq : (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (band d).scale (E N) N p.1 ^ 2 * (sample d).lkErr (E N) N p.1 ω
          ⟨[true, true], [p.2.1, p.2.2]⟩)
      = (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        (band d).scale (E N) N (p.1 : ℝ) ^ 2 *
          ‖SumZeroDyn.lkT (sample d) (E N) N (p.1 : ℝ) ω Grid.sigPP ![p.2.1, p.2.2]‖) := by
    funext N p ω
    rw [SumZeroDyn.norm_lkT, idx_sigPP_two]
  rw [heq]
  exact h3

/-! ### `Ξ^{(L-K)}` for the charges `(+,+)` -/

/-- **`Ξ^{(L-K)}_{(+,+)} ≺ 1 + R² + R^{5/2}`** uniformly in time. It uses
`stochDom_pp_timeIcc_plainN`, `stochDom_flowXiLKSigmaN`. -/
theorem hpp_gauss_plainN {κ c : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) {E : ℕ → ℝ}
    (hEκ : ∀ N, |E N| ≤ 2 - κ)
    {s t : ℕ → ℝ} (hB : BoundsCoreN (sample d) E s) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc0 : 0 < c)
    (hreg0 : ∀ᶠ N : ℕ in atTop, (etaT (E N) (s N) / etaT (E N) (t N)) ^ 30 ≤
      (band d).scale (E N) N (t N))
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N)) :
    StochDom (band d).P (fun N => Step3.flowXiLKSigma (sample d) (E N) s t true true N)
      (fun N _ _ => 1 + Grid.RPP d s t N ^ 2 + Grid.RPP d s t N ^ (5 / 2 : ℝ)) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hA : ∀ N (u : TimeIcc s t N), (0 : ℝ) < (band d).scale (E N) N u := fun N u =>
    (band d).scale_pos' (hE N) N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hT1 := stochDom_pp_timeIcc_plainN d hκ0 hκ1 hEκ hB hs0 hst ht1 hc0 hreg0 hAc
  have hraw := stochDom_div_factor
    (ξ := fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
      (sample d).lkErr (E N) N p.1 ω ⟨[true, true], [p.2.1, p.2.2]⟩)
    (k := fun N p => (band d).scale (E N) N p.1 ^ 2)
    (c := fun N _ => thetaPP d s t N) (fun N p => pow_pos (hA N p.1) 2) hT1
  have hbr := stochDom_flowXiLKSigmaN (σ₁ := true) (σ₂ := true)
    (f := fun N u => thetaPP d s t N * ((band d).scale (E N) N u ^ 2)⁻¹) (sample d)
    (fun N u => (hA N u).le) hraw
  refine Step3.stochDom_mono (fun N _ _ => zero_le_one.trans (one_le_thetaPP d s t N)) 1
    (Eventually.of_forall fun N u _ => ?_) hbr
  have hne : (band d).scale (E N) N u ^ 2 ≠ 0 := pow_ne_zero 2 (hA N u).ne'
  change thetaPP d s t N * ((band d).scale (E N) N u ^ 2)⁻¹ * (band d).scale (E N) N u ^ 2
    ≤ 1 * thetaPP d s t N
  rw [one_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one]

section CompatN

end CompatN

end RBM.Gauss

end

