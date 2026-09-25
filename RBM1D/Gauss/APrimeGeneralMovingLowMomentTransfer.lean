/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeAssembly
import RBM1D.Gauss.APrimeGeneralMovingMesh
import RBM1D.Gauss.APrimeGeneralMovingDetFields
import RBM1D.Gauss.APrimeGeneralMovingInitialHinit
import RBM1D.Gauss.APrimeGeneralMovingCommonSources

#check @RBM.APrimeWeight.widenedW
#check @RBM.APrimeAssembly.aprimeSlot_of_widened_family
#check @RBM.APrimeGeneralMovingCommonSources.positive_length_common_support_witness

/-!
# T991: low-order transfer for the actual general-moving widened cutoff

This file only lowers a completed high-order probability moment.  It supplies
no high-order model estimate and makes no A-prime closure claim.
-/

namespace RBM.APrimeGeneralMovingLowMomentTransfer

open Filter MeasureTheory Gauss CutHypTheta MomentDuhamelCut Step2Bootstrap

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The order-free base cutoff underlying the actual piecewise `widenedW`.
On the inactive branch it is one, so its every natural power is one there. -/
noncomputable def baseCutoff (r : ℕ → ℕ) (N₀ : ℕ)
    (J : ℕ → ℝ → Ω d → ℝ) (s t mesh : ℕ → ℝ) (δ : ℝ)
    (N k : ℕ) (ω : Ω d) : ℝ :=
  if k ≤ cutNetTop s t mesh N ∧ N₀ ≤ N then
    APrimeWeight.prefixSoftW (r N) J s mesh N k
      (2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N) ω
  else 1

theorem widenedW_eq_baseCutoff_pow (r : ℕ → ℕ) (N₀ : ℕ)
    (J : ℕ → ℝ → Ω d → ℝ) (s t mesh : ℕ → ℝ) (δ : ℝ)
    (p N k : ℕ) (ω : Ω d) :
    APrimeWeight.widenedW r N₀ J s t mesh δ p N k ω =
      baseCutoff r N₀ J s t mesh δ N k ω ^ (2 * p) := by
  simp [APrimeWeight.widenedW, baseCutoff]

theorem widenedW_active (r : ℕ → ℕ) (N₀ : ℕ)
    (J : ℕ → ℝ → Ω d → ℝ) (s t mesh : ℕ → ℝ) (δ : ℝ)
    (p N k : ℕ) (hN : N₀ ≤ N) (hk : k ≤ cutNetTop s t mesh N)
    (ω : Ω d) :
    APrimeWeight.widenedW r N₀ J s t mesh δ p N k ω =
      APrimeWeight.prefixSoftW (r N) J s mesh N k
        (2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N) ω ^ (2 * p) := by
  simp [APrimeWeight.widenedW, hN, hk]

theorem widenedW_inactive (r : ℕ → ℕ) (N₀ : ℕ)
    (J : ℕ → ℝ → Ω d → ℝ) (s t mesh : ℕ → ℝ) (δ : ℝ)
    (p N k : ℕ) (hactive : ¬ (k ≤ cutNetTop s t mesh N ∧ N₀ ≤ N))
    (ω : Ω d) :
    APrimeWeight.widenedW r N₀ J s t mesh δ p N k ω = 1 := by
  simp [APrimeWeight.widenedW, hactive]

/-- Probability-space Lyapunov transfer for one fixed base cutoff.  The cutoff
and sample observable are identical at orders `p` and `q`; only the power
changes. -/
theorem integral_cutoff_pow_le_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {χ Y : Ω → ℝ} (hχ : ∀ ω, 0 ≤ χ ω)
    (_hlo : Integrable (fun ω => |χ ω * Y ω| ^ (2 * p)) P)
    (hhi : Integrable (fun ω => |χ ω * Y ω| ^ (2 * q)) P) :
    ∫ ω, χ ω ^ (2 * p) * |Y ω| ^ (2 * p) ∂P ≤
      (∫ ω, χ ω ^ (2 * q) * |Y ω| ^ (2 * q) ∂P) ^
        ((p : ℝ) / (q : ℝ)) := by
  have hq : 1 ≤ q := hp.trans hpq
  let Z : Ω → ℝ := fun ω => χ ω * Y ω
  have hmono := MomentDuhamel.momNorm_le_momNorm_of_exponent_le
    (P := P) (p := 2 * p) (q := 2 * q) (by omega) (by omega)
    (Y := Z) hhi
  have hpEq : (fun ω => |Z ω| ^ (2 * p)) =
      fun ω => χ ω ^ (2 * p) * |Y ω| ^ (2 * p) := by
    funext ω
    simp [Z, abs_mul, abs_of_nonneg (hχ ω), mul_pow]
  have hqEq : (fun ω => |Z ω| ^ (2 * q)) =
      fun ω => χ ω ^ (2 * q) * |Y ω| ^ (2 * q) := by
    funext ω
    simp [Z, abs_mul, abs_of_nonneg (hχ ω), mul_pow]
  have hhiZ : Integrable (fun ω => |Z ω| ^ (2 * q)) P := hqEq.symm ▸ hhi
  have hmono := MomentDuhamel.momNorm_le_momNorm_of_exponent_le
    (P := P) (p := 2 * p) (q := 2 * q) (by omega) (by omega)
    (Y := Z) hhiZ
  rw [MomentDuhamel.momNorm_eq_rpow, MomentDuhamel.momNorm_eq_rpow] at hmono
  have hp0 : 0 ≤ ∫ ω, |Z ω| ^ (2 * p) ∂P :=
    integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _
  have hq0 : 0 ≤ ∫ ω, |Z ω| ^ (2 * q) ∂P :=
    integral_nonneg fun ω => pow_nonneg (abs_nonneg _) _
  have hpL : ((∫ ω, |Z ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^
      (2 * (p : ℝ)) = ∫ ω, |Z ω| ^ (2 * p) ∂P := by
    rw [← Real.rpow_mul hp0]
    have hpne : (2 * (p : ℝ)) ≠ 0 := by positivity
    rw [one_div, inv_mul_cancel₀ hpne, Real.rpow_one]
  have hqL : ((∫ ω, |Z ω| ^ (2 * q) ∂P) ^ ((1 : ℝ) / (2 * (q : ℝ)))) ^
      (2 * (p : ℝ)) =
      (∫ ω, |Z ω| ^ (2 * q) ∂P) ^ ((p : ℝ) / (q : ℝ)) := by
    rw [← Real.rpow_mul hq0]
    congr 1
    field_simp
  have hIntP : (∫ ω, χ ω ^ (2 * p) * |Y ω| ^ (2 * p) ∂P) =
      ∫ ω, |Z ω| ^ (2 * p) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => (hpEq).symm ▸ rfl
  have hIntQ : (∫ ω, χ ω ^ (2 * q) * |Y ω| ^ (2 * q) ∂P) =
      ∫ ω, |Z ω| ^ (2 * q) ∂P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω => (hqEq).symm ▸ rfl
  rw [hIntP, hIntQ]
  calc
    ∫ ω, |Z ω| ^ (2 * p) ∂P =
        ((∫ ω, |Z ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^
          (2 * (p : ℝ)) := hpL.symm
    _ ≤ ((∫ ω, |Z ω| ^ (2 * q) ∂P) ^ ((1 : ℝ) / (2 * (q : ℝ)))) ^
          (2 * (p : ℝ)) := by
      exact Real.rpow_le_rpow (Real.rpow_nonneg hp0 _) hmono (by positivity)
    _ = (∫ ω, |Z ω| ^ (2 * q) ∂P) ^ ((p : ℝ) / (q : ℝ)) := hqL

/-- The high-order `N^(δq/2)` estimate passes to every fixed positive order
with the sharp constant `C^(p/q)`.  The chosen `q` is fixed before the
eventual-in-`N` bound is used. -/
theorem low_integral_of_high_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {χ Y : Ω → ℝ} (hχ : ∀ ω, 0 ≤ χ ω)
    (_hlo : Integrable (fun ω => |χ ω * Y ω| ^ (2 * p)) P)
    (hhi : Integrable (fun ω => |χ ω * Y ω| ^ (2 * q)) P)
    {C N δ : ℝ} (hC : 0 < C) (hN : 1 ≤ N) (_hδ : 0 < δ)
    (hhigh : ∫ ω, χ ω ^ (2 * q) * |Y ω| ^ (2 * q) ∂P ≤
      C * N ^ (δ / 2 * (q : ℝ))) :
    ∫ ω, χ ω ^ (2 * p) * |Y ω| ^ (2 * p) ∂P ≤
      C ^ ((p : ℝ) / (q : ℝ)) * N ^ (δ / 2 * (p : ℝ)) := by
  have htransfer := integral_cutoff_pow_le_rpow hp hpq hχ _hlo hhi
  have hnonneg : 0 ≤ ∫ ω, χ ω ^ (2 * q) * |Y ω| ^ (2 * q) ∂P :=
    integral_nonneg fun ω => mul_nonneg (pow_nonneg (hχ ω) _) (by positivity)
  have hExp : 0 < (p : ℝ) / (q : ℝ) := by
    exact div_pos (by exact_mod_cast hp) (by exact_mod_cast (show 0 < q by omega))
  calc
    _ ≤ (∫ ω, χ ω ^ (2 * q) * |Y ω| ^ (2 * q) ∂P) ^
        ((p : ℝ) / (q : ℝ)) := htransfer
    _ ≤ (C * N ^ (δ / 2 * (q : ℝ))) ^ ((p : ℝ) / (q : ℝ)) :=
      Real.rpow_le_rpow hnonneg hhigh hExp.le
    _ = C ^ ((p : ℝ) / (q : ℝ)) * N ^ (δ / 2 * (p : ℝ)) := by
      rw [Real.mul_rpow hC.le (by positivity)]
      rw [← Real.rpow_mul (by positivity : 0 ≤ N)]
      congr 1
      field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (show q ≠ 0 by omega)]

/-- Family form with the A-prime quantifier order: first fix `δ` and `p`,
then choose the high order and its constant, and only afterward take `N`
eventually.  `Y N k` is the same observable at all orders. -/
theorem eventually_low_family_of_high_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s t mesh : ℕ → ℝ} {δ₀ : ℝ} {χ : ℝ → ℕ → ℕ → Ω → ℝ}
    {Y : ℕ → ℕ → Ω → ℝ} (qOf : ℝ → ℕ → ℕ)
    (hqOf : ∀ δ p, 1 ≤ p → p ≤ qOf δ p)
    (hχ0 : ∀ δ N k ω, 0 ≤ χ δ N k ω)
    (hInt : ∀ δ p N k,
      Integrable (fun ω => |χ δ N k ω * Y N k ω| ^ (2 * p)) P)
    (hHigh : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ q : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∫ ω, χ δ N k ω ^ (2 * q) * |Y N k ω| ^ (2 * q) ∂P
          ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ))) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∫ ω, χ δ N k ω ^ (2 * p) * |Y N k ω| ^ (2 * p) ∂P
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  intro δ hδ hδ₀ p
  by_cases hp : p = 0
  · subst p
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N k hk
    simp
  · have hp1 : 1 ≤ p := by omega
    let q := qOf δ p
    have hpq : p ≤ q := hqOf δ p hp1
    obtain ⟨C, hC, hCev⟩ := hHigh δ hδ hδ₀ q
    have hqpos : 0 < q := by omega
    have hpqexp : 0 < (p : ℝ) / (q : ℝ) :=
      div_pos (by exact_mod_cast hp1) (by exact_mod_cast hqpos)
    refine ⟨C ^ ((p : ℝ) / (q : ℝ)),
      Real.rpow_pos_of_pos hC ((p : ℝ) / (q : ℝ)), ?_⟩
    filter_upwards [hCev, eventually_ge_atTop (1 : ℕ)] with N hN hN1 k hk
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hlow := low_integral_of_high_integral hp1 hpq
      (hχ0 δ N k) (hInt δ p N k) (hInt δ q N k) hC hNr hδ (hN k hk)
    exact hlow

/-- At order zero the actual probability integral is exactly one, including
the inactive branch of the piecewise widened weight. -/
theorem zero_order_widened_integral (τ' delta : ℝ) (N k : ℕ) :
    ∫ ω, APrimeWeight.widenedW
        (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
          (APrimeGeneralMovingMesh.targetMesh 60)) 1
        (APrimeGeneralMovingDetFields.J 0 60 (fun _ => 0))
        (fun _ => 0) (firstCellT τ') (APrimeGeneralMovingMesh.targetMesh 60)
        delta 0 N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * delta))
        (APrimeGeneralMovingDetFields.J 0 60 (fun _ => 0) N
          (cutNetPt (fun _ => 0) (APrimeGeneralMovingMesh.targetMesh 60) N k) ω)| ^ 0
      ∂(Gauss.band d).P = 1 := by
  let r := APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
    (APrimeGeneralMovingMesh.targetMesh 60)
  let J := APrimeGeneralMovingDetFields.J 0 60 (fun _ => 0)
  have hweight : ∀ ω, APrimeWeight.widenedW r 1 J (fun _ => 0)
      (firstCellT τ') (APrimeGeneralMovingMesh.targetMesh 60)
      delta 0 N k ω = 1 := by
    intro ω
    rw [APrimeWeight.widenedW]
    split_ifs <;> simp
  have hweight' : ∀ ω, APrimeWeight.widenedW
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
        (APrimeGeneralMovingMesh.targetMesh 60)) 1
      (APrimeGeneralMovingDetFields.J 0 60 (fun _ => 0))
      (fun _ => 0) (firstCellT τ') (APrimeGeneralMovingMesh.targetMesh 60)
      delta 0 N k ω = 1 := by
    simpa only [r, J] using hweight
  have heq : (fun ω => APrimeWeight.widenedW
      (APrimeWeight.canonicalR (fun _ => 0) (firstCellT τ')
        (APrimeGeneralMovingMesh.targetMesh 60)) 1
      (APrimeGeneralMovingDetFields.J 0 60 (fun _ => 0))
      (fun _ => 0) (firstCellT τ') (APrimeGeneralMovingMesh.targetMesh 60)
      delta 0 N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * delta))
        (APrimeGeneralMovingDetFields.J 0 60 (fun _ => 0) N
          (cutNetPt (fun _ => 0) (APrimeGeneralMovingMesh.targetMesh 60) N k) ω)| ^ 0) =
      fun _ => (1 : ℝ) := by
    funext ω
    rw [hweight' ω]
    simp
  rw [heq]
  simp [Gauss.band]

/-- Repaired family interface: the observable may depend on `δ`, and the
high-order estimate is requested only at a selected order `q ≥ p`.  The
selection and its constant precede the eventual bound in `N`. -/
theorem eventually_low_family_of_selected_high_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s t mesh : ℕ → ℝ} {δ₀ : ℝ} {χ : ℝ → ℕ → ℕ → Ω → ℝ}
    {Y : ℝ → ℕ → ℕ → Ω → ℝ}
    (hχ0 : ∀ δ N k ω, 0 ≤ χ δ N k ω)
    (hInt : ∀ δ p N k, 1 ≤ N →
      Integrable (fun ω => |χ δ N k ω * Y δ N k ω| ^ (2 * p)) P)
    (hHigh : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
          ∫ ω, χ δ N k ω ^ (2 * q) * |Y δ N k ω| ^ (2 * q) ∂P
            ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ))) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∫ ω, χ δ N k ω ^ (2 * p) * |Y δ N k ω| ^ (2 * p) ∂P
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  intro δ hδ hδ₀ p
  by_cases hp : p = 0
  · subst p
    refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro N k hk
    simp
  · have hp1 : 1 ≤ p := by omega
    obtain ⟨q, hpq, C, hC, hCev⟩ := hHigh δ hδ hδ₀ p hp1
    refine ⟨C ^ ((p : ℝ) / (q : ℝ)),
      Real.rpow_pos_of_pos hC ((p : ℝ) / (q : ℝ)), ?_⟩
    filter_upwards [hCev, eventually_ge_atTop (1 : ℕ)] with N hN hN1 k hk
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact low_integral_of_high_integral hp1 hpq
      (hχ0 δ N k) (hInt δ p N k hN1) (hInt δ q N k hN1)
      hC hNr hδ (hN k hk)

/-- The selected-high-order interface specializes literally to the Gaussian
`jSnorm` at `cutNetPt`, with truncation level `N^(2δ)` and the actual widened
prefix weight.  No high-order Gaussian estimate is asserted here. -/
theorem eventually_actual_widened_family_of_selected_high
    (E D : ℝ) (s t mesh : ℕ → ℝ) (δ₀ : ℝ)
    (hHigh : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
          ∫ ω, APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
            (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
            s t mesh δ q N k ω *
            |cutTrunc ((N : ℝ) ^ (2 * δ))
              (Step2Moment.jSnorm (Gauss.sample d) E D s N
                (cutNetPt s mesh N k) ω)| ^ (2 * q) ∂(Gauss.band d).P
            ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ))) :
    ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ,
      ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∫ ω, APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
          (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
          s t mesh δ p N k ω *
          |cutTrunc ((N : ℝ) ^ (2 * δ))
            (Step2Moment.jSnorm (Gauss.sample d) E D s N
              (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂(Gauss.band d).P
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ)) := by
  letI := (Gauss.band d).isProbabilityMeasure
  let J : ℕ → ℝ → Ω d → ℝ := fun N u ω =>
    Step2Moment.jSnorm (Gauss.sample d) E D s N u ω
  let r := APrimeWeight.canonicalR s t mesh
  let χ : ℝ → ℕ → ℕ → Ω d → ℝ := fun δ N k ω =>
    baseCutoff r 1 J s t mesh δ N k ω
  let Y : ℝ → ℕ → ℕ → Ω d → ℝ := fun δ N k ω =>
    cutTrunc ((N : ℝ) ^ (2 * δ)) (J N (cutNetPt s mesh N k) ω)
  have hJ0 : ∀ N u ω, 0 ≤ J N u ω := by
    intro N u ω
    exact div_nonneg
      (zero_le_one.trans (Step2Moment.one_le_jS (Gauss.sample d) N u ω))
      (by positivity)
  have hJm : ∀ N u, Measurable (J N u) := fun N u =>
    APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E D s N u
  have hχ0 : ∀ δ N k ω, 0 ≤ χ δ N k ω := by
    intro δ N k ω
    simp only [χ, baseCutoff]
    split_ifs
    · exact softW_nonneg _ _ _ _
    · norm_num
  have hInt : ∀ δ p N k, 1 ≤ N →
      Integrable (fun ω => |χ δ N k ω * Y δ N k ω| ^ (2 * p)) (Gauss.band d).P := by
    intro δ p N k hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hθ : 0 < (N : ℝ) ^ (2 * δ) := Real.rpow_pos_of_pos hNr _
    have h := Step2Bootstrap.integrable_weight_mul
      (P := (Gauss.band d).P)
      (W := APrimeWeight.widenedW r 1 J s t mesh δ p N k)
      (g := J N (cutNetPt s mesh N k)) hθ
      (APrimeWeight.widenedW_nonneg r 1 J s t mesh δ p N k)
      (APrimeWeight.widenedW_le_one r 1 J s t mesh δ p N k)
      (APrimeWeight.widenedW_meas r 1 J s t mesh (fun N u => hJm N u) p δ N k)
      (hJ0 N _) (hJm N _).aestronglyMeasurable (2 * p)
    convert h using 1
    funext ω
    simp [Y, χ, widenedW_eq_baseCutoff_pow, abs_mul,
      abs_of_nonneg (hχ0 δ N k ω), mul_pow]
  have hHigh' : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∃ q : ℕ, p ≤ q ∧ ∃ C > (0 : ℝ),
        ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
          ∫ ω, χ δ N k ω ^ (2 * q) * |Y δ N k ω| ^ (2 * q) ∂(Gauss.band d).P
            ≤ C * (N : ℝ) ^ (δ / 2 * (q : ℝ)) := by
    intro δ hδ hδ₀ p hp
    obtain ⟨q, hpq, C, hC, hev⟩ := hHigh δ hδ hδ₀ p hp
    refine ⟨q, hpq, C, hC, ?_⟩
    filter_upwards [hev] with N hN k hk
    simpa only [widenedW_eq_baseCutoff_pow, χ, Y, J, r] using hN k hk
  have h := eventually_low_family_of_selected_high_family
    (s := s) (t := t) (mesh := mesh) (δ₀ := δ₀) hχ0 hInt hHigh'
  intro δ hδ hδ₀ p
  obtain ⟨C, hC, hev⟩ := h δ hδ hδ₀ p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with N hN k hk
  simpa only [widenedW_eq_baseCutoff_pow, χ, Y, J, r] using hN k hk

/-- Order zero is exactly one for every Gaussian parameter, mesh point, and
branch of the actual piecewise widened weight. -/
theorem actual_zero_order_widened_integral
    (E D : ℝ) (s t mesh : ℕ → ℝ) (δ : ℝ) (N k : ℕ) :
    ∫ ω, APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
        (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
        s t mesh δ 0 N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ))
        (Step2Moment.jSnorm (Gauss.sample d) E D s N
          (cutNetPt s mesh N k) ω)| ^ (2 * 0) ∂(Gauss.band d).P = 1 := by
  have hweight : ∀ ω : Ω d, APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t mesh) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E D s N u ω)
      s t mesh δ 0 N k ω = 1 := by
    intro ω
    rw [APrimeWeight.widenedW]
    split_ifs <;> simp
  simp only [hweight, mul_zero, pow_zero, mul_one]
  simp [Gauss.band]

#print axioms integral_cutoff_pow_le_rpow
#print axioms low_integral_of_high_integral
#print axioms eventually_low_family_of_high_family
#print axioms zero_order_widened_integral
#print axioms eventually_low_family_of_selected_high_family
#print axioms eventually_actual_widened_family_of_selected_high
#print axioms actual_zero_order_widened_integral

end
end RBM.APrimeGeneralMovingLowMomentTransfer
