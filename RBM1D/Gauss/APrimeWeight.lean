/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSlotFields
import RBM1D.Gauss.APrimePrior
import RBM1D.Gauss.APrimeOneStep

/-!
# T280a: prefix soft weights for the first A-prime pass

The weight in the structural interface is independent of the moment order.  The widened
weight used to estimate a particular moment may depend on that order.  The two weights are
compared within each one-step integral.  The prefix propagation theorem uses only earlier
net points; it starts at index one, as the initial index has an empty prefix.
-/

namespace RBM
namespace APrimeWeight

open Real Filter MeasureTheory Step2Bootstrap MomentDuhamelCut CutHypTheta Cutoff

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The soft maximum over precisely the net points earlier than `k`. -/
noncomputable def prefixSoftW (r : ℕ) (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ)
    (N k : ℕ) (θ : ℝ) (ω : Ω) : ℝ :=
  softW r (Finset.range k) (fun j => J N (cutNetPt s mesh N j) ω) θ

theorem measurable_prefixSoftW (r : ℕ) (J : ℕ → ℝ → Ω → ℝ) (s mesh : ℕ → ℝ)
    (N k : ℕ) (θ : ℝ) (hJ : ∀ u, Measurable (fun ω => J N u ω)) :
    Measurable (prefixSoftW r J s mesh N k θ) := by
  unfold prefixSoftW softW softMax
  have hsum : Measurable (fun ω =>
      ∑ j ∈ Finset.range k, J N (cutNetPt s mesh N j) ω ^ (2 * r)) := by
    exact Finset.measurable_sum _ fun j _ => (hJ _).pow_const _
  exact differentiable_cutChi.continuous.measurable.comp
    (((Real.continuous_rpow_const (by positivity :
        (0 : ℝ) ≤ (1 : ℝ) / (2 * (r : ℝ)))).measurable.comp hsum).div_const θ)

/-- The weight is one on the finite prefix event.  The calibration is uniform in `k`. -/
theorem one_le_prefixSoftW_of_prefNet {r : ℕ} (hr : 1 ≤ r)
    {J : ℕ → ℝ → Ω → ℝ} {s mesh : ℕ → ℝ} {N k : ℕ} {Λ κ : ℝ}
    (hΛ : 0 < Λ) (hκ : 0 < κ)
    (hcard : (k : ℝ) ^ ((1 : ℝ) / (2 * (r : ℝ))) ≤ κ)
    (hJ0 : ∀ u ω, 0 ≤ J N u ω)
    {ω : Ω} (hω : ω ∈ prefNet J s mesh (fun _ _ => Λ) N k) :
    1 ≤ prefixSoftW r J s mesh N k (κ * Λ) ω := by
  unfold prefixSoftW
  apply one_le_softW hr hΛ hκ (by simpa using hcard)
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  rw [abs_of_nonneg (hJ0 _ _)]
  exact hω j hjk

/-- Support of the prefix weight propagates to the whole prefix interval. -/
theorem le_of_prefixSoftW_ne_zero_of_modulus {r : ℕ} (hr : 1 ≤ r)
    {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ} {N k : ℕ}
    {Kmod γ θ Θ : ℝ} (hγ : 0 < γ) (hθ : 0 < θ)
    (hst : s N ≤ t N) (hm : 0 < mesh N) (hk : 1 ≤ k)
    (hkT : k ≤ cutNetTop s t mesh N) {ω : Ω}
    (hne : prefixSoftW r J s mesh N k θ ω ≠ 0)
    (hmod : ∀ v ∈ Set.Icc (s N) (t N), ∀ w ∈ Set.Icc (s N) (t N),
      |J N v ω - J N w ω| ≤ (N : ℝ) ^ Kmod * |v - w| ^ γ)
    (hfine : (N : ℝ) ^ Kmod * (1 / mesh N) ^ γ ≤ Θ) :
    ∀ v ∈ Set.Icc (s N) (cutNetPt s mesh N k), J N v ω ≤ 2 * θ + Θ := by
  apply prefix_of_modulus hγ hst hm hk hkT hmod hfine
  intro j hj
  have hbound : |J N (cutNetPt s mesh N j) ω| ≤ 2 * θ :=
    abs_le_two_mul_of_softW_ne_zero hr hθ hne (Finset.mem_range.mpr hj)
  exact (le_abs_self _).trans hbound

/-- The narrow cutoff is bounded by every moment power of the doubled cutoff. -/
theorem softW_le_widened_pow (r : ℕ) (S : Finset ℕ) (ρ : ℕ → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (p : ℕ) :
    softW r S ρ θ ≤ (softW r S ρ (2 * θ)) ^ (2 * p) := by
  by_cases h : softMax r S ρ ≤ 2 * θ
  · have hwide : softW r S ρ (2 * θ) = 1 := by
      unfold softW
      exact cutChi_eq_one ((div_le_one (by positivity)).2 h)
    rw [hwide, one_pow]
    exact softW_le_one _ _ _ _
  · have hnarrow : softW r S ρ θ = 0 := by
      unfold softW
      exact cutChi_eq_zero ((le_div_iff₀ hθ).2 (le_of_lt (lt_of_not_ge h)))
    rw [hnarrow]
    exact pow_nonneg (softW_nonneg _ _ _ _) _

/-- A prefix cutoff at the ordinary threshold on the active range, and `1` elsewhere.
The boundary is chosen independently of `δ`, so all four interface properties hold for
every `δ,N,k`, including small `N` and indices beyond the net. -/
noncomputable def piecewiseW (r : ℕ → ℕ) (N₀ : ℕ) (J : ℕ → ℝ → Ω → ℝ)
    (s t mesh : ℕ → ℝ) (δ : ℝ) (N k : ℕ) (ω : Ω) : ℝ :=
  if k ≤ cutNetTop s t mesh N ∧ N₀ ≤ N then
    prefixSoftW (r N) J s mesh N k
      (Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N) ω
  else 1

/-- The order-dependent widened cutoff used inside the `2p` moment estimate. -/
noncomputable def widenedW (r : ℕ → ℕ) (N₀ : ℕ) (J : ℕ → ℝ → Ω → ℝ)
    (s t mesh : ℕ → ℝ) (δ : ℝ) (p N k : ℕ) (ω : Ω) : ℝ :=
  if k ≤ cutNetTop s t mesh N ∧ N₀ ≤ N then
    (prefixSoftW (r N) J s mesh N k
      (2 * Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N) ω) ^ (2 * p)
  else 1

theorem piecewiseW_meas {P : Measure Ω} (r : ℕ → ℕ) (N₀ : ℕ)
    (J : ℕ → ℝ → Ω → ℝ) (s t mesh : ℕ → ℝ)
    (hJ : ∀ N u, Measurable (fun ω => J N u ω)) (δ : ℝ) (N k : ℕ) :
    AEStronglyMeasurable (piecewiseW r N₀ J s t mesh δ N k) P := by
  unfold piecewiseW
  split_ifs
  · exact (measurable_prefixSoftW (r N) J s mesh N k _ (hJ N)).aestronglyMeasurable
  · exact aestronglyMeasurable_const

theorem piecewiseW_nonneg (r : ℕ → ℕ) (N₀ : ℕ) (J : ℕ → ℝ → Ω → ℝ)
    (s t mesh : ℕ → ℝ) (δ : ℝ) (N k : ℕ) (ω : Ω) :
    0 ≤ piecewiseW r N₀ J s t mesh δ N k ω := by
  unfold piecewiseW
  split_ifs
  · exact softW_nonneg _ _ _ _
  · norm_num

theorem piecewiseW_le_one (r : ℕ → ℕ) (N₀ : ℕ) (J : ℕ → ℝ → Ω → ℝ)
    (s t mesh : ℕ → ℝ) (δ : ℝ) (N k : ℕ) (ω : Ω) :
    piecewiseW r N₀ J s t mesh δ N k ω ≤ 1 := by
  unfold piecewiseW
  split_ifs
  · exact softW_le_one _ _ _ _
  · exact le_rfl

theorem widenedW_meas {P : Measure Ω} (r : ℕ → ℕ) (N₀ : ℕ)
    (J : ℕ → ℝ → Ω → ℝ) (s t mesh : ℕ → ℝ)
    (hJ : ∀ N u, Measurable (fun ω => J N u ω)) (p : ℕ) (δ : ℝ) (N k : ℕ) :
    AEStronglyMeasurable (widenedW r N₀ J s t mesh δ p N k) P := by
  unfold widenedW
  split_ifs
  · exact ((measurable_prefixSoftW (r N) J s mesh N k _ (hJ N)).pow_const
      (2 * p)).aestronglyMeasurable
  · exact aestronglyMeasurable_const

theorem widenedW_nonneg (r : ℕ → ℕ) (N₀ : ℕ) (J : ℕ → ℝ → Ω → ℝ)
    (s t mesh : ℕ → ℝ) (δ : ℝ) (p N k : ℕ) (ω : Ω) :
    0 ≤ widenedW r N₀ J s t mesh δ p N k ω := by
  unfold widenedW
  split_ifs
  · exact pow_nonneg (softW_nonneg _ _ _ _) _
  · norm_num

theorem widenedW_le_one (r : ℕ → ℕ) (N₀ : ℕ) (J : ℕ → ℝ → Ω → ℝ)
    (s t mesh : ℕ → ℝ) (δ : ℝ) (p N k : ℕ) (ω : Ω) :
    widenedW r N₀ J s t mesh δ p N k ω ≤ 1 := by
  unfold widenedW
  split_ifs
  · unfold prefixSoftW
    simpa using pow_le_pow_left₀ (softW_nonneg _ _ _ _)
      (softW_le_one _ _ _ _) (2 * p)
  · exact le_rfl

/-- The unconditional interface field `W_dom`, under a uniform calibration of the
finite prefix cardinality.  The calibration is independent of `δ`. -/
theorem piecewiseW_dom {r : ℕ → ℕ} {N₀ : ℕ}
    {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ}
    (hN₀ : 1 ≤ N₀) (hr : ∀ N, 1 ≤ r N)
    (hcalib : ∀ N k, N₀ ≤ N → k ≤ cutNetTop s t mesh N →
      (k : ℝ) ^ ((1 : ℝ) / (2 * (r N : ℝ))) ≤ Real.exp 1)
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω)
    (δ : ℝ) (N k : ℕ) (ω : Ω)
    (hω : ω ∈ prefNet J s mesh (fun N _ => (N : ℝ) ^ (2 * δ) * 1) N k) :
    1 ≤ piecewiseW r N₀ J s t mesh δ N k ω := by
  unfold piecewiseW
  split_ifs with ha
  · have hN : 1 ≤ N := hN₀.trans ha.2
    have hΛ : 0 < APrimePrior.priorLevel δ (fun _ => 1) N :=
      APrimePrior.priorLevel_pos hN (by norm_num)
    have hω' : ω ∈ prefNet J s mesh
        (fun _ _ => APrimePrior.priorLevel δ (fun _ => 1) N) N k := by
      intro j hj
      simpa [APrimePrior.priorLevel] using hω j hj
    exact one_le_prefixSoftW_of_prefNet (hr N) hΛ (Real.exp_pos 1)
      (hcalib N k ha.2 ha.1) (hJ0 N) hω'
  · exact le_rfl

/-- A concrete cardinal calibration.  Taking the even order `2(top+1)` makes the soft
maximum's cardinal factor at most `e` for every prefix, at every `N`. -/
theorem card_calib_top (n k : ℕ) (hk : k ≤ n) :
    (k : ℝ) ^ ((1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) ≤ Real.exp 1 := by
  have hd : (0 : ℝ) < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  have he : (0 : ℝ) < (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ)) := by positivity
  by_cases hk0 : k = 0
  · subst k
    push_cast
    have he' : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    rw [Real.zero_rpow he'.ne']
    exact (Real.exp_pos 1).le
  · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
    have hlog : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
    have hkn : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ_of_le hk
    rw [Real.rpow_def_of_pos hkpos]
    apply Real.exp_le_exp.mpr
    have hden : Real.log (k : ℝ) ≤ 2 * ((n + 1 : ℕ) : ℝ) := by linarith
    simpa [div_eq_mul_inv] using (div_le_one hd).mpr hden

/-- The canonical choice of soft-max order.  It avoids any unsatisfied asymptotic
cardinality assumption; a logarithmic-order optimization can be substituted later. -/
noncomputable def canonicalR (s t mesh : ℕ → ℝ) (N : ℕ) : ℕ :=
  cutNetTop s t mesh N + 1

theorem piecewiseW_dom_canonical
    {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ}
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω)
    (δ : ℝ) (N k : ℕ) (ω : Ω)
    (hω : ω ∈ prefNet J s mesh (fun N _ => (N : ℝ) ^ (2 * δ) * 1) N k) :
    1 ≤ piecewiseW (canonicalR s t mesh) 1 J s t mesh δ N k ω := by
  refine piecewiseW_dom (r := canonicalR s t mesh) (N₀ := 1)
    (by norm_num) (fun N => by simp [canonicalR]) ?_ hJ0 δ N k ω hω
  intro N' k' _ hk'
  simpa [canonicalR] using card_calib_top (cutNetTop s t mesh N') k' hk'

theorem piecewiseW_le_widenedW {r : ℕ → ℕ} {N₀ : ℕ}
    {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ}
    (hN₀ : 1 ≤ N₀) (δ : ℝ) (p N k : ℕ) (ω : Ω) :
    piecewiseW r N₀ J s t mesh δ N k ω ≤
      widenedW r N₀ J s t mesh δ p N k ω := by
  unfold piecewiseW widenedW
  split_ifs with ha
  · have hN : 1 ≤ N := hN₀.trans ha.2
    have hθ : 0 < Real.exp 1 * APrimePrior.priorLevel δ (fun _ => 1) N :=
      mul_pos (Real.exp_pos 1) (APrimePrior.priorLevel_pos hN (by norm_num))
    simpa [prefixSoftW, mul_assoc] using
      softW_le_widened_pow (r N) (Finset.range k)
        (fun j => J N (cutNetPt s mesh N j) ω) hθ p
  · exact le_rfl

/-- A one-step estimate proved with a moment-order-dependent widened weight gives the
`p`-independent weight required by `APrimeHypOn`.  The comparison is made inside each
integral, so the existing `weightedMoment_mono` (whose larger weight is fixed over `p`)
cannot replace this lemma. -/
theorem weightedMoment_of_stepBound_mono {P : Measure Ω} [IsProbabilityMeasure P]
    {J : ℕ → ℝ → Ω → ℝ} {s t mesh : ℕ → ℝ}
    {lev : ℕ → ℝ → ℝ} {Θ : ℕ → ℝ}
    {W : ℝ → ℕ → ℕ → Ω → ℝ}
    {Wp : ℕ → ℝ → ℕ → ℕ → Ω → ℝ} {δ₀ m : ℝ}
    (hm : 0 < m) (hΘ : ∀ N, Θ N = 1)
    (hmesh : ∀ N, 0 < mesh N) (hwin : ∀ N, s N ≤ t N)
    (hlev : ∀ N, ∀ u ∈ Set.Icc (s N) (t N), Θ N ≤ lev N u)
    (hJ0 : ∀ N u ω, 0 ≤ J N u ω)
    (hJm : ∀ N u, AEStronglyMeasurable (fun ω => J N u ω) P)
    (hW0 : ∀ δ N k ω, 0 ≤ W δ N k ω)
    (hW1 : ∀ δ N k ω, W δ N k ω ≤ 1)
    (hWm : ∀ δ N k, AEStronglyMeasurable (fun ω => W δ N k ω) P)
    (hWp0 : ∀ p δ N k ω, 0 ≤ Wp p δ N k ω)
    (hWp1 : ∀ p δ N k ω, Wp p δ N k ω ≤ 1)
    (hWpm : ∀ p δ N k, AEStronglyMeasurable (fun ω => Wp p δ N k ω) P)
    (hle : ∀ p δ N k ω, W δ N k ω ≤ Wp p δ N k ω)
    (H : ∀ δ, 0 < δ → δ ≤ δ₀ → ∀ p : ℕ, 1 ≤ p →
      ∀ᶠ N : ℕ in atTop, ∀ k ≤ cutNetTop s t mesh N,
        ∃ R Ξ A ε q β γ κ Jv : ℝ,
          StepSideAPrime.StepSide'' ((N : ℝ) ^ (δ / 8)) R Ξ A ε q β γ κ Jv ∧
          ∫ ω, Wp p δ N k ω *
              |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
                (J N (cutNetPt s mesh N k) ω)| ^ (2 * p) ∂P
            ≤ (StepSideAPrime.stepRhs'' m ((N : ℝ) ^ (δ / 8))
                R Ξ A ε q β γ κ Jv / R ^ 4) ^ (2 * p)) :
    WeightedMoment P J s t mesh lev Θ δ₀ W := by
  refine APrimeOneStep.weightedMoment_of_stepBoundPos'' hm hΘ hW0 hW1 hWm ?_
  intro δ hδ0 hδ p hp
  filter_upwards [H δ hδ0 hδ p hp, eventually_ge_atTop 1] with N hN hN1 k hk
  obtain ⟨R, Ξ, A, ε, q, β, γ, κ, Jv, hside, hbound⟩ := hN k hk
  refine ⟨R, Ξ, A, ε, q, β, γ, κ, Jv, hside, ?_⟩
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hmem : cutNetPt s mesh N k ∈ Set.Icc (s N) (t N) :=
    netFinset_subset_Icc (hwin N) (hmesh N) _ (cutNetPt_mem_netFinset hk)
  have hθ : 0 < (N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k) := by
    have hlev0 : 0 < lev N (cutNetPt s mesh N k) := by
      have hΘ0 : 0 < Θ N := by rw [hΘ]; norm_num
      exact hΘ0.trans_le (hlev N _ hmem)
    exact mul_pos (Real.rpow_pos_of_pos hNR _) hlev0
  have hRi : Integrable (fun ω => Wp p δ N k ω *
      |cutTrunc ((N : ℝ) ^ (2 * δ) * lev N (cutNetPt s mesh N k))
        (J N (cutNetPt s mesh N k) ω)| ^ (2 * p)) P :=
    integrable_weight_mul hθ (hWp0 p δ N k) (hWp1 p δ N k)
      (hWpm p δ N k) (fun ω => hJ0 N _ ω)
      (hJm N (cutNetPt s mesh N k)) (2 * p)
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => ?_) hRi
    (Filter.Eventually.of_forall fun ω => ?_)).trans hbound
  · exact mul_nonneg (hW0 δ N k ω) (by positivity)
  · exact mul_le_mul_of_nonneg_right (hle p δ N k ω) (by positivity)

/-- The four weight fields specialized to the complete `jSnorm` functional.  These are
the exact fields left open by `APrimeSlotFields.aprimeHypOn_jSnorm_event`. -/
theorem jSnorm_piecewiseW_fields {P : Measure Ω} {B : Band Ω}
    (X : Sample B) (E D : ℝ) (s t mesh : ℕ → ℝ) :
    let J := fun N u ω => Step2Moment.jSnorm X E D s N u ω
    let W := piecewiseW (canonicalR s t mesh) 1 J s t mesh
    (∀ δ N k, AEStronglyMeasurable (fun ω => W δ N k ω) P) ∧
    (∀ δ N k ω, 0 ≤ W δ N k ω) ∧
    (∀ δ N k ω, W δ N k ω ≤ 1) ∧
    (∀ δ N k ω,
      ω ∈ prefNet J s mesh (fun N _ => (N : ℝ) ^ (2 * δ) * 1) N k →
        1 ≤ W δ N k ω) := by
  dsimp
  have hJ0 : ∀ N u ω, 0 ≤ Step2Moment.jSnorm X E D s N u ω := by
    intro N u ω
    have h1 : (0 : ℝ) ≤ Step2.jS X E D N u ω :=
      le_trans zero_le_one (Step2Moment.one_le_jS X N u ω)
    have h2 : (0 : ℝ) ≤ Step2Moment.ratR E s N u ^ 4 := by positivity
    exact div_nonneg h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro δ N k
    exact piecewiseW_meas _ _ _ _ _ _
      (fun N u => APrimeSlotFields.measurable_jSnorm X E D s N u) δ N k
  · intro δ N k ω
    exact piecewiseW_nonneg (canonicalR s t mesh) 1 _ s t mesh δ N k ω
  · intro δ N k ω
    exact piecewiseW_le_one (canonicalR s t mesh) 1 _ s t mesh δ N k ω
  · intro δ N k ω hω
    exact piecewiseW_dom_canonical hJ0 δ N k ω hω

section Witness

private def satS : ℕ → ℝ := fun _ => 0
private def satT : ℕ → ℝ := fun _ => 1
private def satMesh : ℕ → ℝ := fun _ => 1
private def satJ : ℕ → ℝ → ℝ → ℝ := fun _ _ ω => max ω 0

private theorem sat_top : cutNetTop satS satT satMesh 1 = 1 := by
  norm_num [cutNetTop, satS, satT, satMesh]

/-- The piecewise cutoff has a nonempty support and vanishes at another point of the
same nonnegative sample event.  The cardinal calibration is supplied by `card_calib_top`;
there is no abstract consistency assumption in this witness. -/
theorem sat_piecewiseW_nonconstant :
    piecewiseW (canonicalR satS satT satMesh) 1 satJ satS satT satMesh
      (1 / 2) 1 1 (0 : ℝ) = 1 ∧
    piecewiseW (canonicalR satS satT satMesh) 1 satJ satS satT satMesh
      (1 / 2) 1 1 (2 * Real.exp 1 + 1 : ℝ) = 0 := by
  have hactive : 1 ≤ cutNetTop satS satT satMesh 1 ∧ 1 ≤ (1 : ℕ) := by
    rw [sat_top]; omega
  have hθ : 0 < Real.exp 1 * APrimePrior.priorLevel (1 / 2)
      (fun _ => 1) 1 := by
    exact mul_pos (Real.exp_pos 1) (APrimePrior.priorLevel_pos (by norm_num) (by norm_num))
  constructor
  · rw [piecewiseW, if_pos hactive]
    have hrval : canonicalR satS satT satMesh 1 = 2 := by simp [canonicalR, sat_top]
    have hz : softMax (canonicalR satS satT satMesh 1) (Finset.range 1)
        (fun j => satJ 1 (cutNetPt satS satMesh 1 j) (0 : ℝ)) = 0 := by
      simp [hrval, softMax, satJ]
    rw [prefixSoftW, softW, hz]
    exact cutChi_eq_one (by norm_num)
  · rw [piecewiseW, if_pos hactive]
    unfold prefixSoftW
    apply softW_eq_zero (i := 0) (by simp [canonicalR, sat_top]) hθ (by simp)
    simp only [satJ, APrimePrior.priorLevel, Nat.cast_one, one_pow, mul_one]
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have hp : 0 ≤ 2 * Real.exp 1 + 1 := by linarith
    rw [max_eq_left hp, abs_of_nonneg hp]
    linarith

/-- Both sample points of the witness belong to the same nontrivial event. -/
theorem sat_piecewiseW_on_good :
    ∃ ω₁ ω₂ : ℝ, ω₁ ∈ Set.Ici 0 ∧ ω₂ ∈ Set.Ici 0 ∧
      piecewiseW (canonicalR satS satT satMesh) 1 satJ satS satT satMesh
        (1 / 2) 1 1 ω₁ = 1 ∧
      piecewiseW (canonicalR satS satT satMesh) 1 satJ satS satT satMesh
        (1 / 2) 1 1 ω₂ = 0 := by
  refine ⟨0, 2 * Real.exp 1 + 1, by simp, ?_,
    sat_piecewiseW_nonconstant.1, sat_piecewiseW_nonconstant.2⟩
  have := Real.exp_pos 1
  simp only [Set.mem_Ici]
  linarith

end Witness

end APrimeWeight
end RBM
