/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQuantMoment

/-!
# T512: the first-cell coordinate maximum under one high-order weight

The maximum of the actual endpoint coordinate family is estimated at the
same fixed order and under the same canonical weight as every T509
coordinate.  The exact family cost is `card^(1/(2P))`; `P ≥ 8000` pays it
with `N^(delta/4)` without a multiplicative constant.
-/

namespace RBM.APrimeFirstCellFamilyHighMoment

open Filter MeasureTheory Set Gauss CutHypTheta
open RBM.MomentDuhamel APrimeFirstCellMinkowskiExact

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow

noncomputable abbrev delta : ℝ := APrimeFirstCellQuantMoment.delta
noncomputable abbrev alpha : ℝ := APrimeFirstCellQuantMoment.alpha

/-- The literal finite maximum of the absolute actual endpoint coordinates. -/
noncomputable def familyMax (N k : ℕ) (ω : Ω d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : LoopArg (d.L N) 2 => |Y N k a (endpoint N k) ω|)

/-- Taking a finite maximum and then a natural power costs only the sum of
the corresponding powers, with coefficient one. -/
theorem finsetMax_pow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (n : ℕ) :
    |Finset.univ.sup' Finset.univ_nonempty (fun i => |f i|)| ^ n ≤
      ∑ i, |f i| ^ n := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : ι => |f i|)
  rw [hmax, abs_abs]
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : ι => |f j| ^ n)
    (fun j _ => pow_nonneg (abs_nonneg _) _) hi

/-- Integrability of the weighted maximum follows from the same weighted
coordinate powers, via a finite supremum of integrable functions. -/
theorem integrable_weighted_finsetMax_pow
    {Ω' ι : Type*} [MeasurableSpace Ω'] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω') (w : Ω' → ℝ) (f : ι → Ω' → ℝ) (n : ℕ)
    (hw0 : ∀ ω, 0 ≤ w ω)
    (hint : ∀ i, Integrable (fun ω => w ω * |f i ω| ^ n) μ) :
    Integrable (fun ω => w ω *
      |Finset.univ.sup' Finset.univ_nonempty (fun i => |f i ω|)| ^ n) μ := by
  have hsup : Integrable
      ((Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i ω => w ω * |f i ω| ^ n)) μ :=
    Finset.sup'_induction (p := fun g : Ω' → ℝ => Integrable g μ)
      Finset.univ_nonempty (fun i ω => w ω * |f i ω| ^ n)
      (fun _ hf _ hg => hf.sup hg) (fun i _ => hint i)
  have heq : (fun ω => w ω *
      |Finset.univ.sup' Finset.univ_nonempty (fun i => |f i ω|)| ^ n) =
      (Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i ω => w ω * |f i ω| ^ n) := by
    funext ω
    rw [Finset.sup'_apply]
    obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun i : ι => |f i ω|)
    have hmax0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun i : ι => |f i ω|) := by
      rw [hmax]
      exact abs_nonneg _
    rw [abs_of_nonneg hmax0]
    apply le_antisymm
    · rw [hmax]
      exact Finset.le_sup' (fun j => w ω * |f j ω| ^ n) hi
    · apply Finset.sup'_le
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg (f j ω))
          (Finset.le_sup' (fun i : ι => |f i ω|) hj) n) (hw0 ω)
  rw [heq]
  exact hsup

/-- A finite family under one common nonnegative weight has the exact
`card^(1/(2p))` moment-norm cost. -/
theorem momNormW_finsetMax_le
    {Ω' ι : Type*} [MeasurableSpace Ω'] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω') (w : Ω' → ℝ) (f : ι → Ω' → ℝ)
    (p : ℕ) (hp : 1 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (hw0 : ∀ ω, 0 ≤ w ω)
    (hint : ∀ i, Integrable (fun ω => w ω * |f i ω| ^ (2 * p)) μ)
    (hcoord : ∀ i, momNormW μ w p (f i) ≤ c) :
    momNormW μ w p
      (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => |f i ω|)) ≤
      (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) * c := by
  have hintMax := integrable_weighted_finsetMax_pow μ w f (2 * p) hw0 hint
  have hintSum : Integrable (fun ω => ∑ i, w ω * |f i ω| ^ (2 * p)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hint i)
  have hcoordInt : ∀ i, (∫ ω, w ω * |f i ω| ^ (2 * p) ∂μ) ≤ c ^ (2 * p) :=
    fun i => APrimeOneStep.integral_le_of_momNormW_le hw0 hp (hcoord i)
  have hi : (∫ ω, w ω *
      |Finset.univ.sup' Finset.univ_nonempty (fun i => |f i ω|)| ^ (2 * p) ∂μ) ≤
      (Fintype.card ι : ℝ) * c ^ (2 * p) := by
    calc
      _ ≤ ∫ ω, ∑ i, w ω * |f i ω| ^ (2 * p) ∂μ :=
        integral_mono hintMax hintSum (fun ω => by
          simpa only [Finset.mul_sum] using
            mul_le_mul_of_nonneg_left (finsetMax_pow_le_sum (fun i => f i ω) (2 * p))
              (hw0 ω))
      _ = ∑ i, ∫ ω, w ω * |f i ω| ^ (2 * p) ∂μ :=
        integral_finsetSum Finset.univ (fun i _ => hint i)
      _ ≤ ∑ _i : ι, c ^ (2 * p) := Finset.sum_le_sum (fun i _ => hcoordInt i)
      _ = (Fintype.card ι : ℝ) * c ^ (2 * p) := by simp
  have hI0 : 0 ≤ (∫ ω, w ω *
      |Finset.univ.sup' Finset.univ_nonempty (fun i => |f i ω|)| ^ (2 * p) ∂μ) :=
    integral_nonneg fun ω => mul_nonneg (hw0 ω) (by positivity)
  have hexp : (1 : ℝ) / (2 * (p : ℝ)) = (((2 * p : ℕ) : ℝ))⁻¹ := by
    push_cast
    rw [one_div]
  calc
    _ ≤ ((Fintype.card ι : ℝ) * c ^ (2 * p)) ^ ((1 : ℝ) / (2 * (p : ℝ))) :=
      Real.rpow_le_rpow hI0 hi (by positivity)
    _ = (Fintype.card ι : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) * c := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hc _), hexp,
        Real.pow_rpow_inv_natCast hc (by omega : 2 * p ≠ 0)]

/-- The actual two-coordinate family has exactly `L_N^2` members. -/
theorem family_card_eq (N : ℕ) :
    Fintype.card (LoopArg (d.L N) 2) = (d.L N) ^ 2 := by
  simpa only [Finset.card_univ] using (Gauss.card_loopArg_two (L := d.L N))

/-- The requested polynomial cardinality bound is valid from size 81. -/
theorem family_card_le {N : ℕ} (hN : 81 ≤ N) :
    Fintype.card (LoopArg (d.L N) 2) ≤ N ^ 2 := by
  have hL : d.L N ≤ N := by
    have h27 := Dims.twentyseven_mul_growL_le N hN
    change Dims.growL N ≤ N
    omega
  rw [family_card_eq]
  exact Nat.pow_le_pow_left hL 2

/-- The exact family-root cost is at most `N^(delta/4)` also at `p=8000`. -/
theorem family_card_root_le {N p : ℕ} (hN : 81 ≤ N) (hp : 8000 ≤ p) :
    (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) ≤
      (N : ℝ) ^ (delta / 4) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpr : (8000 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hcard : (Fintype.card (LoopArg (d.L N) 2) : ℝ) ≤ (N : ℝ) ^ 2 := by
    exact_mod_cast family_card_le hN
  have hpexp : (1 : ℝ) / (p : ℝ) ≤ delta / 4 := by
    rw [div_le_iff₀ hp0]
    norm_num [delta, APrimeFirstCellQuantMoment.delta_eq_one_over_two_thousand]
    linarith
  calc
    _ ≤ ((N : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / (2 * (p : ℝ))) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hcard (by positivity)
    _ = (N : ℝ) ^ ((1 : ℝ) / (p : ℝ)) := by
      rw [← Real.rpow_natCast_mul (Nat.cast_nonneg N)]
      congr 1
      push_cast
      field_simp
    _ ≤ (N : ℝ) ^ (delta / 4) := Real.rpow_le_rpow_of_exponent_le hNr hpexp

/-- The finite-family target, always under the same canonical order-`p` weight. -/
def familyMomentAt (τ' : ℝ) (p N k : ℕ) : Prop :=
  momNormW (Gauss.P d) (weight τ' p N k) p (familyMax N k) ≤
    (N : ℝ) ^ (delta / 2) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))

/-- Fixed-size passage from T509's entire coordinate family under the same
weight to its literal maximum. -/
theorem familyMomentAt_of_coords {τ' : ℝ} (hτ' : 0 < τ') {p N k : ℕ}
    (hp : 8000 ≤ p) (hN : 81 ≤ N)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hcoords : ∀ a : LoopArg (d.L N) 2,
      APrimeFirstCellQuantMoment.quantMomentAt τ' p N k a) :
    familyMomentAt τ' p N k := by
  have hp1 : 1 ≤ p := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) _ (cutNetPt_mem_netFinset hk)
  have hv1 : endpoint N k < 1 := hv.2.trans_lt (ht.2.trans_lt (by norm_num))
  have hR : 0 < etaT 0 0 / etaT 0 (endpoint N k) :=
    Step2Moment.ratR_pos (s := fun _ => 0) (N := N) (by norm_num) (by norm_num) hv1
  have hc : 0 ≤ (N : ℝ) ^ (delta / 4) *
      (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hR.le _)
  have hw0 : ∀ ω, 0 ≤ weight τ' p N k ω := fun ω =>
    APrimeSmoothWeightActual.weight_nonneg d 0 60 delta (fun _ => 0)
      (firstCellT τ') APrimeSmoothTransition.transitionMesh 2 p N k
      (canonicalM τ' N) ω
  have hint : ∀ a : LoopArg (d.L N) 2,
      Integrable (fun ω => weight τ' p N k ω *
        |Y N k a (endpoint N k) ω| ^ (2 * p)) (Gauss.P d) := by
    intro a
    exact (APrimeFirstCellSampleRegularity.actual_generator_sampleRegularity_endpoints
      (δ := delta) hτ' hp1 (by omega) hk a).2.hYi
  have hmax := momNormW_finsetMax_le (Gauss.P d) (weight τ' p N k)
    (fun a => Y N k a (endpoint N k)) p hp1 hc hw0 hint hcoords
  change momNormW (Gauss.P d) (weight τ' p N k) p (familyMax N k) ≤ _ at hmax
  calc
    _ ≤ (Fintype.card (LoopArg (d.L N) 2) : ℝ) ^ ((1 : ℝ) / (2 * (p : ℝ))) *
        ((N : ℝ) ^ (delta / 4) *
          (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) := hmax
    _ ≤ (N : ℝ) ^ (delta / 4) * ((N : ℝ) ^ (delta / 4) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_right (family_card_root_le hN hp) hc
    _ = (N : ℝ) ^ (delta / 2) *
        (etaT 0 0 / etaT 0 (endpoint N k)) ^ (-(2 : ℝ)) := by
      rw [← mul_assoc, ← Real.rpow_add hNpos]
      congr 2
      ring

def actualFamilyHighMoment (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k →
    k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N → familyMomentAt τ' p N k

/-- The high order is fixed before a threshold uniform in all active indices. -/
theorem actualFamilyHighMoment_of_coords {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 8000 ≤ p)
    (hcoords : APrimeFirstCellQuantMoment.actualQuantMoment τ' p) :
    actualFamilyHighMoment τ' p := by
  filter_upwards [hcoords, eventually_ge_atTop 81] with N hcoordsN hN
  intro k hk1 hk
  exact familyMomentAt_of_coords hτ' hp hN hk (hcoordsN k hk1 hk)

def kZeroFamilyHighMoment (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    endpoint N 0 = 0 ∧ familyMomentAt τ' p N 0 ∧
      momNormW (Gauss.P d) (weight τ' p N 0) p (familyMax N 0) ≤
        (N : ℝ) ^ (delta / 2)

/-- The zero endpoint is handled with T509's separate zero-coordinate branch. -/
theorem eventually_kZeroFamilyHighMoment {τ' : ℝ} (hτ' : 0 < τ')
    (p : ℕ) (hp : 8000 ≤ p) : kZeroFamilyHighMoment τ' p := by
  filter_upwards [APrimeFirstCellQuantMoment.eventually_kZeroQuantMoment
    hτ' p (by omega), eventually_ge_atTop 81] with N hzero hN
  have hv : endpoint N 0 = 0 := by simp [endpoint, cutNetPt_zero]
  have hfamily := familyMomentAt_of_coords hτ' hp hN (Nat.zero_le _)
    (fun a => (hzero a).2.1)
  refine ⟨hv, hfamily, ?_⟩
  simpa [familyMomentAt, hv, etaT, mE_zero] using hfamily

def positiveTwoFamilyHighMomentResident (τ' : ℝ) (p : ℕ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∃ ω ∈
      APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N,
    2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N ∧
    0 < endpoint N 2 ∧ endpoint N 2 ≤ firstCellT τ' N ∧
    weight τ' p N 2 ω = 1 ∧ familyMomentAt τ' p N 2

/-- T509's same-event, same-weight positive resident also carries the maximum bound. -/
theorem positiveTwoFamilyHighMomentResident_of_coords {τ' : ℝ} {p : ℕ}
    (hresident : APrimeFirstCellQuantMoment.positiveTwoQuantMomentResident τ' p)
    (hfamily : actualFamilyHighMoment τ' p) :
    positiveTwoFamilyHighMomentResident τ' p := by
  filter_upwards [hresident, hfamily] with N hr hf
  obtain ⟨ω, hω, hk, hvpos, hvle, hw, _hcoords⟩ := hr
  exact ⟨ω, hω, hk, hvpos, hvle, hw, hf 2 (by norm_num) hk⟩

/-- A single T509 parameter and literal sharp event supply the order-`p`
maximum moment, with `p ≥ 8000` fixed before `N`, zero branch, and a genuine
positive canonical-weight-one resident. -/
theorem exists_familyHighMoment_with_resident :
    ∃ τ' : ℝ, 0 < τ' ∧ ∀ p : ℕ, 8000 ≤ p →
      (∀ N, MeasurableSet
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N)) ∧
      HighProb (Gauss.P d)
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha) ∧
      (∀ᶠ N : ℕ in atTop,
        (APrimeFirstCellSharpCommonEvent.sharpCommonEvent τ' delta alpha N).Nonempty) ∧
      actualFamilyHighMoment τ' p ∧ kZeroFamilyHighMoment τ' p ∧
      positiveTwoFamilyHighMomentResident τ' p := by
  obtain ⟨τ', hτ', hall⟩ := APrimeFirstCellQuantMoment.exists_quantMoment_with_resident
  refine ⟨τ', hτ', ?_⟩
  intro p hp
  obtain ⟨hm, hprob, hne, hcoords, _hzero, hresident⟩ := hall p (by omega)
  have hfamily := actualFamilyHighMoment_of_coords hτ' p hp hcoords
  exact ⟨hm, hprob, hne, hfamily, eventually_kZeroFamilyHighMoment hτ' p hp,
    positiveTwoFamilyHighMomentResident_of_coords hresident hfamily⟩

#print axioms finsetMax_pow_le_sum
#print axioms integrable_weighted_finsetMax_pow
#print axioms momNormW_finsetMax_le
#print axioms family_card_eq
#print axioms family_card_le
#print axioms family_card_root_le
#print axioms familyMomentAt_of_coords
#print axioms actualFamilyHighMoment_of_coords
#print axioms eventually_kZeroFamilyHighMoment
#print axioms positiveTwoFamilyHighMomentResident_of_coords
#print axioms exists_familyHighMoment_with_resident

end

end RBM.APrimeFirstCellFamilyHighMoment
