/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSlotArith
import RBM1D.Gauss.Envelope
import RBM1D.Gauss.APrimeSlotFields

/-!
# T280b: obstruction in the proposed family summation budget

The current one-coordinate `oneStep_of_slots` estimate at `x = N^(δ/8)` already has the
full `N^(δp/2)` power of `WeightedMoment`.  Hence a family summation charged using only
`L² ≤ N²` cannot be absorbed into the same power with an `N`-independent constant.
-/

namespace RBM.APrimeInit

open Real StepSideAPrime APrimeSlotArith

/-- A coordinate bound that already spends the full `N^e` budget cannot be
summed over a growing `N²` family at the same exponent. -/
theorem no_family_absorption (e : ℝ) :
    ¬ ∃ C : ℝ, 0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ e ≤ C * (N : ℝ) ^ e) := by
  rintro ⟨C, -, h⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 1)
  obtain ⟨N, hN, hNn⟩ := (h.and (Filter.eventually_ge_atTop n)).exists
  have hn1 : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right C 1) hn
  have hN1 : 1 < (N : ℝ) := lt_of_lt_of_le hn1 (by exact_mod_cast hNn)
  have hCN : C < (N : ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left C 1) hn) (by exact_mod_cast hNn)
  have hsq : C < (N : ℝ) ^ (2 : ℕ) := by nlinarith
  have hpow : 0 < (N : ℝ) ^ e := Real.rpow_pos_of_pos (by linarith) e
  nlinarith [mul_pos (sub_pos.mpr hsq) hpow]

/-- The exact exponent in `WeightedMoment` and in the T276 slot specialization
`x = N^(δ/8)`: for fixed `δ,p`, the factor `N²` cannot be paid by the same
`N^(δp/2)` power, even with an arbitrary fixed constant. -/
theorem no_family_absorption_slot (δ : ℝ) (p : ℕ) :
    ¬ ∃ C : ℝ, 0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (δ / 2 * (p : ℝ))
          ≤ C * (N : ℝ) ^ (δ / 2 * (p : ℝ))) :=
  no_family_absorption (δ / 2 * (p : ℝ))

/-! ## The corrected one-coordinate budget -/

/-- If the two formerly saturated slots are bounded by `y`, all eight terms of the
step RHS fit into `x*y`, with the same numerical constant as T263. -/
theorem stepRhs''_div_le_small {m x y R Ξ A ε q β γ κ Jv : ℝ}
    (hm : 0 < m) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (H : StepSide'' x R Ξ A ε q β γ κ Jv)
    (hΞ : Ξ ≤ y) (hκ : κ ≤ y) :
    stepRhs'' m x R Ξ A ε q β γ κ Jv / R ^ 4
      ≤ (Step2MomentStep.cStep' m + 1) * (x * y) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hR : 1 ≤ R := H.R_ge
  have hR0 : 0 < R := by linarith
  have hmI : 0 < m⁻¹ := inv_pos.mpr hm
  have hc0 : 0 < cWt := cWt_pos
  have hε0 := H.ε_nonneg
  have hq0 := H.q_nonneg
  have hβ0 := H.β_nonneg
  have hγ0 := H.γ_nonneg
  have hJ0 := H.Jv_nonneg
  have hR24 : R ^ 2 ≤ R ^ 4 := pow_le_pow_right₀ hR (by norm_num)
  have hxy1 : 1 ≤ x * y * R ^ 4 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hx hy) (one_le_pow₀ hR)
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) H.A_ge
  have hxA : cWt ^ 2 * x ^ 33 * R ^ 10 * A⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hA0]; exact H.A_ge
  have hsq : √Jv ≤ √cWt * x ^ 8 * R ^ 2 := by
    have heq : (√cWt * x ^ 8 * R ^ 2) ^ 2 = cWt * x ^ 16 * R ^ 4 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hc0.le]; ring
    have h := Real.sqrt_le_sqrt H.Jv_le
    rwa [← heq, Real.sqrt_sq (by positivity)] at h
  have hJJ : Jv * √Jv ≤ cWt * √cWt * x ^ 24 * R ^ 6 := by
    calc
      Jv * √Jv ≤ (cWt * x ^ 16 * R ^ 4) * (√cWt * x ^ 8 * R ^ 2) :=
        mul_le_mul H.Jv_le hsq (Real.sqrt_nonneg _) (by positivity)
      _ = cWt * √cWt * x ^ 24 * R ^ 6 := by ring
  have t1 : x * R ^ 2 * Ξ ≤ x * y * R ^ 4 := by
    calc x * R ^ 2 * Ξ ≤ x * R ^ 2 * y := by gcongr
      _ = (x * y) * R ^ 2 := by ring
      _ ≤ (x * y) * R ^ 4 := mul_le_mul_of_nonneg_left hR24 (by positivity)
      _ = x * y * R ^ 4 := by ring
  have tκ : x * R ^ 2 * κ ≤ x * y * R ^ 4 := by
    calc x * R ^ 2 * κ ≤ x * R ^ 2 * y := by gcongr
      _ = (x * y) * R ^ 2 := by ring
      _ ≤ (x * y) * R ^ 4 := mul_le_mul_of_nonneg_left hR24 (by positivity)
      _ = x * y * R ^ 4 := by ring
  have t2 : Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 *
      (36 * m⁻¹ * R ^ 2 * A⁻¹)) ≤ 36 * exp 1 * m⁻¹ * (x * y * R ^ 4) := by
    calc
      Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 *
          (36 * m⁻¹ * R ^ 2 * A⁻¹))
          = 36 * exp 1 * m⁻¹ * (Ξ * (cWt ^ 2 * x ^ 32 * R ^ 10) * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * (x * (cWt ^ 2 * x ^ 32 * R ^ 10) * A⁻¹) := by
          gcongr; exact H.Ξ_le
      _ = 36 * exp 1 * m⁻¹ * (cWt ^ 2 * x ^ 33 * R ^ 10 * A⁻¹) := by ring
      _ ≤ 36 * exp 1 * m⁻¹ * 1 := by gcongr
      _ ≤ 36 * exp 1 * m⁻¹ * (x * y * R ^ 4) := by gcongr
  have t3 : Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 *
      (R ^ 2 * ε)) ≤ exp 1 * (x * y * R ^ 4) := by
    calc
      Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
          = exp 1 * (Ξ * (cWt ^ 2 * x ^ 32 * R ^ 10) * ε) := by ring
      _ ≤ exp 1 * (x * (cWt ^ 2 * x ^ 32 * R ^ 10) * ε) := by
          gcongr; exact H.Ξ_le
      _ = exp 1 * (ε * (cWt ^ 2 * x ^ 33 * R ^ 10)) := by ring
      _ ≤ exp 1 * 1 := by gcongr; exact H.ε_le
      _ ≤ exp 1 * (x * y * R ^ 4) := by gcongr
  have t4 : Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ m⁻¹ * (x * y * R ^ 4) := by
    calc
      Ξ * (x * m⁻¹ * R ^ 2 * q) ≤ y * (x * m⁻¹ * R ^ 2 * R ^ 2) := by
        gcongr; exact H.q_le
      _ = m⁻¹ * (x * y * R ^ 4) := by ring
  have t5 : Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv)) ≤
      m⁻¹ * (x * y * R ^ 4) := by
    calc
      Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv))
          ≤ y * (x * m⁻¹ * R ^ 2 * (β * (cWt * x ^ 16 * R ^ 4))) := by
            gcongr; exact H.Jv_le
      _ = m⁻¹ * (x * y * R ^ 4) * (β * (cWt * x ^ 16 * R ^ 2)) := by ring
      _ ≤ m⁻¹ * (x * y * R ^ 4) * 1 := by gcongr; exact H.β_le
      _ = m⁻¹ * (x * y * R ^ 4) := mul_one _
  have t6 : Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv))) ≤
      m⁻¹ * (x * y * R ^ 4) := by
    calc
      Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv)))
          ≤ y * (x * m⁻¹ * R ^ 2 * (γ * (cWt * √cWt * x ^ 24 * R ^ 6))) := by
            gcongr
      _ = m⁻¹ * (x * y * R ^ 4) * (γ * (cWt * √cWt * x ^ 24 * R ^ 4)) := by ring
      _ ≤ m⁻¹ * (x * y * R ^ 4) * 1 := by gcongr; exact H.γ_le
      _ = m⁻¹ * (x * y * R ^ 4) := mul_one _
  have t7 : x * (R ^ 2 + 1) ≤ 2 * (x * y * R ^ 4) := by
    have hR14 : (1 : ℝ) ≤ R ^ 4 := one_le_pow₀ hR
    calc
      x * (R ^ 2 + 1) ≤ x * (2 * R ^ 4) := by gcongr; linarith
      _ = 2 * (x * R ^ 4) := by ring
      _ ≤ 2 * (x * y * R ^ 4) := by
          gcongr
          nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hy)]
  have hsplit : stepRhs'' m x R Ξ A ε q β γ κ Jv =
      x * R ^ 2 * Ξ + x * R ^ 2 * κ
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 *
          (36 * m⁻¹ * R ^ 2 * A⁻¹))
        + Ξ * (exp 1 * (cWt * x ^ 16 * R ^ 4) ^ 2 * (R ^ 2 * ε))
        + Ξ * (x * m⁻¹ * R ^ 2 * q)
        + Ξ * (x * m⁻¹ * R ^ 2 * (β * Jv))
        + Ξ * (x * m⁻¹ * R ^ 2 * (γ * (Jv * √Jv)))
        + x * (R ^ 2 + 1) + 1 := by unfold stepRhs''; ring
  rw [div_le_iff₀ (by positivity : 0 < R ^ 4), hsplit, Step2MomentStep.cStep']
  nlinarith

/-- The alternate initial-loss and cross-term slots leave room for the family cardinality. -/
noncomputable def slotXi' (x : ℝ) : ℝ := x ^ (1 / 4 : ℝ)
noncomputable def slotKappa' (x : ℝ) : ℝ := x ^ (1 / 4 : ℝ)

theorem slotXi'_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ slotXi' x := by
  unfold slotXi'
  exact Real.one_le_rpow hx (by norm_num)

theorem slotXi'_le_x {x : ℝ} (hx : 1 ≤ x) : slotXi' x ≤ x := by
  unfold slotXi'
  calc x ^ (1 / 4 : ℝ) ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = x := Real.rpow_one x

/-- Replace just `Ξ` and `κ` in T276's eight-field certificate. -/
theorem side_replace {x R Ξ A ε q β γ κ Jv Ξ' κ' : ℝ}
    (H : StepSide'' x R Ξ A ε q β γ κ Jv)
    (hΞ0 : 0 ≤ Ξ') (hΞ : Ξ' ≤ x) (hκ0 : 0 ≤ κ') (hκ : κ' ≤ x) :
    StepSide'' x R Ξ' A ε q β γ κ' Jv :=
  ⟨H.R_ge, hΞ0, hΞ, H.A_ge, H.ε_nonneg, H.ε_le, H.q_nonneg, H.q_le,
    H.β_nonneg, H.β_le, H.γ_nonneg, H.γ_le, hκ0, hκ, H.Jv_nonneg, H.Jv_le⟩

/-- The small slots still satisfy all T263 side conditions. -/
theorem slotSide' {x R : ℝ} (hx : 1 ≤ x) (hR : 1 ≤ R) :
    StepSide'' x R (slotXi' x) (slotA x R) (slotEps x R) (slotQ R)
      (slotBeta x R) (slotGamma x R) (slotKappa' x) (slotJv x R) := by
  exact side_replace (slotSide hx hR)
    (by unfold slotXi'; positivity) (slotXi'_le_x hx)
    (by unfold slotKappa'; positivity) (slotXi'_le_x hx)

/-- `x=N^(δ/8)` and the small slots give an `x^(5/4)` one-coordinate bound. -/
theorem stepRhs''_div_le_small_slots {m x R : ℝ} (hm : 0 < m)
    (hx : 1 ≤ x) (hR : 1 ≤ R) :
    stepRhs'' m x R (slotXi' x) (slotA x R) (slotEps x R) (slotQ R)
        (slotBeta x R) (slotGamma x R) (slotKappa' x) (slotJv x R) / R ^ 4
      ≤ (Step2MomentStep.cStep' m + 1) * x ^ (5 / 4 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hxy : x * slotXi' x = x ^ (5 / 4 : ℝ) := by
    unfold slotXi'
    calc
      x * x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) * x ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + 1 / 4) := (Real.rpow_add hx0 1 (1 / 4)).symm
      _ = x ^ (5 / 4 : ℝ) := by norm_num
  rw [← hxy]
  exact stepRhs''_div_le_small hm hx (slotXi'_ge_one hx) (slotSide' hx hR) le_rfl le_rfl

/-- The coordinate form of T271's (G) chain, keeping the sharper power before
any `max_a` summation. -/
theorem coordinate_integral_of_small_slots {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {m x R : ℝ}
    (hm : 0 < m) (hx : 1 ≤ x) (hR : 1 ≤ R)
    {a b : ℝ} {p : ℕ} (hp : 1 ≤ p)
    {W : Ω → ℝ} {Y : ℝ → Ω → ℝ} {Adr Bcr g : ℝ → ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω)
    (hG : MomentDuhamel.momNormW P W p (Y b) ≤
      MomentDuhamel.momNormW P W p (Y a) +
        2 * (∫ r in a..b, (Adr r + Bcr r)) +
        √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r))
    (hinit : MomentDuhamel.momNormW P W p (Y a) ≤
      APrimeOneStep.initTerm x R (slotXi' x) / R ^ 4)
    (hdrift : 2 * (∫ r in a..b, (Adr r + Bcr r)) ≤
      APrimeOneStep.driftTerm m x R (slotXi' x) (slotA x R) (slotEps x R)
        (slotQ R) (slotBeta x R) (slotGamma x R) (slotJv x R) / R ^ 4)
    (hqv : √((2 * (p : ℝ) - 1) * ∫ r in a..b, g r) ≤
      APrimeOneStep.tailTerm x R (slotKappa' x) / R ^ 4) :
    ∫ ω, W ω * |Y b ω| ^ (2 * p) ∂P ≤
      ((Step2MomentStep.cStep' m + 1) * x ^ (5 / 4 : ℝ)) ^ (2 * p) := by
  have hnorm := APrimeOneStep.stepRhs''_div_of_slots hG hinit hdrift hqv
  have hfit := stepRhs''_div_le_small_slots hm hx hR
  exact (APrimeOneStep.integral_le_of_momNormW_le hW0 hp (hnorm.trans hfit))

/-! ## Maximum to family -/

/-- The pointwise `max_a` step before integrating.  The baseline `1` survives explicitly. -/
theorem cutTrunc_pow_le_family {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (Y : ι → ℝ) {J θ : ℝ} (hJ0 : 0 ≤ J)
    (hJ : J ≤ 1 + S.sup' hS (fun i => |Y i|)) (p : ℕ) :
    |MomentDuhamelCut.cutTrunc θ J| ^ (2 * p) ≤
      2 ^ (2 * p - 1) * (1 + ∑ i ∈ S, |Y i| ^ (2 * p)) := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' hS (fun i => |Y i|)
  have hM0 : 0 ≤ S.sup' hS (fun i => |Y i|) := by
    rw [hmax]; exact abs_nonneg _
  have hcut0 := MomentDuhamelCut.cutTrunc_nonneg (Θ := θ) hJ0
  have hcut : |MomentDuhamelCut.cutTrunc θ J| ≤
      1 + S.sup' hS (fun i => |Y i|) := by
    rw [abs_of_nonneg hcut0]
    exact (MomentDuhamelCut.cutTrunc_le_self hJ0).trans hJ
  have hmaxpow : (S.sup' hS fun i => |Y i|) ^ (2 * p) ≤
      ∑ i ∈ S, |Y i| ^ (2 * p) := by
    rw [hmax]
    exact Finset.single_le_sum (s := S) (f := fun i => |Y i| ^ (2 * p))
      (fun i _ => by positivity) hi
  calc
    |MomentDuhamelCut.cutTrunc θ J| ^ (2 * p)
        ≤ (1 + S.sup' hS (fun i => |Y i|)) ^ (2 * p) :=
          pow_le_pow_left₀ (abs_nonneg _) hcut _
    _ ≤ 2 ^ (2 * p - 1) * (1 ^ (2 * p) +
        (S.sup' hS fun i => |Y i|) ^ (2 * p)) :=
          add_pow_le (by norm_num) hM0 _
    _ ≤ 2 ^ (2 * p - 1) * (1 + ∑ i ∈ S, |Y i| ^ (2 * p)) := by
          have hsum : (1 : ℝ) + (S.sup' hS fun i => |Y i|) ^ (2 * p) ≤
              1 + ∑ i ∈ S, |Y i| ^ (2 * p) := by linarith [hmaxpow]
          simpa only [one_pow] using
            (mul_le_mul_of_nonneg_left hsum
              (show (0 : ℝ) ≤ 2 ^ (2 * p - 1) by positivity))

/-- Integrate the maximum-to-family inequality against a nonnegative bounded weight. -/
theorem integral_cutTrunc_le_family {Ω ι : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (S : Finset ι) (hS : S.Nonempty) {W J : Ω → ℝ} {Y : ι → Ω → ℝ}
    {θ : ℝ} {p : ℕ} {c : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hJ0 : ∀ ω, 0 ≤ J ω)
    (hJ : ∀ ω, J ω ≤ 1 + S.sup' hS (fun i => |Y i ω|))
    (hintW : MeasureTheory.Integrable W P)
    (hintY : ∀ i ∈ S,
      MeasureTheory.Integrable (fun ω => W ω * |Y i ω| ^ (2 * p)) P)
    (hintJ : MeasureTheory.Integrable
      (fun ω => W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p)) P)
    (hcoord : ∀ i ∈ S,
      ∫ ω, W ω * |Y i ω| ^ (2 * p) ∂P ≤ c ^ (2 * p)) :
    ∫ ω, W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p) ∂P ≤
      2 ^ (2 * p - 1) * (1 + S.card * c ^ (2 * p)) := by
  let f : ι → Ω → ℝ := fun i ω => W ω * |Y i ω| ^ (2 * p)
  have hintSum : MeasureTheory.Integrable (fun ω => ∑ i ∈ S, f i ω) P :=
    MeasureTheory.integrable_finsetSum S (fun i hi => hintY i hi)
  have hpt : ∀ ω, W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p) ≤
      2 ^ (2 * p - 1) * (W ω + ∑ i ∈ S, f i ω) := by
    intro ω
    have h := cutTrunc_pow_le_family S hS (fun i => Y i ω)
      (θ := θ) (hJ0 ω) (hJ ω) p
    have hw := mul_le_mul_of_nonneg_left h (hW0 ω)
    convert hw using 1; simp [f, mul_add, Finset.mul_sum, mul_assoc, mul_comm]
  have hmain : ∫ ω, W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p) ∂P ≤
      2 ^ (2 * p - 1) * (∫ ω, W ω ∂P + ∑ i ∈ S, ∫ ω, f i ω ∂P) := by
    have hintR : MeasureTheory.Integrable
        (fun ω => 2 ^ (2 * p - 1) * (W ω + ∑ i ∈ S, f i ω)) P :=
      (hintW.add hintSum).const_mul _
    have hmono := MeasureTheory.integral_mono hintJ hintR hpt
    convert hmono using 1
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hintW hintSum,
      MeasureTheory.integral_finsetSum S (fun i hi => hintY i hi)]
  have hWbd : (∫ ω, W ω ∂P) ≤ 1 := by
    calc
      (∫ ω, W ω ∂P) ≤ ∫ _ω : Ω, (1 : ℝ) ∂P :=
        MeasureTheory.integral_mono hintW (MeasureTheory.integrable_const _) hW1
      _ = 1 := by simp
  calc
    (∫ ω, W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p) ∂P)
        ≤ 2 ^ (2 * p - 1) *
            ((∫ ω, W ω ∂P) + ∑ i ∈ S, ∫ ω, f i ω ∂P) := hmain
    _ ≤ 2 ^ (2 * p - 1) * (1 + S.card * c ^ (2 * p)) := by
      have hsum : (∑ i ∈ S, ∫ ω, f i ω ∂P) ≤ S.card * c ^ (2 * p) := by
        calc
          (∑ i ∈ S, ∫ ω, f i ω ∂P) ≤ ∑ _i ∈ S, c ^ (2 * p) := by
              gcongr with i hi
              exact hcoord i hi
          _ = S.card * c ^ (2 * p) := by simp
      gcongr

/-! ## Reverse bridge for the numerical initial moment -/

/-- The reverse `StochDom → MomentDom` bridge, followed by `W ≤ 1`, gives the
unconditional weighted moments needed before fitting the numerical `hinit` slot. -/
theorem weightedMomentDom_of_stochDom_of_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure P]
    {U : ℕ → Type*} {Y : ∀ N, U N → Ω → ℝ}
    {Φ : ∀ N, U N → ℝ} {Env : ℕ → ℝ} {Kenv B : ℝ}
    {W : ∀ N, U N → Ω → ℝ}
    (hY0 : ∀ N (u : U N) (ω : Ω), 0 ≤ Y N u ω)
    (hmeas : ∀ N (u : U N), Measurable (Y N u))
    (hint : ∀ (p N : ℕ) (u : U N),
      MeasureTheory.Integrable (fun ω => |Y N u ω| ^ (2 * p)) P)
    (hΦ : ∀ N u, 0 < Φ N u) (hB : 0 ≤ B)
    (hΦlow : ∀ᶠ N : ℕ in Filter.atTop, ∀ u, (N : ℝ) ^ (-B) ≤ Φ N u)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ N (u : U N) (ω : Ω), Y N u ω ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in Filter.atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hdom : StochDom P Y (fun N u _ => Φ N u))
    (hW1 : ∀ N (u : U N) ω, W N u ω ≤ 1)
    (hintW : ∀ (p N : ℕ) (u : U N),
      MeasureTheory.Integrable (fun ω => W N u ω * |Y N u ω| ^ (2 * p)) P) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in Filter.atTop,
      ∀ u : U N, ∫ ω, W N u ω * |Y N u ω| ^ (2 * p) ∂P
        ≤ C * ((N : ℝ) ^ (ε * p) * Φ N u ^ (2 * p)) := by
  have hmd := Gauss.momentDom_of_stochDom_of_nonneg hY0 hmeas hint hΦ hB hΦlow
    hEnv0 hKenv henv hEnvpoly hdom
  intro ε hε p
  obtain ⟨C, hC, hCev⟩ := hmd ε hε p
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCev] with N hN u
  have hw : (∫ ω, W N u ω * |Y N u ω| ^ (2 * p) ∂P) ≤
      ∫ ω, |Y N u ω| ^ (2 * p) ∂P :=
    MeasureTheory.integral_mono (hintW p N u) (hint p N u) fun ω => by
      nlinarith [hW1 N u ω, pow_nonneg (abs_nonneg (Y N u ω)) (2 * p)]
  exact hw.trans (hN u)

/-- The exact numerical form of the `hinit` step after the reverse bridge's
weighted integral bound has been fitted to the chosen slot. -/
theorem numerical_hinit_of_weighted_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {W Y : Ω → ℝ} {p : ℕ} {c : ℝ}
    (hp : 1 ≤ p) (hc : 0 ≤ c) (hW0 : ∀ ω, 0 ≤ W ω)
    (h : ∫ ω, W ω * |Y ω| ^ (2 * p) ∂P ≤ c ^ (2 * p)) :
    MomentDuhamel.momNormW P W p Y ≤ c := by
  have hp0 : 2 * p ≠ 0 := by omega
  have hI0 : 0 ≤ (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) :=
    MeasureTheory.integral_nonneg fun ω => mul_nonneg (hW0 ω) (by positivity)
  have hr := Real.rpow_le_rpow hI0 h
    (show (0 : ℝ) ≤ ((2 * p : ℕ) : ℝ)⁻¹ by positivity)
  rw [Real.pow_rpow_inv_natCast hc hp0] at hr
  simpa [MomentDuhamel.momNormW, one_div] using hr

/-! ## Cardinality arithmetic -/

/-- For the new `x^(5/4)` coordinate bound, the `N²` family price fits in the
remaining exponent exactly when `32 ≤ 3δp`. -/
theorem family_cardinality_budget {N p : ℕ} {δ : ℝ}
    (hN : 1 ≤ N) (hp : 32 ≤ 3 * δ * (p : ℝ)) :
    (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (5 * δ * (p : ℝ) / 16)
      ≤ (N : ℝ) ^ (δ * (p : ℝ) / 2) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have he : (2 : ℝ) ≤ 3 * δ * (p : ℝ) / 16 := by linarith
  have hpow : (N : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (3 * δ * (p : ℝ) / 16) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; exact he)
  calc
    (N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (5 * δ * (p : ℝ) / 16)
        ≤ (N : ℝ) ^ (3 * δ * (p : ℝ) / 16) *
          (N : ℝ) ^ (5 * δ * (p : ℝ) / 16) :=
          mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
    _ = (N : ℝ) ^ (3 * δ * (p : ℝ) / 16 + 5 * δ * (p : ℝ) / 16) :=
          (Real.rpow_add hN0 _ _).symm
    _ = (N : ℝ) ^ (δ * (p : ℝ) / 2) := by congr 1; ring

/-- High-exponent family moment after the sharper coordinate bound.  All analytic
inputs are the same as `integral_cutTrunc_le_family`; this lemma only spends
the `N²` cardinality and records the resulting `WeightedMoment` exponent. -/
theorem integral_cutTrunc_le_family_high {Ω ι : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {N p : ℕ} {δ C : ℝ} (hN : 1 ≤ N)
    (hp : 32 ≤ 3 * δ * (p : ℝ)) (hC : 0 ≤ C)
    (S : Finset ι) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤ (N : ℝ) ^ (2 : ℕ))
    {W J : Ω → ℝ} {Y : ι → Ω → ℝ} {θ : ℝ}
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hJ0 : ∀ ω, 0 ≤ J ω)
    (hJ : ∀ ω, J ω ≤ 1 + S.sup' hS (fun i => |Y i ω|))
    (hintW : MeasureTheory.Integrable W P)
    (hintY : ∀ i ∈ S,
      MeasureTheory.Integrable (fun ω => W ω * |Y i ω| ^ (2 * p)) P)
    (hintJ : MeasureTheory.Integrable
      (fun ω => W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p)) P)
    (hcoord : ∀ i ∈ S,
      ∫ ω, W ω * |Y i ω| ^ (2 * p) ∂P ≤
        (C * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * p)) :
    ∫ ω, W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p) ∂P ≤
      2 ^ (2 * p - 1) * (1 + C ^ (2 * p)) *
        (N : ℝ) ^ (δ * (p : ℝ) / 2) := by
  have hbase := integral_cutTrunc_le_family S hS hW0 hW1 hJ0 hJ
    hintW hintY hintJ hcoord
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hpow : ((N : ℝ) ^ (5 * δ / 32)) ^ (2 * p) =
      (N : ℝ) ^ (5 * δ * (p : ℝ) / 16) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1
    push_cast
    ring
  have htarget1 : (1 : ℝ) ≤ (N : ℝ) ^ (δ * (p : ℝ) / 2) := by
    apply Real.one_le_rpow hN1
    nlinarith [hp]
  have hsum : (S.card : ℝ) *
      (C * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * p) ≤
      C ^ (2 * p) * (N : ℝ) ^ (δ * (p : ℝ) / 2) := by
    rw [mul_pow, hpow]
    calc
      (S.card : ℝ) * (C ^ (2 * p) * (N : ℝ) ^ (5 * δ * (p : ℝ) / 16))
          ≤ (N : ℝ) ^ (2 : ℕ) *
            (C ^ (2 * p) * (N : ℝ) ^ (5 * δ * (p : ℝ) / 16)) := by
              gcongr
      _ = C ^ (2 * p) *
          ((N : ℝ) ^ (2 : ℕ) * (N : ℝ) ^ (5 * δ * (p : ℝ) / 16)) := by ring
      _ ≤ C ^ (2 * p) * (N : ℝ) ^ (δ * (p : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left (family_cardinality_budget hN hp) (by positivity)
  calc
    (∫ ω, W ω * |MomentDuhamelCut.cutTrunc θ (J ω)| ^ (2 * p) ∂P)
        ≤ 2 ^ (2 * p - 1) *
          (1 + S.card * (C * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * p)) := hbase
    _ ≤ 2 ^ (2 * p - 1) * (1 + C ^ (2 * p)) *
          (N : ℝ) ^ (δ * (p : ℝ) / 2) := by
            have hinside : 1 + (S.card : ℝ) *
                (C * (N : ℝ) ^ (5 * δ / 32)) ^ (2 * p) ≤
                (1 + C ^ (2 * p)) * (N : ℝ) ^ (δ * (p : ℝ) / 2) := by
              nlinarith
            nlinarith [mul_nonneg
              (show (0 : ℝ) ≤ 2 ^ (2 * p - 1) by positivity)
              (sub_nonneg.mpr hinside)]

/-! ## Weighted Lyapunov at small exponents -/

/-- The lower moment is controlled by the same fractional-weighted variable that
encodes the higher moment. -/
theorem weighted_pow_le_fractional {w z : ℝ} {p q : ℕ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp : 1 ≤ p) (hpq : p ≤ q) :
    w * |z| ^ (2 * p) ≤
      |w ^ (((2 * q : ℕ) : ℝ)⁻¹) * z| ^ (2 * p) := by
  have hq : 2 * q ≠ 0 := by omega
  have hp0 : 2 * p ≠ 0 := by omega
  have hexp : (((2 * q : ℕ) : ℝ)⁻¹) * ((2 * p : ℕ) : ℝ) ≤ 1 := by
    have hqpos : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
    rw [inv_mul_le_iff₀ hqpos]
    simpa only [mul_one] using (by exact_mod_cast (by omega : 2 * p ≤ 2 * q) :
      ((2 * p : ℕ) : ℝ) ≤ ((2 * q : ℕ) : ℝ))
  have hw : w ≤ w ^ ((((2 * q : ℕ) : ℝ)⁻¹) * ((2 * p : ℕ) : ℝ)) := by
    by_cases hzero : w = 0
    · subst w; exact Real.rpow_nonneg (le_refl 0) _
    · have hpos : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hzero)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hpos hw1 hexp
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hw0 _), mul_pow,
    ← Real.rpow_natCast (w ^ _) (2 * p), ← Real.rpow_mul hw0]
  exact mul_le_mul_of_nonneg_right hw (pow_nonneg (abs_nonneg z) _)

theorem fractional_pow_high {w z : ℝ} {q : ℕ} (hw0 : 0 ≤ w) (hq : 1 ≤ q) :
    |w ^ (((2 * q : ℕ) : ℝ)⁻¹) * z| ^ (2 * q) = w * |z| ^ (2 * q) := by
  have hq0 : 2 * q ≠ 0 := by omega
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hw0 _), mul_pow,
    Real.rpow_inv_natCast_pow hw0 hq0]

/-- Weighted Lyapunov's inequality for `0 ≤ W ≤ 1`.  The integrability hypotheses
are explicit, as they are available for the truncated model observable. -/
theorem momNormW_le_momNormW_of_exponent_le {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {W Y : Ω → ℝ} {p q : ℕ}
    (hp : 1 ≤ p) (hpq : p ≤ q)
    (hW0 : ∀ ω, 0 ≤ W ω) (hW1 : ∀ ω, W ω ≤ 1)
    (hlo : MeasureTheory.Integrable (fun ω => W ω * |Y ω| ^ (2 * p)) P)
    (hhi : MeasureTheory.Integrable (fun ω => W ω * |Y ω| ^ (2 * q)) P)
    (hzlo : MeasureTheory.Integrable
      (fun ω => |W ω ^ (((2 * q : ℕ) : ℝ)⁻¹) * Y ω| ^ (2 * p)) P) :
    MomentDuhamel.momNormW P W p Y ≤ MomentDuhamel.momNormW P W q Y := by
  let Z : Ω → ℝ := fun ω => W ω ^ (((2 * q : ℕ) : ℝ)⁻¹) * Y ω
  have hq : 1 ≤ q := hp.trans hpq
  have hZhi : (fun ω => |Z ω| ^ (2 * q)) =
      (fun ω => W ω * |Y ω| ^ (2 * q)) := by
    funext ω; exact fractional_pow_high (hW0 ω) hq
  have hzhi : MeasureTheory.Integrable (fun ω => |Z ω| ^ (2 * q)) P := by
    rw [hZhi]; exact hhi
  have hIlo : (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ≤
      ∫ ω, |Z ω| ^ (2 * p) ∂P :=
    MeasureTheory.integral_mono hlo hzlo fun ω =>
      weighted_pow_le_fractional (hW0 ω) (hW1 ω) hp hpq
  have hI0 : 0 ≤ (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) :=
    MeasureTheory.integral_nonneg fun ω => mul_nonneg (hW0 ω) (by positivity)
  have hroot : (∫ ω, W ω * |Y ω| ^ (2 * p) ∂P) ^
      ((1 : ℝ) / (2 * (p : ℝ))) ≤
      (∫ ω, |Z ω| ^ (2 * p) ∂P) ^ ((1 : ℝ) / (2 * (p : ℝ))) :=
    Real.rpow_le_rpow hI0 hIlo (by positivity)
  have hmono := MomentDuhamel.momNorm_le_momNorm_of_exponent_le
    (P := P) (Y := Z) (p := 2 * p) (q := 2 * q) (by omega) (by omega) hzhi
  calc
    MomentDuhamel.momNormW P W p Y ≤ MomentDuhamel.momNorm P (2 * p) Z := by
      simpa only [MomentDuhamel.momNormW, MomentDuhamel.momNorm_eq_rpow,
        Nat.cast_mul, Nat.cast_ofNat] using hroot
    _ ≤ MomentDuhamel.momNorm P (2 * q) Z := hmono
    _ = MomentDuhamel.momNormW P W q Y := by
      rw [MomentDuhamel.momNorm_eq_rpow, MomentDuhamel.momNormW, hZhi]

/-- Explicit nondegenerate slot instance: `x>1`, `R>1`, and both new
slots are strictly above `1`. -/
theorem sat_small_slots_nondegenerate :
    StepSide'' 16 2 (slotXi' 16) (slotA 16 2) (slotEps 16 2) (slotQ 2)
      (slotBeta 16 2) (slotGamma 16 2) (slotKappa' 16) (slotJv 16 2) ∧
    1 < slotXi' 16 ∧ 1 < slotKappa' 16 ∧
    stepRhs'' 1 16 2 (slotXi' 16) (slotA 16 2) (slotEps 16 2) (slotQ 2)
      (slotBeta 16 2) (slotGamma 16 2) (slotKappa' 16) (slotJv 16 2) / 2 ^ 4
      ≤ (Step2MomentStep.cStep' 1 + 1) * 16 ^ (5 / 4 : ℝ) := by
  refine ⟨slotSide' (by norm_num) (by norm_num), ?_, ?_,
    stepRhs''_div_le_small_slots (by norm_num) (by norm_num) (by norm_num)⟩
  · exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 16) (by norm_num)
  · exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 16) (by norm_num)

#print axioms RBM.APrimeInit.no_family_absorption
#print axioms RBM.APrimeInit.no_family_absorption_slot
#print axioms RBM.APrimeInit.stepRhs''_div_le_small_slots
#print axioms RBM.APrimeInit.coordinate_integral_of_small_slots
#print axioms RBM.APrimeInit.cutTrunc_pow_le_family
#print axioms RBM.APrimeInit.integral_cutTrunc_le_family_high
#print axioms RBM.APrimeInit.weightedMomentDom_of_stochDom_of_nonneg
#print axioms RBM.APrimeInit.numerical_hinit_of_weighted_integral
#print axioms RBM.APrimeInit.momNormW_le_momNormW_of_exponent_le
#print axioms RBM.APrimeInit.sat_small_slots_nondegenerate

end RBM.APrimeInit
