/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFirstCellQVCurrentRows
import RBM1D.Gauss.APrimeFirstCellPrefixGlobalPoly
import RBM1D.Gauss.APrimeTimeInt

/-!
# T457: finite-N integrability of the literal first-cell full-cross rate

The only time singularity is the totalized factor `(sqrt r)⁻¹`.  The three
current-rate rows are continuous on a moving first-cell interval, including
both endpoints.
-/

namespace RBM.APrimeFirstCellFullCrossIntegrability

open Filter MeasureTheory Set Gauss CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

/-- The literal T361 full-cross candidate with fixed numerical envelope
parameters. -/
noncomputable def Bfull (p : ℕ) (b Eall ρ δ ν : ℝ) (N : ℕ) (v r : ℝ) : ℝ :=
  (15 * (p : ℝ) / 8) * (Real.sqrt r)⁻¹ *
    (b * Real.sqrt
        (APrimeFirstCellQVCurrentRows.currentRate δ (δ / 16) ν N v r) +
      Eall * ρ ^ (1 / (2 * (p : ℝ))))

/-- Totalization of the inverse square root makes the full-cross candidate
exactly zero at the left endpoint. -/
@[simp] theorem Bfull_zero (p : ℕ) (b Eall ρ δ ν : ℝ) (N : ℕ) (v : ℝ) :
    Bfull p b Eall ρ δ ν N v 0 = 0 := by
  simp [Bfull]

/-- The moving current rate is continuous on every first-cell interval. -/
theorem continuousOn_currentRate {δ ν : ℝ} {N : ℕ} {v : ℝ}
    (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2) :
    ContinuousOn
      (fun r => APrimeFirstCellQVCurrentRows.currentRate
        δ (δ / 16) ν N v r) (Icc (0 : ℝ) v) := by
  have hηc : Continuous fun r : ℝ => etaT 0 r :=
    APrimeTimeInt.etaT_continuous 0
  have hηne : ∀ r ∈ Icc (0 : ℝ) v, etaT 0 r ≠ 0 := by
    intro r hr
    exact (Step2.etaT_pos' (by norm_num)
      (hr.2.trans_lt (hvhalf.trans_lt (by norm_num)))).ne'
  have hxc : ContinuousOn (fun r => APrimeFirstCellLoopCap.xRate r)
      (Icc (0 : ℝ) v) := by
    unfold APrimeFirstCellLoopCap.xRate
    exact continuousOn_const.div hηc.continuousOn hηne
  have hxpos : ∀ r ∈ Icc (0 : ℝ) v,
      0 < APrimeFirstCellLoopCap.xRate r := by
    intro r hr
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num)
        (hr.2.trans_lt (hvhalf.trans_lt (by norm_num))))
  have hxpow (q : ℝ) : ContinuousOn
      (fun r => APrimeFirstCellLoopCap.xRate r ^ q) (Icc (0 : ℝ) v) :=
    hxc.rpow_const (fun r hr => Or.inl (hxpos r hr).ne')
  have hηinv : ContinuousOn (fun r => (etaT 0 r)⁻¹) (Icc (0 : ℝ) v) :=
    hηc.continuousOn.inv₀ hηne
  have hpref : ContinuousOn
      (fun r =>
        (APrimeFirstCellQVCurrentRows.currentConstant * (N : ℝ) ^ ν) *
          (etaT 0 r)⁻¹ *
            APrimeFirstCellLoopCap.xRate v ^ (-(4 : ℝ)))
      (Icc (0 : ℝ) v) :=
    (continuousOn_const.mul hηinv).mul continuousOn_const
  have hrow1 := hxpow (-(3 / 2 : ℝ))
  have hrow2 : ContinuousOn
      (fun r =>
        ((N : ℝ) ^ (4 * δ + 2 * (δ / 16)) *
          APrimeFirstCellLoopCap.endpointScale N v ^ (-(1 / 2 : ℝ))) *
            APrimeFirstCellLoopCap.xRate r ^ (19 / 4 : ℝ))
      (Icc (0 : ℝ) v) :=
    continuousOn_const.mul (hxpow (19 / 4 : ℝ))
  have hrow3 : ContinuousOn
      (fun r =>
        ((N : ℝ) ^ (6 * δ + 3 * (δ / 16)) *
          (APrimeFirstCellLoopCap.endpointScale N v)⁻¹) *
            APrimeFirstCellLoopCap.xRate r ^ (8 : ℝ))
      (Icc (0 : ℝ) v) :=
    continuousOn_const.mul (hxpow (8 : ℝ))
  unfold APrimeFirstCellQVCurrentRows.currentRate
  exact hpref.mul ((hrow1.add hrow2).add hrow3)

/-- Every one of the three current rows is nonnegative on the first cell. -/
theorem currentRate_nonneg {δ ν : ℝ} {N : ℕ} {v r : ℝ}
    (hN : 1 ≤ N) (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hr : r ∈ Icc (0 : ℝ) v) :
    0 ≤ APrimeFirstCellQVCurrentRows.currentRate
      δ (δ / 16) ν N v r := by
  have hr1 : r < 1 := hr.2.trans_lt (hvhalf.trans_lt (by norm_num))
  have hv1 : v < 1 := hvhalf.trans_lt (by norm_num)
  have hηr : 0 < etaT 0 r := Step2.etaT_pos' (by norm_num) hr1
  have hxr : 0 < APrimeFirstCellLoopCap.xRate r := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num)) hηr
  have hxv : 0 < APrimeFirstCellLoopCap.xRate v := by
    unfold APrimeFirstCellLoopCap.xRate
    exact div_pos (Step2.etaT_pos' (by norm_num) (by norm_num))
      (Step2.etaT_pos' (by norm_num) hv1)
  have hA : 0 < APrimeFirstCellLoopCap.endpointScale N v :=
    B.scale_pos' (by norm_num) N hv0 hv1
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold APrimeFirstCellQVCurrentRows.currentRate
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg
          APrimeFirstCellQVCurrentRows.currentConstant_pos.le
          (Real.rpow_nonneg hNR.le _)
      · exact inv_nonneg.mpr hηr.le
    · exact Real.rpow_nonneg hxv.le _
  · apply add_nonneg
    · apply add_nonneg
      · exact Real.rpow_nonneg hxr.le _
      · exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hNR.le _)
            (Real.rpow_nonneg hA.le _))
          (Real.rpow_nonneg hxr.le _)
    · exact mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hNR.le _) (inv_nonneg.mpr hA.le))
        (Real.rpow_nonneg hxr.le _)

/-- Fixed-N integrability of the literal full-cross candidate, together with
all prefix restrictions of its moving time interval. -/
theorem intervalIntegrable_Bfull {δ ν b Eall ρ : ℝ} {N p : ℕ} {v : ℝ}
    (hδ : 0 ≤ δ) (hν : 0 < ν) (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hv0 : 0 ≤ v) (hvhalf : v ≤ 1 / 2)
    (hb : 0 ≤ b) (hEall : 0 ≤ Eall) (hρ : 0 ≤ ρ) :
    IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 v ∧
      ∀ u ∈ Icc (0 : ℝ) v,
        IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 u := by
  have hrate := continuousOn_currentRate (δ := δ) (ν := ν) (N := N)
    hv0 hvhalf
  have hsqrt : ContinuousOn
      (fun r => Real.sqrt
        (APrimeFirstCellQVCurrentRows.currentRate δ (δ / 16) ν N v r))
      (Icc (0 : ℝ) v) :=
    Real.continuous_sqrt.comp_continuousOn hrate
  have hbracket : ContinuousOn
      (fun r => b * Real.sqrt
          (APrimeFirstCellQVCurrentRows.currentRate δ (δ / 16) ν N v r) +
        Eall * ρ ^ (1 / (2 * (p : ℝ))))
      (Icc (0 : ℝ) v) :=
    (continuousOn_const.mul hsqrt).add continuousOn_const
  have hbase : IntervalIntegrable
      (fun r : ℝ => (15 * (p : ℝ) / 8) * (Real.sqrt r)⁻¹)
      volume 0 v := by
    simpa using (APrimeTimeInt.intervalIntegrable_sqrt_inv hv0).const_mul
      (15 * (p : ℝ) / 8)
  have hfull : IntervalIntegrable (Bfull p b Eall ρ δ ν N v)
      volume 0 v := by
    change IntervalIntegrable
      (fun r : ℝ => (15 * (p : ℝ) / 8) * (Real.sqrt r)⁻¹ *
        (b * Real.sqrt
            (APrimeFirstCellQVCurrentRows.currentRate
              δ (δ / 16) ν N v r) +
          Eall * ρ ^ (1 / (2 * (p : ℝ))))) volume 0 v
    exact hbase.mul_continuousOn (by
      simpa only [Set.uIcc_of_le hv0] using hbracket)
  refine ⟨hfull, ?_⟩
  intro u hu
  apply hfull.mono_set
  rw [Set.uIcc_of_le hu.1, Set.uIcc_of_le hv0]
  intro r hr
  exact ⟨hr.1, hr.2.trans hu.2⟩

/-- The fixed-N result at an actual moving first-cell endpoint. -/
theorem actual_intervalIntegrable_Bfull {τ' δ ν b Eall ρ : ℝ}
    (hτ' : 0 < τ') (hδ : 0 ≤ δ) (hν : 0 < ν)
    {N p k : ℕ} (hN : 1 ≤ N) (hp : 1 ≤ p)
    (hk : k ≤ cutNetTop (fun _ => 0) (firstCellT τ')
      APrimeSmoothTransition.transitionMesh N)
    (hb : 0 ≤ b) (hEall : 0 ≤ Eall) (hρ : 0 ≤ ρ) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N k
    IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 v ∧
      ∀ u ∈ Icc (0 : ℝ) v,
        IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 u := by
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N k
  have ht := APrimeSupportRunning.firstT_bounds hτ' N
  have hv := MomentDuhamelCut.netFinset_subset_Icc ht.1
    (APrimeSupportRunning.mesh_pos N) v (cutNetPt_mem_netFinset hk)
  exact intervalIntegrable_Bfull hδ hν hN hp hv.1 (hv.2.trans ht.2)
    hb hEall hρ

/-- The zero mesh index has the empty time interval. -/
theorem intervalIntegrable_Bfull_k0 (δ ν b Eall ρ : ℝ) (N p : ℕ) :
    let v := cutNetPt (fun _ => 0)
      APrimeSmoothTransition.transitionMesh N 0
    IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 v := by
  simp only [cutNetPt_zero]
  simp

/-- The first positive two-step resident has the same fixed-N integrability
package.  No transition-set inhabitance is asserted. -/
theorem eventually_positive_two_Bfull {τ' δ ν b Eall ρ : ℝ}
    (p : ℕ) (hp : 1 ≤ p) (hτ' : 0 < τ') (hδ : 0 ≤ δ) (hν : 0 < ν)
    (hb : 0 ≤ b) (hEall : 0 ≤ Eall) (hρ : 0 ≤ ρ) :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧
        2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N ∧
        IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 v ∧
        ∀ u ∈ Icc (0 : ℝ) v,
          IntervalIntegrable (Bfull p b Eall ρ δ ν N v) volume 0 u := by
  filter_upwards
    [APrimeFirstCellPrefixGlobalPoly.eventually_positive_two_prefix_le_poly
      hτ' hδ, eventually_ge_atTop 1] with N hgeo hN
  let v := cutNetPt (fun _ => 0)
    APrimeSmoothTransition.transitionMesh N 2
  have hvpos : 0 < v := by
    dsimp only [v]
    simp only [cutNetPt, zero_add, Nat.cast_ofNat]
    exact div_pos (by norm_num) (APrimeSupportRunning.mesh_pos N)
  have hint := actual_intervalIntegrable_Bfull hτ' hδ hν hN hp hgeo.2.1
    hb hEall hρ
  exact ⟨hvpos, hgeo.2.1, hint.1, hint.2⟩

/-- A nonzero numerical instance of the positive two-step package, with
`b = Eall = ρ = 1`. -/
theorem eventually_positive_two_unit_Bfull {τ' δ ν : ℝ}
    (p : ℕ) (hp : 1 ≤ p) (hτ' : 0 < τ') (hδ : 0 ≤ δ) (hν : 0 < ν) :
    ∀ᶠ N : ℕ in atTop,
      let v := cutNetPt (fun _ => 0)
        APrimeSmoothTransition.transitionMesh N 2
      0 < v ∧
        2 ≤ cutNetTop (fun _ => 0) (firstCellT τ')
          APrimeSmoothTransition.transitionMesh N ∧
        IntervalIntegrable (Bfull p 1 1 1 δ ν N v) volume 0 v ∧
        ∀ u ∈ Icc (0 : ℝ) v,
          IntervalIntegrable (Bfull p 1 1 1 δ ν N v) volume 0 u :=
  eventually_positive_two_Bfull p hp hτ' hδ hν
    (by norm_num) (by norm_num) (by norm_num)

#print axioms Bfull_zero
#print axioms continuousOn_currentRate
#print axioms currentRate_nonneg
#print axioms intervalIntegrable_Bfull
#print axioms actual_intervalIntegrable_Bfull
#print axioms intervalIntegrable_Bfull_k0
#print axioms eventually_positive_two_Bfull
#print axioms eventually_positive_two_unit_Bfull

end RBM.APrimeFirstCellFullCrossIntegrability
