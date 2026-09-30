/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUCommonFlow
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.DistEq
import RBM1D.Hierarchy.GUEPhase

/-!
# The GUE-phase grid carrier, path and laws (7.25)/(7.26)

The GUE-phase flow of §7.2,
`H̃_u = √t₁ X + √(u - t₁) Y` in law with `Y` an independent GUE matrix, is realised as a
genuinely discrete grid walk: `K N` independent unit-GUE draws replace the Brownian
increment on `[t₁, t₀]`. This mirrors `RBM.Gauss.Grid` (`Gauss/GridPath.lean`) but with a
**mixed** step law: the band field `P d` at grid step `0`, independent unit-GUE fields
(`gueUnit d`) at every later step.

Only the one-time law at the last grid step `K N` is used ((7.25)/(7.26)); no pathwise identity
between the OU flow and this grid is claimed. `gueGridK` is a proof device
(the grid resolution); it is never used as a hypothesis witness.
-/

noncomputable section

namespace RBM.Gauss.GUEGrid

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

variable (d : Dims)

/-! ### The GUE-phase grid measure -/

/-- Unit GUE coordinate variance: `1` on the diagonal, `1/2` per real component off it. -/
def gueUnitVar (c : Coord d) : ℝ≥0 := if c.2.1 = c.2.2.1 then 1 else 1 / 2

/-- One unit GUE coordinate field (all sizes at once). -/
def gueUnit : Measure (Ω d) := Measure.infinitePi fun c => gaussianReal 0 (gueUnitVar d c)

instance gueUnit_isProbabilityMeasure : IsProbabilityMeasure (gueUnit d) := by
  unfold gueUnit; infer_instance

/-- Step laws: the band field at step `0`, unit GUE fields at steps `k ≥ 1`. -/
def gueStepMeasure : ℕ → Measure (Ω d)
  | 0 => P d
  | _ + 1 => gueUnit d

instance gueStepMeasure_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (gueStepMeasure d k) := by
  cases k <;> simp only [gueStepMeasure] <;> infer_instance

/-- The GUE-phase grid measure on `Grid.Ωg d = ℕ → Ω d` (independent of `N`). -/
def Pgue : Measure (Grid.Ωg d) := Measure.infinitePi (gueStepMeasure d)

instance Pgue_isProbabilityMeasure : IsProbabilityMeasure (Pgue d) := by
  unfold Pgue; infer_instance

/-! ### The GUE-phase grid path -/

/-- The GUE-phase grid path: `H_k = √t₁ X + √(Δ/M) ∑_{i=1}^k Y_i`, `Δ = (t₀-t₁)/K`, `M = L W`. -/
def gueH (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d) :
    Matrix (d.Idx N) (d.Idx N) ℂ :=
  (Real.sqrt (t1 N) : ℂ) • Xmat d N (ω 0) +
    (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ) •
      ∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i)

/-! ### Pointwise algebraic identities (private helpers; reproduce the pattern of
`Gauss/GridPath.lean`'s private `Xentry_add`/`Xentry_smul`/`Xentry_zero`/`Xentry_sum`, which are
not visible outside that file). -/

section Algebra

variable {d}

private lemma ggXentry_add (N : ℕ) (ω1 ω2 : Ω d) (i j : d.Idx N) :
    Xentry d N (ω1 + ω2) i j = Xentry d N ω1 i j + Xentry d N ω2 i j := by
  simp only [Xentry, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

private lemma ggXentry_smul (N : ℕ) (a : ℝ) (ω : Ω d) (i j : d.Idx N) :
    Xentry d N (a • ω) i j = (a : ℂ) * Xentry d N ω i j := by
  simp only [Xentry, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private lemma ggXentry_zero (N : ℕ) (i j : d.Idx N) : Xentry d N (0 : Ω d) i j = 0 := by
  simp only [Xentry, Pi.zero_apply]
  split_ifs <;> simp

private lemma ggXentry_sum {ι : Type*} (N : ℕ) (S : Finset ι) (ω : ι → Ω d) (i j : d.Idx N) :
    Xentry d N (∑ l ∈ S, ω l) i j = ∑ l ∈ S, Xentry d N (ω l) i j := by
  classical
  induction S using Finset.induction with
  | empty => simp [ggXentry_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, ggXentry_add, ih, Finset.sum_insert ha]

private lemma ggSmul_Xmat (N : ℕ) (r : ℝ) (s : Ω d) :
    (r : ℂ) • Xmat d N s = Xmat d N (r • s) := by
  ext i j
  simp only [Matrix.smul_apply, Xmat_apply, smul_eq_mul]
  exact (ggXentry_smul N r s i j).symm

private lemma ggMeasurable_Xmat (N : ℕ) : Measurable (Xmat d N) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d N i j

end Algebra

theorem gueH_isHermitian (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d) :
    (gueH d t1 t0 K N k ω).IsHermitian := by
  have h0 : (Xmat d N (ω 0))ᴴ = Xmat d N (ω 0) := Xmat_isHermitian d N (ω 0)
  have hsum : (∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i))ᴴ
      = ∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i) := by
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => Xmat_isHermitian d N (ω i)
  show (gueH d t1 t0 K N k ω)ᴴ = gueH d t1 t0 K N k ω
  unfold gueH
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    show star (Real.sqrt (t1 N) : ℂ) = (Real.sqrt (t1 N) : ℂ) from Complex.conj_ofReal _,
    show star (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ)
        = (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ)
      from Complex.conj_ofReal _,
    h0, hsum]

theorem gueH_adapted (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (i j : d.Idx N) :
    StronglyMeasurable[Grid.filt d k] (fun ω : Grid.Ωg d => gueH d t1 t0 K N k ω i j) := by
  rw [stronglyMeasurable_iff_measurable]
  have heq : (fun ω : Grid.Ωg d => gueH d t1 t0 K N k ω i j) =
      fun ω => (Real.sqrt (t1 N) : ℂ) * Xentry d N (ω 0) i j
        + (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ) *
            ∑ l ∈ Finset.Icc 1 k, Xentry d N (ω l) i j := by
    funext ω
    simp [gueH, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, Finset.mul_sum]
  rw [heq]
  have hmeas : ∀ l : ℕ, l ≤ k → Measurable[Grid.filt d k] (fun ω : Grid.Ωg d => ω l) := by
    intro l hl
    have : (fun ω : Grid.Ωg d => ω l)
        = (fun g : Set.Iic k → Ω d => g ⟨l, hl⟩) ∘ (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) := rfl
    rw [this]
    exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
      (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k))
  apply Measurable.add
  · exact ((measurable_Xentry d N i j).comp (hmeas 0 (by omega))).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l hl =>
      (measurable_Xentry d N i j).comp (hmeas l (by simp only [Finset.mem_Icc] at hl; omega))

theorem gueH_measurable (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    Measurable (gueH d t1 t0 K N k) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  have heq : (fun ω : Grid.Ωg d => gueH d t1 t0 K N k ω i j) =
      fun ω => (Real.sqrt (t1 N) : ℂ) * Xentry d N (ω 0) i j
        + (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ) *
            ∑ l ∈ Finset.Icc 1 k, Xentry d N (ω l) i j := by
    funext ω
    simp [gueH, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, Finset.mul_sum]
  rw [heq]
  apply Measurable.add
  · exact ((measurable_Xentry d N i j).comp (measurable_pi_apply 0)).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l _ =>
      (measurable_Xentry d N i j).comp (measurable_pi_apply l)

/-! ### A common "mixed step" carrier used to compute both (7.26)'s law and, via
`Measure.infinitePi_map_eval_prod`, the fixed-time OU law of `Flow/OUMarginalGaussian.lean`.

`mixedStepMeasure d v0 v1` is the same shape as `gueStepMeasure`: variance family `v0` at step
`0`, `v1` at steps `≥ 1`. Applied with `(v0, v1) = (gvar d, gueUnitVar d)` it recovers
`gueStepMeasure`; applied with `(v0, v1) = (gvar d, gueCoordVar d N)` and read only at steps
`{0, 1}` it recovers `ouProductMeasure d N`. This lets the same "swap" computation (mirroring
`Gauss/GridPath.lean`'s private `Pg'`/`swapEquiv`/`Pg_swap_eq`, generalized from a constant step
law to a mixed one) serve both laws. -/

section MixedGrid

variable {d}

private def mixedStepMeasure (v0 v1 : Coord d → ℝ≥0) : ℕ → Measure (Ω d)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private instance mixedStepMeasure_isProbabilityMeasure (v0 v1 : Coord d → ℝ≥0) (k : ℕ) :
    IsProbabilityMeasure (mixedStepMeasure v0 v1 k) := by
  cases k <;> simp only [mixedStepMeasure] <;> infer_instance

private def mixedRawStep (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance mixedRawStep_isProbabilityMeasure (v0 v1 : Coord d → ℝ≥0) (c : Coord d)
    (i : ℕ) : IsProbabilityMeasure (mixedRawStep v0 v1 c i) := by
  unfold mixedRawStep; split_ifs <;> infer_instance

private lemma mixedStepMeasure_eq (v0 v1 : Coord d → ℝ≥0) (i : ℕ) :
    mixedStepMeasure v0 v1 i = Measure.infinitePi (fun c => mixedRawStep v0 v1 c i) := by
  cases i <;> simp [mixedStepMeasure, mixedRawStep]

/-- Same nesting as `Gauss/GridPath.lean`'s private `Pg'`: `Coord d` first, then `ℕ`. -/
private def mixedRaw' (v0 v1 : Coord d → ℝ≥0) : Measure (Coord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Coord d => Measure.infinitePi (fun i : ℕ => mixedRawStep v0 v1 c i))

/-- Same reindexing map as `Gauss/GridPath.lean`'s private `swapEquiv`. -/
private def mixedSwapEquiv : (Coord d → ℕ → ℝ) → (ℕ → Ω d) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
    (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm

private lemma measurable_mixedSwapEquiv : Measurable (mixedSwapEquiv (d := d)) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm.measurable)

private lemma mixedSwapEquiv_apply (X : Coord d → ℕ → ℝ) (i : ℕ) (c : Coord d) :
    mixedSwapEquiv X i c = X c i := by
  show (MeasurableEquiv.curry ℕ (Coord d) ℝ)
      ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
        ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm X)) i c = X c i
  rw [MeasurableEquiv.coe_curry]
  show (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
      ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm X) (i, c) = X c i
  have key := MeasurableEquiv.piCongrLeft_apply_apply (Equiv.prodComm (Coord d) ℕ)
    (β := fun _ : ℕ × Coord d => ℝ) ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm X) (c, i)
  rw [show Equiv.prodComm (Coord d) ℕ (c, i) = (i, c) from rfl] at key
  rw [key, MeasurableEquiv.coe_curry_symm]
  rfl

private lemma mixedRaw'_swap_eq (v0 v1 : Coord d → ℝ≥0) :
    (mixedRaw' v0 v1).map mixedSwapEquiv = Measure.infinitePi (mixedStepMeasure v0 v1) := by
  have ha : (mixedRaw' v0 v1).map ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Coord d × ℕ => mixedRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm (μ := fun (c : Coord d) (i : ℕ) => mixedRawStep v0 v1 c i)
  have hb : (Measure.infinitePi (fun p : Coord d × ℕ => mixedRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Coord d => mixedRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Coord d => mixedRawStep v0 v1 p.2 p.1) (Equiv.prodComm (Coord d) ℕ)
  have hc : (Measure.infinitePi (fun p : ℕ × Coord d => mixedRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Coord d) ℝ) = Measure.infinitePi (mixedStepMeasure v0 v1) := by
    rw [Measure.infinitePi_map_curry (μ := fun (i : ℕ) (c : Coord d) => mixedRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi (funext fun i => (mixedStepMeasure_eq v0 v1 i).symm)
  show (mixedRaw' v0 v1).map ((MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm) = Measure.infinitePi (mixedStepMeasure v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- **The one-dimensional mixed-variance sum lemma.** Generalizes `Gauss/GridPath.lean`'s private
`sumIcc_map_gaussianReal`: the law is uniform `w` only from index `1` on (index `0` is untouched
by the conclusion, and indeed unused by this induction, exactly as in the original). -/
private lemma sumIcc_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w : ℝ≥0} (hYd : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w) (k : ℕ) :
    μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w) := by
  induction k with
  | zero =>
      have hEmpty : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
      simp only [hEmpty, Finset.sum_empty]
      rw [Measure.map_const, measure_univ, one_smul, zero_smul, gaussianReal_zero_var]
  | succ k ih =>
      have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
      have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hfun : (fun ω => ∑ i ∈ Finset.Icc 1 (k + 1), Y i ω)
          = (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) + Y (k + 1) := by
        funext ω
        rw [hins, Finset.sum_insert hnotmem, add_comm]
        rfl
      rw [hfun]
      have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
        Finset.measurable_sum _ fun i _ => hYm i
      have hlaw1 : HasLaw (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (gaussianReal 0 (k • w)) μ' :=
        ⟨hsummeas.aemeasurable, ih⟩
      have hlaw2 : HasLaw (Y (k + 1)) (gaussianReal 0 w) μ' :=
        ⟨(hYm (k + 1)).aemeasurable, hYd (k + 1) (by omega)⟩
      have hindep : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y (k + 1)) μ' := by
        have h := hY.indepFun_finsetSum_of_notMem hYm hnotmem
        have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
          funext ω; simp [Finset.sum_apply]
        rwa [heq] at h
      have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw1 hlaw2
      rw [hres, add_zero, ← succ_nsmul]

/-- **The two-scale mixed weighted sum lemma.** Generalizes `Gauss/GridPath.lean`'s private
`weightedSum_map_gaussianReal`: `Y 0` may have a different variance `w0` from the common
variance `w1` of `Y 1, Y 2, …`. -/
private lemma weightedSum_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w0 w1 : ℝ≥0} (hY0 : μ'.map (Y 0) = gaussianReal 0 w0)
    (hY1 : ∀ i, 1 ≤ i → μ'.map (Y i) = gaussianReal 0 w1) (a b : ℝ) (k : ℕ) :
    μ'.map (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * w1)) := by
  classical
  have hindep : IndepFun (fun ω => a * Y 0 ω) (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω) μ' := by
    have h0 : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y 0) μ' := by
      have h := hY.indepFun_finsetSum_of_notMem hYm (s := Finset.Icc 1 k) (i := 0) (by simp)
      have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
        funext ω; simp [Finset.sum_apply]
      rwa [heq] at h
    exact h0.symm.comp (φ := (a * ·)) (ψ := (b * ·)) (by fun_prop) (by fun_prop)
  have hlaw0 : HasLaw (fun ω => a * Y 0 ω) (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0)) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω => a * Y 0 ω) = (a * ·) ∘ Y 0 := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hYm 0), hY0, gaussianReal_map_const_mul, mul_zero]
  have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hYm i
  have hlawsum : μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w1) :=
    sumIcc_map_gaussianReal_mixed hYm hY hY1 k
  have hlaw1 : HasLaw (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (k • w1))) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have heq : (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
        = (b * ·) ∘ (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) := rfl
    rw [heq, ← Measure.map_map (by fun_prop) hsummeas, hlawsum, gaussianReal_map_const_mul, mul_zero]
  have hgoal_eq : (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = (fun ω => a * Y 0 ω) + fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω := rfl
  rw [hgoal_eq]
  have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw0 hlaw1
  rw [hres, add_zero]
  congr 1
  rw [nsmul_eq_mul, nsmul_eq_mul]
  apply NNReal.coe_injective
  push_cast
  ring

private lemma map_column_eq_mixed (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => mixedRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => mixedRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => mixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [mixedRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi (fun i : ℕ => mixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y i) = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    unfold mixedRawStep
    rw [if_neg (by omega)]
  exact weightedSum_map_gaussianReal_mixed hYm hY hY0 hY1 a b k

/-- **The mixed-grid combined law.** Same conclusion shape as `Gauss/GridPath.lean`'s private
`map_combined_eq`, generalized from a constant step law to the mixed `(v0, v1)` law. -/
private lemma map_combined_eq_mixed (v0 v1 : Coord d → ℝ≥0) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (mixedStepMeasure v0 v1)).map (fun ω : ℕ → Ω d =>
        a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
            + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c))) := by
  have hmeasComb : Measurable (fun ω : ℕ → Ω d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : ℕ → Ω d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : ℕ → Ω d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hcomp : (fun ω : ℕ → Ω d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) ∘ mixedSwapEquiv
      = (fun X : Coord d → ℕ → ℝ => fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      mixedSwapEquiv_apply]
  rw [← mixedRaw'_swap_eq v0 v1, Measure.map_map hmeasComb measurable_mixedSwapEquiv, hcomp]
  have hfmeas : ∀ c : Coord d, Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) :=
    fun c => by
      have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
      have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
        Finset.measurable_sum _ fun i _ => measurable_pi_apply i
      exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Coord d => Measure.infinitePi (fun i : ℕ => mixedRawStep v0 v1 c i))
      (f := fun c : Coord d => fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [mixedRaw']
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => map_column_eq_mixed v0 v1 c a b k))

end MixedGrid

/-! ### Identification of `Pgue d` and (via `Measure.infinitePi_map_eval_prod`) of
`ouProductMeasure d N` as instances of the mixed-grid carrier -/

section Identification

private lemma Pgue_eq_mixed : Pgue d = Measure.infinitePi (mixedStepMeasure (gvar d) (gueUnitVar d)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

private lemma ouProductMeasure_eq_mixed_map (N : ℕ) :
    ouProductMeasure d N =
      (Measure.infinitePi (mixedStepMeasure (gvar d) (gueCoordVar d N))).map (fun ω => (ω 0, ω 1)) := by
  rw [Measure.infinitePi_map_eval_prod
    (P := mixedStepMeasure (gvar d) (gueCoordVar d N)) (by norm_num : (0 : ℕ) ≠ 1)]
  rfl

/-- `gueCoordVar` (`Flow/OUMarginalGaussian.lean`) is the unit-GUE variance `gueUnitVar` scaled
down by the matrix size `M`. -/
private lemma gg_gueCoordVar_eq (N : ℕ) (c : Coord d) :
    gueCoordVar d N c = gueUnitVar d c / (ouMatrixSize d N : ℝ≥0) := by
  unfold gueCoordVar gueUnitVar
  split_ifs with h
  · rfl
  · rw [div_div]

end Identification

/-! ### The one-time laws (7.25)/(7.26) -/

/-- Step `0` has the law of the band flow at `t₁`. -/
theorem map_gueH_zero (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ht1 : 0 ≤ t1 N) :
    (Pgue d).map (gueH d t1 t0 K N 0) = (P d).map (Hflow d N (t1 N)) := by
  have heq : gueH d t1 t0 K N 0 = (Hflow d N (t1 N)) ∘ (fun ω : Grid.Ωg d => ω 0) := by
    funext ω
    show gueH d t1 t0 K N 0 ω = Hflow d N (t1 N) (ω 0)
    unfold gueH
    simp [Hflow]
  have hmeasHflow : Measurable (Hflow d N (t1 N)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Hflow d N (t1 N) i j
  rw [heq, ← Measure.map_map hmeasHflow (measurable_pi_apply (0 : ℕ))]
  congr 1
  show (Pgue d).map (fun ω : Grid.Ωg d => ω 0) = P d
  unfold Pgue
  rw [Measure.infinitePi_map_eval]
  rfl

/-- Step `K` with `t₁ = (1 - ζ(τ)) t₀` has the law of `√t₀ · H_τ` ((7.25), (7.26)). -/
theorem map_gueH_last (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ht0 : 0 ≤ t0 N) (hτ : 0 ≤ τ N)
    (hK : K N ≠ 0) :
    (Pgue d).map (gueH d (fun N => (1 - ouZeta (τ N)) * t0 N) t0 K N (K N)) =
      (ouProductMeasure d N).map (fun ω => ((Real.sqrt (t0 N) : ℝ) : ℂ) • ouMatrix d N (τ N) ω) := by
  set t1fn : ℕ → ℝ := fun N' => (1 - ouZeta (τ N')) * t0 N' with ht1fndef
  have hζ0 : 0 ≤ ouZeta (τ N) := by
    unfold ouZeta
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hτ)
    linarith
  have hζ1 : ouZeta (τ N) ≤ 1 := by
    unfold ouZeta
    have := (Real.exp_pos (-(τ N))).le
    linarith
  have ht1N : t1fn N = (1 - ouZeta (τ N)) * t0 N := rfl
  have ht1N0 : 0 ≤ t1fn N := by rw [ht1N]; exact mul_nonneg (by linarith) ht0
  have ht1Nt0 : t1fn N ≤ t0 N := by
    rw [ht1N]; nlinarith
  have hΔ : 0 ≤ Grid.step t1fn t0 K N :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  set M : ℝ := (ouMatrixSize d N : ℝ) with hMdef
  set a : ℝ := Real.sqrt (t1fn N) with hadef
  set b : ℝ := Real.sqrt (Grid.step t1fn t0 K N / M) with hbdef
  set a' : ℝ := Real.sqrt (t0 N) * ouBandCoeff (τ N) with ha'def
  set b' : ℝ := Real.sqrt (t0 N) * ouGueCoeff (τ N) with hb'def
  -- Step 1: rewrite both sides as `Xmat d N` of a real-coordinate combination.
  have hHeq : gueH d t1fn t0 K N (K N)
      = fun ω => Xmat d N (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K N), ω i) := by
    funext ω
    ext i j
    simp only [gueH, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, smul_eq_mul,
      hadef, hbdef, hMdef]
    rw [ggXentry_add, ggXentry_smul, ggXentry_smul, ggXentry_sum]
  have hRHSeq : (fun ω : Ω d × Ω d => ((Real.sqrt (t0 N) : ℝ) : ℂ) • ouMatrix d N (τ N) ω)
      = fun ω => Xmat d N (a' • ω.1 + b' • ω.2) := by
    funext ω
    rw [ouMatrix_eq_interpolatedMatrix]
    unfold ouInterpolatedMatrix
    rw [ggSmul_Xmat]
    congr 1
    funext c
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, ouInterpolatedSample, ha'def, hb'def]
    ring
  have hLHSmeasurable : Measurable (fun ω : ℕ → Ω d =>
      a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K N), ω i) := by
    have h1 : Measurable (fun ω : ℕ → Ω d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : ℕ → Ω d => ∑ i ∈ Finset.Icc 1 (K N), ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hRHSmeasurable : Measurable (fun ω : Ω d × Ω d => a' • ω.1 + b' • ω.2) :=
    (measurable_fst.const_smul a').add (measurable_snd.const_smul b')
  rw [hHeq, hRHSeq,
    show (fun ω : Grid.Ωg d => Xmat d N (a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K N), ω i))
      = Xmat d N ∘ (fun ω => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K N), ω i) from rfl,
    show (fun ω : Ω d × Ω d => Xmat d N (a' • ω.1 + b' • ω.2))
      = Xmat d N ∘ (fun ω => a' • ω.1 + b' • ω.2) from rfl,
    ← Measure.map_map (ggMeasurable_Xmat N) hLHSmeasurable,
    ← Measure.map_map (ggMeasurable_Xmat N) hRHSmeasurable]
  congr 1
  -- Step 2: reduce both sides to instances of the mixed-grid carrier and finish by matching
  -- per-coordinate variances.
  have hRHSstep : (ouProductMeasure d N).map (fun ω => a' • ω.1 + b' • ω.2)
      = (Measure.infinitePi (mixedStepMeasure (gvar d) (gueCoordVar d N))).map
          (fun ω : ℕ → Ω d => a' • ω 0 + b' • ∑ i ∈ Finset.Icc 1 1, ω i) := by
    rw [ouProductMeasure_eq_mixed_map,
      Measure.map_map hRHSmeasurable (show Measurable (fun ω : ℕ → Ω d => (ω 0, ω 1)) by fun_prop)]
    congr 1
    funext ω
    simp [Finset.Icc_self]
  have hLHSstep : (Pgue d).map (fun ω => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 (K N), ω i)
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * gvar d c
            + (K N) • (NNReal.mk (b ^ 2) (sq_nonneg b) * gueUnitVar d c))) := by
    rw [Pgue_eq_mixed]; exact map_combined_eq_mixed (gvar d) (gueUnitVar d) a b (K N)
  have hRHSfinal : (Measure.infinitePi (mixedStepMeasure (gvar d) (gueCoordVar d N))).map
        (fun ω : ℕ → Ω d => a' • ω 0 + b' • ∑ i ∈ Finset.Icc 1 1, ω i)
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0
          (NNReal.mk (a' ^ 2) (sq_nonneg a') * gvar d c
            + (1 : ℕ) • (NNReal.mk (b' ^ 2) (sq_nonneg b') * gueCoordVar d N c))) :=
    map_combined_eq_mixed (gvar d) (gueCoordVar d N) a' b' 1
  rw [hRHSstep, hLHSstep, hRHSfinal]
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  congr 1
  rw [gg_gueCoordVar_eq]
  apply NNReal.coe_injective
  have hMpos : (0 : ℝ) < M := by rw [hMdef]; exact_mod_cast ouMatrixSize_pos d N
  have hΔdiv : 0 ≤ Grid.step t1fn t0 K N / M := div_nonneg hΔ hMpos.le
  have ha2 : a ^ 2 = t1fn N := by rw [hadef, Real.sq_sqrt ht1N0]
  have hb2 : b ^ 2 = Grid.step t1fn t0 K N / M := by rw [hbdef, Real.sq_sqrt hΔdiv]
  have ha'2 : a' ^ 2 = t0 N * (1 - ouZeta (τ N)) := by
    rw [ha'def, mul_pow, Real.sq_sqrt ht0, ouBandCoeff_sq]
  have hb'2 : b' ^ 2 = t0 N * ouZeta (τ N) := by
    rw [hb'def, mul_pow, Real.sq_sqrt ht0, ouGueCoeff_sq _ hτ]
  have hstepval : Grid.step t1fn t0 K N = (t0 N - t1fn N) / (K N : ℝ) := rfl
  have hKcast : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  push_cast [nsmul_eq_mul]
  rw [ha2, hb2, ha'2, hb'2, ht1N, hstepval, hMdef]
  field_simp
  ring

/-- The same on the common carrier of `ouCommonFlow`. -/
theorem map_ouCommonFlow_smul_eq_gueH_last (t0 τ : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (ht0 : 0 ≤ t0 N) (hτ : 0 ≤ τ N) (hK : K N ≠ 0) :
    (ouCommonMeasure d).map
        (fun ω => ((Real.sqrt (t0 N) : ℝ) : ℂ) • (ouCommonFlow d).Ht N (τ N) ω) =
      (Pgue d).map (gueH d (fun N => (1 - ouZeta (τ N)) * t0 N) t0 K N (K N)) := by
  have hmatMeas : Measurable (ouMatrix d N (τ N)) := by
    rw [show ouMatrix d N (τ N) = ouInterpolatedMatrix d N (τ N) from
      funext (ouMatrix_eq_interpolatedMatrix d N (τ N))]
    apply measurable_pi_iff.2; intro i; apply measurable_pi_iff.2; intro j
    have hs : Measurable (ouInterpolatedSample d N (τ N)) := by
      apply measurable_pi_iff.2; intro c
      simp only [ouInterpolatedSample]; fun_prop
    exact (measurable_Xentry d N i j).comp hs
  have hmeas : Measurable (fun ω : Ω d × Ω d => ((Real.sqrt (t0 N) : ℝ) : ℂ) • ouMatrix d N (τ N) ω) :=
    hmatMeas.const_smul ((Real.sqrt (t0 N) : ℝ) : ℂ)
  show (ouCommonMeasure d).map
      ((fun ω' => ((Real.sqrt (t0 N) : ℝ) : ℂ) • ouMatrix d N (τ N) ω') ∘ (ouCommonProjection d N))
      = _
  rw [← Measure.map_map hmeas (ouCommonProjection_measurable d N), ouCommonProjection_map,
    map_gueH_last d t0 τ K N ht0 hτ hK]

/-! ### The grid resolution (a proof device, never a hypothesis witness) -/

/-- The grid size used for the GUE phase: `K N = (N+1)^(32 n₀ + 64)`. -/
def gueGridK (n0 N : ℕ) : ℕ := (N + 1) ^ (32 * n0 + 64)

theorem gueGridK_ne_zero (n0 N : ℕ) : gueGridK n0 N ≠ 0 := by
  unfold gueGridK; positivity

/-- `N η_u` of the GUE phase (`N = L W`). -/
def gueScale (E : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ := ((d.L N * d.W N : ℕ) : ℝ) * etaT (E N) u

/-- **The output of the §7.2 random layer** at the grid times `k ≤ K N`: (7.28) for
`1 ≤ n ≤ n₀` against a primitive family `Kt`, and `‖G̃ - m‖_max ≺ (N η_u)^{-1/2}`. -/
structure GUEPathBounds (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n0 : ℕ)
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (d.L N)) → ℂ) : Prop where
  lk : ∀ n : ℕ, 1 ≤ n → n ≤ n0 → StochDom (Pgue d)
    (fun N (p : Fin (K N + 1) × LoopData (d.L N) n) ω =>
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N p.1 ω) (zt (E N) (Grid.time t1 t0 K N p.1))
          p.2.idx - Kt N (Grid.time t1 t0 K N p.1) p.2.idx‖)
    (fun N p _ => (gueScale d E N (Grid.time t1 t0 K N p.1))⁻¹ ^ n)
  localLaw : StochDom (Pgue d)
    (fun N (p : Fin (K N + 1) × (d.Idx N × d.Idx N)) ω =>
      ‖(green (gueH d t1 t0 K N p.1 ω) (zt (E N) (Grid.time t1 t0 K N p.1)) -
          mE (E N) • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) p.2.1 p.2.2‖)
    (fun N p _ => (gueScale d E N (Grid.time t1 t0 K N p.1))⁻¹ ^ ((1 : ℝ) / 2))

/-! ### The GUE-phase flow carrying only the `t₀`-marginal, and (7.26) -/

private lemma smul_isHermitian {n : Type*} (r : ℝ)
    (M : Matrix n n ℂ) (hM : M.IsHermitian) : ((r : ℂ) • M).IsHermitian :=
  hM.smul (R := ℂ) (Complex.conj_ofReal r)

/-- The `GUEFlow` carrying only the `t₀`-marginal that `Eq747Inputs` evaluates:
`H̃_s := √s · H_{t_N}` on the common carrier.  It is **not** a GUE-phase path. -/
def gueFlowCommon (t : ℕ → ℝ) : GUEPhase.GUEFlow (ouCommonBand d) where
  Ht N s ω := ((Real.sqrt s : ℝ) : ℂ) • (ouCommonFlow d).Ht N (t N) ω
  hermitian N s ω := smul_isHermitian (Real.sqrt s) _ ((ouCommonFlow d).hermitian N (t N) ω)

/-- **General homogeneity of `gloop`** for any Hermitian-typed `M` and `z` with `0 < z.im`:
`gloop M z = (√t₀)^n · gloop (√t₀ • M) (zt (lemE z) (lemT z))`, `t₀ = lemT z`, `n` the loop
length.  This is the general (matrix-free of `Xmat`) form of `Gauss/DistEq.lean`'s
`gloop_Hflow_lemT_eq`, obtained from the same two general facts: `RBM.Gauss.zt_eq_sqrt_lemT_mul`
and `RBM.Gauss.gloop_smul_mul` (a private helper reproducing an existing pattern for a
matrix that is not `Xmat`). -/
private lemma gloop_smul_lemT_eq {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) {z : ℂ} (hz : 0 < z.im)
    (σ : List Bool) (a : List (ZMod L)) :
    gloop L W M z ⟨σ, a⟩
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        gloop L W (((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • M)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨σ, a⟩ := by
  have hs : ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RBM.lemT_pos hz)).ne'
  rw [zt_eq_sqrt_lemT_mul hz, gloop_smul_mul hs]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]

/-- **General homogeneity of the 2-loop `gloop`**: for any `M` and `z` with `0 < z.im`,
`gloop M z = t₀ · gloop (√t₀ • M) (zt (lemE z) (lemT z))`, `t₀ = lemT z`. -/
private lemma gloop_two_smul_lemT_eq {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) {z : ℂ} (hz : 0 < z.im) (σ₂ : Bool)
    (a b : ZMod L) :
    gloop L W M z ⟨[true, σ₂], [a, b]⟩
      = ((RBM.lemT z : ℝ) : ℂ) *
        gloop L W (((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • M)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨[true, σ₂], [a, b]⟩ := by
  have hlen : (([true, σ₂] : List Bool).zip [a, b]).length = 2 := rfl
  rw [gloop_smul_lemT_eq M hz [true, σ₂] [a, b], hlen, ← Complex.ofReal_pow,
    Real.sq_sqrt (RBM.lemT_pos hz).le]

/-- **(7.26)**, pointwise scaling: the `law726` field of `Eq747Inputs` for `gueFlowCommon`. -/
theorem law726_gueFlowCommon (t : ℕ → ℝ) (τ : ℝ) (E : ℕ → ℝ) :
    ∀ N (σ₂ : Bool) (a b : ZMod ((ouCommonBand d).L N)),
      ∫ ω, gloop ((ouCommonBand d).L N) ((ouCommonBand d).W N) ((ouCommonFlow d).Ht N (t N) ω)
          ((ouCommonBand d).queZ τ E N) ⟨[true, σ₂], [a, b]⟩ ∂(ouCommonBand d).P =
        (lemT ((ouCommonBand d).queZ τ E N) : ℂ) *
          ∫ ω, GUEPhase.loopG (gueFlowCommon d t) N (lemE ((ouCommonBand d).queZ τ E N))
            (lemT ((ouCommonBand d).queZ τ E N)) ω σ₂ a b ∂(ouCommonBand d).P := by
  intro N σ₂ a b
  have hsize_pos : 0 < (ouCommonBand d).size N := by
    have h := (ouCommonBand d).one_le_size N; omega
  have hW_pos : 0 < (ouCommonBand d).W N := (ouCommonBand d).W_pos N
  have hz : 0 < ((ouCommonBand d).queZ τ E N).im := by
    rw [Band.queZ_im]; exact queEta_pos (by exact_mod_cast hsize_pos) (by exact_mod_cast hW_pos)
  have key : ∀ ω, gloop ((ouCommonBand d).L N) ((ouCommonBand d).W N)
        ((ouCommonFlow d).Ht N (t N) ω) ((ouCommonBand d).queZ τ E N) ⟨[true, σ₂], [a, b]⟩
      = (lemT ((ouCommonBand d).queZ τ E N) : ℂ) *
          GUEPhase.loopG (gueFlowCommon d t) N (lemE ((ouCommonBand d).queZ τ E N))
            (lemT ((ouCommonBand d).queZ τ E N)) ω σ₂ a b := by
    intro ω
    unfold GUEPhase.loopG gueFlowCommon
    exact gloop_two_smul_lemT_eq ((ouCommonFlow d).Ht N (t N) ω) hz σ₂ a b
  simp only [key]
  rw [MeasureTheory.integral_const_mul]

end RBM.Gauss.GUEGrid
