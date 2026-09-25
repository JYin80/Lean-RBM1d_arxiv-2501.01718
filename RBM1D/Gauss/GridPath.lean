/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Probability.Process.Filtration

/-!
# The discrete grid path replacing the Brownian flow (2.34), §5.3

Formalization of pilot P1 (`docs/claude-team/pilot-P4P5-paper.md` §2): a genuinely discrete
model `H_{u_k}` built from `K` independent, one-time draws of the Gaussian band matrix `X`
(`RBM.Gauss.Xmat`), together with a **transfer lemma** identifying its one-time law with that of
the existing flow `RBM.Gauss.Hflow` at the matching grid time.

This is T1481 (amend-1), pilot P1 of the True-Path track.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

variable (d : Dims)

/-! ### T1 : the grid sample space -/

/-- The grid sample space: one full one-time draw of `X` per grid step `k : ℕ`. -/
abbrev Ωg : Type := ℕ → Ω d

/-- The grid measure: independent copies of `RBM.Gauss.P d`, one per grid step. -/
def Pg : Measure (Ωg d) := Measure.infinitePi fun _ : ℕ => P d

instance isProbabilityMeasure_Pg (d : Dims) : IsProbabilityMeasure (Pg d) := by
  unfold Pg; infer_instance

/-! ### T2 : the grid times -/

variable (s t : ℕ → ℝ) (K : ℕ → ℕ)

/-- The grid spacing `Δ = (t - s) / K` at size parameter `N`. -/
def step (N : ℕ) : ℝ := (t N - s N) / K N

/-- The grid time `u_k = s + k Δ` at size parameter `N`. -/
def time (N k : ℕ) : ℝ := s N + k * step s t K N

@[simp] theorem time_zero (N : ℕ) : time s t K N 0 = s N := by simp [time]

theorem time_last (N : ℕ) (hK : K N ≠ 0) : time s t K N (K N) = t N := by
  have hK' : (K N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
  unfold time step
  rw [mul_div_cancel₀ _ hK']
  ring

/-! ### T3 : the grid flow -/

/-- The grid flow at grid step `k` and size parameter `N`: the partial sum
`H_{u_k} = √(s N) X_0 + √Δ ∑_{i=1}^{k} X_i` of independent draws of `X`. -/
def H (N k : ℕ) (ω : Ωg d) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  (Real.sqrt (s N) : ℂ) • Xmat d N (ω 0)
    + (Real.sqrt (step s t K N) : ℂ) • ∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i)

theorem H_isHermitian (N k : ℕ) (ω : Ωg d) : (H d s t K N k ω).IsHermitian := by
  have h0 : (Xmat d N (ω 0))ᴴ = Xmat d N (ω 0) := Xmat_isHermitian d N (ω 0)
  have hsum : (∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i))ᴴ
      = ∑ i ∈ Finset.Icc 1 k, Xmat d N (ω i) := by
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun i _ => Xmat_isHermitian d N (ω i)
  show (H d s t K N k ω)ᴴ = H d s t K N k ω
  unfold H
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul,
    show star (Real.sqrt (s N) : ℂ) = (Real.sqrt (s N) : ℂ) from Complex.conj_ofReal _,
    show star (Real.sqrt (step s t K N) : ℂ) = (Real.sqrt (step s t K N) : ℂ)
      from Complex.conj_ofReal _,
    h0, hsum]

theorem measurable_H (N k : ℕ) (i j : d.Idx N) :
    Measurable fun ω : Ωg d => H d s t K N k ω i j := by
  have heq : (fun ω : Ωg d => H d s t K N k ω i j) =
      fun ω => (Real.sqrt (s N) : ℂ) * Xentry d N (ω 0) i j
        + (Real.sqrt (step s t K N) : ℂ) * ∑ l ∈ Finset.Icc 1 k, Xentry d N (ω l) i j := by
    funext ω
    simp [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, Finset.mul_sum]
  rw [heq]
  apply Measurable.add
  · exact ((measurable_Xentry d N i j).comp (measurable_pi_apply 0)).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l _ => (measurable_Xentry d N i j).comp (measurable_pi_apply l)

/-! ### T5 : the coordinate filtration -/

/-- The coordinate filtration on the grid sample space: `filt d k` consists of the events
depending only on the draws `ω 0, …, ω k`. -/
def filt : Filtration ℕ (inferInstance : MeasurableSpace (Ωg d)) :=
  MeasureTheory.Filtration.piLE

theorem H_adapted (N k : ℕ) (i j : d.Idx N) :
    StronglyMeasurable[filt d k] (fun ω : Ωg d => H d s t K N k ω i j) := by
  rw [stronglyMeasurable_iff_measurable]
  have heq : (fun ω : Ωg d => H d s t K N k ω i j) =
      fun ω => (Real.sqrt (s N) : ℂ) * Xentry d N (ω 0) i j
        + (Real.sqrt (step s t K N) : ℂ) * ∑ l ∈ Finset.Icc 1 k, Xentry d N (ω l) i j := by
    funext ω
    simp [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, Finset.mul_sum]
  rw [heq]
  have hmeas : ∀ l : ℕ, l ≤ k → Measurable[filt d k] (fun ω : Ωg d => ω l) := by
    intro l hl
    have : (fun ω : Ωg d => ω l)
        = (fun g : Set.Iic k → Ω d => g ⟨l, hl⟩) ∘ (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) := rfl
    rw [this]
    exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
      (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k))
  apply Measurable.add
  · exact ((measurable_Xentry d N i j).comp (hmeas 0 (by omega))).const_mul _
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun l hl =>
      (measurable_Xentry d N i j).comp (hmeas l (by simp only [Finset.mem_Icc] at hl; omega))

/-! ### T6 : increment independence and law -/

/-- The `k`-th increment `ω ↦ ω (k+1)` is independent of the coordinate filtration `filt d k`. -/
theorem indep_incr (k : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : Ωg d => ω (k + 1)) inferInstance) (filt d k) (Pg d) := by
  have hI : iIndepFun (fun i : ℕ => (fun ω : Ωg d => ω i)) (Pg d) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : Ω d → Ω d)) (mX := fun _ => measurable_id)
  have hIndep : iIndep (fun n : ℕ => MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance)
      (Pg d) := (iIndepFun_iff_iIndep (fun _ : ℕ => (inferInstance : MeasurableSpace (Ω d)))
        (fun i ω => ω i) (Pg d)).mp hI
  have hle : ∀ n : ℕ, MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance
      ≤ (inferInstance : MeasurableSpace (Ωg d)) :=
    fun n => le_iSup (fun n => MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance) n
  have hsplit := indep_biSup_compl hle hIndep (Set.Iic k)
  have hfilt : filt d k
      = ⨆ n ∈ Set.Iic k, MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance := by
    have hshow : filt d k =
        (inferInstance : MeasurableSpace (↥(Set.Iic k) → Ω d)).comap
          (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) := rfl
    have hpi : (inferInstance : MeasurableSpace (↥(Set.Iic k) → Ω d))
        = ⨆ a : ↥(Set.Iic k),
            MeasurableSpace.comap (fun g : ↥(Set.Iic k) → Ω d => g a) inferInstance := rfl
    rw [hshow, hpi, MeasurableSpace.comap_iSup, iSup_subtype]
    simp only [MeasurableSpace.comap_comp]
    apply iSup_congr
    intro i
    apply iSup_congr
    intro _
    rfl
  rw [hfilt]
  have hmono : MeasurableSpace.comap (fun ω : Ωg d => ω (k + 1)) inferInstance
      ≤ ⨆ n ∈ (Set.Iic k)ᶜ, MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance := by
    have hmem : (k + 1) ∈ (Set.Iic k)ᶜ := by simp
    exact le_biSup (fun n => MeasurableSpace.comap (fun ω : Ωg d => ω n) inferInstance) hmem
  exact indep_of_indep_of_le_left hsplit.symm hmono

/-- The law of a single increment is `P d`. -/
theorem map_incr (k : ℕ) : (Pg d).map (fun ω : Ωg d => ω (k + 1)) = P d :=
  MeasureTheory.Measure.infinitePi_map_eval _ (k + 1)

/-! ### T4 : the transfer lemma

`combined d s t K N k` collapses `k+1` independent one-time draws of `X` into a single
`Ω d`-valued (real, coordinatewise) linear combination whose law, at each raw coordinate, matches
that of a single draw scaled to variance `time s t K N k`. -/

section AlgebraicIdentities

variable {d}

private lemma Xentry_add (N : ℕ) (ω1 ω2 : Ω d) (i j : d.Idx N) :
    Xentry d N (ω1 + ω2) i j = Xentry d N ω1 i j + Xentry d N ω2 i j := by
  simp only [Xentry, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

private lemma Xentry_smul (N : ℕ) (a : ℝ) (ω : Ω d) (i j : d.Idx N) :
    Xentry d N (a • ω) i j = (a : ℂ) * Xentry d N ω i j := by
  simp only [Xentry, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private lemma Xentry_zero (N : ℕ) (i j : d.Idx N) : Xentry d N (0 : Ω d) i j = 0 := by
  simp only [Xentry, Pi.zero_apply]
  split_ifs <;> simp

private lemma Xentry_sum {ι : Type*} (N : ℕ) (S : Finset ι) (ω : ι → Ω d) (i j : d.Idx N) :
    Xentry d N (∑ l ∈ S, ω l) i j = ∑ l ∈ S, Xentry d N (ω l) i j := by
  classical
  induction S using Finset.induction with
  | empty => simp [Xentry_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Xentry_add, ih, Finset.sum_insert ha]

end AlgebraicIdentities

section OneDimensionalGaussianSum

/-- **The Icc-sum of an iid centred Gaussian family is Gaussian with added variance.** A pure
probability fact, with no reference to the Gaussian band model. -/
private lemma sumIcc_map_gaussianReal {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w : ℝ≥0} (hYd : ∀ i, μ'.map (Y i) = gaussianReal 0 w) (k : ℕ) :
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
      have hlaw2 : HasLaw (Y (k + 1)) (gaussianReal 0 w) μ' := ⟨(hYm (k + 1)).aemeasurable, hYd (k + 1)⟩
      have hindep : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y (k + 1)) μ' := by
        have h := hY.indepFun_finsetSum_of_notMem hYm hnotmem
        have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
          funext ω; simp [Finset.sum_apply]
        rwa [heq] at h
      have hres := gaussianReal_add_gaussianReal_of_indepFun hindep hlaw1 hlaw2
      rw [hres, add_zero, ← succ_nsmul]

/-- **The two-scale weighted sum lemma.** With `a` scaling the base draw `Y 0` and `b` scaling
each of the `k` increments `Y 1, …, Y k`, the total variance is `a² w + k (b² w)`. This is the
one-dimensional core of the transfer lemma (T4): applied at each raw coordinate `c`, and again to
the family `ν c := infinitePi (fun _ : ℕ ↦ gaussianReal 0 (gvar d c))`, it produces the law of the
grid combination `combined`. -/
private lemma weightedSum_map_gaussianReal {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {Y : ℕ → Ω' → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hY : iIndepFun Y μ') {w : ℝ≥0} (hYd : ∀ i, μ'.map (Y i) = gaussianReal 0 w) (a b : ℝ) (k : ℕ) :
    μ'.map (fun ω => a * Y 0 ω + b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * w)) := by
  classical
  have hindep : IndepFun (fun ω => a * Y 0 ω) (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω) μ' := by
    have h0 : IndepFun (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) (Y 0) μ' := by
      have h := hY.indepFun_finsetSum_of_notMem hYm (s := Finset.Icc 1 k) (i := 0) (by simp)
      have heq : (∑ j ∈ Finset.Icc 1 k, Y j) = fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω := by
        funext ω; simp [Finset.sum_apply]
      rwa [heq] at h
    exact h0.symm.comp (φ := (a * ·)) (ψ := (b * ·)) (by fun_prop) (by fun_prop)
  have hlaw0 : HasLaw (fun ω => a * Y 0 ω) (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w)) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω => a * Y 0 ω) = (a * ·) ∘ Y 0 := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hYm 0), hYd 0, gaussianReal_map_const_mul, mul_zero]
  have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hYm i
  have hlawsum : μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w) :=
    sumIcc_map_gaussianReal hYm hY hYd k
  have hlaw1 : HasLaw (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (k • w))) μ' := by
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

end OneDimensionalGaussianSum

section NNRealHelpers

private lemma NNReal_mk_add_smul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    NNReal.mk x hx + k • NNReal.mk y hy
      = NNReal.mk (x + k * y) (add_nonneg hx (mul_nonneg (Nat.cast_nonneg k) hy)) := by
  apply NNReal.coe_injective
  push_cast
  ring

end NNRealHelpers

section CombinedIdentities

variable {d}

/-- `H` collapses to `Xmat` evaluated at the real-linear grid combination of the raw draws. -/
private lemma H_eq_Xmat_combined (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Ωg d) :
    H d s t K N k ω
      = Xmat d N ((Real.sqrt (s N) : ℝ) • ω 0
          + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i) := by
  ext i j
  simp only [H, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, smul_eq_mul]
  rw [Xentry_add, Xentry_smul, Xentry_smul, Xentry_sum]

/-- `Hflow` collapses to `Xmat` evaluated at the real scaling `√u • ω'`. -/
private lemma Hflow_eq_Xmat_smul (N : ℕ) (u : ℝ) (ω' : Ω d) :
    Hflow d N u ω' = Xmat d N ((Real.sqrt u : ℝ) • ω') := by
  ext i j
  rw [Hflow_apply, Xmat_apply, Xentry_smul]

private lemma measurable_Xmat (N : ℕ) : Measurable (Xmat d N) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d N i j

private lemma measurable_combined (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    Measurable (fun ω : Ωg d => (Real.sqrt (s N) : ℝ) • ω 0
      + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i) := by
  have h1 : Measurable (fun ω : Ωg d => ω 0) := measurable_pi_apply 0
  have h2 : Measurable (fun ω : Ωg d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (h1.const_smul (Real.sqrt (s N))).add (h2.const_smul (Real.sqrt (step s t K N)))

private lemma measurable_smul_Ω (u : ℝ) : Measurable (fun ω' : Ω d => (Real.sqrt u : ℝ) • ω') :=
  measurable_id.const_smul (Real.sqrt u)

end CombinedIdentities

section TheTransferLemma

variable {d}

/-- **The column law.** At a fixed raw coordinate `c`, the `k+1`-fold grid combination of iid
copies of `gaussianReal 0 (gvar d c)` is Gaussian with the added variance. -/
private lemma map_column_eq (c : Coord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 (gvar d c))).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * gvar d c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * gvar d c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 (gvar d c))) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hYd : ∀ i : ℕ, (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 (gvar d c))).map
      (fun y : ℕ → ℝ => y i) = gaussianReal 0 (gvar d c) := fun i => Measure.infinitePi_map_eval _ i
  exact weightedSum_map_gaussianReal hYm hY hYd a b k

/-- The nested product over `Coord d` first, then over the grid index `ℕ`. -/
private def Pg' (d : Dims) : Measure (Coord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Coord d => Measure.infinitePi (fun _ : ℕ => gaussianReal 0 (gvar d c)))

/-- The composite reindexing map `(Coord d → ℕ → ℝ) → Ωg d`: uncurry, swap the two axes, curry
back. -/
private def swapEquiv (d : Dims) : (Coord d → ℕ → ℝ) → Ωg d :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
    (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm

private lemma measurable_swapEquiv : Measurable (swapEquiv d) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm.measurable)

/-- **The swap identity.** `Pg' d`, the nested product `infinitePi (fun c ↦ infinitePi (fun _ ↦ …))`
over `Coord d` first, coincides after reordering the two axes with `Pg d`. Obtained from
`Measure.infinitePi_map_curry_symm`, `Measure.infinitePi_map_piCongrLeft` (with the axis swap
`Equiv.prodComm`) and `Measure.infinitePi_map_curry`, chained together. -/
private lemma Pg_swap_eq : (Pg' d).map (swapEquiv d) = Pg d := by
  have ha : (Pg' d).map ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Coord d × ℕ => gaussianReal 0 (gvar d p.1)) :=
    Measure.infinitePi_map_curry_symm (μ := fun (c : Coord d) (_ : ℕ) => gaussianReal 0 (gvar d c))
  have hb : (Measure.infinitePi (fun p : Coord d × ℕ => gaussianReal 0 (gvar d p.1))).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Coord d => gaussianReal 0 (gvar d p.2)) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Coord d => gaussianReal 0 (gvar d p.2)) (Equiv.prodComm (Coord d) ℕ)
  have hc : (Measure.infinitePi (fun p : ℕ × Coord d => gaussianReal 0 (gvar d p.2))).map
      (MeasurableEquiv.curry ℕ (Coord d) ℝ) = Pg d :=
    Measure.infinitePi_map_curry (μ := fun (_ : ℕ) (c : Coord d) => gaussianReal 0 (gvar d c))
  show (Pg' d).map ((MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm) = Pg d
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- The pointwise formula for the swap map: entry `i` of the `c`-th row, read after uncurrying
and swapping the two axes, is entry `i` of `X c`. -/
private lemma swapEquiv_apply (X : Coord d → ℕ → ℝ) (i : ℕ) (c : Coord d) :
    swapEquiv d X i c = X c i := by
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

/-- **The combined-grid law.** The `k+1`-fold grid combination has, at each raw coordinate, the
Gaussian law of the sum of the variances contributed by the base draw and by the `k` increments. -/
private lemma map_combined_eq (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    (Pg d).map (fun ω : Ωg d => (Real.sqrt (s N) : ℝ) • ω 0
        + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i)
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0
          (NNReal.mk (Real.sqrt (s N) ^ 2) (sq_nonneg _) * gvar d c
            + k • (NNReal.mk (Real.sqrt (step s t K N) ^ 2) (sq_nonneg _) * gvar d c))) := by
  have hcomp : (fun ω : Ωg d => (Real.sqrt (s N) : ℝ) • ω 0
        + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i) ∘ (swapEquiv d)
      = (fun X : Coord d → ℕ → ℝ => fun c => Real.sqrt (s N) * X c 0
          + Real.sqrt (step s t K N) * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      swapEquiv_apply]
  rw [← Pg_swap_eq, Measure.map_map (measurable_combined s t K N k) measurable_swapEquiv, hcomp]
  have hfmeas : ∀ c : Coord d, Measurable (fun y : ℕ → ℝ => Real.sqrt (s N) * y 0
      + Real.sqrt (step s t K N) * ∑ i ∈ Finset.Icc 1 k, y i) := fun c => by
    have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
    have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Coord d => Measure.infinitePi (fun _ : ℕ => gaussianReal 0 (gvar d c)))
      (f := fun c : Coord d => fun y : ℕ → ℝ => Real.sqrt (s N) * y 0
        + Real.sqrt (step s t K N) * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [Pg']
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => map_column_eq c (Real.sqrt (s N)) (Real.sqrt (step s t K N)) k))

/-- **The scaled-flow law.** The law of `√u • X` at each raw coordinate is Gaussian with variance
`u` times the original variance. -/
private lemma map_smul_eq (N : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (P d).map (fun ω' : Ω d => (Real.sqrt u : ℝ) • ω')
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0 (NNReal.mk u hu * gvar d c)) := by
  have hfmeas : ∀ c : Coord d, Measurable ((Real.sqrt u : ℝ) * ·) := fun c => by fun_prop
  have h1 : (P d).map (fun ω' : Ω d => fun c => (Real.sqrt u : ℝ) * ω' c)
      = Measure.infinitePi (fun c : Coord d => (gaussianReal 0 (gvar d c)).map ((Real.sqrt u : ℝ) * ·)) :=
    Measure.infinitePi_map_pi (μ := fun c : Coord d => gaussianReal 0 (gvar d c))
      (f := fun _ : Coord d => ((Real.sqrt u : ℝ) * ·)) hfmeas
  have heq : (fun ω' : Ω d => (Real.sqrt u : ℝ) • ω') = (fun ω' : Ω d => fun c => (Real.sqrt u : ℝ) * ω' c) := by
    funext ω' c; simp [smul_eq_mul]
  rw [heq, h1]
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  push_cast
  rw [Real.sq_sqrt hu]

/-- **T4 : the transfer lemma.** The grid path `H` at grid step `k` has the same law as the
continuous flow `Hflow` at the matching grid time. -/
theorem map_H_eq (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (hs : 0 ≤ s N) (hst : s N ≤ t N)
    (hK : K N ≠ 0) :
    (Pg d).map (H d s t K N k) = (P d).map (Hflow d N (time s t K N k)) := by
  have hstep : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hu : 0 ≤ time s t K N k := by
    have : 0 ≤ (k : ℝ) * step s t K N := mul_nonneg (Nat.cast_nonneg k) hstep
    unfold time; linarith
  have hHeq : H d s t K N k = fun ω => Xmat d N ((Real.sqrt (s N) : ℝ) • ω 0
      + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i) :=
    funext (H_eq_Xmat_combined s t K N k)
  have hHfloweq : Hflow d N (time s t K N k) = fun ω' => Xmat d N ((Real.sqrt (time s t K N k) : ℝ) • ω') :=
    funext (Hflow_eq_Xmat_smul N (time s t K N k))
  rw [hHeq, hHfloweq,
    show (fun ω : Ωg d => Xmat d N ((Real.sqrt (s N) : ℝ) • ω 0
        + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i))
      = Xmat d N ∘ (fun ω => (Real.sqrt (s N) : ℝ) • ω 0
        + (Real.sqrt (step s t K N) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i) from rfl,
    show (fun ω' : Ω d => Xmat d N ((Real.sqrt (time s t K N k) : ℝ) • ω'))
      = Xmat d N ∘ (fun ω' => (Real.sqrt (time s t K N k) : ℝ) • ω') from rfl,
    ← Measure.map_map (measurable_Xmat N) (measurable_combined s t K N k),
    ← Measure.map_map (measurable_Xmat N) (measurable_smul_Ω (time s t K N k)),
    map_combined_eq s t K N k, map_smul_eq N (time s t K N k) hu]
  congr 1
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  have hvar : NNReal.mk (Real.sqrt (s N) ^ 2) (sq_nonneg _) * gvar d c
      + k • (NNReal.mk (Real.sqrt (step s t K N) ^ 2) (sq_nonneg _) * gvar d c)
      = NNReal.mk (time s t K N k) hu * gvar d c := by
    have h1 : Real.sqrt (s N) ^ 2 = s N := Real.sq_sqrt hs
    have h2 : Real.sqrt (step s t K N) ^ 2 = step s t K N := Real.sq_sqrt hstep
    apply NNReal.coe_injective
    push_cast
    rw [h1, h2]
    unfold time
    ring
  rw [hvar]

end TheTransferLemma

end RBM.Gauss.Grid

end
