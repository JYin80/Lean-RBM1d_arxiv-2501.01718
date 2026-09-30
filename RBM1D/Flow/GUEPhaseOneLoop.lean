/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseGrid
import RBM1D.Gauss.SteinMatrix
import RBM1D.Gauss.IBP
import RBM1D.Gauss.Step6Hyp
import RBM1D.Propagator.Edges

/-!
# Lemma 5.15 for the GUE-phase profile

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.8, Lemma 5.15
((5.126)–(5.128)), for the GUE-phase grid path of §7.2 (`RBM1D/Flow/GUEPhaseGrid.lean`).

At grid step `k` the matrix `gueH k` has the one-time law of `Xmat` under the product Gaussian
`⊗_c N(0, t₁ gvar_c + k (Δ/M) gueUnitVar_c)` (the coordinate description of
`Flow/GUEPhaseGrid.lean`). Its variance profile is `S_u = t₁ S + (u - t₁)/M` (row sums `u`). Stein's
identity for that product measure gives the exact identity (5.127)/(5.128) for the block profile
`Ŝ = t₁ S^{(B)} + ((u - t₁)/L) J`:

  `E⟨(G-m)E_a⟩ = m² (Ŝ E⟨(G-m)E_·⟩)_a + m E[⟨(G-m)E_a⟩ (Ŝ⟨(G-m)E_·⟩)_a]`.

Stability: summing over `a` gives the average through `(1 - u m²)⁻¹`, bounded by
`|1 - u m²| ≥ √κ` for **every** `u ∈ [0,1]` (`RBM.sqrt_le_norm_one_sub_short`),
and the rest is `Θ_{t₁ m²}` (`RBM.sum_norm_Theta_short_edge_le`). This is the Sherman–Morrison
step without forming the inverse. The quadratic term is controlled by the pathwise
input `h1` on its good event and by `‖G‖ ≤ η⁻¹` on the bad event.

Only the one-time law of `gueH k` at a fixed grid step is used; no pathwise identity.
-/

noncomputable section

namespace RBM.Gauss.GUEGrid

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ### 1. Stein's identity for an arbitrary product Gaussian on `Ω d` -/

section Stein

variable {d : Dims}

/-- The product Gaussian with variance family `v`. -/
private def olQ (v : Coord d → ℝ≥0) : Measure (Ω d) :=
  Measure.infinitePi fun c => gaussianReal 0 (v c)

private instance olQ_isProbabilityMeasure (v : Coord d → ℝ≥0) :
    IsProbabilityMeasure (olQ v) := by
  unfold olQ; infer_instance

private lemma olQ_pi (v : Coord d → ℝ≥0) {s : Finset (Coord d)} {t : Coord d → Set ℝ}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    olQ v (Set.pi (↑s) t) = ∏ i ∈ s, (gaussianReal 0 (v i)) (t i) := by
  unfold olQ
  exact Measure.infinitePi_pi _ ht

/-- Resampling one coordinate leaves `olQ v` invariant (`RBM.Gauss.P_map_update` for `v`). -/
private lemma olQ_map_update (v : Coord d → ℝ≥0) (c : Coord d) :
    ((olQ v).prod (gaussianReal 0 (v c))).map (upd d c) = olQ v := by
  classical
  have hUm : Measurable (upd d c) := measurable_upd d c
  conv_rhs => rw [olQ]
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hst : MeasurableSet (Set.pi (↑s) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply hUm hst]
  by_cases hc : c ∈ s
  · have hpre : upd d c ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑(s.erase c)) t) ×ˢ t c := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.coe_erase,
        Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_coe]
      constructor
      · intro h
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [← upd_of_ne c p hi.2]
          exact h i hi.1
        · rw [← upd_self c p]
          exact h c hc
      · rintro ⟨h1, h2⟩ i hi
        by_cases hic : i = c
        · subst hic
          rwa [upd_self]
        · rw [upd_of_ne c p hic]
          exact h1 i ⟨hi, hic⟩
    rw [hpre, Measure.prod_prod, olQ_pi v (fun i _ => ht i), ← Finset.prod_erase_mul s _ hc]
  · have hpre : upd d c ⁻¹' (Set.pi (↑s) t) = (Set.pi (↑s) t) ×ˢ (Set.univ : Set ℝ) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Set.mem_univ, and_true,
        Finset.mem_coe]
      constructor
      · intro h i hi
        rw [← upd_of_ne c p (fun hh => hc (hh ▸ hi))]
        exact h i hi
      · intro h i hi
        rw [upd_of_ne c p (fun hh => hc (hh ▸ hi))]
        exact h i hi
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, olQ_pi v (fun i _ => ht i)]

/-- **Stein's identity for `olQ v`**, one coordinate, bounded `C¹` test functions
(`RBM.Gauss.matrixStein` with `gvar d` replaced by `v`). -/
private lemma olQ_stein (v : Coord d → ℝ≥0) (c : Coord d) {g g' : Ω d → ℂ}
    (hgc : Continuous g) (hg'c : Continuous g')
    (hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c))
    {C₀ : ℝ} (hC : ∀ ω, ‖g ω‖ ≤ C₀) (hC' : ∀ ω, ‖g' ω‖ ≤ C₀) :
    ∫ ω, (ω c : ℂ) * g ω ∂(olQ v) = ((v c : ℝ) : ℂ) * ∫ ω, g' ω ∂(olQ v) := by
  have hgm : Measurable g := hgc.measurable
  have hg'm : Measurable g' := hg'c.measurable
  have hUm : Measurable (upd d c) := measurable_upd d c
  have hfib : ∀ (ω : Ω d) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s)) (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  have hInt : Integrable (fun p : Ω d × ℝ => (p.2 : ℂ) * g (upd d c p))
      ((olQ v).prod (gaussianReal 0 (v c))) := by
    have hbase : Integrable (fun p : Ω d × ℝ => p.2)
        ((olQ v).prod (gaussianReal 0 (v c))) :=
      (RBM.integrable_id_gaussianReal (var := v c)).comp_snd (olQ v)
    refine Integrable.mono' (hbase.abs.const_mul C₀) ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((Complex.measurable_ofReal.comp measurable_snd).mul
        (hgm.comp hUm)).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg p.2)
  have hInt' : Integrable (fun p : Ω d × ℝ => g' (upd d c p))
      ((olQ v).prod (gaussianReal 0 (v c))) := by
    refine Integrable.mono' (integrable_const C₀) ?_
      (Eventually.of_forall fun p => hC' _)
    exact (hg'm.comp hUm).aestronglyMeasurable
  have hL : ∫ ω, (ω c : ℂ) * g ω ∂(olQ v)
      = ∫ p : Ω d × ℝ, (p.2 : ℂ) * g (upd d c p) ∂((olQ v).prod (gaussianReal 0 (v c))) := by
    conv_lhs => rw [← olQ_map_update v c]
    rw [integral_map hUm.aemeasurable (by
      rw [olQ_map_update v c]
      exact ((Complex.measurable_ofReal.comp (measurable_pi_apply c)).mul
        hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(olQ v)
      = ∫ p : Ω d × ℝ, g' (upd d c p) ∂((olQ v).prod (gaussianReal 0 (v c))) := by
    conv_lhs => rw [← olQ_map_update v c]
    rw [integral_map hUm.aemeasurable (by
      rw [olQ_map_update v c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hInt, integral_prod _ hInt', ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  change ∫ t : ℝ, (t : ℂ) * g (Function.update ω c t) ∂(gaussianReal 0 (v c))
      = ((v c : ℝ) : ℂ) * ∫ t : ℝ, g' (Function.update ω c t) ∂(gaussianReal 0 (v c))
  have hcont : Continuous fun t : ℝ => g' (Function.update ω c t) :=
    hg'c.comp (continuous_update_coord c ω)
  exact integral_mul_gaussianReal_complex' (var := v c)
    (f := fun t => g (Function.update ω c t)) (f' := fun t => g' (Function.update ω c t))
    (C := C₀) (hfib ω) hcont (fun t => hC _) (fun t => hC' _)

end Stein

/-! ### 2. The one-time law of grid step `k` (the coordinate description)

The mixed-grid computation below reproduces the private one of `RBM1D/Flow/GUEPhaseGrid.lean`
(renamed `ol*` copies; the originals are not visible outside that file). -/

section OlMixedGrid

variable {d}

private def olMixedStepMeasure (v0 v1 : Coord d → ℝ≥0) : ℕ → Measure (Ω d)
  | 0 => Measure.infinitePi fun c => gaussianReal 0 (v0 c)
  | _ + 1 => Measure.infinitePi fun c => gaussianReal 0 (v1 c)

private def olMixedRawStep (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (i : ℕ) : Measure ℝ :=
  if i = 0 then gaussianReal 0 (v0 c) else gaussianReal 0 (v1 c)

private instance olMixedRawStep_isProb (v0 v1 : Coord d → ℝ≥0) (c : Coord d)
    (i : ℕ) : IsProbabilityMeasure (olMixedRawStep v0 v1 c i) := by
  unfold olMixedRawStep; split_ifs <;> infer_instance

private lemma olMixedStepMeasure_eq (v0 v1 : Coord d → ℝ≥0) (i : ℕ) :
    olMixedStepMeasure v0 v1 i = Measure.infinitePi (fun c => olMixedRawStep v0 v1 c i) := by
  cases i <;> simp [olMixedStepMeasure, olMixedRawStep]

/-- Same nesting as `Gauss/GridPath.lean`'s private `Pg'`: `Coord d` first, then `ℕ`. -/
private def olMixedRaw' (v0 v1 : Coord d → ℝ≥0) : Measure (Coord d → ℕ → ℝ) :=
  Measure.infinitePi (fun c : Coord d => Measure.infinitePi (fun i : ℕ => olMixedRawStep v0 v1 c i))

/-- Same reindexing map as `Gauss/GridPath.lean`'s private `swapEquiv`. -/
private def olMixedSwapEquiv : (Coord d → ℕ → ℝ) → (ℕ → Ω d) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
    (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
    (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm

private lemma ol_measurable_olMixedSwapEquiv : Measurable (olMixedSwapEquiv (d := d)) :=
  (MeasurableEquiv.curry ℕ (Coord d) ℝ).measurable.comp
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ)
      (Equiv.prodComm (Coord d) ℕ)).measurable.comp
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm.measurable)

private lemma olMixedSwapEquiv_apply (X : Coord d → ℕ → ℝ) (i : ℕ) (c : Coord d) :
    olMixedSwapEquiv X i c = X c i := by
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

private lemma olMixedRaw'_swap_eq (v0 v1 : Coord d → ℝ≥0) :
    (olMixedRaw' v0 v1).map olMixedSwapEquiv = Measure.infinitePi (olMixedStepMeasure v0 v1) := by
  have ha : (olMixedRaw' v0 v1).map ((MeasurableEquiv.curry (Coord d) ℕ ℝ).symm)
      = Measure.infinitePi (fun p : Coord d × ℕ => olMixedRawStep v0 v1 p.1 p.2) :=
    Measure.infinitePi_map_curry_symm (μ := fun (c : Coord d) (i : ℕ) => olMixedRawStep v0 v1 c i)
  have hb : (Measure.infinitePi (fun p : Coord d × ℕ => olMixedRawStep v0 v1 p.1 p.2)).map
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ))
      = Measure.infinitePi (fun p : ℕ × Coord d => olMixedRawStep v0 v1 p.2 p.1) :=
    Measure.infinitePi_map_piCongrLeft
      (μ := fun p : ℕ × Coord d => olMixedRawStep v0 v1 p.2 p.1) (Equiv.prodComm (Coord d) ℕ)
  have hc : (Measure.infinitePi (fun p : ℕ × Coord d => olMixedRawStep v0 v1 p.2 p.1)).map
      (MeasurableEquiv.curry ℕ (Coord d) ℝ) = Measure.infinitePi (olMixedStepMeasure v0 v1) := by
    rw [Measure.infinitePi_map_curry (μ := fun (i : ℕ) (c : Coord d) => olMixedRawStep v0 v1 c i)]
    exact congrArg Measure.infinitePi (funext fun i => (olMixedStepMeasure_eq v0 v1 i).symm)
  show (olMixedRaw' v0 v1).map ((MeasurableEquiv.curry ℕ (Coord d) ℝ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : ℕ × Coord d => ℝ) (Equiv.prodComm (Coord d) ℕ)) ∘
      (MeasurableEquiv.curry (Coord d) ℕ ℝ).symm) = Measure.infinitePi (olMixedStepMeasure v0 v1)
  rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
    ha, hb, hc]

/-- **The one-dimensional mixed-variance sum lemma.** Generalizes `Gauss/GridPath.lean`'s private
`sumIcc_map_gaussianReal`: the law is uniform `w` only from index `1` on (index `0` is untouched
by the conclusion, and indeed unused by this induction, exactly as in the original). -/
private lemma olSumIcc_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
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
private lemma olWeightedSum_map_gaussianReal_mixed {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'}
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
  have hlaw0 : HasLaw (fun ω => a * Y 0 ω)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * w0)) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun ω => a * Y 0 ω) = (a * ·) ∘ Y 0 := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hYm 0), hY0, gaussianReal_map_const_mul, mul_zero]
  have hsummeas : Measurable (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hYm i
  have hlawsum : μ'.map (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) = gaussianReal 0 (k • w1) :=
    olSumIcc_map_gaussianReal_mixed hYm hY hY1 k
  have hlaw1 : HasLaw (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
      (gaussianReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b) * (k • w1))) μ' := by
    refine ⟨by fun_prop, ?_⟩
    have heq : (fun ω => b * ∑ i ∈ Finset.Icc 1 k, Y i ω)
        = (b * ·) ∘ (fun ω => ∑ i ∈ Finset.Icc 1 k, Y i ω) := rfl
    rw [heq, ← Measure.map_map (by fun_prop) hsummeas, hlawsum, gaussianReal_map_const_mul,
      mul_zero]
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

private lemma olMap_column_eq_mixed (v0 v1 : Coord d → ℝ≥0) (c : Coord d) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (fun i : ℕ => olMixedRawStep v0 v1 c i)).map
        (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i)
      = gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
          + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c)) := by
  have hY : iIndepFun (fun i : ℕ => (fun y : ℕ → ℝ => y i))
      (Measure.infinitePi (fun i : ℕ => olMixedRawStep v0 v1 c i)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : ℝ → ℝ)) (mX := fun _ => measurable_id)
  have hYm : ∀ i : ℕ, Measurable (fun y : ℕ → ℝ => y i) := fun i => measurable_pi_apply i
  have hY0 : (Measure.infinitePi (fun i : ℕ => olMixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y 0) = gaussianReal 0 (v0 c) := by
    rw [Measure.infinitePi_map_eval]
    simp [olMixedRawStep]
  have hY1 : ∀ i : ℕ, 1 ≤ i → (Measure.infinitePi (fun i : ℕ => olMixedRawStep v0 v1 c i)).map
      (fun y : ℕ → ℝ => y i) = gaussianReal 0 (v1 c) := by
    intro i hi
    rw [Measure.infinitePi_map_eval]
    unfold olMixedRawStep
    exact ite_eq_right_iff.2 fun h => absurd h (by omega)
  exact olWeightedSum_map_gaussianReal_mixed hYm hY hY0 hY1 a b k

/-- **The mixed-grid combined law.** Same conclusion shape as `Gauss/GridPath.lean`'s private
`map_combined_eq`, generalized from a constant step law to the mixed `(v0, v1)` law. -/
private lemma olMap_combined_eq_mixed (v0 v1 : Coord d → ℝ≥0) (a b : ℝ) (k : ℕ) :
    (Measure.infinitePi (olMixedStepMeasure v0 v1)).map (fun ω : ℕ → Ω d =>
        a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i)
      = Measure.infinitePi (fun c : Coord d => gaussianReal 0
          (NNReal.mk (a ^ 2) (sq_nonneg a) * v0 c
            + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * v1 c))) := by
  have hmeasComb : Measurable (fun ω : ℕ → Ω d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) := by
    have h1 : Measurable (fun ω : ℕ → Ω d => ω 0) := measurable_pi_apply 0
    have h2 : Measurable (fun ω : ℕ → Ω d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    exact (h1.const_smul a).add (h2.const_smul b)
  have hcomp : (fun ω : ℕ → Ω d => a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i) ∘ olMixedSwapEquiv
      = (fun X : Coord d → ℕ → ℝ => fun c => a * X c 0 + b * ∑ i ∈ Finset.Icc 1 k, X c i) := by
    funext X
    funext c
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      olMixedSwapEquiv_apply]
  rw [← olMixedRaw'_swap_eq v0 v1, Measure.map_map hmeasComb ol_measurable_olMixedSwapEquiv, hcomp]
  have hfmeas : ∀ c : Coord d,
      Measurable (fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) :=
    fun c => by
      have h1 : Measurable (fun y : ℕ → ℝ => y 0) := measurable_pi_apply 0
      have h2 : Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.Icc 1 k, y i) :=
        Finset.measurable_sum _ fun i _ => measurable_pi_apply i
      exact (h1.const_mul _).add (h2.const_mul _)
  have hpi := Measure.infinitePi_map_pi
      (μ := fun c : Coord d => Measure.infinitePi (fun i : ℕ => olMixedRawStep v0 v1 c i))
      (f := fun c : Coord d => fun y : ℕ → ℝ => a * y 0 + b * ∑ i ∈ Finset.Icc 1 k, y i) hfmeas
  rw [olMixedRaw']
  exact hpi.trans (congrArg Measure.infinitePi
    (funext fun c => olMap_column_eq_mixed v0 v1 c a b k))

end OlMixedGrid

section Law

variable (d)

private lemma olXentry_add (N : ℕ) (ω1 ω2 : Ω d) (i j : d.Idx N) :
    Xentry d N (ω1 + ω2) i j = Xentry d N ω1 i j + Xentry d N ω2 i j := by
  simp only [Xentry, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

private lemma olXentry_smul (N : ℕ) (a : ℝ) (ω : Ω d) (i j : d.Idx N) :
    Xentry d N (a • ω) i j = (a : ℂ) * Xentry d N ω i j := by
  simp only [Xentry, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

private lemma olXentry_zero (N : ℕ) (i j : d.Idx N) : Xentry d N (0 : Ω d) i j = 0 := by
  simp only [Xentry, Pi.zero_apply]
  split_ifs <;> simp

private lemma olXentry_sum {ι : Type*} (N : ℕ) (S : Finset ι) (ω : ι → Ω d) (i j : d.Idx N) :
    Xentry d N (∑ l ∈ S, ω l) i j = ∑ l ∈ S, Xentry d N (ω l) i j := by
  classical
  induction S using Finset.induction with
  | empty => simp [olXentry_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, olXentry_add, ih, Finset.sum_insert ha]

/-- The real-coordinate combination read by grid step `k`. -/
private def olComb (a b : ℝ) (k : ℕ) (ω : Grid.Ωg d) : Ω d :=
  a • ω 0 + b • ∑ i ∈ Finset.Icc 1 k, ω i

private lemma olComb_measurable (a b : ℝ) (k : ℕ) : Measurable (olComb d a b k) := by
  have h1 : Measurable (fun ω : ℕ → Ω d => ω 0) := measurable_pi_apply 0
  have h2 : Measurable (fun ω : ℕ → Ω d => ∑ i ∈ Finset.Icc 1 k, ω i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  exact (h1.const_smul a).add (h2.const_smul b)

/-- The coordinate variances of step `k`. -/
private def olVar (a b : ℝ) (k : ℕ) : Coord d → ℝ≥0 := fun c =>
  NNReal.mk (a ^ 2) (sq_nonneg a) * gvar d c
    + k • (NNReal.mk (b ^ 2) (sq_nonneg b) * gueUnitVar d c)

private lemma ol_Pgue_eq_mixed :
    Pgue d = Measure.infinitePi (olMixedStepMeasure (gvar d) (gueUnitVar d)) := by
  unfold Pgue
  refine congrArg Measure.infinitePi (funext fun k => ?_)
  cases k with
  | zero => rfl
  | succ k => rfl

/-- **The one-time law of step `k`**: the combination has the product Gaussian law `olVar`. -/
private lemma ol_map_comb (a b : ℝ) (k : ℕ) :
    (Pgue d).map (olComb d a b k) = olQ (olVar d a b k) := by
  rw [ol_Pgue_eq_mixed]
  exact olMap_combined_eq_mixed (gvar d) (gueUnitVar d) a b k

/-- `gueH` at step `k` is `Xmat` (i.e. `Hflow` at time `1`) of the combination. -/
private lemma ol_gueH_eq (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d) :
    gueH d t1 t0 K N k ω
      = Hflow d N 1 (olComb d (Real.sqrt (t1 N))
          (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ))) k ω) := by
  ext i j
  simp only [gueH, Hflow_apply, Real.sqrt_one, Complex.ofReal_one, one_mul, olComb,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Xmat_apply, smul_eq_mul]
  rw [olXentry_add, olXentry_smul, olXentry_smul, olXentry_sum]

/-- The step-`k` variance of a used coordinate: `S_u` on the diagonal, `S_u / 2` off it,
`S_u = a² S + k b²`. -/
private lemma olVar_crd (a b : ℝ) (k N : ℕ) (p : d.Idx N × d.Idx N × Bool) :
    (olVar d a b k (crd d N p) : ℝ)
      = if p.1 = p.2.1 then a ^ 2 * Sblk (d.L N) (d.W N) p.1 p.2.1 + k * b ^ 2
        else (a ^ 2 * Sblk (d.L N) (d.W N) p.1 p.2.1 + k * b ^ 2) / 2 := by
  have hg := gvar_crd d N p
  unfold olVar
  simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul]
  rw [hg]
  simp only [gueUnitVar, crd]
  split_ifs <;> push_cast <;> ring

end Law

/-! ### 3. Gaussian integration by parts for the step-`k` law

The display in the proof of Lemma 4.1 / (5.127), `E[(H G)_{xx}] = -∑_y S_u(x,y) E[G_xx G_yy]` for an
arbitrary product Gaussian whose used coordinates carry `S_u` on the diagonal and `S_u / 2` off it
(`RBM.Gauss.integral_Hflow_mul_green_diag` with `gvar`, `Sblk` replaced by `v`, `S_u`). -/

section IBP

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ} {E u : ℝ}

private lemma ol_cont_green (hE : |E| < 2) (hu : u < 1) :
    Continuous fun ω : Ω d => green (Hflow d N 1 ω) (zt E u) :=
  continuous_green_comp (continuous_Hflow d N 1) (Hflow_isHermitian d N 1)
    (zt_im_ne_zero_of_lt_one hE hu)

private lemma ol_norm_green_le (hE : |E| < 2) (hu : u < 1) (ω : Ω d) :
    ‖green (Hflow d N 1 ω) (zt E u)‖ ≤ (etaT E u)⁻¹ :=
  norm_green_zt_le (Hflow_isHermitian d N 1 ω) hE hu

private lemma ol_integrable_of_bdd (v : Coord d → ℝ≥0) {f : Ω d → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (olQ v) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

private lemma ol_integrable_coord_mul (v : Coord d → ℝ≥0) (c : Coord d) {f : Ω d → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable (fun ω : Ω d => (ω c : ℂ) * f ω) (olQ v) := by
  have hmap : (olQ v).map (fun ω : Ω d => ω c) = gaussianReal 0 (v c) := by
    unfold olQ
    exact Measure.infinitePi_map_eval _ c
  have hid : Integrable (fun x : ℝ => x) ((olQ v).map (fun ω : Ω d => ω c)) := by
    rw [hmap]; exact RBM.integrable_id_gaussianReal
  have hc : Integrable (fun ω : Ω d => ω c) (olQ v) :=
    hid.comp_measurable (measurable_pi_apply c)
  refine Integrable.mono' (hc.abs.const_mul C) ?_ (Eventually.of_forall fun ω => ?_)
  · exact ((Complex.continuous_ofReal.comp (continuous_apply c)).mul hf).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)

private lemma ol_norm_mul_green_apply_le (hE : |E| < 2) (hu : u < 1)
    (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a b : d.Idx N) (ω : Ω d) :
    ‖(B * green (Hflow d N 1 ω) (zt E u)) a b‖ ≤ ‖B‖ * (etaT E u)⁻¹ :=
  calc ‖(B * green (Hflow d N 1 ω) (zt E u)) a b‖
        ≤ ‖B * green (Hflow d N 1 ω) (zt E u)‖ := norm_apply_le_l2_opNorm _ a b
    _ ≤ ‖B‖ * ‖green (Hflow d N 1 ω) (zt E u)‖ := norm_mul_le _ _
    _ ≤ ‖B‖ * (etaT E u)⁻¹ := by gcongr; exact ol_norm_green_le hE hu ω

private lemma ol_norm_sandwich0_le (hE : |E| < 2) (hu : u < 1)
    (B : Matrix (d.Idx N) (d.Idx N) ℂ) (a b : d.Idx N) (ω : Ω d) :
    ‖(green (Hflow d N 1 ω) (zt E u) * B * green (Hflow d N 1 ω) (zt E u)) a b‖
      ≤ (etaT E u)⁻¹ * ‖B‖ * (etaT E u)⁻¹ := by
  set G := green (Hflow d N 1 ω) (zt E u)
  have hG := ol_norm_green_le (N := N) hE hu ω
  have hη := (etaT_pos_of_lt_one hE hu).le
  calc ‖(G * B * G) a b‖ ≤ ‖G * B * G‖ := norm_apply_le_l2_opNorm _ a b
    _ ≤ ‖G * B‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ (‖G‖ * ‖B‖) * ‖G‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ (etaT E u)⁻¹ * ‖B‖ * (etaT E u)⁻¹ := by gcongr

private lemma ol_norm_sandwich_le (hE : |E| < 2) (hu : u < 1)
    (B B' : Matrix (d.Idx N) (d.Idx N) ℂ) (a b : d.Idx N) (ω : Ω d) :
    ‖(B' * (green (Hflow d N 1 ω) (zt E u) * B * green (Hflow d N 1 ω) (zt E u))) a b‖
      ≤ ‖B'‖ * ((etaT E u)⁻¹ * ‖B‖ * (etaT E u)⁻¹) := by
  set G := green (Hflow d N 1 ω) (zt E u)
  have hG := ol_norm_green_le (N := N) hE hu ω
  have hη := (etaT_pos_of_lt_one hE hu).le
  calc ‖(B' * (G * B * G)) a b‖ ≤ ‖B' * (G * B * G)‖ := norm_apply_le_l2_opNorm _ a b
    _ ≤ ‖B'‖ * (‖G * B‖ * ‖G‖) := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ ‖B'‖ * ((‖G‖ * ‖B‖) * ‖G‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖B'‖ * ((etaT E u)⁻¹ * ‖B‖ * (etaT E u)⁻¹) := by gcongr

/-- **Stein for one resolvent entry** under `olQ v`. -/
private lemma ol_integral_coord_mul_green (v : Coord d → ℝ≥0) (hE : |E| < 2) (hu : u < 1)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) (l a : d.Idx N) :
    ∫ ω, (ω (crd d N p) : ℂ) * green (Hflow d N 1 ω) (zt E u) l a ∂(olQ v)
      = ((v (crd d N p) : ℝ) : ℂ) * ∫ ω, -((green (Hflow d N 1 ω) (zt E u)
          * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u)) l a) ∂(olQ v) := by
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  have hG := ol_cont_green (d := d) (N := N) hE hu
  refine olQ_stein v (crd d N p) (hG.matrix_elem l a)
    (((hG.matrix_mul continuous_const).matrix_mul hG).matrix_elem l a).neg ?_
    (C₀ := max (etaT E u)⁻¹ ((etaT E u)⁻¹ * ‖B‖ * (etaT E u)⁻¹)) ?_ ?_
  · intro ω
    have h := hasDerivAt_green_apply_update d N 1 (zt_im_ne_zero_of_lt_one hE hu) ω hp l a
    simpa [Real.sqrt_one] using h
  · intro ω
    exact (norm_green_apply_le_etaT hE hu 1 l a ω).trans (le_max_left _ _)
  · intro ω
    rw [norm_neg]
    exact (ol_norm_sandwich0_le (N := N) hE hu B l a ω).trans (le_max_right _ _)

/-- **The coordinate sum collapses to a row of `S_u`** (`RBM.Gauss.sum_gvar_Bmat_sandwich_diag`
with `gvar`, `Sblk` replaced by `v`, `S_u`). -/
private lemma ol_sum_var_Bmat_sandwich_diag (v : Coord d → ℝ≥0)
    (Su : d.Idx N → d.Idx N → ℝ) (hSu : ∀ x y, Su x y = Su y x)
    (hv : ∀ p : d.Idx N × d.Idx N × Bool, (v (crd d N p) : ℝ)
      = if p.1 = p.2.1 then Su p.1 p.2.1 else Su p.1 p.2.1 / 2)
    (G : Matrix (d.Idx N) (d.Idx N) ℂ) (a : d.Idx N) :
    ∑ p ∈ usedCoord d N, (v (crd d N p) : ℝ) •
        (Bmat d N p.1 p.2.1 p.2.2 * (G * Bmat d N p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (Su a k : ℂ) * (G a a * G k k) := by
  classical
  set f : d.Idx N × d.Idx N × Bool → ℂ :=
    fun p => (Bmat d N p.1 p.2.1 p.2.2 * (G * Bmat d N p.1 p.2.1 p.2.2 * G)) a a with hf
  have hgv : ∑ p ∈ usedCoord d N, (v (crd d N p) : ℝ) • f p
      = ∑ p ∈ usedCoord d N,
        (if p.1 = p.2.1 then Su p.1 p.2.1 else Su p.1 p.2.1 / 2) • f p :=
    Finset.sum_congr rfl fun p _ => by rw [hv]
  rw [hgv, show usedCoord d N = Finset.univ.filter
      (fun p : d.Idx N × d.Idx N × Bool =>
        idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
    sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N) Su hSu f
      (fun x y => Bmat_sandwich_diag_swap G x y true a)
      (fun x y => Bmat_sandwich_diag_swap G x y false a)]
  have hterm : ∀ x y : d.Idx N,
      (Su x y : ℝ) •
          (if x = y then f (x, x, true) else (1 / 4 : ℝ) • (f (x, y, true) + f (x, y, false)))
        = (if x = a then (2 : ℂ)⁻¹ * ((Su a y : ℂ) * (G a a * G y y)) else 0)
          + (if y = a then (2 : ℂ)⁻¹ * ((Su x a : ℂ) * (G x x * G a a)) else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [hf, ite_true, Bmat_sandwich_diag_diag G x a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        simp only [ite_true]
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        simp only [ite_eq_right hax, ite_eq_right hxa]
        ring
    · simp only [hf, ite_eq_right hxy, Bmat_sandwich_diag_add_of_ne G hxy a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        have hya : ¬ (y = a) := fun h => hxy h.symm
        simp only [ite_true, ite_eq_right hxy, ite_eq_right hya]
        push_cast
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        by_cases hay : a = y
        · subst hay
          simp only [ite_true, ite_eq_right hax, ite_eq_right hxa]
          push_cast
          ring
        · have hya : ¬ (y = a) := fun h => hay h.symm
          simp only [ite_eq_right hax, ite_eq_right hay, ite_eq_right hxa, ite_eq_right hya]
          push_cast
          ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y : d.Idx N =>
      if x = a then (2 : ℂ)⁻¹ * ((Su a y : ℂ) * (G a a * G y y)) else 0)]
  simp only [Finset.sum_ite_eq' Finset.univ a, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hSu k a]
  ring

/-- **The whole row** under `olQ v`: `E[(H G)_{xx}] = -∑_y S_u(x,y) E[G_xx G_yy]`. -/
private lemma ol_integral_Hflow_mul_green_diag (v : Coord d → ℝ≥0)
    (Su : d.Idx N → d.Idx N → ℝ) (hSu : ∀ x y, Su x y = Su y x)
    (hv : ∀ p : d.Idx N × d.Idx N × Bool, (v (crd d N p) : ℝ)
      = if p.1 = p.2.1 then Su p.1 p.2.1 else Su p.1 p.2.1 / 2)
    (hE : |E| < 2) (hu : u < 1) (x : d.Idx N) :
    ∫ ω, (Hflow d N 1 ω * green (Hflow d N 1 ω) (zt E u)) x x ∂(olQ v)
      = -∑ y, (Su x y : ℂ) * ∫ ω, green (Hflow d N 1 ω) (zt E u) x x
          * green (Hflow d N 1 ω) (zt E u) y y ∂(olQ v) := by
  classical
  have hG := ol_cont_green (d := d) (N := N) hE hu
  set η := etaT E u with hηdef
  have hη : 0 ≤ η⁻¹ := (inv_pos.2 (etaT_pos_of_lt_one hE hu)).le
  -- the coordinate decomposition of `H = Xmat`
  have h1 : ∀ ω : Ω d, (Hflow d N 1 ω * green (Hflow d N 1 ω) (zt E u)) x x
      = ∑ p ∈ usedCoord d N, (ω (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u)) x x := by
    intro ω
    set G := green (Hflow d N 1 ω) (zt E u) with hGdef
    have hH : Hflow d N 1 ω = ∑ p ∈ usedCoord d N, ω (crd d N p) • Bmat d N p.1 p.2.1 p.2.2 := by
      rw [Hflow_eq_realSmul, Real.sqrt_one, one_smul, Xmat_eq_sum]
    rw [hH, Finset.sum_mul]
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul]
  have hintp : ∀ p ∈ usedCoord d N, Integrable (fun ω : Ω d => (ω (crd d N p) : ℂ)
      * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u)) x x) (olQ v) :=
    fun p _ => ol_integrable_coord_mul v (crd d N p)
      ((continuous_const.matrix_mul hG).matrix_elem x x)
      (ol_norm_mul_green_apply_le hE hu _ x x)
  simp only [h1]
  rw [integral_finsetSum _ hintp]
  -- integrate by parts coordinate by coordinate
  have hstep : ∀ p ∈ usedCoord d N,
      ∫ ω, (ω (crd d N p) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u)) x x ∂(olQ v)
        = -(((v (crd d N p) : ℝ) : ℂ)
            * ∫ ω, (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N 1 ω) (zt E u)
              * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u))) x x ∂(olQ v)) := by
    intro p hp
    set B := Bmat d N p.1 p.2.1 p.2.2 with hB
    have hpt1 : ∀ ω : Ω d, (ω (crd d N p) : ℂ) * (B * green (Hflow d N 1 ω) (zt E u)) x x
        = ∑ l, B x l * ((ω (crd d N p) : ℂ) * green (Hflow d N 1 ω) (zt E u) l x) := by
      intro ω
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hpt2 : ∀ ω : Ω d, (B * (green (Hflow d N 1 ω) (zt E u) * B
          * green (Hflow d N 1 ω) (zt E u))) x x
        = ∑ l, B x l * (green (Hflow d N 1 ω) (zt E u) * B
          * green (Hflow d N 1 ω) (zt E u)) l x := by
      intro ω
      rw [Matrix.mul_apply]
    have hi1 : ∀ l, Integrable (fun ω : Ω d => B x l
        * ((ω (crd d N p) : ℂ) * green (Hflow d N 1 ω) (zt E u) l x)) (olQ v) :=
      fun l => (ol_integrable_coord_mul v (crd d N p) (hG.matrix_elem l x)
        (fun ω => norm_green_apply_le_etaT hE hu 1 l x ω)).const_mul _
    have hi2 : ∀ l, Integrable (fun ω : Ω d => B x l
        * (green (Hflow d N 1 ω) (zt E u) * B * green (Hflow d N 1 ω) (zt E u)) l x) (olQ v) :=
      fun l => (ol_integrable_of_bdd v
        (((hG.matrix_mul continuous_const).matrix_mul hG).matrix_elem l x)
        (ol_norm_sandwich0_le hE hu B l x)).const_mul _
    simp only [hpt1, hpt2]
    rw [integral_finsetSum _ fun l _ => hi1 l, integral_finsetSum _ fun l _ => hi2 l,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, integral_const_mul, ol_integral_coord_mul_green v hE hu hp l x,
      integral_neg]
    ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib]
  congr 1
  -- pull the constants in and recombine the coordinate sum
  have hintq : ∀ p ∈ usedCoord d N, Integrable (fun ω : Ω d => ((v (crd d N p) : ℝ) : ℂ)
      * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N 1 ω) (zt E u)
        * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u))) x x) (olQ v) :=
    fun p _ => (ol_integrable_of_bdd v
      ((continuous_const.matrix_mul
        ((hG.matrix_mul continuous_const).matrix_mul hG)).matrix_elem x x)
      (ol_norm_sandwich_le hE hu _ _ x x)).const_mul _
  have hintk : ∀ k ∈ (Finset.univ : Finset (d.Idx N)), Integrable (fun ω : Ω d =>
      (Su x k : ℂ) * (green (Hflow d N 1 ω) (zt E u) x x
        * green (Hflow d N 1 ω) (zt E u) k k)) (olQ v) :=
    fun k _ => (ol_integrable_of_bdd v ((hG.matrix_elem x x).mul (hG.matrix_elem k k))
      (C := η⁻¹ * η⁻¹) (fun ω => by
        simp only [Pi.mul_apply]
        rw [norm_mul]
        exact mul_le_mul (norm_green_apply_le_etaT hE hu 1 x x ω)
          (norm_green_apply_le_etaT hE hu 1 k k ω) (norm_nonneg _) hη)).const_mul _
  have hL : ∑ p ∈ usedCoord d N, ((v (crd d N p) : ℝ) : ℂ)
        * ∫ ω, (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N 1 ω) (zt E u)
          * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u))) x x ∂(olQ v)
      = ∫ ω, ∑ p ∈ usedCoord d N, ((v (crd d N p) : ℝ) : ℂ)
          * (Bmat d N p.1 p.2.1 p.2.2 * (green (Hflow d N 1 ω) (zt E u)
            * Bmat d N p.1 p.2.1 p.2.2 * green (Hflow d N 1 ω) (zt E u))) x x ∂(olQ v) := by
    rw [integral_finsetSum _ hintq]
    exact Finset.sum_congr rfl fun p _ => (integral_const_mul _ _).symm
  have hR : ∑ k, (Su x k : ℂ) * ∫ ω, green (Hflow d N 1 ω) (zt E u) x x
          * green (Hflow d N 1 ω) (zt E u) k k ∂(olQ v)
      = ∫ ω, ∑ k, (Su x k : ℂ) * (green (Hflow d N 1 ω) (zt E u) x x
          * green (Hflow d N 1 ω) (zt E u) k k) ∂(olQ v) := by
    rw [integral_finsetSum _ hintk]
    exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
  rw [hL, hR]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have h := ol_sum_var_Bmat_sandwich_diag v Su hSu hv (green (Hflow d N 1 ω) (zt E u)) x
  simp only [Complex.real_smul] at h
  exact h

end IBP

/-! ### 4. The block identity (5.127)/(5.128) for the step-`k` profile -/

section Block

variable {d : Dims} {N : ℕ} {E u : ℝ}

/-- The block profile `Ŝ(a,b) = t₁ S^{(B)}_{ab} + σ` (`σ = (u - t₁)/L`). -/
private def olSh (L : ℕ) (t1 σ : ℝ) (a b : ZMod L) : ℝ := t1 * sbKre L (b - a) + σ

private lemma olSh_nonneg {L : ℕ} {t1 σ : ℝ} (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ) (a b : ZMod L) :
    0 ≤ olSh L t1 σ a b :=
  add_nonneg (mul_nonneg ht1 (sbKre_nonneg _)) hσ

private lemma sum_olSh {L : ℕ} [NeZero L] (hL : 3 ≤ L) (t1 σ : ℝ) (a : ZMod L) :
    ∑ b, olSh L t1 σ a b = t1 + L * σ := by
  simp only [olSh, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sbKre_sub_right hL a,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-- The `1`-loop as a block average of diagonal Green entries (any matrix). -/
private lemma ol_gloop_eq (H : Matrix (d.Idx N) (d.Idx N) ℂ) (z : ℂ) (b : ZMod (d.L N)) :
    gloop (d.L N) (d.W N) H z (Step6.oneLoop b)
      = ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * green H z k k := by
  rw [gloop_oneLoop_eq_trace, trace_mul_Eblk_eq_sum]

private lemma ol_norm_gloop_le (hE : |E| < 2) (hu : u < 1) (ω : Ω d) (b : ZMod (d.L N)) :
    ‖gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop b)‖ ≤ (etaT E u)⁻¹ := by
  rw [ol_gloop_eq]
  calc ‖∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * green (Hflow d N 1 ω) (zt E u) k k‖
      ≤ ∑ k, ‖(blkCoef (d.L N) (d.W N) b k : ℂ) * green (Hflow d N 1 ω) (zt E u) k k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k, |blkCoef (d.L N) (d.W N) b k| * (etaT E u)⁻¹ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_green_apply_le_etaT hE hu 1 k k ω) (abs_nonneg _)
    _ = (etaT E u)⁻¹ := by rw [← Finset.sum_mul, sum_abs_blkCoef, one_mul]

private lemma ol_cont_gloop (hE : |E| < 2) (hu : u < 1) (b : ZMod (d.L N)) :
    Continuous fun ω : Ω d =>
      gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop b) := by
  have hG := ol_cont_green (d := d) (N := N) hE hu
  simp only [ol_gloop_eq]
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (hG.matrix_elem k k)

/-- `∑_k S_u(p,k) F_k` with `S_u = t₁ S + c₀` is a block-profile sum of block averages. -/
private lemma ol_sum_Su_eq (t1 c0 : ℝ) (p : d.Idx N) (F : d.Idx N → ℂ) :
    ∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ) * F k
      = ∑ b, (olSh (d.L N) t1 (c0 * d.W N) p.1 b : ℂ)
          * ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * F k := by
  classical
  have hW : (d.W N : ℂ) ≠ 0 := by exact_mod_cast (d.W_pos N).ne'
  have h1 := sum_Sblk_eq_sum_SB_blkCoef (L := d.L N) (W := d.W N) p F
  have hcol : ∀ k : d.Idx N, ∑ b, (blkCoef (d.L N) (d.W N) b k : ℂ) = (d.W N : ℂ)⁻¹ := by
    intro k
    rw [Finset.sum_eq_single k.1 (fun b _ hb => by simp [blkCoef, Ne.symm hb])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp [blkCoef]
  have h2 : ∑ b, ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * F k = (d.W N : ℂ)⁻¹ * ∑ k, F k := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, hcol]
  calc ∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ) * F k
      = (t1 : ℂ) * ∑ k, (Sblk (d.L N) (d.W N) p k : ℂ) * F k + (c0 : ℂ) * ∑ k, F k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast; ring
    _ = (t1 : ℂ) * ∑ b, SB (d.L N) b p.1 * ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * F k
          + (c0 * d.W N : ℂ) * ∑ b, ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * F k := by
        rw [h1, h2]
        field_simp
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [SB_eq_ofReal, olSh]
        push_cast
        ring

/-- **(5.127)/(5.128) for the step-`k` law.** With `v_b = ⟨(G - m)E_b⟩` and the block profile
`Ŝ = olSh t₁ (c₀ W)`:
`E v_a = m² ∑_b Ŝ_{ab} E v_b + m E[v_a ∑_b Ŝ_{ab} v_b]`. -/
private lemma ol_selfConsistent (v : Coord d → ℝ≥0) (t1 c0 : ℝ)
    (hv : ∀ p : d.Idx N × d.Idx N × Bool, (v (crd d N p) : ℝ)
      = if p.1 = p.2.1 then t1 * Sblk (d.L N) (d.W N) p.1 p.2.1 + c0
        else (t1 * Sblk (d.L N) (d.W N) p.1 p.2.1 + c0) / 2)
    (hsum : t1 + (d.L N : ℝ) * (c0 * d.W N) = u) (hE : |E| < 2) (hu : u < 1)
    (a : ZMod (d.L N)) :
    ∫ ω, (gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop a) - mE E) ∂(olQ v)
      = mE E ^ 2 * ∑ b, (olSh (d.L N) t1 (c0 * d.W N) a b : ℂ)
          * ∫ ω, (gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop b) - mE E)
              ∂(olQ v)
        + mE E * ∫ ω, (gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop a) - mE E)
            * ∑ b, (olSh (d.L N) t1 (c0 * d.W N) a b : ℂ)
              * (gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop b) - mE E)
            ∂(olQ v) := by
  classical
  set m := mE E with hm
  set σ := c0 * (d.W N : ℝ) with hσ
  set Sh := olSh (d.L N) t1 σ with hSh
  set g : Ω d → ZMod (d.L N) → ℂ := fun ω b =>
    gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt E u) (Step6.oneLoop b) with hg
  set G : Ω d → Matrix (d.Idx N) (d.Idx N) ℂ := fun ω => green (Hflow d N 1 ω) (zt E u) with hGd
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu
  have hGc := ol_cont_green (d := d) (N := N) hE hu
  set η := etaT E u with hηdef
  have hη : 0 ≤ η⁻¹ := (inv_pos.2 (etaT_pos_of_lt_one hE hu)).le
  have hgc : ∀ b, Continuous fun ω => g ω b := fun b => ol_cont_gloop hE hu b
  have hgb : ∀ b ω, ‖g ω b‖ ≤ η⁻¹ := fun b ω => ol_norm_gloop_le hE hu ω b
  have hgi : ∀ b, Integrable (fun ω => g ω b) (olQ v) :=
    fun b => ol_integrable_of_bdd v (hgc b) (hgb b)
  have hShsum : ∑ b, Sh a b = u := by rw [hSh, sum_olSh (d.three_le_L N), hsum]
  -- `H G = 1 + z G`, so `(H G)_{pp}` is bounded
  have hHG : ∀ ω (p : d.Idx N), (Hflow d N 1 ω * G ω) p p = 1 + zt E u * G ω p p := by
    intro ω p
    have h := sub_mul_green_of_im (Hflow_isHermitian d N 1 ω) hz
    have h2 : Hflow d N 1 ω * G ω = 1 + zt E u • G ω := by
      rw [sub_mul, Matrix.smul_mul, Matrix.one_mul] at h
      rw [← h]; simp [hGd]
    rw [h2]
    simp
  have hHGi : ∀ p : d.Idx N, Integrable (fun ω => (blkCoef (d.L N) (d.W N) a p : ℂ)
      * (Hflow d N 1 ω * G ω) p p) (olQ v) := by
    intro p
    refine (ol_integrable_of_bdd v (C := 1 + ‖zt E u‖ * η⁻¹)
      (((continuous_Hflow d N 1).matrix_mul hGc).matrix_elem p p) (fun ω => ?_)).const_mul _
    rw [hHG ω p]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul]
    gcongr
    exact norm_green_apply_le_etaT hE hu 1 p p ω
  -- the pointwise self-consistent equation
  have hpt : ∀ ω, g ω a - m
      = -(m * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ) * (Hflow d N 1 ω * G ω) p p)
        - (u : ℂ) * m ^ 2 * g ω a := by
    intro ω
    have h := trace_green_mul_Eblk_sub_mE (Hflow_isHermitian d N 1 ω) hE.le hz a
    rwa [← gloop_oneLoop_eq_trace, trace_mul_Eblk_eq_sum] at h
  -- the integration by parts display, block-collapsed
  have hSu : ∀ x y : d.Idx N, t1 * Sblk (d.L N) (d.W N) x y + c0
      = t1 * Sblk (d.L N) (d.W N) y x + c0 := fun x y => by rw [Sblk_comm]
  have hrow : ∀ p : d.Idx N, ∫ ω, (Hflow d N 1 ω * G ω) p p ∂(olQ v)
      = -∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ)
          * ∫ ω, G ω p p * G ω k k ∂(olQ v) :=
    fun p => ol_integral_Hflow_mul_green_diag v
      (fun x y => t1 * Sblk (d.L N) (d.W N) x y + c0) hSu hv hE hu p
  have hGGi : ∀ p k : d.Idx N, Integrable (fun ω => G ω p p * G ω k k) (olQ v) := by
    intro p k
    refine ol_integrable_of_bdd v ((hGc.matrix_elem p p).mul (hGc.matrix_elem k k))
      (C := η⁻¹ * η⁻¹) (fun ω => ?_)
    rw [norm_mul]
    exact mul_le_mul (norm_green_apply_le_etaT hE hu 1 p p ω)
      (norm_green_apply_le_etaT hE hu 1 k k ω) (norm_nonneg _) hη
  have hquad : ∀ ω, ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
        * ∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ) * (G ω p p * G ω k k)
      = g ω a * ∑ b, (Sh a b : ℂ) * g ω b := by
    intro ω
    have hgb' : ∀ b, g ω b = ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ) * G ω k k :=
      fun b => ol_gloop_eq _ _ b
    have hp : ∀ p : d.Idx N, (blkCoef (d.L N) (d.W N) a p : ℂ)
        * ∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ) * (G ω p p * G ω k k)
        = (blkCoef (d.L N) (d.W N) a p : ℂ) * G ω p p * ∑ b, (Sh a b : ℂ) * g ω b := by
      intro p
      have hs : ∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ) * (G ω p p * G ω k k)
          = G ω p p * ∑ k, ((t1 * Sblk (d.L N) (d.W N) p k + c0 : ℝ) : ℂ) * G ω k k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hs, ol_sum_Su_eq t1 c0 p (fun k => G ω k k)]
      by_cases hpa : p.1 = a
      · rw [hpa]
        simp only [hgb', hSh, hσ]
        ring
      · simp [blkCoef, hpa]
    rw [Finset.sum_congr rfl fun p _ => hp p, ← Finset.sum_mul, hgb' a]
  have hIBP : ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ) * ∫ ω, (Hflow d N 1 ω * G ω) p p ∂(olQ v)
      = -∫ ω, g ω a * ∑ b, (Sh a b : ℂ) * g ω b ∂(olQ v) := by
    simp only [hrow]
    rw [← integral_congr_ae (Eventually.of_forall hquad)]
    rw [integral_finsetSum _ fun p _ => (integrable_finsetSum _ fun k _ =>
      (hGGi p k).const_mul _).const_mul _]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun k _ => (hGGi p k).const_mul _]
    simp only [integral_const_mul]
    ring
  -- integrate the pointwise equation
  have hmain : ∫ ω, (g ω a - m) ∂(olQ v)
      = ∫ ω, (m * (g ω a * ∑ b, (Sh a b : ℂ) * g ω b) - (u : ℂ) * m ^ 2 * g ω a) ∂(olQ v) := by
    have hA : Integrable (fun ω => -(m * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
        * (Hflow d N 1 ω * G ω) p p)) (olQ v) :=
      ((integrable_finsetSum _ fun p _ => hHGi p).const_mul m).neg
    have hB : Integrable (fun ω => (u : ℂ) * m ^ 2 * g ω a) (olQ v) := (hgi a).const_mul _
    have hQi : Integrable (fun ω => g ω a * ∑ b, (Sh a b : ℂ) * g ω b) (olQ v) := by
      refine ol_integrable_of_bdd v ((hgc a).mul (continuous_finsetSum _ fun b _ =>
        continuous_const.mul (hgc b))) (C := η⁻¹ * ∑ b, ‖(Sh a b : ℂ)‖ * η⁻¹) (fun ω => ?_)
      rw [norm_mul]
      refine mul_le_mul (hgb a ω) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
        (norm_nonneg _) hη
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hgb b ω) (norm_nonneg _)
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_sub hA hB, integral_neg,
      integral_const_mul, integral_finsetSum _ fun p _ => hHGi p,
      integral_sub (hQi.const_mul m) hB, integral_const_mul]
    simp only [integral_const_mul] at hIBP ⊢
    rw [hIBP]
    ring
  -- pointwise algebra: `m g_a (Ŝg)_a - u m² g_a = m² (Ŝv)_a + m v_a (Ŝv)_a`
  have halg : ∀ ω, m * (g ω a * ∑ b, (Sh a b : ℂ) * g ω b) - (u : ℂ) * m ^ 2 * g ω a
      = m ^ 2 * ∑ b, (Sh a b : ℂ) * (g ω b - m)
        + m * ((g ω a - m) * ∑ b, (Sh a b : ℂ) * (g ω b - m)) := by
    intro ω
    have hsplit : ∑ b, (Sh a b : ℂ) * g ω b
        = ∑ b, (Sh a b : ℂ) * (g ω b - m) + (u : ℂ) * m := by
      have : ∑ b, (Sh a b : ℂ) * m = (u : ℂ) * m := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, hShsum]
      rw [← this, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [hsplit]
    ring
  have hvi : ∀ b, Integrable (fun ω => g ω b - m) (olQ v) :=
    fun b => (hgi b).sub (integrable_const _)
  have hRi : Integrable (fun ω => (g ω a - m) * ∑ b, (Sh a b : ℂ) * (g ω b - m)) (olQ v) := by
    refine ol_integrable_of_bdd v (((hgc a).sub continuous_const).mul
      (continuous_finsetSum _ fun b _ => continuous_const.mul ((hgc b).sub continuous_const)))
      (C := (η⁻¹ + ‖m‖) * ∑ b, ‖(Sh a b : ℂ)‖ * (η⁻¹ + ‖m‖)) (fun ω => ?_)
    have hvb : ∀ b, ‖g ω b - m‖ ≤ η⁻¹ + ‖m‖ :=
      fun b => (norm_sub_le _ _).trans (by gcongr; exact hgb b ω)
    rw [norm_mul]
    refine mul_le_mul (hvb a) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
      (norm_nonneg _) (by positivity)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hvb b) (norm_nonneg _)
  rw [hmain, integral_congr_ae (Eventually.of_forall halg),
    integral_add ((integrable_finsetSum _ fun b _ => (hvi b).const_mul _).const_mul _)
      (hRi.const_mul m),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun b _ => (hvi b).const_mul _]
  simp only [integral_const_mul]
  rfl

end Block

/-! ### 5. Stability of `1 - m² Ŝ` in `max → max`

`Ŝ = t₁ S^{(B)} + σ J`. The average is recovered through `1 - u m²`, `u = t₁ + L σ`, and
`|1 - u m²| ≥ √κ` for every `u ∈ [0, 1]`; the rest is `Θ_{t₁ m²}`. -/

section Stability

/-- The stability constant: `K_Θ(κ) (1 + 1/√κ)`. -/
private def olC (κ : ℝ) : ℝ := (2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ) * (1 + 1 / Real.sqrt κ)

private lemma olC_nonneg {κ : ℝ} : 0 ≤ olC κ := by
  have h1 := cTwo52_pos
  have h2 := cZero_pos
  unfold olC
  positivity

private lemma ol_stable {L : ℕ} [NeZero L] (hL : 3 ≤ L) {E κ t1 σ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht1 : 0 ≤ t1) (ht1' : t1 < 1) (hσ : 0 ≤ σ)
    (hu : t1 + L * σ ≤ 1) (x y : ZMod L → ℂ)
    (hxy : ∀ a, x a = mE E ^ 2 * ∑ b, (olSh L t1 σ a b : ℂ) * x b + y a)
    {B : ℝ} (hB : ∀ a, ‖y a‖ ≤ B) (a : ZMod L) :
    ‖x a‖ ≤ olC κ * B := by
  classical
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  set m := mE E with hm
  have hm1 : ‖m‖ = 1 := norm_mE hE2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ0
  set u := t1 + L * σ with hudef
  have hu0 : 0 ≤ u := by positivity
  set S := ∑ b, x b with hS
  -- the average: `(1 - u m²) ∑ x = ∑ y`
  have hcol : ∀ b : ZMod L, ∑ a, olSh L t1 σ a b = u := by
    intro b
    simp only [olSh, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [show ∑ a : ZMod L, sbKre L (b - a) = 1 from sum_sbKre_sub_left hL b]
    ring
  have hsum : (1 - (u : ℂ) * m ^ 2) * S = ∑ a, y a := by
    have h1 : S = m ^ 2 * ∑ b, (u : ℂ) * x b + ∑ a, y a := by
      rw [hS]
      conv_lhs => rw [Finset.sum_congr rfl fun a _ => hxy a]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
      congr 2
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, hcol b]
    rw [← Finset.mul_sum] at h1
    linear_combination h1
  have hden : Real.sqrt κ ≤ ‖1 - (u : ℂ) * m ^ 2‖ :=
    sqrt_le_norm_one_sub_short hκ0 hκ1 hE hu0 hu
  have hY : ‖∑ a, y a‖ ≤ L * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖y a‖ ≤ ∑ _a : ZMod L, B := Finset.sum_le_sum fun a _ => hB a
      _ = L * B := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hSle : ‖S‖ ≤ L * B / Real.sqrt κ := by
    rw [le_div_iff₀ hsk]
    calc ‖S‖ * Real.sqrt κ ≤ ‖S‖ * ‖1 - (u : ℂ) * m ^ 2‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ = ‖∑ a, y a‖ := by rw [← hsum, norm_mul, mul_comm]
      _ ≤ L * B := hY
  -- the remainder `r = y + m² σ ∑ x`
  set r : ZMod L → ℂ := fun a => y a + m ^ 2 * (σ : ℂ) * S with hr
  have hLσ : (L : ℝ) * σ ≤ 1 := by linarith
  have hrle : ∀ a, ‖r a‖ ≤ (1 + 1 / Real.sqrt κ) * B := by
    intro a
    calc ‖r a‖ ≤ ‖y a‖ + ‖m ^ 2 * (σ : ℂ) * S‖ := norm_add_le _ _
      _ ≤ B + σ * (L * B / Real.sqrt κ) := by
          gcongr
          · exact hB a
          · rw [norm_mul, norm_mul, norm_pow, hm1, one_pow, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hσ]
            exact mul_le_mul_of_nonneg_left hSle hσ
      _ = B + (L * σ) * B / Real.sqrt κ := by ring
      _ ≤ B + 1 * B / Real.sqrt κ := by gcongr
      _ = (1 + 1 / Real.sqrt κ) * B := by ring
  -- `(1 - t₁ m² S^{(B)}) x = r`
  set ξ : ℂ := (t1 : ℂ) * m ^ 2 with hξ
  have hξ1 : ‖ξ‖ < 1 := by rw [hξ, norm_short_edge hE2 ht1]; exact ht1'
  have hmv : (1 - ξ • SB L) *ᵥ x = r := by
    funext a
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    have h1 : (SB L *ᵥ x) a = ∑ b, SB L a b * x b := rfl
    rw [h1, hxy a, hr]
    simp only
    have h2 : ∑ b, (olSh L t1 σ a b : ℂ) * x b
        = (t1 : ℂ) * ∑ b, SB L a b * x b + (σ : ℂ) * S := by
      rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [SB_eq_ofReal, olSh, ← sbKre_neg, neg_sub]
      push_cast
      ring
    rw [h2, hξ]
    ring
  have hxeq : x = Theta L ξ *ᵥ r := by
    rw [← hmv, Matrix.mulVec_mulVec, Theta_mul L hL hξ1, Matrix.one_mulVec]
  have hΘ := sum_norm_Theta_short_edge_le L hL hκ0 hκ1 hE ht1 ht1' a
  rw [hxeq]
  calc ‖(Theta L ξ *ᵥ r) a‖ = ‖∑ c, Theta L ξ a c * r c‖ := rfl
    _ ≤ ∑ c, ‖Theta L ξ a c * r c‖ := norm_sum_le _ _
    _ ≤ ∑ c, ‖Theta L ξ a c‖ * ((1 + 1 / Real.sqrt κ) * B) := Finset.sum_le_sum fun c _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hrle c) (norm_nonneg _)
    _ = (∑ c, ‖Theta L ξ a c‖) * ((1 + 1 / Real.sqrt κ) * B) := by rw [Finset.sum_mul]
    _ ≤ (2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ) * ((1 + 1 / Real.sqrt κ) * B) := by
        gcongr
    _ = olC κ * B := by unfold olC; ring

end Stability

/-! ### 6. From the pathwise input to the expectation bound -/

section Main

variable (d : Dims)

private lemma ol_integral_comb (a b : ℝ) (k : ℕ) {Φ : Ω d → ℂ} (hΦ : Continuous Φ) :
    ∫ ω, Φ (olComb d a b k ω) ∂(Pgue d) = ∫ ω, Φ ω ∂(olQ (olVar d a b k)) := by
  rw [← ol_map_comb d a b k,
    integral_map (olComb_measurable d a b k).aemeasurable hΦ.aestronglyMeasurable]

/-- **The bound at one grid time**, for an abstract exceptional set of probability `≤ N^{-3}`
off which every `1`-loop of step `k` is `≤ ρ Λ`: `|E⟨(G-m)E_a⟩| ≤ C_κ (ρ² + 4) Λ²`. -/
private lemma ol_expect_bound {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (N : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : |E N| ≤ 2 - κ) (ht1 : 0 ≤ t1 N) (ht10 : t1 N ≤ t0 N)
    (ht0 : t0 N < 1) (K : ℕ → ℕ) (hK : K N ≠ 0) (k : ℕ) (hkK' : k ≤ K N)
    (hdim : d.W N * d.L N ≤ N) (hN1 : 1 ≤ N)
    {ρ : ℝ} (Bset : Set (Grid.Ωg d))
    (hPB : Pgue d Bset ≤ ENNReal.ofReal ((N : ℝ) ^ (-(3 : ℝ))))
    (hgood : ∀ ω ∉ Bset, ∀ b : ZMod (d.L N),
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω)
          (zt (E N) (Grid.time t1 t0 K N k)) ⟨[true], [b]⟩ - mE (E N)‖
        ≤ ρ * (gueScale d E N (Grid.time t1 t0 K N k))⁻¹)
    (a : ZMod (d.L N)) :
    ‖(∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω)
          (zt (E N) (Grid.time t1 t0 K N k)) ⟨[true], [a]⟩ ∂(Pgue d)) - mE (E N)‖
      ≤ olC κ * (ρ ^ 2 + 4) * (gueScale d E N (Grid.time t1 t0 K N k))⁻¹ ^ 2 := by
  classical
  set u := Grid.time t1 t0 K N k with hudef
  set Δ := Grid.step t1 t0 K N with hΔdef
  set M : ℝ := (ouMatrixSize d N : ℝ) with hMdef
  have hLpos : (0 : ℝ) < d.L N := by
    have := d.three_le_L N; exact_mod_cast (show 0 < d.L N by omega)
  have hWpos : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hMeq : M = (d.L N : ℝ) * d.W N := by
    rw [hMdef]; unfold ouMatrixSize; push_cast; ring
  have hMpos : 0 < M := by rw [hMeq]; positivity
  have hKpos : (0 : ℝ) < K N := by
    exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hKpos.le
  have hkK : (k : ℝ) ≤ K N := by exact_mod_cast hkK'
  have hkΔ : (k : ℝ) * Δ ≤ t0 N - t1 N := by
    calc (k : ℝ) * Δ ≤ K N * Δ := mul_le_mul_of_nonneg_right hkK hΔ0
      _ = t0 N - t1 N := by rw [hΔdef, Grid.step]; field_simp
  have hu_eq : u = t1 N + (k : ℝ) * Δ := rfl
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
  have hu0 : 0 ≤ u := by rw [hu_eq]; linarith
  have hu1 : u < 1 := by rw [hu_eq]; linarith
  have hE2 : |E N| < 2 := by linarith
  set m := mE (E N) with hm
  have hm1 : ‖m‖ = 1 := norm_mE hE2.le
  set η := etaT (E N) u with hηdef
  have hηpos : 0 < η := etaT_pos_of_lt_one hE2 hu1
  have hη1 : η ≤ 1 := by
    rw [hηdef, etaT]
    have him := mE_im_pos hE2
    have hle : (mE (E N)).im ≤ 1 :=
      le_of_abs_le ((Complex.abs_im_le_norm _).trans (norm_mE hE2.le).le)
    nlinarith
  set Λ := (gueScale d E N u)⁻¹ with hΛdef
  have hscale : gueScale d E N u = M * η := by
    rw [gueScale, hMdef, hηdef]; unfold ouMatrixSize; push_cast; ring
  have hΛ : Λ = (M * η)⁻¹ := by rw [hΛdef, hscale]
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hηinv : η⁻¹ = M * Λ := by rw [hΛ]; field_simp
  -- the one-time law of step `k`
  set aa := Real.sqrt (t1 N) with haa
  set bb := Real.sqrt (Δ / M) with hbb
  set c0 : ℝ := (k : ℝ) * bb ^ 2 with hc0
  have haa2 : aa ^ 2 = t1 N := Real.sq_sqrt ht1
  have hbb2 : bb ^ 2 = Δ / M := Real.sq_sqrt (div_nonneg hΔ0 hMpos.le)
  have hc00 : 0 ≤ c0 := by rw [hc0]; positivity
  set Q := olQ (olVar d aa bb k) with hQ
  have hv : ∀ p : d.Idx N × d.Idx N × Bool, (olVar d aa bb k (crd d N p) : ℝ)
      = if p.1 = p.2.1 then t1 N * Sblk (d.L N) (d.W N) p.1 p.2.1 + c0
        else (t1 N * Sblk (d.L N) (d.W N) p.1 p.2.1 + c0) / 2 := by
    intro p
    rw [olVar_crd, haa2, hc0]
  set σ : ℝ := c0 * d.W N with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hsum : t1 N + (d.L N : ℝ) * σ = u := by
    rw [hσ, hc0, hbb2, hu_eq, hMeq]
    field_simp
  -- the functions on `Ω d`
  set Φ : ZMod (d.L N) → Ω d → ℂ := fun b ω =>
    gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt (E N) u) (Step6.oneLoop b) - m with hΦ
  have hΦc : ∀ b, Continuous (Φ b) := fun b => (ol_cont_gloop hE2 hu1 b).sub continuous_const
  have hΦb : ∀ b ω, ‖Φ b ω‖ ≤ 2 * η⁻¹ := by
    intro b ω
    have h1 : 1 ≤ η⁻¹ := by rw [le_inv_comm₀ one_pos hηpos, inv_one]; exact hη1
    calc ‖Φ b ω‖ ≤ ‖gloop (d.L N) (d.W N) (Hflow d N 1 ω) (zt (E N) u) (Step6.oneLoop b)‖
          + ‖m‖ := norm_sub_le _ _
      _ ≤ η⁻¹ + η⁻¹ := by rw [hm1]; exact add_le_add (ol_norm_gloop_le hE2 hu1 ω b) h1
      _ = 2 * η⁻¹ := by ring
  set Sh := olSh (d.L N) (t1 N) σ with hSh
  have hSh0 : ∀ a b, 0 ≤ Sh a b := fun a b => olSh_nonneg ht1 hσ0 a b
  have hShsum : ∀ a, ∑ b, Sh a b = u := fun a => by
    rw [hSh, sum_olSh (d.three_le_L N), hsum]
  set R : ZMod (d.L N) → Ω d → ℂ := fun a ω => Φ a ω * ∑ b, (Sh a b : ℂ) * Φ b ω with hR
  have hRc : ∀ a, Continuous (R a) := fun a =>
    (hΦc a).mul (continuous_finsetSum _ fun b _ => continuous_const.mul (hΦc b))
  -- the step-`k` loops are `Φ ∘ olComb`
  have hcomb : ∀ ω b, gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) u) ⟨[true], [b]⟩
      - m = Φ b (olComb d aa bb k ω) := by
    intro ω b
    rw [ol_gueH_eq]
    rfl
  -- the self-consistent equation for `x_b = E Φ_b`
  set x : ZMod (d.L N) → ℂ := fun b => ∫ ω, Φ b ω ∂Q with hx
  set y : ZMod (d.L N) → ℂ := fun a => m * ∫ ω, R a ω ∂Q with hy
  have hxy : ∀ a, x a = m ^ 2 * ∑ b, (Sh a b : ℂ) * x b + y a := by
    intro a
    exact ol_selfConsistent (olVar d aa bb k) (t1 N) c0 hv hsum hE2 hu1 a
  -- the bound on `y`, from the pathwise input
  set T := toMeasurable (Pgue d) Bset with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hPT : (Pgue d).real T ≤ (N : ℝ) ^ (-(3 : ℝ)) := by
    rw [measureReal_def, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg N) _) hPB
  have hRpt : ∀ a ω, ‖R a (olComb d aa bb k ω)‖
      ≤ (ρ * Λ) ^ 2 + T.indicator (fun _ => (2 * η⁻¹) ^ 2) ω := by
    intro a ω
    set ω' := olComb d aa bb k ω
    have hSv : ∀ B : ℝ, (∀ b, ‖Φ b ω'‖ ≤ B) → ‖R a ω'‖ ≤ B * B := by
      intro B hB
      have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB a)
      rw [hR, norm_mul]
      refine mul_le_mul (hB a) ?_ (norm_nonneg _) hB0
      calc ‖∑ b, (Sh a b : ℂ) * Φ b ω'‖ ≤ ∑ b, ‖(Sh a b : ℂ) * Φ b ω'‖ := norm_sum_le _ _
        _ ≤ ∑ b, Sh a b * B := Finset.sum_le_sum fun b _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSh0 a b)]
            exact mul_le_mul_of_nonneg_left (hB b) (hSh0 a b)
        _ = u * B := by rw [← Finset.sum_mul, hShsum a]
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right hu1.le hB0
        _ = B := one_mul B
    by_cases hω : ω ∈ Bset
    · have hωT : ω ∈ T := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hωT]
      have h := hSv (2 * η⁻¹) (fun b => hΦb b ω')
      exact le_add_of_nonneg_of_le (sq_nonneg _) (h.trans_eq (sq _).symm)
    · have hg : ∀ b, ‖Φ b ω'‖ ≤ ρ * Λ := by
        intro b
        have h := hgood ω hω b
        rw [hcomb ω b] at h
        exact h
      have h1 := hSv (ρ * Λ) hg
      have h2 : 0 ≤ T.indicator (fun _ => (2 * η⁻¹) ^ 2) ω :=
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω
      exact le_add_of_le_of_nonneg (h1.trans_eq (sq _).symm) h2
  have hyle : ∀ a, ‖y a‖ ≤ (ρ ^ 2 + 4) * Λ ^ 2 := by
    intro a
    have hint1 : Integrable (fun ω => ‖R a (olComb d aa bb k ω)‖) (Pgue d) := by
      refine Integrable.of_bound (C := (2 * η⁻¹) * (2 * η⁻¹))
        ((((hRc a).measurable.comp (olComb_measurable d aa bb k)).norm).aestronglyMeasurable)
        (Eventually.of_forall fun ω => ?_)
      rw [norm_norm, hR, norm_mul]
      refine mul_le_mul (hΦb a _) ?_ (norm_nonneg _) (by positivity)
      calc ‖∑ b, (Sh a b : ℂ) * Φ b (olComb d aa bb k ω)‖
          ≤ ∑ b, ‖(Sh a b : ℂ) * Φ b (olComb d aa bb k ω)‖ := norm_sum_le _ _
        _ ≤ ∑ b, Sh a b * (2 * η⁻¹) := Finset.sum_le_sum fun b _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSh0 a b)]
            exact mul_le_mul_of_nonneg_left (hΦb b _) (hSh0 a b)
        _ = u * (2 * η⁻¹) := by rw [← Finset.sum_mul, hShsum a]
        _ ≤ 1 * (2 * η⁻¹) := mul_le_mul_of_nonneg_right hu1.le (by positivity)
        _ = 2 * η⁻¹ := one_mul _
    have hint2 : Integrable (fun ω => (ρ * Λ) ^ 2 + T.indicator (fun _ => (2 * η⁻¹) ^ 2) ω)
        (Pgue d) := (integrable_const _).add ((integrable_const _).indicator hTm)
    have hE1 : ‖∫ ω, R a ω ∂Q‖ ≤ (ρ * Λ) ^ 2 + (Pgue d).real T * (2 * η⁻¹) ^ 2 := by
      rw [← ol_integral_comb d aa bb k (hRc a)]
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_mono hint1 hint2 fun ω => hRpt a ω).trans ?_
      rw [integral_add (integrable_const _) ((integrable_const _).indicator hTm),
        integral_const, integral_indicator_const _ hTm]
      simp
    have hbad : (Pgue d).real T * (2 * η⁻¹) ^ 2 ≤ 4 * Λ ^ 2 := by
      have hMN : M ≤ N := by
        rw [hMeq]
        have : ((d.W N * d.L N : ℕ) : ℝ) ≤ N := by exact_mod_cast hdim
        push_cast at this
        linarith
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      have hN3 : (N : ℝ) ^ (-(3 : ℝ)) = ((N : ℝ) ^ 3)⁻¹ := by
        rw [Real.rpow_neg hN0.le]; norm_cast
      have hNM : (N : ℝ) ^ (-(3 : ℝ)) * M ^ 2 ≤ 1 := by
        rw [hN3, inv_mul_le_iff₀ (by positivity), mul_one]
        calc M ^ 2 ≤ (N : ℝ) ^ 2 := by gcongr
          _ ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast hN1) (by norm_num)
      have hPT0 : 0 ≤ (Pgue d).real T := measureReal_nonneg
      rw [hηinv]
      calc (Pgue d).real T * (2 * (M * Λ)) ^ 2
          = (Pgue d).real T * M ^ 2 * (4 * Λ ^ 2) := by ring
        _ ≤ (N : ℝ) ^ (-(3 : ℝ)) * M ^ 2 * (4 * Λ ^ 2) := by gcongr
        _ ≤ 1 * (4 * Λ ^ 2) := by gcongr
        _ = 4 * Λ ^ 2 := one_mul _
    calc ‖y a‖ = ‖m‖ * ‖∫ ω, R a ω ∂Q‖ := by rw [hy]; exact norm_mul _ _
      _ ≤ 1 * ((ρ * Λ) ^ 2 + 4 * Λ ^ 2) := by rw [hm1]; gcongr; linarith
      _ = (ρ ^ 2 + 4) * Λ ^ 2 := by ring
  -- stability
  have hxa := ol_stable (d.three_le_L N) hκ0 hκ1 hE ht1 (by linarith) hσ0
    (by rw [hsum]; exact hu1.le) x y hxy hyle a
  -- the conclusion is `x a`
  have hint : Integrable (fun ω => gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) u)
      ⟨[true], [a]⟩) (Pgue d) := by
    have hfun : (fun ω => gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) u)
        ⟨[true], [a]⟩) = fun ω => Φ a (olComb d aa bb k ω) + m := by
      funext ω; rw [← hcomb ω a]; ring
    rw [hfun]
    refine (Integrable.of_bound (C := 2 * η⁻¹)
      (((hΦc a).measurable.comp (olComb_measurable d aa bb k)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => hΦb a _)).add (integrable_const _)
  have hconc : (∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt (E N) u)
      ⟨[true], [a]⟩ ∂(Pgue d)) - m = x a := by
    rw [hx]
    simp only
    rw [← ol_integral_comb d aa bb k (hΦc a), ← integral_congr_ae
      (Eventually.of_forall fun ω => hcomb ω a), integral_sub hint (integrable_const _),
      integral_const]
    simp
  rw [hconc]
  calc ‖x a‖ ≤ olC κ * ((ρ ^ 2 + 4) * Λ ^ 2) := hxa
    _ = olC κ * (ρ ^ 2 + 4) * Λ ^ 2 := by ring

/-- **Lemma 5.15 for the GUE-phase profile** at every grid time: the `1`-loop expectation
is `≺ (N η_u)^{-2}` given the pathwise `1`-loop bound `≺ (N η_u)^{-1}`. -/
theorem gueGrid_expect_oneLoop {κ : ℝ} (hκ : 0 < κ) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (h1 : StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × ZMod (d.L N)) ω =>
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) ⟨[true], [p.2]⟩ - mE (E N)‖)
      (fun N p _ => (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹)) :
    UnifDetDom
      (fun N (p : Fin (gueGridK n0 N + 1) × ZMod (d.L N)) =>
        ‖(∫ ω, gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) ⟨[true], [p.2]⟩ ∂(Pgue d)) -
          mE (E N)‖)
      (fun N p => (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹ ^ 2) := by
  set κ' := min κ 1 with hκ'
  have hκ'0 : 0 < κ' := lt_min hκ one_pos
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hE' : ∀ N, |E N| ≤ 2 - κ' := fun N => (hE N).trans (by linarith [min_le_left κ 1])
  set C := olC κ' with hC
  have hC0 : 0 ≤ C := olC_nonneg
  intro τ hτ
  have hbad := h1 (τ / 4) (by positivity) 3 (by norm_num)
  filter_upwards [hbad, d.dim, eventually_le_rpow (8 * C + 1) (half_pos hτ),
    eventually_ge_atTop 1] with N hPN hdim hNτ hN1
  rintro ⟨k, a⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have key := ol_expect_bound d hκ'0 hκ'1 N (hE' N) (ht1 N) (ht10 N) (ht0 N) (gueGridK n0)
    (gueGridK_ne_zero n0 N) k (Nat.lt_succ_iff.1 k.isLt) hdim.1 hN1
    _ hPN (fun ω hω b => by
      by_contra hc
      exact hω ⟨(k, b), lt_of_not_ge hc⟩) a
  refine key.trans ?_
  set Λ2 := (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N k))⁻¹ ^ 2 with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by rw [hΛ2]; exact sq_nonneg _
  set X := (N : ℝ) ^ (τ / 2) with hX
  have hsq : ((N : ℝ) ^ (τ / 4)) ^ 2 = X := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num; ring_nf
  have hτeq : (N : ℝ) ^ τ = X * X := by
    rw [hX, ← Real.rpow_add hN0]; ring_nf
  rw [hsq, hτeq]
  have hX1 : 8 * C + 1 ≤ X := hNτ
  have hXC : C * (X + 4) ≤ X * X := by nlinarith
  exact mul_le_mul_of_nonneg_right hXC hΛ20

end Main

end RBM.Gauss.GUEGrid
