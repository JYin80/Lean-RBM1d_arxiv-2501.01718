/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Generator
import RBM1D.Gauss.Stein

/-!
# T70 (matrix version): discharging `MatrixStein`

`RBM1D/Gauss/Generator.lean` states `RBM.Gauss.MatrixStein` as a structure and consumes it in
the generator identity.  This file proves it.

The route avoids any disintegration machinery.  Write `upd d c (ω, t)` for `ω` with its
`c`-th coordinate replaced by `t`.  Because the coordinates of `P d` are independent and the
`c`-th one has law `gaussianReal 0 (gvar d c)`, replacing it by an independent sample of its
own law leaves the measure invariant:

* `RBM.Gauss.P_map_update` — `((P d) ⊗ γ_c).map (upd d c) = P d`.

Both sides of Stein's identity are then pushed through that map, Fubini on the product
separates the coordinate `t` from the rest, and the inner integral is the one-dimensional
complex Stein identity of `RBM1D/Gauss/Stein.lean`.  Independence enters exactly once, in
`P_map_update`, and it is checked on measurable boxes via `Measure.eq_infinitePi`.

Note that the `FinDep` hypotheses of `MatrixStein` are *not* needed on this route; they are
accepted and ignored, so that the interface T71 consumes is unchanged.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-! ### Stein in one real variable, with no restriction on the variance -/

/-- The complex one-dimensional Stein identity without the hypothesis `v ≠ 0`: at `v = 0` the
Gaussian is a Dirac mass at `0` and both sides vanish. -/
theorem integral_mul_gaussianReal_complex' {var : ℝ≥0} {f f' : ℝ → ℂ} {C : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf'c : Continuous f')
    (hb : ∀ x, ‖f x‖ ≤ C) (hb' : ∀ x, ‖f' x‖ ≤ C) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  · exact RBM.integral_mul_gaussianReal_complex hv hf hf'c hb hb'

/-! ### Updating one coordinate -/

variable {d : Dims}

/-- `upd d c (ω, t)` is `ω` with its `c`-th coordinate replaced by `t`. -/
noncomputable def upd (d : Dims) (c : Coord d) (p : Ω d × ℝ) : Ω d :=
  Function.update p.1 c p.2

@[simp] theorem upd_self (c : Coord d) (p : Ω d × ℝ) : upd d c p c = p.2 :=
  Function.update_self _ _ _

theorem upd_of_ne (c : Coord d) (p : Ω d × ℝ) {i : Coord d} (h : i ≠ c) :
    upd d c p i = p.1 i :=
  Function.update_of_ne h _ _

theorem measurable_upd (d : Dims) (c : Coord d) : Measurable (upd d c) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [upd_self] using measurable_snd
  · simpa only [upd_of_ne c _ h, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

/-- Moving one coordinate is continuous, in the product topology on `Ω d`. -/
theorem continuous_update_coord (c : Coord d) (ω : Ω d) :
    Continuous fun t : ℝ => Function.update ω c t := by
  refine continuous_pi fun i => ?_
  by_cases h : i = c
  · subst h
    simpa only [Function.update_self] using continuous_id'
  · simpa only [Function.update_of_ne h] using continuous_const

/-- The measure of a measurable box under `P d`: the coordinates are independent. -/
theorem P_pi (d : Dims) {s : Finset (Coord d)} {t : Coord d → Set ℝ}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    P d (Set.pi (↑s) t) = ∏ i ∈ s, (gaussianReal 0 (gvar d i)) (t i) := by
  unfold P
  exact Measure.infinitePi_pi _ ht

/-- **Resampling one coordinate leaves `P d` invariant.**  This is the only place where the
independence of the Gaussian coordinates is used. -/
theorem P_map_update (d : Dims) (c : Coord d) :
    ((P d).prod (gaussianReal 0 (gvar d c))).map (upd d c) = P d := by
  classical
  have hUm : Measurable (upd d c) := measurable_upd d c
  change _ = Measure.infinitePi _
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
    rw [hpre, Measure.prod_prod, P_pi d (fun i _ => ht i), ← Finset.prod_erase_mul s _ hc]
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
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, P_pi d (fun i _ => ht i)]

/-! ### The matrix Stein identity -/

/-- **T70, matrix version.**  Discharges the structure `RBM.Gauss.MatrixStein` that T71 uses. -/
theorem matrixStein (d : Dims) : MatrixStein d := by
  refine ⟨fun c g g' hgc hg'c _ _ hderiv hgb hg'b => ?_⟩
  obtain ⟨C₀, hC₀⟩ := hgb
  obtain ⟨C₁, hC₁⟩ := hg'b
  have hC : ∀ ω, ‖g ω‖ ≤ max C₀ C₁ := fun ω => (hC₀ ω).trans (le_max_left _ _)
  have hC' : ∀ ω, ‖g' ω‖ ≤ max C₀ C₁ := fun ω => (hC₁ ω).trans (le_max_right _ _)
  have hgm : Measurable g := hgc.measurable
  have hg'm : Measurable g' := hg'c.measurable
  have hUm : Measurable (upd d c) := measurable_upd d c
  -- the derivative along the fibre through an arbitrary point
  have hfib : ∀ (ω : Ω d) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s)) (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  -- integrability on the product
  have hInt : Integrable (fun p : Ω d × ℝ => p.2 • g (upd d c p))
      ((P d).prod (gaussianReal 0 (gvar d c))) := by
    have hbase : Integrable (fun p : Ω d × ℝ => p.2)
        ((P d).prod (gaussianReal 0 (gvar d c))) :=
      (RBM.integrable_id_gaussianReal (var := gvar d c)).comp_snd (P d)
    refine Integrable.mono' (hbase.abs.const_mul (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (measurable_snd.smul (hgm.comp hUm)).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg p.2)
  have hInt' : Integrable (fun p : Ω d × ℝ => g' (upd d c p))
      ((P d).prod (gaussianReal 0 (gvar d c))) := by
    refine Integrable.mono' (integrable_const (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => hC' _)
    exact (hg'm.comp hUm).aestronglyMeasurable
  -- both sides through the resampling map
  have hL : ∫ ω, ω c • g ω ∂(P d)
      = ∫ p : Ω d × ℝ, p.2 • g (upd d c p) ∂((P d).prod (gaussianReal 0 (gvar d c))) := by
    conv_lhs => rw [← P_map_update d c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update d c]
      exact ((measurable_pi_apply c).smul hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(P d)
      = ∫ p : Ω d × ℝ, g' (upd d c p) ∂((P d).prod (gaussianReal 0 (gvar d c))) := by
    conv_lhs => rw [← P_map_update d c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update d c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hInt, integral_prod _ hInt', ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  change ∫ t : ℝ, t • g (Function.update ω c t) ∂(gaussianReal 0 (gvar d c))
      = (gvar d c : ℝ) • ∫ t : ℝ, g' (Function.update ω c t) ∂(gaussianReal 0 (gvar d c))
  have hcont : Continuous fun t : ℝ => g' (Function.update ω c t) :=
    hg'c.comp (continuous_update_coord c ω)
  have hst := integral_mul_gaussianReal_complex' (var := gvar d c)
    (f := fun t => g (Function.update ω c t)) (f' := fun t => g' (Function.update ω c t))
    (C := max C₀ C₁) (hfib ω) hcont (fun t => hC _) (fun t => hC' _)
  simpa only [Complex.real_smul] using hst

end RBM.Gauss
