/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.OUCommonCarrier
import RBM1D.Gauss.SteinMatrix
import RBM1D.Gauss.TestFunHerm
import RBM1D.Flow.OUComparisonHessian

/-!
# The OU generator identity

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*: the exact second-order Gaussian interpolation identity that replaces (2.25) on the
Gaussian model,

  `d/dt E Φ(H_t) = -½ e^{-t} ∑_{ab} S°_{ab} E ∂_{ab}∂_{ba} Φ(H_t)`,

where `H_t = ouMatrix d N t` is the fixed-time OU interpolation of
`RBM1D/Flow/OUMarginalGaussian.lean` (`e^{-t/2} X + √(1-e^{-t}) Y`, `X` the band field, `Y` an
independent normalized GUE field) and
`S°_{ab} = S_{ab} - M⁻¹` is `RBM.centeredVarianceEntry`.

## Route

`ouMatrix d N t ω = ouBandCoeff t • Xmat d N ω.1 + ouGueCoeff t • Xmat d N ω.2` factors through the
same coordinate template `Xmat`/`Bmat`/`usedCoord` used by `Gauss/Generator.lean` for both
independent fields, applied to the two samples `ω.1 : Ω d` (band, law `P d`) and `ω.2 : Ω d` (GUE,
law `gueMeasure d N`).  The derivative in `t` is a chain rule producing a sum of **two** terms
(one Gaussian coordinate contribution from each field), each of which is turned into a second
derivative by **Stein's identity for that field's own coordinate law**:
`RBM.Gauss.matrixStein` for `P d` (`Gauss/SteinMatrix.lean`, reused unchanged) and a fresh
`gueMatrixStein`, proved here by the identical route (`Gauss/SteinMatrix.lean`'s `P_map_update`
argument, with `gvar d` replaced by `gueCoordVar d N`).

Collapsing the two independent coordinate sums to the paper's index-pair sum uses the same
purely algebraic lemma `RBM.Gauss.sum_used_eq_sum_pairs` (`Gauss/Generator.lean`) both times: once
with the weight `Sblk` (band) and once with the constant weight `M⁻¹` (GUE); the two collapse to
the *single* sum with weight `Sblk - M⁻¹ = centeredVarianceEntry`, because
`a'(t) a(t) = -½ e^{-t}` and `b'(t) b(t) = ½ e^{-t}` (`ouBandCoeff`, `ouGueCoeff`).

`TestFun'` is used through the Hermitian bridge of `Gauss/TestFunHerm.lean`: since `ouMatrix` is
always Hermitian, the identity for the global class `TestFun` (proved first, for `hermFun d N Φ`)
transports to `Φ` itself.

## Main results

* `ouCommon_hasDerivAt_integral`, `ouCommon_integral_sub_eq`, `testFun'_stieltjesImProduct` —
  the three main results.  The third one (§10) bounds the Fréchet derivatives of `∏ Im m(z_i)` in
  every real direction (Hermitian and non-Hermitian) at Hermitian matrices, as `TestFun'` requires.

No `sorry`, no `axiom`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal ComplexConjugate Matrix.Norms.L2Operator

/-! ## 1. A Stein identity for the GUE coordinate field

Literally `RBM1D/Gauss/SteinMatrix.lean`'s route (`P_pi`, `P_map_update`, `matrixStein`), with
`P d = Measure.infinitePi (fun c => gaussianReal 0 (gvar d c))` replaced by
`gueMeasure d N = Measure.infinitePi (fun c => gaussianReal 0 (gueCoordVar d N c))`
(`RBM1D/Flow/OUMarginalGaussian.lean`). -/

section GueStein

variable (d : Dims) (N : ℕ)

private theorem gueMeasure_pi {s : Finset (Coord d)} {t : Coord d → Set ℝ}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    gueMeasure d N (Set.pi (↑s) t) = ∏ i ∈ s, (gaussianReal 0 (gueCoordVar d N i)) (t i) := by
  unfold gueMeasure
  exact Measure.infinitePi_pi _ ht

/-- **The law of one GUE coordinate.**  The `gueMeasure` analogue of `RBM.Gauss.P_map_eval`. -/
private theorem gueMeasure_map_eval (c : Coord d) :
    (gueMeasure d N).map (fun ω => ω c) = gaussianReal 0 (gueCoordVar d N c) :=
  Measure.infinitePi_map_eval _ c

/-- Each GUE coordinate is integrable (first moment of a centred Gaussian). -/
private theorem integrable_coord_gue (c : Coord d) :
    Integrable (fun ω : Ω d => ω c) (gueMeasure d N) := by
  have hf : AEMeasurable (fun ω : Ω d => ω c) (gueMeasure d N) :=
    (measurable_pi_apply c).aemeasurable
  have hg : Integrable (fun x : ℝ => x) ((gueMeasure d N).map fun ω => ω c) := by
    rw [gueMeasure_map_eval]
    exact (memLp_id_gaussianReal (μ := 0) (v := gueCoordVar d N c) 1).integrable le_rfl
  exact (integrable_map_measure hg.aestronglyMeasurable hf).1 hg

/-- **Resampling one GUE coordinate leaves `gueMeasure d N` invariant.** -/
private theorem gueMeasure_map_update (c : Coord d) :
    ((gueMeasure d N).prod (gaussianReal 0 (gueCoordVar d N c))).map (upd d c)
      = gueMeasure d N := by
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
    rw [hpre, Measure.prod_prod, gueMeasure_pi d N (fun i _ => ht i),
      ← Finset.prod_erase_mul s _ hc]
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
    rw [hpre, Measure.prod_prod, measure_univ, mul_one, gueMeasure_pi d N (fun i _ => ht i)]

/-- **The GUE-field Stein identity.**  Same statement and proof as `RBM.Gauss.matrixStein`,
for `gueMeasure d N` in place of `P d` and `gueCoordVar d N` in place of `gvar d`. -/
private theorem gueMatrixStein (c : Coord d) (g g' : Ω d → ℂ)
    (hgc : Continuous g) (hg'c : Continuous g')
    (hderiv : ∀ ω, HasDerivAt (fun t : ℝ => g (Function.update ω c t)) (g' ω) (ω c))
    (hgb : ∃ C : ℝ, ∀ ω, ‖g ω‖ ≤ C) (hg'b : ∃ C : ℝ, ∀ ω, ‖g' ω‖ ≤ C) :
    ∫ ω, ω c • g ω ∂(gueMeasure d N) = (gueCoordVar d N c : ℝ) • ∫ ω, g' ω ∂(gueMeasure d N) := by
  obtain ⟨C₀, hC₀⟩ := hgb
  obtain ⟨C₁, hC₁⟩ := hg'b
  have hC : ∀ ω, ‖g ω‖ ≤ max C₀ C₁ := fun ω => (hC₀ ω).trans (le_max_left _ _)
  have hC' : ∀ ω, ‖g' ω‖ ≤ max C₀ C₁ := fun ω => (hC₁ ω).trans (le_max_right _ _)
  have hgm : Measurable g := hgc.measurable
  have hg'm : Measurable g' := hg'c.measurable
  have hUm : Measurable (upd d c) := measurable_upd d c
  have hfib : ∀ (ω : Ω d) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s)) (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  have hInt : Integrable (fun p : Ω d × ℝ => p.2 • g (upd d c p))
      ((gueMeasure d N).prod (gaussianReal 0 (gueCoordVar d N c))) := by
    have hbase : Integrable (fun p : Ω d × ℝ => p.2)
        ((gueMeasure d N).prod (gaussianReal 0 (gueCoordVar d N c))) :=
      (RBM.integrable_id_gaussianReal (var := gueCoordVar d N c)).comp_snd (gueMeasure d N)
    refine Integrable.mono' (hbase.abs.const_mul (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (measurable_snd.smul (hgm.comp hUm)).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg p.2)
  have hInt' : Integrable (fun p : Ω d × ℝ => g' (upd d c p))
      ((gueMeasure d N).prod (gaussianReal 0 (gueCoordVar d N c))) := by
    refine Integrable.mono' (integrable_const (max C₀ C₁)) ?_
      (Eventually.of_forall fun p => hC' _)
    exact (hg'm.comp hUm).aestronglyMeasurable
  have hL : ∫ ω, ω c • g ω ∂(gueMeasure d N)
      = ∫ p : Ω d × ℝ, p.2 • g (upd d c p)
          ∂((gueMeasure d N).prod (gaussianReal 0 (gueCoordVar d N c))) := by
    conv_lhs => rw [← gueMeasure_map_update d N c]
    rw [integral_map hUm.aemeasurable (by
      rw [gueMeasure_map_update d N c]
      exact ((measurable_pi_apply c).smul hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(gueMeasure d N)
      = ∫ p : Ω d × ℝ, g' (upd d c p)
          ∂((gueMeasure d N).prod (gaussianReal 0 (gueCoordVar d N c))) := by
    conv_lhs => rw [← gueMeasure_map_update d N c]
    rw [integral_map hUm.aemeasurable (by
      rw [gueMeasure_map_update d N c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hInt, integral_prod _ hInt', ← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  change ∫ t : ℝ, t • g (Function.update ω c t) ∂(gaussianReal 0 (gueCoordVar d N c))
      = (gueCoordVar d N c : ℝ) • ∫ t : ℝ, g' (Function.update ω c t)
          ∂(gaussianReal 0 (gueCoordVar d N c))
  have hcont : Continuous fun t : ℝ => g' (Function.update ω c t) :=
    hg'c.comp (continuous_update_coord c ω)
  have hst := integral_mul_gaussianReal_complex' (var := gueCoordVar d N c)
    (f := fun t => g (Function.update ω c t)) (f' := fun t => g' (Function.update ω c t))
    (C := max C₀ C₁) (hfib ω) hcont (fun t => hC _) (fun t => hC' _)
  simpa only [Complex.real_smul] using hst

end GueStein

/-! ## 2. The two interpolation coefficients: elementary derivatives

`ouBandCoeff t = exp(-t/2)`, `ouGueCoeff t = √(ouZeta t)`, `ouZeta t = 1 - exp(-t)`
(`RBM1D/Flow/OUMarginalGaussian.lean`). -/

section CoeffDeriv

private theorem hasDerivAt_ouBandCoeff (t : ℝ) :
    HasDerivAt ouBandCoeff (-(1 / 2 : ℝ) * Real.exp (-t / 2)) t := by
  unfold ouBandCoeff
  have hg : HasDerivAt (fun s : ℝ => -s / 2) (-(1 / 2 : ℝ)) t := by
    have h := (hasDerivAt_id t).neg.div_const (2 : ℝ)
    norm_num at h
    convert h using 1
  have h2 := hg.exp
  rw [mul_comm] at h2
  exact h2

private theorem hasDerivAt_ouZeta (t : ℝ) :
    HasDerivAt ouZeta (Real.exp (-t)) t := by
  unfold ouZeta
  have hg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := (hasDerivAt_id t).neg
  have h2 := hg.exp
  have h3 := h2.const_sub (1 : ℝ)
  simp only [mul_neg_one, neg_neg] at h3
  exact h3

private theorem ouZeta_pos {t : ℝ} (ht : 0 < t) : 0 < ouZeta t := by
  unfold ouZeta
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

private theorem hasDerivAt_ouGueCoeff {t : ℝ} (ht : 0 < t) :
    HasDerivAt ouGueCoeff (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) t := by
  unfold ouGueCoeff
  have htz : ouZeta t ≠ 0 := (ouZeta_pos ht).ne'
  exact (hasDerivAt_ouZeta t).sqrt htz

end CoeffDeriv

/-! ## 3. Coordinate calculus on a shifted scalar-linear flow

`Y + a • Xmat d N ω`, a fixed matrix `Y` plus a real multiple of the coordinate template applied
to one sample `ω`.  This is the common shape both fields' contributions take once the other
field's sample is frozen (Fubini). -/

section ShiftScalarCalc

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **The coordinate derivative of `coordD1` along the shifted scalar-linear flow.**  Moving the
Gaussian coordinate `p` of `ω` moves the matrix argument along `a • Bmat p`; this is where
Stein's identity (for either field) turns a coordinate value into a second derivative. -/
private theorem hasDerivAt_coordD1_shift_update (h : TestFun d N Φ)
    (Y : Matrix (d.Idx N) (d.Idx N) ℂ) (a : ℝ) (ω : Ω d)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    HasDerivAt
      (fun t : ℝ => coordD1 d N Φ (Y + a • Xmat d N (Function.update ω (crd d N p) t)) p)
      (a • coordD2 d N Φ (Y + a • Xmat d N ω) p) (ω (crd d N p)) := by
  set c := crd d N p with hc
  set B := Bmat d N p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Y + a • Xmat d N (Function.update ω c t)
      = (Y + a • Xmat d N ω) + (a * (t - ω c)) • B := by
    intro t
    rw [Xmat_update d N ω hp t, smul_add, smul_smul]
    abel
  have hscal : HasDerivAt (fun t : ℝ => a * (t - ω c)) a (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul a
  have hpath : HasDerivAt (fun t : ℝ => Y + a • Xmat d N (Function.update ω c t))
      (a • B) (ω c) := by
    have h1 : HasDerivAt (fun t : ℝ => (Y + a • Xmat d N ω) + (a * (t - ω c)) • B)
        (a • B) (ω c) := (hscal.smul_const B).const_add _
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun t => hline t)
  have hself : Y + a • Xmat d N (Function.update ω c (ω c)) = Y + a • Xmat d N ω := by
    rw [Function.update_eq_self]
  have key := (hasFDerivAt_fderiv_apply h B
    (Y + a • Xmat d N (Function.update ω c (ω c)))).comp_hasDerivAt (ω c) hpath
  rw [hself] at key
  have hval : ((fderiv ℝ (fderiv ℝ Φ) (Y + a • Xmat d N ω)).flip B) (a • B)
      = a • coordD2 d N Φ (Y + a • Xmat d N ω) p := by
    rw [ContinuousLinearMap.flip_apply, map_smul]
    rfl
  rw [hval] at key
  exact key

end ShiftScalarCalc

/-! ## 4. The pointwise chain rule along the OU flow -/

section PointwiseChain

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **The pointwise `t`-derivative of `Φ` along the OU interpolation.**  A sum of two Gaussian
coordinate contributions, one from each independent field, matching the exact second-order
Gaussian interpolation identity before Stein is applied. -/
private theorem hasDerivAt_ouMatrix_Phi (h : TestFun d N Φ) (ω1 ω2 : Ω d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Φ (ouBandCoeff s • Xmat d N ω1 + ouGueCoeff s • Xmat d N ω2))
      ((-(1 / 2 : ℝ) * Real.exp (-t / 2)) • (∑ p ∈ usedCoord d N,
          ω1 (crd d N p) • coordD1 d N Φ
            (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p)
        + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) • (∑ p ∈ usedCoord d N,
            ω2 (crd d N p) • coordD1 d N Φ
              (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p)) t := by
  have hM : HasDerivAt (fun s : ℝ => ouBandCoeff s • Xmat d N ω1 + ouGueCoeff s • Xmat d N ω2)
      ((-(1 / 2 : ℝ) * Real.exp (-t / 2)) • Xmat d N ω1
        + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) • Xmat d N ω2) t :=
    ((hasDerivAt_ouBandCoeff t).smul_const (Xmat d N ω1)).add
      ((hasDerivAt_ouGueCoeff ht).smul_const (Xmat d N ω2))
  have key := (h.differentiable _).hasFDerivAt.comp_hasDerivAt t hM
  rw [map_add, map_smul, map_smul, fderiv_apply_Xmat, fderiv_apply_Xmat] at key
  exact key

end PointwiseChain

/-! ## 5. Differentiating under the joint integral -/

section JointDominated

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

/-- **The generator identity, joint-integral form, for a global `TestFun`.**  Differentiation
under the integral sign over `ouProductMeasure d N`, dominated on `Set.Ioi (t/2)` (the OU
coefficients are smooth away from `0`; `ouGueCoeff` alone has a `√`-type singularity at `0`,
which is why `t > 0` and the `t/2` margin, exactly as `Hflow`'s `u/2` margin in
`Gauss/Generator.lean`). -/
private theorem ouProductMeasure_hasDerivAt_integral (h : TestFun d N Φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => ∫ z : Ω d × Ω d,
        Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2) ∂(ouProductMeasure d N))
      (∫ z : Ω d × Ω d,
        ((-(1 / 2 : ℝ) * Real.exp (-t / 2)) • (∑ p ∈ usedCoord d N,
            z.1 (crd d N p) • coordD1 d N Φ
              (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p)
          + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) • (∑ p ∈ usedCoord d N,
              z.2 (crd d N p) • coordD1 d N Φ
                (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p))
        ∂(ouProductMeasure d N)) t := by
  obtain ⟨C₀, hC₀⟩ := h.bdd₀
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  have ht2 : 0 < t / 2 := by linarith
  have hcontM : ∀ x : ℝ, Continuous fun z : Ω d × Ω d =>
      ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2 :=
    fun x => (((continuous_Xmat d N).comp continuous_fst).const_smul (ouBandCoeff x)).add
      (((continuous_Xmat d N).comp continuous_snd).const_smul (ouGueCoeff x))
  have hcontF : ∀ x : ℝ, Continuous fun z : Ω d × Ω d =>
      Φ (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) :=
    fun x => h.contDiff.continuous.comp (hcontM x)
  have hcontD1 : ∀ x : ℝ, Continuous fun z : Ω d × Ω d =>
      (∑ p ∈ usedCoord d N, z.1 (crd d N p) • coordD1 d N Φ
          (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) :=
    fun x => continuous_finsetSum (usedCoord d N) fun p _ =>
      ((continuous_apply (crd d N p)).comp continuous_fst).smul
        ((h.continuous_fderiv.comp (hcontM x)).clm_apply continuous_const)
  have hcontD2 : ∀ x : ℝ, Continuous fun z : Ω d × Ω d =>
      (∑ p ∈ usedCoord d N, z.2 (crd d N p) • coordD1 d N Φ
          (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) :=
    fun x => continuous_finsetSum (usedCoord d N) fun p _ =>
      ((continuous_apply (crd d N p)).comp continuous_snd).smul
        ((h.continuous_fderiv.comp (hcontM x)).clm_apply continuous_const)
  have hcontF' : ∀ x : ℝ, Continuous fun z : Ω d × Ω d =>
      ((-(1 / 2 : ℝ) * Real.exp (-x / 2)) • (∑ p ∈ usedCoord d N, z.1 (crd d N p) •
            coordD1 d N Φ (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p)
        + (Real.exp (-x) / (2 * Real.sqrt (ouZeta x))) • (∑ p ∈ usedCoord d N, z.2 (crd d N p) •
              coordD1 d N Φ (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p)) :=
    fun x => ((hcontD1 x).const_smul (-(1 / 2 : ℝ) * Real.exp (-x / 2))).add
      ((hcontD2 x).const_smul (Real.exp (-x) / (2 * Real.sqrt (ouZeta x))))
  have hboundA : ∀ x : ℝ, t / 2 < x → |-(1 / 2 : ℝ) * Real.exp (-x / 2)| ≤ (1 / 2 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have he1 : Real.exp (-x / 2) ≤ 1 := by
      have : -x / 2 ≤ 0 := by linarith
      exact Real.exp_le_one_iff.mpr this
    rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_pos (Real.exp_pos _)]
    nlinarith [Real.exp_pos (-x / 2)]
  have hboundB : ∀ x : ℝ, t / 2 < x →
      |Real.exp (-x) / (2 * Real.sqrt (ouZeta x))|
        ≤ Real.exp (-(t / 2)) / (2 * Real.sqrt (ouZeta (t / 2))) := by
    intro x hx
    have hzt2 : 0 < ouZeta (t / 2) := ouZeta_pos ht2
    have hzx : 0 < ouZeta x := ouZeta_pos (lt_trans ht2 hx)
    have hmono : ouZeta (t / 2) ≤ ouZeta x := by
      have hexp : Real.exp (-x) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith)
      unfold ouZeta
      linarith
    have hexp : Real.exp (-x) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_pos (by positivity)]
    gcongr
  set B1 : ℝ := Real.exp (-(t / 2)) / (2 * Real.sqrt (ouZeta (t / 2))) with hB1
  have hbound : ∀ᵐ z ∂(ouProductMeasure d N), ∀ x ∈ Set.Ioi (t / 2),
      ‖((-(1 / 2 : ℝ) * Real.exp (-x / 2)) • (∑ p ∈ usedCoord d N, z.1 (crd d N p) •
            coordD1 d N Φ (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p)
        + (Real.exp (-x) / (2 * Real.sqrt (ouZeta x))) • (∑ p ∈ usedCoord d N, z.2 (crd d N p) •
              coordD1 d N Φ (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p))‖
        ≤ (1 / 2 : ℝ) * (∑ p ∈ usedCoord d N,
              |z.1 (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖))
          + B1 * (∑ p ∈ usedCoord d N,
              |z.2 (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)) := by
    refine Eventually.of_forall fun z x hx => ?_
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul (hboundA x hx) ?_ (norm_nonneg _) (by norm_num)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD1_le hC₁ _ p) (abs_nonneg _)
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul (hboundB x hx) ?_ (norm_nonneg _) (by positivity)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD1_le hC₁ _ p) (abs_nonneg _)
  have hbndint : Integrable (fun z : Ω d × Ω d =>
      (1 / 2 : ℝ) * (∑ p ∈ usedCoord d N,
            |z.1 (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖))
        + B1 * (∑ p ∈ usedCoord d N,
            |z.2 (crd d N p)| * (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖)))
      (ouProductMeasure d N) := by
    refine Integrable.add (Integrable.const_mul ?_ _) (Integrable.const_mul ?_ _)
    · exact integrable_finsetSum _ fun p _ =>
        (((integrable_coord d (crd d N p)).abs).comp_fst (gueMeasure d N)).mul_const _
    · exact integrable_finsetSum _ fun p _ =>
        (((integrable_coord_gue d N (crd d N p)).abs).comp_snd (P d)).mul_const _
  have hdiff : ∀ᵐ z ∂(ouProductMeasure d N), ∀ x ∈ Set.Ioi (t / 2),
      HasDerivAt (fun s : ℝ => Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2))
        ((-(1 / 2 : ℝ) * Real.exp (-x / 2)) • (∑ p ∈ usedCoord d N, z.1 (crd d N p) •
              coordD1 d N Φ (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p)
          + (Real.exp (-x) / (2 * Real.sqrt (ouZeta x))) • (∑ p ∈ usedCoord d N,
                z.2 (crd d N p) • coordD1 d N Φ
                  (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p)) x :=
    Eventually.of_forall fun z x hx => hasDerivAt_ouMatrix_Phi h z.1 z.2 (lt_trans ht2 hx)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ouProductMeasure d N) (𝕜 := ℝ)
    (F := fun (s : ℝ) (z : Ω d × Ω d) =>
      Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2))
    (F' := fun (s : ℝ) (z : Ω d × Ω d) =>
      (-(1 / 2 : ℝ) * Real.exp (-s / 2)) • (∑ p ∈ usedCoord d N, z.1 (crd d N p) •
            coordD1 d N Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2) p)
        + (Real.exp (-s) / (2 * Real.sqrt (ouZeta s))) • (∑ p ∈ usedCoord d N, z.2 (crd d N p) •
              coordD1 d N Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2) p))
    (x₀ := t) (s := Set.Ioi (t / 2))
    (Ioi_mem_nhds (by linarith : t / 2 < t))
    (Eventually.of_forall fun x => (hcontF x).aestronglyMeasurable)
    (by
      have hcm : AEStronglyMeasurable
          (fun z : Ω d × Ω d => Φ (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2))
          (ouProductMeasure d N) := (hcontF t).aestronglyMeasurable
      exact (memLp_top_of_bound hcm C₀ (Eventually.of_forall fun z => hC₀ _)).integrable le_top)
    (hcontF' t).aestronglyMeasurable hbound hbndint hdiff).2

end JointDominated

/-! ## 6. Turning the coordinate sum into the index-pair sum, per field

`sum_used_eq_sum_pairs` (`Gauss/Generator.lean`) is purely algebraic (no measure); it is reused
unchanged, once with the weight `Sblk` (band field) and once with the constant weight `M⁻¹`
(GUE field, `RBM.Gauss.gueCoordVar`'s diagonal value). -/

section StepFubiniStein

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

private theorem Xmat_congr_of_agree (d : Dims) (N : ℕ) (ω ω' : Ω d)
    (hagree : ∀ e ∈ (usedCoord d N).image (crd d N), ω e = ω' e) :
    Xmat d N ω = Xmat d N ω' := by
  rw [Xmat_eq_sum, Xmat_eq_sum]
  exact Finset.sum_congr rfl fun p hp => by rw [hagree (crd d N p) (Finset.mem_image_of_mem _ hp)]

private theorem finDep_ouMatrix_shift {V : Type*} (Y : Matrix (d.Idx N) (d.Idx N) ℂ) (a : ℝ)
    (F : Matrix (d.Idx N) (d.Idx N) ℂ → V) :
    FinDep d (fun ω : Ω d => F (Y + a • Xmat d N ω)) :=
  ⟨(usedCoord d N).image (crd d N), fun ω ω' hagree => by
    change F (Y + a • Xmat d N ω) = F (Y + a • Xmat d N ω')
    rw [Xmat_congr_of_agree d N ω ω' hagree]⟩

private theorem continuous_ouShift (Y : Matrix (d.Idx N) (d.Idx N) ℂ) (a : ℝ) :
    Continuous fun ω : Ω d => Y + a • Xmat d N ω :=
  continuous_const.add ((continuous_Xmat d N).const_smul a)

private theorem continuous_coordD1_shift (h : TestFun d N Φ) (Y : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a : ℝ) (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun ω : Ω d => coordD1 d N Φ (Y + a • Xmat d N ω) p :=
  (h.continuous_fderiv.comp (continuous_ouShift Y a)).clm_apply continuous_const

private theorem continuous_coordD2_shift (h : TestFun d N Φ) (Y : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a : ℝ) (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun ω : Ω d => coordD2 d N Φ (Y + a • Xmat d N ω) p :=
  ((h.continuous_fderiv2.comp (continuous_ouShift Y a)).clm_apply
    continuous_const).clm_apply continuous_const

/-- **Stein's identity for the band field, under a fixed GUE shift.** -/
private theorem coordD1_stein_band (h : TestFun d N Φ) (Y : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a : ℝ) (p : d.Idx N × d.Idx N × Bool) (hp : p ∈ usedCoord d N) :
    ∫ ω1, ω1 (crd d N p) • coordD1 d N Φ (Y + a • Xmat d N ω1) p ∂(P d)
      = (gvar d (crd d N p) : ℝ) •
          ∫ ω1, a • coordD2 d N Φ (Y + a • Xmat d N ω1) p ∂(P d) := by
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  exact (matrixStein d).stein (crd d N p)
    (fun ω1 => coordD1 d N Φ (Y + a • Xmat d N ω1) p)
    (fun ω1 => a • coordD2 d N Φ (Y + a • Xmat d N ω1) p)
    (continuous_coordD1_shift h Y a p)
    ((continuous_coordD2_shift h Y a p).const_smul a)
    (finDep_ouMatrix_shift Y a (fun M => coordD1 d N Φ M p))
    (finDep_ouMatrix_shift Y a (fun M => a • coordD2 d N Φ M p))
    (fun ω1 => hasDerivAt_coordD1_shift_update h Y a ω1 hp)
    ⟨C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖, fun ω1 => norm_coordD1_le hC₁ _ p⟩
    ⟨|a| * (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖), fun ω1 => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD2_le hC₂ _ p) (abs_nonneg _)⟩

/-- **Stein's identity for the GUE field, under a fixed band shift.** -/
private theorem coordD1_stein_gue (h : TestFun d N Φ) (Y : Matrix (d.Idx N) (d.Idx N) ℂ)
    (a : ℝ) (p : d.Idx N × d.Idx N × Bool) (hp : p ∈ usedCoord d N) :
    ∫ ω2, ω2 (crd d N p) • coordD1 d N Φ (Y + a • Xmat d N ω2) p ∂(gueMeasure d N)
      = (gueCoordVar d N (crd d N p) : ℝ) •
          ∫ ω2, a • coordD2 d N Φ (Y + a • Xmat d N ω2) p ∂(gueMeasure d N) := by
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  exact gueMatrixStein d N (crd d N p)
    (fun ω2 => coordD1 d N Φ (Y + a • Xmat d N ω2) p)
    (fun ω2 => a • coordD2 d N Φ (Y + a • Xmat d N ω2) p)
    (continuous_coordD1_shift h Y a p)
    ((continuous_coordD2_shift h Y a p).const_smul a)
    (fun ω2 => hasDerivAt_coordD1_shift_update h Y a ω2 hp)
    ⟨C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖, fun ω2 => norm_coordD1_le hC₁ _ p⟩
    ⟨|a| * (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖), fun ω2 => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_coordD2_le hC₂ _ p) (abs_nonneg _)⟩

/-! ### Continuity and integrability of the coordinate terms over the joint measure -/

private theorem continuous_ouMatrix_apply (d : Dims) (N : ℕ) (x : ℝ) :
    Continuous fun z : Ω d × Ω d =>
      ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2 :=
  (((continuous_Xmat d N).comp continuous_fst).const_smul (ouBandCoeff x)).add
    (((continuous_Xmat d N).comp continuous_snd).const_smul (ouGueCoeff x))

private theorem integrable_ouMatrix_coordD1_apply_fst (h : TestFun d N Φ) (x : ℝ)
    (p : d.Idx N × d.Idx N × Bool) :
    Integrable (fun z : Ω d × Ω d => z.1 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) (ouProductMeasure d N) := by
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  have hcont : Continuous fun z : Ω d × Ω d => coordD1 d N Φ
      (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p :=
    (h.continuous_fderiv.comp (continuous_ouMatrix_apply d N x)).clm_apply continuous_const
  exact ((integrable_coord d (crd d N p)).comp_fst (gueMeasure d N)).smul_bdd
    (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) hcont.aestronglyMeasurable
    (Eventually.of_forall fun z => norm_coordD1_le hC₁ _ p)

private theorem integrable_ouMatrix_coordD1_apply_snd (h : TestFun d N Φ) (x : ℝ)
    (p : d.Idx N × d.Idx N × Bool) :
    Integrable (fun z : Ω d × Ω d => z.2 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) (ouProductMeasure d N) := by
  obtain ⟨C₁, hC₁⟩ := h.bdd₁
  have hcont : Continuous fun z : Ω d × Ω d => coordD1 d N Φ
      (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p :=
    (h.continuous_fderiv.comp (continuous_ouMatrix_apply d N x)).clm_apply continuous_const
  exact ((integrable_coord_gue d N (crd d N p)).comp_snd (P d)).smul_bdd
    (C₁ * ‖Bmat d N p.1 p.2.1 p.2.2‖) hcont.aestronglyMeasurable
    (Eventually.of_forall fun z => norm_coordD1_le hC₁ _ p)

private theorem integrable_ouMatrix_coordD2_apply (h : TestFun d N Φ) (x : ℝ)
    (p : d.Idx N × d.Idx N × Bool) :
    Integrable (fun z : Ω d × Ω d => coordD2 d N Φ
        (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) (ouProductMeasure d N) := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  have hcont : Continuous fun z : Ω d × Ω d => coordD2 d N Φ
      (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p :=
    ((h.continuous_fderiv2.comp (continuous_ouMatrix_apply d N x)).clm_apply
      continuous_const).clm_apply continuous_const
  exact (memLp_top_of_bound hcont.aestronglyMeasurable
      (C₂ * ‖Bmat d N p.1 p.2.1 p.2.2‖ * ‖Bmat d N p.1 p.2.1 p.2.2‖)
      (Eventually.of_forall fun z => norm_coordD2_le hC₂ _ p)).integrable le_top

private theorem integrable_ouMatrix_coordD1_sum_fst (h : TestFun d N Φ) (x : ℝ) :
    Integrable (fun z : Ω d × Ω d => ∑ p ∈ usedCoord d N, z.1 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) (ouProductMeasure d N) :=
  integrable_finsetSum _ fun p _ => integrable_ouMatrix_coordD1_apply_fst h x p

private theorem integrable_ouMatrix_coordD1_sum_snd (h : TestFun d N Φ) (x : ℝ) :
    Integrable (fun z : Ω d × Ω d => ∑ p ∈ usedCoord d N, z.2 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff x • Xmat d N z.1 + ouGueCoeff x • Xmat d N z.2) p) (ouProductMeasure d N) :=
  integrable_finsetSum _ fun p _ => integrable_ouMatrix_coordD1_apply_snd h x p

/-! ### Stein under Fubini, at the level of the joint measure -/

/-- **The band-field Stein identity, at the level of the joint measure.** -/
private theorem joint_stein_fst (h : TestFun d N Φ) (t : ℝ)
    (p : d.Idx N × d.Idx N × Bool) (hp : p ∈ usedCoord d N) :
    ∫ z : Ω d × Ω d, z.1 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p ∂(ouProductMeasure d N)
      = (gvar d (crd d N p) : ℝ) • ouBandCoeff t •
          ∫ z : Ω d × Ω d, coordD2 d N Φ
            (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p
          ∂(ouProductMeasure d N) := by
  have hInt1 : Integrable (fun z : Ω d × Ω d => z.1 (crd d N p) • coordD1 d N Φ
      (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p) (ouProductMeasure d N) :=
    integrable_ouMatrix_coordD1_apply_fst h t p
  have hInt2 : Integrable (fun z : Ω d × Ω d => coordD2 d N Φ
      (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p) (ouProductMeasure d N) :=
    integrable_ouMatrix_coordD2_apply h t p
  unfold ouProductMeasure
  have hstep : ∀ ω2 : Ω d, ∫ ω1, ω1 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p ∂(P d)
      = (gvar d (crd d N p) : ℝ) • ouBandCoeff t •
          ∫ ω1, coordD2 d N Φ (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p
            ∂(P d) := by
    intro ω2
    have hcomm : (fun ω1 : Ω d => ω1 (crd d N p) • coordD1 d N Φ
          (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p)
        = fun ω1 : Ω d => ω1 (crd d N p) • coordD1 d N Φ
          (ouGueCoeff t • Xmat d N ω2 + ouBandCoeff t • Xmat d N ω1) p := by
      funext ω1; rw [add_comm]
    have hcomm' : (fun ω1 : Ω d => coordD2 d N Φ
          (ouGueCoeff t • Xmat d N ω2 + ouBandCoeff t • Xmat d N ω1) p)
        = fun ω1 : Ω d => coordD2 d N Φ
          (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p := by
      funext ω1; rw [add_comm]
    rw [hcomm, coordD1_stein_band h (ouGueCoeff t • Xmat d N ω2) (ouBandCoeff t) p hp,
      integral_smul, hcomm']
  rw [integral_prod_symm _ hInt1, funext hstep]
  simp_rw [integral_smul]
  rw [← integral_prod_symm _ hInt2]

/-- **The GUE-field Stein identity, at the level of the joint measure.** -/
private theorem joint_stein_snd (h : TestFun d N Φ) (t : ℝ)
    (p : d.Idx N × d.Idx N × Bool) (hp : p ∈ usedCoord d N) :
    ∫ z : Ω d × Ω d, z.2 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p ∂(ouProductMeasure d N)
      = (gueCoordVar d N (crd d N p) : ℝ) • ouGueCoeff t •
          ∫ z : Ω d × Ω d, coordD2 d N Φ
            (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p
          ∂(ouProductMeasure d N) := by
  have hInt1 : Integrable (fun z : Ω d × Ω d => z.2 (crd d N p) • coordD1 d N Φ
      (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p) (ouProductMeasure d N) :=
    integrable_ouMatrix_coordD1_apply_snd h t p
  have hInt2 : Integrable (fun z : Ω d × Ω d => coordD2 d N Φ
      (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p) (ouProductMeasure d N) :=
    integrable_ouMatrix_coordD2_apply h t p
  unfold ouProductMeasure
  have hstep : ∀ ω1 : Ω d, ∫ ω2, ω2 (crd d N p) • coordD1 d N Φ
        (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p ∂(gueMeasure d N)
      = (gueCoordVar d N (crd d N p) : ℝ) • ouGueCoeff t •
          ∫ ω2, coordD2 d N Φ (ouBandCoeff t • Xmat d N ω1 + ouGueCoeff t • Xmat d N ω2) p
            ∂(gueMeasure d N) := by
    intro ω1
    rw [coordD1_stein_gue h (ouBandCoeff t • Xmat d N ω1) (ouGueCoeff t) p hp, integral_smul]
  rw [integral_prod _ hInt1, funext hstep]
  simp_rw [integral_smul]
  rw [← integral_prod _ hInt2]

/-- The GUE-field coordinate variance, read off from the index pair (the `gueCoordVar` analogue
of `RBM.Gauss.gvar_crd`). -/
private theorem gueCoordVar_crd (p : d.Idx N × d.Idx N × Bool) :
    (gueCoordVar d N (crd d N p) : ℝ)
      = if p.1 = p.2.1 then (ouMatrixSize d N : ℝ)⁻¹ else (ouMatrixSize d N : ℝ)⁻¹ / 2 := by
  unfold gueCoordVar crd
  by_cases hpp : p.1 = p.2.1
  · simp [hpp]
  · simp [hpp]; ring

/-- The `wirtSecond` expectation over the joint measure, in terms of the two real directional
derivatives (the `ouProductMeasure` analogue of `RBM.Gauss.integral_wirtSecond`). -/
private theorem integral_wirtSecond_ouMatrix (h : TestFun d N Φ) (t : ℝ) (i j : d.Idx N) :
    ∫ z : Ω d × Ω d, wirtSecond d N Φ
        (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) i j ∂(ouProductMeasure d N)
      = if i = j then ∫ z : Ω d × Ω d, coordD2 d N Φ
            (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) (i, i, true)
            ∂(ouProductMeasure d N)
        else (1 / 4 : ℝ) • (∫ z : Ω d × Ω d, coordD2 d N Φ
              (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) (i, j, true)
              ∂(ouProductMeasure d N)
            + ∫ z : Ω d × Ω d, coordD2 d N Φ
                (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) (i, j, false)
                ∂(ouProductMeasure d N)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    change wirtSecond d N Φ (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) i i = _
    rw [wirtSecond, ite_eq_left rfl]
  · rw [ite_eq_right hij]
    have hpt : (fun z : Ω d × Ω d => wirtSecond d N Φ
          (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) i j)
        = fun z : Ω d × Ω d => (1 / 4 : ℝ) • (coordD2 d N Φ
              (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) (i, j, true)
            + coordD2 d N Φ
                (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) (i, j, false)) := by
      funext z
      rw [wirtSecond, ite_eq_right hij]
    rw [hpt, integral_smul, integral_add (integrable_ouMatrix_coordD2_apply h t _)
      (integrable_ouMatrix_coordD2_apply h t _)]

/-- Combining two weighted double sums that share the same values `W i j` into one, with the
weights combined pointwise: pure `Finset` algebra, used once with `Sblk` and the constant `M⁻¹`
weight. -/
private theorem sum2_combine {ι : Type*} [Fintype ι] (S1 S2 : ι → ι → ℝ) (c1 c2 : ℝ)
    (W : ι → ι → ℂ) :
    c1 • (∑ i, ∑ j, S1 i j • W i j) + c2 • (∑ i, ∑ j, S2 i j • W i j)
      = ∑ i, ∑ j, (c1 * S1 i j + c2 * S2 i j) • W i j := by
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, ← add_smul]

/-- **The GUE generator identity, joint-integral form, for a global `TestFun`, in the paper's
`∑_{ij} S°_{ij} ∂_ij ∂_ji` form.** The `Sblk` collapse (band field) and the constant-weight
collapse (GUE field) both use `RBM.Gauss.sum_used_eq_sum_pairs` with the *same* function
`p ↦ ∫ z, coordD2 Φ (ouMatrix t z) p`; they combine into the single weight
`Sblk - M⁻¹ = RBM.centeredVarianceEntry` because `a'(t) a(t) = -½ e^{-t}` and
`b'(t) b(t) = ½ e^{-t}` (`ouBandCoeff`, `ouGueCoeff`). -/
private theorem ouProductMeasure_hasDerivAt_integral_pairs (h : TestFun d N Φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => ∫ z : Ω d × Ω d,
        Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2) ∂(ouProductMeasure d N))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
          (centeredVarianceEntry d N a b : ℂ) *
            ∫ z : Ω d × Ω d, wirtSecond d N Φ
              (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) a b
              ∂(ouProductMeasure d N)) t := by
  have hbase := ouProductMeasure_hasDerivAt_integral h ht
  set f : d.Idx N × d.Idx N × Bool → ℂ := fun p => ∫ z : Ω d × Ω d, coordD2 d N Φ
      (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p ∂(ouProductMeasure d N)
    with hf
  have hswap : ∀ (i j : d.Idx N) (b : Bool), f (i, j, b) = f (j, i, b) := by
    intro i j b
    simp only [hf]
    exact integral_congr_ae (Eventually.of_forall fun z => coordD2_swap Φ _ i j b)
  have hband : ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • f p
      = ∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j •
          (if i = j then f (i, i, true) else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
    have hlhs : ∑ p ∈ usedCoord d N, (gvar d (crd d N p) : ℝ) • f p
        = ∑ p ∈ usedCoord d N,
          (if p.1 = p.2.1 then Sblk (d.L N) (d.W N) p.1 p.2.1
           else Sblk (d.L N) (d.W N) p.1 p.2.1 / 2) • f p :=
      Finset.sum_congr rfl fun p _ => by rw [gvar_crd]
    rw [hlhs, show usedCoord d N = Finset.univ.filter
        (fun p : d.Idx N × d.Idx N × Bool =>
          idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
      sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N) (Sblk (d.L N) (d.W N))
        (Sblk_comm (d.L N) (d.W N)) f (fun i j => hswap i j true) (fun i j => hswap i j false)]
  have hgue : ∑ p ∈ usedCoord d N, (gueCoordVar d N (crd d N p) : ℝ) • f p
      = ∑ i : d.Idx N, ∑ j : d.Idx N, (ouMatrixSize d N : ℝ)⁻¹ •
          (if i = j then f (i, i, true) else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
    have hlhs : ∑ p ∈ usedCoord d N, (gueCoordVar d N (crd d N p) : ℝ) • f p
        = ∑ p ∈ usedCoord d N,
          (if p.1 = p.2.1 then (ouMatrixSize d N : ℝ)⁻¹
           else (ouMatrixSize d N : ℝ)⁻¹ / 2) • f p :=
      Finset.sum_congr rfl fun p _ => by rw [gueCoordVar_crd]
    rw [hlhs, show usedCoord d N = Finset.univ.filter
        (fun p : d.Idx N × d.Idx N × Bool =>
          idxKey d N p.1 < idxKey d N p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) from rfl,
      sum_used_eq_sum_pairs (idxKey d N) (idxKey_injective d N)
        (fun _ _ => (ouMatrixSize d N : ℝ)⁻¹) (fun _ _ => rfl) f
        (fun i j => hswap i j true) (fun i j => hswap i j false)]
  have hIeq : (∫ z : Ω d × Ω d,
        ((-(1 / 2 : ℝ) * Real.exp (-t / 2)) • (∑ p ∈ usedCoord d N, z.1 (crd d N p) •
              coordD1 d N Φ (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p)
          + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) • (∑ p ∈ usedCoord d N, z.2 (crd d N p) •
                coordD1 d N Φ (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p))
        ∂(ouProductMeasure d N))
      = (-(1 / 2 : ℝ) * Real.exp (-t / 2)) • (∑ p ∈ usedCoord d N,
              (gvar d (crd d N p) : ℝ) • ouBandCoeff t • f p)
        + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) • (∑ p ∈ usedCoord d N,
              (gueCoordVar d N (crd d N p) : ℝ) • ouGueCoeff t • f p) := by
    have hA : Integrable (fun z : Ω d × Ω d => (-(1 / 2 : ℝ) * Real.exp (-t / 2)) •
        ∑ p ∈ usedCoord d N, z.1 (crd d N p) • coordD1 d N Φ
          (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p) (ouProductMeasure d N) :=
      Integrable.smul (-(1 / 2 : ℝ) * Real.exp (-t / 2)) (integrable_ouMatrix_coordD1_sum_fst h t)
    have hB : Integrable (fun z : Ω d × Ω d => (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) •
        ∑ p ∈ usedCoord d N, z.2 (crd d N p) • coordD1 d N Φ
          (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p) (ouProductMeasure d N) :=
      Integrable.smul (Real.exp (-t) / (2 * Real.sqrt (ouZeta t)))
        (integrable_ouMatrix_coordD1_sum_snd h t)
    rw [integral_add hA hB, integral_smul, integral_smul,
      integral_finsetSum _ (fun p _ => integrable_ouMatrix_coordD1_apply_fst h t p),
      integral_finsetSum _ (fun p _ => integrable_ouMatrix_coordD1_apply_snd h t p),
      Finset.sum_congr rfl (fun p hp => joint_stein_fst h t p hp),
      Finset.sum_congr rfl (fun p hp => joint_stein_snd h t p hp)]
  have hcomm1 : ∀ p : d.Idx N × d.Idx N × Bool,
      (gvar d (crd d N p) : ℝ) • ouBandCoeff t • f p
        = ouBandCoeff t • (gvar d (crd d N p) : ℝ) • f p := fun p => by
    rw [smul_smul, smul_smul, mul_comm]
  have hcomm2 : ∀ p : d.Idx N × d.Idx N × Bool,
      (gueCoordVar d N (crd d N p) : ℝ) • ouGueCoeff t • f p
        = ouGueCoeff t • (gueCoordVar d N (crd d N p) : ℝ) • f p := fun p => by
    rw [smul_smul, smul_smul, mul_comm]
  rw [Finset.sum_congr rfl (fun p _ => hcomm1 p), Finset.sum_congr rfl (fun p _ => hcomm2 p),
    ← Finset.smul_sum, ← Finset.smul_sum, smul_smul, smul_smul, hband, hgue] at hIeq
  -- both terms now share the same `W a b := if a = b then f(a,a,tt) else ¼(f(a,b,tt)+f(a,b,ff))`
  set W : d.Idx N → d.Idx N → ℂ := fun a b =>
    if a = b then f (a, a, true) else (1 / 4 : ℝ) • (f (a, b, true) + f (a, b, false)) with hW
  have hcard : (Fintype.card (d.Idx N) : ℝ) = (ouMatrixSize d N : ℝ) := by
    have h1 : Fintype.card (d.Idx N) = d.L N * d.W N := by simp [ZMod.card]
    unfold ouMatrixSize
    exact_mod_cast h1
  have hcve : ∀ a b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℝ)
      = Sblk (d.L N) (d.W N) a b - (ouMatrixSize d N : ℝ)⁻¹ := by
    intro a b
    unfold RBM.centeredVarianceEntry
    rw [hcard]
  have hcoef : ouBandCoeff t * (-(1 / 2 : ℝ) * Real.exp (-t / 2))
      = -(1 / 2 : ℝ) * Real.exp (-t) := by
    unfold ouBandCoeff
    rw [show Real.exp (-t / 2) * (-(1 / 2 : ℝ) * Real.exp (-t / 2))
        = -(1 / 2 : ℝ) * (Real.exp (-t / 2) * Real.exp (-t / 2)) by ring,
      ← Real.exp_add, show -t / 2 + -t / 2 = -t by ring]
  have hcoef2 : ouGueCoeff t * (Real.exp (-t) / (2 * Real.sqrt (ouZeta t)))
      = (1 / 2 : ℝ) * Real.exp (-t) := by
    unfold ouGueCoeff
    have hpos : 0 < Real.sqrt (ouZeta t) := Real.sqrt_pos.mpr (ouZeta_pos ht)
    field_simp
  have hscalar : ∀ a b : d.Idx N,
      (-(1 / 2 : ℝ) * Real.exp (-t / 2)) * ouBandCoeff t * Sblk (d.L N) (d.W N) a b
        + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) * ouGueCoeff t * (ouMatrixSize d N : ℝ)⁻¹
        = -(1 / 2 : ℝ) * Real.exp (-t) * (RBM.centeredVarianceEntry d N a b : ℝ) := by
    intro a b
    rw [mul_comm (-(1 / 2 : ℝ) * Real.exp (-t / 2)) (ouBandCoeff t),
      mul_comm (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) (ouGueCoeff t), hcoef, hcoef2, hcve a b]
    ring
  have hcombine : ((-(1 / 2 : ℝ) * Real.exp (-t / 2)) * ouBandCoeff t) •
        (∑ i : d.Idx N, ∑ j : d.Idx N, Sblk (d.L N) (d.W N) i j • W i j)
      + ((Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) * ouGueCoeff t) •
        (∑ i : d.Idx N, ∑ j : d.Idx N, (ouMatrixSize d N : ℝ)⁻¹ • W i j)
      = (-(1 / 2 : ℝ) * Real.exp (-t)) •
        ∑ i : d.Idx N, ∑ j : d.Idx N, (RBM.centeredVarianceEntry d N i j : ℝ) • W i j := by
    rw [sum2_combine, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hscalar i j, smul_smul]
  have hfinal : ∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ z : Ω d × Ω d, wirtSecond d N Φ
          (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) a b ∂(ouProductMeasure d N)
      = ∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℝ) • W a b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [integral_wirtSecond_ouMatrix h t a b, Complex.real_smul]
    rfl
  have heq : (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
        (RBM.centeredVarianceEntry d N a b : ℂ) *
          ∫ z : Ω d × Ω d, wirtSecond d N Φ
            (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) a b ∂(ouProductMeasure d N)
      = ∫ z : Ω d × Ω d,
        ((-(1 / 2 : ℝ) * Real.exp (-t / 2)) • (∑ p ∈ usedCoord d N, z.1 (crd d N p) •
              coordD1 d N Φ (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p)
          + (Real.exp (-t) / (2 * Real.sqrt (ouZeta t))) • (∑ p ∈ usedCoord d N, z.2 (crd d N p) •
                coordD1 d N Φ (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) p))
        ∂(ouProductMeasure d N) := by
    rw [hfinal, hIeq, ← hcombine]
  rw [heq]
  exact hbase

end StepFubiniStein

/-! ## 7. The bridge from `TestFun` to `TestFun'`, and from `ouProductMeasure` to
`ouCommonMeasure` -/

section Bridge

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

private theorem complex_smul_eq_real_smul {n : Type*} [Fintype n] [DecidableEq n]
    (r : ℝ) (A : Matrix n n ℂ) : (r : ℂ) • A = r • A := by
  ext k l
  simp [Matrix.smul_apply, Complex.real_smul]

/-- `ouMatrix`'s definition, converted to the real-scalar convention used throughout §§3–6. -/
private theorem ouMatrix_eq_realSmul (d : Dims) (N : ℕ) (t : ℝ) (z : Ω d × Ω d) :
    ouMatrix d N t z = ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2 := by
  change (ouBandCoeff t : ℂ) • ouBandMatrix d N z + (ouGueCoeff t : ℂ) • ouGueMatrix d N z = _
  rw [ouBandMatrix, ouGueMatrix, complex_smul_eq_real_smul, complex_smul_eq_real_smul]

private theorem continuous_ouMatrix (d : Dims) (N : ℕ) (s : ℝ) :
    Continuous fun z : Ω d × Ω d => ouMatrix d N s z := by
  have hfun : (fun z : Ω d × Ω d => ouMatrix d N s z)
      = fun z => ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2 :=
    funext (ouMatrix_eq_realSmul d N s)
  rw [hfun]
  exact continuous_ouMatrix_apply d N s

private theorem continuous_coordD2_ouMatrix (h : TestFun d N Φ) (s : ℝ)
    (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun z : Ω d × Ω d => coordD2 d N Φ (ouMatrix d N s z) p :=
  ((h.continuous_fderiv2.comp (continuous_ouMatrix d N s)).clm_apply
    continuous_const).clm_apply continuous_const

private theorem continuous_wirtSecond_ouMatrix (h : TestFun d N Φ) (s : ℝ) (i j : d.Idx N) :
    Continuous fun z : Ω d × Ω d => wirtSecond d N Φ (ouMatrix d N s z) i j := by
  unfold wirtSecond
  split
  · exact continuous_coordD2_ouMatrix h s (i, i, true)
  · exact ((continuous_coordD2_ouMatrix h s (i, j, true)).add
      (continuous_coordD2_ouMatrix h s (i, j, false))).const_smul (1 / 4 : ℝ)

/-- **The generator identity, `ouMatrix` form, for `RBM.Gauss.TestFun'`.**  The Hermitian bridge
of `Gauss/TestFunHerm.lean`: `ouMatrix d N s z` is always Hermitian, so the identity for the
global class `TestFun`, proved in §6 for `hermFun d N Φ`, transports to `Φ` itself. -/
private theorem ouProductMeasure_hasDerivAt_integral_pairs' (h : TestFun' d N Φ) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ z : Ω d × Ω d, Φ (ouMatrix d N s z) ∂(ouProductMeasure d N))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
          (RBM.centeredVarianceEntry d N a b : ℂ) *
            ∫ z : Ω d × Ω d, wirtSecond d N Φ (ouMatrix d N t z) a b
              ∂(ouProductMeasure d N)) t := by
  have key := ouProductMeasure_hasDerivAt_integral_pairs h.herm ht
  have hherm : ∀ (s : ℝ) (z : Ω d × Ω d),
      (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2).IsHermitian := by
    intro s z
    rw [← ouMatrix_eq_realSmul]
    exact ouMatrix_isHermitian d N s z
  have hval : ∀ (s : ℝ) (z : Ω d × Ω d),
      hermFun d N Φ (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2)
        = Φ (ouMatrix d N s z) := by
    intro s z
    rw [ouMatrix_eq_realSmul]
    exact hermFun_of_isHermitian (hherm s z)
  have hwirt : ∀ (z : Ω d × Ω d) (i j : d.Idx N),
      wirtSecond d N (hermFun d N Φ)
          (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) i j
        = wirtSecond d N Φ (ouMatrix d N t z) i j := by
    intro z i j
    rw [ouMatrix_eq_realSmul]
    exact wirtSecond_hermFun (hherm t z) (h.contDiffAt _ (hherm t z)) i j
  have hfun : (fun s : ℝ => ∫ z : Ω d × Ω d, hermFun d N Φ
        (ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2) ∂(ouProductMeasure d N))
      = fun s : ℝ => ∫ z : Ω d × Ω d, Φ (ouMatrix d N s z) ∂(ouProductMeasure d N) := by
    funext s
    exact integral_congr_ae (Eventually.of_forall fun z => hval s z)
  have hintwirt : ∀ a b : d.Idx N,
      (∫ z : Ω d × Ω d, wirtSecond d N (hermFun d N Φ)
          (ouBandCoeff t • Xmat d N z.1 + ouGueCoeff t • Xmat d N z.2) a b ∂(ouProductMeasure d N))
        = ∫ z : Ω d × Ω d, wirtSecond d N Φ (ouMatrix d N t z) a b ∂(ouProductMeasure d N) := by
    intro a b
    exact integral_congr_ae (Eventually.of_forall fun z => hwirt z a b)
  rw [hfun, Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl fun b _ => by
    rw [hintwirt a b])] at key
  exact key

/-- `ouCommonProjection` pushes the integral of any measurable function forward from
`ouCommonMeasure` to `ouProductMeasure`. -/
private theorem ouCommon_integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Dims) (N : ℕ) (g : Ω d × Ω d → E)
    (hg : AEStronglyMeasurable g (ouProductMeasure d N)) :
    ∫ ω, g (ouCommonProjection d N ω) ∂(ouCommonMeasure d) = ∫ z, g z ∂(ouProductMeasure d N) := by
  rw [← ouCommonProjection_map d N] at hg ⊢
  exact (integral_map (ouCommonProjection_measurable d N).aemeasurable hg).symm

end Bridge

/-! ## 8. The main results -/

/-- **The OU generator identity**, on the common carrier, for `TestFun'`. -/
theorem ouCommon_hasDerivAt_integral (d : Dims) (N : ℕ)
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun' d N Φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => ∫ ω, Φ (ouMatrix d N s (ouCommonProjection d N ω)) ∂(ouCommonMeasure d))
      ((-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
        (RBM.centeredVarianceEntry d N a b : ℂ) *
          ∫ ω, wirtSecond d N Φ (ouMatrix d N t (ouCommonProjection d N ω)) a b
            ∂(ouCommonMeasure d)) t := by
  have hbase := ouProductMeasure_hasDerivAt_integral_pairs' hΦ ht
  have hAS1 : ∀ s : ℝ, AEStronglyMeasurable (fun z : Ω d × Ω d => Φ (ouMatrix d N s z))
      (ouProductMeasure d N) := by
    intro s
    have heq : (fun z : Ω d × Ω d => Φ (ouMatrix d N s z))
        = fun z => hermFun d N Φ (ouMatrix d N s z) := by
      funext z
      exact (hermFun_of_isHermitian (ouMatrix_isHermitian d N s z)).symm
    rw [heq]
    exact (hΦ.herm.contDiff.continuous.comp (continuous_ouMatrix d N s)).aestronglyMeasurable
  have hAS2 : ∀ a b : d.Idx N, AEStronglyMeasurable
      (fun z : Ω d × Ω d => wirtSecond d N Φ (ouMatrix d N t z) a b) (ouProductMeasure d N) := by
    intro a b
    have heq : (fun z : Ω d × Ω d => wirtSecond d N Φ (ouMatrix d N t z) a b)
        = fun z => wirtSecond d N (hermFun d N Φ) (ouMatrix d N t z) a b := by
      funext z
      exact (wirtSecond_hermFun (ouMatrix_isHermitian d N t z)
        (hΦ.contDiffAt _ (ouMatrix_isHermitian d N t z)) a b).symm
    rw [heq]
    exact (continuous_wirtSecond_ouMatrix hΦ.herm t a b).aestronglyMeasurable
  have hfun : (fun s : ℝ => ∫ ω, Φ (ouMatrix d N s (ouCommonProjection d N ω))
        ∂(ouCommonMeasure d))
      = fun s : ℝ => ∫ z : Ω d × Ω d, Φ (ouMatrix d N s z) ∂(ouProductMeasure d N) :=
    funext fun s => ouCommon_integral_eq d N _ (hAS1 s)
  have hval : (∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ (ouMatrix d N t (ouCommonProjection d N ω)) a b
          ∂(ouCommonMeasure d))
      = ∑ a : d.Idx N, ∑ b : d.Idx N, (RBM.centeredVarianceEntry d N a b : ℂ) *
          ∫ z : Ω d × Ω d, wirtSecond d N Φ (ouMatrix d N t z) a b ∂(ouProductMeasure d N) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      rw [ouCommon_integral_eq d N _ (hAS2 a b)]
  rw [hfun, hval]
  exact hbase

/-! ## 9. Continuity at `t = 0` and the FTC corollary -/

section FTC

variable {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}

private theorem continuous_ouBandCoeff : Continuous ouBandCoeff := by
  unfold ouBandCoeff; fun_prop

private theorem continuous_ouGueCoeff : Continuous ouGueCoeff := by
  unfold ouGueCoeff ouZeta
  exact ((continuous_const.sub (Real.continuous_exp.comp continuous_neg))).sqrt

/-- `s ↦ ouMatrix d N s z` is continuous **everywhere**, including at `s = 0`: only its
`t`-derivative (via `ouGueCoeff`) is singular there. -/
private theorem continuous_ouMatrix_in_s (d : Dims) (N : ℕ) (z : Ω d × Ω d) :
    Continuous fun s : ℝ => ouMatrix d N s z := by
  have heq : (fun s : ℝ => ouMatrix d N s z)
      = fun s => ouBandCoeff s • Xmat d N z.1 + ouGueCoeff s • Xmat d N z.2 :=
    funext fun s => ouMatrix_eq_realSmul d N s z
  rw [heq]
  exact (continuous_ouBandCoeff.smul continuous_const).add
    (continuous_ouGueCoeff.smul continuous_const)

/-- **`s ↦ ∫ ω, Φ (ouMatrix d N s (ouCommonProjection d N ω)) ∂(ouCommonMeasure d)` is
continuous everywhere**, in particular at `s = 0` where it is not differentiable. -/
private theorem continuous_ouCommon_integral (hΦ : TestFun' d N Φ) :
    Continuous
      (fun s : ℝ => ∫ ω, Φ (ouMatrix d N s (ouCommonProjection d N ω)) ∂(ouCommonMeasure d)) := by
  have hval : ∀ (s : ℝ) (z : Ω d × Ω d),
      Φ (ouMatrix d N s z) = hermFun d N Φ (ouMatrix d N s z) := fun s z =>
    (hermFun_of_isHermitian (ouMatrix_isHermitian d N s z)).symm
  have hAS : ∀ s : ℝ, AEStronglyMeasurable (fun z : Ω d × Ω d => Φ (ouMatrix d N s z))
      (ouProductMeasure d N) := by
    intro s
    have heq : (fun z : Ω d × Ω d => Φ (ouMatrix d N s z))
        = fun z => hermFun d N Φ (ouMatrix d N s z) := funext (hval s)
    rw [heq]
    exact (hΦ.herm.contDiff.continuous.comp (continuous_ouMatrix d N s)).aestronglyMeasurable
  have hfun : (fun s : ℝ => ∫ ω, Φ (ouMatrix d N s (ouCommonProjection d N ω))
        ∂(ouCommonMeasure d))
      = fun s : ℝ => ∫ z : Ω d × Ω d, Φ (ouMatrix d N s z) ∂(ouProductMeasure d N) :=
    funext fun s => ouCommon_integral_eq d N _ (hAS s)
  rw [hfun]
  obtain ⟨C₀, hC₀⟩ := hΦ.herm.bdd₀
  refine continuous_of_dominated (fun s => hAS s) (fun s => Eventually.of_forall fun z => ?_)
    (integrable_const C₀) (Eventually.of_forall fun z => ?_)
  · rw [hval s z]
    exact hC₀ _
  · have heq : (fun s : ℝ => Φ (ouMatrix d N s z))
        = fun s => hermFun d N Φ (ouMatrix d N s z) := funext fun s => hval s z
    rw [heq]
    exact hΦ.herm.contDiff.continuous.comp (continuous_ouMatrix_in_s d N z)

/-- A crude but sufficient global bound on `wirtSecond`, for a fixed index pair. -/
private theorem exists_bound_wirtSecond (h : TestFun d N Φ) (a b : d.Idx N) :
    ∃ C : ℝ, ∀ M : Matrix (d.Idx N) (d.Idx N) ℂ, ‖wirtSecond d N Φ M a b‖ ≤ C := by
  obtain ⟨C₂, hC₂⟩ := h.bdd₂
  rcases eq_or_ne a b with rfl | hab
  · refine ⟨C₂ * ‖Bmat d N a a true‖ * ‖Bmat d N a a true‖, fun M => ?_⟩
    unfold wirtSecond
    rw [if_pos rfl]
    exact norm_coordD2_le hC₂ M (a, a, true)
  · refine ⟨(1 / 4 : ℝ) * (C₂ * ‖Bmat d N a b true‖ * ‖Bmat d N a b true‖
        + C₂ * ‖Bmat d N a b false‖ * ‖Bmat d N a b false‖), fun M => ?_⟩
    unfold wirtSecond
    rw [if_neg hab]
    calc ‖(1 / 4 : ℝ) • (coordD2 d N Φ M (a, b, true) + coordD2 d N Φ M (a, b, false))‖
        = (1 / 4 : ℝ) * ‖coordD2 d N Φ M (a, b, true) + coordD2 d N Φ M (a, b, false)‖ := by
          rw [norm_smul]; simp
      _ ≤ (1 / 4 : ℝ) * (‖coordD2 d N Φ M (a, b, true)‖ + ‖coordD2 d N Φ M (a, b, false)‖) := by
          gcongr
          exact norm_add_le _ _
      _ ≤ (1 / 4 : ℝ) * (C₂ * ‖Bmat d N a b true‖ * ‖Bmat d N a b true‖
            + C₂ * ‖Bmat d N a b false‖ * ‖Bmat d N a b false‖) := by
          gcongr
          · exact norm_coordD2_le hC₂ M _
          · exact norm_coordD2_le hC₂ M _

/-- `coordD2` composed with the OU line, as a function of `s` for a **fixed** sample: the
`s`-continuity companion to `continuous_coordD2_ouMatrix` (which fixes `s` and varies the
sample). -/
private theorem continuous_coordD2_ouMatrix_in_s (h : TestFun d N Φ) (z : Ω d × Ω d)
    (p : d.Idx N × d.Idx N × Bool) :
    Continuous fun s : ℝ => coordD2 d N Φ (ouMatrix d N s z) p :=
  ((h.continuous_fderiv2.comp (continuous_ouMatrix_in_s d N z)).clm_apply
    continuous_const).clm_apply continuous_const

/-- `wirtSecond` composed with the OU line, as a function of `s` for a fixed sample. -/
private theorem continuous_wirtSecond_ouMatrix_in_s (h : TestFun d N Φ) (z : Ω d × Ω d)
    (a b : d.Idx N) :
    Continuous fun s : ℝ => wirtSecond d N Φ (ouMatrix d N s z) a b := by
  unfold wirtSecond
  split
  · exact continuous_coordD2_ouMatrix_in_s h z (a, a, true)
  · exact ((continuous_coordD2_ouMatrix_in_s h z (a, b, true)).add
      (continuous_coordD2_ouMatrix_in_s h z (a, b, false))).const_smul (1 / 4 : ℝ)

/-- **`s ↦ ∫ ω, wirtSecond Φ (ouMatrix d N s (ouCommonProjection ω)) a b ∂(ouCommonMeasure d)` is
continuous everywhere.** -/
private theorem continuous_ouCommon_integral_wirtSecond (hΦ : TestFun' d N Φ) (a b : d.Idx N) :
    Continuous (fun s : ℝ => ∫ ω, wirtSecond d N Φ (ouMatrix d N s (ouCommonProjection d N ω)) a b
      ∂(ouCommonMeasure d)) := by
  have hval : ∀ (s : ℝ) (z : Ω d × Ω d), wirtSecond d N Φ (ouMatrix d N s z) a b
      = wirtSecond d N (hermFun d N Φ) (ouMatrix d N s z) a b := fun s z =>
    (wirtSecond_hermFun (ouMatrix_isHermitian d N s z)
      (hΦ.contDiffAt _ (ouMatrix_isHermitian d N s z)) a b).symm
  have hAS : ∀ s : ℝ, AEStronglyMeasurable
      (fun z : Ω d × Ω d => wirtSecond d N Φ (ouMatrix d N s z) a b) (ouProductMeasure d N) := by
    intro s
    have heq : (fun z : Ω d × Ω d => wirtSecond d N Φ (ouMatrix d N s z) a b)
        = fun z => wirtSecond d N (hermFun d N Φ) (ouMatrix d N s z) a b := funext (hval s)
    rw [heq]
    exact (continuous_wirtSecond_ouMatrix hΦ.herm s a b).aestronglyMeasurable
  have hfun : (fun s : ℝ => ∫ ω, wirtSecond d N Φ (ouMatrix d N s (ouCommonProjection d N ω)) a b
        ∂(ouCommonMeasure d))
      = fun s : ℝ =>
        ∫ z : Ω d × Ω d, wirtSecond d N Φ (ouMatrix d N s z) a b ∂(ouProductMeasure d N) :=
    funext fun s => ouCommon_integral_eq d N _ (hAS s)
  rw [hfun]
  obtain ⟨C, hC⟩ := exists_bound_wirtSecond hΦ.herm a b
  refine continuous_of_dominated (fun s => hAS s) (fun s => Eventually.of_forall fun z => ?_)
    (integrable_const C) (Eventually.of_forall fun z => ?_)
  · rw [hval s z]
    exact hC _
  · have heq : (fun s : ℝ => wirtSecond d N Φ (ouMatrix d N s z) a b)
        = fun s => wirtSecond d N (hermFun d N Φ) (ouMatrix d N s z) a b := funext fun s => hval s z
    rw [heq]
    exact continuous_wirtSecond_ouMatrix_in_s hΦ.herm z a b

/-- The continuity of `g`, needed for interval integrability. -/
private theorem continuous_g (hΦ : TestFun' d N Φ) :
    Continuous (fun t : ℝ => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
      (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ (ouMatrix d N t (ouCommonProjection d N ω)) a b
          ∂(ouCommonMeasure d)) := by
  have hc : Continuous fun t : ℝ => -(1 / 2 : ℝ) * Real.exp (-t) := by fun_prop
  have hs : Continuous fun t : ℝ => ∑ a : d.Idx N, ∑ b : d.Idx N,
      (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ (ouMatrix d N t (ouCommonProjection d N ω)) a b
          ∂(ouCommonMeasure d) :=
    continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      continuous_const.mul (continuous_ouCommon_integral_wirtSecond hΦ a b)
  exact hc.smul hs

/-- **The `t = 0` FTC form** of the generator identity. -/
theorem ouCommon_integral_sub_eq (d : Dims) (N : ℕ)
    {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : TestFun' d N Φ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, Φ (ouMatrix d N T (ouCommonProjection d N ω)) ∂(ouCommonMeasure d)) -
        ∫ ω, Φ (ouMatrix d N 0 (ouCommonProjection d N ω)) ∂(ouCommonMeasure d) =
      ∫ t in (0 : ℝ)..T, (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
        (RBM.centeredVarianceEntry d N a b : ℂ) *
          ∫ ω, wirtSecond d N Φ (ouMatrix d N t (ouCommonProjection d N ω)) a b
            ∂(ouCommonMeasure d) := by
  set F : ℝ → ℂ := fun s => ∫ ω, Φ (ouMatrix d N s (ouCommonProjection d N ω))
      ∂(ouCommonMeasure d) with hF
  set g : ℝ → ℂ := fun t => (-(1 / 2 : ℝ) * Real.exp (-t)) • ∑ a : d.Idx N, ∑ b : d.Idx N,
      (RBM.centeredVarianceEntry d N a b : ℂ) *
        ∫ ω, wirtSecond d N Φ (ouMatrix d N t (ouCommonProjection d N ω)) a b
          ∂(ouCommonMeasure d) with hg
  rcases eq_or_lt_of_le hT with hT0 | hT0
  · simp [← hT0]
  have hcont : ContinuousOn F (Set.Icc 0 T) := (continuous_ouCommon_integral hΦ).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt F (g t) t := fun t ht =>
    ouCommon_hasDerivAt_integral d N hΦ ht.1
  have hint : IntervalIntegrable g MeasureTheory.volume 0 T :=
    (continuous_g hΦ).intervalIntegrable 0 T
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT0.le hcont hderiv hint |>.symm

end FTC

/-! ## 10. `∏ Im m(z_i)` is a `TestFun'`

`TestFun'` asks for bounds on `‖DΦ‖` and `‖D²Φ‖` as operator norms over **all** real directions
at Hermitian matrices, not only Hermitian directions.  Near a Hermitian `x`, each factor is
`K ↦ ℓ(Ring.inverse (K - w))` with `ℓ = Im ∘ (|ι|⁻¹ tr)` real-linear; `Ring.inverse` is smooth on
the open set of units, `D inv(u) = -mulLeftRight u⁻¹ u⁻¹` (`fderiv_inverse`), and on the units
`D inv(y) = mulLeftRight (-y⁻¹) y⁻¹`, whose derivative is bounded by Mathlib's bilinear Leibniz
bound `ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear`, giving
`‖D^k inv(u)‖ ≤ ‖u⁻¹‖, ‖u⁻¹‖², 2‖u⁻¹‖³` for `k = 0, 1, 2`.  At Hermitian `x` with `Im w > 0`,
`‖(x - w)⁻¹‖ ≤ (Im w)⁻¹` (`norm_green_le`).  The finite product is handled by Mathlib's
`norm_iteratedFDerivWithin_prod_le` on the open set where every factor's shift is a unit, and the
lift to `ℂ` by `Complex.ofRealCLM`.  The negation is placed inside the first argument of
`mulLeftRight` so that no negation on the iterated operator space is ever needed. -/

section StieltjesTestFun

open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem ouGen_inv_norm_iter_one {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    ‖iteratedFDeriv ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ ≤
      ‖Ring.inverse u‖ * ‖Ring.inverse u‖ := by
  rw [norm_iteratedFDeriv_one]
  obtain ⟨v, rfl⟩ := hu
  rw [fderiv_inverse, norm_neg, ← Ring.inverse_unit]
  exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _

private theorem ouGen_inv_fderiv_eventually {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    fderiv ℝ (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) =ᶠ[𝓝 u]
      fun y => ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) (-Ring.inverse y)
        (Ring.inverse y) := by
  filter_upwards [Units.isOpen.mem_nhds hu] with y hy
  obtain ⟨v, rfl⟩ := hy
  rw [fderiv_inverse, Ring.inverse_unit]
  ext h : 1
  simp

private theorem ouGen_inv_norm_iter_two {u : Matrix ι ι ℂ} (hu : IsUnit u) :
    ‖iteratedFDeriv ℝ 2 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ ≤
      2 * (‖Ring.inverse u‖ * ‖Ring.inverse u‖ * ‖Ring.inverse u‖) := by
  set s : Set (Matrix ι ι ℂ) := {x | IsUnit x}
  have hs : IsOpen s := Units.isOpen
  have hcd : ContDiffOn ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) s := fun y hy => by
    obtain ⟨v, rfl⟩ := hy
    exact ((contDiffAt_ringInverse ℝ v).of_le (by exact_mod_cast le_top)).contDiffWithinAt
  have hcd' : ContDiffOn ℝ 1 (fun y : Matrix ι ι ℂ => -Ring.inverse y) s := hcd.neg
  rw [← norm_iteratedFDeriv_fderiv,
    ((ouGen_inv_fderiv_eventually hu).iteratedFDeriv ℝ 1).eq_of_nhds,
    ← iteratedFDerivWithin_of_isOpen 1 hs hu]
  have hB :=
    (ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ)).norm_iteratedFDerivWithin_le_of_bilinear
      hcd' hcd hs.uniqueDiffOn hu (n := 1) le_rfl
  refine hB.trans ?_
  refine le_trans (mul_le_of_le_one_left (by positivity) ?_) ?_
  · exact ContinuousLinearMap.opNorm_mulLeftRight_le ℝ (Matrix ι ι ℂ)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_one_right, Nat.cast_one, one_mul, zero_add, Nat.sub_zero]
  rw [iteratedFDerivWithin_of_isOpen 0 hs hu, iteratedFDerivWithin_of_isOpen 1 hs hu,
    iteratedFDerivWithin_of_isOpen 0 hs hu, iteratedFDerivWithin_of_isOpen 1 hs hu,
    norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero, norm_neg]
  have hneg : ‖iteratedFDeriv ℝ 1 (fun y : Matrix ι ι ℂ => -Ring.inverse y) u‖ =
      ‖iteratedFDeriv ℝ 1 (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ) u‖ := by
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, fderiv_fun_neg, norm_neg]
  rw [hneg]
  have h1 := ouGen_inv_norm_iter_one hu
  have h0 := norm_nonneg (Ring.inverse u)
  nlinarith [mul_le_mul_of_nonneg_left h1 h0]

/-- `K ↦ Im (|ι|⁻¹ tr K)`, the real-linear functional through which `Im m` factors. -/
private noncomputable def ouGen_stImCLM (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (Complex.imLm.comp (((Fintype.card ι : ℂ)⁻¹ • Matrix.traceLinearMap ι ℂ ℂ).restrictScalars ℝ))

private theorem ouGen_stieltjes_im_eq (K : Matrix ι ι ℂ) (w : ℂ) :
    (RBM.stieltjes K w).im = ouGen_stImCLM ι (Ring.inverse (K - w • (1 : Matrix ι ι ℂ))) := by
  simp [ouGen_stImCLM, RBM.stieltjes, RBM.green, Matrix.nonsing_inv_eq_ringInverse]

private theorem ouGen_contDiffAt_inv_shift {x : Matrix ι ι ℂ} {w : ℂ}
    (hx : IsUnit (x - w • (1 : Matrix ι ι ℂ))) :
    ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => Ring.inverse (K - w • (1 : Matrix ι ι ℂ))) x := by
  obtain ⟨v, hv⟩ := hx
  have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := 2) v
  rw [hv] at h
  exact h.comp x (contDiffAt_id.sub contDiffAt_const)

private theorem ouGen_contDiffAt_stieltjes_im {x : Matrix ι ι ℂ} {w : ℂ}
    (hx : IsUnit (x - w • (1 : Matrix ι ι ℂ))) :
    ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => (RBM.stieltjes K w).im) x := by
  have : (fun K : Matrix ι ι ℂ => (RBM.stieltjes K w).im) =
      ouGen_stImCLM ι ∘ fun K : Matrix ι ι ℂ => Ring.inverse (K - w • (1 : Matrix ι ι ℂ)) := by
    funext K; exact ouGen_stieltjes_im_eq K w
  rw [this]
  exact (ouGen_stImCLM ι).contDiff.contDiffAt.comp x (ouGen_contDiffAt_inv_shift hx)

/-- The derivatives of order `≤ 2` of one factor `Im m(w)`, at a Hermitian matrix, in every
real direction. -/
private theorem ouGen_norm_iteratedFDeriv_stieltjes_im_le {x : Matrix ι ι ℂ} (hx : x.IsHermitian)
    {w : ℂ} (hw : 0 < w.im) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun K : Matrix ι ι ℂ => (RBM.stieltjes K w).im) x‖ ≤
      ‖ouGen_stImCLM ι‖ * (w.im⁻¹ + w.im⁻¹ * w.im⁻¹ + 2 * (w.im⁻¹ * w.im⁻¹ * w.im⁻¹)) := by
  have hu : IsUnit (x - w • (1 : Matrix ι ι ℂ)) := isUnit_sub_smul_one_of_im_ne_zero hx hw.ne'
  have hg : ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ ≤ w.im⁻¹ := by
    have := norm_green_le hx hw (le_abs_self w.im)
    simpa [RBM.green, Matrix.nonsing_inv_eq_ringInverse] using this
  have h0 : 0 ≤ ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ := norm_nonneg _
  have hr : 0 ≤ w.im⁻¹ := inv_nonneg.mpr hw.le
  have : (fun K : Matrix ι ι ℂ => (RBM.stieltjes K w).im) =
      ouGen_stImCLM ι ∘ fun K : Matrix ι ι ℂ => Ring.inverse (K - w • (1 : Matrix ι ι ℂ)) := by
    funext K; exact ouGen_stieltjes_im_eq K w
  rw [this]
  refine ((ouGen_stImCLM ι).norm_iteratedFDeriv_comp_left (N := 2) (ouGen_contDiffAt_inv_shift hu)
    (by exact_mod_cast hk)).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [iteratedFDeriv_comp_sub]
  have hB : ‖iteratedFDeriv ℝ k (Ring.inverse : Matrix ι ι ℂ → Matrix ι ι ℂ)
      (x - w • (1 : Matrix ι ι ℂ))‖ ≤
      ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ +
        ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ * ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ +
        2 * (‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖ *
          ‖Ring.inverse (x - w • (1 : Matrix ι ι ℂ))‖) := by
    interval_cases k
    · rw [norm_iteratedFDeriv_zero]; nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
    · have := ouGen_inv_norm_iter_one hu; nlinarith [mul_nonneg (mul_nonneg h0 h0) h0]
    · have := ouGen_inv_norm_iter_two hu; nlinarith [mul_nonneg h0 h0]
  refine hB.trans ?_
  gcongr

/-- **`Φ = ∏ Im m(z_i)` lifted to `ℂ` has bounded derivatives of order `≤ 2` at Hermitian
matrices.** -/
private theorem ouGen_norm_iteratedFDeriv_stieltjesImProduct_le {m : ℕ} (z : Fin m → ℂ)
    (hz : ∀ i, 0 < (z i).im) {k : ℕ} (hk : k ≤ 2) :
    ∃ C : ℝ, ∀ x : Matrix ι ι ℂ, x.IsHermitian →
      ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => ((∏ i, (RBM.stieltjes K (z i)).im : ℝ) : ℂ)) x ∧
      ‖iteratedFDeriv ℝ k
        (fun K : Matrix ι ι ℂ => ((∏ i, (RBM.stieltjes K (z i)).im : ℝ) : ℂ)) x‖ ≤ C := by
  set β : Fin m → ℝ := fun i => ‖ouGen_stImCLM ι‖ *
    ((z i).im⁻¹ + (z i).im⁻¹ * (z i).im⁻¹ + 2 * ((z i).im⁻¹ * (z i).im⁻¹ * (z i).im⁻¹))
  refine ⟨‖Complex.ofRealCLM‖ * ∑ p ∈ (Finset.univ : Finset (Fin m)).sym k,
    ((p : Multiset (Fin m)).countPerms : ℝ) * ∏ j, β j, fun x hx => ?_⟩
  set s : Set (Matrix ι ι ℂ) := {K | ∀ i, IsUnit (K - z i • (1 : Matrix ι ι ℂ))}
  have hs : IsOpen s := by
    have : s = ⋂ i, (fun K : Matrix ι ι ℂ => K - z i • (1 : Matrix ι ι ℂ)) ⁻¹' {y | IsUnit y} := by
      ext K; simp [s]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      Units.isOpen.preimage (continuous_id.sub continuous_const)
  have hxs : x ∈ s := fun i => isUnit_sub_smul_one_of_im_ne_zero hx (hz i).ne'
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ContDiffOn ℝ 2 (fun K : Matrix ι ι ℂ => (RBM.stieltjes K (z i)).im) s :=
    fun i _ K hK => (ouGen_contDiffAt_stieltjes_im (hK i)).contDiffWithinAt
  have hP : ContDiffAt ℝ 2 (fun K : Matrix ι ι ℂ => ∏ i, (RBM.stieltjes K (z i)).im) x :=
    contDiffAt_prod fun i _ => ouGen_contDiffAt_stieltjes_im (hxs i)
  refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp x hP, ?_⟩
  have hcomp : (fun K : Matrix ι ι ℂ => ((∏ i, (RBM.stieltjes K (z i)).im : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ fun K : Matrix ι ι ℂ => ∏ i, (RBM.stieltjes K (z i)).im := rfl
  rw [hcomp]
  refine (Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (N := 2) hP (by exact_mod_cast hk)).trans
    (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [← iteratedFDerivWithin_of_isOpen k hs hxs]
  refine (norm_iteratedFDerivWithin_prod_le hfac hs.uniqueDiffOn hxs
    (by exact_mod_cast hk)).trans ?_
  refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
  have hcnt : Multiset.count j (p : Multiset (Fin m)) ≤ 2 :=
    ((Multiset.count_le_card _ _).trans_eq p.2).trans hk
  rw [iteratedFDerivWithin_of_isOpen _ hs hxs]
  exact ouGen_norm_iteratedFDeriv_stieltjes_im_le hx (hz j) hcnt

end StieltjesTestFun

/-- A product of imaginary parts of Stieltjes transforms at spectral
parameters in the upper half-plane is a `TestFun'`: bounds on the value and on the first and
second Fréchet derivatives, in every real direction, at every Hermitian matrix. -/
theorem testFun'_stieltjesImProduct (d : Dims) (N : ℕ) {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) :
    TestFun' d N (fun K => ((∏ i, (RBM.stieltjes K (z i)).im : ℝ) : ℂ)) := by
  obtain ⟨C0, hC0⟩ :=
    ouGen_norm_iteratedFDeriv_stieltjesImProduct_le (ι := d.Idx N) z hz (k := 0) (by norm_num)
  obtain ⟨C1, hC1⟩ :=
    ouGen_norm_iteratedFDeriv_stieltjesImProduct_le (ι := d.Idx N) z hz (k := 1) (by norm_num)
  obtain ⟨C2, hC2⟩ :=
    ouGen_norm_iteratedFDeriv_stieltjesImProduct_le (ι := d.Idx N) z hz (k := 2) le_rfl
  refine ⟨fun M hM => (hC0 M hM).1, ⟨C0, fun M hM => ?_⟩, ⟨C1, fun M hM => ?_⟩,
    ⟨C2, fun M hM => ?_⟩⟩
  · have h := (hC0 M hM).2
    rwa [norm_iteratedFDeriv_zero] at h
  · have h := (hC1 M hM).2
    rwa [norm_iteratedFDeriv_one] at h
  · have h := (hC2 M hM).2
    rwa [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h

end RBM.Gauss
