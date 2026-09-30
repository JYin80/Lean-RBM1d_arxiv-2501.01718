/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseGrid
import RBM1D.Gauss.GridMarkov

/-!
# The `Pgue` Markov toolkit

Reproduces, for the GUE-phase grid measure
`Pgue d` (`RBM.Gauss.GUEGrid.Pgue`), the freezing / conditional sub-Gaussianity toolkit that
`RBM1D/Gauss/GridMarkov.lean` provides for the band grid measure `Pg d`, plus a new general
freezing-based conditional sub-Gaussianity lemma and the entrywise truncation event used by the
discrete Duhamel/Azuma argument of `Flow/GUEPhaseDuhamel.lean`.

Route: the three results of `GridMarkov.lean`, copied with `P d → gueUnit d`,
`gvar d → gueUnitVar d`, `Pg d → Pgue d`.
-/

noncomputable section

namespace RBM.Gauss.GUEGrid

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss
open scoped NNReal ENNReal

variable {d : Dims}

/-! ### Private helpers: the `Pgue`-analogues of `GridMarkov.lean`'s `condExp_freeze` plumbing.
(The same private facts exist, unnamed outside their file, in `Flow/GUEPhaseStep.lean`;
reproduced here since `private` declarations are not visible across files, and the freezing
lemma is public here.) -/

section Freeze

private theorem gcpIndepIncr (k : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : Grid.Ωg d => ω (k + 1)) inferInstance) (Grid.filt d k)
      (Pgue d) := by
  have hI : iIndepFun (fun i : ℕ => (fun ω : Grid.Ωg d => ω i)) (Pgue d) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => (id : Ω d → Ω d)) (mX := fun _ => measurable_id)
  have hIndep : iIndep (fun n : ℕ => MeasurableSpace.comap (fun ω : Grid.Ωg d => ω n) inferInstance)
      (Pgue d) := (iIndepFun_iff_iIndep (fun _ : ℕ => (inferInstance : MeasurableSpace (Ω d)))
        (fun i ω => ω i) (Pgue d)).mp hI
  have hle : ∀ n : ℕ, MeasurableSpace.comap (fun ω : Grid.Ωg d => ω n) inferInstance
      ≤ (inferInstance : MeasurableSpace (Grid.Ωg d)) :=
    fun n => le_iSup (fun n => MeasurableSpace.comap (fun ω : Grid.Ωg d => ω n) inferInstance) n
  have hsplit := indep_biSup_compl hle hIndep (Set.Iic k)
  have hfilt : Grid.filt d k
      = ⨆ n ∈ Set.Iic k, MeasurableSpace.comap (fun ω : Grid.Ωg d => ω n) inferInstance := by
    have hshow : Grid.filt d k =
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
  have hmono : MeasurableSpace.comap (fun ω : Grid.Ωg d => ω (k + 1)) inferInstance
      ≤ ⨆ n ∈ (Set.Iic k)ᶜ, MeasurableSpace.comap (fun ω : Grid.Ωg d => ω n) inferInstance := by
    have hmem : (k + 1) ∈ (Set.Iic k)ᶜ := by simp
    exact le_biSup (fun n => MeasurableSpace.comap (fun ω : Grid.Ωg d => ω n) inferInstance) hmem
  exact indep_of_indep_of_le_left hsplit.symm hmono

private theorem gcpMapIncr (k : ℕ) :
    (Pgue d).map (fun ω : Grid.Ωg d => ω (k + 1)) = gueUnit d :=
  Measure.infinitePi_map_eval _ (k + 1)

/-- **T1 for `Pgue`, public: `gueCondExp_freeze`** (the public successor of
`GUEPhaseStep.lean`'s private `gueStep_condExp_freeze`). -/
theorem gueCondExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : Grid.Ωg d → β} (hY : Measurable[Grid.filt d k] Y)
    {F : β → Ω d → ℝ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | Grid.filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set μ : Measure (Grid.Ωg d) := Pgue d with hμdef
  set Z : Grid.Ωg d → Ω d := fun ω => ω (k + 1) with hZdef
  set Φ : Grid.Ωg d → β × Ω d := fun ω => (Y ω, Z ω) with hΦdef
  set ν : Measure (Ω d) := gueUnit d with hνdef
  set G : β → ℝ := fun y => ∫ x, F y x ∂ν with hGdef
  have hYmeas : Measurable Y := hY.mono ((Grid.filt d).le k) le_rfl
  have hZmeas : Measurable Z := measurable_pi_apply (k + 1)
  have hΦmeas : Measurable Φ := hYmeas.prodMk hZmeas
  have hFsm : StronglyMeasurable (fun p : β × Ω d => F p.1 p.2) := hF.stronglyMeasurable
  have hνmap : μ.map Z = ν := gcpMapIncr k
  have hindYZ : IndepFun Y Z μ := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ Grid.filt d k := hY.comap_le
    exact (indep_of_indep_of_le_right (gcpIndepIncr k) hcle).symm
  have hIntΦ : Integrable (fun p : β × Ω d => F p.1 p.2) (μ.map Φ) := by
    rw [integrable_map_measure hFsm.aestronglyMeasurable hΦmeas.aemeasurable]
    exact hInt
  have hprodglobal : μ.map Φ = (μ.map Y).prod ν := by
    rw [← hνmap]
    exact hindYZ.map_prod_eq_prod_map_map hYmeas.aemeasurable hZmeas.aemeasurable
  have hGmeas : StronglyMeasurable G := hFsm.integral_prod_right'
  have hkey : ∀ A : Set (Grid.Ωg d), MeasurableSet[Grid.filt d k] A →
      ∫ ω in A, F (Y ω) (Z ω) ∂μ = ∫ ω in A, G (Y ω) ∂μ := by
    intro A hA
    have hprodA : (μ.restrict A).map Φ = ((μ.restrict A).map Y).prod ν := by
      refine (Measure.prod_eq ?_).symm
      intro s t hs ht
      have hpre : Φ ⁻¹' (s ×ˢ t) = Y ⁻¹' s ∩ Z ⁻¹' t := by
        ext ω; simp [Φ, Set.mem_prod]
      rw [Measure.map_apply hΦmeas (hs.prod ht), Measure.map_apply hYmeas hs,
        Measure.restrict_apply (hΦmeas (hs.prod ht)), Measure.restrict_apply (hYmeas hs), hpre]
      have hrearrange : Y ⁻¹' s ∩ Z ⁻¹' t ∩ A = Z ⁻¹' t ∩ (A ∩ Y ⁻¹' s) := by
        ext ω; simp only [Set.mem_inter_iff]; tauto
      rw [hrearrange]
      have hASmem : MeasurableSet[Grid.filt d k] (A ∩ Y ⁻¹' s) := hA.inter (hY hs)
      have hZTmem : MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' t) :=
        ⟨t, ht, rfl⟩
      have hindep := (Indep_iff (MeasurableSpace.comap Z inferInstance) (Grid.filt d k) μ).1
        (gcpIndepIncr k) (Z ⁻¹' t) (A ∩ Y ⁻¹' s) hZTmem hASmem
      rw [hindep, ← Measure.map_apply hZmeas ht, hνmap, Set.inter_comm (Y ⁻¹' s) A]
      ring
    have hIntΦA : Integrable (fun p : β × Ω d => F p.1 p.2) ((μ.restrict A).map Φ) :=
      hIntΦ.mono_measure (Measure.map_mono Measure.restrict_le_self hΦmeas)
    calc
      ∫ ω in A, F (Y ω) (Z ω) ∂μ
          = ∫ p, F p.1 p.2 ∂((μ.restrict A).map Φ) :=
            (integral_map hΦmeas.aemeasurable hFsm.aestronglyMeasurable).symm
      _ = ∫ p, F p.1 p.2 ∂(((μ.restrict A).map Y).prod ν) := by rw [hprodA]
      _ = ∫ y, G y ∂((μ.restrict A).map Y) := integral_prod _ (hprodA ▸ hIntΦA)
      _ = ∫ ω in A, G (Y ω) ∂μ := integral_map hYmeas.aemeasurable hGmeas.aestronglyMeasurable
  have hIntG : Integrable G (μ.map Y) := by
    have hIntΦY : Integrable (fun p : β × Ω d => F p.1 p.2) ((μ.map Y).prod ν) :=
      hprodglobal ▸ hIntΦ
    exact hIntΦY.integral_prod_left
  have hGYint : Integrable (fun ω => G (Y ω)) μ :=
    (integrable_map_measure hGmeas.aestronglyMeasurable hYmeas.aemeasurable).mp hIntG
  have hGYmeas : StronglyMeasurable[Grid.filt d k] (fun ω => G (Y ω)) := hGmeas.comp_measurable hY
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((Grid.filt d).le k) hInt
    (fun s _ _ => hGYint.integrableOn) (fun s hs _ => (hkey s hs).symm)
    hGYmeas.aestronglyMeasurable).symm

end Freeze

/-! ### `gueHasCondSubgaussianMGF_of_frozen`: conditional sub-Gaussianity from a uniform-in-`y`
unconditional bound on the frozen family. -/

section OfFrozen

/-- **`gueHasCondSubgaussianMGF_of_frozen`**. -/
theorem gueHasCondSubgaussianMGF_of_frozen {β : Type*} [MeasurableSpace β]
    [StandardBorelSpace β] (k : ℕ) {Y : Grid.Ωg d → β} (hY : Measurable[Grid.filt d k] Y)
    {F : β → Ω d → ℝ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2)) {c : ℝ≥0}
    (hsub : ∀ y, HasSubgaussianMGF (F y) c (gueUnit d)) :
    HasCondSubgaussianMGF (Grid.filt d k) ((Grid.filt d).le k)
      (fun ω => F (Y ω) (ω (k + 1))) c (Pgue d) := by
  classical
  set hm := (Grid.filt d).le k
  have hYmeas : Measurable Y := hY.mono hm le_rfl
  have hUmeas : Measurable (fun ω : Grid.Ωg d => ω (k + 1)) := measurable_pi_apply (k + 1)
  have hindep : IndepFun (fun ω : Grid.Ωg d => ω (k + 1)) Y (Pgue d) := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ Grid.filt d k := hY.comap_le
    exact indep_of_indep_of_le_right (gcpIndepIncr k) hcle
  -- integrability of `exp (t * X)` for every real `t`, by Tonelli across the independent pair.
  have hintegrable : ∀ t : ℝ,
      Integrable (fun ω : Grid.Ωg d => Real.exp (t * F (Y ω) (ω (k + 1)))) (Pgue d) := by
    intro t
    set Fe : Ω d × β → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (t * F p.2 p.1)) with hFedef
    have hFe : Measurable Fe := by
      have h0 : Measurable (fun p : Ω d × β => F p.2 p.1) := hF.comp measurable_swap
      exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (h0.const_mul t))
    have hbound : ∀ y : β, (∫⁻ x, Fe (x, y) ∂(Pgue d).map (fun ω : Grid.Ωg d => ω (k + 1)))
        ≤ ENNReal.ofReal (Real.exp ((c : ℝ) * t ^ 2 / 2)) := by
      intro y
      rw [gcpMapIncr k]
      have hintY : Integrable (fun x => Real.exp (t * F y x)) (gueUnit d) :=
        (hsub y).integrable_exp_mul t
      have hofreal := ofReal_integral_eq_lintegral_ofReal hintY
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      have : (∫ x, Real.exp (t * F y x) ∂(gueUnit d)) = mgf (F y) (gueUnit d) t := rfl
      rw [hFedef]
      dsimp only
      rw [← hofreal, this]
      exact ENNReal.ofReal_le_ofReal ((hsub y).mgf_le t)
    have hlt := lintegral_indep_pair_le hUmeas hYmeas hindep hFe hbound
    refine ⟨?_, ?_⟩
    · have h1 : Measurable (fun ω : Grid.Ωg d => F (Y ω) (ω (k + 1))) := by
        have heq : (fun ω : Grid.Ωg d => F (Y ω) (ω (k + 1)))
            = (fun p : β × Ω d => F p.1 p.2) ∘ (fun ω => (Y ω, ω (k + 1))) := rfl
        rw [heq]
        exact hF.comp (hYmeas.prodMk hUmeas)
      exact (Real.measurable_exp.comp (h1.const_mul t)).aestronglyMeasurable
    · rw [hasFiniteIntegral_def]
      have heq : ∀ ω, ‖Real.exp (t * F (Y ω) (ω (k + 1)))‖ₑ = Fe (ω (k + 1), Y ω) := by
        intro ω
        rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFedef]
      simp_rw [heq]
      exact lt_of_le_of_lt hlt ENNReal.ofReal_lt_top
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro t
    rw [condExpKernel_comp_trim hm]
    exact hintegrable t
  · intro q
    set t : ℝ := (q : ℝ) with htdef
    set X : Grid.Ωg d → ℝ := fun ω => F (Y ω) (ω (k + 1)) with hXdef
    set Gr : Grid.Ωg d → ℝ := fun ω => Real.exp (t * X ω) with hGrdef
    set Fr : β → Ω d → ℝ := fun y x => Real.exp (t * F y x) with hFrdef
    have hFrmeas : Measurable (fun p : β × Ω d => Fr p.1 p.2) :=
      Real.measurable_exp.comp (hF.const_mul t)
    have hGreq : (fun ω : Grid.Ωg d => Fr (Y ω) (ω (k + 1))) = Gr := by
      funext ω; rw [hFrdef, hGrdef, hXdef]
    have hIntGr : Integrable Gr (Pgue d) := hintegrable t
    have hfreeze := gueCondExp_freeze k hY hFrmeas (hGreq ▸ hIntGr)
    have hRHS : (fun ω : Grid.Ωg d => ∫ x, Fr (Y ω) x ∂(gueUnit d))
        = fun ω => mgf (F (Y ω)) (gueUnit d) t := rfl
    rw [hRHS, hGreq] at hfreeze
    have hsm1 : StronglyMeasurable[Grid.filt d k] ((Pgue d)[Gr | Grid.filt d k]) :=
      stronglyMeasurable_condExp
    have hsm2 : StronglyMeasurable[Grid.filt d k] (fun ω => mgf (F (Y ω)) (gueUnit d) t) := by
      have hFrsm : StronglyMeasurable (fun p : β × Ω d => Fr p.1 p.2) := hFrmeas.stronglyMeasurable
      have hGmeas : StronglyMeasurable (fun y => ∫ x, Fr y x ∂(gueUnit d)) :=
        hFrsm.integral_prod_right'
      exact hGmeas.comp_measurable hY
    have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
    have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
    have hcomb : ∀ᵐ ρ ∂(Pgue d).trim hm,
        (∫ σ, Gr σ ∂condExpKernel (Pgue d) (Grid.filt d k) ρ) = mgf (F (Y ρ)) (gueUnit d) t := by
      filter_upwards [hbridge, htrim] with ρ h1 h2
      rw [← h1, h2]
    filter_upwards [hcomb] with ρ hρ
    change (∫ σ, Gr σ ∂condExpKernel (Pgue d) (Grid.filt d k) ρ) ≤ Real.exp ((c : ℝ) * t ^ 2 / 2)
    rw [hρ, htdef]
    exact (hsub (Y ρ)).mgf_le _

end OfFrozen

/-! ### `vGue`, `gueMap_lin_Xmat`: the law of a frozen linear functional under `gueUnit d`.
The deterministic plumbing (`Grid.lin`, `Grid.coordFinset`, `Grid.lin_Xmat_eq_sum`) is public and
measure-free, reused verbatim; only the two facts tying `gueUnit d` to `Coord d`
(independence, per-coordinate law) are new. -/

section LinearVariance

private theorem gcpUnitMapEval (c : Coord d) :
    (gueUnit d).map (fun ω : Ω d => ω c) = gaussianReal 0 (gueUnitVar d c) :=
  Measure.infinitePi_map_eval _ c

private theorem gcpUnitIIndepFun :
    iIndepFun (fun (c : Coord d) (ω : Ω d) => ω c) (gueUnit d) := by
  have := iIndepFun_infinitePi (P := fun c : Coord d => gaussianReal 0 (gueUnitVar d c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [gueUnit] using this

variable (d) in
/-- **`vGue`**: the conditional variance of a frozen linear functional under `gueUnit d`,
in the direction `A`. -/
def vGue (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ≥0 :=
  linVar (gueUnitVar d) (fun c => Grid.lin (d := d) N A (Xmat d N (Pi.single c 1)))
    (Grid.coordFinset (d := d) N)

/-- **`gueMap_lin_Xmat`**: the law of a frozen linear functional. -/
theorem gueMap_lin_Xmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (gueUnit d).map (fun y => Grid.lin (d := d) N A (Xmat d N y)) =
      gaussianReal 0 (vGue d N A) := by
  classical
  have hfun : (fun y : Ω d => Grid.lin (d := d) N A (Xmat d N y))
      = fun y => ∑ c ∈ Grid.coordFinset (d := d) N,
          (Grid.lin (d := d) N A (Xmat d N (Pi.single c 1))) * y c := by
    funext y
    rw [Grid.lin_Xmat_eq_sum]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hfun]
  have hsum := map_sum_const_mul_of_indep (P := gueUnit d)
    (X := fun (c : Coord d) (ω : Ω d) => ω c) (v := gueUnitVar d)
    (fun c => measurable_pi_apply c) gcpUnitMapEval gcpUnitIIndepFun
    (fun c => Grid.lin (d := d) N A (Xmat d N (Pi.single c 1))) (Grid.coordFinset (d := d) N)
  rw [hsum]
  rfl

end LinearVariance

/-! ### `gueHasCondSubgaussianMGF_linear`: the `Pgue`-analogue of `GridMarkov.lean`'s T2/T3
pointwise-bound route (its private `measurable_lin_uncurry`, `mgf_lin_Xmat`,
`integrable_exp_mul_X`, `condMGF_le`), reproduced here (those helpers are private in a
different file) with `P d → gueUnit d`, `gvar d → gueUnitVar d`, `Pg d → Pgue d`, `v → vGue`,
and using this file's own `gueCondExp_freeze` for the freezing step. -/

section LinearMGF

private theorem gcpLinEqSum (N : ℕ) (A X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Grid.lin (d := d) N A X = ∑ i : d.Idx N, ∑ k : d.Idx N, (A i k * X k i).re := by
  unfold Grid.lin
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem gcpMeasurableLinUncurry (N : ℕ) :
    Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      Grid.lin (d := d) N p.1 (Xmat d N p.2)) := by
  have heq : (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
        Grid.lin (d := d) N p.1 (Xmat d N p.2))
      = fun p => ∑ i : d.Idx N, ∑ k' : d.Idx N, (p.1 i k' * Xmat d N p.2 k' i).re :=
    funext fun p => gcpLinEqSum N p.1 (Xmat d N p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
  have hM : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => p.1 i k') :=
    Measurable.eval_matrix (i := i) (j := k') measurable_fst
  have hX : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => Xmat d N p.2 k' i) :=
    Measurable.eval_matrix (i := k') (j := i) ((measurable_Xmat d N).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem gcpMeasurableLinLeft (N : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Measurable (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => Grid.lin (d := d) N A M) := by
  have heq : (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => Grid.lin (d := d) N A M)
      = fun A => ∑ i : d.Idx N, ∑ k' : d.Idx N, (A i k' * M k' i).re :=
    funext fun A => gcpLinEqSum N A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k')).mul measurable_const)

private theorem gcpMeasurableLinXmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Measurable (fun x : Ω d => Grid.lin (d := d) N A (Xmat d N x)) := by
  have heq : (fun x : Ω d => Grid.lin (d := d) N A (Xmat d N x))
      = fun x => ∑ i : d.Idx N, ∑ k' : d.Idx N, (A i k' * Xmat d N x k' i).re :=
    funext fun x => gcpLinEqSum N A (Xmat d N x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k') (j := i) (measurable_Xmat d N)))

private theorem gcpVGueEqSum (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (vGue d N A : ℝ) = ∑ c ∈ Grid.coordFinset (d := d) N,
      (Grid.lin (d := d) N A (Xmat d N (Pi.single c 1))) ^ 2 * (gueUnitVar d c : ℝ) := by
  unfold vGue linVar
  push_cast [NNReal.coe_mk]
  rfl

private theorem gcpMeasurableVGue (N : ℕ) :
    Measurable (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => (vGue d N A : ℝ)) := by
  have heq : (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => (vGue d N A : ℝ))
      = fun A => ∑ c ∈ Grid.coordFinset (d := d) N,
          (Grid.lin (d := d) N A (Xmat d N (Pi.single c 1))) ^ 2 * (gueUnitVar d c : ℝ) :=
    funext (gcpVGueEqSum N)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ => ((gcpMeasurableLinLeft N _).pow_const 2).mul_const _

private theorem gcpMgfLinXmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) (r : ℝ) :
    mgf (fun x => Grid.lin (d := d) N A (Xmat d N x)) (gueUnit d) r
      = Real.exp ((vGue d N A : ℝ) * r ^ 2 / 2) := by
  have hlaw : HasLaw (fun x => Grid.lin (d := d) N A (Xmat d N x))
      (gaussianReal 0 (vGue d N A)) (gueUnit d) :=
    ⟨(gcpMeasurableLinXmat N A).aemeasurable, gueMap_lin_Xmat N A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  ring

private theorem gcpIntegrableExpLinXmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * Grid.lin (d := d) N A (Xmat d N x))) (gueUnit d) := by
  have h : Integrable (fun x : ℝ => Real.exp (r * x))
      ((gueUnit d).map (fun x => Grid.lin (d := d) N A (Xmat d N x))) := by
    rw [gueMap_lin_Xmat N A]; exact integrable_exp_mul_gaussianReal r
  exact (integrable_map_measure h.aestronglyMeasurable (gcpMeasurableLinXmat N A).aemeasurable).1 h

private theorem gcpLinZero (N : ℕ) (X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Grid.lin (d := d) N 0 X = 0 := by unfold Grid.lin; simp

private theorem gcpVGueZero (N : ℕ) : vGue d N (0 : Matrix (d.Idx N) (d.Idx N) ℂ) = 0 := by
  unfold vGue linVar; simp [gcpLinZero]

private instance gcpStandardBorelMatrix (N : ℕ) :
    StandardBorelSpace (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  inferInstanceAs (StandardBorelSpace (d.Idx N → d.Idx N → ℂ))

section MGFBound

variable {N k : ℕ} {A : Grid.Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ}

private theorem gcpIntegrableExpMulX (hA : Measurable[Grid.filt d k] A) {s c : ℝ} (_hc : 0 ≤ c)
    (hAs : ∀ ω, s ^ 2 * (vGue d N (A ω) : ℝ) ≤ c) (r : ℝ) :
    Integrable (fun ω : Grid.Ωg d =>
      Real.exp (r * (s * Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1)))))) (Pgue d) := by
  classical
  set U : Grid.Ωg d → Ω d := fun ω => ω (k + 1) with hUdef
  set F : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp ((r * s) * Grid.lin (d := d) N p.2
      (Xmat d N p.1))) with hFdef
  have hUmeas : Measurable U := measurable_pi_apply (k + 1)
  have hAmeas : Measurable A := hA.mono ((Grid.filt d).le k) le_rfl
  have hindep : IndepFun U A (Pgue d) := by
    have hcle : MeasurableSpace.comap A inferInstance ≤ Grid.filt d k := hA.comap_le
    exact indep_of_indep_of_le_right (gcpIndepIncr k) hcle
  have hFmeas : Measurable F := by
    have h0 : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ =>
        Grid.lin (d := d) N p.2 (Xmat d N p.1)) := by
      have heq : (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ =>
            Grid.lin (d := d) N p.2 (Xmat d N p.1))
          = fun p => ∑ i : d.Idx N, ∑ k' : d.Idx N, (p.2 i k' * Xmat d N p.1 k' i).re :=
        funext fun p => gcpLinEqSum N p.2 (Xmat d N p.1)
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
      have hM : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ => p.2 i k') :=
        Measurable.eval_matrix (i := i) (j := k') measurable_snd
      have hX : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ => Xmat d N p.1 k' i) :=
        Measurable.eval_matrix (i := k') (j := i) ((measurable_Xmat d N).comp measurable_fst)
      exact Complex.measurable_re.comp (hM.mul hX)
    have h1 : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (r * s) * Grid.lin (d := d) N p.2 (Xmat d N p.1)) := h0.const_mul _
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1)
  have hkey := lintegral_indep_pair hUmeas hAmeas hindep hFmeas
  rw [gcpMapIncr k] at hkey
  have hinner : ∀ y : Matrix (d.Idx N) (d.Idx N) ℂ,
      (∫⁻ x, F (x, y) ∂(gueUnit d)) =
        ENNReal.ofReal (Real.exp ((vGue d N y : ℝ) * (r * s) ^ 2 / 2)) := by
    intro y
    have hint := gcpIntegrableExpLinXmat N y (r * s)
    have hofreal := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hmgf := gcpMgfLinXmat N y (r * s)
    rw [mgf] at hmgf
    rw [hFdef]
    dsimp only
    rw [← hofreal, hmgf]
  have hp : MeasurableSet {y : Matrix (d.Idx N) (d.Idx N) ℂ |
      (vGue d N y : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2} :=
    measurableSet_le (((gcpMeasurableVGue N).mul_const _).div_const _) measurable_const
  have hptwise : ∀ ω, (vGue d N (A ω) : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    intro ω
    have h2 := hAs ω
    nlinarith [sq_nonneg r]
  have hae : ∀ᵐ y ∂(Pgue d).map A, (vGue d N y : ℝ) * (r * s) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    rw [ae_map_iff hAmeas.aemeasurable hp]
    exact Filter.Eventually.of_forall hptwise
  have houter_eq : ∫⁻ ω, F (U ω, A ω) ∂(Pgue d)
      = ∫⁻ y, ENNReal.ofReal (Real.exp ((vGue d N y : ℝ) * (r * s) ^ 2 / 2))
          ∂((Pgue d).map A) := by
    rw [hkey]; exact lintegral_congr hinner
  have houter_le : ∫⁻ ω, F (U ω, A ω) ∂(Pgue d) ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
    rw [houter_eq]
    calc ∫⁻ y, ENNReal.ofReal (Real.exp ((vGue d N y : ℝ) * (r * s) ^ 2 / 2))
          ∂((Pgue d).map A)
        ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) ∂((Pgue d).map A) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hy)
      _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pgue d).map A) Set.univ := by
          rw [lintegral_const]
      _ ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
          calc ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pgue d).map A) Set.univ
              ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * 1 := by
                gcongr
                exact prob_le_one
            _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := mul_one _
  refine ⟨?_, ?_⟩
  · have hXmeas : Measurable (fun ω : Grid.Ωg d =>
        Real.exp (r * (s * Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1)))))) := by
      have h1 : Measurable (fun ω : Grid.Ωg d =>
          Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1)))) := by
        have heq : (fun ω : Grid.Ωg d => Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1))))
            = fun ω => ∑ i : d.Idx N, ∑ k' : d.Idx N,
              (A ω i k' * Xmat d N (ω (k + 1)) k' i).re :=
          funext fun ω => gcpLinEqSum N (A ω) (Xmat d N (ω (k + 1)))
        rw [heq]
        refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
        have hM : Measurable (fun ω : Grid.Ωg d => A ω i k') := Measurable.eval_matrix hAmeas
        have hX : Measurable (fun ω : Grid.Ωg d => Xmat d N (ω (k + 1)) k' i) :=
          Measurable.eval_matrix ((measurable_Xmat d N).comp hUmeas)
        exact Complex.measurable_re.comp (hM.mul hX)
      exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
    exact hXmeas.aestronglyMeasurable
  · rw [hasFiniteIntegral_def]
    have heq : ∀ ω, ‖Real.exp (r * (s *
        Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1)))))‖ₑ = F (U ω, A ω) := by
      intro ω
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFdef]
      dsimp only
      congr 2
      ring
    simp_rw [heq]
    exact lt_of_le_of_lt houter_le ENNReal.ofReal_lt_top

private theorem gcpCondMGFLe (hA : Measurable[Grid.filt d k] A) {s c : ℝ} (hc : 0 ≤ c)
    (hAs : ∀ ω, s ^ 2 * (vGue d N (A ω) : ℝ) ≤ c) (r : ℝ) :
    ∀ᵐ ω ∂((Pgue d).trim ((Grid.filt d).le k)),
      mgf (fun ρ => s * Grid.lin (d := d) N (A ρ) (Xmat d N (ρ (k + 1))))
        (condExpKernel (Pgue d) (Grid.filt d k) ω) r ≤ Real.exp (c * r ^ 2 / 2) := by
  classical
  set X : Grid.Ωg d → ℝ := fun ρ => s * Grid.lin (d := d) N (A ρ)
    (Xmat d N (ρ (k + 1))) with hXdef
  set Gr : Grid.Ωg d → ℝ := fun ρ => Real.exp (r * X ρ) with hGrdef
  set Fr : Matrix (d.Idx N) (d.Idx N) ℂ → Ω d → ℝ :=
    fun y x => Real.exp (r * (s * Grid.lin (d := d) N y (Xmat d N x))) with hFrdef
  have hFrmeas : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => Fr p.1 p.2) := by
    have h1 : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
        Grid.lin (d := d) N p.1 (Xmat d N p.2)) := gcpMeasurableLinUncurry N
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : Grid.Ωg d => Fr (A ρ) (ρ (k + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef, hXdef]
  have hIntGr : Integrable Gr (Pgue d) := gcpIntegrableExpMulX hA hc hAs r
  have hfreeze := gueCondExp_freeze k hA hFrmeas (hGreq ▸ hIntGr)
  have hRHS : (fun ρ : Grid.Ωg d => ∫ x, Fr (A ρ) x ∂(gueUnit d))
      = fun ρ => Real.exp ((vGue d N (A ρ) : ℝ) * (r * s) ^ 2 / 2) := by
    funext ρ
    have hmgf := gcpMgfLinXmat N (A ρ) (r * s)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x
        = Real.exp ((r * s) * Grid.lin (d := d) N (A ρ) (Xmat d N x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  have hm : Grid.filt d k ≤ (inferInstance : MeasurableSpace (Grid.Ωg d)) := (Grid.filt d).le k
  have hsm1 : StronglyMeasurable[Grid.filt d k] ((Pgue d)[Gr | Grid.filt d k]) :=
    stronglyMeasurable_condExp
  have hsm2 : StronglyMeasurable[Grid.filt d k]
      (fun ρ => Real.exp ((vGue d N (A ρ) : ℝ) * (r * s) ^ 2 / 2)) := by
    have hcont : Measurable (fun y : Matrix (d.Idx N) (d.Idx N) ℂ =>
        Real.exp ((vGue d N y : ℝ) * (r * s) ^ 2 / 2)) :=
      Real.measurable_exp.comp (((gcpMeasurableVGue N).mul_const _).div_const _)
    exact (hcont.comp hA).stronglyMeasurable
  have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
  have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
  have hcomb : ∀ᵐ ρ ∂(Pgue d).trim hm,
      (∫ σ, Gr σ ∂condExpKernel (Pgue d) (Grid.filt d k) ρ)
        = Real.exp ((vGue d N (A ρ) : ℝ) * (r * s) ^ 2 / 2) := by
    filter_upwards [hbridge, htrim] with ρ h1 h2
    rw [← h1, h2]
  filter_upwards [hcomb] with ρ hρ
  change (∫ σ, Gr σ ∂condExpKernel (Pgue d) (Grid.filt d k) ρ) ≤ Real.exp (c * r ^ 2 / 2)
  rw [hρ]
  apply Real.exp_le_exp.2
  have h2 := hAs ρ
  nlinarith [sq_nonneg r]

end MGFBound

/-- **T2/T3 for `Pgue`: `gueHasCondSubgaussianMGF_linear`**. -/
theorem gueHasCondSubgaussianMGF_linear (N k : ℕ) (s : ℝ)
    {A : Grid.Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ} (hA : Measurable[Grid.filt d k] A)
    (E : Set (Grid.Ωg d)) (hE : MeasurableSet[Grid.filt d k] E) (c : ℝ≥0)
    (hbound : ∀ ω ∈ E, s ^ 2 * (vGue d N (A ω) : ℝ) ≤ c) :
    HasCondSubgaussianMGF (Grid.filt d k) ((Grid.filt d).le k)
      (fun ω => E.indicator (fun ω => s * Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1)))) ω)
      c (Pgue d) := by
  classical
  have hc : (0 : ℝ) ≤ (c : ℝ) := c.coe_nonneg
  set A' : Grid.Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ := fun ω => if ω ∈ E then A ω else 0
    with hA'def
  have hA'meas : Measurable[Grid.filt d k] A' :=
    Measurable.ite (p := fun ω => ω ∈ E) hE hA measurable_const
  have hAs : ∀ ω, s ^ 2 * (vGue d N (A' ω) : ℝ) ≤ c := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [hA'def, hω] using hbound ω hω
    · simp only [hA'def, hω, ite_false, gcpVGueZero, NNReal.coe_zero, mul_zero]
      exact hc
  have hXeq : (fun ω => E.indicator
      (fun ω => s * Grid.lin (d := d) N (A ω) (Xmat d N (ω (k + 1)))) ω)
      = fun ω => s * Grid.lin (d := d) N (A' ω) (Xmat d N (ω (k + 1))) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp [Set.indicator, hω, hA'def]
    · simp [Set.indicator, hω, hA'def, gcpLinZero]
  rw [hXeq]
  change Kernel.HasSubgaussianMGF (fun ω => s * Grid.lin (d := d) N (A' ω) (Xmat d N (ω (k + 1))))
    c (condExpKernel (Pgue d) (Grid.filt d k)) ((Pgue d).trim ((Grid.filt d).le k))
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro r
    rw [condExpKernel_comp_trim ((Grid.filt d).le k)]
    exact gcpIntegrableExpMulX hA'meas hc hAs r
  · intro q
    exact gcpCondMGFLe hA'meas hc hAs (q : ℝ)

end LinearMGF

/-! ### `gue_highProb_incr_le`: the entrywise truncation event. -/

section Truncation

/-- If every raw coordinate of `y` read at size `N` is `≤ t` in absolute value, every entry of
`Xmat d N y` is `≤ 2t` in norm (triangle inequality on the two coordinates `Xentry` reads; the
third, diagonal case needs only one of them, plus `t ≥ 0` from the other). -/
private theorem gcpNormXentryLe (N : ℕ) (y : Ω d) (i j : d.Idx N) {t : ℝ}
    (h : ∀ c ∈ Grid.coordFinset (d := d) N, |y c| ≤ t) : ‖Xentry d N y i j‖ ≤ 2 * t := by
  have hmem : ∀ a b : d.Idx N, ∀ bl : Bool,
      (⟨N, a, b, bl⟩ : Coord d) ∈ Grid.coordFinset (d := d) N :=
    fun a b bl => (Grid.mem_coordFinset N _).2 rfl
  unfold Xentry
  split_ifs with h1 h2
  · calc ‖(y (⟨N, i, j, true⟩ : Coord d) : ℂ) + Complex.I * (y (⟨N, i, j, false⟩ : Coord d) : ℂ)‖
        ≤ ‖(y (⟨N, i, j, true⟩ : Coord d) : ℂ)‖
          + ‖Complex.I * (y (⟨N, i, j, false⟩ : Coord d) : ℂ)‖ := norm_add_le _ _
      _ = |y (⟨N, i, j, true⟩ : Coord d)| + |y (⟨N, i, j, false⟩ : Coord d)| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ t + t := add_le_add (h _ (hmem i j true)) (h _ (hmem i j false))
      _ = 2 * t := by ring
  · calc ‖(y (⟨N, j, i, true⟩ : Coord d) : ℂ) - Complex.I * (y (⟨N, j, i, false⟩ : Coord d) : ℂ)‖
        ≤ ‖(y (⟨N, j, i, true⟩ : Coord d) : ℂ)‖
          + ‖Complex.I * (y (⟨N, j, i, false⟩ : Coord d) : ℂ)‖ := norm_sub_le _ _
      _ = |y (⟨N, j, i, true⟩ : Coord d)| + |y (⟨N, j, i, false⟩ : Coord d)| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ t + t := add_le_add (h _ (hmem j i true)) (h _ (hmem j i false))
      _ = 2 * t := by ring
  · have h1 := h _ (hmem i j true)
    have h2 := h _ (hmem i j false)
    have ht0 : (0 : ℝ) ≤ t := (abs_nonneg _).trans h2
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith

end Truncation

/-! ### The Gaussian tail bound and the exponential-beats-polynomial fact used to turn the
per-coordinate bound into `HighProb`. -/

section Tail

private theorem gcpHasSubgaussianMGFId (v : ℝ≥0) :
    HasSubgaussianMGF (fun x : ℝ => x) v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    have hlaw : HasLaw (fun x : ℝ => x) (gaussianReal 0 v) (gaussianReal (0 : ℝ) v) :=
      ⟨measurable_id.aemeasurable, by
        rw [show (fun x : ℝ => x) = id from rfl]; exact Measure.map_id⟩
    rw [mgf_gaussianReal hlaw]
    simp

/-- The two-sided Gaussian tail bound: for a centred Gaussian of variance `v ≤ 1`, the probability
of exceeding `t ≥ 0` in absolute value is `≤ 2 exp(-t²/2)`. -/
private theorem gcpGaussianTailLe {v : ℝ≥0} (hv0 : 0 < (v : ℝ)) (hv1 : (v : ℝ) ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) :
    (gaussianReal 0 v) {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := by
  have hsub : HasSubgaussianMGF (fun x : ℝ => x) v (gaussianReal 0 v) := gcpHasSubgaussianMGFId v
  have hexple : Real.exp (-(t ^ 2) / (2 * (v : ℝ))) ≤ Real.exp (-(t ^ 2) / 2) := by
    apply Real.exp_le_exp.2
    have hden : (0 : ℝ) < 2 * (v : ℝ) := by positivity
    have hle : (2 : ℝ) * (v : ℝ) ≤ 2 := by linarith
    have hkey : t ^ 2 / 2 ≤ t ^ 2 / (2 * (v : ℝ)) :=
      div_le_div_of_nonneg_left (sq_nonneg t) hden hle
    rw [neg_div, neg_div]
    linarith
  have h1 : (gaussianReal 0 v).real {x : ℝ | t ≤ x} ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) :=
    hsub.measure_ge_le ht
  have h2 : (gaussianReal 0 v).real {x : ℝ | t ≤ -x} ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) := by
    have h2' := hsub.neg.measure_ge_le ht
    simpa using h2'
  have hsub' : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases le_total 0 x with hx0 | hx0
    · have heq : |x| = x := abs_of_nonneg hx0
      exact Or.inl (le_of_lt (heq ▸ hx))
    · have heq : |x| = -x := abs_of_nonpos hx0
      exact Or.inr (le_of_lt (heq ▸ hx))
  have hreal : (gaussianReal 0 v).real {x : ℝ | t < |x|} ≤ 2 * Real.exp (-(t ^ 2) / 2) := by
    calc (gaussianReal 0 v).real {x : ℝ | t < |x|}
        ≤ (gaussianReal 0 v).real ({x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x}) :=
          measureReal_mono hsub'
      _ ≤ (gaussianReal 0 v).real {x : ℝ | t ≤ x} + (gaussianReal 0 v).real {x : ℝ | t ≤ -x} :=
          measureReal_union_le _ _
      _ ≤ Real.exp (-(t ^ 2) / (2 * (v : ℝ))) + Real.exp (-(t ^ 2) / (2 * (v : ℝ))) :=
          add_le_add h1 h2
      _ ≤ Real.exp (-(t ^ 2) / 2) + Real.exp (-(t ^ 2) / 2) := add_le_add hexple hexple
      _ = 2 * Real.exp (-(t ^ 2) / 2) := by ring
  calc (gaussianReal 0 v) {x : ℝ | t < |x|}
      = ENNReal.ofReal ((gaussianReal 0 v).real {x : ℝ | t < |x|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := ENNReal.ofReal_le_ofReal hreal

/-- The Gaussian tail `2 exp(-N²/8)` beats every polynomial `N^{-D'}`. -/
private theorem gcpEventuallyExpBeatsRpow (D' : ℝ) :
    ∀ᶠ N : ℕ in atTop, 2 * Real.exp (-((N : ℝ) ^ 2) / 8) ≤ (N : ℝ) ^ (-D') := by
  have hz : Filter.Tendsto (fun u : ℝ => u ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * u)) atTop
      (nhds 0) := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D' / 2 + 1) (1 / 8) (by norm_num)
  have hsq : Filter.Tendsto (fun x : ℝ => x ^ (2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hN : Filter.Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcomp : Filter.Tendsto (fun N : ℕ =>
      ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * (N : ℝ) ^ (2 : ℝ))) atTop
      (nhds 0) := hz.comp (hsq.comp hN)
  have hev : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) * Real.exp (-(1 / 8) * (N : ℝ) ^ (2 : ℝ)) < 1 :=
    hcomp.eventually (eventually_lt_nhds one_pos)
  filter_upwards [hev, eventually_ge_atTop 2] with N hev hN2
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hrpoweq : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have hpoweq : ((N : ℝ) ^ (2 : ℝ)) ^ (D' / 2 + 1) = (N : ℝ) ^ (D' + 2) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  have hexpeq : -(1 / 8 : ℝ) * (N : ℝ) ^ (2 : ℝ) = -((N : ℝ) ^ 2) / 8 := by
    rw [hrpoweq]; ring
  rw [hpoweq, hexpeq] at hev
  have hDpos : (0 : ℝ) < (N : ℝ) ^ D' := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ (D' + 2) = (N : ℝ) ^ D' * (N : ℝ) ^ (2 : ℕ) := by
    rw [← hrpoweq, Real.rpow_add hN0]
  rw [hsplit] at hev
  have hN2R : (2 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    nlinarith [sq_nonneg ((N : ℝ) - 2)]
  have hnn : (0 : ℝ) ≤ Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D' :=
    mul_nonneg (Real.exp_pos _).le hDpos.le
  have hfinal : 2 * (Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D')
      ≤ (N : ℝ) ^ 2 * (Real.exp (-((N : ℝ) ^ 2) / 8) * (N : ℝ) ^ D') :=
    mul_le_mul_of_nonneg_right hN2R hnn
  rw [Real.rpow_neg (Nat.cast_nonneg N), inv_eq_one_div, le_div_iff₀ hDpos]
  nlinarith [hfinal, hev]

end Tail

/-! ### The cardinality of the (step, coordinate) index set is polynomial in `N`. -/

section Cardinality

private theorem gcpCardIdxEq (N : ℕ) : Fintype.card (d.Idx N) = d.L N * d.W N := by
  change Fintype.card (ZMod (d.L N) × Fin (d.W N)) = d.L N * d.W N
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]

private theorem gcpCardCoordFinsetEq (N : ℕ) :
    (Grid.coordFinset (d := d) N).card = d.L N * d.W N * (d.L N * d.W N) * 2 := by
  have h1 : Fintype.card (d.Idx N × d.Idx N × Bool)
      = Fintype.card (d.Idx N) * Fintype.card (d.Idx N × Bool) := Fintype.card_prod _ _
  have h2 : Fintype.card (d.Idx N × Bool) = Fintype.card (d.Idx N) * Fintype.card Bool :=
    Fintype.card_prod _ _
  change (Finset.univ.map (Function.Embedding.sigmaMk N)).card = _
  rw [Finset.card_map, Finset.card_univ, h1, h2, Fintype.card_bool, gcpCardIdxEq]
  ring

private theorem gcpCardKEq (n0 N : ℕ) :
    Fintype.card (Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N))
      = gueGridK n0 N * (d.L N * d.W N * (d.L N * d.W N) * 2) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, gcpCardCoordFinsetEq]

private theorem gcpEventuallyCardKLe (n0 : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N)) : ℝ)
        ≤ (N : ℝ) ^ ((32 * n0 + 68 : ℕ) : ℝ) := by
  filter_upwards [d.dim, eventually_ge_atTop (2 ^ (32 * n0 + 65))] with N hdim hNbig
  have hN1 : 1 ≤ N := le_trans (Nat.one_le_two_pow) hNbig
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLW : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact hdim.1
  have hnat : Fintype.card (Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N))
      ≤ (N + 1) ^ (32 * n0 + 64) * (N * N * 2) := by
    rw [gcpCardKEq]
    unfold gueGridK
    have h1 : d.L N * d.W N * (d.L N * d.W N) * 2 ≤ N * N * 2 := by
      have := Nat.mul_le_mul hLW hLW
      omega
    exact Nat.mul_le_mul_left _ h1
  have hcast : (Fintype.card (Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N)) : ℝ)
      ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2) := by
    have := hnat
    calc (Fintype.card (Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N)) : ℝ)
        ≤ (((N + 1) ^ (32 * n0 + 64) * (N * N * 2) : ℕ) : ℝ) := by exact_mod_cast this
      _ = ((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2) := by push_cast; ring
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h2N : (N : ℝ) + 1 ≤ 2 * N := by linarith
  have hpow1 : ((N : ℝ) + 1) ^ (32 * n0 + 64) ≤ (2 * (N : ℝ)) ^ (32 * n0 + 64) :=
    pow_le_pow_left₀ (by linarith) h2N _
  have hpow2 : (2 * (N : ℝ)) ^ (32 * n0 + 64)
      = (2 : ℝ) ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64) :=
    mul_pow 2 (N : ℝ) _
  have hbig : (2 : ℝ) ^ (32 * n0 + 65) ≤ (N : ℝ) := by
    have : ((2 ^ (32 * n0 + 65) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNbig
    rwa [Nat.cast_pow, Nat.cast_ofNat] at this
  have hstep : ((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2)
      ≤ (2 : ℝ) ^ (32 * n0 + 65) * (N : ℝ) ^ (32 * n0 + 66) := by
    calc ((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2)
        ≤ (2 * (N : ℝ)) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2) := by
          gcongr
      _ = (2 : ℝ) ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2) := by
          rw [hpow2]
      _ = (2 : ℝ) ^ (32 * n0 + 65) * (N : ℝ) ^ (32 * n0 + 66) := by ring
  have hfinal : (2 : ℝ) ^ (32 * n0 + 65) * (N : ℝ) ^ (32 * n0 + 66) ≤ (N : ℝ) ^ (32 * n0 + 68) := by
    have hN66 : (0:ℝ) ≤ (N:ℝ) ^ (32 * n0 + 66) := by positivity
    calc (2 : ℝ) ^ (32 * n0 + 65) * (N : ℝ) ^ (32 * n0 + 66)
        ≤ (N : ℝ) * (N : ℝ) ^ (32 * n0 + 66) := mul_le_mul_of_nonneg_right hbig hN66
      _ = (N : ℝ) ^ (32 * n0 + 67) := by ring
      _ ≤ (N : ℝ) ^ (32 * n0 + 68) := by
          have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          exact pow_le_pow_right₀ hN1' (by omega)
  rw [show ((32 * n0 + 68 : ℕ) : ℝ) = ((32 * n0 + 68 : ℕ) : ℝ) from rfl,
    show (N:ℝ) ^ ((32*n0+68:ℕ):ℝ) = (N:ℝ)^(32*n0+68) from Real.rpow_natCast (N:ℝ) (32*n0+68)]
  calc (Fintype.card (Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N)) : ℝ)
      ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) * N * 2) := hcast
    _ ≤ (2 : ℝ) ^ (32 * n0 + 65) * (N : ℝ) ^ (32 * n0 + 66) := hstep
    _ ≤ (N : ℝ) ^ (32 * n0 + 68) := hfinal

end Cardinality

/-! ### `gue_highProb_incr_le`. -/

section IncrTruncation

private theorem gcpUnitVarPos (c : Coord d) : 0 < (gueUnitVar d c : ℝ) := by
  unfold gueUnitVar; split_ifs <;> norm_num

private theorem gcpUnitVarLeOne (c : Coord d) : (gueUnitVar d c : ℝ) ≤ 1 := by
  unfold gueUnitVar; split_ifs <;> norm_num

/-- **`gue_highProb_incr_le`**: with high probability, every entry of every grid increment
`X(ω k)`, `1 ≤ k ≤ gueGridK n₀ N`, is at most `N` in modulus. -/
theorem gue_highProb_incr_le (n0 : ℕ) :
    HighProb (Pgue d) (fun N => {ω | ∀ k, 1 ≤ k → k ≤ gueGridK n0 N → ∀ i j : d.Idx N,
      ‖Xmat d N (ω k) i j‖ ≤ N}) := by
  classical
  set K : ℕ → Type := fun N => Fin (gueGridK n0 N) × ↥(Grid.coordFinset (d := d) N) with hKdef
  set Ξ : ∀ N, K N → Set (Grid.Ωg d) :=
    fun N p => {ω | |ω (p.1.1 + 1) (p.2 : Coord d)| ≤ (N : ℝ) / 2} with hΞdef
  have hmeas : ∀ N (p : K N), Measurable (fun ω : Grid.Ωg d => ω (p.1.1 + 1) (p.2 : Coord d)) :=
    fun N p => (measurable_pi_apply (p.2 : Coord d)).comp (measurable_pi_apply (p.1.1 + 1))
  have hcompl : ∀ D : ℝ, 0 < D → ∀ᶠ N : ℕ in atTop, ∀ p : K N,
      (Pgue d) (Ξ N p)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    intro D _
    filter_upwards [gcpEventuallyExpBeatsRpow D] with N hN p
    have hms : MeasurableSet {y : ℝ | (N : ℝ) / 2 < |y|} :=
      measurableSet_lt measurable_const measurable_norm
    have heq : (Ξ N p)ᶜ = (fun ω : Grid.Ωg d => ω (p.1.1 + 1) (p.2 : Coord d)) ⁻¹'
        {y : ℝ | (N : ℝ) / 2 < |y|} := by
      ext ω; simp [hΞdef, not_le]
    rw [heq, ← Measure.map_apply (hmeas N p) hms]
    have hmapeq : (Pgue d).map (fun ω : Grid.Ωg d => ω (p.1.1 + 1) (p.2 : Coord d))
        = gaussianReal 0 (gueUnitVar d (p.2 : Coord d)) := by
      rw [show (fun ω : Grid.Ωg d => ω (p.1.1 + 1) (p.2 : Coord d))
          = (fun y : Ω d => y (p.2 : Coord d)) ∘ (fun ω : Grid.Ωg d => ω (p.1.1 + 1)) from rfl,
        ← Measure.map_map (measurable_pi_apply (p.2 : Coord d)) (measurable_pi_apply (p.1.1 + 1)),
        gcpMapIncr p.1.1, gcpUnitMapEval (p.2 : Coord d)]
    rw [hmapeq]
    have htail := gcpGaussianTailLe (gcpUnitVarPos (p.2 : Coord d))
      (gcpUnitVarLeOne (p.2 : Coord d)) (show (0 : ℝ) ≤ (N : ℝ) / 2 by positivity)
    have hEq : -(((N : ℝ) / 2) ^ 2) / 2 = -((N : ℝ) ^ 2) / 8 := by ring
    rw [hEq] at htail
    exact htail.trans (ENNReal.ofReal_le_ofReal hN)
  have hsub : ∀ N, (⋂ p : K N, Ξ N p) ⊆ {ω | ∀ k, 1 ≤ k → k ≤ gueGridK n0 N → ∀ i j : d.Idx N,
      ‖Xmat d N (ω k) i j‖ ≤ N} := by
    intro N ω hω k hk1 hkK i j
    simp only [Set.mem_iInter] at hω
    have hbound : ∀ c ∈ Grid.coordFinset (d := d) N, |ω k c| ≤ (N : ℝ) / 2 := by
      intro c hc
      have hkey := hω (⟨⟨k - 1, by omega⟩, ⟨c, hc⟩⟩ : K N)
      simp only [hΞdef, Set.mem_ofPred_eq] at hkey
      have heqk : k - 1 + 1 = k := by omega
      rwa [heqk] at hkey
    have hle := gcpNormXentryLe N (ω k) i j hbound
    rw [Xmat_apply]
    calc ‖Xentry d N (ω k) i j‖ ≤ 2 * ((N : ℝ) / 2) := hle
      _ = N := by ring
  refine HighProb.mono ?_ (Filter.Eventually.of_forall hsub)
  exact HighProb.biInter (by positivity) (gcpEventuallyCardKLe n0) hcompl

end IncrTruncation

end RBM.Gauss.GUEGrid
