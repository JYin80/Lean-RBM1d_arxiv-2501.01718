/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.LinearForm
import Mathlib.Probability.Moments.SubGaussian

/-!
# The discrete grid Markov property (2.34), §5.3

Pilot P2 of the True-Path track (T1482, amend-1): the freezing lemma for the grid filtration
`RBM.Gauss.Grid.filt` — conditioning a function of a `filt d k`-measurable coefficient and the
independent next increment amounts to averaging out the increment against its own law.

This is used downstream (pilot P4, discrete Duhamel/Azuma argument, `docs/claude-team/pilot-P4P5
-paper.md` §3–§4) to produce a deterministic conditional sub-Gaussian moment-generating function
for the linear part of a martingale difference.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal MeasureTheory

variable (d : Dims)

/-! ### T1 : the freezing lemma -/

section Freeze

variable {d}

/-- **The freezing lemma.** For `k`, a `filt d k`-measurable `Y : Ωg d → β` and a jointly
measurable `F : β → Ω d → ℝ` with `F (Y ·) (· (k+1))` integrable, conditioning on `filt d k`
freezes `Y` and averages the independent next increment `ω (k+1)` against its own law `P d`. -/
theorem condExp_freeze {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : Ωg d → β} (hY : Measurable[filt d k] Y)
    {F : β → Ω d → ℝ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pg d)) :
    (Pg d)[fun ω => F (Y ω) (ω (k + 1)) | filt d k]
      =ᵐ[Pg d] fun ω => ∫ x, F (Y ω) x ∂(P d) := by
  classical
  set μ : Measure (Ωg d) := Pg d with hμdef
  set Z : Ωg d → Ω d := fun ω => ω (k + 1) with hZdef
  set Φ : Ωg d → β × Ω d := fun ω => (Y ω, Z ω) with hΦdef
  set ν : Measure (Ω d) := P d with hνdef
  set G : β → ℝ := fun y => ∫ x, F y x ∂ν with hGdef
  have hYmeas : Measurable Y := hY.mono ((filt d).le k) le_rfl
  have hZmeas : Measurable Z := measurable_pi_apply (k + 1)
  have hΦmeas : Measurable Φ := hYmeas.prodMk hZmeas
  have hFsm : StronglyMeasurable (fun p : β × Ω d => F p.1 p.2) := hF.stronglyMeasurable
  have hνmap : μ.map Z = ν := map_incr d k
  have hindYZ : IndepFun Y Z μ := by
    have hcle : MeasurableSpace.comap Y inferInstance ≤ filt d k := hY.comap_le
    exact (indep_of_indep_of_le_right (indep_incr d k) hcle).symm
  have hIntΦ : Integrable (fun p : β × Ω d => F p.1 p.2) (μ.map Φ) := by
    rw [integrable_map_measure hFsm.aestronglyMeasurable hΦmeas.aemeasurable]
    exact hInt
  have hprodglobal : μ.map Φ = (μ.map Y).prod ν := by
    rw [← hνmap]
    exact hindYZ.map_prod_eq_prod_map_map hYmeas.aemeasurable hZmeas.aemeasurable
  have hGmeas : StronglyMeasurable G := hFsm.integral_prod_right'
  -- the key set-wise identity, for every `A ∈ filt d k`
  have hkey : ∀ A : Set (Ωg d), MeasurableSet[filt d k] A →
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
      have hASmem : MeasurableSet[filt d k] (A ∩ Y ⁻¹' s) := hA.inter (hY hs)
      have hZTmem : MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' t) :=
        ⟨t, ht, rfl⟩
      have hindep := (Indep_iff (MeasurableSpace.comap Z inferInstance) (filt d k) μ).1
        (indep_incr d k) (Z ⁻¹' t) (A ∩ Y ⁻¹' s) hZTmem hASmem
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
  have hGYmeas : StronglyMeasurable[filt d k] (fun ω => G (Y ω)) := hGmeas.comp_measurable hY
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((filt d).le k) hInt
    (fun s _ _ => hGYint.integrableOn) (fun s hs _ => (hkey s hs).symm)
    hGYmeas.aestronglyMeasurable).symm

end Freeze

/-! ### T2/T3 : the conditional Gaussian MGF of a frozen linear functional -/

section LinearFunctional

variable {d}

/-- The real-linear pairing `Re(trace(A*X))` used to read off one real-linear coordinate of the
Hermitian matrix `X` in the direction `A`. -/
def lin (N : ℕ) (A X : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ := (Matrix.trace (A * X)).re

/-- The (finite) set of raw coordinates of `Ω d` read by `Xmat d N`. -/
def coordFinset (N : ℕ) : Finset (Coord d) :=
  Finset.univ.map (Function.Embedding.sigmaMk N)

@[simp] theorem mem_coordFinset (N : ℕ) (c : Coord d) : c ∈ coordFinset N ↔ c.1 = N := by
  obtain ⟨c1, c2⟩ := c
  unfold coordFinset
  rw [Finset.mem_map]
  constructor
  · rintro ⟨p, -, hp⟩
    exact (congrArg Sigma.fst hp).symm
  · intro h
    simp only at h
    subst h
    exact ⟨c2, Finset.mem_univ _, rfl⟩

private theorem lin_add (N : ℕ) (A X Y : Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N A (X + Y) = lin N A X + lin N A Y := by
  unfold lin
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

private theorem lin_smul (N : ℕ) (A X : Matrix (d.Idx N) (d.Idx N) ℂ) (a : ℝ) :
    lin N A ((a : ℂ) • X) = a * lin N A X := by
  unfold lin
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

private theorem Xmat_add' (N : ℕ) (y₁ y₂ : Ω d) :
    Xmat d N (y₁ + y₂) = Xmat d N y₁ + Xmat d N y₂ := by
  ext i j
  simp only [Xmat_apply, Matrix.add_apply, Xentry, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

private theorem Xmat_smul' (N : ℕ) (a : ℝ) (y : Ω d) :
    Xmat d N (a • y) = (a : ℂ) • Xmat d N y := by
  ext i j
  simp only [Xmat_apply, Matrix.smul_apply, Xentry, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

/-- `Xmat d N` reads only the coordinates in `coordFinset N`. -/
private theorem Xmat_congr (N : ℕ) {y y' : Ω d} (h : ∀ c ∈ coordFinset N, y c = y' c) :
    Xmat d N y = Xmat d N y' := by
  ext i j
  simp only [Xmat_apply, Xentry]
  have h1 := h ⟨N, i, j, true⟩ ((mem_coordFinset N _).2 rfl)
  have h2 := h ⟨N, i, j, false⟩ ((mem_coordFinset N _).2 rfl)
  have h3 := h ⟨N, j, i, true⟩ ((mem_coordFinset N _).2 rfl)
  have h4 := h ⟨N, j, i, false⟩ ((mem_coordFinset N _).2 rfl)
  split_ifs <;> simp only [h1, h2, h3, h4]

private theorem Xmat_zero' (N : ℕ) : Xmat d N (0 : Ω d) = 0 := by
  ext i j; simp [Xmat_apply, Xentry]

private theorem Xmat_sum (N : ℕ) (S : Finset (Coord d)) (y : Coord d → ℝ) :
    Xmat d N (∑ c ∈ S, y c • Pi.single c 1)
      = ∑ c ∈ S, (y c : ℂ) • Xmat d N (Pi.single c 1) := by
  classical
  induction S using Finset.induction with
  | empty => simp [Xmat_zero']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Xmat_add', ih, Xmat_smul']

private theorem lin_sum (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) (S : Finset (Coord d))
    (y : Coord d → ℝ) (M : Coord d → Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N A (∑ c ∈ S, (y c : ℂ) • M c) = ∑ c ∈ S, y c * lin N A (M c) := by
  classical
  induction S using Finset.induction with
  | empty => simp [lin]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, lin_add, ih, lin_smul]

/-- The (real, coordinatewise) decomposition of `y` into the raw coordinates read by `Xmat d N`. -/
private theorem sum_single_agree (N : ℕ) (y : Ω d) {c : Coord d} (hc : c ∈ coordFinset N) :
    (∑ c' ∈ coordFinset N, y c' • Pi.single c' 1 : Ω d) c = y c := by
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, hc, ite_true]

/-- **The linear decomposition.** `lin N A (Xmat d N y)` is the finite real-linear form in the
coordinates of `y` read by `Xmat d N`, with coefficients the values of `lin N A ∘ Xmat d N` at the
standard basis vectors. -/
theorem lin_Xmat_eq_sum (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) :
    lin N A (Xmat d N y)
      = ∑ c ∈ coordFinset N, y c * lin N A (Xmat d N (Pi.single c 1)) := by
  classical
  have hagree : ∀ c ∈ coordFinset N, y c = (∑ c' ∈ coordFinset N, y c' • Pi.single c' 1 : Ω d) c :=
    fun c hc => (sum_single_agree N y hc).symm
  rw [Xmat_congr N hagree, Xmat_sum, lin_sum]

/-- **The conditional variance of a frozen linear functional** at size `N`, in the direction `A`:
the weighted sum, over the raw coordinates read by `Xmat d N`, of the coordinate variance times the
squared coefficient of that coordinate in `lin N A ∘ Xmat d N`. -/
def v (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  linVar (gvar d) (fun c => lin N A (Xmat d N (Pi.single c 1))) (coordFinset N)

theorem v_nonneg (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) : 0 ≤ v N A := by
  unfold v linVar
  positivity

/-- **The law of a fixed-direction frozen linear functional.** For a *fixed* (deterministic)
matrix `A`, `y ↦ lin N A (Xmat d N y)` is, under `P d`, a centred Gaussian of variance `v N A`. -/
theorem map_lin_Xmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (P d).map (fun y => lin N A (Xmat d N y))
      = gaussianReal 0 (NNReal.mk (v N A) (v_nonneg N A)) := by
  have hfun : (fun y : Ω d => lin N A (Xmat d N y))
      = fun y => ∑ c ∈ coordFinset N, (lin N A (Xmat d N (Pi.single c 1))) * y c := by
    funext y
    rw [lin_Xmat_eq_sum]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  rw [hfun, map_sum_const_mul_coord d (fun c => lin N A (Xmat d N (Pi.single c 1))) (coordFinset N)]
  rfl

/-- **The mean of a fixed-direction frozen linear functional is zero.** -/
private theorem measurable_Xmat' (N : ℕ) : Measurable (Xmat d N) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d N i j

/-- Joint measurability of `lin`, uncurried, via the explicit finite double sum
`Re(trace(M*X)) = ∑ i, ∑ k, Re(M i k * X k i)`. -/
private theorem lin_eq_sum (N : ℕ) (A X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N A X = ∑ i : d.Idx N, ∑ k : d.Idx N, (A i k * X k i).re := by
  unfold lin
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem measurable_lin_uncurry (N : ℕ) :
    Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => lin N p.1 (Xmat d N p.2)) := by
  have heq : (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => lin N p.1 (Xmat d N p.2))
      = fun p => ∑ i : d.Idx N, ∑ k : d.Idx N, (p.1 i k * Xmat d N p.2 k i).re :=
    funext fun p => lin_eq_sum N p.1 (Xmat d N p.2)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => p.1 i k) :=
    Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => Xmat d N p.2 k i) :=
    Measurable.eval_matrix (i := k) (j := i) ((measurable_Xmat' N).comp measurable_snd)
  exact Complex.measurable_re.comp (hM.mul hX)

theorem integral_lin_Xmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∫ x, lin N A (Xmat d N x) ∂(P d) = 0 := by
  have hmeas : Measurable (fun x : Ω d => lin N A (Xmat d N x)) := by
    have heq : (fun x : Ω d => lin N A (Xmat d N x))
        = fun x => ∑ i : d.Idx N, ∑ k : d.Idx N, (A i k * Xmat d N x k i).re :=
      funext fun x => lin_eq_sum N A (Xmat d N x)
    rw [heq]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
    exact Complex.measurable_re.comp
      (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (measurable_Xmat' N)))
  have h := integral_map (μ := P d) (φ := fun x : Ω d => lin N A (Xmat d N x))
    (f := fun y : ℝ => y) hmeas.aemeasurable stronglyMeasurable_id.aestronglyMeasurable
  rw [map_lin_Xmat] at h
  rw [← h, integral_id_gaussianReal]

private instance instStandardBorelSpaceMatrix (N : ℕ) :
    StandardBorelSpace (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  inferInstanceAs (StandardBorelSpace (d.Idx N → d.Idx N → ℂ))

variable (s t : ℕ → ℝ) (K : ℕ → ℕ)

/-- **T3: the conditional mean of a frozen linear functional is zero.** Under the structural
hypotheses of (T2) (a `filt d k`-measurable direction `A`, a `filt d k`-measurable set `E`) plus
integrability of the un-truncated linear functional, the conditional expectation of the
`E`-truncated variable is `0` a.e. -/
theorem condExp_linear_eq_zero (N k : ℕ) {A : Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hA : Measurable[filt d k] A) (E : Set (Ωg d)) (hE : MeasurableSet[filt d k] E)
    (hIntG : Integrable
      (fun ω => Real.sqrt (step s t K N) * lin N (A ω) (Xmat d N (ω (k + 1)))) (Pg d)) :
    (Pg d)[fun ω => E.indicator
        (fun ω => Real.sqrt (step s t K N) * lin N (A ω) (Xmat d N (ω (k + 1)))) ω | filt d k]
      =ᵐ[Pg d] (fun _ => (0 : ℝ)) := by
  set G : Ωg d → ℝ := fun ω => Real.sqrt (step s t K N) * lin N (A ω) (Xmat d N (ω (k + 1)))
    with hGdef
  set F : Matrix (d.Idx N) (d.Idx N) ℂ → Ω d → ℝ :=
    fun p x => Real.sqrt (step s t K N) * lin N p (Xmat d N x) with hFdef
  have hF : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => F p.1 p.2) :=
    (measurable_lin_uncurry N).const_mul _
  have hIntG' : Integrable (fun ω => F (A ω) (ω (k + 1))) (Pg d) := hIntG
  have hfreeze := condExp_freeze k hA hF hIntG'
  have hzero : (fun ω : Ωg d => ∫ x, F (A ω) x ∂(P d)) = fun _ => (0 : ℝ) := by
    funext ω
    change ∫ x, Real.sqrt (step s t K N) * lin N (A ω) (Xmat d N x) ∂(P d) = 0
    rw [integral_const_mul, integral_lin_Xmat, mul_zero]
  rw [hzero] at hfreeze
  have hFG : (fun ω : Ωg d => F (A ω) (ω (k + 1))) = G := by
    funext ω; rw [hFdef, hGdef]
  rw [hFG] at hfreeze
  have hEmeas : MeasurableSet E := (filt d).le k E hE
  have hcondEq : (Pg d)[fun ω => E.indicator (fun ω => G ω) ω | filt d k]
      =ᵐ[Pg d] (Set.indicator E (fun _ => (1 : ℝ))) * (Pg d)[G | filt d k] := by
    have heq : (fun ω => E.indicator (fun ω => G ω) ω)
        = (Set.indicator E (fun _ => (1 : ℝ))) * G := by
      funext ω
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω]
    rw [heq]
    refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ ?_
    · exact (stronglyMeasurable_const.indicator hE)
    · rw [← heq]; exact hIntG.indicator hEmeas
    · exact hIntG
  refine hcondEq.trans ?_
  filter_upwards [hfreeze] with ω hω
  simp only [Pi.mul_apply, hω, mul_zero]

/-! ### T2 : the conditional Gaussian MGF of a frozen linear functional -/

/-- `lin` vanishes at the zero direction. -/
private theorem lin_zero (N : ℕ) (X : Matrix (d.Idx N) (d.Idx N) ℂ) : lin N 0 X = 0 := by
  unfold lin; simp

/-- The conditional variance vanishes at the zero direction. -/
private theorem v_zero (N : ℕ) : v N (0 : Matrix (d.Idx N) (d.Idx N) ℂ) = 0 := by
  unfold v linVar; simp [lin_zero]

/-- `lin N A M` is measurable (in fact continuous) in the direction `A`, for a fixed matrix `M`. -/
private theorem measurable_lin_left (N : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Measurable (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => lin N A M) := by
  have heq : (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => lin N A M)
      = fun A => ∑ i : d.Idx N, ∑ k : d.Idx N, (A i k * M k i).re :=
    funext fun A => lin_eq_sum N A M
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    ((Matrix.measurable_apply (i := i) (j := k)).mul measurable_const)

/-- The real-valued formula for `v`, unfolding the `ℝ≥0`-valued `linVar`. -/
private theorem v_eq_sum (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    v N A = ∑ c ∈ coordFinset N, (lin N A (Xmat d N (Pi.single c 1))) ^ 2 * (gvar d c : ℝ) := by
  unfold v linVar
  push_cast [NNReal.coe_mk]
  rfl

/-- `v` is measurable in the direction argument. -/
private theorem measurable_v (N : ℕ) :
    Measurable (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => v N A) := by
  have heq : (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => v N A)
      = fun A => ∑ c ∈ coordFinset N, (lin N A (Xmat d N (Pi.single c 1))) ^ 2 * (gvar d c : ℝ) :=
    funext (v_eq_sum N)
  rw [heq]
  exact Finset.measurable_sum _ fun c _ => ((measurable_lin_left N _).pow_const 2).mul_const _

/-- `lin N A (Xmat d N ·)` is measurable in the sample point, for a fixed direction `A`. -/
private theorem measurable_lin_Xmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Measurable (fun x : Ω d => lin N A (Xmat d N x)) := by
  have heq : (fun x : Ω d => lin N A (Xmat d N x))
      = fun x => ∑ i : d.Idx N, ∑ k : d.Idx N, (A i k * Xmat d N x k i).re :=
    funext fun x => lin_eq_sum N A (Xmat d N x)
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  exact Complex.measurable_re.comp
    (measurable_const.mul (Measurable.eval_matrix (i := k) (j := i) (measurable_Xmat' N)))

/-- **The mgf of the fixed-direction frozen linear functional.** For a *fixed* matrix `A`,
`lin N A ∘ Xmat d N` is (exactly) Gaussian of variance `v N A`, so its mgf is the Gaussian mgf. -/
private theorem mgf_lin_Xmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) (r : ℝ) :
    mgf (fun x => lin N A (Xmat d N x)) (P d) r = Real.exp (v N A * r ^ 2 / 2) := by
  have hlaw : HasLaw (fun x => lin N A (Xmat d N x))
      (gaussianReal 0 (NNReal.mk (v N A) (v_nonneg N A))) (P d) :=
    ⟨(measurable_lin_Xmat N A).aemeasurable, map_lin_Xmat N A⟩
  rw [mgf_gaussianReal hlaw]
  congr 1
  push_cast [NNReal.coe_mk]
  ring

/-- `exp (r · lin N A (Xmat d N ·))` is integrable, for a fixed direction `A`. -/
private theorem integrable_exp_lin_Xmat (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) (r : ℝ) :
    Integrable (fun x => Real.exp (r * lin N A (Xmat d N x))) (P d) := by
  have h : Integrable (fun x : ℝ => Real.exp (r * x))
      ((P d).map (fun x => lin N A (Xmat d N x))) := by
    rw [map_lin_Xmat N A]; exact integrable_exp_mul_gaussianReal r
  exact (integrable_map_measure h.aestronglyMeasurable (measurable_lin_Xmat N A).aemeasurable).1 h

section MGFBound

variable {N k : ℕ} {A : Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ}

/-- **The unconditional integrability of `exp (r · X)`** for the frozen linear functional
`X ω = √Δ · lin N (A ω) (Xmat d N (ω (k+1)))`, given the deterministic pointwise variance bound
`(√Δ)² · v N (A ω) ≤ c` for *every* `ω`. Proved by Tonelli
(`RBM.Gauss.lintegral_indep_pair`) across the independent pair `(ω (k+1), A ω)`: the inner
integral is the exact Gaussian mgf `exp (v N (A ω) · (r√Δ)² / 2)`, uniformly bounded by
`exp (c r² / 2)` since the deterministic bound holds for every `ω`, hence for
`(Pg d).map A`-almost every value of the direction. -/
private theorem integrable_exp_mul_X (hA : Measurable[filt d k] A) {Δ c : ℝ} (hc : 0 ≤ c)
    (hAle2 : ∀ ω, (Real.sqrt Δ) ^ 2 * v N (A ω) ≤ c) (r : ℝ) :
    Integrable (fun ω : Ωg d =>
      Real.exp (r * (Real.sqrt Δ * lin N (A ω) (Xmat d N (ω (k + 1)))))) (Pg d) := by
  classical
  set U : Ωg d → Ω d := fun ω => ω (k + 1) with hUdef
  set F : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp ((r * Real.sqrt Δ) * lin N p.2 (Xmat d N p.1))) with hFdef
  have hUmeas : Measurable U := measurable_pi_apply (k + 1)
  have hAmeas : Measurable A := hA.mono ((filt d).le k) le_rfl
  have hindep : IndepFun U A (Pg d) := by
    have hcle : MeasurableSpace.comap A inferInstance ≤ filt d k := hA.comap_le
    exact indep_of_indep_of_le_right (indep_incr d k) hcle
  have hFmeas : Measurable F := by
    have h0 : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ =>
        lin N p.2 (Xmat d N p.1)) := by
      have heq : (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ => lin N p.2 (Xmat d N p.1))
          = fun p => ∑ i : d.Idx N, ∑ k' : d.Idx N, (p.2 i k' * Xmat d N p.1 k' i).re :=
        funext fun p => lin_eq_sum N p.2 (Xmat d N p.1)
      rw [heq]
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
      have hM : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ => p.2 i k') :=
        Measurable.eval_matrix (i := i) (j := k') measurable_snd
      have hX : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ => Xmat d N p.1 k' i) :=
        Measurable.eval_matrix (i := k') (j := i) ((measurable_Xmat' N).comp measurable_fst)
      exact Complex.measurable_re.comp (hM.mul hX)
    have h1 : Measurable (fun p : Ω d × Matrix (d.Idx N) (d.Idx N) ℂ =>
        (r * Real.sqrt Δ) * lin N p.2 (Xmat d N p.1)) := h0.const_mul _
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp h1)
  have hkey := lintegral_indep_pair hUmeas hAmeas hindep hFmeas
  rw [map_incr d k] at hkey
  have hinner : ∀ y : Matrix (d.Idx N) (d.Idx N) ℂ,
      (∫⁻ x, F (x, y) ∂ (P d)) = ENNReal.ofReal (Real.exp (v N y * (r * Real.sqrt Δ) ^ 2 / 2)) := by
    intro y
    have hint := integrable_exp_lin_Xmat N y (r * Real.sqrt Δ)
    have hofreal := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hmgf := mgf_lin_Xmat N y (r * Real.sqrt Δ)
    rw [mgf] at hmgf
    rw [hFdef]
    dsimp only
    rw [← hofreal, hmgf]
  have hp : MeasurableSet {y : Matrix (d.Idx N) (d.Idx N) ℂ |
      v N y * (r * Real.sqrt Δ) ^ 2 / 2 ≤ c * r ^ 2 / 2} :=
    measurableSet_le (((measurable_v N).mul_const _).div_const _) measurable_const
  have hptwise : ∀ ω, v N (A ω) * (r * Real.sqrt Δ) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    intro ω
    have h2 := hAle2 ω
    nlinarith [sq_nonneg r]
  have hae : ∀ᵐ y ∂ (Pg d).map A, v N y * (r * Real.sqrt Δ) ^ 2 / 2 ≤ c * r ^ 2 / 2 := by
    rw [ae_map_iff hAmeas.aemeasurable hp]
    exact Filter.Eventually.of_forall hptwise
  have houter_eq : ∫⁻ ω, F (U ω, A ω) ∂ (Pg d)
      = ∫⁻ y, ENNReal.ofReal (Real.exp (v N y * (r * Real.sqrt Δ) ^ 2 / 2)) ∂ ((Pg d).map A) := by
    rw [hkey]; exact lintegral_congr hinner
  have houter_le : ∫⁻ ω, F (U ω, A ω) ∂ (Pg d) ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
    rw [houter_eq]
    calc ∫⁻ y, ENNReal.ofReal (Real.exp (v N y * (r * Real.sqrt Δ) ^ 2 / 2)) ∂ ((Pg d).map A)
        ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) ∂ ((Pg d).map A) := by
          apply lintegral_mono_ae
          filter_upwards [hae] with y hy
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hy)
      _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pg d).map A) Set.univ := by
          rw [lintegral_const]
      _ ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := by
          calc ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * ((Pg d).map A) Set.univ
              ≤ ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) * 1 := by
                gcongr
                exact prob_le_one
            _ = ENNReal.ofReal (Real.exp (c * r ^ 2 / 2)) := mul_one _
  refine ⟨?_, ?_⟩
  · have hXmeas : Measurable (fun ω : Ωg d =>
        Real.exp (r * (Real.sqrt Δ * lin N (A ω) (Xmat d N (ω (k + 1)))))) := by
      have h1 : Measurable (fun ω : Ωg d => lin N (A ω) (Xmat d N (ω (k + 1)))) := by
        have heq : (fun ω : Ωg d => lin N (A ω) (Xmat d N (ω (k + 1))))
            = fun ω => ∑ i : d.Idx N, ∑ k' : d.Idx N,
              (A ω i k' * Xmat d N (ω (k + 1)) k' i).re :=
          funext fun ω => lin_eq_sum N (A ω) (Xmat d N (ω (k + 1)))
        rw [heq]
        refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k' _ => ?_
        have hM : Measurable (fun ω : Ωg d => A ω i k') := Measurable.eval_matrix hAmeas
        have hX : Measurable (fun ω : Ωg d => Xmat d N (ω (k + 1)) k' i) :=
          Measurable.eval_matrix ((measurable_Xmat' N).comp hUmeas)
        exact Complex.measurable_re.comp (hM.mul hX)
      exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
    exact hXmeas.aestronglyMeasurable
  · rw [hasFiniteIntegral_def]
    have heq : ∀ ω, ‖Real.exp (r * (Real.sqrt Δ * lin N (A ω) (Xmat d N (ω (k + 1)))))‖ₑ
        = F (U ω, A ω) := by
      intro ω
      rw [Real.enorm_eq_ofReal (Real.exp_pos _).le, hFdef]
      dsimp only
      congr 2
      ring
    simp_rw [heq]
    exact lt_of_le_of_lt houter_le ENNReal.ofReal_lt_top

/-- **The a.e. conditional mgf bound.** For a fixed real `r`, almost everywhere (w.r.t. the
trimmed measure), the mgf of the frozen linear functional at `r` with respect to the conditional
expectation kernel is at most the deterministic Gaussian bound `exp (c r² / 2)`. Proved by
`condExp_freeze` (identifying the conditional expectation of `exp (r · X)` with the frozen
Gaussian mgf `y ↦ exp (v N y · (r√Δ)² / 2)`) bridged to the kernel via
`condExp_ae_eq_trim_integral_condExpKernel`, exactly as in
`RBM.actualPrefix_increment_hasCondSubgaussianMGF`
(`Gauss/PermutationFourierDoobCondMGF.lean:72`), with the Gaussian mgf replacing the Hoeffding
step. -/
private theorem condMGF_le (hA : Measurable[filt d k] A) {Δ c : ℝ} (hc : 0 ≤ c)
    (hAle2 : ∀ ω, (Real.sqrt Δ) ^ 2 * v N (A ω) ≤ c) (r : ℝ) :
    ∀ᵐ ω ∂ ((Pg d).trim ((filt d).le k)),
      mgf (fun ρ => Real.sqrt Δ * lin N (A ρ) (Xmat d N (ρ (k + 1))))
        (condExpKernel (Pg d) (filt d k) ω) r ≤ Real.exp (c * r ^ 2 / 2) := by
  classical
  set X : Ωg d → ℝ := fun ρ => Real.sqrt Δ * lin N (A ρ) (Xmat d N (ρ (k + 1))) with hXdef
  set Gr : Ωg d → ℝ := fun ρ => Real.exp (r * X ρ) with hGrdef
  set Fr : Matrix (d.Idx N) (d.Idx N) ℂ → Ω d → ℝ :=
    fun y x => Real.exp (r * (Real.sqrt Δ * lin N y (Xmat d N x))) with hFrdef
  have hFrmeas : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => Fr p.1 p.2) := by
    have h1 : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
        lin N p.1 (Xmat d N p.2)) := measurable_lin_uncurry N
    exact Real.measurable_exp.comp ((h1.const_mul _).const_mul _)
  have hGreq : (fun ρ : Ωg d => Fr (A ρ) (ρ (k + 1))) = Gr := by
    funext ρ; rw [hFrdef, hGrdef, hXdef]
  have hIntGr : Integrable Gr (Pg d) := integrable_exp_mul_X hA hc hAle2 r
  have hfreeze := condExp_freeze k hA hFrmeas (hGreq ▸ hIntGr)
  have hRHS : (fun ρ : Ωg d => ∫ x, Fr (A ρ) x ∂ (P d))
      = fun ρ => Real.exp (v N (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2) := by
    funext ρ
    have hmgf := mgf_lin_Xmat N (A ρ) (r * Real.sqrt Δ)
    rw [mgf] at hmgf
    rw [← hmgf]
    have hpt : ∀ x, Fr (A ρ) x = Real.exp ((r * Real.sqrt Δ) * lin N (A ρ) (Xmat d N x)) := by
      intro x; rw [hFrdef]; ring_nf
    simp_rw [hpt]
  rw [hRHS] at hfreeze
  rw [hGreq] at hfreeze
  have hm : filt d k ≤ (inferInstance : MeasurableSpace (Ωg d)) := (filt d).le k
  have hsm1 : StronglyMeasurable[filt d k] ((Pg d)[Gr | filt d k]) := stronglyMeasurable_condExp
  have hsm2 : StronglyMeasurable[filt d k]
      (fun ρ => Real.exp (v N (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2)) := by
    have hcont : Measurable (fun y : Matrix (d.Idx N) (d.Idx N) ℂ =>
        Real.exp (v N y * (r * Real.sqrt Δ) ^ 2 / 2)) :=
      Real.measurable_exp.comp (((measurable_v N).mul_const _).div_const _)
    exact (hcont.comp hA).stronglyMeasurable
  have htrim := StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm hsm1 hsm2 hfreeze
  have hbridge := condExp_ae_eq_trim_integral_condExpKernel hm hIntGr
  have hcomb : ∀ᵐ ρ ∂ (Pg d).trim hm,
      (∫ σ, Gr σ ∂ condExpKernel (Pg d) (filt d k) ρ)
        = Real.exp (v N (A ρ) * (r * Real.sqrt Δ) ^ 2 / 2) := by
    filter_upwards [hbridge, htrim] with ρ h1 h2
    rw [← h1, h2]
  filter_upwards [hcomb] with ρ hρ
  change (∫ σ, Gr σ ∂ condExpKernel (Pg d) (filt d k) ρ) ≤ Real.exp (c * r ^ 2 / 2)
  rw [hρ]
  apply Real.exp_le_exp.2
  have h2 := hAle2 ρ
  nlinarith [sq_nonneg r]

end MGFBound

/-- **T2: the conditional Gaussian MGF of a frozen linear functional.** For a `filt d k`-measurable
direction `A`, a `filt d k`-measurable set `E`, and a deterministic bound `c ≥ 0` with
`step s t K N · v N (A ω) ≤ c` for every `ω ∈ E`, the `E`-truncated frozen linear functional
`√(step s t K N) · lin N (A ω) (Xmat d N (ω (k+1)))` has a conditionally sub-Gaussian mgf with
parameter `c` given `filt d k`. -/
theorem hasCondSubgaussianMGF_linear (N k : ℕ) {A : Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hA : Measurable[filt d k] A) (E : Set (Ωg d)) (hE : MeasurableSet[filt d k] E)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ ω ∈ E, step s t K N * v N (A ω) ≤ c) :
    HasCondSubgaussianMGF (filt d k) ((filt d).le k)
      (fun ω => E.indicator
        (fun ω => Real.sqrt (step s t K N) * lin N (A ω) (Xmat d N (ω (k + 1)))) ω)
      ⟨c, hc⟩ (Pg d) := by
  classical
  set Δ : ℝ := step s t K N with hΔdef
  set A' : Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ := fun ω => if ω ∈ E then A ω else 0 with hA'def
  have hA'meas : Measurable[filt d k] A' :=
    Measurable.ite (p := fun ω => ω ∈ E) hE hA measurable_const
  have hAle : ∀ ω, Δ * v N (A' ω) ≤ c := by
    intro ω
    by_cases hω : ω ∈ E
    · simpa [hA'def, hω] using hbound ω hω
    · simp only [hA'def, hω, ite_false, v_zero, mul_zero]
      exact hc
  have hAle2 : ∀ ω, (Real.sqrt Δ) ^ 2 * v N (A' ω) ≤ c := by
    intro ω
    by_cases hΔ : 0 ≤ Δ
    · rw [Real.sq_sqrt hΔ]; exact hAle ω
    · rw [Real.sqrt_eq_zero_of_nonpos (not_le.mp hΔ).le]
      simpa using hc
  have hXeq : (fun ω => E.indicator
      (fun ω => Real.sqrt Δ * lin N (A ω) (Xmat d N (ω (k + 1)))) ω)
      = fun ω => Real.sqrt Δ * lin N (A' ω) (Xmat d N (ω (k + 1))) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp [Set.indicator, hω, hA'def]
    · simp [Set.indicator, hω, hA'def, lin_zero]
  rw [hXeq]
  change Kernel.HasSubgaussianMGF (fun ω => Real.sqrt Δ * lin N (A' ω) (Xmat d N (ω (k + 1))))
    ⟨c, hc⟩ (condExpKernel (Pg d) (filt d k)) ((Pg d).trim ((filt d).le k))
  refine Kernel.HasSubgaussianMGF.of_rat ?_ ?_
  · intro r
    rw [condExpKernel_comp_trim ((filt d).le k)]
    exact integrable_exp_mul_X hA'meas hc hAle2 r
  · intro q
    exact condMGF_le hA'meas hc hAle2 (q : ℝ)

end LinearFunctional

end RBM.Gauss.Grid

end
