/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Gauss.Moments
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

/-!
# Linear forms in the Gaussian coordinates

The coordinates of the model are independent centred Gaussians (`P` is an infinite product), so
a finite real linear combination of them is again a centred Gaussian, with variance the weighted
sum of the coordinate variances.

This is the scalar input of the large deviation estimates: conditionally on the coordinates
outside row `i`, the row sum `∑_{k ≠ i} H_{ik} G^{(i)}_{kj}` is such a linear form.

## Main statements

* `RBM.Gauss.iIndepFun_coord` : the coordinates are independent
* `RBM.Gauss.hasLaw_coord` : each coordinate is `N(0, gvar c)`
* `RBM.Gauss.hasLaw_const_mul_coord` : `a · ω c` is `N(0, a² gvar c)`
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable (d : Dims)

/-- **The coordinates are independent.**  `P` is an infinite product measure. -/
theorem iIndepFun_coord : iIndepFun (fun (c : Coord d) (ω : Ω d) => ω c) (P d) := by
  have := iIndepFun_infinitePi (P := fun c : Coord d => gaussianReal 0 (gvar d c))
    (X := fun _ x => x) (fun _ => measurable_id)
  simpa [P] using this

/-- Each coordinate is a centred Gaussian of variance `gvar d c`. -/
theorem hasLaw_coord (c : Coord d) :
    HasLaw (fun ω : Ω d => ω c) (gaussianReal 0 (gvar d c)) (P d) :=
  ⟨measurable_pi_apply c |>.aemeasurable, P_map_eval d c⟩

/-- A scaled coordinate is a centred Gaussian of variance `a² gvar d c`. -/
theorem hasLaw_const_mul_coord (a : ℝ) (c : Coord d) :
    HasLaw (fun ω : Ω d => a * ω c)
      (gaussianReal 0 (NNReal.mk (a ^ 2) (sq_nonneg _) * gvar d c)) (P d) := by
  refine ⟨((measurable_const.mul (measurable_pi_apply c)).aemeasurable), ?_⟩
  have h : (P d).map (fun ω : Ω d => a * ω c)
      = ((P d).map (fun ω : Ω d => ω c)).map (fun x : ℝ => a * x) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h, P_map_eval d c, gaussianReal_map_const_mul a]
  simp

section General

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι]

/-- **A finite real linear form in an independent Gaussian family is a centred Gaussian**, with
variance `∑ a_i² v_i`.  Induction on the finite set: a scaled variable is independent of the sum
of the others, and Gaussians convolve. -/
theorem map_sum_const_mul_of_indep {X : ι → Ω → ℝ} {v : ι → ℝ≥0} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i)) (hindep : iIndepFun X P) (a : ι → ℝ)
    (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω)
      = gaussianReal 0 (∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
  classical
  have hmul : ∀ i, Measurable (fun ω => a i * X i ω) := fun i => (hmeas i).const_mul _
  have hindep' : iIndepFun (fun i ω => a i * X i ω) P :=
    hindep.comp (fun i => fun x : ℝ => a i * x) fun _ => by fun_prop
  have hlaw' : ∀ i, P.map (fun ω => a i * X i ω)
      = gaussianReal 0 (NNReal.mk (a i ^ 2) (sq_nonneg _) * v i) := by
    intro i
    have h : P.map (fun ω => a i * X i ω) = (P.map (X i)).map (fun x : ℝ => a i * x) := by
      rw [Measure.map_map (by fun_prop) (hmeas i)]
      rfl
    rw [h, hlaw i, gaussianReal_map_const_mul (a i)]
    simp
  induction s using Finset.induction with
  | empty => simp [Measure.map_const]
  | insert i₀ s hi₀ ih =>
    have hsum : Measurable (fun ω => ∑ i ∈ s, a i * X i ω) :=
      Finset.measurable_sum _ fun i _ => hmul i
    have hindep0 := hindep'.indepFun_finsetSum_of_notMem (fun i => hmul i) hi₀
    have hfun : (∑ j ∈ s, fun ω => a j * X j ω) = fun ω => ∑ i ∈ s, a i * X i ω := by
      funext ω
      simp [Finset.sum_apply]
    rw [hfun] at hindep0
    have hadd : (fun ω => ∑ i ∈ insert i₀ s, a i * X i ω)
        = (fun ω => a i₀ * X i₀ ω) + (fun ω => ∑ i ∈ s, a i * X i ω) := by
      funext ω
      simp [Finset.sum_insert hi₀]
    rw [hadd, (hindep0.symm).map_add_eq_map_conv_map (hmul i₀) hsum, ih, hlaw' i₀,
      gaussianReal_conv_gaussianReal, Finset.sum_insert hi₀]
    simp

end General

/-- The family of scaled coordinates is independent. -/
theorem iIndepFun_const_mul_coord (a : Coord d → ℝ) :
    iIndepFun (fun (c : Coord d) (ω : Ω d) => a c * ω c) (P d) :=
  (iIndepFun_coord d).comp (fun c => fun x : ℝ => a c * x) fun _ => by fun_prop

/-- **A finite real linear form in the coordinates is a centred Gaussian**, with variance the
weighted sum `∑ a_c² v_c`. -/
theorem map_sum_const_mul_coord (a : Coord d → ℝ) (s : Finset (Coord d)) :
    (P d).map (fun ω : Ω d => ∑ c ∈ s, a c * ω c)
      = gaussianReal 0 (∑ c ∈ s, NNReal.mk (a c ^ 2) (sq_nonneg _) * gvar d c) :=
  map_sum_const_mul_of_indep (fun c => measurable_pi_apply c) (fun c => P_map_eval d c)
    (iIndepFun_coord d) a s

section MomentBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type*} [DecidableEq ι] {X : ι → Ω → ℝ} {v : ι → ℝ≥0}

/-- The variance of the linear form `∑ a_i X_i`. -/
noncomputable def linVar (v : ι → ℝ≥0) (a : ι → ℝ) (s : Finset ι) : ℝ≥0 :=
  ∑ i ∈ s, NNReal.mk (a i ^ 2) (sq_nonneg _) * v i

variable (hmeas : ∀ i, Measurable (X i)) (hlaw : ∀ i, P.map (X i) = gaussianReal 0 (v i))
  (hindep : iIndepFun X P)
include hmeas hlaw hindep

omit [IsProbabilityMeasure P] [DecidableEq ι] hlaw hindep in
theorem measurable_lin (a : ι → ℝ) (s : Finset ι) :
    Measurable fun ω => ∑ i ∈ s, a i * X i ω :=
  Finset.measurable_sum _ fun i _ => (hmeas i).const_mul _

/-- The law of the linear form, in terms of `linVar`. -/
theorem map_lin (a : ι → ℝ) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * X i ω) = gaussianReal 0 (linVar v a s) :=
  map_sum_const_mul_of_indep hmeas hlaw hindep a s

/-- All even moments of a linear form exist. -/
theorem integrable_pow_lin (a : ι → ℝ) (s : Finset ι) (p : ℕ) :
    Integrable (fun ω => (∑ i ∈ s, a i * X i ω) ^ (2 * p)) P := by
  have hm := measurable_lin hmeas a s
  have h := integrable_pow_gaussianReal (linVar v a s) (2 * p)
  rw [← map_lin hmeas hlaw hindep a s] at h
  exact (integrable_map_measure ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
    hm.aemeasurable).1 h

/-- **The even moments of a linear form**: `E[(∑ a_i X_i)^{2p}] = (2p-1)!! (∑ a_i² v_i)^p`. -/
theorem integral_pow_lin (a : ι → ℝ) (s : Finset ι) (p : ℕ) :
    ∫ ω, (∑ i ∈ s, a i * X i ω) ^ (2 * p) ∂P = dfac p * (linVar v a s : ℝ) ^ p := by
  have hm := measurable_lin hmeas a s
  have h := integral_map (μ := P) (φ := fun ω => ∑ i ∈ s, a i * X i ω)
    (f := fun y : ℝ => y ^ (2 * p)) hm.aemeasurable
    ((measurable_id.pow_const (2 * p)).aestronglyMeasurable)
  rw [map_lin hmeas hlaw hindep a s] at h
  rw [← h, integral_pow_gaussianReal']

/-- **The moment bound for the modulus of a complex linear form.**  If `Y = ∑ a_i X_i` and
`Y' = ∑ b_i X_i` are the real and imaginary parts, then
`E[(Y² + Y'²)^p] ≤ 2^p (2p-1)!! (V_a^p + V_b^p)`; in the circular case `V_a = V_b = σ²/2` this
is `E‖Z‖^{2p} ≤ (2p-1)!! σ^{2p}`. -/
theorem integral_sq_add_sq_pow_le (a b : ι → ℝ) (s : Finset ι) (p : ℕ) :
    ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ 2 ^ p * (dfac p * ((linVar v a s : ℝ) ^ p + (linVar v b s : ℝ) ^ p)) := by
  have hia := integrable_pow_lin hmeas hlaw hindep a s p
  have hib := integrable_pow_lin hmeas hlaw hindep b s p
  have hpt : ∀ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p
      ≤ 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p) + (∑ i ∈ s, b i * X i ω) ^ (2 * p)) := by
    intro ω
    set x := (∑ i ∈ s, a i * X i ω) ^ 2 with hx
    set y := (∑ i ∈ s, b i * X i ω) ^ 2 with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hmax : x + y ≤ 2 * max x y := by
      rcases le_total x y with h | h
      · simp [max_eq_right h]; linarith
      · simp [max_eq_left h]; linarith
    have h1 : (x + y) ^ p ≤ (2 * max x y) ^ p :=
      pow_le_pow_left₀ (by positivity) hmax p
    have h2 : (2 * max x y) ^ p = 2 ^ p * max x y ^ p := by rw [mul_pow]
    have h3 : max x y ^ p ≤ x ^ p + y ^ p := by
      rcases le_total x y with h | h
      · rw [max_eq_right h]
        have : (0 : ℝ) ≤ x ^ p := by positivity
        linarith
      · rw [max_eq_left h]
        have : (0 : ℝ) ≤ y ^ p := by positivity
        linarith
    have hxp : x ^ p = (∑ i ∈ s, a i * X i ω) ^ (2 * p) := by
      rw [hx, ← pow_mul]
    have hyp : y ^ p = (∑ i ∈ s, b i * X i ω) ^ (2 * p) := by
      rw [hy, ← pow_mul]
    calc (x + y) ^ p ≤ 2 ^ p * max x y ^ p := by rw [← h2]; exact h1
      _ ≤ 2 ^ p * (x ^ p + y ^ p) := by
          have : (0 : ℝ) ≤ 2 ^ p := by positivity
          exact mul_le_mul_of_nonneg_left h3 this
      _ = _ := by rw [hxp, hyp]
  have hint : Integrable (fun ω => 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
      + (∑ i ∈ s, b i * X i ω) ^ (2 * p))) P := (hia.add hib).const_mul _
  have hle := integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hint
    (Filter.Eventually.of_forall hpt)
  calc ∫ ω, ((∑ i ∈ s, a i * X i ω) ^ 2 + (∑ i ∈ s, b i * X i ω) ^ 2) ^ p ∂P
      ≤ ∫ ω, 2 ^ p * ((∑ i ∈ s, a i * X i ω) ^ (2 * p)
          + (∑ i ∈ s, b i * X i ω) ^ (2 * p)) ∂P := hle
    _ = 2 ^ p * (dfac p * ((linVar v a s : ℝ) ^ p + (linVar v b s : ℝ) ^ p)) := by
        rw [integral_const_mul, integral_add hia hib, integral_pow_lin hmeas hlaw hindep,
          integral_pow_lin hmeas hlaw hindep]
        ring

end MomentBound

section Block

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Conditioning on an independent block.**  If `U` and `V` are independent, an integral of
`F(U, V)` is the iterated integral against their laws: the outer variable `V` may be frozen and
the inner integral computed against the law of `U` alone. -/
theorem integral_indep_pair {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ} (hF : Integrable F ((P.map U).prod (P.map V))) :
    ∫ ω, F (U ω, V ω) ∂P = ∫ y, (∫ x, F (x, y) ∂(P.map U)) ∂(P.map V) := by
  have hpair : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  have hmap := integral_map (μ := P) (φ := fun ω => (U ω, V ω)) (f := F)
    (hU.prodMk hV).aemeasurable (by rw [hpair]; exact hF.aestronglyMeasurable)
  rw [hpair] at hmap
  rw [← hmap, integral_prod_symm F hF]

/-- The same, as an upper bound: a uniform bound on the inner (conditional) integral gives a
bound on the whole integral. -/
theorem integral_indep_pair_le {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ} (hF : Integrable F ((P.map U).prod (P.map V)))
    {g : β → ℝ} (hg : Integrable g (P.map V))
    (hbound : ∀ᵐ y ∂(P.map V), (∫ x, F (x, y) ∂(P.map U)) ≤ g y) :
    ∫ ω, F (U ω, V ω) ∂P ≤ ∫ y, g y ∂(P.map V) := by
  rw [integral_indep_pair hU hV h hF]
  exact integral_mono_ae hF.integral_prod_right hg hbound

/-- **Tonelli across an independent pair.**  For a nonnegative measurable `F`, no integrability
is needed: the integral of `F(U, V)` is the iterated integral against the two laws.  This is what
lets the conditional bound be proved without assuming integrability first. -/
theorem lintegral_indep_pair {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (U ω, V ω) ∂P = ∫⁻ y, (∫⁻ x, F (x, y) ∂(P.map U)) ∂(P.map V) := by
  have hpair : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 h
  rw [← lintegral_map hF (hU.prodMk hV), hpair, lintegral_prod_symm' F hF]

/-- The same, as an upper bound from a bound on the inner (conditional) integral. -/
theorem lintegral_indep_pair_le {U : Ω → α} {V : Ω → β} (hU : Measurable U) (hV : Measurable V)
    (h : IndepFun U V P) {F : α × β → ℝ≥0∞} (hF : Measurable F) {c : ℝ≥0∞}
    (hbound : ∀ y, (∫⁻ x, F (x, y) ∂(P.map U)) ≤ c) [IsProbabilityMeasure P] :
    ∫⁻ ω, F (U ω, V ω) ∂P ≤ c := by
  rw [lintegral_indep_pair hU hV h hF]
  calc ∫⁻ y, (∫⁻ x, F (x, y) ∂(P.map U)) ∂(P.map V)
      ≤ ∫⁻ _y, c ∂(P.map V) := lintegral_mono hbound
    _ = c := by
        rw [lintegral_const]
        simp

end Block

section Glue

variable {ι : Type*} [DecidableEq ι]

/-- Glue two coordinate blocks into a full sample point, filling the rest with `0`. -/
def glue (S T : Finset ι) (p : (S → ℝ) × (T → ℝ)) : ι → ℝ := fun c =>
  if h : c ∈ S then p.1 ⟨c, h⟩ else if h' : c ∈ T then p.2 ⟨c, h'⟩ else 0

theorem measurable_glue (S T : Finset ι) : Measurable (glue S T) := by
  refine Measurable.of_eval fun c => ?_
  by_cases h : c ∈ S
  · simpa [glue, h] using (measurable_fst.eval : Measurable fun p : (S → ℝ) × (T → ℝ) => p.1 _)
  · by_cases h' : c ∈ T
    · simpa [glue, h, h'] using
        (measurable_snd.eval : Measurable fun p : (S → ℝ) × (T → ℝ) => p.2 _)
    · simp only [glue, h, h', ↓reduceDIte]
      exact measurable_const

/-- Gluing the two blocks of `ω` back together reproduces `ω` on `S ∪ T`. -/
theorem glue_agree (S T : Finset ι) (ω : ι → ℝ) {c : ι} (hc : c ∈ S ∪ T) :
    glue S T ((fun c : S => ω c), (fun c : T => ω c)) c = ω c := by
  simp only [glue]
  by_cases h : c ∈ S
  · simp [h]
  · have h' : c ∈ T := by
      rcases Finset.mem_union.1 hc with h'' | h''
      · exact absurd h'' h
      · exact h''
    simp [h, h']

/-- **A quantity that reads only `S ∪ T` is a function of the two blocks.**  This is the shape
required by `integral_indep_pair`. -/
theorem eq_glue_of_congr {V : Type*} (S T : Finset ι) (g : (ι → ℝ) → V)
    (hg : ∀ ω ω' : ι → ℝ, (∀ c ∈ S ∪ T, ω c = ω' c) → g ω = g ω') (ω : ι → ℝ) :
    g ω = (fun p => g (glue S T p)) ((fun c : S => ω c), (fun c : T => ω c)) :=
  hg _ _ fun _ hc => (glue_agree S T ω hc).symm

end Glue

end RBM.Gauss
