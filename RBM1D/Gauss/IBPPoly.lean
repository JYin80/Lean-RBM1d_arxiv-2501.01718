/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuad
import RBM1D.Gauss.LDEDiag
import RBM1D.Gauss.SteinMatrix

/-!
# Discharging `GaussIBP` — T104

`RBM1D/Gauss/LDEQuad.lean` carries the structure `RBM.Gauss.GaussIBP` with two fields:

* `stein` — Gaussian integration by parts against a `Tame` (continuous, finitely dependent,
  **polynomially** bounded) integrand;
* `polyInt` — all polynomial moments of `P d` are finite.

Its header suggests deriving `stein` from `RBM.Gauss.matrixStein` (T70, which assumes the
integrand *globally bounded*) by a smooth cutoff.  That detour is unnecessary: the
one-dimensional identity `RBM.integral_mul_gaussianReal` of `RBM1D/Gauss/Stein.lean` already
takes **integrability** hypotheses rather than boundedness — `RBM.Gauss.matrixStein` merely uses
its bounded corollary.  So the same fibrewise argument, with "bounded" replaced by "polynomially
bounded, hence integrable", proves `stein` directly.

## Main statements

* `RBM.Gauss.integrable_polyW_pow` : `polyInt`
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Finset

open scoped NNReal

variable {d : Dims}

/-! ### An elementary inequality -/

/-- `(a+b)^n ≤ 2^n (a^n + b^n)` for `a, b ≥ 0`. -/
theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ 2 ^ n * (a ^ n + b ^ n) := by
  have h0 : 0 ≤ max a b := le_max_of_le_left ha
  have hmax : a + b ≤ 2 * max a b := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (a + b) ^ n ≤ (2 * max a b) ^ n := pow_le_pow_left₀ (by linarith) hmax n
    _ = 2 ^ n * max a b ^ n := by rw [mul_pow]
    _ ≤ 2 ^ n * (a ^ n + b ^ n) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total a b with h | h
        · rw [max_eq_right h]
          have : (0 : ℝ) ≤ a ^ n := pow_nonneg ha n
          linarith
        · rw [max_eq_left h]
          have : (0 : ℝ) ≤ b ^ n := pow_nonneg hb n
          linarith

/-! ### All polynomial moments are finite -/

/-- `|ω_c|^n` is integrable. -/
theorem integrable_abs_pow_coord (d : Dims) (c : Coord d) (n : ℕ) :
    Integrable (fun ω : Ω d => |ω c| ^ n) (P d) := by
  have h := (integrable_pow_coord d c n).abs
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  show |ω c ^ n| = |ω c| ^ n
  rw [abs_pow]

theorem continuous_polyW (I : Finset (Coord d)) : Continuous fun ω : Ω d => polyW I ω := by
  refine continuous_const.add ?_
  exact continuous_finsetSum _ fun c _ => (continuous_apply c).abs

/-- **`polyInt`**: every polynomial moment of `P d` is finite.  Induction on the finite set of
coordinates, using `(a+b)^n ≤ 2^n(a^n+b^n)` and the one-coordinate moments. -/
theorem integrable_polyW_pow (d : Dims) (I : Finset (Coord d)) (n : ℕ) :
    Integrable (fun ω : Ω d => polyW I ω ^ n) (P d) := by
  classical
  induction I using Finset.induction generalizing n with
  | empty =>
      have h : ∀ ω : Ω d, polyW (∅ : Finset (Coord d)) ω ^ n = 1 := by
        intro ω; simp [polyW]
      simp only [h]
      exact integrable_const 1
  | insert c I hc ih =>
      have hsplit : ∀ ω : Ω d, polyW (insert c I) ω = polyW I ω + |ω c| := by
        intro ω
        show 1 + ∑ x ∈ insert c I, |ω x| = (1 + ∑ x ∈ I, |ω x|) + |ω c|
        rw [Finset.sum_insert hc]
        ring
      have hmaj : Integrable
          (fun ω : Ω d => 2 ^ n * (polyW I ω ^ n + |ω c| ^ n)) (P d) :=
        ((ih n).add (integrable_abs_pow_coord d c n)).const_mul _
      refine Integrable.mono' hmaj
        (((continuous_polyW (insert c I)).pow n).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      have hp : (0 : ℝ) ≤ polyW I ω := (polyW_nonneg I ω)
      have hq : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      have hb := add_pow_le_two_pow_mul hp hq n
      rw [Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (polyW_nonneg (insert c I) ω) n), hsplit ω]
      exact hb

/-! ### One-dimensional Stein, with integrability instead of boundedness

`RBM.integral_mul_gaussianReal` already takes integrability hypotheses, but stated against the
density.  These are the same statements with the hypotheses against the measure, which is the
form the fibrewise argument produces. -/

/-- The real one-dimensional Stein identity, hypotheses stated against the Gaussian measure. -/
theorem integral_mul_gaussianReal_int {var : ℝ≥0} (hv : var ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal 0 var))
    (hxfi : Integrable (fun x : ℝ => x * f x) (gaussianReal 0 var))
    (hf'i : Integrable f' (gaussianReal 0 var)) :
    ∫ x : ℝ, x * f x ∂(gaussianReal 0 var)
      = (var : ℝ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  refine integral_mul_gaussianReal hv hf ?_ (integrable_mul_gaussianPDFReal hv hf'i)
    (integrable_mul_gaussianPDFReal hv hfi)
  have hv' : (var : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have h := integrable_mul_gaussianPDFReal hv (hxfi.const_mul (-(1 / (var : ℝ))))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show -(1 / (var : ℝ)) * (x * f x) * gaussianPDFReal 0 var x
    = f x * (-(x / (var : ℝ)) * gaussianPDFReal 0 var x)
  field_simp

/-- The complex one-dimensional Stein identity, hypotheses stated against the Gaussian measure
and with no restriction on the variance. -/
theorem integral_mul_gaussianReal_complex_int {var : ℝ≥0} {f f' : ℝ → ℂ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal 0 var))
    (hxfi : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var))
    (hf'i : Integrable f' (gaussianReal 0 var)) :
    ∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)
      = ((var : ℝ) : ℂ) * ∫ x : ℝ, f' x ∂(gaussianReal 0 var) := by
  by_cases hv : var = 0
  · subst hv
    simp [gaussianReal_zero_var]
  -- real and imaginary parts
  have hre : ∀ x, HasDerivAt (fun y : ℝ => (f y).re) ((f' x).re) x := by
    intro x
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simpa only [Function.comp_def, Complex.reCLM_apply] using h
  have him : ∀ x, HasDerivAt (fun y : ℝ => (f y).im) ((f' x).im) x := by
    intro x
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hf x)
    simpa only [Function.comp_def, Complex.imCLM_apply] using h
  have hxre : Integrable (fun x : ℝ => x * (f x).re) (gaussianReal 0 var) := by
    refine hxfi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    show ((x : ℂ) * f x).re = x * (f x).re
    simp [Complex.mul_re]
  have hxim : Integrable (fun x : ℝ => x * (f x).im) (gaussianReal 0 var) := by
    refine hxfi.im.congr (Filter.Eventually.of_forall fun x => ?_)
    show ((x : ℂ) * f x).im = x * (f x).im
    simp [Complex.mul_im]
  have hR := integral_mul_gaussianReal_int hv hre hfi.re hxre hf'i.re
  have hI := integral_mul_gaussianReal_int hv him hfi.im hxim hf'i.im
  -- assemble
  have hIl : Integrable (fun x : ℝ => (x : ℂ) * f x) (gaussianReal 0 var) := hxfi
  have hlre : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, x * (f x).re ∂(gaussianReal 0 var) := by
    have h := (Complex.reCLM.integral_comp_comm hIl).symm
    simp only [Complex.reCLM_apply] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.mul_re])
  have hlim : (∫ x : ℝ, (x : ℂ) * f x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, x * (f x).im ∂(gaussianReal 0 var) := by
    have h := (Complex.imCLM.integral_comp_comm hIl).symm
    simp only [Complex.imCLM_apply] at h
    rw [h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.mul_im])
  have hrre : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).re
      = ∫ x : ℝ, (f' x).re ∂(gaussianReal 0 var) := by
    have h := (Complex.reCLM.integral_comp_comm hf'i).symm
    simpa only [Complex.reCLM_apply] using h
  have hrim : (∫ x : ℝ, f' x ∂(gaussianReal 0 var)).im
      = ∫ x : ℝ, (f' x).im ∂(gaussianReal 0 var) := by
    have h := (Complex.imCLM.integral_comp_comm hf'i).symm
    simpa only [Complex.imCLM_apply] using h
  refine Complex.ext ?_ ?_
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hlre, hrre]
    exact hR
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hlim, hrim]
    exact hI

/-! ### The fibrewise argument -/

/-- `|x|^k` is integrable for a centred Gaussian. -/
theorem integrable_abs_pow_gaussianReal (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 v) := by
  have h := (integrable_pow_gaussianReal v k).abs
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  show |x ^ k| = |x| ^ k
  rw [abs_pow]

/-- Updating one coordinate increases the polynomial weight by at most `|t|`. -/
theorem polyW_upd_le (d : Dims) (c : Coord d) (I : Finset (Coord d)) (p : Ω d × ℝ) :
    polyW I (upd d c p) ≤ polyW I p.1 + |p.2| := by
  classical
  have hterm : ∀ x ∈ I, |(upd d c p) x| ≤ |p.1 x| + (if x = c then |p.2| else 0) := by
    intro x _
    by_cases hx : x = c
    · subst hx
      rw [upd_self]
      simp
    · rw [upd_of_ne c p hx, ite_eq_right hx]
      simp
  have hsum : ∑ x ∈ I, |(upd d c p) x|
      ≤ ∑ x ∈ I, (|p.1 x| + (if x = c then |p.2| else 0)) :=
    Finset.sum_le_sum hterm
  have hsplit : ∑ x ∈ I, (|p.1 x| + (if x = c then |p.2| else 0))
      = (∑ x ∈ I, |p.1 x|) + ∑ x ∈ I, (if x = c then |p.2| else 0) :=
    Finset.sum_add_distrib
  have hlast : (∑ x ∈ I, (if x = c then |p.2| else 0)) ≤ |p.2| := by
    by_cases hc : c ∈ I
    · rw [Finset.sum_ite_eq' I c fun _ => |p.2|, ite_eq_left hc]
    · rw [Finset.sum_ite_eq' I c fun _ => |p.2|, ite_eq_right hc]
      exact abs_nonneg _
  show 1 + ∑ x ∈ I, |(upd d c p) x| ≤ (1 + ∑ x ∈ I, |p.1 x|) + |p.2|
  rw [hsplit] at hsum
  linarith

/-- The majorant used for the product integrability. -/
theorem norm_le_of_tame_upd (d : Dims) (c : Coord d) {f : Ω d → ℂ} {I : Finset (Coord d)}
    {n : ℕ} {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C * polyW I ω ^ n) (hC : 0 ≤ C) (p : Ω d × ℝ) :
    ‖f (upd d c p)‖ ≤ C * 2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n) := by
  refine (hb _).trans ?_
  have h1 : polyW I (upd d c p) ^ n ≤ (polyW I p.1 + |p.2|) ^ n :=
    pow_le_pow_left₀ (polyW_nonneg _ _) (polyW_upd_le d c I p) n
  have h2 : (polyW I p.1 + |p.2|) ^ n ≤ 2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n) :=
    add_pow_le_two_pow_mul (polyW_nonneg _ _) (abs_nonneg _) n
  calc C * polyW I (upd d c p) ^ n ≤ C * ((polyW I p.1 + |p.2|) ^ n) :=
        mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * (2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n)) := mul_le_mul_of_nonneg_left h2 hC
    _ = C * 2 ^ n * (polyW I p.1 ^ n + |p.2| ^ n) := by ring

/-- **`GaussIBP`, discharged.**  The same fibrewise argument as `RBM.Gauss.matrixStein`, with
"globally bounded" replaced by "polynomially bounded"; no smooth cutoff is needed, because the
one-dimensional identity only ever wanted integrability. -/
theorem gaussIBP (d : Dims) : GaussIBP d := by
  refine ⟨fun c g g' hg hg' hderiv => ?_, integrable_polyW_pow d⟩
  classical
  obtain ⟨Ig, ng, Cg, hgb0⟩ := hg.poly
  obtain ⟨Ig', ng', Cg', hg'b0⟩ := hg'.poly
  -- the constants may be taken nonnegative
  have hCg : (0 : ℝ) ≤ max Cg 0 := le_max_right _ _
  have hCg' : (0 : ℝ) ≤ max Cg' 0 := le_max_right _ _
  have hgb : ∀ ω, ‖g ω‖ ≤ max Cg 0 * polyW Ig ω ^ ng := fun ω =>
    (hgb0 ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (polyW_nonneg _ _) _))
  have hg'b : ∀ ω, ‖g' ω‖ ≤ max Cg' 0 * polyW Ig' ω ^ ng' := fun ω =>
    (hg'b0 ω).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (pow_nonneg (polyW_nonneg _ _) _))
  have hUm : Measurable (upd d c) := measurable_upd d c
  have hgm : Measurable g := hg.cont.measurable
  have hg'm : Measurable g' := hg'.cont.measurable
  have hfib : ∀ (ω : Ω d) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (Function.update ω c s)) (g' (Function.update ω c t)) t := by
    intro ω t
    simpa only [Function.update_idem, Function.update_self] using
      hderiv (Function.update ω c t)
  -- the three integrability facts on the product
  have hprodg : Integrable (fun p : Ω d × ℝ => g (upd d c p))
      ((P d).prod (gaussianReal 0 (gvar d c))) := by
    refine Integrable.mono'
      ((((integrable_polyW_pow d Ig ng).comp_fst _).add
        ((integrable_abs_pow_gaussianReal (gvar d c) ng).comp_snd _)).const_mul
          (max Cg 0 * 2 ^ ng))
      ((hgm.comp hUm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using norm_le_of_tame_upd d c hgb hCg p
  have hprodg' : Integrable (fun p : Ω d × ℝ => g' (upd d c p))
      ((P d).prod (gaussianReal 0 (gvar d c))) := by
    refine Integrable.mono'
      ((((integrable_polyW_pow d Ig' ng').comp_fst _).add
        ((integrable_abs_pow_gaussianReal (gvar d c) ng').comp_snd _)).const_mul
          (max Cg' 0 * 2 ^ ng'))
      ((hg'm.comp hUm).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    simpa using norm_le_of_tame_upd d c hg'b hCg' p
  have hprodx : Integrable (fun p : Ω d × ℝ => (p.2 : ℂ) * g (upd d c p))
      ((P d).prod (gaussianReal 0 (gvar d c))) := by
    have hmaj : Integrable
        (fun p : Ω d × ℝ => max Cg 0 * 2 ^ ng *
          (polyW Ig p.1 ^ ng * |p.2| + 1 * |p.2| ^ (ng + 1)))
        ((P d).prod (gaussianReal 0 (gvar d c))) := by
      refine Integrable.const_mul ?_ _
      refine Integrable.add ?_ ?_
      · exact (integrable_polyW_pow d Ig ng).mul_prod
          (by simpa using integrable_abs_pow_gaussianReal (gvar d c) 1)
      · exact (integrable_const (1 : ℝ)).mul_prod
          (integrable_abs_pow_gaussianReal (gvar d c) (ng + 1))
    refine Integrable.mono' hmaj
      (((Complex.continuous_ofReal.measurable.comp measurable_snd).mul
        (hgm.comp hUm)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => ?_)
    have hb := norm_le_of_tame_upd d c hgb hCg p
    have habs : (0 : ℝ) ≤ |p.2| := abs_nonneg _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |p.2| * ‖g (upd d c p)‖
        ≤ |p.2| * (max Cg 0 * 2 ^ ng * (polyW Ig p.1 ^ ng + |p.2| ^ ng)) :=
          mul_le_mul_of_nonneg_left hb habs
      _ = max Cg 0 * 2 ^ ng * (polyW Ig p.1 ^ ng * |p.2| + 1 * |p.2| ^ (ng + 1)) := by
          rw [pow_succ]; ring
  -- both sides through the resampling map
  have hL : ∫ ω, (ω c : ℂ) * g ω ∂(P d)
      = ∫ p : Ω d × ℝ, (p.2 : ℂ) * g (upd d c p)
          ∂((P d).prod (gaussianReal 0 (gvar d c))) := by
    conv_lhs => rw [← P_map_update d c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update d c]
      exact ((Complex.continuous_ofReal.measurable.comp
        (measurable_pi_apply c)).mul hgm).aestronglyMeasurable)]
    simp only [upd_self]
  have hR : ∫ ω, g' ω ∂(P d)
      = ∫ p : Ω d × ℝ, g' (upd d c p) ∂((P d).prod (gaussianReal 0 (gvar d c))) := by
    conv_lhs => rw [← P_map_update d c]
    rw [integral_map hUm.aemeasurable (by
      rw [P_map_update d c]
      exact hg'm.aestronglyMeasurable)]
  rw [hL, hR, integral_prod _ hprodx, integral_prod _ hprodg', ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hprodx.prod_right_ae, hprodg.prod_right_ae, hprodg'.prod_right_ae]
    with ω h1 h2 h3
  exact integral_mul_gaussianReal_complex_int (hfib ω) h2 h1 h3

end RBM.Gauss
