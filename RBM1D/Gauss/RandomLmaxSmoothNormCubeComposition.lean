/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.SmoothNormOuterHigherDerivatives
import RBM1D.Gauss.MultiaffineShiftedFaces
import RBM1D.Gauss.FiniteCubeRepeatedFTCLocal
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Abstract smooth-norm composition on a finite cube

This module proves the corrected deterministic finite-cube estimate from T1424.  It makes no
claim about a Gaussian source, a probability event, or manuscript formula (4.12).
-/

noncomputable section

open Finset Real Set
open scoped ContDiff BigOperators

namespace RBM.Gauss.RandomLmaxSmoothNormCubeComposition

open RBM.Gauss.PowerSumHigherDerivatives
open RBM.Gauss.SmoothNormOuterHigherDerivatives

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem qNorm_eq_piLp_norm (q : ℕ) (hq : 2 ≤ q)
    (x : ι → ℝ) :
    ‖(WithLp.toLp (q : ENNReal) x : PiLp (q : ENNReal) (fun _ : ι => ℝ))‖ = qNorm q x := by
  have hp : 0 < ((q : ENNReal).toReal) := by
    rw [ENNReal.toReal_natCast]
    exact_mod_cast (show 0 < q by omega)
  rw [PiLp.norm_eq_sum hp]
  unfold qNorm
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    simp [PiLp.toLp_apply, norm_eq_abs, ENNReal.toReal_natCast]
  · rw [ENNReal.toReal_natCast]
    congr 1
    field_simp

private theorem qNorm_mono_of_nonneg {q : ℕ} (hq : 0 < q) {x y : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    qNorm q x ≤ qNorm q y := by
  unfold qNorm
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) q
  · apply Finset.sum_le_sum
    intro i hi
    rw [abs_of_nonneg (hx i), abs_of_nonneg (le_trans (hx i) (hxy i))]
    exact pow_le_pow_left₀ (hx i) (hxy i) _
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem qNorm_nonneg_of_nonneg (q : ℕ) (x : ι → ℝ) :
    0 ≤ qNorm q x := qNorm_nonneg q x

private theorem qNorm_smul_of_nonneg (q : ℕ) (hq : 0 < q) {c : ℝ} (hc : 0 ≤ c)
    (x : ι → ℝ) : qNorm q (fun i => c * x i) = c * qNorm q x := by
  unfold qNorm
  have hsum : (∑ i, |c * x i| ^ q) = c ^ q * ∑ i, |x i| ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_mul, abs_of_nonneg hc, ← mul_pow]
  have hS : 0 ≤ ∑ i, |x i| ^ q := Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) q
  rw [hsum, Real.mul_rpow (pow_nonneg hc q) hS]
  rw [← Real.rpow_natCast c q, ← Real.rpow_mul hc]
  rw [show (q : ℝ) * (q : ℝ)⁻¹ = 1 by
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp]
  rw [Real.rpow_one]

private theorem multiaffineInterpOn_nonneg {κ : Type*} [DecidableEq κ]
    (coords : List κ) (b : κ → Bool)
    (a : (κ → Bool) → (ι → ℝ)) (t : κ → ℝ)
    (ht : ∀ i ∈ coords, 0 ≤ t i ∧ t i ≤ 1)
    (ha : ∀ v i, 0 ≤ a v i) :
    ∀ i, 0 ≤ RBM.Gauss.multiaffineInterpOn coords b a t i := by
  induction coords generalizing b with
  | nil =>
      intro i
      exact ha b i
  | cons j js ih =>
      intro i
      have hj := ht j (by simp)
      have hj0 := ih (b := Function.update b j false)
        (fun k hk => ht k (List.mem_cons_of_mem _ hk)) i
      have hj1 := ih (b := Function.update b j true)
        (fun k hk => ht k (List.mem_cons_of_mem _ hk)) i
      simp only [RBM.Gauss.multiaffineInterpOn]
      exact add_nonneg (mul_nonneg (by linarith [hj.2]) hj0)
        (mul_nonneg hj.1 hj1)

private theorem multiaffineInterpOn_lower_vertex {κ : Type*} [DecidableEq κ]
    (coords : List κ) (b : κ → Bool)
    (a : (κ → Bool) → (ι → ℝ)) (t : κ → ℝ)
    (ht : ∀ i ∈ coords, 0 ≤ t i ∧ t i ≤ 1)
    (ha : ∀ v i, 0 ≤ a v i) :
    ∃ v : κ → Bool, ∀ i,
      (2 : ℝ)⁻¹ ^ coords.length * a v i ≤
        RBM.Gauss.multiaffineInterpOn coords b a t i := by
  induction coords generalizing b with
  | nil =>
      refine ⟨b, ?_⟩
      intro i
      simp [RBM.Gauss.multiaffineInterpOn]
  | cons j js ih =>
      have hj := ht j (by simp)
      by_cases hhalf : t j ≤ (1 : ℝ) / 2
      · obtain ⟨v, hv⟩ := ih (b := Function.update b j false)
          (fun k hk => ht k (List.mem_cons_of_mem _ hk))
        refine ⟨v, ?_⟩
        intro i
        have hnonneg0 := multiaffineInterpOn_nonneg (ι := ι) js
          (Function.update b j false) a t (fun k hk => ht k (List.mem_cons_of_mem _ hk)) ha i
        have hnonneg1 := multiaffineInterpOn_nonneg (ι := ι) js
          (Function.update b j true) a t (fun k hk => ht k (List.mem_cons_of_mem _ hk)) ha i
        have hcoef : (1 : ℝ) / 2 ≤ 1 - t j := by linarith
        have hsel := hv i
        have hwa : 0 ≤ (2 : ℝ)⁻¹ ^ js.length * a v i :=
          mul_nonneg (by positivity) (ha v i)
        have hweight : 0 ≤ 1 - t j := by linarith [hj.2]
        have hsmall : ((1 : ℝ) / 2) * ((2 : ℝ)⁻¹ ^ js.length * a v i) ≤
            (1 - t j) * ((2 : ℝ)⁻¹ ^ js.length * a v i) :=
          mul_le_mul_of_nonneg_right hcoef hwa
        have hface := mul_le_mul_of_nonneg_left hsel hweight
        have hother : 0 ≤ t j * RBM.Gauss.multiaffineInterpOn js
            (Function.update b j true) a t i := mul_nonneg hj.1 hnonneg1
        simp only [RBM.Gauss.multiaffineInterpOn]
        calc
          (2 : ℝ)⁻¹ ^ (js.length + 1) * a v i =
              ((1 : ℝ) / 2) * ((2 : ℝ)⁻¹ ^ js.length * a v i) := by
                rw [pow_succ]
                ring
          _ ≤ (1 - t j) * RBM.Gauss.multiaffineInterpOn js
                (Function.update b j false) a t i +
              t j * RBM.Gauss.multiaffineInterpOn js
                (Function.update b j true) a t i := by
                  calc
                    _ ≤ (1 - t j) * ((2 : ℝ)⁻¹ ^ js.length * a v i) := hsmall
                    _ ≤ (1 - t j) * RBM.Gauss.multiaffineInterpOn js
                          (Function.update b j false) a t i := hface
                    _ ≤ _ := by nlinarith
      · obtain ⟨v, hv⟩ := ih (b := Function.update b j true)
          (fun k hk => ht k (List.mem_cons_of_mem _ hk))
        refine ⟨v, ?_⟩
        intro i
        have hnonneg0 := multiaffineInterpOn_nonneg (ι := ι) js
          (Function.update b j false) a t (fun k hk => ht k (List.mem_cons_of_mem _ hk)) ha i
        have hnonneg1 := multiaffineInterpOn_nonneg (ι := ι) js
          (Function.update b j true) a t (fun k hk => ht k (List.mem_cons_of_mem _ hk)) ha i
        have hcoef : (1 : ℝ) / 2 ≤ t j := by linarith
        have hsel := hv i
        have hwa : 0 ≤ (2 : ℝ)⁻¹ ^ js.length * a v i :=
          mul_nonneg (by positivity) (ha v i)
        have hweight : 0 ≤ t j := hj.1
        have hsmall : ((1 : ℝ) / 2) * ((2 : ℝ)⁻¹ ^ js.length * a v i) ≤
            t j * ((2 : ℝ)⁻¹ ^ js.length * a v i) :=
          mul_le_mul_of_nonneg_right hcoef hwa
        have hface := mul_le_mul_of_nonneg_left hsel hweight
        have hother : 0 ≤ (1 - t j) * RBM.Gauss.multiaffineInterpOn js
            (Function.update b j false) a t i :=
          mul_nonneg (by linarith [hj.2]) hnonneg0
        simp only [RBM.Gauss.multiaffineInterpOn]
        calc
          (2 : ℝ)⁻¹ ^ (js.length + 1) * a v i =
              ((1 : ℝ) / 2) * ((2 : ℝ)⁻¹ ^ js.length * a v i) := by
                rw [pow_succ]
                ring
          _ ≤ (1 - t j) * RBM.Gauss.multiaffineInterpOn js
                (Function.update b j false) a t i +
              t j * RBM.Gauss.multiaffineInterpOn js
                (Function.update b j true) a t i := by
                  calc
                    _ ≤ t j * ((2 : ℝ)⁻¹ ^ js.length * a v i) := hsmall
                    _ ≤ t j * RBM.Gauss.multiaffineInterpOn js
                          (Function.update b j true) a t i := hface
                    _ ≤ _ := by nlinarith

private theorem qNorm_lower_on_unitCube (M r q : ℕ) (c Γ : ℝ)
    (hq : 0 < q) (hrM : r ≤ M)
    (a : (Fin r → Bool) → (ι → ℝ))
    (hΓ : 0 < Γ) (hc : 0 < c)
    (ha : ∀ v i, 0 ≤ a v i)
    (hlower : ∀ v, c * Γ ≤ qNorm q (a v))
    (t : Fin r → ℝ) (ht : t ∈ RBM.Gauss.unitCoordinateCube r) :
    (2 : ℝ) ^ (-(M : ℤ) : ℝ) * min c 1 * Γ ≤
      qNorm q (RBM.Gauss.multiaffineInterpolation a t) := by
  have ht' : ∀ i ∈ (Finset.univ : Finset (Fin r)).toList,
      0 ≤ t i ∧ t i ≤ 1 := by
    intro i hi
    have h := ht i
    simpa only [Set.mem_Icc] using h
  obtain ⟨v, hv⟩ := multiaffineInterpOn_lower_vertex (κ := Fin r)
    (Finset.univ.toList) (fun _ => false) a t ht' ha
  have hpoint : ∀ i : ι,
      (2 : ℝ)⁻¹ ^ ((Finset.univ : Finset (Fin r)).toList.length) * a v i ≤
        (RBM.Gauss.multiaffineInterpolation (ι := Fin r) (V := ι → ℝ) a t) i := by
    intro i
    simpa [RBM.Gauss.multiaffineInterpolation] using hv i
  have hlen : (Finset.univ : Finset (Fin r)).toList.length = r := by simp
  have hscale : (2 : ℝ)⁻¹ ^ r = 2 ^ (-(r : ℤ) : ℝ) := by
    calc
      (2 : ℝ)⁻¹ ^ r = (2 : ℝ)⁻¹ ^ (r : ℝ) := by rw [← Real.rpow_natCast]
      _ = ((2 : ℝ) ^ (r : ℝ))⁻¹ :=
        Real.inv_rpow (x := 2) (by norm_num) (r : ℝ)
      _ = (2 : ℝ) ^ (-(r : ℝ)) := by rw [Real.rpow_neg (by norm_num)]
      _ = (2 : ℝ) ^ (-(r : ℤ) : ℝ) := by congr 1 <;> simp
  have hnorm := qNorm_mono_of_nonneg (q := q) hq
      (fun i => mul_nonneg (by positivity) (ha v i)) hpoint
  rw [hlen, hscale, qNorm_smul_of_nonneg q hq (by positivity)] at hnorm
  have hM : (2 : ℝ) ^ (-(M : ℤ) : ℝ) ≤ (2 : ℝ) ^ (-(r : ℤ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    simp only [neg_le_neg_iff]
    exact_mod_cast hrM
  have hmin : min c 1 ≤ c := min_le_left _ _
  have hminpos : 0 < min c 1 := lt_min hc zero_lt_one
  have hcmp : (2 : ℝ) ^ (-(M : ℤ) : ℝ) * min c 1 * Γ ≤
      (2 : ℝ) ^ (-(r : ℤ) : ℝ) * qNorm q (a v) := by
    have hfactor : 0 ≤ (2 : ℝ) ^ (-(r : ℤ) : ℝ) := Real.rpow_nonneg (by norm_num) _
    calc
      (2 : ℝ) ^ (-(M : ℤ) : ℝ) * min c 1 * Γ ≤
          (2 : ℝ) ^ (-(r : ℤ) : ℝ) * min c 1 * Γ := by
            have h := mul_le_mul_of_nonneg_right hM (mul_nonneg hminpos.le hΓ.le)
            nlinarith [h]
      _ ≤ (2 : ℝ) ^ (-(r : ℤ) : ℝ) * c * Γ := by
            have h := mul_le_mul_of_nonneg_right hmin (mul_nonneg hfactor hΓ.le)
            nlinarith [h]
      _ ≤ (2 : ℝ) ^ (-(r : ℤ) : ℝ) * qNorm q (a v) := by
            calc
              (2 : ℝ) ^ (-(r : ℤ) : ℝ) * c * Γ =
                  (2 : ℝ) ^ (-(r : ℤ) : ℝ) * (c * Γ) := by ring
              _ ≤ (2 : ℝ) ^ (-(r : ℤ) : ℝ) * qNorm q (a v) :=
                mul_le_mul_of_nonneg_left (hlower v) hfactor
  exact hcmp.trans hnorm

private def reverseAxisDirections {r : ℕ} :
    (coords : List (Fin r)) → Fin coords.length → (Fin r → ℝ)
  | [] => fun j => Fin.elim0 j
  | i :: js => Fin.lastCases (Pi.single i 1) (fun j => reverseAxisDirections js j)

private theorem cubePartial_eq_fderiv_axis {r : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin r → ℝ) → V} (t : Fin r → ℝ)
    (hf : DifferentiableAt ℝ f t) (i : Fin r) :
    RBM.Gauss.cubePartial i f t =
      fderiv ℝ f t (Pi.single i (1 : ℝ)) := by
  let e : Fin r → ℝ := Pi.single i 1
  let line : ℝ → (Fin r → ℝ) := fun s => Function.update t i s
  have hlineEq : line = fun s => (t - t i • e) + s • e := by
    funext s
    ext j
    by_cases hji : j = i
    · subst j
      simp [line, e]
    · simp [line, e, Function.update_of_ne hji, Pi.single_eq_of_ne hji]
  have hline : HasDerivAt line e (t i) := by
    rw [hlineEq]
    have hc : HasDerivAt (fun _ : ℝ => t - t i • e) 0 (t i) := hasDerivAt_const _ _
    have hs : HasDerivAt (fun s : ℝ => s • e) e (t i) := by
      simpa using (hasDerivAt_id (t i)).smul_const e
    convert hc.add hs using 1 <;> simp
  have hlineval : line (t i) = t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [line]
    · simp [line, Function.update_of_ne hji]
  have houter : HasFDerivAt f (fderiv ℝ f t) (line (t i)) := by
    simpa [hlineval] using hf.hasFDerivAt
  have hcomp := HasFDerivAt.comp_hasDerivAt (t i) houter hline
  change deriv (fun s => f (line s)) (t i) = _
  exact hcomp.deriv

private theorem iteratedFDeriv_reverseAxes_eq_cubeMixedPartial {r : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin r → ℝ) → V} (coords : List (Fin r)) (t : Fin r → ℝ)
    (hf : ContDiff ℝ coords.length f) :
    (iteratedFDeriv ℝ coords.length f t (reverseAxisDirections coords)) =
      RBM.Gauss.cubeMixedPartial coords f t := by
  induction coords generalizing f with
  | nil => simp [RBM.Gauss.cubeMixedPartial, reverseAxisDirections]
  | cons i js ih =>
      have hfn : ContDiff ℝ (js.length + 1) f := by simpa using hf
      have hderiv : ContDiff ℝ js.length
          (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
            fderiv ℝ f p.1 p.2) := by
        exact hfn.contDiff_fderiv_apply (by simp)
      let e : Fin r → ℝ := Pi.single i 1
      have hpair : ContDiff ℝ js.length (fun y : Fin r → ℝ => (y, e)) := by fun_prop
      have hrestricted : ContDiff ℝ js.length (fun y => fderiv ℝ f y e) :=
        hderiv.comp hpair
      have hfderiv : ContDiff ℝ js.length (fun y => fderiv ℝ f y) :=
        hfn.fderiv_right (by simp)
      let ev : ((Fin r → ℝ) →L[ℝ] V) →L[ℝ] V :=
        ContinuousLinearMap.apply ℝ V e
      have heval : (fun y => fderiv ℝ f y e) = ev ∘ (fun y => fderiv ℝ f y) := by
        rfl
      have hfdAt : ContDiffAt ℝ js.length (fun y => fderiv ℝ f y) t :=
        hfderiv.contDiffAt
      have hcomp := ev.iteratedFDeriv_comp_left
        (f := fun y => fderiv ℝ f y) hfdAt (i := js.length) le_rfl
      let dirs : Fin (js.length + 1) → (Fin r → ℝ) :=
        reverseAxisDirections (i :: js)
      have hmain := iteratedFDeriv_succ_apply_right
        (𝕜 := ℝ) (E := Fin r → ℝ)
        (f := f) (x := t) (n := js.length) dirs
      have hinit : Fin.init dirs = reverseAxisDirections js := by
        funext j
        simp [Fin.init, dirs, reverseAxisDirections]
      have hlast : dirs (Fin.last js.length) = e := by
        simp [dirs, reverseAxisDirections, e]
      have hdiff : Differentiable ℝ f := hfn.differentiable (by simp)
      have hcubeEq : (fun y => fderiv ℝ f y e) =
          (fun y => RBM.Gauss.cubePartial i f y) := by
        funext y
        exact (cubePartial_eq_fderiv_axis y (hdiff.differentiableAt) i).symm
      change (iteratedFDeriv ℝ (js.length + 1) f t) dirs =
        RBM.Gauss.cubeMixedPartial (i :: js) f t
      rw [hmain, hinit, hlast]
      have hscalar :
          iteratedFDeriv ℝ js.length (fun y => fderiv ℝ f y e) t =
            ev.compContinuousMultilinearMap
              (iteratedFDeriv ℝ js.length (fun y => fderiv ℝ f y) t) := by
        rw [heval]
        exact hcomp
      have hrestricted' : ContDiff ℝ js.length (fun y => cubePartial i f y) := by
        rw [← hcubeEq]
        exact hrestricted
      have hpartial := ih (f := fun y => cubePartial i f y) hrestricted'
      have hscalarCube := hscalar
      rw [hcubeEq] at hscalarCube
      have hscalarEval := congrArg (fun L => L (reverseAxisDirections js)) hscalarCube
      have hscalarEq :
          iteratedFDeriv ℝ js.length (fun y => cubePartial i f y) t
              (reverseAxisDirections js) =
            ((iteratedFDeriv ℝ js.length (fun y => fderiv ℝ f y) t)
              (reverseAxisDirections js)) e := by
        simpa [ev] using hscalarEval
      exact hscalarEq.symm.trans hpartial

private theorem iteratedFDeriv_comp_apply_sum
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) (f : E → F) (g : F → G) (x : E) (v : Fin k → E)
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g (f x)) :
    (iteratedFDeriv ℝ k (g ∘ f) x) v =
      ∑ c : OrderedFinpartition k,
        (iteratedFDeriv ℝ c.length g (f x))
          (fun m => (iteratedFDeriv ℝ (c.partSize m) f x)
            (fun j => v (c.emb m j))) := by
  have hcomp := iteratedFDeriv_comp hg hf (i := k) le_rfl
  change (iteratedFDeriv ℝ k (g ∘ f) x) v = _
  rw [hcomp]
  simp [FormalMultilinearSeries.taylorComp,
    OrderedFinpartition.compAlongOrderedFinpartition,
    OrderedFinpartition.compAlongOrderFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, smul_eq_mul]
  simp only [ftaylorSeries]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1

private theorem continuousLinearMap_multiaffineInterpOn
    {κ : Type*} [Fintype κ] [DecidableEq κ] {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (coords : List κ) (b : κ → Bool)
    (a : (κ → Bool) → V) (t : κ → ℝ) :
    L (RBM.Gauss.multiaffineInterpOn coords b a t) =
      RBM.Gauss.multiaffineInterpOn coords b (fun v => L (a v)) t := by
  induction coords generalizing b with
  | nil => rfl
  | cons i is ih =>
      simp only [RBM.Gauss.multiaffineInterpOn]
      rw [map_add, map_smul, map_smul, ih (Function.update b i false),
        ih (Function.update b i true)]

private theorem continuousLinearMap_shiftedDifferenceList
    {κ : Type*} [Fintype κ] [DecidableEq κ] {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (coords : List κ) (a : (κ → Bool) → V) (b : κ → Bool) :
    L (RBM.Gauss.shiftedDifferenceList coords a b) =
      RBM.Gauss.shiftedDifferenceList coords (fun v => L (a v)) b := by
  induction coords generalizing a with
  | nil => rfl
  | cons i is ih =>
      simp only [RBM.Gauss.shiftedDifferenceList]
      rw [ih (a := RBM.Gauss.shiftedDifference i a)]
      have hfun : (fun v => L (RBM.Gauss.shiftedDifference i a v)) =
            RBM.Gauss.shiftedDifference i (fun v => L (a v)) := by
        funext v
        simp [RBM.Gauss.shiftedDifference, map_sub]
      rw [hfun]

private theorem multiaffineInterpOn_perm {κ : Type*} [Fintype κ] [DecidableEq κ] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {xs ys : List κ} (hperm : xs.Perm ys)
    (hnd : xs.Nodup) (b : κ → Bool) (a : (κ → Bool) → V) (t : κ → ℝ) :
    RBM.Gauss.multiaffineInterpOn xs b a t =
      RBM.Gauss.multiaffineInterpOn ys b a t := by
  induction hperm generalizing b a t with
  | nil => rfl
  | cons i hperm ih =>
      have hnd' : List.Nodup _ := (List.nodup_cons.mp hnd).2
      simp only [RBM.Gauss.multiaffineInterpOn]
      rw [ih hnd' (Function.update b i false) a t,
        ih hnd' (Function.update b i true) a t]
  | swap x y rest =>
      have hxy : x ≠ y := by
        intro hxy
        have hnot := (List.nodup_cons.mp hnd).1
        apply hnot
        simp [hxy]
      simp only [RBM.Gauss.multiaffineInterpOn, Function.update_comm hxy]
      module
  | trans h₁ h₂ ih₁ ih₂ =>
      have hnd' : List.Nodup _ := h₁.nodup_iff.mp hnd
      exact (ih₁ hnd b a t).trans (ih₂ hnd' b a t)

private theorem multiaffineInterpOn_contDiff {κ : Type*} [Fintype κ] [DecidableEq κ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (coords : List κ) (b : κ → Bool) (a : (κ → Bool) → V) :
    ContDiff ℝ n (fun t => RBM.Gauss.multiaffineInterpOn coords b a t) := by
  induction coords generalizing b with
  | nil => exact contDiff_const
  | cons i is ih =>
      simp only [RBM.Gauss.multiaffineInterpOn]
      have h0 := ih (Function.update b i false)
      have h1 := ih (Function.update b i true)
      have hc0 : ContDiff ℝ n (fun t : κ → ℝ => (1 - t i : ℝ)) := by fun_prop
      have hc1 : ContDiff ℝ n (fun t : κ → ℝ => (t i : ℝ)) := by fun_prop
      exact (hc0.smul h0).add (hc1.smul h1)

private theorem multiaffineInterpolation_contDiff {r : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (a : (Fin r → Bool) → V) :
    ContDiff ℝ n (RBM.Gauss.multiaffineInterpolation a) := by
  unfold RBM.Gauss.multiaffineInterpolation
  exact multiaffineInterpOn_contDiff n _ _ _

private theorem continuousLinearMap_cubeMixedPartial
    {r : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] W) (coords : List (Fin r)) (f : (Fin r → ℝ) → V)
    (t : Fin r → ℝ) (hf : ContDiff ℝ coords.length f) :
    L (RBM.Gauss.cubeMixedPartial coords f t) =
      RBM.Gauss.cubeMixedPartial coords (L ∘ f) t := by
  have hLf : ContDiff ℝ coords.length (L ∘ f) := L.contDiff.comp hf
  calc
    L (RBM.Gauss.cubeMixedPartial coords f t) =
        L ((iteratedFDeriv ℝ coords.length f t) (reverseAxisDirections coords)) := by
          rw [iteratedFDeriv_reverseAxes_eq_cubeMixedPartial coords t hf]
    _ = (iteratedFDeriv ℝ coords.length (L ∘ f) t)
          (reverseAxisDirections coords) := by
        have hcomp := L.iteratedFDeriv_comp_left (f := f) (x := t) hf.contDiffAt
          (i := coords.length) le_rfl
        have hEval := congrArg (fun D => D (reverseAxisDirections coords)) hcomp
        simpa only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
          Function.comp_apply]
          using hEval.symm
    _ = RBM.Gauss.cubeMixedPartial coords (L ∘ f) t :=
          iteratedFDeriv_reverseAxes_eq_cubeMixedPartial coords t hLf

private theorem qNorm_multiaffineFace_le (q r : ℕ)
    [Fact (1 ≤ (q : ENNReal))] (hq : 2 ≤ q)
    (coords : List (Fin r)) (hcoords : coords.Nodup)
    (a : (Fin r → Bool) → (ι → ℝ)) (t : Fin r → ℝ) (B : ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (hface : ∀ b, (∀ i ∈ coords, b i = false) →
      qNorm q (RBM.Gauss.shiftedDifferenceList coords a b) ≤ B) :
    qNorm q
      (RBM.Gauss.cubeMixedPartial coords
        (fun x => RBM.Gauss.multiaffineInterpolation a x) t) ≤ B := by
  classical
  let J : Finset (Fin r) := coords.toFinset
  let ks : List (Fin r) := (Finset.univ \ J).toList
  have hndAppend : (coords ++ ks).Nodup := by
    apply List.Nodup.append hcoords (Finset.nodup_toList _)
    intro x hx hc
    have hxJ : x ∈ J := by simpa [J, List.mem_toFinset] using hx
    have hc' : x ∈ Finset.univ \ J := by
      simpa only [ks, Finset.mem_toList] using hc
    exact (Finset.mem_sdiff.mp hc').2 hxJ
  have hperm : (coords ++ ks).Perm (Finset.univ : Finset (Fin r)).toList := by
    apply (List.perm_ext_iff_of_nodup hndAppend Finset.univ.nodup_toList).2
    intro i
    by_cases hi : i ∈ coords
    · simp [hi, J, ks, List.mem_toFinset, Finset.mem_sdiff, List.mem_append]
    · simp [hi, J, ks, List.mem_toFinset, Finset.mem_sdiff, List.mem_append]
  let L : (ι → ℝ) →L[ℝ] PiLp (q : ENNReal) (fun _ : ι => ℝ) :=
    (PiLp.continuousLinearEquiv (q : ENNReal) ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
  let aQ : (Fin r → Bool) → PiLp (q : ENNReal) (fun _ : ι => ℝ) :=
    fun v => L (a v)
  have hstandard : (fun x => RBM.Gauss.multiaffineInterpolation aQ x) =
      (fun x => RBM.Gauss.multiaffineInterpOn (coords ++ ks) (fun _ => false) aQ x) := by
    funext x
    dsimp [RBM.Gauss.multiaffineInterpolation]
    exact (multiaffineInterpOn_perm hperm hndAppend (fun _ => false) aQ x).symm
  have hface' : ∀ b, (∀ i ∈ J, b i = false) →
      ‖RBM.Gauss.shiftedDifferenceList coords aQ b‖ ≤ B := by
    intro b hb
    have hzero : ∀ i ∈ coords, b i = false := by
      intro i hi
      exact hb i (by simpa [J, List.mem_toFinset] using hi)
    have hmap := continuousLinearMap_shiftedDifferenceList L coords a b
    rw [← hmap]
    have hnorm : ‖L (RBM.Gauss.shiftedDifferenceList coords a b)‖ =
        qNorm q (RBM.Gauss.shiftedDifferenceList coords a b) := by
      simpa [L, PiLp.coe_symm_continuousLinearEquiv] using
        qNorm_eq_piLp_norm q hq (RBM.Gauss.shiftedDifferenceList coords a b)
    rw [hnorm]
    exact hface b hzero
  have hbound : ‖RBM.Gauss.multiaffineInterpOn ks (fun _ => false)
      (RBM.Gauss.shiftedDifferenceList coords aQ) t‖ ≤ B := by
    apply RBM.Gauss.multiaffineInterpOn_norm_le_on_complement ks J
    · intro i hi
      have hi' : i ∈ Finset.univ \ J := by simpa [ks] using hi
      exact (Finset.mem_sdiff.mp hi').2
    · intro i hi
      exact ht i
    · intro i hi
      rfl
    · exact hface'
  have hpartial := RBM.Gauss.cubeMixedPartial_multiaffineInterpOn_prefix
    coords ks hndAppend (fun _ => false) aQ t
  have hcontDiff : ContDiff ℝ coords.length (RBM.Gauss.multiaffineInterpolation a) :=
    multiaffineInterpolation_contDiff coords.length a
  have hmapStandard :
      (fun x => L (RBM.Gauss.multiaffineInterpolation a x)) =
        (fun x => RBM.Gauss.multiaffineInterpolation aQ x) := by
    funext x
    unfold RBM.Gauss.multiaffineInterpolation
    exact continuousLinearMap_multiaffineInterpOn L Finset.univ.toList
      (fun _ => false) a x
  have hresult := continuousLinearMap_cubeMixedPartial L coords
    (RBM.Gauss.multiaffineInterpolation a) t hcontDiff
  have hmapStandard' : (L ∘ RBM.Gauss.multiaffineInterpolation a) =
      RBM.Gauss.multiaffineInterpolation aQ := by
    funext x
    exact congrFun hmapStandard x
  have hresult' := hresult.trans (congrArg
    (fun f => RBM.Gauss.cubeMixedPartial coords f t) hmapStandard')
  calc
    qNorm q (RBM.Gauss.cubeMixedPartial coords
        (fun x => RBM.Gauss.multiaffineInterpolation a x) t) =
        ‖L (RBM.Gauss.cubeMixedPartial coords
          (fun x => RBM.Gauss.multiaffineInterpolation a x) t)‖ := by
            symm
            simpa [L, PiLp.coe_symm_continuousLinearEquiv] using
              qNorm_eq_piLp_norm q hq
                (RBM.Gauss.cubeMixedPartial coords
                  (fun x => RBM.Gauss.multiaffineInterpolation a x) t)
    _ = ‖RBM.Gauss.cubeMixedPartial coords
          (fun x => RBM.Gauss.multiaffineInterpolation aQ x) t‖ := by
            rw [hresult']
    _ = ‖RBM.Gauss.multiaffineInterpOn ks (fun _ => false)
          (RBM.Gauss.shiftedDifferenceList coords aQ) t‖ := by
            rw [hstandard, hpartial]
    _ ≤ B := hbound

private theorem multiaffineInterpOn_vertex {κ : Type*} [Fintype κ] [DecidableEq κ]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (coords : List κ) (hnd : coords.Nodup) (b : κ → Bool)
    (a : (κ → Bool) → V) (v : κ → Bool) (t : κ → ℝ)
    (ht : ∀ i ∈ coords, t i = if v i then 1 else 0)
    (hb : ∀ i, i ∉ coords → b i = v i) :
    RBM.Gauss.multiaffineInterpOn coords b a t = a v := by
  induction coords generalizing b with
  | nil =>
      have hEq : b = v := by
        funext i
        exact hb i (by simp)
      simpa [hEq] using (RBM.Gauss.multiaffineInterpOn_nil b a t)
  | cons i is ih =>
      have hnd' : is.Nodup := (List.nodup_cons.mp hnd).2
      have hiNot : i ∉ is := (List.nodup_cons.mp hnd).1
      have hbase (j : κ) (hj : j ∉ is) :
          Function.update b i (v i) j = v j := by
        by_cases hji : j = i
        · subst j
          simp
        · have hj' : j ∉ i :: is := by simp [hji, hj]
          simp [Function.update_of_ne hji, hb j hj']
      have htail := ih hnd' (Function.update b i (v i))
        (fun j hj => ht j (by simp [hj])) hbase
      have hiValue := ht i (by simp)
      by_cases hvi : v i
      · have htone : t i = 1 := by simpa [hvi] using hiValue
        rw [RBM.Gauss.multiaffineInterpOn, htone]
        simp only [sub_self, zero_smul, one_smul, zero_add]
        simpa [hvi] using htail
      · have htzero : t i = 0 := by simpa [hvi] using hiValue
        rw [RBM.Gauss.multiaffineInterpOn, htzero]
        simp only [one_mul, zero_mul, zero_smul, one_smul, add_zero]
        simpa [hvi] using htail

private def reverseOfFn {r : ℕ} : (n : ℕ) → (Fin n → Fin r) → List (Fin r)
  | 0, _ => []
  | n + 1, e => e (Fin.last n) :: reverseOfFn n (fun j => e j.castSucc)

private theorem reverseOfFn_length {r n : ℕ} (e : Fin n → Fin r) :
    (reverseOfFn n e).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [reverseOfFn, ih]

private theorem reverseOfFn_eq_reverse_listOfFn {r n : ℕ} (e : Fin n → Fin r) :
    reverseOfFn n e = (List.ofFn e).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let et : Fin n → Fin r := fun j => e j.castSucc
      rw [reverseOfFn, List.ofFn_succ']
      simp [et, ih]

private theorem reverseOfFn_nodup {r n : ℕ} (e : Fin n → Fin r)
    (he : Function.Injective e) : (reverseOfFn n e).Nodup := by
  rw [reverseOfFn_eq_reverse_listOfFn]
  exact List.nodup_reverse.mpr (List.nodup_ofFn_ofInjective he)

private def orderedBlockCoordinates {r : ℕ} (c : OrderedFinpartition r)
    (m : Fin c.length) : List (Fin r) :=
  reverseOfFn (c.partSize m) (c.emb m)

private theorem orderedBlockCoordinates_length {r : ℕ} (c : OrderedFinpartition r)
    (m : Fin c.length) : (orderedBlockCoordinates c m).length = c.partSize m := by
  exact reverseOfFn_length (c.emb m)

private theorem orderedBlockCoordinates_nodup {r : ℕ} (c : OrderedFinpartition r)
    (m : Fin c.length) : (orderedBlockCoordinates c m).Nodup := by
  exact reverseOfFn_nodup (c.emb m) (c.emb_strictMono m).injective

private theorem iteratedFDeriv_finAxes_eq_cubeMixedPartial {r n : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → Fin r) {f : (Fin r → ℝ) → V} (t : Fin r → ℝ)
    (hf : ContDiff ℝ n f) :
    (iteratedFDeriv ℝ n f t) (fun j => Pi.single (e j) (1 : ℝ)) =
      RBM.Gauss.cubeMixedPartial (reverseOfFn n e) f t := by
  induction n generalizing f with
  | zero => simp [reverseOfFn, RBM.Gauss.cubeMixedPartial]
  | succ n ih =>
      let i : Fin r := e (Fin.last n)
      let et : Fin n → Fin r := fun j => e j.castSucc
      have hfn : ContDiff ℝ (n + 1) f := by simpa using hf
      have hderiv : ContDiff ℝ n
          (fun p : (Fin r → ℝ) × (Fin r → ℝ) => fderiv ℝ f p.1 p.2) := by
        exact hfn.contDiff_fderiv_apply (by simp)
      let v : Fin r → ℝ := Pi.single i 1
      have hpair : ContDiff ℝ n (fun y : Fin r → ℝ => (y, v)) := by fun_prop
      have hrestricted : ContDiff ℝ n (fun y => fderiv ℝ f y v) := hderiv.comp hpair
      have hfderiv : ContDiff ℝ n (fun y => fderiv ℝ f y) := hfn.fderiv_right (by simp)
      let ev : ((Fin r → ℝ) →L[ℝ] V) →L[ℝ] V := ContinuousLinearMap.apply ℝ V v
      have heval : (fun y => fderiv ℝ f y v) = ev ∘ (fun y => fderiv ℝ f y) := rfl
      have hfdAt : ContDiffAt ℝ n (fun y => fderiv ℝ f y) t := hfderiv.contDiffAt
      have hcomp := ev.iteratedFDeriv_comp_left
        (f := fun y => fderiv ℝ f y) (x := t) hfdAt (i := n) le_rfl
      let dirs : Fin (n + 1) → (Fin r → ℝ) := fun j => Pi.single (e j) 1
      have hmain := iteratedFDeriv_succ_apply_right
        (𝕜 := ℝ) (E := Fin r → ℝ) (f := f) (x := t) (n := n) dirs
      have hinit : Fin.init dirs = fun j => Pi.single (et j) 1 := by
        funext j
        rfl
      have hlast : dirs (Fin.last n) = v := by simp [dirs, v, i]
      have hdiff : Differentiable ℝ f := hfn.differentiable (by simp)
      have hcubeEq : (fun y => fderiv ℝ f y v) =
          (fun y => RBM.Gauss.cubePartial i f y) := by
        funext y
        exact (cubePartial_eq_fderiv_axis y hdiff.differentiableAt i).symm
      change (iteratedFDeriv ℝ (n + 1) f t) dirs =
        RBM.Gauss.cubeMixedPartial (reverseOfFn (n + 1) e) f t
      rw [hmain, hinit, hlast]
      have hscalar :
          iteratedFDeriv ℝ n (fun y => fderiv ℝ f y v) t =
            ev.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) t) := by
        rw [heval]
        exact hcomp
      have hrestricted' : ContDiff ℝ n (fun y => RBM.Gauss.cubePartial i f y) := by
        rw [← hcubeEq]
        exact hrestricted
      have htail := ih (e := et) (f := fun y => RBM.Gauss.cubePartial i f y) hrestricted'
      have hscalar' := hscalar
      rw [hcubeEq] at hscalar'
      have hscalarEval := congrArg (fun L => L (fun j => Pi.single (et j) 1)) hscalar'
      have hscalarEq :
          iteratedFDeriv ℝ n (fun y => RBM.Gauss.cubePartial i f y) t
              (fun j => Pi.single (et j) 1) =
            (iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) t
              (fun j => Pi.single (et j) 1)) v := by
        simpa [ev] using hscalarEval
      rw [reverseOfFn]
      exact hscalarEq.symm.trans htail

private theorem abs_iteratedUnitIntegral_le {r : ℕ}
    (f : (Fin r → ℝ) → ℝ) (C : ℝ)
    (hpoint : ∀ t ∈ RBM.Gauss.unitCoordinateCube r, |f t| ≤ C) :
    |RBM.Gauss.iteratedUnitIntegral r f| ≤ C := by
  induction r with
  | zero =>
      change |f (fun i => Fin.elim0 i)| ≤ C
      apply hpoint
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      change |RBM.Gauss.iteratedUnitIntegral n
        (fun t => ∫ x in (0 : ℝ)..1, f (Fin.cons x t))| ≤ C
      apply ih
      intro t ht
      have hinner : ‖∫ x in (0 : ℝ)..1, f (Fin.cons x t)‖ ≤ C := by
        have htmp := intervalIntegral.norm_integral_le_of_norm_le_const
          (f := fun x => f (Fin.cons x t)) (C := C) (a := (0 : ℝ)) (b := 1)
          (by
            intro x hx
            have hx0 : 0 < x := by simpa using hx.1
            have hx1 : x ≤ 1 := by simpa using hx.2
            have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hx0, hx1⟩
            have ht' : Fin.cons x t ∈ RBM.Gauss.unitCoordinateCube (n + 1) :=
              RBM.Gauss.unitCoordinateCube_cons x t hxI ht
            simpa [Real.norm_eq_abs] using hpoint (Fin.cons x t) ht')
        simpa using htmp
      simpa [Real.norm_eq_abs] using hinner

private theorem multiaffineInterpolation_vertex {r : ℕ}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : (Fin r → Bool) → V) (v : Fin r → Bool) :
    RBM.Gauss.multiaffineInterpolation a (fun i => if v i then 1 else 0) = a v := by
  unfold RBM.Gauss.multiaffineInterpolation
  apply multiaffineInterpOn_vertex (Finset.univ.toList) Finset.univ.nodup_toList
    (fun _ => false) a v (fun i => if v i then 1 else 0)
  · intro i hi
    simp
  · intro i hi
    simp at hi

private theorem orderedFinpartition_sum_partSize {r : ℕ} (c : OrderedFinpartition r) :
    ∑ m : Fin c.length, c.partSize m = r := by
  have hcard := Fintype.card_congr c.equivSigma
  simpa using hcard

private theorem orderedFinpartition_gamma_scale {r : ℕ} (c : OrderedFinpartition r)
    (s : ℤ) (rho Gamma : ℝ) (hrho : 0 < rho) (hGamma : 0 < Gamma)
    (B : ℕ → ℝ) :
    (rho * Gamma) ^ ((s : ℝ) - (c.length : ℝ)) *
        ∏ m : Fin c.length,
          (B (c.partSize m) * Gamma ^ (1 + (c.partSize m : ℝ) / 2)) =
      Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
        rho ^ ((s : ℝ) - (c.length : ℝ)) *
          ∏ m : Fin c.length, B (c.partSize m) := by
  have hsumexp :
    ∑ m : Fin c.length, (1 + (c.partSize m : ℝ) / 2) =
        (c.length : ℝ) + (r : ℝ) / 2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, one_mul]
    rw [← Nat.cast_sum, orderedFinpartition_sum_partSize]
    norm_num
  have hprod :
      ∏ m : Fin c.length,
        (B (c.partSize m) * Gamma ^ (1 + (c.partSize m : ℝ) / 2)) =
      (∏ m : Fin c.length, B (c.partSize m)) *
        Gamma ^ ((c.length : ℝ) + (r : ℝ) / 2) := by
    rw [Finset.prod_mul_distrib]
    rw [← Real.rpow_sum_of_pos hGamma (fun m : Fin c.length =>
      (1 + (c.partSize m : ℝ) / 2)) Finset.univ]
    rw [hsumexp]
  calc
    (rho * Gamma) ^ ((s : ℝ) - (c.length : ℝ)) *
        ∏ m : Fin c.length,
          (B (c.partSize m) * Gamma ^ (1 + (c.partSize m : ℝ) / 2)) =
      (rho ^ ((s : ℝ) - (c.length : ℝ)) *
        Gamma ^ ((s : ℝ) - (c.length : ℝ))) *
        ((∏ m : Fin c.length, B (c.partSize m)) *
          Gamma ^ ((c.length : ℝ) + (r : ℝ) / 2)) := by
            rw [Real.mul_rpow hrho.le hGamma.le, hprod]
    _ = Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
          rho ^ ((s : ℝ) - (c.length : ℝ)) *
            ∏ m : Fin c.length, B (c.partSize m) := by
          let e : ℝ := (s : ℝ) - (c.length : ℝ)
          let k : ℝ := (c.length : ℝ) + (r : ℝ) / 2
          have hpow : Gamma ^ e * Gamma ^ k = Gamma ^ ((s : ℝ) + (r : ℝ) / 2) := by
            change Gamma ^ ((s : ℝ) - (c.length : ℝ)) *
                Gamma ^ ((c.length : ℝ) + (r : ℝ) / 2) =
              Gamma ^ ((s : ℝ) + (r : ℝ) / 2)
            rw [← Real.rpow_add hGamma]
            ring_nf
          calc
            rho ^ ((s : ℝ) - (c.length : ℝ)) *
                  Gamma ^ ((s : ℝ) - (c.length : ℝ)) *
                  ((∏ m : Fin c.length, B (c.partSize m)) *
                    Gamma ^ ((c.length : ℝ) + (r : ℝ) / 2)) =
                rho ^ ((s : ℝ) - (c.length : ℝ)) *
                  (Gamma ^ ((s : ℝ) - (c.length : ℝ)) *
                    Gamma ^ ((c.length : ℝ) + (r : ℝ) / 2)) *
                  ∏ m : Fin c.length, B (c.partSize m) := by ring
            _ = rho ^ ((s : ℝ) - (c.length : ℝ)) *
                  Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
                  ∏ m : Fin c.length, B (c.partSize m) := by rw [hpow]
            _ = Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
                  rho ^ ((s : ℝ) - (c.length : ℝ)) *
                  ∏ m : Fin c.length, B (c.partSize m) := by ring

/-- The alternating-vertex bound for either smooth norm or reciprocal norm power.  Each block
uses the norm bound for its shifted face, with the exact block-size Gamma exponent. -/
theorem alternatingSmoothNormPower_cube_bound (_hι : Nonempty ι)
    (M r q : ℕ) (s : ℤ)
    (hqeven : Even q) (hqM : max 2 (4 * M) ≤ q)
    (hr : 1 ≤ r) (hrM : r ≤ M) (hs : s = 1 ∨ s = -1)
    (c Gamma : ℝ) (hc : 0 < c) (hGamma : 0 < Gamma)
    (a : (Fin r → Bool) → (ι → ℝ))
    (ha : ∀ v i, 0 ≤ a v i)
    (hlower : ∀ v, c * Gamma ≤ qNorm q (a v))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hface : ∀ coords : List (Fin r), coords.Nodup → coords ≠ [] →
      ∀ b, (∀ i ∈ coords, b i = false) →
        qNorm q (RBM.Gauss.shiftedDifferenceList coords a b) ≤
          B coords.length * Gamma ^ (1 + (coords.length : ℝ) / 2)) :
    |RBM.Gauss.alternatingVertexSum r
        (fun v => smoothNormPower q s (a v))| ≤
      Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
        ∑ d : OrderedFinpartition r,
          outerDerivativeConstant d.length * (q : ℝ) ^ (d.length - 1) *
            ((2 : ℝ) ^ (-(M : ℤ) : ℝ) * min c 1) ^
                ((s : ℝ) - (d.length : ℝ)) *
              ∏ m : Fin d.length, B (d.partSize m) := by
  classical
  let rho : ℝ := (2 : ℝ) ^ (-(M : ℤ) : ℝ) * min c 1
  let A : (Fin r → ℝ) → (ι → ℝ) := RBM.Gauss.multiaffineInterpolation a
  let G : (ι → ℝ) → ℝ := smoothNormPower q s
  let f : (Fin r → ℝ) → ℝ := G ∘ A
  have hq2 : 2 ≤ q := le_trans (le_max_left 2 (4 * M)) hqM
  have hqpos : 0 < q := by omega
  have hqFact : Fact (1 ≤ (q : ENNReal)) := ⟨by
    exact_mod_cast (show 1 ≤ q by omega)⟩
  haveI := hqFact
  have hrho : 0 < rho := by
    dsimp [rho]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (lt_min hc zero_lt_one)
  have hAcont : ContDiff ℝ r A := by
    exact multiaffineInterpolation_contDiff r a
  have hGcont : ContDiffOn ℝ r G {x | x ≠ 0} := by
    intro x hx
    exact (smoothNormPower_contDiffAt q s r x hqeven hq2 hx).contDiffWithinAt
  let U : Set (Fin r → ℝ) := A ⁻¹' {x | x ≠ 0}
  have hUopen : IsOpen U := by
    exact isOpen_ne.preimage hAcont.continuous
  have hUcube : RBM.Gauss.unitCoordinateCube r ⊆ U := by
    intro t ht
    change A t ≠ 0
    have hlow := qNorm_lower_on_unitCube M r q c Gamma hqpos hrM a
      hGamma hc ha hlower t ht
    have hpositive : 0 < qNorm q (A t) := lt_of_lt_of_le
      (mul_pos hrho hGamma) (by simpa [rho, A] using hlow)
    intro hz
    have hzero : qNorm q (A t) = 0 := by
      rw [← qNorm_eq_piLp_norm q hq2, hz]
      simp
    linarith
  have hmaps : Set.MapsTo A U {x | x ≠ 0} := by
    intro t ht
    exact ht
  have hfcont : ContDiffOn ℝ r f U := by
    exact hGcont.comp hAcont.contDiffOn hmaps
  have hFTC := RBM.Gauss.alternatingVertexSum_eq_iteratedUnitIntegral_of_contDiffOn
    f U hUopen hUcube hfcont
  have hvertices :
      (fun v => f (fun i => if v i then 1 else 0)) =
        (fun v => smoothNormPower q s (a v)) := by
    funext v
    change smoothNormPower q s
        (RBM.Gauss.multiaffineInterpolation a (fun i => if v i then 1 else 0)) = _
    rw [multiaffineInterpolation_vertex a v]
  have hFTC' :
      RBM.Gauss.alternatingVertexSum r
          (fun v => smoothNormPower q s (a v)) =
        RBM.Gauss.iteratedUnitIntegral r (RBM.Gauss.cubeMixedDerivative f) := by
    simpa only [← hvertices] using hFTC
  let R : ℝ := Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
      ∑ d : OrderedFinpartition r,
        outerDerivativeConstant d.length * (q : ℝ) ^ (d.length - 1) *
          rho ^ ((s : ℝ) - (d.length : ℝ)) *
            ∏ m : Fin d.length, B (d.partSize m)
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    apply mul_nonneg (Real.rpow_nonneg hGamma.le _)
    apply Finset.sum_nonneg
    intro d hd
    have hC : 0 ≤ outerDerivativeConstant d.length := by
      unfold outerDerivativeConstant
      apply Finset.sum_nonneg
      intro e he
      exact Nat.cast_nonneg _
    have hqpow : 0 ≤ (q : ℝ) ^ (d.length - 1) := pow_nonneg (by positivity) _
    have hrpow : 0 ≤ rho ^ ((s : ℝ) - (d.length : ℝ)) :=
      Real.rpow_nonneg hrho.le _
    have hBprod : 0 ≤ ∏ m : Fin d.length, B (d.partSize m) :=
      Finset.prod_nonneg fun m hm => hB _
    positivity
  have hpoint : ∀ t ∈ RBM.Gauss.unitCoordinateCube r,
      |RBM.Gauss.cubeMixedDerivative f t| ≤ R := by
    intro t ht
    have ht01 : ∀ i, 0 ≤ t i ∧ t i ≤ 1 := by
      intro i
      have hi := ht i
      simpa only [Set.mem_Icc] using hi
    have hlow := qNorm_lower_on_unitCube M r q c Gamma hqpos hrM a
      hGamma hc ha hlower t ht
    have hlow' : rho * Gamma ≤ qNorm q (A t) := by
      simpa [rho, A] using hlow
    have hAtne : A t ≠ 0 := by
      intro hz
      have hzero : qNorm q (A t) = 0 := by
        rw [← qNorm_eq_piLp_norm q hq2, hz]
        simp
      have hpos : 0 < qNorm q (A t) := lt_of_lt_of_le
        (mul_pos hrho hGamma) hlow'
      linarith
    have hGAt : ContDiffAt ℝ r G (A t) :=
      smoothNormPower_contDiffAt q s r (A t) hqeven hq2 hAtne
    let dirs : Fin r → (Fin r → ℝ) := fun j => Pi.single j 1
    have hcomp := iteratedFDeriv_comp_apply_sum r A G t dirs
      hAcont.contDiffAt hGAt
    have hsumabs :
        |∑ d : OrderedFinpartition r,
          (iteratedFDeriv ℝ d.length G (A t))
            (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
              (fun j => dirs (d.emb m j)))| ≤
          ∑ d : OrderedFinpartition r,
            |(iteratedFDeriv ℝ d.length G (A t))
              (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
                (fun j => dirs (d.emb m j)))| :=
      Finset.abs_sum_le_sum_abs _ _
    have hterm : ∀ d : OrderedFinpartition r,
        |(iteratedFDeriv ℝ d.length G (A t))
          (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
            (fun j => dirs (d.emb m j)))| ≤
          Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
            (outerDerivativeConstant d.length * (q : ℝ) ^ (d.length - 1) *
              rho ^ ((s : ℝ) - (d.length : ℝ)) *
                ∏ m : Fin d.length, B (d.partSize m)) := by
      intro d
      let k := d.length
      have hkpos : 1 ≤ k := by
        dsimp [k]
        exact d.length_pos (by omega)
      have hkle : k ≤ M := by
        dsimp [k]
        exact le_trans d.length_le hrM
      let v : Fin k → (ι → ℝ) := fun m =>
        (iteratedFDeriv ℝ (d.partSize m) A t)
          (fun j => dirs (d.emb m j))
      have houter := abs_iteratedFDeriv_smoothNormPower_le M q k s hqeven hqM
        hkpos hkle hs (A t) hAtne v
      have hblock : ∀ m : Fin k,
          qNorm q (v m) ≤ B (d.partSize m) * Gamma ^
            (1 + (d.partSize m : ℝ) / 2) := by
        intro m
        let coords := orderedBlockCoordinates d m
        have hcoords : coords.Nodup := orderedBlockCoordinates_nodup d m
        have hcoordsNe : coords ≠ [] := by
          intro hz
          have hlen : coords.length = d.partSize m := by
            simpa [coords] using orderedBlockCoordinates_length d m
          rw [hz] at hlen
          have hpos : 0 < d.partSize m := d.partSize_pos m
          simp at hlen
          omega
        have hfaces := hface coords hcoords hcoordsNe
        have hpartialBound := qNorm_multiaffineFace_le q r hq2 coords hcoords
          a t (B (d.partSize m) * Gamma ^ (1 + (d.partSize m : ℝ) / 2)) ht01
          (by
            intro b hb
            have h := hfaces b hb
            have hlen : coords.length = d.partSize m := by
              simpa [coords] using orderedBlockCoordinates_length d m
            rw [hlen] at h
            exact h)
        have hAcontBlock : ContDiff ℝ (d.partSize m) A :=
          hAcont.of_le (by exact_mod_cast d.partSize_le m)
        have heq :
            (iteratedFDeriv ℝ (d.partSize m) A t)
                (fun j => dirs (d.emb m j)) =
              RBM.Gauss.cubeMixedPartial coords A t := by
          simpa [coords, orderedBlockCoordinates, dirs] using
            (iteratedFDeriv_finAxes_eq_cubeMixedPartial
              (d.emb m) t hAcontBlock)
        change qNorm q
            ((iteratedFDeriv ℝ (d.partSize m) A t)
              (fun j => dirs (d.emb m j))) ≤ _
        rw [heq]
        simpa [A] using hpartialBound
      have hprod :
          ∏ m : Fin k, qNorm q (v m) ≤
            ∏ m : Fin k, (B (d.partSize m) * Gamma ^
              (1 + (d.partSize m : ℝ) / 2)) := by
        apply Finset.prod_le_prod₀
        · intro m hm
          exact qNorm_nonneg q (v m)
        · intro m hm
          exact hblock m
      have hprodNonneg : 0 ≤ ∏ m : Fin k, qNorm q (v m) :=
        Finset.prod_nonneg fun m hm => qNorm_nonneg q (v m)
      have hprodTargetNonneg :
          0 ≤ ∏ m : Fin k, (B (d.partSize m) * Gamma ^
              (1 + (d.partSize m : ℝ) / 2)) := by
        apply Finset.prod_nonneg
        intro m hm
        exact mul_nonneg (hB _) (Real.rpow_nonneg hGamma.le _)
      have he : (s : ℝ) - (k : ℝ) ≤ 0 := by
        rcases hs with hs | hs
        · have hs' : (s : ℝ) = 1 := by exact_mod_cast hs
          rw [hs']
          have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkpos
          exact sub_nonpos.mpr hk'
        · have hs' : (s : ℝ) = -1 := by exact_mod_cast hs
          rw [hs']
          have hk' : (0 : ℝ) ≤ (k : ℝ) := by positivity
          have hk'' : (-1 : ℝ) ≤ (k : ℝ) := by linarith
          exact sub_nonpos.mpr hk''
      have hnormpow :
          qNorm q (A t) ^ ((s : ℝ) - (k : ℝ)) ≤
            (rho * Gamma) ^ ((s : ℝ) - (k : ℝ)) := by
        apply Real.rpow_le_rpow_of_nonpos (mul_pos hrho hGamma)
        · exact hlow'
        · exact he
      have hcore :
          qNorm q (A t) ^ ((s : ℝ) - (k : ℝ)) *
              ∏ m : Fin k, qNorm q (v m) ≤
            (rho * Gamma) ^ ((s : ℝ) - (k : ℝ)) *
              ∏ m : Fin k, (B (d.partSize m) * Gamma ^
                (1 + (d.partSize m : ℝ) / 2)) :=
        mul_le_mul hnormpow hprod hprodNonneg
          (Real.rpow_nonneg (mul_pos hrho hGamma).le _)
      have hcoef : 0 ≤ outerDerivativeConstant k * (q : ℝ) ^ (k - 1) := by
        apply mul_nonneg
        · unfold outerDerivativeConstant
          apply Finset.sum_nonneg
          intro e he'
          exact Nat.cast_nonneg _
        · exact pow_nonneg (by positivity) _
      have hcoefBound :
          outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
              qNorm q (A t) ^ ((s : ℝ) - (k : ℝ)) *
                ∏ m : Fin k, qNorm q (v m) ≤
            outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
              ((rho * Gamma) ^ ((s : ℝ) - (k : ℝ)) *
                ∏ m : Fin k, (B (d.partSize m) * Gamma ^
                  (1 + (d.partSize m : ℝ) / 2))) := by
        calc
          _ = (outerDerivativeConstant k * (q : ℝ) ^ (k - 1)) *
                (qNorm q (A t) ^ ((s : ℝ) - (k : ℝ)) *
                  ∏ m : Fin k, qNorm q (v m)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hcore hcoef
      have hscaled := orderedFinpartition_gamma_scale d s rho Gamma hrho hGamma B
      have hterm' :
          outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
              ((rho * Gamma) ^ ((s : ℝ) - (k : ℝ)) *
                ∏ m : Fin k, (B (d.partSize m) * Gamma ^
                  (1 + (d.partSize m : ℝ) / 2))) =
            Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
              (outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
                rho ^ ((s : ℝ) - (k : ℝ)) *
                  ∏ m : Fin k, B (d.partSize m)) := by
        calc
          outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
                ((rho * Gamma) ^ ((s : ℝ) - (k : ℝ)) *
                  ∏ m : Fin k, (B (d.partSize m) * Gamma ^
                    (1 + (d.partSize m : ℝ) / 2))) =
              outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
                (Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
                  rho ^ ((s : ℝ) - (k : ℝ)) *
                    ∏ m : Fin k, B (d.partSize m)) := by
                  rw [hscaled]
          _ = Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
                (outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
                  rho ^ ((s : ℝ) - (k : ℝ)) *
                    ∏ m : Fin k, B (d.partSize m)) := by ring
      calc
        |(iteratedFDeriv ℝ d.length G (A t))
            (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
              (fun j => dirs (d.emb m j)))| ≤
            outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
              qNorm q (A t) ^ ((s : ℝ) - (k : ℝ)) *
                ∏ m : Fin k, qNorm q (v m) := by
                  simpa [k, v] using houter
        _ ≤ outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
              ((rho * Gamma) ^ ((s : ℝ) - (k : ℝ)) *
                ∏ m : Fin k, (B (d.partSize m) * Gamma ^
                  (1 + (d.partSize m : ℝ) / 2))) := hcoefBound
        _ = Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
              (outerDerivativeConstant k * (q : ℝ) ^ (k - 1) *
                rho ^ ((s : ℝ) - (k : ℝ)) *
                  ∏ m : Fin k, B (d.partSize m)) := hterm'
    have hsumBound :
        ∑ d : OrderedFinpartition r,
          |(iteratedFDeriv ℝ d.length G (A t))
            (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
              (fun j => dirs (d.emb m j)))| ≤ R := by
      dsimp [R]
      calc
        _ ≤ ∑ d : OrderedFinpartition r,
              Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
                (outerDerivativeConstant d.length * (q : ℝ) ^ (d.length - 1) *
                  rho ^ ((s : ℝ) - (d.length : ℝ)) *
                    ∏ m : Fin d.length, B (d.partSize m)) := by
                      apply Finset.sum_le_sum
                      intro d hd
                      exact hterm d
        _ = Gamma ^ ((s : ℝ) + (r : ℝ) / 2) *
              ∑ d : OrderedFinpartition r,
                outerDerivativeConstant d.length * (q : ℝ) ^ (d.length - 1) *
                  rho ^ ((s : ℝ) - (d.length : ℝ)) *
                    ∏ m : Fin d.length, B (d.partSize m) := by
              rw [Finset.mul_sum]
    calc
      |RBM.Gauss.cubeMixedDerivative f t| =
          |(iteratedFDeriv ℝ r (G ∘ A) t) dirs| := by
            simp [RBM.Gauss.cubeMixedDerivative, dirs, f]
      _ = |∑ d : OrderedFinpartition r,
          (iteratedFDeriv ℝ d.length G (A t))
            (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
              (fun j => dirs (d.emb m j)))| := by rw [hcomp]
      _ ≤ ∑ d : OrderedFinpartition r,
          |(iteratedFDeriv ℝ d.length G (A t))
            (fun m => (iteratedFDeriv ℝ (d.partSize m) A t)
              (fun j => dirs (d.emb m j)))| := hsumabs
      _ ≤ R := hsumBound
  have hintegral := abs_iteratedUnitIntegral_le
    (RBM.Gauss.cubeMixedDerivative f) R hpoint
  rw [hFTC']
  simpa [R, rho] using hintegral

/-- A simultaneous witness with an individual zero coordinate and positive q-norm. -/
theorem constant_positive_zero_coordinate_witness :
    ∃ a : (Fin 1 → Bool) → (Fin 2 → ℝ),
      (∀ v i, 0 ≤ a v i) ∧
      (∀ v, (1 : ℝ) ≤ qNorm 4 (a v)) ∧
      (∀ v, ∃ i : Fin 2, a v i = 0) ∧
      (∀ coords : List (Fin 1), coords.Nodup → coords ≠ [] →
        ∀ b, (∀ i ∈ coords, b i = false) →
          qNorm 4 (RBM.Gauss.shiftedDifferenceList coords a b) ≤
            (0 : ℝ) * (1 : ℝ) ^ (1 + (coords.length : ℝ) / 2)) := by
  classical
  let a : (Fin 1 → Bool) → (Fin 2 → ℝ) := fun _ i => if i = 0 then 0 else 1
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · intro v i
    by_cases hi : i = 0 <;> simp [a, hi]
  · intro v
    unfold qNorm
    norm_num [a, Fin.sum_univ_succ]
  · intro v
    exact ⟨0, by simp [a]⟩
  · intro coords hcoords hne b hb
    have hzero : RBM.Gauss.shiftedDifferenceList coords a b = 0 := by
      have hconstant (js : List (Fin 1)) (bb : Fin 1 → Bool) :
          RBM.Gauss.shiftedDifferenceList js (fun _ => (0 : Fin 2 → ℝ)) bb = 0 := by
        induction js with
        | nil => rfl
        | cons j js ih =>
            change RBM.Gauss.shiftedDifferenceList js
              (RBM.Gauss.shiftedDifference j (fun _ => (0 : Fin 2 → ℝ))) bb = 0
            have hdiff : RBM.Gauss.shiftedDifference j
                (fun _ => (0 : Fin 2 → ℝ)) = (fun _ => (0 : Fin 2 → ℝ)) := by
              funext w
              ext l
              simp [RBM.Gauss.shiftedDifference]
            rw [hdiff]
            exact ih
      induction coords with
      | nil => cases hne rfl
      | cons i is ih =>
          change RBM.Gauss.shiftedDifferenceList is
            (RBM.Gauss.shiftedDifference i a) b = 0
          have hdiff : RBM.Gauss.shiftedDifference i a =
              (fun _ => (0 : Fin 2 → ℝ)) := by
            funext w
            ext j
            simp [RBM.Gauss.shiftedDifference, a]
          rw [hdiff]
          exact hconstant is b
    rw [hzero]
    simp [qNorm]

end RandomLmaxSmoothNormCubeComposition

end Gauss

end RBM
