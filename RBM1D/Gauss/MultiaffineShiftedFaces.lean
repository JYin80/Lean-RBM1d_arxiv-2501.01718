/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib

/-!
# Mixed derivatives of finite multiaffine interpolations

The interpolation is evaluated recursively along an ordered list of coordinates.  The recursive
formula is the usual product-weight interpolation: at coordinate `i` it takes the convex blend
with coefficients `1 - t i` and `t i` of the two `i`-faces.
-/

open scoped BigOperators

noncomputable section

namespace RBM.Gauss

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The recursive product-weight (multiaffine) interpolation over a coordinate list. -/
def multiaffineInterpOn : List ι → (ι → Bool) → ((ι → Bool) → V) → (ι → ℝ) → V
  | [], b, a, _ => a b
  | i :: is, b, a, t =>
      (1 - t i) • multiaffineInterpOn is (Function.update b i false) a t +
      t i • multiaffineInterpOn is (Function.update b i true) a t

/-- The shifted face difference in coordinate `i`. -/
def shiftedDifference (i : ι) (a : (ι → Bool) → V) : (ι → Bool) → V :=
  fun b => a (Function.update b i true) - a (Function.update b i false)

/-- Directional partial derivative in coordinate `i`, using the scalar derivative after updating
that coordinate. -/
def cubePartial (i : ι) (f : (ι → ℝ) → V) (t : ι → ℝ) : V :=
  deriv (fun s => f (Function.update t i s)) (t i)

/-- Iterated mixed partial, differentiating the listed distinct coordinates in list order. -/
def cubeMixedPartial : List ι → ((ι → ℝ) → V) → (ι → ℝ) → V
  | [], f, t => f t
  | i :: is, f, t => cubeMixedPartial is (fun x => cubePartial i f x) t

/-- Apply the listed coordinate differences to a vertex family in list order. -/
def shiftedDifferenceList : List ι → ((ι → Bool) → V) → (ι → Bool) → V
  | [], a, b => a b
  | i :: is, a, b => shiftedDifferenceList is (shiftedDifference i a) b

/-- The finite tree of complementary-coordinate weights and face values. Each branch chooses the
zero or one face of its next coordinate; the coefficient is the product of the branch weights. -/
def multiaffineTerms : List ι → ((ι → Bool) → V) → (ι → Bool) → (ι → ℝ) → List (ℝ × V)
  | [], a, b, _ => [(1, a b)]
  | i :: is, a, b, t =>
      (multiaffineTerms is a (Function.update b i false) t).map
          (fun p => ((1 - t i) * p.1, p.2)) ++
        (multiaffineTerms is a (Function.update b i true) t).map
          (fun p => (t i * p.1, p.2))

/-- Evaluate a finite list of scalar-weighted vectors, retaining repeated terms. -/
def weightedTermsValue : List (ℝ × V) → V
  | [] => 0
  | p :: ps => p.1 • p.2 + weightedTermsValue ps

/-- Sum the scalar weights in a finite list of terms. -/
def weightedTermsMass : List (ℝ × V) → ℝ
  | [] => 0
  | p :: ps => p.1 + weightedTermsMass ps

@[simp] theorem multiaffineInterpOn_nil (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn [] b a t = a b := rfl

theorem multiaffineInterpOn_update_irrel (coords : List ι) (i : ι)
    (h : i ∉ coords) (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) (s : ℝ) :
    multiaffineInterpOn coords b a (Function.update t i s) =
      multiaffineInterpOn coords b a t := by
  induction coords generalizing b with
  | nil => rfl
  | cons j js ih =>
      simp only [List.mem_cons, not_or] at h
      simp [multiaffineInterpOn, Function.update_of_ne (Ne.symm h.1),
        ih h.2 (Function.update b j false),
        ih h.2 (Function.update b j true)]

theorem multiaffineInterpOn_sub (coords : List ι) (b : ι → Bool)
    (a c : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn coords b (fun x => a x - c x) t =
      multiaffineInterpOn coords b a t - multiaffineInterpOn coords b c t := by
  induction coords generalizing b with
  | nil => rfl
  | cons i is ih =>
      simp only [multiaffineInterpOn, ih]
      module

theorem multiaffineInterpOn_update_family (coords : List ι) (i : ι)
    (h : i ∉ coords) (bit : Bool) (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn coords b (fun x => a (Function.update x i bit)) t =
      multiaffineInterpOn coords (Function.update b i bit) a t := by
  induction coords generalizing b with
  | nil => rfl
  | cons j js ih =>
      simp only [List.mem_cons, not_or] at h
      simp only [multiaffineInterpOn, ih h.2]
      rw [Function.update_comm (Ne.symm h.1) _ _ b,
        Function.update_comm (Ne.symm h.1) _ _ b]

theorem multiaffineInterpOn_shiftedDifference (coords : List ι) (i : ι)
    (h : i ∉ coords) (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn coords b (shiftedDifference i a) t =
      multiaffineInterpOn coords (Function.update b i true) a t -
        multiaffineInterpOn coords (Function.update b i false) a t := by
  change multiaffineInterpOn coords b
      (fun x => a (Function.update x i true) - a (Function.update x i false)) t = _
  rw [multiaffineInterpOn_sub,
    multiaffineInterpOn_update_family coords i h true,
    multiaffineInterpOn_update_family coords i h false]

/-- Two distinct adjacent coordinates can be blended in either order. -/
private theorem multiaffineInterpOn_swap (i j : ι) (is : List ι) (hij : i ≠ j)
    (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn (i :: j :: is) b a t =
      multiaffineInterpOn (j :: i :: is) b a t := by
  simp only [multiaffineInterpOn, Function.update_comm hij]
  module

/-- Reordering an enumeration of the full coordinate set leaves the standard interpolation
unchanged. -/
private theorem multiaffineInterpOn_perm {xs ys : List ι} (hperm : xs.Perm ys)
    (hnd : xs.Nodup) (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn xs b a t = multiaffineInterpOn ys b a t := by
  induction hperm generalizing b a t with
  | nil => rfl
  | cons i hperm ih =>
      have hnd' : List.Nodup _ := (List.nodup_cons.mp hnd).2
      simp only [multiaffineInterpOn]
      rw [ih hnd' (Function.update b i false) a t,
        ih hnd' (Function.update b i true) a t]
  | swap x y rest =>
      have hxy : x ≠ y := by
        intro hxy
        have hnot := (List.nodup_cons.mp hnd).1
        apply hnot
        simp [hxy]
      exact (multiaffineInterpOn_swap x y rest hxy b a t).symm
  | trans h₁ h₂ ih₁ ih₂ =>
      have hnd' : List.Nodup _ := (h₁.nodup_iff.mp hnd)
      exact (ih₁ hnd b a t).trans (ih₂ hnd' b a t)

/-- A unit-cube interpolation is bounded by the largest norm among its vertices. -/
theorem multiaffineInterpOn_norm_le (coords : List ι) (b : ι → Bool)
    (a : (ι → Bool) → V) (t : ι → ℝ) (B : ℝ)
    (ht : ∀ i ∈ coords, 0 ≤ t i ∧ t i ≤ 1)
    (ha : ∀ x, ‖a x‖ ≤ B) :
    ‖multiaffineInterpOn coords b a t‖ ≤ B := by
  induction coords generalizing b with
  | nil => simpa [multiaffineInterpOn] using ha b
  | cons i is ih =>
      have hi := ht i (by simp)
      have ht' : ∀ j ∈ is, 0 ≤ t j ∧ t j ≤ 1 := fun j hj => ht j (by simp [hj])
      have hlow := ih (Function.update b i false) ht'
      have hhigh := ih (Function.update b i true) ht'
      calc
        ‖multiaffineInterpOn (i :: is) b a t‖ ≤
            ‖(1 - t i) • multiaffineInterpOn is (Function.update b i false) a t‖ +
              ‖t i • multiaffineInterpOn is (Function.update b i true) a t‖ := norm_add_le _ _
        _ = |1 - t i| * ‖multiaffineInterpOn is (Function.update b i false) a t‖ +
              |t i| * ‖multiaffineInterpOn is (Function.update b i true) a t‖ := by
                simp [norm_smul, Real.norm_eq_abs]
        _ ≤ (1 - t i) * B + (t i) * B := by
              rw [abs_of_nonneg (by linarith [hi.2]), abs_of_nonneg hi.1]
              exact add_le_add
                (mul_le_mul_of_nonneg_left hlow (by linarith [hi.2]))
                (mul_le_mul_of_nonneg_left hhigh hi.1)
        _ = B := by ring

/-- Norm interpolation when the vertex bound is required only on a prescribed coordinate face.
Coordinates blended by the interpolation must be disjoint from the coordinates fixed on that face.
-/
theorem multiaffineInterpOn_norm_le_on_complement (coords : List ι) (J : Finset ι)
    (hdisj : ∀ i ∈ coords, i ∉ J) (b : ι → Bool) (a : (ι → Bool) → V)
    (t : ι → ℝ) (B : ℝ)
    (ht : ∀ i ∈ coords, 0 ≤ t i ∧ t i ≤ 1)
    (hb : ∀ i ∈ J, b i = false)
    (ha : ∀ x, (∀ i ∈ J, x i = false) → ‖a x‖ ≤ B) :
    ‖multiaffineInterpOn coords b a t‖ ≤ B := by
  induction coords generalizing b hb with
  | nil =>
      simpa [multiaffineInterpOn] using ha b hb
  | cons i is ih =>
      have hiJ : i ∉ J := hdisj i (by simp)
      have hdisj' : ∀ j ∈ is, j ∉ J := fun j hj => hdisj j (by simp [hj])
      have ht' : ∀ j ∈ is, 0 ≤ t j ∧ t j ≤ 1 := fun j hj => ht j (by simp [hj])
      have hb0 : ∀ j ∈ J, Function.update b i false j = false := by
        intro j hj
        by_cases hji : j = i
        · subst j
          exact (hiJ hj).elim
        · simp [Function.update_of_ne hji, hb j hj]
      have hb1 : ∀ j ∈ J, Function.update b i true j = false := by
        intro j hj
        by_cases hji : j = i
        · subst j
          exact (hiJ hj).elim
        · simp [Function.update_of_ne hji, hb j hj]
      have hlow := ih (b := Function.update b i false) (hb := hb0)
        (hdisj := hdisj') (ht := ht')
      have hhigh := ih (b := Function.update b i true) (hb := hb1)
        (hdisj := hdisj') (ht := ht')
      have hi := ht i (by simp)
      calc
        ‖multiaffineInterpOn (i :: is) b a t‖ ≤
            ‖(1 - t i) • multiaffineInterpOn is (Function.update b i false) a t‖ +
              ‖t i • multiaffineInterpOn is (Function.update b i true) a t‖ := norm_add_le _ _
        _ = |1 - t i| * ‖multiaffineInterpOn is (Function.update b i false) a t‖ +
              |t i| * ‖multiaffineInterpOn is (Function.update b i true) a t‖ := by
                simp [norm_smul, Real.norm_eq_abs]
        _ ≤ (1 - t i) * B + (t i) * B := by
              rw [abs_of_nonneg (by linarith [hi.2]), abs_of_nonneg hi.1]
              exact add_le_add
                (mul_le_mul_of_nonneg_left hlow (by linarith [hi.2]))
                (mul_le_mul_of_nonneg_left hhigh hi.1)
        _ = B := by ring

private theorem weightedTermsValue_append (xs ys : List (ℝ × V)) :
    weightedTermsValue (xs ++ ys) = weightedTermsValue xs + weightedTermsValue ys := by
  induction xs with
  | nil => simp [weightedTermsValue]
  | cons x xs ih => simp [weightedTermsValue, ih, add_assoc]

private theorem weightedTermsValue_map_scale (c : ℝ) (xs : List (ℝ × V)) :
    weightedTermsValue (xs.map (fun p => (c * p.1, p.2))) = c • weightedTermsValue xs := by
  induction xs with
  | nil => simp [weightedTermsValue]
  | cons x xs ih =>
      simp [weightedTermsValue, ih, mul_smul, smul_add, mul_comm]

/-- Recursive product interpolation is the finite convex sum encoded by its branch terms. -/
theorem multiaffineInterpOn_eq_weightedTerms (coords : List ι) (b : ι → Bool)
    (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpOn coords b a t = weightedTermsValue (multiaffineTerms coords a b t) := by
  induction coords generalizing b with
  | nil => simp [multiaffineInterpOn, multiaffineTerms, weightedTermsValue]
  | cons i is ih =>
      simp only [multiaffineInterpOn, multiaffineTerms, weightedTermsValue_append,
        weightedTermsValue_map_scale, ih]

private theorem weightedTermsMass_append (xs ys : List (ℝ × V)) :
    weightedTermsMass (xs ++ ys) = weightedTermsMass xs + weightedTermsMass ys := by
  induction xs with
  | nil => simp [weightedTermsMass]
  | cons x xs ih => simp [weightedTermsMass, ih, add_assoc]

private theorem weightedTermsMass_map_scale (c : ℝ) (xs : List (ℝ × V)) :
    weightedTermsMass (xs.map (fun p => (c * p.1, p.2))) = c * weightedTermsMass xs := by
  induction xs with
  | nil => simp [weightedTermsMass]
  | cons x xs ih => simp [weightedTermsMass, ih, mul_add, mul_comm]

/-- The branch weights of every finite multiaffine interpolation sum to one. -/
theorem multiaffineTerms_mass (coords : List ι) (a : (ι → Bool) → V)
    (b : ι → Bool) (t : ι → ℝ) : weightedTermsMass (multiaffineTerms coords a b t) = 1 := by
  induction coords generalizing b with
  | nil => simp [multiaffineTerms, weightedTermsMass]
  | cons i is ih =>
      simp only [multiaffineTerms, weightedTermsMass_append,
        weightedTermsMass_map_scale]
      rw [ih (Function.update b i false), ih (Function.update b i true)]
      ring

/-- The branch tree contains one term for every Boolean assignment of its listed coordinates. -/
theorem multiaffineTerms_length (coords : List ι) (a : (ι → Bool) → V)
    (b : ι → Bool) (t : ι → ℝ) :
    (multiaffineTerms coords a b t).length = 2 ^ coords.length := by
  induction coords generalizing b with
  | nil => simp [multiaffineTerms]
  | cons i is ih =>
      simp only [multiaffineTerms, List.length_append, List.length_map, ih]
      simp only [List.length_cons]
      rw [pow_succ]
      ring

/-- Every branch weight is nonnegative when all interpolation coordinates lie in `[0,1]`. -/
theorem multiaffineTerms_weight_nonneg (coords : List ι) (a : (ι → Bool) → V)
    (b : ι → Bool) (t : ι → ℝ)
    (ht : ∀ i ∈ coords, 0 ≤ t i ∧ t i ≤ 1) :
    ∀ p ∈ multiaffineTerms coords a b t, 0 ≤ p.1 := by
  induction coords generalizing b with
  | nil => simp [multiaffineTerms]
  | cons i is ih =>
      have hi := ht i (by simp)
      have ht' : ∀ j ∈ is, 0 ≤ t j ∧ t j ≤ 1 := fun j hj => ht j (by simp [hj])
      intro p hp
      simp only [multiaffineTerms, List.mem_append, List.mem_map] at hp
      rcases hp with hp | hp
      · rcases hp with ⟨q, hq, rfl⟩
        exact mul_nonneg (by linarith [hi.2]) (ih (Function.update b i false) ht' q hq)
      · rcases hp with ⟨q, hq, rfl⟩
        exact mul_nonneg hi.1 (ih (Function.update b i true) ht' q hq)

/-- The standard finite-cube interpolation in the canonical finite coordinate order. -/
def multiaffineInterpolation (a : (ι → Bool) → V) (t : ι → ℝ) : V :=
  multiaffineInterpOn Finset.univ.toList (fun _ => false) a t

/-- The same interpolation written with the selected coordinates first. This order is used to
differentiate one coordinate at a time. -/
def multiaffineInterpolationBySubsetOrder (J : Finset ι) (a : (ι → Bool) → V)
    (t : ι → ℝ) : V :=
  multiaffineInterpOn (J.toList ++ (Finset.univ \ J).toList) (fun _ => false) a t

private theorem multiaffineSubsetPartition_nodup (J : Finset ι) :
    (J.toList ++ (Finset.univ \ J).toList).Nodup := by
  apply List.Nodup.append J.nodup_toList (Finset.nodup_toList (Finset.univ \ J))
  intro x hxJ hxC
  have hJ : x ∈ J := by simpa only [Finset.mem_toList] using hxJ
  have hC : x ∈ Finset.univ \ J := by simpa only [Finset.mem_toList] using hxC
  exact (Finset.mem_sdiff.mp hC).2 hJ

private theorem multiaffineInterpolationBySubsetOrder_eq (J : Finset ι)
    (a : (ι → Bool) → V) (t : ι → ℝ) :
    multiaffineInterpolationBySubsetOrder J a t = multiaffineInterpolation a t := by
  have hperm : (J.toList ++ (Finset.univ \ J).toList).Perm Finset.univ.toList := by
    apply (List.perm_ext_iff_of_nodup (multiaffineSubsetPartition_nodup J)
      (Finset.univ.nodup_toList)).2
    intro i
    by_cases hi : i ∈ J <;> simp [hi, Finset.mem_sdiff]
  exact multiaffineInterpOn_perm hperm (multiaffineSubsetPartition_nodup J)
    (fun _ => false) a t

theorem deriv_affine_blend (x y : V) (s : ℝ) :
    deriv (fun u : ℝ => (1 - u) • x + u • y) s = y - x := by
  have h₁ : DifferentiableAt ℝ (fun u : ℝ => 1 - u) s := by fun_prop
  have h₂ : DifferentiableAt ℝ (fun u : ℝ => u) s := differentiableAt_id
  have h₁' : deriv (fun u : ℝ => 1 - u) s = -1 := by simp
  have h₂' : deriv (fun u : ℝ => u) s = 1 := by simp
  change deriv ((fun u : ℝ => (1 - u) • x) + (fun u : ℝ => u • y)) s = y - x
  rw [deriv_add (h₁.smul_const x) (h₂.smul_const y),
    deriv_smul_const h₁ x, deriv_smul_const h₂ y]
  rw [h₁', h₂']
  simp only [neg_smul, one_smul]
  abel

/-- Differentiating the first coordinate of a recursive interpolation replaces its vertex family
by the corresponding shifted face difference. -/
theorem cubePartial_multiaffineInterpOn_head (i : ι) (is : List ι)
    (h : i ∉ is) (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubePartial i (fun x => multiaffineInterpOn (i :: is) b a x) t =
      multiaffineInterpOn is b (shiftedDifference i a) t := by
  have hfun :
      (fun s : ℝ => multiaffineInterpOn (i :: is) b a (Function.update t i s)) =
        (fun s => (1 - s) • multiaffineInterpOn is (Function.update b i false) a t +
          s • multiaffineInterpOn is (Function.update b i true) a t) := by
    funext s
    simp [multiaffineInterpOn, multiaffineInterpOn_update_irrel is i h]
  rw [cubePartial, hfun, deriv_affine_blend]
  exact (multiaffineInterpOn_shiftedDifference is i h b a t).symm

/-- All mixed partials on a prefix of coordinates are the interpolation of the corresponding
iterated shifted-face differences on the remaining coordinates. -/
theorem cubeMixedPartial_multiaffineInterpOn_prefix (js ks : List ι)
    (hnd : (js ++ ks).Nodup) (b : ι → Bool) (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubeMixedPartial js (fun x => multiaffineInterpOn (js ++ ks) b a x) t =
      multiaffineInterpOn ks b (shiftedDifferenceList js a) t := by
  induction js generalizing ks a with
  | nil => rfl
  | cons i is ih =>
      change List.Nodup (i :: (is ++ ks)) at hnd
      have hnd' : i ∉ is ++ ks ∧ (is ++ ks).Nodup := by
        simpa only [List.nodup_cons] using hnd
      simp only [cubeMixedPartial]
      have hpart :
          (fun x => cubePartial i (fun y => multiaffineInterpOn (i :: (is ++ ks)) b a y) x) =
            (fun x => multiaffineInterpOn (is ++ ks) b (shiftedDifference i a) x) := by
        funext x
        exact cubePartial_multiaffineInterpOn_head i (is ++ ks) hnd'.1 b a x
      change cubeMixedPartial is
          (fun x => cubePartial i (fun y => multiaffineInterpOn (i :: (is ++ ks)) b a y) x) t =
        multiaffineInterpOn ks b (shiftedDifferenceList (i :: is) a) t
      rw [hpart]
      simpa [shiftedDifferenceList] using ih ks hnd'.2 (shiftedDifference i a)

/-- For every coordinate subset, the mixed partial of the finite-cube interpolation is the
convex tree sum of all shifted face differences. The complement coordinates index the branches. -/
private theorem cubeMixedPartial_shiftedFaces_subsetOrder (J : Finset ι)
    (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubeMixedPartial J.toList (fun x => multiaffineInterpolationBySubsetOrder J a x) t =
      weightedTermsValue
        (multiaffineTerms (Finset.univ \ J).toList (shiftedDifferenceList J.toList a)
          (fun _ => false) t) := by
  simp only [multiaffineInterpolationBySubsetOrder]
  rw [cubeMixedPartial_multiaffineInterpOn_prefix J.toList (Finset.univ \ J).toList
    (multiaffineSubsetPartition_nodup J) (fun _ => false) a t]
  exact multiaffineInterpOn_eq_weightedTerms _ _ _ _

/-- For every coordinate subset, the mixed partial of the standard finite-cube interpolation is
the convex tree sum of all shifted face differences. The complement coordinates index the branches. -/
theorem cubeMixedPartial_shiftedFaces (J : Finset ι) (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubeMixedPartial J.toList (fun x => multiaffineInterpolation a x) t =
      weightedTermsValue
        (multiaffineTerms (Finset.univ \ J).toList (shiftedDifferenceList J.toList a)
          (fun _ => false) t) := by
  have hfun : (fun x => multiaffineInterpolation a x) =
      (fun x => multiaffineInterpolationBySubsetOrder J a x) := by
    funext x
    exact (multiaffineInterpolationBySubsetOrder_eq J a x).symm
  rw [hfun]
  exact cubeMixedPartial_shiftedFaces_subsetOrder J a t

/-- The shifted-face coefficients in `cubeMixedPartial_shiftedFaces` sum to one. -/
theorem cubeMixedPartial_shiftedFaces_weights_sum (J : Finset ι)
    (a : (ι → Bool) → V) (t : ι → ℝ) :
    weightedTermsMass
      (multiaffineTerms (Finset.univ \ J).toList (shiftedDifferenceList J.toList a)
        (fun _ => false) t) = 1 :=
  multiaffineTerms_mass _ _ _ _

/-- Every coefficient in the shifted-face sum is nonnegative on the unit cube. -/
theorem cubeMixedPartial_shiftedFaces_weights_nonneg (J : Finset ι)
    (a : (ι → Bool) → V) (t : ι → ℝ)
    (ht : ∀ i ∈ Finset.univ \ J, 0 ≤ t i ∧ t i ≤ 1) :
    ∀ p ∈ multiaffineTerms (Finset.univ \ J).toList (shiftedDifferenceList J.toList a)
      (fun _ => false) t, 0 ≤ p.1 := by
  apply multiaffineTerms_weight_nonneg
  intro i hi
  exact ht i (by simpa only [Finset.mem_toList] using hi)

/-- The coefficients are nonnegative whenever `t` lies in the full unit cube. -/
theorem cubeMixedPartial_shiftedFaces_weights_nonneg_on_unitCube (J : Finset ι)
    (a : (ι → Bool) → V) (t : ι → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ∀ p ∈ multiaffineTerms (Finset.univ \ J).toList (shiftedDifferenceList J.toList a)
      (fun _ => false) t, 0 ≤ p.1 := by
  apply cubeMixedPartial_shiftedFaces_weights_nonneg J a t
  intro i hi
  exact ht i

/-- A uniform norm bound for every shifted face controls the mixed derivative. The face hypothesis
is imposed only at bases whose selected-coordinate bits are false, so it ranges exactly over the
complementary shifts. -/
theorem cubeMixedPartial_shiftedFaces_norm_le (J : Finset ι) (a : (ι → Bool) → V)
    (t : ι → ℝ) (B : ℝ)
    (ht : ∀ i ∈ Finset.univ \ J, 0 ≤ t i ∧ t i ≤ 1)
    (hface : ∀ b, (∀ i ∈ J, b i = false) →
      ‖shiftedDifferenceList J.toList a b‖ ≤ B) :
    ‖cubeMixedPartial J.toList (fun x => multiaffineInterpolation a x) t‖ ≤ B := by
  have hfun : (fun x => multiaffineInterpolation a x) =
      (fun x => multiaffineInterpolationBySubsetOrder J a x) := by
    funext x
    exact (multiaffineInterpolationBySubsetOrder_eq J a x).symm
  rw [hfun]
  simp only [multiaffineInterpolationBySubsetOrder,
    cubeMixedPartial_multiaffineInterpOn_prefix J.toList (Finset.univ \ J).toList
      (multiaffineSubsetPartition_nodup J) (fun _ => false) a t]
  apply multiaffineInterpOn_norm_le_on_complement (Finset.univ \ J).toList J
  · intro i hi
    have hi' : i ∈ Finset.univ \ J := by
      simpa only [Finset.mem_toList] using hi
    exact (Finset.mem_sdiff.mp hi').2
  · intro i hi
    exact ht i (by simpa only [Finset.mem_toList] using hi)
  · intro i hi
    simp
  · exact hface

/-- The norm estimate in particular holds for every `t` in the full unit cube. -/
theorem cubeMixedPartial_shiftedFaces_norm_le_on_unitCube (J : Finset ι)
    (a : (ι → Bool) → V) (t : ι → ℝ) (B : ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (hface : ∀ b, (∀ i ∈ J, b i = false) →
      ‖shiftedDifferenceList J.toList a b‖ ≤ B) :
    ‖cubeMixedPartial J.toList (fun x => multiaffineInterpolation a x) t‖ ≤ B :=
  cubeMixedPartial_shiftedFaces_norm_le J a t B (fun i _ => ht i) hface

/-- The empty subset is the zeroth-order identity. This also covers dimension zero, where there
are no nonempty coordinate subsets. -/
theorem cubeMixedPartial_empty (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubeMixedPartial ([] : List ι) (fun x => multiaffineInterpolation a x) t =
      multiaffineInterpolation a t := rfl

/-- For the full coordinate set there is one shifted face and its weight is one. -/
theorem cubeMixedPartial_full (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubeMixedPartial Finset.univ.toList (fun x => multiaffineInterpolation a x) t =
      shiftedDifferenceList Finset.univ.toList a (fun _ => false) := by
  simpa [cubeMixedPartial_shiftedFaces, multiaffineTerms, weightedTermsValue]

/-- For a singleton `J`, the same formula averages all shifted first-face differences on its
complementary coordinates. -/
theorem cubeMixedPartial_singleton (i : ι) (a : (ι → Bool) → V) (t : ι → ℝ) :
    cubeMixedPartial ({i} : Finset ι).toList (fun x => multiaffineInterpolation a x) t =
      weightedTermsValue
        (multiaffineTerms (Finset.univ \ {i}).toList
          (shiftedDifferenceList ({i} : Finset ι).toList a) (fun _ => false) t) :=
  cubeMixedPartial_shiftedFaces _ _ _

/-- `Fin 0` has no nonempty coordinate subset. -/
theorem fin_zero_has_no_nonempty_subset (J : Finset (Fin 0)) : ¬ J.Nonempty := by
  rintro ⟨i, hi⟩
  exact Fin.elim0 i

/-- The prescribed product witness in dimension two has a nonzero second shifted face. -/
def shiftedFaceWitness2 (v : Bool → Bool) : ℝ :=
  ∏ i : Bool, (1 + if v i then (1 : ℝ) else 0)

theorem shiftedFaceWitness2_secondFace :
    shiftedDifferenceList [false, true] shiftedFaceWitness2 (fun _ => false) = 1 := by
  norm_num [shiftedDifferenceList, shiftedDifference, shiftedFaceWitness2, Function.update]

/-- The same witness has a nonzero full mixed derivative of its multiaffine interpolation. -/
theorem shiftedFaceWitness2_mixedDerivative (t : Bool → ℝ) :
    cubeMixedPartial [false, true]
      (fun x => multiaffineInterpOn [false, true] (fun _ => false) shiftedFaceWitness2 x) t = 1 := by
  calc
    cubeMixedPartial [false, true]
        (fun x => multiaffineInterpOn [false, true] (fun _ => false) shiftedFaceWitness2 x) t =
      multiaffineInterpOn [] (fun _ => false)
        (shiftedDifferenceList [false, true] shiftedFaceWitness2) t := by
          simpa using cubeMixedPartial_multiaffineInterpOn_prefix [false, true] [] (by decide)
            (fun _ => false) shiftedFaceWitness2 t
    _ = 1 := by simpa using shiftedFaceWitness2_secondFace

end RBM.Gauss
