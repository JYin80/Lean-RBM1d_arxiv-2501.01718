/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Repeated fundamental theorem of calculus on finite boxes

For every finite dimension, the alternating sum over the vertices of the unit box is the nested
integral of the mixed derivative using each coordinate exactly once.  The derivative coordinates
are ordered by `Fin`; the recursion splits off coordinate `0`, with the upper face minus the lower
face.  No interpolation or vertex-family data is used.
-/

open Set intervalIntegral

noncomputable section

namespace RBM.Gauss

/-- The alternating vertex sum, recursively splitting the first coordinate.  At each step the
upper face has positive orientation and the lower face negative orientation, so its coefficients
are `(-1)^(r - number of upper coordinates)`. -/
def alternatingVertexSum : (r : ℕ) → ((Fin r → Bool) → ℝ) → ℝ
  | 0, f => f (fun i => Fin.elim0 i)
  | n + 1, f => alternatingVertexSum n (fun v => f (Fin.cons true v)) -
      alternatingVertexSum n (fun v => f (Fin.cons false v))

/-- Nested unit-interval integration, in coordinate order from the first coordinate inward. -/
def iteratedUnitIntegral : (r : ℕ) → ((Fin r → ℝ) → ℝ) → ℝ
  | 0, f => f (fun i => Fin.elim0 i)
  | n + 1, f => iteratedUnitIntegral n (fun t => ∫ x in (0 : ℝ)..1, f (Fin.cons x t))

/-- The full mixed derivative, evaluated on the coordinate unit vectors in `Fin` order. -/
def cubeMixedDerivative {r : ℕ} (f : (Fin r → ℝ) → ℝ) (t : Fin r → ℝ) : ℝ :=
  iteratedFDeriv ℝ r f t (fun i => Pi.single i 1)

/-- Evaluation of a continuous multilinear map at fixed arguments, as a continuous linear map. -/
def continuousMultilinearEval {ι : Type*} [Fintype ι] {E : ι → Type*}
    [(i : ι) → SeminormedAddCommGroup (E i)] [(i : ι) → NormedSpace ℝ (E i)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : (i : ι) → E i) : ContinuousMultilinearMap ℝ E F →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun f => f v
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
    (∏ i, ‖v i‖)
    (by
      intro f
      calc
        ‖f v‖ ≤ ‖f‖ * ∏ i, ‖v i‖ := f.le_opNorm v
        _ = (∏ i, ‖v i‖) * ‖f‖ := by ring)

/-- Insert a zero first coordinate as a continuous linear map. -/
def tailEmbedding (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (Fin.cases 0 (fun i => ContinuousLinearMap.proj i))

@[simp]
theorem tailEmbedding_apply (n : ℕ) (t : Fin n → ℝ) :
    tailEmbedding n t = Fin.cons 0 t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [tailEmbedding]
  · simp [tailEmbedding]

@[simp]
theorem tailEmbedding_single (n : ℕ) (i : Fin n) :
    tailEmbedding n (Pi.single i (1 : ℝ)) = Pi.single i.succ 1 := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [tailEmbedding]
  · simp [tailEmbedding, Pi.single_apply]

/-- Restricting a smooth function to a coordinate face differentiates in the remaining coordinate
directions by evaluating the ambient derivative on the corresponding shifted unit vectors. -/
theorem cubeMixedDerivative_slice {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ContDiff ℝ n f) (x : ℝ) (t : Fin n → ℝ) :
    cubeMixedDerivative (fun u => f (Fin.cons x u)) t =
      iteratedFDeriv ℝ n f (Fin.cons x t) (fun i => Pi.single i.succ 1) := by
  let c : Fin (n + 1) → ℝ := Fin.cons x 0
  let f' : (Fin (n + 1) → ℝ) → ℝ := fun z => f (c + z)
  have hf' : ContDiff ℝ n f' := by
    have htrans : ContDiff ℝ n (fun z : Fin (n + 1) → ℝ => c + z) := by
      exact (contDiff_const : ContDiff ℝ n (fun _ : Fin (n + 1) → ℝ => c)).add contDiff_id
    exact hf.comp htrans
  have hcomp := (tailEmbedding n).iteratedFDeriv_comp_right hf' t (i := n) le_rfl
  have hfun : (fun u => f (Fin.cons x u)) = f' ∘ tailEmbedding n := by
    funext u
    simp only [Function.comp_apply, f', c, tailEmbedding_apply]
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [cubeMixedDerivative, hfun, hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hshift : iteratedFDeriv ℝ n f' (tailEmbedding n t) =
      iteratedFDeriv ℝ n f (Fin.cons x t) := by
    have hct : c + Fin.cons 0 t = Fin.cons x t := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [c]
    rw [show f' = fun z => f (c + z) from rfl, iteratedFDeriv_comp_add_left]
    simpa [tailEmbedding_apply] using congrArg (iteratedFDeriv ℝ n f) hct
  rw [hshift]
  congr 1
  funext i
  exact tailEmbedding_single n i

/-- The recursive box integral is linear over differences of continuous integrands. -/
theorem iteratedUnitIntegral_sub {r : ℕ} (f g : (Fin r → ℝ) → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    iteratedUnitIntegral r (fun t => f t - g t) =
      iteratedUnitIntegral r f - iteratedUnitIntegral r g := by
  induction r with
  | zero => simp [iteratedUnitIntegral]
  | succ n ih =>
      have hparam (h : (Fin (n + 1) → ℝ) → ℝ) (hh : Continuous h) :
          Continuous (fun t : Fin n → ℝ => ∫ x in (0 : ℝ)..1, h (Fin.cons x t)) := by
        apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        fun_prop
      have hpoint :
          (fun t : Fin n → ℝ => ∫ x in (0 : ℝ)..1,
            (f (Fin.cons x t) - g (Fin.cons x t))) =
          (fun t => ∫ x in (0 : ℝ)..1, f (Fin.cons x t)) -
            (fun t => ∫ x in (0 : ℝ)..1, g (Fin.cons x t)) := by
        funext t
        rw [intervalIntegral.integral_sub]
        · rfl
        · exact (hf.comp (by fun_prop)).intervalIntegrable 0 1
        · have hcont : Continuous (fun x : ℝ => g (Fin.cons x t)) := by fun_prop
          exact hcont.intervalIntegrable 0 1
      change iteratedUnitIntegral n
          (fun t => ∫ x in (0 : ℝ)..1, (f (Fin.cons x t) - g (Fin.cons x t))) = _
      calc
        iteratedUnitIntegral n
            (fun t => ∫ x in (0 : ℝ)..1, (f (Fin.cons x t) - g (Fin.cons x t))) =
            iteratedUnitIntegral n
              (fun t => (∫ x in (0 : ℝ)..1, f (Fin.cons x t)) -
                (∫ x in (0 : ℝ)..1, g (Fin.cons x t))) := by
                  congr 1
        _ = _ := by
          rw [ih _ _ (hparam f hf) (hparam g hg)]
          rfl

/-- The coordinate directions used in the full mixed derivative. -/
def cubeCoordinateDirections (r : ℕ) : Fin r → (Fin r → ℝ) :=
  fun i => Pi.single i 1

/-- Continuity of the full mixed derivative of a `C^r` function. -/
theorem cubeMixedDerivative_continuous {r : ℕ} (f : (Fin r → ℝ) → ℝ)
    (hf : ContDiff ℝ r f) : Continuous (cubeMixedDerivative f) := by
  unfold cubeMixedDerivative
  exact (continuousMultilinearEval (cubeCoordinateDirections r)).continuous.comp
    (hf.continuous_iteratedFDeriv le_rfl)

/-- Smoothness, as a function of the base point, of the order-`n` derivative in the tail
coordinates. -/
theorem cubeTailMixed_contDiff {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ)
    (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ 1 (fun z => iteratedFDeriv ℝ n f z
      (fun i => Pi.single i.succ 1)) := by
  let d : Fin n → (Fin (n + 1) → ℝ) := fun i => Pi.single i.succ 1
  have hiter : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (m := 1) (by norm_cast; omega)
  change ContDiff ℝ 1 (continuousMultilinearEval d ∘ iteratedFDeriv ℝ n f)
  exact (continuousMultilinearEval d).contDiff.comp hiter

/-- Differentiating the tail mixed derivative in the first coordinate gives the full mixed
derivative. -/
theorem cubeMixedDerivative_cons_hasDerivAt {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : ContDiff ℝ (n + 1) f)
    (t : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun y => cubeMixedDerivative (fun u => f (Fin.cons y u)) t)
      (cubeMixedDerivative f (Fin.cons x t)) x := by
  let d : Fin n → (Fin (n + 1) → ℝ) := fun i => Pi.single i.succ 1
  let F : (Fin (n + 1) → ℝ) → ℝ :=
    fun z => iteratedFDeriv ℝ n f z d
  have hF : ContDiff ℝ 1 F := by
    change ContDiff ℝ 1 (fun z => iteratedFDeriv ℝ n f z d)
    exact cubeTailMixed_contDiff f hf
  let line : ℝ → (Fin (n + 1) → ℝ) :=
    fun y => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) y t
  have hline : HasDerivAt line
      (Pi.single (0 : Fin (n + 1)) 1) x := by
    have heq : line = fun y => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0 t +
        y • Pi.single (0 : Fin (n + 1)) 1 := by
      funext y
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [line]
    rw [heq]
    convert (hasDerivAt_const x (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0 t)).add
      ((hasDerivAt_id x).smul_const (Pi.single (0 : Fin (n + 1)) 1)) using 1
    · funext y
      rfl
    · simp
  have hFdifferentiable : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hcomp := (hFdifferentiable (line x)).hasFDerivAt.comp x hline.hasFDerivAt
  have hFderiv : fderiv ℝ F (line x) (Pi.single (0 : Fin (n + 1)) 1) =
      cubeMixedDerivative f (Fin.cons x t) := by
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) (line x) :=
      ((hf.iteratedFDeriv_right (m := 1) (by norm_cast; omega)).differentiable
        (by norm_num)) (line x)
    rw [cubeMixedDerivative]
    have htail : Fin.tail (fun i : Fin (n + 1) =>
          (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)) =
        (fun i : Fin n => (Pi.single i.succ (1 : ℝ) : Fin (n + 1) → ℝ)) := by
      funext i
      rfl
    simpa [F, d, cubeCoordinateDirections, line, htail] using
      (DifferentiableAt.iteratedFDeriv_succ_apply_left'
        (m := fun i => Pi.single i 1) hdiff).symm
  have hpsi : HasDerivAt (fun y : ℝ => F (Fin.cons y t))
      (cubeMixedDerivative f (Fin.cons x t)) x := by
    have h := hcomp.hasDerivAt
    convert h using 1
    · rfl
    · simpa using hFderiv.symm
  have hfun : (fun y => cubeMixedDerivative (fun u => f (Fin.cons y u)) t) =
      fun y => F (line y) := by
    funext y
    simpa [F, d] using cubeMixedDerivative_slice f (hf.of_le (by norm_cast; omega)) y t
  rw [hfun]
  exact hpsi

/-- Inserting a fixed first coordinate is a smooth affine map. -/
theorem contDiff_finCons (n : ℕ) (b : ℝ) :
    ContDiff ℝ n (fun v : Fin n → ℝ =>
      Fin.cons (α := fun _ : Fin (n + 1) => ℝ) b v) := by
  let c : Fin (n + 1) → ℝ := Fin.cons (α := fun _ : Fin (n + 1) => ℝ) b 0
  have hsum : ContDiff ℝ n (fun v : Fin n → ℝ => c + tailEmbedding n v) := by
    exact (contDiff_const : ContDiff ℝ n (fun _ : Fin n → ℝ => c)).add
      (tailEmbedding n).contDiff
  have heq : (fun v : Fin n → ℝ => c + tailEmbedding n v) =
      (fun v => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) b v) := by
    funext v
    rw [tailEmbedding_apply]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [c]
  rw [← heq]
  exact hsum

/-- Repeated one-dimensional FTC on the unit box: the alternating vertex sum equals the nested
integral of the full mixed derivative, for every finite dimension. -/
theorem alternatingVertexSum_eq_iteratedUnitIntegral {r : ℕ}
    (f : (Fin r → ℝ) → ℝ) (hf : ContDiff ℝ r f) :
    alternatingVertexSum r (fun v => f (fun i => if v i then 1 else 0)) =
      iteratedUnitIntegral r (cubeMixedDerivative f) := by
  induction r with
  | zero =>
      simp only [alternatingVertexSum, iteratedUnitIntegral, cubeMixedDerivative,
        iteratedFDeriv_zero_apply]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      have hf' : ContDiff ℝ n f := hf.of_le (by norm_cast; omega)
      have htrue : ContDiff ℝ n
          (fun v : Fin n → ℝ => f (Fin.cons 1 v)) := by
        exact hf'.comp (contDiff_finCons n 1)
      have hfalse : ContDiff ℝ n
          (fun v : Fin n → ℝ => f (Fin.cons 0 v)) := by
        exact hf'.comp (contDiff_finCons n 0)
      have htrueFTC := ih (f := fun v : Fin n → ℝ => f (Fin.cons 1 v)) htrue
      have hfalseFTC := ih (f := fun v : Fin n → ℝ => f (Fin.cons 0 v)) hfalse
      have hcontTrue := cubeMixedDerivative_continuous
        (fun v : Fin n → ℝ => f (Fin.cons 1 v)) htrue
      have hcontFalse := cubeMixedDerivative_continuous
        (fun v : Fin n → ℝ => f (Fin.cons 0 v)) hfalse
      have hFTC (t : Fin n → ℝ) :
          ∫ x in (0 : ℝ)..1, cubeMixedDerivative f (Fin.cons x t) =
            cubeMixedDerivative (fun v : Fin n → ℝ => f (Fin.cons 1 v)) t -
              cubeMixedDerivative (fun v : Fin n → ℝ => f (Fin.cons 0 v)) t := by
        let ψ : ℝ → ℝ := fun y =>
          cubeMixedDerivative (fun v : Fin n → ℝ => f (Fin.cons y v)) t
        have hderiv (x : ℝ) : HasDerivAt ψ (cubeMixedDerivative f (Fin.cons x t)) x := by
          simpa [ψ] using cubeMixedDerivative_cons_hasDerivAt f hf t x
        have hEq : (fun x => deriv ψ x) = fun x => cubeMixedDerivative f (Fin.cons x t) := by
          funext x
          exact (hderiv x).deriv
        have hcont : Continuous (fun x : ℝ => cubeMixedDerivative f (Fin.cons x t)) := by
          exact (cubeMixedDerivative_continuous f hf).comp (by fun_prop)
        have hint : IntervalIntegrable (deriv ψ) MeasureTheory.volume 0 1 := by
          have hcontDeriv : Continuous (deriv ψ) := by
            change Continuous (fun x => deriv ψ x)
            rw [hEq]
            exact hcont
          exact hcontDeriv.intervalIntegrable 0 1
        rw [← hEq]
        exact intervalIntegral.integral_deriv_eq_sub
          (fun x _ => (hderiv x).differentiableAt) hint
      have hvertices (b : Bool) (v : Fin n → Bool) :
          (fun i : Fin (n + 1) =>
            if Fin.cons (α := fun _ : Fin (n + 1) => Bool) b v i then 1 else 0) =
            Fin.cons (α := fun _ : Fin (n + 1) => ℝ) (if b then 1 else 0)
              (fun i => if v i then 1 else 0) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      calc
        alternatingVertexSum (n + 1)
            (fun v => f (fun i => if v i then 1 else 0)) =
            iteratedUnitIntegral n (cubeMixedDerivative
                (fun v : Fin n → ℝ => f (Fin.cons 1 v))) -
              iteratedUnitIntegral n (cubeMixedDerivative
                (fun v : Fin n → ℝ => f (Fin.cons 0 v))) := by
                  simp only [alternatingVertexSum]
                  rw [show (fun v : Fin n → Bool =>
                      f (fun i => if Fin.cons (α := fun _ : Fin (n + 1) => Bool) true v i
                        then 1 else 0)) =
                        (fun v => f (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 1
                          (fun i => if v i then 1 else 0))) by
                          funext v
                          exact congrArg f (hvertices true v)]
                  rw [show (fun v : Fin n → Bool =>
                      f (fun i => if Fin.cons (α := fun _ : Fin (n + 1) => Bool) false v i
                        then 1 else 0)) =
                        (fun v => f (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0
                          (fun i => if v i then 1 else 0))) by
                          funext v
                          exact congrArg f (hvertices false v)]
                  rw [htrueFTC, hfalseFTC]
        _ = iteratedUnitIntegral n (fun t =>
              cubeMixedDerivative (fun v : Fin n → ℝ => f (Fin.cons 1 v)) t -
                cubeMixedDerivative (fun v : Fin n → ℝ => f (Fin.cons 0 v)) t) := by
                  symm
                  exact iteratedUnitIntegral_sub _ _ hcontTrue hcontFalse
        _ = iteratedUnitIntegral n (fun t =>
              ∫ x in (0 : ℝ)..1, cubeMixedDerivative f (Fin.cons x t)) := by
                  congr 1
                  funext t
                  exact (hFTC t).symm
        _ = iteratedUnitIntegral (n + 1) (cubeMixedDerivative f) := rfl

/-- The coordinate product is a nondegenerate witness: its alternating vertex sum is one in
every dimension, including dimension zero. -/
theorem alternatingVertexSum_coordinateProduct (r : ℕ) :
    alternatingVertexSum r (fun v => ∏ i : Fin r, if v i then 1 else 0) = 1 := by
  induction r with
  | zero => simp [alternatingVertexSum]
  | succ n ih =>
      have hzero : ∀ m : ℕ,
          alternatingVertexSum m (fun _ : Fin m → Bool => (0 : ℝ)) = 0 := by
        intro m
        induction m with
        | zero => simp [alternatingVertexSum]
        | succ k ih => simp [alternatingVertexSum, ih]
      simp [alternatingVertexSum, Fin.prod_univ_succ, ih, hzero]

/-- The full mixed derivative of `c * ∏ i, t_i` is the constant `c`, with no repeated
coordinate direction. -/
theorem cubeMixedDerivative_scaledCoordinateProduct {r : ℕ} (c : ℝ) (t : Fin r → ℝ) :
    cubeMixedDerivative (fun u => c * ∏ i : Fin r, u i) t = c := by
  induction r generalizing c with
  | zero => simp [cubeMixedDerivative]
  | succ n ih =>
      let x : ℝ := t 0
      let u : Fin n → ℝ := Fin.tail t
      have ht : t = Fin.cons (α := fun _ : Fin (n + 1) => ℝ) x u := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [x]
        · rfl
      rw [ht]
      let g : (Fin (n + 1) → ℝ) → ℝ := fun z => c * ∏ i : Fin (n + 1), z i
      have hg : ContDiff ℝ (n + 1) g := by
        dsimp [g]
        fun_prop
      have hrec := cubeMixedDerivative_cons_hasDerivAt g hg u x
      have hslice :
          (fun y : ℝ => cubeMixedDerivative
            (fun v : Fin n → ℝ => c * ∏ i : Fin (n + 1),
              Fin.cons (α := fun _ : Fin (n + 1) => ℝ) y v i) u) =
            fun y => c * y := by
        funext y
        have hprod :
            (fun v : Fin n → ℝ => c * ∏ i : Fin (n + 1),
              Fin.cons (α := fun _ : Fin (n + 1) => ℝ) y v i) =
            fun v => (c * y) * ∏ i : Fin n, v i := by
          funext v
          rw [Fin.prod_univ_succ]
          simp [Fin.cons, mul_assoc]
        rw [hprod]
        exact ih (c * y) u
      calc
        cubeMixedDerivative g (Fin.cons x u) =
            deriv (fun y : ℝ => cubeMixedDerivative
              (fun v : Fin n → ℝ => g (Fin.cons y v)) u) x := by
                symm
                exact hrec.deriv
        _ = deriv (fun y : ℝ => c * y) x := by
              congr 1
        _ = c := by simp

/-- The requested product witness has alternating sum, full mixed derivative, and nested integral
all equal to one, including the empty-dimensional case. -/
theorem cubeFTC_coordinateProduct_witness (r : ℕ) :
    alternatingVertexSum r (fun v => ∏ i : Fin r, if v i then 1 else 0) = 1 ∧
      (∀ t : Fin r → ℝ,
        cubeMixedDerivative (fun u => ∏ i : Fin r, u i) t = 1) ∧
      iteratedUnitIntegral r (cubeMixedDerivative (fun u => ∏ i : Fin r, u i)) = 1 := by
  have hsum := alternatingVertexSum_coordinateProduct r
  have hderiv : ∀ t : Fin r → ℝ,
      cubeMixedDerivative (fun u => ∏ i : Fin r, u i) t = 1 := by
    intro t
    simpa using cubeMixedDerivative_scaledCoordinateProduct (r := r) 1 t
  have hFTC := alternatingVertexSum_eq_iteratedUnitIntegral
    (f := fun u : Fin r → ℝ => ∏ i : Fin r, u i) (by fun_prop)
  exact ⟨hsum, hderiv, by rw [← hFTC, hsum]⟩

end RBM.Gauss
