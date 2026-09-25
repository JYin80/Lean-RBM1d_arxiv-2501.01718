/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FiniteCubeRepeatedFTC
import Mathlib.Topology.TietzeExtension

/-!
# Local-neighborhood repeated fundamental theorem of calculus on finite cubes

The alternating vertex identity needs only `C^r` regularity on an open neighborhood of the
unit cube.  The proof keeps the analytic argument inside that neighborhood; continuous Tietze
extensions are used only to justify linearity of the nested integrals.
-/

open Set intervalIntegral Filter

noncomputable section

namespace RBM.Gauss

/-- The closed coordinate unit cube in a finite-dimensional real function space. -/
def unitCoordinateCube (r : ℕ) : Set (Fin r → ℝ) :=
  {t | ∀ i, t i ∈ Icc (0 : ℝ) 1}

theorem unitCoordinateCube_closed (r : ℕ) : IsClosed (unitCoordinateCube r) := by
  rw [unitCoordinateCube, Set.ofPred_forall]
  exact isClosed_iInter fun i => IsClosed.preimage (continuous_apply i) isClosed_Icc

theorem unitCoordinateCube_cons {r : ℕ} (x : ℝ) (t : Fin r → ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) (ht : t ∈ unitCoordinateCube r) :
    Fin.cons x t ∈ unitCoordinateCube (r + 1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · exact ht j

/-- Equality of nested unit-cube integrals depends only on values on the cube. -/
theorem iteratedUnitIntegral_congr_unitCoordinateCube {r : ℕ}
    (f g : (Fin r → ℝ) → ℝ)
    (hfg : ∀ t ∈ unitCoordinateCube r, f t = g t) :
    iteratedUnitIntegral r f = iteratedUnitIntegral r g := by
  induction r with
  | zero =>
      change f (fun i => Fin.elim0 i) = g (fun i => Fin.elim0 i)
      exact hfg _ (by intro i; exact Fin.elim0 i)
  | succ n ih =>
      change iteratedUnitIntegral n
          (fun t => ∫ x in (0 : ℝ)..1, f (Fin.cons x t)) =
        iteratedUnitIntegral n
          (fun t => ∫ x in (0 : ℝ)..1, g (Fin.cons x t))
      apply ih
      intro t ht
      apply intervalIntegral.integral_congr
      intro x hx
      have h01 : (0 : ℝ) ≤ 1 := by norm_num
      have hxIcc : x ∈ Icc (0 : ℝ) 1 := (uIcc_of_le h01).symm ▸ hx
      exact hfg (Fin.cons x t) (unitCoordinateCube_cons x t hxIcc ht)

/-- A continuous scalar function on the closed cube has a continuous global extension. -/
theorem exists_continuous_extension_unitCoordinateCube {r : ℕ}
    (f : (Fin r → ℝ) → ℝ) (hf : ContinuousOn f (unitCoordinateCube r)) :
    ∃ F : (Fin r → ℝ) → ℝ, Continuous F ∧
      ∀ t ∈ unitCoordinateCube r, F t = f t := by
  let fC : C(unitCoordinateCube r, ℝ) :=
    ⟨(unitCoordinateCube r).domRestrict f, hf.domRestrict⟩
  obtain ⟨F, -, hF⟩ := fC.exists_extension_forall_mem_of_isClosedEmbedding
    (t := Set.univ) (fun _ => mem_univ _) univ_nonempty
    (unitCoordinateCube_closed r).isClosedEmbedding_subtypeVal
  refine ⟨F, F.continuous, ?_⟩
  intro t ht
  have hval := congrFun hF ⟨t, ht⟩
  exact hval

/-- Local-domain version of linearity for nested cube integrals.  The extension theorem above is
used only for the continuous integrands; no differentiability is extended outside the cube. -/
theorem iteratedUnitIntegral_sub_of_continuousOn_unitCoordinateCube {r : ℕ}
    (f g : (Fin r → ℝ) → ℝ)
    (hf : ContinuousOn f (unitCoordinateCube r))
    (hg : ContinuousOn g (unitCoordinateCube r)) :
    iteratedUnitIntegral r (fun t => f t - g t) =
      iteratedUnitIntegral r f - iteratedUnitIntegral r g := by
  obtain ⟨F, hFcont, hF⟩ := exists_continuous_extension_unitCoordinateCube f hf
  obtain ⟨G, hGcont, hG⟩ := exists_continuous_extension_unitCoordinateCube g hg
  have hfg : ∀ t ∈ unitCoordinateCube r, f t - g t = F t - G t := by
    intro t ht
    rw [← hF t ht, ← hG t ht]
  have hf' : ∀ t ∈ unitCoordinateCube r, f t = F t := fun t ht => (hF t ht).symm
  have hg' : ∀ t ∈ unitCoordinateCube r, g t = G t := fun t ht => (hG t ht).symm
  rw [iteratedUnitIntegral_congr_unitCoordinateCube _ _ hfg,
    iteratedUnitIntegral_congr_unitCoordinateCube _ _ hf',
    iteratedUnitIntegral_congr_unitCoordinateCube _ _ hg']
  exact iteratedUnitIntegral_sub F G hFcont hGcont

/-- The mixed derivative is continuous on any open domain on which the input is `C^r`. -/
theorem cubeMixedDerivative_continuousOn_of_contDiffOn {r : ℕ}
    (f : (Fin r → ℝ) → ℝ) (U : Set (Fin r → ℝ)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ r f U) : ContinuousOn (cubeMixedDerivative f) U := by
  unfold cubeMixedDerivative
  exact (continuousMultilinearEval (cubeCoordinateDirections r)).continuous.comp_continuousOn
    (ContinuousOn.continuousOn_iteratedFDeriv hf hU le_rfl)

/-- Restricting to a face and differentiating the remaining coordinates agrees with the
corresponding ambient iterated derivative, provided the point lies in the open smoothness domain. -/
theorem cubeMixedDerivative_slice_of_contDiffOn {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (U : Set (Fin (n + 1) → ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ n f U) (x : ℝ) (t : Fin n → ℝ)
    (hxt : Fin.cons x t ∈ U) :
    cubeMixedDerivative (fun u => f (Fin.cons x u)) t =
      iteratedFDeriv ℝ n f (Fin.cons x t) (fun i => Pi.single i.succ 1) := by
  let c : Fin (n + 1) → ℝ := Fin.cons x 0
  let trans : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun z => c + z
  let V : Set (Fin (n + 1) → ℝ) := trans ⁻¹' U
  let emb := tailEmbedding n
  let W : Set (Fin n → ℝ) := emb ⁻¹' V
  let f' : (Fin (n + 1) → ℝ) → ℝ := f ∘ trans
  let q : (Fin n → ℝ) → ℝ := f' ∘ emb
  have hV : IsOpen V := hU.preimage (by fun_prop : Continuous trans)
  have hW : IsOpen W := hV.preimage emb.continuous
  have htrans : ContDiffOn ℝ n trans V :=
    (contDiff_const.add contDiff_id : ContDiff ℝ n trans).contDiffOn
  have hmap : MapsTo trans V U := fun z hz => hz
  have hf' : ContDiffOn ℝ n f' V := by
    exact hf.comp htrans hmap
  have hq : ContDiffOn ℝ n q W := hf'.comp_continuousLinearMap emb
  have hc : c + emb t = Fin.cons x t := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [c, emb, tailEmbedding_apply]
  have htW : t ∈ W := by
    change trans (emb t) ∈ U
    simpa [trans, hc] using hxt
  have hembV : emb t ∈ V := htW
  have hqAt : ContDiffAt ℝ n q t := hq.contDiffAt (hW.mem_nhds htW)
  have hf'At : ContDiffAt ℝ n f' (emb t) := hf'.contDiffAt (hV.mem_nhds hembV)
  have hqWithin := emb.iteratedFDerivWithin_comp_right (f := f') (s := V)
    hf' hV.uniqueDiffOn hW.uniqueDiffOn hembV (i := n) le_rfl
  have hqAmbient : iteratedFDerivWithin ℝ n q W t = iteratedFDeriv ℝ n q t :=
    iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn hqAt htW
  have hf'ambient :
      iteratedFDerivWithin ℝ n f' V (emb t) = iteratedFDeriv ℝ n f' (emb t) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hf'At hembV
  have hqEq : q = fun u => f (Fin.cons x u) := by
    funext u
    change f (c + emb u) = f (Fin.cons x u)
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [c, emb, tailEmbedding_apply]
    · simp [c, emb, tailEmbedding_apply]
  calc
    cubeMixedDerivative (fun u => f (Fin.cons x u)) t =
        iteratedFDeriv ℝ n q t (cubeCoordinateDirections n) := by
          change iteratedFDeriv ℝ n (fun u => f (Fin.cons x u)) t
              (fun i => Pi.single i 1) =
            iteratedFDeriv ℝ n q t (fun i => Pi.single i 1)
          rw [hqEq]
    _ = iteratedFDerivWithin ℝ n q W t (cubeCoordinateDirections n) := by
          rw [hqAmbient]
    _ = iteratedFDerivWithin ℝ n f' V (emb t)
          (fun i => emb (cubeCoordinateDirections n i)) := by
          rw [hqWithin]
          simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, cubeCoordinateDirections]
    _ = iteratedFDeriv ℝ n f' (emb t)
          (fun i => emb (cubeCoordinateDirections n i)) := by
          rw [hf'ambient]
    _ = iteratedFDeriv ℝ n f (Fin.cons x t)
          (fun i => Pi.single i.succ 1) := by
          rw [show f' = fun z => f (c + z) from rfl, iteratedFDeriv_comp_add_left]
          rw [hc]
          congr 1
          funext i
          change tailEmbedding n (Pi.single i 1) = Pi.single i.succ 1
          exact tailEmbedding_single n i

/-- One additional derivative of the tail mixed derivative is available at each point of the
open local `C^(n+1)` domain. -/
theorem cubeTailMixed_contDiffAt_of_contDiffAt {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (z : Fin (n + 1) → ℝ)
    (hf : ContDiffAt ℝ (n + 1) f z) :
    ContDiffAt ℝ 1
      (fun y => iteratedFDeriv ℝ n f y (fun i => Pi.single i.succ 1)) z := by
  let d : Fin n → (Fin (n + 1) → ℝ) := fun i => Pi.single i.succ 1
  let F : (Fin (n + 1) → ℝ) → ℝ := fun y => iteratedFDeriv ℝ n f y d
  have hiter : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) z :=
    hf.iteratedFDeriv_right (i := n) (m := 1) (by norm_num [Nat.cast_add, add_comm])
  have hF : ContDiffAt ℝ 1 F z := by
    change ContDiffAt ℝ 1 (continuousMultilinearEval d ∘ iteratedFDeriv ℝ n f) z
    exact (continuousMultilinearEval d).contDiff.contDiffAt.comp z hiter
  simpa [F, d] using hF

/-- The all-finite-dimensional alternating-vertex identity under the local regularity needed on
the cube: `g` is `C^r` on an open neighborhood of that cube only. -/
theorem alternatingVertexSum_eq_iteratedUnitIntegral_of_contDiffOn
    {r : ℕ} (f : (Fin r → ℝ) → ℝ) (U : Set (Fin r → ℝ))
    (hU : IsOpen U) (hcube : unitCoordinateCube r ⊆ U)
    (hf : ContDiffOn ℝ r f U) :
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
      let faceTrue : (Fin n → ℝ) → ℝ := fun v => f (Fin.cons 1 v)
      let faceFalse : (Fin n → ℝ) → ℝ := fun v => f (Fin.cons 0 v)
      let UTrue : Set (Fin n → ℝ) := (fun v => Fin.cons 1 v) ⁻¹' U
      let UFalse : Set (Fin n → ℝ) := (fun v => Fin.cons 0 v) ⁻¹' U
      have hTrueOpen : IsOpen UTrue := hU.preimage (by fun_prop)
      have hFalseOpen : IsOpen UFalse := hU.preimage (by fun_prop)
      have hTrueCube : unitCoordinateCube n ⊆ UTrue := by
        intro t ht
        exact hcube (unitCoordinateCube_cons 1 t (by norm_num) ht)
      have hFalseCube : unitCoordinateCube n ⊆ UFalse := by
        intro t ht
        exact hcube (unitCoordinateCube_cons 0 t (by norm_num) ht)
      have hbase : ContDiffOn ℝ n f U := hf.of_le (by norm_cast; omega)
      have hconsTrue : ContDiffOn ℝ n
          (fun v : Fin n → ℝ => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 1 v) UTrue :=
        ContDiffOn.mono (s := Set.univ) (t := UTrue)
          (contDiffOn_univ.mpr (contDiff_finCons n 1)) (Set.subset_univ UTrue)
      have hconsFalse : ContDiffOn ℝ n
          (fun v : Fin n → ℝ => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0 v) UFalse :=
        ContDiffOn.mono (s := Set.univ) (t := UFalse)
          (contDiffOn_univ.mpr (contDiff_finCons n 0)) (Set.subset_univ UFalse)
      have hFaceTrue : ContDiffOn ℝ n faceTrue UTrue := by
        exact hbase.comp hconsTrue (fun v hv => hv)
      have hFaceFalse : ContDiffOn ℝ n faceFalse UFalse := by
        exact hbase.comp hconsFalse (fun v hv => hv)
      have htrueFTC := ih faceTrue UTrue hTrueOpen hTrueCube hFaceTrue
      have hfalseFTC := ih faceFalse UFalse hFalseOpen hFalseCube hFaceFalse
      have hcontTrueU :=
        cubeMixedDerivative_continuousOn_of_contDiffOn faceTrue UTrue hTrueOpen hFaceTrue
      have hcontFalseU :=
        cubeMixedDerivative_continuousOn_of_contDiffOn faceFalse UFalse hFalseOpen hFaceFalse
      have hcontTrue : ContinuousOn (cubeMixedDerivative faceTrue) (unitCoordinateCube n) :=
        hcontTrueU.mono hTrueCube
      have hcontFalse : ContinuousOn (cubeMixedDerivative faceFalse) (unitCoordinateCube n) :=
        hcontFalseU.mono hFalseCube
      have hFTC (t : Fin n → ℝ) (ht : t ∈ unitCoordinateCube n) :
          ∫ x in (0 : ℝ)..1, cubeMixedDerivative f (Fin.cons x t) =
            cubeMixedDerivative faceTrue t - cubeMixedDerivative faceFalse t := by
        let d : Fin n → (Fin (n + 1) → ℝ) := fun i => Pi.single i.succ 1
        let F : (Fin (n + 1) → ℝ) → ℝ := fun z =>
          iteratedFDeriv ℝ n f z d
        let line : ℝ → (Fin (n + 1) → ℝ) := fun y => Fin.cons y t
        let ψ : ℝ → ℝ := fun y => cubeMixedDerivative (fun u => f (Fin.cons y u)) t
        have hderiv (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
            HasDerivAt ψ (cubeMixedDerivative f (Fin.cons x t)) x := by
          have hline : HasDerivAt line (Pi.single (0 : Fin (n + 1)) 1) x := by
            have heq : line = fun y =>
                Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0 t +
                  y • Pi.single (0 : Fin (n + 1)) 1 := by
              funext y
              ext i
              refine Fin.cases ?_ (fun j => ?_) i <;> simp [line]
            rw [heq]
            convert (hasDerivAt_const x
                (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0 t)).add
              ((hasDerivAt_id x).smul_const (Pi.single (0 : Fin (n + 1)) 1)) using 1
            · funext y
              rfl
            · simp
          have hxCube : Fin.cons x t ∈ unitCoordinateCube (n + 1) :=
            unitCoordinateCube_cons x t hx ht
          have hxU : Fin.cons x t ∈ U := hcube hxCube
          have hfAt : ContDiffAt ℝ (n + 1) f (Fin.cons x t) :=
            hf.contDiffAt (hU.mem_nhds hxU)
          have hFAt : ContDiffAt ℝ 1 F (Fin.cons x t) := by
            simpa [F, d] using cubeTailMixed_contDiffAt_of_contDiffAt f
              (Fin.cons x t) hfAt
          have hFderiv : fderiv ℝ F (Fin.cons x t)
                (Pi.single (0 : Fin (n + 1)) 1) = cubeMixedDerivative f (Fin.cons x t) := by
            have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) (Fin.cons x t) :=
              (hfAt.iteratedFDeriv_right (i := n) (m := 1)
                (by norm_num [Nat.cast_add, add_comm])).differentiableAt
                (by norm_num)
            rw [cubeMixedDerivative]
            have htail : Fin.tail (fun i : Fin (n + 1) =>
                  (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ)) =
                (fun i : Fin n => (Pi.single i.succ (1 : ℝ) : Fin (n + 1) → ℝ)) := by
              funext i
              rfl
            simpa [F, d, cubeCoordinateDirections, line, htail] using
              (DifferentiableAt.iteratedFDeriv_succ_apply_left'
                (m := fun i => Pi.single i 1) hdiff).symm
          have hderivF : HasDerivAt (fun y => F (line y))
              (cubeMixedDerivative f (Fin.cons x t)) x := by
            have hcomp := (hFAt.differentiableAt (by norm_num)).hasFDerivAt.comp x
              hline.hasFDerivAt
            have hderiv := hcomp.hasDerivAt
            convert hderiv using 1
            · rfl
            · simpa [line] using hFderiv.symm
          have hlineU : IsOpen (line ⁻¹' U) := hU.preimage (by fun_prop)
          have hxlineU : x ∈ line ⁻¹' U := hxU
          have heventual : ψ =ᶠ[nhds x] fun y => F (line y) := by
            filter_upwards [hlineU.mem_nhds hxlineU] with y hy
            have hslice := cubeMixedDerivative_slice_of_contDiffOn f U hU
              (hf.of_le (by norm_cast; omega)) y t hy
            simpa [ψ, F, d, line] using hslice
          exact HasDerivAt.congr_of_eventuallyEq hderivF heventual
        have hcontMix := cubeMixedDerivative_continuousOn_of_contDiffOn f U hU hf
        have hcontLine : ContinuousOn (fun y => cubeMixedDerivative f (Fin.cons y t))
            (Icc (0 : ℝ) 1) := by
          apply hcontMix.comp (by fun_prop)
          intro y hy
          exact hcube (unitCoordinateCube_cons y t hy ht)
        have h01 : (0 : ℝ) ≤ 1 := by norm_num
        have hEqIcc : EqOn (deriv ψ) (fun y => cubeMixedDerivative f (Fin.cons y t))
            (uIcc (0 : ℝ) 1) := by
          intro y hy
          exact (hderiv y ((uIcc_of_le h01).symm ▸ hy)).deriv
        have hEqUic : EqOn (deriv ψ) (fun y => cubeMixedDerivative f (Fin.cons y t))
            (uIoc (0 : ℝ) 1) := by
          intro y hy
          exact hEqIcc (uIoc_subset_uIcc hy)
        have hintLine : IntervalIntegrable
            (fun y => cubeMixedDerivative f (Fin.cons y t)) MeasureTheory.volume 0 1 :=
          hcontLine.intervalIntegrable_of_Icc zero_le_one
        have hint : IntervalIntegrable (deriv ψ) MeasureTheory.volume 0 1 :=
          (intervalIntegrable_congr hEqUic).mpr hintLine
        calc
          ∫ y in (0 : ℝ)..1, cubeMixedDerivative f (Fin.cons y t) =
              ∫ y in (0 : ℝ)..1, deriv ψ y := by
                exact intervalIntegral.integral_congr hEqIcc.symm
          _ = ψ 1 - ψ 0 :=
            intervalIntegral.integral_deriv_eq_sub
              (fun y hy => (hderiv y ((uIcc_of_le h01).symm ▸ hy)).differentiableAt)
              hint
          _ = cubeMixedDerivative faceTrue t - cubeMixedDerivative faceFalse t := by
                simp [ψ, faceTrue, faceFalse]
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
            iteratedUnitIntegral n (cubeMixedDerivative faceTrue) -
              iteratedUnitIntegral n (cubeMixedDerivative faceFalse) := by
                simp only [alternatingVertexSum]
                rw [show (fun v : Fin n → Bool =>
                    f (fun i => if Fin.cons (α := fun _ : Fin (n + 1) => Bool) true v i
                      then 1 else 0)) =
                    (fun v => faceTrue (fun i => if v i then 1 else 0)) by
                    funext v
                    simp [faceTrue, hvertices true v]]
                rw [show (fun v : Fin n → Bool =>
                    f (fun i => if Fin.cons (α := fun _ : Fin (n + 1) => Bool) false v i
                      then 1 else 0)) =
                    (fun v => faceFalse (fun i => if v i then 1 else 0)) by
                    funext v
                    simp [faceFalse, hvertices false v]]
                rw [htrueFTC, hfalseFTC]
        _ = iteratedUnitIntegral n
            (fun t => cubeMixedDerivative faceTrue t - cubeMixedDerivative faceFalse t) := by
              symm
              exact iteratedUnitIntegral_sub_of_continuousOn_unitCoordinateCube
                _ _ hcontTrue hcontFalse
        _ = iteratedUnitIntegral n
            (fun t => ∫ x in (0 : ℝ)..1, cubeMixedDerivative f (Fin.cons x t)) := by
              apply iteratedUnitIntegral_congr_unitCoordinateCube
              intro t ht
              exact (hFTC t ht).symm
        _ = iteratedUnitIntegral (n + 1) (cubeMixedDerivative f) := rfl

/-- The local theorem retains the nonzero all-order coordinate-product witness. -/
theorem cubeFTC_coordinateProduct_witness_local (r : ℕ) :
    alternatingVertexSum r (fun v => ∏ i : Fin r, if v i then 1 else 0) = 1 ∧
      (∀ t : Fin r → ℝ,
        cubeMixedDerivative (fun u => ∏ i : Fin r, u i) t = 1) ∧
      iteratedUnitIntegral r (cubeMixedDerivative (fun u => ∏ i : Fin r, u i)) = 1 :=
  cubeFTC_coordinateProduct_witness r

end RBM.Gauss
