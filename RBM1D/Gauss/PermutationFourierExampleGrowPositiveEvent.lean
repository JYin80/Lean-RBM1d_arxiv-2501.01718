/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowStrictMargin
import RBM1D.Gauss.FiniteSupportCore
import RBM1D.Gauss.Hierarchy
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore
import Mathlib.Topology.Compactness.Compact

/-! Positive actual Gaussian mass of the literal closed-half-time flow event.

A strict full-flow margin at one zero-variance-compatible sample gives a finite
coordinate open cylinder inside `goodSetFlow`. Intersecting the active-coordinate
part of that cylinder with the zero-variance coordinates fixed at zero gives a
set of positive mass under the actual product Gaussian law.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace RBM.Gauss

/-- Joint continuity of the full resolvent along the matrix flow and the moving
spectral parameter, at every point below time one. -/
theorem continuousAt_green_joint (d : Dims) (N : ℕ) (E : ℝ)
    (p : Ω d × ℝ) (hE : |E| < 2) (hp : p.2 < 1) :
    ContinuousAt (fun q : Ω d × ℝ => green (Hflow d N q.2 q.1) (zt E q.2)) p := by
  have hmat : Continuous (fun q : Ω d × ℝ => Hflow d N q.2 q.1) := by
    have h := ((Real.continuous_sqrt.comp continuous_snd).smul
      ((continuous_Xmat d N).comp continuous_fst))
    convert h using 1
    funext q
    exact (Hflow_eq_realSmul d N q.2 q.1).symm
  have hz : Continuous (fun q : Ω d × ℝ => zt E q.2) := by
    unfold zt
    fun_prop
  have him : (zt E p.2).im ≠ 0 := by
    rw [zt_im]
    exact ne_of_gt (mul_pos (by linarith) (mE_im_pos hE))
  have hU : IsUnit (Hflow d N p.2 p.1 - zt E p.2 •
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero (Hflow_isHermitian d N p.2 p.1) him
  have hspec : ((hU.unit : (Matrix (d.Idx N) (d.Idx N) ℂ)ˣ) :
      Matrix (d.Idx N) (d.Idx N) ℂ) =
      Hflow d N p.2 p.1 - zt E p.2 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) :=
    IsUnit.unit_spec _
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
      (Hflow d N p.2 p.1 - zt E p.2 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) := by
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun q : Ω d × ℝ =>
      Hflow d N q.2 q.1 - zt E q.2 • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) p :=
    hmat.continuousAt.sub (hz.continuousAt.smul continuousAt_const)
  have h3 := ContinuousAt.comp (g := Ring.inverse
      (M₀ := Matrix (d.Idx N) (d.Idx N) ℂ))
    (f := fun q : Ω d × ℝ => Hflow d N q.2 q.1 - zt E q.2 •
      (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) h1 h2
  simpa [green, Function.comp_def, Matrix.nonsing_inv_eq_ringInverse] using h3

private theorem topology_cylinder_local
    {ι α : Type*} (ω₀ : ι → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (Q : Finset α) (F : α → ((ι → ℝ) × ℝ) → ℝ) (δ : ℝ)
    (hcont : ∀ q ∈ Q, ∀ p : (ι → ℝ) × ℝ, p.2 < 1 → ContinuousAt (F q) p)
    (hKlt : ∀ u ∈ K, u < 1)
    (hstrict : ∀ q ∈ Q, ∀ u ∈ K, F q (ω₀,u) < δ) :
    ∃ J : Finset ι, ∃ V : ι → Set ℝ,
      (∀ i, IsOpen (V i)) ∧ (∀ i ∈ J, ω₀ i ∈ V i) ∧
      (∀ ω : ι → ℝ, (∀ i ∈ J, ω i ∈ V i) →
        ∀ q ∈ Q, ∀ u ∈ K, F q (ω,u) < δ) := by
  let U : Set ((ι → ℝ) × ℝ) :=
    {p | p.2 < 1 ∧ ∀ q ∈ Q, F q p < δ}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have htime : {p : (ι → ℝ) × ℝ | p.2 < 1} ∈ 𝓝 p :=
      (isOpen_Iio.preimage continuous_snd).mem_nhds hp.1
    have hq : ∀ q ∈ Q,
        {p : (ι → ℝ) × ℝ | F q p < δ} ∈ 𝓝 p := by
      intro q hq
      exact (hcont q hq p hp.1).preimage_mem_nhds
        (isOpen_Iio.mem_nhds (hp.2 q hq))
    have hraw : ({p : (ι → ℝ) × ℝ | p.2 < 1} ∩
        ⋂ q ∈ Q, {p : (ι → ℝ) × ℝ | F q p < δ}) ∈ 𝓝 p :=
      Filter.inter_mem htime ((Filter.biInter_mem Q.finite_toSet).2 hq)
    have heq : U = ({p : (ι → ℝ) × ℝ | p.2 < 1} ∩
        ⋂ q ∈ Q, {p : (ι → ℝ) × ℝ | F q p < δ}) := by
      ext x
      simp [U]
    rw [heq]
    exact hraw
  have hsub : ({ω₀} ×ˢ K) ⊆ U := by
    rintro ⟨ω,u⟩ ⟨hω,hu⟩
    change ω = ω₀ at hω
    subst ω
    exact ⟨hKlt u hu, fun q hq => hstrict q hq u hu⟩
  obtain ⟨O,T,hO,hT,hωO,hKT,hOT⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := ω₀)) hK hU hsub
  have hOn : O ∈ 𝓝 ω₀ := hO.mem_nhds (hωO rfl)
  rw [nhds_pi, Filter.mem_pi'] at hOn
  obtain ⟨J,V,hV,hJO⟩ := hOn
  refine ⟨J, fun i => interior (V i), fun i => isOpen_interior, ?_, ?_⟩
  · intro i hi
    exact mem_interior_iff_mem_nhds.mpr (hV i)
  · intro ω hω q hq u hu
    have hp : (ω,u) ∈ U :=
      hOT ⟨hJO (fun i hi => interior_subset (hω i hi)), hKT hu⟩
    exact hp.2 q hq

/-- A strict all-time entry margin supplies one finite-coordinate cylinder
inside the literal flow event. -/
theorem strict_goodSetFlow_cylinder (d : Dims) (N : ℕ) (E : ℝ)
    (ω₀ : Ω d) (δ : ℝ) (hE : |E| < 2)
    (hstrict : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      ∀ i j : d.Idx N,
        ‖green (Hflow d N u ω₀) (zt E u) i j -
          (if i = j then mE E else 0)‖ < δ) :
    ∃ J : Finset (Coord d), ∃ V : Coord d → Set ℝ,
      (∀ c, IsOpen (V c)) ∧ (∀ c ∈ J, ω₀ c ∈ V c) ∧
      (∀ ω : Ω d, (∀ c ∈ J, ω c ∈ V c) →
        ω ∈ goodSetFlow d E (fun _ => 0) (fun _ => 1/2) (fun _ => δ) N) := by
  classical
  let Q : Finset (d.Idx N × d.Idx N) := Finset.univ
  let F : (d.Idx N × d.Idx N) → (Ω d × ℝ) → ℝ :=
    fun ij p => ‖green (Hflow d N p.2 p.1) (zt E p.2) ij.1 ij.2 -
      (if ij.1 = ij.2 then mE E else 0)‖
  have hcont : ∀ ij ∈ Q, ∀ p : Ω d × ℝ, p.2 < 1 → ContinuousAt (F ij) p := by
    intro ij _ p hp
    have hg := continuousAt_green_joint d N E p hE hp
    have hrow : ContinuousAt (fun q : Ω d × ℝ =>
        (green (Hflow d N q.2 q.1) (zt E q.2)) ij.1) p := by
      exact (continuous_apply ij.1).continuousAt.comp hg
    have he : ContinuousAt (fun q : Ω d × ℝ =>
        ((green (Hflow d N q.2 q.1) (zt E q.2)) ij.1) ij.2) p := by
      exact (continuous_apply ij.2).continuousAt.comp hrow
    exact (he.sub continuousAt_const).norm
  have hKlt : ∀ u ∈ Set.Icc (0 : ℝ) (1/2 : ℝ), u < 1 := by
    intro u hu
    linarith [hu.2]
  obtain ⟨J,V,hV,hcenter,hbound⟩ :=
    topology_cylinder_local ω₀ (Set.Icc (0 : ℝ) (1/2 : ℝ)) isCompact_Icc
      Q F δ hcont hKlt (by
        intro ij _ u hu
        exact hstrict u hu ij.1 ij.2)
  refine ⟨J,V,hV,hcenter,?_⟩
  intro ω hω u hu i j
  exact (hbound ω hω (i,j) (Finset.mem_univ _) u hu).le

/-- Turning the finite cylinder into an open set on exactly the active Gaussian
coordinates, while fixing every zero-variance coordinate at its support value. -/
private theorem strict_cylinder_support_pos (d : Dims) (J : Finset (Coord d))
    (V : Coord d → Set ℝ) (ω₀ : Ω d)
    (hV : ∀ c, IsOpen (V c))
    (hcenter : ∀ c ∈ J, ω₀ c ∈ V c)
    (hcompat : ∀ c, (gvar d c : ℝ) = 0 → ω₀ c = 0)
    {E : ℝ} {δ : ℕ → ℝ} {N : ℕ}
    (hinside : ∀ ω : Ω d, (∀ c ∈ J, ω c ∈ V c) →
      ω ∈ goodSetFlow d E (fun _ => 0) (fun _ => 1/2) δ N) :
    0 < P d (goodSetFlow d E (fun _ => 0) (fun _ => 1/2) δ N) := by
  classical
  let I := effectiveCoords d J
  let U : Set (∀ c : I, ℝ) := {x | ∀ c, x c ∈ V c.1}
  have hU : IsOpen U := by
    rw [show U = ⋂ c : I, {x : ∀ c : I, ℝ | x c ∈ V c.1} by
      ext x
      simp [U]]
    exact isOpen_iInter_of_finite fun c =>
      (hV c.1).preimage (continuous_apply c)
  have hUne : U.Nonempty := by
    refine ⟨fun c => ω₀ c.1, ?_⟩
    exact fun c => hcenter c.1 (Finset.mem_filter.1 c.property).1
  have hpos := support_cylinder_pos d J hU hUne
  have hsub : supportCylinder d J U ⊆
      goodSetFlow d E (fun _ => 0) (fun _ => 1/2) δ N := by
    intro ω hω
    apply hinside
    intro c hc
    by_cases hvar : gvar d c ≠ 0
    · exact hω.1 ⟨c, Finset.mem_filter.mpr ⟨hc, hvar⟩⟩
    · have hzero : gvar d c = 0 := by
        apply Classical.byContradiction
        exact hvar
      have hcenterZero : ω₀ c = 0 := by
        apply hcompat
        exact_mod_cast hzero
      have hVzero : (0 : ℝ) ∈ V c := by
        simpa [hcenterZero] using hcenter c hc
      have hωzero : ω c = 0 := hω.2 c hc hzero
      simpa [hωzero] using hVzero
  exact lt_of_lt_of_le hpos (measure_mono hsub)

/-- Eventually the actual growing-model Gaussian law assigns positive mass to
the literal all-time good event. The center is simultaneously nonzero and
compatible with all zero-variance coordinates. -/
theorem eventually_exampleGrow_goodSetFlow_pos_nondegenerate :
    ∀ᶠ N : ℕ in atTop,
      0 < P Dims.exampleGrow
        (goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1/2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1/2)) N) ∧
      ∃ ω : Ω Dims.exampleGrow,
        ω ∈ goodSetFlow Dims.exampleGrow 0 (fun _ => 0) (fun _ => 1/2)
          (flowDelta Dims.exampleGrow 0 (fun _ => 1/2)) N ∧
        Xmat Dims.exampleGrow N ω ≠ 0 ∧
        (∀ c : Coord Dims.exampleGrow,
          (gvar Dims.exampleGrow c : ℝ) = 0 → ω c = 0) := by
  filter_upwards [eventually_quantile_block_strict_resolvent_nondegenerate] with N hN
  obtain ⟨π, ω₀, hW, hωeq, hGood, hstrict, hnonzero, hcompat⟩ := hN
  let δ := flowDelta Dims.exampleGrow 0 (fun _ => 1/2) N
  obtain ⟨J,V,hV,hcenter,hinside⟩ := strict_goodSetFlow_cylinder
    Dims.exampleGrow N 0 ω₀ δ (by norm_num) (by
      intro u hu i j
      change ‖green (Hflow Dims.exampleGrow N u ω₀) (zt 0 u) i j -
          (if i = j then mE 0 else 0)‖ < flowDelta Dims.exampleGrow 0
            (fun _ => 1/2) N
      simpa [mE_zero] using hstrict u hu i j)
  refine ⟨strict_cylinder_support_pos Dims.exampleGrow J V ω₀ hV hcenter
      hcompat hinside, ⟨ω₀, hGood, hnonzero, hcompat⟩⟩

#print axioms continuousAt_green_joint
#print axioms strict_goodSetFlow_cylinder
#print axioms eventually_exampleGrow_goodSetFlow_pos_nondegenerate

end RBM.Gauss
