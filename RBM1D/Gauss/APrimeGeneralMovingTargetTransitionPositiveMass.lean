/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingTargetTransitionExists
import RBM1D.Gauss.FiniteSupportCore

/-!
# T1065: positive Gaussian mass of the exact target-mesh transition

The scalar-ray witness from T1051 lies in the support of the finite Gaussian
coordinates that determine its prefix. Strictness and continuity then give a
nonempty open cylinder in the literal transition set.
-/

set_option autoImplicit false

namespace RBM.Gauss.APrimeGeneralMovingTargetTransitionPositiveMass

open Filter MeasureTheory Set Real Topology CutHypTheta
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private abbrev s : ℕ → ℝ := fun _ => 0
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60

/-- The actual prefix at size `N` depends only on the finite coordinates read
by the size-`N` Gaussian matrix. -/
private theorem prefixSample_congr_of_agree (E D : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) (ω ω' : Gauss.Ω d)
    (hagree : ∀ e ∈ (Gauss.usedCoord d N).image (Gauss.crd d N), ω e = ω' e) :
    APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω =
      APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω' := by
  unfold APrimeSmoothWeightActual.prefixSample
  apply congrArg
    (APrimeSmoothWeightActual.prefixMatrix d E D s mesh N k m)
  rw [Gauss.Xmat_eq_sum, Gauss.Xmat_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hagree (Gauss.crd d N p) (Finset.mem_image_of_mem _ hp)]

private theorem prefixSample_finDep (E D : ℝ) (s mesh : ℕ → ℝ)
    (N k m : ℕ) :
    Gauss.FinDep d (fun ω =>
      APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω) := by
  exact ⟨(Gauss.usedCoord d N).image (Gauss.crd d N), fun ω ω' h =>
    prefixSample_congr_of_agree E D s mesh N k m ω ω' h⟩

private theorem scalarSample_zero_of_gvar_zero (x : ℝ) (c : Gauss.Coord d)
    (hvar : (Gauss.gvar d c : ℝ) = 0) :
    APrimeSmoothTransition.scalarSample d x c = 0 := by
  rcases c with ⟨N, i, j, b⟩
  by_cases hij : i = j
  · subst j
    have hpos : 0 < (Gauss.gvar d (Gauss.crd d N (i, i, b)) : ℝ) := by
      rw [Gauss.gvar_crd_diag_exact]
      have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
      positivity
    have hzero : (Gauss.gvar d (Gauss.crd d N (i, i, b)) : ℝ) = 0 := by
      simpa [Gauss.crd] using hvar
    exact (ne_of_gt hpos hzero).elim
  · simp [APrimeSmoothTransition.scalarSample, hij]

/-- Any support-compatible sample in the exact strict transition has positive
Gaussian measure. The openness argument uses the literal prefix observable;
the finite-dependence lemma above identifies its complete size-`N` coordinate
input. -/
private theorem transition_pos_of_compatible_sample
    (E D δ : ℝ) (s mesh : ℕ → ℝ) (N k m : ℕ) (ω₀ : Gauss.Ω d)
    (hE : |E| < 2) (hs : s N < 1) (hN : 0 < N) (hm : 1 ≤ m)
    (hu : ∀ j < k, cutNetPt s mesh N j < 1)
    (hω₀ : ω₀ ∈ APrimeCrossJointSplit.transition d E D δ s mesh N k m)
    (hcompat : ∀ c, (Gauss.gvar d c : ℝ) = 0 → ω₀ c = 0) :
    0 < Gauss.P d (APrimeCrossJointSplit.transition d E D δ s mesh N k m) := by
  classical
  let f : Gauss.Ω d → ℝ := fun ω =>
    APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω /
      APrimeSmoothWeightActual.threshold δ N
  have hf : Continuous f := by
    dsimp [f]
    have hprefix : Continuous (fun ω =>
        APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω) := by
      have hC := APrimeSmoothWeightActual.contDiff_prefixMatrix d
        (E := E) (D := D) (s := s) (mesh := mesh) (N := N) (k := k) (m := m)
        hE hs hN hm hu
      exact hC.continuous.comp (Gauss.continuous_Xmat d N)
    exact hprefix.div_const _
  have hopen : IsOpen (APrimeCrossJointSplit.transition d E D δ s mesh N k m) := by
    change IsOpen {ω | 1 < f ω ∧ f ω < 2}
    exact (isOpen_lt continuous_const hf).inter (isOpen_lt hf continuous_const)
  have hOn : APrimeCrossJointSplit.transition d E D δ s mesh N k m ∈ 𝓝 ω₀ :=
    hopen.mem_nhds hω₀
  rw [nhds_pi, Filter.mem_pi'] at hOn
  obtain ⟨J₀, V, hV, hJ⟩ := hOn
  let V' : Gauss.Coord d → Set ℝ := fun c => interior (V c)
  have hV' : ∀ c, IsOpen (V' c) := fun c => isOpen_interior
  have hcenter : ∀ c ∈ J₀, ω₀ c ∈ V' c := by
    intro c hc
    exact mem_interior_iff_mem_nhds.mpr (hV c)
  let K : Finset (Gauss.Coord d) :=
    (Gauss.usedCoord d N).image (Gauss.crd d N)
  let V₀ : Gauss.Coord d → Set ℝ := fun c =>
    if c ∈ J₀ then V' c else Set.univ
  let I := Gauss.effectiveCoords d K
  let U : Set (∀ c : I, ℝ) := {x | ∀ c, x c ∈ V₀ c.1}
  have hUcoord : ∀ c : I, IsOpen {x : ∀ c : I, ℝ | x c ∈ V₀ c.1} := by
    intro c
    change IsOpen ((fun x : ∀ c : I, ℝ => x c) ⁻¹' V₀ c.1)
    by_cases hc : c.1 ∈ J₀
    · simp only [V₀, if_pos hc]
      exact (hV' c.1).preimage (continuous_apply c)
    · simp only [V₀, if_neg hc]
      exact isOpen_univ.preimage (continuous_apply c)
  have hU : IsOpen U := by
    rw [show U = ⋂ c : I, {x : ∀ c : I, ℝ | x c ∈ V₀ c.1} by
      ext x
      simp [U]]
    exact isOpen_iInter_of_finite hUcoord
  have hUne : U.Nonempty := by
    refine ⟨fun c => ω₀ c.1, ?_⟩
    intro c
    by_cases hc : c.1 ∈ J₀
    · simpa [V₀, hc] using hcenter c.1 hc
    · simp [V₀, hc]
  have hpos := Gauss.support_cylinder_pos d K hU hUne
  have hsub : Gauss.supportCylinder d K U ⊆
      APrimeCrossJointSplit.transition d E D δ s mesh N k m := by
    intro ω hω
    have hω' : I.restrict ω ∈ U ∧ ω ∈ Gauss.zeroFix d K := by
      change I.restrict ω ∈ U ∧ ω ∈ Gauss.zeroFix d K at hω
      exact hω
    have hVω : ∀ c ∈ K, ω c ∈ V₀ c := by
      intro c hc
      by_cases hvar : (Gauss.gvar d c : ℝ) ≠ 0
      · have hvar' : Gauss.gvar d c ≠ 0 := by
          intro hz
          apply hvar
          exact_mod_cast hz
        have hcI : c ∈ I := Finset.mem_filter.mpr ⟨hc, hvar'⟩
        have hUω : ∀ q : I, (I.restrict ω) q ∈ V₀ q.1 := by
          simpa [U] using hω'.1
        simpa using hUω ⟨c, hcI⟩
      · have hz : (Gauss.gvar d c : ℝ) = 0 := by
          exact Classical.byContradiction hvar
        have hωzero : ω c = 0 := hω'.2 c hc (by exact_mod_cast hz)
        have hω₀zero : ω₀ c = 0 := hcompat c hz
        by_cases hc₀ : c ∈ J₀
        · have hzeroV : (0 : ℝ) ∈ V' c := by
            simpa [hω₀zero] using hcenter c hc₀
          simpa [V₀, hc₀, hωzero] using hzeroV
        · simp [V₀, hc₀]
    let ω' : Gauss.Ω d := fun c => if hc : c ∈ K then ω c else ω₀ c
    have hω'J : ∀ c ∈ J₀, ω' c ∈ V' c := by
      intro c hc
      by_cases hcK : c ∈ K
      · have hval : ω c ∈ V' c := by
          simpa [V₀, hc] using hVω c hcK
        simpa [ω', hcK] using hval
      · simpa [ω', hcK] using hcenter c hc
    have hω'Joriginal : ∀ c ∈ J₀, ω' c ∈ V c := by
      intro c hc
      exact interior_subset (hω'J c hc)
    have htransition' : ω' ∈ APrimeCrossJointSplit.transition d E D δ s mesh N k m :=
      hJ hω'Joriginal
    have hprefixEq :
        APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω =
          APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω' := by
      apply prefixSample_congr_of_agree E D s mesh N k m ω ω'
      intro c hc
      have hcK : c ∈ K := by simpa [K] using hc
      change ω c = (if h : c ∈ K then ω c else ω₀ c)
      rw [dif_pos hcK]
    change (1 < APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω /
        APrimeSmoothWeightActual.threshold δ N ∧
      APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω /
        APrimeSmoothWeightActual.threshold δ N < 2)
    change (1 < APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω' /
        APrimeSmoothWeightActual.threshold δ N ∧
      APrimeSmoothWeightActual.prefixSample d E D s mesh N k m ω' /
        APrimeSmoothWeightActual.threshold δ N < 2) at htransition'
    rw [hprefixEq]
    exact htransition'
  exact lt_of_lt_of_le hpos (measure_mono hsub)

/-- Eventually, the literal T1051 first-cell transition has positive mass under
the actual product-Gaussian law. The parameters, target mesh, canonical order,
T995 `deltaWeight`, and active index `k=2` are unchanged. -/
theorem eventually_exampleGrow_target_transition_pos {τ c δ : ℝ}
    (hτ : 0 < τ) (hc : 0 < c) (hδ : 0 < δ)
    (hδsmall : δ ≤ min 1 (c / 100)) :
    ∀ᶠ N : ℕ in atTop,
      0 < Gauss.P d
        (APrimeCrossJointSplit.transition d 0 60
          (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
          s mesh N 2
          (APrimeSmoothWeightActual.canonicalM d s
            (Gauss.firstCellT τ) mesh N)) := by
  filter_upwards [
    APrimeGeneralMovingTargetTransitionExists.eventually_exampleGrow_target_transition
      hτ hc hδ hδsmall,
    eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  obtain ⟨hs, ht, hk, x, hx, htransition, hratio₁, hratio₂⟩ := hN
  change 2 ≤ cutNetTop s (Gauss.firstCellT τ) mesh N at hk
  have hN' : 0 < N := by omega
  have hm : 1 ≤ APrimeSmoothWeightActual.canonicalM d s
      (Gauss.firstCellT τ) mesh N :=
    APrimeSmoothWeightActual.canonicalM_pos d s (Gauss.firstCellT τ) mesh N
  have hstored : ∀ j < 2, cutNetPt s mesh N j < 1 := by
    intro j hj
    have hjk : j ≤ cutNetTop s (Gauss.firstCellT τ) mesh N := by omega
    have hmem := MomentDuhamelCut.netFinset_subset_Icc
      (show s N ≤ Gauss.firstCellT τ N by rw [ht]; norm_num [s])
      (APrimeGeneralMovingMesh.targetMesh_pos 60 N) _
      (cutNetPt_mem_netFinset hjk)
    exact hmem.2.trans_lt (by rw [ht]; norm_num)
  have hωcompat : ∀ q, (Gauss.gvar d q : ℝ) = 0 →
      APrimeSmoothTransition.scalarSample d x q = 0 :=
    fun q hq => scalarSample_zero_of_gvar_zero x q hq
  exact transition_pos_of_compatible_sample 0 60
    (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s mesh N 2
    (APrimeSmoothWeightActual.canonicalM d s (Gauss.firstCellT τ) mesh N)
    (APrimeSmoothTransition.scalarSample d x)
    (by norm_num) (by norm_num [s]) hN' hm hstored htransition hωcompat

theorem explicit_parameter_witness :
    ∃ τ c δ : ℝ, 0 < τ ∧ 0 < c ∧ 0 < δ ∧ δ ≤ min 1 (c / 100) :=
  APrimeGeneralMovingTargetTransitionExists.explicit_parameter_witness

#print axioms prefixSample_finDep
#print axioms scalarSample_zero_of_gvar_zero
#print axioms transition_pos_of_compatible_sample
#print axioms eventually_exampleGrow_target_transition_pos
#print axioms explicit_parameter_witness

end RBM.Gauss.APrimeGeneralMovingTargetTransitionPositiveMass
