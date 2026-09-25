/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowJointPositive
import RBM1D.Gauss.PermutationFourierExampleGrowPositiveEvent
import RBM1D.Gauss.PermutationFourierExampleGrowCenteredEvent
import RBM1D.Gauss.PermutationFourierExampleGrowMeshNorm
import RBM1D.Gauss.FiniteSupportCore
import Mathlib.Topology.Compactness.Compact

/-! A strict common carrier lies in the literal flow, centered-trace, and
operator-norm mesh events on a finite-coordinate Gaussian support cylinder.
The eventual result is a positive actual Gaussian mass statement for this
specific three-event intersection. -/

set_option autoImplicit false
open MeasureTheory Set Filter Topology Matrix Real
open scoped Matrix.Norms.L2Operator

namespace RBM.Gauss

private noncomputable abbrev d981 : Dims := Dims.exampleGrow
private noncomputable abbrev s981 : ℕ → ℝ := fun _ => 0
private noncomputable abbrev t981 : ℕ → ℝ := fun _ => 1 / 2

private theorem topology_cylinder_local_981
    {ι α : Type*} (ω₀ : ι → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (Q : Finset α) (F : α → ((ι → ℝ) × ℝ) → ℝ) (δ : ℝ)
    (hcont : ∀ q ∈ Q, ∀ p : (ι → ℝ) × ℝ, p.2 < 1 → ContinuousAt (F q) p)
    (hKlt : ∀ u ∈ K, u < 1)
    (hstrict : ∀ q ∈ Q, ∀ u ∈ K, F q (ω₀,u) < δ) :
    ∃ J : Finset ι, ∃ V : ι → Set ℝ,
      (∀ i, IsOpen (V i)) ∧ (∀ i ∈ J, ω₀ i ∈ V i) ∧
      (∀ ω : ι → ℝ, (∀ i ∈ J, ω i ∈ V i) →
        ∀ q ∈ Q, ∀ u ∈ K, F q (ω,u) < δ) := by
  let U : Set ((ι → ℝ) × ℝ) := {p | p.2 < 1 ∧ ∀ q ∈ Q, F q p < δ}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have htime : {p : (ι → ℝ) × ℝ | p.2 < 1} ∈ 𝓝 p :=
      (isOpen_Iio.preimage continuous_snd).mem_nhds hp.1
    have hq : ∀ q ∈ Q, {p : (ι → ℝ) × ℝ | F q p < δ} ∈ 𝓝 p := by
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

private theorem continuousAt_centeredTrace_true_joint_981 (N : ℕ)
    (p : Ω d981 × ℝ) (hp : p.2 < 1) (b : ZMod (d981.L N)) :
    ContinuousAt (fun q : Ω d981 × ℝ =>
      APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N q.2 q.1 true b) p := by
  have hg := continuousAt_green_joint d981 N 0 p (by norm_num) hp
  let T : Matrix (d981.Idx N) (d981.Idx N) ℂ → ℂ := fun A =>
    Matrix.trace ((A - mSigma 0 true • (1 : Matrix (d981.Idx N) (d981.Idx N) ℂ)) *
      Eblk (d981.L N) (d981.W N) b)
  have hT : Continuous T := by
    dsimp [T]
    fun_prop
  have h := hT.continuousAt.comp hg
  convert h using 1
  ext q
  rfl

private theorem strict_centered_cylinder_981 (N : ℕ) (zeta δ : ℝ)
    (hthreshold : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      δ ≤ (N : ℝ) ^ zeta *
        (2 * APrimeGeneralMovingControlExtension.qExt 0 s981 t981 N u))
    (ω₀ : Ω d981)
    (hstrict : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ b : ZMod (d981.L N),
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω₀ true b‖ < δ) :
    ∃ J : Finset (Coord d981), ∃ V : Coord d981 → Set ℝ,
      (∀ c, IsOpen (V c)) ∧ (∀ c ∈ J, ω₀ c ∈ V c) ∧
      (∀ ω : Ω d981, (∀ c ∈ J, ω c ∈ V c) →
        ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N) := by
  classical
  let Q : Finset (ZMod (d981.L N)) := Finset.univ
  let F : ZMod (d981.L N) → (Ω d981 × ℝ) → ℝ := fun b p =>
    ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N p.2 p.1 true b‖
  have hcont : ∀ b ∈ Q, ∀ p : Ω d981 × ℝ, p.2 < 1 → ContinuousAt (F b) p := by
    intro b _ p hp
    exact (continuousAt_centeredTrace_true_joint_981 N p hp b).norm
  have hKlt : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), u < 1 := by
    intro u hu
    linarith [hu.2]
  obtain ⟨J,V,hV,hcenter,hbound⟩ :=
    topology_cylinder_local_981 ω₀ (Set.Icc (0 : ℝ) (1 / 2)) isCompact_Icc
      Q F δ hcont hKlt (by
        intro b _ u hu
        exact hstrict u hu b)
  refine ⟨J,V,hV,hcenter,?_⟩
  intro ω hω σ p
  obtain ⟨u,hu⟩ := p.1
  have hu' : u ∈ Set.Icc (0 : ℝ) (1 / 2) := by simpa [s981, t981] using hu
  have htrue := hbound ω hω p.2 (Finset.mem_univ _) u hu'
  have hle := hthreshold u hu'
  have htrue' : ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
      0 N u ω true p.2‖ ≤
      (N : ℝ) ^ zeta * (2 * APrimeGeneralMovingControlExtension.qExt 0 s981 t981 N u) :=
    (htrue.le).trans hle
  cases σ with
  | true => exact htrue'
  | false =>
      rw [APrimeGeneralMovingTwoChargeModulus.centeredTrace_false_norm_eq_true]
      exact htrue'

private theorem norm_cylinder_981 (N : ℕ) (ω₀ : Ω d981) (δ : ℝ)
    (hstrict : ‖Xmat d981 N ω₀‖ < δ) :
    ∃ J : Finset (Coord d981), ∃ V : Coord d981 → Set ℝ,
      (∀ c, IsOpen (V c)) ∧ (∀ c ∈ J, ω₀ c ∈ V c) ∧
      (∀ ω : Ω d981, (∀ c ∈ J, ω c ∈ V c) → ‖Xmat d981 N ω‖ < δ) := by
  have hcont : Continuous (fun ω : Ω d981 => ‖Xmat d981 N ω‖) :=
    continuous_norm.comp (continuous_Xmat d981 N)
  have hneigh : {ω : Ω d981 | ‖Xmat d981 N ω‖ < δ} ∈ 𝓝 ω₀ :=
    (isOpen_lt hcont continuous_const).mem_nhds hstrict
  rw [nhds_pi, Filter.mem_pi'] at hneigh
  obtain ⟨J,V,hV,hJ⟩ := hneigh
  refine ⟨J, fun c => interior (V c), fun c => isOpen_interior, ?_, ?_⟩
  · intro c hc
    exact mem_interior_iff_mem_nhds.mpr (hV c)
  · intro ω hω
    have : ω ∈ {ω : Ω d981 | ‖Xmat d981 N ω‖ < δ} :=
      hJ (fun c hc => interior_subset (hω c hc))
    exact this

private theorem support_cylinder_pos_triple_981 (J : Finset (Coord d981))
    (V : Coord d981 → Set ℝ) (ω₀ : Ω d981)
    (hV : ∀ c, IsOpen (V c)) (hcenter : ∀ c ∈ J, ω₀ c ∈ V c)
    (hcompat : ∀ c, (gvar d981 c : ℝ) = 0 → ω₀ c = 0)
    {R : Set (Ω d981)}
    (hinside : ∀ ω, (∀ c ∈ J, ω c ∈ V c) → ω ∈ R) : 0 < P d981 R := by
  classical
  let I := effectiveCoords d981 J
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
  have hpos := support_cylinder_pos d981 J hU hUne
  have hsub : supportCylinder d981 J U ⊆ R := by
    intro ω hω
    apply hinside
    intro c hc
    by_cases hvar : gvar d981 c ≠ 0
    · exact hω.1 ⟨c, Finset.mem_filter.mpr ⟨hc, hvar⟩⟩
    · have hzero : gvar d981 c = 0 := by
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

/-- Conditional fixed-N three-event support statement. -/
theorem exampleGrow_common_goodSetFlow_centeredEvent_goodMesh_pos_of_strict
    (N : ℕ) (zeta δ : ℝ) (ω₀ : Ω d981)
    (hthreshold : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      δ ≤ (N : ℝ) ^ zeta *
        (2 * APrimeGeneralMovingControlExtension.qExt 0 s981 t981 N u))
    (hflow : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i j : d981.Idx N,
      ‖green (Hflow d981 N u ω₀) (zt 0 u) i j -
        (if i = j then mE 0 else 0)‖ < flowDelta d981 0 t981 N)
    (hctr : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ b : ZMod (d981.L N),
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω₀ true b‖ < δ)
    (hnorm : ‖Xmat d981 N ω₀‖ < (N : ℝ))
    (hcompat : ∀ c : Coord d981, (gvar d981 c : ℝ) = 0 → ω₀ c = 0) :
    0 < P d981
      (goodSetFlow d981 0 s981 t981 (fun _ => flowDelta d981 0 t981 N) N ∩
       APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N ∩
       APrimeGeneralMovingGoodMesh.good N) := by
  obtain ⟨Jf,Vf,hVf,hcf,hif⟩ := strict_goodSetFlow_cylinder
    d981 N 0 ω₀ (flowDelta d981 0 t981 N) (by norm_num) (by
      intro u hu i j
      simpa [mE_zero] using hflow u hu i j)
  obtain ⟨Jc,Vc,hVc,hcc,hic⟩ := strict_centered_cylinder_981
    N zeta δ hthreshold ω₀ hctr
  obtain ⟨Jm,Vm,hVm,hcm,him⟩ := norm_cylinder_981 N ω₀ (N : ℝ) hnorm
  let J : Finset (Coord d981) := (Jf ∪ Jc) ∪ Jm
  let V : Coord d981 → Set ℝ := fun c =>
    ((if c ∈ Jf then Vf c else Set.univ) ∩
      (if c ∈ Jc then Vc c else Set.univ)) ∩
      (if c ∈ Jm then Vm c else Set.univ)
  have hV : ∀ c, IsOpen (V c) := by
    intro c
    by_cases h1 : c ∈ Jf
    · by_cases h2 : c ∈ Jc
      · by_cases h3 : c ∈ Jm
        · simpa [V, h1, h2, h3] using (((hVf c).inter (hVc c)).inter (hVm c))
        · simpa [V, h1, h2, h3] using (hVf c).inter (hVc c)
      · by_cases h3 : c ∈ Jm
        · simpa [V, h1, h2, h3] using (hVf c).inter (hVm c)
        · simpa [V, h1, h2, h3] using hVf c
    · by_cases h2 : c ∈ Jc
      · by_cases h3 : c ∈ Jm
        · simpa [V, h1, h2, h3] using (hVc c).inter (hVm c)
        · simpa [V, h1, h2, h3] using hVc c
      · by_cases h3 : c ∈ Jm
        · simpa [V, h1, h2, h3] using hVm c
        · simp [V, h1, h2, h3]
  have hcenter : ∀ c ∈ J, ω₀ c ∈ V c := by
    intro c hc
    have hf : c ∈ Jf ∨ c ∈ Jc ∨ c ∈ Jm := by
      simpa [J, Finset.mem_union] using hc
    have h1 : ω₀ c ∈ (if c ∈ Jf then Vf c else Set.univ) := by
      by_cases h : c ∈ Jf
      · simpa [h] using hcf c h
      · simp [h]
    have h2 : ω₀ c ∈ (if c ∈ Jc then Vc c else Set.univ) := by
      by_cases h : c ∈ Jc
      · simpa [h] using hcc c h
      · simp [h]
    have h3 : ω₀ c ∈ (if c ∈ Jm then Vm c else Set.univ) := by
      by_cases h : c ∈ Jm
      · simpa [h] using hcm c h
      · simp [h]
    exact ⟨⟨h1, h2⟩, h3⟩
  have hinside : ∀ ω : Ω d981, (∀ c ∈ J, ω c ∈ V c) →
      ω ∈ goodSetFlow d981 0 s981 t981 (fun _ => flowDelta d981 0 t981 N) N ∧
      ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N ∧
      ω ∈ APrimeGeneralMovingGoodMesh.good N := by
    intro ω hω
    have hf : ∀ c ∈ Jf, ω c ∈ Vf c := by
      intro c hc
      have hv := hω c (by simp [J, hc])
      simpa [V, hc] using hv.1.1
    have hc : ∀ c ∈ Jc, ω c ∈ Vc c := by
      intro c hc
      have hv := hω c (by simp [J, hc])
      simpa [V, hc] using hv.1.2
    have hm : ∀ c ∈ Jm, ω c ∈ Vm c := by
      intro c hc
      have hv := hω c (by simp [J, hc])
      simpa [V, hc] using hv.2
    have hmesh : ‖Xmat d981 N ω‖ < (N : ℝ) := him ω hm
    change ω ∈ goodSetFlow d981 0 s981 t981
        (fun _ => flowDelta d981 0 t981 N) N ∧
      ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N ∧
      ‖Xmat d981 N ω‖ ≤ (N : ℝ)
    exact ⟨hif ω hf, hic ω hc, hmesh.le⟩
  have hprob := support_cylinder_pos_triple_981 J V ω₀ hV hcenter hcompat
    (fun ω hω => hinside ω hω)
  rw [Set.inter_assoc]
  change 0 < P d981 (goodSetFlow d981 0 s981 t981
      (fun _ => flowDelta d981 0 t981 N) N ∩
      (APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N ∩
        {ω : Ω d981 | ‖Xmat d981 N ω‖ ≤ (N : ℝ)}))
  exact hprob


private theorem quantile_sample_diagonal_981 (N : ℕ)
    (perm : Equiv.Perm (Fin (d981.W N))) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (b : ZMod (d981.L N)) :
    ∀ α : Fin (d981.W N),
      Gsig (Hflow d981 N u
        (omegaOfHermitian d981 N (blockDiagonal d981 N
          (fun _ => permutationFourierBlock (d981.W N) (d981.W_pos N) perm))))
        (zt 0 u) true (b, α) (b, α) =
      (((Real.sqrt u : ℂ) • permutationFourierBlock (d981.W N)
          (d981.W_pos N) perm -
        (Complex.I * ((1-u : ℝ) : ℂ)) •
          (1 : Matrix (Fin (d981.W N)) (Fin (d981.W N)) ℂ))⁻¹) α α := by
  intro α
  let C := permutationFourierBlock (d981.W N) (d981.W_pos N) perm
  have hread : Xmat d981 N
      (omegaOfHermitian d981 N (blockDiagonal d981 N (fun _ => C))) =
        blockDiagonal d981 N (fun _ => C) :=
    blockDiagonal_readback d981 N _
      (fun _ => permutationFourierBlock_hermitian _ _ perm)
  change green (Hflow d981 N u
      (omegaOfHermitian d981 N (blockDiagonal d981 N (fun _ => C))))
      (zt 0 u) (b, α) (b, α) = _
  rw [Hflow, hread, zt_zero_energy]
  rw [blockDiagonal_const_resolvent d981 N C
    (permutationFourierBlock_hermitian _ _ perm) u hu.2 (b, α) (b, α)]
  simp only [ite_true]
  change ((Real.sqrt u : ℂ) • C -
    (((1-u : ℝ) : ℂ) * Complex.I) •
      (1 : Matrix (Fin (d981.W N)) (Fin (d981.W N)) ℂ))⁻¹ α α = _
  rw [mul_comm (((1-u : ℝ) : ℂ)) Complex.I]

set_option maxHeartbeats 1000000 in
-- The full inverse matrix expression needs additional reduction heartbeats.
private theorem centered_strict_for_quantile_sample_981
    (N : ℕ) (zeta : ℝ)
    (perm : Equiv.Perm (Fin (d981.W N)))
    (ω₀ : Ω d981)
    (hω₀ : ω₀ = omegaOfHermitian d981 N
      (blockDiagonal d981 N (fun _ => permutationFourierBlock (d981.W N)
        (d981.W_pos N) perm)))
    (hlarge : 4 * Real.sqrt 2 < (N : ℝ) ^ zeta) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ b : ZMod (d981.L N),
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω₀ true b‖ <
          (N : ℝ) ^ zeta * (2 / (d981.W N : ℝ)) := by
  intro u hu b
  subst ω₀
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1 / 2 := hu.2
  have hdiag := quantile_sample_diagonal_981 N perm u hu b
  have htrace := actual_twoCharge_of_oneBlock_diagonal N u hu0 hu1
    (omegaOfHermitian d981 N (blockDiagonal d981 N
        (fun _ => permutationFourierBlock (d981.W N) (d981.W_pos N) perm))) b perm hdiag true
  simp only [↓reduceIte] at htrace
  rw [htrace]
  have herr := permutationFourierSemicircleZeroMode_bound (d981.W N)
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (d981.W_pos N))) u hu0 hu1 perm
  have hW : (0 : ℝ) < (d981.W N : ℝ) := by exact_mod_cast d981.W_pos N
  have hbase : 8 * Real.sqrt 2 / (d981.W N : ℝ) <
      (N : ℝ) ^ zeta * (2 / (d981.W N : ℝ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hi : 0 < ((d981.W N : ℝ)⁻¹) := inv_pos.mpr hW
    nlinarith [mul_lt_mul_of_pos_right hlarge hi]
  exact lt_of_le_of_lt herr hbase

private theorem l2_opNorm_one_nonempty_981 {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] : ‖(1 : Matrix ι ι ℂ)‖ = 1 := by
  rw [show (1 : Matrix ι ι ℂ) = Matrix.diagonal (fun _ : ι => (1 : ℂ)) by
    ext i j
    simp]
  rw [Matrix.l2_opNorm_diagonal]
  simp

private theorem l2_opNorm_conj_diagonal_le_two_981 {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) (v : ι → ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (hv : ∀ i, ‖v i‖ ≤ 2) : ‖Uᴴ * Matrix.diagonal v * U‖ ≤ 2 := by
  have hUnorm : ‖U‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [hU, l2_opNorm_one_nonempty_981] at h
    nlinarith [norm_nonneg U]
  have hUstar : ‖Uᴴ‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self Uᴴ
    rw [show (Uᴴ)ᴴ * Uᴴ = 1 by simpa using hU', l2_opNorm_one_nonempty_981] at h
    nlinarith [norm_nonneg Uᴴ]
  have hdiag : ‖(Matrix.diagonal v : Matrix ι ι ℂ)‖ ≤ 2 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2 hv
  calc
    ‖Uᴴ * Matrix.diagonal v * U‖ ≤ ‖Uᴴ‖ * ‖Matrix.diagonal v‖ * ‖U‖ := by
      calc
        _ ≤ ‖Uᴴ * Matrix.diagonal v‖ * ‖U‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ (‖Uᴴ‖ * ‖Matrix.diagonal v‖) * ‖U‖ :=
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖Matrix.diagonal v‖ := by rw [hUstar, hUnorm]; ring
    _ ≤ 2 := hdiag

private theorem physicalFourierBlock_opNorm_le_two_981 (d : Dims) (N : ℕ)
    (perm : Equiv.Perm (Fin (d.W N))) :
    ‖blockDiagonal d N (fun _ =>
      permutationFourierBlock (d.W N) (d.W_pos N) perm)‖ ≤ 2 := by
  let W := d.W N
  let L := d.L N
  let F := permutationFourierMatrix W
  let U : Matrix (d.Idx N) (d.Idx N) ℂ := blockDiagonal d N (fun _ => F)
  let V : d.Idx N → ℂ := fun i =>
    (semicircleLambda W (d.W_pos N) (perm i.2).val (perm i.2).isLt : ℂ)
  let D : Matrix (d.Idx N) (d.Idx N) ℂ := Matrix.diagonal V
  have hF : Fᴴ * F = 1 := permutationFourierMatrix_conjTranspose_mul W (d.W_pos N)
  have hF' : F * Fᴴ = 1 := permutationFourierMatrix_mul_conjTranspose W (d.W_pos N)
  have hstar : Uᴴ = blockDiagonal d N (fun _ => Fᴴ) := by
    ext ⟨a, x⟩ ⟨b, y⟩
    change star (blockDiagonal d N (fun _ => F) (b, y) (a, x)) = _
    simp only [blockDiagonal]
    by_cases hab : a = b
    · subst b
      simp [Matrix.conjTranspose_apply]
    · have hba : b ≠ a := fun h => hab h.symm
      simp [hab, hba]
  have hU : Uᴴ * U = 1 := by
    rw [hstar]
    dsimp [U]
    change blockDiagonal d N (fun _ => Fᴴ) * blockDiagonal d N (fun _ => F) = 1
    rw [blockDiagonal_mul, hF, blockDiagonal_one]
  have hU' : U * Uᴴ = 1 := by
    rw [hstar]
    dsimp [U]
    change blockDiagonal d N (fun _ => F) * blockDiagonal d N (fun _ => Fᴴ) = 1
    rw [blockDiagonal_mul, hF', blockDiagonal_one]
  have hV : ∀ i, ‖V i‖ ≤ 2 := by
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hi := semicircleLambda_mem_open_support W (d.W_pos N)
      (perm i.2).val (perm i.2).isLt
    exact ⟨le_of_lt hi.1, le_of_lt hi.2⟩
  have hfactor : Uᴴ * D * U =
      blockDiagonal d N (fun _ => permutationFourierBlock W (d.W_pos N) perm) := by
    have hD : D = blockDiagonal d N (fun _ =>
        Matrix.diagonal (fun j : Fin W =>
          (semicircleLambda W (d.W_pos N) (perm j).val (perm j).isLt : ℂ))) := by
      ext ⟨a, x⟩ ⟨b, y⟩
      by_cases hab : a = b
      · subst b
        simp [D, V, blockDiagonal, Matrix.diagonal_apply]
      · simp [D, blockDiagonal, hab]
    rw [hstar, hD]
    dsimp only [U]
    change blockDiagonal d N (fun _ => Fᴴ) *
      blockDiagonal d N (fun _ => Matrix.diagonal (fun j : Fin W =>
        (semicircleLambda W (d.W_pos N) (perm j).val (perm j).isLt : ℂ))) *
      blockDiagonal d N (fun _ => F) = _
    rw [blockDiagonal_mul, blockDiagonal_mul]
    rfl
  rw [← hfactor]
  exact l2_opNorm_conj_diagonal_le_two_981 U V hU hU' hV


/-- Eventual specialization to the same T971 center, with strict norm interior. -/
theorem eventually_exampleGrow_common_goodSetFlow_centeredEvent_goodMesh_pos_of_strict
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop,
      0 < P d981
        (goodSetFlow d981 0 s981 t981 (fun _ => flowDelta d981 0 t981 N) N ∩
          (APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N ∩
            APrimeGeneralMovingGoodMesh.good N)) ∧
      ∃ ω : Ω d981,
        ω ∈ goodSetFlow d981 0 s981 t981
          (fun _ => flowDelta d981 0 t981 N) N ∧
        ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 s981 t981 zeta N ∧
        ω ∈ APrimeGeneralMovingGoodMesh.good N ∧
        2 ≤ d981.W N ∧ Xmat d981 N ω ≠ 0 ∧
        (∀ c : Coord d981, (gvar d981 c : ℝ) = 0 → ω c = 0) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) ^ zeta) atTop atTop :=
    (tendsto_rpow_atTop hzeta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * Real.sqrt 2 < (N : ℝ) ^ zeta :=
    htop.eventually_gt_atTop (4 * Real.sqrt 2)
  filter_upwards [eventually_quantile_block_strict_resolvent_nondegenerate,
    eventually_ge_atTop 3, hlarge] with N hN hN3 hlargeN
  obtain ⟨perm, ω₀, hW2, hωeq, hGood, hflowStrict, hnonzero, hcompat⟩ := hN
  have hctr := centered_strict_for_quantile_sample_981 N zeta perm ω₀ hωeq hlargeN
  let δ : ℝ := (N : ℝ) ^ zeta * (2 / (d981.W N : ℝ))
  have hthreshold : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      δ ≤ (N : ℝ) ^ zeta *
        (2 * APrimeGeneralMovingControlExtension.qExt 0 s981 t981 N u) := by
    intro u hu
    dsimp [δ]
    have hq := permutationFourierExampleGrow_qExt_ge_invW N hu
    have hpow : 0 ≤ (N : ℝ) ^ zeta := Real.rpow_nonneg (Nat.cast_nonneg N) zeta
    calc
      (N : ℝ) ^ zeta * (2 / (d981.W N : ℝ)) =
          (N : ℝ) ^ zeta * (2 * (1 / (d981.W N : ℝ))) := by ring
      _ ≤ (N : ℝ) ^ zeta *
          (2 * APrimeGeneralMovingControlExtension.qExt 0 s981 t981 N u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hq (by norm_num)) hpow
  have hnorm2 : ‖blockDiagonal d981 N (fun _ =>
      permutationFourierBlock (d981.W N) (d981.W_pos N) perm)‖ ≤ 2 :=
    physicalFourierBlock_opNorm_le_two_981 d981 N perm
  have hnorm : ‖Xmat d981 N ω₀‖ < (N : ℝ) := by
    rw [hωeq, blockDiagonal_readback d981 N _
      (fun _ => permutationFourierBlock_hermitian _ _ perm)]
    exact lt_of_le_of_lt hnorm2 (by exact_mod_cast (by omega : 2 < N))
  obtain ⟨Jc, Vc, hVc, hcc, hic⟩ :=
    strict_centered_cylinder_981 N zeta δ hthreshold ω₀ hctr
  have hcentered := hic ω₀ hcc
  have hmesh : ω₀ ∈ APrimeGeneralMovingGoodMesh.good N := by
    change ‖Xmat d981 N ω₀‖ ≤ (N : ℝ)
    exact hnorm.le
  have hflow : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ i j : d981.Idx N,
      ‖green (Hflow d981 N u ω₀) (zt 0 u) i j -
        (if i = j then mE 0 else 0)‖ < flowDelta d981 0 t981 N := by
    intro u hu i j
    change ‖green (Hflow Dims.exampleGrow N u ω₀) (zt 0 u) i j -
      (if i = j then mE 0 else 0)‖ < flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N
    simpa [mE_zero] using hflowStrict u hu i j
  have hprob := exampleGrow_common_goodSetFlow_centeredEvent_goodMesh_pos_of_strict
    N zeta δ ω₀ hthreshold hflow hctr hnorm hcompat
  refine ⟨?_, ⟨ω₀, hGood, hcentered, hmesh, hW2, hnonzero, hcompat⟩⟩
  simpa [Set.inter_assoc] using hprob

#print axioms eventually_exampleGrow_common_goodSetFlow_centeredEvent_goodMesh_pos_of_strict

end RBM.Gauss
