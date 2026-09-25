/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PermutationFourierExampleGrowStrictMargin
import RBM1D.Gauss.PermutationFourierExampleGrowCenteredEvent
import RBM1D.Gauss.PermutationFourierExampleGrowCenteredZeroMargin
import RBM1D.Gauss.PermutationFourierExampleGrowPositiveEvent
import RBM1D.Gauss.FiniteSupportCore
import RBM1D.Gauss.APrimeGeneralMovingCommonSources
import Mathlib.Topology.Compactness.Compact

/-! Positive actual Gaussian mass of the literal joint flow and centered-trace event.

A single Fourier-quantile sample has strict margins in both events over the
closed half-time interval. Compact-time continuity gives a finite-coordinate
cylinder inside their intersection, and compatible Gaussian support gives that
cylinder positive actual product-Gaussian mass.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Matrix Real
open scoped Matrix.Norms.L2Operator

namespace RBM.Gauss

private noncomputable abbrev dEG : Dims := Dims.exampleGrow
private noncomputable abbrev sEG : ℕ → ℝ := fun _ => 0
private noncomputable abbrev tEG : ℕ → ℝ := fun _ => 1 / 2

/-- The true-charge centered trace is jointly continuous in the sample and
flow time below time one. -/
private theorem continuousAt_centeredTrace_true_joint (N : ℕ)
    (p : Ω dEG × ℝ) (hp : p.2 < 1) (b : ZMod (dEG.L N)) :
    ContinuousAt (fun q : Ω dEG × ℝ =>
      APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N q.2 q.1 true b) p := by
  have hg := continuousAt_green_joint dEG N 0 p (by norm_num) hp
  let T : Matrix (dEG.Idx N) (dEG.Idx N) ℂ → ℂ := fun A =>
    Matrix.trace ((A - mSigma 0 true • (1 : Matrix (dEG.Idx N) (dEG.Idx N) ℂ)) *
      Eblk (dEG.L N) (dEG.W N) b)
  have hT : Continuous T := by
    dsimp [T]
    fun_prop
  have h := hT.continuousAt.comp hg
  convert h using 1
  ext q
  rfl

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

/-- Strict true-charge trace control yields a finite cylinder that remains
inside the literal two-charge centered event, provided the supplied constant
margin is below its actual threshold. -/
private theorem strict_centeredEvent_cylinder (N : ℕ) (zeta δ : ℝ)
    (hthreshold : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      δ ≤ (N : ℝ) ^ zeta *
        (2 * APrimeGeneralMovingControlExtension.qExt 0 sEG tEG N u))
    (ω₀ : Ω dEG)
    (hstrict : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ b : ZMod (dEG.L N),
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω₀ true b‖ < δ) :
    ∃ J : Finset (Coord dEG), ∃ V : Coord dEG → Set ℝ,
      (∀ c, IsOpen (V c)) ∧ (∀ c ∈ J, ω₀ c ∈ V c) ∧
      (∀ ω : Ω dEG, (∀ c ∈ J, ω c ∈ V c) →
        ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N) := by
  classical
  let Q : Finset (ZMod (dEG.L N)) := Finset.univ
  let F : ZMod (dEG.L N) → (Ω dEG × ℝ) → ℝ := fun b p =>
    ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N p.2 p.1 true b‖
  have hcont : ∀ b ∈ Q, ∀ p : Ω dEG × ℝ, p.2 < 1 → ContinuousAt (F b) p := by
    intro b _ p hp
    exact (continuousAt_centeredTrace_true_joint N p hp b).norm
  have hKlt : ∀ u ∈ Set.Icc (0 : ℝ) (1/2), u < 1 := by
    intro u hu
    linarith [hu.2]
  obtain ⟨J,V,hV,hcenter,hbound⟩ :=
    topology_cylinder_local ω₀ (Set.Icc (0 : ℝ) (1/2)) isCompact_Icc
      Q F δ hcont hKlt (by
        intro b _ u hu
        exact hstrict u hu b)
  refine ⟨J,V,hV,hcenter,?_⟩
  intro ω hω σ p
  obtain ⟨u,hu⟩ := p.1
  have hu' : u ∈ Set.Icc (0 : ℝ) (1/2) := by simpa [sEG, tEG] using hu
  have htrue := hbound ω hω p.2 (Finset.mem_univ _) u hu'
  have hle := hthreshold u hu'
  have htrue' : ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace
      0 N u ω true p.2‖ ≤
      (N : ℝ)^zeta * (2 * APrimeGeneralMovingControlExtension.qExt 0 sEG tEG N u) :=
    (htrue.le).trans hle
  cases σ with
  | true => exact htrue'
  | false =>
      rw [APrimeGeneralMovingTwoChargeModulus.centeredTrace_false_norm_eq_true]
      exact htrue'

private theorem quantile_sample_diagonal (N : ℕ)
    (perm : Equiv.Perm (Fin (dEG.W N))) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) (1 / 2)) (b : ZMod (dEG.L N)) :
    ∀ α : Fin (dEG.W N),
      Gsig (Hflow dEG N u
        (omegaOfHermitian dEG N (blockDiagonal dEG N
          (fun _ => permutationFourierBlock (dEG.W N) (dEG.W_pos N) perm))))
        (zt 0 u) true (b, α) (b, α) =
      (((Real.sqrt u : ℂ) • permutationFourierBlock (dEG.W N)
          (dEG.W_pos N) perm -
        (Complex.I * ((1-u : ℝ) : ℂ)) •
          (1 : Matrix (Fin (dEG.W N)) (Fin (dEG.W N)) ℂ))⁻¹) α α := by
  intro α
  let C := permutationFourierBlock (dEG.W N) (dEG.W_pos N) perm
  have hread : Xmat dEG N
      (omegaOfHermitian dEG N (blockDiagonal dEG N (fun _ => C))) =
        blockDiagonal dEG N (fun _ => C) :=
    blockDiagonal_readback dEG N _
      (fun _ => permutationFourierBlock_hermitian _ _ perm)
  change green (Hflow dEG N u
      (omegaOfHermitian dEG N (blockDiagonal dEG N (fun _ => C))))
      (zt 0 u) (b, α) (b, α) = _
  rw [Hflow, hread, zt_zero_energy]
  rw [blockDiagonal_const_resolvent dEG N C
    (permutationFourierBlock_hermitian _ _ perm) u hu.2 (b, α) (b, α)]
  simp only [ite_true]
  change ((Real.sqrt u : ℂ) • C -
    (((1-u : ℝ) : ℂ) * Complex.I) •
      (1 : Matrix (Fin (dEG.W N)) (Fin (dEG.W N)) ℂ))⁻¹ α α = _
  rw [mul_comm (((1-u : ℝ) : ℂ)) Complex.I]

set_option maxHeartbeats 1000000 in
-- The full finite-matrix inverse expression in this estimate needs extra reduction heartbeats.
private theorem centered_strict_for_quantile_sample
    (N : ℕ) (zeta : ℝ)
    (perm : Equiv.Perm (Fin (dEG.W N)))
    (ω₀ : Ω dEG)
    (hω₀ : ω₀ = omegaOfHermitian dEG N
      (blockDiagonal dEG N (fun _ => permutationFourierBlock (dEG.W N)
        (dEG.W_pos N) perm)))
    (hlarge : 4 * Real.sqrt 2 < (N : ℝ) ^ zeta) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ b : ZMod (dEG.L N),
        ‖APrimeGeneralMovingTwoChargeModulus.centeredTrace 0 N u ω₀ true b‖ <
          (N : ℝ) ^ zeta * (2 / (dEG.W N : ℝ)) := by
  intro u hu b
  subst ω₀
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u ≤ 1 / 2 := hu.2
  have hdiag := quantile_sample_diagonal N perm u hu b
  have htrace := actual_twoCharge_of_oneBlock_diagonal N u hu0 hu1
    (omegaOfHermitian dEG N (blockDiagonal dEG N
        (fun _ => permutationFourierBlock (dEG.W N) (dEG.W_pos N) perm))) b perm hdiag true
  simp only [↓reduceIte] at htrace
  rw [htrace]
  have herr := permutationFourierSemicircleZeroMode_bound (dEG.W N)
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (dEG.W_pos N))) u hu0 hu1 perm
  have hW : (0 : ℝ) < (dEG.W N : ℝ) := by exact_mod_cast dEG.W_pos N
  have hbase : 8 * Real.sqrt 2 / (dEG.W N : ℝ) <
      (N : ℝ)^zeta * (2 / (dEG.W N : ℝ)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hi : 0 < ((dEG.W N : ℝ)⁻¹) := inv_pos.mpr hW
    nlinarith [mul_lt_mul_of_pos_right hlarge hi]
  exact lt_of_le_of_lt herr hbase

private theorem strict_cylinder_support_pos_joint (N : ℕ) (zeta : ℝ)
    (ω₀ : Ω dEG) (J : Finset (Coord dEG)) (V : Coord dEG → Set ℝ)
    (hV : ∀ c, IsOpen (V c))
    (hcenter : ∀ c ∈ J, ω₀ c ∈ V c)
    (hcompat : ∀ c, (gvar dEG c : ℝ) = 0 → ω₀ c = 0)
    (hinside : ∀ ω : Ω dEG, (∀ c ∈ J, ω c ∈ V c) →
      ω ∈ goodSetFlow dEG 0 sEG tEG
          (fun _ => flowDelta dEG 0 tEG N) N ∧
        ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N) :
    0 < P dEG
      (goodSetFlow dEG 0 sEG tEG (fun _ => flowDelta dEG 0 tEG N) N ∩
        APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N) := by
  classical
  let I := effectiveCoords dEG J
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
  have hpos := support_cylinder_pos dEG J hU hUne
  have hsub : supportCylinder dEG J U ⊆
      goodSetFlow dEG 0 sEG tEG (fun _ => flowDelta dEG 0 tEG N) N ∩
        APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N := by
    intro ω hω
    apply hinside
    intro c hc
    by_cases hvar : gvar dEG c ≠ 0
    · exact hω.1 ⟨c, Finset.mem_filter.mpr ⟨hc, hvar⟩⟩
    · have hzero : gvar dEG c = 0 := by
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

/-- Eventually the actual Gaussian measure of the literal joint event is
positive. The same witness is nonzero and vanishes on every zero-variance
coordinate. -/
theorem eventually_exampleGrow_joint_goodSetFlow_centeredEvent_pos_nondegenerate
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∀ᶠ N : ℕ in atTop,
      0 < P dEG
        (goodSetFlow dEG 0 sEG tEG
          (fun _ => flowDelta dEG 0 tEG N) N ∩
          APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N) ∧
      ∃ ω : Ω dEG,
        ω ∈ goodSetFlow dEG 0 sEG tEG
          (fun _ => flowDelta dEG 0 tEG N) N ∧
        ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N ∧
        Xmat dEG N ω ≠ 0 ∧
        (∀ c : Coord dEG, (gvar dEG c : ℝ) = 0 → ω c = 0) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ)^zeta) atTop atTop :=
    (tendsto_rpow_atTop hzeta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 * Real.sqrt 2 < (N : ℝ)^zeta :=
    htop.eventually_gt_atTop (4 * Real.sqrt 2)
  filter_upwards [eventually_quantile_block_strict_resolvent_nondegenerate,
    hlarge] with N hN hlargeN
  obtain ⟨perm, ω₀, hW2, hωeq, hGood, hflowStrict, hnonzero, hcompat⟩ := hN
  let δ : ℝ := (N : ℝ)^zeta * (2 / (dEG.W N : ℝ))
  have hW : (0 : ℝ) < (dEG.W N : ℝ) := by exact_mod_cast dEG.W_pos N
  have hq : ∀ u ∈ Set.Icc (0 : ℝ) (1/2),
      1 / (dEG.W N : ℝ) ≤
        APrimeGeneralMovingControlExtension.qExt 0 sEG tEG N u := by
    intro u hu
    exact permutationFourierExampleGrow_qExt_ge_invW N hu
  have hthreshold : ∀ u ∈ Set.Icc (0 : ℝ) (1/2),
      δ ≤ (N : ℝ)^zeta *
        (2 * APrimeGeneralMovingControlExtension.qExt 0 sEG tEG N u) := by
    intro u hu
    dsimp [δ]
    have hpow : 0 ≤ (N : ℝ)^zeta := Real.rpow_nonneg (Nat.cast_nonneg N) zeta
    calc
      (N : ℝ)^zeta * (2 / (dEG.W N : ℝ)) =
          (N : ℝ)^zeta * (2 * (1 / (dEG.W N : ℝ))) := by ring
      _ ≤ (N : ℝ)^zeta *
          (2 * APrimeGeneralMovingControlExtension.qExt 0 sEG tEG N u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hq u hu) (by norm_num)) hpow
  have hcenterStrict := centered_strict_for_quantile_sample N zeta perm ω₀ hωeq hlargeN
  obtain ⟨Jf,Vf,hVf,hcf,hif⟩ := strict_goodSetFlow_cylinder
    Dims.exampleGrow N 0 ω₀
    (flowDelta Dims.exampleGrow 0 (fun _ => 1 / 2) N) (by norm_num) (by
      intro u hu i j
      simpa [mE_zero] using hflowStrict u hu i j)
  obtain ⟨Jc,Vc,hVc,hcc,hic⟩ := strict_centeredEvent_cylinder
    N zeta δ hthreshold ω₀ hcenterStrict
  let J : Finset (Coord dEG) := Jf ∪ Jc
  let V : Coord dEG → Set ℝ := fun c =>
    (if c ∈ Jf then Vf c else Set.univ) ∩
      (if c ∈ Jc then Vc c else Set.univ)
  have hV : ∀ c, IsOpen (V c) := by
    intro c
    by_cases hcf' : c ∈ Jf <;> by_cases hcc' : c ∈ Jc
    · simpa [V, hcf', hcc'] using (hVf c).inter (hVc c)
    · simp [V, hcf', hcc', hVf]
    · simp [V, hcf', hcc', hVc]
    · simp [V, hcf', hcc']
  have hcenter : ∀ c ∈ J, ω₀ c ∈ V c := by
    intro c hc
    rcases Finset.mem_union.mp hc with hcf' | hcc'
    · dsimp [V]
      simp only [if_pos hcf']
      by_cases hcc' : c ∈ Jc
      · simp only [if_pos hcc']
        exact ⟨hcf c hcf', hcc c hcc'⟩
      · simp only [if_neg hcc']
        exact ⟨hcf c hcf', Set.mem_univ _⟩
    · dsimp [V]
      simp only [if_pos hcc']
      by_cases hcf' : c ∈ Jf
      · simp only [if_pos hcf']
        exact ⟨hcf c hcf', hcc c hcc'⟩
      · simp only [if_neg hcf']
        exact ⟨Set.mem_univ _, hcc c hcc'⟩
  have hinside : ∀ ω : Ω dEG, (∀ c ∈ J, ω c ∈ V c) →
      ω ∈ goodSetFlow dEG 0 sEG tEG (fun _ => flowDelta dEG 0 tEG N) N ∧
      ω ∈ APrimeGeneralMovingCommonSources.centeredEvent 0 sEG tEG zeta N := by
    intro ω hω
    constructor
    · apply hif ω
      intro c hc
      have hcV := hω c (Finset.mem_union.mpr (Or.inl hc))
      dsimp [V] at hcV
      simpa [hc] using hcV.1
    · apply hic ω
      intro c hc
      have hcV := hω c (Finset.mem_union.mpr (Or.inr hc))
      dsimp [V] at hcV
      simpa [hc] using hcV.2
  have hprob := strict_cylinder_support_pos_joint N zeta ω₀ J V hV hcenter hcompat hinside
  refine ⟨hprob, ⟨ω₀, hGood, (hinside ω₀ hcenter).2, hnonzero, hcompat⟩⟩

#print axioms continuousAt_centeredTrace_true_joint
#print axioms strict_centeredEvent_cylinder
#print axioms eventually_exampleGrow_joint_goodSetFlow_centeredEvent_pos_nondegenerate

end RBM.Gauss
