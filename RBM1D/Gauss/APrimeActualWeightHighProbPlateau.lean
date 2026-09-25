/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeFreeLossGaussianStep2
import RBM1D.Gauss.APrimeSmoothWeightActual
import RBM1D.Gauss.APrimeGeneralMovingCommonSources

/-!
# T1345: an all-cell high-probability plateau for the actual smooth weight

The event is the finite-net restriction of the accepted uniform `JSNormDom`
bound. The same event calibrates every active prefix, independently of its
cell and moment order.
-/

namespace RBM.Gauss.APrimeActualWeightHighProbPlateau

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev mesh : ℕ → ℝ := APrimeGeneralMovingMesh.targetMesh 60
private noncomputable abbrev J (E : ℝ) (s : ℕ → ℝ) : ℕ → ℝ → Ω d → ℝ :=
  fun N u ω => Step2Moment.jSnorm (Gauss.sample d) E 60 s N u ω

/-- The measurable finite-net event at scale `N^(2 lam)`. -/
def Good (E lam : ℝ) (s t : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  prefNet (J E s) s mesh (fun _ _ => (N : ℝ) ^ (2 * lam) * 1) N
    (cutNetTop s t mesh N)

theorem measurableSet_Good (E lam : ℝ) (s t : ℕ → ℝ) (N : ℕ) :
    MeasurableSet (Good E lam s t N) := by
  unfold Good
  apply measurableSet_prefNet
  intro u
  exact APrimeSlotFields.measurable_jSnorm (Gauss.sample d) E 60 s N u

private theorem netPoint_mem_Icc {s t : ℕ → ℝ} (hst : ∀ N, s N ≤ t N)
    (N j : ℕ) (hj : j < cutNetTop s t mesh N) :
    cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) := by
  have hm : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  have hjle : j ≤ cutNetTop s t mesh N := Nat.le_of_lt hj
  have htop : ((cutNetTop s t mesh N : ℕ) : ℝ) ≤ (t N - s N) * mesh N :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr (hst N)) hm.le)
  have hupper : cutNetPt s mesh N j ≤ t N := by
    have hidx : (j : ℝ) ≤ (cutNetTop s t mesh N : ℝ) := by exact_mod_cast hjle
    unfold cutNetPt
    have hfrac : (j : ℝ) / mesh N ≤ t N - s N := by
      apply (div_le_iff₀ hm).2
      calc (j : ℝ) ≤ (cutNetTop s t mesh N : ℝ) := hidx
        _ ≤ (t N - s N) * mesh N := htop
    linarith
  refine ⟨?_, hupper⟩
  unfold cutNetPt
  have hfrac : 0 ≤ (j : ℝ) / mesh N := div_nonneg (Nat.cast_nonneg _) hm.le
  linarith

private theorem jSnorm_nonneg (E : ℝ) (s : ℕ → ℝ) (N : ℕ) (u : ℝ)
    (ω : Ω d) : 0 ≤ J E s N u ω := by
  have hj : 0 ≤ Step2.jS (Gauss.sample d) E 60 N u ω :=
    le_trans zero_le_one (Step2Moment.one_le_jS (Gauss.sample d) N u ω)
  have hr : 0 ≤ Step2Moment.ratR E s N u ^ 4 := by positivity
  exact div_nonneg hj hr

/-- A finite-net event inherits high probability from T1337's existential
failure event over the entire time interval; no net-cardinality loss is used. -/
theorem highProb_Good
    {E lam c : ℝ} {s t : ℕ → ℝ}
    (hlam : 0 < lam) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    HighProb (Gauss.P d) (Good E lam s t) := by
  have hkappa : 0 < (2 - |E|) / 2 := by
    have hgap : 0 < 2 - |E| := by linarith
    positivity
  have hEkappa : |E| ≤ 2 - (2 - |E|) / 2 := by nlinarith
  have hJS : APrimeModel.JSNormDom (Gauss.sample d) E s t 60 :=
    APrimeFreeLossGaussianStep2.jsNormDom_of_gaussian_hypotheses
      (κ := (2 - |E|) / 2) (E := E) (c := c) (s := s) (t := t)
      hkappa hEkappa
      hs0 hst ht1 hc hreg hB 60 (by norm_num)
  have htime := StochDom.highProb hJS (by positivity : 0 < 2 * lam)
  apply HighProb.mono htime
  filter_upwards [] with N
  intro ω hω
  intro j hj
  have hu : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
    netPoint_mem_Icc hst N j hj
  let u : TimeIcc s t N := ⟨cutNetPt s mesh N j, hu.1, hu.2⟩
  have hbound := hω u
  change J E s N (cutNetPt s mesh N j) ω ≤
    (N : ℝ) ^ (2 * lam) * (1 : ℝ) at hbound
  simpa [Good, J] using hbound

/-- On a probability space, a measurable high-probability event has positive
measure eventually. -/
theorem eventually_measure_pos_of_highProb {Ξ : ℕ → Set (Ω d)}
    (hΞ : HighProb (Gauss.P d) Ξ)
    (hΞm : ∀ N, MeasurableSet (Ξ N)) :
    ∀ᶠ N : ℕ in atTop, 0 < (Gauss.P d) (Ξ N) := by
  filter_upwards [hΞ 1 one_pos, eventually_ge_atTop 2] with N htail hN
  by_contra hzero
  have hzero' : (Gauss.P d) (Ξ N) = 0 :=
    le_antisymm (not_lt.mp hzero) bot_le
  have hfin : (Gauss.P d) (Ξ N) ≠ (⊤ : ENNReal) := by
    exact ne_of_lt (measure_lt_top _ _)
  have hcompl : (Gauss.P d) (Ξ N)ᶜ = 1 := by
    rw [measure_compl (hΞm N) hfin, measure_univ, hzero']
    simp
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (-(1 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  have hlt : ENNReal.ofReal ((N : ℝ) ^ (-(1 : ℝ))) < 1 := ENNReal.ofReal_lt_one.mpr hpow
  rw [hcompl] at htail
  exact (not_le_of_gt hlt) htail

/-- The finite-net event itself has strictly positive probability eventually. -/
theorem eventually_Good_pos
    {E lam c : ℝ} {s t : ℕ → ℝ}
    (hlam : 0 < lam) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (Gauss.band d) E s t c)
    (hB : BoundsCore (Gauss.sample d) E s) :
    ∀ᶠ N : ℕ in atTop, 0 < (Gauss.P d) (Good E lam s t N) :=
  eventually_measure_pos_of_highProb
    (highProb_Good hlam hE hs0 hst ht1 hc hreg hB)
    (measurableSet_Good E lam s t)

/-- On `Good`, the existing actual canonical weight equals one for every
natural moment order and every active cell. -/
theorem weight_eq_one_of_mem_Good
    {E lam : ℝ} {s t : ℕ → ℝ} {N k p : ℕ} {ω : Ω d}
    (hE : |E| < 2) (hlam : 0 < lam)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hω : ω ∈ Good E lam s t N)
    (hk : k ≤ cutNetTop s t mesh N) :
    APrimeSmoothWeightActual.weight d E 60 lam s t mesh 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω = 1 := by
  have hJ0 : ∀ N u ω, 0 ≤ J E s N u ω := fun N u ω => jSnorm_nonneg E s N u ω
  have hprefix : ω ∈ prefNet (J E s) s mesh
      (fun N' _ => (N' : ℝ) ^ (2 * lam) * 1) N k := by
    intro j hj
    have hjbound := hω j (lt_of_lt_of_le hj hk)
    simpa [Good, J] using hjbound
  have hdom := APrimeWeight.piecewiseW_dom_canonical
    (J := J E s) (s := s) (t := t) (mesh := mesh) hJ0 lam N k ω hprefix
  have hwide :
      APrimeWeight.piecewiseW (APrimeWeight.canonicalR s t mesh) 1
          (J E s) s t mesh lam N k ω ≤
        APrimeWeight.widenedW (APrimeWeight.canonicalR s t mesh) 1
          (J E s) s t mesh lam p N k ω :=
    APrimeWeight.piecewiseW_le_widenedW
      (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
      (J := J E s) (s := s) (t := t) (mesh := mesh) (by norm_num)
      lam p N k ω
  have hmesh : 0 < mesh N := APrimeGeneralMovingMesh.targetMesh_pos 60 N
  have hactual := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (D := (60 : ℝ)) hE hlam.le N p k ω (hst N) (ht1 N) hmesh
  have hle : 1 ≤ APrimeSmoothWeightActual.weight d E 60 lam s t mesh 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω :=
    hdom.trans (hwide.trans hactual)
  exact le_antisymm
    (APrimeSmoothWeightActual.weight_le_one d E 60 lam s t mesh 2 p N k
      (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω) hle

/-- The joint witness retains T1337's incoming `BoundsCore`, positive window,
and a same-sample good event with an actual positive active-cell weight. -/
structure PositiveWindowWitness (c lam : ℝ) (s t : ℕ → ℝ) where
  base : APrimeFreeLossGaussianMovingSlot.PositiveWindowSlotWitness c s t
  jointMass : ∀ᶠ N : ℕ in atTop,
    0 < (Gauss.P d) (APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
      (lam / 1000) (lam / 1000) (lam / 1000) N ∩ Good 0 lam s t N)
  resident : ∀ᶠ N : ℕ in atTop,
    s N < t N ∧ ∃ ω,
      ω ∈ APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
        (lam / 1000) (lam / 1000) (lam / 1000) N ∧
      ω ∈ Good 0 lam s t N ∧
      1 ≤ cutNetTop s t mesh N ∧
      0 < APrimeSmoothWeightActual.weight d 0 60 lam s t mesh 2 1 N 1
        (APrimeSmoothWeightActual.canonicalM d s t mesh N) ω

/-- A nondegenerate same-parameter witness, intersecting the finite-net plateau
event with T1337's common source event. -/
theorem positive_window_joint_witness {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℝ, 0 < c ∧ ∃ s t : ℕ → ℝ,
      Nonempty (PositiveWindowWitness c lam s t) := by
  obtain ⟨c, hc, s, t, ⟨base⟩⟩ :=
    APrimeFreeLossGaussianMovingSlot.positive_window_joint_slot_witness
  have hGood := highProb_Good hlam (by norm_num) base.hs0 base.hst base.ht1
    base.hc base.hreg base.hB
  have hCommon := APrimeGeneralMovingCommonSources.highProb_commonEvent
    (E := 0) (D := 60) (c := c) (s := s) (t := t)
    (by norm_num) (by norm_num) base.hs0 base.hst base.ht1 base.hc base.hreg base.hB
    (lam / 1000) (lam / 1000) (lam / 1000) (by positivity) (by positivity) (by positivity)
  have hjoint := HighProb.inter hCommon hGood
  have hjointMeas : ∀ N, MeasurableSet
      (APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
        (lam / 1000) (lam / 1000) (lam / 1000) N ∩ Good 0 lam s t N) := by
    intro N
    exact (APrimeGeneralMovingCommonSources.measurableSet_commonEvent
      0 60 s t (lam / 1000) (lam / 1000) (lam / 1000) N).inter
      (measurableSet_Good 0 lam s t N)
  have hjointMass := eventually_measure_pos_of_highProb hjoint hjointMeas
  have hnonempty := HighProb.nonempty (P := Gauss.P d) (by simp) hjoint
  have hresident := base.resident (min (1 / 10000) (c / 10000)) (by positivity)
    (le_of_eq rfl)
  let W : PositiveWindowWitness c lam s t := {
    base := base
    jointMass := hjointMass
    resident := by
      filter_upwards [hresident, hnonempty] with N hres hne
      obtain ⟨hpos, ω₀, hcomm₀, htop₀, hwiden₀, hweight₀⟩ := hres
      obtain ⟨ω, hω⟩ := hne
      have hcomm : ω ∈ APrimeGeneralMovingCommonSources.commonEvent 0 60 s t
          (lam / 1000) (lam / 1000) (lam / 1000) N := hω.1
      have hgood : ω ∈ Good 0 lam s t N := hω.2
      have htop : 1 ≤ cutNetTop s t mesh N := htop₀
      have hweight := weight_eq_one_of_mem_Good (by norm_num) hlam base.hs0
        base.hst base.ht1 hgood (N := N) (k := 1) (p := 1) htop
      exact ⟨hpos, ⟨ω, hcomm, hgood, htop, by simpa [hweight] using (one_pos : (0 : ℝ) < 1)⟩⟩
  }
  exact ⟨c, hc, s, t, ⟨W⟩⟩

#print axioms measurableSet_Good
#print axioms highProb_Good
#print axioms eventually_measure_pos_of_highProb
#print axioms eventually_Good_pos
#print axioms weight_eq_one_of_mem_Good
#print axioms positive_window_joint_witness

end RBM.Gauss.APrimeActualWeightHighProbPlateau
