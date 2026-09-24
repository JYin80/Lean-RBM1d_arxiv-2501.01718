/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingSlotLossSchedule
import RBM1D.Gauss.APrimeGeneralMovingInitialWitnessCore

/-!
# T1049: sharp eventual canonical smooth-prefix factor

On the concrete first-cell half-time window, the actual canonical smoothing
order makes the active cardinal factor tend to one uniformly over the whole
net prefix, including its zero index.
-/

namespace RBM.APrimeGeneralMovingCanonicalSharpFactor

open Filter MeasureTheory Set Gauss Step2Bootstrap CutHypTheta

noncomputable section

private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := band d
private noncomputable abbrev targetMesh60 : Nat → Real :=
  APrimeGeneralMovingMesh.targetMesh 60

private noncomputable def activeCount (τ' : Real) (N : Nat) : Nat :=
  cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N *
    Fintype.card (LoopArg (d.L N) 2)

private theorem tendsto_targetMesh60 :
    Tendsto targetMesh60 atTop atTop := by
  have hcast : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : Nat => (N : Real) ^ (258 : Real)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num)).comp hcast
  have heq : (fun N : Nat => targetMesh60 N) =ᶠ[atTop]
      (fun N : Nat => (N : Real) ^ (258 : Real)) := by
    filter_upwards [APrimeGeneralMovingMesh.eventually_targetMesh_eq 60] with N hN
    norm_num at hN ⊢
    simpa only [targetMesh60] using hN
  exact Tendsto.congr' heq.symm hpow

/-- On any first-cell window whose endpoint is eventually one half, the
literal target mesh has an unbounded number of active cells. -/
private theorem tendsto_firstCell_top {τ' : Real}
    (hs : ∀ N, Gauss.firstCellS τ' N = 0)
    (ht : ∀ᶠ N : Nat in atTop, Gauss.firstCellT τ' N = 1 / 2) :
    Tendsto (fun N => cutNetTop (Gauss.firstCellS τ')
      (Gauss.firstCellT τ') targetMesh60 N) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  have hmesh := (tendsto_targetMesh60).eventually_ge_atTop (2 * (b : Real))
  have htop : ∀ᶠ N : Nat in atTop,
      b ≤ cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N := by
    filter_upwards [ht, hmesh] with N htN hmeshN
    unfold cutNetTop
    rw [hs N, htN]
    apply Nat.le_floor
    nlinarith
  exact Filter.eventually_atTop.1 htop

private theorem tendsto_activeCount {τ' : Real}
    (hs : ∀ N, Gauss.firstCellS τ' N = 0)
    (ht : ∀ᶠ N : Nat in atTop, Gauss.firstCellT τ' N = 1 / 2) :
    Tendsto (activeCount τ') atTop atTop := by
  have htop := tendsto_firstCell_top hs ht
  have hcard : ∀ N, 1 ≤ Fintype.card (LoopArg (d.L N) 2) := by
    intro N
    apply Fintype.card_pos_iff.mpr
    exact ⟨fun _ => (0 : ZMod (d.L N))⟩
  rw [Filter.tendsto_atTop_atTop]
  intro b
  rw [Filter.tendsto_atTop_atTop] at htop
  obtain ⟨N₀, hN₀⟩ := htop b
  refine ⟨N₀, ?_⟩
  intro N hN
  dsimp [activeCount]
  exact (hN₀ N hN).trans (by
    calc
      cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N =
          cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (hcard N))

/-- The exact count in `canonicalM` diverges on a half-time first-cell
window. Its exponent therefore makes the maximal active cardinal factor tend
to one. -/
private theorem tendsto_canonicalMaxFactor {τ' : Real}
    (hs : ∀ N, Gauss.firstCellS τ' N = 0)
    (ht : ∀ᶠ N : Nat in atTop, Gauss.firstCellT τ' N = 1 / 2) :
    Tendsto (fun N =>
      (activeCount τ' N : Real) ^
        ((1 : Real) / (2 * (APrimeSmoothWeightActual.canonicalM d
          (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N : Real))))
      atTop (nhds 1) := by
  have hcount : Tendsto (fun N => (activeCount τ' N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_activeCount hs ht)
  have hbase := (_root_.tendsto_rpow_div_mul_add (1 / 2 : Real) 1 1 zero_ne_one).comp hcount
  have hEq : (fun N =>
      (activeCount τ' N : Real) ^
        ((1 : Real) / (2 * (APrimeSmoothWeightActual.canonicalM d
          (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N : Real)))) =ᶠ[atTop]
      (fun N => (activeCount τ' N : Real) ^
        ((1 / 2 : Real) / (1 * (activeCount τ' N : Real) + 1))) := by
    filter_upwards with N
    simp only [activeCount, APrimeSmoothWeightActual.canonicalM, targetMesh60]
    congr 1
    push_cast
    field_simp
  exact Tendsto.congr' hEq.symm hbase

private theorem eventually_firstCell_widened_weight_one {τ' δ : Real}
    (hδ : 0 < δ) :
    ∀ᶠ N : Nat in atTop, ∀ ω : Ω d, ∀ p : Nat,
      1 ≤ cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ')
        targetMesh60 N →
      APrimeWeight.widenedW
        (APrimeWeight.canonicalR (Gauss.firstCellS τ')
          (Gauss.firstCellT τ') targetMesh60) 1
        (APrimeGeneralMovingDetFields.J 0 60 (Gauss.firstCellS τ'))
        (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 δ p N 1 ω = 1 := by
  filter_upwards [eventually_ge_atTop 1] with N hN ω p hactive
  let s := Gauss.firstCellS τ'
  let t := Gauss.firstCellT τ'
  let mesh := targetMesh60
  let J := APrimeGeneralMovingDetFields.J 0 60 s
  have hsfun : s = fun _ => (0 : Real) := funext (Gauss.firstCellS_eq_zero τ')
  have hJzero : J N (cutNetPt s mesh N 0) ω = 1 := by
    change Step2Moment.jSnorm (Gauss.sample d) 0 60 s N
      (cutNetPt s mesh N 0) ω = 1
    rw [cutNetPt_zero, hsfun]
    exact APrimeFirstCellCommon.J_zero N ω
  have hpref : ω ∈ prefNet J s mesh
      (fun M _ => (M : Real) ^ (2 * δ) * 1) N 1 := by
    intro j hj
    have hj0 : j = 0 := by
      simpa only [Finset.mem_range, Nat.lt_one_iff] using hj
    subst j
    rw [hJzero]
    have hNr : (1 : Real) ≤ N := by exact_mod_cast hN
    have hpow : 1 ≤ (N : Real) ^ (2 * δ) :=
      Real.one_le_rpow hNr (by linarith)
    simpa using hpow
  have hpieceLower : 1 ≤ APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ N 1 ω :=
    APrimeWeight.piecewiseW_dom_canonical
      (APrimeGeneralMovingDetFields.J_nonneg 0 60 s) δ N 1 ω hpref
  have hpieceUpper := APrimeWeight.piecewiseW_le_one
    (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ N 1 ω
  have hpiece : APrimeWeight.piecewiseW
      (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ N 1 ω = 1 :=
    le_antisymm hpieceUpper hpieceLower
  have hlower := APrimeWeight.piecewiseW_le_widenedW
    (r := APrimeWeight.canonicalR s t mesh) (N₀ := 1)
    (J := J) (s := s) (t := t) (mesh := mesh)
    (by norm_num) δ p N 1 ω
  have hupper := APrimeWeight.widenedW_le_one
    (APrimeWeight.canonicalR s t mesh) 1 J s t mesh δ p N 1 ω
  rw [hpiece] at hlower
  exact le_antisymm hupper hlower

/-- For every fixed `ε>0`, the actual canonical order gives one eventual
cutoff valid simultaneously for all active `k`; `k=0` is included. -/
theorem eventually_uniform_active_factor {τ' ε : Real} (hτ' : 0 < τ')
    (hε : 0 < ε) :
    ∀ᶠ N : Nat in atTop, ∀ k : Nat,
      k ≤ cutNetTop (Gauss.firstCellS τ') (Gauss.firstCellT τ')
        targetMesh60 N →
      (((k * Fintype.card (LoopArg (d.L N) 2) : Nat) : Real) ^
        ((1 : Real) / (2 * (APrimeSmoothWeightActual.canonicalM d
          (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N : Real)))) ≤
        1 + ε := by
  have hs : ∀ N, Gauss.firstCellS τ' N = 0 :=
    Gauss.firstCellS_eq_zero τ'
  have ht : ∀ᶠ N : Nat in atTop, Gauss.firstCellT τ' N = 1 / 2 := by
    have hWt : Tendsto (fun N : Nat => ((d.W N : Real)) ^ (-τ'))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hτ').comp (Step2.tendsto_W B)
    filter_upwards [hWt.eventually_lt_const (by norm_num : (0 : Real) < 1 / 2)] with N hW
    change gridT ((B.W N : Real)) τ' (1 / 2 : Real) 1 = 1 / 2
    apply gridT_of_le
    rw [gridS]
    norm_num
    change (Dims.growW N : Real) ^ (-τ') < 1 / 2 at hW
    linarith
  have hlimit := tendsto_canonicalMaxFactor hs ht
  have hlt : ∀ᶠ N : Nat in atTop,
      (activeCount τ' N : Real) ^
        ((1 : Real) / (2 * (APrimeSmoothWeightActual.canonicalM d
          (Gauss.firstCellS τ') (Gauss.firstCellT τ') targetMesh60 N : Real))) <
          1 + ε :=
    hlimit.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hlt] with N hN
  intro k hk
  have hnat : k * Fintype.card (LoopArg (d.L N) 2) ≤ activeCount τ' N :=
    Nat.mul_le_mul_right _ hk
  have hbase : ((k * Fintype.card (LoopArg (d.L N) 2) : Nat) : Real) ≤
      (activeCount τ' N : Real) := by exact_mod_cast hnat
  have hexp : 0 ≤ (1 : Real) / (2 *
      (APrimeSmoothWeightActual.canonicalM d (Gauss.firstCellS τ')
        (Gauss.firstCellT τ') targetMesh60 N : Real)) := by positivity
  exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hbase hexp).trans hN.le

/-- A concrete T995-compatible half-time first-cell witness carries the
uniform `1+ε` cardinal factor and a nonempty same-event positive actual
smooth-weight cell.  The event and weight fields refer to the same sample;
no transition-event intersection is asserted. -/
theorem exists_t995_half_window_factor_and_resident {ε : Real} (hε : 0 < ε) :
    ∃ τ' c δ : Real, 0 < τ' ∧ 0 < c ∧ 0 < δ ∧ δ ≤ min 1 (c / 100) ∧
      let s := Gauss.firstCellS τ'
      let t := Gauss.firstCellT τ'
      (∀ N, s N = 0) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      Cond272Reg B 0 s t c ∧ BoundsCore (Gauss.sample d) 0 s ∧
      (∀ᶠ N : Nat in atTop, t N = 1 / 2) ∧
      (∀ᶠ N : Nat in atTop, ∀ k : Nat,
        k ≤ cutNetTop s t targetMesh60 N →
        (((k * Fintype.card (LoopArg (d.L N) 2) : Nat) : Real) ^
          ((1 : Real) / (2 * (APrimeSmoothWeightActual.canonicalM d s t
            targetMesh60 N : Real)))) ≤ 1 + ε) ∧
      (∀ᶠ N : Nat in atTop,
        s N < t N ∧ ∃ ω,
          ω ∈ APrimeGeneralMovingCommonSources.commonEvent
            0 60 s t
            (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
            (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
            (APrimeGeneralMovingSlotLossSchedule.tauG δ) N ∧
          1 ≤ cutNetTop s t targetMesh60 N ∧
          APrimeWeight.widenedW
            (APrimeWeight.canonicalR s t targetMesh60) 1
            (APrimeGeneralMovingDetFields.J 0 60 s) s t targetMesh60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) 1 N 1 ω = 1 ∧
          0 < APrimeSmoothWeightActual.weight d 0 60
            (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t targetMesh60
            2 1 N 1 (APrimeSmoothWeightActual.canonicalM d s t targetMesh60 N) ω) := by
  obtain ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1, hreg, hB, hlength, hhalf⟩ :=
    APrimeGeneralMovingInitialHinit.positive_length_hinit_witness'
  let s := Gauss.firstCellS τ'
  let t := Gauss.firstCellT τ'
  change (∀ N, s N = 0) at hsEq
  change (∀ N, 0 ≤ s N) at hs0
  change (∀ N, s N ≤ t N) at hst
  change (∀ N, t N < 1) at ht1
  change Cond272Reg B 0 s t c at hreg
  change BoundsCore (Gauss.sample d) 0 s at hB
  change ∀ᶠ N : Nat in atTop, s N < t N at hlength
  change ∀ᶠ N : Nat in atTop, t N = 1 / 2 at hhalf
  let δ : Real := min 1 (c / 100) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδsmall : δ ≤ min 1 (c / 100) := by
    dsimp [δ]
    have hmin : 0 < min 1 (c / 100) := by positivity
    linarith
  obtain ⟨hdw, hxi, hcap, htau, hsrc, hctr, _hsum, _hsrcTau,
      _htauCap, _hcapC, _hroom, _hgap₁, _hgap₂⟩ :=
    APrimeGeneralMovingSlotLossSchedule.schedule_room hc hδ hδsmall
  have hfactor := eventually_uniform_active_factor hτ' hε
  have hcommon := APrimeGeneralMovingCommonSources.highProb_commonEvent
    (E := 0) (D := 60) (c := c) (by norm_num) (by norm_num)
    hs0 hst ht1 hc hreg hB
    (APrimeGeneralMovingSlotLossSchedule.zetaSrc δ)
    (APrimeGeneralMovingSlotLossSchedule.zetaCtr δ)
    (APrimeGeneralMovingSlotLossSchedule.tauG δ) hsrc hctr htau
  have hnonempty := hcommon.nonempty (by simp)
  have htop := tendsto_firstCell_top hsEq hhalf
  have hactive := htop.eventually_ge_atTop 1
  have hwide := eventually_firstCell_widened_weight_one (τ' := τ')
    (δ := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) hdw
  refine ⟨τ', c, δ, hτ', hc, hδ, hδsmall, hsEq, hst, ht1, hreg, hB,
    hhalf, hfactor, ?_⟩
  filter_upwards [hlength, hnonempty, hactive, hwide] with
    N hlengthN hnonemptyN hactiveN hwideN
  obtain ⟨ω, hω⟩ := hnonemptyN
  have hwideOne := hwideN ω 1 hactiveN
  have hcompare := APrimeSmoothWeightActual.widenedW_le_weight_canonical d
    (E := 0) (D := 60)
    (δ := APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
    (s := s) (t := t) (mesh := targetMesh60)
    (by norm_num) hdw.le N 1 1 ω (hst N) (ht1 N)
    (APrimeGeneralMovingMesh.targetMesh_pos 60 N)
  have hwideOne' : APrimeWeight.widenedW
      (APrimeWeight.canonicalR s t targetMesh60) 1
      (fun N u ω => Step2Moment.jSnorm (Gauss.sample d) 0 60 s N u ω)
      s t targetMesh60 (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ)
      1 N 1 ω = 1 := by
    simpa only [APrimeGeneralMovingDetFields.J] using hwideOne
  have hweight : 0 < APrimeSmoothWeightActual.weight d 0 60
      (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t targetMesh60
      2 1 N 1 (APrimeSmoothWeightActual.canonicalM d s t targetMesh60 N) ω := by
    have hweightOne : 1 ≤ APrimeSmoothWeightActual.weight d 0 60
        (APrimeGeneralMovingSlotLossSchedule.deltaWeight δ) s t targetMesh60
        2 1 N 1 (APrimeSmoothWeightActual.canonicalM d s t targetMesh60 N) ω := by
      simpa only [hwideOne'] using hcompare
    exact lt_of_lt_of_le (by norm_num) hweightOne
  exact ⟨hlengthN, ω, hω, hactiveN, hwideOne, hweight⟩

#print axioms eventually_uniform_active_factor
#print axioms exists_t995_half_window_factor_and_resident

end
end RBM.APrimeGeneralMovingCanonicalSharpFactor
