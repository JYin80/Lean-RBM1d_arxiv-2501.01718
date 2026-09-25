/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeGeneralMovingCommonSources

/-!
# T987: measurability of the literal all-time block event

At fixed matrix size, both actual sides of the block comparison are continuous
in the Gaussian sample at each admissible time. Its all-time event is an
arbitrary intersection of closed comparison sets.
-/

set_option autoImplicit false

namespace RBM.APrimeGeneralMovingBlockEventMeasurable
open Gauss
private noncomputable abbrev d : Dims := Dims.exampleGrow
private noncomputable abbrev B : Band (Ω d) := band d

private theorem continuous_gmBlk_fixed (E : ℝ) (hE : |E| < 2)
    (N : ℕ) (u : ℝ) (hu : u < 1) (x y : ZMod (d.L N)) :
    Continuous (fun ω : Ω d =>
      APrimeJG.gmBlk (sample d) E N u ω x y) := by
  unfold APrimeJG.gmBlk
  apply Continuous.finset_sup'_apply
    (by exact ⟨(true, ⟨0, B.W_pos N⟩, ⟨0, B.W_pos N⟩), Finset.mem_univ _⟩)
  intro z _
  have hG := continuous_Gsig_Hflow d N u
    (zt_im_ne_zero_of_lt_one hE hu) z.1
  have hentry : Continuous (fun ω : Ω d =>
      Gsig (Hflow d N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2)) := by
    fun_prop
  change Continuous (fun ω : Ω d =>
    ‖Gsig (Hflow d N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖)
  exact hentry.norm

private theorem continuous_gsqBlk_fixed (E : ℝ) (hE : |E| < 2)
    (N : ℕ) (u : ℝ) (hu : u < 1) (x y : ZMod (d.L N)) :
    Continuous (fun ω : Ω d =>
      APrimeJG.gsqBlk (sample d) E N u ω x y) := by
  unfold APrimeJG.gsqBlk
  apply Continuous.finset_sup'_apply (by exact ⟨0, Finset.mem_univ _⟩)
  intro x' _
  split_ifs
  · exact (continuous_gmBlk_fixed E hE N u hu y x').mul
      (continuous_gmBlk_fixed E hE N u hu x' y)
  · exact continuous_const

private theorem continuous_jG_fixed (E : ℝ) (hE : |E| < 2)
    (D : ℝ) (N : ℕ) (u : ℝ) (hu : u < 1) :
    Continuous (fun ω : Ω d =>
      APrimeJG.jG (sample d) E N u ω (B.ell N u) (etaT E u) D) := by
  unfold APrimeJG.jG
  apply Continuous.const_add
  apply Continuous.finset_sup'_apply (by exact ⟨(0, 0), Finset.mem_univ _⟩)
  intro p _
  split_ifs
  · exact (continuous_gsqBlk_fixed E hE N u hu p.1 p.2).div_const _
  · exact continuous_const

private theorem continuous_jS_fixed (E : ℝ) (hE : |E| < 2)
    (D : ℝ) (N : ℕ) (u : ℝ) (hu : u < 1) :
    Continuous (fun ω : Ω d => Step2.jS (sample d) E D N u ω) := by
  unfold Step2.jS Step2.jStar
  apply Continuous.add_const
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro a _
  have hloop : Continuous (fun ω : Ω d =>
      (sample d).Lval E N u ω (LoopData.idx (Step2.sigPM, a))) := by
    change Continuous (fun ω : Ω d =>
      gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u)
        (LoopData.idx (Step2.sigPM, a)))
    exact continuous_gloop_Hflow d N u (zt_im_ne_zero_of_lt_one hE hu)
        (LoopData.idx (Step2.sigPM, a))
  have hlk : Continuous (fun ω : Ω d => Step2.lk (sample d) E N u ω a) :=
    hloop.sub continuous_const
  exact hlk.norm.div_const _

private theorem fixed_time_isClosed (E : ℝ) (hE : |E| < 2)
    (D τ : ℝ) (N : ℕ) (u : ℝ) (hu : u < 1) :
    IsClosed {ω : Ω d |
      APrimeJG.jG (sample d) E N u ω (B.ell N u) (etaT E u) D ≤
      1 + (N : ℝ)^τ *
        (9 * Real.exp (Real.sqrt 3) * Step2.jS (sample d) E D N u ω + 2)} := by
  apply isClosed_le (continuous_jG_fixed E hE D N u hu)
  exact continuous_const.add
    (continuous_const.mul ((continuous_const.mul
      (continuous_jS_fixed E hE D N u hu)).add continuous_const))


/-- The literal all-time block event is closed at fixed matrix size. -/
theorem isClosed_blockEvent {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (N : ℕ) (htN : t N < 1) (D τ : ℝ) :
    IsClosed (APrimeGeneralMovingCommonSources.blockEvent E D s t τ N) := by
  have heq : APrimeGeneralMovingCommonSources.blockEvent E D s t τ N =
      ⋂ u : TimeIcc s t N,
        {ω : Ω d |
          APrimeJG.jG (sample d) E N (u : ℝ) ω
            (B.ell N (u : ℝ)) (etaT E (u : ℝ)) D ≤
          1 + (N : ℝ)^τ *
            (9 * Real.exp (Real.sqrt 3) *
              Step2.jS (sample d) E D N (u : ℝ) ω + 2)} := by
    ext ω
    simp only [APrimeGeneralMovingCommonSources.blockEvent,
      Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  apply isClosed_iInter
  intro u
  exact fixed_time_isClosed E hE D τ N (u : ℝ)
    (u.2.2.trans_lt htN)

/-- The literal block event is measurable without a measurable-core replacement. -/
theorem measurableSet_blockEvent {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (N : ℕ) (htN : t N < 1) (D τ : ℝ) :
    MeasurableSet (APrimeGeneralMovingCommonSources.blockEvent E D s t τ N) :=
  (isClosed_blockEvent hE N htN D τ).measurableSet

/-- The spectral and endpoint hypotheses hold on the concrete half-time window. -/
theorem isClosed_blockEvent_E0_halfTime (N : ℕ) (D τ : ℝ) :
    IsClosed (APrimeGeneralMovingCommonSources.blockEvent 0 D
      (fun _ => 0) (fun _ => 1 / 2) τ N) :=
  isClosed_blockEvent (by norm_num) N (by norm_num) D τ


/-- The literal block event has a resident on the positive-length half-time
window at zero energy, for every fixed positive loss exponent eventually. -/
theorem eventually_nonempty_blockEvent_E0_halfTime {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (APrimeGeneralMovingCommonSources.blockEvent 0 60
        (fun _ => 0) (fun _ => 1 / 2) τ N).Nonempty := by
  obtain ⟨τ', hτ', c, hc, hsEq, hs0, hst, ht1,
    hreg, hB, _hpos, htEq⟩ :=
    APrimeGeneralMovingInitialHinit.positive_length_hinit_witness'
  let s : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 0
  let t : ℕ → ℝ := fun N => gridT ((B.W N : ℝ)) τ' (1 / 2 : ℝ) 1
  change ∀ N, s N = 0 at hsEq
  change ∀ N, 0 ≤ s N at hs0
  change ∀ N, s N ≤ t N at hst
  change ∀ N, t N < 1 at ht1
  change Cond272Reg B 0 s t c at hreg
  change BoundsCore (sample d) 0 s at hB
  change ∀ᶠ N : ℕ in Filter.atTop, t N = 1 / 2 at htEq
  have hHP := APrimeGeneralMovingCommonSources.highProb_commonEvent
    (E := 0) (D := 60) (c := c)
    (by norm_num) (by norm_num) hs0 hst ht1 hc hreg hB
    1 1 τ (by norm_num) (by norm_num) hτ
  have hnonempty : ∀ᶠ N : ℕ in Filter.atTop,
      (APrimeGeneralMovingCommonSources.commonEvent 0 60 s t 1 1 τ N).Nonempty :=
    hHP.nonempty (by simp)
  filter_upwards [htEq, hnonempty] with N ht hn
  obtain ⟨ω, hω⟩ := hn
  have hb : ω ∈ APrimeGeneralMovingCommonSources.blockEvent 0 60 s t τ N :=
    (APrimeGeneralMovingCommonSources.commonEvent_subset_rawCarrier
      0 60 s t 1 1 τ N hω).2
  refine ⟨ω, ?_⟩
  rw [show s = (fun _ => 0) from funext hsEq] at hb
  -- Only the fixed matrix size matters in the time index of the event.
  change (∀ u : ↥(Set.Icc (0 : ℝ) (1 / 2 : ℝ)), _)
  change (∀ u : ↥(Set.Icc (0 : ℝ) (t N)), _) at hb
  rw [ht] at hb
  exact hb

#print axioms isClosed_blockEvent
#print axioms measurableSet_blockEvent
#print axioms isClosed_blockEvent_E0_halfTime
#print axioms eventually_nonempty_blockEvent_E0_halfTime

end RBM.APrimeGeneralMovingBlockEventMeasurable
