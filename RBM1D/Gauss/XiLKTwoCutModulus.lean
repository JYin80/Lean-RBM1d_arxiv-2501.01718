/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514XiPoly
import RBM1D.Gauss.APrimeGeneralMovingWindowFloor
import RBM1D.Flow.FirstCell
import RBM1D.Gauss.XiLKTwoCutMoment

/-!
# The actual all-charge two-loop cutoff modulus (T1339)

The modulus is for the finite maximum in (5.76), with its literal scale squared.
The coordinate estimate is `hHol_flow` at `m = 2` and `c = 2`; taking a finite
maximum costs no factor depending on the number of charges or labels.
-/

namespace RBM.Gauss.XiLKTwoCutModulus

open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The actual measurable all-charge observable in (5.76), with no restriction on
`Im (zt E u)`. -/
theorem measurable_xiLK_two (d : Dims) (E : ℝ) (N : ℕ) (u : ℝ) :
    Measurable (fun ω : Ω d => (sample d).xiLK E N u ω 2) := by
  let F : LoopData ((band d).L N) 2 → Ω d → ℝ := fun q ω =>
    (sample d).lkErr E N u ω q.idx
  have hF : ∀ q, Measurable (F q) := by
    intro q
    change Measurable fun ω => ‖(sample d).Lval E N u ω q.idx - (band d).Kval E N u q.idx‖
    exact ((RBM.measurable_Lval (sample d) E N u q.idx).sub
      measurable_const).norm
  have hmax : Measurable (fun ω : Ω d => (sample d).lkMax E N u ω 2) := by
    have hEq : (fun ω : Ω d => (sample d).lkMax E N u ω 2) =
        fun ω => (Finset.univ.sup' Finset.univ_nonempty
          (fun q ω' => F q ω')) ω := by
      funext ω
      unfold Sample.lkMax
      rw [Finset.sup'_apply]
      apply le_antisymm
      · apply ciSup_le
        intro q
        simpa [F] using Finset.le_sup' (fun r : LoopData ((band d).L N) 2 => F r ω)
          (Finset.mem_univ q)
      · apply Finset.sup'_le
        intro q hq
        exact le_ciSup (f := fun q : LoopData ((band d).L N) 2 =>
          (sample d).lkErr E N u ω q.idx) (Set.finite_range _).bddAbove q
    simp only [hEq]
    exact Finset.measurable_sup' Finset.univ_nonempty (fun q _ => hF q)
  change Measurable (fun ω : Ω d =>
    (sample d).lkMax E N u ω 2 * (band d).scale E N u ^ 2)
  exact hmax.mul_const _


/-- The Step-3 normalization is eventually positive, from the geometric scale clauses of
(2.72) alone. -/
theorem theta_positive_of_cond272
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      0 < Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2) := by
  have hscale := (Step3.scales_flow (B := band d) hE hs0 hst ht1 hreg.toCond272).one_le_As
  filter_upwards [hscale] with N hN
  exact lt_of_lt_of_le (by norm_num) (Real.one_le_rpow hN (by norm_num))

/-- The exact Step-3 threshold is positive at every index of the natural window. -/
theorem theta_pos_all
    (d : Dims) {E : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) :
    ∀ N, 0 < Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2) := by
  intro N
  exact Real.rpow_pos_of_pos
    ((band d).scale_pos' hE N (hs0 N) ((hst N).trans_lt (ht1 N))) _

/-- `xiLK` is nonnegative at every time where the deterministic scale is nonnegative. -/
theorem xiLK_two_nonneg (d : Dims) {E : ℝ} {N : ℕ} {u : ℝ} (ω : Ω d)
    (hA : 0 ≤ (band d).scale E N u) : 0 ≤ (sample d).xiLK E N u ω 2 :=
  (sample d).xiLK_nonneg hA

/-- The two-loop maximum is nonnegative at every real time, including times outside the
natural window, because its scale is squared. -/
theorem xiLK_two_nonneg_all (d : Dims) (E : ℝ) :
    ∀ (N : ℕ) (u : ℝ) (ω : Ω d), 0 ≤ (sample d).xiLK E N u ω 2 := by
  intro N u ω
  unfold Sample.xiLK
  exact mul_nonneg (sample d).lkMax_nonneg (sq_nonneg _)

/-- A finite maximum is 1-Lipschitz for the sup norm on its coordinates. -/
private theorem finiteMax_abs_sub_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ i, |f i - g i| ≤ C) :
    |Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g| ≤ C := by
  have hab : Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.sup' Finset.univ_nonempty g ≤ C := by
    obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    rw [hmax]
    have hgi : g i ≤ Finset.univ.sup' Finset.univ_nonempty g :=
      Finset.le_sup' g (Finset.mem_univ i)
    have := (abs_le.mp (hfg i)).2
    linarith
  have hba : Finset.univ.sup' Finset.univ_nonempty g -
      Finset.univ.sup' Finset.univ_nonempty f ≤ C := by
    obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty g
    rw [hmax]
    have hfi : f i ≤ Finset.univ.sup' Finset.univ_nonempty f :=
      Finset.le_sup' f (Finset.mem_univ i)
    have := (abs_le.mp (hfg i)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For every Gaussian dimension, the *actual* finite-maximum process from (5.76) obeys the
`K=21`, `gamma=1/2` time modulus on the natural norm event. -/
theorem xiLK_two_event_modulus
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : 0 < c)
    (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ω : Ω d, ‖Xmat d N ω‖ ≤ (N : ℝ) →
      ∀ v ∈ Set.Icc (s N) (t N),
      ∀ w ∈ Set.Icc (s N) (t N),
        |(sample d).xiLK E N v ω 2 - (sample d).xiLK E N w ω 2| ≤
          (N : ℝ) ^ (21 : ℝ) * |v - w| ^ ((1 : ℝ) / 2) := by
  have hfloor := Gauss.rpow_neg_one_le_one_sub_of_scale_ge
    (band d) hE ht1 hc hreg.2
  have honeSub : ∀ᶠ N : ℕ in atTop, (1 - t N)⁻¹ ≤ (N : ℝ) := by
    filter_upwards [hfloor, eventually_ge_atTop (1 : ℕ)] with N hN hN1
    have htpos : 0 < 1 - t N := by linarith [ht1 N]
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hNinv : (N : ℝ)⁻¹ ≤ 1 - t N := by simpa [Real.rpow_neg_one] using hN
    exact (inv_le_comm₀ htpos hNpos).2 hNinv
  have hEta := eventually_etaT_inv_le_sq_window (band d) hE hs0 hst ht1 hreg.toCond272
  have honeSub' : ∀ᶠ N : ℕ in atTop, (1 - t N)⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    simpa only [Real.rpow_one] using honeSub
  have hK := norm_Kval_two_le_rpow d hE ht1 (c := 1) honeSub'
  have hHol := hHol_flow d hE hs0 ht1 (Ξ := fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)})
    (c := 2) (by norm_num) (m := 2) (by norm_num)
    (by
      filter_upwards [hEta] with N hN
      exact le_trans (hN (TimeIcc.last hst N)) (by norm_num))
    (by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN ω hω
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have hx : ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) + 1 := by linarith [hω]
      have hpoly : (N : ℝ) + 1 ≤ (N : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith
      exact hx.trans hpoly)
    (by
      filter_upwards [hK, eventually_ge_atTop (1 : ℕ)] with N hKN hN
      intro w hw J hJ hlen₁ hlen₂
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hk := hKN w hw J hJ (by omega)
      have hweak : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      exact hk.trans hweak)
  filter_upwards [hHol] with N hN ω hω v hv w hw
  let f : LoopData ((band d).L N) 2 → ℝ := fun q =>
    (band d).scale E N v ^ 2 * ‖SumZeroDyn.lkT (sample d) E N v ω q.1 q.2‖
  let g : LoopData ((band d).L N) 2 → ℝ := fun q =>
    (band d).scale E N w ^ 2 * ‖SumZeroDyn.lkT (sample d) E N w ω q.1 q.2‖
  have hcoords : ∀ q : LoopData ((band d).L N) 2,
      |f q - g q| ≤ (N : ℝ) ^ (21 : ℝ) * |v - w| ^ ((1 : ℝ) / 2) := by
    intro q
    have hq := hN ω hω q v hv w hw
    simpa [f, g, band_L, show (2 : ℝ) * (3 * 2 + 4) + 1 = 21 by norm_num] using hq
  have hscalev : 0 ≤ (band d).scale E N v :=
    ((band d).scale_pos' hE N (le_trans (hs0 N) hv.1) (hv.2.trans_lt (ht1 N))).le
  have hscalew : 0 ≤ (band d).scale E N w :=
    ((band d).scale_pos' hE N (le_trans (hs0 N) hw.1) (hw.2.trans_lt (ht1 N))).le
  have hxiEq (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
      (sample d).xiLK E N u ω 2 =
        Finset.univ.sup' Finset.univ_nonempty (fun q : LoopData ((band d).L N) 2 =>
          (band d).scale E N u ^ 2 * ‖SumZeroDyn.lkT (sample d) E N u ω q.1 q.2‖) := by
    unfold Sample.xiLK
    change (sample d).lkMax E N u ω 2 * (band d).scale E N u ^ 2 = _
    have hmax : (sample d).lkMax E N u ω 2 =
        Finset.univ.sup' Finset.univ_nonempty
          (fun q : LoopData ((band d).L N) 2 => (sample d).lkErr E N u ω q.idx) := by
      unfold Sample.lkMax
      apply le_antisymm
      · apply ciSup_le
        intro q
        exact Finset.le_sup' (fun r : LoopData ((band d).L N) 2 =>
          (sample d).lkErr E N u ω r.idx) (Finset.mem_univ q)
      · obtain ⟨q, hq, hqmax⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun q : LoopData ((band d).L N) 2 => (sample d).lkErr E N u ω q.idx)
        rw [hqmax]
        exact le_ciSup (f := fun q : LoopData ((band d).L N) 2 =>
          (sample d).lkErr E N u ω q.idx) (Set.finite_range _).bddAbove q
    rw [hmax]
    calc
      Finset.univ.sup' Finset.univ_nonempty
          (fun q : LoopData ((band d).L N) 2 => (sample d).lkErr E N u ω q.idx) *
            (band d).scale E N u ^ 2 =
        Finset.univ.sup' Finset.univ_nonempty
          (fun q : LoopData ((band d).L N) 2 =>
            (sample d).lkErr E N u ω q.idx * (band d).scale E N u ^ 2) := by
              rw [Finset.sup'_mul₀ (sq_nonneg ((band d).scale E N u))]
      _ = Finset.univ.sup' Finset.univ_nonempty
          (fun q : LoopData ((band d).L N) 2 =>
            (band d).scale E N u ^ 2 * ‖SumZeroDyn.lkT (sample d) E N u ω q.1 q.2‖) := by
              apply congrArg
              funext q
              rw [← SumZeroDyn.norm_lkT]
              ring
  rw [hxiEq v (le_trans (hs0 N) hv.1) (hv.2.trans_lt (ht1 N)),
      hxiEq w (le_trans (hs0 N) hw.1) (hw.2.trans_lt (ht1 N))]
  exact finiteMax_abs_sub_le f g (by positivity) hcoords

/-- The matching mesh data for the requested modulus. -/
theorem xiLK_two_mesh_data {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    (∀ (N : ℕ), (N : ℝ) ^ (21 : ℝ) * (1 / meshK (21 : ℝ) ((1 : ℝ) / 2) N) ^ ((1 : ℝ) / 2) ≤ 1) ∧
      ∀ᶠ N : ℕ in atTop,
        (t N - s N) * meshK (21 : ℝ) ((1 : ℝ) / 2) N + 2 ≤ (N : ℝ) ^ (43 : ℝ) := by
  constructor
  · intro N
    simpa using mesh_fine_at_meshK (Kmod := 21) (γ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) N
  · filter_upwards [card_le_at_meshK (Kmod := 21) (γ := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) hs0 ht1] with N hN
    norm_num at hN ⊢
    exact hN

/-- The exact fine-mesh inequality with the literal `flowAs` threshold required by
`CutHypEvOn.mesh_fine`. -/
theorem xiLK_two_mesh_fine_theta
    (d : Dims) {E c : ℝ} {s t : ℕ → ℝ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hreg : Cond272Reg (band d) E s t c) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (21 : ℝ) *
        (1 / meshK (21 : ℝ) ((1 : ℝ) / 2) N) ^ ((1 : ℝ) / 2) ≤
          Step3.flowAs (band d) E s N ^ ((1 : ℝ) / 2) := by
  have hscale := (Step3.scales_flow (B := band d) hE hs0 hst ht1 hreg.toCond272).one_le_As
  have hmesh := (xiLK_two_mesh_data hs0 ht1).1
  filter_upwards [hscale] with N hN
  exact (hmesh N).trans (Real.one_le_rpow hN (by norm_num))

/-- The natural norm event is measurable and has high probability from the proved trace moment
bound; in particular it is eventually nonempty on the probability space. -/
theorem norm_event_data (d : Dims) :
    (∀ N, MeasurableSet {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}) ∧
      HighProb (band d).P (fun N => {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}) ∧
      ∀ᶠ N : ℕ in atTop, {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)}.Nonempty := by
  exact ⟨Gauss.measurableSet_normX_le d, Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d),
    (Gauss.highProb_normX_le d (Gauss.traceMomentBound_gauss d)).nonempty
      (band d).isProbabilityMeasure.measure_univ⟩

/-- A same-window satisfiability certificate at exampleGrow.  It has the incoming BoundsCore,
the natural high-probability event, an eventually positive Step-3 threshold, and an explicit
strictly positive point of the matching `meshK 21 (1/2)` net. -/
theorem exampleGrow_joint_window_witness :
    ∃ s t : ℕ → ℝ, ∃ c : ℝ,
      (∀ N, 0 ≤ s N) ∧ (∀ N, s N ≤ t N) ∧ (∀ N, t N < 1) ∧
      0 < c ∧ Cond272Reg (band Dims.exampleGrow) 0 s t c ∧
      BoundsCore (sample Dims.exampleGrow) 0 s ∧
      (∀ᶠ N : ℕ in atTop, s N < t N) ∧
      (∀ᶠ N : ℕ in atTop,
        ∃ v ∈ MomentDuhamelCut.netFinset s t (meshK 21 ((1 : ℝ) / 2)) N, s N < v) ∧
      (∀ᶠ N : ℕ in atTop,
        0 < Step3.flowAs (band Dims.exampleGrow) 0 s N ^ ((1 : ℝ) / 2)) ∧
      HighProb (band Dims.exampleGrow).P
        (fun N => {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}) ∧
      ∀ᶠ N : ℕ in atTop,
        {ω : Ω Dims.exampleGrow | ‖Xmat Dims.exampleGrow N ω‖ ≤ (N : ℝ)}.Nonempty := by
  obtain ⟨τ', hτ', c, hc, n₀, hgrid⟩ :=
    cond272Reg_grid_step_domain (band Dims.exampleGrow)
      (κ := 1) (τ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  let terminal : ℕ → ℝ := fun _ => 1 / 2
  have hterminal0 : ∀ N, 0 ≤ terminal N := fun _ => by norm_num [terminal]
  have hpow : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-1 + (1 / 2 : ℝ)) ≤ 1 - terminal N := by
    have htend : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    filter_upwards [htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with N hN
    norm_num [terminal] at ⊢
    exact hN.le
  obtain ⟨_, hstep⟩ := hgrid 0 (by norm_num) terminal hterminal0 hpow
  let s : ℕ → ℝ := fun N => gridT ((band Dims.exampleGrow).W N) τ' (terminal N) 0
  let t : ℕ → ℝ := fun N => gridT ((band Dims.exampleGrow).W N) τ' (terminal N) 1
  have hdom := hstep 0
  have hs0 : ∀ N, 0 ≤ s N := hdom.1
  have hst : ∀ N, s N ≤ t N := hdom.2.1
  have ht1 : ∀ N, t N < 1 := hdom.2.2.1
  have hreg : Cond272Reg (band Dims.exampleGrow) 0 s t c := hdom.2.2.2
  have hlen : ∀ᶠ N : ℕ in atTop, s N < t N := by
    filter_upwards [eventually_gridT_zero_lt_gridT_one (band Dims.exampleGrow) hτ'
      (Eventually.of_forall fun N => by positivity : ∀ᶠ N : ℕ in atTop, 0 < terminal N)] with N hN
    simpa [s, t, terminal] using hN
  have hWpow : ∀ᶠ N : ℕ in atTop,
      ((band Dims.exampleGrow).W N : ℝ) ^ (-τ') < 1 / 2 := by
    have htend : Tendsto (fun N : ℕ => ((band Dims.exampleGrow).W N : ℝ) ^ (-τ'))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp (Step2.tendsto_W (band Dims.exampleGrow))
    exact htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hnet : ∀ᶠ N : ℕ in atTop,
      ∃ v ∈ MomentDuhamelCut.netFinset s t (meshK 21 ((1 : ℝ) / 2)) N, s N < v := by
    filter_upwards [hWpow, eventually_ge_atTop (1 : ℕ)] with N hW hN
    have hs : s N = 0 := by
      dsimp [s, terminal]
      rw [gridT_zero (by norm_num)]
    have ht : t N = 1 / 2 := by
      dsimp [t, terminal]
      rw [gridT]
      have hW' : (Dims.exampleGrow.W N : ℝ) ^ (-τ') < 1 / 2 := by
        simpa [band] using hW
      have hpow'' : ((Dims.exampleGrow.W N : ℝ) ^ (-((1 : ℝ) * τ'))) < 1 / 2 := by
        simpa only [one_mul] using hW'
      have hlarge : (1 / 2 : ℝ) ≤ gridS (Dims.exampleGrow.W N) τ' 1 := by
        rw [gridS]
        simp only [Nat.cast_one, one_mul]
        linarith [hpow'']
      change min (gridS (Dims.exampleGrow.W N) τ' 1) (1 / 2 : ℝ) = 1 / 2
      exact min_eq_right hlarge
    have hmesh : 2 ≤ meshK 21 ((1 : ℝ) / 2) N := by
      rw [meshK]
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
      have hp := Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 : ℝ) ≤ 42)
      have hbase2 : (2 : ℝ) ≤ (N : ℝ) + 1 := by linarith
      calc
        (2 : ℝ) ≤ (N : ℝ) + 1 := hbase2
        _ = ((N : ℝ) + 1) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ ((N : ℝ) + 1) ^ (42 : ℝ) := hp
        _ = meshK 21 ((1 : ℝ) / 2) N := by norm_num [meshK]
    have hprod : 1 ≤ (t N - s N) * meshK 21 ((1 : ℝ) / 2) N := by
      rw [hs, ht]
      nlinarith
    have hfloor : 1 ≤ ⌊(t N - s N) * meshK 21 ((1 : ℝ) / 2) N⌋₊ :=
      Nat.le_floor (by exact_mod_cast hprod)
    refine ⟨1 / meshK 21 ((1 : ℝ) / 2) N, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨1, Finset.mem_range.mpr ?_, ?_⟩
      · omega
      · rw [hs]
        norm_num
    · rw [hs]
      positivity
  have htheta := theta_positive_of_cond272 Dims.exampleGrow (by norm_num) hs0 hst ht1 hreg
  have hsEq : ∀ N, s N = 0 := by
    intro N
    dsimp [s, terminal]
    exact gridT_zero (by norm_num)
  have hB : BoundsCore (sample Dims.exampleGrow) 0 s :=
    RBM.boundsCore_gauss_witness.1.congr (sample Dims.exampleGrow)
      (Eventually.of_forall fun N => (hsEq N).symm)
  have hHP := Gauss.highProb_normX_le Dims.exampleGrow
    (Gauss.traceMomentBound_gauss Dims.exampleGrow)
  exact ⟨s, t, c, hs0, hst, ht1, hc, hreg, hB, hlen, hnet, htheta, hHP,
    hHP.nonempty (band Dims.exampleGrow).isProbabilityMeasure.measure_univ⟩

#print axioms measurable_xiLK_two
#print axioms xiLK_two_event_modulus
#print axioms xiLK_two_mesh_data
#print axioms theta_positive_of_cond272
#print axioms theta_pos_all
#print axioms xiLK_two_nonneg
#print axioms xiLK_two_nonneg_all
#print axioms xiLK_two_mesh_fine_theta
#print axioms norm_event_data
#print axioms exampleGrow_joint_window_witness

end
end RBM.Gauss.XiLKTwoCutModulus
