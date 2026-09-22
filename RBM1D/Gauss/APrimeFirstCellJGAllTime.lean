/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.DimsExample
import RBM1D.Gauss.OpNorm

/-!
# T407: unconditional all-time first-cell block Green cap

This file isolates the deterministic last step of the block Combes--Thomas
argument.  A uniform entrywise exponential Green bound is converted into the
literal `gmBlk`/`gsqBlk`/`jG` observable, retaining the `W⁻⁶⁰` floor.
-/

namespace RBM.APrimeFirstCellJGAllTime

open Filter Real Gauss
open scoped Matrix.Norms.L2Operator

private noncomputable abbrev d : Gauss.Dims := Gauss.Dims.exampleGrow
private noncomputable abbrev B : Band (Gauss.Ω d) := Gauss.band d

/-- The weight used in the audited cyclic block Combes--Thomas argument. -/
noncomputable def ctAlpha : ℝ := Real.log (65 / 64 : ℝ)

theorem ctAlpha_pos : 0 < ctAlpha := by
  exact Real.log_pos (by norm_num)

/-- A direct numerical form of the literal `W⁻⁶⁰` floor comparison. -/
theorem floor_bound_of_log {W ℓ : ℝ} (hW : 0 < W) (hℓ : 1 ≤ ℓ)
    (hlog0 : 0 ≤ Real.log W)
    (hbig : Real.log 16 + 2 * ctAlpha + 60 * Real.log W ≤
      ctAlpha * Real.log W ^ ((3 : ℝ) / 2))
    {r : ℕ} (hfar : ellStar W ℓ / 2 ≤ (r : ℝ)) :
    16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) ≤ W ^ (-(60 : ℝ)) := by
  have hp : 0 ≤ Real.log W ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hlog0 _
  have hpell : Real.log W ^ ((3 : ℝ) / 2) ≤
      Real.log W ^ ((3 : ℝ) / 2) * ℓ := by
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hℓ)]
  have hr : Real.log W ^ ((3 : ℝ) / 2) ≤ 2 * (r : ℝ) := by
    unfold ellStar at hfar
    linarith
  have harg : Real.log 16 + (-2 * ctAlpha * ((r : ℝ) - 1)) ≤
      -60 * Real.log W := by
    nlinarith [mul_le_mul_of_nonneg_left hr ctAlpha_pos.le]
  calc
    16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) =
        Real.exp (Real.log 16 + (-2 * ctAlpha * ((r : ℝ) - 1))) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
    _ ≤ Real.exp (-60 * Real.log W) := Real.exp_le_exp.mpr harg
    _ = W ^ (-(60 : ℝ)) := by
      rw [Real.rpow_def_of_pos hW]
      congr 1
      ring

theorem floor_bound_of_large_log {W ℓ : ℝ} (hW : 0 < W) (hℓ : 1 ≤ ℓ)
    (hlog1 : 1 ≤ Real.log W)
    (hconst : Real.log 16 + 2 * ctAlpha ≤ Real.log W)
    (hroot : 61 ≤ ctAlpha * Real.sqrt (Real.log W))
    {r : ℕ} (hfar : ellStar W ℓ / 2 ≤ (r : ℝ)) :
    16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) ≤ W ^ (-(60 : ℝ)) := by
  have hlog0 : 0 ≤ Real.log W := by linarith
  have hlogpos : 0 < Real.log W := by linarith
  have hsplit : Real.log W ^ ((3 : ℝ) / 2) =
      Real.log W * Real.sqrt (Real.log W) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hlogpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  refine floor_bound_of_log hW hℓ hlog0 ?_ hfar
  rw [hsplit]
  calc
    Real.log 16 + 2 * ctAlpha + 60 * Real.log W
        ≤ Real.log W + 60 * Real.log W := by linarith
    _ = 61 * Real.log W := by ring
    _ ≤ (ctAlpha * Real.sqrt (Real.log W)) * Real.log W := by
      exact mul_le_mul_of_nonneg_right hroot hlog0
    _ = ctAlpha * (Real.log W * Real.sqrt (Real.log W)) := by ring

private noncomputable def floorLogThreshold : ℝ :=
  max 1 (max (Real.log 16 + 2 * ctAlpha) ((61 / ctAlpha) ^ 2))

theorem eventually_floor_bound :
    ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ r : ℕ,
      ellStar ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N u) / 2 ≤ (r : ℝ) →
      16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) ≤
        ((Gauss.band d).W N : ℝ) ^ (-(60 : ℝ)) := by
  have hWlarge := B.eventually_le_W (Real.exp floorLogThreshold)
  filter_upwards [hWlarge] with N hWN u hu r hfar
  have hlogC : floorLogThreshold ≤ Real.log ((Gauss.band d).W N : ℝ) := by
    calc
      floorLogThreshold = Real.log (Real.exp floorLogThreshold) := by simp
      _ ≤ Real.log ((Gauss.band d).W N : ℝ) :=
        Real.log_le_log (Real.exp_pos _) hWN
  have hlog1 : 1 ≤ Real.log ((Gauss.band d).W N : ℝ) :=
    (le_max_left _ _).trans hlogC
  have hconst : Real.log 16 + 2 * ctAlpha ≤
      Real.log ((Gauss.band d).W N : ℝ) :=
    (le_max_left (Real.log 16 + 2 * ctAlpha) ((61 / ctAlpha) ^ 2) |>.trans
      (le_max_right 1 _)).trans hlogC
  have hsq : (61 / ctAlpha) ^ 2 ≤ Real.log ((Gauss.band d).W N : ℝ) :=
    (le_max_right (Real.log 16 + 2 * ctAlpha) ((61 / ctAlpha) ^ 2) |>.trans
      (le_max_right 1 _)).trans hlogC
  have hratio0 : 0 ≤ 61 / ctAlpha :=
    div_nonneg (by norm_num) ctAlpha_pos.le
  have hratio : 61 / ctAlpha ≤ Real.sqrt (Real.log ((Gauss.band d).W N : ℝ)) := by
    have hs := Real.sqrt_le_sqrt hsq
    simpa [Real.sqrt_sq hratio0] using hs
  have hroot : 61 ≤ ctAlpha * Real.sqrt (Real.log ((Gauss.band d).W N : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hratio ctAlpha_pos.le
    have heq : ctAlpha * (61 / ctAlpha) = 61 := by
      field_simp [ne_of_gt ctAlpha_pos]
    linarith
  have hℓ : 1 ≤ (Gauss.band d).ell N u := by
    exact one_le_ellHat (B.L N) (B.three_le_L N) hu.1 (by linarith [hu.2])
  exact floor_bound_of_large_log
    (by exact_mod_cast d.W_pos N) hℓ hlog1 hconst hroot hfar

/-- The unnormalised `W × W` block of the Gaussian matrix. -/
noncomputable def xBlock (N : ℕ) (ω : Gauss.Ω d)
    (x y : ZMod ((Gauss.band d).L N)) :
    Matrix (Fin ((Gauss.band d).W N)) (Fin ((Gauss.band d).W N)) ℂ :=
  fun p q => Xmat d N ω (x, p) (y, q)

/-- The probability-one band-support condition.  It is included explicitly
because zero-variance coordinates are not pointwise zero on the product
sample space. -/
def offBandEvent (N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ∀ (x y : ZMod ((Gauss.band d).L N)),
    1 < zdist ((Gauss.band d).L N) (x - y) →
      ∀ (p q : Fin ((Gauss.band d).W N)), xBlock N ω x y p q = 0}

/-- Every distinct nearest-neighbour off-diagonal block has norm at most `8`. -/
def adjacentBlockEvent (N : ℕ) : Set (Gauss.Ω d) :=
  {ω | ∀ (x y : ZMod ((Gauss.band d).L N)), x ≠ y →
    zdist ((Gauss.band d).L N) (x - y) ≤ 1 → ‖xBlock N ω x y‖ ≤ 8}

/-- The single static event used for every running time. -/
def good (N : ℕ) : Set (Gauss.Ω d) := offBandEvent N ∩ adjacentBlockEvent N

theorem measurable_xBlock (N : ℕ) (x y : ZMod ((Gauss.band d).L N)) :
    Measurable fun ω : Gauss.Ω d => xBlock N ω x y := by
  apply measurable_pi_lambda
  intro p
  apply measurable_pi_lambda
  intro q
  exact Gauss.measurable_Xentry d N (x, p) (y, q)

theorem measurableSet_offBandEvent (N : ℕ) : MeasurableSet (offBandEvent N) := by
  simp only [offBandEvent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro _hxy
  apply MeasurableSet.iInter
  intro p
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_eq_fun
    (Gauss.measurable_Xentry d N (x, p) (y, q)) measurable_const

theorem measurableSet_adjacentBlockEvent (N : ℕ) :
    MeasurableSet (adjacentBlockEvent N) := by
  simp only [adjacentBlockEvent, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro _hxy
  apply MeasurableSet.iInter
  intro _hnear
  exact measurableSet_le (measurable_xBlock N x y).norm measurable_const

theorem measurableSet_good (N : ℕ) : MeasurableSet (good N) :=
  (measurableSet_offBandEvent N).inter (measurableSet_adjacentBlockEvent N)

theorem ae_xBlock_entry_eq_zero_of_offBand (N : ℕ)
    (x y : ZMod ((Gauss.band d).L N))
    (hxy : 1 < zdist ((Gauss.band d).L N) (x - y))
    (p q : Fin ((Gauss.band d).W N)) :
    ∀ᵐ ω ∂Gauss.P d, xBlock N ω x y p q = 0 := by
  have hmem : x - y ∉ sbSupport ((Gauss.band d).L N) := by
    intro h
    exact (not_le_of_gt hxy)
      (zdist_le_one_of_mem_sbSupport ((Gauss.band d).L N) (d.three_le_L N) h)
  have hS : Sblk ((Gauss.band d).L N) ((Gauss.band d).W N) (x, p) (y, q) = 0 := by
    simp only [Sblk, sbKre, hmem, if_false, zero_div]
  have hint := Gauss.integrable_normSq_Xentry d N (x, p) (y, q)
  have hzero :
      ∫ ω, ‖Xentry d N ω (x, p) (y, q)‖ ^ 2 ∂Gauss.P d = 0 := by
    rw [Gauss.integral_normSq_Xentry]
    simpa only [Gauss.band] using hS
  have hae : (fun ω : Gauss.Ω d => ‖Xentry d N ω (x, p) (y, q)‖ ^ 2) =ᵐ[Gauss.P d] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp hzero
  filter_upwards [hae] with ω hω
  have hn : ‖Xentry d N ω (x, p) (y, q)‖ = 0 := by
    simpa only [Pi.zero_apply, sq_eq_zero_iff] using hω
  exact norm_eq_zero.mp hn

theorem ae_mem_offBandEvent (N : ℕ) :
    ∀ᵐ ω ∂Gauss.P d, ω ∈ offBandEvent N := by
  change ∀ᵐ ω ∂Gauss.P d, ∀ x y,
    1 < zdist ((Gauss.band d).L N) (x - y) →
      ∀ p q, xBlock N ω x y p q = 0
  rw [MeasureTheory.ae_all_iff]
  intro x
  rw [MeasureTheory.ae_all_iff]
  intro y
  by_cases hxy : 1 < zdist ((Gauss.band d).L N) (x - y)
  · simp only [hxy, true_implies]
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro q
    exact ae_xBlock_entry_eq_zero_of_offBand N x y hxy p q
  · exact Filter.Eventually.of_forall fun _ => hxy.elim

theorem highProb_offBandEvent : HighProb (Gauss.P d) offBandEvent := by
  intro D hD
  filter_upwards with N
  have hzero : (Gauss.P d) (offBandEvent N)ᶜ = 0 := by
    change (Gauss.P d) {ω | ω ∉ offBandEvent N} = 0
    simpa [MeasureTheory.ae_iff] using ae_mem_offBandEvent N
  rw [hzero]
  exact bot_le

theorem highProb_good_of_adjacent
    (hadjacent : HighProb (Gauss.P d) adjacentBlockEvent) :
    HighProb (Gauss.P d) good := by
  exact highProb_offBandEvent.inter hadjacent

/-- Deterministic terminal step of T407.  The first premise is the output of
the block-scalar Combes--Thomas conjugation.  The second is precisely the
large-bandwidth comparison with the literal `W⁻⁶⁰` floor. -/
theorem jG_le_two_of_green_decay
    (N : ℕ) (u : ℝ) (ω : Gauss.Ω d) (ℓ η : ℝ)
    (hdecay : ∀ (x y : ZMod ((Gauss.band d).L N)) (p q : Fin ((Gauss.band d).W N)),
      ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (x, p) (y, q)‖ ≤
        4 * Real.exp (-ctAlpha * (zdist ((Gauss.band d).L N) (x - y) : ℝ)))
    (hfloor : ∀ r : ℕ,
      ellStar ((Gauss.band d).W N : ℝ) ℓ / 2 ≤ (r : ℝ) →
      16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) ≤
        ((Gauss.band d).W N : ℝ) ^ (-(60 : ℝ))) :
    APrimeJG.jG (Gauss.sample d) 0 N u ω ℓ η 60 ≤ 2 := by
  have hW : (0 : ℝ) < (Gauss.band d).W N := by exact_mod_cast d.W_pos N
  have h := APrimeJG.jG_le_of_neighbor_green_sq
    (X := Gauss.sample d) 0 N u ω ℓ η 60 1 hW (by norm_num)
  suffices hentries : ∀ (x y x' : ZMod ((Gauss.band d).L N)),
      ellStar ((Gauss.band d).W N : ℝ) ℓ / 2 ≤
          (zdist ((Gauss.band d).L N) (x - y) : ℝ) →
      SB ((Gauss.band d).L N) x x' ≠ 0 →
      ∀ (p q : Fin ((Gauss.band d).W N)),
        ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (y, p) (x', q)‖ ^ 2 ≤
            1 * tailT ((Gauss.band d).W N : ℝ) ℓ η 60
              (zdist ((Gauss.band d).L N) (x - y)) ∧
        ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (x', p) (y, q)‖ ^ 2 ≤
            1 * tailT ((Gauss.band d).W N : ℝ) ℓ η 60
              (zdist ((Gauss.band d).L N) (x - y)) by
    have hh := h hentries
    norm_num at hh ⊢
    exact hh
  intro x y x' hxy hxx' p q
  have hmem := APrimeJG.mem_sbSupport_of_SB_ne_zero hxx'
  have hnearN : zdist ((Gauss.band d).L N) (x - x') ≤ 1 :=
    zdist_le_one_of_mem_sbSupport ((Gauss.band d).L N) (d.three_le_L N) hmem
  have htriN := zdist_sub_le_add ((Gauss.band d).L N) x y x'
  have hswap : zdist ((Gauss.band d).L N) (y - x') = zdist ((Gauss.band d).L N) (x' - y) :=
    Lemma57.zdist_sub_comm ((Gauss.band d).L N) y x'
  have htriN' : (zdist ((Gauss.band d).L N) (x - y) : ℝ) ≤
      (zdist ((Gauss.band d).L N) (x - x') : ℝ) + (zdist ((Gauss.band d).L N) (x' - y) : ℝ) := by
    calc
      (zdist ((Gauss.band d).L N) (x - y) : ℝ) ≤
          (zdist ((Gauss.band d).L N) (x - x') : ℝ) + (zdist ((Gauss.band d).L N) (y - x') : ℝ) := htriN
      _ = (zdist ((Gauss.band d).L N) (x - x') : ℝ) +
          (zdist ((Gauss.band d).L N) (x' - y) : ℝ) := by rw [hswap]
  have hnear : (zdist ((Gauss.band d).L N) (x - x') : ℝ) ≤ 1 := by exact_mod_cast hnearN
  have hdist : (zdist ((Gauss.band d).L N) (x - y) : ℝ) ≤
      (zdist ((Gauss.band d).L N) (x' - y) : ℝ) + 1 := by linarith
  have hα : 0 ≤ ctAlpha := ctAlpha_pos.le
  have hentry (a b : ZMod ((Gauss.band d).L N)) (pa qb : Fin ((Gauss.band d).W N))
      (hd : (zdist ((Gauss.band d).L N) (x - y) : ℝ) ≤
        (zdist ((Gauss.band d).L N) (a - b) : ℝ) + 1) :
      ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (a, pa) (b, qb)‖ ^ 2 ≤
        tailT ((Gauss.band d).W N : ℝ) ℓ η 60 (zdist ((Gauss.band d).L N) (x - y)) := by
    let r : ℕ := zdist ((Gauss.band d).L N) (x - y)
    let s : ℕ := zdist ((Gauss.band d).L N) (a - b)
    have hs : (r : ℝ) - 1 ≤ (s : ℝ) := by simpa [r, s] using (sub_le_iff_le_add.mpr hd)
    have hexp : Real.exp (-2 * ctAlpha * (s : ℝ)) ≤
        Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hgreen : ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (a, pa) (b, qb)‖ ≤
        4 * Real.exp (-ctAlpha * (s : ℝ)) := by simpa only [s] using hdecay a b pa qb
    have hsq : ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (a, pa) (b, qb)‖ ^ 2 ≤
        16 * Real.exp (-2 * ctAlpha * (s : ℝ)) := by
      calc
        ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (a, pa) (b, qb)‖ ^ 2
            ≤ (4 * Real.exp (-ctAlpha * (s : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hgreen 2
        _ = 16 * Real.exp (-2 * ctAlpha * (s : ℝ)) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num
          ring
    have hpow := hfloor r (by simpa [r] using hxy)
    have htail := rpow_neg_le_tailT
      (W := ((Gauss.band d).W N : ℝ)) (ℓu := ℓ) (ηu := η) (D := (60 : ℝ)) r
    calc
      ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (a, pa) (b, qb)‖ ^ 2
          ≤ 16 * Real.exp (-2 * ctAlpha * (s : ℝ)) := hsq
      _ ≤ 16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ ((Gauss.band d).W N : ℝ) ^ (-(60 : ℝ)) := hpow
      _ ≤ tailT ((Gauss.band d).W N : ℝ) ℓ η 60 r := htail
  constructor
  · simpa only [one_mul] using hentry y x' p q (by
      rw [Lemma57.zdist_sub_comm ((Gauss.band d).L N) y x']
      exact hdist)
  · simpa only [one_mul] using hentry x' y p q hdist

/-- The deterministic estimate is uniform over the whole first-cell time
interval once the Combes--Thomas entry estimate and the numerical floor
comparison are uniform there. -/
theorem all_time_jG_le_two_of_green_decay
    (N : ℕ) (ω : Gauss.Ω d)
    (hdecay : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ (x y : ZMod ((Gauss.band d).L N))
        (p q : Fin ((Gauss.band d).W N)),
        ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (x, p) (y, q)‖ ≤
          4 * Real.exp (-ctAlpha *
            (zdist ((Gauss.band d).L N) (x - y) : ℝ)))
    (hfloor : ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ r : ℕ,
      ellStar ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N u) / 2 ≤ (r : ℝ) →
      16 * Real.exp (-2 * ctAlpha * ((r : ℝ) - 1)) ≤
        ((Gauss.band d).W N : ℝ) ^ (-(60 : ℝ))) :
    ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      APrimeJG.jG (Gauss.sample d) 0 N u ω
        ((Gauss.band d).ell N u) (etaT 0 u) 60 ≤ 2 := by
  intro u hu
  exact jG_le_two_of_green_decay N u ω
    ((Gauss.band d).ell N u) (etaT 0 u) (hdecay u hu) (hfloor u hu)

/-- Event-level composition of the probabilistic block estimate, the
Combes--Thomas decay, and the literal `W⁻⁶⁰` floor comparison. -/
theorem highProb_all_time_jG_le_two_of_good
    (hgood : HighProb (Gauss.P d) good)
    (hdecay : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good N,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ (x y : ZMod ((Gauss.band d).L N))
        (p q : Fin ((Gauss.band d).W N)),
        ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (x, p) (y, q)‖ ≤
          4 * Real.exp (-ctAlpha *
            (zdist ((Gauss.band d).L N) (x - y) : ℝ))) :
    HighProb (Gauss.P d) (fun N =>
      {ω | ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        APrimeJG.jG (Gauss.sample d) 0 N u ω
          ((Gauss.band d).ell N u) (etaT 0 u) 60 ≤ 2}) := by
  refine HighProb.mono hgood ?_
  filter_upwards [hdecay, eventually_floor_bound] with N hdecayN hfloorN
  intro ω hω
  exact all_time_jG_le_two_of_green_decay N ω (hdecayN ω hω) hfloorN

theorem highProb_all_time_jG_le_two_of_adjacent_of_decay
    (hadjacent : HighProb (Gauss.P d) adjacentBlockEvent)
    (hdecay : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ good N,
      ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∀ (x y : ZMod ((Gauss.band d).L N))
        (p q : Fin ((Gauss.band d).W N)),
        ‖green ((Gauss.sample d).H N u ω) (zt 0 u) (x, p) (y, q)‖ ≤
          4 * Real.exp (-ctAlpha *
            (zdist ((Gauss.band d).L N) (x - y) : ℝ))) :
    HighProb (Gauss.P d) (fun N =>
      {ω | ∀ u ∈ Set.Icc (0 : ℝ) (1 / 2),
        APrimeJG.jG (Gauss.sample d) 0 N u ω
          ((Gauss.band d).ell N u) (etaT 0 u) 60 ≤ 2}) :=
  highProb_all_time_jG_le_two_of_good (highProb_good_of_adjacent hadjacent) hdecay

#print axioms ctAlpha_pos
#print axioms eventually_floor_bound
#print axioms measurableSet_good
#print axioms highProb_offBandEvent
#print axioms jG_le_two_of_green_decay
#print axioms all_time_jG_le_two_of_green_decay
#print axioms highProb_all_time_jG_le_two_of_good
#print axioms highProb_all_time_jG_le_two_of_adjacent_of_decay

end RBM.APrimeFirstCellJGAllTime
