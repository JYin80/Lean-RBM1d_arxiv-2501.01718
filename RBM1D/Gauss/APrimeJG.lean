/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeQVEndpoint
import RBM1D.Gauss.EntryBoundTime
import RBM1D.Gauss.GoodSetFlow
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Hierarchy.Step2FarInputs
import RBM1D.Gauss.APrimeGeneralMovingCarrierCore

/-!
# T280f: block-resolved Green control for (5.42)

The block maxima retain the spatial support of the Green entries.  The old global
`EarlyQVRateEv.jStar` does not have this property.
-/

namespace RBM
namespace APrimeJG

open Finset Real MeasureTheory Filter
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}




/-- `hGm`: a Green entry is bounded by its block maximum. -/
theorem norm_Gsig_le_gmBlk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (s : Bool) (x y : ZMod (B.L N)) (p q : Fin (B.W N)) :
    ‖Gsig (X.H N u ω) (zt E u) s (x, p) (y, q)‖ ≤ gmBlk X E N u ω x y :=
  Finset.le_sup' (f := fun z : Bool × Fin (B.W N) × Fin (B.W N) =>
    ‖Gsig (X.H N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖)
    (Finset.mem_univ (s, p, q))

/-- `hGm0`. -/
theorem gmBlk_nonneg (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) : 0 ≤ gmBlk X E N u ω x y :=
  (norm_nonneg _).trans (norm_Gsig_le_gmBlk X E N u ω true x y
    ⟨0, B.W_pos N⟩ ⟨0, B.W_pos N⟩)

/-- `hGsq0`. -/
theorem gsqBlk_nonneg (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) : 0 ≤ gsqBlk X E N u ω x y := by
  unfold gsqBlk
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : ZMod (B.L N))))
  split_ifs
  · exact mul_nonneg (gmBlk_nonneg X E N u ω _ _) (gmBlk_nonneg X E N u ω _ _)
  · exact le_rfl

private theorem SB_diag_ne_zero (N : ℕ) (x : ZMod (B.L N)) : SB (B.L N) x x ≠ 0 := by
  simp [SB_apply, sbKernel, sbSupport]

/-- `hGsq2`: the `x'=x` term is present in the neighbour maximum. -/
theorem gmBlk_mul_swap_le_gsqBlk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) :
    gmBlk X E N u ω x y * gmBlk X E N u ω y x ≤ gsqBlk X E N u ω x y := by
  unfold gsqBlk
  have h := Finset.le_sup'
    (s := (Finset.univ : Finset (ZMod (B.L N))))
    (f := fun x' => if SB (B.L N) x x' ≠ 0 then
      gmBlk X E N u ω y x' * gmBlk X E N u ω x' y else 0)
    (Finset.mem_univ x)
  simpa [SB_diag_ne_zero (B := B) N x, mul_comm] using h

/-- `hrow`: a nonzero row coefficient selects precisely one term of the maximum. -/
theorem gmBlk_row_le_gsqBlk (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x bb bb' : ZMod (B.L N)) (hbb : SB (B.L N) bb bb' ≠ 0) :
    gmBlk X E N u ω x bb' * gmBlk X E N u ω bb' x
      ≤ gsqBlk X E N u ω bb x := by
  unfold gsqBlk
  exact le_trans (le_of_eq (by simp [hbb]))
    (Finset.le_sup' _ (Finset.mem_univ bb'))

theorem one_le_jG (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    {ℓu ηu D : ℝ} (hW : (0 : ℝ) < (B.W N : ℝ)) :
    1 ≤ jG X E N u ω ℓu ηu D := by
  have h0 : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
        then gsqBlk X E N u ω p.1 p.2 /
          tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ ((0 : ZMod (B.L N)),
      (0 : ZMod (B.L N)))))
    dsimp only
    split
    · exact div_nonneg (gsqBlk_nonneg X E N u ω _ _)
        (tailT_pos hW _).le
    · exact le_rfl
  unfold jG
  linarith

/-- `h42sq` for the block-resolved control. -/
theorem gsqBlk_le_jG_mul_tailT (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    {ℓu ηu D : ℝ} (hW : (0 : ℝ) < (B.W N : ℝ))
    (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ)) :
    gsqBlk X E N u ω x y ≤ jG X E N u ω ℓu ηu D *
      tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
  let T := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))
  have hT : 0 < T := tailT_pos hW _
  have hsup : gsqBlk X E N u ω x y / T ≤
      (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
        then gsqBlk X E N u ω p.1 p.2 /
          tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (x, y)))
    dsimp only
    split
    · rfl
    · rename_i hn
      exact absurd hxy hn
  have hle : gsqBlk X E N u ω x y / T ≤ jG X E N u ω ℓu ηu D := by
    unfold jG
    linarith
  have := mul_le_mul_of_nonneg_right hle hT.le
  simpa [T, div_mul_cancel₀ _ hT.ne'] using this

/-- The block maximum obeys the deterministic resolvent norm bound. -/
theorem gmBlk_le_inv_etaT (X : Sample B) {E : ℝ} (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu : u < 1) (ω : Ω) (x y : ZMod (B.L N)) :
    gmBlk X E N u ω x y ≤ (etaT E u)⁻¹ := by
  have hη : 0 < etaT E u := Gauss.etaT_pos_of_lt_one' hE hu
  have hzim : (zt E u).im ≠ 0 := by
    rw [SumZeroDyn.zt_im_eq]
    exact hη.ne'
  unfold gmBlk
  refine Finset.sup'_le _ _ (fun z _ => ?_)
  calc ‖Gsig (X.H N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖
      ≤ ‖Gsig (X.H N u ω) (zt E u) z.1‖ := norm_apply_le_l2_opNorm _ _ _
    _ ≤ |(zt E u).im|⁻¹ := norm_Gsig_le (X.hermitian N u ω) hzim z.1
    _ = (etaT E u)⁻¹ := by rw [SumZeroDyn.zt_im_eq, abs_of_pos hη]

/-- The requested deterministic global cap, retained only as a cap on the block witness. -/
theorem gsqBlk_le_inv_etaT_sq (X : Sample B) {E : ℝ} (hE : |E| < 2)
    (N : ℕ) {u : ℝ} (hu : u < 1) (ω : Ω) (x y : ZMod (B.L N)) :
    gsqBlk X E N u ω x y ≤ (etaT E u)⁻¹ ^ 2 := by
  have hη : 0 < etaT E u := Gauss.etaT_pos_of_lt_one' hE hu
  have hηi : 0 ≤ (etaT E u)⁻¹ := (inv_pos.mpr hη).le
  unfold gsqBlk
  refine Finset.sup'_le _ _ (fun x' _ => ?_)
  split_ifs
  · have h1 := gmBlk_le_inv_etaT X hE N hu ω y x'
    have h2 := gmBlk_le_inv_etaT X hE N hu ω x' y
    nlinarith [gmBlk_nonneg X E N u ω y x', gmBlk_nonneg X E N u ω x' y,
      mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  · exact sq_nonneg _

/-- A nonzero block covariance coefficient has nearest-neighbour support. -/
theorem mem_sbSupport_of_SB_ne_zero {L : ℕ} {x x' : ZMod L}
    (h : SB L x x' ≠ 0) : x - x' ∈ sbSupport L := by
  rw [SB_apply, sbKernel] at h
  by_contra hnot
  simp [hnot] at h

/-- The block pair in each `(4.2)` summand is still far.  The three lattice steps
are: one in the row of `SB`, and one at each end of `Lre`. -/
theorem shifted_pair_far {L : ℕ} (hL : 3 ≤ L) {x y x' a b : ZMod L}
    (hxx' : SB L x x' ≠ 0) (ha : a ∈ sbSupport L) (hb : b ∈ sbSupport L)
    {ℓstar : ℝ} (hbig : 12 ≤ ℓstar)
    (hxy : ℓstar / 2 ≤ (zdist L (x - y) : ℝ)) :
    ℓstar / 4 ≤ (zdist L ((y + b) - (x' + a)) : ℝ) := by
  letI : NeZero L := ⟨by omega⟩
  have hmem := mem_sbSupport_of_SB_ne_zero hxx'
  have hnearN : zdist L (x - x') ≤ 1 := zdist_le_one_of_mem_sbSupport L hL hmem
  have hnear : (zdist L (x - x') : ℝ) ≤ 1 := by exact_mod_cast hnearN
  have htri := zdist_sub_le_add L x y x'
  have hswap : zdist L (y - x') = zdist L (x' - y) := Lemma57.zdist_sub_comm L y x'
  have hshiftN := Decay.zdist_le_add_two L hL (u := x' - y) ha hb
  have hshift : (zdist L (x' - y) : ℝ) ≤
      (zdist L ((x' + a) - (y + b)) : ℝ) + 2 := by
    have hshiftN' : zdist L (x' - y) ≤ zdist L ((x' + a) - (y + b)) + 2 := by
      convert hshiftN using 1 <;> ring
    exact_mod_cast hshiftN'
  have hrev : zdist L ((x' + a) - (y + b)) = zdist L ((y + b) - (x' + a)) :=
    Lemma57.zdist_sub_comm L _ _
  rw [hrev] at hshift
  rw [hswap] at htri
  linarith

/-- The matching upper distance estimate for the same three block shifts. -/
theorem shifted_pair_dist_le {L : ℕ} (hL : 3 ≤ L) {x y x' a b : ZMod L}
    (hxx' : SB L x x' ≠ 0) (ha : a ∈ sbSupport L) (hb : b ∈ sbSupport L) :
    (zdist L ((y + b) - (x' + a)) : ℝ) ≤ (zdist L (x - y) : ℝ) + 3 := by
  letI : NeZero L := ⟨by omega⟩
  have hmem := mem_sbSupport_of_SB_ne_zero hxx'
  have hnearN : zdist L (x - x') ≤ 1 := zdist_le_one_of_mem_sbSupport L hL hmem
  have hnear : (zdist L (x - x') : ℝ) ≤ 1 := by exact_mod_cast hnearN
  have htri := zdist_sub_le_add L y x' x
  have hswap : zdist L (y - x) = zdist L (x - y) := Lemma57.zdist_sub_comm L y x
  rw [hswap] at htri
  have hnear' : zdist L (x' - x) = zdist L (x - x') :=
    Lemma57.zdist_sub_comm L x' x
  rw [hnear'] at htri
  have hshiftN := Decay.zdist_le_add_two L hL
    (u := (y + b) - (x' + a))
    (v := -b) (w := -a)
    ((neg_mem_sbSupport L).2 hb) ((neg_mem_sbSupport L).2 ha)
  have hshiftN' : zdist L ((y + b) - (x' + a)) ≤ zdist L (y - x') + 2 := by
    convert hshiftN using 1 <;> ring
  have hshift : (zdist L ((y + b) - (x' + a)) : ℝ) ≤ zdist L (y - x') + 2 := by
    exact_mod_cast hshiftN'
  linarith

/-- Distance can decrease by at most three under the row and endpoint shifts. -/
theorem shifted_pair_dist_ge {L : ℕ} (hL : 3 ≤ L) {x y x' a b : ZMod L}
    (hxx' : SB L x x' ≠ 0) (ha : a ∈ sbSupport L) (hb : b ∈ sbSupport L) :
    (zdist L (x - y) : ℝ) ≤ (zdist L ((y + b) - (x' + a)) : ℝ) + 3 := by
  letI : NeZero L := ⟨by omega⟩
  have hmem := mem_sbSupport_of_SB_ne_zero hxx'
  have hnearN : zdist L (x - x') ≤ 1 := zdist_le_one_of_mem_sbSupport L hL hmem
  have hnear : (zdist L (x - x') : ℝ) ≤ 1 := by exact_mod_cast hnearN
  have htri := zdist_sub_le_add L x y x'
  have hswap : zdist L (y - x') = zdist L (x' - y) := Lemma57.zdist_sub_comm L y x'
  rw [hswap] at htri
  have hshiftN := Decay.zdist_le_add_two L hL (u := x' - y) ha hb
  have hshiftN' : zdist L (x' - y) ≤ zdist L ((x' + a) - (y + b)) + 2 := by
    convert hshiftN using 1 <;> ring
  have hshift : (zdist L (x' - y) : ℝ) ≤
      zdist L ((y + b) - (x' + a)) + 2 := by
    rw [Lemma57.zdist_sub_comm L (x'+a) (y+b)] at hshiftN'
    exact_mod_cast hshiftN'
  linarith

/-- The far geometry threshold is eventually uniform along a nonnegative flow window. -/
theorem eventually_twelve_le_ellStar {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hst : ∀ N, s N ≤ t N) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      12 ≤ ellStar (B.W N : ℝ) (B.ell N (u : ℝ)) := by
  have hW := Step2.tendsto_W B
  have hlog : Tendsto (fun N => Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_log_atTop.comp hW)
  filter_upwards [hlog.eventually_ge_atTop 12, hW.eventually_ge_atTop 1] with
    N h12 hW1 u
  have hℓ : 1 ≤ B.ell N (u : ℝ) :=
    one_le_ellHat_of_nonneg (B.one_le_L N) ((hs0 N).trans u.2.1)
      (u.2.2.trans_lt (ht1 N))
  unfold ellStar
  have hlog0 : 0 ≤ Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (Real.log_nonneg hW1) _
  nlinarith

/-- A neighbour of a far block is outside the support of the block covariance. -/
theorem far_neighbor_not_support {L : ℕ} (hL : 3 ≤ L) {x y x' : ZMod L}
    (hxx' : SB L x x' ≠ 0) {ℓstar : ℝ} (hbig : 12 ≤ ℓstar)
    (hxy : ℓstar / 2 ≤ (zdist L (x - y) : ℝ)) :
    x' - y ∉ sbSupport L := by
  letI : NeZero L := ⟨by omega⟩
  intro hmem
  have hnear1 : zdist L (x - x') ≤ 1 :=
    zdist_le_one_of_mem_sbSupport L hL (mem_sbSupport_of_SB_ne_zero hxx')
  have hnear2 : zdist L (x' - y) ≤ 1 :=
    zdist_le_one_of_mem_sbSupport L hL hmem
  have htri := zdist_add_le L (x - x') (x' - y)
  have heq : x - x' + (x' - y) = x - y := by ring
  rw [heq] at htri
  have htri' : (zdist L (x - y) : ℝ) ≤ 2 := by exact_mod_cast (htri.trans (by omega))
  linarith

/-- The shifted `Lre` term in (4.2) is controlled by `jS` as soon as the
shifted block pair lies in the far region. -/
theorem eventually_Lre_le_jS_mul_tailT {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (X : Sample B) (hc : Cond272 B E s t) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : TimeIcc s t N) (ω : Ω)
      (x y : ZMod (B.L N)),
      ellStar (B.W N : ℝ) (B.ell N (u : ℝ)) / 2 ≤
          (zdist (B.L N) (x - y) : ℝ) →
      Lre (X.H N (u : ℝ) ω) (zt E (u : ℝ)) x y ≤
        Step2.jS X E D N (u : ℝ) ω *
          Step2.tT B E N D (u : ℝ) (zdist (B.L N) (x - y)) := by
  filter_upwards [Step2FarInputs.eventually_norm_Kval_pm_le_tT
    hE hs0 hst ht1 hc D] with N hK u ω x y hfar
  rw [← norm_gloop_pm_eq_Lre (X.hermitian N (u : ℝ) ω) x y]
  exact Step2FarInputs.norm_gloop_pm_le_jS_mul_tT X E D N (u : ℝ) ω x y
    (hK u x y hfar)

/-- The same bridge at the quarter-radius needed after the three block shifts in (4.2). -/
theorem eventually_Lre_le_jS_mul_tailT_quarter {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (X : Sample B) (hc : Cond272 B E s t) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : TimeIcc s t N) (ω : Ω)
      (x y : ZMod (B.L N)),
      ellStar (B.W N : ℝ) (B.ell N (u : ℝ)) / 4 ≤
          (zdist (B.L N) (x - y) : ℝ) →
      Lre (X.H N (u : ℝ) ω) (zt E (u : ℝ)) x y ≤
        Step2.jS X E D N (u : ℝ) ω *
          Step2.tT B E N D (u : ℝ) (zdist (B.L N) (x - y)) := by
  filter_upwards [Step2.eq530 hE hs0 hst ht1 hc (δ := 1 / 4) (D := D)
    (by norm_num)] with N hK u ω x y hfar
  rw [← norm_gloop_pm_eq_Lre (X.hermitian N (u : ℝ) ω) x y]
  apply Step2FarInputs.norm_gloop_pm_le_jS_mul_tT X E D N (u : ℝ) ω x y
  exact (Step2FarInputs.norm_Kval_pm_le_norm_Theta hE.le B N (u : ℝ) x y).trans
    ((hK u x y (by simpa [one_div, inv_mul_eq_div] using hfar)).1.trans
      (rpow_neg_le_tailT _))

/-- Three nearest-neighbour shifts cost a fixed factor in the stretched-exponential tail. -/
theorem tailT_shift_three {W ℓu ηu D d₁ d₂ : ℝ} (hW : 0 ≤ W) (hℓu : 1 ≤ ℓu)
    (hshift : d₂ ≤ d₁ + 3) :
    tailT W ℓu ηu D d₁ ≤
      Real.exp (Real.sqrt 3) * tailT W ℓu ηu D d₂ := by
  have hℓpos : 0 < ℓu := by linarith
  have hdiv : d₂ / ℓu ≤ d₁ / ℓu + 3 := by
    have hthree : 3 / ℓu ≤ (3 : ℝ) := (div_le_iff₀ hℓpos).2 (by nlinarith)
    have := (div_le_div_of_nonneg_right hshift hℓpos.le)
    rw [add_div] at this
    linarith
  have hsqrt := Real.sqrt_le_sqrt hdiv
  have hkey : Real.sqrt (d₂ / ℓu) ≤ Real.sqrt (d₁ / ℓu) + Real.sqrt 3 :=
    hsqrt.trans (sqrt_add_le_add_sqrt _ (by norm_num))
  have he : Real.exp (-Real.sqrt (d₁ / ℓu)) ≤
      Real.exp (Real.sqrt 3) * Real.exp (-Real.sqrt (d₂ / ℓu)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hA : 0 ≤ ((W * ℓu * ηu) ^ 2)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW _
  unfold tailT
  have hmul := mul_le_mul_of_nonneg_left he hA
  have hexp : 1 ≤ Real.exp (Real.sqrt 3) := Real.one_le_exp (Real.sqrt_nonneg _)
  nlinarith

/-- Both charges reduce to a plus-resolvent entry, with reversed indices for minus. -/
theorem norm_Gsig_eq_green_or_swap {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (z : ℂ) (s : Bool) (i j : n) :
    ‖Gsig H z s i j‖ =
      if s then ‖green H z i j‖ else ‖green H z j i‖ := by
  cases s
  · have h := congrArg (fun M : Matrix n n ℂ => M i j)
      (Gsig_conjTranspose hH z true)
    simp only [Bool.not_true, Gsig_true, Matrix.conjTranspose_apply] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← h, norm_star]
  · simp

/-- Lift a pointwise square bound through the finite block maximum. -/
theorem gmBlk_sq_le_of_entry_sq_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (s : Bool) (p q : Fin (B.W N)),
      ‖Gsig (X.H N u ω) (zt E u) s (x, p) (y, q)‖ ^ 2 ≤ C) :
    gmBlk X E N u ω x y ^ 2 ≤ C := by
  have hmax : gmBlk X E N u ω x y ≤ Real.sqrt C := by
    unfold gmBlk
    refine Finset.sup'_le _ _ (fun z _ => ?_)
    have hz := h z.1 z.2.1 z.2.2
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C, norm_nonneg
      (Gsig (X.H N u ω) (zt E u) z.1 (x, z.2.1) (y, z.2.2))]
  nlinarith [Real.sq_sqrt hC, gmBlk_nonneg X E N u ω x y]

/-- Two oppositely oriented block entries bounded in square control their product. -/
theorem gmBlk_mul_le_of_sq_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N)) {C : ℝ}
    (hxy : gmBlk X E N u ω x y ^ 2 ≤ C)
    (hyx : gmBlk X E N u ω y x ^ 2 ≤ C) :
    gmBlk X E N u ω x y * gmBlk X E N u ω y x ≤ C := by
  nlinarith [sq_nonneg (gmBlk X E N u ω x y - gmBlk X E N u ω y x)]

/-- The nine shifted `(4.2)` loop terms cost only a constant for a far block pair. -/
theorem sum_shifted_control_le_jS_tail (X : Sample B) (E D : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω) (F : ZMod (B.L N) → ZMod (B.L N) → ℝ)
    (hℓ : 1 ≤ B.ell N u)
    (hstar : 12 ≤ ellStar (B.W N : ℝ) (B.ell N u))
    (hF : ∀ a b : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 4 ≤ (zdist (B.L N) (a - b) : ℝ) →
      F a b ≤
        Step2.jS X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (a - b)))
    {x y x' : ZMod (B.L N)} (hxx' : SB (B.L N) x x' ≠ 0)
    (hxy : ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤
      (zdist (B.L N) (x - y) : ℝ)) :
    (∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
      F (y + b) (x' + a)) ≤
      9 * Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω *
        Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
  have hW : (0 : ℝ) ≤ B.W N := by positivity
  have hJ : 0 ≤ Step2.jS X E D N u ω :=
    (Step2Moment.one_le_jS X N u ω).trans' (by norm_num)
  have hterm : ∀ a ∈ sbSupport (B.L N), ∀ b ∈ sbSupport (B.L N),
      F (y + b) (x' + a) ≤
        Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω *
          Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
    intro a ha b hb
    have hfar := shifted_pair_far (B.three_le_L N) hxx' ha hb hstar hxy
    have hdist := shifted_pair_dist_ge (B.three_le_L N)
      (x := x) (y := y) (x' := x') (a := a) (b := b) hxx' ha hb
    have htail : Step2.tT B E N D u (zdist (B.L N) ((y+b)-(x'+a))) ≤
        Real.exp (Real.sqrt 3) * Step2.tT B E N D u (zdist (B.L N) (x-y)) :=
      tailT_shift_three hW hℓ hdist
    calc F (y+b) (x'+a)
        ≤ Step2.jS X E D N u ω *
          Step2.tT B E N D u (zdist (B.L N) ((y+b)-(x'+a))) :=
          hF _ _ hfar
      _ ≤ Step2.jS X E D N u ω *
          (Real.exp (Real.sqrt 3) * Step2.tT B E N D u (zdist (B.L N) (x-y))) :=
          mul_le_mul_of_nonneg_left htail hJ
      _ = _ := by ring
  calc (∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
        F (y + b) (x' + a))
      ≤ ∑ a ∈ sbSupport (B.L N), ∑ _b ∈ sbSupport (B.L N),
          Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω *
            Step2.tT B E N D u (zdist (B.L N) (x - y)) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = _ := by simp [card_sbSupport (B.L N) (B.three_le_L N)]; ring

/-- The finite maxima introduce no further loss once each neighbouring Green entry is
controlled in both orientations. -/
theorem jG_le_of_neighbor_green_sq (X : Sample B) (E : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω) (ℓu ηu D F : ℝ)
    (hW : (0 : ℝ) < B.W N) (hF : 0 ≤ F)
    (hentry : ∀ (x y x' : ZMod (B.L N)),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      SB (B.L N) x x' ≠ 0 →
      ∀ (p q : Fin (B.W N)),
        ‖green (X.H N u ω) (zt E u) (y, p) (x', q)‖ ^ 2 ≤
            F * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) ∧
        ‖green (X.H N u ω) (zt E u) (x', p) (y, q)‖ ^ 2 ≤
            F * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    jG X E N u ω ℓu ηu D ≤ 1 + F := by
  have hG : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x-y) : ℝ) →
      gsqBlk X E N u ω x y ≤
        F * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x-y)) := by
    intro x y hxy
    unfold gsqBlk
    refine Finset.sup'_le _ _ (fun x' _ => ?_)
    split_ifs with hxx'
    · let T := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x-y))
      have hC : 0 ≤ F * T := mul_nonneg hF (tailT_pos hW _).le
      have hfirst : gmBlk X E N u ω y x' ^ 2 ≤ F * T := by
        apply gmBlk_sq_le_of_entry_sq_le X E N u ω y x' hC
        intro s p q
        rw [norm_Gsig_eq_green_or_swap (X.hermitian N u ω)]
        split
        · exact (hentry x y x' hxy hxx' p q).1
        · exact (hentry x y x' hxy hxx' q p).2
      have hsecond : gmBlk X E N u ω x' y ^ 2 ≤ F * T := by
        apply gmBlk_sq_le_of_entry_sq_le X E N u ω x' y hC
        intro s p q
        rw [norm_Gsig_eq_green_or_swap (X.hermitian N u ω)]
        split
        · exact (hentry x y x' hxy hxx' p q).2
        · exact (hentry x y x' hxy hxx' q p).1
      exact gmBlk_mul_le_of_sq_le X E N u ω y x' hfirst hsecond
    · exact mul_nonneg hF (tailT_pos hW _).le
  unfold jG
  have hsup : (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
        then gsqBlk X E N u ω p.1 p.2 /
          tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
        else 0) ≤ F := by
    refine Finset.sup'_le _ _ (fun p _ => ?_)
    split_ifs with hp
    · exact (div_le_iff₀ (tailT_pos hW _)).2 (hG p.1 p.2 hp)
    · exact hF
  linarith

/-- On a path where floored (4.2) holds for every off-diagonal entry, its neighbour
terms are controlled by the block-resolved loop bound. -/
theorem neighbor_green_sq_le_of_entry_event (X : Sample B) (E D τ : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω)
    (hℓ : 1 ≤ B.ell N u)
    (hstar : 12 ≤ ellStar (B.W N : ℝ) (B.ell N u))
    (hLre : ∀ a b : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 4 ≤ (zdist (B.L N) (a - b) : ℝ) →
      Lre (X.H N u ω) (zt E u) a b ≤
        Step2.jS X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (a - b)))
    (hentry : ∀ (i j : ZMod (B.L N) × Fin (B.W N)), i ≠ j →
      ‖green (X.H N u ω) (zt E u) i j‖ ^ 2 ≤
        (N : ℝ) ^ τ *
          ((∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
              Lre (X.H N u ω) (zt E u) (j.1 + b) (i.1 + a)) +
           (if i.1 - j.1 ∈ sbSupport (B.L N) then (B.W N : ℝ)⁻¹ else 0) +
           2 * (N : ℝ) ^ (-D)))
    (hfloor : ∀ x y : ZMod (B.L N),
      2 * (N : ℝ) ^ (-D) ≤
        2 * Step2.tT B E N D u (zdist (B.L N) (x-y)))
    {x y x' : ZMod (B.L N)} (hxx' : SB (B.L N) x x' ≠ 0)
    (hxy : ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤
      (zdist (B.L N) (x-y) : ℝ))
    (p q : Fin (B.W N)) :
    ‖green (X.H N u ω) (zt E u) (y,p) (x',q)‖ ^ 2 ≤
      (N : ℝ) ^ τ * (9 * Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω + 2) *
        Step2.tT B E N D u (zdist (B.L N) (x-y)) ∧
    ‖green (X.H N u ω) (zt E u) (x',p) (y,q)‖ ^ 2 ≤
      (N : ℝ) ^ τ * (9 * Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω + 2) *
        Step2.tT B E N D u (zdist (B.L N) (x-y)) := by
  have hnot : x' - y ∉ sbSupport (B.L N) :=
    far_neighbor_not_support (B.three_le_L N) hxx' hstar hxy
  have hnot' : y - x' ∉ sbSupport (B.L N) := by
    intro hmem
    have hneg := (neg_mem_sbSupport (B.L N)).2 hmem
    have heq : -(y - x') = x' - y := by ring
    rw [heq] at hneg
    exact hnot hneg
  have hne : x' ≠ y := by
    intro heq
    apply hnot
    simp [heq, sbSupport]
  have hnpow : 0 ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (by positivity) _
  have hsum₁ := sum_shifted_control_le_jS_tail X E D N u ω
    (Lre (X.H N u ω) (zt E u)) hℓ hstar hLre hxx' hxy
  have hLreOp : ∀ a b : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 4 ≤ (zdist (B.L N) (a-b) : ℝ) →
      Lre (X.H N u ω) (zt E u) b a ≤
        Step2.jS X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (a-b)) := by
    intro a b hab
    have heq : zdist (B.L N) (b-a) = zdist (B.L N) (a-b) :=
      Lemma57.zdist_sub_comm (B.L N) b a
    rw [← heq] at hab ⊢
    exact hLre b a hab
  have hsum₂raw := sum_shifted_control_le_jS_tail X E D N u ω
    (fun a b => Lre (X.H N u ω) (zt E u) b a)
    hℓ hstar hLreOp hxx' hxy
  have hsum₂ :
      (∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
        Lre (X.H N u ω) (zt E u) (x' + b) (y + a)) ≤
      9 * Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω *
        Step2.tT B E N D u (zdist (B.L N) (x-y)) := by
    calc
      (∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
        Lre (X.H N u ω) (zt E u) (x' + b) (y + a))
          = ∑ b ∈ sbSupport (B.L N), ∑ a ∈ sbSupport (B.L N),
              Lre (X.H N u ω) (zt E u) (x' + b) (y + a) := Finset.sum_comm
      _ ≤ _ := hsum₂raw
  constructor
  · have hi : (y,p) ≠ (x',q) := by
      intro heq
      exact hne (congrArg Prod.fst heq).symm
    have he := hentry (y,p) (x',q) hi
    simp only [hnot', ↓reduceIte] at he
    calc ‖green (X.H N u ω) (zt E u) (y,p) (x',q)‖ ^ 2
        ≤ (N : ℝ) ^ τ *
          ((∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
              Lre (X.H N u ω) (zt E u) (x' + b) (y + a)) +
            2 * (N : ℝ) ^ (-D)) := by simpa only [add_zero, zero_add] using he
      _ ≤ (N : ℝ) ^ τ *
          ((9 * Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω *
            Step2.tT B E N D u (zdist (B.L N) (x-y))) +
            2 * Step2.tT B E N D u (zdist (B.L N) (x-y))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hsum₂ (hfloor x y)) hnpow
      _ = _ := by ring
  · have hi : (x',p) ≠ (y,q) := by
      intro heq
      exact hne (congrArg Prod.fst heq)
    have he := hentry (x',p) (y,q) hi
    simp only [hnot, ↓reduceIte] at he
    calc ‖green (X.H N u ω) (zt E u) (x',p) (y,q)‖ ^ 2
        ≤ (N : ℝ) ^ τ *
          ((∑ a ∈ sbSupport (B.L N), ∑ b ∈ sbSupport (B.L N),
              Lre (X.H N u ω) (zt E u) (y + b) (x' + a)) +
            2 * (N : ℝ) ^ (-D)) := by simpa only [add_zero, zero_add] using he
      _ ≤ (N : ℝ) ^ τ *
          ((9 * Real.exp (Real.sqrt 3) * Step2.jS X E D N u ω *
            Step2.tT B E N D u (zdist (B.L N) (x-y))) +
            2 * Step2.tT B E N D u (zdist (B.L N) (x-y))) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hsum₁ (hfloor x y)) hnpow
      _ = _ := by ring

/-- The floored (4.2) event and the along-flow good event jointly control the block
witness at every time.  The only probabilistic inputs are exactly those two events. -/
theorem highProb_jG_le_of_entryBoundFlow (d : Gauss.Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (Gauss.band d) E s t)
    (D : ℝ) (hD : 0 ≤ D)
    (hEntry : Gauss.EntryBoundFlow' d E s t (fun N => 2 * (N : ℝ) ^ (-D)))
    (hGood : HighProb (Gauss.P d)
      (Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t)))
    {τ : ℝ} (hτ : 0 < τ) :
    HighProb (Gauss.P d) (fun N => {ω | ∀ u : TimeIcc s t N,
      jG (Gauss.sample d) E N (u : ℝ) ω
        ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D ≤
      1 + (N : ℝ) ^ τ *
        (9 * Real.exp (Real.sqrt 3) * Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2)}) := by
  have hEntryHP := hEntry.highProb hτ
  have hBoth := hEntryHP.inter hGood
  refine hBoth.mono ?_
  filter_upwards [eventually_Lre_le_jS_mul_tailT_quarter hE hs0 hst ht1 (Gauss.sample d) hc D,
    eventually_twelve_le_ellStar (B := Gauss.band d) hs0 ht1 hst,
    (Gauss.band d).dim, Filter.eventually_ge_atTop 1] with N hLre hstar hdim hN1 ω hω' u
  obtain ⟨hentryω, hgoodω⟩ := hω'
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hWpos : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hLpos : (1 : ℝ) ≤ (d.L N : ℝ) := by
    exact_mod_cast (Gauss.band d).one_le_L N
  have hWN : (d.W N : ℝ) ≤ N := by
    have hdim' : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hfloor : ∀ x y : ZMod (d.L N),
      2 * (N : ℝ) ^ (-D) ≤
        2 * Step2.tT (Gauss.band d) E N D (u : ℝ) (zdist (d.L N) (x-y)) := by
    intro x y
    have hWD : (N : ℝ) ^ (-D) ≤ (d.W N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_nonpos hWpos hWN (by linarith)
    have hT := rpow_neg_le_tailT (W := (d.W N : ℝ))
      (ℓu := (Gauss.band d).ell N (u : ℝ)) (ηu := etaT E (u : ℝ))
      (D := D) (zdist (d.L N) (x-y))
    dsimp [Step2.tT]
    linarith
  have hℓ : 1 ≤ (Gauss.band d).ell N (u : ℝ) :=
    one_le_ellHat_of_nonneg ((Gauss.band d).one_le_L N)
      ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hentryPoint : ∀ (i j : ZMod (d.L N) × Fin (d.W N)), i ≠ j →
      ‖green ((Gauss.sample d).H N (u : ℝ) ω) (zt E (u : ℝ)) i j‖ ^ 2 ≤
        (N : ℝ) ^ τ *
          ((∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
              Lre ((Gauss.sample d).H N (u : ℝ) ω) (zt E (u : ℝ)) (j.1 + b) (i.1 + a)) +
           (if i.1 - j.1 ∈ sbSupport (d.L N) then (d.W N : ℝ)⁻¹ else 0) +
           2 * (N : ℝ) ^ (-D)) := by
    intro i j hij
    have hmem : ω ∈ goodSet (L := d.L) (W := d.W)
        (fun N ω => Gauss.Hflow d N (u : ℝ) ω) (zt E (u : ℝ))
        (mE E) (Gauss.flowDelta d E t) N := hgoodω (u : ℝ) u.2
    have he := hentryω (u, (⟨(i,j), hij⟩ : OffPair d.L d.W N))
    simp only [Set.indicator_of_mem hmem] at he
    convert he using 1 <;> simp only [Gauss.sample_H, Gauss.band_L, Gauss.band_W]
    · rfl
  have hF0 : 0 ≤ (N : ℝ) ^ τ *
      (9 * Real.exp (Real.sqrt 3) * Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2) := by
    have hJ := Step2Moment.one_le_jS (Gauss.sample d) (E := E) (D := D) N (u : ℝ) ω
    positivity
  apply jG_le_of_neighbor_green_sq (Gauss.sample d) E N (u : ℝ) ω
    ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D
    ((N : ℝ) ^ τ *
      (9 * Real.exp (Real.sqrt 3) * Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2))
    (by simpa only [Gauss.band_W] using hWpos) hF0
  intro x y x' hxy hxx' p q
  exact neighbor_green_sq_le_of_entry_event (Gauss.sample d) E D τ N (u : ℝ) ω
    hℓ (hstar u) (hLre u ω) hentryPoint hfloor hxx' hxy p q

/-- The block-resolved `J` is stochastically dominated by `1+jS` on the whole flow
window.  The same along-flow good event works for both charges. -/
theorem stochDom_jG_of_entryBoundFlow (d : Gauss.Dims) {E : ℝ} (hE : |E| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (Gauss.band d) E s t)
    (D : ℝ) (hD : 0 ≤ D)
    (hEntry : Gauss.EntryBoundFlow' d E s t (fun N => 2 * (N : ℝ) ^ (-D)))
    (hGood : HighProb (Gauss.P d)
      (Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t))) :
    StochDom (Gauss.P d)
      (U := fun N => TimeIcc s t N)
      (fun N u ω => jG (Gauss.sample d) E N (u : ℝ) ω
        ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D)
      (fun N u ω => (9 * Real.exp (Real.sqrt 3) + 3) *
        (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)) := by
  intro τ hτ K hK
  have hτ2 : 0 < τ / 2 := by linarith
  have hHP := highProb_jG_le_of_entryBoundFlow d hE hs0 hst ht1 hc D hD
    hEntry hGood hτ2
  filter_upwards [hHP K hK, Filter.eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : 1 ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' hτ2.le
  have hNpow : (N : ℝ) ^ τ = (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add (by linarith : (0 : ℝ) < N)]
    congr 1
    ring
  calc
    Gauss.P d (badSet
      (fun N (u : TimeIcc s t N) ω => jG (Gauss.sample d) E N (u : ℝ) ω
        ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D)
      (fun N (u : TimeIcc s t N) ω => (9 * Real.exp (Real.sqrt 3) + 3) *
        (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)) τ N)
      ≤ Gauss.P d {ω | ¬ ∀ u : TimeIcc s t N,
          jG (Gauss.sample d) E N (u : ℝ) ω
            ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D ≤
          1 + (N : ℝ) ^ (τ / 2) *
            (9 * Real.exp (Real.sqrt 3) *
              Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2)} := by
        apply measure_mono
        intro ω hbad hgood
        obtain ⟨u, hu⟩ := hbad
        have hj := hgood u
        have hJ := Step2Moment.one_le_jS (Gauss.sample d) (E := E) (D := D)
          N (u : ℝ) ω
        let A := 9 * Real.exp (Real.sqrt 3)
        have hA : 0 ≤ A := by dsimp [A]; positivity
        let C := A + 3
        have hC : 0 ≤ C := by dsimp [C]; positivity
        have hctrl : 0 ≤ C * (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω) := by
          positivity
        have hbound : 1 + (N : ℝ) ^ (τ / 2) *
            (A * Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2) ≤
            (N : ℝ) ^ τ *
              (C * (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)) := by
          calc
            1 + (N : ℝ) ^ (τ / 2) *
                (A * Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 2)
              ≤ (N : ℝ) ^ (τ / 2) *
                  (A * Step2.jS (Gauss.sample d) E D N (u : ℝ) ω + 3) := by
                    nlinarith
            _ ≤ (N : ℝ) ^ (τ / 2) *
                  (C * (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)) := by
                    apply mul_le_mul_of_nonneg_left _ (by linarith)
                    dsimp [C]
                    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
                      (by linarith : 0 ≤ Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)]
            _ ≤ (N : ℝ) ^ τ *
                  (C * (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)) := by
                    rw [hNpow]
                    exact mul_le_mul_of_nonneg_right
                      (by nlinarith [sq_nonneg ((N : ℝ) ^ (τ / 2) - 1)]) hctrl
        exact (not_lt_of_ge (hj.trans hbound)) hu
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-K)) := hN

/-- Provider-level form: floored (4.2) and the along-flow Good event are produced with
the same Gaussian sample, window, and threshold. -/
theorem stochDom_jG_of_localLaw (d : Gauss.Dims) {E : ℝ} (hE : |E| < 2)
    {s t Ψ : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 (Gauss.band d) E s t)
    (D : ℝ) (hD : 0 ≤ D)
    {Kη c₀ Kll Bll τll : ℝ} (hKη : 0 ≤ Kη)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-Kη) ≤ etaT E (t N))
    (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop,
      Gauss.flowDelta d E t N ≤ (N : ℝ) ^ (-c₀))
    (hτll : 0 < τll) (hKll : 0 ≤ Kll) (hBll : 0 ≤ Bll)
    (hKbig : ∀ᶠ N : ℕ in atTop,
      (etaT E (t N))⁻¹ * (etaT E (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ Kll)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-Bll) ≤ Ψ N)
    (hll : Gauss.LocalLawUnifIcc d E s t Ψ)
    (hmargin : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ τll * Ψ N ≤ Gauss.flowDelta d E t N) :
    StochDom (Gauss.P d)
      (U := fun N => TimeIcc s t N)
      (fun N u ω => jG (Gauss.sample d) E N (u : ℝ) ω
        ((Gauss.band d).ell N (u : ℝ)) (etaT E (u : ℝ)) D)
      (fun N u ω => (9 * Real.exp (Real.sqrt 3) + 3) *
        (1 + Step2.jS (Gauss.sample d) E D N (u : ℝ) ω)) := by
  exact stochDom_jG_of_entryBoundFlow d hE hs0 hst ht1 hc D hD
    (Gauss.entryBoundFlow_floor d hE hs0 hst ht1 hKη hη hc₀ hδ hD)
    (Gauss.highProb_goodSetFlow_of_localLaw d hτll hE hs0 ht1 hst
      hKll hBll hKbig hΨ0 hΨlow hll hmargin)

/-- Anti-vacuity of the two events used in the probabilistic lift. -/
theorem eventually_joint_entry_good_nonempty (d : Gauss.Dims) {E : ℝ}
    {s t : ℕ → ℝ} {D : ℝ}
    (hEntry : Gauss.EntryBoundFlow' d E s t (fun N => 2 * (N : ℝ) ^ (-D)))
    (hGood : HighProb (Gauss.P d)
      (Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t))) :
    ∀ᶠ N : ℕ in atTop,
      ({ω | ∀ p : TimeIcc s t N × OffPair d.L d.W N,
        (goodSet (L := d.L) (W := d.W)
          (fun N ω => Gauss.Hflow d N (p.1 : ℝ) ω)
          (zt E (p.1 : ℝ)) (mE E) (Gauss.flowDelta d E t) N).indicator
            (fun ω => ‖green (Gauss.Hflow d N (p.1 : ℝ) ω)
              (zt E (p.1 : ℝ)) p.2.1.1 p.2.1.2‖ ^ 2) ω ≤
        (N : ℝ) ^ (1 : ℝ) *
          ((∑ a ∈ sbSupport (d.L N), ∑ b ∈ sbSupport (d.L N),
              Lre (Gauss.Hflow d N (p.1 : ℝ) ω)
                (zt E (p.1 : ℝ)) (p.2.1.2.1 + b) (p.2.1.1.1 + a)) +
           (if p.2.1.1.1 - p.2.1.2.1 ∈ sbSupport (d.L N)
              then (d.W N : ℝ)⁻¹ else 0) +
           2 * (N : ℝ) ^ (-D))} ∩
        Gauss.goodSetFlow d E s t (Gauss.flowDelta d E t) N).Nonempty := by
  exact HighProb.nonempty (P := Gauss.P d) (by simp)
    ((hEntry.highProb (by norm_num : (0 : ℝ) < 1)).inter hGood)

end APrimeJG
end RBM
