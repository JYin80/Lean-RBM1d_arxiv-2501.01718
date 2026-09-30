/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.FullQuadVar
import RBM1D.Gauss.RawSources
import RBM1D.Gauss.CenteredOneLoopAllTime
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Gauss.LoopC2

set_option maxHeartbeats 1000000

/-!
# The good set `G_j` of σ, as matrix sets, and its `HighProb` on the grid

The stopped Duhamel argument of `GridDuhamelTail.lean` needs deterministic constants on `{j < τ}`,
but the quadratic-variation and drift bounds come from *flow-level* `HighProb` events. So the
stopping time must also stop when the grid state leaves a good set `G_j`, defined here as a
measurable set of matrices, with `HighProb (Pg d) {∀ k ≤ K, H_k ∈ G_{u_k}}` transferred from the
flow via `highProb_grid_of_flow` (`Gauss/GridJStar.lean`), exactly as `GridJStar.lean` does for
`eq273Set`/`eq557Set`.

## `qvSet` and the raw/regularised bridge

`quadVar (band d).toDims N (fun M' => lkFun ... M' sigPM a) M`, the target quantity, is a
*derivative* of the raw (unregularised) loop `gloop`; `TestFunHerm.lean` shows this raw function
is **not** globally `TestFun` (the resolvent is discontinuous off the Hermitian set), so its
`quadVar` is not obviously measurable on the whole matrix space. `qvVal` below is the exact same
quantity **at every Hermitian `M`** — in particular at every `M` that is ever actually produced by
`Hflow` — and is `0` off the Hermitian set (an arbitrary, harmless value there, never evaluated in
any downstream use, since `Hflow` is always Hermitian, `Hflow_isHermitian`); measurability follows
because at Hermitian `M` it agrees with `quadVar` of the Hermitian *regularisation* `loopObs`
(`EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs`), which is `TestFun`, hence continuous, on the
**whole** matrix space (`RBM.Gauss.testFun_loopObs_of_im_le`).  The pattern is that of
`Grid.continuous_coordD2_arg`, one derivative level down.

## `h554Set`: a fully general (`∀ a₁ a₂`) deterministic (5.54) bound with a `W^{-D}` size

The (5.54) bound is needed **unconditionally** in `a₁, a₂`, while a near-triple bound applies
only when `a₁, a₂` are *near* each other. `h554Set` is therefore proved from the deterministic
(5.60) bound `Lemma57.norm_gloop_three_le` plus a two-far-factor split: for `‖a₂-b‖ > ℓ**`, the
triangle inequality gives `‖a₂-a₁‖ ≥ ℓ**/2` or `‖a₁-b‖ > ℓ**/2`, so **two** of the three
Green-function factors are far (bounded by `√(J T)` through `jGMat`), and only one is capped by
`η_u⁻¹` (`RBM.norm_Gsig_le`). The bound `rho554 d E N u D J = η_u⁻¹ J √(T(ℓ**) T(ℓ**/2))` is an
explicit deterministic function of `(E, N, u, D, J)`, evaluated at `J := jGMat … M`, and is
`≤ 2 η_u⁻¹ J W^{-D}` once `2D² ≤ log W` (`rho554_le_two_mul_rpow`).

## Main results

* `jGMat`, `measurable_jGMat`, `jG_eq_jGMat`.
* `qvSet`, `jgSet`, `h554Set` (with `rho554`, `rho554_mono`, `rho554_le_two_mul_rpow`,
  `mem_h554Set_of_isHermitian`), `honeSet`, `goodSet`, and their `measurableSet_…` lemmas.
* `highProb_flow_restrict`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped Matrix.Norms.L2Operator

variable (d : Dims)

/-! ## T1 : `jGMat`, the matrix form of `BlockGreen.jG` -/

/-- The matrix form of `BlockGreen.gmBlk`. -/
private noncomputable def gmBlkMat (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (x y : ZMod (d.L N)) : ℝ :=
  (Finset.univ : Finset (Bool × Fin (d.W N) × Fin (d.W N))).sup'
    ⟨(true, ⟨0, d.W_pos N⟩, ⟨0, d.W_pos N⟩), Finset.mem_univ _⟩
    (fun z => ‖Gsig M (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖)

/-- The matrix form of `BlockGreen.gsqBlk`. -/
private noncomputable def gsqBlkMat (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (x y : ZMod (d.L N)) : ℝ :=
  (Finset.univ : Finset (ZMod (d.L N))).sup'
    ⟨0, Finset.mem_univ _⟩
    (fun x' => if SB (d.L N) x x' ≠ 0 then
      gmBlkMat d E N u M y x' * gmBlkMat d E N u M x' y else 0)

/-- `jGMat` is `BlockGreen.jG`'s formula with the matrix `M` taken directly as input,
instead of going through a `Sample`'s `ω`; exactly as `jSMat` is for `Step2.jS`. -/
noncomputable def jGMat (E : ℝ) (N : ℕ) (u : ℝ) (ℓu ηu D : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  1 + (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N))).sup'
    ⟨(0, 0), Finset.mem_univ _⟩
    (fun p => if ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (p.1 - p.2) : ℝ)
      then gsqBlkMat d E N u M p.1 p.2 /
        tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (p.1 - p.2))
      else 0)

theorem measurable_gmBlkMat (E : ℝ) (N : ℕ) (u : ℝ) (x y : ZMod (d.L N)) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => gmBlkMat d E N u M x y) := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (z : Bool × Fin (d.W N) × Fin (d.W N)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        ‖Gsig M (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖)) :=
    Finset.measurable_sup' Finset.univ_nonempty fun z _ =>
      (measurable_Gsig_matrix d N (zt E u) z.1 (x, z.2.1) (y, z.2.2)).norm
  have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => gmBlkMat d E N u M x y) =
      Finset.univ.sup' Finset.univ_nonempty
      (fun (z : Bool × Fin (d.W N) × Fin (d.W N)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        ‖Gsig M (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖) := by
    funext M
    unfold gmBlkMat
    rw [Finset.sup'_apply]
  rw [heq]
  exact hsup

theorem measurable_gsqBlkMat (E : ℝ) (N : ℕ) (u : ℝ) (x y : ZMod (d.L N)) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => gsqBlkMat d E N u M x y) := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (x' : ZMod (d.L N)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        if SB (d.L N) x x' ≠ 0 then gmBlkMat d E N u M y x' * gmBlkMat d E N u M x' y
        else 0)) := by
    refine Finset.measurable_sup' Finset.univ_nonempty fun x' _ => ?_
    split_ifs with h
    · exact (measurable_gmBlkMat d E N u y x').mul (measurable_gmBlkMat d E N u x' y)
    · exact measurable_const
  have heq : (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => gsqBlkMat d E N u M x y) =
      Finset.univ.sup' Finset.univ_nonempty
      (fun (x' : ZMod (d.L N)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        if SB (d.L N) x x' ≠ 0 then gmBlkMat d E N u M y x' * gmBlkMat d E N u M x' y
        else 0) := by
    funext M
    unfold gsqBlkMat
    rw [Finset.sup'_apply]
  rw [heq]
  exact hsup

theorem measurable_jGMat (E : ℝ) (N : ℕ) (u ℓu ηu D : ℝ) :
    Measurable (jGMat d E N u ℓu ηu D) := by
  have hsup : Measurable (Finset.univ.sup' Finset.univ_nonempty
      (fun (p : ZMod (d.L N) × ZMod (d.L N)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        if ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (p.1 - p.2) : ℝ)
          then gsqBlkMat d E N u M p.1 p.2 /
            tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (p.1 - p.2))
          else 0)) := by
    refine Finset.measurable_sup' Finset.univ_nonempty fun p _ => ?_
    split_ifs with h
    · exact (measurable_gsqBlkMat d E N u p.1 p.2).div_const _
    · exact measurable_const
  have heq : jGMat d E N u ℓu ηu D =
      (fun _ : Matrix (d.Idx N) (d.Idx N) ℂ => (1 : ℝ)) +
      Finset.univ.sup' Finset.univ_nonempty
      (fun (p : ZMod (d.L N) × ZMod (d.L N)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) =>
        if ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (p.1 - p.2) : ℝ)
          then gsqBlkMat d E N u M p.1 p.2 /
            tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (p.1 - p.2))
          else 0) := by
    funext M
    unfold jGMat
    rw [Pi.add_apply, Finset.sup'_apply]
  rw [heq]
  exact measurable_const.add hsup

/-- **(T1)** `jG` evaluated at `Hflow d N u ω` is literally `jGMat` at the same matrix — the
exact analogue of `jS_eq_jSMat`. -/
theorem jG_eq_jGMat (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω d) (ℓu ηu D : ℝ) :
    RBM.BlockGreen.jG (sample d) E N u ω ℓu ηu D = jGMat d E N u ℓu ηu D (Hflow d N u ω) := rfl

/-! ### The fully general (`∀ a₁ a₂`) crude bound for `h554Set`

Matrix-level mirrors of the `BlockGreen` algebra, needed because the (5.54) bound is required
unconditionally in `a₁, a₂` (see the module docstring). Every lemma here is either purely
`Finset.sup'` algebra (no Hermitian dependence, a direct mirror of the corresponding `BlockGreen`
fact) or takes `M.IsHermitian` directly (never through a `Sample`), matching
`RBM.norm_Gsig_le`/`RBM.BlockGreen.norm_Gsig_eq_green_or_swap`'s own signatures. -/

private theorem norm_Gsig_le_gmBlkMat (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (s : Bool) (x y : ZMod (d.L N)) (p q : Fin (d.W N)) :
    ‖Gsig M (zt E u) s (x, p) (y, q)‖ ≤ gmBlkMat d E N u M x y :=
  Finset.le_sup' (f := fun z : Bool × Fin (d.W N) × Fin (d.W N) =>
    ‖Gsig M (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖) (Finset.mem_univ (s, p, q))

private theorem gmBlkMat_nonneg (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x y : ZMod (d.L N)) : 0 ≤ gmBlkMat d E N u M x y :=
  (norm_nonneg _).trans
    (norm_Gsig_le_gmBlkMat d E N u M true x y ⟨0, d.W_pos N⟩ ⟨0, d.W_pos N⟩)

private theorem gsqBlkMat_nonneg (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (x y : ZMod (d.L N)) : 0 ≤ gsqBlkMat d E N u M x y := by
  unfold gsqBlkMat
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : ZMod (d.L N))))
  split_ifs
  · exact mul_nonneg (gmBlkMat_nonneg d E N u M _ _) (gmBlkMat_nonneg d E N u M _ _)
  · exact le_rfl

private theorem one_le_jGMat (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {ℓu ηu D : ℝ} : 1 ≤ jGMat d E N u ℓu ηu D M := by
  have h0 : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (p.1 - p.2) : ℝ)
        then gsqBlkMat d E N u M p.1 p.2 /
          tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ ((0 : ZMod (d.L N)), (0 : ZMod (d.L N)))))
    dsimp only
    split
    · exact div_nonneg (gsqBlkMat_nonneg d E N u M _ _)
        (tailT_pos (by exact_mod_cast d.W_pos N) _).le
    · exact le_rfl
  unfold jGMat
  linarith

private theorem SB_diag_ne_zero' (N : ℕ) (x : ZMod (d.L N)) : SB (d.L N) x x ≠ 0 := by
  simp [SB_apply, sbKernel, sbSupport]

private theorem gmBlkMat_mul_swap_le_gsqBlkMat (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (x y : ZMod (d.L N)) :
    gmBlkMat d E N u M x y * gmBlkMat d E N u M y x ≤ gsqBlkMat d E N u M x y := by
  unfold gsqBlkMat
  have h := Finset.le_sup' (s := (Finset.univ : Finset (ZMod (d.L N))))
    (f := fun x' => if SB (d.L N) x x' ≠ 0 then
      gmBlkMat d E N u M y x' * gmBlkMat d E N u M x' y else 0)
    (Finset.mem_univ x)
  simpa [SB_diag_ne_zero' d N x, mul_comm] using h

private theorem gsqBlkMat_le_jGMat_mul_tailT (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) {ℓu ηu D : ℝ} (x y : ZMod (d.L N))
    (hxy : ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (x - y) : ℝ)) :
    gsqBlkMat d E N u M x y ≤ jGMat d E N u ℓu ηu D M *
      tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y)) := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  let T := tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y))
  have hT : 0 < T := tailT_pos hW _
  have hsup : gsqBlkMat d E N u M x y / T ≤
      (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (p.1 - p.2) : ℝ)
        then gsqBlkMat d E N u M p.1 p.2 /
          tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (x, y)))
    dsimp only
    split
    · rfl
    · rename_i hn
      exact absurd hxy hn
  have hle : gsqBlkMat d E N u M x y / T ≤ jGMat d E N u ℓu ηu D M := by
    unfold jGMat
    linarith
  have := mul_le_mul_of_nonneg_right hle hT.le
  simpa [T, div_mul_cancel₀ _ hT.ne'] using this

private theorem gmBlkMat_comm (E : ℝ) (N : ℕ) (u : ℝ) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (x y : ZMod (d.L N)) :
    gmBlkMat d E N u M x y = gmBlkMat d E N u M y x := by
  have hflip (s : Bool) (p q : Fin (d.W N)) :
      ‖Gsig M (zt E u) s (x, p) (y, q)‖ = ‖Gsig M (zt E u) (!s) (y, q) (x, p)‖ := by
    rw [RBM.BlockGreen.norm_Gsig_eq_green_or_swap hM, RBM.BlockGreen.norm_Gsig_eq_green_or_swap hM]
    cases s <;> rfl
  apply le_antisymm
  · change (Finset.univ : Finset (Bool × Fin (d.W N) × Fin (d.W N))).sup'
        ⟨(true, ⟨0, d.W_pos N⟩, ⟨0, d.W_pos N⟩), Finset.mem_univ _⟩
        (fun z => ‖Gsig M (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖) ≤ gmBlkMat d E N u M y x
    refine Finset.sup'_le _ _ (fun z _ => ?_)
    exact (hflip z.1 z.2.1 z.2.2).trans_le
      (norm_Gsig_le_gmBlkMat d E N u M (!z.1) y x z.2.2 z.2.1)
  · change (Finset.univ : Finset (Bool × Fin (d.W N) × Fin (d.W N))).sup'
        ⟨(true, ⟨0, d.W_pos N⟩, ⟨0, d.W_pos N⟩), Finset.mem_univ _⟩
        (fun z => ‖Gsig M (zt E u) z.1 (y, z.2.1) (x, z.2.2)‖) ≤ gmBlkMat d E N u M x y
    refine Finset.sup'_le _ _ (fun z _ => ?_)
    have h := hflip (!z.1) z.2.2 z.2.1
    simp only [Bool.not_not] at h
    exact h.symm.trans_le (norm_Gsig_le_gmBlkMat d E N u M (!z.1) x y z.2.2 z.2.1)

private theorem gmBlkMat_le_sqrt_jGMat_tail (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) {ℓu ηu D : ℝ}
    (x y : ZMod (d.L N)) (hxy : ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) (x - y) : ℝ)) :
    gmBlkMat d E N u M x y ≤
      Real.sqrt (jGMat d E N u ℓu ηu D M * tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y))) := by
  have hJ : 0 ≤ jGMat d E N u ℓu ηu D M := (one_le_jGMat d E N u M).trans' (by norm_num)
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hT : 0 ≤ tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y)) := (tailT_pos hW _).le
  have hsq : gmBlkMat d E N u M x y ^ 2 ≤
      jGMat d E N u ℓu ηu D M * tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y)) := by
    calc
      _ = gmBlkMat d E N u M x y * gmBlkMat d E N u M y x := by
            rw [← gmBlkMat_comm d E N u hM x y]; ring
      _ ≤ gsqBlkMat d E N u M x y := gmBlkMat_mul_swap_le_gsqBlkMat d E N u M x y
      _ ≤ _ := gsqBlkMat_le_jGMat_mul_tailT d E N u M x y hxy
  have hK : 0 ≤ jGMat d E N u ℓu ηu D M * tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y)) :=
    mul_nonneg hJ hT
  nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg
    (jGMat d E N u ℓu ηu D M * tailT (d.W N : ℝ) ℓu ηu D (zdist (d.L N) (x - y))),
    gmBlkMat_nonneg d E N u M x y]

private theorem gmBlkMat_le_inv_etaT {E : ℝ} (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu : u < 1)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (x y : ZMod (d.L N)) :
    gmBlkMat d E N u M x y ≤ (etaT E u)⁻¹ := by
  have hη : 0 < etaT E u := etaT_pos_of_lt_one' hE hu
  have hzim : (zt E u).im ≠ 0 := by rw [SumZeroDyn.zt_im_eq]; exact hη.ne'
  unfold gmBlkMat
  refine Finset.sup'_le _ _ (fun z _ => ?_)
  calc ‖Gsig M (zt E u) z.1 (x, z.2.1) (y, z.2.2)‖
      ≤ ‖Gsig M (zt E u) z.1‖ := norm_apply_le_l2_opNorm _ _ _
    _ ≤ |(zt E u).im|⁻¹ := norm_Gsig_le hM hzim z.1
    _ = (etaT E u)⁻¹ := by rw [SumZeroDyn.zt_im_eq]; exact congrArg Inv.inv (abs_of_pos hη)

private theorem norm_gloop_three_le_gmBlkMat (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (a₁ a₂ b : ZMod (d.L N)) :
    ‖gloop (d.L N) (d.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      gmBlkMat d E N u M a₂ b * gmBlkMat d E N u M a₁ b * gmBlkMat d E N u M a₂ a₁ := by
  have h := Lemma57.norm_gloop_three_le (L := d.L N) (Wb := d.W N)
    (H := M) (z := zt E u) false true true a₂ b a₁
    (gmBlkMat_nonneg d E N u M)
    (by
      intro p q hp hq
      rcases p with ⟨px, pi⟩
      rcases q with ⟨qy, qi⟩
      dsimp at hp hq ⊢
      subst px; subst qy
      exact norm_Gsig_le_gmBlkMat d E N u M false a₁ a₂ pi qi)
    (by
      intro q r hq hr
      rcases q with ⟨qx, qi⟩
      rcases r with ⟨ry, ri⟩
      dsimp at hq hr ⊢
      subst qx; subst ry
      exact norm_Gsig_le_gmBlkMat d E N u M true a₂ b qi ri)
    (by
      intro r p hr hp
      rcases r with ⟨rx, ri⟩
      rcases p with ⟨py, pi⟩
      dsimp at hr hp ⊢
      subst rx; subst py
      exact norm_Gsig_le_gmBlkMat d E N u M true b a₁ ri pi)
  rw [gmBlkMat_comm d E N u hM b a₁, gmBlkMat_comm d E N u hM a₁ a₂] at h
  convert h using 1 <;> ring

private theorem ellStar_le_ellStarStar {W ℓu : ℝ} (hW : 1 ≤ Real.log W) (hℓu : 0 ≤ ℓu) :
    ellStar W ℓu ≤ Lemma57.ellStarStar W ℓu := by
  unfold ellStar Lemma57.ellStarStar
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hW (by norm_num)) hℓu

/-! ## T2(a) : `qvSet` -/

/-- The `M.IsHermitian`-conditional bridge value: exactly `quadVar (lkFun)` at every
Hermitian `M` (in particular at every `Hflow d N u ω`), `0` off the Hermitian set (an arbitrary,
never-evaluated value there). See the module docstring for why this is needed for measurability
on the whole matrix space. -/
noncomputable def qvVal (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (d.L N) 2)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℝ :=
  if _hM : M.IsHermitian then
    RBM.Gauss.quadVar (band d).toDims N
      (fun M' => RBM.MomentDuhamel.lkFun (band d) E N u M' RBM.Step2.sigPM a) M
  else 0

theorem measurableSet_isHermitian (N : ℕ) :
    MeasurableSet {M : Matrix (d.Idx N) (d.Idx N) ℂ | M.IsHermitian} := by
  have hcont : Continuous (fun M : Matrix (d.Idx N) (d.Idx N) ℂ => Mᴴ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.conjTranspose_apply]
    exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
  have heq : {M : Matrix (d.Idx N) (d.Idx N) ℂ | M.IsHermitian} = {M | Mᴴ = M} := rfl
  rw [heq]
  exact (isClosed_eq hcont continuous_id).measurableSet

private theorem continuous_quadVar_loopObs (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (d.L N) 2)
    (hz : (zt E u).im ≠ 0) :
    Continuous fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      RBM.Gauss.quadVar (band d).toDims N
        (RBM.Gauss.loopObs (band d).toDims N (zt E u) (RBM.Gauss.toIdx RBM.Step2.sigPM a)) M := by
  have hwf : (RBM.Gauss.toIdx RBM.Step2.sigPM a).WF := RBM.Gauss.toIdx_wf _ _
  have hn : 1 ≤ (RBM.Gauss.toIdx RBM.Step2.sigPM a).a.length := by
    simp [RBM.Gauss.toIdx, LoopData.idx, LoopIdx.length]
  have hTF : RBM.Gauss.TestFun (band d).toDims N
      (RBM.Gauss.loopObs (band d).toDims N (zt E u) (RBM.Gauss.toIdx RBM.Step2.sigPM a)) :=
    RBM.Gauss.testFun_loopObs_of_im_le hz (abs_pos.mpr hz) le_rfl hwf hn
  unfold RBM.Gauss.quadVar
  refine continuous_finsetSum _ fun q _ => ?_
  exact continuous_const.mul ((hTF.continuous_fderiv.clm_apply continuous_const).norm.pow 2)

theorem measurable_qvVal (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (d.L N) 2)
    (hE : |E| < 2) (hu1 : u < 1) : Measurable (qvVal d E N u a) := by
  have hz : (zt E u).im ≠ 0 := by
    rw [SumZeroDyn.zt_im_eq]; exact (etaT_pos_of_lt_one' hE hu1).ne'
  have heq : qvVal d E N u a = fun M => if M.IsHermitian then
      RBM.Gauss.quadVar (band d).toDims N
        (RBM.Gauss.loopObs (band d).toDims N (zt E u) (RBM.Gauss.toIdx RBM.Step2.sigPM a)) M
      else 0 := by
    funext M
    by_cases hM : M.IsHermitian
    · rw [qvVal, dif_pos hM, if_pos hM]
      exact RBM.EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs (B := band d) hz RBM.Step2.sigPM hM a
    · rw [qvVal, dif_neg hM, if_neg hM]
  rw [heq]
  exact Measurable.ite (measurableSet_isHermitian d N)
    (continuous_quadVar_loopObs d E N u a hz).measurable measurable_const

/-- The quadratic-variation event, pointwise in `u`, with `Hflow` replaced by `M`: the
matrix-set form of the per-`u` quadratic-variation `jS`-conditioned bound. Gated behind `u < 1`,
harmlessly: this is where `qvVal`'s measurability proof needs `(zt E u).im ≠ 0`, and every actual
use is at `u` in a window with `t N < 1`. -/
def qvSet (E : ℝ) (N : ℕ) (u ℓs τ D : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | u < 1 → jSMat d E D N u M ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
    ∀ a : LoopArg (d.L N) 2,
      qvVal d E N u a M ≤
        (N : ℝ) ^ τ * RBM.QVEndpoint.diagShape' (band d) N
          ((band d).ell N u) ℓs (etaT E u) D
          (jGMat d E N u ((band d).ell N u) (etaT E u) D M)
          (RBM.EarlyQVRateEv.sDet (band d) E N u ℓs)
          (RBM.EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
            ((band d).ell N u) (etaT E u) D
            (jGMat d E N u ((band d).ell N u) (etaT E u) D M)) a}

private theorem measurable_qvRHS (E : ℝ) (N : ℕ) (u ℓs τ D : ℝ) (a : LoopArg (d.L N) 2) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (N : ℝ) ^ τ * RBM.QVEndpoint.diagShape' (band d) N
        ((band d).ell N u) ℓs (etaT E u) D
        (jGMat d E N u ((band d).ell N u) (etaT E u) D M)
        (RBM.EarlyQVRateEv.sDet (band d) E N u ℓs)
        (RBM.EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
          ((band d).ell N u) (etaT E u) D
          (jGMat d E N u ((band d).ell N u) (etaT E u) D M)) a) := by
  have hJ : Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      jGMat d E N u ((band d).ell N u) (etaT E u) D M) := measurable_jGMat d E N u _ _ _
  have hcont : Continuous (fun J : ℝ =>
      (N : ℝ) ^ τ * RBM.QVEndpoint.diagShape' (band d) N
        ((band d).ell N u) ℓs (etaT E u) D J
        (RBM.EarlyQVRateEv.sDet (band d) E N u ℓs)
        (RBM.EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
          ((band d).ell N u) (etaT E u) D J) a) := by
    unfold RBM.QVEndpoint.diagShape' RBM.QVEndpoint.diagNearRate
      RBM.QVEndpoint.diagFarRate RBM.EEDef.nearEpsilon
    fun_prop
  exact hcont.measurable.comp hJ

theorem measurableSet_qvSet (E : ℝ) (N : ℕ) (u ℓs τ D : ℝ) (hE : |E| < 2) :
    MeasurableSet (qvSet d E N u ℓs τ D) := by
  by_cases hu1 : u < 1
  · have heq0 : qvSet d E N u ℓs τ D =
        {M | jSMat d E D N u M ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
          ∀ a : LoopArg (d.L N) 2, qvVal d E N u a M ≤
            (N : ℝ) ^ τ * RBM.QVEndpoint.diagShape' (band d) N
              ((band d).ell N u) ℓs (etaT E u) D
              (jGMat d E N u ((band d).ell N u) (etaT E u) D M)
              (RBM.EarlyQVRateEv.sDet (band d) E N u ℓs)
              (RBM.EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
                ((band d).ell N u) (etaT E u) D
                (jGMat d E N u ((band d).ell N u) (etaT E u) D M)) a} := by
      unfold qvSet
      ext M
      constructor
      · intro h; exact h hu1
      · intro h _; exact h
    have heq : qvSet d E N u ℓs τ D =
        {M | jSMat d E D N u M ≤ (N : ℝ) ^ ((1 : ℝ) / 2)}ᶜ ∪
          ⋂ a : LoopArg (d.L N) 2, {M | qvVal d E N u a M ≤
            (N : ℝ) ^ τ * RBM.QVEndpoint.diagShape' (band d) N
              ((band d).ell N u) ℓs (etaT E u) D
              (jGMat d E N u ((band d).ell N u) (etaT E u) D M)
              (RBM.EarlyQVRateEv.sDet (band d) E N u ℓs)
              (RBM.EEDef.nearEpsilon ((band d).W N : ℝ) ((band d).L N : ℝ)
                ((band d).ell N u) (etaT E u) D
                (jGMat d E N u ((band d).ell N u) (etaT E u) D M)) a} := by
      rw [heq0]
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iInter,
        imp_iff_not_or]
    rw [heq]
    refine (measurableSet_le (measurable_jSMat d E D N u) measurable_const).compl.union ?_
    exact MeasurableSet.iInter fun a =>
      measurableSet_le (measurable_qvVal d E N u a hE hu1) (measurable_qvRHS d E N u ℓs τ D a)
  · have heq : qvSet d E N u ℓs τ D = Set.univ := by
      unfold qvSet; ext M; simp [hu1]
    rw [heq]; exact MeasurableSet.univ

/-! ## T2(b) : `jgSet` -/

/-- The event `jG ≤ N^{2ε} jS`, as a set of matrices. -/
def jgSet (E : ℝ) (N : ℕ) (u ε D : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | jGMat d E N u ((band d).ell N u) (etaT E u) D M ≤
    (N : ℝ) ^ (2 * ε) * jSMat d E D N u M}

theorem measurableSet_jgSet (E : ℝ) (N : ℕ) (u ε D : ℝ) : MeasurableSet (jgSet d E N u ε D) :=
  measurableSet_le (measurable_jGMat d E N u _ _ _) (measurable_const.mul (measurable_jSMat d E D N u))

/-! ## T2(c) : `h554Set`, `honeSet` -/

/-- **(T2)(c), the (5.54) bound `ρ`.** An explicit deterministic function of `(E, N, u, D, J)`:
`ρ(J) = η_u⁻¹ · J · √(T_{u,D}(ℓ**_u) · T_{u,D}(ℓ**_u / 2))`, with `T_{u,D} = tailT W ℓ_u η_u D`
((5.27)) and `ℓ**_u = Lemma57.ellStarStar W ℓ_u`. `h554Set` evaluates it at `J := jGMat … M`;
downstream, `rho554_mono` lets `J` be replaced by any deterministic cap (e.g. the one available on
`jgSet ∩ {jSMat ≤ thr}`), and `rho554_le_two_mul_rpow` shows `ρ(J) ≤ 2 η_u⁻¹ J W^{-D}` once
`2D² ≤ log W` and `1 ≤ W ℓ_u η_u`. -/
noncomputable def rho554 (E : ℝ) (N : ℕ) (u D J : ℝ) : ℝ :=
  (etaT E u)⁻¹ * J *
    Real.sqrt (tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
        (Lemma57.ellStarStar (d.W N : ℝ) ((band d).ell N u)) *
      tailT (d.W N : ℝ) ((band d).ell N u) (etaT E u) D
        (Lemma57.ellStarStar (d.W N : ℝ) ((band d).ell N u) / 2))

theorem rho554_mono (E : ℝ) (N : ℕ) (u D : ℝ) (hη : 0 < etaT E u) {J J' : ℝ} (hJJ : J ≤ J') :
    rho554 d E N u D J ≤ rho554 d E N u D J' := by
  unfold rho554
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJJ (inv_pos.mpr hη).le)
    (Real.sqrt_nonneg _)

/-- **Size of `ρ`: a genuine `W^{-D}` bound.**
`T_{u,D}(ℓ**_u/2) = A⁻² e^{-(log W)^{3/2}/√2} + W^{-D}` with `A = W ℓ_u η_u`, and `e^{-(log W)^{3/2}/√2} ≤ W^{-D}` as soon as `2D² ≤ log W`; hence
`ρ(J) ≤ 2 η_u⁻¹ J W^{-D}`. Deterministic; for fixed `D` the hypothesis `2D² ≤ log W` holds
eventually in `N` since `W → ∞`. -/
theorem rho554_le_two_mul_rpow (E : ℝ) (N : ℕ) {u D J : ℝ} (hη : 0 < etaT E u)
    (hℓu : 0 < (band d).ell N u) (hA : 1 ≤ (d.W N : ℝ) * (band d).ell N u * etaT E u)
    (hlog : 2 * D ^ 2 ≤ Real.log (d.W N : ℝ)) (hJ : 0 ≤ J) :
    rho554 d E N u D J ≤ 2 * (etaT E u)⁻¹ * J * (d.W N : ℝ) ^ (-D) := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  set ℓ := (band d).ell N u with hℓdef
  set η := etaT E u with hηdef
  set W : ℝ := (d.W N : ℝ) with hWdef
  set Lss := Lemma57.ellStarStar W ℓ with hLssdef
  have hlogW0 : 0 ≤ Real.log W := le_trans (by positivity) hlog
  have hLss0 : 0 ≤ Lss := by
    rw [hLssdef]; unfold Lemma57.ellStarStar
    exact mul_nonneg (Real.rpow_nonneg hlogW0 _) hℓu.le
  have hT1 : tailT W ℓ η D Lss ≤ tailT W ℓ η D (Lss / 2) :=
    tailT_antitone hℓu (by linarith)
  have hT2nn : 0 ≤ tailT W ℓ η D (Lss / 2) := tailT_nonneg hW.le _
  have hT1nn : 0 ≤ tailT W ℓ η D Lss := tailT_nonneg hW.le _
  have hsq : Real.sqrt (tailT W ℓ η D Lss * tailT W ℓ η D (Lss / 2)) ≤
      tailT W ℓ η D (Lss / 2) := by
    calc Real.sqrt (tailT W ℓ η D Lss * tailT W ℓ η D (Lss / 2))
        ≤ Real.sqrt (tailT W ℓ η D (Lss / 2) * tailT W ℓ η D (Lss / 2)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hT1 hT2nn)
      _ = tailT W ℓ η D (Lss / 2) := Real.sqrt_mul_self hT2nn
  -- the stretched-exponential part is below `W^{-D}`
  have hexp : Real.exp (-Real.sqrt (Lss / 2 / ℓ)) ≤ W ^ (-D) := by
    rw [Real.rpow_def_of_pos hW]
    apply Real.exp_le_exp.mpr
    have hin : Lss / 2 / ℓ = Real.log W ^ 3 / 2 := by
      rw [hLssdef]; unfold Lemma57.ellStarStar
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [hin]
    have hle : D * Real.log W ≤ Real.sqrt (Real.log W ^ 3 / 2) := by
      apply Real.le_sqrt_of_sq_le
      have h2 : (D * Real.log W) ^ 2 = D ^ 2 * Real.log W ^ 2 := by ring
      rw [h2]
      have h3 : 0 ≤ Real.log W ^ 2 := sq_nonneg _
      nlinarith
    linarith
  have hAinv : ((W * ℓ * η) ^ 2)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    nlinarith
  have hT2 : tailT W ℓ η D (Lss / 2) ≤ 2 * W ^ (-D) := by
    unfold tailT
    have hexp0 : 0 ≤ Real.exp (-Real.sqrt (Lss / 2 / ℓ)) := (Real.exp_pos _).le
    have : ((W * ℓ * η) ^ 2)⁻¹ * Real.exp (-Real.sqrt (Lss / 2 / ℓ)) ≤ W ^ (-D) :=
      (mul_le_of_le_one_left hexp0 hAinv).trans hexp
    linarith
  have hηi : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  unfold rho554
  calc η⁻¹ * J * Real.sqrt (tailT W ℓ η D Lss * tailT W ℓ η D (Lss / 2))
      ≤ η⁻¹ * J * (2 * W ^ (-D)) :=
        mul_le_mul_of_nonneg_left (hsq.trans hT2) (mul_nonneg hηi hJ)
    _ = 2 * η⁻¹ * J * W ^ (-D) := by ring

private theorem sqrt_mul_sqrt_mul_eq {J T₁ T₂ : ℝ} (hJ : 0 ≤ J) (hT₁ : 0 ≤ T₁) :
    Real.sqrt (J * T₁) * Real.sqrt (J * T₂) = J * Real.sqrt (T₁ * T₂) := by
  rw [Real.sqrt_mul hJ, Real.sqrt_mul hJ, Real.sqrt_mul hT₁]
  calc Real.sqrt J * Real.sqrt T₁ * (Real.sqrt J * Real.sqrt T₂)
      = (Real.sqrt J * Real.sqrt J) * (Real.sqrt T₁ * Real.sqrt T₂) := by ring
    _ = J * (Real.sqrt T₁ * Real.sqrt T₂) := by rw [Real.mul_self_sqrt hJ]

/-- The far-triple-loop input `h554` of `RBM.Gauss.Grid.eGpm_le_rhs535_of_jG_mat'`, as a set of
matrices, with `ρ := rho554 d E N u D J` evaluated at `J := jGMat d E N u ℓ_u η_u D M` (the same
`J` that its conclusion carries). Gated behind `M.IsHermitian`, harmlessly: `Hflow` is
always Hermitian, and the deterministic proof (`mem_h554Set_of_isHermitian`) needs it. -/
def h554Set (E : ℝ) (N : ℕ) (u D : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | M.IsHermitian →
    ∀ a₁ a₂ b : ZMod (d.L N),
      Lemma57.ellStarStar (d.W N : ℝ) ((band d).ell N u) < (zdist (d.L N) (a₂ - b) : ℝ) →
      ‖gloop (d.L N) (d.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
        rho554 d E N u D (jGMat d E N u ((band d).ell N u) (etaT E u) D M)}

private theorem measurable_h554RHS (E : ℝ) (N : ℕ) (u D : ℝ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      rho554 d E N u D (jGMat d E N u ((band d).ell N u) (etaT E u) D M)) := by
  unfold rho554
  exact (measurable_const.mul (measurable_jGMat d E N u _ _ _)).mul measurable_const

theorem measurableSet_h554Set (E : ℝ) (N : ℕ) (u D : ℝ) :
    MeasurableSet (h554Set d E N u D) := by
  have heq : h554Set d E N u D = {M | M.IsHermitian}ᶜ ∪
      ⋂ a₁ : ZMod (d.L N), ⋂ a₂ : ZMod (d.L N), ⋂ b : ZMod (d.L N),
        {M | Lemma57.ellStarStar (d.W N : ℝ) ((band d).ell N u) < (zdist (d.L N) (a₂ - b) : ℝ) →
          ‖gloop (d.L N) (d.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
            rho554 d E N u D (jGMat d E N u ((band d).ell N u) (etaT E u) D M)} := by
    unfold h554Set
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iInter, imp_iff_not_or]
  rw [heq]
  refine (measurableSet_isHermitian d N).compl.union ?_
  refine MeasurableSet.iInter fun a₁ => MeasurableSet.iInter fun a₂ =>
    MeasurableSet.iInter fun b => ?_
  by_cases hb : Lemma57.ellStarStar (d.W N : ℝ) ((band d).ell N u) < (zdist (d.L N) (a₂ - b) : ℝ)
  · simp only [hb, forall_true_left]
    exact measurableSet_le
      ((measurable_gloop_matrix d N (zt E u) _).norm) (measurable_h554RHS d E N u D)
  · simp only [hb, false_implies, Set.setOf_true]
    exact MeasurableSet.univ

/-- **The deterministic (5.54) bound: every Hermitian matrix lies in `h554Set`.** The (5.60)
product `G(a₂,b) G(a₁,b) G(a₂,a₁)` always has **two** far factors at distance `≥ ℓ**/2`: by the
triangle inequality `‖a₂-b‖ ≤ ‖a₂-a₁‖ + ‖a₁-b‖` and `‖a₂-b‖ > ℓ**`, either `‖a₂-a₁‖ ≥ ℓ**/2`
(then `G(a₂,a₁)` is far) or `‖a₁-b‖ > ℓ**/2` (then `G(a₁,b)` is far). Both far factors are bounded
by `√(J T)` (`gmBlkMat_le_sqrt_jGMat_tail`, `tailT_antitone`), the remaining one by `η_u⁻¹`.
Valid for all `a₁, a₂`. -/
theorem mem_h554Set_of_isHermitian {E : ℝ} (hE : |E| < 2) (N : ℕ) {u D : ℝ} (hu : u < 1)
    (hℓu : 0 < (band d).ell N u) (hlogW : 1 ≤ Real.log (d.W N : ℝ))
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) : M ∈ h554Set d E N u D := by
  intro _ a₁ a₂ b hb
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have hη : 0 < etaT E u := etaT_pos_of_lt_one' hE hu
  set ℓ := (band d).ell N u with hℓdef
  set η := etaT E u with hηdef
  set J := jGMat d E N u ℓ η D M with hJdef
  set Lss := Lemma57.ellStarStar (d.W N : ℝ) ℓ with hLssdef
  set T : ℝ → ℝ := tailT (d.W N : ℝ) ℓ η D with hTdef
  have hJ : 0 ≤ J := (one_le_jGMat d E N u M).trans' (by norm_num)
  have hStarLe : ellStar (d.W N : ℝ) ℓ ≤ Lss := ellStar_le_ellStarStar hlogW hℓu.le
  have hStarNN : 0 ≤ ellStar (d.W N : ℝ) ℓ := by
    unfold ellStar
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hℓu.le
  have hTnn : ∀ x, 0 ≤ T x := fun x => tailT_nonneg hW.le x
  have hηi : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
  have hGnn : ∀ x y : ZMod (d.L N), 0 ≤ gmBlkMat d E N u M x y :=
    fun x y => gmBlkMat_nonneg d E N u M x y
  -- a far factor at distance `≥ ℓ`, `ℓ*/2 ≤ ℓ`, is bounded by `√(J T(ℓ))`
  have hfar : ∀ (x y : ZMod (d.L N)) (r : ℝ), ellStar (d.W N : ℝ) ℓ / 2 ≤ r →
      r ≤ (zdist (d.L N) (x - y) : ℝ) → gmBlkMat d E N u M x y ≤ Real.sqrt (J * T r) := by
    intro x y r hr hrxy
    have h1 := gmBlkMat_le_sqrt_jGMat_tail d E N u hM (ℓu := ℓ) (ηu := η) (D := D) x y
      (hr.trans hrxy)
    exact h1.trans (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (tailT_antitone hℓu hrxy) hJ))
  have hcap : ∀ x y : ZMod (d.L N), gmBlkMat d E N u M x y ≤ η⁻¹ :=
    fun x y => gmBlkMat_le_inv_etaT d hE N hu hM x y
  have h1 := norm_gloop_three_le_gmBlkMat d E N u hM a₁ a₂ b
  have g2b : gmBlkMat d E N u M a₂ b ≤ Real.sqrt (J * T Lss) :=
    hfar a₂ b Lss (by linarith) hb.le
  have htri : (zdist (d.L N) (a₂ - b) : ℝ) ≤
      (zdist (d.L N) (a₂ - a₁) : ℝ) + (zdist (d.L N) (a₁ - b) : ℝ) := by
    have h := zdist_add_le (d.L N) (a₂ - a₁) (a₁ - b)
    rw [show a₂ - a₁ + (a₁ - b) = a₂ - b by ring] at h
    exact_mod_cast h
  have hS1 : 0 ≤ Real.sqrt (J * T Lss) := Real.sqrt_nonneg _
  have hprod : gmBlkMat d E N u M a₂ b * gmBlkMat d E N u M a₁ b * gmBlkMat d E N u M a₂ a₁ ≤
      Real.sqrt (J * T Lss) * Real.sqrt (J * T (Lss / 2)) * η⁻¹ := by
    by_cases hA : Lss / 2 ≤ (zdist (d.L N) (a₂ - a₁) : ℝ)
    · -- Case A: `G(a₂,a₁)` is the second far factor, `G(a₁,b)` is capped
      have g21 : gmBlkMat d E N u M a₂ a₁ ≤ Real.sqrt (J * T (Lss / 2)) :=
        hfar a₂ a₁ (Lss / 2) (by linarith) hA
      calc gmBlkMat d E N u M a₂ b * gmBlkMat d E N u M a₁ b * gmBlkMat d E N u M a₂ a₁
          ≤ Real.sqrt (J * T Lss) * η⁻¹ * Real.sqrt (J * T (Lss / 2)) :=
            mul_le_mul (mul_le_mul g2b (hcap a₁ b) (hGnn _ _) hS1) g21 (hGnn _ _)
              (mul_nonneg hS1 hηi)
        _ = _ := by ring
    · -- Case B: `‖a₁-b‖ > ℓ**/2`, so `G(a₁,b)` is the second far factor, `G(a₂,a₁)` is capped
      have hB : Lss / 2 ≤ (zdist (d.L N) (a₁ - b) : ℝ) := by
        push Not at hA; linarith
      have g1b : gmBlkMat d E N u M a₁ b ≤ Real.sqrt (J * T (Lss / 2)) :=
        hfar a₁ b (Lss / 2) (by linarith) hB
      exact mul_le_mul (mul_le_mul g2b g1b (hGnn _ _) hS1) (hcap a₂ a₁) (hGnn _ _)
        (mul_nonneg hS1 (Real.sqrt_nonneg _))
  have heq : Real.sqrt (J * T Lss) * Real.sqrt (J * T (Lss / 2)) * η⁻¹ =
      rho554 d E N u D J := by
    unfold rho554
    rw [sqrt_mul_sqrt_mul_eq hJ (hTnn Lss)]
    ring
  exact h1.trans (hprod.trans heq.le)

/-- The centered one-resolvent trace input `hone` of `RBM.Gauss.Grid.eGpm_le_rhs535_of_jG_mat'`
((4.2)/(5.31)), as a set of matrices, `κ` an explicit deterministic function of
`(E, N, u, ℓs, ζCtr)` (no `M`-dependence). -/
def honeSet (E : ℝ) (N : ℕ) (u ℓs ζCtr : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ (σ : Bool) (b : ZMod (d.L N)),
    ‖Matrix.trace ((Gsig M (zt E u) σ - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) b)‖ ≤
      (N : ℝ) ^ ζCtr * (2 * ((band d).ell N u / ℓs) * ((band d).scale E N u)⁻¹)}

private theorem measurable_honeTrace (E : ℝ) (N : ℕ) (u : ℝ) (σ : Bool) (b : ZMod (d.L N)) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      Matrix.trace ((Gsig M (zt E u) σ - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
        Eblk (d.L N) (d.W N) b)) := by
  have hA : ∀ i k : d.Idx N, Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (Gsig M (zt E u) σ - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) i k) := by
    intro i k
    simp only [Matrix.sub_apply]
    exact (measurable_Gsig_matrix d N (zt E u) σ i k).sub measurable_const
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun k _ => (hA i k).mul measurable_const

theorem measurableSet_honeSet (E : ℝ) (N : ℕ) (u ℓs ζCtr : ℝ) :
    MeasurableSet (honeSet d E N u ℓs ζCtr) := by
  have heq : honeSet d E N u ℓs ζCtr =
      ⋂ σ : Bool, ⋂ b : ZMod (d.L N), {M | ‖Matrix.trace
        ((Gsig M (zt E u) σ - mSigma E σ • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) *
          Eblk (d.L N) (d.W N) b)‖ ≤
        (N : ℝ) ^ ζCtr * (2 * ((band d).ell N u / ℓs) * ((band d).scale E N u)⁻¹)} := by
    unfold honeSet; ext M; simp
  rw [heq]
  exact MeasurableSet.iInter fun σ => MeasurableSet.iInter fun b =>
    measurableSet_le (measurable_honeTrace d E N u σ b).norm measurable_const

/-! ## T2(d) : `goodSet` -/

/-- **(T2)(d)** `goodSet := qvSet ∩ jgSet ∩ h554Set ∩ honeSet ∩ eq273Set(n=3) ∩ eq557Set`. -/
def goodSet (E : ℝ) (N : ℕ) (u ℓs τ ε ζCtr τ3 τ57 D : ℝ) :
    Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  qvSet d E N u ℓs τ D ∩ jgSet d E N u ε D ∩ h554Set d E N u D ∩ honeSet d E N u ℓs ζCtr ∩
    eq273Set d E N 3 u ℓs τ3 ∩ eq557Set d E N u ℓs τ57

theorem measurableSet_goodSet (E : ℝ) (N : ℕ) (u ℓs τ ε ζCtr τ3 τ57 D : ℝ)
    (hE : |E| < 2) : MeasurableSet (goodSet d E N u ℓs τ ε ζCtr τ3 τ57 D) :=
  ((((measurableSet_qvSet d E N u ℓs τ D hE).inter (measurableSet_jgSet d E N u ε D)).inter
    (measurableSet_h554Set d E N u D)).inter
    (measurableSet_honeSet d E N u ℓs ζCtr)).inter (measurableSet_eq273Set d E N 3 u ℓs τ3)
    |>.inter (measurableSet_eq557Set d E N u ℓs τ57)

/-! ## T3 : flow `HighProb` for each piece -/

/-! ## T4 : grid `HighProb` for `goodSet` -/

/-- **The window restriction.** A flow event over `TimeIcc s t` implies the same event over
`TimeIcc s u` when `u ≤ t`. -/
theorem highProb_flow_restrict {s t u : ℕ → ℝ} (hut : ∀ N, u N ≤ t N)
    (S : ∀ N : ℕ, ℝ → Set (Matrix (d.Idx N) (d.Idx N) ℂ))
    (h : HighProb (P d) (fun N => {ω | ∀ v : TimeIcc s t N, Hflow d N (v : ℝ) ω ∈ S N (v : ℝ)})) :
    HighProb (P d) (fun N => {ω | ∀ v : TimeIcc s u N, Hflow d N (v : ℝ) ω ∈ S N (v : ℝ)}) := by
  refine h.mono ?_
  filter_upwards with N ω hω v
  exact hω ⟨(v : ℝ), v.2.1, v.2.2.trans (hut N)⟩

end RBM.Gauss.Grid

end
