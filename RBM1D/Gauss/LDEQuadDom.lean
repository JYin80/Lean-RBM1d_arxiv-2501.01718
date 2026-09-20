/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEQuadInst

/-!
# From the moment bound to `≺`, for the quadratic estimate — T96

`RBM.Gauss.integral_ldeQuadLHS_pow_le` (T95) gives

`E[(ldeQuadLHS)^p] ≤ A_p u^{2p} E[(ldeQuadRHS)^p]`,

but `RBM.diag_bound_stochDom` needs `StochDom P ldeQuadLHS ldeQuadRHS`, whose control is
**random**, while `RBM.Gauss.stochDom_of_momentDom` only accepts a deterministic one.  A plain
Markov inequality does not bridge the two: the threshold `N^τ ζ(ω)` moves with `ω`.

The bridge is the **normalised** chaos.  Rescaling the matrix by a *constant in `(k,l)`* — the
off-row-measurable factor `(V_q + ε)^{-1/2}` — rescales the chaos by the same factor and makes
the control `V_q/(V_q+ε) ≤ 1`.  So

`E[(|Q|²/(V_q+ε))^p] ≤ A_p`   for every `ε > 0`,  with `A_p` free of `ε`,

and Markov now has a *deterministic* threshold.  Finally
`{|Q|² > λV_q} = ⋃_n {|Q|² > λ(V_q + 1/n)}` is an increasing union, so continuity of the
measure from below removes `ε` with no integral limit theorem and no separate treatment of
`{V_q = 0}`.

`(V_q+ε)^{-1/2}` keeps the rescaled matrix globally bounded (by `Bbd/√ε`), which is what
`RowChaos` requires; the bound blows up as `ε → 0`, but it never enters the conclusion.

## Main statements

* `RBM.Gauss.modelChaosEps` : the `ε`-normalised row chaos
* `RBM.Gauss.chaos_modelChaosEps`, `RBM.Gauss.Vq_modelChaosEps` : it is the base chaos and
  control, divided by `V_q + ε`
-/

namespace RBM.Gauss

open MeasureTheory Matrix Finset

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ} {u : ℝ} {z : ℂ}

/-! ### The control of the model instance, as a function of `ω` -/

/-- `V_q` of the model instance, written out: `∑_{k,l} (uS_{ik})‖G^{(i)}_{kl}‖²(uS_{il})`. -/
noncomputable def vqM (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (i : d.Idx N) (ω : Ω d) : ℝ :=
  ∑ k : {a : d.Idx N // a ≠ i}, ∑ l : {a : d.Idx N // a ≠ i},
    (u * Sblk (d.L N) (d.W N) i k.1) * ‖minorRes d N u z i ω k l‖ ^ 2 *
      (u * Sblk (d.L N) (d.W N) i l.1)

theorem vqM_nonneg (hu : 0 ≤ u) (i : d.Idx N) (ω : Ω d) : 0 ≤ vqM d N u z i ω :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hu (Sblk_nonneg _ _)) (by positivity))
      (mul_nonneg hu (Sblk_nonneg _ _))

theorem continuous_vqM (hz : z.im ≠ 0) (i : d.Idx N) :
    Continuous fun ω : Ω d => vqM d N u z i ω := by
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact ((continuous_const.mul (((continuous_minorRes hz i k l).norm).pow 2)).mul
    continuous_const)

theorem vqM_congr (i : d.Idx N) {ω ω' : Ω d} (h : ∀ c ∈ offRowCoord d N i, ω c = ω' c) :
    vqM d N u z i ω = vqM d N u z i ω' := by
  unfold vqM
  rw [minorRes_congr (u := u) (z := z) i h]

theorem vqM_eq (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) (ω : Ω d) :
    (modelChaos d N u hz i).Vq ω = vqM d N u z i ω := by
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [modelChaos_sg hz i hu k, modelChaos_sg hz i hu l]
  rfl

/-! ### The `ε`-normalised instance -/

/-- The normalising factor `(V_q + ε)^{1/2}`. -/
noncomputable def sqVq (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (i : d.Idx N) (ε : ℝ) (ω : Ω d) : ℝ :=
  Real.sqrt (vqM d N u z i ω + ε)

theorem sqVq_pos (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) (i : d.Idx N) (ω : Ω d) :
    0 < sqVq d N u z i ε ω :=
  Real.sqrt_pos.2 (by linarith [vqM_nonneg (z := z) hu i ω])

theorem sq_sqVq (hu : 0 ≤ u) {ε : ℝ} (hε : 0 < ε) (i : d.Idx N) (ω : Ω d) :
    sqVq d N u z i ε ω ^ 2 = vqM d N u z i ω + ε :=
  Real.sq_sqrt (by linarith [vqM_nonneg (z := z) hu i ω])

theorem sqVq_ge (hu : 0 ≤ u) {ε : ℝ} (_hε : 0 < ε) (i : d.Idx N) (ω : Ω d) :
    Real.sqrt ε ≤ sqVq d N u z i ε ω :=
  Real.sqrt_le_sqrt (by linarith [vqM_nonneg (z := z) hu i ω])

/-- **The `ε`-normalised row chaos**: the same row, with the matrix divided by
`(V_q + ε)^{1/2}`.  The factor does not depend on `(k, l)`, so the chaos is divided by it too,
and it reads only the off-row block, so `B_free` survives. -/
noncomputable def modelChaosEps (d : Dims) (N : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (hu : 0 ≤ u) (i : d.Idx N) (ε : ℝ) (hε : 0 < ε) : RowChaos d {a : d.Idx N // a ≠ i} :=
  { modelChaos d N u hz i with
    B := fun ω k l => minorRes d N u z i ω k l / ((sqVq d N u z i ε ω : ℝ) : ℂ)
    B_cont := fun k l => by
      refine (continuous_minorRes hz i k l).div ?_ ?_
      · exact Complex.continuous_ofReal.comp
          ((continuous_vqM (u := u) hz i).add continuous_const).sqrt
      · intro ω
        exact_mod_cast (sqVq_pos (z := z) hu hε i ω).ne'
    Bbd := |z.im|⁻¹ / Real.sqrt ε
    B_bdd := fun ω k l => by
      have hpos := sqVq_pos (z := z) hu hε i ω
      have hge := sqVq_ge (z := z) hu hε i ω
      have hεp : (0 : ℝ) < Real.sqrt ε := Real.sqrt_pos.2 hε
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      refine div_le_div₀ (by positivity) (norm_minorRes_le hz i ω k l) hεp hge
    B_free := fun ω ω' h => by
      have hs : sqVq d N u z i ε ω = sqVq d N u z i ε ω' := by
        unfold sqVq
        rw [vqM_congr (u := u) (z := z) i h]
      funext k l
      rw [minorRes_congr (u := u) (z := z) i h, hs] }

@[simp] theorem modelChaosEps_B (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ} (hε : 0 < ε)
    (ω : Ω d) (k l : {a : d.Idx N // a ≠ i}) :
    (modelChaosEps d N u hz hu i ε hε).B ω k l
      = minorRes d N u z i ω k l / ((sqVq d N u z i ε ω : ℝ) : ℂ) := rfl

@[simp] theorem modelChaosEps_sg (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ}
    (hε : 0 < ε) (k : {a : d.Idx N // a ≠ i}) :
    (modelChaosEps d N u hz hu i ε hε).sg k = (modelChaos d N u hz i).sg k := rfl

@[simp] theorem modelChaosEps_h (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ}
    (hε : 0 < ε) (ω : Ω d) (k : {a : d.Idx N // a ≠ i}) :
    (modelChaosEps d N u hz hu i ε hε).h ω k = (modelChaos d N u hz i).h ω k := rfl

/-- **The normalised chaos is the chaos, divided by `(V_q+ε)^{1/2}`.** -/
theorem chaos_modelChaosEps (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ} (hε : 0 < ε)
    (ω : Ω d) :
    (modelChaosEps d N u hz hu i ε hε).chaos ω
      = (modelChaos d N u hz i).chaos ω / ((sqVq d N u z i ε ω : ℝ) : ℂ) := by
  have hne : ((sqVq d N u z i ε ω : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sqVq_pos (z := z) hu hε i ω).ne'
  unfold RowChaos.chaos RowChaos.cen
  rw [sub_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    show (modelChaos d N u hz i).h ω k *
        (minorRes d N u z i ω k l / ((sqVq d N u z i ε ω : ℝ) : ℂ)) *
        (starRingEnd ℂ) ((modelChaos d N u hz i).h ω l)
      = (modelChaos d N u hz i).h ω k * minorRes d N u z i ω k l *
        (starRingEnd ℂ) ((modelChaos d N u hz i).h ω l) / ((sqVq d N u z i ε ω : ℝ) : ℂ)
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (((modelChaos d N u hz i).sg k : ℝ) : ℂ) *
        (minorRes d N u z i ω k k / ((sqVq d N u z i ε ω : ℝ) : ℂ))
      = (((modelChaos d N u hz i).sg k : ℝ) : ℂ) * minorRes d N u z i ω k k /
        ((sqVq d N u z i ε ω : ℝ) : ℂ)
    ring

/-- **The normalised control is `V_q/(V_q+ε) ≤ 1`.** -/
theorem Vq_modelChaosEps (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ} (hε : 0 < ε)
    (ω : Ω d) :
    (modelChaosEps d N u hz hu i ε hε).Vq ω
      = vqM d N u z i ω / (vqM d N u z i ω + ε) := by
  have hpos := sqVq_pos (z := z) hu hε i ω
  have hsq := sq_sqVq (z := z) hu hε i ω
  have hpt : ∀ k l : {a : d.Idx N // a ≠ i},
      (modelChaosEps d N u hz hu i ε hε).sg k *
          ‖(modelChaosEps d N u hz hu i ε hε).B ω k l‖ ^ 2 *
          (modelChaosEps d N u hz hu i ε hε).sg l
        = ((modelChaos d N u hz i).sg k * ‖(modelChaos d N u hz i).B ω k l‖ ^ 2 *
            (modelChaos d N u hz i).sg l) / (vqM d N u z i ω + ε) := by
    intro k l
    show (modelChaos d N u hz i).sg k *
        ‖minorRes d N u z i ω k l / ((sqVq d N u z i ε ω : ℝ) : ℂ)‖ ^ 2 *
        (modelChaos d N u hz i).sg l = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le, div_pow, hsq]
    show _ = ((modelChaos d N u hz i).sg k * ‖minorRes d N u z i ω k l‖ ^ 2 *
      (modelChaos d N u hz i).sg l) / (vqM d N u z i ω + ε)
    ring
  have hd : ∀ (A : {a : d.Idx N // a ≠ i} → {a : d.Idx N // a ≠ i} → ℝ) (c : ℝ),
      (∑ k, ∑ l, A k l / c) = (∑ k, ∑ l, A k l) / c := by
    intro A c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_div _ _ _).symm
  unfold RowChaos.Vq
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l,
    hd (fun k l => (modelChaos d N u hz i).sg k * ‖(modelChaos d N u hz i).B ω k l‖ ^ 2 *
      (modelChaos d N u hz i).sg l) (vqM d N u z i ω + ε),
    show (∑ k, ∑ l, (modelChaos d N u hz i).sg k *
        ‖(modelChaos d N u hz i).B ω k l‖ ^ 2 * (modelChaos d N u hz i).sg l)
      = vqM d N u z i ω from vqM_eq hz hu i ω]

theorem Vq_modelChaosEps_le_one (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ}
    (hε : 0 < ε) (ω : Ω d) : (modelChaosEps d N u hz hu i ε hε).Vq ω ≤ 1 := by
  rw [Vq_modelChaosEps hz hu i hε ω]
  have h0 := vqM_nonneg (z := z) hu i ω
  rw [div_le_one (by linarith)]
  linarith

/-! ### The moment bound for the normalised chaos -/

/-- The constant of T93 at `p = q+1`. -/
noncomputable def hwConst (q : ℕ) : ℝ := ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1)

theorem hwConst_pos (q : ℕ) : 0 < hwConst q := by unfold hwConst; positivity

/-- **`E[(|Q|²/(V_q+ε))^{q+1}] ≤ A_{q+1}`, uniformly in `ε`.** -/
theorem mom_modelChaosEps_le (hG : GaussIBP d) (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N)
    {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (modelChaosEps d N u hz hu i ε hε).mom (q + 1) ≤ hwConst q := by
  have h := (modelChaosEps d N u hz hu i ε hε).mom_le_momVpow hG q
  have hV : (modelChaosEps d N u hz hu i ε hε).momVpow (q + 1) ≤ 1 := by
    show (∫ ω, (modelChaosEps d N u hz hu i ε hε).Vq ω ^ (q + 1) ∂(P d)) ≤ 1
    calc ∫ ω, (modelChaosEps d N u hz hu i ε hε).Vq ω ^ (q + 1) ∂(P d)
        ≤ ∫ _ω : Ω d, (1 : ℝ) ∂(P d) :=
          MeasureTheory.integral_mono
            ((modelChaosEps d N u hz hu i ε hε).integrable_Vq_pow hG (q + 1))
            (MeasureTheory.integrable_const 1)
            (fun ω => pow_le_one₀ (RowChaos.Vq_nonneg ω)
              (Vq_modelChaosEps_le_one hz hu i hε ω))
      _ = 1 := by simp
  have hc : (0 : ℝ) ≤ hwConst q := (hwConst_pos q).le
  refine h.trans ?_
  calc hwConst q * (modelChaosEps d N u hz hu i ε hε).momVpow (q + 1)
      ≤ hwConst q * 1 := mul_le_mul_of_nonneg_left hV hc
    _ = hwConst q := mul_one _

/-! ### The tail bound, at fixed `ε` and then in the limit -/

theorem norm_chaos_modelChaosEps (hz : z.im ≠ 0) (hu : 0 ≤ u) (i : d.Idx N) {ε : ℝ}
    (hε : 0 < ε) (ω : Ω d) :
    ‖(modelChaosEps d N u hz hu i ε hε).chaos ω‖
      = ‖(modelChaos d N u hz i).chaos ω‖ / sqVq d N u z i ε ω := by
  rw [chaos_modelChaosEps hz hu i hε ω, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sqVq_pos (z := z) hu hε i ω).le]

/-- **Markov at fixed `ε`.** -/
theorem meas_lt_normSq_chaos_le_eps (hG : GaussIBP d) (hz : z.im ≠ 0) (hu : 0 ≤ u)
    (i : d.Idx N) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (P d) {ω | lam * (vqM d N u z i ω + ε) < ‖(modelChaos d N u hz i).chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set C' := modelChaosEps d N u hz hu i ε hε with hC'
  set Y : Ω d → ℝ := fun ω => ‖C'.chaos ω‖ with hY
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => norm_nonneg _
  have habs : ∀ ω, |Y ω| ^ (2 * (q + 1)) = ‖C'.chaos ω‖ ^ (2 * (q + 1)) := fun ω => by
    rw [hY, abs_of_nonneg (hYnn ω)]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * (q + 1))) (P d) := by
    simpa only [habs] using C'.integrable_norm_pow hG (q + 1)
  have hmom0 : (∫ ω, ‖C'.chaos ω‖ ^ (2 * (q + 1)) ∂(P d)) ≤ hwConst q :=
    mom_modelChaosEps_le hG hz hu i hε q
  have hmom : ∫ ω, |Y ω| ^ (2 * (q + 1)) ∂(P d) ≤ hwConst q := by
    simpa only [habs] using hmom0
  have ht : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hmark := meas_gt_le_of_moment (P := P d) (Y := Y) ht hint hmom
  have hset : {ω | lam * (vqM d N u z i ω + ε) < ‖(modelChaos d N u hz i).chaos ω‖ ^ 2}
      = {ω | Real.sqrt lam < Y ω} := by
    ext ω
    have hs := sqVq_pos (z := z) hu hε i ω
    have hsq := sq_sqVq (z := z) hu hε i ω
    have hYv : Y ω = ‖(modelChaos d N u hz i).chaos ω‖ / sqVq d N u z i ε ω := by
      rw [hY, hC']; exact norm_chaos_modelChaosEps hz hu i hε ω
    have hc : (0 : ℝ) ≤ ‖(modelChaos d N u hz i).chaos ω‖ := norm_nonneg _
    have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsln : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg lam
    simp only [Set.mem_ofPred_eq, hYv]
    rw [lt_div_iff₀ hs, ← hsq]
    constructor
    · intro h
      nlinarith [h, hs, hc, hsl, hsln,
        sq_nonneg (Real.sqrt lam * sqVq d N u z i ε ω - ‖(modelChaos d N u hz i).chaos ω‖),
        sq_nonneg (Real.sqrt lam * sqVq d N u z i ε ω + ‖(modelChaos d N u hz i).chaos ω‖)]
    · intro h
      have hms := mul_self_lt_mul_self (mul_nonneg hsln hs.le) h
      nlinarith [hms, hsl, hs]
  rw [hset]
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : Real.sqrt lam ^ (2 * (q + 1)) = lam ^ (q + 1) := by
    rw [pow_mul, Real.sq_sqrt hlam.le]
  rw [hpow]

end RBM.Gauss
