/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2FarInputsJG
import RBM1D.Hierarchy.Step2
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.GridGoodSet
import RBM1D.Gauss.GridExpansion

/-!
# T1515: the pointwise drift bound on the good set, and its time sum

## Amend-1 (option (d), `docs/tickets/T1515-amend-1.md`): the (5.54) residue on the near band

`Lemma57.eG_le` adds the (5.54) residue `κ₁ (ℓ_u η_u)⁻¹ L ρ` on both branches, although its far
branch (`eG_far_le`) uses neither `h554` nor `ρ`; the paper (p.59) uses (5.54) only for
`|a₁-a₂| ≤ ℓ*_u`. The primed chain below confines the residue to the near band and absorbs it
there against `T_{u,D} ≥ A_u⁻² e^{-(log W)^{3/4}}`:
* (R1) `eG_le'`; (R2) `eG_le_reduced_of_schwarz'`, `eG_le_reduced'`, `eGpm_le_reduced'`,
  `rhs535'`, `eGpm_le_rhs535'`, `eGpm_le_rhs535_of_jG_mat'`;
* (R3) `rhs535'_le_mul_tailT_near` (generic), `DriftPt.resCoef_le` (the absorption arithmetic,
  `D ≥ D₀ = 8 + 2ζ`), `rhs535'_le_mul_tailT`;
* (T3') `mdr'`, `drift_point_le'`, `drift_point_le_blk'`;
* (T4') `drift_time_sum_le'` (`ℓ_s = ℓ_{s N}`, `D ≥ 8`), `drift_time_sum_le_rescaled'`
  (`ℓ_s' = ℓ_{s N}/(4N^ζ)`, `D ≥ 8 + 2ζ`), both with T1513's `ρ_j ≤ 2 η⁻¹ J_j W^{-D}` and
  exponent `2`; `drift_time_sum_inputs_witness'`;
* (T5) `drift_point_le_heG` (T1518 (T1)'s `hdrift` shape, on `jSMat ≤ thr`, `jGMat ≤ N^{2ε} thr`),
  `mgDrift`, `mgDrift_le`, `drift_point_le_heG_scalars`, `Dgrid_eq_drift`.
The unprimed (T3)/(T4) below are kept; (T4)'s `LρW^D ≤ 1` premise is unsatisfiable with T1513's
`ρ`, so (T4) is superseded by (T4').

Ticket `docs/tickets/T1515.md`, supervisor `docs/supervisor/2026-09-26-0048.md` §1d (M4),
§2 R3(b).

`RBM.Gauss.Grid.drift_point_le` (T3) bounds the drift `D(M) := (eGterm + primBil(A,A))(M)` of
T1506 (T4), with `A := gloop(M) − Kval_u` restricted to the `(+,-)` `2`-loop, against the
`T_{u,D}`-normalized profile that T1510's `weighted_duhamel_sum_stopped` needs.
`RBM.Gauss.Grid.drift_point_le_blk` is the same bound with the concrete block maximum in place of
the free `Gm` (no `h560`), stated with the coefficient function `mdr`.
`RBM.Gauss.Grid.eGpm_le_rhs535_of_jG_mat` (T1) is T1501's `h560`-free (5.35) at matrix level.
`RBM.Gauss.Grid.drift_time_sum_le` (T4) bounds the time sum
`Σ_{j<k} Δ Mdr(u_j) ((1-u_{j+1})/(1-u_k))² ≤ (300/Im m) N^κ ((η_s/η_{u_k})² + 1)`: exponent `2`.

## Step 0 (read-only checks, see the math preflight report for detail)

* `Step2.jStar` (`RBM1D/Gauss/APrimeSmoothPrefixCanonicalCore.lean:79`) is the genuine `J*` of
  (5.29): `jStar L f W ℓu ηu D = sup_a (f a / T_{u,D}(‖a₁-a₂‖)) + 1`. `GridJStar.jSMat` is
  *literally* this formula with the matrix `M` substituted for a `Sample`'s Green function
  (`rfl`, `GridJStar.lean:121`). **This is not** `RBM.APrimeJG.EarlyQVRateEv.jStar`
  (`EarlyQVRateEv.lean:146`), which is a *different*, squared-`G`-pair, far-pairs-only maximum
  used only inside the `jG`/`gmBlk` machinery of (5.60)-(5.61); the ticket flags this
  distinction and it is used correctly throughout this file: every threshold hypothesis below
  is stated against `Step2.jStar`/`GridJStar.jSMat`, never against `EarlyQVRateEv.jStar`.
* `eGpm_le_rhs535_of_jS` (`Hierarchy/Step2FarInputs.lean`, §17 "Instantiate") is the
  *forbidden* route (DECISIONS §10b): its `h560` comes from `gmOfJS`, shown unsatisfiable by
  T1499. This file never calls it. The route used is T1501's (`Step2FarInputsJG.lean`), the
  `h560`-free "Option B": (5.60) proved by block maxima, deterministically, and the far-field
  two-loop bound only invoked on far pairs.
* `T1513`'s `jGMat` (the matrix analogue of `RBM.APrimeJG.jG`) was **not merged** when the
  original (T1)-(T4) were written (it is merged now; amend-1's (T5) uses it through the
  `jGMat` corollary `DriftPt.two_loop_re_le_jGMat`, `DriftPt.gmBlkM_le_sqrt_jGMat`).
  Per the ticket's explicit fallback: (T1) `eGpm_le_rhs535_of_jG_mat` is stated with a
  **generic `J`** together with the two block bounds `h531`/`h42` that `jG` supplies in T1501's
  own proof, `h42` on the concrete matrix block maximum `DriftPt.gmBlkM`; `h560` is discharged
  by `DriftPt.norm_gloop_three_le_gmBlkM`. `drift_point_le` (T3, unchanged) takes `J`, `Gm`,
  `h531`, `h42`, `h560`, `hGm` raw; its successor `drift_point_le_blk` fixes `Gm := gmBlkM`.
  In (T4) the ticket's `jGMat(u_j) ≤ N^{2ε} thr(u_j)` is the hypothesis `J_j ≤ N^{2ε} thr(u_j)`
  on the generic `J`. Once T1513 merges, a `jGMat` corollary can be added.
-/

namespace RBM.Gauss.Grid

open Real Finset RBM RBM.Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ## (T1) : matrix versions of the two deterministic Sample-level results -/

/-- **(T1), quadratic part, matrix version of `RBM.Step2FarInputs.quadGlue_pm_eq_eLL`.**
Route (i) (restate and re-run the proof with `M` generalised): the original proof is already
free of any Sample-specific fact — `X.H N u ω` only ever occurs as the argument of `gloop`, via
`Sample.Lval`'s defining equation `X.Lval E N u ω I = gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
I` (`rfl`, `Flow/Hypotheses.lean:242`) — so the identical script closes for an arbitrary
Hermitian-or-not matrix `M`. No `u = 0`/`H_zero` case split is needed: the identity is an
algebraic rearrangement (`EGDef.primBil_two_eq` plus unfolding `Step2.eLL`), true at every `u`,
not a probabilistic fact about the flow. -/
theorem quadGlue_pm_eq_eLL_mat (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (x y : ZMod (B.L N)) :
    primBil (B.L N) (B.W N)
        (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
        (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
        ⟨[true, false], [x, y]⟩
      = Step2.eLL (B.L N) ((B.W N : ℝ))
          (fun a : LoopArg (B.L N) 2 =>
            gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
              - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) ![x, y] := by
  rw [EGDef.primBil_two_eq]
  simp only [Step2.eLL, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_natCast]
  rfl

/-- **Superseded by (R3) `rhs535'_le_mul_tailT`** (amend-1): absorbing the residue on far pairs
against `W^{-D}` costs `W^D`, which T1513's `ρ` cannot pay.

**(T1), EG part, generic-`J` route.** `rhs535` collapses to a single `M₁ · T_{u,D}` term:
the additive `ρ`-remainder is absorbed into the floor `T_{u,D} ≥ W^{-D}`
(`RBM.rpow_neg_le_tailT`), for *every* `ρ ≥ 0` — no smallness hypothesis on `ρ` is needed, because
the compensating factor `W^{D}` can always be folded into the new coefficient. This is the step
T3's route calls "`rhs535 ≤ M₁ · tailT`", made explicit and reusable; combined with
`RBM.Step2FarInputs.eGpm_le_rhs535` (already the matrix-level, generic-`J` form of T1501's
result — no further restatement of the "(T1) EG part" is needed, since that theorem was never
Sample-specific to begin with) this supplies (T1)'s EG-part output. -/
theorem rhs535_le_mul_tailT {Wr Lr ℓu ℓs ηu D J ρ d : ℝ}
    (hW : 0 < Wr) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hρ : 0 ≤ ρ) (hLr : 0 ≤ Lr) :
    Step2FarInputs.rhs535 Wr Lr ℓu ℓs ηu D J ρ d ≤
      (ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0)
            + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
            + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
          + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * Wr ^ D)
        * tailT Wr ℓu ηu D d := by
  have hfloor : Wr ^ (-D) ≤ tailT Wr ℓu ηu D d := rpow_neg_le_tailT d
  have hcoef0 : (0 : ℝ) ≤ ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ := by positivity
  have hstep : ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * Wr ^ D * Wr ^ (-D)
      ≤ ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * Wr ^ D * tailT Wr ℓu ηu D d :=
    mul_le_mul_of_nonneg_left hfloor (by positivity)
  have heq : ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * Wr ^ D * Wr ^ (-D)
      = ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ := by
    rw [mul_assoc _ (Wr ^ D), ← Real.rpow_add hW]
    simp
  rw [heq] at hstep
  rw [Step2FarInputs.rhs535]
  nlinarith [hstep]

/-! ## (T1), EG part: T1501's `h560`-free route at matrix level

`RBM.Step2FarInputs.eGpm_le_rhs535_of_jG` (T1501) instantiates the frozen
`RBM.Step2FarInputs.eGpm_le_rhs535` with `Gm := RBM.APrimeJG.gmBlk` and proves `h560` from the
block maxima. Here the same is done for an arbitrary Hermitian matrix `M` (route (i)): the block
maximum `DriftPt.gmBlkM` is `APrimeJG.gmBlk`'s formula with `X.H N u ω`, `zt E u` replaced by
`M`, `z` (`rfl`-equal at `M = X.H N u ω`, `DriftPt.gmBlkM_sample`), and the only sample fact
T1501 uses, `X.hermitian N u ω`, becomes the hypothesis `M.IsHermitian`. -/

namespace DriftPt

/-- **Matrix-level block maximum**: the largest resolvent entry between the blocks `x`, `y`, over
both charges, `max_{σ,p,q} ‖G^σ(M,z)_{(x,p),(y,q)}‖`. -/
noncomputable def gmBlkM (B : Band Ω) (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : ℝ :=
  (Finset.univ : Finset (Bool × Fin (B.W N) × Fin (B.W N))).sup'
    ⟨(true, ⟨0, B.W_pos N⟩, ⟨0, B.W_pos N⟩), Finset.mem_univ _⟩
    (fun q => ‖Gsig M z q.1 (x, q.2.1) (y, q.2.2)‖)

/-- At a flow sample, `gmBlkM` is `RBM.APrimeJG.gmBlk` (definitional). -/
theorem gmBlkM_sample (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) :
    gmBlkM B N (X.H N u ω) (zt E u) = APrimeJG.gmBlk X E N u ω := rfl

theorem norm_Gsig_le_gmBlkM (B : Band Ω) (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (σ : Bool) (x y : ZMod (B.L N)) (p q : Fin (B.W N)) :
    ‖Gsig M z σ (x, p) (y, q)‖ ≤ gmBlkM B N M z x y :=
  Finset.le_sup' (f := fun q : Bool × Fin (B.W N) × Fin (B.W N) =>
    ‖Gsig M z q.1 (x, q.2.1) (y, q.2.2)‖) (Finset.mem_univ (σ, p, q))

theorem gmBlkM_nonneg (B : Band Ω) (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : 0 ≤ gmBlkM B N M z x y :=
  (norm_nonneg _).trans (norm_Gsig_le_gmBlkM B N M z true x y ⟨0, B.W_pos N⟩ ⟨0, B.W_pos N⟩)

/-- For Hermitian `M`, the block maximum is symmetric in the two blocks (the reversed entry
occurs with the opposite charge). -/
theorem gmBlkM_comm {N : ℕ} {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (z : ℂ)
    (x y : ZMod (B.L N)) : gmBlkM B N M z x y = gmBlkM B N M z y x := by
  have hflip (s : Bool) (p q : Fin (B.W N)) :
      ‖Gsig M z s (x, p) (y, q)‖ = ‖Gsig M z (!s) (y, q) (x, p)‖ := by
    rw [APrimeJG.norm_Gsig_eq_green_or_swap hM, APrimeJG.norm_Gsig_eq_green_or_swap hM]
    cases s <;> rfl
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun q _ => ?_)
    exact (hflip q.1 q.2.1 q.2.2).trans_le (norm_Gsig_le_gmBlkM B N M z (!q.1) y x q.2.2 q.2.1)
  · refine Finset.sup'_le _ _ (fun q _ => ?_)
    have h := hflip (!q.1) q.2.2 q.2.1
    simp only [Bool.not_not] at h
    exact h.symm.trans_le (norm_Gsig_le_gmBlkM B N M z (!q.1) x y q.2.2 q.2.1)

/-- **(5.60) at matrix level**: the `(-,+,+)` triple loop is bounded by its three block maxima,
deterministically, for every `b` (matrix analogue of T1501's `norm_gloop_three_le_gmBlk'`). -/
theorem norm_gloop_three_le_gmBlkM {N : ℕ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (a₁ a₂ b : ZMod (B.L N)) :
    ‖gloop (B.L N) (B.W N) M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      gmBlkM B N M z a₂ b * gmBlkM B N M z a₁ b * gmBlkM B N M z a₂ a₁ := by
  have : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  have : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  have h := Lemma57.norm_gloop_three_le (L := B.L N) (Wb := B.W N)
    (H := M) (z := z) false true true a₂ b a₁
    (gmBlkM_nonneg B N M z)
    (by
      intro p q hp hq
      rcases p with ⟨px, pi⟩
      rcases q with ⟨qy, qi⟩
      dsimp at hp hq ⊢
      subst px
      subst qy
      exact norm_Gsig_le_gmBlkM B N M z false a₁ a₂ pi qi)
    (by
      intro q r hq hr
      rcases q with ⟨qx, qi⟩
      rcases r with ⟨ry, ri⟩
      dsimp at hq hr ⊢
      subst qx
      subst ry
      exact norm_Gsig_le_gmBlkM B N M z true a₂ b qi ri)
    (by
      intro r p hr hp
      rcases r with ⟨rx, ri⟩
      rcases p with ⟨py, pi⟩
      dsimp at hr hp ⊢
      subst rx
      subst py
      exact norm_Gsig_le_gmBlkM B N M z true b a₁ ri pi)
  rw [gmBlkM_comm hM z b a₁, gmBlkM_comm hM z a₁ a₂] at h
  convert h using 1; ring

/-- **The `(+,-)` two-loop is bounded by the product of the two block maxima**, at matrix level
(matrix analogue of T1501's `two_loop_re_le_gsqBlk'`, stopped before the neighbour maximum). -/
theorem two_loop_re_le_gmBlkM {N : ℕ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (x y : ZMod (B.L N)) :
    (gloop (B.L N) (B.W N) M z ⟨[true, false], [x, y]⟩).re ≤
      gmBlkM B N M z x y * gmBlkM B N M z y x := by
  have : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  have : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  set G : ℝ := gmBlkM B N M z x y with hG
  have hterm (p q : ZMod (B.L N) × Fin (B.W N)) :
      Lemma57.blkW (B.L N) (B.W N) p y *
          (Lemma57.blkW (B.L N) (B.W N) q x * ‖green M z p q‖ ^ 2) ≤
      Lemma57.blkW (B.L N) (B.W N) p y * (Lemma57.blkW (B.L N) (B.W N) q x * G ^ 2) := by
    by_cases hp : p.1 = y
    · by_cases hq : q.1 = x
      · have hentry : ‖green M z p q‖ ≤ G := by
          rcases p with ⟨px, pi⟩
          rcases q with ⟨qx, qi⟩
          dsimp at hp hq ⊢
          subst px
          subst qx
          have h := norm_Gsig_le_gmBlkM B N M z true y x pi qi
          rw [Gsig_true] at h
          rw [gmBlkM_comm hM z y x] at h
          exact h
        have hsq : ‖green M z p q‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hentry 2
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq (Lemma57.blkW_nonneg (B.L N) (B.W N) q x))
          (Lemma57.blkW_nonneg (B.L N) (B.W N) p y)
      · simp [Lemma57.blkW, hq]
    · simp [Lemma57.blkW, hp]
  calc
    (gloop (B.L N) (B.W N) M z ⟨[true, false], [x, y]⟩).re =
        ∑ p : ZMod (B.L N) × Fin (B.W N), ∑ q : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) p y *
            (Lemma57.blkW (B.L N) (B.W N) q x * ‖green M z p q‖ ^ 2) :=
      (Lemma57.sum_blkW_normSq (B.L N) (B.W N) hM x y).symm
    _ ≤ ∑ p : ZMod (B.L N) × Fin (B.W N), ∑ q : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) p y * (Lemma57.blkW (B.L N) (B.W N) q x * G ^ 2) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = G ^ 2 := by
      have hinner (p : ZMod (B.L N) × Fin (B.W N)) :
          (∑ q : ZMod (B.L N) × Fin (B.W N),
              Lemma57.blkW (B.L N) (B.W N) p y * (Lemma57.blkW (B.L N) (B.W N) q x * G ^ 2)) =
            Lemma57.blkW (B.L N) (B.W N) p y * G ^ 2 := by
        rw [← Finset.mul_sum, ← Finset.sum_mul, Lemma57.sum_blkW, one_mul]
      simp_rw [hinner, ← Finset.sum_mul, Lemma57.sum_blkW, one_mul]
    _ = gmBlkM B N M z x y * gmBlkM B N M z y x := by
      rw [← gmBlkM_comm hM z x y, hG]; ring

end DriftPt

open DriftPt in
/-- **(T1), EG part: `eGpm_le_rhs535_of_jG_mat`** — T1501's `eGpm_le_rhs535_of_jG`
(`Hierarchy/Step2FarInputsJG.lean:170`) for an arbitrary Hermitian matrix `M` in place of
`X.H N u ω`, in the ticket's generic-`J` fallback form (T1513's `jGMat` is not merged): the two
block bounds that `jG` supplies are hypotheses, `h531` on the actual `(+,-)` two-loop of `M` and
`h42` on the concrete block maximum `gmBlkM` of `M`, both only on far pairs. **There is no `h560`
and no free `Gm`**: (5.60) is `DriftPt.norm_gloop_three_le_gmBlkM`, deterministic, every `b`.
Route (i). The compiled witness `eGpm_le_rhs535_of_jG_mat_sample` below instantiates `J := jG`. -/
theorem eGpm_le_rhs535_of_jG_mat {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓs D' : ℝ} (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ))
    (hℓu : 1 ≤ B.ell N u) (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hD : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (a₁ a₂ : ZMod (B.L N)) {J ρ κ : ℝ} (hJ : 1 ≤ J) (hρ : 0 ≤ ρ)
    (h273 : ∀ b, ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖
      ≤ (B.ell N u / ℓs) ^ 2 * ((((B.W N : ℝ) * B.ell N u * etaT E u)) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (a₂ - b) : ℝ) →
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          J * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' (zdist (B.L N) (x - y)))
    (h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        gmBlkM B N M (zt E u) x y ≤
          √J * √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' (zdist (B.L N) (x - y))))
    (h557C : ∀ (x y : ZMod (B.L N)) (p : ZMod (B.L N) × Fin (B.W N)), p.1 = y →
      ∑ r : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖
        ≤ √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : ZMod (B.L N) × Fin (B.W N)), r.1 = x →
      ∑ p : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖
        ≤ √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs) :
    ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) M (zt E u) a₁ a₂‖
      ≤ Step2FarInputs.rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) ℓs (etaT E u) D' J ρ
          (zdist (B.L N) (a₁ - a₂)) :=
  Step2FarInputs.eGpm_le_rhs535 hM hL hW hℓu hℓs hηu hJ hA hr hD a₁ a₂ hρ
    (gmBlkM_nonneg B N M (zt E u)) h273 h554 h531 h42 h557C h557R
    (fun b => norm_gloop_three_le_gmBlkM hM (zt E u) a₁ a₂ b) (mSigma E) hone hκ

open DriftPt in
/-- **Compiled satisfiability witness for (T1)'s generic-`J` hypotheses.** At any flow sample,
`M := X.H N u ω` and the genuine block-level `J := RBM.APrimeJG.jG` satisfy `hJ`, `h531`, `h42`
deterministically, and `eGpm_le_rhs535_of_jG_mat` reproduces T1501's `eGpm_le_rhs535_of_jG`. -/
theorem eGpm_le_rhs535_of_jG_mat_sample (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}
    {ℓs D' : ℝ} (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 1 ≤ B.ell N u)
    (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hD : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (a₁ a₂ : ZMod (B.L N)) {ρ κ : ℝ} (hρ : 0 ≤ ρ)
    (h273 : ∀ b, ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[false, true, true], [a₂, b, a₁]⟩‖
      ≤ (B.ell N u / ℓs) ^ 2 * ((((B.W N : ℝ) * B.ell N u * etaT E u)) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (a₂ - b) : ℝ) →
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h557C : ∀ (x y : ZMod (B.L N)) (p : ZMod (B.L N) × Fin (B.W N)), p.1 = y →
      ∑ r : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) r x * ‖green (X.H N u ω) (zt E u) r p‖
        ≤ √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : ZMod (B.L N) × Fin (B.W N)), r.1 = x →
      ∑ p : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) p y * ‖green (X.H N u ω) (zt E u) r p‖
        ≤ √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig (X.H N u ω) (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs) :
    ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) (X.H N u ω) (zt E u) a₁ a₂‖
      ≤ Step2FarInputs.rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) ℓs (etaT E u) D'
          (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D') ρ
          (zdist (B.L N) (a₁ - a₂)) := by
  have hWpos : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ1 : 1 ≤ APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D' :=
    APrimeJG.one_le_jG X E N u ω hWpos
  have hJ0 : 0 ≤ APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D' := hJ1.trans' (by norm_num)
  refine eGpm_le_rhs535_of_jG_mat (X.hermitian N u ω) hL hW hℓu hℓs hηu hA hr hD a₁ a₂ hJ1 hρ
    h273 h554 ?_ ?_ h557C h557R hone hκ
  · intro x y hxy
    exact ((two_loop_re_le_gmBlkM (X.hermitian N u ω) (zt E u) x y).trans
      (APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω x y)).trans
      (APrimeJG.gsqBlk_le_jG_mul_tailT X E N u ω hWpos x y hxy)
  · intro x y hxy
    rw [gmBlkM_sample]
    exact (APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail X E N u ω x y hxy).trans_eq
      (Real.sqrt_mul hJ0 _)

/-! ## (T2) : the σ-orientation check -/

/-- **(T2)**: `eGterm` at the `(+,-)` `2`-loop `⟨[true, false], [x, y]⟩` — this list literally
*is* `Step2.sigPM = ![true, false]` read as a two-element list, so the σ-orientation matches —
equals `EGDef.eGpm`. This is `EGDef.eGpm_eq_eGterm` read backwards; no coefficients or
relabelling are needed (unlike the `3`-loops inside `eGpm`'s own definition, whose labels are
exchanged relative to the paper's (5.51), see `EGDef.eGpm`'s docstring). -/
theorem eGterm_eq_eGpm (m : Bool → ℂ) {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (x y : ZMod L) :
    RBM.Gauss.eGterm L W m M z ⟨[true, false], [x, y]⟩ = EGDef.eGpm L W m M z x y :=
  (EGDef.eGpm_eq_eGterm m M z x y).symm

/-! ## (T3) : the pointwise drift bound on the good set -/

/-- **(T3)**: the pointwise drift bound `‖D(M) b‖ ≤ Mdr(u) · T_{u,D}(b)`, `D(M) := (eGterm +
primBil(A,A))(M)` the drift of T1506 (T4), `A := gloop(M) − Kval_u` restricted to the `(+,-)`
`2`-loop.

**Hypotheses**: `M` Hermitian; the structural scale facts `hL,hW,hℓu,hℓs,hηu,hA,hD,hr`; the
per-matrix inputs of (T1) that do not involve `jG`/`jGMat` (`h273`, `h554` with its `ρ`,
`h557C`/`h557R`, `hone` with its `κ`, `hκ`), each now quantified over every pair `(x,y)` (not
only a fixed one, since the conclusion is `∀ b`); the **generic-`J`** EG-part inputs `h531`,
`h42`, `h560`, `hGm`, `hJ` (T1501's own hypotheses, before it specializes `J := jG` — the
`jGMat(u,M) ≤ N^{2ε} thr(u)` route the ticket asks for is deferred to a corollary once T1513
merges, per the ticket's explicit fallback); and the quadratic-part input `hjS : jStar(A) ≤
thr(u)` (the genuine `Step2.jStar`/`GridJStar.jSMat`, **not** `EarlyQVRateEv.jStar`).

**Route**: EG part via (T2) (`eGterm_eq_eGpm`), (T1) (`Step2FarInputs.eGpm_le_rhs535` at `a₁ :=
b 0, a₂ := b 1`, then `rhs535_le_mul_tailT`, with the near/far indicator of `rhs535` coarsened
to its trivial bound `1` so that the resulting coefficient is `b`-independent, as
`weighted_duhamel_sum_le`'s `M j` must be). Quadratic part via `quadGlue_pm_eq_eLL_mat` then
`Step2.norm_eLL_le`, with `jStar ≤ jSMat ≤ thr(u)` substituted (`Step2.jStar` throughout, per
Step 0). `Mdr(u) := M₁ + exp 1 * thr(u) ^ 2 * (36 * (η_u⁻¹ * A_u⁻¹) + W * L * W ^ (-D))`, `M₁`
written out in full below. -/
theorem drift_point_le {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓs D δ : ℝ} {s : ℕ → ℝ}
    (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 1 ≤ B.ell N u)
    (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hDreg : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    {J : ℝ} (hJ : 1 ≤ J) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ (B.ell N u / ℓs) ^ 2 * (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹)
    (h554 : ∀ x y c : ZMod (B.L N),
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (y - c) : ℝ) →
        ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          J * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)))
    (h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        Gm x y ≤ √J * √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y))))
    (h557C : ∀ (x y : ZMod (B.L N)) (p : B.Idx N), p.1 = y →
      ∑ r : B.Idx N, Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : B.Idx N), r.1 = x →
      ∑ p : B.Idx N, Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h560 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤
        Gm y c * Gm x c * Gm y x)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs)
    (hjS : Step2.jStar (B.L N)
        (fun a : LoopArg (B.L N) 2 =>
          ‖gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
            - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
        (B.W N) (B.ell N u) (etaT E u) D ≤ Step2.thr E s δ N u) :
    ∀ b : LoopArg (B.L N) 2,
      ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], [b 0, b 1]⟩
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              ⟨[true, false], [b 0, b 1]⟩‖
        ≤ (((etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
                + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
                    (B.ell N u / ℓs * √(B.ell N u / ℓs)
                      * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
                + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
              + B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ
                  * (B.W N : ℝ) ^ D)
            + exp 1 * Step2.thr E s δ N u ^ 2 *
                (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
                  + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)))
          * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)) := by
  intro b
  set x := b 0 with hx
  set y := b 1 with hy
  have hWpos : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓupos : (0 : ℝ) < B.ell N u := by linarith
  -- (T2) + (T1), EG part
  have hEG := Step2FarInputs.eGpm_le_rhs535 (M := M) (z := zt E u) hM hL hW hℓu hℓs hηu hJ hA hr
    hDreg x y hρ hGm (h273 x y) (h554 x y) h531 h42 h557C h557R
    (h560 x y) (mSigma E) hone hκ
  have hEGmul := rhs535_le_mul_tailT (Wr := (B.W N : ℝ)) (Lr := (B.L N : ℝ)) (ℓu := B.ell N u)
    (ℓs := ℓs) (ηu := etaT E u) (D := D) (J := J) (ρ := ρ) (d := (zdist (B.L N) (x - y) : ℝ))
    hWpos hℓupos hℓs hηu hρ (Nat.cast_nonneg _)
  have hEGterm : RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], [x, y]⟩
      = EGDef.eGpm (B.L N) (B.W N) (mSigma E) M (zt E u) x y :=
    eGterm_eq_eGpm (mSigma E) M (zt E u) x y
  have hEGfinal : ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
      ⟨[true, false], [x, y]⟩‖ ≤
      ((etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
              * (if (zdist (B.L N) (x - y) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
                  then (1 : ℝ) else 0)
            + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
                (B.ell N u / ℓs * √(B.ell N u / ℓs)
                  * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
            + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
          + B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ * (B.W N : ℝ) ^ D)
        * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) := by
    rw [hEGterm]; exact hEG.trans hEGmul
  have hindicator : (if (zdist (B.L N) (x - y) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
      then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hcNear0 : 0 ≤ Lemma57.cNear (B.W N : ℝ) (B.ell N u) := Lemma57.cNear_nonneg hW hℓupos
  have hEGfinal' : ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
      ⟨[true, false], [x, y]⟩‖ ≤
      ((etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
            + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
                (B.ell N u / ℓs * √(B.ell N u / ℓs)
                  * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
            + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
          + B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ * (B.W N : ℝ) ^ D)
        * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) := by
    refine hEGfinal.trans (mul_le_mul_of_nonneg_right ?_
      (tailT_nonneg hWpos.le _))
    have hr30 : (0:ℝ) ≤ (B.ell N u / ℓs) ^ 3 := by positivity
    have hη0 : (0:ℝ) ≤ (etaT E u)⁻¹ := by positivity
    have hnear : Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
          * (if (zdist (B.L N) (x - y) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u) then (1:ℝ) else 0)
        ≤ Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3 := by
      have := mul_le_mul_of_nonneg_left hindicator (mul_nonneg hcNear0 hr30)
      linarith [this]
    have hcomb : (etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
              * (if (zdist (B.L N) (x - y) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u)
                  then (1 : ℝ) else 0)
            + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
                (B.ell N u / ℓs * √(B.ell N u / ℓs)
                  * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
            + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
        ≤ (etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
            + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
                (B.ell N u / ℓs * √(B.ell N u / ℓs)
                  * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
            + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J))) := by
      have := mul_le_mul_of_nonneg_left hnear hη0
      linarith [this]
    linarith [hcomb]
  -- Quadratic part
  have hA_def : (fun a : LoopArg (B.L N) 2 =>
        gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
          - B.Kval E N u (LoopData.idx (Step2.sigPM, a)))
      = (fun a : LoopArg (B.L N) 2 =>
        gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
          - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) := rfl
  have hquadEq := quadGlue_pm_eq_eLL_mat E N u M x y
  have hquad := Step2.norm_eLL_le hL hWpos hℓu hηu D
    (fun a : LoopArg (B.L N) 2 =>
      gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
        - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) ![x, y]
  have hJstarNonneg : 0 ≤ Step2.jStar (B.L N)
      (fun a : LoopArg (B.L N) 2 => ‖gloop (B.L N) (B.W N) M (zt E u)
          (LoopData.idx (Step2.sigPM, a)) - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
      (B.W N) (B.ell N u) (etaT E u) D :=
    (Step2.one_le_jStar hWpos (fun a => norm_nonneg _)).trans' (by norm_num)
  have hjSsq : Step2.jStar (B.L N)
      (fun a : LoopArg (B.L N) 2 => ‖gloop (B.L N) (B.W N) M (zt E u)
          (LoopData.idx (Step2.sigPM, a)) - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
      (B.W N) (B.ell N u) (etaT E u) D ^ 2 ≤ Step2.thr E s δ N u ^ 2 :=
    pow_le_pow_left₀ hJstarNonneg hjS 2
  have hquad' : ‖Step2.eLL (B.L N) (B.W N : ℝ)
      (fun a : LoopArg (B.L N) 2 =>
        gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
          - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) ![x, y]‖ ≤
      exp 1 * Step2.thr E s δ N u ^ 2 *
          (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
            + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D))
        * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (![x, y] 0 - ![x, y] 1)) := by
    refine hquad.trans ?_
    have he0 : (0:ℝ) ≤ exp 1 := (exp_pos 1).le
    have hbrak0 : (0:ℝ) ≤ 36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
        + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) := by positivity
    have hT0 : (0:ℝ) ≤ tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D
        (zdist (B.L N) (![x, y] 0 - ![x, y] 1)) := tailT_nonneg hWpos.le _
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjSsq hbrak0) hT0
    nlinarith [this]
  have hxy01 : (![x, y] : LoopArg (B.L N) 2) 0 - (![x, y] : LoopArg (B.L N) 2) 1 = x - y := by
    simp
  rw [hxy01] at hquad'
  have hprimBil : primBil (B.L N) (B.W N)
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨[true, false], [x, y]⟩
      = Step2.eLL (B.L N) (B.W N : ℝ)
          (fun a : LoopArg (B.L N) 2 =>
            gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
              - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) ![x, y] := hquadEq
  have hquadfinal : ‖primBil (B.L N) (B.W N)
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨[true, false], [x, y]⟩‖ ≤
      exp 1 * Step2.thr E s δ N u ^ 2 *
          (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
            + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D))
        * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) := by
    rw [hprimBil]; exact hquad'
  -- combine
  have htT_eq : Step2.tT B E N D u (zdist (B.L N) (x - y))
      = tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) := rfl
  rw [htT_eq]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add hEGfinal' hquadfinal
  nlinarith [this]

/-! ## (T3) in terms of an explicit coefficient function, with the block maximum -/

/-- **(T3)'s coefficient `Mdr(u)` as a function** of the time `u` and of the two per-matrix
inputs `J` (the generic `J` of (T3); `jGMat(u,M)` on the good set) and `ρ` (the far triple-loop
bound of `h554`). Literally the right-hand-side coefficient of `drift_point_le`, with
`ℓs` the reference scale:
`Mdr = η_u⁻¹ (c_near r³ + c_far r^{3/2} A_u^{-1/2} J + 169 r A_u⁻¹ J^{3/2}) + r (ℓ_u η_u)⁻¹ L ρ W^D
  + e thr(u)² (36 η_u⁻¹ A_u⁻¹ + W L W^{-D})`, `r = ℓ_u/ℓs`, `A_u = W ℓ_u η_u`. -/
noncomputable def mdr (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (δ D ℓs : ℝ) (N : ℕ) (u J ρ : ℝ) : ℝ :=
  ((etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
        + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
            (B.ell N u / ℓs * √(B.ell N u / ℓs)
              * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
        + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
      + B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ * (B.W N : ℝ) ^ D)
    + exp 1 * Step2.thr E s δ N u ^ 2 *
        (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
          + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D))

open DriftPt in
/-- **(T3), `h560`-free successor `drift_point_le_blk`**: `drift_point_le` with the free `Gm`
replaced by the concrete matrix block maximum `DriftPt.gmBlkM` and `h560`, `hGm` discharged
(`DriftPt.norm_gloop_three_le_gmBlkM`, `DriftPt.gmBlkM_nonneg`), stated with the coefficient
function `mdr`. The EG inputs are now exactly those of (T1) `eGpm_le_rhs535_of_jG_mat`
(`hJ`, `h531`, `h42` on `gmBlkM`); `drift_point_le` itself is unchanged. -/
theorem drift_point_le_blk {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓs D δ : ℝ} {s : ℕ → ℝ}
    (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 1 ≤ B.ell N u)
    (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hDreg : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    {J ρ κ : ℝ} (hJ : 1 ≤ J) (hρ : 0 ≤ ρ)
    (h273 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ (B.ell N u / ℓs) ^ 2 * (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹)
    (h554 : ∀ x y c : ZMod (B.L N),
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (y - c) : ℝ) →
        ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          J * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)))
    (h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        gmBlkM B N M (zt E u) x y ≤
          √J * √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y))))
    (h557C : ∀ (x y : ZMod (B.L N)) (p : B.Idx N), p.1 = y →
      ∑ r : B.Idx N, Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : B.Idx N), r.1 = x →
      ∑ p : B.Idx N, Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs)
    (hjS : Step2.jStar (B.L N)
        (fun a : LoopArg (B.L N) 2 =>
          ‖gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
            - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
        (B.W N) (B.ell N u) (etaT E u) D ≤ Step2.thr E s δ N u) :
    ∀ b : LoopArg (B.L N) 2,
      ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], [b 0, b 1]⟩
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              ⟨[true, false], [b 0, b 1]⟩‖
        ≤ mdr B E s δ D ℓs N u J ρ * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)) :=
  drift_point_le hM hL hW hℓu hℓs hηu hA hr hDreg hJ hρ (gmBlkM_nonneg B N M (zt E u))
    h273 h554 h531 h42 h557C h557R
    (fun x y c => norm_gloop_three_le_gmBlkM hM (zt E u) x y c) hone hκ hjS

/-! ## (T4) : the time sum of the drift bound

The target is `Σ_{j<k} Δ · Mdr(u_j) · ((1 - u_{j+1})/(1 - u_k))² ≤ Cdr · N^κ · (R_{u_k}^e + 1)`,
`R_w = η_s/η_w`, with `Mdr(u_j) = mdr … (u_j) (J_j) (ρ_j)` (T3's coefficient at the grid time with
its own per-time inputs). No monotonicity of `Mdr` in `j` is used. Every `η_{u_j}⁻¹` stays paired
with its own propagator factor (`step_bound`'s `hr2`), and `r_{u_j} = ℓ_{u_j}/ℓ_s` stays at its
own time (cap-robust `ℓ_w √(1-w) ≤ ℓ_s √(1-s)`), so the near term telescopes.
**Exponent `e = 2`**. -/

namespace DriftPt

/-- Cap-robust scale ratio: `ℓ_w √(1-w) ≤ ℓ_s √(1-s)` for `s ≤ w < 1`. -/
theorem ell_mul_sqrt_le (B : Band Ω) (N : ℕ) {s w : ℝ} (hw1 : w < 1) (hsw : s ≤ w) :
    B.ell N w * √(1 - w) ≤ B.ell N s * √(1 - s) := by
  have h1 : ∀ x : ℝ, x < 1 → B.ell N x * √(1 - x) = min 1 ((B.L N : ℝ) * √(1 - x)) := by
    intro x hx1
    have hsqrt : 0 < √(1 - x) := Real.sqrt_pos.2 (by linarith)
    unfold Band.ell
    rw [ellHat_ofReal _ hx1, min_mul_of_nonneg _ _ hsqrt.le, one_div_mul_cancel hsqrt.ne']
  rw [h1 w hw1, h1 s (hsw.trans_lt hw1)]
  exact min_le_min le_rfl
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Nat.cast_nonneg _))

/-- `c_near(W, ℓ) ≤ c_near(W, 1)` for `ℓ ≥ 1`. -/
theorem cNear_le_one {W ℓ : ℝ} (hℓ : 1 ≤ ℓ) : Lemma57.cNear W ℓ ≤ Lemma57.cNear W 1 := by
  unfold Lemma57.cNear
  have : 2 / ℓ ≤ 2 / 1 := div_le_div_of_nonneg_left (by norm_num) one_pos hℓ
  exact mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le

/-- `c_far(W, ℓ) ≤ c_far(W, 1)` for `ℓ ≥ 1`. -/
theorem cFar_le_one {W ℓ : ℝ} (hℓ : 1 ≤ ℓ) : Lemma57.cFar W ℓ ≤ Lemma57.cFar W 1 := by
  unfold Lemma57.cFar
  have : 8 / ℓ ≤ 8 / 1 := div_le_div_of_nonneg_left (by norm_num) one_pos hℓ
  exact mul_le_mul_of_nonneg_right (by linarith) (Lemma57.loss32_pos W).le

/-- **Telescoping** (no mesh condition): on a uniform grid with `u_k < 1`,
`Σ_{j<k} Δ/√(1-u_j) ≤ 2√(1-u_0)`, from `Δ/√a ≤ 2(√a - √(a-Δ))`. -/
theorem sum_step_div_sqrt_le (u : ℕ → ℝ) (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hu_step : ∀ j, u (j + 1) = u j + Δ) {k : ℕ} (huk1 : u k < 1) :
    ∑ j ∈ Finset.range k, Δ / √(1 - u j) ≤ 2 * √(1 - u 0) := by
  have hu_mono : Monotone u :=
    monotone_nat_of_le_succ fun j => by rw [hu_step j]; linarith
  have hterm : ∀ j ∈ Finset.range k,
      Δ / √(1 - u j) ≤ 2 * (√(1 - u j) - √(1 - u (j + 1))) := by
    intro j hj
    have hj1k : j + 1 ≤ k := Finset.mem_range.1 hj
    have hb0 : 0 ≤ 1 - u (j + 1) := by linarith [hu_mono hj1k]
    have ha0 : 0 < 1 - u j := by linarith [hu_mono (Nat.le_succ j), hu_mono hj1k]
    have hsa : 0 < √(1 - u j) := Real.sqrt_pos.2 ha0
    have hsa2 : √(1 - u j) ^ 2 = 1 - u j := Real.sq_sqrt ha0.le
    have hsb2 : √(1 - u (j + 1)) ^ 2 = 1 - u (j + 1) := Real.sq_sqrt hb0
    have hamgm : 2 * (√(1 - u j) * √(1 - u (j + 1))) ≤ (1 - u j) + (1 - u (j + 1)) := by
      nlinarith [sq_nonneg (√(1 - u j) - √(1 - u (j + 1)))]
    rw [div_le_iff₀ hsa]
    have hΔ : Δ = (1 - u j) - (1 - u (j + 1)) := by rw [hu_step j]; ring
    nlinarith
  calc ∑ j ∈ Finset.range k, Δ / √(1 - u j)
      ≤ ∑ j ∈ Finset.range k, 2 * (√(1 - u j) - √(1 - u (j + 1))) := Finset.sum_le_sum hterm
    _ = 2 * (√(1 - u 0) - √(1 - u k)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub' (fun j => √(1 - u j)) k]
    _ ≤ 2 * √(1 - u 0) := by linarith [Real.sqrt_nonneg (1 - u k)]

/-- **Pointwise domination, scalar core.** With `η = a m`, `A = W ℓ_w η`, `r = ℓ_w/ℓ_s`,
`thr = x (c₀/a)^4` (`a = 1-w`, `b = 1-v`, `c₀ = 1-s`, `x = N^δ`), the six pieces of
`Mdr(w) · p` (`p ≤ (a/b)²` the propagator factor) are bounded as in the (T4) preflight. -/
theorem mdr_core {W L ℓw ℓs a b c0 m x J ρ D cNw cFw cN cF p : ℝ}
    (hW1 : 1 ≤ W) (hL0 : 0 ≤ L) (hm0 : 0 < m) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hac : a ≤ c0) (hℓs1 : 1 ≤ ℓs) (hℓsw : ℓs ≤ ℓw) (hrsq : ℓw / ℓs * √a ≤ √c0)
    (hx1 : 1 ≤ x) (hAw : x ^ 24 * (c0 / a) ^ 30 ≤ W * ℓw * (a * m))
    (hAv : x ^ 24 * (c0 / b) ^ 30 ≤ W * L)
    (hJ1 : 1 ≤ J) (hJx : J ≤ x ^ 2 * (c0 / a) ^ 4) (hρ0 : 0 ≤ ρ) (hρ : L * ρ * W ^ D ≤ 1)
    (hcNw0 : 0 ≤ cNw) (hcNw : cNw ≤ cN) (hcFw0 : 0 ≤ cFw) (hcFw : cFw ≤ cF)
    (hp0 : 0 ≤ p) (hp : p ≤ (a / b) ^ 2) :
    (((a * m)⁻¹ * (cNw * (ℓw / ℓs) ^ 3
          + cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J)
          + 169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J)))
        + ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ * W ^ D)
      + exp 1 * (x * (c0 / a) ^ 4) ^ 2 *
          (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹) + W * L * W ^ (-D))) * p
      ≤ cN * c0 * √c0 / (m * b ^ 2) / √a
        + (cF + 170 + 36 * exp 1) / (m * b ^ 2) * a
        + exp 1 * ((W * L) ^ 2 * W ^ (-D)) := by
  have hW0 : 0 < W := by linarith
  have hc0 : 0 < c0 := by linarith
  have hℓw : 0 < ℓw := by linarith
  have hℓs : 0 < ℓs := by linarith
  have hr0 : 0 ≤ ℓw / ℓs := div_nonneg hℓw.le hℓs.le
  have hr1 : 1 ≤ ℓw / ℓs := by rw [le_div_iff₀ hℓs]; linarith
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsc : 0 < √c0 := Real.sqrt_pos.2 hc0
  have hr2a : (ℓw / ℓs) ^ 2 * a ≤ c0 := by
    have h := pow_le_pow_left₀ (mul_nonneg hr0 hsa.le) hrsq 2
    rwa [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hc0.le] at h
  have hRw1 : 1 ≤ c0 / a := by rw [le_div_iff₀ ha]; linarith
  have hRwv : c0 / a ≤ c0 / b := div_le_div_of_nonneg_left hc0.le hb hba
  have hRv1 : 1 ≤ c0 / b := hRw1.trans hRwv
  have hr2R : (ℓw / ℓs) ^ 2 ≤ c0 / a := by rw [le_div_iff₀ ha]; exact hr2a
  have hrR : ℓw / ℓs ≤ c0 / a := (le_self_pow₀ hr1 two_ne_zero).trans hr2R
  have hRw0 : 0 ≤ c0 / a := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hApos : 0 < W * ℓw * (a * m) := by positivity
  have hmono : ∀ i j : ℕ, i ≤ 24 → j ≤ 30 → x ^ i * (c0 / a) ^ j ≤ W * ℓw * (a * m) :=
    fun i j hi hj =>
      (mul_le_mul (pow_le_pow_right₀ hx1 hi) (pow_le_pow_right₀ hRw1 hj) (by positivity)
        (by positivity)).trans hAw
  have hJ0 : 0 ≤ J := by linarith
  have habs1 : (ℓw / ℓs) ^ 3 * J ^ 2 ≤ W * ℓw * (a * m) :=
    calc (ℓw / ℓs) ^ 3 * J ^ 2 ≤ (c0 / a) ^ 3 * (x ^ 2 * (c0 / a) ^ 4) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ hr0 hrR 3) (pow_le_pow_left₀ hJ0 hJx 2) (by positivity)
            (by positivity)
      _ = x ^ 4 * (c0 / a) ^ 11 := by ring
      _ ≤ W * ℓw * (a * m) := hmono 4 11 (by norm_num) (by norm_num)
  have habs2 : ℓw / ℓs * J ^ 2 ≤ W * ℓw * (a * m) :=
    calc ℓw / ℓs * J ^ 2 ≤ c0 / a * (x ^ 2 * (c0 / a) ^ 4) ^ 2 :=
          mul_le_mul hrR (pow_le_pow_left₀ hJ0 hJx 2) (by positivity) (by positivity)
      _ = x ^ 4 * (c0 / a) ^ 9 := by ring
      _ ≤ W * ℓw * (a * m) := hmono 4 9 (by norm_num) (by norm_num)
  have habs3 : (x * (c0 / a) ^ 4) ^ 2 ≤ W * ℓw * (a * m) := by
    calc (x * (c0 / a) ^ 4) ^ 2 = x ^ 2 * (c0 / a) ^ 8 := by ring
      _ ≤ W * ℓw * (a * m) := hmono 2 8 (by norm_num) (by norm_num)
  have habs4 : x ^ 2 * (c0 / b) ^ 8 ≤ W * L :=
    (mul_le_mul (pow_le_pow_right₀ hx1 (by norm_num : 2 ≤ 24))
      (pow_le_pow_right₀ hRv1 (by norm_num : 8 ≤ 30)) (by positivity) (by positivity)).trans hAv
  -- the pairing `η_w⁻¹ p ≤ a/(m b²)`
  have hq0 : 0 ≤ (a * m)⁻¹ * p := by positivity
  have hq : (a * m)⁻¹ * p ≤ a / (m * b ^ 2) := by
    calc (a * m)⁻¹ * p ≤ (a * m)⁻¹ * (a / b) ^ 2 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = a / (m * b ^ 2) := by field_simp
  have hQ0 : 0 ≤ a / (m * b ^ 2) := by positivity
  have hcN0 : 0 ≤ cN := hcNw0.trans hcNw
  have hcF0 : 0 ≤ cF := hcFw0.trans hcFw
  -- (a) near
  have hTa : (a * m)⁻¹ * (cNw * (ℓw / ℓs) ^ 3) * p ≤ cN * c0 * √c0 / (m * b ^ 2) / √a := by
    have hr3 : (ℓw / ℓs) ^ 3 * a ≤ c0 * √c0 / √a := by
      rw [le_div_iff₀ hsa]
      calc (ℓw / ℓs) ^ 3 * a * √a = ((ℓw / ℓs) ^ 2 * a) * (ℓw / ℓs * √a) := by ring
        _ ≤ c0 * √c0 := mul_le_mul hr2a hrsq (by positivity) hc0.le
    calc (a * m)⁻¹ * (cNw * (ℓw / ℓs) ^ 3) * p
        = cNw * (ℓw / ℓs) ^ 3 * ((a * m)⁻¹ * p) := by ring
      _ ≤ cN * (ℓw / ℓs) ^ 3 * (a / (m * b ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcNw (by positivity)) hq hq0 (by positivity)
      _ = cN * ((ℓw / ℓs) ^ 3 * a) / (m * b ^ 2) := by ring
      _ ≤ cN * (c0 * √c0 / √a) / (m * b ^ 2) := by gcongr
      _ = cN * c0 * √c0 / (m * b ^ 2) / √a := by ring
  -- (b) far, `c_far` part
  have hTb : (a * m)⁻¹ * (cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J)) * p
      ≤ cF * (a / (m * b ^ 2)) := by
    have hsA : 0 < √(W * ℓw * (a * m)) := Real.sqrt_pos.2 hApos
    have hk : ℓw / ℓs * √(ℓw / ℓs) * J ≤ √(W * ℓw * (a * m)) := by
      have h1 : (ℓw / ℓs * √(ℓw / ℓs) * J) ^ 2 ≤ (√(W * ℓw * (a * m))) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hr0, Real.sq_sqrt hApos.le]
        calc (ℓw / ℓs) ^ 2 * (ℓw / ℓs) * J ^ 2 = (ℓw / ℓs) ^ 3 * J ^ 2 := by ring
          _ ≤ W * ℓw * (a * m) := habs1
      exact (pow_le_pow_iff_left₀ (by positivity) hsA.le (by norm_num)).1 h1
    have hk' : ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J ≤ 1 := by
      rw [show ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J
          = ℓw / ℓs * √(ℓw / ℓs) * J / √(W * ℓw * (a * m)) by ring, div_le_one hsA]
      exact hk
    calc (a * m)⁻¹ * (cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J)) * p
        = cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J) * ((a * m)⁻¹ * p) := by
          ring
      _ ≤ cF * 1 * (a / (m * b ^ 2)) :=
          mul_le_mul (mul_le_mul hcFw hk' (by positivity) hcF0) hq hq0 (by positivity)
      _ = cF * (a / (m * b ^ 2)) := by ring
  -- (c) far, `169` part
  have hTc : (a * m)⁻¹ * (169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J))) * p
      ≤ 169 * (a / (m * b ^ 2)) := by
    have hsJ : √J ≤ J := by
      have := Real.sqrt_le_sqrt (le_self_pow₀ hJ1 two_ne_zero)
      rwa [Real.sqrt_sq hJ0] at this
    have hk : ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J) ≤ 1 := by
      rw [show ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J)
          = ℓw / ℓs * (J * √J) / (W * ℓw * (a * m)) by ring, div_le_one hApos]
      calc ℓw / ℓs * (J * √J) ≤ ℓw / ℓs * (J * J) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsJ hJ0) hr0
        _ = ℓw / ℓs * J ^ 2 := by ring
        _ ≤ W * ℓw * (a * m) := habs2
    calc (a * m)⁻¹ * (169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J))) * p
        = 169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J)) * ((a * m)⁻¹ * p) := by ring
      _ ≤ 169 * 1 * (a / (m * b ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hq hq0 (by positivity)
      _ = 169 * (a / (m * b ^ 2)) := by ring
  -- (d) the `ρ` remainder
  have hTd : ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ * W ^ D * p ≤ a / (m * b ^ 2) := by
    have hinv : ℓs⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓs1
    have heq : ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ * W ^ D * p
        = ℓs⁻¹ * (L * ρ * W ^ D) * ((a * m)⁻¹ * p) := by
      field_simp
    rw [heq]
    have hρ' : 0 ≤ L * ρ * W ^ D := by have := Real.rpow_nonneg hW0.le D; positivity
    calc ℓs⁻¹ * (L * ρ * W ^ D) * ((a * m)⁻¹ * p) ≤ 1 * 1 * (a / (m * b ^ 2)) :=
          mul_le_mul (mul_le_mul hinv hρ hρ' zero_le_one) hq hq0 (by norm_num)
      _ = a / (m * b ^ 2) := by ring
  -- (e) the `36 η⁻¹ A⁻¹ thr²` part
  have hTe : exp 1 * (x * (c0 / a) ^ 4) ^ 2 * (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹)) * p
      ≤ 36 * exp 1 * (a / (m * b ^ 2)) := by
    have hk : (x * (c0 / a) ^ 4) ^ 2 * (W * ℓw * (a * m))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hApos]; exact habs3
    calc exp 1 * (x * (c0 / a) ^ 4) ^ 2 * (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹)) * p
        = 36 * exp 1 * ((x * (c0 / a) ^ 4) ^ 2 * (W * ℓw * (a * m))⁻¹) * ((a * m)⁻¹ * p) := by
          ring
      _ ≤ 36 * exp 1 * 1 * (a / (m * b ^ 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hk (by positivity)) hq hq0 (by positivity)
      _ = 36 * exp 1 * (a / (m * b ^ 2)) := by ring
  -- (f) the `W L W^{-D} thr²` part
  have hTf : exp 1 * (x * (c0 / a) ^ 4) ^ 2 * (W * L * W ^ (-D)) * p
      ≤ exp 1 * ((W * L) ^ 2 * W ^ (-D)) := by
    have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    have hk : (x * (c0 / a) ^ 4) ^ 2 * p ≤ W * L := by
      have hRab : c0 / a * (a / b) = c0 / b := by field_simp
      calc (x * (c0 / a) ^ 4) ^ 2 * p ≤ (x * (c0 / a) ^ 4) ^ 2 * (a / b) ^ 2 :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = x ^ 2 * (c0 / a) ^ 6 * (c0 / a * (a / b)) ^ 2 := by ring
        _ = x ^ 2 * (c0 / a) ^ 6 * (c0 / b) ^ 2 := by rw [hRab]
        _ ≤ x ^ 2 * (c0 / b) ^ 6 * (c0 / b) ^ 2 := by gcongr
        _ = x ^ 2 * (c0 / b) ^ 8 := by ring
        _ ≤ W * L := habs4
    calc exp 1 * (x * (c0 / a) ^ 4) ^ 2 * (W * L * W ^ (-D)) * p
        = exp 1 * (W * L * W ^ (-D)) * ((x * (c0 / a) ^ 4) ^ 2 * p) := by ring
      _ ≤ exp 1 * (W * L * W ^ (-D)) * (W * L) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = exp 1 * ((W * L) ^ 2 * W ^ (-D)) := by ring
  -- assemble
  have hRHS : (cF + 170 + 36 * exp 1) / (m * b ^ 2) * a
      = cF * (a / (m * b ^ 2)) + 169 * (a / (m * b ^ 2)) + a / (m * b ^ 2)
        + 36 * exp 1 * (a / (m * b ^ 2)) := by ring
  rw [hRHS]
  have hsplit : (((a * m)⁻¹ * (cNw * (ℓw / ℓs) ^ 3
          + cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J)
          + 169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J)))
        + ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ * W ^ D)
      + exp 1 * (x * (c0 / a) ^ 4) ^ 2 *
          (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹) + W * L * W ^ (-D))) * p
      = (a * m)⁻¹ * (cNw * (ℓw / ℓs) ^ 3) * p
        + (a * m)⁻¹ * (cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J)) * p
        + (a * m)⁻¹ * (169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J))) * p
        + ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ * W ^ D * p
        + exp 1 * (x * (c0 / a) ^ 4) ^ 2 * (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹)) * p
        + exp 1 * (x * (c0 / a) ^ 4) ^ 2 * (W * L * W ^ (-D)) * p := by ring
  rw [hsplit]
  linarith [hTa, hTb, hTc, hTd, hTe, hTf]

/-- **Pointwise domination of one summand** (`s ≤ w ≤ w' ≤ v ≤ t < 1`, `w = u_j`,
`w' = u_{j+1}`, `v = u_k`):
`Mdr(w) ((1-w')/(1-v))² ≤ c_near(W,1)(1-s)^{3/2}/(m(1-v)²) · (1-w)^{-1/2}
  + (c_far(W,1) + 170 + 36e)/(m(1-v)²) · (1-w) + e (WL)² W^{-D}`. -/
theorem mdr_mul_le (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {δ ε D c : ℝ} {N : ℕ}
    {w w' v t J ρ : ℝ} (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsw : s N ≤ w) (hww' : w ≤ w')
    (hw'v : w' ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hreg : (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 ≤ B.scale E N t)
    (hδ0 : 0 ≤ δ) (hδc : 24 * δ ≤ c) (hεδ : 2 * ε ≤ δ)
    (hJ1 : 1 ≤ J) (hJ : J ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N w)
    (hρ0 : 0 ≤ ρ) (hρ : (B.L N : ℝ) * ρ * (B.W N : ℝ) ^ D ≤ 1) :
    mdr B E s δ D (B.ell N (s N)) N w J ρ * ((1 - w') / (1 - v)) ^ 2 ≤
      Lemma57.cNear (B.W N : ℝ) 1 * (1 - s N) * √(1 - s N) / ((mE E).im * (1 - v) ^ 2)
          / √(1 - w)
        + (Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1) / ((mE E).im * (1 - v) ^ 2) * (1 - w)
        + exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) := by
  have hW1 : (1 : ℝ) ≤ B.W N := B.one_le_W N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hw1 : w < 1 := by linarith
  have hv1 : v < 1 := by linarith
  have hs1 : s N < 1 := by linarith
  have hw0 : 0 ≤ w := hs0.trans hsw
  have hv0 : 0 ≤ v := by linarith
  have hwt : w ≤ t := by linarith
  have ha : 0 < 1 - w := by linarith
  have hb : 0 < 1 - v := by linarith
  have hc0 : 0 < 1 - s N := by linarith
  have ht0 : 0 < 1 - t := by linarith
  -- scales
  have hℓw1 : 1 ≤ B.ell N w := one_le_ellHat_of_nonneg hL1 hw0 hw1
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1 hs0 hs1
  have hℓsw : B.ell N (s N) ≤ B.ell N w := Step3.ellHat_mono hsw hw1
  have hℓvL : B.ell N v ≤ (B.L N : ℝ) := min_le_right _ _
  have hℓv1 : 1 ≤ B.ell N v := one_le_ellHat_of_nonneg hL1 hv0 hv1
  have hK := ell_mul_sqrt_le B N hw1 hsw
  have hrsq : B.ell N w / B.ell N (s N) * √(1 - w) ≤ √(1 - s N) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  -- `N^δ`, the gain, and `J`
  have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have hx24 : ((N : ℝ) ^ δ) ^ 24 ≤ (N : ℝ) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hNε : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
  have hthr : Step2.thr E s δ N w = (N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4 := by
    rw [Step2.thr, Step2.etaT_ratio hE]
  have hJx : J ≤ ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - w)) ^ 4 := by
    have h0 : 0 ≤ (N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4 := by positivity
    calc J ≤ (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4) := hthr ▸ hJ
      _ ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4) :=
          mul_le_mul_of_nonneg_right hNε h0
      _ = ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - w)) ^ 4 := by ring
  -- `hreg` transported to `w` and to `v`
  have hRt : etaT E (s N) / etaT E t = (1 - s N) / (1 - t) := Step2.etaT_ratio hE _ _
  have hscale_w : B.scale E N t ≤ B.scale E N w :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hw1.le) (Set.mem_Iic.2 ht1.le) hwt
  have hscale_v : B.scale E N t ≤ B.scale E N v :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hv1.le) (Set.mem_Iic.2 ht1.le) hvt
  have hNc0 : 0 ≤ (N : ℝ) ^ c := by positivity
  have hreg' : ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30 ≤ B.scale E N t := by
    calc ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30
        ≤ (N : ℝ) ^ c * ((1 - s N) / (1 - t)) ^ 30 :=
          mul_le_mul_of_nonneg_right hx24 (by positivity)
      _ = (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 := by rw [hRt]
      _ ≤ B.scale E N t := hreg
  have hAw : ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - w)) ^ 30
      ≤ (B.W N : ℝ) * B.ell N w * ((1 - w) * (mE E).im) := by
    have h1 : ((1 - s N) / (1 - w)) ^ 30 ≤ ((1 - s N) / (1 - t)) ^ 30 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hc0.le ht0 (by linarith)) 30
    calc ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - w)) ^ 30
        ≤ ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ B.scale E N t := hreg'
      _ ≤ B.scale E N w := hscale_w
      _ = (B.W N : ℝ) * B.ell N w * ((1 - w) * (mE E).im) := rfl
  have hAv : ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - v)) ^ 30 ≤ (B.W N : ℝ) * B.L N := by
    have h1 : ((1 - s N) / (1 - v)) ^ 30 ≤ ((1 - s N) / (1 - t)) ^ 30 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hc0.le ht0 (by linarith)) 30
    have hsv : B.scale E N v ≤ (B.W N : ℝ) * B.L N := by
      change (B.W N : ℝ) * B.ell N v * ((1 - v) * (mE E).im) ≤ (B.W N : ℝ) * B.L N
      have h2 : (1 - v) * (mE E).im ≤ 1 := by nlinarith
      calc (B.W N : ℝ) * B.ell N v * ((1 - v) * (mE E).im)
          ≤ (B.W N : ℝ) * B.L N * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hℓvL hW0.le) h2 (by positivity)
              (by positivity)
        _ = (B.W N : ℝ) * B.L N := mul_one _
    calc ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - v)) ^ 30
        ≤ ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ B.scale E N t := hreg'
      _ ≤ B.scale E N v := hscale_v
      _ ≤ (B.W N : ℝ) * B.L N := hsv
  have hp : ((1 - w') / (1 - v)) ^ 2 ≤ ((1 - w) / (1 - v)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hb.le)
      (div_le_div_of_nonneg_right (by linarith) hb.le) 2
  have hcore := mdr_core (L := (B.L N : ℝ)) (D := D) hW1 (Nat.cast_nonneg _) hm0 ha hb
    (by linarith) (by linarith) hℓs1 hℓsw hrsq hx1 hAw hAv hJ1 hJx hρ0 hρ
    (Lemma57.cNear_nonneg hW1 (by linarith)) (cNear_le_one hℓw1)
    (Lemma57.cFar_nonneg hW1 (by linarith)) (cFar_le_one hℓw1) (sq_nonneg _) hp
  unfold mdr
  rw [hthr]
  exact hcore

end DriftPt

open DriftPt in
/-- **(T4), deterministic core at one size parameter `N`.** For a uniform grid
`u_{j+1} = u_j + Δ` with `s N ≤ u_0`, `u_k ≤ t < 1`, step2's `hreg` at `t` with gain `c`,
`0 ≤ δ`, `24δ ≤ c`, `2ε ≤ δ`, and per-time inputs `1 ≤ J_j ≤ N^{2ε} thr(u_j)`,
`0 ≤ ρ_j`, `L ρ_j W^D ≤ 1` (for `j < k`):
`Σ_{j<k} Δ Mdr(u_j) ((1-u_{j+1})/(1-u_k))²
  ≤ (2 c_near(W,1) + c_far(W,1) + 170 + 36e) · m⁻¹ · (η_s/η_{u_k})² + e (WL)² W^{-D}`.
Exponent `2` on `R_{u_k} = η_s/η_{u_k}`; no monotonicity of `Mdr`, no mesh condition. -/
theorem drift_time_sum_le_of (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ}
    {δ ε D c : ℝ} {N : ℕ} (u : ℕ → ℝ) (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hu_step : ∀ j, u (j + 1) = u j + Δ) (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N)
    (hsu : s N ≤ u 0) {k : ℕ} {t : ℝ} (hkt : u k ≤ t) (ht1 : t < 1)
    (hreg : (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 ≤ B.scale E N t)
    (hδ0 : 0 ≤ δ) (hδc : 24 * δ ≤ c) (hεδ : 2 * ε ≤ δ)
    (J ρ : ℕ → ℝ) (hJ1 : ∀ j < k, 1 ≤ J j)
    (hJ : ∀ j < k, J j ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (u j))
    (hρ0 : ∀ j < k, 0 ≤ ρ j) (hρ : ∀ j < k, (B.L N : ℝ) * ρ j * (B.W N : ℝ) ^ D ≤ 1) :
    ∑ j ∈ Finset.range k, Δ * mdr B E s δ D (B.ell N (s N)) N (u j) (J j) (ρ j) *
        ((1 - u (j + 1)) / (1 - u k)) ^ 2
      ≤ (2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1)
          * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (u k)) ^ 2
        + exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) := by
  have hu_mono : Monotone u :=
    monotone_nat_of_le_succ fun j => by rw [hu_step j]; linarith
  have hu_eq : ∀ j : ℕ, u j = u 0 + (j : ℝ) * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ n ih => rw [hu_step n, ih]; push_cast; ring
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have huk1 : u k < 1 := by linarith
  have hb : 0 < 1 - u k := by linarith
  have hs1 : s N < 1 := by linarith [hu_mono (Nat.zero_le k)]
  have hW0 : (0 : ℝ) < B.W N := by have := B.one_le_W N; linarith
  set α := Lemma57.cNear (B.W N : ℝ) 1 * (1 - s N) * √(1 - s N) / ((mE E).im * (1 - u k) ^ 2)
    with hα
  set β := (Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1) / ((mE E).im * (1 - u k) ^ 2)
    with hβ
  set γ := exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) with hγ
  have hcN0 : 0 ≤ Lemma57.cNear (B.W N : ℝ) 1 := Lemma57.cNear_nonneg (B.one_le_W N) one_pos
  have hcF0 : 0 ≤ Lemma57.cFar (B.W N : ℝ) 1 := Lemma57.cFar_nonneg (B.one_le_W N) one_pos
  have hα0 : 0 ≤ α := by
    rw [hα]; have : 0 ≤ 1 - s N := by linarith
    positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hγ0 : 0 ≤ γ := by rw [hγ]; have := Real.rpow_nonneg hW0.le (-D); positivity
  have hterm : ∀ j ∈ Finset.range k,
      Δ * mdr B E s δ D (B.ell N (s N)) N (u j) (J j) (ρ j) * ((1 - u (j + 1)) / (1 - u k)) ^ 2
        ≤ α * (Δ / √(1 - u j)) + Δ * (β * (1 - s N) + γ) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    have hsj : s N ≤ u j := hsu.trans (hu_mono (Nat.zero_le j))
    have hjj : u j ≤ u (j + 1) := hu_mono (Nat.le_succ j)
    have hj1k : u (j + 1) ≤ u k := hu_mono hjk
    have hpt := mdr_mul_le B hE hN1 hs0 hsj hjj hj1k hkt ht1 hreg hδ0 hδc hεδ (hJ1 j hjk)
      (hJ j hjk) (hρ0 j hjk) (hρ j hjk)
    have hβj : β * (1 - u j) ≤ β * (1 - s N) := mul_le_mul_of_nonneg_left (by linarith) hβ0
    calc Δ * mdr B E s δ D (B.ell N (s N)) N (u j) (J j) (ρ j) * ((1 - u (j + 1)) / (1 - u k)) ^ 2
        = Δ * (mdr B E s δ D (B.ell N (s N)) N (u j) (J j) (ρ j) *
            ((1 - u (j + 1)) / (1 - u k)) ^ 2) := by ring
      _ ≤ Δ * (α / √(1 - u j) + β * (1 - u j) + γ) := mul_le_mul_of_nonneg_left hpt hΔ0
      _ ≤ Δ * (α / √(1 - u j) + β * (1 - s N) + γ) := by gcongr
      _ = α * (Δ / √(1 - u j)) + Δ * (β * (1 - s N) + γ) := by ring
  have hkΔ : (k : ℝ) * Δ ≤ 1 - s N := by
    have := hu_eq k; linarith
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := by positivity
  have htel := DriftPt.sum_step_div_sqrt_le u Δ hΔ0 hu_step huk1
  have hsq0 : √(1 - u 0) ≤ √(1 - s N) := Real.sqrt_le_sqrt (by linarith)
  have hC0 : 0 ≤ β * (1 - s N) + γ := by
    have : 0 ≤ 1 - s N := by linarith
    positivity
  have hRatio : etaT E (s N) / etaT E (u k) = (1 - s N) / (1 - u k) := Step2.etaT_ratio hE _ _
  have hss : √(1 - s N) * √(1 - s N) = 1 - s N := Real.mul_self_sqrt (by linarith)
  calc ∑ j ∈ Finset.range k, Δ * mdr B E s δ D (B.ell N (s N)) N (u j) (J j) (ρ j) *
          ((1 - u (j + 1)) / (1 - u k)) ^ 2
      ≤ ∑ j ∈ Finset.range k, (α * (Δ / √(1 - u j)) + Δ * (β * (1 - s N) + γ)) :=
        Finset.sum_le_sum hterm
    _ = α * ∑ j ∈ Finset.range k, Δ / √(1 - u j) + (k : ℝ) * Δ * (β * (1 - s N) + γ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
    _ ≤ α * (2 * √(1 - s N)) + (1 - s N) * (β * (1 - s N) + γ) := by
        gcongr
        exact htel.trans (by linarith)
    _ ≤ α * (2 * √(1 - s N)) + (β * (1 - s N) ^ 2 + γ) := by
        have : (1 - s N) * γ ≤ γ := mul_le_of_le_one_left hγ0 (by linarith [hs0])
        nlinarith
    _ = (2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1)
          * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (u k)) ^ 2 + γ := by
        rw [hRatio, hα, hβ]
        have hb2 : (1 - u k) ^ 2 ≠ 0 := by positivity
        field_simp
        have hsq : √(1 - s N) ^ 2 = 1 - s N := Real.sq_sqrt (by linarith)
        linear_combination (2 * Lemma57.cNear (B.W N : ℝ) 1 * (1 - s N)) * hsq

namespace DriftPt

/-- **Stretched-exponential absorption** of the two `W^{o(1)}` coefficients: for every `κ > 0`,
eventually `c_near(W,1) ≤ N^κ` and `c_far(W,1) ≤ N^κ`. -/
theorem eventually_cNear_cFar_le (B : Band Ω) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in Filter.atTop, Lemma57.cNear (B.W N : ℝ) 1 ≤ (N : ℝ) ^ κ ∧
      Lemma57.cFar (B.W N : ℝ) 1 ≤ (N : ℝ) ^ κ := by
  have ha : 0 < κ / 2 := by positivity
  have hlog3 := (Asymptotics.isLittleO_iff_nat_mul_le'.1
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) ha)) 8
  have hlog32 := (Asymptotics.isLittleO_iff_nat_mul_le'.1
    (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) ha)) 16
  have hW3 := (Step2.tendsto_W B).eventually hlog3
  have hW32 := (Step2.tendsto_W B).eventually hlog32
  have hexpW := (Step2.tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 1 ha)
  have h16 := ((tendsto_rpow_atTop ha).comp (Step2.tendsto_W B)).eventually_ge_atTop 16
  filter_upwards [hW3, hW32, hexpW, h16, B.dim] with N h3 h32 hex h16N hdim
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := B.one_le_W N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hWN : (B.W N : ℝ) ≤ N := by
    have hL : (1 : ℝ) ≤ (B.L N : ℝ) := by exact_mod_cast B.one_le_L N
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hlog0 : 0 ≤ Real.log (B.W N : ℝ) := Real.log_nonneg hW1
  set P := (B.W N : ℝ) ^ (κ / 2) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hW0.le _
  have h3' : 8 * Real.log (B.W N : ℝ) ^ (3 : ℝ) ≤ P := by
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg hP0] using h3
  have h32' : 16 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) ≤ P := by
    simpa only [Nat.cast_ofNat, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
      abs_of_nonneg hP0] using h32
  have hex' : exp (Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) ≤ P := by
    simpa only [one_mul] using hex
  have h16' : (16 : ℝ) ≤ P := by simpa only [Function.comp_apply] using h16N
  have hPP : P * P ≤ (N : ℝ) ^ κ := by
    rw [hP, ← Real.rpow_add hW0, add_halves]
    exact Real.rpow_le_rpow hW0.le hWN hκ.le
  have hl3 : 0 ≤ Real.log (B.W N : ℝ) ^ (3 : ℝ) := Real.rpow_nonneg hlog0 _
  have hl32 : 0 ≤ Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hlog0 _
  have hl34 : 0 ≤ Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg hlog0 _
  refine ⟨?_, ?_⟩
  · unfold Lemma57.cNear
    calc (2 * Real.log (B.W N : ℝ) ^ (3 : ℝ) + 2 / 1) * exp (Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))
        ≤ P * P := mul_le_mul (by linarith) hex' (exp_pos _).le (by linarith)
      _ ≤ (N : ℝ) ^ κ := hPP
  · unfold Lemma57.cFar Lemma57.loss32
    have hsq : √(1 / 2 : ℝ) ≤ 1 := Real.sqrt_le_one.2 (by norm_num)
    have hl : exp (√(1 / 2 : ℝ) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))
        ≤ exp (Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ)) := by
      apply exp_le_exp.2
      nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ)]
    calc (4 * Real.log (B.W N : ℝ) ^ (3 / 2 : ℝ) + 8 / 1)
          * exp (√(1 / 2 : ℝ) * Real.log (B.W N : ℝ) ^ (3 / 4 : ℝ))
        ≤ P * P := mul_le_mul (by linarith) (hl.trans hex') (exp_pos _).le (by linarith)
      _ ≤ (N : ℝ) ^ κ := hPP

/-- Eventually `(WL)² W^{-D} ≤ 1` for `D ≥ 4` (from `WL ≤ N ≤ W²`). -/
theorem eventually_sq_WL_rpow_le (B : Band Ω) {D : ℝ} (hD : 4 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D) ≤ 1 := by
  filter_upwards [B.dim, Step2.eventually_le_W_sq B] with N hdim hNW
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := B.one_le_W N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
  have hWL0 : 0 ≤ (B.W N : ℝ) * (B.L N : ℝ) := by positivity
  have h1 : ((B.W N : ℝ) * B.L N) ^ 2 ≤ (B.W N : ℝ) ^ (4 : ℝ) := by
    calc ((B.W N : ℝ) * B.L N) ^ 2 ≤ ((B.W N : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ hWL0 (hWL.trans hNW) 2
      _ = (B.W N : ℝ) ^ (4 : ℝ) := by
          rw [← pow_mul, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hWD : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  calc ((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)
      ≤ (B.W N : ℝ) ^ (4 : ℝ) * (B.W N : ℝ) ^ (-D) := mul_le_mul_of_nonneg_right h1 hWD
    _ = (B.W N : ℝ) ^ (4 - D) := by rw [← Real.rpow_add hW0]; ring_nf
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)

end DriftPt

/-- The explicit constant of (T4): `Cdr = 300 / Im m(E)`; it depends only on `E`. -/
noncomputable def driftSumConst (E : ℝ) : ℝ := 300 / (mE E).im

open DriftPt in
/-- **(T4) `RBM.Gauss.Grid.drift_time_sum_le`** — the time sum of (T3)'s pointwise drift bound,
with the propagator factor and endpoint `u_k`.

**Superseded by (T4') `drift_time_sum_le'`; its `LρW^D ≤ 1` premise is unsatisfiable with
T1513's ρ** (`rho554(J) ≥ η_u⁻¹ W^{-D}` forces `L η_u⁻¹ ≤ 1`). Kept only for reference.

Hypotheses: `|E| < 2`, `0 ≤ s`, `t < 1`, step2's `hreg` with gain `c` (eventually, at `t N`),
`0 ≤ δ ≤ c/24`, `2ε ≤ δ`, `4 ≤ D`. Conclusion: for every `κ > 0`, eventually in `N`, uniformly in
the endpoint `T N ∈ [s N, t N]`, the step count `Kq N ≥ 1`, every `k ≤ Kq N`, and every choice of
per-time inputs with `1 ≤ J_j ≤ N^{2ε} thr(u_j)` (the ticket's `jGMat(u_j) ≤ N^{2ε} thr(u_j)`),
`0 ≤ ρ_j`, `L ρ_j W^D ≤ 1` (`j < k`), with `u_j = Grid.time s T Kq N j`, `Δ = Grid.step s T Kq N`:
`Σ_{j<k} Δ · Mdr(u_j) · ((1-u_{j+1})/(1-u_k))² ≤ (300/Im m) · N^κ · ((η_s/η_{u_k})² + 1)`,
`Mdr(u_j) = mdr B E s δ D ℓ_s N u_j J_j ρ_j` (T3's coefficient, `drift_point_le_blk`).

**Exponent `e = 2`**: `phi`'s drift-slot prefactor `m⁻¹R²` with an `N^{o(1)}` bracket — one
power of `R` better than `phi_arith`'s `m⁻¹R²q ≤ R³`. The hypothesis `L ρ_j W^D ≤ 1` is the
ρ-smallness the ticket asked to check; with T1513's `rho554` at the same `D` it fails (see
above), which is why (T4') confines the (5.54) residue to the near band instead. -/
theorem drift_time_sum_le (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) (hεδ : 2 * ε ≤ δ) (hD : 4 ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N → ∀ J ρ : ℕ → ℝ,
        (∀ j < k, 1 ≤ J j) →
        (∀ j < k, J j ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s T Kq N j)) →
        (∀ j < k, 0 ≤ ρ j) →
        (∀ j < k, (B.L N : ℝ) * ρ j * (B.W N : ℝ) ^ D ≤ 1) →
        ∑ j ∈ Finset.range k, step s T Kq N *
            mdr B E s δ D (B.ell N (s N)) N (time s T Kq N j) (J j) (ρ j) *
            ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 2
          ≤ driftSumConst E * (N : ℝ) ^ κ *
              ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 2 + 1) := by
  intro κ hκ
  filter_upwards [eventually_cNear_cFar_le B hκ, eventually_sq_WL_rpow_le B hD, hreg,
    Filter.eventually_ge_atTop 1]
    with N hcNF hWL hregN hN1 T Kq hsT hTt hK k hk J ρ hJ1 hJ hρ0 hρ
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hKpos : (0 : ℝ) < (Kq N : ℝ) := by exact_mod_cast hK
  have hΔ0 : 0 ≤ step s T Kq N := div_nonneg (by linarith) hKpos.le
  have hKΔ : (Kq N : ℝ) * step s T Kq N = T N - s N := by
    unfold step; field_simp
  have hu_step : ∀ j, time s T Kq N (j + 1) = time s T Kq N j + step s T Kq N := by
    intro j; unfold time; push_cast; ring
  have hkt : time s T Kq N k ≤ t N := by
    have : (k : ℝ) ≤ Kq N := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right this hΔ0
    unfold time; linarith
  have hcore := drift_time_sum_le_of B hE (time s T Kq N) (step s T Kq N) hΔ0 hu_step hN1'
    (hs0 N) (by simp) hkt (ht1 N) hregN hδ0 (by linarith) hεδ J ρ hJ1 hJ hρ0 hρ
  refine hcore.trans ?_
  obtain ⟨hcN, hcF⟩ := hcNF
  set P := (N : ℝ) ^ κ with hP
  set R2 := (etaT E (s N) / etaT E (time s T Kq N k)) ^ 2 with hR2
  set mi := ((mE E).im)⁻¹ with hmi
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1' hκ.le
  have hR20 : 0 ≤ R2 := sq_nonneg _
  have hmi1 : 1 ≤ mi := (one_le_inv₀ hm0).2 hm1
  have he3 : exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < exp 1 := exp_pos 1
  have hγ : exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) ≤ 3 :=
    (mul_le_mul_of_nonneg_left hWL he0.le).trans (by linarith)
  have hbr : 2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1
      ≤ 274 * P := by
    have := Real.exp_one_lt_d9
    linarith
  have hbr0 : 0 ≤ 2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170
      + 36 * exp 1 := by
    have := Lemma57.cNear_nonneg (B.one_le_W N) one_pos
    have := Lemma57.cFar_nonneg (B.one_le_W N) one_pos
    positivity
  have hdc : driftSumConst E = 300 * mi := by rw [driftSumConst, hmi]; ring
  rw [hdc]
  have hmiR : 0 ≤ mi * R2 := by positivity
  have h1 : (2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1)
      * mi * R2 ≤ 274 * P * (mi * R2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hbr hmiR
  have hPm : 1 ≤ P * mi := one_le_mul_of_one_le_of_one_le hP1 hmi1
  have hX0 : 0 ≤ P * mi * R2 := by positivity
  have e1 : 274 * P * (mi * R2) = 274 * (P * mi * R2) := by ring
  have e2 : 300 * mi * P * (R2 + 1) = 300 * (P * mi * R2) + 300 * (P * mi) := by ring
  rw [e2]
  linarith

/-! ### Witness for the per-time inputs of (T4)

`J_j := 1`, `ρ_j := 0` satisfy the per-time hypotheses of `drift_time_sum_le` at every grid time
`u ∈ [s N, 1)` once `N ≥ 1`, `0 ≤ ε`, `0 ≤ δ` (the remaining hypotheses — `hreg`, `δ ≤ c/24`,
`2ε ≤ δ`, `D ≥ 4` — are those of T1508's compiled witness
`RBM.Gauss.Grid.qv_time_sum_le_hyps_witness`, with `D = 60`). -/
theorem drift_time_sum_inputs_witness (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ}
    {δ ε D : ℝ} {N : ℕ} (hN1 : (1 : ℝ) ≤ N) (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) {u : ℝ}
    (hsu : s N ≤ u) (hu1 : u < 1) :
    (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ∧
      (0 : ℝ) ≤ 0 ∧ (B.L N : ℝ) * 0 * (B.W N : ℝ) ^ D ≤ 1 := by
  refine ⟨le_rfl, ?_, le_rfl, by simp⟩
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hR : 1 ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith)]; linarith
  have h1 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have h2 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have h3 : 1 ≤ (etaT E (s N) / etaT E u) ^ 4 := one_le_pow₀ hR
  unfold Step2.thr
  calc (1 : ℝ) = 1 * (1 * 1) := by ring
    _ ≤ (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 4) := by gcongr

/-! ## (R1)-(R2) : the (5.54) residue confined to the near band (amend-1, option (d)) -/

/-- **(R1) `eG_le'`**: `RBM.Lemma57.eG_le` with the (5.54) residue `κ₁ (ℓ_u η_u)⁻¹ L ρ`
multiplied by the near indicator `1(‖a₁-a₂‖ ≤ ℓ*_u)`. Same hypotheses as `eG_le`. Near branch:
exactly `Lemma57.eG_near_le`. Far branch: exactly `Lemma57.eG_far_le` (no `h554`, no `ρ`): the
near term and the residue are both `0` there, as in the paper (p.59: (5.54) is used only for
`|a₁-a₂| ≤ ℓ*_u`). -/
theorem eG_le' (L : ℕ) [NeZero L] {W ℓu ℓs ηu D J : ℝ}
    (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (a₁ a₂ : ZMod L)
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {κ₁ κ₂ ρ EG : ℝ}
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, L3 b ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L3 b ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * κ₂)
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * κ₂)
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ κ₁ * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * κ₁ * (Lemma57.cNear W ℓu * (ℓu / ℓs) ^ 2 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0)
        + Lemma57.cFar W ℓu * J * κ₂
        + J * √J * (168 * (W * ℓu * ηu)⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂))
      + κ₁ * (ℓu * ηu)⁻¹ * L * ρ *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0) := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hsJ : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hcF : 0 ≤ Lemma57.cFar W ℓu := Lemma57.cFar_nonneg hW hℓ
  have hε : (0 : ℝ) ≤ √(W ^ (-D)) := Real.sqrt_nonneg _
  have hfarterm : (0 : ℝ) ≤ ηu⁻¹ * κ₁ * (Lemma57.cFar W ℓu * J * κ₂
      + J * √J * (168 * (W * ℓu * ηu)⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by positivity
  split_ifs with hd
  · have := Lemma57.eG_near_le (D := D) L hW hℓu hℓs hηu hd hρ hκ₁ h273 h554 hEG
    have heq : ηu⁻¹ * κ₁ * ((2 * log W ^ (3 : ℝ) + 2 / ℓu) * (ℓu / ℓs) ^ 2 *
        exp (log W ^ (3 / 4 : ℝ))) * tailT W ℓu ηu D (zdist L (a₁ - a₂))
        = ηu⁻¹ * κ₁ * (Lemma57.cNear W ℓu * (ℓu / ℓs) ^ 2 * 1) *
          tailT W ℓu ηu D (zdist L (a₁ - a₂)) := by
      unfold Lemma57.cNear; ring
    rw [heq] at this
    nlinarith [this, hfarterm]
  · rw [not_le] at hd
    have := Lemma57.eG_far_le L hW hℓu hηu hJ hd.le hκ₁ hκ₂ hGm h531 h42 h558a h558b h560 hEG
    calc EG ≤ _ := this
      _ = _ := by ring

/-- **(R2) `eG_le_reduced_of_schwarz'`**: `RBM.Lemma57.eG_le_reduced_of_schwarz` (shape 2 of
(5.35)) re-proved from `eG_le'`: the residue `r (ℓ_u η_u)⁻¹ L ρ` carries the near indicator. -/
theorem eG_le_reduced_of_schwarz' (L : ℕ) [NeZero L] {W ℓu ℓs ηu D J : ℝ}
    (hW : 1 ≤ W) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ W * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * √(W ^ (-D)) ≤ ℓu * (W * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L)
    {L2 Gm : ZMod L → ZMod L → ℝ} {L3 : ZMod L → ℝ} {ρ EG : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, L3 b ≤ (ℓu / ℓs) ^ 2 * ((W * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar W ℓu < (zdist L (a₁ - b) : ℝ) → L3 b ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      L2 x y ≤ J * tailT W ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar W ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT W ℓu ηu D (zdist L (x - y))))
    (h558a : ∀ b, (zdist L (a₁ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 a₂ b) * (√(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹))
    (h558b : ∀ b, (zdist L (a₂ - b) : ℝ) ≤ ellStar W ℓu / 2 →
      L3 b ≤ (L2 a₂ a₁ + L2 b a₁) * (√(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹))
    (h560 : ∀ b, L3 b ≤ Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ * ∑ b : ZMod L, L3 b) :
    EG ≤ ηu⁻¹ * (Lemma57.cNear W ℓu * (ℓu / ℓs) ^ 3 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0)
        + Lemma57.cFar W ℓu * ((ℓu / ℓs) * √(ℓu / ℓs) * (√(W * ℓu * ηu))⁻¹ * J)
        + 169 * ((ℓu / ℓs) * (W * ℓu * ηu)⁻¹ * (J * √J)))
      * tailT W ℓu ηu D (zdist L (a₁ - a₂))
      + (ℓu / ℓs) * (ℓu * ηu)⁻¹ * L * ρ *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0) := by
  set A : ℝ := W * ℓu * ηu with hAdef
  set r : ℝ := ℓu / ℓs with hrdef
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ : 0 < ℓu := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hT0 : 0 ≤ tailT W ℓu ηu D (zdist L (a₁ - a₂)) := tailT_nonneg hW0.le _
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hsJ : (0 : ℝ) ≤ √J := Real.sqrt_nonneg _
  have hsA : (0 : ℝ) < √A := Real.sqrt_pos.2 hA0
  have hκ₂0 : (0 : ℝ) ≤ √r * (√A)⁻¹ := by positivity
  have hmaster := eG_le' L hW hℓu hℓs hηu hJ a₁ a₂ hr0 hκ₂0 hρ hGm h273 h554 h531 h42
    h558a h558b h560 hEG
  refine hmaster.trans ?_
  set ind : ℝ := if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar W ℓu then 1 else 0 with hind
  have hη0 : (0 : ℝ) < ηu⁻¹ := by positivity
  have hfloor : (L : ℝ) * √(W ^ (-D)) / ℓu ≤ A⁻¹ := by
    rw [div_le_iff₀ hℓ]
    calc (L : ℝ) * √(W ^ (-D)) ≤ ℓu * A⁻¹ := hD
      _ = A⁻¹ * ℓu := by ring
  have u2 : 168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu ≤ 169 * A⁻¹ := by linarith [hfloor]
  have t2 := mul_le_mul_of_nonneg_left u2 (by positivity : (0 : ℝ) ≤ r * (J * √J))
  have hXY : r * (Lemma57.cNear W ℓu * r ^ 2 * ind + Lemma57.cFar W ℓu * J * (√r * (√A)⁻¹)
        + J * √J * (168 * A⁻¹ + (L : ℝ) * √(W ^ (-D)) / ℓu)) ≤
      Lemma57.cNear W ℓu * r ^ 3 * ind + Lemma57.cFar W ℓu * (r * √r * (√A)⁻¹ * J)
        + 169 * (r * A⁻¹ * (J * √J)) := by
    linarith [t2]
  have hTt := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXY hη0.le) hT0
  linarith [hTt]

/-- **(R2) `eG_le_reduced'`**: `RBM.Lemma57.eG_le_reduced` (shape 2, `3`-loops of `RBM.gloop`,
(5.58) proved by `Lemma57.gloop_h558a'`/`b'`) with the residue carrying the near indicator. -/
theorem eG_le_reduced' (L : ℕ) [NeZero L] {ℓu ℓs ηu D J : ℝ} (Wb : ℕ) [NeZero Wb]
    {H : Matrix (ZMod L × Fin Wb) (ZMod L × Fin Wb) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (hW : 1 ≤ (Wb : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hJ : 1 ≤ J) (hA : 1 ≤ (Wb : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * √((Wb : ℝ) ^ (-D)) ≤ ℓu * ((Wb : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ EG : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((Wb : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (Wb : ℝ) ℓu < (zdist L (a₁ - b) : ℝ) →
      ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (Wb : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L Wb H z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (Wb : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (Wb : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ √J * √(tailT (Wb : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin Wb), p.1 = y →
      ∑ r : ZMod L × Fin Wb, Lemma57.blkW L Wb r x * ‖green H z r p‖ ≤
        √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹)
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin Wb), r.1 = x →
      ∑ p : ZMod L × Fin Wb, Lemma57.blkW L Wb p y * ‖green H z r p‖ ≤
        √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹)
    (h560 : ∀ b, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖ ≤
      Gm a₁ b * Gm a₂ b * Gm a₁ a₂)
    (hEG : EG ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ *
      ∑ b : ZMod L, ‖gloop L Wb H z ⟨[false, true, true], [a₁, b, a₂]⟩‖) :
    EG ≤ ηu⁻¹ * (Lemma57.cNear (Wb : ℝ) ℓu * (ℓu / ℓs) ^ 3 *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar (Wb : ℝ) ℓu then 1 else 0)
        + Lemma57.cFar (Wb : ℝ) ℓu *
            ((ℓu / ℓs) * √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹ * J)
        + 169 * ((ℓu / ℓs) * ((Wb : ℝ) * ℓu * ηu)⁻¹ * (J * √J)))
      * tailT (Wb : ℝ) ℓu ηu D (zdist L (a₁ - a₂))
      + (ℓu / ℓs) * (ℓu * ηu)⁻¹ * L * ρ *
          (if (zdist L (a₁ - a₂) : ℝ) ≤ ellStar (Wb : ℝ) ℓu then 1 else 0) := by
  have hκ : (0 : ℝ) ≤ √(ℓu / ℓs) * (√((Wb : ℝ) * ℓu * ηu))⁻¹ := by positivity
  exact eG_le_reduced_of_schwarz' L hW hℓu hℓs hηu hJ hA hr hD a₁ a₂ hρ hGm h273 h554 h531 h42
    (fun b _ => Lemma57.gloop_h558a' L Wb hH a₁ a₂ b hκ (h557C a₁ b) (h557R a₁ b))
    (fun b _ => Lemma57.gloop_h558b' L Wb hH a₁ a₂ b hκ (h557C b a₂) (h557R b a₂)) h560 hEG

/-- **(R2) `eGpm_le_reduced'`**: `RBM.EGDef.eGpm_le_reduced` ((5.35) for `E^{(G̃)}` itself,
shape 2) with the (5.54) residue carrying the near indicator `1(‖a₂-a₁‖ ≤ ℓ*_u)`. -/
theorem eGpm_le_reduced' {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    {ℓu ℓs ηu D J : ℝ} (hM : M.IsHermitian) (hL : 3 ≤ L)
    (hW : 1 ≤ (W : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (W : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * Real.sqrt ((W : ℝ) ^ (-D)) ≤ ℓu * ((W : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((W : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (W : ℝ) ℓu < (zdist L (a₂ - b) : ℝ) →
      ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L W M z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (W : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ Real.sqrt J * Real.sqrt (tailT (W : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin W), p.1 = y →
      ∑ r : ZMod L × Fin W, Lemma57.blkW L W r x * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin W), r.1 = x →
      ∑ p : ZMod L × Fin W, Lemma57.blkW L W p y * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h560 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      Gm a₂ b * Gm a₁ b * Gm a₂ a₁)
    (m : Bool → ℂ)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M z σ
        - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)‖
      ≤ κ * ((W : ℝ) * ℓu * ηu)⁻¹)
    (hκ : 2 * κ ≤ ℓu / ℓs) :
    ‖EGDef.eGpm L W m M z a₁ a₂‖
      ≤ ηu⁻¹ * (Lemma57.cNear (W : ℝ) ℓu * (ℓu / ℓs) ^ 3 *
            (if (zdist L (a₂ - a₁) : ℝ) ≤ ellStar (W : ℝ) ℓu then 1 else 0)
          + Lemma57.cFar (W : ℝ) ℓu *
              ((ℓu / ℓs) * Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹ * J)
          + 169 * ((ℓu / ℓs) * ((W : ℝ) * ℓu * ηu)⁻¹ * (J * Real.sqrt J)))
        * tailT (W : ℝ) ℓu ηu D (zdist L (a₂ - a₁))
        + (ℓu / ℓs) * (ℓu * ηu)⁻¹ * (L : ℝ) * ρ *
            (if (zdist L (a₂ - a₁) : ℝ) ≤ ellStar (W : ℝ) ℓu then 1 else 0) := by
  have hS0 : (0 : ℝ) ≤ ∑ b : ZMod L, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbase := EGDef.norm_eGpm_le (L := L) (W := W) hL hM m (c := κ * ((W : ℝ) * ℓu * ηu)⁻¹)
    hone a₁ a₂
  have hcoef : 2 * (W : ℝ) * (κ * ((W : ℝ) * ℓu * ηu)⁻¹) ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ := by
    have hW0 : (0 : ℝ) < W := by linarith
    have hℓ0 : (0 : ℝ) < ℓu := by linarith
    have hEq : 2 * (W : ℝ) * (κ * ((W : ℝ) * ℓu * ηu)⁻¹) = (2 * κ) * (ℓu * ηu)⁻¹ := by
      field_simp
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hκ (by positivity)
  have hEG : ‖EGDef.eGpm L W m M z a₁ a₂‖
      ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ *
        ∑ b : ZMod L, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ :=
    hbase.trans (mul_le_mul_of_nonneg_right hcoef hS0)
  exact eG_le_reduced' L W hM hW hℓu hℓs hηu hJ hA hr hD a₂ a₁ hρ hGm
    h273 h554 h531 h42 h557C h557R h560 hEG

/-- **`rhs535'`**: `RBM.Step2FarInputs.rhs535` (the right-hand side of (5.35), shape 2) with its
additive (5.54) term `ℓu/ℓs · (ℓu ηu)⁻¹ · Lr · ρ` multiplied by the near indicator
`1(d ≤ ℓ*_u)`. -/
noncomputable def rhs535' (Wr Lr ℓu ℓs ηu D J ρ d : ℝ) : ℝ :=
  ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * (if d ≤ ellStar Wr ℓu then 1 else 0)
      + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
      + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
    * tailT Wr ℓu ηu D d
  + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * (if d ≤ ellStar Wr ℓu then 1 else 0)

/-- `rhs535' ≤ rhs535` (the residue only loses its far part). -/
theorem rhs535'_le_rhs535 {Wr Lr ℓu ℓs ηu D J ρ d : ℝ} (hℓu : 0 < ℓu) (hℓs : 0 < ℓs)
    (hηu : 0 < ηu) (hLr : 0 ≤ Lr) (hρ : 0 ≤ ρ) :
    rhs535' Wr Lr ℓu ℓs ηu D J ρ d ≤ Step2FarInputs.rhs535 Wr Lr ℓu ℓs ηu D J ρ d := by
  have h0 : 0 ≤ ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ := by positivity
  have hi : (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  unfold rhs535' Step2FarInputs.rhs535
  nlinarith [mul_le_mul_of_nonneg_left hi h0]

/-- **(R2) `eGpm_le_rhs535'`**: the frozen `RBM.Step2FarInputs.eGpm_le_rhs535` with `rhs535'`
(residue on the near band only). Same hypotheses. -/
theorem eGpm_le_rhs535' {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    {ℓu ℓs ηu D J : ℝ} (hM : M.IsHermitian) (hL : 3 ≤ L)
    (hW : 1 ≤ (W : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (W : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * Real.sqrt ((W : ℝ) ^ (-D)) ≤ ℓu * ((W : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((W : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (W : ℝ) ℓu < (zdist L (a₂ - b) : ℝ) →
      ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L W M z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (W : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ Real.sqrt J * Real.sqrt (tailT (W : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin W), p.1 = y →
      ∑ r : ZMod L × Fin W, Lemma57.blkW L W r x * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin W), r.1 = x →
      ∑ p : ZMod L × Fin W, Lemma57.blkW L W p y * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h560 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      Gm a₂ b * Gm a₁ b * Gm a₂ a₁)
    (m : Bool → ℂ)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M z σ
        - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)‖
      ≤ κ * ((W : ℝ) * ℓu * ηu)⁻¹)
    (hκ : 2 * κ ≤ ℓu / ℓs) :
    ‖EGDef.eGpm L W m M z a₁ a₂‖
      ≤ rhs535' (W : ℝ) (L : ℝ) ℓu ℓs ηu D J ρ (zdist L (a₁ - a₂)) := by
  rw [rhs535', Lemma57.zdist_sub_comm L a₁ a₂]
  exact eGpm_le_reduced' hM hL hW hℓu hℓs hηu hJ hA hr hD a₁ a₂ hρ hGm h273 h554 h531
    h42 h557C h557R h560 m hone hκ

open DriftPt in
/-- **(R2) `eGpm_le_rhs535_of_jG_mat'`**: (T1) `eGpm_le_rhs535_of_jG_mat` with `rhs535'`
(the (5.54) residue on the near band only). Hypotheses identical to (T1); no `h560`, no free
`Gm` ((5.60) is `DriftPt.norm_gloop_three_le_gmBlkM`). -/
theorem eGpm_le_rhs535_of_jG_mat' {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓs D' : ℝ} (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ))
    (hℓu : 1 ≤ B.ell N u) (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hD : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (a₁ a₂ : ZMod (B.L N)) {J ρ κ : ℝ} (hJ : 1 ≤ J) (hρ : 0 ≤ ρ)
    (h273 : ∀ b, ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖
      ≤ (B.ell N u / ℓs) ^ 2 * ((((B.W N : ℝ) * B.ell N u * etaT E u)) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (a₂ - b) : ℝ) →
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          J * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' (zdist (B.L N) (x - y)))
    (h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        gmBlkM B N M (zt E u) x y ≤
          √J * √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' (zdist (B.L N) (x - y))))
    (h557C : ∀ (x y : ZMod (B.L N)) (p : ZMod (B.L N) × Fin (B.W N)), p.1 = y →
      ∑ r : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖
        ≤ √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : ZMod (B.L N) × Fin (B.W N)), r.1 = x →
      ∑ p : ZMod (B.L N) × Fin (B.W N),
          Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖
        ≤ √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs) :
    ‖EGDef.eGpm (B.L N) (B.W N) (mSigma E) M (zt E u) a₁ a₂‖
      ≤ rhs535' (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) ℓs (etaT E u) D' J ρ
          (zdist (B.L N) (a₁ - a₂)) :=
  eGpm_le_rhs535' hM hL hW hℓu hℓs hηu hJ hA hr hD a₁ a₂ hρ
    (gmBlkM_nonneg B N M (zt E u)) h273 h554 h531 h42 h557C h557R
    (fun b => norm_gloop_three_le_gmBlkM hM (zt E u) a₁ a₂ b) (mSigma E) hone hκ

/-! ## (R3) : absorbing the near-band residue into the near slot -/

/-- **(R3), generic step (any `ρ ≥ 0`, no smallness hypothesis).** On the near band
`d ≤ ℓ*_u`, `A_u⁻² ≤ e^{(log W)^{3/4}} T_{u,D}(d)` (`Lemma57.inv_sq_le_tailT`), so the residue
`c · 1(near)` of `rhs535'` is at most `c · e^{(log W)^{3/4}} A_u² · 1(near) · T_{u,D}(d)`; off the
band it is `0`. -/
theorem rhs535'_le_mul_tailT_near {Wr Lr ℓu ℓs ηu D J ρ d : ℝ}
    (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hρ : 0 ≤ ρ) (hLr : 0 ≤ Lr) :
    rhs535' Wr Lr ℓu ℓs ηu D J ρ d ≤
      (ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0)
            + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
            + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
          + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * (exp (log Wr ^ (3 / 4 : ℝ)) * (Wr * ℓu * ηu) ^ 2)
            * (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0))
        * tailT Wr ℓu ηu D d := by
  have hW0 : (0 : ℝ) < Wr := by linarith
  have hT0 : 0 ≤ tailT Wr ℓu ηu D d := tailT_nonneg hW0.le d
  have hX0 : 0 ≤ ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ := by positivity
  unfold rhs535'
  split_ifs with hd
  · have hinv := Lemma57.inv_sq_le_tailT (D := D) hW hℓu hηu hd
    have hA0 : 0 < (Wr * ℓu * ηu) ^ 2 := by positivity
    have h1 : 1 ≤ exp (log Wr ^ (3 / 4 : ℝ)) * (Wr * ℓu * ηu) ^ 2 * tailT Wr ℓu ηu D d := by
      have h2 := mul_le_mul_of_nonneg_left hinv hA0.le
      rw [mul_inv_cancel₀ hA0.ne'] at h2
      calc (1 : ℝ) ≤ (Wr * ℓu * ηu) ^ 2 * (exp (log Wr ^ (3 / 4 : ℝ)) * tailT Wr ℓu ηu D d) := h2
        _ = _ := by ring
    have key := mul_le_mul_of_nonneg_left h1 hX0
    calc _ = ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * 1
            + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
            + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J))) * tailT Wr ℓu ηu D d
          + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * 1 := rfl
      _ ≤ ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * 1
            + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
            + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J))) * tailT Wr ℓu ηu D d
          + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ *
            (exp (log Wr ^ (3 / 4 : ℝ)) * (Wr * ℓu * ηu) ^ 2 * tailT Wr ℓu ηu D d) := by
          linarith [key]
      _ = _ := by ring
  · exact le_of_eq (by ring)

namespace DriftPt

/-- `e^{(log W)^{3/4}} ≤ W` once `W ≥ 8` (then `log W ≥ 1`). -/
theorem exp_log_rpow_le_self {W : ℝ} (hW8 : 8 ≤ W) : exp (log W ^ (3 / 4 : ℝ)) ≤ W := by
  have hW0 : 0 < W := by linarith
  have hlog1 : 1 ≤ log W := by
    rw [Real.le_log_iff_exp_le hW0]
    have := Real.exp_one_lt_d9
    linarith
  have h : log W ^ (3 / 4 : ℝ) ≤ log W := by
    calc log W ^ (3 / 4 : ℝ) ≤ log W ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
      _ = log W := Real.rpow_one _
  calc exp (log W ^ (3 / 4 : ℝ)) ≤ exp (log W) := exp_le_exp.2 h
    _ = W := Real.exp_log hW0

/-- **(R3), the absorption arithmetic.** The residue coefficient
`c_ρ = r (ℓ_u η_u)⁻¹ L ρ e^{(log W)^{3/4}} A_u²` of `rhs535'_le_mul_tailT_near` is `≤ η_u⁻¹`
under T1513's `ρ ≤ 2 η_u⁻¹ J W^{-D}` (`rho554_le_two_mul_rpow`, at the **same** `D`), with
`ℓ_u ≤ L ≤ W`, `J ≤ W`, `η_u ≤ 1`, `r = ℓ_u/ℓ_s ≤ g ℓ_u`, `g ≤ 4 W^{2ζ}`, `W ≥ 8` and
`D ≥ D₀ := 8 + 2ζ`: indeed `c_ρ ≤ 2 (r ℓ_u) L J e^λ W^{2-D} ≤ 8 W^{2ζ+7-D} ≤ 8/W ≤ 1`. -/
theorem resCoef_le {Wr Lr ℓu ℓs ηu D J ρ g ζ : ℝ} (hW8 : 8 ≤ Wr) (hℓu : 0 < ℓu)
    (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hη1 : ηu ≤ 1)
    (hρ : ρ ≤ 2 * ηu⁻¹ * J * Wr ^ (-D)) (hJ0 : 0 ≤ J) (hJW : J ≤ Wr) (hℓL : ℓu ≤ Lr)
    (hLW : Lr ≤ Wr) (hr : ℓu / ℓs ≤ g * ℓu) (hgW : g ≤ 4 * Wr ^ (2 * ζ)) (hD : 8 + 2 * ζ ≤ D) :
    ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * (exp (log Wr ^ (3 / 4 : ℝ)) * (Wr * ℓu * ηu) ^ 2)
      ≤ ηu⁻¹ := by
  have hW0 : 0 < Wr := by linarith
  have hW1 : 1 ≤ Wr := by linarith
  have hL0 : 0 ≤ Lr := by linarith
  set e := exp (log Wr ^ (3 / 4 : ℝ)) with he
  have he0 : 0 ≤ e := (exp_pos _).le
  have heW : e ≤ Wr := exp_log_rpow_le_self hW8
  have hWD0 : 0 ≤ Wr ^ (-D) := Real.rpow_nonneg hW0.le _
  have hWz0 : 0 ≤ Wr ^ (2 * ζ) := Real.rpow_nonneg hW0.le _
  have hr0 : 0 ≤ ℓu / ℓs := by positivity
  -- step 1 : insert the bound on `ρ`
  have h1 : ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * (e * (Wr * ℓu * ηu) ^ 2)
      ≤ ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * (2 * ηu⁻¹ * J * Wr ^ (-D)) * (e * (Wr * ℓu * ηu) ^ 2) := by
    gcongr
  have h2 : ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * (2 * ηu⁻¹ * J * Wr ^ (-D)) * (e * (Wr * ℓu * ηu) ^ 2)
      = 2 * (ℓu / ℓs * ℓu) * Lr * J * e * Wr ^ 2 * Wr ^ (-D) := by
    field_simp
  -- step 2 : the elementary facts
  have hrl : ℓu / ℓs * ℓu ≤ 4 * Wr ^ (2 * ζ) * Wr * Wr := by
    have hℓW : ℓu ≤ Wr := hℓL.trans hLW
    calc ℓu / ℓs * ℓu ≤ g * ℓu * ℓu := mul_le_mul_of_nonneg_right hr hℓu.le
      _ ≤ 4 * Wr ^ (2 * ζ) * Wr * Wr := by
          have hg0' : 0 ≤ g := by
            by_contra h
            push Not at h
            nlinarith [hr0.trans hr]
          calc g * ℓu * ℓu ≤ g * Wr * Wr := by gcongr
            _ ≤ 4 * Wr ^ (2 * ζ) * Wr * Wr := by gcongr
  have h3 : 2 * (ℓu / ℓs * ℓu) * Lr * J * e * Wr ^ 2 * Wr ^ (-D)
      ≤ 2 * (4 * Wr ^ (2 * ζ) * Wr * Wr) * Wr * Wr * Wr * Wr ^ 2 * Wr ^ (-D) := by
    gcongr
  -- step 3 : the power of `W`
  have hP : Wr ^ (2 * ζ) * Wr ^ (-D) ≤ (Wr ^ 8)⁻¹ := by
    rw [← Real.rpow_add hW0]
    calc Wr ^ (2 * ζ + -D) ≤ Wr ^ (-(8 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
      _ = (Wr ^ 8)⁻¹ := by
          rw [Real.rpow_neg hW0.le]
          norm_cast
  have h4 : 2 * (4 * Wr ^ (2 * ζ) * Wr * Wr) * Wr * Wr * Wr * Wr ^ 2 * Wr ^ (-D)
      = 8 * Wr ^ 7 * (Wr ^ (2 * ζ) * Wr ^ (-D)) := by ring
  have h5 : 8 * Wr ^ 7 * (Wr ^ (2 * ζ) * Wr ^ (-D)) ≤ 8 * Wr ^ 7 * (Wr ^ 8)⁻¹ :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have h6 : 8 * Wr ^ 7 * (Wr ^ 8)⁻¹ = 8 / Wr := by
    field_simp
  have h7 : 8 / Wr ≤ 1 := by rw [div_le_one hW0]; exact hW8
  have h8 : (1 : ℝ) ≤ ηu⁻¹ := (one_le_inv₀ hηu).2 hη1
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := h3
    _ = _ := h4
    _ ≤ _ := h5
    _ = _ := h6
    _ ≤ 1 := h7
    _ ≤ ηu⁻¹ := h8

/-- Coarsening a `0/1` indicator in a nonnegative coefficient. -/
theorem coarsen_ind {P : Prop} [Decidable P] {η a b c x T : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (hx : 0 ≤ x) (hT : 0 ≤ T) :
    (η * (a * (if P then (1 : ℝ) else 0) + b + c) + x * (if P then (1 : ℝ) else 0)) * T
      ≤ (η * (a + b + c) + x) * T := by
  refine mul_le_mul_of_nonneg_right ?_ hT
  split_ifs
  · simp
  · nlinarith [mul_nonneg hη ha]

end DriftPt

/-- **(R3) `rhs535'_le_mul_tailT`** (replaces `rhs535_le_mul_tailT`): under T1513's
`ρ ≤ 2 η_u⁻¹ J W^{-D}` and the elementary scale facts of `DriftPt.resCoef_le`, with
`D ≥ D₀ := 8 + 2ζ`, the near-band residue of `rhs535'` moves into the near slot as `+1`:
`rhs535' ≤ η_u⁻¹ ((c_near r³ + 1) 1(near) + c_far r^{3/2} A^{-1/2} J
  + 169 r A⁻¹ J^{3/2}) T_{u,D}(d)`.
-/
theorem rhs535'_le_mul_tailT {Wr Lr ℓu ℓs ηu D J ρ d g ζ : ℝ} (hW8 : 8 ≤ Wr) (hℓu : 0 < ℓu)
    (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hη1 : ηu ≤ 1) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 2 * ηu⁻¹ * J * Wr ^ (-D)) (hJ0 : 0 ≤ J) (hJW : J ≤ Wr) (hℓL : ℓu ≤ Lr)
    (hLW : Lr ≤ Wr) (hr : ℓu / ℓs ≤ g * ℓu) (hgW : g ≤ 4 * Wr ^ (2 * ζ)) (hD : 8 + 2 * ζ ≤ D) :
    rhs535' Wr Lr ℓu ℓs ηu D J ρ d ≤
      ηu⁻¹ * ((Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 + 1) *
            (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0)
          + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
          + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
        * tailT Wr ℓu ηu D d := by
  have hW1 : 1 ≤ Wr := by linarith
  have hW0 : 0 < Wr := by linarith
  have hL0 : 0 ≤ Lr := by linarith
  have hgen := rhs535'_le_mul_tailT_near (D := D) (J := J) (d := d) hW1 hℓu hℓs hηu hρ0 hL0
  have hres := DriftPt.resCoef_le hW8 hℓu hℓs hηu hη1 hρ hJ0 hJW hℓL hLW hr hgW hD
  have hT0 : 0 ≤ tailT Wr ℓu ηu D d := tailT_nonneg hW0.le d
  refine hgen.trans ?_
  set ind : ℝ := if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0 with hind
  set X := ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * (exp (log Wr ^ (3 / 4 : ℝ)) * (Wr * ℓu * ηu) ^ 2)
    with hX
  have hi0 : (0 : ℝ) ≤ ind := by rw [hind]; split_ifs <;> norm_num
  have h1 : X * ind ≤ ηu⁻¹ * ind := mul_le_mul_of_nonneg_right hres hi0
  have h2 := mul_le_mul_of_nonneg_right h1 hT0
  have heq : ηu⁻¹ * ((Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 + 1) * ind
          + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
          + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J))) * tailT Wr ℓu ηu D d
      = (ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * ind
            + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
            + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))) * tailT Wr ℓu ηu D d
        + ηu⁻¹ * ind * tailT Wr ℓu ηu D d := by ring
  rw [heq, add_mul]
  linarith [h2]

/-! ## (T3') : the pointwise drift bound with `rhs535'` -/

/-- **(T3')'s coefficient `Mdr'(u)`**: `mdr` with the `ρ`-piece `r (ℓ_u η_u)⁻¹ L ρ W^D` (absorption
of the residue on **all** pairs against the floor `W^{-D}`) replaced by
`c_ρ = r (ℓ_u η_u)⁻¹ L ρ e^{(log W)^{3/4}} A_u²` (absorption on the **near band only**, against
`T_{u,D} ≥ A_u⁻² e^{-(log W)^{3/4}}`):
`Mdr' = η_u⁻¹ (c_near r³ + c_far r^{3/2} A_u^{-1/2} J + 169 r A_u⁻¹ J^{3/2}) + c_ρ
  + e thr(u)² (36 η_u⁻¹ A_u⁻¹ + W L W^{-D})`, `r = ℓ_u/ℓs`, `A_u = W ℓ_u η_u`. -/
noncomputable def mdr' (B : Band Ω) (E : ℝ) (s : ℕ → ℝ) (δ D ℓs : ℝ) (N : ℕ) (u J ρ : ℝ) : ℝ :=
  ((etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
        + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
            (B.ell N u / ℓs * √(B.ell N u / ℓs)
              * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
        + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
      + B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ
          * (exp (log (B.W N : ℝ) ^ (3 / 4 : ℝ)) * ((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2))
    + exp 1 * Step2.thr E s δ N u ^ 2 *
        (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
          + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D))

/-- **(T3') `drift_point_le'`**: (T3) `drift_point_le` with `rhs535'` in place of `rhs535`:
`‖D(M) b‖ ≤ Mdr'(u) · T_{u,D}(b)`, `D(M) := (eGterm + primBil(A,A))(M)` the drift of T1506 (T4).
**Same hypotheses as `drift_point_le`** (generic `J`, `Gm`, `h560`, `hGm`); no smallness of `ρ`
is assumed here: the residue is absorbed on the near band by `rhs535'_le_mul_tailT_near`. -/
theorem drift_point_le' {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓs D δ : ℝ} {s : ℕ → ℝ}
    (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 1 ≤ B.ell N u)
    (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hDreg : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    {J : ℝ} (hJ : 1 ≤ J) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ (B.ell N u / ℓs) ^ 2 * (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹)
    (h554 : ∀ x y c : ZMod (B.L N),
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (y - c) : ℝ) →
        ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          J * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)))
    (h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        Gm x y ≤ √J * √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y))))
    (h557C : ∀ (x y : ZMod (B.L N)) (p : B.Idx N), p.1 = y →
      ∑ r : B.Idx N, Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : B.Idx N), r.1 = x →
      ∑ p : B.Idx N, Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h560 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤
        Gm y c * Gm x c * Gm y x)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs)
    (hjS : Step2.jStar (B.L N)
        (fun a : LoopArg (B.L N) 2 =>
          ‖gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
            - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
        (B.W N) (B.ell N u) (etaT E u) D ≤ Step2.thr E s δ N u) :
    ∀ b : LoopArg (B.L N) 2,
      ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], [b 0, b 1]⟩
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              ⟨[true, false], [b 0, b 1]⟩‖
        ≤ mdr' B E s δ D ℓs N u J ρ * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)) := by
  intro b
  set x := b 0 with hx
  set y := b 1 with hy
  have hWpos : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hℓupos : (0 : ℝ) < B.ell N u := by linarith
  set T := tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) with hTdef
  have hT0 : 0 ≤ T := tailT_nonneg hWpos.le _
  -- EG part: (T2) + (R2) + (R3, generic) + coarsening of the two indicators
  have hEG := eGpm_le_rhs535' (M := M) (z := zt E u) hM hL hW hℓu hℓs hηu hJ hA hr
    hDreg x y hρ hGm (h273 x y) (h554 x y) h531 h42 h557C h557R
    (h560 x y) (mSigma E) hone hκ
  have hEGmul := rhs535'_le_mul_tailT_near (Wr := (B.W N : ℝ)) (Lr := (B.L N : ℝ))
    (ℓu := B.ell N u) (ℓs := ℓs) (ηu := etaT E u) (D := D) (J := J) (ρ := ρ)
    (d := (zdist (B.L N) (x - y) : ℝ)) hW hℓupos hℓs hηu hρ (Nat.cast_nonneg _)
  have hcN0 : 0 ≤ Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3 := by
    have := Lemma57.cNear_nonneg hW hℓupos; positivity
  have hX0 : 0 ≤ B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ
      * (exp (log (B.W N : ℝ) ^ (3 / 4 : ℝ)) * ((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2) := by
    positivity
  have hcoarse := DriftPt.coarsen_ind
    (P := (zdist (B.L N) (x - y) : ℝ) ≤ ellStar (B.W N : ℝ) (B.ell N u))
    (b := Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
            (B.ell N u / ℓs * √(B.ell N u / ℓs)
              * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J))
    (c := 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
    (inv_nonneg.2 hηu.le) hcN0 hX0 hT0
  have hEGterm : RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], [x, y]⟩
      = EGDef.eGpm (B.L N) (B.W N) (mSigma E) M (zt E u) x y :=
    eGterm_eq_eGpm (mSigma E) M (zt E u) x y
  have hEGfinal : ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
      ⟨[true, false], [x, y]⟩‖ ≤
      ((etaT E u)⁻¹ * (Lemma57.cNear (B.W N : ℝ) (B.ell N u) * (B.ell N u / ℓs) ^ 3
            + Lemma57.cFar (B.W N : ℝ) (B.ell N u) *
                (B.ell N u / ℓs * √(B.ell N u / ℓs)
                  * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹ * J)
            + 169 * (B.ell N u / ℓs * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ * (J * √J)))
          + B.ell N u / ℓs * (B.ell N u * etaT E u)⁻¹ * (B.L N : ℝ) * ρ
            * (exp (log (B.W N : ℝ) ^ (3 / 4 : ℝ)) * ((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2))
        * T := by
    rw [hEGterm]; exact (hEG.trans hEGmul).trans hcoarse
  -- Quadratic part (unchanged from (T3))
  have hquadEq := quadGlue_pm_eq_eLL_mat E N u M x y
  have hquad := Step2.norm_eLL_le hL hWpos hℓu hηu D
    (fun a : LoopArg (B.L N) 2 =>
      gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
        - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) ![x, y]
  have hJstarNonneg : 0 ≤ Step2.jStar (B.L N)
      (fun a : LoopArg (B.L N) 2 => ‖gloop (B.L N) (B.W N) M (zt E u)
          (LoopData.idx (Step2.sigPM, a)) - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
      (B.W N) (B.ell N u) (etaT E u) D :=
    (Step2.one_le_jStar hWpos (fun a => norm_nonneg _)).trans' (by norm_num)
  have hjSsq : Step2.jStar (B.L N)
      (fun a : LoopArg (B.L N) 2 => ‖gloop (B.L N) (B.W N) M (zt E u)
          (LoopData.idx (Step2.sigPM, a)) - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
      (B.W N) (B.ell N u) (etaT E u) D ^ 2 ≤ Step2.thr E s δ N u ^ 2 :=
    pow_le_pow_left₀ hJstarNonneg hjS 2
  have hxy01 : (![x, y] : LoopArg (B.L N) 2) 0 - (![x, y] : LoopArg (B.L N) 2) 1 = x - y := by
    simp
  have hquad' : ‖Step2.eLL (B.L N) (B.W N : ℝ)
      (fun a : LoopArg (B.L N) 2 =>
        gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
          - B.Kval E N u (LoopData.idx (Step2.sigPM, a))) ![x, y]‖ ≤
      exp 1 * Step2.thr E s δ N u ^ 2 *
          (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
            + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)) * T := by
    refine hquad.trans ?_
    rw [hxy01]
    have he0 : (0:ℝ) ≤ exp 1 := (exp_pos 1).le
    have hbrak0 : (0:ℝ) ≤ 36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
        + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjSsq hbrak0) hT0
    nlinarith [this]
  have hquadfinal : ‖primBil (B.L N) (B.W N)
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨[true, false], [x, y]⟩‖ ≤
      exp 1 * Step2.thr E s δ N u ^ 2 *
          (36 * ((etaT E u)⁻¹ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
            + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)) * T := by
    rw [hquadEq]; exact hquad'
  have htT_eq : Step2.tT B E N D u (zdist (B.L N) (x - y)) = T := rfl
  rw [htT_eq]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add hEGfinal hquadfinal
  unfold mdr'
  linarith [this]

open DriftPt in
/-- **(T3'), block-maximum form `drift_point_le_blk'`**: `drift_point_le'` with `Gm := gmBlkM`
(no `h560`, no `hGm`); the EG inputs are those of `eGpm_le_rhs535_of_jG_mat'`. -/
theorem drift_point_le_blk' {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓs D δ : ℝ} {s : ℕ → ℝ}
    (hL : 3 ≤ B.L N) (hW : 1 ≤ (B.W N : ℝ)) (hℓu : 1 ≤ B.ell N u)
    (hℓs : 0 < ℓs) (hηu : 0 < etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) (hr : 1 ≤ B.ell N u / ℓs)
    (hDreg : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D))
      ≤ B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    {J ρ κ : ℝ} (hJ : 1 ≤ J) (hρ : 0 ≤ ρ)
    (h273 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ (B.ell N u / ℓs) ^ 2 * (((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹)
    (h554 : ∀ x y c : ZMod (B.L N),
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (y - c) : ℝ) →
        ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          J * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)))
    (h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        gmBlkM B N M (zt E u) x y ≤
          √J * √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y))))
    (h557C : ∀ (x y : ZMod (B.L N)) (p : B.Idx N), p.1 = y →
      ∑ r : B.Idx N, Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : B.Idx N), r.1 = x →
      ∑ p : B.Idx N, Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / ℓs) * (√((B.W N : ℝ) * B.ell N u * etaT E u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / ℓs)
    (hjS : Step2.jStar (B.L N)
        (fun a : LoopArg (B.L N) 2 =>
          ‖gloop (B.L N) (B.W N) M (zt E u) (LoopData.idx (Step2.sigPM, a))
            - B.Kval E N u (LoopData.idx (Step2.sigPM, a))‖)
        (B.W N) (B.ell N u) (etaT E u) D ≤ Step2.thr E s δ N u) :
    ∀ b : LoopArg (B.L N) 2,
      ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], [b 0, b 1]⟩
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              ⟨[true, false], [b 0, b 1]⟩‖
        ≤ mdr' B E s δ D ℓs N u J ρ * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)) :=
  drift_point_le' hM hL hW hℓu hℓs hηu hA hr hDreg hJ hρ (gmBlkM_nonneg B N M (zt E u))
    h273 h554 h531 h42 h557C h557R
    (fun x y c => norm_gloop_three_le_gmBlkM hM (zt E u) x y c) hone hκ hjS

/-! ## (T4') : the time sum of `Mdr'`, exponent `2`

As in (T4), every `η_{u_j}⁻¹` stays paired with its own propagator factor, `r_{u_j}` stays at its
own time, and the near term telescopes. The only change is the `ρ`-piece: `c_ρ ≤ η_{u_j}⁻¹`
(`DriftPt.resCoef_le`, under T1513's `ρ_j ≤ 2 η_{u_j}⁻¹ J_j W^{-D}` and `D ≥ 8 + 2ζ`), which then
pairs like every other `η⁻¹`-piece. A scale factor `g ≥ 1` (`r√(1-w) ≤ g √(1-s)`) covers the
rescaled `ℓ_s' = ℓ_s/(4N^ζ)` (`g = 4N^ζ`); `ℓ_s ≥ 1` is no longer assumed. -/

namespace DriftPt

/-- `ℓ_w √(1-w) ≤ 1` for `w < 1` (`ℓ_w √(1-w) = min(1, L√(1-w))`). -/
theorem ell_mul_sqrt_le_one (B : Band Ω) (N : ℕ) {w : ℝ} (hw1 : w < 1) :
    B.ell N w * √(1 - w) ≤ 1 := by
  have hsqrt : 0 < √(1 - w) := Real.sqrt_pos.2 (by linarith)
  unfold Band.ell
  rw [ellHat_ofReal _ hw1, min_mul_of_nonneg _ _ hsqrt.le, one_div_mul_cancel hsqrt.ne']
  exact min_le_left _ _

/-- **Pointwise domination, scalar core, for `Mdr'`** (successor of `mdr_core`): with a scale
factor `g ≥ 1` (`r √a ≤ g √c₀`, `r = ℓ_w/ℓ_s`, no lower bound on `ℓ_s`) and the residue
coefficient bounded by `η_w⁻¹ = (a m)⁻¹` (`hres`, from `resCoef_le`). -/
theorem mdr'_core {W L ℓw ℓs a b c0 m x J ρ D cNw cFw cN cF p g : ℝ}
    (hW1 : 1 ≤ W) (hL0 : 0 ≤ L) (hm0 : 0 < m) (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hac : a ≤ c0) (hℓs : 0 < ℓs) (hℓw : 0 < ℓw) (hg1 : 1 ≤ g)
    (hrsq : ℓw / ℓs * √a ≤ g * √c0)
    (hx1 : 1 ≤ x) (hAw : x ^ 24 * (c0 / a) ^ 30 ≤ W * ℓw * (a * m))
    (hAv : x ^ 24 * (c0 / b) ^ 30 ≤ W * L)
    (hJ1 : 1 ≤ J) (hJx : J ≤ x ^ 2 * (c0 / a) ^ 4)
    (hres : ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ *
        (exp (log W ^ (3 / 4 : ℝ)) * (W * ℓw * (a * m)) ^ 2) ≤ (a * m)⁻¹)
    (hcNw0 : 0 ≤ cNw) (hcNw : cNw ≤ cN) (hcFw0 : 0 ≤ cFw) (hcFw : cFw ≤ cF)
    (hp0 : 0 ≤ p) (hp : p ≤ (a / b) ^ 2) :
    (((a * m)⁻¹ * (cNw * (ℓw / ℓs) ^ 3
          + cFw * (ℓw / ℓs * √(ℓw / ℓs) * (√(W * ℓw * (a * m)))⁻¹ * J)
          + 169 * (ℓw / ℓs * (W * ℓw * (a * m))⁻¹ * (J * √J)))
        + ℓw / ℓs * (ℓw * (a * m))⁻¹ * L * ρ *
            (exp (log W ^ (3 / 4 : ℝ)) * (W * ℓw * (a * m)) ^ 2))
      + exp 1 * (x * (c0 / a) ^ 4) ^ 2 *
          (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹) + W * L * W ^ (-D))) * p
      ≤ g ^ 3 * (cN * c0 * √c0 / (m * b ^ 2) / √a
          + (cF + 170 + 36 * exp 1) / (m * b ^ 2) * a)
        + exp 1 * ((W * L) ^ 2 * W ^ (-D)) := by
  have hW0 : 0 < W := by linarith
  have hc0 : 0 < c0 := by linarith
  have hg0 : 0 < g := by linarith
  set r := ℓw / ℓs with hrdef
  have hr0 : 0 ≤ r := div_nonneg hℓw.le hℓs.le
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hsc : 0 < √c0 := Real.sqrt_pos.2 hc0
  have hRw1 : 1 ≤ c0 / a := by rw [le_div_iff₀ ha]; linarith
  have hRwv : c0 / a ≤ c0 / b := div_le_div_of_nonneg_left hc0.le hb hba
  have hRv1 : 1 ≤ c0 / b := hRw1.trans hRwv
  set R := c0 / a with hRdef
  have hR0 : 0 ≤ R := by linarith
  -- the unscaled ratio `ρ̃ = r/g`
  set q := r / g with hqdef
  have hq0 : 0 ≤ q := div_nonneg hr0 hg0.le
  have hrq : r = g * q := by rw [hqdef]; field_simp
  have hqsq : q * √a ≤ √c0 := by
    rw [hqdef, div_mul_eq_mul_div, div_le_iff₀ hg0]; linarith
  have hq2a : q ^ 2 * a ≤ c0 := by
    have h := pow_le_pow_left₀ (mul_nonneg hq0 hsa.le) hqsq 2
    rwa [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hc0.le] at h
  have hq2R : q ^ 2 ≤ R := by rw [hRdef, le_div_iff₀ ha]; exact hq2a
  have hqR : q ≤ R := by nlinarith
  have hrR : r ≤ g * R := by rw [hrq]; exact mul_le_mul_of_nonneg_left hqR hg0.le
  have hr2a : r ^ 2 * a ≤ g ^ 2 * c0 := by
    rw [hrq]; nlinarith [hq2a, sq_nonneg g]
  have hrsq' : r * √a ≤ g * √c0 := hrsq
  have hx0 : 0 ≤ x := by linarith
  have hApos : 0 < W * ℓw * (a * m) := by positivity
  have hmono : ∀ i j : ℕ, i ≤ 24 → j ≤ 30 → x ^ i * R ^ j ≤ W * ℓw * (a * m) :=
    fun i j hi hj =>
      (mul_le_mul (pow_le_pow_right₀ hx1 hi) (pow_le_pow_right₀ hRw1 hj) (by positivity)
        (by positivity)).trans hAw
  have hJ0 : 0 ≤ J := by linarith
  have hg3 : 1 ≤ g ^ 3 := one_le_pow₀ hg1
  have hgg3 : g ≤ g ^ 3 := by
    calc g = g ^ 1 := (pow_one g).symm
      _ ≤ g ^ 3 := pow_le_pow_right₀ hg1 (by norm_num)
  have habs1 : r ^ 3 * J ^ 2 ≤ g ^ 3 * (W * ℓw * (a * m)) :=
    calc r ^ 3 * J ^ 2 ≤ (g * R) ^ 3 * (x ^ 2 * R ^ 4) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ hr0 hrR 3) (pow_le_pow_left₀ hJ0 hJx 2) (by positivity)
            (by positivity)
      _ = g ^ 3 * (x ^ 4 * R ^ 11) := by ring
      _ ≤ g ^ 3 * (W * ℓw * (a * m)) :=
          mul_le_mul_of_nonneg_left (hmono 4 11 (by norm_num) (by norm_num)) (by positivity)
  have habs2 : r * J ^ 2 ≤ g * (W * ℓw * (a * m)) :=
    calc r * J ^ 2 ≤ g * R * (x ^ 2 * R ^ 4) ^ 2 :=
          mul_le_mul hrR (pow_le_pow_left₀ hJ0 hJx 2) (by positivity) (by positivity)
      _ = g * (x ^ 4 * R ^ 9) := by ring
      _ ≤ g * (W * ℓw * (a * m)) :=
          mul_le_mul_of_nonneg_left (hmono 4 9 (by norm_num) (by norm_num)) hg0.le
  have habs3 : (x * R ^ 4) ^ 2 ≤ W * ℓw * (a * m) := by
    calc (x * R ^ 4) ^ 2 = x ^ 2 * R ^ 8 := by ring
      _ ≤ W * ℓw * (a * m) := hmono 2 8 (by norm_num) (by norm_num)
  have habs4 : x ^ 2 * (c0 / b) ^ 8 ≤ W * L :=
    (mul_le_mul (pow_le_pow_right₀ hx1 (by norm_num : 2 ≤ 24))
      (pow_le_pow_right₀ hRv1 (by norm_num : 8 ≤ 30)) (by positivity) (by positivity)).trans hAv
  -- the pairing `η_w⁻¹ p ≤ a/(m b²)`
  have hq0' : 0 ≤ (a * m)⁻¹ * p := by positivity
  have hpair : (a * m)⁻¹ * p ≤ a / (m * b ^ 2) := by
    calc (a * m)⁻¹ * p ≤ (a * m)⁻¹ * (a / b) ^ 2 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = a / (m * b ^ 2) := by field_simp
  set Q := a / (m * b ^ 2) with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  have hcN0 : 0 ≤ cN := hcNw0.trans hcNw
  have hcF0 : 0 ≤ cF := hcFw0.trans hcFw
  -- (a) near
  have hTa : (a * m)⁻¹ * (cNw * r ^ 3) * p ≤ g ^ 3 * (cN * c0 * √c0 / (m * b ^ 2) / √a) := by
    have hr3 : r ^ 3 * a ≤ g ^ 3 * (c0 * √c0) / √a := by
      rw [le_div_iff₀ hsa]
      calc r ^ 3 * a * √a = (r ^ 2 * a) * (r * √a) := by ring
        _ ≤ (g ^ 2 * c0) * (g * √c0) := mul_le_mul hr2a hrsq' (by positivity) (by positivity)
        _ = g ^ 3 * (c0 * √c0) := by ring
    calc (a * m)⁻¹ * (cNw * r ^ 3) * p
        = cNw * r ^ 3 * ((a * m)⁻¹ * p) := by ring
      _ ≤ cN * r ^ 3 * Q :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcNw (by positivity)) hpair hq0' (by positivity)
      _ = cN * (r ^ 3 * a) / (m * b ^ 2) := by rw [hQdef]; ring
      _ ≤ cN * (g ^ 3 * (c0 * √c0) / √a) / (m * b ^ 2) := by gcongr
      _ = g ^ 3 * (cN * c0 * √c0 / (m * b ^ 2) / √a) := by ring
  -- (b) far, `c_far` part
  have hTb : (a * m)⁻¹ * (cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J)) * p
      ≤ g ^ 3 * (cF * Q) := by
    have hsA : 0 < √(W * ℓw * (a * m)) := Real.sqrt_pos.2 hApos
    have hk : r * √r * J ≤ g ^ 3 * √(W * ℓw * (a * m)) := by
      have h1 : (r * √r * J) ^ 2 ≤ (g ^ 3 * √(W * ℓw * (a * m))) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hr0, Real.sq_sqrt hApos.le]
        calc r ^ 2 * r * J ^ 2 = r ^ 3 * J ^ 2 := by ring
          _ ≤ g ^ 3 * (W * ℓw * (a * m)) := habs1
          _ ≤ (g ^ 3) ^ 2 * (W * ℓw * (a * m)) :=
              mul_le_mul_of_nonneg_right (le_self_pow₀ hg3 two_ne_zero) hApos.le
      have hl0 : 0 ≤ r * √r * J := mul_nonneg (mul_nonneg hr0 (Real.sqrt_nonneg _)) hJ0
      have hr0' : 0 ≤ g ^ 3 * √(W * ℓw * (a * m)) :=
        mul_nonneg (by linarith) (Real.sqrt_nonneg _)
      exact (pow_le_pow_iff_left₀ hl0 hr0' two_ne_zero).1 h1
    have hk' : r * √r * (√(W * ℓw * (a * m)))⁻¹ * J ≤ g ^ 3 := by
      rw [show r * √r * (√(W * ℓw * (a * m)))⁻¹ * J
          = r * √r * J / √(W * ℓw * (a * m)) by ring, div_le_iff₀ hsA]
      exact hk
    calc (a * m)⁻¹ * (cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J)) * p
        = cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J) * ((a * m)⁻¹ * p) := by ring
      _ ≤ cF * g ^ 3 * Q :=
          mul_le_mul (mul_le_mul hcFw hk' (by positivity) hcF0) hpair hq0' (by positivity)
      _ = g ^ 3 * (cF * Q) := by ring
  -- (c) far, `169` part
  have hTc : (a * m)⁻¹ * (169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J))) * p
      ≤ g ^ 3 * (169 * Q) := by
    have hsJ : √J ≤ J := Lemma57.sqrt_le_self hJ1
    have hk : r * (W * ℓw * (a * m))⁻¹ * (J * √J) ≤ g ^ 3 := by
      rw [show r * (W * ℓw * (a * m))⁻¹ * (J * √J)
          = r * (J * √J) / (W * ℓw * (a * m)) by ring, div_le_iff₀ hApos]
      calc r * (J * √J) ≤ r * (J * J) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsJ hJ0) hr0
        _ = r * J ^ 2 := by ring
        _ ≤ g * (W * ℓw * (a * m)) := habs2
        _ ≤ g ^ 3 * (W * ℓw * (a * m)) := mul_le_mul_of_nonneg_right hgg3 hApos.le
    calc (a * m)⁻¹ * (169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J))) * p
        = 169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J)) * ((a * m)⁻¹ * p) := by ring
      _ ≤ 169 * g ^ 3 * Q :=
          mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hpair hq0' (by positivity)
      _ = g ^ 3 * (169 * Q) := by ring
  -- (d) the residue
  have hTd : r * (ℓw * (a * m))⁻¹ * L * ρ *
        (exp (log W ^ (3 / 4 : ℝ)) * (W * ℓw * (a * m)) ^ 2) * p ≤ Q :=
    (mul_le_mul_of_nonneg_right hres hp0).trans hpair
  -- (e) the `36 η⁻¹ A⁻¹ thr²` part
  have hTe : exp 1 * (x * R ^ 4) ^ 2 * (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹)) * p
      ≤ 36 * exp 1 * Q := by
    have hk : (x * R ^ 4) ^ 2 * (W * ℓw * (a * m))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hApos]; exact habs3
    calc exp 1 * (x * R ^ 4) ^ 2 * (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹)) * p
        = 36 * exp 1 * ((x * R ^ 4) ^ 2 * (W * ℓw * (a * m))⁻¹) * ((a * m)⁻¹ * p) := by
          ring
      _ ≤ 36 * exp 1 * 1 * Q :=
          mul_le_mul (mul_le_mul_of_nonneg_left hk (by positivity)) hpair hq0' (by positivity)
      _ = 36 * exp 1 * Q := by ring
  -- (f) the `W L W^{-D} thr²` part
  have hTf : exp 1 * (x * R ^ 4) ^ 2 * (W * L * W ^ (-D)) * p
      ≤ exp 1 * ((W * L) ^ 2 * W ^ (-D)) := by
    have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    have hk : (x * R ^ 4) ^ 2 * p ≤ W * L := by
      have hRab : R * (a / b) = c0 / b := by rw [hRdef]; field_simp
      calc (x * R ^ 4) ^ 2 * p ≤ (x * R ^ 4) ^ 2 * (a / b) ^ 2 :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = x ^ 2 * R ^ 6 * (R * (a / b)) ^ 2 := by ring
        _ = x ^ 2 * R ^ 6 * (c0 / b) ^ 2 := by rw [hRab]
        _ ≤ x ^ 2 * (c0 / b) ^ 6 * (c0 / b) ^ 2 := by gcongr
        _ = x ^ 2 * (c0 / b) ^ 8 := by ring
        _ ≤ W * L := habs4
    calc exp 1 * (x * R ^ 4) ^ 2 * (W * L * W ^ (-D)) * p
        = exp 1 * (W * L * W ^ (-D)) * ((x * R ^ 4) ^ 2 * p) := by ring
      _ ≤ exp 1 * (W * L * W ^ (-D)) * (W * L) :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ = exp 1 * ((W * L) ^ 2 * W ^ (-D)) := by ring
  -- assemble
  have hQg : Q ≤ g ^ 3 * Q := le_mul_of_one_le_left hQ0 hg3
  have h36g : 36 * exp 1 * Q ≤ g ^ 3 * (36 * exp 1 * Q) :=
    le_mul_of_one_le_left (by positivity) hg3
  have hRHS : g ^ 3 * (cN * c0 * √c0 / (m * b ^ 2) / √a
        + (cF + 170 + 36 * exp 1) / (m * b ^ 2) * a)
      = g ^ 3 * (cN * c0 * √c0 / (m * b ^ 2) / √a) + g ^ 3 * (cF * Q) + g ^ 3 * (169 * Q)
        + g ^ 3 * Q + g ^ 3 * (36 * exp 1 * Q) := by rw [hQdef]; ring
  rw [hRHS]
  have hsplit : (((a * m)⁻¹ * (cNw * r ^ 3)
          + (a * m)⁻¹ * (cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J))
          + (a * m)⁻¹ * (169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J)))) * p
        + r * (ℓw * (a * m))⁻¹ * L * ρ *
            (exp (log W ^ (3 / 4 : ℝ)) * (W * ℓw * (a * m)) ^ 2) * p
        + exp 1 * (x * R ^ 4) ^ 2 * (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹)) * p
        + exp 1 * (x * R ^ 4) ^ 2 * (W * L * W ^ (-D)) * p)
      = (((a * m)⁻¹ * (cNw * r ^ 3
          + cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J)
          + 169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J)))
        + r * (ℓw * (a * m))⁻¹ * L * ρ *
            (exp (log W ^ (3 / 4 : ℝ)) * (W * ℓw * (a * m)) ^ 2))
      + exp 1 * (x * R ^ 4) ^ 2 *
          (36 * ((a * m)⁻¹ * (W * ℓw * (a * m))⁻¹) + W * L * W ^ (-D))) * p := by ring
  rw [← hsplit]
  have hTabc := add_le_add (add_le_add hTa hTb) hTc
  have e3 : ((a * m)⁻¹ * (cNw * r ^ 3)
          + (a * m)⁻¹ * (cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J))
          + (a * m)⁻¹ * (169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J)))) * p
      = (a * m)⁻¹ * (cNw * r ^ 3) * p
          + (a * m)⁻¹ * (cFw * (r * √r * (√(W * ℓw * (a * m)))⁻¹ * J)) * p
          + (a * m)⁻¹ * (169 * (r * (W * ℓw * (a * m))⁻¹ * (J * √J))) * p := by ring
  rw [e3]
  linarith [hTabc, hTd, hTe, hTf, hQg, h36g]

/-- **Pointwise domination of one summand of (T4')** (`s ≤ w ≤ w' ≤ v ≤ t < 1`, `w = u_j`,
`w' = u_{j+1}`, `v = u_k`), for a reference scale `ℓ_s > 0` with `ℓ_{s N} ≤ g ℓ_s`,
`1 ≤ g ≤ 4W^{2ζ}`
(`g = 1`, `ℓ_s = ℓ_{s N}`; or `g = 4N^ζ`, `ℓ_s = ℓ_{s N}/(4N^ζ)`), `W ≥ 8`, `L ≤ W`,
`D ≥ 8 + 2ζ`, and T1513's `ρ ≤ 2 η_w⁻¹ J W^{-D}`:
`Mdr'(w) ((1-w')/(1-v))² ≤ g³ (c_near(W,1)(1-s)^{3/2}/(m(1-v)²) (1-w)^{-1/2}
  + (c_far(W,1) + 170 + 36e)/(m(1-v)²) (1-w)) + e (WL)² W^{-D}`. -/
theorem mdr'_mul_le (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {δ ε D c ℓs g ζ : ℝ}
    {N : ℕ} {w w' v t J ρ : ℝ} (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsw : s N ≤ w)
    (hww' : w ≤ w') (hw'v : w' ≤ v) (hvt : v ≤ t) (ht1 : t < 1)
    (hreg : (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 ≤ B.scale E N t)
    (hδ0 : 0 ≤ δ) (hδc : 24 * δ ≤ c) (hεδ : 2 * ε ≤ δ)
    (hℓs : 0 < ℓs) (hg1 : 1 ≤ g) (hℓsg : B.ell N (s N) ≤ g * ℓs)
    (hgW : g ≤ 4 * (B.W N : ℝ) ^ (2 * ζ)) (hW8 : 8 ≤ (B.W N : ℝ))
    (hLW : (B.L N : ℝ) ≤ B.W N) (hD : 8 + 2 * ζ ≤ D)
    (hJ1 : 1 ≤ J) (hJ : J ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N w)
    (hρ : ρ ≤ 2 * (etaT E w)⁻¹ * J * (B.W N : ℝ) ^ (-D)) :
    mdr' B E s δ D ℓs N w J ρ * ((1 - w') / (1 - v)) ^ 2 ≤
      g ^ 3 * (Lemma57.cNear (B.W N : ℝ) 1 * (1 - s N) * √(1 - s N)
            / ((mE E).im * (1 - v) ^ 2) / √(1 - w)
          + (Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1) / ((mE E).im * (1 - v) ^ 2)
            * (1 - w))
        + exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) := by
  have hW1 : (1 : ℝ) ≤ B.W N := B.one_le_W N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL1 : 1 ≤ B.L N := B.one_le_L N
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hw1 : w < 1 := by linarith
  have hv1 : v < 1 := by linarith
  have hs1 : s N < 1 := by linarith
  have hw0 : 0 ≤ w := hs0.trans hsw
  have hv0 : 0 ≤ v := by linarith
  have hwt : w ≤ t := by linarith
  have ha : 0 < 1 - w := by linarith
  have hb : 0 < 1 - v := by linarith
  have hc0 : 0 < 1 - s N := by linarith
  have ht0 : 0 < 1 - t := by linarith
  -- scales
  have hℓw1 : 1 ≤ B.ell N w := one_le_ellHat_of_nonneg hL1 hw0 hw1
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg hL1 hs0 hs1
  have hℓwL : B.ell N w ≤ (B.L N : ℝ) := min_le_right _ _
  have hℓvL : B.ell N v ≤ (B.L N : ℝ) := min_le_right _ _
  have hK := ell_mul_sqrt_le B N hw1 hsw
  have hrsq : B.ell N w / ℓs * √(1 - w) ≤ g * √(1 - s N) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hℓs]
    calc B.ell N w * √(1 - w) ≤ B.ell N (s N) * √(1 - s N) := hK
      _ ≤ g * ℓs * √(1 - s N) := mul_le_mul_of_nonneg_right hℓsg (Real.sqrt_nonneg _)
      _ = g * √(1 - s N) * ℓs := by ring
  -- `N^δ`, the gain, and `J`
  have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have hx24 : ((N : ℝ) ^ δ) ^ 24 ≤ (N : ℝ) ^ c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  have hNε : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
  have hthr : Step2.thr E s δ N w = (N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4 := by
    rw [Step2.thr, Step2.etaT_ratio hE]
  have hJx : J ≤ ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - w)) ^ 4 := by
    have h0 : 0 ≤ (N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4 := by positivity
    calc J ≤ (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4) := hthr ▸ hJ
      _ ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * ((1 - s N) / (1 - w)) ^ 4) :=
          mul_le_mul_of_nonneg_right hNε h0
      _ = ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - w)) ^ 4 := by ring
  -- `hreg` transported to `w` and to `v`
  have hRt : etaT E (s N) / etaT E t = (1 - s N) / (1 - t) := Step2.etaT_ratio hE _ _
  have hscale_w : B.scale E N t ≤ B.scale E N w :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hw1.le) (Set.mem_Iic.2 ht1.le) hwt
  have hscale_v : B.scale E N t ≤ B.scale E N v :=
    flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hv1.le) (Set.mem_Iic.2 ht1.le) hvt
  have hreg' : ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30 ≤ B.scale E N t := by
    calc ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30
        ≤ (N : ℝ) ^ c * ((1 - s N) / (1 - t)) ^ 30 :=
          mul_le_mul_of_nonneg_right hx24 (by positivity)
      _ = (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 := by rw [hRt]
      _ ≤ B.scale E N t := hreg
  have hAw : ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - w)) ^ 30
      ≤ (B.W N : ℝ) * B.ell N w * ((1 - w) * (mE E).im) := by
    have h1 : ((1 - s N) / (1 - w)) ^ 30 ≤ ((1 - s N) / (1 - t)) ^ 30 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hc0.le ht0 (by linarith)) 30
    calc ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - w)) ^ 30
        ≤ ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ B.scale E N t := hreg'
      _ ≤ B.scale E N w := hscale_w
      _ = (B.W N : ℝ) * B.ell N w * ((1 - w) * (mE E).im) := rfl
  have hAv : ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - v)) ^ 30 ≤ (B.W N : ℝ) * B.L N := by
    have h1 : ((1 - s N) / (1 - v)) ^ 30 ≤ ((1 - s N) / (1 - t)) ^ 30 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left hc0.le ht0 (by linarith)) 30
    have hsv : B.scale E N v ≤ (B.W N : ℝ) * B.L N := by
      change (B.W N : ℝ) * B.ell N v * ((1 - v) * (mE E).im) ≤ (B.W N : ℝ) * B.L N
      have h2 : (1 - v) * (mE E).im ≤ 1 := by nlinarith
      calc (B.W N : ℝ) * B.ell N v * ((1 - v) * (mE E).im)
          ≤ (B.W N : ℝ) * B.L N * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hℓvL hW0.le) h2 (by positivity)
              (by positivity)
        _ = (B.W N : ℝ) * B.L N := mul_one _
    calc ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - v)) ^ 30
        ≤ ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t)) ^ 30 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ B.scale E N t := hreg'
      _ ≤ B.scale E N v := hscale_v
      _ ≤ (B.W N : ℝ) * B.L N := hsv
  -- the residue: `J ≤ A_w ≤ W`, `η_w ≤ 1`, `r ≤ g ℓ_w`
  have hRw1 : 1 ≤ (1 - s N) / (1 - w) := by rw [le_div_iff₀ ha]; linarith
  have hJA : J ≤ (B.W N : ℝ) * B.ell N w * ((1 - w) * (mE E).im) := by
    calc J ≤ ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - w)) ^ 4 := hJx
      _ ≤ ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - w)) ^ 30 :=
          mul_le_mul (pow_le_pow_right₀ hx1 (by norm_num)) (pow_le_pow_right₀ hRw1 (by norm_num))
            (by positivity) (by positivity)
      _ ≤ _ := hAw
  have hℓη1 : B.ell N w * ((1 - w) * (mE E).im) ≤ 1 := by
    have h1 := ell_mul_sqrt_le_one B N hw1
    have hs : √(1 - w) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have hsq : √(1 - w) * √(1 - w) = 1 - w := Real.mul_self_sqrt ha.le
    have hℓ0 : 0 ≤ B.ell N w := by linarith
    calc B.ell N w * ((1 - w) * (mE E).im) = (B.ell N w * √(1 - w)) * √(1 - w) * (mE E).im := by
          conv_lhs => rw [← hsq]
          ring
      _ ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  have hJW : J ≤ (B.W N : ℝ) := by
    calc J ≤ (B.W N : ℝ) * B.ell N w * ((1 - w) * (mE E).im) := hJA
      _ = (B.W N : ℝ) * (B.ell N w * ((1 - w) * (mE E).im)) := by ring
      _ ≤ (B.W N : ℝ) * 1 := mul_le_mul_of_nonneg_left hℓη1 hW0.le
      _ = (B.W N : ℝ) := mul_one _
  have hη0 : 0 < etaT E w := etaT_pos_of_lt_one' hE hw1
  have hη1 : etaT E w ≤ 1 := by
    rw [Step2.etaT_eq]
    calc (1 - w) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
      _ = 1 := one_mul 1
  have hrg : B.ell N w / ℓs ≤ g * B.ell N w := by
    rw [div_le_iff₀ hℓs]
    calc B.ell N w = B.ell N w * 1 := (mul_one _).symm
      _ ≤ B.ell N w * B.ell N (s N) := mul_le_mul_of_nonneg_left hℓs1 (by linarith)
      _ ≤ B.ell N w * (g * ℓs) := mul_le_mul_of_nonneg_left hℓsg (by linarith)
      _ = g * B.ell N w * ℓs := by ring
  have hres := resCoef_le (Lr := (B.L N : ℝ)) (ρ := ρ) hW8 (by linarith : 0 < B.ell N w) hℓs hη0
    hη1 hρ (by linarith) hJW hℓwL hLW hrg hgW hD
  rw [Step2.etaT_eq] at hres
  have hp : ((1 - w') / (1 - v)) ^ 2 ≤ ((1 - w) / (1 - v)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hb.le)
      (div_le_div_of_nonneg_right (by linarith) hb.le) 2
  have hcore := mdr'_core (L := (B.L N : ℝ)) (D := D) (ρ := ρ) hW1 (Nat.cast_nonneg _) hm0 ha hb
    (by linarith) (by linarith) hℓs (by linarith) hg1 hrsq hx1 hAw hAv hJ1 hJx hres
    (Lemma57.cNear_nonneg hW1 (by linarith)) (cNear_le_one hℓw1)
    (Lemma57.cFar_nonneg hW1 (by linarith)) (cFar_le_one hℓw1) (sq_nonneg _) hp
  unfold mdr'
  rw [hthr, Step2.etaT_eq]
  exact hcore

end DriftPt

open DriftPt in
/-- **(T4'), deterministic core at one size parameter `N`** (successor of
`drift_time_sum_le_of`). Uniform grid `u_{j+1} = u_j + Δ`, `s N ≤ u_0`, `u_k ≤ t < 1`, step2's
`hreg` at `t` with gain `c`, `0 ≤ δ`, `24δ ≤ c`, `2ε ≤ δ`; reference scale `ℓ_s > 0` with
`ℓ_{s N} ≤ g ℓ_s`, `1 ≤ g ≤ 4 W^{2ζ}`; `W ≥ 8`, `L ≤ W`, `D ≥ 8 + 2ζ`; per-time inputs
`1 ≤ J_j ≤ N^{2ε} thr(u_j)` and T1513's `ρ_j ≤ 2 η_{u_j}⁻¹ J_j W^{-D}` (`j < k`):
`Σ_{j<k} Δ Mdr'(u_j) ((1-u_{j+1})/(1-u_k))²
  ≤ g³ ((2 c_near(W,1) + c_far(W,1) + 170 + 36e) m⁻¹ (η_s/η_{u_k})²) + e (WL)² W^{-D}`.
Exponent `2` on `R_{u_k}`. -/
theorem drift_time_sum_le_of' (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ}
    {δ ε D c ℓs g ζ : ℝ} {N : ℕ} (u : ℕ → ℝ) (Δ : ℝ) (hΔ0 : 0 ≤ Δ)
    (hu_step : ∀ j, u (j + 1) = u j + Δ) (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N)
    (hsu : s N ≤ u 0) {k : ℕ} {t : ℝ} (hkt : u k ≤ t) (ht1 : t < 1)
    (hreg : (N : ℝ) ^ c * (etaT E (s N) / etaT E t) ^ 30 ≤ B.scale E N t)
    (hδ0 : 0 ≤ δ) (hδc : 24 * δ ≤ c) (hεδ : 2 * ε ≤ δ)
    (hℓs : 0 < ℓs) (hg1 : 1 ≤ g) (hℓsg : B.ell N (s N) ≤ g * ℓs)
    (hgW : g ≤ 4 * (B.W N : ℝ) ^ (2 * ζ)) (hW8 : 8 ≤ (B.W N : ℝ))
    (hLW : (B.L N : ℝ) ≤ B.W N) (hD : 8 + 2 * ζ ≤ D)
    (J ρ : ℕ → ℝ) (hJ1 : ∀ j < k, 1 ≤ J j)
    (hJ : ∀ j < k, J j ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (u j))
    (hρ : ∀ j < k, ρ j ≤ 2 * (etaT E (u j))⁻¹ * J j * (B.W N : ℝ) ^ (-D)) :
    ∑ j ∈ Finset.range k, Δ * mdr' B E s δ D ℓs N (u j) (J j) (ρ j) *
        ((1 - u (j + 1)) / (1 - u k)) ^ 2
      ≤ g ^ 3 * ((2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170
            + 36 * exp 1) * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (u k)) ^ 2)
        + exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) := by
  have hu_mono : Monotone u :=
    monotone_nat_of_le_succ fun j => by rw [hu_step j]; linarith
  have hu_eq : ∀ j : ℕ, u j = u 0 + (j : ℝ) * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ n ih => rw [hu_step n, ih]; push_cast; ring
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have huk1 : u k < 1 := by linarith
  have hb : 0 < 1 - u k := by linarith
  have hs1 : s N < 1 := by linarith [hu_mono (Nat.zero_le k)]
  have hW0 : (0 : ℝ) < B.W N := by have := B.one_le_W N; linarith
  have hg3 : 0 ≤ g ^ 3 := by positivity
  set α := g ^ 3 * (Lemma57.cNear (B.W N : ℝ) 1 * (1 - s N) * √(1 - s N)
    / ((mE E).im * (1 - u k) ^ 2)) with hα
  set β := g ^ 3 * ((Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1)
    / ((mE E).im * (1 - u k) ^ 2)) with hβ
  set γ := exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) with hγ
  have hcN0 : 0 ≤ Lemma57.cNear (B.W N : ℝ) 1 := Lemma57.cNear_nonneg (B.one_le_W N) one_pos
  have hcF0 : 0 ≤ Lemma57.cFar (B.W N : ℝ) 1 := Lemma57.cFar_nonneg (B.one_le_W N) one_pos
  have hα0 : 0 ≤ α := by
    rw [hα]; have : 0 ≤ 1 - s N := by linarith
    positivity
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hγ0 : 0 ≤ γ := by rw [hγ]; have := Real.rpow_nonneg hW0.le (-D); positivity
  have hterm : ∀ j ∈ Finset.range k,
      Δ * mdr' B E s δ D ℓs N (u j) (J j) (ρ j) * ((1 - u (j + 1)) / (1 - u k)) ^ 2
        ≤ α * (Δ / √(1 - u j)) + Δ * (β * (1 - s N) + γ) := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    have hsj : s N ≤ u j := hsu.trans (hu_mono (Nat.zero_le j))
    have hjj : u j ≤ u (j + 1) := hu_mono (Nat.le_succ j)
    have hj1k : u (j + 1) ≤ u k := hu_mono hjk
    have hpt := mdr'_mul_le B hE hN1 hs0 hsj hjj hj1k hkt ht1 hreg hδ0 hδc hεδ hℓs hg1 hℓsg
      hgW hW8 hLW hD (hJ1 j hjk) (hJ j hjk) (hρ j hjk)
    have hpt' : mdr' B E s δ D ℓs N (u j) (J j) (ρ j) * ((1 - u (j + 1)) / (1 - u k)) ^ 2
        ≤ α / √(1 - u j) + β * (1 - u j) + γ := by
      refine hpt.trans (le_of_eq ?_)
      rw [hα, hβ, hγ]; ring
    have hβj : β * (1 - u j) ≤ β * (1 - s N) := mul_le_mul_of_nonneg_left (by linarith) hβ0
    calc Δ * mdr' B E s δ D ℓs N (u j) (J j) (ρ j) * ((1 - u (j + 1)) / (1 - u k)) ^ 2
        = Δ * (mdr' B E s δ D ℓs N (u j) (J j) (ρ j) *
            ((1 - u (j + 1)) / (1 - u k)) ^ 2) := by ring
      _ ≤ Δ * (α / √(1 - u j) + β * (1 - u j) + γ) := mul_le_mul_of_nonneg_left hpt' hΔ0
      _ ≤ Δ * (α / √(1 - u j) + β * (1 - s N) + γ) := by gcongr
      _ = α * (Δ / √(1 - u j)) + Δ * (β * (1 - s N) + γ) := by ring
  have hkΔ : (k : ℝ) * Δ ≤ 1 - s N := by
    have := hu_eq k; linarith
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := by positivity
  have htel := DriftPt.sum_step_div_sqrt_le u Δ hΔ0 hu_step huk1
  have hsq0 : √(1 - u 0) ≤ √(1 - s N) := Real.sqrt_le_sqrt (by linarith)
  have hC0 : 0 ≤ β * (1 - s N) + γ := by
    have : 0 ≤ 1 - s N := by linarith
    positivity
  have hRatio : etaT E (s N) / etaT E (u k) = (1 - s N) / (1 - u k) := Step2.etaT_ratio hE _ _
  calc ∑ j ∈ Finset.range k, Δ * mdr' B E s δ D ℓs N (u j) (J j) (ρ j) *
          ((1 - u (j + 1)) / (1 - u k)) ^ 2
      ≤ ∑ j ∈ Finset.range k, (α * (Δ / √(1 - u j)) + Δ * (β * (1 - s N) + γ)) :=
        Finset.sum_le_sum hterm
    _ = α * ∑ j ∈ Finset.range k, Δ / √(1 - u j) + (k : ℝ) * Δ * (β * (1 - s N) + γ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        ring
    _ ≤ α * (2 * √(1 - s N)) + (1 - s N) * (β * (1 - s N) + γ) := by
        gcongr
        exact htel.trans (by linarith)
    _ ≤ α * (2 * √(1 - s N)) + (β * (1 - s N) ^ 2 + γ) := by
        have : (1 - s N) * γ ≤ γ := mul_le_of_le_one_left hγ0 (by linarith [hs0])
        nlinarith
    _ = g ^ 3 * ((2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170
            + 36 * exp 1) * ((mE E).im)⁻¹ * (etaT E (s N) / etaT E (u k)) ^ 2) + γ := by
        rw [hRatio, hα, hβ]
        have hb2 : (1 - u k) ^ 2 ≠ 0 := by positivity
        field_simp
        have hsq : √(1 - s N) ^ 2 = 1 - s N := Real.sq_sqrt (by linarith)
        linear_combination (2 * g ^ 3 * Lemma57.cNear (B.W N : ℝ) 1 * (1 - s N)) * hsq

open DriftPt in
/-- **(T4'), eventual form with a reference-scale family.** For fixed `|E| < 2`, `0 ≤ s`, `t < 1`,
step2's `hreg` (eventually, at `t N`), `0 ≤ δ ≤ c/24`, `2ε ≤ δ`, `0 ≤ ζ`, `D ≥ 8 + 2ζ`, and a
family `(ℓs N, g N)` with, eventually (whenever `s N < 1`), `0 < ℓs N`, `1 ≤ g N`,
`ℓ_{s N} ≤ g N · ℓs N`, `g N ≤ 4 W^{2ζ}`: for every `κ > 0`, eventually in `N`, uniformly in
`T N ∈ [s N, t N]`, `Kq N ≥ 1`, `k ≤ Kq N` and all per-time inputs `1 ≤ J_j ≤ N^{2ε} thr(u_j)`,
`ρ_j ≤ 2 η_{u_j}⁻¹ J_j W^{-D}`:
`Σ_{j<k} Δ Mdr'(u_j) ((1-u_{j+1})/(1-u_k))² ≤ (300/Im m) · g³ · N^κ · ((η_s/η_{u_k})² + 1)`. -/
theorem drift_time_sum_le_scale' (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D ζ : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ)
    (hD : 8 + 2 * ζ ≤ D) (ℓsF gF : ℕ → ℝ)
    (hscale : ∀ᶠ N : ℕ in Filter.atTop, s N < 1 → 0 < ℓsF N ∧ 1 ≤ gF N ∧
      B.ell N (s N) ≤ gF N * ℓsF N ∧ gF N ≤ 4 * (B.W N : ℝ) ^ (2 * ζ)) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N → ∀ J ρ : ℕ → ℝ,
        (∀ j < k, 1 ≤ J j) →
        (∀ j < k, J j ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s T Kq N j)) →
        (∀ j < k, ρ j ≤ 2 * (etaT E (time s T Kq N j))⁻¹ * J j * (B.W N : ℝ) ^ (-D)) →
        ∑ j ∈ Finset.range k, step s T Kq N *
            mdr' B E s δ D (ℓsF N) N (time s T Kq N j) (J j) (ρ j) *
            ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 2
          ≤ driftSumConst E * gF N ^ 3 * (N : ℝ) ^ κ *
              ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 2 + 1) := by
  intro κ hκ
  have hD4 : 4 ≤ D := by linarith
  filter_upwards [eventually_cNear_cFar_le B hκ, eventually_sq_WL_rpow_le B hD4, hreg,
    Filter.eventually_ge_atTop 1, hscale, (Step2.tendsto_W B).eventually_ge_atTop 8,
    B.dim, Step2.eventually_le_W_sq B]
    with N hcNF hWL hregN hN1 hsc hW8 hdim hNW T Kq hsT hTt hK k hk J ρ hJ1 hJ hρ
  have hsN1 : s N < 1 := lt_of_le_of_lt (hsT.trans hTt) (ht1 N)
  obtain ⟨hℓs, hg1, hℓsg, hgW⟩ := hsc hsN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hLW : (B.L N : ℝ) ≤ B.W N := by
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  have hKpos : (0 : ℝ) < (Kq N : ℝ) := by exact_mod_cast hK
  have hΔ0 : 0 ≤ step s T Kq N := div_nonneg (by linarith) hKpos.le
  have hu_step : ∀ j, time s T Kq N (j + 1) = time s T Kq N j + step s T Kq N := by
    intro j; unfold time; push_cast; ring
  have hkt : time s T Kq N k ≤ t N := by
    have : (k : ℝ) ≤ Kq N := by exact_mod_cast hk
    have := mul_le_mul_of_nonneg_right this hΔ0
    have hKΔ : (Kq N : ℝ) * step s T Kq N = T N - s N := by
      unfold step; field_simp
    unfold time; linarith
  have hcore := drift_time_sum_le_of' B hE (time s T Kq N) (step s T Kq N) hΔ0 hu_step hN1'
    (hs0 N) (by simp) hkt (ht1 N) hregN hδ0 (by linarith) hεδ hℓs hg1 hℓsg hgW hW8 hLW hD
    J ρ hJ1 hJ hρ
  refine hcore.trans ?_
  obtain ⟨hcN, hcF⟩ := hcNF
  set P := (N : ℝ) ^ κ with hP
  set R2 := (etaT E (s N) / etaT E (time s T Kq N k)) ^ 2 with hR2
  set mi := ((mE E).im)⁻¹ with hmi
  set G := gF N ^ 3 with hG
  have hG1 : 1 ≤ G := one_le_pow₀ hg1
  have hP1 : 1 ≤ P := Real.one_le_rpow hN1' hκ.le
  have hR20 : 0 ≤ R2 := sq_nonneg _
  have hmi1 : 1 ≤ mi := (one_le_inv₀ hm0).2 hm1
  have he3 : exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 : 0 < exp 1 := exp_pos 1
  have hγ : exp 1 * (((B.W N : ℝ) * B.L N) ^ 2 * (B.W N : ℝ) ^ (-D)) ≤ 3 :=
    (mul_le_mul_of_nonneg_left hWL he0.le).trans (by linarith)
  have hbr : 2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170 + 36 * exp 1
      ≤ 274 * P := by
    have := Real.exp_one_lt_d9
    linarith
  have hdc : driftSumConst E = 300 * mi := by rw [driftSumConst, hmi]; ring
  rw [hdc]
  have hmiR : 0 ≤ mi * R2 := by positivity
  have h1 : G * ((2 * Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170
        + 36 * exp 1) * mi * R2) ≤ G * (274 * P * (mi * R2)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hbr hmiR
  have hGPm : 1 ≤ G * P * mi := by
    have := one_le_mul_of_one_le_of_one_le hG1 hP1
    exact one_le_mul_of_one_le_of_one_le this hmi1
  have hX0 : 0 ≤ G * P * mi * R2 := by positivity
  have e1 : G * (274 * P * (mi * R2)) = 274 * (G * P * mi * R2) := by ring
  have e2 : 300 * mi * G * P * (R2 + 1) = 300 * (G * P * mi * R2) + 300 * (G * P * mi) := by ring
  rw [e2]
  linarith

open DriftPt in
/-- **(T4') `RBM.Gauss.Grid.drift_time_sum_le'`** — successor of `drift_time_sum_le`, with the
unsatisfiable premise `L ρ_j W^D ≤ 1` replaced by T1513's `ρ_j ≤ 2 η_{u_j}⁻¹ J_j W^{-D}`
(`rho554_le_two_mul_rpow`, same `D`), `D ≥ D₀ = 8`, and the coefficient `Mdr'` (residue absorbed
on the near band only). Reference scale `ℓ_s = ℓ_{s N}`. Conclusion unchanged:
`Σ_{j<k} Δ · Mdr'(u_j) · ((1-u_{j+1})/(1-u_k))² ≤ (300/Im m) · N^κ · ((η_s/η_{u_k})² + 1)`.
**Exponent `e = 2`.** No `1 ≤ ℓ_s` premise. -/
theorem drift_time_sum_le' (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) (hεδ : 2 * ε ≤ δ) (hD : 8 ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N → ∀ J ρ : ℕ → ℝ,
        (∀ j < k, 1 ≤ J j) →
        (∀ j < k, J j ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s T Kq N j)) →
        (∀ j < k, ρ j ≤ 2 * (etaT E (time s T Kq N j))⁻¹ * J j * (B.W N : ℝ) ^ (-D)) →
        ∑ j ∈ Finset.range k, step s T Kq N *
            mdr' B E s δ D (B.ell N (s N)) N (time s T Kq N j) (J j) (ρ j) *
            ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 2
          ≤ driftSumConst E * (N : ℝ) ^ κ *
              ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 2 + 1) := by
  intro κ hκ
  have h := drift_time_sum_le_scale' B hE hs0 ht1 hreg (D := D) (ζ := 0) hδ0 hδc hεδ le_rfl
    (by linarith) (fun N => B.ell N (s N)) (fun _ => 1)
    (Filter.Eventually.of_forall fun N hs1 => by
      refine ⟨?_, le_rfl, by simp, ?_⟩
      · have := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
        exact lt_of_lt_of_le one_pos this
      · simp only [mul_zero, Real.rpow_zero, mul_one]; norm_num) κ hκ
  filter_upwards [h] with N hN T Kq hsT hTt hK k hk J ρ hJ1 hJ hρ
  have := hN T Kq hsT hTt hK k hk J ρ hJ1 hJ hρ
  simpa using this

/-- `N^ζ ≤ W^{2ζ}` from `N ≤ W²`, `ζ ≥ 0`. -/
theorem DriftPt.natCast_rpow_le_W_rpow {N W ζ : ℝ} (hN0 : 0 ≤ N) (hNW : N ≤ W ^ 2)
    (hζ0 : 0 ≤ ζ) (hW0 : 0 ≤ W) : N ^ ζ ≤ W ^ (2 * ζ) := by
  calc N ^ ζ ≤ (W ^ 2) ^ ζ := Real.rpow_le_rpow hN0 hNW hζ0
    _ = W ^ (2 * ζ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; norm_num

open DriftPt in
/-- **(T4'), rescaled reference scale `ℓ_s' = ℓ_{s N}/(4N^ζ)`** (the scale at which T1501 is
applied on T1513's good set, because of `honeSet`'s `hκ` and `eq273Set`'s `N^{τ3}` loss): the same
time sum with `Mdr'` evaluated at `ℓ_s'`, for `ζ ≥ 0`, `D ≥ D₀ = 8 + 2ζ`. The factor `(4N^ζ)³ =
64 N^{3ζ}` goes into the constant (downstream, `κ, ζ ≤ δ/48` keeps `N^{κ+3ζ} ≤ N^{δ/8}`). -/
theorem drift_time_sum_le_rescaled' (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D ζ : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ)
    (hD : 8 + 2 * ζ ≤ D) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (T : ℕ → ℝ) (Kq : ℕ → ℕ),
      s N ≤ T N → T N ≤ t N → 1 ≤ Kq N → ∀ k : ℕ, k ≤ Kq N → ∀ J ρ : ℕ → ℝ,
        (∀ j < k, 1 ≤ J j) →
        (∀ j < k, J j ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N (time s T Kq N j)) →
        (∀ j < k, ρ j ≤ 2 * (etaT E (time s T Kq N j))⁻¹ * J j * (B.W N : ℝ) ^ (-D)) →
        ∑ j ∈ Finset.range k, step s T Kq N *
            mdr' B E s δ D (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) N (time s T Kq N j) (J j) (ρ j) *
            ((1 - time s T Kq N (j + 1)) / (1 - time s T Kq N k)) ^ 2
          ≤ driftSumConst E * (4 * (N : ℝ) ^ ζ) ^ 3 * (N : ℝ) ^ κ *
              ((etaT E (s N) / etaT E (time s T Kq N k)) ^ 2 + 1) := by
  refine drift_time_sum_le_scale' B hE hs0 ht1 hreg (D := D) hδ0 hδc hεδ hζ0 hD
    (fun N => B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) (fun N => 4 * (N : ℝ) ^ ζ) ?_
  filter_upwards [Filter.eventually_ge_atTop 1, Step2.eventually_le_W_sq B] with N hN1 hNW hs1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN1' hζ0
  have hℓ1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg (B.one_le_L N) (hs0 N) hs1
  have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  refine ⟨by positivity, by linarith, le_of_eq (by field_simp), ?_⟩
  have := natCast_rpow_le_W_rpow (Nat.cast_nonneg N) hNW hζ0 hW0
  linarith

/-- **Compiled witness for the per-time inputs of (T4')**: the extreme choices
`J = N^{2ε} thr(u)` and `ρ = 2 η_u⁻¹ J W^{-D}` (strictly positive, the largest value the premise
allows) satisfy `1 ≤ J ≤ N^{2ε} thr(u)` and `0 < ρ ≤ 2 η_u⁻¹ J W^{-D}` at every
`u ∈ [s N, 1)`, `N ≥ 1`, `0 ≤ δ`, `0 ≤ ε`. The fixed-parameter premises (`hreg`, `δ ≤ c/24`,
`2ε ≤ δ`, `D ≥ 60 ≥ 8 + 2ζ` for `ζ ≤ 26`) are those of T1508's compiled
`qv_time_sum_le_hyps_witness`. T1513's own `rho554(J)` also satisfies the `ρ`-premise once
`2D² ≤ log W` (`rho554_le_two_mul_rpow`). -/
theorem drift_time_sum_inputs_witness' (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ}
    {δ ε D : ℝ} {N : ℕ} (hN1 : (1 : ℝ) ≤ N) (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) {u : ℝ}
    (hsu : s N ≤ u) (hu1 : u < 1) :
    1 ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ∧
      (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ∧
      0 < 2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) * (B.W N : ℝ) ^ (-D) ∧
      2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) * (B.W N : ℝ) ^ (-D)
        ≤ 2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) * (B.W N : ℝ) ^ (-D) := by
  have hs1 : s N < 1 := hsu.trans_lt hu1
  have hR : 1 ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith)]; linarith
  have h1 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have h2 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have h3 : 1 ≤ (etaT E (s N) / etaT E u) ^ 4 := one_le_pow₀ hR
  have hJ1 : 1 ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u := by
    unfold Step2.thr
    calc (1 : ℝ) = 1 * (1 * 1) := by ring
      _ ≤ (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * (etaT E (s N) / etaT E u) ^ 4) := by gcongr
  have hη : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hW0 : (0 : ℝ) < B.W N := by have := B.one_le_W N; linarith
  have hWD : 0 < (B.W N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW0 _
  refine ⟨hJ1, le_rfl, ?_, le_rfl⟩
  have : 0 < (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u := by linarith
  positivity

/-! ## (T5) : the drift bound in the `hdrift` shape of T1518 (T1)

On the good set `{jSMat ≤ thr(u)} ∩ {jGMat ≤ N^{2ε} thr(u)}` (T1513), with the rescaled
reference scale `ℓ_s' = ℓ_{s N}/(4N^ζ)` and `J := N^{2ε} thr(u)`. The `jGMat` corollary: T1513's
block quantities `gmBlkMat`/`gsqBlkMat` and their lemmas are `private`, so `DriftPt.gsqBlkM` below
restates `gsqBlkMat`'s body with `DriftPt.gmBlkM`, `DriftPt.jGMat_eq` identifies `jGMat` with it
by `rfl`, and the three short proofs (`gmBlkMat_mul_swap_le_gsqBlkMat`,
`gsqBlkMat_le_jGMat_mul_tailT`, `one_le_jGMat`) are copied. -/

namespace DriftPt

/-- The two-block maximum of T1513's `jGMat` (same body as T1513's private `gsqBlkMat`). -/
noncomputable def gsqBlkM (B : Band Ω) (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : ℝ :=
  (Finset.univ : Finset (ZMod (B.L N))).sup' ⟨0, Finset.mem_univ _⟩
    (fun x' => if SB (B.L N) x x' ≠ 0 then gmBlkM B N M z y x' * gmBlkM B N M z x' y else 0)

/-- T1513's `jGMat`, unfolded through `gsqBlkM` (definitional). -/
theorem jGMat_eq (E : ℝ) (N : ℕ) (u ℓu ηu D : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) :
    jGMat B.toDims E N u ℓu ηu D M = 1 +
      (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup' ⟨(0, 0), Finset.mem_univ _⟩
        (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
          then gsqBlkM B N M (zt E u) p.1 p.2 /
            tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
          else 0) := rfl

theorem gsqBlkM_nonneg (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : 0 ≤ gsqBlkM B N M z x y := by
  unfold gsqBlkM
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : ZMod (B.L N))))
  split_ifs
  · exact mul_nonneg (gmBlkM_nonneg B N M z _ _) (gmBlkM_nonneg B N M z _ _)
  · exact le_rfl

/-- Copy of T1513's private `one_le_jGMat`. -/
theorem one_le_jGMat' (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    {ℓu ηu D : ℝ} : 1 ≤ jGMat B.toDims E N u ℓu ηu D M := by
  rw [jGMat_eq]
  have h0 : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
        then gsqBlkM B N M (zt E u) p.1 p.2 /
          tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans ?_
      (Finset.le_sup' _ (Finset.mem_univ ((0 : ZMod (B.L N)), (0 : ZMod (B.L N)))))
    dsimp only
    split
    · exact div_nonneg (gsqBlkM_nonneg N M _ _ _)
        (tailT_pos (by exact_mod_cast B.W_pos N) _).le
    · exact le_rfl
  linarith

/-- Copy of T1513's private `gmBlkMat_mul_swap_le_gsqBlkMat`. -/
theorem gmBlkM_mul_swap_le_gsqBlkM (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : gmBlkM B N M z x y * gmBlkM B N M z y x ≤ gsqBlkM B N M z x y := by
  unfold gsqBlkM
  have hSB : SB (B.L N) x x ≠ 0 := by simp [SB_apply, sbKernel, sbSupport]
  have h := Finset.le_sup' (s := (Finset.univ : Finset (ZMod (B.L N))))
    (f := fun x' => if SB (B.L N) x x' ≠ 0 then
      gmBlkM B N M z y x' * gmBlkM B N M z x' y else 0)
    (Finset.mem_univ x)
  simpa [hSB, mul_comm] using h

/-- Copy of T1513's private `gsqBlkMat_le_jGMat_mul_tailT`. -/
theorem gsqBlkM_le_jGMat_mul_tailT (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    {ℓu ηu D : ℝ} (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ)) :
    gsqBlkM B N M (zt E u) x y ≤ jGMat B.toDims E N u ℓu ηu D M *
      tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
  have hW : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  set T := tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) with hTdef
  have hT : 0 < T := tailT_pos hW _
  have hsup : gsqBlkM B N M (zt E u) x y / T ≤
      (Finset.univ : Finset (ZMod (B.L N) × ZMod (B.L N))).sup'
      ⟨(0, 0), Finset.mem_univ _⟩
      (fun p => if ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (p.1 - p.2) : ℝ)
        then gsqBlkM B N M (zt E u) p.1 p.2 /
          tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (p.1 - p.2))
        else 0) := by
    refine le_trans (le_of_eq ?_) (Finset.le_sup' _ (Finset.mem_univ (x, y)))
    dsimp only
    split
    · rfl
    · rename_i hn
      exact absurd hxy hn
  have hle : gsqBlkM B N M (zt E u) x y / T ≤ jGMat B.toDims E N u ℓu ηu D M := by
    rw [jGMat_eq]
    linarith
  have := mul_le_mul_of_nonneg_right hle hT.le
  rwa [div_mul_cancel₀ _ hT.ne'] at this

/-- **`jGMat` corollary, (5.31) side**: on far pairs the `(+,-)` two-loop of a Hermitian `M` is
`≤ jGMat(M) · T_{u,D}` (T1501's `h531` with `J := jGMat`). -/
theorem two_loop_re_le_jGMat {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓu ηu D : ℝ} (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ)) :
    (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
      jGMat B.toDims E N u ℓu ηu D M * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
  ((two_loop_re_le_gmBlkM hM (zt E u) x y).trans
    (gmBlkM_mul_swap_le_gsqBlkM N M (zt E u) x y)).trans
    (gsqBlkM_le_jGMat_mul_tailT E N u M x y hxy)

/-- **`jGMat` corollary, (4.2) side**: on far pairs the block maximum of a Hermitian `M` is
`≤ √(jGMat(M) · T_{u,D})` (T1501's `h42` with `J := jGMat`). -/
theorem gmBlkM_le_sqrt_jGMat {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓu ηu D : ℝ} (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ)) :
    gmBlkM B N M (zt E u) x y ≤
      √(jGMat B.toDims E N u ℓu ηu D M * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) := by
  apply Real.le_sqrt_of_sq_le
  calc gmBlkM B N M (zt E u) x y ^ 2
      = gmBlkM B N M (zt E u) x y * gmBlkM B N M (zt E u) y x := by
        rw [← gmBlkM_comm hM (zt E u) x y]; ring
    _ ≤ gsqBlkM B N M (zt E u) x y := gmBlkM_mul_swap_le_gsqBlkM N M (zt E u) x y
    _ ≤ _ := gsqBlkM_le_jGMat_mul_tailT E N u M x y hxy

/-- `A_u = W ℓ_u η_u ≤ W` for `0 ≤ u < 1` (`ℓ_u √(1-u) ≤ 1`, `Im m ≤ 1`). -/
theorem scale_le_W (B : Band Ω) {E : ℝ} (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) : B.scale E N u ≤ (B.W N : ℝ) := by
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have ha : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have hℓ1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hℓ0 : 0 ≤ B.ell N u := by linarith
  have h1 := ell_mul_sqrt_le_one B N hu1
  have hs : √(1 - u) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hsq : √(1 - u) * √(1 - u) = 1 - u := Real.mul_self_sqrt ha.le
  have hℓη : B.ell N u * ((1 - u) * (mE E).im) ≤ 1 := by
    calc B.ell N u * ((1 - u) * (mE E).im)
        = (B.ell N u * √(1 - u)) * √(1 - u) * (mE E).im := by
          conv_lhs => rw [← hsq]
          ring
      _ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  change (B.W N : ℝ) * B.ell N u * ((1 - u) * (mE E).im) ≤ (B.W N : ℝ)
  calc (B.W N : ℝ) * B.ell N u * ((1 - u) * (mE E).im)
      = (B.W N : ℝ) * (B.ell N u * ((1 - u) * (mE E).im)) := by ring
    _ ≤ (B.W N : ℝ) * 1 := mul_le_mul_of_nonneg_left hℓη hW0
    _ = (B.W N : ℝ) := mul_one _

/-- **(T5), scalar core**: the `η⁻¹`-part of `Mdr'` at `ℓ_s' = ℓ_s/g`, `J = yΛ`, is bounded by the
`Mg η⁻¹ (q + A^{-1/3} Λ³)` slot of T1518's `hdrift`, `Mg = g² (c_near + c_far + 170)`,
`q = (g r₀)³ + 1`, when `r₀ = ℓ_u/ℓ_s ≥ 1`, `r₀² ≤ R`, `Λ = x R⁴`, `1 ≤ y ≤ x`, `A ≥ 1`, and the
residue coefficient is `≤ η⁻¹`. -/
theorem heG_coef_le {η A cNw cFw cN cF g r r0 R x y Λ res : ℝ}
    (hη : 0 < η) (hA : 1 ≤ A) (hcNw0 : 0 ≤ cNw) (hcNw : cNw ≤ cN) (hcFw0 : 0 ≤ cFw)
    (hcFw : cFw ≤ cF) (hg1 : 1 ≤ g) (hr : r = g * r0) (hr01 : 1 ≤ r0) (hr0R : r0 ^ 2 ≤ R)
    (hx1 : 1 ≤ x) (hΛ : Λ = x * R ^ 4) (hy1 : 1 ≤ y) (hyx : y ≤ x) (hres : res ≤ η⁻¹) :
    η⁻¹ * (cNw * r ^ 3 + cFw * (r * √r * (√A)⁻¹ * (y * Λ))
        + 169 * (r * A⁻¹ * ((y * Λ) * √(y * Λ)))) + res
      ≤ g ^ 2 * (cN + cF + 170) * η⁻¹ * (((g * r0) ^ 3 + 1) + A⁻¹ ^ ((1 : ℝ) / 3) * Λ ^ 3) := by
  subst hr hΛ
  have hηi : 0 < η⁻¹ := inv_pos.2 hη
  have hA0 : 0 < A := by linarith
  have hR1 : 1 ≤ R := by nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hr00 : 0 ≤ r0 := by linarith
  have hcN0 : 0 ≤ cN := hcNw0.trans hcNw
  have hcF0 : 0 ≤ cF := hcFw0.trans hcFw
  set Λ := x * R ^ 4 with hΛdef
  have hΛ1 : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le hx1 (one_le_pow₀ hR1)
  have hΛ0 : 0 ≤ Λ := by linarith
  set A' := A⁻¹ ^ ((1 : ℝ) / 3) with hA'
  have hA'0 : 0 ≤ A' := Real.rpow_nonneg (by positivity) _
  have hsA : (√A)⁻¹ ≤ A' := Lemma57.inv_sqrt_le_rpow_third hA
  have hiA : A⁻¹ ≤ A' := Lemma57.inv_le_rpow_third hA
  have hgr1 : 1 ≤ g * r0 := one_le_mul_of_one_le_of_one_le hg1 hr01
  have hg2 : 1 ≤ g ^ 2 := one_le_pow₀ hg1
  -- (2) the `c_far` piece
  have hsg : √g ≤ g := Lemma57.sqrt_le_self hg1
  have hrr : g * r0 * √(g * r0) ≤ g ^ 2 * (r0 * √r0) := by
    rw [Real.sqrt_mul hg0]
    calc g * r0 * (√g * √r0) = √g * (g * (r0 * √r0)) := by ring
      _ ≤ g * (g * (r0 * √r0)) := by
          apply mul_le_mul_of_nonneg_right hsg; positivity
      _ = g ^ 2 * (r0 * √r0) := by ring
  have hk2 : r0 * √r0 * (y * Λ) ≤ Λ ^ 3 := by
    have hl0 : 0 ≤ r0 * √r0 * (y * Λ) := by positivity
    have hr0 : 0 ≤ Λ ^ 3 := by positivity
    refine (pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero).1 ?_
    have hr3 : r0 ^ 3 ≤ R ^ 2 := by
      calc r0 ^ 3 ≤ r0 ^ 4 := pow_le_pow_right₀ hr01 (by norm_num)
        _ = (r0 ^ 2) ^ 2 := by ring
        _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hr0R 2
    have hy2 : y ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy0 hyx 2
    have hRx : R ^ 2 * x ^ 2 ≤ Λ ^ 4 := by
      rw [hΛdef]
      calc R ^ 2 * x ^ 2 ≤ R ^ 16 * x ^ 4 :=
            mul_le_mul (pow_le_pow_right₀ hR1 (by norm_num)) (pow_le_pow_right₀ hx1 (by norm_num))
              (by positivity) (by positivity)
        _ = (x * R ^ 4) ^ 4 := by ring
    calc (r0 * √r0 * (y * Λ)) ^ 2 = r0 ^ 2 * (√r0) ^ 2 * y ^ 2 * Λ ^ 2 := by ring
      _ = r0 ^ 3 * y ^ 2 * Λ ^ 2 := by rw [Real.sq_sqrt hr00]; ring
      _ ≤ R ^ 2 * x ^ 2 * Λ ^ 2 := by gcongr
      _ ≤ Λ ^ 4 * Λ ^ 2 := by gcongr
      _ = (Λ ^ 3) ^ 2 := by ring
  have hT2 : cFw * (g * r0 * √(g * r0) * (√A)⁻¹ * (y * Λ)) ≤ g ^ 2 * cF * (A' * Λ ^ 3) := by
    calc cFw * (g * r0 * √(g * r0) * (√A)⁻¹ * (y * Λ))
        = cFw * ((g * r0 * √(g * r0)) * (y * Λ) * (√A)⁻¹) := by ring
      _ ≤ cF * ((g ^ 2 * (r0 * √r0)) * (y * Λ) * A') := by gcongr
      _ = g ^ 2 * cF * ((r0 * √r0 * (y * Λ)) * A') := by ring
      _ ≤ g ^ 2 * cF * (Λ ^ 3 * A') := by gcongr
      _ = g ^ 2 * cF * (A' * Λ ^ 3) := by ring
  -- (3) the `169` piece
  have hk3 : r0 * ((y * Λ) * √(y * Λ)) ≤ Λ ^ 3 := by
    have hl0 : 0 ≤ r0 * ((y * Λ) * √(y * Λ)) := by positivity
    have hr0 : 0 ≤ Λ ^ 3 := by positivity
    refine (pow_le_pow_iff_left₀ hl0 hr0 two_ne_zero).1 ?_
    have hy3 : y ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hy0 hyx 3
    have hRx : R * x ^ 3 ≤ Λ ^ 3 := by
      rw [hΛdef]
      calc R * x ^ 3 ≤ R ^ 12 * x ^ 3 :=
            mul_le_mul_of_nonneg_right (le_self_pow₀ hR1 (by norm_num)) (by positivity)
        _ = (x * R ^ 4) ^ 3 := by ring
    have hyΛ : 0 ≤ y * Λ := by positivity
    calc (r0 * ((y * Λ) * √(y * Λ))) ^ 2 = r0 ^ 2 * (y * Λ) ^ 2 * (√(y * Λ)) ^ 2 := by ring
      _ = r0 ^ 2 * y ^ 3 * Λ ^ 3 := by rw [Real.sq_sqrt hyΛ]; ring
      _ ≤ R * x ^ 3 * Λ ^ 3 := by gcongr
      _ ≤ Λ ^ 3 * Λ ^ 3 := by gcongr
      _ = (Λ ^ 3) ^ 2 := by ring
  have hT3 : 169 * (g * r0 * A⁻¹ * ((y * Λ) * √(y * Λ))) ≤ g ^ 2 * 169 * (A' * Λ ^ 3) := by
    have hgg : g ≤ g ^ 2 := le_self_pow₀ hg1 two_ne_zero
    calc 169 * (g * r0 * A⁻¹ * ((y * Λ) * √(y * Λ)))
        = 169 * (g * (r0 * ((y * Λ) * √(y * Λ))) * A⁻¹) := by ring
      _ ≤ 169 * (g ^ 2 * Λ ^ 3 * A') := by gcongr
      _ = g ^ 2 * 169 * (A' * Λ ^ 3) := by ring
  -- (1) the near piece and the residue
  have hT1 : cNw * (g * r0) ^ 3 ≤ cN * ((g * r0) ^ 3 + 1) := by
    have : cNw * (g * r0) ^ 3 ≤ cN * (g * r0) ^ 3 := by gcongr
    nlinarith
  -- assemble
  have hM1 : cN + 1 ≤ g ^ 2 * (cN + cF + 170) := by nlinarith
  have hM2 : g ^ 2 * (cF + 169) ≤ g ^ 2 * (cN + cF + 170) := by nlinarith
  have hq0 : 0 ≤ (g * r0) ^ 3 + 1 := by positivity
  have hAL0 : 0 ≤ A' * Λ ^ 3 := by positivity
  have hsum : cNw * (g * r0) ^ 3 + cFw * (g * r0 * √(g * r0) * (√A)⁻¹ * (y * Λ))
        + 169 * (g * r0 * A⁻¹ * ((y * Λ) * √(y * Λ))) + 1
      ≤ g ^ 2 * (cN + cF + 170) * (((g * r0) ^ 3 + 1) + A' * Λ ^ 3) := by
    have hq1 : 1 ≤ (g * r0) ^ 3 + 1 := by
      have := pow_nonneg (by linarith : (0 : ℝ) ≤ g * r0) 3; linarith
    have e1 : cN * ((g * r0) ^ 3 + 1) + 1 ≤ (cN + 1) * ((g * r0) ^ 3 + 1) := by
      have h : (cN + 1) * ((g * r0) ^ 3 + 1) = cN * ((g * r0) ^ 3 + 1) + ((g * r0) ^ 3 + 1) := by
        ring
      linarith
    have e2 := mul_le_mul_of_nonneg_right hM1 hq0
    have e3 := mul_le_mul_of_nonneg_right hM2 hAL0
    linarith [hT1, hT2, hT3, e1, e2, e3]
  have := mul_le_mul_of_nonneg_left hsum hηi.le
  linarith [this, hres]

end DriftPt

/-- **The explicit drift constant `Mg` of (T5)**: `Mg = (4N^ζ)² (c_near(W,1) + c_far(W,1) + 170)`,
a function of `N` only (no dependence on `u`, the matrix, or `b`). -/
noncomputable def mgDrift (B : Band Ω) (ζ : ℝ) (N : ℕ) : ℝ :=
  (4 * (N : ℝ) ^ ζ) ^ 2 * (Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170)

/-- `Mg ≤ 2752 N^{κ+3ζ}` eventually, for every `κ > 0` and `ζ ≥ 0` (in fact `≤ 2752 N^{κ+2ζ}`). -/
theorem mgDrift_le (B : Band Ω) {κ ζ : ℝ} (hκ : 0 < κ) (hζ0 : 0 ≤ ζ) :
    ∀ᶠ N : ℕ in Filter.atTop, mgDrift B ζ N ≤ 2752 * (N : ℝ) ^ (κ + 3 * ζ) := by
  filter_upwards [DriftPt.eventually_cNear_cFar_le B hκ, Filter.eventually_ge_atTop 1]
    with N hc hN1
  obtain ⟨hcN, hcF⟩ := hc
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hP1 : 1 ≤ (N : ℝ) ^ κ := Real.one_le_rpow hN1' hκ.le
  have hsq : ((N : ℝ) ^ ζ) ^ 2 = (N : ℝ) ^ (2 * ζ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hexp : (N : ℝ) ^ (2 * ζ) * (N : ℝ) ^ κ ≤ (N : ℝ) ^ (κ + 3 * ζ) := by
    rw [← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hz0 : 0 ≤ (N : ℝ) ^ (2 * ζ) := Real.rpow_nonneg hN0.le _
  unfold mgDrift
  calc (4 * (N : ℝ) ^ ζ) ^ 2 * (Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170)
      = 16 * (N : ℝ) ^ (2 * ζ) *
          (Lemma57.cNear (B.W N : ℝ) 1 + Lemma57.cFar (B.W N : ℝ) 1 + 170) := by
        rw [mul_pow, hsq]; ring
    _ ≤ 16 * (N : ℝ) ^ (2 * ζ) * (172 * (N : ℝ) ^ κ) := by
        gcongr; linarith
    _ = 2752 * ((N : ℝ) ^ (2 * ζ) * (N : ℝ) ^ κ) := by ring
    _ ≤ 2752 * (N : ℝ) ^ (κ + 3 * ζ) := by gcongr

open DriftPt in
/-- **(T5) `RBM.Gauss.Grid.drift_point_le_heG`**: (T3')'s conclusion in exactly the `hdrift` shape
of T1518 (T1),
`‖D b‖ ≤ (e Λ(u)² (36 η_u⁻¹ A_u⁻¹ + W L W^{-D}) + Mg η_u⁻¹ (q_u + A_u^{-1/3} Λ(u)³)) T_u(b)`,
`Λ = thr E s δ N`, `A_u = B.scale E N u`, `q_u = (4N^ζ ℓ_u/ℓ_{s N})³ + 1`, `Mg = mgDrift B ζ N`
(`≤ 2752 N^{κ+3ζ}` eventually, `mgDrift_le`), `T_u(b) = tT B E N D u (zdist (b 0 - b 1))`, the left
side written as in `Dgrid` (`List.ofFn b`; see `Dgrid_eq_drift`).

Inputs: the good-event bounds `jSMat(M) ≤ Λ(u)` and `jGMat(M) ≤ N^{2ε} Λ(u)` (T1513); T1501's
per-matrix inputs `h273`, `h557C/R`, `hone`/`hκ` at the rescaled scale `ℓ_s' = ℓ_{s N}/(4N^ζ)`;
the scalar facts `|E| < 2`, `1 ≤ N`, `0 ≤ s N ≤ u < 1`, `0 ≤ δ`, `0 ≤ ε`, `2ε ≤ δ`, `0 ≤ ζ`,
`D ≥ 8 + 2ζ`, `W ≥ 8`, `L ≤ W`, `N ≤ W²`, `2D² ≤ log W`, `N^{2ε} Λ(u) ≤ A_u`, `hDreg` (all of
which hold eventually, uniformly in `u ∈ [s N, t N]`, under step2's `hreg`:
`drift_point_le_heG_scalars`). `h554` is **not** an input: every Hermitian `M` satisfies it with
T1513's `ρ = rho554(jGMat M)` (`mem_h554Set_of_isHermitian`), and
`ρ ≤ rho554(N^{2ε}Λ) ≤ 2 η_u⁻¹ N^{2ε}Λ W^{-D}` (`rho554_mono`, `rho554_le_two_mul_rpow`), which
`resCoef_le` absorbs at the same `D`. `J := N^{2ε} Λ(u)`. -/
theorem drift_point_le_heG {E : ℝ} (hE : |E| < 2) {s : ℕ → ℝ} {δ ε ζ D : ℝ} {N : ℕ} {u : ℝ}
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (hN1 : (1 : ℝ) ≤ N) (hs0 : 0 ≤ s N) (hsu : s N ≤ u) (hu1 : u < 1)
    (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε) (hεδ : 2 * ε ≤ δ) (hζ0 : 0 ≤ ζ) (hD : 8 + 2 * ζ ≤ D)
    (hW8 : 8 ≤ (B.W N : ℝ)) (hLW : (B.L N : ℝ) ≤ B.W N) (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hlog : 2 * D ^ 2 ≤ Real.log (B.W N : ℝ))
    (hJA : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ≤ B.scale E N u)
    (hDreg : (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D)) ≤ B.ell N u * (B.scale E N u)⁻¹)
    {κ : ℝ}
    (h273 : ∀ x y c : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖
        ≤ (B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))) ^ 2 * ((B.scale E N u) ^ 2)⁻¹)
    (h557C : ∀ (x y : ZMod (B.L N)) (p : B.Idx N), p.1 = y →
      ∑ r : B.Idx N, Lemma57.blkW (B.L N) (B.W N) r x * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))) * (√(B.scale E N u))⁻¹)
    (h557R : ∀ (x y : ZMod (B.L N)) (r : B.Idx N), r.1 = x →
      ∑ p : B.Idx N, Lemma57.blkW (B.L N) (B.W N) p y * ‖green M (zt E u) r p‖ ≤
        √(B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))) * (√(B.scale E N u))⁻¹)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M (zt E u) σ
        - mSigma E σ • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) b)‖
      ≤ κ * (B.scale E N u)⁻¹)
    (hκ : 2 * κ ≤ B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)))
    (hjS : jSMat B.toDims E D N u M ≤ Step2.thr E s δ N u)
    (hjG : jGMat B.toDims E N u (B.ell N u) (etaT E u) D M
      ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) :
    ∀ b : LoopArg (B.L N) 2,
      ‖RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
            (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))‖
        ≤ (exp 1 * Step2.thr E s δ N u ^ 2 *
              (36 * ((etaT E u)⁻¹ * (B.scale E N u)⁻¹)
                + (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D))
            + mgDrift B ζ N * (etaT E u)⁻¹ *
              (((4 * (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N))) ^ 3 + 1)
                + (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 3) * Step2.thr E s δ N u ^ 3))
          * Step2.tT B E N D u (zdist (B.L N) (b 0 - b 1)) := by
  intro b
  have hofn : List.ofFn b = [b 0, b 1] := by simp [List.ofFn_succ]
  rw [hofn]
  -- scalar facts
  have hW1 : (1 : ℝ) ≤ B.W N := by linarith
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hs1 : s N < 1 := lt_of_le_of_lt hsu hu1
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have hη0 : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hη1 : etaT E u ≤ 1 := by
    rw [Step2.etaT_eq]
    calc (1 - u) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
      _ = 1 := one_mul 1
  have hℓu1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have hℓu0 : 0 < B.ell N u := by linarith
  have hℓs1 : 1 ≤ B.ell N (s N) := one_le_ellHat_of_nonneg (B.one_le_L N) hs0 hs1
  have hℓs0 : 0 < B.ell N (s N) := by linarith
  have hℓsu : B.ell N (s N) ≤ B.ell N u := Step3.ellHat_mono hsu hu1
  have hNz : 1 ≤ (N : ℝ) ^ ζ := Real.one_le_rpow hN1 hζ0
  have hg1 : 1 ≤ 4 * (N : ℝ) ^ ζ := by linarith
  have hg0 : 0 < 4 * (N : ℝ) ^ ζ := by linarith
  have hℓs'0 : 0 < B.ell N (s N) / (4 * (N : ℝ) ^ ζ) := div_pos hℓs0 hg0
  have hrr : B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ))
      = 4 * (N : ℝ) ^ ζ * (B.ell N u / B.ell N (s N)) := by
    field_simp
  have hr01 : 1 ≤ B.ell N u / B.ell N (s N) := by rw [le_div_iff₀ hℓs0]; linarith
  have hr : 1 ≤ B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) := by
    rw [hrr]; exact one_le_mul_of_one_le_of_one_le hg1 hr01
  -- `J := N^{2ε} Λ(u)`
  have hR1 : 1 ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ (by linarith)]; linarith
  have hy1 : 1 ≤ (N : ℝ) ^ (2 * ε) := Real.one_le_rpow hN1 (by linarith)
  have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ0
  have hΛ1 : 1 ≤ Step2.thr E s δ N u := by
    unfold Step2.thr
    exact one_le_mul_of_one_le_of_one_le hx1 (one_le_pow₀ hR1)
  have hJ1 : 1 ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u :=
    one_le_mul_of_one_le_of_one_le hy1 hΛ1
  have hJ0 : 0 ≤ (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u := by linarith
  have hA : 1 ≤ B.scale E N u := hJ1.trans hJA
  -- the `jGMat` corollary with `J := N^{2ε} Λ(u)`
  have h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
          ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) *
            tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y)) := by
    intro x y hxy
    exact (two_loop_re_le_jGMat (ηu := etaT E u) (D := D) hM x y hxy).trans
      (mul_le_mul_of_nonneg_right hjG (tailT_nonneg hW0.le _))
  have h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        gmBlkM B N M (zt E u) x y ≤ √((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) *
          √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (x - y))) := by
    intro x y hxy
    refine (gmBlkM_le_sqrt_jGMat (ηu := etaT E u) (D := D) hM x y hxy).trans ?_
    rw [← Real.sqrt_mul hJ0]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hjG (tailT_nonneg hW0.le _))
  -- `h554`, deterministically, with T1513's `ρ`
  have hlogW1 : 1 ≤ Real.log (B.W N : ℝ) := by
    rw [Real.le_log_iff_exp_le hW0]
    have := Real.exp_one_lt_d9
    linarith
  have h554set := mem_h554Set_of_isHermitian (d := B.toDims) (D := D) hE N hu1 hℓu0 hlogW1
    (M := M) hM
  have h554 : ∀ x y c : ZMod (B.L N),
      Lemma57.ellStarStar (B.W N : ℝ) (B.ell N u) < (zdist (B.L N) (y - c) : ℝ) →
        ‖gloop (B.L N) (B.W N) M (zt E u) ⟨[false, true, true], [y, c, x]⟩‖ ≤
          rho554 B.toDims E N u D (jGMat B.toDims E N u (B.ell N u) (etaT E u) D M) :=
    fun x y c h => h554set hM x y c h
  have hjG1 : 1 ≤ jGMat B.toDims E N u (B.ell N u) (etaT E u) D M := one_le_jGMat' E N u M
  have hρ0 : 0 ≤ rho554 B.toDims E N u D (jGMat B.toDims E N u (B.ell N u) (etaT E u) D M) := by
    unfold rho554
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hη0.le) (by linarith)) (Real.sqrt_nonneg _)
  have hρ : rho554 B.toDims E N u D (jGMat B.toDims E N u (B.ell N u) (etaT E u) D M) ≤
      2 * (etaT E u)⁻¹ * ((N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u) * (B.W N : ℝ) ^ (-D) :=
    (rho554_mono B.toDims E N u D hη0 hjG).trans
      (rho554_le_two_mul_rpow B.toDims E N hη0 hℓu0 hA hlog hJ0)
  -- (T3') at `ℓ_s'`
  have hmain := drift_point_le_blk' (s := s) (δ := δ) (D := D)
    (ℓs := B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) hM hL3 hW1 hℓu1 hℓs'0 hη0 hA hr hDreg hJ1 hρ0
    h273 h554 h531 h42 h557C h557R hone hκ hjS b
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (tailT_nonneg hW0.le _))
  -- the coefficient
  have hJW : (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ≤ B.W N :=
    hJA.trans (scale_le_W B hE N hu0 hu1)
  have hℓL : B.ell N u ≤ (B.L N : ℝ) := min_le_right _ _
  have hrg : B.ell N u / (B.ell N (s N) / (4 * (N : ℝ) ^ ζ)) ≤ 4 * (N : ℝ) ^ ζ * B.ell N u := by
    rw [hrr]
    exact mul_le_mul_of_nonneg_left (div_le_self hℓu0.le hℓs1) hg0.le
  have hgW : 4 * (N : ℝ) ^ ζ ≤ 4 * (B.W N : ℝ) ^ (2 * ζ) := by
    have := natCast_rpow_le_W_rpow (Nat.cast_nonneg N) hNW hζ0 hW0.le
    linarith
  have hres := resCoef_le (Lr := (B.L N : ℝ)) hW8 hℓu0 hℓs'0 hη0 hη1 hρ hJ0 hJW hℓL hLW hrg
    hgW hD
  have hr0R : (B.ell N u / B.ell N (s N)) ^ 2 ≤ etaT E (s N) / etaT E u := by
    have hK := ell_mul_sqrt_le B N hu1 hsu
    have ha : 0 < 1 - u := by linarith
    have hc : 0 < 1 - s N := by linarith
    have hsq := pow_le_pow_left₀ (by positivity) hK 2
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hc.le] at hsq
    rw [Step2.etaT_ratio hE, div_pow, div_le_div_iff₀ (by positivity) ha]
    nlinarith
  have hyx : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 hεδ
  have key := heG_coef_le (η := etaT E u) (A := (B.W N : ℝ) * B.ell N u * etaT E u)
    (cNw := Lemma57.cNear (B.W N : ℝ) (B.ell N u)) (cFw := Lemma57.cFar (B.W N : ℝ) (B.ell N u))
    (cN := Lemma57.cNear (B.W N : ℝ) 1) (cF := Lemma57.cFar (B.W N : ℝ) 1)
    (R := etaT E (s N) / etaT E u) (x := (N : ℝ) ^ δ) (y := (N : ℝ) ^ (2 * ε))
    (Λ := Step2.thr E s δ N u) hη0 hA (Lemma57.cNear_nonneg hW1 hℓu0) (cNear_le_one hℓu1)
    (Lemma57.cFar_nonneg hW1 hℓu0) (cFar_le_one hℓu1) hg1 hrr hr01 hr0R hx1 rfl hy1 hyx hres
  have hsc : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  rw [hsc]
  unfold mdr' mgDrift
  linarith [key]

/-- `Dgrid` (T1516) unfolds to the left side of (T5) at `M := H_j ω`, `u := u_j` (definitional),
so T1518 (T1)'s `hdrift` is (T5) at `M := H B.toDims s t K N j ω` (Hermitian by
`H_isHermitian`). -/
theorem Dgrid_eq_drift (B : Band Ω) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (ω : Ωg B.toDims) (b : LoopArg (B.L N) 2) :
    Dgrid B E s t K N j ω b =
      RBM.Gauss.eGterm (B.L N) (B.W N) (mSigma E) (H B.toDims s t K N j ω) (zt E (time s t K N j))
          (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) (H B.toDims s t K N j ω) (zt E (time s t K N j))
              - B.Kval E N (time s t K N j))
            (gloop (B.L N) (B.W N) (H B.toDims s t K N j ω) (zt E (time s t K N j))
              - B.Kval E N (time s t K N j))
            (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N))) := rfl

/-- **Satisfiability of the scalar premises of (T5).** Under step2's `hreg` at `t` (gain `c`),
`0 ≤ δ ≤ c/24`, `2ε ≤ δ`, `D ≥ 4`: eventually in `N`, `1 ≤ N`, `W ≥ 8`, `L ≤ W`, `N ≤ W²`,
`2D² ≤ log W`, and, uniformly in `u ∈ [s N, t N]`, `N^{2ε} thr(u) ≤ A_u` and
`L √(W^{-D}) ≤ ℓ_u A_u⁻¹`. (With `0 ≤ ζ`, `D ≥ 8 + 2ζ` a fixed choice, e.g. `D = 60`, `ζ ≤ 26`,
these are all the scalar premises of `drift_point_le_heG`.) -/
theorem drift_point_le_heG_scalars (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hreg : ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤ B.scale E N (t N))
    {δ ε D : ℝ} (hδ0 : 0 ≤ δ) (hδc : δ ≤ c / 24) (hεδ : 2 * ε ≤ δ) (hD : 4 ≤ D) :
    ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ N ∧ 8 ≤ (B.W N : ℝ) ∧ (B.L N : ℝ) ≤ B.W N ∧
      (N : ℝ) ≤ (B.W N : ℝ) ^ 2 ∧ 2 * D ^ 2 ≤ Real.log (B.W N : ℝ) ∧
      ∀ u : ℝ, s N ≤ u → u ≤ t N →
        (N : ℝ) ^ (2 * ε) * Step2.thr E s δ N u ≤ B.scale E N u ∧
        (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D)) ≤ B.ell N u * (B.scale E N u)⁻¹ := by
  filter_upwards [Filter.eventually_ge_atTop 1, (Step2.tendsto_W B).eventually_ge_atTop 8,
    B.dim, Step2.eventually_le_W_sq B,
    (Real.tendsto_log_atTop.comp (Step2.tendsto_W B)).eventually_ge_atTop (2 * D ^ 2), hreg]
    with N hN1 hW8 hdim hNW hlog hregN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by linarith
  have hLW : (B.L N : ℝ) ≤ B.W N := by
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N := by exact_mod_cast hdim.1
    nlinarith
  refine ⟨hN1', hW8, hLW, hNW, hlog, fun u hsu hut => ?_⟩
  have hu1 : u < 1 := lt_of_le_of_lt hut (ht1 N)
  have hu0 : 0 ≤ u := (hs0 N).trans hsu
  have hs1 : s N < 1 := lt_of_le_of_lt hsu hu1
  have hm0 : 0 < (mE E).im := mE_im_pos hE
  have hm1 : (mE E).im ≤ 1 := mE_im_le_one hE
  have ha : 0 < 1 - u := by linarith
  have ht0 : 0 < 1 - t N := by linarith [ht1 N]
  have hc0 : 0 < 1 - s N := by linarith
  refine ⟨?_, ?_⟩
  · -- `N^{2ε} thr(u) ≤ x² R_u⁴ ≤ x^{24} R_t^{30} ≤ A_t ≤ A_u`
    have hx1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1' hδ0
    have hNε : (N : ℝ) ^ (2 * ε) ≤ (N : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le hN1' hεδ
    have hx24 : ((N : ℝ) ^ δ) ^ 24 ≤ (N : ℝ) ^ c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le hN1' (by push_cast; linarith)
    have hRu : etaT E (s N) / etaT E u = (1 - s N) / (1 - u) := Step2.etaT_ratio hE _ _
    have hRt : etaT E (s N) / etaT E (t N) = (1 - s N) / (1 - t N) := Step2.etaT_ratio hE _ _
    have hRu1 : 1 ≤ (1 - s N) / (1 - u) := by rw [le_div_iff₀ ha]; linarith
    have hRut : (1 - s N) / (1 - u) ≤ (1 - s N) / (1 - t N) :=
      div_le_div_of_nonneg_left hc0.le ht0 (by linarith)
    have hRt1 : 1 ≤ (1 - s N) / (1 - t N) := hRu1.trans hRut
    have hscale : B.scale E N (t N) ≤ B.scale E N u :=
      flowScale_antitoneOn hW0.le (B.L N) E (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) hut
    unfold Step2.thr
    rw [hRu]
    calc (N : ℝ) ^ (2 * ε) * ((N : ℝ) ^ δ * ((1 - s N) / (1 - u)) ^ 4)
        ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * ((1 - s N) / (1 - u)) ^ 4) :=
          mul_le_mul_of_nonneg_right hNε (by positivity)
      _ = ((N : ℝ) ^ δ) ^ 2 * ((1 - s N) / (1 - u)) ^ 4 := by ring
      _ ≤ ((N : ℝ) ^ δ) ^ 24 * ((1 - s N) / (1 - t N)) ^ 30 :=
          mul_le_mul (pow_le_pow_right₀ hx1 (by norm_num))
            ((pow_le_pow_left₀ (by positivity) hRut 4).trans
              (pow_le_pow_right₀ hRt1 (by norm_num))) (by positivity) (by positivity)
      _ ≤ (N : ℝ) ^ c * ((1 - s N) / (1 - t N)) ^ 30 :=
          mul_le_mul_of_nonneg_right hx24 (by positivity)
      _ = (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 := by rw [hRt]
      _ ≤ B.scale E N (t N) := hregN
      _ ≤ B.scale E N u := hscale
  · -- `L √(W^{-D}) ≤ L W^{-2} ≤ W⁻¹ ≤ (W η_u)⁻¹ = ℓ_u A_u⁻¹`
    have hℓ1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
    have hℓ0 : 0 < B.ell N u := by linarith
    have hη0 : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
    have hη1 : etaT E u ≤ 1 := by
      rw [Step2.etaT_eq]
      calc (1 - u) * (mE E).im ≤ 1 * 1 := mul_le_mul (by linarith) hm1 hm0.le zero_le_one
        _ = 1 := one_mul 1
    have hWD : (B.W N : ℝ) ^ (-D) ≤ ((B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2)⁻¹ := by
      calc (B.W N : ℝ) ^ (-D) ≤ (B.W N : ℝ) ^ (-(4 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = ((B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2)⁻¹ := by
            rw [Real.rpow_neg hW0.le, ← pow_add]; norm_cast
    have hsq : √((B.W N : ℝ) ^ (-D)) ≤ ((B.W N : ℝ) ^ 2)⁻¹ := by
      calc √((B.W N : ℝ) ^ (-D)) ≤ √(((B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ 2)⁻¹) :=
            Real.sqrt_le_sqrt hWD
        _ = ((B.W N : ℝ) ^ 2)⁻¹ := by
            rw [Real.sqrt_inv, Real.sqrt_mul_self (by positivity)]
    have hrhs : B.ell N u * (B.scale E N u)⁻¹ = ((B.W N : ℝ) * etaT E u)⁻¹ := by
      change B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ = ((B.W N : ℝ) * etaT E u)⁻¹
      field_simp
    rw [hrhs]
    calc (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D)) ≤ (B.W N : ℝ) * ((B.W N : ℝ) ^ 2)⁻¹ :=
          mul_le_mul hLW hsq (Real.sqrt_nonneg _) hW0.le
      _ = ((B.W N : ℝ) * 1)⁻¹ := by field_simp
      _ ≤ ((B.W N : ℝ) * etaT E u)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact mul_le_mul_of_nonneg_left hη1 hW0.le

end RBM.Gauss.Grid
