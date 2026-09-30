/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.BlockGreen
import RBM1D.Gauss.NearFieldRemainder
import RBM1D.Hierarchy.Step2
import RBM1D.Gauss.GridJStar
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.GridGoodSet
import RBM1D.Gauss.GridExpansion

/-!
# The pointwise drift bound on the good set

## The (5.54) residue on the near band

The paper uses (5.54) only for `|a₁-a₂| ≤ ℓ*_u`, and the far branch of the (5.35) bound
(`Lemma57.eG_far_le`) uses neither the (5.54) input nor `ρ`.  The chain below confines the
residue `κ₁ (ℓ_u η_u)⁻¹ L ρ` to the near band and absorbs it there against
`T_{u,D} ≥ A_u⁻² e^{-(log W)^{3/4}}`:
* `eG_le'`; `eG_le_reduced_of_schwarz'`, `eG_le_reduced'`, `eGpm_le_reduced'`,
  `rhs535'`, `eGpm_le_rhs535'`, `eGpm_le_rhs535_of_jG_mat'`;
* `rhs535'_le_mul_tailT_near` (generic), `DriftPt.resCoef_le` (the absorption arithmetic,
  `D ≥ D₀ = 8 + 2ζ`);
* `mdr'`, `drift_point_le'`, `drift_point_le_blk'`;
* `mgDrift`, `mgDrift_le`.

`RBM.Gauss.Grid.drift_point_le'` bounds the drift `D(M) := (eGterm + primBil(A,A))(M)` of
`RBM.Gauss.Grid.discrete_hierarchy_step`, with `A := gloop(M) − Kval_u` restricted to the
`(+,-)` `2`-loop, against the `T_{u,D}`-normalized profile that the weighted Duhamel sum
needs.  `RBM.Gauss.Grid.drift_point_le_blk'` is the same bound with the concrete block maximum
in place of the free `Gm`, stated with the coefficient function `mdr'`.
`RBM.Gauss.Grid.eGpm_le_rhs535_of_jG_mat'` is (5.35) at matrix level, without a (5.60)
hypothesis.

## Two different `J*`, and the route for (5.60)

* `Step2.jStar` (`RBM1D/Gauss/Step2JStar.lean`) is the genuine `J*` of (5.29):
  `jStar L f W ℓu ηu D = sup_a (f a / T_{u,D}(‖a₁-a₂‖)) + 1`.  `RBM.Gauss.Grid.jSMat` is
  *literally* this formula with the matrix `M` substituted for a `Sample`'s Green function
  (`rfl`).  **This is not** the squared-`G`-pair, far-pairs-only maximum `jG`, which is used
  only inside the `jG`/`gmBlk` machinery of (5.60)-(5.61).  Every threshold hypothesis below is
  stated against `Step2.jStar`/`RBM.Gauss.Grid.jSMat`.
* The route used here needs no (5.60) hypothesis: (5.60) is proved by block maxima,
  deterministically (`DriftPt.norm_gloop_three_le_gmBlkM`), and the far-field two-loop bound is
  only invoked on far pairs.
* `eGpm_le_rhs535_of_jG_mat'` is stated with a **generic `J`** together with the two block
  bounds `h531`/`h42` that `jG` supplies, `h42` on the concrete matrix block maximum
  `DriftPt.gmBlkM`.  `drift_point_le'` takes `J`, `Gm`, `h531`, `h42`, `h560`, `hGm` raw;
  `drift_point_le_blk'` fixes `Gm := gmBlkM`.  The `jGMat` corollaries are
  `DriftPt.two_loop_re_le_jGMat` and `DriftPt.gmBlkM_le_sqrt_jGMat`.
-/

namespace RBM.Gauss.Grid

open Real Finset RBM RBM.Step2FarInputs

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ## (T1) : matrix versions of the two deterministic Sample-level results -/

/-- **Quadratic part, at matrix level.**  The proof
is free of any `Sample`-specific fact — `X.H N u ω` only ever occurs as the argument of `gloop`,
via `Sample.Lval`'s defining equation
`X.Lval E N u ω I = gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) I` (`rfl`) — so the same proof
works for an arbitrary matrix `M`.  No `u = 0`/`H_zero` case split is needed: the identity is an
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

/-! ## EG part at matrix level, without a (5.60) hypothesis

The block maximum `DriftPt.gmBlkM` is `BlockGreen.gmBlk`'s formula with `X.H N u ω`, `zt E u`
replaced by an arbitrary Hermitian matrix `M` and a spectral parameter `z`, and the only sample
fact used, `X.hermitian N u ω`, becomes the hypothesis `M.IsHermitian`; (5.60) is then proved
from the block maxima. -/

namespace DriftPt

/-- **Matrix-level block maximum**: the largest resolvent entry between the blocks `x`, `y`, over
both charges, `max_{σ,p,q} ‖G^σ(M,z)_{(x,p),(y,q)}‖`. -/
noncomputable def gmBlkM (B : Band Ω) (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : ℝ :=
  (Finset.univ : Finset (Bool × Fin (B.W N) × Fin (B.W N))).sup'
    ⟨(true, ⟨0, B.W_pos N⟩, ⟨0, B.W_pos N⟩), Finset.mem_univ _⟩
    (fun q => ‖Gsig M z q.1 (x, q.2.1) (y, q.2.2)‖)

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
    rw [BlockGreen.norm_Gsig_eq_green_or_swap hM, BlockGreen.norm_Gsig_eq_green_or_swap hM]
    cases s <;> rfl
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun q _ => ?_)
    exact (hflip q.1 q.2.1 q.2.2).trans_le (norm_Gsig_le_gmBlkM B N M z (!q.1) y x q.2.2 q.2.1)
  · refine Finset.sup'_le _ _ (fun q _ => ?_)
    have h := hflip (!q.1) q.2.2 q.2.1
    simp only [Bool.not_not] at h
    exact h.symm.trans_le (norm_Gsig_le_gmBlkM B N M z (!q.1) x y q.2.2 q.2.1)

/-- **(5.60) at matrix level**: the `(-,+,+)` triple loop is bounded by its three block maxima,
deterministically, for every `b`. -/
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
(stopped before the neighbour maximum). -/
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

/-! ## (T3) in terms of an explicit coefficient function, with the block maximum -/

/-! ## (T4) : the time sum of the drift bound

The target is `Σ_{j<k} Δ · Mdr(u_j) · ((1 - u_{j+1})/(1 - u_k))² ≤ Cdr · N^κ · (R_{u_k}^e + 1)`,
`R_w = η_s/η_w`, with `Mdr(u_j) = mdr … (u_j) (J_j) (ρ_j)` (T3's coefficient at the grid time with
its own per-time inputs). No monotonicity of `Mdr` in `j` is used. Every `η_{u_j}⁻¹` stays paired
with its own propagator factor (the η-pairing), and `r_{u_j} = ℓ_{u_j}/ℓ_s` stays at its
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

end DriftPt

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

end DriftPt

/-! ## The (5.54) residue confined to the near band -/

/-- **`eG_le'`**: the (5.35) bound of Lemma 5.7 with the (5.54) residue `κ₁ (ℓ_u η_u)⁻¹ L ρ`
multiplied by the near indicator `1(‖a₁-a₂‖ ≤ ℓ*_u)`. Near branch:
exactly `Lemma57.eG_near_le`. Far branch: exactly `Lemma57.eG_far_le` (no `h554`, no `ρ`): the
near term and the residue are both `0` there, as in the paper ((5.54) is used only for
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

/-- **(R2) `eG_le_reduced_of_schwarz'`**: shape 2 of (5.35), proved from `eG_le'`: the residue
`r (ℓ_u η_u)⁻¹ L ρ` carries the near indicator. -/
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

/-- **(R2) `eG_le_reduced'`**: shape 2 of (5.35) for the `3`-loops of `RBM.gloop` ((5.58) proved
by `Lemma57.gloop_h558a'`/`b'`), with the residue carrying the near indicator. -/
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

/-- **(R2) `eGpm_le_reduced'`**: (5.35) for `E^{(G̃)}` itself, shape 2, with the (5.54) residue
carrying the near indicator `1(‖a₂-a₁‖ ≤ ℓ*_u)`. -/
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

/-- **`rhs535'`**: the right-hand side of (5.35), shape 2, with its additive (5.54) term
`ℓu/ℓs · (ℓu ηu)⁻¹ · Lr · ρ` multiplied by the near indicator `1(d ≤ ℓ*_u)`. -/
noncomputable def rhs535' (Wr Lr ℓu ℓs ηu D J ρ d : ℝ) : ℝ :=
  ηu⁻¹ * (Lemma57.cNear Wr ℓu * (ℓu / ℓs) ^ 3 * (if d ≤ ellStar Wr ℓu then 1 else 0)
      + Lemma57.cFar Wr ℓu * (ℓu / ℓs * √(ℓu / ℓs) * (√(Wr * ℓu * ηu))⁻¹ * J)
      + 169 * (ℓu / ℓs * (Wr * ℓu * ηu)⁻¹ * (J * √J)))
    * tailT Wr ℓu ηu D d
  + ℓu / ℓs * (ℓu * ηu)⁻¹ * Lr * ρ * (if d ≤ ellStar Wr ℓu then 1 else 0)

/-- **`eGpm_le_rhs535'`**: (5.35) for `E^{(G̃)}` with the right-hand side `rhs535'` (residue on
the near band only). -/
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
/-- **(R2) `eGpm_le_rhs535_of_jG_mat'`**: (5.35) at matrix level with `rhs535'` (the (5.54)
residue on the near band only); no (5.60) hypothesis and no free `Gm` ((5.60) is
`DriftPt.norm_gloop_three_le_gmBlkM`). -/
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

/-! ## Absorbing the near-band residue into the near term -/

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

/-- **The absorption arithmetic.** The residue coefficient
`c_ρ = r (ℓ_u η_u)⁻¹ L ρ e^{(log W)^{3/4}} A_u²` of `rhs535'_le_mul_tailT_near` is `≤ η_u⁻¹`
under `ρ ≤ 2 η_u⁻¹ J W^{-D}` (`rho554_le_two_mul_rpow`, at the **same** `D`), with
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

/-- **`drift_point_le'`**:
`‖D(M) b‖ ≤ Mdr'(u) · T_{u,D}(b)`, `D(M) := (eGterm + primBil(A,A))(M)` the drift of
`discrete_hierarchy_step`, with the right-hand side `rhs535'` of (5.35).
The hypotheses are a generic `J`, `Gm`, `h560`, `hGm`; no smallness of `ρ`
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

/-! ## The time sum of `Mdr'`, exponent `2`

Every `η_{u_j}⁻¹` stays paired with its own propagator factor, `r_{u_j}` stays at its own time,
and the near term telescopes. The `ρ`-piece:
`c_ρ ≤ η_{u_j}⁻¹` (`DriftPt.resCoef_le`, under `ρ_j ≤ 2 η_{u_j}⁻¹ J_j W^{-D}` and `D ≥ 8 + 2ζ`),
which then pairs like every other `η⁻¹`-piece. A scale factor `g ≥ 1` (`r√(1-w) ≤ g √(1-s)`) covers
the rescaled `ℓ_s' = ℓ_s/(4N^ζ)` (`g = 4N^ζ`); `ℓ_s ≥ 1` is not assumed. -/

namespace DriftPt

/-- `ℓ_w √(1-w) ≤ 1` for `w < 1` (`ℓ_w √(1-w) = min(1, L√(1-w))`). -/
theorem ell_mul_sqrt_le_one (B : Band Ω) (N : ℕ) {w : ℝ} (hw1 : w < 1) :
    B.ell N w * √(1 - w) ≤ 1 := by
  have hsqrt : 0 < √(1 - w) := Real.sqrt_pos.2 (by linarith)
  unfold Band.ell
  rw [ellHat_ofReal _ hw1, min_mul_of_nonneg _ _ hsqrt.le, one_div_mul_cancel hsqrt.ne']
  exact min_le_left _ _

end DriftPt

/-- `N^ζ ≤ W^{2ζ}` from `N ≤ W²`, `ζ ≥ 0`. -/
theorem DriftPt.natCast_rpow_le_W_rpow {N W ζ : ℝ} (hN0 : 0 ≤ N) (hNW : N ≤ W ^ 2)
    (hζ0 : 0 ≤ ζ) (hW0 : 0 ≤ W) : N ^ ζ ≤ W ^ (2 * ζ) := by
  calc N ^ ζ ≤ (W ^ 2) ^ ζ := Real.rpow_le_rpow hN0 hNW hζ0
    _ = W ^ (2 * ζ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0]; norm_num

/-! ## Block maxima for `RBM.Gauss.Grid.jGMat`, and the drift constant `RBM.Gauss.Grid.mgDrift`

The block quantities `gmBlkMat`/`gsqBlkMat` of `GridGoodSet.lean` and their lemmas are `private`, so
`DriftPt.gsqBlkM` below restates `gsqBlkMat`'s body with `DriftPt.gmBlkM`, `DriftPt.jGMat_eq`
identifies `jGMat` with it by `rfl`, and the three short proofs (`gmBlkMat_mul_swap_le_gsqBlkMat`,
`gsqBlkMat_le_jGMat_mul_tailT`, `one_le_jGMat`) are copied. -/

namespace DriftPt

/-- The two-block maximum of `jGMat` (same body as the private `gsqBlkMat`). -/
noncomputable def gsqBlkM (B : Band Ω) (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : ℝ :=
  (Finset.univ : Finset (ZMod (B.L N))).sup' ⟨0, Finset.mem_univ _⟩
    (fun x' => if SB (B.L N) x x' ≠ 0 then gmBlkM B N M z y x' * gmBlkM B N M z x' y else 0)

/-- `jGMat`, unfolded through `gsqBlkM` (definitional). -/
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

/-- `one_le_jGMat`, restated (the original is private). -/
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

/-- `gmBlkMat_mul_swap_le_gsqBlkMat`, restated (the original is private). -/
theorem gmBlkM_mul_swap_le_gsqBlkM (N : ℕ) (M : Matrix (B.Idx N) (B.Idx N) ℂ) (z : ℂ)
    (x y : ZMod (B.L N)) : gmBlkM B N M z x y * gmBlkM B N M z y x ≤ gsqBlkM B N M z x y := by
  unfold gsqBlkM
  have hSB : SB (B.L N) x x ≠ 0 := by simp [SB_apply, sbKernel, sbSupport]
  have h := Finset.le_sup' (s := (Finset.univ : Finset (ZMod (B.L N))))
    (f := fun x' => if SB (B.L N) x x' ≠ 0 then
      gmBlkM B N M z y x' * gmBlkM B N M z x' y else 0)
    (Finset.mem_univ x)
  simpa [hSB, mul_comm] using h

/-- `gsqBlkMat_le_jGMat_mul_tailT`, restated (the original is private). -/
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
`≤ jGMat(M) · T_{u,D}` (the hypothesis `h531` of `eGpm_le_rhs535_of_jG_mat'` with
`J := jGMat`). -/
theorem two_loop_re_le_jGMat {E : ℝ} {N : ℕ} {u : ℝ} {M : Matrix (B.Idx N) (B.Idx N) ℂ}
    (hM : M.IsHermitian) {ℓu ηu D : ℝ} (x y : ZMod (B.L N))
    (hxy : ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ)) :
    (gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], [x, y]⟩).re ≤
      jGMat B.toDims E N u ℓu ηu D M * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
  ((two_loop_re_le_gmBlkM hM (zt E u) x y).trans
    (gmBlkM_mul_swap_le_gsqBlkM N M (zt E u) x y)).trans
    (gsqBlkM_le_jGMat_mul_tailT E N u M x y hxy)

/-- **`jGMat` corollary, (4.2) side**: on far pairs the block maximum of a Hermitian `M` is
`≤ √(jGMat(M) · T_{u,D})` (the hypothesis `h42` of `eGpm_le_rhs535_of_jG_mat'` with
`J := jGMat`). -/
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

end DriftPt

/-- **The explicit drift constant `Mg`**: `Mg = (4N^ζ)² (c_near(W,1) + c_far(W,1) + 170)`,
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

end RBM.Gauss.Grid
