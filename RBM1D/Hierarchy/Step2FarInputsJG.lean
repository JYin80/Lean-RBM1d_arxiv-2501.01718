/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeDriftNearTriple

/-!
# T1501: (5.35) far-field bound without `h560` (T1499 Option B)

`docs/reports/T1499-prove.md` shows that the hypothesis `h560` of
`RBM.Step2FarInputs.eGpm_le_rhs535_of_jS` / `RBM.Step2FarInputs.h535_of_jS` is not satisfiable in
the regime those theorems are meant to be used in.  This file supplies the paper's actual
(5.60)→(5.61) route instead: bound the triple loop by its three actual block maxima first
(deterministic, every `b`, no hypothesis), then invoke the block-level two-loop bound only on
far pairs.  This is `RBM.Step2FarInputs.eGpm_le_rhs535` instantiated with
`J := RBM.APrimeJG.jG` and `Gm := RBM.APrimeJG.gmBlk`.

The two ingredients (the (5.60) triple-loop bound by block maxima, and the (4.2)-type bound of
the `(+,-)` two-loop by the block square) are proved here for **arbitrary `B : Band Ω`**, from
sublemmas that are already generic in `Band Ω` (`RBM.APrimeJG.norm_Gsig_le_gmBlk`,
`RBM.APrimeJG.gmBlk_nonneg`, `RBM.APrimeJG.gmBlk_mul_swap_le_gsqBlk`,
`RBM.APrimeDriftNearTriple.gmBlk_comm`, `RBM.Lemma57.norm_gloop_three_le`,
`RBM.Lemma57.sum_blkW_normSq`) or have no `Dims`/`Band` dependence at all
(`RBM.Lemma57.norm_gloop_three_le`).  The only *committed, named* declarations with this content
(`RBM.APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk`,
`RBM.APrimeFirstCellEGFar.two_loop_re_le_gsqBlk`) are scoped to `Dims.exampleGrow`
(file-local `abbrev B`), so they are not reused here; see `docs/reports/T1501-prove.md` §Step 0.
-/

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.60), block-resolved, for arbitrary `Band Ω`.**  The actual `(-,+,+)` triple loop is
bounded by its three block maxima, deterministically, for every `b`.  This is the content of
`RBM.APrimeFirstCellEGFar.norm_gloop_three_le_gmBlk`, reproved here for a bound `B : Band Ω`
(that declaration is scoped to `Dims.exampleGrow`); the proof is identical, using only
declarations already generic in `Band Ω`. -/
private theorem norm_gloop_three_le_gmBlk' (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω) (a₁ a₂ b : ZMod (B.L N)) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      APrimeJG.gmBlk X E N u ω a₂ b *
        APrimeJG.gmBlk X E N u ω a₁ b *
          APrimeJG.gmBlk X E N u ω a₂ a₁ := by
  letI : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  letI : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  have h := Lemma57.norm_gloop_three_le (L := B.L N) (Wb := B.W N)
    (H := X.H N u ω) (z := zt E u) false true true a₂ b a₁
    (APrimeJG.gmBlk_nonneg X E N u ω)
    (by
      intro p q hp hq
      rcases p with ⟨px, pi⟩
      rcases q with ⟨qy, qi⟩
      dsimp at hp hq ⊢
      subst px
      subst qy
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω false a₁ a₂ pi qi)
    (by
      intro q r hq hr
      rcases q with ⟨qx, qi⟩
      rcases r with ⟨ry, ri⟩
      dsimp at hq hr ⊢
      subst qx
      subst ry
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω true a₂ b qi ri)
    (by
      intro r p hr hp
      rcases r with ⟨rx, ri⟩
      rcases p with ⟨py, pi⟩
      dsimp at hr hp ⊢
      subst rx
      subst py
      exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω true b a₁ ri pi)
  rw [APrimeDriftNearTriple.gmBlk_comm X E N u ω b a₁,
    APrimeDriftNearTriple.gmBlk_comm X E N u ω a₁ a₂] at h
  convert h using 1 <;> ring

/-- **The `(+,-)` two-loop is bounded by the block square, for arbitrary `Band Ω`.**  This is
the content of `RBM.APrimeFirstCellEGFar.two_loop_re_le_gsqBlk`, reproved here for a bound
`B : Band Ω` (that declaration is scoped to `Dims.exampleGrow`); the proof is identical, using
only declarations already generic in `Band Ω`. -/
private theorem two_loop_re_le_gsqBlk' (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω) (x y : ZMod (B.L N)) :
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[true, false], [x, y]⟩).re ≤ APrimeJG.gsqBlk X E N u ω x y := by
  letI : NeZero (B.L N) := ⟨by have := B.three_le_L N; omega⟩
  letI : NeZero (B.W N) := ⟨by have := B.W_pos N; omega⟩
  let M : ℝ := APrimeJG.gmBlk X E N u ω x y
  have hM : 0 ≤ M := APrimeJG.gmBlk_nonneg X E N u ω x y
  have hterm (p q : ZMod (B.L N) × Fin (B.W N)) :
      Lemma57.blkW (B.L N) (B.W N) p y *
          (Lemma57.blkW (B.L N) (B.W N) q x *
            ‖green (X.H N u ω) (zt E u) p q‖ ^ 2) ≤
      Lemma57.blkW (B.L N) (B.W N) p y *
          (Lemma57.blkW (B.L N) (B.W N) q x * M ^ 2) := by
    by_cases hp : p.1 = y
    · by_cases hq : q.1 = x
      · have hentry : ‖green (X.H N u ω) (zt E u) p q‖ ≤ M := by
          rcases p with ⟨px, pi⟩
          rcases q with ⟨qx, qi⟩
          dsimp at hp hq ⊢
          subst px
          subst qx
          have h := APrimeJG.norm_Gsig_le_gmBlk X E N u ω true y x pi qi
          rw [Gsig_true] at h
          rw [APrimeDriftNearTriple.gmBlk_comm X E N u ω y x] at h
          exact h
        have hsq : ‖green (X.H N u ω) (zt E u) p q‖ ^ 2 ≤ M ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hentry 2
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq
            (Lemma57.blkW_nonneg (B.L N) (B.W N) q x))
          (Lemma57.blkW_nonneg (B.L N) (B.W N) p y)
      · simp only [Lemma57.blkW, if_neg hq, zero_mul, mul_zero]
        exact le_rfl
    · simp only [Lemma57.blkW, if_neg hp, zero_mul]
      exact le_rfl
  calc
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[true, false], [x, y]⟩).re =
        ∑ p : ZMod (B.L N) × Fin (B.W N),
          ∑ q : ZMod (B.L N) × Fin (B.W N),
            Lemma57.blkW (B.L N) (B.W N) p y *
              (Lemma57.blkW (B.L N) (B.W N) q x *
                ‖green (X.H N u ω) (zt E u) p q‖ ^ 2) :=
      (Lemma57.sum_blkW_normSq (B.L N) (B.W N)
        (X.hermitian N u ω) x y).symm
    _ ≤ ∑ p : ZMod (B.L N) × Fin (B.W N),
          ∑ q : ZMod (B.L N) × Fin (B.W N),
            Lemma57.blkW (B.L N) (B.W N) p y *
              (Lemma57.blkW (B.L N) (B.W N) q x * M ^ 2) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = M ^ 2 := by
      have hinner (p : ZMod (B.L N) × Fin (B.W N)) :
          (∑ q : ZMod (B.L N) × Fin (B.W N),
              Lemma57.blkW (B.L N) (B.W N) p y *
                (Lemma57.blkW (B.L N) (B.W N) q x * M ^ 2)) =
            Lemma57.blkW (B.L N) (B.W N) p y * M ^ 2 := by
        rw [← Finset.mul_sum, ← Finset.sum_mul,
          Lemma57.sum_blkW, one_mul]
      simp_rw [hinner, ← Finset.sum_mul, Lemma57.sum_blkW, one_mul]
    _ ≤ APrimeJG.gsqBlk X E N u ω x y := by
      have hcomm : M = APrimeJG.gmBlk X E N u ω y x :=
        APrimeDriftNearTriple.gmBlk_comm X E N u ω x y
      rw [show M ^ 2 = APrimeJG.gmBlk X E N u ω x y *
        APrimeJG.gmBlk X E N u ω y x from by
          change M ^ 2 = M * APrimeJG.gmBlk X E N u ω y x
          rw [← hcomm]
          ring]
      exact APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω x y

/-! ### (T1) (5.35), shape 2, with `J := RBM.APrimeJG.jG` — the `h560`-free route -/

/-- **(5.35), shape 2, with `J := RBM.APrimeJG.jG`.**  `RBM.Step2FarInputs.eGpm_le_rhs535`
verbatim, exactly like `RBM.Step2FarInputs.eGpm_le_rhs535_of_jS`, except that its two
`J`-hypotheses `h531`/`h42` and the (5.60) hypothesis `h560` are no longer assumed: `h560` is
`norm_gloop_three_le_gmBlk'` above (the paper's (5.60), an actual, deterministic entrywise
bound, true for every `b`, not only far ones), `h531` is `two_loop_re_le_gsqBlk'` composed with
`RBM.APrimeJG.gsqBlk_le_jG_mul_tailT` (the paper's (4.2)+(5.31), used only on far pairs), and
`h42` is `RBM.APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail`.  There is no `hK` (the far-field
bound on `K`): `jG`/`gmBlk` never see `K`, only the actual Green function.  This is precisely the
paper's (5.60)→(5.61) route, entries first, then (4.2)/(5.31) only on far pairs — the
replacement `docs/reports/T1499-prove.md` "Option B" for the unsatisfiable
`RBM.Step2FarInputs.eGpm_le_rhs535_of_jS`. -/
theorem eGpm_le_rhs535_of_jG (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}
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
      ≤ rhs535 (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) ℓs (etaT E u) D'
          (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D') ρ
          (zdist (B.L N) (a₁ - a₂)) := by
  have hWpos : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ1 : 1 ≤ APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D' :=
    APrimeJG.one_le_jG X E N u ω hWpos
  have hJnonneg : 0 ≤ APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D' := hJ1.trans' (by norm_num)
  have h531 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[true, false], [x, y]⟩).re ≤
        APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D' *
          tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' (zdist (B.L N) (x - y)) := by
    intro x y hxy
    exact (two_loop_re_le_gsqBlk' X E N u ω x y).trans
      (APrimeJG.gsqBlk_le_jG_mul_tailT X E N u ω hWpos x y hxy)
  have h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      APrimeJG.gmBlk X E N u ω x y ≤
        √(APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D') *
          √(tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' (zdist (B.L N) (x - y))) := by
    intro x y hxy
    exact (APrimeDriftNearTriple.gmBlk_le_sqrt_jG_tail X E N u ω x y hxy).trans_eq
      (Real.sqrt_mul hJnonneg _)
  exact eGpm_le_rhs535 (X.hermitian N u ω) hL hW hℓu hℓs hηu hJ1 hA hr hD a₁ a₂ hρ
    (APrimeJG.gmBlk_nonneg X E N u ω) h273 h554 h531 h42 h557C h557R
    (fun b => norm_gloop_three_le_gmBlk' X E N u ω a₁ a₂ b) (mSigma E) hone hκ

/-! ### (T2, optional) scaling `rhs535` in `J` -/

/-- **`rhs535` scales at most like `c^3` under `J ↦ c^2 J`, for `c ≥ 1`.**  The near/indicator
term and the `ρ`-remainder do not mention `J` (degree `0` in `J`, absorbed by `1 ≤ c^3`); the
`cFar` term is degree `1` in `J` (absorbed by `c^2 ≤ c^3`, after `√(c^2 J) = c * √J`); the `169`
term is degree `3/2` in `J` (`(c^2J) * √(c^2J) = c^3 * (J * √J)`, matched with equality). This is
the analogue of `RBM.rhs535_div_le` (T1496), scaling `J` instead of `ℓs`. -/
theorem rhs535_mul_J_le {Wr Lr ℓu ℓs ηu D J ρ d c : ℝ}
    (hc : 1 ≤ c) (hW : 1 ≤ Wr) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu)
    (hJ0 : 0 ≤ J) (hρ0 : 0 ≤ ρ) (hLr0 : 0 ≤ Lr) (_hd0 : 0 ≤ d) :
    rhs535 Wr Lr ℓu ℓs ηu D (c ^ 2 * J) ρ d
      ≤ c ^ 3 * rhs535 Wr Lr ℓu ℓs ηu D J ρ d := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hWpos : (0 : ℝ) < Wr := lt_of_lt_of_le one_pos hW
  have hA0 : (0 : ℝ) < Wr * ℓu * ηu := by positivity
  have hr0 : (0 : ℝ) ≤ ℓu / ℓs := div_nonneg hℓu.le hℓs.le
  have hcN : 0 ≤ Lemma57.cNear Wr ℓu := Lemma57.cNear_nonneg hW hℓu
  have hcF : 0 ≤ Lemma57.cFar Wr ℓu := Lemma57.cFar_nonneg hW hℓu
  have htail : 0 ≤ tailT Wr ℓu ηu D d := tailT_nonneg hWpos.le d
  have hηi : (0 : ℝ) ≤ ηu⁻¹ := by positivity
  have hAiInv : (0 : ℝ) ≤ (√(Wr * ℓu * ηu))⁻¹ := by positivity
  have hAinv : (0 : ℝ) ≤ (Wr * ℓu * ηu)⁻¹ := by positivity
  have hc1 : (1:ℝ) ≤ c ^ 2 := by nlinarith
  have hc1' : (1:ℝ) ≤ c ^ 3 := by nlinarith [sq_nonneg (c - 1), hcpos.le]
  have hc2le3 : c ^ 2 ≤ c ^ 3 := by nlinarith [sq_nonneg (c - 1), hcpos.le, hc]
  have hsqrtJ : √(c ^ 2 * J) = c * √J := by
    rw [Real.sqrt_mul (by positivity) J, show √(c^2) = c from by
      rw [show c^2 = c*c from by ring, Real.sqrt_mul_self hcpos.le]]
  rw [Step2FarInputs.rhs535, Step2FarInputs.rhs535, hsqrtJ]
  set r : ℝ := ℓu / ℓs with hrdef
  set A : ℝ := Wr * ℓu * ηu with hAdef
  set ind : ℝ := (if d ≤ ellStar Wr ℓu then (1 : ℝ) else 0) with hinddef
  have hind0 : (0:ℝ) ≤ ind := by rw [hinddef]; split_ifs <;> norm_num
  have e1 : Lemma57.cNear Wr ℓu * r ^ 3 * ind
      ≤ c ^ 3 * (Lemma57.cNear Wr ℓu * r ^ 3 * ind) := by
    have hfac : (0:ℝ) ≤ Lemma57.cNear Wr ℓu * r ^ 3 * ind :=
      mul_nonneg (mul_nonneg hcN (by positivity)) hind0
    nlinarith [mul_le_mul_of_nonneg_right hc1' hfac]
  have e2 : Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * (c ^ 2 * J))
      ≤ c ^ 3 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J)) := by
    have hfac : (0 : ℝ) ≤ Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J) :=
      mul_nonneg hcF
        (mul_nonneg (mul_nonneg (mul_nonneg hr0 (Real.sqrt_nonneg r)) hAiInv) hJ0)
    have hcomm : Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * (c ^ 2 * J))
        = c ^ 2 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J)) := by ring
    rw [hcomm]
    exact mul_le_mul_of_nonneg_right hc2le3 hfac
  have e3 : 169 * (r * A⁻¹ * ((c ^ 2 * J) * (c * √J)))
      = c ^ 3 * (169 * (r * A⁻¹ * (J * √J))) := by ring
  have hsum : Lemma57.cNear Wr ℓu * r ^ 3 * ind
        + Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * (c ^ 2 * J))
        + 169 * (r * A⁻¹ * ((c ^ 2 * J) * (c * √J)))
      ≤ c ^ 3 * (Lemma57.cNear Wr ℓu * r ^ 3 * ind)
          + c ^ 3 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J))
          + c ^ 3 * (169 * (r * A⁻¹ * (J * √J))) := by
    rw [e3]; linarith [e1, e2]
  have hmul : ηu⁻¹ * (Lemma57.cNear Wr ℓu * r ^ 3 * ind
          + Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * (c ^ 2 * J))
          + 169 * (r * A⁻¹ * ((c ^ 2 * J) * (c * √J)))) * tailT Wr ℓu ηu D d
      ≤ ηu⁻¹ * (c ^ 3 * (Lemma57.cNear Wr ℓu * r ^ 3 * ind)
          + c ^ 3 * (Lemma57.cFar Wr ℓu * (r * √r * (√A)⁻¹ * J))
          + c ^ 3 * (169 * (r * A⁻¹ * (J * √J)))) * tailT Wr ℓu ηu D d :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hηi) htail
  have e4 : r * (ℓu * ηu)⁻¹ * Lr * ρ ≤ c ^ 3 * (r * (ℓu * ηu)⁻¹ * Lr * ρ) := by
    have hℓηinv : (0 : ℝ) ≤ (ℓu * ηu)⁻¹ := by positivity
    have hfac : (0 : ℝ) ≤ r * (ℓu * ηu)⁻¹ * Lr * ρ :=
      mul_nonneg (mul_nonneg (mul_nonneg hr0 hℓηinv) hLr0) hρ0
    nlinarith [mul_le_mul_of_nonneg_right hc1' hfac]
  have hcomb := add_le_add hmul e4
  refine hcomb.trans_eq ?_
  ring

end Step2FarInputs
end RBM
