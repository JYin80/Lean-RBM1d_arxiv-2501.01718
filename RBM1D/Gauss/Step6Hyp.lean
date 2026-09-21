/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.IBP
import RBM1D.Gauss.IBPPoly
import RBM1D.Hierarchy.Step6

/-!
# T117: the random-layer hypotheses of Step 6, in the Gaussian model

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8 (pp. 72–73).

`RBM.Step6.sharpExpect_step6` (`RBM1D/Hierarchy/Step6.lean`, T56) is deterministic given seven
random-layer hypotheses, none of which had a producer anywhere in the tree.  This file discharges
the ones that are reachable for the moment-route Gaussian model `RBM.Gauss.sample`
(`RBM1D/Gauss/Model.lean`, T69).

## What is discharged

* **`h527` = (5.127)** — `RBM.Gauss.eq527_gauss`.  This is the main content of the file.  It is
  an **exact identity**, with no error term and no stochastic domination, obtained from
  - the algebraic identity `G - m = m(-H - u m)G` (`RBM.Gauss.green_sub_smul_one_eq`, T83),
  - entrywise Gaussian integration by parts
    (`RBM.Gauss.integral_Hflow_mul_green_diag`, T83, which rests on the *proved*
    `RBM.Gauss.gaussIBP` of T104 — no `GaussIBP` hypothesis is carried), and
  - the **block collapse** `S_{(a,α),(b,β)} = S^{(B)}_{ab}/W`
    (`RBM.Gauss.sum_blkCoef_sum_Sblk`), which is what converts the entrywise display
    `E[(H G)_{pp}] = -u ∑_k S_{pk} E[G_{pp} G_{kk}]` into the *loop* display: a sum of products
    of diagonal entries becomes a sum of products of block averages `⟨G E_a⟩`, because `S`
    does not depend on the offsets inside a block.  The row sum `∑_b S^{(B)}_{ba} = 1` then
    cancels the `m³` terms exactly.
* **`hint2`** — `RBM.Gauss.int2_gauss`, from the deterministic envelope (5.2)
  (`RBM.Gauss.norm_sample_Lval_le`, T76) and continuity of the loop in `ω` on a probability
  space.  No moment estimate is involved.

`hint1` is `RBM.Gauss.integrable_sample_Lval` (T76) and `h5132` is literally
`(hb : RBM.Bounds _ E s).expect`; both were already available and are not restated here.

## What is not discharged, and why

* **`hH` = `RBM.Step6.Hierarchy`** and **`hFD` = `RBM.Step6.FastDecayHyp`**, and with them the
  drift tensors `DLK`, `DG` (which are implicit and *not* determined by the goal, so any
  assembly has to produce them existentially).  `RBM.Step6.Hierarchy` is the *integrated*
  hierarchy (5.20) at loop length `2` after taking expectations, written with the evolution
  kernel `RBM.Uker`; T76's `RBM.Gauss.hasDerivAt_integral_Lval_hierarchy` is a *derivative*
  statement with `RBM.primRhs` on the right and no `K`-subtraction, at a frozen spectral
  parameter.  Getting from one to the other needs the Duhamel representation, the splitting of
  the drift into `E E^{((L-K)×(L-K))} + E E^{(G)}`, and the vanishing of the martingale term —
  i.e. T58's deliverable, in the `RBM.Step6.Hierarchy` shape (a *different* object from
  `RBM.SumZeroDyn.Hierarchy`).
* **`h5133`** and **`hG`** are bounds on `DLK` and `DG`; they cannot even be stated until those
  tensors exist.
* **`hq11`, `hq13`** are `≺`-bounds on the *expectations* `E[(L-K)_1 (L-K)_1]`,
  `E[(L-K)_1 (L-K)_3]`.  They follow from (2.78) (`RBM.Steps.sharpLmK`, Step 4's output, which
  *is* available before Step 6 in the assembly) plus a **first-moment reverse bridge**
  "`|Y| ≺ Φ` and `|Y| ≤ Env(N)` deterministically ⟹ `∫ |Y| ≺ Φ`".  T77's
  `RBM.Gauss.momentDom_of_stochDom` produces even *moments* `∫ |Y|^{2p}`, not `∫ |Y|`, so that
  bridge does not exist yet; it is a general tool and belongs with T77, not here.  The purely
  deterministic first step is provided: `RBM.Gauss.norm_quad11_le_integral`,
  `RBM.Gauss.norm_quad13_le_integral`.

## Main results

* `RBM.Gauss.integrable_sample_lkErr_mul`, `RBM.Gauss.int2_gauss` — `hint2`.
* `RBM.Gauss.trace_mul_Eblk_eq_sum`, `RBM.Gauss.gloop_oneLoop_eq_trace`,
  `RBM.Gauss.gloop_oneLoop_eq_sum` — the `1`-loop as a block average.
* `RBM.Gauss.sum_Sblk_eq_sum_SB_blkCoef`, `RBM.Gauss.blkCoef_mul_SB`,
  `RBM.Gauss.sum_blkCoef_sum_Sblk` — the block collapse of the variance profile.
* `RBM.Gauss.trace_green_mul_Eblk_sub_mE` — the pointwise self-consistent equation.
* `RBM.Gauss.integral_gloop_oneLoop_mul` — `E[⟨G E_a⟩⟨G E_b⟩]` as a double block average.
* `RBM.Gauss.eq527_at`, `RBM.Gauss.eq527_gauss` — **(5.127)**, `h527`.
* `RBM.Gauss.norm_quad11_le_integral`, `RBM.Gauss.norm_quad13_le_integral` — the deterministic
  first step of `hq11`, `hq13`.

## Deviations from the paper

None in this file: (5.127) is proved exactly as the paper states it, and the two integrability
statements are Lean bookkeeping that the paper leaves implicit (`‖G_u‖ ≤ η_u^{-1}`).
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix

/-! ### `hint2`: integrability of the products of (5.134) -/

section Integrability

variable {d : Dims}

/-- **The product of two centred loops is integrable.**  Both factors are continuous in `ω`
(`RBM.Gauss.continuous_gloop_Hflow`) and *deterministically* bounded by (5.2)
(`RBM.Gauss.norm_sample_Lval_le`), so the product is a bounded continuous function on a
probability space. -/
theorem integrable_sample_lkErr_mul (d : Dims) (N : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (I J : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hIn : 1 ≤ I.a.length)
    (hJ : J.WF) (hJn : 1 ≤ J.a.length) :
    Integrable (fun ω : Ω d =>
      ((sample d).Lval E N u ω I - (band d).Kval E N u I) *
        ((sample d).Lval E N u ω J - (band d).Kval E N u J)) (band d).P := by
  have hη : 0 < etaT E u := etaT_pos_of_lt_one hE hu
  have hz : etaT E u ≤ |(zt E u).im| := (abs_im_zt E hE hu).ge
  have hz0 : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu
  have hcont : Continuous fun ω : Ω d =>
      ((sample d).Lval E N u ω I - (band d).Kval E N u I) *
        ((sample d).Lval E N u ω J - (band d).Kval E N u J) :=
    ((continuous_gloop_Hflow d N u hz0 I).sub continuous_const).mul
      ((continuous_gloop_Hflow d N u hz0 J).sub continuous_const)
  refine integrable_of_continuous_of_bound hcont
    (C := ((etaT E u)⁻¹ ^ I.a.length * ((d.W N : ℝ))⁻¹ ^ (I.a.length - 1)
        + ‖(band d).Kval E N u I‖) *
      ((etaT E u)⁻¹ ^ J.a.length * ((d.W N : ℝ))⁻¹ ^ (J.a.length - 1)
        + ‖(band d).Kval E N u J‖)) fun ω => ?_
  rw [norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_sample_Lval_le hη hz ω I hI hIn
  · refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_sample_Lval_le hη hz ω J hJ hJn

/-- **`hint2` of `RBM.Step6.sharpExpect_step6` for the Gaussian model**: the products of (5.134)
are integrable. -/
theorem int2_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ (N : ℕ) (v : TimeIcc s t N) (a₁ : ZMod ((band d).L N))
      (w : LoopData ((band d).L N) 3),
      Integrable (fun ω => ((sample d).Lval E N v ω (Step6.oneLoop a₁)
          - (band d).Kval E N v (Step6.oneLoop a₁))
        * ((sample d).Lval E N v ω w.idx - (band d).Kval E N v w.idx)) (band d).P :=
  fun N v a₁ w => integrable_sample_lkErr_mul d N hE (v.2.2.trans_lt (ht1 N)) _ _
    (by rfl) (by exact le_refl 1)
    w.idx_wf (by simp [LoopData.idx])

end Integrability

/-! ### `h527`: the self-consistent equation (5.127), deterministic half -/

section Eq527Det

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
/-- `⟨M E_a⟩ = ∑_k (E_a)_{kk} M_{kk}`, the `m = 0` case of `RBM.trace_sub_mul_Eblk`. -/
theorem trace_mul_Eblk_eq_sum (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a : ZMod L) :
    Matrix.trace (M * Eblk L W a) = ∑ k, (blkCoef L W a k : ℂ) * M k k := by
  simpa using trace_sub_mul_Eblk M 0 a

/-- **The `1`-loop is the block average `⟨G E_a⟩`.** -/
theorem gloop_oneLoop_eq_trace (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (a : ZMod L) :
    gloop L W H z (Step6.oneLoop a) = Matrix.trace (green H z * Eblk L W a) := by
  rw [Step6.oneLoop, gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one, Gsig_true]

omit [NeZero W] in
/-- **The block collapse of the variance profile.**  `S_{(a,α),(b,β)} = S^{(B)}_{ab}/W` does not
depend on the offsets, so a `S`-weighted sum over the full index set is a `S^{(B)}`-weighted sum
of *block averages*.  This is what turns the entrywise integration-by-parts display
`RBM.Gauss.integral_Hflow_mul_green_diag` into the loop display (5.127). -/
theorem sum_Sblk_eq_sum_SB_blkCoef (p : ZMod L × Fin W) (F : ZMod L × Fin W → ℂ) :
    ∑ k, (Sblk L W p k : ℂ) * F k
      = ∑ b, SB L b p.1 * ∑ k, (blkCoef L W b k : ℂ) * F k := by
  classical
  have hright : ∀ b : ZMod L, ∑ k, (blkCoef L W b k : ℂ) * F k
      = ∑ β : Fin W, (W : ℂ)⁻¹ * F (b, β) := by
    intro b
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · exact Finset.sum_congr rfl fun β _ => by simp [blkCoef]
    · intro b' _ hb'
      exact Finset.sum_eq_zero fun β _ => by simp [blkCoef, hb']
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hright b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [SB_apply, sbKernel_eq_ofReal, ← sbKre_neg, neg_sub, Sblk]
  push_cast
  ring

/-- **The pointwise self-consistent equation.**  Taking the block average of
`G - m = m(-H - u m)G` (`RBM.Gauss.green_sub_smul_one_eq`):
`⟨(G-m)E_a⟩ = -m⟨H G E_a⟩ - u m² ⟨G E_a⟩`. -/
theorem trace_green_mul_Eblk_sub_mE {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : H.IsHermitian) {E u : ℝ} (hE : |E| ≤ 2) (hz : (zt E u).im ≠ 0) (a : ZMod L) :
    Matrix.trace (green H (zt E u) * Eblk L W a) - mE E
      = -(mE E * Matrix.trace (H * green H (zt E u) * Eblk L W a))
        - (u : ℂ) * mE E ^ 2 * Matrix.trace (green H (zt E u) * Eblk L W a) := by
  have hkey := green_sub_smul_one_eq hH hE hz (n := ZMod L × Fin W)
  have hl : Matrix.trace ((green H (zt E u) - mE E • (1 : Matrix (ZMod L × Fin W) _ ℂ))
        * Eblk L W a)
      = Matrix.trace (green H (zt E u) * Eblk L W a) - mE E := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul, trace_Eblk, mul_one]
  rw [← hl, hkey]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.sub_mul, Matrix.neg_mul,
    Matrix.one_mul, Matrix.trace_sub, Matrix.trace_neg]
  ring

end Eq527Det

/-! ### `h527`: (5.127) for the Gaussian model -/

section Eq527Gauss

variable {d : Dims}

/-- `blkCoef L W a` is supported on the block `a`, so a factor `S^{(B)}_{b p_1}` under it may be
frozen at `S^{(B)}_{ba}`. -/
theorem blkCoef_mul_SB {L W : ℕ} [NeZero L] (a b : ZMod L) (p : ZMod L × Fin W) :
    (blkCoef L W a p : ℂ) * SB L b p.1 = (blkCoef L W a p : ℂ) * SB L b a := by
  by_cases h : p.1 = a
  · rw [h]
  · simp [blkCoef, h]

/-- **The `1`-loop as a `blkCoef`-weighted sum of diagonal Green entries.** -/
theorem gloop_oneLoop_eq_sum (d : Dims) (N : ℕ) (E u : ℝ) (ω : Ω d) (b : ZMod (d.L N)) :
    gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
      = ∑ p, (blkCoef (d.L N) (d.W N) b p : ℂ) * green (Hflow d N u ω) (zt E u) p p := by
  rw [gloop_oneLoop_eq_trace, trace_mul_Eblk_eq_sum]

/-- The `1`-loop is tame. -/
theorem tame_gloop_oneLoop {N : ℕ} {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    (b : ZMod (d.L N)) :
    Tame d (fun ω : Ω d =>
      gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)) := by
  have hfun : (fun ω : Ω d =>
      gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b))
      = fun ω : Ω d => ∑ p, (blkCoef (d.L N) (d.W N) b p : ℂ)
          * green (Hflow d N u ω) (zt E u) p p :=
    funext fun ω => gloop_oneLoop_eq_sum d N E u ω b
  rw [hfun]
  exact Tame.sum _ fun p _ =>
    (Tame.const (d := d) ((blkCoef (d.L N) (d.W N) b p : ℝ) : ℂ)).mul
      (tame_green_apply hE hu1 u p p)

/-- **The block collapse under a `blkCoef` weight.**  Since `blkCoef L W a` is supported on the
block `a`, the `S^{(B)}` factor produced by `RBM.Gauss.sum_Sblk_eq_sum_SB_blkCoef` is constant
and the `b`-sum can be pulled out. -/
theorem sum_blkCoef_sum_Sblk (L W : ℕ) [NeZero L] (a : ZMod L)
    (Q : (ZMod L × Fin W) → (ZMod L × Fin W) → ℂ) :
    ∑ p, (blkCoef L W a p : ℂ) * ∑ k, (Sblk L W p k : ℂ) * Q p k
      = ∑ b, SB L b a * ∑ p, (blkCoef L W a p : ℂ)
          * ∑ k, (blkCoef L W b k : ℂ) * Q p k := by
  have h1 : ∀ p : ZMod L × Fin W, (blkCoef L W a p : ℂ) * ∑ k, (Sblk L W p k : ℂ) * Q p k
      = ∑ b, SB L b a * ((blkCoef L W a p : ℂ) * ∑ k, (blkCoef L W b k : ℂ) * Q p k) := by
    intro p
    rw [sum_Sblk_eq_sum_SB_blkCoef p (Q p), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hc := blkCoef_mul_SB (L := L) (W := W) a b p
    calc (blkCoef L W a p : ℂ) * (SB L b p.1 * ∑ k, (blkCoef L W b k : ℂ) * Q p k)
        = ((blkCoef L W a p : ℂ) * SB L b p.1)
            * ∑ k, (blkCoef L W b k : ℂ) * Q p k := by ring
      _ = ((blkCoef L W a p : ℂ) * SB L b a)
            * ∑ k, (blkCoef L W b k : ℂ) * Q p k := by rw [hc]
      _ = SB L b a * ((blkCoef L W a p : ℂ)
            * ∑ k, (blkCoef L W b k : ℂ) * Q p k) := by ring
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

/-- **The expectation of a product of two `1`-loops** as a double `blkCoef`-weighted sum of
expectations of products of diagonal Green entries. -/
theorem integral_gloop_oneLoop_mul (d : Dims) (N : ℕ) {E u : ℝ} (hE : |E| < 2) (hu1 : u < 1)
    (a b : ZMod (d.L N)) :
    ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
        * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d)
      = ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ) * ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ)
          * ∫ ω, green (Hflow d N u ω) (zt E u) p p
              * green (Hflow d N u ω) (zt E u) k k ∂(P d) := by
  classical
  have hIBP : GaussIBP d := gaussIBP d
  have hint : ∀ p k : d.Idx N, Integrable (fun ω : Ω d =>
      (blkCoef (d.L N) (d.W N) a p : ℂ) * ((blkCoef (d.L N) (d.W N) b k : ℂ)
        * (green (Hflow d N u ω) (zt E u) p p * green (Hflow d N u ω) (zt E u) k k))) (P d) :=
    fun p k => ((Tame.const (d := d) ((blkCoef (d.L N) (d.W N) a p : ℝ) : ℂ)).mul
      ((Tame.const (d := d) ((blkCoef (d.L N) (d.W N) b k : ℝ) : ℂ)).mul
        ((tame_green_apply hE hu1 u p p).mul (tame_green_apply hE hu1 u k k)))).integrable hIBP
  have hfun : (fun ω : Ω d =>
      gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
        * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b))
      = fun ω : Ω d => ∑ p, ∑ k, (blkCoef (d.L N) (d.W N) a p : ℂ)
          * ((blkCoef (d.L N) (d.W N) b k : ℂ)
            * (green (Hflow d N u ω) (zt E u) p p * green (Hflow d N u ω) (zt E u) k k)) := by
    funext ω
    rw [gloop_oneLoop_eq_sum d N E u ω a, gloop_oneLoop_eq_sum d N E u ω b,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hfun, integral_finsetSum _ fun p _ => integrable_finsetSum _ fun k _ => hint p k]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun k _ => hint p k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul]

/-- The scalar bookkeeping of (5.127): once the one-loop identity and the expansion of the
quadratic term are in hand, (5.127) is linear algebra in `ℂ`. -/
theorem eq527_algebra {m uu La Sq SL SR : ℂ}
    (hmain : La - m = uu * m * SR - uu * m ^ 2 * La)
    (hsumR : SR = Sq + m * SL + m * La - m ^ 2) :
    La - m = uu * m ^ 2 * (SL - m) + uu * m * Sq := by
  rw [hsumR] at hmain
  linear_combination hmain

/-- **(5.127) for the Gaussian model, at a single time `u`.**

`E⟨(G_u-m)E_a⟩ = u m² ∑_b S^{(B)}_{ba} E⟨(G_u-m)E_b⟩ + u m ∑_b S^{(B)}_{ba}
E[⟨(G_u-m)E_b⟩⟨(G_u-m)E_a⟩]`.

This is an **exact identity**, with no error term: the algebraic identity `G - m = m(-H-um)G`
(`RBM.Gauss.green_sub_smul_one_eq`), Gaussian integration by parts entry by entry
(`RBM.Gauss.integral_Hflow_mul_green_diag`, which rests on the *proved* `RBM.Gauss.gaussIBP`),
and the block collapse `S_{(a,α),(b,β)} = S^{(B)}_{ab}/W`
(`RBM.Gauss.sum_blkCoef_sum_Sblk`), which is what converts a sum of products of *diagonal
entries* into a sum of products of *block averages*. -/
theorem eq527_at (d : Dims) (N : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (a : ZMod (d.L N)) :
    Step6.lk1 (sample d) E N u a
      = (u : ℂ) * mE E ^ 2 * ∑ b, SB (d.L N) b a * Step6.lk1 (sample d) E N u b
        + (u : ℂ) * mE E * ∑ b, SB (d.L N) b a * Step6.quad11 (sample d) E N u b a := by
  classical
  have hIBP : GaussIBP d := gaussIBP d
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  have hprob := isProbabilityMeasure_P d
  -- `K` at a `1`-loop is `m`
  have hKv : ∀ b : ZMod (d.L N), (band d).Kval E N u (Step6.oneLoop b) = mE E := by
    intro b
    show Kgen (d.L N) (d.W N) (mSigma E) u (Step6.oneLoop b) = mE E
    rw [Step6.oneLoop, Kgen_one, mSigma_true]
  have hlk : ∀ b : ZMod (d.L N), Step6.lk1 (sample d) E N u b
      = (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
        - mE E := by
    intro b
    have hdef : Step6.lk1 (sample d) E N u b
        = (sample d).ELval E N u (Step6.oneLoop b)
          - (band d).Kval E N u (Step6.oneLoop b) := rfl
    rw [hdef, hKv b]; rfl
  have hga : ∀ b : ZMod (d.L N), Integrable (fun ω : Ω d =>
      gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)) (P d) :=
    fun b => (tame_gloop_oneLoop hE hu1 b).integrable hIBP
  -- `∑_b S^{(B)}_{ba} = 1`
  have hsum1 : ∑ b, SB (d.L N) b a = 1 := by
    rw [Finset.sum_congr rfl fun b _ => SB_apply_comm (d.L N) b a]
    exact sum_SB_row (d.L N) (d.three_le_L N) a
  -- the pointwise self-consistent equation
  have hpt : ∀ ω : Ω d,
      gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) - mE E
        = -(mE E * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
            * (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p)
          - (u : ℂ) * mE E ^ 2
            * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) := by
    intro ω
    have h := trace_green_mul_Eblk_sub_mE (Hflow_isHermitian d N u ω) hE.le hz a
    rwa [← gloop_oneLoop_eq_trace, trace_mul_Eblk_eq_sum] at h
  have hHGint : ∀ p : d.Idx N, Integrable (fun ω : Ω d =>
      (blkCoef (d.L N) (d.W N) a p : ℂ)
        * (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p) (P d) :=
    fun p => ((Tame.const (d := d) ((blkCoef (d.L N) (d.W N) a p : ℝ) : ℂ)).mul
      (tame_Hflow_mul_green_apply hE hu1 u p p)).integrable hIBP
  -- integrate it
  have hmain0 : (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) ∂(P d))
        - mE E
      = -(mE E * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
            * ∫ ω, (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p ∂(P d))
        - (u : ℂ) * mE E ^ 2
          * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) ∂(P d) := by
    have hA : Integrable (fun ω : Ω d => -(mE E * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
        * (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p)) (P d) :=
      ((integrable_finsetSum _ fun p _ => hHGint p).const_mul (mE E)).neg
    have hB : Integrable (fun ω : Ω d => (u : ℂ) * mE E ^ 2
        * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)) (P d) :=
      (hga a).const_mul _
    have hL : ∫ ω, (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) - mE E)
          ∂(P d)
        = (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) ∂(P d))
          - mE E := by
      rw [integral_sub (hga a) (integrable_const _), integral_const]
      simp
    rw [← hL, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hA hB,
      integral_neg, integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun p _ => hHGint p]
    congr 2
    congr 1
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  -- the integration-by-parts display and the block collapse
  have hT : ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
        * ∫ ω, (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p ∂(P d)
      = -((u : ℂ) * ∑ b, SB (d.L N) b a
          * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
              * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d)) := by
    have hstep : ∀ p : d.Idx N,
        ∫ ω, (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p ∂(P d)
          = -((u : ℂ) * ∑ k, (Sblk (d.L N) (d.W N) p k : ℂ)
              * ∫ ω, green (Hflow d N u ω) (zt E u) p p
                  * green (Hflow d N u ω) (zt E u) k k ∂(P d)) :=
      fun p => integral_Hflow_mul_green_diag hIBP hE hu1 hu0 p
    have hcol := sum_blkCoef_sum_Sblk (d.L N) (d.W N) a
      (fun p k => ∫ ω, green (Hflow d N u ω) (zt E u) p p
        * green (Hflow d N u ω) (zt E u) k k ∂(P d))
    calc ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
            * ∫ ω, (Hflow d N u ω * green (Hflow d N u ω) (zt E u)) p p ∂(P d)
        = ∑ p, -((u : ℂ) * ((blkCoef (d.L N) (d.W N) a p : ℂ)
              * ∑ k, (Sblk (d.L N) (d.W N) p k : ℂ)
                * ∫ ω, green (Hflow d N u ω) (zt E u) p p
                    * green (Hflow d N u ω) (zt E u) k k ∂(P d))) :=
          Finset.sum_congr rfl fun p _ => by rw [hstep p]; ring
      _ = -((u : ℂ) * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
              * ∑ k, (Sblk (d.L N) (d.W N) p k : ℂ)
                * ∫ ω, green (Hflow d N u ω) (zt E u) p p
                    * green (Hflow d N u ω) (zt E u) k k ∂(P d)) := by
          rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -((u : ℂ) * ∑ b, SB (d.L N) b a * ∑ p, (blkCoef (d.L N) (d.W N) a p : ℂ)
              * ∑ k, (blkCoef (d.L N) (d.W N) b k : ℂ)
                * ∫ ω, green (Hflow d N u ω) (zt E u) p p
                    * green (Hflow d N u ω) (zt E u) k k ∂(P d)) := by rw [hcol]
      _ = -((u : ℂ) * ∑ b, SB (d.L N) b a
              * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
                  * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d)) := by
          congr 2
          exact Finset.sum_congr rfl fun b _ => by
            rw [integral_gloop_oneLoop_mul d N hE hu1 a b]
  -- the quadratic term
  have hRb : ∀ b : ZMod (d.L N),
      (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
          * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
        = Step6.quad11 (sample d) E N u b a
          + mE E * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
              ∂(P d))
          + mE E * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
              ∂(P d))
          - mE E ^ 2 := by
    intro b
    have hprodint : Integrable (fun ω : Ω d =>
        gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
          * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)) (P d) :=
      ((tame_gloop_oneLoop hE hu1 a).mul (tame_gloop_oneLoop hE hu1 b)).integrable hIBP
    have hq : Step6.quad11 (sample d) E N u b a
        = ∫ ω, (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) - mE E)
            * (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) - mE E)
            ∂(P d) := by
      have hdef : Step6.quad11 (sample d) E N u b a
          = ∫ ω, ((sample d).Lval E N u ω (Step6.oneLoop b)
                - (band d).Kval E N u (Step6.oneLoop b))
              * ((sample d).Lval E N u ω (Step6.oneLoop a)
                - (band d).Kval E N u (Step6.oneLoop a)) ∂(band d).P := rfl
      rw [hdef, hKv b, hKv a]; rfl
    have hq2 : Step6.quad11 (sample d) E N u b a
        = (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
              * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
          - mE E * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
              ∂(P d))
          - mE E * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
              ∂(P d))
          + mE E ^ 2 := by
      rw [hq, integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        show (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) - mE E)
            * (gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) - mE E)
          = gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
              * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
            - mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
            - mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
            + mE E ^ 2 from by ring)]
      have hI2 : Integrable (fun ω : Ω d =>
          mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)) (P d) :=
        (hga b).const_mul _
      have hI3 : Integrable (fun ω : Ω d =>
          mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)) (P d) :=
        (hga a).const_mul _
      have hI12 : Integrable (fun ω : Ω d =>
          gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
              * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
            - mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b))
          (P d) := hprodint.sub hI2
      have hI123 : Integrable (fun ω : Ω d =>
          gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
                * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
              - mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b)
            - mE E * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a))
          (P d) := hI12.sub hI3
      rw [integral_add hI123 (integrable_const (mE E ^ 2)),
        integral_sub hI12 hI3, integral_sub hprodint hI2,
        integral_const_mul, integral_const_mul, integral_const]
      simp
    rw [hq2]; ring
  -- the `b`-sum of the quadratic terms
  have hsumR : (∑ b, SB (d.L N) b a
        * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
            * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
      = (∑ b, SB (d.L N) b a * Step6.quad11 (sample d) E N u b a)
        + mE E * (∑ b, SB (d.L N) b a
            * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
        + mE E * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
            ∂(P d))
        - mE E ^ 2 := by
    have hterm : ∀ b : ZMod (d.L N), SB (d.L N) b a
        * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a)
            * gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d)
        = SB (d.L N) b a * Step6.quad11 (sample d) E N u b a
          + mE E * (SB (d.L N) b a
              * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
          + SB (d.L N) b a * (mE E
              * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop a) ∂(P d))
              - mE E ^ 2) := fun b => by rw [hRb b]; ring
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hsum1, one_mul]
    ring
  -- the `b`-sum of the linear terms
  have hlksum : (∑ b, SB (d.L N) b a * Step6.lk1 (sample d) E N u b)
      = (∑ b, SB (d.L N) b a
          * ∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
        - mE E := by
    have hterm : ∀ b : ZMod (d.L N), SB (d.L N) b a * Step6.lk1 (sample d) E N u b
        = SB (d.L N) b a
            * (∫ ω, gloop (d.L N) (d.W N) (Hflow d N u ω) (zt E u) (Step6.oneLoop b) ∂(P d))
          - SB (d.L N) b a * mE E := fun b => by rw [hlk b]; ring
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hsum1, one_mul]
  rw [hlk a, hlksum]
  refine eq527_algebra ?_ hsumR
  rw [hmain0, hT]; ring

/-- **`h527` of `RBM.Step6.sharpExpect_step6` for the Gaussian model**: (5.127), uniformly in
`u ∈ [s,t]`. -/
theorem eq527_gauss (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    Step6.Eq527 (sample d) E s t :=
  fun N u a => eq527_at d N hE ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N)) a

end Eq527Gauss

/-! ### `hq11`, `hq13`: the deterministic first step -/

section Quad

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`|E[(L-K)_1 (L-K)_1]| ≤ E[|(L-K)_1| |(L-K)_1|]`** — the only step of `hq11` that does not
need the reverse bridge `≺ ⟹ moments`.  What remains, given (2.78) at `n = 1`
(`RBM.Steps.sharpLmK`), is a *first-moment* reverse bridge (`RBM.Gauss.momentDom_of_stochDom`
produces even moments, not `∫ Y`); see the module docstring. -/
theorem norm_quad11_le_integral (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ)
    (b a : ZMod (B.L N)) :
    ‖Step6.quad11 X E N u b a‖
      ≤ ∫ ω, X.lkErr E N u ω (Step6.oneLoop b) * X.lkErr E N u ω (Step6.oneLoop a) ∂B.P :=
  (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Filter.Eventually.of_forall fun _ω => norm_mul _ _))

/-- **`|E[(L-K)_1 (L-K)_3]| ≤ E[|(L-K)_1| |(L-K)_3|]`**, the analogous step for `hq13`. -/
theorem norm_quad13_le_integral (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ)
    (a₁ : ZMod (B.L N)) (w : LoopData (B.L N) 3) :
    ‖Step6.quad13 X E N u a₁ w‖
      ≤ ∫ ω, X.lkErr E N u ω (Step6.oneLoop a₁) * X.lkErr E N u ω w.idx ∂B.P :=
  (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Filter.Eventually.of_forall fun _ω => norm_mul _ _))

end Quad


end RBM.Gauss
