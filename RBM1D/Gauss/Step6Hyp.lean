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
* **`hq11`, `hq13`** (T123) — `RBM.Gauss.quad11_unifDetDom`,
  `RBM.Gauss.quad13_unifDetDom`, for an arbitrary `RBM.Sample`: the deterministic first step
  `RBM.Gauss.norm_quad11_le_integral` / `RBM.Gauss.norm_quad13_le_integral` followed by the
  **first-moment reverse bridge** `RBM.Gauss.unifDetDom_integral_of_stochDom` of T77's
  `RBM1D/Gauss/Envelope.lean`, applied to (2.78) (`RBM.Steps.sharpLmK`, Step 4's output, which
  *is* available before Step 6) at `n = 1` and at `n = 3`.  The bridge's three inputs are
  supplied by `RBM.Gauss.stochDom_lkErr_mul` (the product `≺`-bound),
  `RBM.Gauss.lkErr_le_rpow` (the deterministic envelope, from `RBM.Gauss.norm_gloop_le_det` and
  (2.59) `RBM.Band.norm_Kval_le`) and, for the polynomial lower bound on the control,
  `ℓ_u ≤ L`, `η_u ≤ 1`, `W L ≤ N`.  **`η_u ≥ N^{-c}` is carried explicitly** as the hypothesis
  `hη` of every statement in the section: it is not free, it is the form in which
  `W ℓ_u η_u ≥ 1` — a consequence of (2.72) — enters the envelope.

  The bridge's integrability hypothesis `hint` is the `ℝ`-valued product `|L-K|_m · |L-K|_n`;
  it is **discharged for the Gaussian sample** (T131) by
  `RBM.Gauss.integrable_sample_lkErr_mul_real`, giving the hypothesis-free
  `RBM.Gauss.quad11_unifDetDom_gauss` and `RBM.Gauss.quad13_unifDetDom_gauss`.  The
  general-`RBM.Sample` statements keep `hint`: nothing outside the Gaussian model can supply it,
  since it rests on (5.2) along the flow together with continuity of the loop in `ω`.

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
Consequently `RBM.Step6.sharpExpect_step6` still needs exactly four of its seven random-layer
hypotheses, all four of them bound to the existence of the drift tensors `DLK`, `DG` (T58):
`hH`, `hFD`, `h5133`, `hG`.  (Verified by a probe that instantiates `sharpExpect_step6` with
everything this file provides; only those four goals remain.)

## Main results

* `RBM.Gauss.integrable_sample_lkErr_mul`, `RBM.Gauss.int2_gauss` — `hint2`;
  `RBM.Gauss.integrable_sample_lkErr_mul_real` — its `ℝ`-valued form, the `hint` of the bridge.
* `RBM.Gauss.trace_mul_Eblk_eq_sum`, `RBM.Gauss.gloop_oneLoop_eq_trace`,
  `RBM.Gauss.gloop_oneLoop_eq_sum` — the `1`-loop as a block average.
* `RBM.Gauss.sum_Sblk_eq_sum_SB_blkCoef`, `RBM.Gauss.blkCoef_mul_SB`,
  `RBM.Gauss.sum_blkCoef_sum_Sblk` — the block collapse of the variance profile.
* `RBM.Gauss.trace_green_mul_Eblk_sub_mE` — the pointwise self-consistent equation.
* `RBM.Gauss.integral_gloop_oneLoop_mul` — `E[⟨G E_a⟩⟨G E_b⟩]` as a double block average.
* `RBM.Gauss.eq527_at`, `RBM.Gauss.eq527_gauss` — **(5.127)**, `h527`.
* `RBM.Gauss.norm_quad11_le_integral`, `RBM.Gauss.norm_quad13_le_integral` — the deterministic
  first step of `hq11`, `hq13`.
* `RBM.Gauss.oneLoopData`, `RBM.Gauss.lkErr_le_det`, `RBM.Gauss.lkErr_le_rpow`,
  `RBM.Gauss.lkErr_loopData_le_rpow`, `RBM.Gauss.stochDom_lkErr_mul`,
  `RBM.Gauss.unifDetDom_integral_lkErr_mul` — the inputs of the first-moment reverse bridge for
  a product `|L-K|_m · |L-K|_n`, for an arbitrary `RBM.Sample`.
* `RBM.Gauss.quad11_unifDetDom`, `RBM.Gauss.quad13_unifDetDom` — **`hq11` and `hq13`**, for an
  arbitrary `RBM.Sample`, carrying the integrability hypothesis `hint`.
* `RBM.Gauss.quad11_unifDetDom_gauss`, `RBM.Gauss.quad13_unifDetDom_gauss` — the same two for
  `RBM.Gauss.sample`, with `hint` discharged.

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

/-- **The `ℝ`-valued form of `RBM.Gauss.integrable_sample_lkErr_mul`**: the product of the two
*moduli* `|L-K|_I · |L-K|_J` is integrable.  This is the shape the first-moment reverse bridge
of `RBM.Gauss.unifDetDom_integral_lkErr_mul` consumes (its `hint`), whereas the `ℂ`-valued
statement above is the shape `hint2` of `RBM.Step6.sharpExpect_step6` consumes; the two differ
by `norm_mul`, so one follows from the other by `MeasureTheory.Integrable.norm`. -/
theorem integrable_sample_lkErr_mul_real (d : Dims) (N : ℕ) {E u : ℝ} (hE : |E| < 2) (hu : u < 1)
    (I J : LoopIdx (ZMod (d.L N))) (hI : I.WF) (hIn : 1 ≤ I.a.length)
    (hJ : J.WF) (hJn : 1 ≤ J.a.length) :
    Integrable (fun ω : Ω d =>
      (sample d).lkErr E N u ω I * (sample d).lkErr E N u ω J) (band d).P :=
  ((integrable_sample_lkErr_mul d N hE hu I J hI hIn hJ hJn).norm).congr
    (Filter.Eventually.of_forall fun _ω => norm_mul _ _)

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

/-! ### `hq11`, `hq13`: the first-moment reverse bridge applied -/

section FirstMoment

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The `1`-loop `RBM.Step6.oneLoop a` as an element of `RBM.LoopData _ 1`, so that the
`≺`-bounds of `RBM.Steps`, whose index set is `LoopData`, can be instantiated at it. -/
def oneLoopData {L : ℕ} (a : ZMod L) : LoopData L 1 := (fun _ => true, fun _ => a)

@[simp] theorem idx_oneLoopData {L : ℕ} (a : ZMod L) :
    (oneLoopData a).idx = Step6.oneLoop a := rfl

/-- **The deterministic envelope of `|L - K|` for an arbitrary sample.**  The loop half is (5.2)
along the flow (`RBM.Gauss.norm_gloop_le_det`), which holds for *every* `ω` because `H_u` is
Hermitian pointwise; the `K` half is any pointwise bound, in practice (2.59)
(`RBM.Band.norm_Kval_le`). -/
theorem lkErr_le_det (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ} (hu1 : u < 1)
    (ω : Ω) {I : LoopIdx (ZMod (B.L N))} (hwf : I.WF) (hn : 1 ≤ I.length) :
    X.lkErr E N u ω I
      ≤ (etaT E u)⁻¹ ^ I.length * ((B.W N : ℝ))⁻¹ ^ (I.length - 1) + ‖B.Kval E N u I‖ := by
  have h1 : ‖X.Lval E N u ω I‖
      ≤ (etaT E u)⁻¹ ^ I.length * ((B.W N : ℝ))⁻¹ ^ (I.length - 1) :=
    norm_gloop_le_det (X.hermitian N u ω) hE hu1 I hwf hn
  exact (norm_sub_le _ _).trans (add_le_add h1 le_rfl)

/-- **The envelope at a polynomial scale.**  If `η_u` is not super-polynomially small,
`N^{-c} ≤ η_u`, and `K` obeys (2.59), then `|L_{u,σ,a} - K_{u,σ,a}| ≤ (1 + C) N^{cn}` for every
`ω`.  This is the `henv` input of `RBM.Gauss.unifDetDom_integral_of_stochDom`.

`N^{-c} ≤ η_u` is **not** free; it is the form in which `W ℓ_u η_u ≥ 1` (a consequence of
(2.72)) enters, and it is threaded explicitly through every statement below. -/
theorem lkErr_le_rpow (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) {c : ℝ} (hc0 : 0 ≤ c) (hη : (N : ℝ) ^ (-c) ≤ etaT E u)
    (ω : Ω) {I : LoopIdx (ZMod (B.L N))} (hwf : I.WF) (hn : 1 ≤ I.length)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hK : ‖B.Kval E N u I‖ ≤ CK * (B.scale E N u)⁻¹ ^ (I.length - 1)) :
    X.lkErr E N u ω I ≤ (1 + CK) * (N : ℝ) ^ (c * I.length) := by
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hη0 : 0 < etaT E u := etaT_pos_of_lt_one hE hu1
  have hW1 : 1 ≤ B.W N := B.W_pos N
  have hWge1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast hW1
  have hℓ1 : (1 : ℝ) ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0.le hu1
  have hsc0 : 0 < B.scale E N u := B.scale_pos hE N hu0 hu1
  -- the loop half
  have hloop := det_envelope_le_rpow hη0 hN hη hW1 I.length
  -- `(W ℓ_u η_u)⁻¹ ≤ η_u⁻¹ ≤ N^c`
  have hNc1 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hNge1 hc0
  have hηc : (etaT E u)⁻¹ ≤ (N : ℝ) ^ c := by
    have hpos : (0 : ℝ) < (N : ℝ) ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
    have h := inv_anti₀ hpos hη
    rwa [Real.rpow_neg (by linarith), inv_inv] at h
  have hscη : (B.scale E N u)⁻¹ ≤ (etaT E u)⁻¹ := by
    refine inv_anti₀ hη0 ?_
    have hWℓ : (1 : ℝ) ≤ (B.W N : ℝ) * B.ell N u := by nlinarith
    show etaT E u ≤ (B.W N : ℝ) * B.ell N u * etaT E u
    calc etaT E u = 1 * etaT E u := (one_mul _).symm
      _ ≤ (B.W N : ℝ) * B.ell N u * etaT E u := mul_le_mul_of_nonneg_right hWℓ hη0.le
  have hscN : (B.scale E N u)⁻¹ ≤ (N : ℝ) ^ c := hscη.trans hηc
  -- the `K` half
  have hKpow : (B.scale E N u)⁻¹ ^ (I.length - 1) ≤ (N : ℝ) ^ (c * I.length) := by
    calc (B.scale E N u)⁻¹ ^ (I.length - 1) ≤ ((N : ℝ) ^ c) ^ (I.length - 1) :=
          pow_le_pow_left₀ (by positivity) hscN _
      _ ≤ ((N : ℝ) ^ c) ^ I.length := pow_le_pow_right₀ hNc1 (Nat.sub_le _ _)
      _ = (N : ℝ) ^ (c * I.length) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ c) I.length, ← Real.rpow_mul (by linarith)]
  have hmain := lkErr_le_det X hE hu1 ω hwf hn (I := I)
  have hK' : ‖B.Kval E N u I‖ ≤ CK * (N : ℝ) ^ (c * I.length) :=
    hK.trans (mul_le_mul_of_nonneg_left hKpow hCK0)
  calc X.lkErr E N u ω I
      ≤ (etaT E u)⁻¹ ^ I.length * ((B.W N : ℝ))⁻¹ ^ (I.length - 1) + ‖B.Kval E N u I‖ := hmain
    _ ≤ (N : ℝ) ^ (c * I.length) + CK * (N : ℝ) ^ (c * I.length) := add_le_add hloop hK'
    _ = (1 + CK) * (N : ℝ) ^ (c * I.length) := by ring

/-- `RBM.Gauss.lkErr_le_rpow` for the `RBM.LoopData` index family of `RBM.Steps`. -/
theorem lkErr_loopData_le_rpow (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} (hN : 1 ≤ N)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) {c : ℝ} (hc0 : 0 ≤ c) (hη : (N : ℝ) ^ (-c) ≤ etaT E u)
    (ω : Ω) {k : ℕ} (hk : 1 ≤ k) (v : LoopData (B.L N) k) {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hK : ‖B.Kval E N u v.idx‖ ≤ CK * (B.scale E N u)⁻¹ ^ (k - 1)) :
    X.lkErr E N u ω v.idx ≤ (1 + CK) * (N : ℝ) ^ (c * k) := by
  have h := lkErr_le_rpow X hE hN hu0 hu1 hc0 hη ω (I := v.idx) v.idx_wf
    (by rw [LoopData.idx_length]; exact hk) hCK0 (by rw [LoopData.idx_length]; exact hK)
  rwa [LoopData.idx_length] at h

/-- **The product of two `|L - K|`'s is `≺` the product of the two controls.**  (2.78)
(`RBM.Steps.sharpLmK`) at loop lengths `m` and `n` gives
`|L-K|_{u,m} · |L-K|_{u,n} ≺ (W ℓ_u η_u)^{-(m+n)}`, uniformly in `u ∈ [s,t]` and in *both* loop
indices at once — the two factors live in different index families, so this is a reindexing of
`RBM.StochDom.mul`, not an instance of it. -/
theorem stochDom_lkErr_mul (X : Sample B) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {m n : ℕ}
    (hdm : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ m))
    (hdn : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (LoopData (B.L N) m × LoopData (B.L N) n)) ω =>
        X.lkErr E N p.1 ω p.2.1.idx * X.lkErr E N p.1 ω p.2.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (m + n)) := by
  refine StochDom.of_subset_union hdm hdn fun τ hτ =>
    ⟨τ / 2, half_pos hτ, Filter.Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have h1 := hno.1 (p.1, p.2.1)
  have h2 := hno.2 (p.1, p.2.2)
  have hsc0 : 0 < B.scale E N (p.1 : ℝ) :=
    B.scale_pos hE N ((hs0 N).trans_le p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
  have hinv0 : (0 : ℝ) ≤ (B.scale E N (p.1 : ℝ))⁻¹ := (inv_nonneg.2 hsc0.le)
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hY2 : 0 ≤ X.lkErr E N (p.1 : ℝ) ω p.2.2.idx := norm_nonneg _
  have hζ1 : (0 : ℝ) ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ m := pow_nonneg hinv0 m
  have hkey : X.lkErr E N (p.1 : ℝ) ω p.2.1.idx * X.lkErr E N (p.1 : ℝ) ω p.2.2.idx
      ≤ (N : ℝ) ^ τ * (B.scale E N (p.1 : ℝ))⁻¹ ^ (m + n) := by
    calc X.lkErr E N (p.1 : ℝ) ω p.2.1.idx * X.lkErr E N (p.1 : ℝ) ω p.2.2.idx
        ≤ ((N : ℝ) ^ (τ / 2) * (B.scale E N (p.1 : ℝ))⁻¹ ^ m)
            * X.lkErr E N (p.1 : ℝ) ω p.2.2.idx := mul_le_mul_of_nonneg_right h1 hY2
      _ ≤ ((N : ℝ) ^ (τ / 2) * (B.scale E N (p.1 : ℝ))⁻¹ ^ m)
            * ((N : ℝ) ^ (τ / 2) * (B.scale E N (p.1 : ℝ))⁻¹ ^ n) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hpos hζ1)
      _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2))
            * ((B.scale E N (p.1 : ℝ))⁻¹ ^ m * (B.scale E N (p.1 : ℝ))⁻¹ ^ n) := by ring
      _ = (N : ℝ) ^ τ * (B.scale E N (p.1 : ℝ))⁻¹ ^ (m + n) := by
          rw [UnifDetDom.rpow_half_mul_rpow_half N hτ, ← pow_add]
  linarith

/-- **The first-moment reverse bridge, applied to a product of two `|L - K|`'s.**

`E[|L-K|_{u,m} |L-K|_{u,n}] ≺ (W ℓ_u η_u)^{-(m+n)}`, uniformly in `u ∈ [s,t]` and in both loop
indices: the hypothesis is (2.78) (`RBM.Steps.sharpLmK`) at `m` and at `n`, the conclusion is a
*deterministic* `≺` for the expectation.  This is `RBM.Gauss.unifDetDom_integral_of_stochDom`
with its three inputs supplied:

* the `≺`-bound for the product, `RBM.Gauss.stochDom_lkErr_mul`;
* the deterministic envelope, `RBM.Gauss.lkErr_le_rpow` (from `RBM.Gauss.norm_gloop_le_det` and
  a pointwise bound on `K`, i.e. (2.59) `RBM.Band.norm_Kval_le`);
* the polynomial lower bound `N^{-(m+n)} ≤ (W ℓ_u η_u)^{-(m+n)}` on the control, from
  `ℓ_u ≤ L`, `η_u ≤ 1` and `W L ≤ N` (the field `RBM.Band.dim`).

**The hypothesis `hη` (`η_u ≥ N^{-c}` for every `u ∈ [s,t]`) is not free**: it is the form in
which `W ℓ_u η_u ≥ 1`, a consequence of (2.72), enters the envelope, and it is carried
explicitly here and in every statement below rather than being assumed silently. -/
theorem unifDetDom_integral_lkErr_mul (X : Sample B) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hKm : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) m),
      ‖B.Kval E N u v.idx‖ ≤ CK * (B.scale E N u)⁻¹ ^ (m - 1))
    (hKn : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) n),
      ‖B.Kval E N u v.idx‖ ≤ CK * (B.scale E N u)⁻¹ ^ (n - 1))
    (hint : ∀ N (p : TimeIcc s t N × (LoopData (B.L N) m × LoopData (B.L N) n)),
      Integrable (fun ω => X.lkErr E N p.1 ω p.2.1.idx * X.lkErr E N p.1 ω p.2.2.idx) B.P)
    (hdm : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ m))
    (hdn : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) :
    UnifDetDom
      (fun N (p : TimeIcc s t N × (LoopData (B.L N) m × LoopData (B.L N) n)) =>
        ∫ ω, X.lkErr E N p.1 ω p.2.1.idx * X.lkErr E N p.1 ω p.2.2.idx ∂B.P)
      (fun N p => (B.scale E N p.1)⁻¹ ^ (m + n)) := by
  have := B.isProbabilityMeasure
  refine unifDetDom_integral_of_stochDom_of_nonneg (B := ((m + n : ℕ) : ℝ))
    (Kenv := c * ((m : ℝ) + (n : ℝ)) + 1)
    (fun N p ω => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hint ?_ (by positivity) ?_
    (by positivity) ?_ (stochDom_lkErr_mul X hE hs0 ht1 hdm hdn)
  · -- `0 < (W ℓ_u η_u)^{-(m+n)}`
    intro N p
    have hsc0 : 0 < B.scale E N (p.1 : ℝ) :=
      B.scale_pos hE N ((hs0 N).trans_le p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
    positivity
  · -- the polynomial lower bound on the control
    filter_upwards [B.dim, eventually_ge_atTop 1] with N hdim hN1 p
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hu0 : 0 < (p.1 : ℝ) := (hs0 N).trans_le p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have hsc0 : 0 < B.scale E N (p.1 : ℝ) := B.scale_pos hE N hu0 hu1
    have hell : B.ell N (p.1 : ℝ) ≤ (B.L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hell0 : (0 : ℝ) ≤ B.ell N (p.1 : ℝ) :=
      le_trans zero_le_one (one_le_ellHat_of_nonneg (B.one_le_L N) hu0.le hu1)
    have heta1 : etaT E (p.1 : ℝ) ≤ 1 := etaT_le_one hE hu0.le
    have heta0 : (0 : ℝ) < etaT E (p.1 : ℝ) := etaT_pos_of_lt_one hE hu1
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
    have hscN : B.scale E N (p.1 : ℝ) ≤ (N : ℝ) := by
      have h1 : B.scale E N (p.1 : ℝ) = (B.W N : ℝ) * B.ell N (p.1 : ℝ) * etaT E (p.1 : ℝ) := rfl
      rw [h1]
      have hstep : (B.W N : ℝ) * B.ell N (p.1 : ℝ) * etaT E (p.1 : ℝ)
          ≤ ((B.W N : ℝ) * (B.L N : ℝ)) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hell hW0) heta1 heta0.le (by positivity)
      linarith
    have hinv : (N : ℝ)⁻¹ ≤ (B.scale E N (p.1 : ℝ))⁻¹ := inv_anti₀ hsc0 hscN
    have hpow : ((N : ℝ)⁻¹) ^ (m + n) ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ (m + n) :=
      pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hinv _
    refine le_trans (le_of_eq ?_) hpow
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast, inv_pow]
  · -- the deterministic envelope, at a polynomial scale
    filter_upwards [hη, eventually_ge_atTop 1, eventually_le_rpow ((1 + CK) ^ 2) one_pos] with
      N hηN hN1 hCN p ω
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hu0 : 0 < (p.1 : ℝ) := (hs0 N).trans_le p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have h1 := lkErr_loopData_le_rpow X hE hN1 hu0 hu1 hc0 (hηN p.1) ω hm p.2.1 hCK0
      (hKm N p.1 p.2.1)
    have h2 := lkErr_loopData_le_rpow X hE hN1 hu0 hu1 hc0 (hηN p.1) ω hn p.2.2 hCK0
      (hKn N p.1 p.2.2)
    have hr1 : (0 : ℝ) ≤ (1 + CK) * (N : ℝ) ^ (c * m) := by positivity
    have hstep : X.lkErr E N (p.1 : ℝ) ω p.2.1.idx * X.lkErr E N (p.1 : ℝ) ω p.2.2.idx
        ≤ ((1 + CK) * (N : ℝ) ^ (c * m)) * ((1 + CK) * (N : ℝ) ^ (c * n)) :=
      mul_le_mul h1 h2 (norm_nonneg _) hr1
    refine hstep.trans ?_
    have hCN' : (1 + CK) ^ 2 ≤ (N : ℝ) := by rwa [Real.rpow_one] at hCN
    have hprod0 : (0 : ℝ) ≤ (N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ)) := by positivity
    have hRHS : (N : ℝ) ^ (c * ((m : ℝ) + (n : ℝ)) + 1)
        = ((N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ))) * (N : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    calc ((1 + CK) * (N : ℝ) ^ (c * (m : ℝ))) * ((1 + CK) * (N : ℝ) ^ (c * (n : ℝ)))
        = (1 + CK) ^ 2 * ((N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ))) := by ring
      _ ≤ (N : ℝ) * ((N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hCN' hprod0
      _ = (N : ℝ) ^ (c * ((m : ℝ) + (n : ℝ)) + 1) := by
          rw [hRHS, Real.rpow_one]; ring

/-- **`hq11` of `RBM.Step6.sharpExpect_step6`**: `E[(L-K)_1 (L-K)_1] ≺ (W ℓ_u η_u)^{-2}`,
uniformly in `u ∈ [s,t]` and in the two blocks.

The proof is `RBM.Gauss.norm_quad11_le_integral` (the deterministic first step) followed by the
first-moment reverse bridge `RBM.Gauss.unifDetDom_integral_lkErr_mul` applied to (2.78)
(`RBM.Steps.sharpLmK`) at `n = 1`, twice — Step 4's output, available before Step 6. -/
theorem quad11_unifDetDom (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hint : ∀ N (p : TimeIcc s t N × (LoopData (B.L N) 1 × LoopData (B.L N) 1)),
      Integrable (fun ω => X.lkErr E N p.1 ω p.2.1.idx * X.lkErr E N p.1 ω p.2.2.idx) B.P)
    (hsteps : Steps X E s t) :
    UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 1) le_rfl
  have hK1 : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 1),
      ‖B.Kval E N u v.idx‖ ≤ C1 * (B.scale E N u)⁻¹ ^ (1 - 1) :=
    fun N u v => hC1 N u ((hs0 N).le.trans u.2.1) (u.2.2.trans_lt (ht1 N)) v.idx v.idx_wf (by simp)
  have hmain := unifDetDom_integral_lkErr_mul X hE hs0 ht1 (m := 1) (n := 1) le_rfl le_rfl
    hc0 hη hC10 hK1 hK1 hint (hsteps.sharpLmK 1 le_rfl) (hsteps.sharpLmK 1 le_rfl)
  have hre := hmain.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      (p.1, (oneLoopData p.2.1, oneLoopData p.2.2)))
  refine UnifDetDom.mono_left (Filter.Eventually.of_forall fun N p => ?_) hre
  simpa using norm_quad11_le_integral X E N p.1 p.2.1 p.2.2

/-- **`hq13` of `RBM.Step6.sharpExpect_step6`**: `E[(L-K)_1 (L-K)_3] ≺ (W ℓ_u η_u)^{-4}`,
uniformly in `u ∈ [s,t]`, in the block and in the `3`-loop.  Same proof as
`RBM.Gauss.quad11_unifDetDom`, with (2.78) at `n = 1` and at `n = 3`. -/
theorem quad13_unifDetDom (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hint : ∀ N (p : TimeIcc s t N × (LoopData (B.L N) 1 × LoopData (B.L N) 3)),
      Integrable (fun ω => X.lkErr E N p.1 ω p.2.1.idx * X.lkErr E N p.1 ω p.2.2.idx) B.P)
    (hsteps : Steps X E s t) :
    UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      ‖Step6.quad13 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 4) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 1) le_rfl
  obtain ⟨C3, hC30, hC3⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 3) (by norm_num)
  have hCK0 : (0 : ℝ) ≤ max C1 C3 := le_trans hC10 (le_max_left _ _)
  have hK1 : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 1),
      ‖B.Kval E N u v.idx‖ ≤ max C1 C3 * (B.scale E N u)⁻¹ ^ (1 - 1) := by
    intro N u v
    refine (hC1 N u ((hs0 N).le.trans u.2.1) (u.2.2.trans_lt (ht1 N)) v.idx v.idx_wf
      (by simp)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by norm_num)
  have hK3 : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 3),
      ‖B.Kval E N u v.idx‖ ≤ max C1 C3 * (B.scale E N u)⁻¹ ^ (3 - 1) := by
    intro N u v
    refine (hC3 N u ((hs0 N).le.trans u.2.1) (u.2.2.trans_lt (ht1 N)) v.idx v.idx_wf
      (by simp)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  have hmain := unifDetDom_integral_lkErr_mul X hE hs0 ht1 (m := 1) (n := 3) le_rfl (by norm_num)
    hc0 hη hCK0 hK1 hK3 hint (hsteps.sharpLmK 1 le_rfl) (hsteps.sharpLmK 3 (by norm_num))
  have hre := hmain.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × LoopData (B.L N) 3)) =>
      (p.1, (oneLoopData p.2.1, p.2.2)))
  refine UnifDetDom.mono_left (Filter.Eventually.of_forall fun N p => ?_) hre
  simpa using norm_quad13_le_integral X E N p.1 p.2.1 p.2.2

end FirstMoment

/-! ### `hq11`, `hq13` for the Gaussian model: `hint` discharged -/

section FirstMomentGauss

/-- **`hq11` for the Gaussian model, with no integrability hypothesis.**  Identical to
`RBM.Gauss.quad11_unifDetDom` at `X = RBM.Gauss.sample d`, except that its `hint` is supplied by
`RBM.Gauss.integrable_sample_lkErr_mul_real`: both loops are `1`-loops, hence well-formed and of
length `≥ 1`, and `u < 1` comes from `t_N < 1`.

The general-`RBM.Sample` statement is kept: nothing outside the Gaussian model can prove `hint`,
since it rests on the deterministic envelope (5.2) along the flow together with continuity of the
loop in `ω`. -/
theorem quad11_unifDetDom_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hsteps : Steps (sample d) E s t) :
    UnifDetDom
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) =>
        ‖Step6.quad11 (sample d) E N p.1 p.2.1 p.2.2‖)
      (fun N p => ((band d).scale E N p.1)⁻¹ ^ 2) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  refine quad11_unifDetDom (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hη ?_ hsteps
  intro N p
  exact integrable_sample_lkErr_mul_real d N hE (p.1.2.2.trans_lt (ht1 N)) _ _
    p.2.1.idx_wf (by simp [LoopData.idx]) p.2.2.idx_wf (by simp [LoopData.idx])

/-- **`hq13` for the Gaussian model, with no integrability hypothesis.**  Same as
`RBM.Gauss.quad11_unifDetDom_gauss`, with the second loop of length `3`. -/
theorem quad13_unifDetDom_gauss (d : Dims) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT E u)
    (hsteps : Steps (sample d) E s t) :
    UnifDetDom
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × LoopData ((band d).L N) 3)) =>
        ‖Step6.quad13 (sample d) E N p.1 p.2.1 p.2.2‖)
      (fun N p => ((band d).scale E N p.1)⁻¹ ^ 4) := by
  have hE : |E| < 2 := by linarith [abs_nonneg E]
  refine quad13_unifDetDom (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hη ?_ hsteps
  intro N p
  exact integrable_sample_lkErr_mul_real d N hE (p.1.2.2.trans_lt (ht1 N)) _ _
    p.2.1.idx_wf (by simp [LoopData.idx]) p.2.2.idx_wf (by simp [LoopData.idx])

end FirstMomentGauss

end RBM.Gauss
