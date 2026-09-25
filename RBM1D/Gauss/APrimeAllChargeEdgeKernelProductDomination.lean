/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeAllChargeEdgeKernelDomination

/-!
# Entrywise domination for finite time-ordered edge-kernel products

For an ordered list of time intervals and unit phases, the product is formed with
the latest kernel on the left. Its entries are dominated by the corresponding
product with every phase equal to one. This is a finite matrix-product consequence
of the accepted one-edge comparison.
-/

namespace RBM

/-- One interval and its unit phase. -/
structure EdgeKernelSpec where
  s : ℝ
  t : ℝ
  ξ : ℂ

private noncomputable def edgeKernelComplex (L : ℕ) [NeZero L] (e : EdgeKernelSpec) :
    Matrix (ZMod L) (ZMod L) ℂ :=
  edgeKer L e.ξ (e.s : ℂ) (e.t : ℂ)

private noncomputable def edgeKernelOneReal (L : ℕ) [NeZero L] (e : EdgeKernelSpec) :
    Matrix (ZMod L) (ZMod L) ℝ :=
  fun a b => (edgeKer L 1 (e.s : ℂ) (e.t : ℂ) a b).re

/-- Ordered product in chronological-list order: each later kernel multiplies on the left. -/
noncomputable def edgeKernelChain (L : ℕ) [NeZero L] :
    List EdgeKernelSpec → Matrix (ZMod L) (ZMod L) ℂ
  | [] => 1
  | e :: es => edgeKernelChain L es * edgeKernelComplex L e

/-- The corresponding all-unit-phase product, kept over `ℝ` entry by entry. -/
noncomputable def edgeKernelOneRealChain (L : ℕ) [NeZero L] :
    List EdgeKernelSpec → Matrix (ZMod L) (ZMod L) ℝ
  | [] => 1
  | e :: es => edgeKernelOneRealChain L es * edgeKernelOneReal L e

/-- The corresponding complex product with every phase set to one. -/
noncomputable def edgeKernelOneComplexChain (L : ℕ) [NeZero L] :
    List EdgeKernelSpec → Matrix (ZMod L) (ZMod L) ℂ
  | [] => 1
  | e :: es => edgeKernelOneComplexChain L es * edgeKer L 1 (e.s : ℂ) (e.t : ℂ)

private theorem edgeKernelOne_eq_realCast (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (e : EdgeKernelSpec) (hs : 0 ≤ e.s) (hst : e.s ≤ e.t) (ht : e.t < 1)
    (a b : ZMod L) :
    edgeKer L 1 (e.s : ℂ) (e.t : ℂ) a b =
      ((edgeKer L 1 (e.s : ℂ) (e.t : ℂ) a b).re : ℂ) := by
  let z := edgeKer L 1 (e.s : ℂ) (e.t : ℂ) a b
  have hn : ‖z‖ ≤ z.re := by
    exact norm_edgeKer_unit_phase_le_one L hL hs hst ht (ξ := 1) (by norm_num) a b
  have hp : 0 ≤ z.re := by
    exact edgeKer_one_entry_re_nonneg L hL hs hst ht a b
  have heq : ‖z‖ = z.re := le_antisymm hn (Complex.re_le_norm z)
  have hsq : Complex.normSq z = z.re ^ 2 := by
    rw [← Complex.norm_mul_self_eq_normSq, heq]
    ring
  have himSq : z.im ^ 2 = 0 := by
    rw [Complex.normSq_apply] at hsq
    nlinarith
  have him : z.im = 0 := (sq_eq_zero_iff).mp himSq
  change z = (z.re : ℂ)
  exact Complex.ext rfl him

private theorem edgeKernelOneComplexChain_eq_realCast (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (es : List EdgeKernelSpec)
    (hvalid : ∀ e ∈ es, 0 ≤ e.s ∧ e.s ≤ e.t ∧ e.t < 1)
    (a b : ZMod L) :
    edgeKernelOneComplexChain L es a b = (edgeKernelOneRealChain L es a b : ℂ) := by
  induction es generalizing a b with
  | nil =>
      by_cases hab : a = b <;>
        simp [edgeKernelOneComplexChain, edgeKernelOneRealChain, Matrix.one_apply, hab]
  | cons e es ih =>
      have he := hvalid e (by simp)
      have hrest : ∀ f ∈ es, 0 ≤ f.s ∧ f.s ≤ f.t ∧ f.t < 1 := by
        intro f hf
        exact hvalid f (by simp [hf])
      change (∑ c : ZMod L,
          edgeKernelOneComplexChain L es a c * edgeKer L 1 (e.s : ℂ) (e.t : ℂ) c b)
        = ((∑ c : ZMod L,
          edgeKernelOneRealChain L es a c * edgeKernelOneReal L e c b : ℝ) : ℂ)
      calc
        _ = ∑ c : ZMod L,
            ((edgeKernelOneRealChain L es a c : ℂ) *
              (edgeKernelOneReal L e c b : ℂ)) := by
                apply Finset.sum_congr rfl
                intro c hc
                rw [ih hrest a c, edgeKernelOne_eq_realCast L hL e he.1 he.2.1 he.2.2 c b]
                simp [edgeKernelOneReal]
        _ = ∑ c : ZMod L,
              ((edgeKernelOneRealChain L es a c * edgeKernelOneReal L e c b : ℝ) : ℂ) := by
                apply Finset.sum_congr rfl
                intro c hc
                rw [edgeKernelOneReal]
                rw [← Complex.ofReal_mul]
        _ = ((∑ c : ZMod L,
            edgeKernelOneRealChain L es a c * edgeKernelOneReal L e c b : ℝ) : ℂ) := by
              exact (Complex.ofReal_sum (Finset.univ : Finset (ZMod L)) _).symm

private theorem edgeKernelChain_bound_and_nonneg (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) (es : List EdgeKernelSpec)
    (hvalid : ∀ e ∈ es, 0 ≤ e.s ∧ e.s ≤ e.t ∧ e.t < 1 ∧ ‖e.ξ‖ = 1) :
    ∀ a b : ZMod L,
      ‖edgeKernelChain L es a b‖ ≤ edgeKernelOneRealChain L es a b ∧
        0 ≤ edgeKernelOneRealChain L es a b := by
  induction es with
  | nil =>
      intro a b
      constructor
      · by_cases hab : a = b <;>
          simp [edgeKernelChain, edgeKernelOneRealChain, Matrix.one_apply, hab]
      · by_cases hab : a = b <;>
          simp [edgeKernelOneRealChain, Matrix.one_apply, hab]
    | cons e es ih =>
      have he := hvalid e (by simp)
      have hrest : ∀ f ∈ es, 0 ≤ f.s ∧ f.s ≤ f.t ∧ f.t < 1 ∧ ‖f.ξ‖ = 1 := by
        intro f hf
        exact hvalid f (by simp [hf])
      intro a b
      constructor
      · rw [edgeKernelChain, edgeKernelOneRealChain]
        simp only [Matrix.mul_apply]
        calc
          ‖∑ c : ZMod L,
              edgeKernelChain L es a c * edgeKernelComplex L e c b‖
              ≤ ∑ c : ZMod L,
                  ‖edgeKernelChain L es a c * edgeKernelComplex L e c b‖ := norm_sum_le _ _
          _ = ∑ c : ZMod L,
                ‖edgeKernelChain L es a c‖ * ‖edgeKernelComplex L e c b‖ := by
                  apply Finset.sum_congr rfl
                  intro c hc
                  rw [Complex.norm_mul]
          _ ≤ ∑ c : ZMod L,
                edgeKernelOneRealChain L es a c * edgeKernelOneReal L e c b := by
                  apply Finset.sum_le_sum
                  intro c hc
                  have hprev := ih hrest a c
                  have hedge := norm_edgeKer_unit_phase_le_one L hL
                    he.1 he.2.1 he.2.2.1 he.2.2.2 c b
                  calc
                    ‖edgeKernelChain L es a c‖ * ‖edgeKernelComplex L e c b‖
                        ≤ edgeKernelOneRealChain L es a c *
                            ‖edgeKernelComplex L e c b‖ :=
                              mul_le_mul_of_nonneg_right hprev.1 (norm_nonneg _)
                    _ ≤ edgeKernelOneRealChain L es a c * edgeKernelOneReal L e c b :=
                          mul_le_mul_of_nonneg_left hedge hprev.2
          _ = ∑ c : ZMod L,
                edgeKernelOneRealChain L es a c * edgeKernelOneReal L e c b := rfl
      · change 0 ≤ (edgeKernelOneRealChain L es * edgeKernelOneReal L e) a b
        rw [Matrix.mul_apply]
        exact Finset.sum_nonneg fun c hc =>
          mul_nonneg (ih hrest a c).2
            (edgeKer_one_entry_re_nonneg L hL he.1 he.2.1 he.2.2.1 c b)

/-- Every finite ordered product is entrywise dominated by the all-unit-phase product.

The list is chronological and the latest edge multiplies on the left. The right hand
side is written as the real entry of the complex all-unit-phase matrix product.
-/
theorem norm_edgeKernelChain_le_allOne (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (es : List EdgeKernelSpec)
    (hvalid : ∀ e ∈ es, 0 ≤ e.s ∧ e.s ≤ e.t ∧ e.t < 1 ∧ ‖e.ξ‖ = 1)
    (a b : ZMod L) :
    ‖edgeKernelChain L es a b‖ ≤ (edgeKernelOneComplexChain L es a b).re := by
  have hbound := edgeKernelChain_bound_and_nonneg L hL es hvalid a b
  have htime : ∀ e ∈ es, 0 ≤ e.s ∧ e.s ≤ e.t ∧ e.t < 1 := by
    intro e he
    exact ⟨(hvalid e he).1, (hvalid e he).2.1, (hvalid e he).2.2.1⟩
  have hreal := edgeKernelOneComplexChain_eq_realCast L hL es htime a b
  calc
    ‖edgeKernelChain L es a b‖ ≤ edgeKernelOneRealChain L es a b := hbound.1
    _ = (edgeKernelOneComplexChain L es a b).re := by
      rw [hreal]
      simp

/-- The comparison product is nonnegative, including the empty-chain identity case. -/
theorem edgeKernelOneRealChain_nonneg (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (es : List EdgeKernelSpec)
    (hvalid : ∀ e ∈ es, 0 ≤ e.s ∧ e.s ≤ e.t ∧ e.t < 1)
    (a b : ZMod L) : 0 ≤ edgeKernelOneRealChain L es a b := by
  induction es generalizing a b with
  | nil =>
      by_cases hab : a = b <;> simp [edgeKernelOneRealChain, Matrix.one_apply, hab]
  | cons e es ih =>
      have he := hvalid e (by simp)
      have hrest : ∀ f ∈ es, 0 ≤ f.s ∧ f.s ≤ f.t ∧ f.t < 1 := by
        intro f hf
        exact hvalid f (by simp [hf])
      change 0 ≤ (edgeKernelOneRealChain L es * edgeKernelOneReal L e) a b
      rw [Matrix.mul_apply]
      exact Finset.sum_nonneg fun c hc =>
      mul_nonneg (ih hrest a c)
          (edgeKer_one_entry_re_nonneg L hL he.1 he.2.1 he.2.2 c b)

/-- The entry of the all-unit-phase complex product is real and nonnegative. -/
theorem edgeKernelOneComplexChain_re_nonneg (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (es : List EdgeKernelSpec)
    (hvalid : ∀ e ∈ es, 0 ≤ e.s ∧ e.s ≤ e.t ∧ e.t < 1)
    (a b : ZMod L) : 0 ≤ (edgeKernelOneComplexChain L es a b).re := by
  have hreal := edgeKernelOneComplexChain_eq_realCast L hL es hvalid a b
  rw [hreal]
  exact edgeKernelOneRealChain_nonneg L hL es hvalid a b

end RBM
