/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2

/-!
# (5.42) via M7a plus convolution: the weighted variance bound through `Uker` (T1509)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, the lossless route of
`docs/supervisor/2026-09-25-2004.md` §4 and `2045.md` §3 for (5.42): the entrywise
nonnegativity of the unit-charge kernel `Uker L (fun _ => 1) u v` (from the Neumann series of
`Θ_v`, `RBM.Theta_eq_tsum`), and its consequence, that a convolution against the M7a
(`RBM.Gauss.norm_EEpath_offDiag_sq_le`, `Gauss/EEOffDiag.lean`) shape can be pushed through
`Uker` with no extra loss beyond the already-accepted kernel bound
`RBM.norm_Uker_le_of_tail` (`Hierarchy/Step2.lean:448`).

## Main declarations

* `RBM.Gauss.Grid.Uker_one_nonneg` — **(T1)**: every kernel entry of `Uker L (fun _ => 1) u v`,
  `0 ≤ u ≤ v < 1`, is a nonnegative real.
* `RBM.Gauss.Grid.qv_conv_le` — **(T2)**: the weighted quadratic-variation bound through
  `Uker`, from the M7a Cauchy–Schwarz shape and `RBM.norm_Uker_le_of_tail`.
-/

namespace RBM
namespace Gauss
namespace Grid

open Matrix

/-! ### A local algebra of nonnegative-real complex numbers -/

/-- `z` is a nonnegative real number, viewed inside `ℂ`. Purely a bookkeeping device for the
entrywise sign arguments below; not part of the public API. -/
private def IsRealNonneg (z : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

private theorem IsRealNonneg.ofNonneg {r : ℝ} (hr : 0 ≤ r) : IsRealNonneg (r : ℂ) := ⟨r, hr, rfl⟩

private theorem isRealNonneg_zero : IsRealNonneg (0 : ℂ) := ⟨0, le_refl _, by simp⟩

private theorem isRealNonneg_one : IsRealNonneg (1 : ℂ) := ⟨1, zero_le_one, by simp⟩

private theorem IsRealNonneg.add {z w : ℂ} (hz : IsRealNonneg z) (hw : IsRealNonneg w) :
    IsRealNonneg (z + w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 + r2, by positivity, by rw [e1, e2]; push_cast; ring⟩

private theorem IsRealNonneg.mul {z w : ℂ} (hz : IsRealNonneg z) (hw : IsRealNonneg w) :
    IsRealNonneg (z * w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 * r2, mul_nonneg hr1 hr2, by rw [e1, e2]; push_cast; ring⟩

private theorem IsRealNonneg.eq_ofReal_re {z : ℂ} (hz : IsRealNonneg z) : z = (z.re : ℂ) := by
  obtain ⟨r, _, e⟩ := hz; rw [e]; simp

private theorem IsRealNonneg.re_nonneg {z : ℂ} (hz : IsRealNonneg z) : 0 ≤ z.re := by
  obtain ⟨r, hr, e⟩ := hz; rw [e]; simpa using hr

private theorem IsRealNonneg.norm_eq {z : ℂ} (hz : IsRealNonneg z) : ‖z‖ = z.re := by
  obtain ⟨r, hr, e⟩ := hz
  rw [e, Complex.norm_of_nonneg hr, Complex.ofReal_re]

private theorem IsRealNonneg.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsRealNonneg (f i)) : IsRealNonneg (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsRealNonneg (fun _ _ ha hb => ha.add hb) isRealNonneg_zero h

private theorem IsRealNonneg.prod {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsRealNonneg (f i)) : IsRealNonneg (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsRealNonneg (fun _ _ ha hb => ha.mul hb) isRealNonneg_one h

private theorem IsRealNonneg.tsum {f : ℕ → ℂ} (hf : Summable f)
    (h : ∀ n, IsRealNonneg (f n)) : IsRealNonneg (∑' n, f n) := by
  have hnn : ∀ n, 0 ≤ (f n).re := fun n => (h n).re_nonneg
  have hcast : ∀ n, f n = ((f n).re : ℂ) := fun n => (h n).eq_ofReal_re
  have hnormeq : ∀ n, ‖f n‖ = (f n).re := fun n => (h n).norm_eq
  have hreSummable : Summable (fun n => (f n).re) := by
    have hns := hf.norm
    simpa only [hnormeq] using hns
  refine ⟨∑' n, (f n).re, tsum_nonneg hnn, ?_⟩
  calc ∑' n, f n = ∑' n, ((f n).re : ℂ) := tsum_congr hcast
    _ = ((∑' n, (f n).re : ℝ) : ℂ) := (Complex.ofReal_tsum _).symm

variable {L : ℕ} [NeZero L]

/-! ### Nonnegativity of `S^(B)`, its powers, and `Θ_v` for real `v ∈ [0,1)` -/

omit [NeZero L] in
private theorem SB_isRealNonneg (a b : ZMod L) : IsRealNonneg (SB L a b) := by
  rw [SB_apply]
  unfold sbKernel
  split_ifs
  · exact ⟨(3 : ℝ)⁻¹, by norm_num, by push_cast; ring⟩
  · exact isRealNonneg_zero

private theorem SBpow_isRealNonneg :
    ∀ k : ℕ, ∀ a b : ZMod L, IsRealNonneg ((SB L ^ k) a b) := by
  intro k
  induction k with
  | zero =>
      intro a b
      rw [pow_zero, Matrix.one_apply]
      split_ifs
      · exact isRealNonneg_one
      · exact isRealNonneg_zero
  | succ k ih =>
      intro a b
      rw [pow_succ, Matrix.mul_apply]
      exact IsRealNonneg.sum Finset.univ _ (fun c _ => (ih a c).mul (SB_isRealNonneg c b))

private theorem theta_entries_summable (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) (a b : ZMod L) :
    Summable (fun k : ℕ => ((z • SB L) ^ k) a b) := by
  have hpow := summable_norm_pow L hL hz
  have hnorm : Summable (fun k : ℕ => ‖((z • SB L) ^ k) a b‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_entry_le_norm L _ a b) hpow
  exact hnorm.of_norm

private theorem theta_apply_eq_tsum (hL : 3 ≤ L) {z : ℂ} (hz : ‖z‖ < 1) (a b : ZMod L) :
    Theta L z a b = ∑' k : ℕ, ((z • SB L) ^ k) a b := by
  have hentries : ∀ a b : ZMod L, Summable (fun k : ℕ => ((z • SB L) ^ k) a b) :=
    fun a b => theta_entries_summable hL hz a b
  have hrows : ∀ a : ZMod L, Summable (fun k : ℕ => ((z • SB L) ^ k) a) :=
    fun a => Pi.summable.mpr (fun b => hentries a b)
  have hmat : Summable (fun k : ℕ => (z • SB L) ^ k) := Pi.summable.mpr hrows
  rw [Theta_eq_tsum L hL hz]
  have h1 := congrFun (Pi.tsum_apply (x := a) hmat) b
  have h2 := Pi.tsum_apply (x := b) (hrows a)
  exact h1.trans h2

private theorem Theta_real_isRealNonneg (hL : 3 ≤ L) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (a b : ZMod L) : IsRealNonneg (Theta L (v : ℂ) a b) := by
  have hvNorm : ‖(v : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]; exact hv1
  rw [theta_apply_eq_tsum hL hvNorm a b]
  refine IsRealNonneg.tsum (theta_entries_summable hL hvNorm a b) (fun k => ?_)
  have hterm : (((v : ℂ) • SB L) ^ k) a b = (v : ℂ) ^ k * (SB L ^ k) a b := by
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  rw [hterm]
  have hcoef : IsRealNonneg ((v : ℂ) ^ k) := ⟨v ^ k, pow_nonneg hv0 k, by push_cast; ring⟩
  exact hcoef.mul (SBpow_isRealNonneg k a b)

private theorem SB_mul_Theta_real_isRealNonneg (hL : 3 ≤ L) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (a b : ZMod L) : IsRealNonneg ((SB L * Theta L (v : ℂ)) a b) := by
  rw [Matrix.mul_apply]
  exact IsRealNonneg.sum Finset.univ _
    (fun c _ => (SB_isRealNonneg a c).mul (Theta_real_isRealNonneg hL hv0 hv1 c b))

/-- **The corrected edge kernel `edgeKer L 1 u v = 1 + (v-u) • (S^(B) Θ_v)` is entrywise a
nonnegative real**, for `0 ≤ u ≤ v < 1`. -/
private theorem edgeKer_one_isRealNonneg (hL : 3 ≤ L) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v)
    (hv1 : v < 1) (a b : ZMod L) : IsRealNonneg (edgeKer L 1 (u : ℂ) (v : ℂ) a b) := by
  have hv0 : 0 ≤ v := hu0.trans huv
  have hvξ : ‖(v : ℂ) * (1 : ℂ)‖ < 1 := by
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]; exact hv1
  have hkey := edgeKer_eq (ξ := (1 : ℂ)) (s := (u : ℂ)) (t := (v : ℂ)) L hL hvξ
  have hentry := congrFun (congrFun hkey a) b
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_one] at hentry
  rw [hentry, sub_eq_add_neg]
  have hone : IsRealNonneg ((1 : Matrix (ZMod L) (ZMod L) ℂ) a b) := by
    rw [Matrix.one_apply]
    split_ifs
    · exact isRealNonneg_one
    · exact isRealNonneg_zero
  refine hone.add ?_
  obtain ⟨r, hr, hreq⟩ := SB_mul_Theta_real_isRealNonneg hL hv0 hv1 a b
  have hneg : -(((u : ℂ) - (v : ℂ)) * (SB L * Theta L (v : ℂ)) a b) = (((v - u) * r : ℝ) : ℂ) := by
    rw [hreq]; push_cast; ring
  rw [hneg]
  exact IsRealNonneg.ofNonneg (mul_nonneg (by linarith) hr)

/-! ### (T1) -/

/-- **(T1)**: for `0 ≤ u ≤ v < 1`, every kernel entry of `Uker L (fun _ => 1) u v` — i.e. every
value `∏ i, edgeKer L 1 u v (a i) (b i)` appearing in `Uker_apply` — is a nonnegative real. -/
theorem Uker_one_nonneg (hL : 3 ≤ L) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (a b : LoopArg L 2) :
    ∃ r : ℝ, 0 ≤ r ∧ (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (a i) (b i)) = (r : ℂ) :=
  IsRealNonneg.prod Finset.univ _
    (fun i _ => edgeKer_one_isRealNonneg hL hu0 huv hv1 (a i) (b i))

/-! ### The bridge lemma used by (T2): the triangle-inequality sum against a kernel with
nonnegative-real entries equals `‖Uker … b‖` exactly, with no loss. -/

private theorem sum_edgeProd_mul_ofReal_norm_eq (hL : 3 ≤ L) {u v : ℝ} (hu0 : 0 ≤ u)
    (huv : u ≤ v) (hv1 : v < 1) (x : LoopArg L 2) (c : LoopArg L 2 → ℝ)
    (hc : ∀ y, 0 ≤ c y) :
    ‖∑ y : LoopArg L 2,
        (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)) * (c y : ℂ)‖
      = ∑ y : LoopArg L 2,
          ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)‖ * c y := by
  have hterm : ∀ y : LoopArg L 2,
      (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)) * (c y : ℂ)
        = ((‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)‖ * c y : ℝ) : ℂ) := by
    intro y
    obtain ⟨r, hr, e⟩ :=
      IsRealNonneg.prod Finset.univ (fun i => edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i))
        (fun i _ => edgeKer_one_isRealNonneg hL hu0 huv hv1 (x i) (y i))
    have hnr : ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)‖ = r := by
      rw [e, Complex.norm_of_nonneg hr]
    rw [hnr, e]; push_cast; ring
  calc ‖∑ y : LoopArg L 2,
        (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)) * (c y : ℂ)‖
      = ‖((∑ y : LoopArg L 2,
          ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)‖ * c y : ℝ) : ℂ)‖ := by
        rw [Complex.ofReal_sum]
        exact congrArg norm (Finset.sum_congr rfl fun y _ => hterm y)
    _ = ∑ y : LoopArg L 2, ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (x i) (y i)‖ * c y := by
        rw [Complex.norm_of_nonneg
          (Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (hc y))]

/-! ### (T2) -/

/-- **(T2)**: the weighted quadratic-variation bound through `Uker`, from the M7a
Cauchy–Schwarz shape (`‖EE a a'‖ ≤ √(R a) √(R a')`, `R a ≤ Q · T_u(dist a)²`) and
`RBM.norm_Uker_le_of_tail`. No loss beyond `xiK` (the already-accepted `W^{o(1)}` factor of
that dependency) is introduced: no `e^λ`, no widened indicator. -/
theorem qv_conv_le (hL : 3 ≤ L) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) {u v : ℝ} (hu0 : 0 ≤ u)
    (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1) {W D Q : ℝ} (hW : Real.exp 1 ≤ W) (hQ : 0 ≤ Q)
    (hAuv : W * ellHat L (v : ℂ) * ((1 - v) * m) ≤ W * ellHat L (u : ℂ) * ((1 - u) * m))
    {R : LoopArg L 2 → ℝ} (_hR0 : ∀ a, 0 ≤ R a)
    (hR : ∀ a, R a ≤ Q *
        (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (a 0 - a 1))) ^ 2)
    {EE : LoopArg L 2 → LoopArg L 2 → ℂ}
    (hEE : ∀ a a' : LoopArg L 2, ‖EE a a'‖ ≤ Real.sqrt (R a) * Real.sqrt (R a'))
    (b : LoopArg L 2) :
    ‖∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
        (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) *
          (starRingEnd ℂ) (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)) *
          EE a a'‖
      ≤ (Real.sqrt Q * ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
          tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (b 0 - b 1))) ^ 2 := by
  set c : LoopArg L 2 → ℝ := fun a => Real.sqrt (R a) with hc_def
  have hc_nonneg : ∀ a, 0 ≤ c a := fun a => Real.sqrt_nonneg _
  -- Step 1: triangle inequality.
  have hstep1 :
      ‖∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) *
            (starRingEnd ℂ) (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)) * EE a a'‖
        ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
            ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ *
              ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * ‖EE a a'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    exact le_of_eq (by rw [norm_mul, norm_mul, Complex.norm_conj])
  -- Step 2: the M7a hypothesis, termwise.
  have hstep2 :
      (∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ *
            ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * ‖EE a a'‖)
        ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
            (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a) *
              (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * c a') := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ => ?_
    have hnn1 : (0:ℝ) ≤ ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ *
        ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ := by positivity
    calc ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ *
          ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * ‖EE a a'‖
        ≤ ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ *
            ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * (c a * c a') :=
          mul_le_mul_of_nonneg_left (hEE a a') hnn1
      _ = (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a) *
            (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * c a') := by ring
  -- Step 3: factor the double sum.
  have hstep3 :
      (∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a) *
            (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * c a'))
        = (∑ a : LoopArg L 2,
            ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a) ^ 2 := by
    rw [sq, Fintype.sum_mul_sum]
  -- Step 4: identify the sum with `‖Uker … b‖`, using (T1).
  have hnormUker :
      ‖∑ a : LoopArg L 2,
          (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) * (c a : ℂ)‖
        = ∑ a : LoopArg L 2, ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a :=
    sum_edgeProd_mul_ofReal_norm_eq hL hu0 huv hv1 b c hc_nonneg
  have hUkerApply :
      Uker L (fun _ : Fin 2 => (1 : ℂ)) (u : ℂ) (v : ℂ) (fun a => (c a : ℂ)) b
        = ∑ a : LoopArg L 2,
            (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) * (c a : ℂ) :=
    Uker_apply L (fun _ : Fin 2 => (1 : ℂ)) (u : ℂ) (v : ℂ) (fun a => (c a : ℂ)) b
  -- Step 5: `norm_Uker_le_of_tail`.
  have hA_tail : ∀ a : LoopArg L 2, ‖(c a : ℂ)‖ ≤ Real.sqrt Q *
      tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (a 0 - a 1)) := by
    intro a
    rw [Complex.norm_of_nonneg (hc_nonneg a)]
    have htnn : 0 ≤ tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (a 0 - a 1)) :=
      tailT_nonneg (le_trans (Real.exp_pos 1).le hW) _
    calc c a = Real.sqrt (R a) := rfl
      _ ≤ Real.sqrt (Q *
            (tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (a 0 - a 1))) ^ 2) :=
          Real.sqrt_le_sqrt (hR a)
      _ = Real.sqrt Q * tailT W (ellHat L (u : ℂ)) ((1 - u) * m) D (zdist L (a 0 - a 1)) := by
          rw [Real.sqrt_mul hQ, Real.sqrt_sq htnn]
  have hfinal := Step2.norm_Uker_le_of_tail hL hm0 hm1 hu0 huv hv0 hv1 hW (Real.sqrt_nonneg Q)
    hAuv hA_tail b
  rw [← hUkerApply] at hnormUker
  calc ‖∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)) *
            (starRingEnd ℂ) (∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)) * EE a a'‖
      ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ *
            ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * ‖EE a a'‖ := hstep1
    _ ≤ ∑ a : LoopArg L 2, ∑ a' : LoopArg L 2,
          (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a) *
            (‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a' i)‖ * c a') := hstep2
    _ = (∑ a : LoopArg L 2, ‖∏ i : Fin 2, edgeKer L 1 (u : ℂ) (v : ℂ) (b i) (a i)‖ * c a) ^ 2 :=
        hstep3
    _ = ‖Uker L (fun _ : Fin 2 => (1 : ℂ)) (u : ℂ) (v : ℂ) (fun a => (c a : ℂ)) b‖ ^ 2 := by
        rw [hnormUker]
    _ ≤ (Real.sqrt Q * ((1 - u) / (1 - v)) ^ 2 * Step2.xiK L W m *
          tailT W (ellHat L (v : ℂ)) ((1 - v) * m) D (zdist L (b 0 - b 1))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hfinal 2

end Grid
end Gauss
end RBM
