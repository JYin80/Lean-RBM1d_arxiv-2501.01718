/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Model
import RBM1D.Flow.Consequences
import RBM1D.Loop.ContinuityAssembly

/-!
# The identities in law (2.39), (2.66), (6.1) for the Gaussian model

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 2.8 ((2.39), (2.66)) and (6.1).

In the paper these three statements are justified by *equality in distribution up to a
deterministic scaling*.  In the moment route of `RBM1D/Gauss/Model.lean` the flow is
`H_u = √u • X` with **one fixed** Gaussian band matrix `X`, so the two sides of each of the
three statements are deterministic scalings of **the same** sample point `ω`: no distributional
argument is needed at all, and the identities become algebraic identities of resolvents.

## The algebraic core

`RBM.green (c • H) (c z) = c⁻¹ • RBM.green H z` for `c ≠ 0` (`RBM.Gauss.green_smul_mul`), hence
for real `c` the same for `RBM.Gsig` and, taking `n` factors and a trace,
`RBM.gloop (c • H) (c z) I = c⁻ⁿ · RBM.gloop H z I` (`RBM.Gauss.gloop_smul_mul`).

* **(2.39)/(2.66)**: with `E = lemE z`, `t = lemT z` and `z_t^{(E)} = t^{1/2} z` (2.37,
  `RBM.eq_inv_sqrt_mul_zt`), `H_t = t^{1/2} X`, so
  `G_t^{(E)}(ω) = t^{-1/2} (X(ω) - z)⁻¹`, i.e. `t^{1/2} G_t^{(E)} = G(z)` with `H := X`,
  **pointwise in `ω`** (`RBM.Gauss.green_Hflow_lemT_eq`).  The `n`-loop version gives
  `t^{n/2} L_{t,σ,a} = ` the `n`-loop of `G(z)` (`RBM.Gauss.gloop_Hflow_lemT_eq`), which is
  (2.66) for `n = 2` and the 1-loop identity used for (2.4) for `n = 1`.
* **(6.1)**: `H_{t₂} = (t₂/t₁)^{1/2} H_{t₁}` and `z̃_{t₁} = (t₂/t₁)^{1/2} z_{t₁}`, so the loops
  of `G̃_{t₁}` are `(t₁/t₂)^{n/2} L_{t₁,σ,a}` pointwise, and `(t₁/t₂)^{n/2} ≤ 1`
  (`RBM.Gauss.gloop_Hflow_ztTilde_eq`).

## Main results

* `RBM.Gauss.transfer_gauss` : the `RBM.Transfer` of `RBM.Gauss.sample`, with `Hband = X`.
* `RBM.Gauss.transferLoop1_gauss` : the `RBM.TransferLoop1` of `RBM.Gauss.transfer_gauss`.
* `RBM.Gauss.loopScaling_gauss` : the `RBM.LoopScaling` of `RBM.Gauss.sample`, for
  `0 < t₁ ≤ t₂`.

## Deviations from the paper

* `RBM.Gauss.loopScaling_gauss` carries the hypotheses `0 < t₁ N` and `t₁ N ≤ t₂ N`.  The
  paper uses (6.1) only for `1/2 ≤ t₁ ≤ t₂ < 1` (§6), where both hold, and `RBM.lemma_5_1`
  supplies them from its own `0 < c ≤ t₁ ≤ t₂`.  They are needed because `(t₂/t₁)^{1/2}` is
  meaningless otherwise.
* Nothing here proves that the flow of the moment route is a matrix Brownian motion; it is not.
  This is the deviation already recorded for `RBM1D/Gauss/Model.lean`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix
open scoped NNReal ENNReal

/-! ### Scaling of the resolvent -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar, with no invertibility assumption on `A`
(`Matrix.inv_smul` needs `IsUnit A.det`; when `A` is singular both sides are `0`). -/
theorem inv_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (A : Matrix n n ℂ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- **The scaling of the Green function**: `G(cH, cz) = c⁻¹ G(H, z)`. -/
theorem green_smul_mul {c : ℂ} (hc : c ≠ 0) (H : Matrix n n ℂ) (z : ℂ) :
    RBM.green (c • H) (c * z) = c⁻¹ • RBM.green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix n n ℂ) = c • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold RBM.green
  rw [hsub, inv_smul_of_ne_zero hc]

/-- The same for `RBM.Gsig`: the scalar must be **real**, so that it commutes with the
conjugation of the `σ = false` branch. -/
theorem Gsig_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0) (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) :
    RBM.Gsig ((r : ℂ) • H) ((r : ℂ) * z) σ = ((r : ℂ))⁻¹ • RBM.Gsig H z σ := by
  cases σ with
  | true => simpa only [RBM.Gsig_true] using green_smul_mul hr H z
  | false =>
    rw [RBM.Gsig_false, RBM.Gsig_false, map_mul, Complex.conj_ofReal]
    exact green_smul_mul hr H _

end Algebra

section LoopAlgebra

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `∏ G(cH, cz)(σ_i) E_{a_i} = c⁻ⁿ ∏ G(H, z)(σ_i) E_{a_i}`. -/
theorem gloopProd_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : RBM.LoopIdx (ZMod L)) :
    RBM.gloopProd L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = (((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length) • RBM.gloopProd L W H z I := by
  obtain ⟨σ, a⟩ := I
  induction σ generalizing a with
  | nil => simp [RBM.gloopProd]
  | cons s σ ih =>
    cases a with
    | nil => simp [RBM.gloopProd]
    | cons b a =>
      rw [RBM.gloopProd_cons, RBM.gloopProd_cons, Gsig_smul_mul hr, ih, smul_mul_assoc,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      simp only [List.zip_cons_cons, List.length_cons]
      congr 1
      ring

/-- **The scaling of the `n`-`G` loop**: `L(cH, cz) = c⁻ⁿ L(H, z)`. -/
theorem gloop_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : RBM.LoopIdx (ZMod L)) :
    RBM.gloop L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * RBM.gloop L W H z I := by
  unfold RBM.gloop
  rw [gloopProd_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

end LoopAlgebra

/-! ### (2.37) in multiplicative form -/

/-- **(2.37)** read forwards: `z_t^{(E)} = t^{1/2} z` for `E = lemE z`, `t = lemT z`. -/
theorem zt_eq_sqrt_lemT_mul {z : ℂ} (hz : 0 < z.im) :
    RBM.zt (RBM.lemE z) (RBM.lemT z) = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) * z := by
  have hs : ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RBM.lemT_pos hz)).ne'
  calc RBM.zt (RBM.lemE z) (RBM.lemT z)
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) *
          (((Real.sqrt (RBM.lemT z) : ℝ) : ℂ)⁻¹ * RBM.zt (RBM.lemE z) (RBM.lemT z)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) * z := by rw [← RBM.eq_inv_sqrt_mul_zt hz]

theorem sqrt_lemT_ne_zero {z : ℂ} (hz : 0 < z.im) :
    ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (RBM.lemT_pos hz)).ne'

/-! ### (2.39) and (2.66) for the Gaussian model

`H_t = t^{1/2} X` and `z_t^{(E)} = t^{1/2} z`, so `t^{1/2} G_t^{(E)} = (X - z)⁻¹` pointwise. -/

variable (d : Dims)

/-- **(2.39) pointwise**, entrywise: `G(X(ω), z)_{ij} = t^{1/2} (G_t^{(E)}(ω))_{ij}`, an
*equality*, not merely an equality in law. -/
theorem green_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d) (i j : d.Idx N) :
    RBM.green (Xmat d N ω) z i j
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) *
        RBM.green (Hflow d N (RBM.lemT z) ω) (RBM.zt (RBM.lemE z) (RBM.lemT z)) i j := by
  have hs := sqrt_lemT_ne_zero hz
  have hmat : RBM.green (Hflow d N (RBM.lemT z) ω) (RBM.zt (RBM.lemE z) (RBM.lemT z))
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ)⁻¹ • RBM.green (Xmat d N ω) z := by
    rw [zt_eq_sqrt_lemT_mul hz, show Hflow d N (RBM.lemT z) ω
        = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • Xmat d N ω from rfl, green_smul_mul hs]
  rw [hmat, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

/-- **(2.66) pointwise**, for a loop of any length `n`: the `n`-loop of `G(X(ω), z)` is
`t^{n/2} L_{t,σ,a}(ω)`. -/
theorem gloop_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d)
    (σ : List Bool) (a : List (ZMod (d.L N))) :
    RBM.gloop (d.L N) (d.W N) (Xmat d N ω) z ⟨σ, a⟩
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) ^ (σ.zip a).length *
        RBM.gloop (d.L N) (d.W N) (Hflow d N (RBM.lemT z) ω)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨σ, a⟩ := by
  have hs := sqrt_lemT_ne_zero hz
  rw [zt_eq_sqrt_lemT_mul hz, show Hflow d N (RBM.lemT z) ω
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) • Xmat d N ω from rfl, gloop_smul_mul hs]
  show _ = _ * ((((Real.sqrt (RBM.lemT z) : ℝ) : ℂ))⁻¹ ^ (σ.zip a).length * _)
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]

/-- **(2.39) for the 1-`G` loop**, pointwise: `Tr G(z) E_a = t^{1/2} L_{t,+,a}`. -/
theorem gloop_one_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d)
    (a : ZMod (d.L N)) :
    RBM.gloop (d.L N) (d.W N) (Xmat d N ω) z ⟨[true], [a]⟩
      = ((Real.sqrt (RBM.lemT z) : ℝ) : ℂ) *
        RBM.gloop (d.L N) (d.W N) (Hflow d N (RBM.lemT z) ω)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨[true], [a]⟩ := by
  have hlen : (([true] : List Bool).zip [a]).length = 1 := rfl
  rw [gloop_Hflow_lemT_eq d N hz ω [true] [a], hlen, pow_one]

/-- **(2.66)** for the 2-`G` loop, pointwise:
`Tr G(z) E_a G(z)^{(σ₂)} E_b = t · L_{t,(+,σ₂),(a,b)}`. -/
theorem gloop_two_Hflow_lemT_eq (N : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : Ω d) (σ₂ : Bool)
    (a b : ZMod (d.L N)) :
    RBM.gloop (d.L N) (d.W N) (Xmat d N ω) z ⟨[true, σ₂], [a, b]⟩
      = ((RBM.lemT z : ℝ) : ℂ) *
        RBM.gloop (d.L N) (d.W N) (Hflow d N (RBM.lemT z) ω)
          (RBM.zt (RBM.lemE z) (RBM.lemT z)) ⟨[true, σ₂], [a, b]⟩ := by
  have hlen : (([true, σ₂] : List Bool).zip [a, b]).length = 2 := rfl
  rw [gloop_Hflow_lemT_eq d N hz ω [true, σ₂] [a, b], hlen, ← Complex.ofReal_pow,
    Real.sq_sqrt (RBM.lemT_pos hz).le]

/-! ### The `RBM.Transfer` of the Gaussian model -/

/-- **The band matrix and the identities in law (2.39), (2.66)** for the moment route.
The band matrix is `X` itself and every field is an *equality* of random variables, so the
transfer of `≺`-bounds is a rewriting. -/
noncomputable def transfer_gauss : RBM.Transfer (sample d) where
  Hband := fun N ω => Xmat d N ω
  hermitian := fun N ω => Xmat_isHermitian d N ω
  green := by
    intro z hz c ζ h
    refine RBM.StochDom.of_le_left (fun N ij ω => le_of_eq ?_) h
    congr 2
    exact green_Hflow_lemT_eq d N (hz N) ω ij.1 ij.2
  loop2 := by
    intro z hz σ₂ c ζ h
    refine RBM.StochDom.of_le_left (fun N ab ω => le_of_eq ?_) h
    congr 2
    exact gloop_two_Hflow_lemT_eq d N (hz N) ω σ₂ ab.1 ab.2
  loop2_expect := by
    intro z hz σ₂ N a b
    have key : ∀ ω : Ω d,
        RBM.gloop (d.L N) (d.W N) (Xmat d N ω) (z N) ⟨[true, σ₂], [a, b]⟩
          = ((RBM.lemT (z N) : ℝ) : ℂ) *
            (sample d).Lval (RBM.lemE (z N)) N (RBM.lemT (z N)) ω ⟨[true, σ₂], [a, b]⟩ :=
      fun ω => gloop_two_Hflow_lemT_eq d N (hz N) ω σ₂ a b
    show ∫ ω, RBM.gloop (d.L N) (d.W N) (Xmat d N ω) (z N) ⟨[true, σ₂], [a, b]⟩ ∂(P d) = _
    simp only [key]
    rw [MeasureTheory.integral_const_mul]
    rfl

@[simp] theorem transfer_gauss_Hband (N : ℕ) (ω : Ω d) :
    (transfer_gauss d).Hband N ω = Xmat d N ω := rfl

/-- **(2.39) for the 1-`G` loop** for the moment route: again an equality of random variables. -/
theorem transferLoop1_gauss : RBM.TransferLoop1 (transfer_gauss d) where
  loop1 := by
    intro z hz c ζ h
    refine RBM.StochDom.of_le_left (fun N a ω => le_of_eq ?_) h
    congr 2
    exact gloop_one_Hflow_lemT_eq d N (hz N) ω a

/-! ### (6.1) for the Gaussian model -/

/-- **(6.1) pointwise**: the `n`-loop of `G̃_{t₁} = (H_{t₂} - z̃_{t₁})⁻¹` is
`(t₁/t₂)^{n/2} L_{t₁,σ,a}`, an equality of random variables. -/
theorem gloop_Hflow_ztTilde_eq (N : ℕ) {E t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h₁₂ : t₁ ≤ t₂) (ω : Ω d)
    (I : RBM.LoopIdx (ZMod (d.L N))) :
    RBM.gloop (d.L N) (d.W N) (Hflow d N t₂ ω) (RBM.ztTilde E t₁ t₂) I
      = ((Real.sqrt (t₂ / t₁) : ℝ) : ℂ)⁻¹ ^ (I.σ.zip I.a).length *
        RBM.gloop (d.L N) (d.W N) (Hflow d N t₁ ω) (RBM.zt E t₁) I := by
  set r : ℝ := Real.sqrt (t₂ / t₁) with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.2 (div_pos (lt_of_lt_of_le h₁ h₁₂) h₁)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hmul : r * Real.sqrt t₁ = Real.sqrt t₂ := by
    have hdiv : (0 : ℝ) ≤ t₂ / t₁ := le_of_lt (div_pos (lt_of_lt_of_le h₁ h₁₂) h₁)
    rw [hr_def, ← Real.sqrt_mul hdiv t₁, div_mul_cancel₀ _ h₁.ne']
  have hH : Hflow d N t₂ ω = (r : ℂ) • Hflow d N t₁ ω := by
    show ((Real.sqrt t₂ : ℝ) : ℂ) • Xmat d N ω
      = (r : ℂ) • (((Real.sqrt t₁ : ℝ) : ℂ) • Xmat d N ω)
    rw [smul_smul, ← Complex.ofReal_mul, hmul]
  rw [hH, RBM.ztTilde, gloop_smul_mul hrC]

/-- **(6.1) as a transfer of `≺`-bounds** for the moment route.  The scaling factor
`(t₁/t₂)^{n/2}` is deterministic and `≤ 1`, so every bound transfers verbatim. -/
theorem loopScaling_gauss {E : ℝ} {t₁ t₂ : ℕ → ℝ} (h₁ : ∀ N, 0 < t₁ N) (h₁₂ : ∀ N, t₁ N ≤ t₂ N) :
    RBM.LoopScaling (sample d) E t₁ t₂ where
  transfer := by
    intro n _ ζ h
    refine RBM.StochDom.of_le_left (fun N u ω => ?_) h
    set r : ℝ := Real.sqrt (t₂ N / t₁ N) with hr_def
    have hr1 : 1 ≤ r := by
      rw [hr_def, show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt ((one_le_div (h₁ N)).2 (h₁₂ N))
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
    have hkey := gloop_Hflow_ztTilde_eq d N (E := E) (h₁ N) (h₁₂ N) ω u.idx
    have hL : RBM.gloop ((band d).L N) ((band d).W N) ((sample d).H N (t₂ N) ω)
        (RBM.ztTilde E (t₁ N) (t₂ N)) u.idx
        = ((r : ℂ))⁻¹ ^ (u.idx.σ.zip u.idx.a).length *
          (sample d).Lval E N (t₁ N) ω u.idx := hkey
    rw [hL, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    have hle : |r|⁻¹ ^ (u.idx.σ.zip u.idx.a).length ≤ 1 := by
      rw [abs_of_pos hr0]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
    rw [abs_of_pos hr0] at hle
    calc r⁻¹ ^ (u.idx.σ.zip u.idx.a).length *
        ‖(sample d).Lval E N (t₁ N) ω u.idx‖
        ≤ 1 * ‖(sample d).Lval E N (t₁ N) ω u.idx‖ :=
          mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = _ := one_mul _

end RBM.Gauss


