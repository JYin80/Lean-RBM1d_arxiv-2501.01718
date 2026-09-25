/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LoopIto
import RBM1D.Gauss.LoopLipschitz

/-!
# T1487 — the deterministic Lipschitz bound for the loop drift (pilot P4/P5)

Formalization support for `docs/claude-team/pilot-P4P5-paper.md` §2-3 and ticket T1486 (T3):
the right-hand side of `RBM.Gauss.generator_add_zMotion_gauss` (`Gauss/LoopIto.lean`), i.e. the
drift of the loop hierarchy (2.45)-(2.47), is deterministically Lipschitz in the matrix
argument, with an explicit polynomial constant.

## Main results

* `RBM.Gauss.Grid.norm_green_sub_le_of_herm` (T3) : the resolvent-difference bound, at a fixed
  spectral parameter, for two Hermitian matrices.
* `RBM.Gauss.Grid.loopDrift` (T1) : the right-hand side of `generator_add_zMotion_gauss`, named.
* `RBM.Gauss.Grid.driftLip` : the explicit, closed-form Lipschitz constant.
* `RBM.Gauss.Grid.norm_loopDrift_sub_le` (T2) : `loopDrift` is Lipschitz in `M`, deterministically,
  with constant `driftLip`.

## Route

`eGterm` and `primRhs (gloop ·)` are both finite sums of `A · S^{(B)} · B` terms, where `A`, `B`
are, respectively, a trace of a resolvent-minus-`m` term against a block projector, or a
`G`-loop. `RBM.norm_mul_mul_sub_le` telescopes each such term
(`(A₁-A₂)SB₁ + A₂S(B₁-B₂)`); `RBM.norm_gloop_sub_le` supplies the loop-difference bound and
`RBM.Gauss.Grid.norm_green_sub_le_of_herm` (T3) supplies the resolvent-difference bound feeding
it. Every occurring sub-loop has length at most `I.σ.length + 1` (`RBM.LoopIdx.length_cutGlue`,
`length_cutGlueL_le`, `length_cutGlueR_le`), so a single pair of constants `(C0, Δ0)`, built from
a common envelope `K := 1 + η⁻¹` and Lipschitz modulus, dominates every term uniformly; summing
over the (at most `L² n` and `L² n²`) terms of `eGterm` and `primRhs` gives the polynomial
`driftLip`.
-/

namespace RBM.Gauss.Grid

open Finset Matrix
open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ}

/-! ### (T3) The resolvent-difference bound at a fixed spectral parameter -/

/-- The fully generic core of (T3), over an arbitrary Hermitian-matrix index type: no reference
to `Dims`. Kept `private` and separate from the public statement below so that generic callers
(in particular the `L W : ℕ` core of (T2)) never have to unify `d.Idx N` against `ZMod L × Fin W`
for some existentially-quantified `d, N` — that unification problem is a `whnf` runaway. -/
private theorem norm_green_sub_le_of_herm' {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {M₁ M₂ : Matrix n n ℂ} (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    ‖green M₁ z - green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by
  have hzpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  have hg1 : ‖green M₁ z‖ ≤ |z.im|⁻¹ := norm_green_le hM₁ hzpos le_rfl
  have hg2 : ‖green M₂ z‖ ≤ |z.im|⁻¹ := norm_green_le hM₂ hzpos le_rfl
  have hbase := norm_green_sub_le hM₁ hM₂ hz hz
  have hstep : ‖green M₁ z‖ * (‖M₁ - M₂‖ + ‖z - z‖) * ‖green M₂ z‖
      ≤ |z.im|⁻¹ * ‖M₁ - M₂‖ * |z.im|⁻¹ := by
    rw [sub_self, norm_zero, add_zero]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)) hg2 (norm_nonneg _)
      (by positivity)
  refine hbase.trans (hstep.trans_eq ?_)
  ring

/-- **(T3)**: for Hermitian `M₁, M₂` and `z.im ≠ 0`,
`‖G(M₁, z) - G(M₂, z)‖ ≤ |z.im|⁻¹² ‖M₁ - M₂‖`. -/
theorem norm_green_sub_le_of_herm {M₁ M₂ : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖green M₁ z - green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ :=
  norm_green_sub_le_of_herm' hM₁ hM₂ hz

/-! ### Small deterministic helpers -/

/-- `m ↦ (m : ℝ) * K^m` is monotone for `K ≥ 1`. -/
private theorem real_mul_pow_le_of_le {K : ℝ} (hK : 1 ≤ K) {m n : ℕ} (h : m ≤ n) :
    (m : ℝ) * K ^ m ≤ (n : ℝ) * K ^ n := by
  have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have h2 : K ^ m ≤ K ^ n := pow_le_pow_right₀ hK h
  have hp0 : (0 : ℝ) ≤ K ^ m := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  calc (m : ℝ) * K ^ m ≤ (n : ℝ) * K ^ m := mul_le_mul_of_nonneg_right h1 hp0
    _ ≤ (n : ℝ) * K ^ n := mul_le_mul_of_nonneg_left h2 hn0

/-- The single-matrix envelope of a `G`-loop: `‖L_{σ,a}(M,z)‖ ≤ (LW) K^{σ.length}` whenever
`‖G(M,z)‖ ≤ K`. -/
private theorem norm_gloop_le_of_herm {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian) {z : ℂ} {K : ℝ}
    (hK0 : 0 ≤ K) (hGK : ‖green M z‖ ≤ K) {J : LoopIdx (ZMod L)} (hJ : J.WF) :
    ‖gloop L W M z J‖ ≤ (L : ℝ) * (W : ℝ) * K ^ J.σ.length := by
  obtain ⟨σ, a⟩ := J
  have hJwf : σ.length = a.length := hJ
  have hG : ∀ s : Bool, ‖Gsig M z s‖ ≤ K := fun s => norm_Gsig_le_of_green hM hGK s
  have hp := norm_gloopProd_le_pow hK0 hG σ a hJwf
  have hcard : (Fintype.card (ZMod L × Fin W) : ℝ) = (L : ℝ) * (W : ℝ) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]; push_cast; ring
  calc ‖gloop L W M z ⟨σ, a⟩‖ = ‖Matrix.trace (gloopProd L W M z ⟨σ, a⟩)‖ := rfl
    _ ≤ (Fintype.card (ZMod L × Fin W) : ℝ) * ‖gloopProd L W M z ⟨σ, a⟩‖ :=
        norm_trace_le_card_mul _
    _ ≤ (L : ℝ) * (W : ℝ) * K ^ σ.length := by
        rw [hcard]; exact mul_le_mul_of_nonneg_left hp (by positivity)

/-- A finite sum of pointwise-bounded differences is bounded by cardinality times the bound. -/
private theorem norm_sum_sub_le {ι : Type*} (s : Finset ι) (f g : ι → ℂ) {C : ℝ}
    (h : ∀ i ∈ s, ‖f i - g i‖ ≤ C) :
    ‖(∑ i ∈ s, f i) - ∑ i ∈ s, g i‖ ≤ (s.card : ℝ) * C := by
  rw [← Finset.sum_sub_distrib]
  calc ‖∑ i ∈ s, (f i - g i)‖ ≤ ∑ _i ∈ s, C :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum h)
    _ = (s.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The `primRhs`-difference bound.**  For any two loop functions `K₁, K₂` uniformly
envelope-bounded by `d` and Lipschitz-bounded by `R` on every sub-loop of length in
`[2, I.length]`, `‖primRhs K₁ - primRhs K₂‖ ≤ W · I.length² · L² · 2Rd`. -/
private theorem norm_primRhs_sub_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    (K₁ K₂ : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) (hI : I.WF)
    {R d : ℝ} (hR0 : 0 ≤ R) (hd0 : 0 ≤ d)
    (hEnv2 : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K₂ J‖ ≤ d)
    (hEnv1 : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K₁ J‖ ≤ d)
    (hDiff : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K₁ J - K₂ J‖ ≤ R) :
    ‖primRhs L W K₁ I - primRhs L W K₂ I‖
      ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (R * d)) := by
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖(∑ a : ZMod L, ∑ b : ZMod L, K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b))
        - (∑ a : ZMod L, ∑ b : ZMod L,
            K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b))‖
      ≤ (L : ℝ) ^ 2 * (2 * (R * d)) := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hWFL : ∀ a : ZMod L, (I.cutGlueL k l a).WF := fun a =>
      LoopIdx.WF.cutGlueL a hI hk.1 hl.1 hl.2
    have hWFR : ∀ b : ZMod L, (I.cutGlueR k l b).WF := fun b =>
      LoopIdx.WF.cutGlueR b hI hk.1 hl.1 hl.2
    have h2L : ∀ a : ZMod L, 2 ≤ (I.cutGlueL k l a).length := fun a =>
      LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2
    have h2R : ∀ b : ZMod L, 2 ≤ (I.cutGlueR k l b).length := fun b =>
      LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2
    have hleL : ∀ a : ZMod L, (I.cutGlueL k l a).length ≤ I.length := fun a =>
      LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2
    have hleR : ∀ b : ZMod L, (I.cutGlueR k l b).length ≤ I.length := fun b =>
      LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2
    have hX2 : ∀ a : ZMod L, ‖K₂ (I.cutGlueL k l a)‖ ≤ d :=
      fun a => hEnv2 _ (hWFL a) (h2L a) (hleL a)
    have hY1 : ∀ b : ZMod L, ‖K₁ (I.cutGlueR k l b)‖ ≤ d :=
      fun b => hEnv1 _ (hWFR b) (h2R b) (hleR b)
    have hXsub : ∀ a : ZMod L, ‖K₁ (I.cutGlueL k l a) - K₂ (I.cutGlueL k l a)‖ ≤ R :=
      fun a => hDiff _ (hWFL a) (h2L a) (hleL a)
    have hYsub : ∀ b : ZMod L, ‖K₁ (I.cutGlueR k l b) - K₂ (I.cutGlueR k l b)‖ ≤ R :=
      fun b => hDiff _ (hWFR b) (h2R b) (hleR b)
    have hterm : ∀ a b : ZMod L,
        ‖K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b)
          - K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b)‖ ≤ 2 * (R * d) := by
      intro a b
      refine norm_mul_mul_sub_le (norm_SB_apply_le L hL a b)
        (mul_le_mul (hXsub a) (hY1 b) (norm_nonneg _) (le_trans (norm_nonneg _) (hXsub a))) ?_
      exact (mul_le_mul (hX2 a) (hYsub b) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hX2 a))).trans_eq (mul_comm d R)
    have hinner : ∀ a ∈ (Finset.univ : Finset (ZMod L)),
        ‖(∑ b : ZMod L, K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b))
          - ∑ b : ZMod L, K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b)‖
        ≤ (L : ℝ) * (2 * (R * d)) := by
      intro a _
      refine (norm_sum_sub_le Finset.univ _ _ (fun b _ => hterm a b)).trans ?_
      rw [Finset.card_univ, ZMod.card]
    refine (norm_sum_sub_le Finset.univ _ _ hinner).trans ?_
    rw [Finset.card_univ, ZMod.card]
    exact le_of_eq (by ring)
  have hploc : ∀ k ∈ Icc 1 I.length,
      ‖(∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
            K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b))
        - (∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
            K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b))‖
      ≤ (I.length : ℝ) * ((L : ℝ) ^ 2 * (2 * (R * d))) := by
    intro k hk
    refine (norm_sum_sub_le (Finset.Ioc k I.length) _ _ (fun l hl => hpair k hk l hl)).trans ?_
    rw [Nat.card_Ioc]
    have hle : ((I.length - k : ℕ) : ℝ) ≤ (I.length : ℝ) := by
      exact_mod_cast Nat.sub_le I.length k
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hktotal :
      ‖(∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
            K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b))
        - (∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
            K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b))‖
      ≤ (I.length : ℝ) * ((I.length : ℝ) * ((L : ℝ) ^ 2 * (2 * (R * d)))) := by
    refine (norm_sum_sub_le (Icc 1 I.length) _ _ hploc).trans ?_
    rw [Nat.card_Icc]
    have h : (I.length + 1 - 1 : ℕ) = I.length := by omega
    rw [h]
  calc ‖primRhs L W K₁ I - primRhs L W K₂ I‖
      = ‖(W : ℂ) * ((∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
              K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b))
            - (∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
              K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b)))‖ := by
        rw [primRhs, primRhs, ← mul_sub]
    _ = (W : ℝ) * ‖(∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
              K₁ (I.cutGlueL k l a) * SB L a b * K₁ (I.cutGlueR k l b))
            - (∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
              K₂ (I.cutGlueL k l a) * SB L a b * K₂ (I.cutGlueR k l b))‖ := by
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ (W : ℝ) * ((I.length : ℝ) * ((I.length : ℝ) * ((L : ℝ) ^ 2 * (2 * (R * d))))) :=
        mul_le_mul_of_nonneg_left hktotal hW0
    _ = (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (R * d)) := by ring

/-- **The `eGterm`-difference bound.**  Analogue of `norm_primRhs_sub_le` for the single-`k`
sum structure of `eGterm`; `A` (the trace-minus-`m` factor) and `B` (the `G`-loop factor at
`I.cutGlue k b`) are uniformly envelope/Lipschitz bounded. -/
private theorem norm_eGtermSum_sub_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) (n : ℕ)
    (A₁ A₂ : Bool → ZMod L → ℂ) (B₁ B₂ : ℕ → ZMod L → ℂ) {R d : ℝ}
    (hA2 : ∀ (s : Bool) (a : ZMod L), ‖A₂ s a‖ ≤ d)
    (hB1 : ∀ k ∈ Icc 1 n, ∀ b : ZMod L, ‖B₁ k b‖ ≤ d)
    (hAsub : ∀ (s : Bool) (a : ZMod L), ‖A₁ s a - A₂ s a‖ ≤ R)
    (hBsub : ∀ k ∈ Icc 1 n, ∀ b : ZMod L, ‖B₁ k b - B₂ k b‖ ≤ R) (χ : ℕ → Bool) :
    ‖(∑ k ∈ Icc 1 n, ∑ a : ZMod L, ∑ b : ZMod L, A₁ (χ k) a * SB L a b * B₁ k b)
      - (∑ k ∈ Icc 1 n, ∑ a : ZMod L, ∑ b : ZMod L, A₂ (χ k) a * SB L a b * B₂ k b)‖
      ≤ (n : ℝ) * (L : ℝ) ^ 2 * (2 * (R * d)) := by
  have hterm : ∀ k ∈ Icc 1 n, ∀ (a b : ZMod L),
      ‖A₁ (χ k) a * SB L a b * B₁ k b - A₂ (χ k) a * SB L a b * B₂ k b‖ ≤ 2 * (R * d) := by
    intro k hk a b
    refine norm_mul_mul_sub_le (norm_SB_apply_le L hL a b)
      (mul_le_mul (hAsub (χ k) a) (hB1 k hk b) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hAsub (χ k) a))) ?_
    exact (mul_le_mul (hA2 (χ k) a) (hBsub k hk b) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hA2 (χ k) a))).trans_eq (mul_comm d R)
  have hpair : ∀ k ∈ Icc 1 n,
      ‖(∑ a : ZMod L, ∑ b : ZMod L, A₁ (χ k) a * SB L a b * B₁ k b)
        - (∑ a : ZMod L, ∑ b : ZMod L, A₂ (χ k) a * SB L a b * B₂ k b)‖
      ≤ (L : ℝ) ^ 2 * (2 * (R * d)) := by
    intro k hk
    have hinner : ∀ a ∈ (Finset.univ : Finset (ZMod L)),
        ‖(∑ b : ZMod L, A₁ (χ k) a * SB L a b * B₁ k b)
          - ∑ b : ZMod L, A₂ (χ k) a * SB L a b * B₂ k b‖ ≤ (L : ℝ) * (2 * (R * d)) := by
      intro a _
      refine (norm_sum_sub_le Finset.univ _ _ (fun b _ => hterm k hk a b)).trans ?_
      rw [Finset.card_univ, ZMod.card]
    refine (norm_sum_sub_le Finset.univ _ _ hinner).trans ?_
    rw [Finset.card_univ, ZMod.card]
    exact le_of_eq (by ring)
  refine (norm_sum_sub_le (Icc 1 n) _ _ hpair).trans ?_
  rw [Nat.card_Icc]
  have h : (n + 1 - 1 : ℕ) = n := by omega
  rw [h]
  exact le_of_eq (by ring)

/-! ### (T1) The loop drift -/

/-- **(T1)**: the right-hand side of `RBM.Gauss.generator_add_zMotion_gauss`, named. -/
noncomputable def loopDrift (E u : ℝ) (I : LoopIdx (ZMod (d.L N)))
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
    + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M (zt E u)) I

/-- `loopDrift` is literally the right-hand side of `generator_add_zMotion_gauss`. -/
theorem loopDrift_eq (E u : ℝ) (I : LoopIdx (ZMod (d.L N))) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    loopDrift E u I M = eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
      + primRhs (d.L N) (d.W N) (gloop (d.L N) (d.W N) M (zt E u)) I := rfl

/-! ### The Lipschitz constant -/

/-- **The explicit, closed-form Lipschitz constant.**  Polynomial in `L, W, n, η⁻¹` and
`‖m‖ := max ‖m true‖ ‖m false‖`; no existential, no dependence on the matrix. -/
noncomputable def driftLip (L W n : ℕ) (η : ℝ) (m : Bool → ℂ) : ℝ :=
  4 * (L : ℝ) ^ 4 * (W : ℝ) ^ 3 * (n : ℝ) ^ 2 * ((n : ℝ) + 1)
    * ((1 + η⁻¹) + max ‖m true‖ ‖m false‖) ^ 2 * (1 + η⁻¹) ^ (2 * (n + 1)) * η⁻¹ ^ 2

/-! ### (T2) The Lipschitz bound: the four envelope/Lipschitz building blocks

Each is a standalone lemma (not a `have` inside the main proof) so that its own tactic calls
run in a small local context; the main proof below only combines their conclusions. -/

/-- Envelope for the trace-minus-`m` factor of `eGterm`, bumped by `K^(n+1) ≥ 1` so that it
matches the common bound `C0` used for the `G`-loop factor too. -/
private theorem traceEnv_le {L W : ℕ} [NeZero L] [NeZero W]
    (m : Bool → ℂ) (mAbs : ℝ) (hmAbs : ∀ σ : Bool, ‖m σ‖ ≤ mAbs)
    {z : ℂ} {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {K : ℝ}
    (hM : M.IsHermitian) (hGK : ‖green M z‖ ≤ K) {n : ℕ} (hKpow1 : (1 : ℝ) ≤ K ^ (n + 1))
    (σ : Bool) (a : ZMod L) :
    ‖Matrix.trace ((Gsig M z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
        * Eblk L W a)‖ ≤ (L : ℝ) * (W : ℝ) * (K + mAbs) * K ^ (n + 1) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) hGK
  have hmAbs0 : (0 : ℝ) ≤ mAbs := le_trans (norm_nonneg _) (hmAbs true)
  have hGsig : ‖Gsig M z σ‖ ≤ K := norm_Gsig_le_of_green hM hGK σ
  have hcard : (Fintype.card (ZMod L × Fin W) : ℝ) = (L : ℝ) * (W : ℝ) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]; push_cast; ring
  have hnorm1 : ‖(1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)‖ = 1 := norm_one
  have hXnorm : ‖Gsig M z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)‖
      ≤ K + mAbs := by
    have hstep := norm_sub_le (Gsig M z σ)
      (m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
    rw [norm_smul, hnorm1, mul_one] at hstep
    exact hstep.trans (add_le_add hGsig (hmAbs σ))
  have hbase : ‖Matrix.trace ((Gsig M z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      * Eblk L W a)‖ ≤ (L : ℝ) * (W : ℝ) * (K + mAbs) := by
    calc ‖Matrix.trace ((Gsig M z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
            * Eblk L W a)‖
        ≤ (Fintype.card (ZMod L × Fin W) : ℝ)
            * ‖(Gsig M z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
              * Eblk L W a‖ := norm_trace_le_card_mul _
      _ ≤ (L : ℝ) * (W : ℝ)
            * (‖Gsig M z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)‖
              * ‖Eblk L W a‖) := by
          rw [hcard]; exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
      _ ≤ (L : ℝ) * (W : ℝ) * ((K + mAbs) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hXnorm (norm_Eblk_le_one'' a) (norm_nonneg _) (by positivity)
      _ = (L : ℝ) * (W : ℝ) * (K + mAbs) := by ring
  refine hbase.trans ?_
  have hnn : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) * (K + mAbs) := by positivity
  calc (L : ℝ) * (W : ℝ) * (K + mAbs) = (L : ℝ) * (W : ℝ) * (K + mAbs) * 1 := by ring
    _ ≤ (L : ℝ) * (W : ℝ) * (K + mAbs) * K ^ (n + 1) := mul_le_mul_of_nonneg_left hKpow1 hnn

/-- Lipschitz bound for the trace-minus-`m` factor of `eGterm`, in terms of a resolvent
Lipschitz bound `Δg`. -/
private theorem traceDiff_le {L W : ℕ} [NeZero L] [NeZero W]
    (m : Bool → ℂ) {z : ℂ} {M₁ M₂ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {K mAbs : ℝ} (hKmAbs1 : (1 : ℝ) ≤ K + mAbs)
    {n : ℕ} (hKpow1 : (1 : ℝ) ≤ K ^ (n + 1))
    {Δg : ℝ} (hΔg0 : 0 ≤ Δg) (hΔgreen : ‖green M₁ z - green M₂ z‖ ≤ Δg)
    (σ : Bool) (a : ZMod L) :
    ‖Matrix.trace ((Gsig M₁ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
        * Eblk L W a)
      - Matrix.trace ((Gsig M₂ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
        * Eblk L W a)‖
      ≤ (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1) * Δg := by
  have hcard : (Fintype.card (ZMod L × Fin W) : ℝ) = (L : ℝ) * (W : ℝ) := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]; push_cast; ring
  have hcancel : (Gsig M₁ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      - (Gsig M₂ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
      = Gsig M₁ z σ - Gsig M₂ z σ := by abel
  have heq :
      Matrix.trace ((Gsig M₁ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)
        - Matrix.trace ((Gsig M₂ z σ
            - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)
      = Matrix.trace ((Gsig M₁ z σ - Gsig M₂ z σ) * Eblk L W a) := by
    rw [← Matrix.trace_sub, ← Matrix.sub_mul, hcancel]
  rw [heq]
  have hGdiff : ‖Gsig M₁ z σ - Gsig M₂ z σ‖ ≤ Δg :=
    (norm_Gsig_sub_le_norm_green_sub hM₁ hM₂ σ).trans hΔgreen
  have hbase : ‖Matrix.trace ((Gsig M₁ z σ - Gsig M₂ z σ) * Eblk L W a)‖
      ≤ (L : ℝ) * (W : ℝ) * Δg := by
    calc ‖Matrix.trace ((Gsig M₁ z σ - Gsig M₂ z σ) * Eblk L W a)‖
        ≤ (Fintype.card (ZMod L × Fin W) : ℝ) * ‖(Gsig M₁ z σ - Gsig M₂ z σ) * Eblk L W a‖ :=
          norm_trace_le_card_mul _
      _ ≤ (L : ℝ) * (W : ℝ) * (‖Gsig M₁ z σ - Gsig M₂ z σ‖ * ‖Eblk L W a‖) := by
          rw [hcard]; exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by positivity)
      _ ≤ (L : ℝ) * (W : ℝ) * (Δg * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hGdiff (norm_Eblk_le_one'' a) (norm_nonneg _) hΔg0
      _ = (L : ℝ) * (W : ℝ) * Δg := by ring
  refine hbase.trans ?_
  have hnn : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) * Δg := by positivity
  have hfac : (1 : ℝ) ≤ ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1) := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h2 := mul_le_mul h1 hKmAbs1 (by linarith) (by linarith)
    have h3 := mul_le_mul h2 hKpow1 (by linarith) (by positivity)
    simpa using h3
  calc (L : ℝ) * (W : ℝ) * Δg = (L : ℝ) * (W : ℝ) * Δg * 1 := by ring
    _ ≤ (L : ℝ) * (W : ℝ) * Δg * (((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hfac hnn
    _ = (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1) * Δg := by ring

/-- Envelope for a `G`-loop of length at most `n + 1`, bumped by `K + mAbs ≥ 1` to match the
common bound `C0`. -/
private theorem gloopEnv_le {L W : ℕ} [NeZero L] [NeZero W]
    {z : ℂ} {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian)
    {K : ℝ} (hK1 : (1 : ℝ) ≤ K) (hGK : ‖green M z‖ ≤ K) {mAbs : ℝ} (hKmAbs1 : (1 : ℝ) ≤ K + mAbs)
    {n : ℕ} {J : LoopIdx (ZMod L)} (hJ : J.WF) (hJlen : J.σ.length ≤ n + 1) :
    ‖gloop L W M z J‖ ≤ (L : ℝ) * (W : ℝ) * (K + mAbs) * K ^ (n + 1) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have h1 := norm_gloop_le_of_herm hM hK0 hGK hJ
  refine h1.trans ?_
  have hpow : K ^ J.σ.length ≤ K ^ (n + 1) := pow_le_pow_right₀ hK1 hJlen
  have hLW0 : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) := by positivity
  have step1 : (L : ℝ) * (W : ℝ) * K ^ J.σ.length ≤ (L : ℝ) * (W : ℝ) * K ^ (n + 1) :=
    mul_le_mul_of_nonneg_left hpow hLW0
  refine step1.trans ?_
  have hC0' : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) * K ^ (n + 1) := by positivity
  calc (L : ℝ) * (W : ℝ) * K ^ (n + 1) = (L : ℝ) * (W : ℝ) * K ^ (n + 1) * 1 := by ring
    _ ≤ (L : ℝ) * (W : ℝ) * K ^ (n + 1) * (K + mAbs) := mul_le_mul_of_nonneg_left hKmAbs1 hC0'
    _ = (L : ℝ) * (W : ℝ) * (K + mAbs) * K ^ (n + 1) := by ring

/-- Lipschitz bound for a `G`-loop of length at most `n + 1`, in terms of a resolvent Lipschitz
bound `Δg`. -/
private theorem gloopDiff_le {L W : ℕ} [NeZero L] [NeZero W]
    {z : ℂ} {M₁ M₂ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) {K : ℝ} (hK1 : (1 : ℝ) ≤ K)
    (hGK1 : ‖green M₁ z‖ ≤ K) (hGK2 : ‖green M₂ z‖ ≤ K) {mAbs : ℝ}
    (hKmAbs1 : (1 : ℝ) ≤ K + mAbs) {Δg : ℝ} (hΔg0 : 0 ≤ Δg)
    (hΔgreen : ‖green M₁ z - green M₂ z‖ ≤ Δg)
    {n : ℕ} {J : LoopIdx (ZMod L)} (hJ : J.WF) (hJlen : J.σ.length ≤ n + 1) :
    ‖gloop L W M₁ z J - gloop L W M₂ z J‖
      ≤ (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1) * Δg := by
  have h1 : ‖gloop L W M₁ z J - gloop L W M₂ z J‖
      ≤ (L : ℝ) * (W : ℝ) * (J.σ.length : ℝ) * K ^ J.σ.length * Δg :=
    norm_gloop_sub_le hK1 hΔg0 hM₁ hM₂ hGK1 hGK2 hΔgreen J hJ
  refine h1.trans ?_
  have hmono : (J.σ.length : ℝ) * K ^ J.σ.length ≤ ((n : ℝ) + 1) * K ^ (n + 1) := by
    have := real_mul_pow_le_of_le hK1 hJlen
    simpa using this
  have hLW0 : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) := by positivity
  have stepA : (L : ℝ) * (W : ℝ) * (J.σ.length : ℝ) * K ^ J.σ.length
      ≤ (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * K ^ (n + 1) := by
    calc (L : ℝ) * (W : ℝ) * (J.σ.length : ℝ) * K ^ J.σ.length
        = (L : ℝ) * (W : ℝ) * ((J.σ.length : ℝ) * K ^ J.σ.length) := by ring
      _ ≤ (L : ℝ) * (W : ℝ) * (((n : ℝ) + 1) * K ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hmono hLW0
      _ = (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * K ^ (n + 1) := by ring
  have hC0'' : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * K ^ (n + 1) := by positivity
  have stepB : (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * K ^ (n + 1)
      ≤ (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1) := by
    calc (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * K ^ (n + 1)
        ≤ (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * K ^ (n + 1) * (K + mAbs) :=
          le_mul_of_one_le_right hC0'' hKmAbs1
      _ = (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1) := by ring
  exact mul_le_mul_of_nonneg_right (stepA.trans stepB) hΔg0

/-! ### (T2) The Lipschitz bound: assembly -/

/-- The fully generic core of (T2): no reference to `Dims`, `zt`, or `loopDrift`, just the two
Hermitian matrices, the loop index and the spectral parameter. -/
private theorem norm_loopDrift_sub_le_aux {L W : ℕ} [NeZero L] [NeZero W] (hL3 : 3 ≤ L)
    (m : Bool → ℂ) {z : ℂ} (hz : z.im ≠ 0)
    {M₁ M₂ : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian)
    {I : LoopIdx (ZMod L)} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ‖(eGterm L W m M₁ z I + primRhs L W (gloop L W M₁ z) I)
        - (eGterm L W m M₂ z I + primRhs L W (gloop L W M₂ z) I)‖
      ≤ driftLip L W I.σ.length |z.im| m * ‖M₁ - M₂‖ := by
  set n := I.σ.length with hndef
  have hwf' : n = I.a.length := hwf
  have hlen_eq : I.length = n := hwf'.symm
  have hn' : 1 ≤ n := by rw [hwf']; exact hn
  have hzpos : (0 : ℝ) < |z.im| := abs_pos.mpr hz
  set K : ℝ := 1 + |z.im|⁻¹ with hKdef
  set mAbs : ℝ := max ‖m true‖ ‖m false‖ with hmAbsdef
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    have h0 : (0 : ℝ) ≤ |z.im|⁻¹ := by positivity
    linarith
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hmAbs0 : (0 : ℝ) ≤ mAbs := le_trans (norm_nonneg _) (le_max_left _ _)
  have hKmAbs1 : (1 : ℝ) ≤ K + mAbs := by linarith
  have hmAbsAll : ∀ σ : Bool, ‖m σ‖ ≤ mAbs := by
    intro σ
    cases σ <;> first | exact le_max_left _ _ | exact le_max_right _ _
  show ‖(eGterm L W m M₁ z I + primRhs L W (gloop L W M₁ z) I)
        - (eGterm L W m M₂ z I + primRhs L W (gloop L W M₂ z) I)‖
      ≤ (4 * (L : ℝ) ^ 4 * (W : ℝ) ^ 3 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * (K + mAbs) ^ 2
          * K ^ (2 * (n + 1)) * |z.im|⁻¹ ^ 2) * ‖M₁ - M₂‖
  clear_value K mAbs
  have hGK1 : ‖green M₁ z‖ ≤ K := (norm_green_le hM₁ hzpos le_rfl).trans (by rw [hKdef]; linarith)
  have hGK2 : ‖green M₂ z‖ ≤ K := (norm_green_le hM₂ hzpos le_rfl).trans (by rw [hKdef]; linarith)
  have hΔgreen : ‖green M₁ z - green M₂ z‖ ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ :=
    norm_green_sub_le_of_herm' hM₁ hM₂ hz
  have hΔg0 : (0 : ℝ) ≤ |z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖ := by positivity
  set C0 : ℝ := (L : ℝ) * (W : ℝ) * (K + mAbs) * K ^ (n + 1) with hC0def
  set Δ0 : ℝ := (L : ℝ) * (W : ℝ) * ((n : ℝ) + 1) * (K + mAbs) * K ^ (n + 1)
      * (|z.im|⁻¹ ^ 2 * ‖M₁ - M₂‖) with hΔ0def
  have hC0nn : (0 : ℝ) ≤ C0 := by rw [hC0def]; positivity
  have hΔ0nn : (0 : ℝ) ≤ Δ0 := by rw [hΔ0def]; positivity
  clear_value C0 Δ0
  have hKpow1 : (1 : ℝ) ≤ K ^ (n + 1) := by
    calc (1 : ℝ) = K ^ 0 := (pow_zero K).symm
      _ ≤ K ^ (n + 1) := pow_le_pow_right₀ hK1 (Nat.zero_le _)
  -- Envelope + Lipschitz for the trace-minus-`m` factor of `eGterm`, and for any `G`-loop of
  -- length at most `n + 1`, all bounded uniformly by `C0, Δ0` (`traceEnv_le`, `traceDiff_le`,
  -- `gloopEnv_le`, `gloopDiff_le` above).
  have hTraceEnv2 : ∀ (σ : Bool) (a : ZMod L),
      ‖Matrix.trace ((Gsig M₂ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)‖ ≤ C0 := by
    intro σ a; rw [hC0def]; exact traceEnv_le m mAbs hmAbsAll hM₂ hGK2 hKpow1 σ a
  have hTraceDiff : ∀ (σ : Bool) (a : ZMod L),
      ‖Matrix.trace ((Gsig M₁ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)
        - Matrix.trace ((Gsig M₂ z σ - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W a)‖ ≤ Δ0 := by
    intro σ a; rw [hΔ0def]
    exact traceDiff_le m hM₁ hM₂ hKmAbs1 hKpow1 hΔg0 hΔgreen σ a
  have hGloopEnv2 : ∀ J : LoopIdx (ZMod L), J.WF → J.σ.length ≤ n + 1 →
      ‖gloop L W M₂ z J‖ ≤ C0 := by
    intro J hJ hJlen; rw [hC0def]; exact gloopEnv_le hM₂ hK1 hGK2 hKmAbs1 hJ hJlen
  have hGloopEnv1 : ∀ J : LoopIdx (ZMod L), J.WF → J.σ.length ≤ n + 1 →
      ‖gloop L W M₁ z J‖ ≤ C0 := by
    intro J hJ hJlen; rw [hC0def]; exact gloopEnv_le hM₁ hK1 hGK1 hKmAbs1 hJ hJlen
  have hGloopDiff : ∀ J : LoopIdx (ZMod L), J.WF → J.σ.length ≤ n + 1 →
      ‖gloop L W M₁ z J - gloop L W M₂ z J‖ ≤ Δ0 := by
    intro J hJ hJlen; rw [hΔ0def]
    exact gloopDiff_le hM₁ hM₂ hK1 hGK1 hGK2 hKmAbs1 hΔg0 hΔgreen hJ hJlen
  -- Assemble the `eGterm` and `primRhs` differences.
  have heG_unfold : ∀ M' : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ,
      eGterm L W m M' z I
        = (W : ℂ) * ∑ k ∈ Finset.Icc 1 n, ∑ a : ZMod L, ∑ b : ZMod L,
            Matrix.trace ((Gsig M' z (I.σ.getD (k - 1) true)
                - m (I.σ.getD (k - 1) true)
                  • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
              * Eblk L W a) * SB L a b * gloop L W M' z (I.cutGlue k b) := by
    intro M'
    unfold eGterm
    rw [hlen_eq]
  have hIcutGlueWF : ∀ k : ℕ, k ∈ Finset.Icc 1 n → ∀ b : ZMod L, (I.cutGlue k b).WF := by
    intro k hk b
    rw [Finset.mem_Icc] at hk
    exact hwf.cutGlue b hk.1 (by rw [hlen_eq]; exact hk.2)
  have hIcutGlueLen : ∀ k : ℕ, k ∈ Finset.Icc 1 n → ∀ b : ZMod L,
      (I.cutGlue k b).σ.length ≤ n + 1 := by
    intro k hk b
    rw [Finset.mem_Icc] at hk
    have hWFb : (I.cutGlue k b).WF := hIcutGlueWF k (Finset.mem_Icc.mpr hk) b
    have h1 : (I.cutGlue k b).σ.length = (I.cutGlue k b).a.length := hWFb
    have h2 : (I.cutGlue k b).a.length = (I.cutGlue k b).length := rfl
    have h3 : (I.cutGlue k b).length = I.length + 1 :=
      I.length_cutGlue b (by rw [hlen_eq]; exact hk.2)
    rw [h1, h2, h3, hlen_eq]
  have hEGbound : ‖eGterm L W m M₁ z I - eGterm L W m M₂ z I‖
      ≤ (W : ℝ) * (n : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by
    have hsum := norm_eGtermSum_sub_le (L := L) hL3 n
      (fun s a => Matrix.trace ((Gsig M₁ z s
          - m s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a))
      (fun s a => Matrix.trace ((Gsig M₂ z s
          - m s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a))
      (fun k b => gloop L W M₁ z (I.cutGlue k b)) (fun k b => gloop L W M₂ z (I.cutGlue k b))
      (R := Δ0) (d := C0)
      (fun s a => hTraceEnv2 s a)
      (fun k hk b => hGloopEnv1 (I.cutGlue k b) (hIcutGlueWF k hk b) (hIcutGlueLen k hk b))
      (fun s a => hTraceDiff s a)
      (fun k hk b => hGloopDiff (I.cutGlue k b) (hIcutGlueWF k hk b) (hIcutGlueLen k hk b))
      (fun k => I.σ.getD (k - 1) true)
    calc ‖eGterm L W m M₁ z I - eGterm L W m M₂ z I‖
        = (W : ℝ) *
          ‖(∑ k ∈ Finset.Icc 1 n, ∑ a : ZMod L, ∑ b : ZMod L,
                Matrix.trace ((Gsig M₁ z (I.σ.getD (k - 1) true)
                    - m (I.σ.getD (k - 1) true)
                      • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)
                  * SB L a b * gloop L W M₁ z (I.cutGlue k b))
              - (∑ k ∈ Finset.Icc 1 n, ∑ a : ZMod L, ∑ b : ZMod L,
                Matrix.trace ((Gsig M₂ z (I.σ.getD (k - 1) true)
                    - m (I.σ.getD (k - 1) true)
                      • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W a)
                  * SB L a b * gloop L W M₂ z (I.cutGlue k b))‖ := by
          rw [heG_unfold M₁, heG_unfold M₂, ← mul_sub, norm_mul, Complex.norm_natCast]
      _ ≤ (W : ℝ) * ((n : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))) :=
          mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) W)
      _ = (W : ℝ) * (n : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by ring
  have hPRbound : ‖primRhs L W (gloop L W M₁ z) I - primRhs L W (gloop L W M₂ z) I‖
      ≤ (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by
    have hbound := norm_primRhs_sub_le (L := L) hL3 W (gloop L W M₁ z) (gloop L W M₂ z) I hwf
      (R := Δ0) (d := C0) hΔ0nn hC0nn
      (fun J hJ _ hJlen => by
        have hJeq : J.σ.length = J.length := hJ
        exact hGloopEnv2 J hJ (by omega))
      (fun J hJ _ hJlen => by
        have hJeq : J.σ.length = J.length := hJ
        exact hGloopEnv1 J hJ (by omega))
      (fun J hJ _ hJlen => by
        have hJeq : J.σ.length = J.length := hJ
        exact hGloopDiff J hJ (by omega))
    rw [hlen_eq] at hbound
    exact hbound
  have hn_le_nsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_trans zero_le_one hn1
    calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 hn0
      _ = (n : ℝ) ^ 2 := by ring
  have hrearrange :
      (eGterm L W m M₁ z I + primRhs L W (gloop L W M₁ z) I)
        - (eGterm L W m M₂ z I + primRhs L W (gloop L W M₂ z) I)
      = (eGterm L W m M₁ z I - eGterm L W m M₂ z I)
        + (primRhs L W (gloop L W M₁ z) I - primRhs L W (gloop L W M₂ z) I) := by ring
  rw [hrearrange]
  calc ‖(eGterm L W m M₁ z I - eGterm L W m M₂ z I)
          + (primRhs L W (gloop L W M₁ z) I - primRhs L W (gloop L W M₂ z) I)‖
      ≤ ‖eGterm L W m M₁ z I - eGterm L W m M₂ z I‖
          + ‖primRhs L W (gloop L W M₁ z) I - primRhs L W (gloop L W M₂ z) I‖ := norm_add_le _ _
    _ ≤ (W : ℝ) * (n : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))
          + (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := add_le_add hEGbound hPRbound
    _ ≤ (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))
          + (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by
        have hcomb : (0 : ℝ) ≤ (W : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by positivity
        have hstep : (W : ℝ) * (n : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))
            ≤ (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by
          calc (W : ℝ) * (n : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))
              = (n : ℝ) * ((W : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))) := by ring
            _ ≤ (n : ℝ) ^ 2 * ((W : ℝ) * (L : ℝ) ^ 2 * (2 * (Δ0 * C0))) :=
                mul_le_mul_of_nonneg_right hn_le_nsq hcomb
            _ = (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * (2 * (Δ0 * C0)) := by ring
        linarith
    _ = 4 * (W : ℝ) * (n : ℝ) ^ 2 * (L : ℝ) ^ 2 * Δ0 * C0 := by ring
    _ = (4 * (L : ℝ) ^ 4 * (W : ℝ) ^ 3 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) * (K + mAbs) ^ 2
          * K ^ (2 * (n + 1)) * |z.im|⁻¹ ^ 2) * ‖M₁ - M₂‖ := by
        rw [hΔ0def, hC0def]
        ring

/-- **(T2)**: `loopDrift` is Lipschitz in the matrix argument, deterministically, with the
explicit constant `driftLip`. -/
theorem norm_loopDrift_sub_le {E u : ℝ} (hz : (zt E u).im ≠ 0)
    {M₁ M₂ : Matrix (d.Idx N) (d.Idx N) ℂ} (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian)
    {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length) :
    ‖loopDrift E u I M₁ - loopDrift E u I M₂‖
      ≤ driftLip (d.L N) (d.W N) I.σ.length |(zt E u).im| (mSigma E) * ‖M₁ - M₂‖ := by
  rw [loopDrift_eq, loopDrift_eq]
  exact norm_loopDrift_sub_le_aux (d.three_le_L N) (mSigma E) hz hM₁ hM₂ hwf hn

end RBM.Gauss.Grid
