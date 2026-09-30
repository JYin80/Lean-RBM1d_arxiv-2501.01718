/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.Universality
import RBM1D.Hierarchy.Step1
import Mathlib.Data.Set.Finite.List

/-!
# §7.2: the GUE phase of the flow — (7.25)–(7.47)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §7.2: the auxiliary
estimates (7.27)–(7.29) for the flow whose last stretch `[t₁, t₀]` has the GUE variance profile,
and (7.47), the input of the weak QUE (2.27) for `H_{t_U}` in the proof of Theorem 2.6.

Everything proved here is deterministic.  The random layer enters through hypotheses (never
`axiom`s), in the pathwise/`≺` form used elsewhere in the library.

## Main results

* **(7.25)**: `SBgue` (`(S^{(B)}_{GUE})_{ab} = 1/L`); the profile
  `S̃^{(B)} = (1-ζ) S^{(B)} + ζ S^{(B)}_{GUE}` and its zero mode are `RBM.SBTilde`,
  `RBM.ThetaTilde`.
* **(7.30)**: `ellHat_eq_L` (`ℓ_{t₁} = L`); (7.30) in the form `t - t₁ ≤ ε η_t` enters the
  bootstrap through `mul_le_of_eq730`.
* **(7.33), (7.34), (7.39), (7.40)**: `primBilGUE`, `primRhsGUE` (the primitive equation with
  `S^{(B)} → S^{(B)}_{GUE}`), `primRhsGUE_sub` (the GUE-phase (5.12)/(5.13)), and the power
  counting `norm_primBilGUE_le`, `norm_primRhsGUE_le`
  (`|W ∑_{k<l} ∑_{a,b} K S_{GUE} K'| ≤ n² N ∑_{2≤j≤n} max K^{(n-j+2)} max K'^{(j)}`).
* **The continuity argument**: `continuity_argument` (finitely many continuous quantities, a
  strict bootstrap improvement ⟹ the bound on the whole interval).
* **(7.35) ⟹ (7.36)**: `K_bootstrap` (abstract ODE bootstrap: mean value inequality +
  continuity argument), `eq736` (for solutions of `d/dt K = primRhsGUE K` on loops of length
  `2 ≤ |I| ≤ n`), `eq736_detDom` (the `≺` form, uniform in `t ∈ [t₁, t₀]`).
* **(7.45) ⟹ (7.27), (7.46) ⟹ (7.28)**: `supOn` and its bounds (the `sup_u` on the right sides
  of (7.45), (7.46)); the bootstraps are `eq728G` (`Hierarchy/GUEPhaseG.lean`) and `eq727GE`
  (`Hierarchy/GUEPhaseGEven.lean`).
* **The 2-loop primitive of the GUE phase**: `kTwoGUE` (closed form), `kTwoGUE_self`
  (= (2.57) at `t₁`), `hasDerivAt_kTwoGUE`, `hasDerivAt_kTwoGUELoop` ((7.33) at `n = 2`),
  `kTwoGUE_eq_ThetaTilde` (at `t₀`: `W⁻¹ μ (1 - t₀μ S̃^{(B)})⁻¹`), `lemT_mul_kTwoGUE_pm`,
  `lemT_mul_kTwoGUE_pp` (the main terms of (7.47)).
* **(7.47)**: `GUEFlow`, `loopG`, `Eq747Inputs`, `eq747_of_inputs` — **discharges the
  placeholder `RBM.Eq747` of `Flow/Universality.lean`** from (7.26) and (7.29); (2.27) then
  follows through `RBM.que_flow_of_eq747`.

## Hypotheses (the random layer)

* `Eq747Inputs.law726` — **(7.26)** in expectation (identity in law of the two flows);
  `Eq747Inputs.eq729` — **(7.29)** at `t₀` for `σ = (+, ±)` (in the paper: "following the
  proof of (2.80) in §5.8"); integrability of the loops.
* **(7.45)**, **(7.46)** as `≺` bounds, hypotheses of the bootstraps.  These package the
  Duhamel formula (7.37) (Lemmas 5.3, 5.5 with `s = t₁`) with Lemma 7.1,
  the BDG inequality (7.38), the bounds (7.39)–(7.44) and `E^{(G)}` via (4.5) for `G_t`
  (random inputs).
* Time continuity of `t ↦ max |L_t|`, `t ↦ max |(L-K)_t|` w.h.p. (the continuity argument).
* (7.32) (from Lemmas 2.17, 2.18) as the initial bounds; the GUE-phase primitive equation (7.33)
  (the definition of `K` on `[t₁, t₀]`) as the hypothesis `hK` of `eq736`.

## Deviations from the paper

* The `≺` of (7.27), (7.28), (7.36) is in the sequence index `N` of `RBM.StochDom` /
  `RBM.UnifDetDom`; the matrix size is a separate parameter `Nf` (resp. `W L`), and (7.30) is
  used as `t - t₁ ≤ N^{-τ_U} η_t`, `(Nf η_t)^{-1} ≤ N^{-τ_U}` (any power gain would do).
* The induction on `n` in §7.2 is replaced by a simultaneous continuity argument over all
  lengths `2 ≤ n ≤ n₀` ((7.45) only involves lengths `≤ n`); (7.28) is also proved by the
  continuity argument, from (7.27) at lengths `≤ 2n₀`.
* (7.34) is proved with the constant `C_n = n²`; the maxima of the paper are written as bounds.
* (7.45), (7.46) are hypotheses in the form "`max|L-K| ≺ ` right side" with `sup_u` a real
  `iSup` over `[t₁, t]`; `L_2^{3/2}` is `L_2 · L_2^{1/2}`.
* **(7.29) is used only at `t = t₀` and for `σ = (+, ±)`**, with the GUE-phase 2-loop primitive
  in the closed form `kTwoGUE`; that it is the paper's `K` rests on `kTwoGUE_self` and
  `hasDerivAt_kTwoGUE` (existence) plus uniqueness for the ODE (not formalized).
* (7.47) is stated for `t_1 = (1 - ζ_N) t₀` with `0 ≤ ζ_N ≤ 1` eventually and `|E_N| ≤ 2`; the
  error `(N η_{t₀})^{-3}` of (7.29) is converted to `(N η)^{-3}` with `η_{t₀} = t₀^{1/2} η`,
  `t₀ ≥ 1/16` (`lemT_queZ_ge`, needs `η ≤ 1`), at the cost of `W^{δ/2} → W^δ`.
* (7.29) itself (the §5.8 argument for the GUE phase) and (2.26) are not formalized.
-/

namespace RBM

namespace GUEPhase

open Matrix Finset Filter

/-! ### (7.25): the variance profile `S̃ = (1 - ζ_U) S + ζ_U / N` -/

section Variance

variable (L W : ℕ)

/-- `(S^{(B)}_{GUE})_{ab} = 1/L`. -/
noncomputable def SBgue : Matrix (ZMod L) (ZMod L) ℂ := Matrix.of fun _ _ => (L : ℂ)⁻¹

@[simp] theorem SBgue_apply (a b : ZMod L) : SBgue L a b = (L : ℂ)⁻¹ := rfl

end Variance

/-! ### The continuity argument -/

section Continuity

open Set

/-- **The continuity argument** used for (7.36) and (7.27), (7.28): finitely many continuous
quantities `f i` start strictly below the continuous thresholds `g i` at `t₁`, and whenever all
of them are below their thresholds on `[t₁, t]`, they are strictly below at `t` (the bootstrap
improvement).  Then they stay strictly below on all of `[t₁, t₀]`. -/
theorem continuity_argument {ι : Type*} {S : Set ι} (hS : S.Finite) {f g : ι → ℝ → ℝ}
    {t1 t0 : ℝ} (hf : ∀ i ∈ S, ContinuousOn (f i) (Icc t1 t0))
    (hg : ∀ i ∈ S, ContinuousOn (g i) (Icc t1 t0)) (h0 : ∀ i ∈ S, f i t1 < g i t1)
    (hstep : ∀ t ∈ Icc t1 t0, (∀ u ∈ Icc t1 t, ∀ i ∈ S, f i u ≤ g i u) →
      ∀ i ∈ S, f i t < g i t) :
    ∀ t ∈ Icc t1 t0, ∀ i ∈ S, f i t < g i t := by
  by_contra hno
  push Not at hno
  set F : Set ℝ := {t | t ∈ Icc t1 t0 ∧ ∃ i ∈ S, g i t ≤ f i t} with hFdef
  have hFeq : F = ⋃ i ∈ S, {t | t ∈ Icc t1 t0 ∧ g i t ≤ f i t} := by
    ext t
    simp only [hFdef, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨ht, i, hi, h⟩; exact ⟨i, hi, ht, h⟩
    · rintro ⟨i, hi, ht, h⟩; exact ⟨ht, i, hi, h⟩
  have hFc : IsClosed F := by
    rw [hFeq]
    exact hS.isClosed_biUnion fun i hi => isClosed_Icc.isClosed_le (hg i hi) (hf i hi)
  obtain ⟨t, ht, i, hi, hti⟩ := hno
  have hFne : F.Nonempty := ⟨t, ht, i, hi, hti⟩
  have hFbdd : BddBelow F := ⟨t1, fun x hx => hx.1.1⟩
  set T := sInf F with hT
  have hTF : T ∈ F := hFc.csInf_mem hFne hFbdd
  have hT1 : t1 ≤ T := hTF.1.1
  have hTne : T ≠ t1 := by
    intro h
    obtain ⟨-, j, hj, hle⟩ := hTF
    rw [h] at hle
    exact absurd (h0 j hj) (not_lt.2 hle)
  have hT1' : t1 < T := lt_of_le_of_ne hT1 (Ne.symm hTne)
  have hbelow : ∀ u ∈ Ico t1 T, ∀ j ∈ S, f j u < g j u := by
    intro u hu j hj
    by_contra hle
    push Not at hle
    have huF : u ∈ F := ⟨⟨hu.1, (hu.2.le.trans hTF.1.2)⟩, j, hj, hle⟩
    exact absurd (csInf_le hFbdd huF) (not_le.2 hu.2)
  have hsub : Ico t1 T ⊆ Icc t1 t0 := fun u hu => ⟨hu.1, hu.2.le.trans hTF.1.2⟩
  have hcl : T ∈ closure (Ico t1 T) := by
    rw [closure_Ico hTne.symm]
    exact ⟨hT1, le_rfl⟩
  have hTle : ∀ j ∈ S, f j T ≤ g j T := by
    intro j hj
    exact ContinuousWithinAt.closure_le hcl (((hf j hj) T hTF.1).mono hsub)
      (((hg j hj) T hTF.1).mono hsub) fun y hy => (hbelow y hy j hj).le
  have hall : ∀ u ∈ Icc t1 T, ∀ j ∈ S, f j u ≤ g j u := by
    intro u hu j hj
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hTle j hj
    · exact (hbelow u ⟨hu.1, h⟩ j hj).le
  obtain ⟨hTI, j, hj, hle⟩ := hTF
  exact absurd (hstep T hTI hall j hj) (not_lt.2 hle)

end Continuity

/-! ### (7.30): the scales of the GUE phase -/

section Scales

/-- **(7.30) ⟹ `ℓ_{t₁} = L`**: `ℓ̂(t) = L` as soon as `L² (1 - t) ≤ 1`. -/
theorem ellHat_eq_L {L : ℕ} {t : ℝ} (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ 1) :
    ellHat L (t : ℂ) = L := by
  rw [ellHat_ofReal L ht, min_eq_right]
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hs]
  have h1 : ((L : ℝ) * Real.sqrt (1 - t)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; exact h
  nlinarith [Real.sqrt_nonneg (1 - t), (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

end Scales

/-! ### (7.33), (7.34), (7.39), (7.40): the hierarchy with `S^{(B)} → S^{(B)}_{GUE}` -/

section Hierarchy

variable (L : ℕ) [NeZero L]

/-- The polarized right side of the primitive equation of the GUE phase ((7.33) with independent
left and right factors): `W ∑_{1≤k<l≤n} ∑_{a,b} K(G^{(a),L}_{k,l}) (S^{(B)}_{GUE})_{ab}
K'(G^{(b),R}_{k,l})`, `(S^{(B)}_{GUE})_{ab} = 1/L`. -/
noncomputable def primBilGUE (W : ℕ) (K K' : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  (W : ℂ) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length, ∑ a : ZMod L, ∑ b : ZMod L,
    K (I.cutGlueL k l a) * SBgue L a b * K' (I.cutGlueR k l b)

/-- **(7.33)**: the right side of the primitive equation of the GUE phase,
`d/dt K_{t,σ,a} = W ∑_{k<l} ∑_{a,b} (G^{(a),L}_{k,l} ∘ K) (S^{(B)}_{GUE})_{ab}
(G^{(b),R}_{k,l} ∘ K)`
(the standard (2.48) with `S^{(B)} → S^{(B)}_{GUE}`). -/
noncomputable def primRhsGUE (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) : ℂ :=
  primBilGUE L W K K I

theorem primBilGUE_add_left (W : ℕ) (K₁ K₂ K' : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBilGUE L W (K₁ + K₂) K' I = primBilGUE L W K₁ K' I + primBilGUE L W K₂ K' I := by
  simp only [primBilGUE, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem primBilGUE_add_right (W : ℕ) (K K₁ K₂ : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBilGUE L W K (K₁ + K₂) I = primBilGUE L W K K₁ I + primBilGUE L W K K₂ I := by
  simp only [primBilGUE, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **The GUE-phase version of (5.12)/(5.13)**: the loop hierarchy and the primitive equation
of the GUE phase share their quadratic term, so `d/dt (L - K)` has the drift
`[K ∼ (L-K)] + [(L-K) ∼ K] + E^{((L-K)×(L-K))}`, all with `S^{(B)}_{GUE}` in place of `S^{(B)}`
(the terms (7.39), (7.40)). -/
theorem primRhsGUE_sub (W : ℕ) (Lf K : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primRhsGUE L W Lf I - primRhsGUE L W K I
      = primBilGUE L W K (Lf - K) I + primBilGUE L W (Lf - K) K I
        + primBilGUE L W (Lf - K) (Lf - K) I := by
  have hLf : Lf = K + (Lf - K) := by funext x; simp
  have h1 : primRhsGUE L W Lf I = primBilGUE L W (K + (Lf - K)) (K + (Lf - K)) I := by
    rw [primRhsGUE, ← hLf]
  rw [h1, primBilGUE_add_left, primBilGUE_add_right, primBilGUE_add_right, primRhsGUE]
  ring

/-- **The power counting behind (7.34), (7.39), (7.40)**: if `|K J| ≤ B(|J|)` and
`|K' J| ≤ B'(|J|)` for all well-formed loops `J` of length `2 ≤ |J| ≤ n = |I|`, then
`|W ∑_{k<l} ∑_{a,b} K(G^{L}) (S_{GUE})_{ab} K'(G^{R})| ≤ n² N ∑_{2≤j≤n} B(n-j+2) B'(j)`,
`N = W L`.  Since `S^{(B)}_{GUE}` is the constant `1/L`, the double sum over `a, b` costs exactly
a factor `L` (where the band `S^{(B)}` would cost `O(1)`); this is the factor `N = W L` of
(7.34). -/
theorem norm_primBilGUE_le (W : ℕ) (K K' : LoopIdx (ZMod L) → ℂ) (B B' : ℕ → ℝ)
    (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hB : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ B J.length)
    (hB' : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K' J‖ ≤ B' J.length)
    (hB0 : ∀ j, 0 ≤ B j) (hB0' : ∀ j, 0 ≤ B' j) :
    ‖primBilGUE L W K K' I‖ ≤ (I.length : ℝ) ^ 2 * ((W * L : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B' j := by
  set n := I.length with hn
  set Sm := ∑ j ∈ Icc 2 n, B (n - j + 2) * B' j with hSm
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hSm0 : 0 ≤ Sm := Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0' _)
  -- one pair `(k, l)`
  have hpair : ∀ k ∈ Icc 1 n, ∀ l ∈ Ioc k n,
      ‖∑ a : ZMod L, ∑ b : ZMod L, K (I.cutGlueL k l a) * SBgue L a b * K' (I.cutGlueR k l b)‖
        ≤ (L : ℝ) * Sm := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hlenL : ∀ a : ZMod L, (I.cutGlueL k l a).length = n - (l - k + 1) + 2 := by
      intro a; rw [LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2]; omega
    have hlenR : ∀ b : ZMod L, (I.cutGlueR k l b).length = l - k + 1 := by
      intro b; rw [LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2]
    have hBL : ∀ a : ZMod L, ‖K (I.cutGlueL k l a)‖ ≤ B (n - (l - k + 1) + 2) := by
      intro a
      rw [← hlenL a]
      refine hB _ (LoopIdx.WF.cutGlueL a hI hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
    have hBR : ∀ b : ZMod L, ‖K' (I.cutGlueR k l b)‖ ≤ B' (l - k + 1) := by
      intro b
      rw [← hlenR b]
      refine hB' _ (LoopIdx.WF.cutGlueR b hI hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
    have hj : l - k + 1 ∈ Icc 2 n := by rw [Finset.mem_Icc]; omega
    have hterm : B (n - (l - k + 1) + 2) * B' (l - k + 1) ≤ Sm :=
      Finset.single_le_sum (f := fun j => B (n - j + 2) * B' j)
        (fun j _ => mul_nonneg (hB0 _) (hB0' _)) hj
    have hSB : ‖(L : ℂ)⁻¹‖ = (L : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    calc _ ≤ ∑ a : ZMod L, ∑ b : ZMod L,
          ‖K (I.cutGlueL k l a) * SBgue L a b * K' (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ _a : ZMod L, ∑ _b : ZMod L,
          B (n - (l - k + 1) + 2) * (L : ℝ)⁻¹ * B' (l - k + 1) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul, SBgue_apply, hSB]
          have hLi : (0 : ℝ) ≤ (L : ℝ)⁻¹ := inv_nonneg.2 hL0.le
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hBL a) hLi) (hBR b) (norm_nonneg _)
            (mul_nonneg (hB0 _) hLi)
      _ = (L : ℝ) * (B (n - (l - k + 1) + 2) * B' (l - k + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          field_simp
      _ ≤ (L : ℝ) * Sm := mul_le_mul_of_nonneg_left hterm hL0.le
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  calc ‖primBilGUE L W K K' I‖
      ≤ (W : ℝ) * ∑ k ∈ Icc 1 n, ∑ l ∈ Ioc k n, (L : ℝ) * Sm := by
        rw [primBilGUE, norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) * ∑ _k ∈ Icc 1 n, (n : ℝ) * ((L : ℝ) * Sm) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
        exact mul_le_mul_of_nonneg_right this (mul_nonneg hL0.le hSm0)
    _ = (n : ℝ) ^ 2 * ((W * L : ℕ) : ℝ) * Sm := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

/-- **(7.34)**: `|d/dt K_{t,σ,a}| ≤ n² N ∑_{2≤k≤n} max K^{(k)} · max K^{(n-k+2)}`, with the maxima
written as bounds `B`. -/
theorem norm_primRhsGUE_le (W : ℕ) (K : LoopIdx (ZMod L) → ℂ) (B : ℕ → ℝ)
    (I : LoopIdx (ZMod L)) (hI : I.WF)
    (hB : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖K J‖ ≤ B J.length)
    (hB0 : ∀ j, 0 ≤ B j) :
    ‖primRhsGUE L W K I‖ ≤ (I.length : ℝ) ^ 2 * ((W * L : ℕ) : ℝ) *
      ∑ j ∈ Icc 2 I.length, B (I.length - j + 2) * B j :=
  norm_primBilGUE_le L W K K B B I hI hB hB hB0 hB0

end Hierarchy

/-! ### (7.35), (7.36): the continuity bootstrap for `K` -/

section KBootstrap

open Set

/-- `∑_{2≤j≤m} (c x^{m-j+1}) (c x^{j-1}) = (m-1) c² x^m`. -/
theorem sum_pow_mul_pow (c x : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc 2 m, (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1))
      = ((m - 1 : ℕ) : ℝ) * c ^ 2 * x ^ m := by
  have hterm : ∀ j ∈ Finset.Icc 2 m,
      (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1)) = c ^ 2 * x ^ m := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have he : m - j + 2 - 1 + (j - 1) = m := by omega
    rw [show (c * x ^ (m - j + 2 - 1)) * (c * x ^ (j - 1))
      = c ^ 2 * (x ^ (m - j + 2 - 1) * x ^ (j - 1)) by ring, ← pow_add, he]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have : m + 1 - 2 = m - 1 := by omega
  rw [this]; ring

/-- **(7.35) ⟹ (7.36), deterministic core.**  Let `k_i(t)` (`i ∈ S`, finitely many; `i` stands
for `(σ, a)` of a loop of length `|i| ∈ [2, n]`) solve `d/dt k_i = d_i` on `[t₁, t₀]`, where the
drift obeys the power counting (7.34): whenever `|k_j(t)| ≤ B(|j|)` for all `j`,
`|d_i(t)| ≤ C N ∑_{2≤j≤|i|} B(|i|-j+2) B(j)`.  Let `λ_t = N η_t` be positive, continuous and
non-increasing, and let (7.30) hold in the form `N (t - t₁) ≤ ε λ_t`.  If initially
`|k_i(t₁)| ≤ A λ_{t₁}^{-|i|+1}` ((7.32)) and `4 C n A ε < 1`, then
`|k_i(t)| < 2 A λ_t^{-|i|+1}` on `[t₁, t₀]` ((7.36)).  The integration of (7.34) to (7.35) is
the mean value inequality; the continuity argument is `continuity_argument`. -/
theorem K_bootstrap {ι : Type*} {S : Set ι} (hS : S.Finite) (len : ι → ℕ) {n : ℕ}
    (hlen : ∀ i ∈ S, 2 ≤ len i ∧ len i ≤ n) (k d : ℝ → ι → ℂ) {t1 t0 C N A ε : ℝ}
    (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u)
    (hlamc : ContinuousOn lam (Icc t1 t0))
    (hderiv : ∀ t ∈ Icc t1 t0, ∀ i ∈ S, HasDerivWithinAt (fun s => k s i) (d t i) (Icc t1 t0) t)
    (hd : ∀ t ∈ Icc t1 t0, ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → (∀ j ∈ S, ‖k t j‖ ≤ B (len j)) →
      ∀ i ∈ S, ‖d t i‖ ≤ C * N * ∑ j ∈ Finset.Icc 2 (len i), B (len i - j + 2) * B j)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hA : 0 < A)
    (hinit : ∀ i ∈ S, ‖k t1 i‖ ≤ A * (lam t1)⁻¹ ^ (len i - 1))
    (hsmall : ∀ t ∈ Icc t1 t0, N * (t - t1) ≤ ε * lam t) (hε : 4 * C * n * A * ε < 1) :
    ∀ t ∈ Icc t1 t0, ∀ i ∈ S, ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1) := by
  have ht1' : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
  have hkc : ∀ i ∈ S, ContinuousOn (fun t => ‖k t i‖) (Icc t1 t0) := fun i hi =>
    ContinuousOn.norm (f := fun s => k s i) fun t ht => (hderiv t ht i hi).continuousWithinAt
  have hgc : ∀ i ∈ S, ContinuousOn (fun t => 2 * A * (lam t)⁻¹ ^ (len i - 1)) (Icc t1 t0) :=
    fun i _ => continuousOn_const.mul
      ((hlamc.inv₀ fun t ht => (hlam t ht).ne').pow _)
  refine continuity_argument hS hkc hgc (fun i hi => ?_) (fun t ht hprev i hi => ?_)
  · have hpos : 0 < A * (lam t1)⁻¹ ^ (len i - 1) :=
      mul_pos hA (pow_pos (inv_pos.2 (hlam t1 ht1')) _)
    have := hinit i hi
    show ‖k t1 i‖ < 2 * A * (lam t1)⁻¹ ^ (len i - 1)
    linarith
  -- the improvement step at time `t`
  show ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1)
  have hlt := hlam t ht
  set x := (lam t)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hlt
  set m := len i with hm
  obtain ⟨hm2, hmn⟩ := hlen i hi
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  -- bounds on `[t₁, t]` in terms of `λ_t`
  set Bt : ℕ → ℝ := fun j => 2 * A * x ^ (j - 1) with hBt
  have hBt0 : ∀ j, 0 ≤ Bt j := fun j => by positivity
  have hkB : ∀ u ∈ Icc t1 t, ∀ j ∈ S, ‖k u j‖ ≤ Bt (len j) := by
    intro u hu j hj
    have hu0 := hsub hu
    have h1 : ‖k u j‖ ≤ 2 * A * (lam u)⁻¹ ^ (len j - 1) := hprev u hu j hj
    have hxu : (lam u)⁻¹ ≤ x := inv_anti₀ hlt (hanti u hu0 t ht hu.2)
    refine h1.trans ?_
    simp only [hBt]
    gcongr
    exact (inv_pos.2 (hlam u hu0)).le
  -- the drift bound on `[t₁, t]`
  have hdB : ∀ u ∈ Ico t1 t, ‖d u i‖ ≤ C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) := by
    intro u hu
    have hu' : u ∈ Icc t1 t := Ico_subset_Icc_self hu
    have h := hd u (hsub hu') Bt hBt0 (fun j hj => hkB u hu' j hj) i hi
    rw [← sum_pow_mul_pow]
    exact h
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => k s i) (fun u hu => (hderiv u (hsub hu) i hi).mono hsub) hdB t ⟨ht1t, le_rfl⟩
  -- `λ_{t₁}^{-1} ≤ λ_t^{-1}`
  have hx1 : (lam t1)⁻¹ ≤ x := inv_anti₀ hlt (hanti t1 ht1' t ht ht1t)
  have hinit' : ‖k t1 i‖ ≤ A * x ^ (m - 1) := by
    refine (hinit i hi).trans ?_
    gcongr
    exact (inv_pos.2 (hlam t1 ht1')).le
  -- `C N (m-1)(2A)² x^m (t - t₁) ≤ 4 C n A² ε x^{m-1}`
  have hxm : x ^ m * lam t = x ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    rw [this, pow_succ, Nat.add_sub_cancel, mul_assoc, hx, inv_mul_cancel₀ hlt.ne', mul_one]
  have hkey : C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1)
      ≤ 4 * C * n * A * ε * (A * x ^ (m - 1)) := by
    have hm1 : ((m - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le m 1).trans hmn
    have hsm := hsmall t ht
    have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN (by linarith)
    calc C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1)
        = C * ((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m * (N * (t - t1)) := by ring
      _ ≤ C * n * (2 * A) ^ 2 * x ^ m * (ε * lam t) := by gcongr
      _ = 4 * C * n * A * ε * (A * (x ^ m * lam t)) := by ring
      _ = 4 * C * n * A * ε * (A * x ^ (m - 1)) := by rw [hxm]
  have hmvt' :
      ‖k t i‖ ≤ ‖k t1 i‖ + C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1) := by
    have := norm_sub_norm_le (k t i) (k t1 i)
    have h2 : ‖k t i - k t1 i‖ ≤ C * N * (((m - 1 : ℕ) : ℝ) * (2 * A) ^ 2 * x ^ m) * (t - t1) :=
      hmvt
    linarith
  have hpos : 0 < A * x ^ (m - 1) := mul_pos hA (pow_pos hx0 _)
  nlinarith

/-- Well-formed loop indices of bounded length form a finite set. -/
theorem finite_loopIdx (L : ℕ) [NeZero L] (n : ℕ) :
    {I : LoopIdx (ZMod L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}.Finite := by
  refine (((List.finite_length_le Bool n).prod (List.finite_length_le (ZMod L) n)).image
    (fun p : List Bool × List (ZMod L) => (⟨p.1, p.2⟩ : LoopIdx (ZMod L)))).subset ?_
  rintro ⟨σ, a⟩ ⟨hWF, -, hn⟩
  simp only [LoopIdx.WF, LoopIdx.length] at hWF hn
  exact ⟨(σ, a), ⟨show σ.length ≤ n by omega, show a.length ≤ n from hn⟩, rfl⟩

/-- **(7.36)** for the primitive loops of the GUE phase: if `K_t` solves the GUE-phase primitive
equation (7.33) (`RBM.GUEPhase.primRhsGUE`) on `[t₁, t₀]` for all loops of length `2 ≤ |I| ≤ n`,
`|K_{t₁, I}| ≤ A (N η_{t₁})^{-|I|+1}` ((7.32)), and (7.30) holds as `N (t - t₁) ≤ ε N η_t`
(`N = W L`), with `4 n³ A ε < 1`, then `|K_{t, I}| < 2 A (N η_t)^{-|I|+1}` on `[t₁, t₀]`. -/
theorem eq736 (L W : ℕ) [NeZero L] (Kt : ℝ → LoopIdx (ZMod L) → ℂ) {n : ℕ} {t1 t0 A ε : ℝ}
    (ht10 : t1 ≤ t0) (lam : ℝ → ℝ) (hlam : ∀ t ∈ Icc t1 t0, 0 < lam t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → lam t ≤ lam u)
    (hlamc : ContinuousOn lam (Icc t1 t0))
    (hK : ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → I.length ≤ n →
      HasDerivWithinAt (fun s => Kt s I) (primRhsGUE L W (Kt t) I) (Icc t1 t0) t)
    (hA : 0 < A)
    (hinit : ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t1 I‖ ≤ A * (lam t1)⁻¹ ^ (I.length - 1))
    (hsmall : ∀ t ∈ Icc t1 t0, ((W * L : ℕ) : ℝ) * (t - t1) ≤ ε * lam t)
    (hε : 4 * ((n : ℝ) ^ 2) * n * A * ε < 1) :
    ∀ t ∈ Icc t1 t0, ∀ I : LoopIdx (ZMod L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t I‖ < 2 * A * (lam t)⁻¹ ^ (I.length - 1) := by
  set S := {I : LoopIdx (ZMod L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n} with hSdef
  have hS : S.Finite := finite_loopIdx L n
  have key := K_bootstrap (S := S) hS LoopIdx.length (n := n)
    (fun I hI => ⟨hI.2.1, hI.2.2⟩) Kt (fun t I => primRhsGUE L W (Kt t) I)
    (C := (n : ℝ) ^ 2) (N := ((W * L : ℕ) : ℝ)) ht10 lam hlam hanti hlamc
    (fun t ht I hI => hK t ht I hI.1 hI.2.1 hI.2.2) ?_ (by positivity) (by positivity) hA
    (fun I hI => hinit I hI.1 hI.2.1 hI.2.2) hsmall hε
  · intro t ht I hWF h2 hn
    exact key t ht I ⟨hWF, h2, hn⟩
  · intro t _ B hB0 hB I hI
    have h := norm_primRhsGUE_le L W (Kt t) B I hI.1
      (fun J hJ h2 hJI => hB J ⟨hJ, h2, hJI.trans hI.2.2⟩) hB0
    refine h.trans ?_
    have hsum : 0 ≤ ∑ j ∈ Finset.Icc 2 I.length, B (I.length - j + 2) * B j :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hB0 _) (hB0 _)
    have hlen : (I.length : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : (I.length : ℝ) ≤ n := by exact_mod_cast hI.2.2
      gcongr
    gcongr

/-- Well-formed loop indices of length `2 ≤ |I| ≤ n` (the `(σ, a)` of the maxima in (7.27),
(7.28), (7.36)). -/
abbrev LoopSet (L : ℕ) (n : ℕ) : Type :=
  {I : LoopIdx (ZMod L) // I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}

/-- `4 n³ N^{τ'} N^{-τ_U} < 1` for large `N`, if `τ' < τ_U`. -/
theorem eventually_small {n : ℕ} {τ' τU : ℝ} (h : τ' < τU) :
    ∀ᶠ N : ℕ in atTop, 4 * ((n : ℝ) ^ 2) * n * (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) < 1 := by
  filter_upwards [eventually_le_rpow (8 * (n : ℝ) ^ 3 + 1) (sub_pos.2 h),
    eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (τU - τ') := Real.rpow_pos_of_pos hN0 _
  have he : (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) = ((N : ℝ) ^ (τU - τ'))⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; ring_nf
  have hn0 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  rw [mul_assoc, he, show 4 * (n : ℝ) ^ 2 * n = 4 * (n : ℝ) ^ 3 by ring, ← div_eq_mul_inv,
    div_lt_one hpos]
  linarith

/-- **(7.36)** `max_{σ,a} |K_{t,σ,a}| ≺ (N η_t)^{-n+1}`, uniformly in `t ∈ [t₁, t₀]` and the
loops of length `2 ≤ |I| ≤ n`, from (7.32) `K_{t₁} ≺ (N η_{t₁})^{-n+1}` and (7.30) in the form
`N (t - t₁) ≤ N^{-τ_U} · N η_t`, for a solution of the GUE-phase primitive equation
(7.33).  Here `λ_t = N η_t` is any positive, continuous, non-increasing scale, and `N = W L` is
the matrix size (the `≺` is in the sequence index `N`). -/
theorem eq736_detDom (Lf Wf : ℕ → ℕ) [∀ N, NeZero (Lf N)]
    (Kt : ∀ N, ℝ → LoopIdx (ZMod (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
    (ht10 : ∀ N, t1 N ≤ t0 N) (lam : ℕ → ℝ → ℝ)
    (hlam : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < lam N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → lam N t ≤ lam N u)
    (hlamc : ∀ N, ContinuousOn (lam N) (Icc (t1 N) (t0 N)))
    (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (ZMod (Lf N)), I.WF → 2 ≤ I.length →
      I.length ≤ n →
      HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE (Lf N) (Wf N) (Kt N t) I)
        (Icc (t1 N) (t0 N)) t)
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N),
      ((Wf N * Lf N : ℕ) : ℝ) * (t - t1 N) ≤ (N : ℝ) ^ (-τU) * lam N t)
    (h732 : UnifDetDom (fun N (I : LoopSet (Lf N) n) => ‖Kt N (t1 N) I.1‖)
      (fun N I => (lam N (t1 N))⁻¹ ^ (I.1.length - 1))) :
    UnifDetDom (fun N (p : TimeIcc t1 t0 N × LoopSet (Lf N) n) => ‖Kt N p.1 p.2.1‖)
      (fun N p => (lam N p.1)⁻¹ ^ (p.2.1.length - 1)) := by
  intro τ hτ
  set τ' := min τ τU / 2 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : τ' < τU := by have := min_le_right τ τU; linarith
  filter_upwards [h732 τ' hτ'0, h730, eventually_small (n := n) hτ'U,
    eventually_le_rpow 2 (sub_pos.2 hτ'τ), eventually_ge_atTop 1] with N hinit hsm hε h2 hN1
  rintro ⟨⟨t, ht⟩, I, hI⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hA : 0 < (N : ℝ) ^ τ' := Real.rpow_pos_of_pos hN0 _
  have key := eq736 (Lf N) (Wf N) (Kt N) (ht10 N) (lam N) (hlam N) (hanti N) (hlamc N) (hK N)
    hA (fun J hJ h2J hJn => hinit ⟨J, hJ, h2J, hJn⟩) hsm
    (by simpa [mul_assoc] using hε) t ht I hI.1 hI.2.1 hI.2.2
  have hx : 0 ≤ (lam N t)⁻¹ ^ (I.length - 1) := pow_nonneg (inv_pos.2 (hlam N t ht)).le _
  have hsplit : (N : ℝ) ^ τ = (N : ℝ) ^ (τ - τ') * (N : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; ring_nf
  show ‖Kt N t I‖ ≤ (N : ℝ) ^ τ * (lam N t)⁻¹ ^ (I.length - 1)
  rw [hsplit]
  have : 2 * (N : ℝ) ^ τ' * (lam N t)⁻¹ ^ (I.length - 1)
      ≤ (N : ℝ) ^ (τ - τ') * (N : ℝ) ^ τ' * (lam N t)⁻¹ ^ (I.length - 1) := by
    gcongr
  linarith

end KBootstrap

/-! ### (7.45) ⟹ (7.27) and (7.46) ⟹ (7.28): the pathwise bootstrap for `L` -/

section LBootstrap

open Set

/-- `sup_{u ∈ [a, b]} g(u)` (a conditionally complete supremum; only upper bounds are used). -/
noncomputable def supOn (g : ℝ → ℝ) (a b : ℝ) : ℝ := ⨆ u : Icc a b, g u

theorem supOn_le {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (h : ∀ u ∈ Icc a b, g u ≤ c) :
    supOn g a b ≤ c := by
  have : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  exact ciSup_le fun u => h u u.2

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

/-- The first line of (7.45)/(7.46) under bounds `D_j(u) ≤ c x^{j-1+e}` (`x = (Nη_t)^{-1} ≤ 1`,
`e ∈ {0, 1}`): `sup_u ∑_k ((Nη_u)^{-k+1} + D_k) D_{n-k+2} ≤ n (1 + c) c x^{n+e}`. -/
theorem supOn_line1_le {Dm : ℕ → ℝ → ℝ} {n : ℕ} {t c x : ℝ} (e : ℕ) (he : e ≤ 1)
    (ht1t : t1 ≤ t) (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x)
    (hD : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n → 0 ≤ Dm j u ∧ Dm j u ≤ c * x ^ (j - 1 + e)) :
    supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
      ≤ n * ((1 + c) * c * x ^ (n + e)) := by
  refine supOn_le ht1t fun u hu => ?_
  have hterm : ∀ k ∈ Finset.Icc 2 n, ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u
      ≤ (1 + c) * c * x ^ (n + e) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hDk0, hDk⟩ := hD u hu k hk.1 hk.2
    obtain ⟨hDn0, hDn⟩ := hD u hu (n - k + 2) (by omega) (by omega)
    have h1 : (N * η u)⁻¹ ^ (k - 1) ≤ x ^ (k - 1) := pow_le_pow_left₀ (hxu u hu).1 (hxu u hu).2 _
    have h2 : x ^ (k - 1 + e) ≤ x ^ (k - 1) := pow_le_pow_of_le_one hx0 hx1 (by omega)
    have h3 : (N * η u)⁻¹ ^ (k - 1) + Dm k u ≤ (1 + c) * x ^ (k - 1) := by nlinarith
    have hexp : k - 1 + (n - k + 2 - 1 + e) = n + e := by omega
    calc ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u
        ≤ ((1 + c) * x ^ (k - 1)) * (c * x ^ (n - k + 2 - 1 + e)) :=
          mul_le_mul h3 hDn hDn0 (by positivity)
      _ = (1 + c) * c * x ^ (n + e) := by rw [← hexp, pow_add]; ring
  calc _ ≤ ∑ _k ∈ Finset.Icc 2 n, (1 + c) * c * x ^ (n + e) := Finset.sum_le_sum hterm
    _ = ((n + 1 - 2 : ℕ) : ℝ) * ((1 + c) * c * x ^ (n + e)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ n * ((1 + c) * c * x ^ (n + e)) := by
        gcongr
        exact_mod_cast (by omega : n + 1 - 2 ≤ n)

/-- `N(t - t₁) · y ≤ ε x^{-1} y` from (7.30) in the form `t - t₁ ≤ ε η_t`, `x = (Nη_t)^{-1}`. -/
theorem mul_le_of_eq730 {t ε y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) (hsm : t - t1 ≤ ε * η t) :
    N * (t - t1) * y ≤ ε * ((N * η t)⁻¹)⁻¹ * y := by
  rw [inv_inv]
  have : N * (t - t1) ≤ ε * (N * η t) := by nlinarith
  exact mul_le_mul_of_nonneg_right this hy

/-- The martingale line: `|t - t₁|^{1/2} (N^{-1} η_t^{-2})^{1/2} = (ε (Nη_t)^{-1})^{1/2}` at most,
under (7.30) `t - t₁ ≤ ε η_t`. -/
theorem sqrt_mul_sqrt_le {t ε : ℝ} (hN : 0 < N) (hηt : 0 < η t) (ht1t : t1 ≤ t)
    (hsm : t - t1 ≤ ε * η t) :
    Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) ≤ Real.sqrt (ε * (N * η t)⁻¹) := by
  rw [← Real.sqrt_mul (by linarith)]
  refine Real.sqrt_le_sqrt ?_
  have h0 : 0 ≤ N⁻¹ * (η t)⁻¹ ^ 2 := by positivity
  calc (t - t1) * (N⁻¹ * (η t)⁻¹ ^ 2) ≤ ε * η t * (N⁻¹ * (η t)⁻¹ ^ 2) :=
        mul_le_mul_of_nonneg_right hsm h0
    _ = ε * (N * η t)⁻¹ := by field_simp


/-- `sup_{[a,b]} g ≥ 0` for `g ≥ 0` on `[a, b]`. -/
theorem supOn_nonneg {g : ℝ → ℝ} {a b : ℝ} (h : ∀ u ∈ Icc a b, 0 ≤ g u) : 0 ≤ supOn g a b :=
  Real.iSup_nonneg fun u => h u u.2

/-- `x^{-1} x^n = x^{n-1}` for `n ≥ 1`. -/
theorem inv_mul_pow {x : ℝ} (hx : x ≠ 0) {n : ℕ} (hn : 1 ≤ n) : x⁻¹ * x ^ n = x ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

end LBootstrap

/-! ### The 2-loop primitive of the GUE phase and the zero mode (7.25) -/

section TwoLoop

variable (L W : ℕ) [NeZero L]

/-- The zero-mode coefficient `β(t) = (t - t₁) μ / (L (1 - t₁ μ)(1 - t μ))`. -/
noncomputable def gueShift (μ : ℂ) (t1 t : ℝ) : ℂ :=
  ((t : ℂ) - t1) * μ / ((L : ℂ) * (1 - (t1 : ℂ) * μ) * (1 - (t : ℂ) * μ))

/-- **The 2-loop primitive of the GUE phase** (the solution of (7.33) for `n = 2` on `[t₁, t₀]`
started from (2.57) at `t₁`): `K_{t,σ,(a,b)} = W⁻¹ μ (Θ_{t₁μ} + β(t) J)_{ab}`, `μ = m(σ₁)m(σ₂)`.
By Sherman–Morrison (`RBM.ThetaTilde_eq`) this is
`W⁻¹ μ [(1 - t₁μ S^{(B)} - (t-t₁)μ S^{(B)}_{GUE})⁻¹]_{ab}` (`kTwoGUE_eq_ThetaTilde`). -/
noncomputable def kTwoGUE (m : Bool → ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool) (a b : ZMod L) : ℂ :=
  (W : ℂ)⁻¹ * (m σ₁ * m σ₂) *
    (Theta L ((t1 : ℂ) * (m σ₁ * m σ₂)) a b + gueShift L (m σ₁ * m σ₂) t1 t)

/-- At `t = t₁` the GUE-phase 2-loop primitive is the standard one (2.57): `K` is continuous across
the switch of the flow at `t₁` (§7.2: `K_{t,σ,a} = K_{t,σ,a}` for `t ≤ t₁`). -/
theorem kTwoGUE_self (m : Bool → ℂ) (t1 : ℝ) (σ₁ σ₂ : Bool) (a b : ZMod L) :
    kTwoGUE L W m t1 t1 σ₁ σ₂ a b = kTwo L W m t1 σ₁ σ₂ a b := by
  simp [kTwoGUE, gueShift, kTwo]

/-- **(7.25) and the zero mode**: at `t₀`, with `t₁ = (1 - ζ_U) t₀`, the 2-loop primitive of the GUE
phase is `W⁻¹ μ ((1 - ξ S̃^{(B)})⁻¹)_{ab}`, `ξ = t₀ μ`, `S̃^{(B)} = (1 - ζ_U) S^{(B)} + ζ_U/L`. -/
theorem kTwoGUE_eq_ThetaTilde (hL : 3 ≤ L) (m : Bool → ℂ) {ζ t0 : ℝ} (σ₁ σ₂ : Bool)
    (hT : ‖(t0 : ℂ) * (m σ₁ * m σ₂) * (1 - (ζ : ℂ))‖ < 1) (hξ1 : (t0 : ℂ) * (m σ₁ * m σ₂) ≠ 1)
    (a b : ZMod L) :
    kTwoGUE L W m ((1 - ζ) * t0) t0 σ₁ σ₂ a b
      = (W : ℂ)⁻¹ * (m σ₁ * m σ₂) * ThetaTilde L (ζ : ℂ) ((t0 : ℂ) * (m σ₁ * m σ₂)) a b := by
  rw [ThetaTilde_apply L hL hT hξ1, kTwoGUE, gueShift, zeroMode]
  have e1 : (((1 - ζ) * t0 : ℝ) : ℂ) * (m σ₁ * m σ₂)
      = (t0 : ℂ) * (m σ₁ * m σ₂) * (1 - (ζ : ℂ)) := by
    push_cast; ring
  rw [e1]
  congr 2
  push_cast
  ring

/-- `t K_{t,(+,-),(a,b)}` of the GUE phase at the spectral parameter of Lemma 2.8
(`t₀ = |m_sc(z)|²`, `t₁ = (1 - ζ) t₀`): `W⁻¹ |m_sc|² ((1 - |m_sc|² S̃^{(B)})⁻¹)_{ab}`, the main term
of the first line of (7.47). -/
theorem lemT_mul_kTwoGUE_pm (hL : 3 ≤ L) {z : ℂ} (hz : 0 < z.im) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ ≤ 1) (a b : ZMod L) :
    (lemT z : ℂ) * kTwoGUE L W (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true false a b =
      (W : ℂ)⁻¹ * ((‖msc z‖ ^ 2 : ℝ) : ℂ) * ThetaTilde L (ζ : ℂ) ((‖msc z‖ ^ 2 : ℝ) : ℂ) a b := by
  have hμ : mSigma (lemE z) true * mSigma (lemE z) false = 1 :=
    mSigma_mul_of_ne (abs_lemE_lt_two hz).le (by decide)
  have ht0 := lemT_pos hz
  have ht1 := lemT_lt_one hz
  have hT :
      ‖(lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) false) * (1 - (ζ : ℂ))‖ < 1 := by
    rw [hμ, mul_one,
      show (lemT z : ℂ) * (1 - (ζ : ℂ)) = ((lemT z * (1 - ζ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
    nlinarith
  have hξ1 : (lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) false) ≠ 1 := by
    rw [hμ, mul_one]
    exact_mod_cast ht1.ne
  rw [kTwoGUE_eq_ThetaTilde L W hL _ true false hT hξ1, hμ]
  simp only [mul_one, lemT]
  ring

/-- `t K_{t,(+,+),(a,b)}` of the GUE phase at the spectral parameter of Lemma 2.8:
`W⁻¹ m_sc² ((1 - m_sc² S̃^{(B)})⁻¹)_{ab}`, the main term of the second line of (7.47). -/
theorem lemT_mul_kTwoGUE_pp (hL : 3 ≤ L) {z : ℂ} (hz : 0 < z.im) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ ≤ 1) (a b : ZMod L) :
    (lemT z : ℂ) * kTwoGUE L W (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true true a b =
      (W : ℂ)⁻¹ * msc z ^ 2 * ThetaTilde L (ζ : ℂ) (msc z ^ 2) a b := by
  have h : msc z ^ 2 = (lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true) := by
    rw [msc_eq_sqrt_mul_mE hz, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (lemT_pos hz).le]
    simp only [mSigma, ite_true]
    ring
  have hE := (abs_lemE_lt_two hz).le
  have ht0 := lemT_pos hz
  have ht1 := lemT_lt_one hz
  have hnorm : ‖(lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true)‖ = lemT z := by
    rw [norm_mul, norm_mul, norm_mSigma hE, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    ring
  have hT : ‖(lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true) * (1 - (ζ : ℂ))‖ < 1 := by
    rw [norm_mul, hnorm, show (1 : ℂ) - (ζ : ℂ) = ((1 - ζ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    nlinarith
  have hξ1 : (lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true) ≠ 1 := by
    intro h1
    have := congrArg norm h1
    rw [hnorm, norm_one] at this
    linarith
  rw [kTwoGUE_eq_ThetaTilde L W hL _ true true hT hξ1, ← h]
  have e : (lemT z : ℂ) * ((W : ℂ)⁻¹ * (mSigma (lemE z) true * mSigma (lemE z) true)
      * ThetaTilde L (ζ : ℂ) (msc z ^ 2) a b)
      = (W : ℂ)⁻¹ * ((lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true))
      * ThetaTilde L (ζ : ℂ) (msc z ^ 2) a b := by ring
  rw [e, ← h]

/-- The right side of (7.33) at `n = 2`, written without the cut-and-glue operators:
`W ∑_{a,b} K_{σ,(a₁,a)} (S^{(B)}_{GUE})_{ab} K_{σ,(b,a₂)}` (as `RBM.primRhs_two` for (2.55)). -/
theorem primRhsGUE_two (K : LoopIdx (ZMod L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    primRhsGUE L W K ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          K ⟨[σ₁, σ₂], [a₁, a]⟩ * SBgue L a b * K ⟨[σ₁, σ₂], [b, a₂]⟩ := by
  have h12 : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have h1 : Ioc 1 2 = ({2} : Finset ℕ) := by decide
  have h2 : Ioc 2 2 = (∅ : Finset ℕ) := by decide
  have hlen : (LoopIdx.mk [σ₁, σ₂] [a₁, a₂]).length = 2 := rfl
  rw [primRhsGUE, primBilGUE, hlen, h12, Finset.sum_pair (by norm_num), h1, h2,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change K ⟨[σ₁, σ₂], [b, a₂]⟩ * SBgue L b a * K ⟨[σ₁, σ₂], [a₁, a]⟩ = _
  simp only [SBgue_apply]
  ring

/-- The scalar identity behind `hasDerivAt_kTwoGUE`: with `q + dμ = p`
(`p = 1 - t₁μ`, `q = 1 - tμ`, `d = t - t₁`), the derivative of `W⁻¹ μ dμ/(Lpq)` equals
`W⁻¹ μ² L⁻¹ (p⁻¹ + L dμ/(Lpq))²`; both are `W⁻¹ μ² / (L q²)`. -/
theorem kTwoGUE_deriv_identity (W μ p q d L : ℂ) (h : q + d * μ = p) (hp : p ≠ 0) (hq : q ≠ 0)
    (hL : L ≠ 0) :
    W⁻¹ * μ * ((μ * (L * p * q) - d * μ * (L * p * -μ)) / (L * p * q) ^ 2)
      = W⁻¹ * μ ^ 2 * L⁻¹ *
        ((p⁻¹ + L * (d * μ / (L * p * q))) * (p⁻¹ + L * (d * μ / (L * p * q)))) := by
  have e1 : μ * (L * p * q) - d * μ * (L * p * -μ) = μ * L * p * p := by rw [← h]; ring
  have e2 : p⁻¹ + L * (d * μ / (L * p * q)) = q⁻¹ := by
    have : L * (d * μ / (L * p * q)) = d * μ / (p * q) := by field_simp
    rw [this, inv_eq_one_div, inv_eq_one_div, div_add_div _ _ hp (mul_ne_zero hp hq),
      div_eq_div_iff (mul_ne_zero hp (mul_ne_zero hp hq)) hq, ← h]
    ring
  rw [e1, e2]
  field_simp

/-- **(7.33) at `n = 2`**: the closed form `kTwoGUE` solves the primitive equation of the GUE
phase, `d/dt K_{t,σ,(a₁,a₂)} = W ∑_{a,b} K_{t,σ,(a₁,a)} (S^{(B)}_{GUE})_{ab} K_{t,σ,(b,a₂)}`, as
long as `|t₁ μ| < 1` and `t μ ≠ 1`.  (Together with `kTwoGUE_self` this identifies `kTwoGUE` with
the paper's `K` on `[t₁, t₀]`, by uniqueness for this ODE.) -/
theorem hasDerivAt_kTwoGUE (hL : 3 ≤ L) [NeZero W] (m : Bool → ℂ) {t1 t : ℝ} (σ₁ σ₂ : Bool)
    (h1 : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h2 : (t : ℂ) * (m σ₁ * m σ₂) ≠ 1) (a₁ a₂ : ZMod L) :
    HasDerivAt (fun s => kTwoGUE L W m t1 s σ₁ σ₂ a₁ a₂)
      ((W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
        kTwoGUE L W m t1 t σ₁ σ₂ a₁ a * SBgue L a b * kTwoGUE L W m t1 t σ₁ σ₂ b a₂) t := by
  set μ := m σ₁ * m σ₂ with hμ
  set p : ℂ := 1 - (t1 : ℂ) * μ with hp
  have hp0 : p ≠ 0 := by
    intro h
    have : (t1 : ℂ) * μ = 1 := by rw [hp] at h; linear_combination -h
    rw [this, norm_one] at h1
    exact lt_irrefl _ h1
  have hq0 : (1 : ℂ) - (t : ℂ) * μ ≠ 0 := sub_ne_zero.2 (Ne.symm h2)
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne L)
  have hW0 : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  -- the complex function
  set Θab := Theta L ((t1 : ℂ) * μ) a₁ a₂ with hΘab
  have hf : HasDerivAt (fun w : ℂ => (w - t1) * μ) μ (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).sub_const (t1 : ℂ)).mul_const μ
  have hg : HasDerivAt (fun w : ℂ => (L : ℂ) * p * (1 - w * μ)) ((L : ℂ) * p * -μ) (t : ℂ) := by
    simpa using (((hasDerivAt_id (t : ℂ)).mul_const μ).const_sub 1).const_mul ((L : ℂ) * p)
  have hgt : (L : ℂ) * p * (1 - (t : ℂ) * μ) ≠ 0 := mul_ne_zero (mul_ne_zero hL0 hp0) hq0
  have hdiv := hf.div hg hgt
  have hG := ((hdiv.const_add Θab).const_mul ((W : ℂ)⁻¹ * μ)).comp_ofReal
  refine hG.congr_deriv ?_
  -- evaluate the right side
  have hrow : ∀ a : ZMod L, ∑ b : ZMod L, Theta L ((t1 : ℂ) * μ) a b = p⁻¹ :=
    fun a => sum_Theta_row L hL h1 a
  have hcol : ∀ b : ZMod L, ∑ a : ZMod L, Theta L ((t1 : ℂ) * μ) a b = p⁻¹ := by
    intro b
    have hT := Theta_transpose L hL h1
    rw [← hrow b]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := congrFun (congrFun hT b) a
    simpa [Matrix.transpose_apply] using this
  set β := gueShift L μ t1 t with hβ
  have hsum : (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
      kTwoGUE L W m t1 t σ₁ σ₂ a₁ a * SBgue L a b * kTwoGUE L W m t1 t σ₁ σ₂ b a₂
      = (W : ℂ)⁻¹ * μ ^ 2 * (L : ℂ)⁻¹ * ((p⁻¹ + L * β) * (p⁻¹ + L * β)) := by
    simp only [kTwoGUE, ← hμ, ← hβ, SBgue_apply]
    have e : ∀ a b : ZMod L, (W : ℂ)⁻¹ * μ * (Theta L ((t1 : ℂ) * μ) a₁ a + β) * (L : ℂ)⁻¹ *
        ((W : ℂ)⁻¹ * μ * (Theta L ((t1 : ℂ) * μ) b a₂ + β))
        = ((W : ℂ)⁻¹ * μ) ^ 2 * (L : ℂ)⁻¹ *
          ((Theta L ((t1 : ℂ) * μ) a₁ a + β) * (Theta L ((t1 : ℂ) * μ) b a₂ + β)) := by
      intro a b; ring
    simp only [e, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
    simp only [Finset.sum_add_distrib, hrow, hcol, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    field_simp
  rw [hsum, hβ, gueShift]
  exact kTwoGUE_deriv_identity _ μ p _ _ _ (by rw [hp]; ring) hp0 hq0 hL0

/-- (7.33) at `n = 2` in cut-and-glue form: `kTwoGUE`, as a function of the loop index, satisfies
`d/dt K_{t,I} = primRhsGUE (K_t) I` for every 2-loop `I`. -/
noncomputable def kTwoGUELoop (m : Bool → ℂ) (t1 t : ℝ) (I : LoopIdx (ZMod L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwoGUE L W m t1 t σ₁ σ₂ a₁ a₂
  | _, _ => 0

theorem hasDerivAt_kTwoGUELoop (hL : 3 ≤ L) [NeZero W] (m : Bool → ℂ) {t1 t : ℝ}
    (σ₁ σ₂ : Bool) (h1 : ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1) (h2 : (t : ℂ) * (m σ₁ * m σ₂) ≠ 1)
    (a₁ a₂ : ZMod L) :
    HasDerivAt (fun s => kTwoGUELoop L W m t1 s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
      (primRhsGUE L W (kTwoGUELoop L W m t1 t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  rw [primRhsGUE_two]
  exact hasDerivAt_kTwoGUE L W hL m σ₁ σ₂ h1 h2 a₁ a₂

end TwoLoop

/-! ### (7.47) from (7.29) and (7.26): discharging `RBM.Eq747` -/

section Eq747

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The flow of the GUE phase**: `H_0 = 0`, `dH_{t,ij} = S_{ij}^{1/2} dB_{t,ij}` for
`t ≤ t₁ = (1 - ζ_U) t₀` and `dH_{t,ij} = N^{-1/2} dB_{t,ij}` for `t₁ ≤ t ≤ t₀`, one flow for each
index `N` (the times depend on the spectral parameter `z_N`).  As for `RBM.Sample`, only the path
is recorded; its law enters through the hypotheses of `RBM.GUEPhase.Eq747Inputs`. -/
structure GUEFlow (B : Band Ω) where
  /-- The matrix flow `t ↦ H_t` of the GUE phase. -/
  Ht : ∀ N, ℝ → Ω → Matrix (B.Idx N) (B.Idx N) ℂ
  hermitian : ∀ N t ω, (Ht N t ω).IsHermitian

variable {B : Band Ω} {H : ∀ N, Ω → Matrix (B.Idx N) (B.Idx N) ℂ}

/-- The 2-loop `L_{t,(+,σ₂),(a,b)} = ⟨G_t E_a G_t^{(σ₂)} E_b⟩` of the GUE-phase flow at
`z_t = z_t^{(E)}`. -/
noncomputable def loopG (G : GUEFlow B) (N : ℕ) (E t : ℝ) (ω : Ω) (σ₂ : Bool)
    (a b : ZMod (B.L N)) : ℂ :=
  gloop (B.L N) (B.W N) (G.Ht N t ω) (zt E t) ⟨[true, σ₂], [a, b]⟩

/-- **The inputs of (7.47)** for the matrix `H = H_{t_N}` of the OU flow (2.19) at the spectral
parameters `z_N = E_N + i η_N` of Theorem 2.5 (`RBM.Band.queZ`), with `t₀ = |m_sc(z_N)|²`,
`E' = lemE(z_N)` (Lemma 2.8, `z = t₀^{-1/2} z_{t₀}^{(E')}`) and `t₁ = (1 - ζ_N) t₀`:

* `law726` — **(7.26)** in expectation (as `RBM.Transfer.loop2_expect` for (2.66)):
  `E Tr G(z) E_a G(z)^{(σ₂)} E_b = t₀ E L_{t₀,(+,σ₂),(a,b)}` for the GUE-phase flow;
* `eq729` — **(7.29)** at `t = t₀` for `σ = (+, σ₂)`, in the `W^δ` form of (2.8)/(2.9):
  `|E L_{t₀,σ,(a,b)} - K_{t₀,σ,(a,b)}| ≤ W^δ (N η_{t₀})^{-3}`, where `K` is the 2-loop primitive
  of the GUE phase, `kTwoGUE` (the solution of (7.33) for `n = 2`, `hasDerivAt_kTwoGUE`);
* integrability of the loops of `H` (automatic in the paper since `‖G‖ ≤ η⁻¹`).

In the paper (7.29) is proved "following the proof of (2.80) in §5.8"; that step, and (7.26)
(the identity in law of the two flows), are the genuinely random inputs. -/
structure Eq747Inputs (F : OUFlow B H) (t : ℕ → ℝ) (τ : ℝ) (E ζ : ℕ → ℝ) (G : GUEFlow B) :
    Prop where
  law726 : ∀ N (σ₂ : Bool) (a b : ZMod (B.L N)),
    ∫ ω, gloop (B.L N) (B.W N) (F.Ht N (t N) ω) (B.queZ τ E N) ⟨[true, σ₂], [a, b]⟩ ∂B.P =
      (lemT (B.queZ τ E N) : ℂ) *
        ∫ ω, loopG G N (lemE (B.queZ τ E N)) (lemT (B.queZ τ E N)) ω σ₂ a b ∂B.P
  eq729 : ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (σ₂ : Bool) (a b : ZMod (B.L N)),
    ‖(∫ ω, loopG G N (lemE (B.queZ τ E N)) (lemT (B.queZ τ E N)) ω σ₂ a b ∂B.P) -
      kTwoGUE (B.L N) (B.W N) (mSigma (lemE (B.queZ τ E N)))
        ((1 - ζ N) * lemT (B.queZ τ E N)) (lemT (B.queZ τ E N)) true σ₂ a b‖ ≤
      (B.W N : ℝ) ^ δ * ((B.size N : ℝ) *
        (zt (lemE (B.queZ τ E N)) (lemT (B.queZ τ E N))).im)⁻¹ ^ 3
  integrable_pp : ∀ N x y, Integrable (fun ω => trGG (F.Ht N (t N) ω) (B.queZ τ E N) x y) B.P
  integrable_pm : ∀ N x y, Integrable (fun ω => trGGs (F.Ht N (t N) ω) (B.queZ τ E N) x y) B.P

/-- The scale conversion `(N η_{t₀})^{-3} = t₀^{-3/2} (N η)^{-3}` (`η_{t₀} = t₀^{1/2} η`,
(2.37)): `t₀ a (N t₀^{1/2} y)^{-3} ≤ 4 a (N y)^{-3}` for `t₀ ≥ 1/16`. -/
theorem scale_747 {t0 a n y : ℝ} (ht0 : 1 / 16 ≤ t0) (ha : 0 ≤ a) (hn : 0 < n) (hy : 0 < y) :
    t0 * (a * (n * (Real.sqrt t0 * y))⁻¹ ^ 3) ≤ 4 * a * (n * y)⁻¹ ^ 3 := by
  have ht0' : 0 < t0 := by linarith
  set s := Real.sqrt t0 with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ht0'
  have hss : s * s = t0 := Real.mul_self_sqrt ht0'.le
  have hs4 : 1 / 4 ≤ s := by
    rw [show (1 : ℝ) / 4 = Real.sqrt (1 / 16) by
      rw [show (1 : ℝ) / 16 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht0
  have e : t0 * (a * (n * (s * y))⁻¹ ^ 3) = s⁻¹ * (a * (n * y)⁻¹ ^ 3) := by
    rw [← hss]; field_simp
  rw [e]
  have hsi : s⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ hs0 (by norm_num)]; linarith
  have : 0 ≤ a * (n * y)⁻¹ ^ 3 := by positivity
  nlinarith

/-- `‖z_N‖ ≤ 3` and hence `t₀ = |m_sc(z_N)|² ≥ 1/16` at the spectral parameters of Theorem 2.5,
for `|E_N| ≤ 2` and `η_N ≤ 1`. -/
theorem lemT_queZ_ge (B : Band Ω) {τ : ℝ} (hτ : 0 ≤ τ) {E : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2)
    (N : ℕ) : 1 / 16 ≤ lemT (B.queZ τ E N) := by
  have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hWn : (B.W N : ℝ) ≤ B.size N := by
    have : B.W N ≤ B.size N := by
      unfold Band.size; exact Nat.le_mul_of_pos_left _ (by have := B.three_le_L N; omega)
    exact_mod_cast this
  have hη0 : 0 < B.queEtaN τ N := queEta_pos (by linarith) hW0
  have hη1 : B.queEtaN τ N ≤ 1 := queEta_le_one hn1 hW0 hWn hτ
  have hz : 0 < (B.queZ τ E N).im := by rw [B.queZ_im]; exact hη0
  have hnorm : ‖B.queZ τ E N‖ ≤ 3 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [B.queZ_re, B.queZ_im, abs_of_pos hη0]
    linarith [hE N]
  have h := lemT_ge hz
  have h16 : ((1 + ‖B.queZ τ E N‖) ^ 2)⁻¹ ≥ 1 / 16 := by
    rw [ge_iff_le, one_div, inv_le_inv₀ (by norm_num) (by positivity)]
    nlinarith [norm_nonneg (B.queZ τ E N)]
  linarith

/-- **(7.47) from (7.29) and (7.26)** — the discharge of the placeholder `RBM.Eq747` of
`Flow/Universality.lean`: for `|E_N| ≤ 2`, `0 ≤ ζ_N ≤ 1`, `τ ≥ 0`, the inputs
`RBM.GUEPhase.Eq747Inputs` give exactly `Eq747 F t τ E ζ`, i.e.
`|E Tr G E_a G^{(*)} E_b - W⁻¹ ξ ((1 - ξ S̃^{(B)})⁻¹)_{ab}| ≤ W^δ (N η)^{-3}`, `ξ = |m|², m²`.
The main term is `t₀ K_{t₀}` of the GUE-phase 2-loop primitive (`lemT_mul_kTwoGUE_pm`,
`lemT_mul_kTwoGUE_pp`: this is where `S̃^{(B)} = (1-ζ_U) S^{(B)} + ζ_U/L` of (7.25) comes from),
and the error `t₀ W^{δ/2} (N η_{t₀})^{-3} ≤ 4 W^{δ/2} (N η)^{-3} ≤ W^δ (N η)^{-3}`. -/
theorem eq747_of_inputs (F : OUFlow B H) (t : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (E ζ : ℕ → ℝ)
    (hE : ∀ N, |E N| ≤ 2) (hζ : ∀ᶠ N : ℕ in atTop, 0 ≤ ζ N ∧ ζ N ≤ 1) (G : GUEFlow B)
    (I : Eq747Inputs F t τ E ζ G) : Eq747 F t τ E ζ := by
  -- the common estimate
  have key : ∀ δ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ (σ₂ : Bool) (a b : ZMod (B.L N)),
      ‖(∫ ω, gloop (B.L N) (B.W N) (F.Ht N (t N) ω) (B.queZ τ E N) ⟨[true, σ₂], [a, b]⟩ ∂B.P) -
        (lemT (B.queZ τ E N) : ℂ) * kTwoGUE (B.L N) (B.W N) (mSigma (lemE (B.queZ τ E N)))
          ((1 - ζ N) * lemT (B.queZ τ E N)) (lemT (B.queZ τ E N)) true σ₂ a b‖ ≤
        (B.W N : ℝ) ^ δ * ((B.size N : ℝ) * (B.queZ τ E N).im)⁻¹ ^ 3 := by
    intro δ hδ
    filter_upwards [I.eq729 (δ / 2) (half_pos hδ), B.eventually_le_W ((4 : ℝ) ^ (2 / δ))]
      with N h729 hW σ₂ a b
    set z := B.queZ τ E N with hzdef
    have hn1 : (1 : ℝ) ≤ (B.size N : ℝ) := by exact_mod_cast B.one_le_size N
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have hz : 0 < z.im := by rw [hzdef, B.queZ_im]; exact queEta_pos (by linarith) hW0
    have ht16 := lemT_queZ_ge B hτ hE N
    rw [← hzdef] at ht16
    have ht0 : 0 ≤ lemT z := by linarith
    rw [I.law726 N σ₂ a b, ← hzdef, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    have h1 := h729 σ₂ a b
    rw [zt_im_lemma28 hz] at h1
    have h2 := scale_747 (a := (B.W N : ℝ) ^ (δ / 2)) (n := (B.size N : ℝ)) ht16 (by positivity)
      (by linarith) hz
    have h4 : (4 : ℝ) ≤ (B.W N : ℝ) ^ (δ / 2) := by
      have : ((4 : ℝ) ^ (2 / δ)) ^ (δ / 2) = 4 := by
        rw [← Real.rpow_mul (by norm_num), show 2 / δ * (δ / 2) = 1 by field_simp,
          Real.rpow_one]
      rw [← this]
      exact Real.rpow_le_rpow (by positivity) hW (by positivity)
    have hWδ : (B.W N : ℝ) ^ δ = (B.W N : ℝ) ^ (δ / 2) * (B.W N : ℝ) ^ (δ / 2) := by
      rw [← Real.rpow_add hW0]; ring_nf
    have hpos : 0 ≤ ((B.size N : ℝ) * z.im)⁻¹ ^ 3 := by
      have := hz.le; positivity
    calc lemT z * ‖_‖
        ≤ lemT z * ((B.W N : ℝ) ^ (δ / 2) *
            ((B.size N : ℝ) * (Real.sqrt (lemT z) * z.im))⁻¹ ^ 3) :=
          mul_le_mul_of_nonneg_left h1 ht0
      _ ≤ 4 * (B.W N : ℝ) ^ (δ / 2) * ((B.size N : ℝ) * z.im)⁻¹ ^ 3 := h2
      _ ≤ (B.W N : ℝ) ^ (δ / 2) * (B.W N : ℝ) ^ (δ / 2) * ((B.size N : ℝ) * z.im)⁻¹ ^ 3 := by
          gcongr
      _ = _ := by rw [hWδ]
  have hL : ∀ N, 3 ≤ B.L N := B.three_le_L
  refine ⟨I.integrable_pp, I.integrable_pm, fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [key δ hδ, hζ] with N hN hζN x y
    have hz : 0 < (B.queZ τ E N).im := by
      rw [B.queZ_im]
      exact queEta_pos (by exact_mod_cast B.one_le_size N) (by exact_mod_cast B.W_pos N)
    have h := hN false x y
    have hfun : (fun ω => trGGs (F.Ht N (t N) ω) (B.queZ τ E N) x y) =
        fun ω => gloop (B.L N) (B.W N) (F.Ht N (t N) ω) (B.queZ τ E N) ⟨[true, false], [x, y]⟩ :=
      funext fun ω => (gloop_pm_eq (F.hermitian N (t N) ω) _ _ _).symm
    rw [hfun, ← mul_assoc, ← lemT_mul_kTwoGUE_pm (B.L N) (B.W N) (hL N) hz hζN.1 hζN.2]
    exact h
  · filter_upwards [key δ hδ, hζ] with N hN hζN x y
    have hz : 0 < (B.queZ τ E N).im := by
      rw [B.queZ_im]
      exact queEta_pos (by exact_mod_cast B.one_le_size N) (by exact_mod_cast B.W_pos N)
    have h := hN true x y
    have hfun : (fun ω => trGG (F.Ht N (t N) ω) (B.queZ τ E N) x y) =
        fun ω => gloop (B.L N) (B.W N) (F.Ht N (t N) ω) (B.queZ τ E N) ⟨[true, true], [x, y]⟩ :=
      funext fun ω => (gloop_pp_eq _ _ _ _).symm
    rw [hfun, ← mul_assoc, ← lemT_mul_kTwoGUE_pp (B.L N) (B.W N) (hL N) hz hζN.1 hζN.2]
    exact h

end Eq747

/-! ### (7.27), (7.28) as `≺` statements -/

section Domination

open Set MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `≺` from its good events: if for every `τ > 0` the event `{∀ u, ξ ≤ N^τ ζ}` holds w.h.p.,
then `ξ ≺ ζ`. -/
theorem stochDom_of_forall_highProb {U : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), HighProb P (fun N => {ω | ∀ u, ξ N u ω ≤ (N : ℝ) ^ τ * ζ N u ω})) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono ?_).trans hN
  rintro ω ⟨u, hu⟩ hω
  exact absurd (hω u) (not_le.2 hu)

/-- `N^a ≤ ρ` for large `N`, if `a < 0`, `ρ > 0`. -/
theorem eventually_rpow_le_of_neg {a ρ : ℝ} (ha : a < 0) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ ρ := by
  filter_upwards [eventually_le_rpow ρ⁻¹ (neg_pos.2 ha), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hpos : 0 < (N : ℝ) ^ (-a) := Real.rpow_pos_of_pos hN0 _
  have e : (N : ℝ) ^ a = ((N : ℝ) ^ (-a))⁻¹ := by
    rw [← Real.rpow_neg hN0.le, neg_neg]
  rw [e]
  calc ((N : ℝ) ^ (-a))⁻¹ ≤ (ρ⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hρ) hN
    _ = ρ := inv_inv ρ

/-! #### Maxima over `(σ, a)` -/

end Domination

end GUEPhase

end RBM

