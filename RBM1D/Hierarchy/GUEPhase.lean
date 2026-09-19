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
*Delocalization of One-Dimensional Random Band Matrices*, §7.2 (pp. 81–84): the auxiliary
estimates (7.27)–(7.29) for the flow whose last stretch `[t₁, t₀]` has the GUE variance profile,
and (7.47), the input of the weak QUE (2.27) for `H_{t_U}` in the proof of Theorem 2.6.

Everything proved here is deterministic.  The random layer enters through hypotheses (never
`axiom`s), in the pathwise/`≺` form used elsewhere in the library.

## Main results

* **(7.25)**: `SBgue` (`(S^{(B)}_{GUE})_{ab} = 1/L`), `SBTilde_eq_add`
  (`S̃^{(B)} = (1-ζ) S^{(B)} + ζ S^{(B)}_{GUE}`; the zero mode itself is T46's
  `RBM.SBTilde`/`RBM.ThetaTilde`), `Sgue`, `Stilde`, `Stilde_apply`
  (`S̃_{xy} = (1-ζ_U) S_{xy} + ζ_U/N`), `zetaU` (`ζ_U = 1 - e^{-t_U}`), `zetaU_le`,
  `half_le_zetaU` (`ζ_U ∼ t_U`).
* **(7.30)**: `t0_sub_t1_le`, `le_t0_sub_t1` (`t₀ - t₁ ∼ t_U = N^{-1+τ_U}`), `eq730`
  (`N(t - t₁) ≤ N η_t N^{-τ_U}` from `η_t ≥ N^{-1+2τ_U}`), `ellHat_eq_L` (`ℓ_{t₁} = L`),
  `scale_eq_of_ell_eq_L` (`W ℓ_t η_t = N η_t`, turning (7.31) into (7.32)).
* **(7.33), (7.34), (7.39), (7.40)**: `primBilGUE`, `primRhsGUE` (the primitive equation with
  `S^{(B)} → S^{(B)}_{GUE}`), `primRhsGUE_sub` (the GUE-phase (5.12)/(5.13)), and the power
  counting `norm_primBilGUE_le`, `norm_primRhsGUE_le`
  (`|W ∑_{k<l} ∑_{a,b} K S_{GUE} K'| ≤ n² N ∑_{2≤j≤n} max K^{(n-j+2)} max K'^{(j)}`).
  `eq742_of`, `eq744_of`: the Cauchy–Schwarz / (5.117) reductions (7.41) ⟹ (7.42),
  (7.43) ⟹ (7.44).
* **The continuity argument**: `continuity_argument` (finitely many continuous quantities, a
  strict bootstrap improvement ⟹ the bound on the whole interval).
* **(7.35) ⟹ (7.36)**: `K_bootstrap` (abstract ODE bootstrap: mean value inequality +
  continuity argument), `eq736` (for solutions of `d/dt K = primRhsGUE K` on loops of length
  `2 ≤ |I| ≤ n`), `eq736_detDom` (the `≺` form, uniform in `t ∈ [t₁, t₀]`), `kMax`,
  `kMax_detDom` (the maximum form used below).
* **(7.45) ⟹ (7.27), (7.46) ⟹ (7.28)**: `rhs745`, `rhs746` (the right sides), `eq745_of_terms`
  ((7.37)–(7.44) ⟹ (7.45), pathwise), `eq727_path`, `eq728_path` (pathwise bootstraps),
  `eq727`, `eq728` (`≺` statements), `eq728_of_eq745` (both, chained).
* **The 2-loop primitive of the GUE phase**: `kTwoGUE` (closed form), `kTwoGUE_self`
  (= (2.57) at `t₁`), `hasDerivAt_kTwoGUE`, `hasDerivAt_kTwoGUELoop` ((7.33) at `n = 2`),
  `kTwoGUE_eq_ThetaTilde` (at `t₀`: `W⁻¹ μ (1 - t₀μ S̃^{(B)})⁻¹`), `lemT_mul_kTwoGUE_pm`,
  `lemT_mul_kTwoGUE_pp` (the main terms of (7.47)).
* **(7.47)**: `GUEFlow`, `loopG`, `Eq747Inputs`, `eq747_of_inputs` — **discharges the
  placeholder `RBM.Eq747` of `Flow/Universality.lean`** from (7.26) and (7.29);
  `que_flow_of_inputs` — (2.27) from those inputs (through `RBM.que_flow_of_eq747`).

## Hypotheses (the random layer and T58)

* `Eq747Inputs.law726` — **(7.26)** in expectation (identity in law of the two flows);
  `Eq747Inputs.eq729` — **(7.29)** at `t₀` for `σ = (+, ±)` (in the paper: "following the
  proof of (2.80) in §5.8"); integrability of the loops.
* `eq727`/`eq728`: **(7.45)**, **(7.46)** as `≺` bounds (`h745`, `h746`).  These package the
  Duhamel formula (7.37) (Lemmas 5.3, 5.5 with `s = t₁` — **T58 placeholders**) with Lemma 7.1,
  the BDG inequality (7.38), the bounds (7.39)–(7.44) and `E^{(G)}` via (4.5) for `G_t`
  (random inputs).  `eq745_of_terms` shows how (7.45) follows from the term-wise bounds.
* Time continuity of `t ↦ max |L_t|`, `t ↦ max |(L-K)_t|` w.h.p. (the continuity argument).
* (7.32) (from Lemmas 2.17, 2.18) as the initial bounds; the GUE-phase primitive equation (7.33)
  (the definition of `K` on `[t₁, t₀]`) as the hypothesis `hK` of `eq736`.

## Deviations from the paper

* The `≺` of (7.27), (7.28), (7.36) is in the sequence index `N` of `RBM.StochDom` /
  `RBM.UnifDetDom`; the matrix size is a separate parameter `Nf` (resp. `W L`), and (7.30) is
  used as `t - t₁ ≤ N^{-τ_U} η_t`, `(Nf η_t)^{-1} ≤ N^{-τ_U}` (any power gain would do).
* The induction on `n` of p. 83 is replaced by a simultaneous continuity argument over all
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

theorem SBgue_eq : SBgue L = (L : ℂ)⁻¹ • onesMat L := by
  ext a b
  simp

/-- `S̃^{(B)} = (1 - ζ) S^{(B)} + ζ S^{(B)}_{GUE}`. -/
theorem SBTilde_eq_add [NeZero L] (ζ : ℂ) : SBTilde L ζ = (1 - ζ) • SB L + ζ • SBgue L := by
  rw [SBTilde, SBgue_eq, smul_smul, div_eq_mul_inv]

/-- `(S_{GUE})_{xy} = 1/N`, `N = L W`. -/
noncomputable def Sgue : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  Matrix.of fun _ _ => ((L * W : ℕ) : ℂ)⁻¹

/-- **(7.25)**: `S̃_{xy} = (1 - ζ_U) S_{xy} + ζ_U / N`. -/
noncomputable def Stilde [NeZero L] (ζ : ℂ) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  (1 - ζ) • Svar L W + ζ • Sgue L W

/-- `S̃` is the block matrix of `S̃^{(B)}` (`S̃_{(a,α),(b,β)} = W⁻¹ S̃^{(B)}_{ab}`). -/
theorem Stilde_apply [NeZero L] (ζ : ℂ) (a b : ZMod L) (α β : Fin W) :
    Stilde L W ζ (a, α) (b, β) = SBTilde L ζ a b * (W : ℂ)⁻¹ := by
  simp only [Stilde, Sgue, SBTilde_eq_add, Matrix.add_apply, Matrix.smul_apply, Svar_apply,
    Matrix.of_apply, SBgue_apply, smul_eq_mul]
  push_cast
  rw [mul_inv]
  ring

/-- `ζ_U = 1 - e^{-t_U}`. -/
noncomputable def zetaU (tU : ℝ) : ℝ := 1 - Real.exp (-tU)

theorem zetaU_nonneg {tU : ℝ} (h : 0 ≤ tU) : 0 ≤ zetaU tU := by
  have := Real.exp_le_one_iff.2 (neg_nonpos.2 h)
  unfold zetaU; linarith

theorem zetaU_le {tU : ℝ} : zetaU tU ≤ tU := by
  have := Real.add_one_le_exp (-tU)
  unfold zetaU; linarith

/-- `ζ_U ∼ t_U`: `t_U / 2 ≤ ζ_U` for `0 ≤ t_U ≤ 1`. -/
theorem half_le_zetaU {tU : ℝ} (h0 : 0 ≤ tU) (h1 : tU ≤ 1) : tU / 2 ≤ zetaU tU := by
  have h := Real.add_one_le_exp tU
  have hpos := Real.exp_pos tU
  have hinv : Real.exp (-tU) = (Real.exp tU)⁻¹ := Real.exp_neg tU
  unfold zetaU
  rw [hinv]
  have : (Real.exp tU)⁻¹ ≤ 1 - tU / 2 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

theorem zetaU_lt_one (tU : ℝ) : zetaU tU < 1 := by
  have := Real.exp_pos (-tU)
  unfold zetaU; linarith

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

/-- `t₀ - t₁ = ζ_U t₀` for `t₁ = (1 - ζ_U) t₀`. -/
theorem t0_sub_t1 (ζ t0 : ℝ) : t0 - (1 - ζ) * t0 = ζ * t0 := by ring

/-- **(7.30), `t₀ - t₁ ∼ N^{-1+τ_U}`** (upper bound): `t₀ - t₁ ≤ t_U` for `0 ≤ t₀ ≤ 1`. -/
theorem t0_sub_t1_le {tU t0 : ℝ} (htU : 0 ≤ tU) (ht0 : 0 ≤ t0) (ht01 : t0 ≤ 1) :
    t0 - (1 - zetaU tU) * t0 ≤ tU := by
  rw [t0_sub_t1]
  have h1 := zetaU_le (tU := tU)
  have h2 := zetaU_nonneg htU
  nlinarith

/-- **(7.30), `t₀ - t₁ ∼ N^{-1+τ_U}`** (lower bound): `t_U t₀ / 2 ≤ t₀ - t₁` for `t_U ≤ 1`. -/
theorem le_t0_sub_t1 {tU t0 : ℝ} (htU : 0 ≤ tU) (htU1 : tU ≤ 1) (ht0 : 0 ≤ t0) :
    tU * t0 / 2 ≤ t0 - (1 - zetaU tU) * t0 := by
  rw [t0_sub_t1]
  have h := half_le_zetaU htU htU1
  nlinarith

/-- **(7.30) ⟹ `N(t - t₁) ≤ N η_t N^{-τ_U}`** for `t ∈ [t₁, t₀]`, `t_U = N^{-1+τ_U}`,
`η_t ≥ N^{-1+2τ_U}`. -/
theorem eq730 {N τU t0 t η : ℝ} (hN : 0 < N) (ht0 : 0 ≤ t0) (ht01 : t0 ≤ 1)
    (ht : t ≤ t0) (hη : N ^ (-1 + 2 * τU) ≤ η) :
    N * (t - (1 - zetaU (N ^ (-1 + τU))) * t0) ≤ N * η * N ^ (-τU) := by
  have htU : 0 ≤ N ^ (-1 + τU) := Real.rpow_nonneg hN.le _
  have h1 : t - (1 - zetaU (N ^ (-1 + τU))) * t0 ≤ N ^ (-1 + τU) :=
    le_trans (by linarith) (t0_sub_t1_le htU ht0 ht01)
  have h2 : N ^ (-1 + τU) = N ^ (-1 + 2 * τU) * N ^ (-τU) := by
    rw [← Real.rpow_add hN]; ring_nf
  have h3 : 0 ≤ N ^ (-τU) := Real.rpow_nonneg hN.le _
  calc N * (t - (1 - zetaU (N ^ (-1 + τU))) * t0) ≤ N * N ^ (-1 + τU) :=
        mul_le_mul_of_nonneg_left h1 hN.le
    _ = N * N ^ (-1 + 2 * τU) * N ^ (-τU) := by rw [h2]; ring
    _ ≤ N * η * N ^ (-τU) := by gcongr

/-- **(7.30) ⟹ `ℓ_{t₁} = L`**: `ℓ̂(t) = L` as soon as `L² (1 - t) ≤ 1`. -/
theorem ellHat_eq_L {L : ℕ} {t : ℝ} (ht : t < 1) (h : (L : ℝ) ^ 2 * (1 - t) ≤ 1) :
    ellHat L (t : ℂ) = L := by
  rw [ellHat_ofReal L ht, min_eq_right]
  have hs : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
  rw [le_div_iff₀ hs]
  have h1 : ((L : ℝ) * Real.sqrt (1 - t)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]; exact h
  nlinarith [Real.sqrt_nonneg (1 - t), (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

/-- With `ℓ_t = L`, the scale `W ℓ_t η_t` of (7.31) is `N η_t` (`N = L W`), which turns (7.31)
into (7.32). -/
theorem scale_eq_of_ell_eq_L {L W : ℕ} {ℓ η : ℝ} (hℓ : ℓ = L) :
    (W : ℝ) * ℓ * η = ((L * W : ℕ) : ℝ) * η := by
  rw [hℓ]; push_cast; ring

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
(the terms (7.39), (7.40) of p. 83). -/
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

/-- **(7.41) ⟹ (7.42)**: by Cauchy–Schwarz an `(n+1)`-loop is bounded by a `2`-loop and a
`2n`-loop, `L_{n+1} ≤ (L_2 L_{2n})^{1/2}`, and by (5.117) `L_{2n} ≤ C L_n²`; hence
`L_2 L_{n+1} ≤ C^{1/2} L_2^{3/2} L_n`, turning `E^{(G)} ≺ N L_2 L_{n+1}` into (7.42). -/
theorem eq742_of {L2 Ln Ln1 L2n C : ℝ} (hCS : Ln1 ≤ Real.sqrt (L2 * L2n))
    (h5117 : L2n ≤ C * Ln ^ 2) (hL2 : 0 ≤ L2) (hLn : 0 ≤ Ln) :
    L2 * Ln1 ≤ Real.sqrt C * (L2 * Real.sqrt L2) * Ln := by
  have h1 : Real.sqrt (L2 * L2n) ≤ Real.sqrt L2 * Real.sqrt C * Ln := by
    calc Real.sqrt (L2 * L2n) ≤ Real.sqrt (L2 * (C * Ln ^ 2)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h5117 hL2)
      _ = Real.sqrt L2 * Real.sqrt C * Ln := by
          rw [Real.sqrt_mul hL2, mul_assoc]
          by_cases hC : 0 ≤ C
          · rw [Real.sqrt_mul hC, Real.sqrt_sq hLn]
          · push Not at hC
            have : C * Ln ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC.le (sq_nonneg _)
            rw [Real.sqrt_eq_zero'.2 this, Real.sqrt_eq_zero'.2 hC.le]
            ring
  calc L2 * Ln1 ≤ L2 * (Real.sqrt L2 * Real.sqrt C * Ln) :=
        mul_le_mul_of_nonneg_left (hCS.trans h1) hL2
    _ = Real.sqrt C * (L2 * Real.sqrt L2) * Ln := by ring

/-- **(7.43) ⟹ (7.44)**: with (5.117) `L_{2n} ≤ C L_n²`,
`E ⊗ E ≺ N^{-1} η_u^{-2} L_{2n}` becomes `E ⊗ E ≺ N^{-1} η_u^{-2} L_n²`. -/
theorem eq744_of {EE L2n Ln C a : ℝ} (h743 : EE ≤ a * L2n) (h5117 : L2n ≤ C * Ln ^ 2)
    (ha : 0 ≤ a) : EE ≤ a * C * Ln ^ 2 := by
  calc EE ≤ a * L2n := h743
    _ ≤ a * (C * Ln ^ 2) := mul_le_mul_of_nonneg_left h5117 ha
    _ = a * C * Ln ^ 2 := by ring

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
`N (t - t₁) ≤ N^{-τ_U} · N η_t` (`eq730`), for a solution of the GUE-phase primitive equation
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

/-- **The right side of (7.45)** for loops of length `n`, at time `t`, with `η_u = Im z_u`,
`D_k(u) = max_{σ,a} |(L-K)^{(k)}_{u,σ,a}|`, `L_k(u) = max_{σ,a} |L^{(k)}_{u,σ,a}|`:
`(N|t-t₁|) sup_u ∑_{2≤k≤n} ((Nη_u)^{-k+1} + D_k) D_{n-k+2} + (Nη_t)^{-n}
 + (N|t-t₁|) sup_u L_2^{3/2} L_n + |t-t₁|^{1/2} sup_u (N^{-1} η_u^{-2})^{1/2} L_n`. -/
noncomputable def rhs745 (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Lm 2 u * Real.sqrt (Lm 2 u) * Lm n u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t

/-- **The right side of (7.46)** (the second pass, with loop lengths `n + 1`, `2n` on the right):
`(N|t-t₁|) sup_u ∑_{2≤k≤n} ((Nη_u)^{-k+1} + D_k) D_{n-k+2} + (Nη_t)^{-n}
 + (N|t-t₁|) sup_u L_2 L_{n+1} + |t-t₁|^{1/2} sup_u (N^{-1} η_u^{-2})^{1/2} L_{2n}^{1/2}`. -/
noncomputable def rhs746 (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOn (fun u => Lm 2 u * Lm (n + 1) u) t1 t
    + Real.sqrt (t - t1) * supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) *
        Real.sqrt (Lm (2 * n) u)) t1 t

/-- At `t = t₁` only the initial term `(Nη_{t₁})^{-n}` of (7.45) survives. -/
theorem rhs745_self (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) :
    rhs745 N η t1 Lm Dm n t1 = (N * η t1)⁻¹ ^ n := by
  simp [rhs745]

theorem rhs746_self (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) :
    rhs746 N η t1 Lm Dm n t1 = (N * η t1)⁻¹ ^ n := by
  simp [rhs746]

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

/-- **(7.37)–(7.44) ⟹ (7.45), pathwise.**  The Duhamel formula (7.37) (with Lemma 7.1:
`‖U_{u,t,σ}‖_{max→max} ≤ c₀`) bounds `D_n(t)` by `c₀ (D_n(t₁) + |martingale| + ∫_{t₁}^t F)`, where
the drift `F` collects `∑_{l_K>2}[K ∼ (L-K)]`, `E^{((L-K)×(L-K))}` and `E^{(G)}`.  If `F` obeys the
power counting (7.39) + (7.40) + (7.42) on `[t₁, t]` (with the maxima and the `sup` over `u` of
(7.45)), the martingale obeys (7.38) + (7.44) (BDG), and `D_n(t₁) ≤ c₃ (Nη_t)^{-n}` ((7.32) and
`η_t ≤ η_{t₁}`), then `D_n(t) ≤ c₀ (c₁ + c₂ + c₃) · (right side of (7.45))`. -/
theorem eq745_of_terms {Lm Dm : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {n : ℕ} {t Mart c0 c1 c2 c3 : ℝ}
    (ht1t : t1 ≤ t) (hN : 0 ≤ N) (hL0 : ∀ m u, 0 ≤ Lm m u) (hD0 : ∀ m u, 0 ≤ Dm m u)
    (hη : ∀ u ∈ Icc t1 t, 0 ≤ η u)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hduh : Dm n t ≤ c0 * (Dm n t1 + Mart + ∫ u in t1..t, F u))
    (hFi : IntervalIntegrable F MeasureTheory.volume t1 t)
    (hF : ∀ u ∈ Icc t1 t, F u ≤ c1 * (N * supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
        ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
      + N * supOn (fun u => Lm 2 u * Real.sqrt (Lm 2 u) * Lm n u) t1 t))
    (hmart : Mart ≤ c2 * (Real.sqrt (t - t1) *
      supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t))
    (hinit : Dm n t1 ≤ c3 * (N * η t)⁻¹ ^ n) :
    Dm n t ≤ c0 * (c1 + c2 + c3) * rhs745 N η t1 Lm Dm n t := by
  set S1 := supOn (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t with hS1
  set S3 := supOn (fun u => Lm 2 u * Real.sqrt (Lm 2 u) * Lm n u) t1 t with hS3
  set S4 := supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t with hS4
  have hS1' : 0 ≤ S1 := supOn_nonneg fun u hu => Finset.sum_nonneg fun k _ =>
    mul_nonneg (add_nonneg (pow_nonneg (inv_nonneg.2 (mul_nonneg hN (hη u hu))) _) (hD0 k u))
      (hD0 _ u)
  have hS3' : 0 ≤ S3 := supOn_nonneg fun u _ =>
    mul_nonneg (mul_nonneg (hL0 2 u) (Real.sqrt_nonneg _)) (hL0 n u)
  have hS4' : 0 ≤ S4 := supOn_nonneg fun u _ => mul_nonneg (Real.sqrt_nonneg _) (hL0 n u)
  have hint : ∫ u in t1..t, F u ≤ (t - t1) * (c1 * (N * S1 + N * S3)) := by
    calc ∫ u in t1..t, F u ≤ ∫ _u in t1..t, c1 * (N * S1 + N * S3) :=
          intervalIntegral.integral_mono_on ht1t hFi intervalIntegrable_const hF
      _ = (t - t1) * (c1 * (N * S1 + N * S3)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have hx : 0 ≤ (N * η t)⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (mul_nonneg hN (hη t ⟨ht1t, le_rfl⟩))) _
  have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN (by linarith)
  have hsq : 0 ≤ Real.sqrt (t - t1) := Real.sqrt_nonneg _
  have hrhs : rhs745 N η t1 Lm Dm n t
      = N * (t - t1) * S1 + (N * η t)⁻¹ ^ n + N * (t - t1) * S3 + Real.sqrt (t - t1) * S4 := rfl
  have hsum : Dm n t1 + Mart + ∫ u in t1..t, F u
      ≤ (c1 + c2 + c3) * rhs745 N η t1 Lm Dm n t := by
    rw [hrhs]
    have e1 : (t - t1) * (c1 * (N * S1 + N * S3))
        = c1 * (N * (t - t1) * S1 + N * (t - t1) * S3) := by
      ring
    have h1 : c1 * (N * (t - t1) * S1 + N * (t - t1) * S3)
        ≤ (c1 + c2 + c3) * (N * (t - t1) * S1 + N * (t - t1) * S3) := by
      have : 0 ≤ N * (t - t1) * S1 + N * (t - t1) * S3 := by positivity
      nlinarith
    have h2 : c2 * (Real.sqrt (t - t1) * S4) ≤ (c1 + c2 + c3) * (Real.sqrt (t - t1) * S4) := by
      have : 0 ≤ Real.sqrt (t - t1) * S4 := by positivity
      nlinarith
    have h3 : c3 * (N * η t)⁻¹ ^ n ≤ (c1 + c2 + c3) * (N * η t)⁻¹ ^ n := by nlinarith
    nlinarith
  calc Dm n t ≤ c0 * (Dm n t1 + Mart + ∫ u in t1..t, F u) := hduh
    _ ≤ c0 * ((c1 + c2 + c3) * rhs745 N η t1 Lm Dm n t) := mul_le_mul_of_nonneg_left hsum hc0
    _ = _ := by ring

/-- `x^{-1} x^n = x^{n-1}` for `n ≥ 1`. -/
theorem inv_mul_pow {x : ℝ} (hx : x ≠ 0) {n : ℕ} (hn : 1 ≤ n) : x⁻¹ * x ^ n = x ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel]
  field_simp

/-- **(7.45) ⟹ (7.27), pathwise.**  Fix a realization (a fixed `N` and `ω`).  Let `L_m(t)`,
`D_m(t)` (`2 ≤ m ≤ n₀`) be the maxima `max_{σ,a} |L^{(m)}_{t,σ,a}|`,
`max_{σ,a} |(L-K)^{(m)}_{t,σ,a}|`, with `L_m` continuous in `t` and `|L_m - D_m| ≤ K_m`
(`L = (L-K) + K`), and `K_m ≤ A (Nη_t)^{-m+1}` ((7.36)).  Assume (7.45) holds with the factor
`Φ` (for the `≺`, `Φ = N^τ`), and (7.30) as `t - t₁ ≤ ε η_t`, `(Nη_t)^{-1} ≤ δ ≤ 1`.  If
`A + Φ (ε n₀ (1 + M + A)(M + A) + δ + ε M^{5/2} + ε^{1/2} M) < M`, then
`L_m(t) < M (Nη_t)^{-m+1}` on `[t₁, t₀]` ((7.27)).  The induction on `n` of p. 83 is replaced by
a simultaneous continuity argument over all lengths `2 ≤ m ≤ n₀`. -/
theorem eq727_path {Lm Dm Km : ℕ → ℝ → ℝ} {n0 : ℕ} {t0 A M Φ ε δ : ℝ}
    (hN : 0 < N) (ht10 : t1 ≤ t0)
    (hη : ∀ t ∈ Icc t1 t0, 0 < η t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → η t ≤ η u)
    (hηc : ContinuousOn η (Icc t1 t0))
    (hδ : ∀ t ∈ Icc t1 t0, (N * η t)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hsm : ∀ t ∈ Icc t1 t0, t - t1 ≤ ε * η t) (hε : 0 ≤ ε)
    (hLc : ∀ m ∈ Set.Icc 2 n0, ContinuousOn (Lm m) (Icc t1 t0))
    (hL0 : ∀ m t, 0 ≤ Lm m t) (hD0 : ∀ m t, 0 ≤ Dm m t)
    (hLDK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Lm m t ≤ Dm m t + Km m t)
    (hDLK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Lm m t + Km m t)
    (hK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Km m t ≤ A * (N * η t)⁻¹ ^ (m - 1))
    (h745 : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Φ * rhs745 N η t1 Lm Dm m t)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (hcond : A + Φ * (ε * n0 * ((1 + (M + A)) * (M + A)) + δ + ε * (M * Real.sqrt M * M)
      + Real.sqrt ε * M) < M) :
    ∀ t ∈ Icc t1 t0, ∀ m ∈ Set.Icc 2 n0, Lm m t < M * (N * η t)⁻¹ ^ (m - 1) := by
  have hx0 : ∀ t ∈ Icc t1 t0, 0 < (N * η t)⁻¹ := fun t ht => inv_pos.2 (mul_pos hN (hη t ht))
  have hgc : ∀ m ∈ Set.Icc 2 n0, ContinuousOn (fun t => M * (N * η t)⁻¹ ^ (m - 1)) (Icc t1 t0) :=
    fun m _ => continuousOn_const.mul
      (((continuousOn_const.mul hηc).inv₀ fun t ht => (mul_pos hN (hη t ht)).ne').pow _)
  -- the pieces of `hcond` are nonnegative
  have hc1 : 0 ≤ ε * n0 * ((1 + (M + A)) * (M + A)) := by positivity
  have hc3 : 0 ≤ ε * (M * Real.sqrt M * M) := by positivity
  have hc4 : 0 ≤ Real.sqrt ε * M := by positivity
  refine continuity_argument (Set.finite_Icc 2 n0) hLc hgc (fun m hm => ?_)
    (fun t ht hprev m hm => ?_)
  · -- `t = t₁`
    have ht1 : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
    set x := (N * η t1)⁻¹ with hx
    have hxp := hx0 t1 ht1
    have hD := h745 m hm t1 ht1
    rw [rhs745_self] at hD
    have hxm : x ^ m ≤ δ * x ^ (m - 1) := by
      have : x ^ m = x * x ^ (m - 1) := by
        rw [← pow_succ']; congr 1; have := hm.1; omega
      rw [this]
      exact mul_le_mul_of_nonneg_right (hδ t1 ht1) (by positivity)
    have hLt := hLDK m hm t1 ht1
    have hKt := hK m hm t1 ht1
    have hpos : 0 < x ^ (m - 1) := pow_pos hxp _
    show Lm m t1 < M * x ^ (m - 1)
    have hΦx : Φ * x ^ m ≤ Φ * δ * x ^ (m - 1) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hxm hΦ
    have hcond' : A + Φ * δ < M := by nlinarith
    nlinarith
  -- the improvement step at `t`
  show Lm m t < M * (N * η t)⁻¹ ^ (m - 1)
  set x := (N * η t)⁻¹ with hx
  have hxp := hx0 t ht
  have hx1 : x ≤ 1 := (hδ t ht).trans hδ1
  have hηt := hη t ht
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  obtain ⟨hm2, hmn⟩ := hm
  have hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x := by
    intro u hu
    have hu0 := hsub hu
    refine ⟨(hx0 u hu0).le, inv_anti₀ (mul_pos hN hηt) ?_⟩
    exact mul_le_mul_of_nonneg_left (hanti u hu0 t ht hu.2) hN.le
  have hLu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n0 → Lm j u ≤ M * x ^ (j - 1) := by
    intro u hu j h2 hj
    refine (hprev u hu j ⟨h2, hj⟩).trans ?_
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hDu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ m → 0 ≤ Dm j u ∧
      Dm j u ≤ (M + A) * x ^ (j - 1 + 0) := by
    intro u hu j h2 hj
    refine ⟨hD0 j u, ?_⟩
    have hjn : j ∈ Set.Icc 2 n0 := ⟨h2, hj.trans hmn⟩
    have h1 := hDLK j hjn u (hsub hu)
    have h2' := hK j hjn u (hsub hu)
    have h3 : A * (N * η u)⁻¹ ^ (j - 1) ≤ A * x ^ (j - 1) := by
      gcongr
      · exact (hxu u hu).1
      · exact (hxu u hu).2
    have h4 := hLu u hu j h2 (hj.trans hmn)
    rw [Nat.add_zero]
    nlinarith
  -- line 1
  have hl1 := supOn_line1_le N η t1 (n := m) 0 (by norm_num) ht1t (by positivity) hxp.le hx1 hxu hDu
  have hmx : x⁻¹ * x ^ m = x ^ (m - 1) := inv_mul_pow hxp.ne' (by omega)
  have hm0 : (m : ℝ) ≤ n0 := by exact_mod_cast hmn
  have hline1 : N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (m - k + 2) u) t1 t
      ≤ ε * n0 * ((1 + (M + A)) * (M + A)) * x ^ (m - 1) := by
    have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
    calc _ ≤ N * (t - t1) * (m * ((1 + (M + A)) * (M + A) * x ^ (m + 0))) :=
          mul_le_mul_of_nonneg_left hl1 hNt
      _ ≤ ε * x⁻¹ * (m * ((1 + (M + A)) * (M + A) * x ^ (m + 0))) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * m * ((1 + (M + A)) * (M + A)) * (x⁻¹ * x ^ m) := by ring
      _ ≤ ε * n0 * ((1 + (M + A)) * (M + A)) * (x⁻¹ * x ^ m) := by gcongr
      _ = _ := by rw [hmx]
  -- line 2
  have hline2 : x ^ m ≤ δ * x ^ (m - 1) := by
    have : x ^ m = x * x ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [this]
    exact mul_le_mul_of_nonneg_right (hδ t ht) (by positivity)
  -- line 3
  have hline3 : N * (t - t1) * supOn (fun u => Lm 2 u * Real.sqrt (Lm 2 u) * Lm m u) t1 t
      ≤ ε * (M * Real.sqrt M * M) * x ^ (m - 1) := by
    have hsup : supOn (fun u => Lm 2 u * Real.sqrt (Lm 2 u) * Lm m u) t1 t
        ≤ M * Real.sqrt M * M * x ^ m := by
      refine supOn_le ht1t fun u hu => ?_
      have h2 : Lm 2 u ≤ M * x := by simpa using hLu u hu 2 le_rfl (by omega)
      have hm' : Lm m u ≤ M * x ^ (m - 1) := hLu u hu m hm2 hmn
      have hs : Real.sqrt (Lm 2 u) ≤ Real.sqrt M := by
        refine Real.sqrt_le_sqrt (h2.trans ?_)
        nlinarith
      have hL2 := hL0 2 u
      have hLm := hL0 m u
      calc Lm 2 u * Real.sqrt (Lm 2 u) * Lm m u
          ≤ (M * x) * Real.sqrt M * (M * x ^ (m - 1)) := by
            gcongr
      _ = M * Real.sqrt M * M * (x * x ^ (m - 1)) := by ring
      _ = M * Real.sqrt M * M * x ^ m := by
            rw [← pow_succ']; congr 2; omega
    have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
    calc _ ≤ N * (t - t1) * (M * Real.sqrt M * M * x ^ m) := mul_le_mul_of_nonneg_left hsup hNt
      _ ≤ ε * x⁻¹ * (M * Real.sqrt M * M * x ^ m) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * (M * Real.sqrt M * M) * (x⁻¹ * x ^ m) := by ring
      _ = _ := by rw [hmx]
  -- line 4
  have hline4 : Real.sqrt (t - t1) *
      supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm m u) t1 t
      ≤ Real.sqrt ε * M * x ^ (m - 1) := by
    have hsup : supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm m u) t1 t
        ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * (M * x ^ (m - 1)) := by
      refine supOn_le ht1t fun u hu => ?_
      have hu0 := hsub hu
      have hηu : (η u)⁻¹ ≤ (η t)⁻¹ := inv_anti₀ hηt (hanti u hu0 t ht hu.2)
      have hs : Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have : 0 ≤ (η u)⁻¹ := (inv_pos.2 (hη u hu0)).le
        gcongr
      exact mul_le_mul hs (hLu u hu m hm2 hmn) (hL0 m u) (Real.sqrt_nonneg _)
    have hsq := sqrt_mul_sqrt_le N η t1 hN hηt ht1t (hsm t ht)
    have hsx : Real.sqrt (ε * (N * η t)⁻¹) ≤ Real.sqrt ε := by
      refine Real.sqrt_le_sqrt ?_
      calc ε * (N * η t)⁻¹ ≤ ε * 1 := mul_le_mul_of_nonneg_left hx1 hε
        _ = ε := mul_one ε
    have hpos : 0 ≤ M * x ^ (m - 1) := by positivity
    calc _ ≤ Real.sqrt (t - t1) * (Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * (M * x ^ (m - 1))) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ = (Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2)) * (M * x ^ (m - 1)) := by ring
      _ ≤ Real.sqrt ε * (M * x ^ (m - 1)) :=
          mul_le_mul_of_nonneg_right (hsq.trans hsx) hpos
      _ = _ := by ring
  -- assemble
  have hD := h745 m ⟨hm2, hmn⟩ t ht
  have hrhs : rhs745 N η t1 Lm Dm m t ≤ (ε * n0 * ((1 + (M + A)) * (M + A)) + δ
      + ε * (M * Real.sqrt M * M) + Real.sqrt ε * M) * x ^ (m - 1) := by
    unfold rhs745
    rw [← hx]
    nlinarith
  have hDt : Dm m t ≤ Φ * ((ε * n0 * ((1 + (M + A)) * (M + A)) + δ
      + ε * (M * Real.sqrt M * M) + Real.sqrt ε * M) * x ^ (m - 1)) :=
    hD.trans (mul_le_mul_of_nonneg_left hrhs hΦ)
  have hLt := hLDK m ⟨hm2, hmn⟩ t ht
  have hKt := hK m ⟨hm2, hmn⟩ t ht
  have hpos : 0 < x ^ (m - 1) := pow_pos hxp _
  nlinarith

/-- **(7.46) ⟹ (7.28), pathwise.**  With the loop bound (7.27) `L_j ≤ M (Nη)^{-j+1}` for all
lengths `2 ≤ j ≤ 2n₀` (the right side of (7.46) contains `L_{n+1}` and `L_{2n}`), `D_m`
continuous, (7.46) with the factor `Φ`, and (7.30) as before: if
`Φ (ε n₀ (1 + M') M' + 1 + ε M² + (ε M)^{1/2}) < M'`, then
`D_m(t) < M' (Nη_t)^{-m}` on `[t₁, t₀]` for `2 ≤ m ≤ n₀` ((7.28)). -/
theorem eq728_path {Lm Dm : ℕ → ℝ → ℝ} {n0 : ℕ} {t0 M M' Φ ε δ : ℝ}
    (hN : 0 < N) (ht10 : t1 ≤ t0)
    (hη : ∀ t ∈ Icc t1 t0, 0 < η t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → η t ≤ η u)
    (hηc : ContinuousOn η (Icc t1 t0))
    (hδ : ∀ t ∈ Icc t1 t0, (N * η t)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hsm : ∀ t ∈ Icc t1 t0, t - t1 ≤ ε * η t) (hε : 0 ≤ ε)
    (hDc : ∀ m ∈ Set.Icc 2 n0, ContinuousOn (Dm m) (Icc t1 t0))
    (hL0 : ∀ m t, 0 ≤ Lm m t) (hD0 : ∀ m t, 0 ≤ Dm m t)
    (hL : ∀ j, 2 ≤ j → j ≤ 2 * n0 → ∀ t ∈ Icc t1 t0, Lm j t ≤ M * (N * η t)⁻¹ ^ (j - 1))
    (h746 : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Φ * rhs746 N η t1 Lm Dm m t)
    (hM : 0 ≤ M) (hM' : 0 ≤ M') (hΦ : 0 ≤ Φ)
    (hcond : Φ * (ε * n0 * ((1 + M') * M') + 1 + ε * (M * M) + Real.sqrt (ε * M)) < M') :
    ∀ t ∈ Icc t1 t0, ∀ m ∈ Set.Icc 2 n0, Dm m t < M' * (N * η t)⁻¹ ^ m := by
  have hx0 : ∀ t ∈ Icc t1 t0, 0 < (N * η t)⁻¹ := fun t ht => inv_pos.2 (mul_pos hN (hη t ht))
  have hgc : ∀ m ∈ Set.Icc 2 n0, ContinuousOn (fun t => M' * (N * η t)⁻¹ ^ m) (Icc t1 t0) :=
    fun m _ => continuousOn_const.mul
      (((continuousOn_const.mul hηc).inv₀ fun t ht => (mul_pos hN (hη t ht)).ne').pow _)
  have hc1 : 0 ≤ ε * n0 * ((1 + M') * M') := by positivity
  have hc3 : 0 ≤ ε * (M * M) := by positivity
  have hc4 : 0 ≤ Real.sqrt (ε * M) := Real.sqrt_nonneg _
  refine continuity_argument (Set.finite_Icc 2 n0) hDc hgc (fun m hm => ?_)
    (fun t ht hprev m hm => ?_)
  · have ht1 : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
    have hD := h746 m hm t1 ht1
    rw [rhs746_self] at hD
    have hpos : 0 < (N * η t1)⁻¹ ^ m := pow_pos (hx0 t1 ht1) _
    show Dm m t1 < M' * (N * η t1)⁻¹ ^ m
    have : Φ < M' := by nlinarith
    nlinarith
  show Dm m t < M' * (N * η t)⁻¹ ^ m
  set x := (N * η t)⁻¹ with hx
  have hxp := hx0 t ht
  have hx1 : x ≤ 1 := (hδ t ht).trans hδ1
  have hηt := hη t ht
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  obtain ⟨hm2, hmn⟩ := hm
  have hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x := by
    intro u hu
    have hu0 := hsub hu
    refine ⟨(hx0 u hu0).le, inv_anti₀ (mul_pos hN hηt) ?_⟩
    exact mul_le_mul_of_nonneg_left (hanti u hu0 t ht hu.2) hN.le
  have hLu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ 2 * n0 → Lm j u ≤ M * x ^ (j - 1) := by
    intro u hu j h2 hj
    refine (hL j h2 hj u (hsub hu)).trans ?_
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hDu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ m → 0 ≤ Dm j u ∧
      Dm j u ≤ M' * x ^ (j - 1 + 1) := by
    intro u hu j h2 hj
    refine ⟨hD0 j u, (hprev u hu j ⟨h2, hj.trans hmn⟩).trans ?_⟩
    have : j - 1 + 1 = j := by omega
    rw [this]
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hmx : x⁻¹ * x ^ (m + 1) = x ^ m := by
    rw [inv_mul_pow hxp.ne' (by omega)]; rfl
  have hm0 : (m : ℝ) ≤ n0 := by exact_mod_cast hmn
  have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
  -- line 1
  have hl1 := supOn_line1_le N η t1 (n := m) 1 le_rfl ht1t hM' hxp.le hx1 hxu hDu
  have hline1 : N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (m - k + 2) u) t1 t
      ≤ ε * n0 * ((1 + M') * M') * x ^ m := by
    calc _ ≤ N * (t - t1) * (m * ((1 + M') * M' * x ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left hl1 hNt
      _ ≤ ε * x⁻¹ * (m * ((1 + M') * M' * x ^ (m + 1))) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * m * ((1 + M') * M') * (x⁻¹ * x ^ (m + 1)) := by ring
      _ ≤ ε * n0 * ((1 + M') * M') * (x⁻¹ * x ^ (m + 1)) := by gcongr
      _ = _ := by rw [hmx]
  -- line 3
  have hline3 : N * (t - t1) * supOn (fun u => Lm 2 u * Lm (m + 1) u) t1 t
      ≤ ε * (M * M) * x ^ m := by
    have hsup : supOn (fun u => Lm 2 u * Lm (m + 1) u) t1 t ≤ M * M * x ^ (m + 1) := by
      refine supOn_le ht1t fun u hu => ?_
      have h2 : Lm 2 u ≤ M * x := by simpa using hLu u hu 2 le_rfl (by omega)
      have h3 : Lm (m + 1) u ≤ M * x ^ m := by simpa using hLu u hu (m + 1) (by omega) (by omega)
      calc Lm 2 u * Lm (m + 1) u ≤ (M * x) * (M * x ^ m) :=
            mul_le_mul h2 h3 (hL0 _ u) (by positivity)
        _ = M * M * x ^ (m + 1) := by rw [pow_succ']; ring
    calc _ ≤ N * (t - t1) * (M * M * x ^ (m + 1)) := mul_le_mul_of_nonneg_left hsup hNt
      _ ≤ ε * x⁻¹ * (M * M * x ^ (m + 1)) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * (M * M) * (x⁻¹ * x ^ (m + 1)) := by ring
      _ = _ := by rw [hmx]
  -- line 4
  have hline4 : Real.sqrt (t - t1) *
      supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * m) u)) t1 t
      ≤ Real.sqrt (ε * M) * x ^ m := by
    have hsup : supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * m) u)) t1 t
        ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * Real.sqrt (M * x ^ (2 * m - 1)) := by
      refine supOn_le ht1t fun u hu => ?_
      have hu0 := hsub hu
      have hηu : (η u)⁻¹ ≤ (η t)⁻¹ := inv_anti₀ hηt (hanti u hu0 t ht hu.2)
      have hs : Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have : 0 ≤ (η u)⁻¹ := (inv_pos.2 (hη u hu0)).le
        gcongr
      have hs2 : Real.sqrt (Lm (2 * m) u) ≤ Real.sqrt (M * x ^ (2 * m - 1)) :=
        Real.sqrt_le_sqrt (hLu u hu (2 * m) (by omega) (by omega))
      exact mul_le_mul hs hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq := sqrt_mul_sqrt_le N η t1 hN hηt ht1t (hsm t ht)
    have hfin :
        Real.sqrt (ε * x) * Real.sqrt (M * x ^ (2 * m - 1)) = Real.sqrt (ε * M) * x ^ m := by
      rw [← Real.sqrt_mul (by positivity)]
      have : ε * x * (M * x ^ (2 * m - 1)) = ε * M * (x ^ m) ^ 2 := by
        have h2m : 2 * m - 1 + 1 = m * 2 := by omega
        have hxx : x * x ^ (2 * m - 1) = (x ^ m) ^ 2 := by
          rw [← pow_succ', h2m, pow_mul]
        calc ε * x * (M * x ^ (2 * m - 1)) = ε * M * (x * x ^ (2 * m - 1)) := by ring
          _ = ε * M * (x ^ m) ^ 2 := by rw [hxx]
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc _ ≤ Real.sqrt (t - t1) * (Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) *
            Real.sqrt (M * x ^ (2 * m - 1))) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ = (Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2)) *
            Real.sqrt (M * x ^ (2 * m - 1)) := by ring
      _ ≤ Real.sqrt (ε * x) * Real.sqrt (M * x ^ (2 * m - 1)) :=
          mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
      _ = _ := hfin
  have hD := h746 m ⟨hm2, hmn⟩ t ht
  have hrhs : rhs746 N η t1 Lm Dm m t ≤ (ε * n0 * ((1 + M') * M') + 1
      + ε * (M * M) + Real.sqrt (ε * M)) * x ^ m := by
    unfold rhs746
    rw [← hx]
    nlinarith
  have hDt := hD.trans (mul_le_mul_of_nonneg_left hrhs hΦ)
  have hpos : 0 < x ^ m := pow_pos hxp _
  nlinarith

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
the switch of the flow at `t₁` (p. 81: `K_{t,σ,a} = K_{t,σ,a}` for `t ≤ t₁`). -/
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

/-- **The flow of the GUE phase** (p. 81): `H_0 = 0`, `dH_{t,ij} = S_{ij}^{1/2} dB_{t,ij}` for
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

/-- **(2.27) from the inputs of (7.47)**: Theorem 2.5 holds for `H_{t_N}` (with `τ* = c/3`),
chaining `eq747_of_inputs` with `RBM.que_flow_of_eq747` (T68). -/
theorem que_flow_of_inputs (F : OUFlow B H) {κ : ℝ} (hκ : 0 < κ) (t : ℕ → ℝ) (E : ℕ → ℝ)
    (hE : ∀ N, |E N| ≤ 2 - κ) (ζ : ℕ → ℝ)
    (hζ : ∀ᶠ N : ℕ in atTop, 0 < ζ N ∧ ζ N ≤ 1 / 2 ∧ ζ N ≤ B.queEtaN (B.c / 3) N / 16)
    (G : GUEFlow B) (I : Eq747Inputs F t (B.c / 3) E ζ G) :
    (∀ᶠ N : ℕ in atTop, ∀ a : ZMod (B.L N),
      B.P (queEvent212 (F.hermitian N (t N)) a (E N) (B.queEtaN (B.c / 3) N)
        ((B.size N : ℝ) ^ (-(B.c / 3 / 6)))) ≤ ENNReal.ofReal ((B.size N : ℝ) ^ (-(B.c / 3 / 6)))) ∧
    (∀ᶠ N : ℕ in atTop, ∀ A : Finset (ZMod (B.L N)), A.Nonempty →
      B.P (queEvent213 (F.hermitian N (t N)) A (E N) (B.queEtaN (B.c / 3) N) (B.c / 3)) ≤
        ENNReal.ofReal ((B.size N : ℝ) ^ (-(B.c / 3 / 6)))) := by
  have hc := B.c_pos
  refine que_flow_of_eq747 F hκ t E hE ζ hζ
    (eq747_of_inputs F t (by positivity) E ζ (fun N => (hE N).trans (by linarith)) ?_ G I)
  filter_upwards [hζ] with N h
  exact ⟨h.1.le, by linarith [h.2.1]⟩

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

/-- The smallness bookkeeping of (7.45): with `p = N^{τ'} ≥ 1`, `q = N^{-τ_U}` and
`p³ q ≤ ρ := (36 (20 n₀ + 48))⁻¹`, the condition of `eq727_path` holds with `A = Φ = p`,
`M = 3p`, `ε = δ = q`. -/
theorem cond727 {p q : ℝ} (n0 : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48))) :
    p + p * (q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) + q
      + q * (3 * p * Real.sqrt (3 * p) * (3 * p)) + Real.sqrt q * (3 * p)) < 3 * p := by
  set r := p ^ 3 * q with hrdef
  have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hρ : 1 / (36 * (20 * (n0 : ℝ) + 48)) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 * q ≤ r := by
    rw [hrdef]; have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
    exact mul_le_mul_of_nonneg_right this hq
  have hq1 : q ≤ r := by
    rw [hrdef]; have : 1 ≤ p ^ 3 := one_le_pow₀ hp
    nlinarith
  have hsq3 : Real.sqrt (3 * p) ≤ 3 * p := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hT1 : q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) ≤ 20 * n0 * r := by
    have h1 : (1 + (3 * p + p)) * (3 * p + p) ≤ 20 * p ^ 2 := by nlinarith
    calc q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) ≤ q * n0 * (20 * p ^ 2) := by gcongr
      _ = 20 * n0 * (p ^ 2 * q) := by ring
      _ ≤ 20 * n0 * r := by gcongr
  have hT3 : q * (3 * p * Real.sqrt (3 * p) * (3 * p)) ≤ 27 * r := by
    calc q * (3 * p * Real.sqrt (3 * p) * (3 * p)) ≤ q * (3 * p * (3 * p) * (3 * p)) := by gcongr
      _ = 27 * r := by rw [hrdef]; ring
  have hT4 : Real.sqrt q * (3 * p) ≤ 3 * Real.sqrt r := by
    have : Real.sqrt q * p = Real.sqrt (p ^ 2 * q) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp0.le]; ring
    have h2 : Real.sqrt (p ^ 2 * q) ≤ Real.sqrt r := Real.sqrt_le_sqrt hp2
    nlinarith
  have hsr : Real.sqrt r ≤ 1 / 6 := by
    rw [show (1 : ℝ) / 6 = Real.sqrt (1 / 36) by
      rw [show (1 : ℝ) / 36 = (1 / 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hr.trans hρ)
  have hsum : (20 * n0 + 48) * r ≤ 1 / 36 := by
    have h48 : (0 : ℝ) < 20 * n0 + 48 := by positivity
    calc (20 * n0 + 48) * r ≤ (20 * n0 + 48) * (1 / (36 * (20 * n0 + 48))) := by gcongr
      _ = 1 / 36 := by field_simp
  have hr0 : 0 ≤ r := by positivity
  have hS : q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) + q
      + q * (3 * p * Real.sqrt (3 * p) * (3 * p)) + Real.sqrt q * (3 * p) < 2 := by nlinarith
  nlinarith


/-! #### Maxima over `(σ, a)` -/

/-- `max_i |f_i| ≤ max_i |f_i - g_i| + max_i |g_i|` over a finite index set (the relation
`L = (L - K) + K` between the maxima used in (7.45)). -/
theorem iSup_norm_le_add {ι : Type*} [Finite ι] (f g : ι → ℂ) :
    ⨆ i, ‖f i‖ ≤ (⨆ i, ‖f i - g i‖) + ⨆ i, ‖g i‖ := by
  have h1 : 0 ≤ ⨆ i, ‖f i - g i‖ := Real.iSup_nonneg fun i => norm_nonneg _
  have h2 : 0 ≤ ⨆ i, ‖g i‖ := Real.iSup_nonneg fun i => norm_nonneg _
  refine Real.iSup_le (fun i => ?_) (add_nonneg h1 h2)
  have hb1 : BddAbove (Set.range fun i => ‖f i - g i‖) := Set.finite_range _ |>.bddAbove
  have hb2 : BddAbove (Set.range fun i => ‖g i‖) := Set.finite_range _ |>.bddAbove
  calc ‖f i‖ = ‖(f i - g i) + g i‖ := by rw [sub_add_cancel]
    _ ≤ ‖f i - g i‖ + ‖g i‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (le_ciSup hb1 i) (le_ciSup hb2 i)

/-- The maximum `max_{|I| = m} |K_{t,I}|` over the well-formed loops of length `m`
(`2 ≤ m ≤ n₀`). -/
noncomputable def kMax (Lf : ℕ → ℕ) (Kt : ∀ N, ℝ → LoopIdx (ZMod (Lf N)) → ℂ) (n0 N m : ℕ)
    (t : ℝ) : ℝ :=
  ⨆ I : {I : LoopSet (Lf N) n0 // I.1.length = m}, ‖Kt N t I.1.1‖

/-- **(7.36) in the maximum form used by (7.27)**: the per-loop bound of `eq736_detDom` gives
`max_{σ,a} |K^{(m)}_{t,σ,a}| ≺ λ_t^{-m+1}`, the hypothesis `hK` of `eq727`. -/
theorem kMax_detDom (Lf : ℕ → ℕ) (Kt : ∀ N, ℝ → LoopIdx (ZMod (Lf N)) → ℂ) (n0 : ℕ)
    {t1 t0 : ℕ → ℝ} (lam : ℕ → ℝ → ℝ) (hlam : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < lam N t)
    (h : UnifDetDom (fun N (p : TimeIcc t1 t0 N × LoopSet (Lf N) n0) => ‖Kt N p.1 p.2.1‖)
      (fun N p => (lam N p.1)⁻¹ ^ (p.2.1.length - 1))) :
    UnifDetDom (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) => kMax Lf Kt n0 N p.2 p.1)
      (fun N p => (lam N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) := by
  intro τ hτ
  filter_upwards [h τ hτ, eventually_ge_atTop 1] with N hN hN1
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have hpos : 0 ≤ (N : ℝ) ^ τ * (lam N t)⁻¹ ^ (m - 1) := by
    have := hlam N t ht
    have : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
    positivity
  refine Real.iSup_le (fun I => ?_) hpos
  have h1 := hN (⟨t, ht⟩, I.1)
  rw [I.2] at h1
  exact h1

/-- **(7.27)**: `max_{σ,a} |L_{t,σ,a}| ≺ (N η_t)^{-n+1}` for `t ∈ [t₁, t₀]`, `2 ≤ n ≤ n₀`, from
(7.45) (as a `≺` bound, uniform in `t` and `n`), (7.36) for `K`, (7.30) in the form
`t - t₁ ≤ N^{-τ_U} η_t`, `(N η_t)^{-1} ≤ N^{-τ_U}`, and the time continuity of the loops (w.h.p.).
`Lm N n t ω`, `Dm N n t ω` are the maxima over `(σ, a)` of `|L^{(n)}|`, `|(L-K)^{(n)}|`, and
`Km N n t` that of `|K^{(n)}|`; `Nf N` is the matrix size. -/
theorem eq727 {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ) (Km : ℕ → ℕ → ℝ → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ (N : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (hLDK : ∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc (t1 N) (t0 N), Lm N m t ω ≤ Dm N m t ω + Km N m t)
    (hDLK : ∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc (t1 N) (t0 N), Dm N m t ω ≤ Lm N m t ω + Km N m t)
    (hK : UnifDetDom (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) => Km N p.2 p.1)
      (fun N p => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcont : HighProb P (fun N => {ω | ∀ m ∈ Set.Icc 2 n0,
      ContinuousOn (fun t => Lm N m t ω) (Icc (t1 N) (t0 N))}))
    (h745 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Dm N p.2 p.1 ω)
      (fun N p ω => rhs745 (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2 p.1)) :
    StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) := by
  refine stochDom_of_forall_highProb fun τ hτ => ?_
  set τ' := min τ τU / 16 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : 3 * τ' - τU < 0 := by have := min_le_right τ τU; linarith
  have hρ : (0 : ℝ) < 1 / (36 * (20 * n0 + 48)) := by positivity
  refine ((h745.highProb hτ'0).inter hcont).mono ?_
  filter_upwards [hK τ' hτ'0, h730, hscale, eventually_rpow_le_of_neg hτ'U hρ,
    eventually_le_rpow 3 (sub_pos.2 hτ'τ), eventually_ge_atTop 1]
    with N hKN h730N hscN hrN h3N hN1
  rintro ω ⟨h745ω, hcω⟩
  simp only [Set.mem_ofPred_eq] at h745ω hcω ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set p := (N : ℝ) ^ τ' with hpdef
  set q := (N : ℝ) ^ (-τU) with hqdef
  have hp1 : 1 ≤ p := Real.one_le_rpow (by exact_mod_cast hN1) hτ'0.le
  have hq0 : 0 ≤ q := Real.rpow_nonneg hN0.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  have hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48)) := by
    have : p ^ 3 * q = (N : ℝ) ^ (3 * τ' - τU) := by
      rw [hpdef, hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      push_cast; ring_nf
    rw [this]; exact hrN
  have key := eq727_path (Nf N) (η N) (t1 N) (Lm := fun m t => Lm N m t ω)
    (Dm := fun m t => Dm N m t ω) (Km := Km N) (n0 := n0) (A := p) (M := 3 * p) (Φ := p)
    (ε := q) (δ := q) (hN N) (ht10 N) (hη N) (hanti N) (hηc N) hscN hq1 h730N hq0
    (fun m hm => hcω m hm) (fun m t => hL0 N m t ω) (fun m t => hD0 N m t ω) (hLDK N ω)
    (hDLK N ω) (fun m hm t ht => by simpa using hKN (⟨t, ht⟩, ⟨m, hm⟩))
    (fun m hm t ht => by simpa using h745ω (⟨t, ht⟩, ⟨m, hm⟩)) (by linarith) (by linarith)
    (by linarith) (cond727 n0 hp1 hq0 hr)
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have h1 := key t ht m hm
  have hx : 0 ≤ (Nf N * η N t)⁻¹ ^ (m - 1) := by
    have := hη N t ht; have := hN N; positivity
  have h3 : 3 * p ≤ (N : ℝ) ^ τ := by
    have e : (N : ℝ) ^ τ = (N : ℝ) ^ (τ - τ') * p := by
      rw [hpdef, ← Real.rpow_add hN0]; ring_nf
    rw [e]; nlinarith
  show Lm N m t ω ≤ (N : ℝ) ^ τ * (Nf N * η N t)⁻¹ ^ (m - 1)
  nlinarith

/-- The smallness bookkeeping of (7.46): with `p = N^{τ'} ≥ 1`, `q = N^{-τ_U}`, `p³ q ≤ ρ`, the
condition of `eq728_path` holds with `Φ = M = p`, `M' = 3p`, `ε = q`. -/
theorem cond728 {p q : ℝ} (n0 : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48))) :
    p * (q * n0 * ((1 + 3 * p) * (3 * p)) + 1 + q * (p * p) + Real.sqrt (q * p)) < 3 * p := by
  set r := p ^ 3 * q with hrdef
  have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hρ : 1 / (36 * (20 * (n0 : ℝ) + 48)) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 * q ≤ r := by
    rw [hrdef]; have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
    exact mul_le_mul_of_nonneg_right this hq
  have hp1 : q * p ≤ r := by
    rw [hrdef]; have : p ≤ p ^ 3 := by nlinarith
    nlinarith
  have hT1 : q * n0 * ((1 + 3 * p) * (3 * p)) ≤ 12 * n0 * r := by
    have h1 : (1 + 3 * p) * (3 * p) ≤ 12 * p ^ 2 := by nlinarith
    calc q * n0 * ((1 + 3 * p) * (3 * p)) ≤ q * n0 * (12 * p ^ 2) := by gcongr
      _ = 12 * n0 * (p ^ 2 * q) := by ring
      _ ≤ 12 * n0 * r := by gcongr
  have hsr : Real.sqrt (q * p) ≤ 1 / 6 := by
    rw [show (1 : ℝ) / 6 = Real.sqrt (1 / 36) by
      rw [show (1 : ℝ) / 36 = (1 / 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ((hp1.trans hr).trans hρ)
  have hsum : (20 * n0 + 48) * r ≤ 1 / 36 := by
    have h48 : (0 : ℝ) < 20 * n0 + 48 := by positivity
    calc (20 * n0 + 48) * r ≤ (20 * n0 + 48) * (1 / (36 * (20 * n0 + 48))) := by gcongr
      _ = 1 / 36 := by field_simp
  have hr0 : 0 ≤ r := by positivity
  have hqpp : q * (p * p) ≤ r := by nlinarith
  have hS : q * n0 * ((1 + 3 * p) * (3 * p)) + 1 + q * (p * p) + Real.sqrt (q * p) < 2 := by
    nlinarith
  nlinarith

/-- **(7.28)**: `max_{σ,a} |L_{t,σ,a} - K_{t,σ,a}| ≺ (N η_t)^{-n}` for `t ∈ [t₁, t₀]`,
`2 ≤ n ≤ n₀`, from (7.46) (as a `≺` bound), (7.27) for all lengths `2 ≤ j ≤ 2n₀` (the right side
of (7.46) contains `L^{(n+1)}` and `L^{(2n)}`: "after the induction for `L` has been completed"),
(7.30) as in `eq727`, and the time continuity of `L - K` (w.h.p.). -/
theorem eq728 {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ (N : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (h727 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcont : HighProb P (fun N => {ω | ∀ m ∈ Set.Icc 2 n0,
      ContinuousOn (fun t => Dm N m t ω) (Icc (t1 N) (t0 N))}))
    (h746 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Dm N p.2 p.1 ω)
      (fun N p ω => rhs746 (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2 p.1)) :
    StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Dm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ (p.2 : ℕ)) := by
  refine stochDom_of_forall_highProb fun τ hτ => ?_
  set τ' := min τ τU / 16 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : 3 * τ' - τU < 0 := by have := min_le_right τ τU; linarith
  have hρ : (0 : ℝ) < 1 / (36 * (20 * n0 + 48)) := by positivity
  refine (((h746.highProb hτ'0).inter hcont).inter (h727.highProb hτ'0)).mono ?_
  filter_upwards [h730, hscale, eventually_rpow_le_of_neg hτ'U hρ,
    eventually_le_rpow 3 (sub_pos.2 hτ'τ), eventually_ge_atTop 1]
    with N h730N hscN hrN h3N hN1
  rintro ω ⟨⟨h746ω, hcω⟩, hLω⟩
  simp only [Set.mem_ofPred_eq] at h746ω hcω hLω ⊢
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set p := (N : ℝ) ^ τ' with hpdef
  set q := (N : ℝ) ^ (-τU) with hqdef
  have hp1 : 1 ≤ p := Real.one_le_rpow (by exact_mod_cast hN1) hτ'0.le
  have hq0 : 0 ≤ q := Real.rpow_nonneg hN0.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  have hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48)) := by
    have : p ^ 3 * q = (N : ℝ) ^ (3 * τ' - τU) := by
      rw [hpdef, hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      push_cast; ring_nf
    rw [this]; exact hrN
  have key := eq728_path (Nf N) (η N) (t1 N) (Lm := fun m t => Lm N m t ω)
    (Dm := fun m t => Dm N m t ω) (n0 := n0) (M := p) (M' := 3 * p) (Φ := p)
    (ε := q) (δ := q) (hN N) (ht10 N) (hη N) (hanti N) (hηc N) hscN hq1 h730N hq0
    (fun m hm => hcω m hm) (fun m t => hL0 N m t ω) (fun m t => hD0 N m t ω)
    (fun j h2 hj t ht => by simpa using hLω (⟨t, ht⟩, ⟨j, h2, hj⟩))
    (fun m hm t ht => by simpa using h746ω (⟨t, ht⟩, ⟨m, hm⟩)) (by linarith) (by linarith)
    (by linarith) (cond728 n0 hp1 hq0 hr)
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have h1 := key t ht m hm
  have hx : 0 ≤ (Nf N * η N t)⁻¹ ^ m := by
    have := hη N t ht; have := hN N; positivity
  have h3 : 3 * p ≤ (N : ℝ) ^ τ := by
    have e : (N : ℝ) ^ τ = (N : ℝ) ^ (τ - τ') * p := by
      rw [hpdef, ← Real.rpow_add hN0]; ring_nf
    rw [e]; nlinarith
  show Dm N m t ω ≤ (N : ℝ) ^ τ * (Nf N * η N t)⁻¹ ^ m
  nlinarith

/-- **(7.45) + (7.46) ⟹ (7.27) + (7.28)**, the closing of §7.2: (7.27) is `eq727` at the loop
lengths `2 ≤ j ≤ 2n₀`, which is what the second pass (7.46) needs, and (7.28) then follows from
`eq728` for `2 ≤ n ≤ n₀`. -/
theorem eq728_of_eq745 {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ) (Km : ℕ → ℕ → ℝ → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ (N : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ (N : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (hLDK : ∀ N ω, ∀ m ∈ Set.Icc 2 (2 * n0), ∀ t ∈ Icc (t1 N) (t0 N),
      Lm N m t ω ≤ Dm N m t ω + Km N m t)
    (hDLK : ∀ N ω, ∀ m ∈ Set.Icc 2 (2 * n0), ∀ t ∈ Icc (t1 N) (t0 N),
      Dm N m t ω ≤ Lm N m t ω + Km N m t)
    (hK : UnifDetDom (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) => Km N p.2 p.1)
      (fun N p => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcontL : HighProb P (fun N => {ω | ∀ m ∈ Set.Icc 2 (2 * n0),
      ContinuousOn (fun t => Lm N m t ω) (Icc (t1 N) (t0 N))}))
    (hcontD : HighProb P (fun N => {ω | ∀ m ∈ Set.Icc 2 n0,
      ContinuousOn (fun t => Dm N m t ω) (Icc (t1 N) (t0 N))}))
    (h745 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) ω => Dm N p.2 p.1 ω)
      (fun N p ω => rhs745 (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2 p.1))
    (h746 : StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Dm N p.2 p.1 ω)
      (fun N p ω => rhs746 (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2 p.1)) :
    StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) ∧
    StochDom P (fun N (p : TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Dm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ (p.2 : ℕ)) := by
  have h727 := eq727 (P := P) (n0 := 2 * n0) Nf η t1 t0 Lm Dm Km hN ht10 hη hanti hηc hτU h730
    hscale hL0 hD0 hLDK hDLK hK hcontL h745
  exact ⟨h727, eq728 Nf η t1 t0 Lm Dm hN ht10 hη hanti hηc hτU h730 hscale hL0 hD0 h727 hcontD
    h746⟩

end Domination

end GUEPhase

end RBM

