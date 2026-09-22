/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.DriftDef
import RBM1D.Gauss.MomentDuhamelRhs

/-!
# Lemma 5.10, (5.77) lines 1-3, for the pinned drift (T165)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, Lemma 5.10, (5.77), first three lines, and §5.5's consumption of them.

`RBM1D/Hierarchy/DriftDef.lean` (T58/T118 (iii)) proved that the drift of
`RBM.MomentDuhamel.Hyp` **is** `RBM.DriftDef.driftF`, a definition in the Green function of
the flow, and that its three summands are `RBM.Decay.eG`, `∑_{l_K ≥ 3} RBM.Decay.couplingLen`
and `RBM.primBil (L-K) (L-K)`.  `RBM1D/Hierarchy/Decay.lean` (T59) bounds each of those.  This
file does the `Ξ`-bookkeeping between the two, and then carries the result all the way to the
hypothesis `hFmom` of `RBM.Gauss.hrhs_of_moment_inputs`.

**Nothing here instantiates `RBM.SumZeroDyn.Hierarchy` and nothing here uses a field of
`RBM.SumZeroDyn.Lemma510`** (T118).  (5.77) is a theorem about `RBM.DriftDef.driftF`, not a
structure field.

## The `Ξ`-bookkeeping, term by term

Write `m = n + 2` for the loop length, `A = W ℓ_u η_u` (`RBM.Band.scale`), `ℓ = ℓ_u · Krad`
for the decay radius of Lemma 5.9 (in the paper `Krad = N^τ`), and `δ` for its error.  The
single identity that converts `RBM.Decay`'s shape into (5.77)'s is
`W(ℓ + 1)/A ≤ (Krad + 2)/η_u` (`RBM.Decay.mul_add_one_div_le`), which is where every factor
`η_u^{-1}` of (5.77) comes from.

* `RBM.Decay.norm_couplingLen_le` gives, for each of the `n` values `3 ≤ l_K ≤ m`,
  `4e m² C_K Φ (W(ℓ+1)/A) A^{-m} + 2m² W L δ Φ` with `Φ = ∑_{k=1}^{m-1} Ξ^{(L-K)}_{u,k}` — the
  **first** summand of `RBM.SumZeroDyn.xiRhs`.
* `RBM.Decay.norm_primBil_sub_le` gives `2e m² Φ (W(ℓ+1)/A) A^{-m} + m² W L δ B` with
  `Φ = ∑_{k=2}^{m} Ξ^{(L-K)}_{u,k} Ξ^{(L-K)}_{u,m-k+2} A^{-1}` — the **second** summand of
  `xiRhs` — and `B = ∑_{k=2}^{m} Ξ^{(L-K)}_{u,k}`, which only enters the error.
* `RBM.Decay.norm_eG_le` gives `2e m Ξ₂ Φ (W(ℓ+1)/A) A^{-m} + m W L δ Ξ₂` with
  `Φ = Ξ^{(L)}_{u,m+1}` — the **third** summand of `xiRhs` — and `Ξ₂ = Ξ^{(L-K)}_{u,1}`.

Collecting: `‖F‖ ≤ A^{-m} η_u^{-1} (Krad + 2) · c(n) · Ξ_rhs + W L δ · (error)` with
`c(n) = 4e m² (n C_K + 1 + C₁)` (`RBM.DriftBound.cDrift`).  This is
`RBM.DriftBound.norm_driftF_le`.

### The one input (5.77) does not name

The third line of (5.77) is stated with a *bare* `Ξ^{(L)}_{u,m+1}`, while
`RBM.Decay.norm_eG_le` carries the extra factor `Ξ₂ = Ξ^{(L-K)}_{u,1}`.  The paper drops it
because `Ξ^{(L-K)}_{u,1} ≲ 1` — (2.68) at one loop.  That is *not* derivable from the other
two lines, so it is an explicit hypothesis here, `Ξ^{(L-K)}_{u,1} ≤ C₁`; it is the last field
of `RBM.DriftBound.DriftInputs`.  Every other input is Lemma 5.9's decay or (5.76).

### The length-`0` loop

`RBM.Decay.norm_couplingLen_le` asks for `|(L-K)_J| ≤ Φ A^{-|J|}` at *every* length `|J| < m`,
including `0`, where `L_∅ = ⟨1⟩ = LW` is not small and would force `Φ ≥ LW`.  The coupling
never looks at such a loop (cutting and gluing leaves two loops of length `≥ 2`), so
`RBM.DriftBound.dTrunc` sets `L - K` to `0` below length `2` and
`RBM.DriftBound.couplingLen_dTrunc` shows the coupling does not notice.  Without this step the
first line of (5.77) is unreachable from `RBM.Decay` as stated.

## Main results

* `RBM.DriftBound.norm_driftF_le` — **(5.77), lines 1-3, pointwise**, with every constant
  explicit and an explicit `W L δ (…)` error.
* `RBM.DriftBound.norm_Hyp_F_le` — the same for `RBM.MomentDuhamel.Hyp.F` along the flow, via
  `RBM.DriftDef.Fpath_eq_driftF_of_lt_one`.
* `RBM.DriftBound.stochDom_norm_driftF` — **(5.77), lines 1-3, as `≺`**, with the
  *deterministic* control `(Wℓ_uη_u)^{-(n+2)} η_u^{-1} ((2n+3) Φ)`, from
  `RBM.DriftBound.DriftInputs` with high probability.  The multiplicative `N^τ` and the
  additive `N^{-D}` are absorbed by `RBM.StochDom.of_highProb_add_rpow_neg`.
* `RBM.DriftBound.stochDom_det_of_xiRhs` — `RBM.SumZeroDyn.F_stochDom` with the structures
  removed: the field `F_le` becomes a hypothesis about an ordinary function.
* `RBM.DriftBound.hdom_of_driftInputs` — **the `hdom` of `RBM.Gauss.hFmom_of_stochDom`,
  delivered**, verbatim the conclusion of `RBM.SumZeroDyn.F_stochDom`.
* `RBM.DriftBound.hFmom_of_driftInputs` — and hence `hFmom` of
  `RBM.Gauss.hrhs_of_moment_inputs` itself, with no `Lemma510` field left in the chain.

## What this does *not* do

`RBM.DriftBound.DriftInputs` is a hypothesis, not a theorem: it packages Lemma 5.9's decay of
`K`, `L` and `L - K` at radius `ℓ_u N^τ` with error `N^{-D}`, together with the power counts
(5.76) at the budget `N^τ (2n+3) Φ` and `Ξ^{(L-K)}_{u,1} ≤ C₁`.  These are the inputs of
Lemma 5.10 in the paper, produced elsewhere (`RBM.Decay.lemma59` for the decay, Step 3 for the
counts); none of them mentions the drift.
-/

namespace RBM
namespace DriftBound

open Matrix Finset Real

/-! ### Truncating the second argument of the coupling below length `2` -/

section Trunc

variable (L : ℕ) [NeZero L]

/-- `L - K`, set to `0` on the loops of length `< 2`.  `RBM.Decay.couplingLen` does not see the
difference (`RBM.DriftBound.couplingLen_dTrunc`), because cutting and gluing always leaves two
loops of length `≥ 2`; but the hypothesis of `RBM.Decay.norm_couplingLen_le` quantifies over
*all* shorter loops, and at length `0` the loop `L_∅ = ⟨1⟩ = LW` is not small at all. -/
noncomputable def dTrunc (D : LoopIdx (ZMod L) → ℂ) : LoopIdx (ZMod L) → ℂ :=
  fun J => if 2 ≤ J.length then D J else 0

variable {L}

omit [NeZero L] in
theorem dTrunc_apply_of_two_le {D : LoopIdx (ZMod L) → ℂ} {J : LoopIdx (ZMod L)}
    (h : 2 ≤ J.length) : dTrunc L D J = D J := by
  rw [dTrunc]
  split_ifs
  rfl

omit [NeZero L] in
theorem norm_dTrunc_le {D : LoopIdx (ZMod L) → ℂ} {J : LoopIdx (ZMod L)} {c : ℝ} (hc : 0 ≤ c)
    (h : 2 ≤ J.length → ‖D J‖ ≤ c) : ‖dTrunc L D J‖ ≤ c := by
  rw [dTrunc]
  split_ifs with h2
  · exact h h2
  · simpa using hc

variable (L)

theorem primBilLen_dTrunc (W lK : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    primBilLen L W lK K (dTrunc L D) I = primBilLen L W lK K D I := by
  rw [primBilLen, primBilLen]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [dTrunc_apply_of_two_le (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)]

theorem primBilLenR_dTrunc (W lK : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    Decay.primBilLenR L W lK (dTrunc L D) K I = Decay.primBilLenR L W lK D K I := by
  rw [Decay.primBilLenR, Decay.primBilLenR]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  rw [dTrunc_apply_of_two_le (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)]

/-- **The coupling does not see the truncation.** -/
theorem couplingLen_dTrunc (W lK : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    Decay.couplingLen L W lK K (dTrunc L D) I = Decay.couplingLen L W lK K D I := by
  rw [Decay.couplingLen, Decay.couplingLen, primBilLen_dTrunc, primBilLenR_dTrunc]

end Trunc

/-! ### Every well-formed loop index is the index of a `LoopData` -/

section Repr

theorem exists_loopData {L : ℕ} (J : LoopIdx (ZMod L)) (hJ : J.WF) :
    ∃ d : LoopData L J.length, LoopData.idx d = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at hJ
  simp only [LoopIdx.length]
  refine ⟨(fun i => σ.get (Fin.cast hJ.symm i), fun i => a.get i), ?_⟩
  have hσ' : List.ofFn (fun i : Fin a.length => σ.get (Fin.cast hJ.symm i)) = σ := by
    apply List.ext_get <;> simp [hJ]
  have ha' : List.ofFn (fun i : Fin a.length => a.get i) = a := List.ofFn_get a
  rw [LoopData.idx, hσ', ha']

end Repr

/-! ### The power counts (5.76) as pointwise bounds -/

section Counts

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `|(L - K)_{u,σ,a}| ≤ Ξ^{(L-K)}_{u,j} (Wℓ_uη_u)^{-j}` — (5.76) read backwards. -/
theorem norm_lk_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (hA : B.scale E N u ≠ 0) (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF) {j : ℕ}
    (hj : J.length = j) :
    ‖(gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u) J‖
      ≤ X.xiLK E N u ω j * (B.scale E N u)⁻¹ ^ j := by
  obtain ⟨d, hd⟩ := exists_loopData J hJ
  have h1 : X.lkErr E N u ω J ≤ X.lkMax E N u ω J.length := by
    have := X.lkErr_le_lkMax (E := E) (t := u) (ω := ω) d
    rwa [hd] at this
  subst hj
  have h2 : X.xiLK E N u ω J.length * (B.scale E N u)⁻¹ ^ J.length
      = X.lkMax E N u ω J.length := by
    rw [Sample.xiLK, mul_assoc, ← mul_pow, mul_inv_cancel₀ hA, one_pow, mul_one]
  rw [h2]
  exact h1

/-- `|L_{u,σ,a}| ≤ Ξ^{(L)}_{u,j} (Wℓ_uη_u)^{-(j-1)}` — (5.76) read backwards. -/
theorem norm_gloop_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (hA : B.scale E N u ≠ 0) (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF) {j : ℕ}
    (hj : J.length = j) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) J‖
      ≤ X.xiL E N u ω j * (B.scale E N u)⁻¹ ^ (j - 1) := by
  obtain ⟨d, hd⟩ := exists_loopData J hJ
  have h1 : ‖X.Lval E N u ω J‖ ≤ loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) J.length := by
    have := X.norm_Lval_le_loopMax (E := E) (t := u) (ω := ω) d
    rwa [hd] at this
  subst hj
  have h2 : X.xiL E N u ω J.length * (B.scale E N u)⁻¹ ^ (J.length - 1)
      = loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) J.length := by
    rw [Sample.xiL, loopXi, mul_assoc, ← mul_pow, mul_inv_cancel₀ hA, one_pow, mul_one]
  rw [h2]
  exact h1

end Counts

/-! ### (5.77), lines 1-3, pointwise -/

section Pointwise

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

omit [MeasurableSpace Ω] in
theorem loopTensor_idx {L n : ℕ} (F : LoopIdx (ZMod L) → ℂ) (σ : Fin n → Bool)
    (a : LoopArg L n) : F (LoopData.idx (σ, a)) = Decay.loopTensor L F σ a := rfl

/-- The constant of (5.77) at loop length `n + 2`. -/
noncomputable def cDrift (n : ℕ) (CK C1 : ℝ) : ℝ :=
  4 * Real.exp 1 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) * CK + 1 + C1)

/-- `∑_{k=1}^{m} Ξ^{(L-K)}_{u,k}`, the `Ξ`-factor of the super-polynomially small error. -/
noncomputable def xiSum (X : Sample B) (E : ℝ) (m N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, X.xiLK E N u ω k

theorem main_term_le {e mm nn CK C1 S1 S2 S3 : ℝ} (he : 0 ≤ e) (hmm : 2 ≤ mm) (hnn : 0 ≤ nn)
    (hCK : 0 ≤ CK) (hC1 : 0 ≤ C1) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hS3 : 0 ≤ S3) :
    4 * e * mm ^ 2 * CK * S1 * nn + 2 * e * mm ^ 2 * S2 + 2 * e * mm * C1 * S3
      ≤ 4 * e * mm ^ 2 * (nn * CK + 1 + C1) * (S1 + S2 + S3) := by
  have hm0 : (0 : ℝ) ≤ mm := by linarith
  have hc : (0 : ℝ) ≤ 4 * e * mm ^ 2 := by positivity
  have h4 : (0 : ℝ) ≤ 4 * mm ^ 2 - 2 * mm := by nlinarith
  have h5 : (0 : ℝ) ≤ e * C1 * S3 := by positivity
  have h1 : 2 * e * mm * C1 * S3 ≤ 4 * e * mm ^ 2 * C1 * S3 := by nlinarith [mul_nonneg h5 h4]
  nlinarith [mul_nonneg (mul_nonneg hc (mul_nonneg hnn hCK)) hS2,
    mul_nonneg (mul_nonneg hc (mul_nonneg hnn hCK)) hS3,
    mul_nonneg hc hS1, mul_nonneg hc hS3,
    mul_nonneg (mul_nonneg hc hC1) hS1, mul_nonneg (mul_nonneg hc hC1) hS2]

set_option maxHeartbeats 1600000 in
/-- **(5.77), lines 1-3, for the pinned drift `RBM.DriftDef.driftF`, pointwise.** -/
theorem norm_driftF_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    {Krad δ CK C1 : ℝ}
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u) (hell : 1 / 2 ≤ B.ell N u)
    (hKrad : 1 ≤ Krad) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1) :
    ‖DriftDef.driftF B E N u (X.H N u ω) σ a‖
      ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
          * ((Krad + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
        + (B.W N : ℝ) * (B.L N : ℝ) * δ
            * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1) := by
  classical
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hAne : B.scale E N u ≠ 0 := hA0.ne'
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ0 : (0 : ℝ) < B.ell N u * Krad := by nlinarith
  have hsc : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  have hfrac : (B.W N : ℝ) * (B.ell N u * Krad + 1) / B.scale E N u
      ≤ (Krad + 2) * (etaT E u)⁻¹ := by
    rw [hsc, ← div_eq_mul_inv]
    exact Decay.mul_add_one_div_le hW hell hη
  set A := B.scale E N u with hAdef
  rw [DriftDef.driftF_eq_eG_add]
  set D : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u with hD
  set Lf : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) with hLf
  have hxi : ∀ k, 0 ≤ X.xiLK E N u ω k := fun k => X.xiLK_nonneg hA0.le
  set S1 : ℝ := ∑ k ∈ Finset.Ico 1 (n + 2), X.xiLK E N u ω k with hS1def
  set S2 : ℝ := ∑ k ∈ Finset.Icc 2 (n + 2),
    X.xiLK E N u ω k * X.xiLK E N u ω (n + 2 - k + 2) * A⁻¹ with hS2def
  set S3 : ℝ := X.xiL E N u ω (n + 2 + 1) with hS3def
  set SB : ℝ := ∑ k ∈ Finset.Icc 2 (n + 2), X.xiLK E N u ω k with hSBdef
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun k _ => hxi k
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hxi _) (hxi _)) (inv_nonneg.2 hA0.le)
  have hS30 : 0 ≤ S3 := X.xiL_nonneg hA0.le
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun k _ => hxi k
  have hxiRhs : SumZeroDyn.xiRhs X E (n + 2) N u ω = S1 + S2 + S3 := rfl
  have hSxi1 : S1 ≤ xiSum X E (n + 2) N u ω := by
    rw [hS1def, xiSum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun k _ _ => hxi k)
    rw [Finset.mem_Ico] at hx
    exact Finset.mem_Icc.mpr ⟨hx.1, by omega⟩
  have hSxiB : SB ≤ xiSum X E (n + 2) N u ω := by
    rw [hSBdef, xiSum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun k _ _ => hxi k)
    rw [Finset.mem_Icc] at hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
  -- the bound on `L - K` at every length
  have hDb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → ∀ {j : ℕ}, J.length = j →
      ‖D J‖ ≤ X.xiLK E N u ω j * A⁻¹ ^ j := fun J hJ {j} hj =>
    norm_lk_le X E N u ω hAne J hJ hj
  -- three term bounds
  have hcoup : ∀ lK ∈ Finset.Icc 3 (n + 2),
      ‖Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D (LoopData.idx (σ, a))‖
        ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1
            * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
          + 2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1 := by
    intro lK hlK
    rw [Finset.mem_Icc] at hlK
    rw [← couplingLen_dTrunc]
    have hDt : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length < n + 2 →
        ‖dTrunc (B.L N) D J‖ ≤ S1 * A⁻¹ ^ J.length := by
      intro J hJ hlen
      refine norm_dTrunc_le (by positivity) fun h2 => ?_
      refine (hDb J hJ rfl).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact Finset.single_le_sum (f := fun k => X.xiLK E N u ω k) (fun k _ => hxi k)
        (Finset.mem_Ico.mpr ⟨by omega, hlen⟩)
    have := Decay.norm_loopTensor_couplingLen_le (B.L N) hL3 (B.W N) hlK.1 σ hA hℓ0 hδ hCK
      hS10 hKb hKd hDt a
    push_cast at this ⊢
    exact this
  have hquad : ‖primBil (B.L N) (B.W N) D D (LoopData.idx (σ, a))‖
      ≤ 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2
          * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
        + ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * SB := by
    have hD2 : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
        ‖D J‖ ≤ X.xiLK E N u ω J.length * A⁻¹ ^ J.length := fun J hJ _ _ => hDb J hJ rfl
    have hX : ∀ k, 2 ≤ k → k ≤ n + 2 →
        X.xiLK E N u ω k * X.xiLK E N u ω (n + 2 - k + 2) * A⁻¹ ≤ S2 := fun k h1 h2 =>
      Finset.single_le_sum
        (f := fun k => X.xiLK E N u ω k * X.xiLK E N u ω (n + 2 - k + 2) * A⁻¹)
        (fun k _ => mul_nonneg (mul_nonneg (hxi _) (hxi _)) (inv_nonneg.2 hA0.le))
        (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have hXB : ∀ k, 2 ≤ k → k ≤ n + 2 → X.xiLK E N u ω k ≤ SB := fun k h1 h2 =>
      Finset.single_le_sum (f := fun k => X.xiLK E N u ω k) (fun k _ => hxi k)
        (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have := Decay.norm_loopTensor_primBil_le (B.L N) hL3 (B.W N) σ
      (fun k => X.xiLK E N u ω k) hA hℓ0 hδ hS20 hSB0 hD2 hX hXB hDd a
    push_cast at this ⊢
    exact this
  have heG : ‖Decay.eG (B.L N) (B.W N) D Lf (LoopData.idx (σ, a))‖
      ≤ 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3
          * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
        + ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * δ * C1 := by
    have hXone : ∀ (s : Bool) (b : ZMod (B.L N)),
        ‖D ⟨[s], [b]⟩‖ ≤ C1 * A⁻¹ := by
      intro s b
      have hwf : (⟨[s], [b]⟩ : LoopIdx (ZMod (B.L N))).WF := rfl
      have := hDb ⟨[s], [b]⟩ hwf (j := 1) rfl
      rw [pow_one] at this
      exact this.trans (mul_le_mul_of_nonneg_right hC1 (inv_nonneg.2 hA0.le))
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = (n + 2) + 1 →
        ‖Lf J‖ ≤ S3 * A⁻¹ ^ (n + 2) := by
      intro J hJ hlen
      have := norm_gloop_le X E N u ω hAne J hJ hlen
      simpa using this
    have := Decay.norm_loopTensor_eG_le (B.L N) hL3 (B.W N) σ hA hℓ0 hδ hC10 hXone hY hLd a
    push_cast at this ⊢
    exact this
  clear_value S1 S2 S3 SB
  -- the coupling sum
  have hcard : ((Finset.Icc 3 (n + 2)).card : ℝ) = (n : ℝ) := by
    rw [Nat.card_Icc]; congr 1
  have hsumcoup :
      ‖∑ lK ∈ Finset.Icc 3 (n + 2),
          Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D (LoopData.idx (σ, a))‖
        ≤ (n : ℝ) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1
            * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
          + 2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ lK ∈ Finset.Icc 3 (n + 2),
            ‖Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D (LoopData.idx (σ, a))‖
          ≤ ∑ _lK ∈ Finset.Icc 3 (n + 2), (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1
              * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
            + 2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1) :=
          Finset.sum_le_sum hcoup
      _ = (n : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  refine le_trans ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add heG hsumcoup)) hquad)) ?_
  -- the `Ξ` bookkeeping
  set fr : ℝ := (B.W N : ℝ) * (B.ell N u * Krad + 1) / A with hfrdef
  set P : ℝ := A⁻¹ ^ (n + 2) with hPdef
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; exact pow_nonneg (inv_nonneg.2 hA0.le) _
  have hη0 : (0 : ℝ) ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη.le
  have hWLd : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hδ
  clear_value fr P
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef : (0 : ℝ) ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 := by positivity
  have hT0 : (0 : ℝ) ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
      + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 := by
    have h1 : (0 : ℝ) ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hcoef hCK) hS10) hnn
    have h2 : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 := by
      have : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) ^ 2 := by positivity
      exact mul_nonneg this hS20
    have h3 : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 := by
      have : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) := by positivity
      exact mul_nonneg (mul_nonneg this hC10) hS30
    linarith
  have hTle := main_term_le (e := exp 1) (mm := (n : ℝ) + 2) (nn := (n : ℝ)) (C1 := C1)
    (exp_nonneg 1) (by linarith) hnn hCK hC10 hS10 hS20 hS30
  have hK2 : (0 : ℝ) ≤ Krad + 2 := by linarith
  have hmain : 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 * fr * P
        + (n : ℝ) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * fr * P)
        + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 * fr * P
      ≤ P * (etaT E u)⁻¹ * ((Krad + 2) * cDrift n CK C1 * (S1 + S2 + S3)) := by
    have e1 : 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 * fr * P
          + (n : ℝ) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * fr * P)
          + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 * fr * P
        = (fr * P) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
            + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3) := by
      ring
    rw [e1, cDrift]
    calc (fr * P) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
            + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3)
        ≤ ((Krad + 2) * (etaT E u)⁻¹ * P) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
            + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfrac hP0) hT0
      _ ≤ ((Krad + 2) * (etaT E u)⁻¹ * P)
            * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) * CK + 1 + C1) * (S1 + S2 + S3)) :=
          mul_le_mul_of_nonneg_left hTle
            (mul_nonneg (mul_nonneg hK2 hη0) hP0)
      _ = P * (etaT E u)⁻¹ * ((Krad + 2)
            * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) * CK + 1 + C1)) * (S1 + S2 + S3)) := by
          ring
  -- the error budget
  have herr : ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * δ * C1
        + (n : ℝ) * (2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1)
        + ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * SB
      ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ
          * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
            + ((n : ℝ) + 2) * C1) := by
    have h1 : 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * S1
        ≤ 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω :=
      mul_le_mul_of_nonneg_left hSxi1 (by positivity)
    have h2 : ((n : ℝ) + 2) ^ 2 * SB ≤ ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω :=
      mul_le_mul_of_nonneg_left hSxiB (by positivity)
    have hsum : ((n : ℝ) + 2) * C1 + 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * S1
          + ((n : ℝ) + 2) ^ 2 * SB
        ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
          + ((n : ℝ) + 2) * C1 := by nlinarith [h1, h2]
    calc ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * δ * C1
          + (n : ℝ) * (2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1)
          + ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * SB
        = (B.W N : ℝ) * (B.L N : ℝ) * δ * (((n : ℝ) + 2) * C1
            + 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * S1 + ((n : ℝ) + 2) ^ 2 * SB) := by ring
      _ ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ
            * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1) := mul_le_mul_of_nonneg_left hsum hWLd
  rw [hxiRhs]
  linarith [add_le_add hmain herr]

set_option maxHeartbeats 1600000 in
/-- **(5.77), pointwise, with `K` bounded only at the lengths used by coupling.** -/
theorem norm_driftF_le' (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    {Krad δ CK C1 : ℝ}
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u) (hell : 1 / 2 ≤ B.ell N u)
    (hKrad : 1 ≤ Krad) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1) :
    ‖DriftDef.driftF B E N u (X.H N u ω) σ a‖
      ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
          * ((Krad + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
        + (B.W N : ℝ) * (B.L N : ℝ) * δ
            * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1) := by
  classical
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hAne : B.scale E N u ≠ 0 := hA0.ne'
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hℓ0 : (0 : ℝ) < B.ell N u * Krad := by nlinarith
  have hsc : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  have hfrac : (B.W N : ℝ) * (B.ell N u * Krad + 1) / B.scale E N u
      ≤ (Krad + 2) * (etaT E u)⁻¹ := by
    rw [hsc, ← div_eq_mul_inv]
    exact Decay.mul_add_one_div_le hW hell hη
  set A := B.scale E N u with hAdef
  rw [DriftDef.driftF_eq_eG_add]
  set D : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u with hD
  set Lf : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) with hLf
  have hxi : ∀ k, 0 ≤ X.xiLK E N u ω k := fun k => X.xiLK_nonneg hA0.le
  set S1 : ℝ := ∑ k ∈ Finset.Ico 1 (n + 2), X.xiLK E N u ω k with hS1def
  set S2 : ℝ := ∑ k ∈ Finset.Icc 2 (n + 2),
    X.xiLK E N u ω k * X.xiLK E N u ω (n + 2 - k + 2) * A⁻¹ with hS2def
  set S3 : ℝ := X.xiL E N u ω (n + 2 + 1) with hS3def
  set SB : ℝ := ∑ k ∈ Finset.Icc 2 (n + 2), X.xiLK E N u ω k with hSBdef
  have hS10 : 0 ≤ S1 := Finset.sum_nonneg fun k _ => hxi k
  have hS20 : 0 ≤ S2 := Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg (hxi _) (hxi _)) (inv_nonneg.2 hA0.le)
  have hS30 : 0 ≤ S3 := X.xiL_nonneg hA0.le
  have hSB0 : 0 ≤ SB := Finset.sum_nonneg fun k _ => hxi k
  have hxiRhs : SumZeroDyn.xiRhs X E (n + 2) N u ω = S1 + S2 + S3 := rfl
  have hSxi1 : S1 ≤ xiSum X E (n + 2) N u ω := by
    rw [hS1def, xiSum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun k _ _ => hxi k)
    rw [Finset.mem_Ico] at hx
    exact Finset.mem_Icc.mpr ⟨hx.1, by omega⟩
  have hSxiB : SB ≤ xiSum X E (n + 2) N u ω := by
    rw [hSBdef, xiSum]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun k _ _ => hxi k)
    rw [Finset.mem_Icc] at hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx.2⟩
  -- the bound on `L - K` at every length
  have hDb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → ∀ {j : ℕ}, J.length = j →
      ‖D J‖ ≤ X.xiLK E N u ω j * A⁻¹ ^ j := fun J hJ {j} hj =>
    norm_lk_le X E N u ω hAne J hJ hj
  -- three term bounds
  have hcoup : ∀ lK ∈ Finset.Icc 3 (n + 2),
      ‖Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D (LoopData.idx (σ, a))‖
        ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1
            * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
          + 2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1 := by
    intro lK hlK
    rw [Finset.mem_Icc] at hlK
    rw [← couplingLen_dTrunc]
    have hDt : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length < n + 2 →
        ‖dTrunc (B.L N) D J‖ ≤ S1 * A⁻¹ ^ J.length := by
      intro J hJ hlen
      refine norm_dTrunc_le (by positivity) fun h2 => ?_
      refine (hDb J hJ rfl).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      exact Finset.single_le_sum (f := fun k => X.xiLK E N u ω k) (fun k _ => hxi k)
        (Finset.mem_Ico.mpr ⟨by omega, hlen⟩)
    have := Decay.norm_loopTensor_couplingLen_le' (B.L N) hL3 (B.W N) hlK.1 σ hA hℓ0 hδ hCK
      hS10 hKb hKd hDt a
    push_cast at this ⊢
    exact this
  have hquad : ‖primBil (B.L N) (B.W N) D D (LoopData.idx (σ, a))‖
      ≤ 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2
          * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
        + ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * SB := by
    have hD2 : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
        ‖D J‖ ≤ X.xiLK E N u ω J.length * A⁻¹ ^ J.length := fun J hJ _ _ => hDb J hJ rfl
    have hX : ∀ k, 2 ≤ k → k ≤ n + 2 →
        X.xiLK E N u ω k * X.xiLK E N u ω (n + 2 - k + 2) * A⁻¹ ≤ S2 := fun k h1 h2 =>
      Finset.single_le_sum
        (f := fun k => X.xiLK E N u ω k * X.xiLK E N u ω (n + 2 - k + 2) * A⁻¹)
        (fun k _ => mul_nonneg (mul_nonneg (hxi _) (hxi _)) (inv_nonneg.2 hA0.le))
        (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have hXB : ∀ k, 2 ≤ k → k ≤ n + 2 → X.xiLK E N u ω k ≤ SB := fun k h1 h2 =>
      Finset.single_le_sum (f := fun k => X.xiLK E N u ω k) (fun k _ => hxi k)
        (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    have := Decay.norm_loopTensor_primBil_le (B.L N) hL3 (B.W N) σ
      (fun k => X.xiLK E N u ω k) hA hℓ0 hδ hS20 hSB0 hD2 hX hXB hDd a
    push_cast at this ⊢
    exact this
  have heG : ‖Decay.eG (B.L N) (B.W N) D Lf (LoopData.idx (σ, a))‖
      ≤ 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3
          * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
        + ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * δ * C1 := by
    have hXone : ∀ (s : Bool) (b : ZMod (B.L N)),
        ‖D ⟨[s], [b]⟩‖ ≤ C1 * A⁻¹ := by
      intro s b
      have hwf : (⟨[s], [b]⟩ : LoopIdx (ZMod (B.L N))).WF := rfl
      have := hDb ⟨[s], [b]⟩ hwf (j := 1) rfl
      rw [pow_one] at this
      exact this.trans (mul_le_mul_of_nonneg_right hC1 (inv_nonneg.2 hA0.le))
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = (n + 2) + 1 →
        ‖Lf J‖ ≤ S3 * A⁻¹ ^ (n + 2) := by
      intro J hJ hlen
      have := norm_gloop_le X E N u ω hAne J hJ hlen
      simpa using this
    have := Decay.norm_loopTensor_eG_le (B.L N) hL3 (B.W N) σ hA hℓ0 hδ hC10 hXone hY hLd a
    push_cast at this ⊢
    exact this
  clear_value S1 S2 S3 SB
  -- the coupling sum
  have hcard : ((Finset.Icc 3 (n + 2)).card : ℝ) = (n : ℝ) := by
    rw [Nat.card_Icc]; congr 1
  have hsumcoup :
      ‖∑ lK ∈ Finset.Icc 3 (n + 2),
          Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D (LoopData.idx (σ, a))‖
        ≤ (n : ℝ) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1
            * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
          + 2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ lK ∈ Finset.Icc 3 (n + 2),
            ‖Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D (LoopData.idx (σ, a))‖
          ≤ ∑ _lK ∈ Finset.Icc 3 (n + 2), (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1
              * ((B.W N : ℝ) * (B.ell N u * Krad + 1) / A) * A⁻¹ ^ (n + 2)
            + 2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1) :=
          Finset.sum_le_sum hcoup
      _ = (n : ℝ) * _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  refine le_trans ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add heG hsumcoup)) hquad)) ?_
  -- the `Ξ` bookkeeping
  set fr : ℝ := (B.W N : ℝ) * (B.ell N u * Krad + 1) / A with hfrdef
  set P : ℝ := A⁻¹ ^ (n + 2) with hPdef
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; exact pow_nonneg (inv_nonneg.2 hA0.le) _
  have hη0 : (0 : ℝ) ≤ (etaT E u)⁻¹ := inv_nonneg.2 hη.le
  have hWLd : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hδ
  clear_value fr P
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef : (0 : ℝ) ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 := by positivity
  have hT0 : (0 : ℝ) ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
      + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 := by
    have h1 : (0 : ℝ) ≤ 4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg hcoef hCK) hS10) hnn
    have h2 : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 := by
      have : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) ^ 2 := by positivity
      exact mul_nonneg this hS20
    have h3 : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 := by
      have : (0 : ℝ) ≤ 2 * exp 1 * ((n : ℝ) + 2) := by positivity
      exact mul_nonneg (mul_nonneg this hC10) hS30
    linarith
  have hTle := main_term_le (e := exp 1) (mm := (n : ℝ) + 2) (nn := (n : ℝ)) (C1 := C1)
    (exp_nonneg 1) (by linarith) hnn hCK hC10 hS10 hS20 hS30
  have hK2 : (0 : ℝ) ≤ Krad + 2 := by linarith
  have hmain : 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 * fr * P
        + (n : ℝ) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * fr * P)
        + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 * fr * P
      ≤ P * (etaT E u)⁻¹ * ((Krad + 2) * cDrift n CK C1 * (S1 + S2 + S3)) := by
    have e1 : 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3 * fr * P
          + (n : ℝ) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * fr * P)
          + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 * fr * P
        = (fr * P) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
            + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3) := by
      ring
    rw [e1, cDrift]
    calc (fr * P) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
            + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3)
        ≤ ((Krad + 2) * (etaT E u)⁻¹ * P) * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * CK * S1 * (n : ℝ)
            + 2 * exp 1 * ((n : ℝ) + 2) ^ 2 * S2 + 2 * exp 1 * ((n : ℝ) + 2) * C1 * S3) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfrac hP0) hT0
      _ ≤ ((Krad + 2) * (etaT E u)⁻¹ * P)
            * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) * CK + 1 + C1) * (S1 + S2 + S3)) :=
          mul_le_mul_of_nonneg_left hTle
            (mul_nonneg (mul_nonneg hK2 hη0) hP0)
      _ = P * (etaT E u)⁻¹ * ((Krad + 2)
            * (4 * exp 1 * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) * CK + 1 + C1)) * (S1 + S2 + S3)) := by
          ring
  -- the error budget
  have herr : ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * δ * C1
        + (n : ℝ) * (2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1)
        + ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * SB
      ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ
          * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
            + ((n : ℝ) + 2) * C1) := by
    have h1 : 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * S1
        ≤ 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω :=
      mul_le_mul_of_nonneg_left hSxi1 (by positivity)
    have h2 : ((n : ℝ) + 2) ^ 2 * SB ≤ ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω :=
      mul_le_mul_of_nonneg_left hSxiB (by positivity)
    have hsum : ((n : ℝ) + 2) * C1 + 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * S1
          + ((n : ℝ) + 2) ^ 2 * SB
        ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
          + ((n : ℝ) + 2) * C1 := by nlinarith [h1, h2]
    calc ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * δ * C1
          + (n : ℝ) * (2 * ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * S1)
          + ((n : ℝ) + 2) ^ 2 * (B.W N : ℝ) * (B.L N : ℝ) * δ * SB
        = (B.W N : ℝ) * (B.L N : ℝ) * δ * (((n : ℝ) + 2) * C1
            + 2 * (n : ℝ) * ((n : ℝ) + 2) ^ 2 * S1 + ((n : ℝ) + 2) ^ 2 * SB) := by ring
      _ ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ
            * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1) := mul_le_mul_of_nonneg_left hsum hWLd
  rw [hxiRhs]
  linarith [add_le_add hmain herr]

end Pointwise

/-! ### The same for `RBM.MomentDuhamel.Hyp.F`, and the `≺` step without `Hierarchy` -/

section Hyp

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
  {n : ℕ}

/-- **(5.77), lines 1-3, for the drift of `RBM.MomentDuhamel.Hyp`, pointwise along the flow.**

The drift is not assumed to be anything: `RBM.DriftDef.Fpath_eq_driftF_of_lt_one` pins it to
`RBM.DriftDef.driftF` out of the field `drift`, and `RBM.DriftBound.norm_driftF_le` bounds
that. -/
theorem norm_Hyp_F_le (H : MomentDuhamel.Hyp X E s t n) {N : ℕ} {u : ℝ} (ω : Ω)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N)
    {Krad δ CK C1 : ℝ}
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u) (hell : 1 / 2 ≤ B.ell N u)
    (hKrad : 1 ≤ Krad) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1) :
    ‖H.F N u (X.H N u ω) σ a‖
      ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
          * ((Krad + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
        + (B.W N : ℝ) * (B.L N : ℝ) * δ
            * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1) := by
  have h := DriftDef.Fpath_eq_driftF_of_lt_one H hE hu0 hu1 hsu hut ω σ a
  rw [show H.F N u (X.H N u ω) σ a = H.Fpath N u ω σ a from rfl, h]
  exact norm_driftF_le X E N u ω σ a hA hη hell hKrad hδ hCK hC10 hKb hKd hDd hLd hC1

/-- The flow-pinned version of `norm_driftF_le'`. -/
theorem norm_Hyp_F_le' (H : MomentDuhamel.Hyp X E s t n) {N : ℕ} {u : ℝ} (ω : Ω)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N)
    {Krad δ CK C1 : ℝ}
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u) (hell : 1 / 2 ≤ B.ell N u)
    (hKrad : 1 ≤ Krad) (hδ : 0 ≤ δ) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * Krad) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1) :
    ‖H.F N u (X.H N u ω) σ a‖
      ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
          * ((Krad + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
        + (B.W N : ℝ) * (B.L N : ℝ) * δ
            * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1) := by
  have h := DriftDef.Fpath_eq_driftF_of_lt_one H hE hu0 hu1 hsu hut ω σ a
  rw [show H.F N u (X.H N u ω) σ a = H.Fpath N u ω σ a from rfl, h]
  exact norm_driftF_le' X E N u ω σ a hA hη hell hKrad hδ hCK hC10 hKb hKd hDd hLd hC1

/-- **`RBM.SumZeroDyn.F_stochDom` without a `Hierarchy`.**

The only use `RBM.SumZeroDyn.F_stochDom` makes of the structures `RBM.SumZeroDyn.Hierarchy`
and `RBM.SumZeroDyn.Lemma510` is the field `F_le`; here that field is an ordinary hypothesis
about an ordinary function `F`.  T118 forbids instantiating `Hierarchy`, so this is the form
in which the replacement of the random control `Ξ` by the deterministic `(2n+3) Φ` is
available to the pinned drift. -/
theorem stochDom_det_of_xiRhs (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} (hE : |E| < 2)
    (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1) {n : ℕ}
    {F : ∀ N, TimeIcc s t N → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hF_le : StochDom B.P (fun N p ω => F N p.1 p.2 ω)
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹
          * SumZeroDyn.xiRhs X E (n + 2) N (p.1 : ℝ) ω))
    {Φ : ℕ → ℝ}
    (hxi : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => SumZeroDyn.xiRhs X E (n + 2) N (u : ℝ) ω)
      (fun N _ _ => (2 * n + 3 : ℝ) * Φ N)) :
    StochDom B.P (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω => F N p.1 p.2 ω)
      (fun N p _ => (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹
        * ((2 * n + 3 : ℝ) * Φ N)) := by
  have hpos : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)), 0 < B.scale E N (p.1 : ℝ) :=
    fun N p => B.scale_pos hE N ((hs0 N).trans_le p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
  have hη : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)), 0 < etaT E (p.1 : ℝ) :=
    fun N p => etaT_pos hE (p.1.2.2.trans_lt (ht1 N))
  have hg : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) (_ : Ω),
      0 ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹ := fun N p _ => by
    have := hpos N p; have := hη N p; positivity
  have hxi0 : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω,
      0 ≤ SumZeroDyn.xiRhs X E (n + 2) N (p.1 : ℝ) ω := fun N p ω => by
    have hA := (hpos N p).le
    unfold SumZeroDyn.xiRhs
    refine add_nonneg (add_nonneg (Finset.sum_nonneg fun k _ => X.xiLK_nonneg hA)
      (Finset.sum_nonneg fun k _ => ?_)) (X.xiL_nonneg hA)
    exact mul_nonneg (mul_nonneg (X.xiLK_nonneg hA) (X.xiLK_nonneg hA)) (inv_nonneg.2 hA)
  have hm := StochDom.mul hxi0 hg (StochDom.refl hg)
    (hxi.precomp_param (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) => p.1))
  exact hF_le.trans hm

/-- **The `hdom` of `RBM.Gauss.hFmom_of_stochDom`, without a `RBM.SumZeroDyn.Hierarchy`.**

Shape-for-shape the conclusion of `RBM.SumZeroDyn.F_stochDom`, with
`g N u = (Wℓ_uη_u)^{-(n+2)} η_u^{-1} ((2n+3) Φ N)`; the drift is
`RBM.MomentDuhamel.Hyp.F` read along the flow, and no field of `RBM.SumZeroDyn.Lemma510`
occurs anywhere in the derivation. -/
theorem hdom_of_stochDom_driftF (H : MomentDuhamel.Hyp X E s t n) (hE : |E| < 2)
    (hs0 : ∀ N, 0 < s N) (ht1 : ∀ N, t N < 1)
    (hF_le : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        ‖DriftDef.driftF B E N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun N p ω => (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹
        * SumZeroDyn.xiRhs X E (n + 2) N (p.1 : ℝ) ω))
    {Φ : ℕ → ℝ}
    (hxi : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => SumZeroDyn.xiRhs X E (n + 2) N (u : ℝ) ω)
      (fun N _ _ => (2 * n + 3 : ℝ) * Φ N)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        ‖H.F N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹
        * ((2 * n + 3 : ℝ) * Φ N)) := by
  have heq : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖H.F N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖
        = ‖DriftDef.driftF B E N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖ := by
    intro N p ω
    rw [show H.F N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2
        = H.Fpath N (p.1 : ℝ) ω p.2.1 p.2.2 from rfl,
      DriftDef.Fpath_eq_driftF_of_lt_one H hE ((hs0 N).le.trans p.1.2.1)
        (p.1.2.2.trans_lt (ht1 N)) p.1.2.1 p.1.2.2 ω p.2.1 p.2.2]
  refine StochDom.of_le_left (fun N p ω => le_of_eq (heq N p ω)) ?_
  exact stochDom_det_of_xiRhs X hE hs0 ht1
    (F := fun N p q ω => ‖DriftDef.driftF B E N (p : ℝ) (X.H N (p : ℝ) ω) q.1 q.2‖) hF_le hxi

end Hyp

/-! ### (5.77), lines 1-3, as a `≺` statement -/

section Stoch

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
  {n : ℕ}

/-- **The inputs of (5.77) at one `N`**: Lemma 5.9's `(Krad, δ)` decay of `K`, of `L - K` and
of `L`, the power counts (5.76) at the budget `Ψ`, and `Ξ^{(L-K)}_{u,1} ≤ C₁`, all uniformly in
`u ∈ [s_N, t_N]`.  Every one of them is a statement about the *sample*, not about a structure
field. -/
def DriftInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n N : ℕ) (Krad δ C1 Ψ : ℝ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N,
      Decay.LoopDecay (B.L N) (n + 2) (B.ell N (u : ℝ) * Krad) δ (B.Kval E N (u : ℝ))
    ∧ Decay.LoopDecay (B.L N) (n + 2) (B.ell N (u : ℝ) * Krad) δ
        (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)) - B.Kval E N (u : ℝ))
    ∧ Decay.LoopDecay (B.L N) (n + 3) (B.ell N (u : ℝ) * Krad) δ
        (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)))
    ∧ SumZeroDyn.xiRhs X E (n + 2) N (u : ℝ) ω ≤ Ψ
    ∧ xiSum X E (n + 2) N (u : ℝ) ω ≤ Ψ
    ∧ X.xiLK E N (u : ℝ) ω 1 ≤ C1}

/-- The constant of the error budget. -/
noncomputable def cErr (n : ℕ) (C1 : ℝ) : ℝ :=
  (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * (2 * (n : ℝ) + 3) + ((n : ℝ) + 2) * C1

set_option maxHeartbeats 1600000 in
/-- **(5.77), lines 1-3, for the pinned drift, as a `≺` statement with a deterministic
control.**  No field of `RBM.SumZeroDyn.Lemma510` and no `RBM.SumZeroDyn.Hierarchy` instance
occurs: the left side is `RBM.DriftDef.driftF`, a definition in the Green function of the
flow. -/
theorem stochDom_norm_driftF (X : Sample B) {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}
    (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t)
    {Φ : ℕ → ℝ} {CK C1 Kpoly Blow : ℝ} (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKpoly : 0 ≤ Kpoly) (hΦ0 : ∀ N, 0 ≤ Φ N)
    (hΦpoly : ∀ᶠ N : ℕ in atTop, Φ N ≤ (N : ℝ) ^ Kpoly)
    (hKb : ∀ (N : ℕ) (u : ℝ) (J : LoopIdx (ZMod (B.L N))), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ p : TimeIcc s t N × LoopData (B.L N) (n + 2),
      (N : ℝ) ^ (-Blow)
        ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹ * ((2 * n + 3 : ℝ) * Φ N))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      DriftInputs X E s t n N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) C1
        ((N : ℝ) ^ τ * ((2 * n + 3 : ℝ) * Φ N)))) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        ‖DriftDef.driftF B E N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹
        * ((2 * n + 3 : ℝ) * Φ N)) := by
  refine StochDom.of_highProb_add_rpow_neg (b := Blow)
    (HighProb.of_eventually_univ ?_) ?_
  · filter_upwards [hlow] with N hN ω
    simpa only [Set.mem_ofPred_eq] using hN
  intro τ hτ D hD
  set τ₁ : ℝ := τ / 4 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set K : ℝ := 2 + τ₁ + Kpoly with hKdef
  set D₁ : ℝ := D + K + 1 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def, hKdef]; linarith
  refine HighProb.mono (hin τ₁ hτ₁ D₁ hD₁) ?_
  filter_upwards [SumZeroDyn.flow_crude hE (fun N => (hs0 N).le) hst ht1 hc, hΦpoly,
    SumZeroDyn.eventually_const_mul_rpow_le (3 * cDrift n CK C1)
      (show 2 * τ₁ < τ by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le (2 * cErr n C1)
      (show -D - 1 < -D by linarith),
    eventually_ge_atTop 1] with N hcr hΦN hmainN herrN hN1
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hKrad1 : (1 : ℝ) ≤ (N : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁.le
  have hδ0 : (0 : ℝ) ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
  intro p
  obtain ⟨hKd, hDd, hLd, hxiR, hxiS, hxi1⟩ := hω p.1
  set u : ℝ := (p.1 : ℝ) with hudef
  have hu0 : 0 ≤ u := ((hs0 N).le).trans p.1.2.1
  have hu1 : u < 1 := p.1.2.2.trans_lt (ht1 N)
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hA : 1 ≤ B.scale E N u := (hu p.1).1
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  have hpt := norm_driftF_le X E N u ω p.2.1 p.2.2 hA hη hell hKrad1 hδ0 hCK hC10
    (fun J hJ => hKb N u J hJ) hKd hDd hLd hxi1
  -- the control
  set ζ : ℝ := (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ * ((2 * n + 3 : ℝ) * Φ N) with hζdef
  have hζ0 : 0 ≤ ζ := by
    rw [hζdef]
    have : (0 : ℝ) ≤ (2 * (n : ℝ) + 3) * Φ N := by
      have := hΦ0 N; positivity
    have h1 : (0 : ℝ) ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ :=
      mul_nonneg (pow_nonneg (inv_nonneg.2 hA0.le) _) (inv_nonneg.2 hη.le)
    exact mul_nonneg h1 this
  -- the main term
  have hmain : (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
        * (((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
      ≤ (N : ℝ) ^ τ * ζ := by
    have hcd0 : (0 : ℝ) ≤ cDrift n CK C1 := by
      rw [cDrift]
      have : (0 : ℝ) ≤ (n : ℝ) * CK + 1 + C1 := by positivity
      positivity
    have hfac0 : (0 : ℝ) ≤ ((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ τ₁ + 2 := by linarith
      exact mul_nonneg this hcd0
    have hpre0 : (0 : ℝ) ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ :=
      mul_nonneg (pow_nonneg (inv_nonneg.2 hA0.le) _) (inv_nonneg.2 hη.le)
    have hstep : ((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω
        ≤ ((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * ((N : ℝ) ^ τ₁ * ((2 * n + 3 : ℝ) * Φ N)) :=
      mul_le_mul_of_nonneg_left hxiR hfac0
    have hcoef : ((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * (N : ℝ) ^ τ₁ ≤ (N : ℝ) ^ τ := by
      have h3 : ((N : ℝ) ^ τ₁ + 2) ≤ 3 * (N : ℝ) ^ τ₁ := by linarith
      have h4 : ((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * (N : ℝ) ^ τ₁
          ≤ 3 * cDrift n CK C1 * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁) := by
        have := Real.rpow_nonneg hN0.le τ₁
        nlinarith [mul_nonneg hcd0 this]
      have h5 : (N : ℝ) ^ τ₁ * (N : ℝ) ^ τ₁ = (N : ℝ) ^ (2 * τ₁) := by
        rw [← Real.rpow_add hN0]; ring_nf
      rw [h5] at h4
      exact h4.trans hmainN
    calc (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
          * (((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹
            * (((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * ((N : ℝ) ^ τ₁ * ((2 * n + 3 : ℝ) * Φ N))) :=
          mul_le_mul_of_nonneg_left hstep hpre0
      _ = (((N : ℝ) ^ τ₁ + 2) * cDrift n CK C1 * (N : ℝ) ^ τ₁) * ζ := by rw [hζdef]; ring
      _ ≤ (N : ℝ) ^ τ * ζ := mul_le_mul_of_nonneg_right hcoef hζ0
  -- the error term
  have herr : (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D₁)
        * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
          + ((n : ℝ) + 2) * C1)
      ≤ (N : ℝ) ^ (-D) := by
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (B.L N : ℝ) := Nat.cast_nonneg _
    have hxiS0 : 0 ≤ xiSum X E (n + 2) N u ω :=
      Finset.sum_nonneg fun k _ => X.xiLK_nonneg hA0.le
    have hΦK : (N : ℝ) ^ τ₁ * ((2 * (n : ℝ) + 3) * Φ N)
        ≤ (2 * (n : ℝ) + 3) * (N : ℝ) ^ (τ₁ + Kpoly) := by
      have h1 : Φ N ≤ (N : ℝ) ^ Kpoly := hΦN
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ τ₁ := Real.rpow_nonneg hN0.le _
      have h3 : (N : ℝ) ^ τ₁ * (N : ℝ) ^ Kpoly = (N : ℝ) ^ (τ₁ + Kpoly) := by
        rw [← Real.rpow_add hN0]
      calc (N : ℝ) ^ τ₁ * ((2 * (n : ℝ) + 3) * Φ N)
          ≤ (N : ℝ) ^ τ₁ * ((2 * (n : ℝ) + 3) * (N : ℝ) ^ Kpoly) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
        _ = (2 * (n : ℝ) + 3) * ((N : ℝ) ^ τ₁ * (N : ℝ) ^ Kpoly) := by ring
        _ = (2 * (n : ℝ) + 3) * (N : ℝ) ^ (τ₁ + Kpoly) := by rw [h3]
    have hxiSle : xiSum X E (n + 2) N u ω ≤ (2 * (n : ℝ) + 3) * (N : ℝ) ^ (τ₁ + Kpoly) := by
      exact hxiS.trans hΦK
    have hbig : (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
          + ((n : ℝ) + 2) * C1
        ≤ 2 * cErr n C1 * (N : ℝ) ^ (τ₁ + Kpoly) := by
      have hr1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ₁ + Kpoly) :=
        Real.one_le_rpow hN1' (by linarith)
      have hc1 : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 := by positivity
      have h1 : (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
          ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * ((2 * (n : ℝ) + 3) * (N : ℝ) ^ (τ₁ + Kpoly)) :=
        mul_le_mul_of_nonneg_left hxiSle hc1
      have h2 : ((n : ℝ) + 2) * C1 ≤ ((n : ℝ) + 2) * C1 * (N : ℝ) ^ (τ₁ + Kpoly) := by
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) + 2) hC10]
      rw [cErr]
      nlinarith [Real.rpow_nonneg hN0.le (τ₁ + Kpoly)]
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
      have : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
      rw [this]
      nlinarith
    have hcE0 : (0 : ℝ) ≤ 2 * cErr n C1 := by
      rw [cErr]; have := hC10; positivity
    calc (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D₁)
          * ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
            + ((n : ℝ) + 2) * C1)
        ≤ (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-D₁) * (2 * cErr n C1 * (N : ℝ) ^ (τ₁ + Kpoly)) := by
          have hp1 : (0 : ℝ) ≤ (N : ℝ) ^ (-D₁) := hδ0
          have hp2 : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω
              + ((n : ℝ) + 2) * C1 := by
            have : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * xiSum X E (n + 2) N u ω := by
              have hc : (0 : ℝ) ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 := by positivity
              exact mul_nonneg hc hxiS0
            have h2 : (0 : ℝ) ≤ ((n : ℝ) + 2) * C1 := by
              exact mul_nonneg (by positivity) hC10
            linarith
          have hq : (0 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-D₁) :=
            mul_nonneg (Real.rpow_nonneg hN0.le _) hp1
          have hstep1 : (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D₁)
              ≤ (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-D₁) :=
            mul_le_mul_of_nonneg_right hWL hp1
          exact mul_le_mul hstep1 hbig hp2 hq
      _ = 2 * cErr n C1 * ((N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-D₁) * (N : ℝ) ^ (τ₁ + Kpoly)) := by
          ring
      _ = 2 * cErr n C1 * (N : ℝ) ^ (-D - 1) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
          congr 2
          rw [hD₁def, hKdef]; ring
      _ ≤ (N : ℝ) ^ (-D) := herrN
  refine hpt.trans ?_
  have := add_le_add hmain herr
  linarith

/-- **The `hdom` of `RBM.Gauss.hFmom_of_stochDom`, delivered.**

The conclusion is *verbatim* that of `RBM.SumZeroDyn.F_stochDom` — with
`g N u = (Wℓ_uη_u)^{-(n+2)} η_u^{-1} ((2n+3) Φ N)` — but no field of
`RBM.SumZeroDyn.Lemma510` and no instance of `RBM.SumZeroDyn.Hierarchy` is used anywhere in
its derivation.  The drift is identified with `RBM.DriftDef.driftF` by
`RBM.DriftDef.Fpath_eq_driftF_of_lt_one` (T58) and then bounded by
`RBM.DriftBound.stochDom_norm_driftF`, i.e. by (5.77) lines 1-3 proved from
`RBM1D/Hierarchy/Decay.lean`. -/
theorem hdom_of_driftInputs (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t)
    {Φ : ℕ → ℝ} {CK C1 Kpoly Blow : ℝ} (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKpoly : 0 ≤ Kpoly) (hΦ0 : ∀ N, 0 ≤ Φ N)
    (hΦpoly : ∀ᶠ N : ℕ in atTop, Φ N ≤ (N : ℝ) ^ Kpoly)
    (hKb : ∀ (N : ℕ) (u : ℝ) (J : LoopIdx (ZMod (B.L N))), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ p : TimeIcc s t N × LoopData (B.L N) (n + 2),
      (N : ℝ) ^ (-Blow)
        ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹ * ((2 * n + 3 : ℝ) * Φ N))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      DriftInputs X E s t n N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) C1
        ((N : ℝ) ^ τ * ((2 * n + 3 : ℝ) * Φ N)))) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        ‖H.F N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖)
      (fun N p _ => (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹
        * ((2 * n + 3 : ℝ) * Φ N)) := by
  have heq : ∀ N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖H.F N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖
        = ‖DriftDef.driftF B E N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2‖ := by
    intro N p ω
    rw [show H.F N (p.1 : ℝ) (X.H N (p.1 : ℝ) ω) p.2.1 p.2.2
        = H.Fpath N (p.1 : ℝ) ω p.2.1 p.2.2 from rfl,
      DriftDef.Fpath_eq_driftF_of_lt_one H hE ((hs0 N).le.trans p.1.2.1)
        (p.1.2.2.trans_lt (ht1 N)) p.1.2.1 p.1.2.2 ω p.2.1 p.2.2]
  exact StochDom.of_le_left (fun N p ω => le_of_eq (heq N p ω))
    (stochDom_norm_driftF X hE hs0 hst ht1 hc hCK hC10 hKpoly hΦ0 hΦpoly hKb hlow hin)

end Stoch


/-! ### `hFmom` of `RBM.Gauss.hrhs_of_moment_inputs`, with the `Lemma510` field removed -/

section Hfmom

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}
  {n : ℕ}

/-- **The drift input of `RBM.Gauss.hrhs_of_moment_inputs`, with no `RBM.SumZeroDyn.Hierarchy`
and no field of `RBM.SumZeroDyn.Lemma510` anywhere in the chain.**

T157 discharged `hFmom` from the `hdom` of `RBM.Gauss.hFmom_of_stochDom`, and produced that
`hdom` from `RBM.SumZeroDyn.F_stochDom`, i.e. from the *assumed* (5.77).  Here the same `hdom`
is `RBM.DriftBound.hdom_of_driftInputs`: `RBM.MomentDuhamel.Hyp.F` is pinned to
`RBM.DriftDef.driftF` and then bounded by (5.77) lines 1-3, proved.  The only inputs left are
Lemma 5.9's decay and the power counts (5.76) — `RBM.DriftBound.DriftInputs` — together with
the side conditions of T77's reverse bridge. -/
theorem hFmom_of_driftInputs [IsFiniteMeasure (B.P)] (H : MomentDuhamel.Hyp X E s t n)
    (v : ℕ → ℝ) (hvt : ∀ N, v N ≤ t N)
    {Φ : ℕ → ℝ} {Env : ℕ → ℝ} {Kenv Blow' : ℝ}
    (hmeas : ∀ (N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
      Measurable fun ω => ‖H.F N u (X.H N u ω) σ b‖)
    (hintF : ∀ (r N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)),
      Integrable (fun ω => ‖H.F N u (X.H N u ω) σ b‖ ^ r) B.P)
    (hg : ∀ N (u : ℝ), s N ≤ u → u ≤ v N →
      0 < (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ * ((2 * n + 3 : ℝ) * Φ N))
    (hB : 0 ≤ Blow')
    (hglow : ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, s N ≤ u → u ≤ v N → (N : ℝ) ^ (-Blow')
      ≤ (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ * ((2 * n + 3 : ℝ) * Φ N))
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (henv : ∀ (N : ℕ) (u : ℝ) (σ : Fin (n + 2) → Bool) (b : LoopArg (B.L N) (n + 2)) (ω : Ω),
      ‖H.F N u (X.H N u ω) σ b‖ ≤ Env N)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hgle : ∀ N (u : ℝ), s N ≤ u → u ≤ v N →
      (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ * ((2 * n + 3 : ℝ) * Φ N) ≤ Φ N)
    (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t)
    {CK C1 Kpoly Blow : ℝ} (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (hKpoly : 0 ≤ Kpoly) (hΦ0 : ∀ N, 0 ≤ Φ N)
    (hΦpoly : ∀ᶠ N : ℕ in atTop, Φ N ≤ (N : ℝ) ^ Kpoly)
    (hKb : ∀ (N : ℕ) (u : ℝ) (J : LoopIdx (ZMod (B.L N))), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ p : TimeIcc s t N × LoopData (B.L N) (n + 2),
      (N : ℝ) ^ (-Blow)
        ≤ (B.scale E N (p.1 : ℝ))⁻¹ ^ (n + 2) * (etaT E (p.1 : ℝ))⁻¹ * ((2 * n + 3 : ℝ) * Φ N))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      DriftInputs X E s t n N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) C1
        ((N : ℝ) ^ τ * ((2 * n + 3 : ℝ) * Φ N)))) :
    ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ (q : LoopData (B.L N) (n + 2))
        (b : LoopArg (B.L N) (n + 2)),
        MomentDuhamel.momNorm B.P (2 * p) (fun ω => ‖H.F N u (X.H N u ω) q.1 b‖)
          ≤ C * ((N : ℝ) ^ (ε / 2) * Φ N) :=
  Gauss.hFmom_of_stochDom H v hvt
    (g := fun N u => (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ * ((2 * n + 3 : ℝ) * Φ N))
    hmeas hintF hg hB hglow hEnv0 hKenv henv hEnvpoly hgle
    (hdom_of_driftInputs H hE hs0 hst ht1 hc hCK hC10 hKpoly hΦ0 hΦpoly hKb hlow hin)

end Hfmom

end DriftBound
end RBM
