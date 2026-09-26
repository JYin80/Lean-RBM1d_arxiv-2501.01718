/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridDriftAlgebra
import RBM1D.Gauss.Lemma514Holder

/-!
# T1523 — the grid hierarchy step for general loop length `n`

Generalizes T1506's `RBM1D/Gauss/GridDriftAlgebra.lean` (the `n = 2` template) from the
`σ = (+,-)` `2`-loop to an arbitrary loop index `I` of length `n ≥ 2`, any charge sequence `σ`
(alternating or not).  Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of
One-Dimensional Random Band Matrices*, (2.45)-(2.48), (5.13)-(5.15), Definition 5.2, (2.57).

## Main results

* `RBM.Gauss.Grid.primRhs_split` (T1) : for any `K, D : LoopIdx (ZMod L) → ℂ` and `I` of length
  `n ≥ 2`, `primRhs(K + D) I - primRhs(K) I` splits into the `l_K = 2` coupling, the
  `l_K ≥ 3` couplings, and the quadratic gluing term `primBil D D I` — (5.12)-(5.15) at every
  loop length, purely algebraic.
* `RBM.Gauss.Grid.couplingLen_two_Kval_eq_thetaOp` : the `l_K = 2` coupling of `Kval_u` against
  any `D`, at any loop length `n ≥ 2` and any charge list, is literally `ThetaOp` — the general-`n`
  form of T1506's `couplingLen_two_eq_thetaGenLoop` use, bridged to the `LoopArg`/tensor picture.
* `RBM.Gauss.Grid.loopDrift_sub_K_deriv_n` : combines the two above with `loopDrift_eq` into the
  general-`n` analogue of T1506's (T1) `loopDrift_sub_K_deriv`.
* `RBM.Gauss.Grid.K_step_n` (T2) : the general-`n` analogue of T1506's `K_step`, via
  `hasDerivAt_Kgen_all` and (a new) `norm_primBil_le` plus the mean value theorem, given an
  envelope hypothesis on `Kval` in the shape already used by `norm_Kgen_sub_le`/`norm_primRhs_le`
  (non-vacuous: `exists_norm_Kval_le_upto`).
* `RBM.Gauss.Grid.Uker_step_n` (T2) : the general-`n` analogue of T1506's `Uker_step`, by
  induction on `n` (peeling one coordinate via `Fin.cons`), reducing at `n = 2` to exactly
  T1506's bound `3(1-(u+Δ))⁻²Δ²M`.
* `RBM.Gauss.Grid.discrete_hierarchy_step_n` (T3) : the general-`n` analogue of T1506's (T4)
  `discrete_hierarchy_step`, via `condExp_loop_drift` (already general in `I`) and the three
  results above.

See `docs/reports/T1523-prove.md` for the math preflight (written before this file) and the
open engineering-risk note on `Uker_step_n`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Matrix Finset
open scoped Matrix.Norms.Operator

/-! ### (T1) : the general-length drift-algebra split, (5.12)-(5.15) -/

section T1

variable {L : ℕ} [NeZero L]

/-- Both graded couplings vanish outside `2 ≤ lK ≤ I.length`: every cut sub-loop of `I` has
length in that range (`RBM.LoopIdx.two_le_length_cutGlueL/R`, `length_cutGlueL/R_le`). -/
theorem couplingLen_eq_zero_outside (W : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    {lK : ℕ} (hlK : lK < 2 ∨ I.length < lK) :
    Decay.couplingLen L W lK K D I = 0 := by
  have hzeroL : primBilLen L W lK K D I = 0 := by
    unfold primBilLen
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hcontra
    rcases hlK with h | h
    · have := LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2
      omega
    · have := LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2
      omega
  have hzeroR : Decay.primBilLenR L W lK D K I = 0 := by
    unfold Decay.primBilLenR
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    intro hcontra
    rcases hlK with h | h
    · have := LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2
      omega
    · have := LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2
      omega
  rw [Decay.couplingLen, hzeroL, hzeroR, add_zero]

/-- **(T1)**: for any `K, D : LoopIdx (ZMod L) → ℂ` and any loop index `I` of length `n ≥ 2`,
`primRhs(K + D) I - primRhs(K) I` splits into the `l_K = 2` coupling `[K ∼ D]²`, the `l_K ≥ 3`
couplings `Σ [K ∼ D]^{l_K}`, and the quadratic gluing term `primBil D D I` of (5.13). This is
(5.12)-(5.15) at every loop length: pure algebra on `primRhs`, `primBil`, `couplingLen`, no
stochastic content and no hypothesis beyond `2 ≤ I.length` (needed only so `l_K = 2` is a
meaningful grade to split off). -/
theorem primRhs_split (W : ℕ) (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    (hn : 2 ≤ I.length) :
    primRhs L W (K + D) I - primRhs L W K I
      = Decay.couplingLen L W 2 K D I
        + (∑ lK ∈ Finset.Icc 3 I.length, Decay.couplingLen L W lK K D I)
        + primBil L W D D I := by
  have hDeq : (K + D) - K = D := by funext x; simp
  have hps := primRhs_sub L W (K + D) K I
  rw [hDeq] at hps
  have hN : I.length + 2 ≤ I.length + 2 := le_rfl
  have hsum := Decay.sum_couplingLen L W K D I hN
  have h2mem : (2 : ℕ) ∈ Finset.range (I.length + 2) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h2mem] at hsum
  have hsub : Finset.Icc 3 I.length ⊆ (Finset.range (I.length + 2)).erase 2 := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_erase, Finset.mem_range]
    omega
  have hsum2 : ∑ lK ∈ (Finset.range (I.length + 2)).erase 2, Decay.couplingLen L W lK K D I
      = ∑ lK ∈ Finset.Icc 3 I.length, Decay.couplingLen L W lK K D I := by
    symm
    refine Finset.sum_subset hsub (fun x hx hnx => ?_)
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hnx
    push_neg at hnx
    exact couplingLen_eq_zero_outside W K D I (by omega)
  rw [hsum2] at hsum
  rw [hps, ← hsum]

end T1

/-! ### (T1, continued) : `[Kval_u ∼ D]² = ThetaOp`, general `n`, general charge -/

section T1Theta

/-- `(List.ofFn σ).getD i true * (List.ofFn σ).getD ((i+1) % n) true`, the coefficient
`thetaGenLoop_ofFn` produces, is literally `xiOf` at every `i : Fin n`. -/
theorem xiOf_eq_getD_bridge {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) (m : Bool → ℂ)
    (σ : Fin n → Bool) (i : Fin n) :
    m ((List.ofFn σ).getD (i : ℕ) true) * m ((List.ofFn σ).getD (((i : ℕ) + 1) % n) true)
      = xiOf m σ i := by
  have h1 : (List.ofFn σ).getD (i : ℕ) true
      = σ i := by
    rw [List.getD_eq_getElem (List.ofFn σ) true (by rw [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]
  have hmod : ((i : ℕ) + 1) % n < n := Nat.mod_lt _ (by omega)
  have h2 : (List.ofFn σ).getD (((i : ℕ) + 1) % n) true = σ (i + 1) := by
    rw [List.getD_eq_getElem (List.ofFn σ) true (by rw [List.length_ofFn]; exact hmod),
      List.getElem_ofFn]
    congr 1
    rw [Fin.ext_iff, Fin.val_add, Fin.val_one' n, Nat.mod_eq_of_lt (show 1 < n by omega)]
  rw [h1, h2]
  rfl

/-- **The `l_K = 2` coupling of `Kval_u` against any `D`, at every loop length `n ≥ 2` and every
charge list, is literally `ThetaOp`.**  The general-`n` form of (5.19) / Definition 5.2 /
(2.57): generalizes T1506's use of `couplingLen_two_eq_thetaGenLoop` (there specialized to
`n = 2`) to a literal identity at every `n`.  **Failure-signal check** (per the ticket): the
identification uses only the *wrap-around* edge `xiLoop m I (I.length - 1)` (Example 2.16's
cyclic convention, `m_n m_1`), so it holds for alternating and non-alternating `σ` alike; no
discrepancy for `n ≥ 3`. -/
theorem couplingLen_two_Kval_eq_thetaOp {Ω : Type*} [MeasurableSpace Ω] (B : Band Ω) (E : ℝ)
    (N : ℕ) (u : ℝ) (D : LoopIdx (ZMod (B.L N)) → ℂ) {n : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (σ : Fin n → Bool) (a : LoopArg (B.L N) n)
    (hξ : ‖(u : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) (n - 1)‖ < 1) :
    Decay.couplingLen (B.L N) (B.W N) 2 (B.Kval E N u) D
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      = ThetaOp (B.L N) (xiOf (mSigma E) σ) (u : ℂ)
          (fun v => D ⟨List.ofFn σ, List.ofFn v⟩) a := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  set I : LoopIdx (ZMod (B.L N)) := ⟨List.ofFn σ, List.ofFn a⟩ with hI
  have hwf : I.WF := by
    show I.σ.length = I.a.length
    rw [hI]
    simp
  have hlen : I.length = n := by
    show I.a.length = n
    rw [hI]
    simp
  have hK : ∀ σ₁ σ₂ (a₁ a₂ : ZMod (B.L N)),
      B.Kval E N u ⟨[σ₁, σ₂], [a₁, a₂]⟩
        = kTwo (B.L N) (B.W N) (mSigma E) u σ₁ σ₂ a₁ a₂ := by
    intro σ₁ σ₂ a₁ a₂; rw [Band.Kval, Kgen_two]
  have hcoup := couplingLen_two_eq_thetaGenLoop (L := B.L N) (B.W N) (mSigma E) u
    (B.Kval E N u) D hL3 hK I hwf (by rw [hlen]; exact hn2) (by rw [hI, hlen]; exact hξ)
  rw [hI] at hcoup
  rw [hcoup]
  have hbridge := thetaGenLoop_ofFn (mSigma E) u D (List.ofFn σ) a
  rw [thetaGenOp_eq_ThetaOp] at hbridge
  have hxiEq : (fun i : Fin n => mSigma E ((List.ofFn σ).getD (i : ℕ) true)
        * mSigma E ((List.ofFn σ).getD (((i : ℕ) + 1) % n) true))
      = xiOf (mSigma E) σ := by
    funext i; exact xiOf_eq_getD_bridge hn2 (mSigma E) σ i
  rw [hxiEq] at hbridge
  exact hbridge

end T1Theta

/-! ### (T1, assembled) : the general-`n` drift-minus-`K` identity -/

section T1Drift

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `L_u(M)` at a general loop of length `n` and charge `σ` (T1506's `Lval`, generalized). -/
noncomputable def LvalN (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ} (σ : Fin n → Bool) (v : LoopArg (B.L N) n) : ℂ :=
  gloop (B.L N) (B.W N) M (zt E u) ⟨List.ofFn σ, List.ofFn v⟩

/-- `K_u` at a general loop of length `n` and charge `σ` (T1506's `Kv`, generalized). -/
noncomputable def KvN (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (v : LoopArg (B.L N) n) : ℂ :=
  B.Kval E N u ⟨List.ofFn σ, List.ofFn v⟩

/-- **The general-`n` analogue of T1506's (T1) `loopDrift_sub_K_deriv`**: for a Hermitian `M`
and any loop index of length `n ≥ 2`, `loopDrift(M) − primRhs(K_u)` splits into the
`ThetaOp`-part (5.19), the `l_K ≥ 3` couplings (5.14), the quadratic gluing part (5.13), and
`E^{(G̃)}` (2.47) — exactly (T1)'s displayed identity, now for every loop length. -/
theorem loopDrift_sub_K_deriv_n (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) (σ : Fin n → Bool) (a : LoopArg (B.L N) n)
    (hξ : ‖(u : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) (n - 1)‖ < 1) :
    loopDrift (d := B.toDims) (N := N) E u ⟨List.ofFn σ, List.ofFn a⟩ M
        - primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨List.ofFn σ, List.ofFn a⟩
      = ThetaOp (B.L N) (xiOf (mSigma E) σ) (u : ℂ)
            (fun v => LvalN B E N u M σ v - KvN B E N u σ v) a
          + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))))
          + eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨List.ofFn σ, List.ofFn a⟩
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              ⟨List.ofFn σ, List.ofFn a⟩ := by
  have hn2' : 2 ≤ (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))).length := by
    show 2 ≤ (List.ofFn a).length
    rw [List.length_ofFn]
    exact hn2
  have hsplit := primRhs_split (B.W N) (B.Kval E N u)
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
    (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) hn2'
  have hKD : B.Kval E N u + (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
      = gloop (B.L N) (B.W N) M (zt E u) := by funext x; simp
  rw [hKD] at hsplit
  have hθ := couplingLen_two_Kval_eq_thetaOp B E N u
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) hn2 σ a hξ
  rw [hθ] at hsplit
  have hlenEq : (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))).length = n := by
    show (List.ofFn a).length = n
    rw [List.length_ofFn]
  rw [hlenEq] at hsplit
  have hFunEq : (fun v => LvalN B E N u M σ v - KvN B E N u σ v)
      = (fun v : LoopArg (B.L N) n =>
          (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨List.ofFn σ, List.ofFn v⟩) := rfl
  rw [hFunEq]
  show eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨List.ofFn σ, List.ofFn a⟩
        + primRhs (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u)) ⟨List.ofFn σ, List.ofFn a⟩
      - primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨List.ofFn σ, List.ofFn a⟩
      = _
  linear_combination hsplit

end T1Drift

/-! ### (T2a) : `K_step_n`, the general-length exact quadratic remainder of `K`'s own step -/

section T2a

/-- **The two-envelope generalization of `RBM.norm_primRhs_le`**: `primBil F G I` is bounded by
the product of separate envelopes `BF, BG` on `F, G` at the cut sub-loop lengths `2 … I.length`,
exactly as `norm_primRhs_le` bounds `primRhs K I` using one envelope for `K` against itself
(`primBil K K = primRhs K`, `RBM.primBil_self`). Immediate generalization of the same proof. -/
theorem norm_primBil_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) (F G : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hI : I.WF) {BF BG : ℝ} (hBF0 : 0 ≤ BF) (hBG0 : 0 ≤ BG)
    (hBF : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖F J‖ ≤ BF)
    (hBG : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length → ‖G J‖ ≤ BG) :
    ‖primBil L W F G I‖ ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * BF * BG := by
  have hL0 : (0 : ℝ) < L := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hpair : ∀ k ∈ Icc 1 I.length, ∀ l ∈ Ioc k I.length,
      ‖∑ a : ZMod L, ∑ b : ZMod L,
          F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ ≤ (L : ℝ) * BF * BG := by
    intro k hk l hl
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hBFl : ∀ a : ZMod L, ‖F (I.cutGlueL k l a)‖ ≤ BF := fun a =>
      hBF _ (LoopIdx.WF.cutGlueL a hI hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2)
    have hBGr : ∀ b : ZMod L, ‖G (I.cutGlueR k l b)‖ ≤ BG := fun b =>
      hBG _ (LoopIdx.WF.cutGlueR b hI hk.1 hl.1 hl.2)
        (LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2)
        (LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2)
    calc ‖∑ a : ZMod L, ∑ b : ZMod L,
            F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖
        ≤ ∑ a : ZMod L, ∑ b : ZMod L,
            ‖F (I.cutGlueL k l a) * SB L a b * G (I.cutGlueR k l b)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
      _ ≤ ∑ a : ZMod L, ∑ b : ZMod L, BF * BG * ‖SB L a b‖ := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul, norm_mul]
          calc ‖F (I.cutGlueL k l a)‖ * ‖SB L a b‖ * ‖G (I.cutGlueR k l b)‖
              ≤ BF * ‖SB L a b‖ * BG :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hBFl a) (norm_nonneg _)) (hBGr b)
                  (norm_nonneg _) (by positivity)
            _ = BF * BG * ‖SB L a b‖ := by ring
      _ = ∑ _a : ZMod L, BF * BG := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.mul_sum, sum_norm_SB_row hL a, mul_one]
      _ = (L : ℝ) * BF * BG := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          ring
  calc ‖primBil L W F G I‖
      ≤ (W : ℝ) * ∑ _k ∈ Icc 1 I.length, ∑ _l ∈ Ioc _k I.length, (L : ℝ) * BF * BG := by
        rw [primBil, norm_mul, Complex.norm_natCast]
        refine mul_le_mul_of_nonneg_left ?_ hW0
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l hl => hpair k hk l hl)
    _ ≤ (W : ℝ) * ∑ _k ∈ Icc 1 I.length, (I.length : ℝ) * ((L : ℝ) * BF * BG) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hW0
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
        have hle : ((I.length - k : ℕ) : ℝ) ≤ (I.length : ℝ) := by
          exact_mod_cast Nat.sub_le I.length k
        exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * BF * BG := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        push_cast
        ring

end T2a

/-! ### (T2) : `K_step_n`, the general-length exact quadratic remainder -/

section T2K

/-- **(T2)**: the general-`n` analogue of T1506's `K_step`. `hasDerivAt_Kgen_all` gives the
derivative of `Kgen` at *every* point of the window, not just at `u`; the mean value theorem
applied to `r ↦ Kgen r I − r • primRhs(Kgen u) I` (whose derivative at `r` is
`primRhs(Kgen r) I − primRhs(Kgen u) I`) turns the (already Lipschitz, `norm_Kgen_sub_le`)
modulus of continuity of that derivative into the stated quadratic remainder. The envelope `Bk`
is in the same shape as `norm_Kgen_sub_le`/`norm_primRhs_le`'s own hypothesis (non-vacuous:
`exists_norm_Kval_le_upto`). -/
theorem K_step_n {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ)
    (hm1 : ∀ s, ‖m s‖ ≤ 1) (I : LoopIdx (ZMod L)) (hI : I.WF) (hn2 : 2 ≤ I.length)
    {T : ℝ} (hT : T < 1) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) T, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      J.length ≤ I.length → ‖Kgen L W m w J‖ ≤ Bk)
    {u u' : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) (hu' : u' ∈ Set.Icc (0 : ℝ) T) (huu' : u ≤ u') :
    ‖Kgen L W m u' I - Kgen L W m u I
        - ((u' - u : ℝ) : ℂ) * primRhs L W (Kgen L W m u) I‖
      ≤ (2 * (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk
            * ((W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2)
          + (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ)
              * ((W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2) ^ 2)
        * (u' - u) ^ 2 := by
  set D1 : ℝ := (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2 with hD1
  have hD1_0 : 0 ≤ D1 := by rw [hD1]; positivity
  have hΔ0 : 0 ≤ u' - u := by linarith
  have hΔ1 : u' - u ≤ 1 := by
    have := hu.1; have := hu'.2; linarith
  have hmw : ∀ w ∈ Set.Icc (0 : ℝ) T, ∀ s s' : Bool, ‖(w : ℂ) * (m s * m s')‖ < 1 := fun w hw s s' =>
    lt_of_le_of_lt (norm_mul_le_of_mem_Icc m hm1 hw s s') hT
  -- the Lipschitz bound on `Kgen`, at every sub-loop `J` of length up to `I.length`, common
  -- constant `D1` (using `I.length` conservatively for every `J.length ≤ I.length`).
  have hLipJ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      J.length ≤ I.length → ‖Kgen L W m r J - Kgen L W m u J‖ ≤ D1 * |r - u| := by
    intro r hr J hJwf hJ2 hJle
    have hbound := norm_Kgen_sub_le hL W hm1 hT J hJwf hJ2 hBk0
      (fun w hw K hKwf hK2 hKle => hBk w hw K hKwf hK2 (hKle.trans hJle)) hr hu
    refine hbound.trans ?_
    have hle2 : ((J.length : ℝ)) ^ 2 ≤ ((I.length : ℝ)) ^ 2 := by
      have : (J.length : ℝ) ≤ (I.length : ℝ) := by exact_mod_cast hJle
      gcongr
    have hWL0 : (0 : ℝ) ≤ (W : ℝ) * (L : ℝ) := by positivity
    have hBk2 : (0 : ℝ) ≤ Bk ^ 2 := by positivity
    calc (W : ℝ) * (J.length : ℝ) ^ 2 * (L : ℝ) * Bk ^ 2 * |r - u|
        = (W : ℝ) * (L : ℝ) * ((J.length : ℝ) ^ 2 * Bk ^ 2) * |r - u| := by ring
      _ ≤ (W : ℝ) * (L : ℝ) * ((I.length : ℝ) ^ 2 * Bk ^ 2) * |r - u| := by gcongr
      _ = D1 * |r - u| := by rw [hD1]; ring
  -- for `r ∈ [u,u']`, the envelope on `Kgen r J - Kgen u J` uniform in `r`, using
  -- `|r-u| ≤ u'-u`.
  have hDenv : ∀ r ∈ Set.Icc u u', ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      J.length ≤ I.length → ‖Kgen L W m r J - Kgen L W m u J‖ ≤ D1 * (u' - u) := by
    intro r hr J hJwf hJ2 hJle
    have hr0T : r ∈ Set.Icc (0 : ℝ) T := ⟨hu.1.trans hr.1, hr.2.trans hu'.2⟩
    refine (hLipJ r hr0T J hJwf hJ2 hJle).trans ?_
    have : |r - u| ≤ u' - u := by
      rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2]
    exact mul_le_mul_of_nonneg_left this hD1_0
  -- the envelope for `Kgen u` itself, at every sub-loop length, from `hBk`.
  have hKuEnv : ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖Kgen L W m u J‖ ≤ Bk := fun J hJwf hJ2 hJle => hBk u hu J hJwf hJ2 hJle
  -- the derivative-difference bound, uniform for `r ∈ [u,u']`.
  have hPrimLip : ∀ r ∈ Set.Icc u u',
      ‖primRhs L W (Kgen L W m r) I - primRhs L W (Kgen L W m u) I‖
        ≤ 2 * (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk * D1 * (u' - u)
          + (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * (D1 * (u' - u)) ^ 2 := by
    intro r hr
    have hr0T : r ∈ Set.Icc (0 : ℝ) T := ⟨hu.1.trans hr.1, hr.2.trans hu'.2⟩
    have hDenvr := hDenv r hr
    have hps := primRhs_sub L W (Kgen L W m r) (Kgen L W m u) I
    have hD1u_0 : 0 ≤ D1 * (u' - u) := mul_nonneg hD1_0 (by linarith [hr.1, hu.1])
    have hb1 := norm_primBil_le hL W (Kgen L W m u) (Kgen L W m r - Kgen L W m u) I hI hBk0 hD1u_0
      hKuEnv (fun J hJwf hJ2 hJle => by rw [Pi.sub_apply]; exact hDenvr J hJwf hJ2 hJle)
    have hb2 := norm_primBil_le hL W (Kgen L W m r - Kgen L W m u) (Kgen L W m u) I hI hD1u_0 hBk0
      (fun J hJwf hJ2 hJle => by rw [Pi.sub_apply]; exact hDenvr J hJwf hJ2 hJle) hKuEnv
    have hb3 := norm_primBil_le hL W (Kgen L W m r - Kgen L W m u) (Kgen L W m r - Kgen L W m u) I
      hI hD1u_0 hD1u_0 (fun J hJwf hJ2 hJle => by rw [Pi.sub_apply]; exact hDenvr J hJwf hJ2 hJle)
      (fun J hJwf hJ2 hJle => by rw [Pi.sub_apply]; exact hDenvr J hJwf hJ2 hJle)
    calc ‖primRhs L W (Kgen L W m r) I - primRhs L W (Kgen L W m u) I‖
        = ‖primBil L W (Kgen L W m u) (Kgen L W m r - Kgen L W m u) I
            + primBil L W (Kgen L W m r - Kgen L W m u) (Kgen L W m u) I
            + primBil L W (Kgen L W m r - Kgen L W m u) (Kgen L W m r - Kgen L W m u) I‖ := by
          rw [hps]
      _ ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk * (D1 * (u' - u))
          + (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * (D1 * (u' - u)) * Bk
          + (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * (D1 * (u' - u)) * (D1 * (u' - u)) := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans (add_le_add hb1 hb2)) hb3
      _ = 2 * (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk * D1 * (u' - u)
          + (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * (D1 * (u' - u)) ^ 2 := by ring
  -- the mean value theorem
  set C : ℂ := primRhs L W (Kgen L W m u) I with hCdef
  set g : ℝ → ℂ := fun r => Kgen L W m r I - r • C with hgdef
  have hderiv : ∀ r ∈ Set.Icc u u', HasDerivWithinAt g
      (primRhs L W (Kgen L W m r) I - C) (Set.Icc u u') r := by
    intro r hr
    have hr0T : r ∈ Set.Icc (0 : ℝ) T := ⟨hu.1.trans hr.1, hr.2.trans hu'.2⟩
    have h1 : HasDerivAt (fun r : ℝ => Kgen L W m r I) (primRhs L W (Kgen L W m r) I) r :=
      hasDerivAt_Kgen_all W m hL (fun s s' => hmw r hr0T s s') I hI hn2
    have h2 : HasDerivAt (fun r : ℝ => r • C) ((1 : ℝ) • C) r :=
      (hasDerivAt_id r).smul_const C
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ r ∈ Set.Icc u u',
      ‖primRhs L W (Kgen L W m r) I - C‖
        ≤ 2 * (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * Bk * D1 * (u' - u)
          + (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * (D1 * (u' - u)) ^ 2 := by
    intro r hr
    rw [hCdef]
    exact hPrimLip r hr
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) hderiv hbound
    (convex_Icc u u') (Set.left_mem_Icc.mpr huu') (Set.right_mem_Icc.mpr huu')
  have hgu : g u = Kgen L W m u I - u • C := rfl
  have hgu' : g u' = Kgen L W m u' I - u' • C := rfl
  rw [hgu', hgu] at hmvt
  have hsmuleq : u' • C - u • C = ((u' - u : ℝ) : ℂ) * C := by
    rw [← sub_smul, Complex.real_smul]
  have hnormeq : ‖Kgen L W m u' I - u' • C - (Kgen L W m u I - u • C)‖
      = ‖Kgen L W m u' I - Kgen L W m u I - ((u' - u : ℝ) : ℂ) * C‖ := by
    congr 1
    rw [← hsmuleq]
    ring
  rw [hnormeq] at hmvt
  have hnormyx : ‖u' - u‖ = u' - u := by rw [Real.norm_eq_abs, abs_of_nonneg hΔ0]
  rw [hnormyx] at hmvt
  refine hmvt.trans ?_
  have hcube : (u' - u) ^ 3 ≤ (u' - u) ^ 2 := by
    nlinarith [pow_nonneg hΔ0 2, hΔ1]
  have hD1sq0 : (0 : ℝ) ≤ (W : ℝ) * (I.length : ℝ) ^ 2 * (L : ℝ) * D1 ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcube hD1sq0]

end T2K

/-! ### (T2) : `Uker_step_n`, general length, by induction on `n` (`Fin.cons` peeling) -/

section T2U

/-- Splitting a sum over `LoopArg L (n+1)` into the front coordinate and the rest, via
`Fin.consEquiv`. -/
theorem sum_loopArg_succ {L : ℕ} [NeZero L] {n : ℕ} {β : Type*} [AddCommMonoid β]
    (g : LoopArg L (n + 1) → β) :
    ∑ v : LoopArg L (n + 1), g v = ∑ p : ZMod L, ∑ w : LoopArg L n, g (Fin.cons p w) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => ZMod L)) g,
    Fintype.sum_prod_type]
  rfl

/-- `Uker` at `n+1`, splitting off the front coordinate: the front edge is applied once, and
the rest is a full `Uker` at `n`. -/
theorem Uker_cons_eq {L : ℕ} [NeZero L] {n : ℕ} (ξ0 : ℂ) (ξ' : Fin n → ℂ) (s t : ℂ)
    (A : LoopArg L (n + 1) → ℂ) (a0 : ZMod L) (a' : LoopArg L n) :
    Uker L (Fin.cons ξ0 ξ') s t A (Fin.cons a0 a')
      = ∑ c : ZMod L, edgeKer L ξ0 s t a0 c
          * Uker L ξ' s t (fun w => A (Fin.cons c w)) a' := by
  rw [Uker_apply, sum_loopArg_succ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Uker_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- `ThetaOp` at `n+1`, splitting off the front coordinate. -/
theorem ThetaOp_cons_eq {L : ℕ} [NeZero L] {n : ℕ} (ξ0 : ℂ) (ξ' : Fin n → ℂ) (t : ℂ)
    (A : LoopArg L (n + 1) → ℂ) (a0 : ZMod L) (a' : LoopArg L n) :
    ThetaOp L (Fin.cons ξ0 ξ') t A (Fin.cons a0 a')
      = (∑ c : ZMod L, ξ0 * (Theta L (t * ξ0) * SB L) a0 c * A (Fin.cons c a'))
        + ThetaOp L ξ' t (fun w => A (Fin.cons a0 w)) a' := by
  show (∑ i : Fin (n + 1), ∑ c : ZMod L,
      (Fin.cons ξ0 ξ' : Fin (n + 1) → ℂ) i
        * (Theta L (t * (Fin.cons ξ0 ξ' : Fin (n + 1) → ℂ) i) * SB L)
            ((Fin.cons a0 a' : Fin (n + 1) → ZMod L) i) c
        * A (Function.update (Fin.cons a0 a') i c))
      = _
  rw [Fin.sum_univ_succ]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    simp [Fin.update_cons_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Fin.cons_succ]
    rw [← Fin.cons_update]

/-- `Uker` at `n = 0` is the identity (the unique index, no edges). -/
theorem Uker_zero_eq {L : ℕ} [NeZero L] (ξ : Fin 0 → ℂ) (s t : ℂ) (A : LoopArg L 0 → ℂ)
    (a : LoopArg L 0) : Uker L ξ s t A a = A a := by
  have hsub : ∀ b : LoopArg L 0, b = a := fun b => funext fun i => absurd i.isLt (by omega)
  rw [Uker_apply,
    Finset.sum_eq_single a (fun b _ hb => absurd (hsub b) hb) (fun h => absurd (Finset.mem_univ a) h)]
  simp

/-- Collapsing a sum against the identity matrix's row. -/
theorem sum_one_apply_mul_eq {L : ℕ} [NeZero L] (a0 : ZMod L) (H : ZMod L → ℂ) :
    ∑ c : ZMod L, (1 : Matrix (ZMod L) (ZMod L) ℂ) a0 c * H c = H a0 := by
  simp [Matrix.one_apply, ite_mul, Finset.sum_ite_eq']

/-- **The per-edge `hC`-bound of `RBM.norm_Uker_apply_le` at `s = u, t = u+Δ`**: any edge
parameter of modulus `≤ 1` gives `1 + ‖(s-t)ξ‖(1-‖tξ‖)⁻¹ ≤ 1 + Δβ`, `β := (1-(u+Δ))⁻¹`. -/
theorem edge_C_bound {ξ : ℂ} (hξ1 : ‖ξ‖ ≤ 1) {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ)
    (hut1 : u + Δ < 1) :
    1 + ‖((u : ℂ) - ((u + Δ : ℝ) : ℂ)) * ξ‖ * (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹
      ≤ 1 + Δ * (1 - (u + Δ))⁻¹ := by
  have hβpos : (0 : ℝ) < 1 - (u + Δ) := by linarith
  have h1 : ‖((u : ℂ) - ((u + Δ : ℝ) : ℂ)) * ξ‖ ≤ Δ := by
    have heq : (u : ℂ) - ((u + Δ : ℝ) : ℂ) = -((Δ : ℝ) : ℂ) := by push_cast; ring
    rw [heq, neg_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hΔ0]
    calc Δ * ‖ξ‖ ≤ Δ * 1 := mul_le_mul_of_nonneg_left hξ1 hΔ0
      _ = Δ := mul_one _
  have h3 : ‖((u + Δ : ℝ) : ℂ) * ξ‖ ≤ u + Δ := by
    calc ‖((u + Δ : ℝ) : ℂ) * ξ‖ = (u + Δ) * ‖ξ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left hξ1 (by linarith)
      _ = u + Δ := mul_one _
  have h2 : (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ ≤ (1 - (u + Δ))⁻¹ := inv_anti₀ hβpos (by linarith)
  have hnn2 : (0 : ℝ) ≤ (1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖)⁻¹ := by
    have hpos : (0 : ℝ) < 1 - ‖((u + Δ : ℝ) : ℂ) * ξ‖ := by linarith
    positivity
  have := mul_le_mul h1 h2 hnn2 hΔ0
  linarith

/-- **The `O(Δ)` bound on `Uker − id`** (the auxiliary "Lemma A" of the preflight): by induction
on `n`, peeling one coordinate at a time via `Uker_cons_eq`. Needed because
`RBM.norm_Uker_apply_le`'s coarse bound `‖Uker(F)(a)‖ ≤ C^n M` alone is `O(1)`, too weak to make
the middle term of `Uker_step_n`'s own induction `O(Δ²)`. -/
theorem norm_Uker_sub_self_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) :
    ∀ {n : ℕ} (ξ : Fin n → ℂ), (∀ i, ‖ξ i‖ ≤ 1) → ∀ {u Δ : ℝ}, 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
      ∀ {F : LoopArg L n → ℂ} {M : ℝ}, 0 ≤ M → (∀ b, ‖F b‖ ≤ M) → ∀ a,
        ‖Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) F a - F a‖
          ≤ ((1 + Δ * (1 - (u + Δ))⁻¹) ^ n - 1) * M := by
  intro n
  induction n with
  | zero =>
      intro ξ _ u Δ _ _ _ F M _ _ a
      rw [Uker_zero_eq]
      simp
  | succ n ih =>
      intro ξ hξ u Δ hu0 hΔ0 hut1 F M hM0 hFM a
      have hβpos : (0 : ℝ) < 1 - (u + Δ) := by linarith
      set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
      have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
      have hξt0 : ‖((u + Δ : ℝ) : ℂ) * ξ 0‖ < 1 := by
        calc ‖((u + Δ : ℝ) : ℂ) * ξ 0‖ = (u + Δ) * ‖ξ 0‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by linarith)]
          _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ 0) (by linarith)
          _ = u + Δ := mul_one _
          _ < 1 := hut1
      set a0 := a 0 with ha0def
      set a' := Fin.tail a with ha'def
      have haeq : a = Fin.cons a0 a' := (Fin.cons_self_tail a).symm
      set ξ0 := ξ 0 with hξ0def
      set ξ' := Fin.tail ξ with hξ'def
      have hξeq : ξ = Fin.cons ξ0 ξ' := (Fin.cons_self_tail ξ).symm
      set Fc : ZMod L → LoopArg L n → ℂ := fun c w => F (Fin.cons c w) with hFcdef
      have hFaeq : F (Fin.cons a0 a') = Fc a0 a' := rfl
      have hFcM : ∀ c, ∀ b, ‖Fc c b‖ ≤ M := fun c b => hFM (Fin.cons c b)
      rw [hξeq, haeq, Uker_cons_eq]
      set P0 : ZMod L → ZMod L → ℂ := fun x y =>
          ξ0 * (SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) x y with hP0def
      have hedge : ∀ c, edgeKer L ξ0 (u : ℂ) ((u + Δ : ℝ) : ℂ) a0 c
          = (1 : Matrix (ZMod L) (ZMod L) ℂ) a0 c + (Δ : ℂ) * P0 a0 c := by
        intro c
        have h := congrFun (congrFun
          (edgeKer_eq L hL (ξ := ξ0) (s := (u : ℂ)) (t := ((u + Δ : ℝ) : ℂ)) hξt0) a0) c
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
        rw [h, hP0def]
        have hcast : (u : ℂ) - ((u + Δ : ℝ) : ℂ) = -((Δ : ℝ) : ℂ) := by push_cast; ring
        rw [hcast]
        ring
      have hstep : ∀ c : ZMod L,
          edgeKer L ξ0 (u : ℂ) ((u + Δ : ℝ) : ℂ) a0 c
              * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'
            = (1 : Matrix (ZMod L) (ZMod L) ℂ) a0 c
                * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'
              + (Δ : ℂ) * (P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a') := by
        intro c; rw [hedge c]; ring
      have hUkerExpand :
          (∑ c : ZMod L, edgeKer L ξ0 (u : ℂ) ((u + Δ : ℝ) : ℂ) a0 c
              * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a')
            = Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc a0) a'
              + (Δ : ℂ) * ∑ c : ZMod L,
                  P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a' := by
        simp_rw [hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        exact sum_one_apply_mul_eq a0 (fun c => Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a')
      rw [hUkerExpand]
      have hIH := ih ξ' (fun i => hξ i.succ) hu0 hΔ0 hut1 hM0 (hFcM a0) a'
      have hUkerBound : ∀ c, ‖Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'‖
          ≤ (1 + Δ * β) ^ n * M := by
        intro c
        refine norm_Uker_apply_le L hL (fun i => ?_) hM0 (fun i' => ?_) (hFcM c) a'
        · calc ‖((u + Δ : ℝ) : ℂ) * ξ' i‖ = (u + Δ) * ‖ξ' i‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith)]
            _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ i.succ) (by linarith)
            _ = u + Δ := mul_one _
            _ < 1 := hut1
        · exact edge_C_bound (hξ i'.succ) hu0 hΔ0 hut1
      have hrowP0 : ∑ c : ZMod L, ‖P0 a0 c‖ ≤ β := by
        have hSBTheta : ‖SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ ≤ β := by
          calc ‖SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖
              ≤ ‖SB L‖ * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ := norm_mul_le _ _
            _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ := by rw [norm_SB L hL, one_mul]
            _ ≤ β := by
                have hb : ‖((u + Δ : ℝ) : ℂ) * ξ0‖ ≤ u + Δ := by
                  calc ‖((u + Δ : ℝ) : ℂ) * ξ0‖ = (u + Δ) * ‖ξ0‖ := by
                        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                          abs_of_nonneg (by linarith)]
                    _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ 0) (by linarith)
                    _ = u + Δ := mul_one _
                have h := norm_Theta_le L hL hξt0
                refine h.trans ?_
                rw [hβdef]
                exact inv_anti₀ hβpos (by linarith)
        calc ∑ c : ZMod L, ‖P0 a0 c‖
            = ∑ c : ZMod L, ‖ξ0‖ * ‖(SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) a0 c‖ := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [hP0def, norm_mul]
          _ = ‖ξ0‖ * ∑ c : ZMod L, ‖(SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) a0 c‖ := by
              rw [Finset.mul_sum]
          _ ≤ ‖ξ0‖ * β := by
              gcongr
              exact (sum_norm_row_le L _ a0).trans hSBTheta
          _ ≤ 1 * β := by gcongr; exact hξ 0
          _ = β := one_mul β
      have hsumP0 : ‖∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'‖
          ≤ β * ((1 + Δ * β) ^ n * M) := by
        calc ‖∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'‖
            ≤ ∑ c : ZMod L, ‖P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'‖ :=
              norm_sum_le _ _
          _ = ∑ c : ZMod L, ‖P0 a0 c‖
                * ‖Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'‖ :=
              Finset.sum_congr rfl fun c _ => norm_mul _ _
          _ ≤ ∑ c : ZMod L, ‖P0 a0 c‖ * ((1 + Δ * β) ^ n * M) := by
              refine Finset.sum_le_sum fun c _ => ?_
              gcongr
              exact hUkerBound c
          _ = (∑ c : ZMod L, ‖P0 a0 c‖) * ((1 + Δ * β) ^ n * M) := by rw [Finset.sum_mul]
          _ ≤ β * ((1 + Δ * β) ^ n * M) := by
              gcongr
      have hrw : Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc a0) a'
            + (Δ : ℂ) * ∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'
            - F (Fin.cons a0 a')
          = (Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc a0) a' - Fc a0 a')
            + (Δ : ℂ)
                * ∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a' := by
        rw [hFaeq]; ring
      rw [hrw]
      refine (norm_add_le _ _).trans ?_
      have h2 : ‖(Δ : ℂ)
            * ∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Fc c) a'‖
          ≤ Δ * (β * ((1 + Δ * β) ^ n * M)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ0]
        exact mul_le_mul_of_nonneg_left hsumP0 hΔ0
      refine (add_le_add hIH h2).trans (le_of_eq ?_)
      ring

/-- `ThetaOp` at `n = 0` is `0` (an empty sum, no edges). -/
theorem ThetaOp_zero_eq {L : ℕ} [NeZero L] (ξ : Fin 0 → ℂ) (t : ℂ) (A : LoopArg L 0 → ℂ)
    (a : LoopArg L 0) : ThetaOp L ξ t A a = 0 := by
  simp [ThetaOp]

/-- **(T2)**: the general-length one-step linearization of the evolution kernel, T1506's
`Uker_step` generalized to every `n` by induction (peeling one coordinate via `Fin.cons`,
`Uker_cons_eq`/`ThetaOp_cons_eq`). At `n = 2` the bound reduces *exactly* to T1506's
`3(1-(u+Δ))⁻²Δ²M` (`n·β²Δ² + ((1+Δβ)^n-1-nΔβ) = 2β²Δ² + (Δβ)² = 3β²Δ²`, the sanity check
recorded in the preflight). -/
theorem Uker_step_n {L : ℕ} [NeZero L] (hL : 3 ≤ L) :
    ∀ {n : ℕ} (ξ : Fin n → ℂ), (∀ i, ‖ξ i‖ ≤ 1) → ∀ {u Δ : ℝ}, 0 ≤ u → 0 ≤ Δ → u + Δ < 1 →
      ∀ {A : LoopArg L n → ℂ} {M : ℝ}, 0 ≤ M → (∀ b, ‖A b‖ ≤ M) → ∀ a,
        ‖Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) A a - A a
            - (Δ : ℂ) * ThetaOp L ξ (u : ℂ) A a‖
          ≤ ((n : ℝ) * Δ ^ 2 * (1 - (u + Δ))⁻¹ ^ 2
              + ((1 + Δ * (1 - (u + Δ))⁻¹) ^ n - 1
                  - (n : ℝ) * Δ * (1 - (u + Δ))⁻¹)) * M := by
  intro n
  induction n with
  | zero =>
      intro ξ _ u Δ _ _ _ A M _ _ a
      rw [Uker_zero_eq, ThetaOp_zero_eq]
      simp
  | succ n ih =>
      intro ξ hξ u Δ hu0 hΔ0 hut1 A M hM0 hAM a
      have hβpos : (0 : ℝ) < 1 - (u + Δ) := by linarith
      set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
      have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
      have hpow1 : (1 : ℝ) ≤ (1 + Δ * β) ^ n := one_le_pow₀ (by nlinarith)
      have hpowM0 : (0 : ℝ) ≤ ((1 + Δ * β) ^ n - 1) * M := mul_nonneg (by linarith) hM0
      have hξt0 : ‖((u + Δ : ℝ) : ℂ) * ξ 0‖ < 1 := by
        calc ‖((u + Δ : ℝ) : ℂ) * ξ 0‖ = (u + Δ) * ‖ξ 0‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ 0) (by linarith)
          _ = u + Δ := mul_one _
          _ < 1 := hut1
      have hξu0 : ‖(u : ℂ) * ξ 0‖ < 1 := by
        calc ‖(u : ℂ) * ξ 0‖ = u * ‖ξ 0‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
          _ ≤ u * 1 := mul_le_mul_of_nonneg_left (hξ 0) hu0
          _ = u := mul_one _
          _ < 1 := by linarith
      set a0 := a 0 with ha0def
      set a' := Fin.tail a with ha'def
      have haeq : a = Fin.cons a0 a' := (Fin.cons_self_tail a).symm
      set ξ0 := ξ 0 with hξ0def
      set ξ' := Fin.tail ξ with hξ'def
      have hξeq : ξ = Fin.cons ξ0 ξ' := (Fin.cons_self_tail ξ).symm
      set Ac : ZMod L → LoopArg L n → ℂ := fun c w => A (Fin.cons c w) with hAcdef
      have hAaeq : A (Fin.cons a0 a') = Ac a0 a' := rfl
      have hAcM : ∀ c, ∀ b, ‖Ac c b‖ ≤ M := fun c b => hAM (Fin.cons c b)
      rw [hξeq, haeq, Uker_cons_eq, ThetaOp_cons_eq]
      set P0 : ZMod L → ZMod L → ℂ := fun x y =>
          ξ0 * (SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) x y with hP0def
      set Q0 : ZMod L → ZMod L → ℂ := fun x y =>
          ξ0 * (SB L * Theta L ((u : ℂ) * ξ0)) x y with hQ0def
      have hedge : ∀ c, edgeKer L ξ0 (u : ℂ) ((u + Δ : ℝ) : ℂ) a0 c
          = (1 : Matrix (ZMod L) (ZMod L) ℂ) a0 c + (Δ : ℂ) * P0 a0 c := by
        intro c
        have h := congrFun (congrFun
          (edgeKer_eq L hL (ξ := ξ0) (s := (u : ℂ)) (t := ((u + Δ : ℝ) : ℂ)) hξt0) a0) c
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
        rw [h, hP0def]
        have hcast : (u : ℂ) - ((u + Δ : ℝ) : ℂ) = -((Δ : ℝ) : ℂ) := by push_cast; ring
        rw [hcast]; ring
      have hstep : ∀ c : ZMod L,
          edgeKer L ξ0 (u : ℂ) ((u + Δ : ℝ) : ℂ) a0 c
              * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'
            = (1 : Matrix (ZMod L) (ZMod L) ℂ) a0 c
                * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'
              + (Δ : ℂ) * (P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a') := by
        intro c; rw [hedge c]; ring
      have hUkerExpand :
          (∑ c : ZMod L, edgeKer L ξ0 (u : ℂ) ((u + Δ : ℝ) : ℂ) a0 c
              * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a')
            = Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac a0) a'
              + (Δ : ℂ) * ∑ c : ZMod L,
                  P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' := by
        simp_rw [hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        exact sum_one_apply_mul_eq a0 (fun c => Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a')
      have hThetaZeroTerm : (∑ c : ZMod L, ξ0 * (Theta L ((u : ℂ) * ξ0) * SB L) a0 c
              * A (Fin.cons c a'))
          = ∑ c : ZMod L, Q0 a0 c * Ac c a' := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hcomm : Theta L ((u : ℂ) * ξ0) * SB L = SB L * Theta L ((u : ℂ) * ξ0) :=
          (Theta_commute_SB L hL hξu0).eq
        rw [hcomm]
      rw [hUkerExpand, hThetaZeroTerm]
      have hIHmain := ih ξ' (fun i => hξ i.succ) hu0 hΔ0 hut1 hM0 (hAcM a0) a'
      have hIHzero := norm_Uker_sub_self_le hL ξ' (fun i => hξ i.succ) hu0 hΔ0 hut1 hM0
        (hAcM a0) a'
      have hUkerBound : ∀ c, ‖Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'‖
          ≤ (1 + Δ * β) ^ n * M := by
        intro c
        refine norm_Uker_apply_le L hL (fun i => ?_) hM0 (fun i' => ?_) (hAcM c) a'
        · calc ‖((u + Δ : ℝ) : ℂ) * ξ' i‖ = (u + Δ) * ‖ξ' i‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith)]
            _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ i.succ) (by linarith)
            _ = u + Δ := mul_one _
            _ < 1 := hut1
        · exact edge_C_bound (hξ i'.succ) hu0 hΔ0 hut1
      have hUkerSubBound : ∀ c, ‖Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' - Ac c a'‖
          ≤ ((1 + Δ * β) ^ n - 1) * M := fun c =>
        norm_Uker_sub_self_le hL ξ' (fun i => hξ i.succ) hu0 hΔ0 hut1 hM0 (hAcM c) a'
      have hrowP0 : ∑ c : ZMod L, ‖P0 a0 c‖ ≤ β := by
        have hSBTheta : ‖SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ ≤ β := by
          calc ‖SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖
              ≤ ‖SB L‖ * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ := norm_mul_le _ _
            _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ := by rw [norm_SB L hL, one_mul]
            _ ≤ β := by
                have hb : ‖((u + Δ : ℝ) : ℂ) * ξ0‖ ≤ u + Δ := by
                  calc ‖((u + Δ : ℝ) : ℂ) * ξ0‖ = (u + Δ) * ‖ξ0‖ := by
                        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                          abs_of_nonneg (by linarith)]
                    _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ 0) (by linarith)
                    _ = u + Δ := mul_one _
                have h := norm_Theta_le L hL hξt0
                refine h.trans ?_
                rw [hβdef]
                exact inv_anti₀ hβpos (by linarith)
        calc ∑ c : ZMod L, ‖P0 a0 c‖
            = ∑ c : ZMod L, ‖ξ0‖ * ‖(SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) a0 c‖ := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [hP0def, norm_mul]
          _ = ‖ξ0‖ * ∑ c : ZMod L, ‖(SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) a0 c‖ := by
              rw [Finset.mul_sum]
          _ ≤ ‖ξ0‖ * β := by
              gcongr
              exact (sum_norm_row_le L _ a0).trans hSBTheta
          _ ≤ 1 * β := by gcongr; exact hξ 0
          _ = β := one_mul β
      have hrowPQ0 : ∑ c : ZMod L, ‖P0 a0 c - Q0 a0 c‖ ≤ Δ * β ^ 2 := by
        have hTsub := Theta_sub_Theta L hL (ξ := (u : ℂ) * ξ0) (ζ := ((u + Δ : ℝ) : ℂ) * ξ0)
          hξu0 hξt0
        have hcast : ((u + Δ : ℝ) : ℂ) * ξ0 - (u : ℂ) * ξ0 = ((Δ : ℝ) : ℂ) * ξ0 := by
          push_cast; ring
        rw [hcast] at hTsub
        have hentry : ∀ c : ZMod L, P0 a0 c - Q0 a0 c
            = (((Δ : ℝ) : ℂ) * ξ0 ^ 2) *
                (SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0)))
                  a0 c := by
          intro c
          rw [hP0def, hQ0def]
          simp only
          rw [show ξ0 * (SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ0)) a0 c
                - ξ0 * (SB L * Theta L ((u : ℂ) * ξ0)) a0 c
              = ξ0 * (SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) - Theta L ((u : ℂ) * ξ0))) a0 c
              from by
                simp only [Matrix.mul_sub, Matrix.sub_apply]; ring,
            hTsub, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
          ring
        have hnormeq : ∀ c : ZMod L, ‖P0 a0 c - Q0 a0 c‖
            = Δ * ‖ξ0‖ ^ 2 * ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L
                * Theta L ((u : ℂ) * ξ0))) a0 c‖ := by
          intro c
          rw [hentry c, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hΔ0, norm_pow]
        simp_rw [hnormeq]
        rw [← Finset.mul_sum]
        have hop : ‖SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0))‖
            ≤ β ^ 2 := by
          have hT1 : ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ ≤ β := by
            refine (norm_Theta_le L hL hξt0).trans ?_
            have hb : ‖((u + Δ : ℝ) : ℂ) * ξ0‖ ≤ u + Δ := by
              calc ‖((u + Δ : ℝ) : ℂ) * ξ0‖ = (u + Δ) * ‖ξ0‖ := by
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                      abs_of_nonneg (by linarith)]
                _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ 0) (by linarith)
                _ = u + Δ := mul_one _
            rw [hβdef]
            exact inv_anti₀ hβpos (by linarith)
          have hT2 : ‖Theta L ((u : ℂ) * ξ0)‖ ≤ β := by
            refine (norm_Theta_le L hL hξu0).trans ?_
            have hb : ‖(u : ℂ) * ξ0‖ ≤ u := by
              calc ‖(u : ℂ) * ξ0‖ = u * ‖ξ0‖ := by
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
                _ ≤ u * 1 := mul_le_mul_of_nonneg_left (hξ 0) hu0
                _ = u := mul_one _
            rw [hβdef]
            refine inv_anti₀ hβpos ?_
            linarith
          have hSB1 : ‖SB L‖ ≤ 1 := (norm_SB L hL).le
          calc ‖SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0))‖
              ≤ ‖SB L‖ * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0)‖ :=
                norm_mul_le _ _
            _ ≤ 1 * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0)‖ := by
                gcongr
            _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0)‖ := one_mul _
            _ ≤ ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L‖ * ‖Theta L ((u : ℂ) * ξ0)‖ :=
                norm_mul_le _ _
            _ ≤ (‖Theta L (((u + Δ : ℝ) : ℂ) * ξ0)‖ * ‖SB L‖) * ‖Theta L ((u : ℂ) * ξ0)‖ := by
                gcongr; exact norm_mul_le _ _
            _ ≤ (β * 1) * β := by gcongr
            _ = β ^ 2 := by ring
        have hξ02 : ‖ξ0‖ ^ 2 ≤ 1 := by
          have h0 : 0 ≤ ‖ξ0‖ := norm_nonneg _
          nlinarith [hξ 0]
        have hrowsum : ∑ c : ZMod L,
            ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0))) a0 c‖
              ≤ β ^ 2 :=
          (sum_norm_row_le L _ a0).trans hop
        calc Δ * ‖ξ0‖ ^ 2 * ∑ c : ZMod L,
              ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ0) * SB L * Theta L ((u : ℂ) * ξ0))) a0 c‖
            ≤ Δ * ‖ξ0‖ ^ 2 * β ^ 2 := by gcongr
          _ ≤ Δ * 1 * β ^ 2 := by gcongr
          _ = Δ * β ^ 2 := by ring
      have hsplit1 : ‖∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'
            - ∑ c : ZMod L, Q0 a0 c * Ac c a'‖
          ≤ β * (((1 + Δ * β) ^ n - 1) * M) + Δ * β ^ 2 * M := by
        have hrw2 : (∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a')
              - ∑ c : ZMod L, Q0 a0 c * Ac c a'
            = (∑ c : ZMod L, P0 a0 c
                * (Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' - Ac c a'))
              + ∑ c : ZMod L, (P0 a0 c - Q0 a0 c) * Ac c a' := by
          rw [← Finset.sum_add_distrib]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun c _ => ?_
          ring
        rw [hrw2]
        refine (norm_add_le _ _).trans ?_
        have hb1 : ‖∑ c : ZMod L, P0 a0 c
              * (Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' - Ac c a')‖
            ≤ β * (((1 + Δ * β) ^ n - 1) * M) := by
          calc ‖∑ c : ZMod L, P0 a0 c
                * (Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' - Ac c a')‖
              ≤ ∑ c : ZMod L, ‖P0 a0 c
                  * (Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' - Ac c a')‖ := norm_sum_le _ _
            _ = ∑ c : ZMod L, ‖P0 a0 c‖
                  * ‖Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a' - Ac c a'‖ :=
                Finset.sum_congr rfl fun c _ => norm_mul _ _
            _ ≤ ∑ c : ZMod L, ‖P0 a0 c‖ * (((1 + Δ * β) ^ n - 1) * M) := by
                refine Finset.sum_le_sum fun c _ => ?_
                exact mul_le_mul_of_nonneg_left (hUkerSubBound c) (norm_nonneg _)
            _ = (∑ c : ZMod L, ‖P0 a0 c‖) * (((1 + Δ * β) ^ n - 1) * M) := by
                rw [Finset.sum_mul]
            _ ≤ β * (((1 + Δ * β) ^ n - 1) * M) :=
                mul_le_mul_of_nonneg_right hrowP0 hpowM0
        have hb2 : ‖∑ c : ZMod L, (P0 a0 c - Q0 a0 c) * Ac c a'‖ ≤ Δ * β ^ 2 * M := by
          calc ‖∑ c : ZMod L, (P0 a0 c - Q0 a0 c) * Ac c a'‖
              ≤ ∑ c : ZMod L, ‖(P0 a0 c - Q0 a0 c) * Ac c a'‖ := norm_sum_le _ _
            _ = ∑ c : ZMod L, ‖P0 a0 c - Q0 a0 c‖ * ‖Ac c a'‖ :=
                Finset.sum_congr rfl fun c _ => norm_mul _ _
            _ ≤ ∑ c : ZMod L, ‖P0 a0 c - Q0 a0 c‖ * M := by
                refine Finset.sum_le_sum fun c _ => ?_
                gcongr
                exact hAcM c a'
            _ = (∑ c : ZMod L, ‖P0 a0 c - Q0 a0 c‖) * M := by rw [Finset.sum_mul]
            _ ≤ Δ * β ^ 2 * M := by gcongr
        exact add_le_add hb1 hb2
      have hrwfin : Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac a0) a'
            + (Δ : ℂ) * ∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'
            - A (Fin.cons a0 a')
            - (Δ : ℂ) * (∑ c : ZMod L, Q0 a0 c * Ac c a'
                + ThetaOp L ξ' (u : ℂ) (fun w => A (Fin.cons a0 w)) a')
          = (Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac a0) a' - Ac a0 a'
                - (Δ : ℂ) * ThetaOp L ξ' (u : ℂ) (fun w => A (Fin.cons a0 w)) a')
            + (Δ : ℂ) * (∑ c : ZMod L, P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'
                - ∑ c : ZMod L, Q0 a0 c * Ac c a') := by
        rw [hAaeq]; ring
      rw [hrwfin]
      refine (norm_add_le _ _).trans ?_
      have hb3 : ‖(Δ : ℂ) * (∑ c : ZMod L,
            P0 a0 c * Uker L ξ' (u : ℂ) ((u + Δ : ℝ) : ℂ) (Ac c) a'
              - ∑ c : ZMod L, Q0 a0 c * Ac c a')‖
          ≤ Δ * (β * (((1 + Δ * β) ^ n - 1) * M) + Δ * β ^ 2 * M) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ0]
        exact mul_le_mul_of_nonneg_left hsplit1 hΔ0
      refine (add_le_add hIHmain hb3).trans (le_of_eq ?_)
      have hcast1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast1]
      ring

/-- **Satisfiability witness for `Uker_step_n`'s hypotheses at `n = 3`** (self-contained, no
probability space needed): `L = 5`, `ξ ≡ 1/2` (nonzero, `‖ξ_i‖ ≤ 1`), `u = 1/4`, `Δ = 1/8`
(so `u + Δ = 3/8 < 1`), `M = 1`, `A ≡ 1` (a genuine nonzero tensor, `‖A b‖ ≤ M`). Nothing
degenerates: `n = 3 ≠ 0`, `ξ ≠ 0`, `A ≠ 0`, `Δ > 0`. -/
example :
    ∃ (L : ℕ) (_ : NeZero L) (ξ : Fin 3 → ℂ), (∀ i, ‖ξ i‖ ≤ 1) ∧ (∀ i, ξ i ≠ 0) ∧
      ∃ (u Δ : ℝ), 0 ≤ u ∧ 0 < Δ ∧ u + Δ < 1 ∧
        ∃ (A : LoopArg L 3 → ℂ) (M : ℝ), 0 ≤ M ∧ (∀ b, ‖A b‖ ≤ M) ∧ (∀ b, A b ≠ 0) := by
  refine ⟨5, ⟨by norm_num⟩, fun _ => (1 / 2 : ℂ), fun i => ?_, fun i => ?_,
    1 / 4, 1 / 8, by norm_num, by norm_num, by norm_num,
    fun _ => (1 : ℂ), 1, by norm_num, fun b => ?_, fun b => ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end T2U

/-! ### (T3) : `discrete_hierarchy_step_n`, general loop length -/

section T3N

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The explicit deterministic error of (T3), general loop length `n`.** T1503's
`condExp_loop_drift` remainder (the first two summands, unchanged, already general in `n` via
`zMotionZLip/zMotionLip/genPtLip`), plus the (T2) `K_step_n` remainder, plus the (T2)
`Uker_step_n` remainder with the deterministic sup bound on `A_k` (`Lval`, unconditional via
`norm_gloop_le_of_le_abs_im`, plus the `Kval` envelope `Bk`). Polynomial in `Δ`, `N` (via
`B.L N, B.W N`), `n`, `Bk` — no existential. -/
noncomputable def stepErrN (B : Band Ω) (E : ℝ) (N n : ℕ) (uk uk1 Δ Bk : ℝ) : ℝ :=
  zMotionZLip (B.L N) (B.W N) n ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖ * Δ ^ 2 / 2
    + (zMotionLip (B.L N) (B.W N) n |(zt E uk).im| (mSigma E)
        + (2 / 3) * genPtLip (B.L N) (B.W N) n |(zt E uk).im| (mSigma E))
      * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat B.toDims N x‖ ∂ (P B.toDims))
    + (2 * (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk
          * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2)
        + (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ)
            * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2) ^ 2) * Δ ^ 2
    + ((n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
        + ((1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹))
        * (|(zt E uk).im|⁻¹ ^ n * (B.W N : ℝ)⁻¹ ^ (n - 1) + Bk)

/-- **(T3)**: the general-length analogue of T1506's (T4) `discrete_hierarchy_step`. Route:
exactly T1506's proof (`condExp_loop_drift`, already general in the loop index), with
`loopDrift_sub_K_deriv_n` (T1) replacing `loopDrift_sub_K_deriv`, `K_step_n` and `Uker_step_n`
(T2) replacing `K_step`/`Uker_step`. Holds for every charge sequence `σ` (alternating or not),
via `Fin n → Bool`. The `Kval` envelope `Bk` is threaded exactly as in `K_step_n` (witnessed,
non-vacuous, `exists_norm_Kval_le_upto`). -/
theorem discrete_hierarchy_step_n (B : Band Ω) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hst : s N < t N) (hk : k < K N) (hu0 : 0 ≤ time s t K N k)
    (hu1 : time s t K N (k + 1) < 1)
    {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) (σ : Fin n → Bool)
    {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (k + 1)), ∀ J : LoopIdx (ZMod (B.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ n → ‖B.Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (B.L N) n, ‖(time s t K N k : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) (n - 1)‖ < 1) :
    ∀ᵐ ω ∂ (Pg B.toDims), ∀ a : LoopArg (B.L N) n,
      ‖(Pg B.toDims)[fun ω' => LvalN B E N (time s t K N (k + 1))
              (H B.toDims s t K N (k + 1) ω') σ a
            - KvN B E N (time s t K N (k + 1)) σ a | filt B.toDims k] ω
          - Uker (B.L N) (xiOf (mSigma E) σ) (time s t K N k : ℂ)
              (time s t K N (k + 1) : ℂ)
              (fun v => LvalN B E N (time s t K N k) (H B.toDims s t K N k ω) σ v
                - KvN B E N (time s t K N k) σ v) a
          - (step s t K N : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) (H B.toDims s t K N k ω)
                    (zt E (time s t K N k)) ⟨List.ofFn σ, List.ofFn a⟩
                + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (B.L N) (B.W N) lK
                    (B.Kval E N (time s t K N k))
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))))
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    ⟨List.ofFn σ, List.ofFn a⟩)‖
        ≤ stepErrN B E N n (time s t K N k) (time s t K N (k + 1)) (step s t K N) Bk := by
  set d : Dims := B.toDims with hd
  set uk : ℝ := time s t K N k with hukdef
  set uk1 : ℝ := time s t K N (k + 1) with huk1def
  set Δ : ℝ := step s t K N with hΔdef
  have hKpos : 0 < K N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hΔpos : 0 < Δ := by
    rw [hΔdef]; unfold step; exact div_pos (by linarith) (by exact_mod_cast hKpos)
  have huk1eq : uk1 = uk + Δ := by
    rw [huk1def, hukdef, hΔdef]; unfold time; push_cast; ring
  have hukuk1 : uk ≤ uk1 := by rw [huk1eq]; linarith
  have huk_lt : uk < 1 := by linarith
  have hzk : (zt E uk).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb huk_lt
  have hzk1 : (zt E uk1).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  have hηk : 0 < |(zt E uk).im| := abs_pos.mpr hzk
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hukIcc : uk ∈ Set.Icc (0 : ℝ) uk1 := ⟨hu0, hukuk1⟩
  have hlabel : ∀ a : LoopArg (B.L N) n, ∀ᵐ ω ∂ (Pg d),
      ‖(Pg d)[fun ω' => LvalN B E N uk1 (H d s t K N (k + 1) ω') σ a
              - KvN B E N uk1 σ a | filt d k] ω
          - Uker (B.L N) (xiOf (mSigma E) σ) (uk : ℂ) (uk1 : ℂ)
              (fun v => LvalN B E N uk (H d s t K N k ω) σ v - KvN B E N uk σ v) a
          - (Δ : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) (H d s t K N k ω) (zt E uk)
                    ⟨List.ofFn σ, List.ofFn a⟩
                + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (B.L N) (B.W N) lK
                    (B.Kval E N uk)
                    (gloop (B.L N) (B.W N) (H d s t K N k ω) (zt E uk) - B.Kval E N uk)
                    (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))))
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) (H d s t K N k ω) (zt E uk) - B.Kval E N uk)
                    (gloop (B.L N) (B.W N) (H d s t K N k ω) (zt E uk) - B.Kval E N uk)
                    ⟨List.ofFn σ, List.ofFn a⟩)‖
        ≤ stepErrN B E N n uk uk1 Δ Bk := by
    intro a
    set I : LoopIdx (ZMod (d.L N)) := ⟨List.ofFn σ, List.ofFn a⟩ with hIdef
    have hwf : I.WF := by show (List.ofFn σ).length = (List.ofFn a).length; simp
    have hn1 : 1 ≤ I.a.length := by show 1 ≤ (List.ofFn a).length; rw [List.length_ofFn]; omega
    have hIlen : I.length = n := by show (List.ofFn a).length = n; rw [List.length_ofFn]
    have hIn2 : 2 ≤ I.length := by rw [hIlen]; exact hn2
    -- integrability of `Φ_{u_{k+1}} ∘ H_{k+1}`
    have hTF : TestFun d N (loopObs d N (zt E uk1) I) :=
      testFun_loopObs_of_im_le hzk1 (abs_pos.mpr hzk1) le_rfl hwf hn1
    obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
    have hHk1meas : Measurable (fun ω : Ωg d => H d s t K N (k + 1) ω) :=
      (H_measurable_filt d s t K N (k + 1)).mono ((filt d).le (k + 1)) le_rfl
    have hInt : Integrable
        (fun ω : Ωg d => loopObs d N (zt E uk1) I (H d s t K N (k + 1) ω)) (Pg d) :=
      (memLp_top_of_bound
        (hTF.contDiff.continuous.measurable.comp hHk1meas).aestronglyMeasurable C₀
        (Eventually.of_forall fun ω => hC₀ _)).integrable le_top
    have hfun : (fun ω' => LvalN B E N uk1 (H d s t K N (k + 1) ω') σ a - KvN B E N uk1 σ a)
        = (fun ω' : Ωg d => loopObs d N (zt E uk1) I (H d s t K N (k + 1) ω'))
          - (fun _ => KvN B E N uk1 σ a) := by
      funext ω'
      rw [Pi.sub_apply, loopObs_of_isHermitian (H_isHermitian d s t K N (k + 1) ω')]
      rfl
    have hCE : (Pg d)[fun ω' => LvalN B E N uk1 (H d s t K N (k + 1) ω') σ a - KvN B E N uk1 σ a
          | filt d k]
        =ᵐ[Pg d] fun ω => (Pg d)[fun ω' : Ωg d => loopObs d N (zt E uk1) I
            (H d s t K N (k + 1) ω') | filt d k] ω - KvN B E N uk1 σ a := by
      rw [hfun]
      filter_upwards [condExp_sub hInt (integrable_const (KvN B E N uk1 σ a)) (filt d k)]
        with ω hω
      rw [hω, Pi.sub_apply, condExp_const ((filt d).le k)]
    have hT := condExp_loop_drift s t K N k E hEb hwf hn1 hst hk hu0 hu1 hzk hzk1
    filter_upwards [hT, hCE] with ω h1 h2
    rw [h2]
    set M : Matrix (d.Idx N) (d.Idx N) ℂ := H d s t K N k ω with hMdef
    have hM : M.IsHermitian := H_isHermitian d s t K N k ω
    set c : ℂ := (Pg d)[fun ω' : Ωg d => loopObs d N (zt E uk1) I
      (H d s t K N (k + 1) ω') | filt d k] ω with hcdef
    have hσlen : I.σ.length = n := hwf.trans hIlen
    -- (e₁) T1503
    have he1 : ‖c - LvalN B E N uk M σ a - (Δ : ℂ) * loopDrift (d := d) (N := N) E uk I M‖
        ≤ zMotionZLip (B.L N) (B.W N) n ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖ * Δ ^ 2 / 2
          + (zMotionLip (B.L N) (B.W N) n |(zt E uk).im| (mSigma E)
              + (2 / 3) * genPtLip (B.L N) (B.W N) n |(zt E uk).im| (mSigma E))
            * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
      rw [loopObs_of_isHermitian hM, hσlen, smul_eq_mul] at h1
      exact h1
    -- (T1) at `u_k`, `M = H_k ω`
    have hT1 := loopDrift_sub_K_deriv_n B E N uk hM hzk hn2 σ a (hξ a)
    -- (T2) at `u_k → u_{k+1}`
    have hBkI : ∀ w ∈ Set.Icc (0 : ℝ) uk1, ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
        2 ≤ J.length → J.length ≤ I.length → ‖B.Kval E N w J‖ ≤ Bk := by
      intro w hw J hJwf hJ2 hJle
      exact hBk w hw J hJwf hJ2 (hIlen ▸ hJle)
    have hT2raw := K_step_n hL3 (B.W N) (mSigma E) (fun s' => norm_mSigma_le_one hEb s')
      I hwf hIn2 hu1 hBk0 hBkI hukIcc (Set.right_mem_Icc.mpr (hu0.trans hukuk1)) hukuk1
    have he2 : ‖KvN B E N uk1 σ a - KvN B E N uk σ a
          - (Δ : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N uk) I‖
        ≤ (2 * (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk
              * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2)
            + (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ)
                * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2) ^ 2) * Δ ^ 2 := by
      have huk1uk : uk1 - uk = Δ := by rw [huk1eq]; ring
      rw [huk1uk] at hT2raw
      have hcast : (I.length : ℝ) = (n : ℝ) := by exact_mod_cast hIlen
      calc ‖KvN B E N uk1 σ a - KvN B E N uk σ a
              - (Δ : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N uk) I‖
          = ‖Kgen (B.L N) (B.W N) (mSigma E) uk1 I - Kgen (B.L N) (B.W N) (mSigma E) uk I
              - (Δ : ℂ) * primRhs (B.L N) (B.W N) (Kgen (B.L N) (B.W N) (mSigma E) uk) I‖ := rfl
        _ ≤ (2 * (B.W N : ℝ) * (I.length : ℝ) ^ 2 * (B.L N : ℝ) * Bk
                * ((B.W N : ℝ) * (I.length : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2)
              + (B.W N : ℝ) * (I.length : ℝ) ^ 2 * (B.L N : ℝ)
                  * ((B.W N : ℝ) * (I.length : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2) ^ 2)
              * Δ ^ 2 := hT2raw
        _ = (2 * (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk
                * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2)
              + (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ)
                  * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2) ^ 2) * Δ ^ 2 := by
            rw [hcast]
    -- (T3) with the deterministic sup bound `M_k`
    set Mk : ℝ := |(zt E uk).im|⁻¹ ^ n * (B.W N : ℝ)⁻¹ ^ (n - 1) + Bk with hMk
    have hMk0 : 0 ≤ Mk := by
      have h1 : (0:ℝ) ≤ |(zt E uk).im|⁻¹ ^ n * (B.W N : ℝ)⁻¹ ^ (n - 1) := by positivity
      linarith
    have hA : ∀ b, ‖LvalN B E N uk M σ b - KvN B E N uk σ b‖ ≤ Mk := by
      intro b
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · have h := norm_gloop_le_of_le_abs_im (L := B.L N) (W := B.W N) hM hηk le_rfl
          (⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod (B.L N)))
          (by show (List.ofFn σ).length = (List.ofFn b).length; simp)
          (by show 1 ≤ (List.ofFn b).length; rw [List.length_ofFn]; omega)
        simpa [LvalN, List.length_ofFn] using h
      · exact hBk uk hukIcc _ (by show (List.ofFn σ).length = (List.ofFn b).length; simp)
          (by rw [show ((⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod (B.L N))).length) = n from
            by show (List.ofFn b).length = n; rw [List.length_ofFn]]; exact hn2)
          (by rw [show ((⟨List.ofFn σ, List.ofFn b⟩ : LoopIdx (ZMod (B.L N))).length) = n from
            by show (List.ofFn b).length = n; rw [List.length_ofFn]])
    have hut1 : uk + Δ < 1 := by rw [← huk1eq]; exact hu1
    have hξOf1 : ∀ i : Fin n, ‖xiOf (mSigma E) σ i‖ ≤ 1 := by
      intro i
      show ‖mSigma E (σ i) * mSigma E (σ (i + 1))‖ ≤ 1
      calc ‖mSigma E (σ i) * mSigma E (σ (i + 1))‖
          = ‖mSigma E (σ i)‖ * ‖mSigma E (σ (i + 1))‖ := norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (norm_mSigma_le_one hEb _) (norm_mSigma_le_one hEb _)
            (norm_nonneg _) zero_le_one
        _ = 1 := mul_one _
    have hT3 := Uker_step_n hL3 (xiOf (mSigma E) σ) hξOf1 hu0 hΔpos.le hut1 hMk0 hA a
    rw [← huk1eq] at hT3
    -- the exact cancellation
    have hident : c - KvN B E N uk1 σ a
          - Uker (B.L N) (xiOf (mSigma E) σ) (uk : ℂ) (uk1 : ℂ)
              (fun v => LvalN B E N uk M σ v - KvN B E N uk σ v) a
          - (Δ : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) M (zt E uk) ⟨List.ofFn σ, List.ofFn a⟩
                + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (B.L N) (B.W N) lK
                    (B.Kval E N uk)
                    (gloop (B.L N) (B.W N) M (zt E uk) - B.Kval E N uk)
                    (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))))
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) M (zt E uk) - B.Kval E N uk)
                    (gloop (B.L N) (B.W N) M (zt E uk) - B.Kval E N uk)
                    ⟨List.ofFn σ, List.ofFn a⟩)
        = (c - LvalN B E N uk M σ a - (Δ : ℂ) * loopDrift (d := d) (N := N) E uk I M)
          - (KvN B E N uk1 σ a - KvN B E N uk σ a
              - (Δ : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N uk) I)
          - (Uker (B.L N) (xiOf (mSigma E) σ) (uk : ℂ) (uk1 : ℂ)
                (fun v => LvalN B E N uk M σ v - KvN B E N uk σ v) a
              - (LvalN B E N uk M σ a - KvN B E N uk σ a)
              - (Δ : ℂ) * ThetaOp (B.L N) (xiOf (mSigma E) σ) (uk : ℂ)
                (fun v => LvalN B E N uk M σ v - KvN B E N uk σ v) a) := by
      have hprI : primRhs (B.L N) (B.W N) (B.Kval E N uk) I
          = primRhs (B.L N) (B.W N) (B.Kval E N uk)
              (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) := rfl
      linear_combination (Δ : ℂ) * hT1 - (Δ : ℂ) * hprI
    have key : ∀ x y z : ℂ, ‖x - y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := fun x y z => by
      linarith [norm_sub_le (x - y) z, norm_sub_le x y]
    have hfinal : stepErrN B E N n uk uk1 Δ Bk
        = (zMotionZLip (B.L N) (B.W N) n ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖
              * Δ ^ 2 / 2
            + (zMotionLip (B.L N) (B.W N) n |(zt E uk).im| (mSigma E)
                + (2 / 3) * genPtLip (B.L N) (B.W N) n |(zt E uk).im| (mSigma E))
              * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)))
          + (2 * (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk
                * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2)
              + (B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ)
                  * ((B.W N : ℝ) * (n : ℝ) ^ 2 * (B.L N : ℝ) * Bk ^ 2) ^ 2) * Δ ^ 2
          + ((n : ℝ) * Δ ^ 2 * (1 - uk1)⁻¹ ^ 2
              + ((1 + Δ * (1 - uk1)⁻¹) ^ n - 1 - (n : ℝ) * Δ * (1 - uk1)⁻¹)) * Mk := by
      rw [hMk]; rfl
    rw [hident, hfinal]
    refine (key _ _ _).trans ?_
    linarith [he1, he2, hT3]
  exact ae_all_iff.mpr hlabel

end T3N
