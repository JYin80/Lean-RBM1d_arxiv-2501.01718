/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EEUker
import RBM1D.Gauss.TestFunHerm
import RBM1D.Hierarchy.EGDef
import RBM1D.Hierarchy.EEDef

/-!
# The early-time quadratic-variation rate, `U = id`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2–§5.3, Lemma 5.7, (5.22)–(5.25), (5.36), (5.63), (5.71)–(5.72).

(S3) denotes the early-time quadratic-variation bound: the instance of (5.36) at `t = u`,
`a = a' = b`, `U = id`, i.e. a bound on

`quadVar (M ↦ (L - K)_{u,σ,b}(M)) (H_u)`

with **no evolution kernel in front of the loop**.  This file supplies its **deterministic**
half.

## What is here

* `RBM.EarlyQVRate.quadVar_lkFun_eq_quadVarPairs_loopObs` — the three-step identification
  `quadVar (L - K) = quadVar (L) = quadVar (loopObs) = quadVarPairs (loopObs)`: the constant
  `K` drops out of `fderiv`, and at a Hermitian `M` the Hermitian regularization `hermCLM`
  that `RBM.Gauss.loopObs` carries does not change the derivative along a used coordinate
  (`RBM.Gauss.coordD1_hermFun`, with `RBM.EGDef.contDiffAt_gloop_matrix` for the
  differentiability side condition — the raw `gloop` is `C^∞` in the matrix only *at* a
  Hermitian point, which is exactly where it is evaluated here).

* `RBM.EarlyQVRate.quadVar_lkFun_le_norm_eeFun` — **the `U = id` bridge**:

  `quadVar (M ↦ (L-K)_{u,σ,b}(M)) M ≤ (n+2) · ‖(E ⊗ E)_{u,σ,b,b}‖`,

  obtained from `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun'` at `v = u`, where
  `RBM.Uker_self` collapses the evolution kernel on **both** sides to the identity; taking
  `t = u` needs nothing new.  The statement is pointwise in `M`, so the probabilistic wrapper
  of (S3) composes with it from outside and is **not** part of this file.

## The far field

The far field of `(E ⊗ E)/T²` carries no factor `W^{-1}`.  A far field

`W^{-1} A_u^{-1/2} r_u^{3/2} (J*)^2 + W^{-1} A_u^{-1} (J*)^3`   (`A_u = W ℓ_u η_u`),

would follow from (5.71)/(5.72) and the identity `ℓ_u A_u^{-3/2} = η_u^{-1} W^{-1} A_u^{-1/2}`.
The identity is correct, but it is about the **`b`-sum** `∑_{b,b'} L^{(1)}`, which is what
(5.71)/(5.72) bound.  Definition 5.4 (5.22) carries a factor `W` in front of that sum
(`RBM.EEDef.norm_eeTens_le_W_sum`, hypothesis `hEE : EE ≤ W * ∑ b, L6 b` of
`RBM.Lemma57.ee_le_sym'`), and `W · ℓ_u A_u^{-3/2} = η_u^{-1} A_u^{-1/2}`.  So the correct sharp
far field of `(E ⊗ E)/T²` is

`η_u^{-1} r_u^{3/2} A_u^{-1/2} (J*)^2 + η_u^{-1} A_u^{-1} (J*)^3`   (+ the `J* W^{-3}` tail),

with **no** `W^{-1}`; that is exactly the conclusion of `RBM.Lemma57.ee_le_sym'` (far part:
`η_u^{-1}(cFar2 · J^2 · (A_u μ) + 72 J^3 A_u^{-1}) T^2`, with `μ = r_u^{3/2} A_u^{-3/2}` from
(2.73) at `n = 4`).  The sharpening used downstream is `(J*)^2` in place of the `(J*)^3` of the
*statement* (5.36), which is worth a factor `J* ≤ c₀ N^{2δ}R^4`; the `W^{-1}` is not available
and not needed.

Nothing here is an `axiom` and nothing is `sorry`.
-/

namespace RBM

namespace EarlyQVRate

open Matrix Finset RBM.Gauss
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ### 1. `L - K`, `L` and `loopObs` have the same quadratic variation at a Hermitian point -/

/-- **The coordinate derivative of `(L - K)` is that of `RBM.Gauss.loopObs`.**

Two things happen: the deterministic `K` of (5.13) does not depend on the matrix, so
`fderiv` drops it (`fderiv_sub_const`); and at a Hermitian `M`, along a Hermitian coordinate
direction, the projection `hermCLM` that `loopObs` pre-composes with is invisible
(`RBM.Gauss.coordD1_hermFun`).  The differentiability side condition is
`RBM.EGDef.contDiffAt_gloop_matrix`, which holds **at** Hermitian points only. -/
theorem coordD1_lkFun_eq {E : ℝ} {N n : ℕ} {u : ℝ} (hz : (zt E u).im ≠ 0)
    (σ : Fin n → Bool) {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (a : LoopArg (B.L N) n) {q : B.toDims.Idx N × B.toDims.Idx N × Bool}
    (hq : q ∈ usedCoord B.toDims N) :
    coordD1 B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M q
      = coordD1 B.toDims N (loopObs B.toDims N (zt E u) (toIdx σ a)) M q := by
  have hdiff : DifferentiableAt ℝ
      (fun M' : Matrix (B.Idx N) (B.Idx N) ℂ =>
        gloop (B.L N) (B.W N) M' (zt E u) (toIdx σ a)) M :=
    (EGDef.contDiffAt_gloop_matrix (L := B.L N) (W := B.W N) (k := 2) hM hz
      (toIdx σ a)).differentiableAt (by norm_num)
  have h1 : coordD1 B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M q
      = coordD1 B.toDims N
        (fun M' : Matrix (B.Idx N) (B.Idx N) ℂ =>
          gloop (B.L N) (B.W N) M' (zt E u) (toIdx σ a)) M q := by
    change fderiv ℝ (fun M' : Matrix (B.Idx N) (B.Idx N) ℂ =>
        gloop (B.L N) (B.W N) M' (zt E u) (toIdx σ a) - B.Kval E N u (toIdx σ a)) M
          (Bmat B.toDims N q.1 q.2.1 q.2.2)
      = fderiv ℝ (fun M' : Matrix (B.Idx N) (B.Idx N) ℂ =>
        gloop (B.L N) (B.W N) M' (zt E u) (toIdx σ a)) M (Bmat B.toDims N q.1 q.2.1 q.2.2)
    rw [fderiv_sub_const]
  have hherm : loopObs B.toDims N (zt E u) (toIdx σ a)
      = hermFun B.toDims N (fun M' : Matrix (B.Idx N) (B.Idx N) ℂ =>
          gloop (B.L N) (B.W N) M' (zt E u) (toIdx σ a)) := rfl
  rw [h1, hherm, coordD1_hermFun hM hdiff hq]

/-- **`quadVar (L - K) = quadVar (loopObs)` at a Hermitian matrix.** -/
theorem quadVar_lkFun_eq_quadVar_loopObs {E : ℝ} {N n : ℕ} {u : ℝ}
    (hz : (zt E u).im ≠ 0) (σ : Fin n → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (a : LoopArg (B.L N) n) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M
      = quadVar B.toDims N (loopObs B.toDims N (zt E u) (toIdx σ a)) M := by
  simp only [quadVar]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [coordD1_lkFun_eq hz σ hM a hq]

/-- **`quadVar (L - K) = quadVarPairs (loopObs)` at a Hermitian matrix.**  The left-hand side
is the object (S3) is about; the right-hand side is the one `(5.25)` bridge speaks
of. -/
theorem quadVar_lkFun_eq_quadVarPairs_loopObs {E : ℝ} {N n : ℕ} {u : ℝ}
    (hz : (zt E u).im ≠ 0) (σ : Fin n → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (a : LoopArg (B.L N) n) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M
      = quadVarPairs B.toDims N (loopObs B.toDims N (zt E u) (toIdx σ a)) M := by
  rw [quadVar_lkFun_eq_quadVar_loopObs hz σ hM a]
  exact secondOrder_eq_quadVar (d := B.toDims) (N := N) _ _

/-! ### 2. The `U = id` bridge -/

/-- **(5.25) at `U = id`.**  `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun'` is (5.25) with the
evolution kernel `U_{u,v,σ}` in front of the loop; at `v = u` the kernel is the identity
(`RBM.Uker_self`, `RBM.edgeKer_self`) on **both** sides, and what is left is the bound
`(S3)` needs:

`∑_α S_α ‖∂_α (L - K)_{u,σ,b}‖² ≤ (n+2) · ‖(E ⊗ E)_{u,σ}(b, b)‖`.
-/
theorem quadVar_lkFun_le_norm_eeFun {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin (n + 2) → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian)
    (a : LoopArg (B.L N) (n + 2)) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M
      ≤ ((n : ℝ) + 2) * ‖MomentDuhamel.eeFun B E N u M σ (Fin.append a a)‖ := by
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  have hu : ‖((u : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hu0]; exact hu1
  have ht : ∀ i : Fin (n + 2), ‖((u : ℝ) : ℂ) * xiOf (mSigma E) σ i‖ < 1 :=
    fun i => norm_mul_mSigma_lt_one hE.le hu0 hu1 (σ i) (σ (i + 1))
  have ht2 : ∀ i : Fin ((n + 2) + (n + 2)), ‖((u : ℝ) : ℂ) * EEUker.xi2bar E σ i‖ < 1 := by
    intro i
    have hb : ‖EEUker.xi2bar E σ i‖ ≤ 1 := by
      rw [← EEUker.xi2_eq_xi2bar]; exact SumZeroDyn.norm_xi2_le hE σ i
    calc ‖((u : ℝ) : ℂ) * EEUker.xi2bar E σ i‖
        = ‖((u : ℝ) : ℂ)‖ * ‖EEUker.xi2bar E σ i‖ := norm_mul _ _
      _ ≤ ‖((u : ℝ) : ℂ)‖ * 1 := by
          exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hu
  have hkey := EEUker.quadVarPairs_Uker_le_norm_eeFun' (B := B) (u := u) (v := u)
    hE hu1 hu0 hu1 σ hM a
  rw [congrFun (Uker_self (B.L N) (B.three_le_L N) ht2 (MomentDuhamel.eeFun B E N u M σ))
    (Fin.append a a)] at hkey
  rw [quadVar_lkFun_eq_quadVarPairs_loopObs hz σ hM a]
  refine Eq.trans_le ?_ hkey
  congr 1
  funext M'
  exact (congrFun (Uker_self (B.L N) (B.three_le_L N) ht
    (fun b => loopObs B.toDims N (zt E u) (toIdx σ b) M')) a).symm

/-! ### 3. The two labels of the doubled argument of a `2`-loop -/

theorem lab₁_append {N : ℕ} (a : LoopArg (B.L N) (0 + 2)) :
    EEDef.lab₁ (Fin.append a a) = a 0 := by
  rw [EEDef.lab₁, EEBridge.leftArg_append]

theorem lab₂_append {N : ℕ} (a : LoopArg (B.L N) (0 + 2)) :
    EEDef.lab₂ (Fin.append a a) = a 1 := by
  rw [EEDef.lab₂, EEBridge.leftArg_append]

/-! ### 4. Satisfiability

`quadVar_lkFun_le_norm_eeFun` carries no hypothesis that could be vacuous: `|E| < 2`,
`0 ≤ u < 1` and `M.IsHermitian` are the standing window conditions, and they hold at
`M = H_u(ω)` for any `ω`, so nothing here is an empty event. -/

/-! ### Deviations

None from the paper.  Every statement here is an instance of results already in the
library, and the far field is the one the paper's own proof gives, (5.71)+(5.72) times the
factor `W` of (5.22).
-/


end EarlyQVRate

end RBM
