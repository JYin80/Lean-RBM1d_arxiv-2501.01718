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
# T262: the early-time quadratic-variation rate, `U = id`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2–§5.3, Lemma 5.7, (5.22)–(5.25), (5.36), (5.63), (5.71)–(5.72).

This file supplies the **deterministic** half of the statement `(S3)` of
`docs/reports/V548-referee.md` §6: the instance of (5.36) at `t = u`, `a = a' = b`,
`U = id`, i.e. a bound on

`quadVar (M ↦ (L - K)_{u,σ,b}(M)) (H_u)`

with **no evolution kernel in front of the loop**.

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

  obtained from T213's `RBM.EEUker.quadVarPairs_Uker_le_norm_eeFun'` at `v = u`, where
  `RBM.Uker_self` collapses the evolution kernel on **both** sides to the identity.  This
  answers the question the referee left open in §6 ("是否已到能取 `U = id` 的程度"): the
  bridge was already complete, and taking `t = u` needs nothing new.

* `RBM.EarlyQVRate.quadVar_lkFun_le_tailT` — the bridge in the `B · T² + R` shape that
  `RBM.Gauss.sum_cutWeight_quadForm_tailT_le` consumes.

* `RBM.EarlyQVRate.quadVar_lkFun_le_ee` — the bridge composed with `RBM.EEDef.ee_le_EEpath`,
  i.e. with (5.36) for the pinned `E ⊗ E`, at arbitrary loop length.

* `RBM.EarlyQVRate.quadVar_lkFun_le_ee_sym` — **(S3) itself**: the same at the `2`-loop
  `σ = (+,-)` with `a = a' = b`, through `RBM.EEDef.ee_le_EEpath_sym`, in which the
  Cauchy–Schwarz step `h566`, the `(G†E_bG)` step `h572` and the "by symmetry" half `hsym`
  are all **discharged** (T156/T172/T178).  The surviving hypotheses are the three a-priori
  Step-1 inputs `h273`, `h564`, `h42sq` together with the structural witnesses `Gm`, `Gsq`,
  `Smax`.  The statement is pointwise in `(u, ω)`, so the probabilistic wrapper of (S3)
  (Step 1's `≺` event, uniformly over the grid `j ≤ n_N` and over all `b`) composes with it
  from outside and is **not** part of this file.

## The far field is sharp, and the referee's `W^{-1}` is a slip

The V548 referee states (S3) with a far field

`W^{-1} A_u^{-1/2} r_u^{3/2} (J*)^2 + W^{-1} A_u^{-1} (J*)^3`   (`A_u = W ℓ_u η_u`),

citing (5.71)/(5.72) and the identity `ℓ_u A_u^{-3/2} = η_u^{-1} W^{-1} A_u^{-1/2}`.  The
identity is correct, but it is about the **`b`-sum** `∑_{b,b'} L^{(1)}`, which is what
(5.71)/(5.72) bound.  Definition 5.4 (5.22) carries a factor `W` in front of that sum
(`RBM.Lemma57.norm_eeTens_le_W_sum`, hypothesis `hEE : EE ≤ W * ∑ b, L6 b` of
`RBM.Lemma57.ee_le`), and `W · ℓ_u A_u^{-3/2} = η_u^{-1} A_u^{-1/2}`.  So the correct sharp
far field of `(E ⊗ E)/T²` is

`η_u^{-1} r_u^{3/2} A_u^{-1/2} (J*)^2 + η_u^{-1} A_u^{-1} (J*)^3`   (+ the `J* W^{-3}` tail),

with **no** `W^{-1}`; that is exactly the conclusion of `RBM.Lemma57.ee_le` (far part:
`η_u^{-1}(cFar2 · J^2 · (A_u μ) + 72 J^3 A_u^{-1}) T^2`, with `μ = r_u^{3/2} A_u^{-3/2}` from
(2.73) at `n = 4`).  The sharpening the referee actually needs — and gets — is `(J*)^2` in
place of the `(J*)^3` of the *statement* (5.36), which is worth a factor `J* ≤ c₀ N^{2δ}R^4`;
the `W^{-1}` is not available and not needed.  See the `Deviations` section at the end.

Nothing here is an `axiom` and nothing is `sorry`.
-/

namespace RBM

namespace EarlyQVRate

open Matrix Finset RBM.Gauss
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ### 1. `L - K`, `L` and `loopObs` have the same quadratic variation at a Hermitian point -/

/-- `RBM.Gauss.loopObs` is the Hermitian regularization (`RBM.Gauss.hermFun`) of the raw loop
`RBM.gloop`.  Definitional, but worth a name: it is the only place where the two differ. -/
theorem loopObs_eq_hermFun (d : Dims) (N : ℕ) (z : ℂ) (I : LoopIdx (ZMod (d.L N))) :
    loopObs d N z I = hermFun d N (fun M' => gloop (d.L N) (d.W N) M' z I) := rfl

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
is the object (S3) is about; the right-hand side is the one T213's `(5.25)` bridge speaks
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

The referee's open question in §6 (iii) — whether the repository's `eeFun`/`EE` bridge had
reached the point where `U = id` may be taken — is answered here in the affirmative: it had,
and no new estimate is needed to specialize it. -/
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

/-! ### 3. Composition with (5.36): the deterministic skeleton of (S3) -/

/-- **The `B · T² + R` repackaging.**  `RBM.Gauss.sum_cutWeight_quadForm_tailT_le` — the step
that turns a per-entry `(5.36)` into a bound on the quadratic variation of the smooth maximum
`J̃` — consumes its input in the shape `∑_α S_α ‖∂_α f_i‖² ≤ B · T_{u,D}(d_i)² + R`.  This is
the `U = id` bridge in that shape. -/
theorem quadVar_lkFun_le_tailT {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin (n + 2) → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (a : LoopArg (B.L N) (n + 2))
    {Wr ℓu ηu D ℓ Bfac R : ℝ}
    (hEE : ‖MomentDuhamel.eeFun B E N u M σ (Fin.append a a)‖
      ≤ Bfac * tailT Wr ℓu ηu D ℓ ^ 2 + R) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M
      ≤ (((n : ℝ) + 2) * Bfac) * tailT Wr ℓu ηu D ℓ ^ 2 + ((n : ℝ) + 2) * R := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  have h := quadVar_lkFun_le_norm_eeFun hE hu0 hu1 σ hM a
  have h2 := mul_le_mul_of_nonneg_left hEE hn
  calc quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M
      ≤ ((n : ℝ) + 2) * ‖MomentDuhamel.eeFun B E N u M σ (Fin.append a a)‖ := h
    _ ≤ ((n : ℝ) + 2) * (Bfac * tailT Wr ℓu ηu D ℓ ^ 2 + R) := h2
    _ = (((n : ℝ) + 2) * Bfac) * tailT Wr ℓu ηu D ℓ ^ 2 + ((n : ℝ) + 2) * R := by ring

/-- **(S3) for the loop `(L - K)_{u,σ,b}` at `t = u`, `U = id`, `a = a' = b`**: the `U = id`
bridge composed with `RBM.EEDef.ee_le_EEpath`, i.e. with (5.36) in the **sharp** far-field
form its proof (5.71)+(5.72) gives.

The right-hand side, after dividing by `T_{u,D}(‖b₁-b₂‖)²`, is

`η_u^{-1} ( c_near · r_u^5 · 1(‖b₁-b₂‖ ≤ 4 ℓ*_u)
          + c_far · (J*)² · A_u μ  +  72 (J*)³ A_u^{-1} )`   `+ (tail)`,

and with `μ = r_u^{3/2} A_u^{-3/2}` from (2.73) at `n = 4` the middle term is
`c_far · r_u^{3/2} A_u^{-1/2} (J*)²`.  That is the far field the cross term of (A′) needs:
under (2.72) (`A_t ≥ R^{30}`) and on the support of the weight (`J* ≤ c₀ N^{2δ} R^4`),
`(t-s) · κ̂^{far} ≲ R^{5/2} A_t^{-1/2} + N^{2δ} R^5 A_t^{-1} ≲ R^{-12}`, which closes with
room to spare.  No `W^{-1}` is available and none is needed (see the module docstring). -/
theorem quadVar_lkFun_le_ee (X : Sample B) {E : ℝ} (hE : |E| < 2) {n N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (a : LoopArg (B.L N) (n + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (a₁ a₂ : ZMod (B.L N))
    {Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
      EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (h566 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ)
    (h572 : ∀ b, ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
      EEDef.eeL6 X E N u ω σ (Fin.append a a) b
        ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter (fun b : ZMod (B.L N) =>
        ¬ ((zdist (B.L N) (a₁ - b) : ℝ) ≤ (zdist (B.L N) (a₂ - b) : ℝ))),
          EEDef.eeL6 X E N u ω σ (Fin.append a a) b) ≤
      ((2 * ellStar (B.W N : ℝ) ℓu + 2) * (J ^ 2 * Lemma57.loss1 (B.W N : ℝ) * μ)
        + J ^ 3 * (36 * ℓu * (((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹
          + (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)))
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ ((n : ℝ) + 2) *
        (ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
              (if (zdist (B.L N) (a₁ - a₂) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu then 1 else 0)
            + Lemma57.cFar2 (B.W N : ℝ) ℓu * (J ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * μ))
            + 72 * J ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2
          + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
            + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3
              * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  refine (quadVar_lkFun_le_norm_eeFun hE hu0 hu1 σ (X.hermitian N u ω) a).trans ?_
  exact mul_le_mul_of_nonneg_left
    (EEDef.ee_le_EEpath X E u ω σ (Fin.append a a) hℓu hℓs hηu hJ a₁ a₂ hμ hρ hGsq
      h273 h564 h42sq h566 h572 hsym) hn

/-! ### 3b. (S3) proper: the `2`-loop `σ = (+,-)`, `a = a' = b`, with `h566`/`h572`/`hsym`
discharged -/

theorem lab₁_append {N : ℕ} (a : LoopArg (B.L N) (0 + 2)) :
    EEDef.lab₁ (Fin.append a a) = a 0 := by
  rw [EEDef.lab₁, EEBridge.leftArg_append]

theorem lab₂_append {N : ℕ} (a : LoopArg (B.L N) (0 + 2)) :
    EEDef.lab₂ (Fin.append a a) = a 1 := by
  rw [EEDef.lab₂, EEBridge.leftArg_append]

/-- **(S3).**  The early-time quadratic-variation rate of the `(+,-)` loop `L - K` at
`t = u`, `U = id`, `a = a' = b = (b₁, b₂)`, with the **sharp** far field of (5.71)+(5.72) and
with the Cauchy–Schwarz step (5.65)/(5.66), the `(G†E_bG)` step (5.72) and the "by symmetry"
half all discharged (T156/T172/T178, `RBM.EEDef.ee_le_EEpath_sym`).

What is left on the hypothesis side is exactly the three a-priori Step-1 inputs `h273`,
`h564`, `h42sq` (plus the structural witnesses `Gm`, `Gsq`, `Smax` of `ee_le_EEpath_sym`).
That is the precise interface at which the probabilistic wrapper of (S3) — "on the Step-1 `≺`
event, uniformly over all grid points `j ≤ n_N` and all `b`" — has to be plugged in: this
statement is pointwise in `(u, ω)`, so a union bound over the grid enters *outside* it and
changes nothing here. -/
theorem quadVar_lkFun_le_ee_sym (X : Sample B) {E : ℝ} (hE : |E| < 2) {N : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a : LoopArg (B.L N) (0 + 2))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax)
    (h273 : ∀ b, EEDef.eeL6 X E N u ω σ (Fin.append a a) b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (a 0 - b) : ℝ) → EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) (X.H N u ω)
      ≤ 2 * (ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
              (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
                then 1 else 0)
            + Lemma57.cFar2 (B.W N : ℝ) ℓu
              * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
            + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1)) ^ 2
          + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
            + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
              * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a 0 - a 1)) ^ 2)) := by
  have hbridge := quadVar_lkFun_le_norm_eeFun (n := 0) hE hu0 hu1 σ (X.hermitian N u ω) a
  have hc0 : EEBridge.rightArg (Fin.append a a) 0 = EEBridge.leftArg (Fin.append a a) 0 := by
    rw [EEBridge.leftArg_append, EEBridge.rightArg_append]
  have hc1 : EEBridge.rightArg (Fin.append a a) 1 = EEBridge.leftArg (Fin.append a a) 1 := by
    rw [EEBridge.leftArg_append, EEBridge.rightArg_append]
  have h564' : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (EEDef.lab₁ (Fin.append a a) - b) : ℝ) →
      EEDef.eeL6 X E N u ω σ (Fin.append a a) b ≤ ρ := by
    rw [lab₁_append]; exact h564
  have hee := EEDef.ee_le_EEpath_sym X E u ω σ (Fin.append a a) hℓu hℓs hηu hJ hc0 hc1 hρ
    hGm0 hGm hGsq0 hGsq2 hrow hSmax h273 h564' h42sq
  rw [lab₁_append, lab₂_append] at hee
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  refine hbridge.trans ?_
  have hcast : ((0 : ℕ) : ℝ) + 2 = 2 := by norm_num
  rw [hcast]
  exact mul_le_mul_of_nonneg_left hee h2


/-! ### 4. Satisfiability

`quadVar_lkFun_le_norm_eeFun` and `quadVar_lkFun_le_tailT` carry no hypothesis that could be
vacuous: `|E| < 2`, `0 ≤ u < 1` and `M.IsHermitian` are the standing window conditions, and
`hEE` is an *upper* bound on a quantity that is finite, so it can always be met with a large
enough `Bfac`.  The witness below records that explicitly, with **both** constants strictly
positive (no `Bfac = 0`, no `R = 0`) and at an arbitrary Hermitian `M` — in particular at
`M = H_u(ω)` for any `ω`, so nothing here is an empty event. -/
theorem sat_quadVar_lkFun_le_tailT {E : ℝ} (hE : |E| < 2) {N n : ℕ} {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (σ : Fin (n + 2) → Bool)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (a : LoopArg (B.L N) (n + 2))
    {Wr ℓu ηu D ℓ : ℝ} (hWr : 1 ≤ Wr) :
    ∃ Bfac R : ℝ, 0 < Bfac ∧ 0 < R ∧
      ‖MomentDuhamel.eeFun B E N u M σ (Fin.append a a)‖
        ≤ Bfac * tailT Wr ℓu ηu D ℓ ^ 2 + R ∧
      quadVar B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' σ a) M
        ≤ (((n : ℝ) + 2) * Bfac) * tailT Wr ℓu ηu D ℓ ^ 2 + ((n : ℝ) + 2) * R := by
  refine ⟨1, ‖MomentDuhamel.eeFun B E N u M σ (Fin.append a a)‖ + 1, one_pos, ?_, ?_, ?_⟩
  · positivity
  · have hT : 0 < tailT Wr ℓu ηu D ℓ := tailT_pos (by linarith) ℓ
    nlinarith [hT]
  · refine quadVar_lkFun_le_tailT hE hu0 hu1 σ hM a ?_
    have hT : 0 < tailT Wr ℓu ηu D ℓ := tailT_pos (by linarith) ℓ
    nlinarith [hT]

/-! ### Deviations

None from the paper.  Every statement here is an instance of results already in the
repository, and the far field is the one the paper's own proof gives, (5.71)+(5.72) times the
factor `W` of (5.22).

**T262a** (not a paper deviation; a correction to `docs/reports/V548-referee.md`): §2c.4, §6
(S3) and the `(iii)` discussion of that report state the sharp far field with an extra factor
`W^{-1}`.  Checked against the printed paper, p. 62–63: (5.71) reads
`∑_{b,b'} L^{(1)} ≺ (ℓ_u/ℓ_s)^{3/2} ℓ_u (W ℓ_u η_u)^{-3/2} (J*_{u,D})² (T_{t,D}(|a₁-a₂|))²`
and (5.72) reads `∑_{b,b'} L^{(1)} ≺ (J*_{u,D})³ ℓ_t (W ℓ_t η_t)^{-2} (T_{t,D}(|a₁-a₂|))²`.
These bound the `b`-sum; (5.22) puts a factor `W` in front of it, and
`W · ℓ_u A_u^{-3/2} = η_u^{-1} A_u^{-1/2}`, `W · ℓ_t A_t^{-2} = η_t^{-1} A_t^{-1}`.  So the
`W^{-1}` of the referee's identity `ℓ_u A_u^{-3/2} = η_u^{-1} W^{-1} A_u^{-1/2}` is cancelled
by (5.22) and does not survive into `(E ⊗ E)`.  The sharpening that is real, and that the
cross term of (A′) actually uses, is `(J*)²` in place of the `(J*)³` of the *statement*
(5.36) — worth a factor `J* ≤ c₀ N^{2δ} R^4`.  Paper unchanged; report line to be corrected;
0 lines of Lean affected (`RBM.Lemma57.ee_le` already had the correct form). -/


end EarlyQVRate

end RBM
