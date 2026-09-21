/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57
import RBM1D.Gauss.MomentDuhamel

/-!
# T167: (5.36) applied to the pinned `E ⊗ E`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.22) and (5.36) (pp. 53, 61-63).

T156 (`RBM1D/Hierarchy/Lemma57.lean`) proved **(5.36)** as a pointwise inequality
`RBM.Lemma57.ee_le` about an *abstract* real number `EE`, tied to the `b`-sum of (5.22) only
through the hypothesis

`hEE : EE ≤ W * ∑ b, L^{(1)}(b)`,

with `L^{(1)}` itself abstract (item 9 of the deviation list in `Lemma57.lean`).  That is the
same fiat hole T163 closed for `E^{(G̃)}`: as long as `L^{(1)}` is a parameter, nothing says
the estimate is about the `E ⊗ E` the moment Duhamel actually consumes.

This file closes it on the `E ⊗ E` side.  The pinned object is
`RBM.MomentDuhamel.EEpath = RBM.EEBridge.eeField` (T127/T135/T145), a **definition**, and
(5.22) is already a theorem in the repository — `RBM.EEBridge.eeEdge_eq_sum_gloop`.  Putting
the two together makes both `hEE` and `hL6` *provable* rather than assumed.

## Main results

* `RBM.EEDef.glueSum` — `L^{(1)}(b)` of (5.22), **defined**: `∑_k ∑_{b'} |S^{(B)}_{bb'}|
  ‖L_{glue(I,I',k,b,b')}‖`, the `(2n+2)`-loop of (5.23) summed over the cut edge `k` and the
  second glue label `b'`.
* `RBM.EEDef.norm_eeTens_le_W_sum` — **(5.22) in the shape `hEE` wants**:
  `‖(E⊗E)_{σ,a,a'}‖ ≤ W ∑_b L^{(1)}(b)`.  This is the expansion that `Lemma57.lean` records as
  "not in the repository"; it is, via T74's `eeEdge_eq_sum_SB` and T127's `glueLoop_loopCut`.
* `RBM.EEDef.eeL6`, `RBM.EEDef.norm_EEpath_le_W_sum`, `RBM.EEDef.norm_eeField_le_W_sum` — the
  same for the pinned `E ⊗ E` along the flow.
* `RBM.EEDef.ee_le_EEpath`, `RBM.EEDef.ee_le_paper_EEpath` — **(5.36) for
  `‖RBM.MomentDuhamel.EEpath X E n N u ω σ c‖`**, i.e. for the very term the moment Duhamel
  integrates.  `hEE`, `hL6` and `1 ≤ W` are gone; `L^{(1)}` is no longer a parameter.
* `RBM.EEDef.ee_le_EEpath_labels` — the same with `a₁`, `a₂` taken to be the loop's *own*
  first two labels, so that the normalization `T_{u,D}(‖a₁-a₂‖)` of (5.36) is not a free
  choice either.
* `RBM.EEDef.ee_hyp_consistent` — the six surviving hypotheses are **jointly satisfiable**
  for the concrete `eeL6`, with an explicit witness.  Without this the wiring could have
  produced a theorem with an empty hypothesis set, which is what T172's scan found elsewhere.
* `RBM.EEDef.eeL6k`, `RBM.EEDef.eeL6_two_eq`, `RBM.EEDef.glueIdx_two_zero`,
  `RBM.EEDef.glueIdx_two_one` (T178) — the `k`-sum of (5.22) at `n = 0` and the two explicit
  glued `6`-loops of Figure 14.
* `RBM.EEDef.eeL6k_two_one_le`, `RBM.EEDef.eeL6k_two_zero_le`, `RBM.EEDef.eeL6_two_le` (T178)
  — **(5.65) + (5.66)** for each summand of (5.22), i.e. the content of `h566`, at the
  granularity at which it is true.  See the section "⚠ What this says about `h566`" below.
* `RBM.EEDef.eeL6k_two_one_le_glue`, `RBM.EEDef.eeL6k_two_zero_le_glue` (T178) — **(5.65) +
  (5.72)** for each summand, i.e. the content of `h572`.

## What remains assumed, and why

Six hypotheses survive, and none of them is about the plumbing:

* `h273` — (2.73) at `n = 6` for the glued loop.  An a-priori Step-1 input.
* `h564` — the `‖a₁-b‖ > ℓ**_u` part of the `b`-sum is `≤ ρ`.  Lemma 5.9's decay for the
  glued `(2n+2)`-loop; kept as an explicit additive remainder (deviation 5 of `Lemma57.lean`).
* `h42sq` — (4.2)/(4.5) + (5.31) for the squared `G`-pair `Gsq`.  The Lemma 4.1 chain.
* `h566` — the Cauchy-Schwarz step (5.65)/(5.66).  The `6`-loop machinery it needs now exists
  (`RBM.Lemma57.norm_gloop_six_le_schwarz` and the section at the end of this file, T178), and
  the estimate holds for the **`k = 1` summand** of (5.22), `RBM.EEDef.eeL6k_two_one_le`.  It
  does **not** hold for `eeL6`, which is the sum over `k`: the `k = 0` summand has the two
  `b'`-edges attached to `a₁`, not `a₂`, so it carries `Gsq b a₁` where `h566` asks for
  `Gsq b a₂`, and exactly where `case2a_pointwise` uses `h566` the former has no decay.  So
  `h566` is *not* independent of `hsym`; see "⚠ What this says about `h566`" below.
* `h572` — `(G†E_bG)_{x₁x₁'} ≤ max_{y ∈ I_b} ‖G_{yx₁}‖‖G_{yx₁'}‖` (the honest index order;
  `G(z)` is not symmetric).  **Done**: `RBM.Lemma57.norm_conjTranspose_mul_Eblk_mul_apply_le`,
  and for the glued loop itself `RBM.EEDef.eeL6k_two_one_le_glue` /
  `RBM.EEDef.eeL6k_two_zero_le_glue` (T178), which *both* summands of (5.22) satisfy.
* `hsym` — the half `‖a₂-b‖ < ‖a₁-b‖`.  **Known gap, and a negative result**: T156 established
  (`docs/paper-deltas.md` #113 ②) that the paper's "by symmetry" is the `k=1`/`k=2` symmetry of
  (5.22), *not* a relabelling inside the `k=1` term — on that half the `(b,a₂)` pair of
  `G`-edges of (5.65) is short and (5.31) does not apply.  It cannot be derived from the `k=1`
  term, so it is *not* attempted here.

The wiring in the middle of this file is deliberately indifferent to all six: they are stated
about the concrete `RBM.EEDef.eeL6`, so discharging any one of them later needs no change to
`ee_le_EEpath` itself.

## Fiat audit

Every quantity on the left of `ee_le_EEpath` is a definition: `EEpath` (T145) is `eeField`
(T127) is `eeArg` is `RBM.Gauss.eeTens` of Definition 5.4, evaluated at the flow's own matrix
`X.H N u ω` and spectral parameter `z_u`.  The `b`-sum on the right is `eeL6`, again a
definition, and the inequality between them is a theorem, not an assumption.  No structure
field occurs anywhere in the statement, and no `RBM.SumZeroDyn.Hierarchy` is instantiated
(T118).  The witnesses a caller must still supply — `Gsq`, `μ`, `ρ` — occur in the
*hypotheses*, and `Gsq`, `μ` also in the conclusion of the master form, exactly as `Gm` does
in T163's `eG_le_reduced`; `ee_le_paper_EEpath` eliminates `μ`.
-/

namespace RBM
namespace EEDef

open Matrix Finset Gauss EEBridge MomentDuhamel

/-! ### (5.22) as the `b`-sum that (5.36) consumes -/

section Generic

variable {d : Dims} {N : ℕ} {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}

/-- **`L^{(1)}(b)` of (5.22)**: the glued `(2n+2)`-loop of (5.23), summed over the cut edge `k`
and over the second glue label `b'` against the weight `S^{(B)}_{bb'}`.

The factor `W` of (5.22) is *not* included; it sits in front of the `b`-sum, where
`RBM.Lemma57.ee_le` expects it. -/
noncomputable def glueSum (d : Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) (m : ℕ) (b : ZMod (d.L N)) : ℝ :=
  ∑ k ∈ Finset.range m, ∑ b' : ZMod (d.L N),
    ‖SB (d.L N) b b'‖ * ‖gloop (d.L N) (d.W N) M z (glueIdx I I' k b b')‖

theorem glueSum_nonneg (d : Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) (m : ℕ) (b : ZMod (d.L N)) :
    0 ≤ glueSum d N z M I I' m b := by
  unfold glueSum; positivity

/-- **(5.22) in the shape `RBM.Lemma57.ee_le` consumes it**:
`‖(E⊗E)_{σ,a,a'}‖ ≤ W ∑_b L^{(1)}(b)`.

`RBM.Gauss.eeTens` is the `k`-sum of `RBM.Gauss.eeEdge` over the `n` edges of the loop, and
each edge is `W ∑_{b,b'} S^{(B)}_{bb'} · L_{glue}` by T74's `eeEdge_eq_sum_SB` read through
T127's gluing identity (`RBM.EEBridge.eeEdge_eq_sum_gloop`).  Taking norms and exchanging the
`k`- and `b`-sums is all that happens here. -/
theorem norm_eeTens_le_W_sum (hM : M.IsHermitian) (I I' : LoopIdx (ZMod (d.L N))) {m : ℕ}
    (hm : I.length = m) :
    ‖eeTens d N z M I I'‖
      ≤ (d.W N : ℝ) * ∑ b : ZMod (d.L N), glueSum d N z M I I' m b := by
  classical
  subst hm
  have hsum : eeTens d N z M I I'
      = ∑ k ∈ Finset.range I.length, eeEdge d N z M I I' k := rfl
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ k ∈ Finset.range I.length,
      ‖eeEdge d N z M I I' k‖
        ≤ (d.W N : ℝ) * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
            ‖SB (d.L N) b b'‖ * ‖gloop (d.L N) (d.W N) M z (glueIdx I I' k b b')‖ := by
    intro k _
    rw [eeEdge_eq_sum_gloop hM I I' k, norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => le_of_eq (norm_mul _ _))
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
  unfold glueSum
  rw [Finset.sum_comm]

end Generic

/-! ### The same for the pinned `E ⊗ E` along the flow -/

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`L^{(1)}(b)` of (5.22) for the `E ⊗ E` of the flow**, `RBM.EEDef.glueSum` at the matrix
`H_u` and the spectral parameter `z_u`, with the two loops the two halves of the doubled
argument `c`. -/
noncomputable def eeL6 (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) : ℝ :=
  ∑ k ∈ Finset.range m, ∑ b' : ZMod (B.L N),
    ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) k b b')‖

theorem eeL6_eq_glueSum (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) :
    eeL6 X E N u ω σ c b
      = glueSum B.toDims N (zt E u) (X.H N u ω)
          (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) m b := rfl

theorem eeL6_nonneg (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) :
    0 ≤ eeL6 X E N u ω σ c b := by
  unfold eeL6; positivity

/-- **(5.22) for `RBM.MomentDuhamel.eeFun`.** -/
theorem norm_eeFun_le_W_sum (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) :
    ‖eeFun B E N u (X.H N u ω) σ c‖
      ≤ (B.W N : ℝ) * ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b := by
  have h := norm_eeTens_le_W_sum (d := B.toDims) (N := N) (z := zt E u)
      (M := X.H N u ω) (X.hermitian N u ω)
      (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) (m := m) (toIdx_length _ _)
  simp only [eeL6_eq_glueSum]
  exact h

/-- **(5.22) for the pinned `E ⊗ E`, `RBM.MomentDuhamel.EEpath`.**  This is the hypothesis
`hEE` of `RBM.Lemma57.ee_le`, proved. -/
theorem norm_EEpath_le_W_sum (X : Sample B) (E : ℝ) {n N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    ‖MomentDuhamel.EEpath X E n N u ω σ c‖
      ≤ (B.W N : ℝ) * ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b :=
  norm_eeFun_le_W_sum X E N u ω σ c

/-- **(5.22) for T127's `RBM.EEBridge.eeField`** — the same statement, `EEpath` being
`eeField` by `rfl`. -/
theorem norm_eeField_le_W_sum (X : Sample B) (E : ℝ) {n N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2))) :
    ‖EEBridge.eeField X E n N u ω σ c‖
      ≤ (B.W N : ℝ) * ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b :=
  norm_eeFun_le_W_sum X E N u ω σ c

theorem one_le_W (B : Band Ω) (N : ℕ) : 1 ≤ (B.W N : ℝ) := by
  exact_mod_cast B.W_pos N

end Path

/-! ### (5.36) for the pinned `E ⊗ E` -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.36) for `RBM.MomentDuhamel.EEpath`**, the master form.

This is `RBM.Lemma57.ee_le` with `L := B.L N`, `W := W N`, `EE := ‖EEpath …‖` and
`L^{(1)} := RBM.EEDef.eeL6`.  Three of its hypotheses are discharged here — `hEE` by
`RBM.EEDef.norm_EEpath_le_W_sum` (i.e. by (5.22)), `hL6` by `RBM.EEDef.eeL6_nonneg`, and
`1 ≤ W` by `B.W_pos` — and nothing is left that could be satisfied by choosing the `E ⊗ E`
conveniently: it is not chosen at all.

What survives is listed in the module docstring; `h566` and `hsym` are the two known gaps. -/
theorem ee_le_EEpath (X : Sample B) (E : ℝ) {n N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (a₁ a₂ : ZMod (B.L N))
    {Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
      eeL6 X E N u ω σ c b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (h566 : ∀ b, eeL6 X E N u ω σ c b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ)
    (h572 : ∀ b, ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
      eeL6 X E N u ω σ c b
        ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter (fun b : ZMod (B.L N) =>
        ¬ ((zdist (B.L N) (a₁ - b) : ℝ) ≤ (zdist (B.L N) (a₂ - b) : ℝ))),
          eeL6 X E N u ω σ c b) ≤
      ((2 * ellStar (B.W N : ℝ) ℓu + 2) * (J ^ 2 * Lemma57.loss1 (B.W N : ℝ) * μ)
        + J ^ 3 * (36 * ℓu * (((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹
          + (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)))
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2) :
    ‖MomentDuhamel.EEpath X E n N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (a₁ - a₂) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu then 1 else 0)
          + Lemma57.cFar2 (B.W N : ℝ) ℓu * (J ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * μ))
          + 72 * J ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2) :=
  Lemma57.ee_le (B.L N) (one_le_W B N) hℓu hℓs hηu hJ a₁ a₂ hμ hρ
    (eeL6_nonneg X E N u ω σ c) hGsq h273 h564 h42sq h566 h572 hsym
    (norm_EEpath_le_W_sum X E u ω σ c)

/-- **(5.36) for `RBM.MomentDuhamel.EEpath`, in the paper's shape.**  `μ` is instantiated from
(2.73) at `n = 4`, so it no longer occurs; the right-hand side is

`η_u^{-1}[(ℓ_u/ℓ_s)^5 1(‖a₁-a₂‖ ≤ 4ℓ*_u) + (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} (J*)³] T_{u,D}(‖a₁-a₂‖)²`

plus the two explicit remainders, which is (5.36) up to the `(ℓ_u/ℓ_s)^{3/2}` the paper drops
(deviation 8 of `Lemma57.lean`). -/
theorem ee_le_paper_EEpath (X : Sample B) (E : ℝ) {n N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (B.W N : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs) (a₁ a₂ : ZMod (B.L N))
    {Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
      eeL6 X E N u ω σ c b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (h566 : ∀ b, eeL6 X E N u ω σ c b ≤ Gsq a₁ a₂ * Gsq b a₂ *
      (ℓu / ℓs * √(ℓu / ℓs) * ((√((B.W N : ℝ) * ℓu * ηu))⁻¹ * ((B.W N : ℝ) * ℓu * ηu)⁻¹)))
    (h572 : ∀ b, ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
      eeL6 X E N u ω σ c b
        ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - b))))
    (hsym : (∑ b ∈ Finset.univ.filter (fun b : ZMod (B.L N) =>
        ¬ ((zdist (B.L N) (a₁ - b) : ℝ) ≤ (zdist (B.L N) (a₂ - b) : ℝ))),
          eeL6 X E N u ω σ c b) ≤
      ((2 * ellStar (B.W N : ℝ) ℓu + 2) * (J ^ 2 * Lemma57.loss1 (B.W N : ℝ) *
          (ℓu / ℓs * √(ℓu / ℓs) *
            ((√((B.W N : ℝ) * ℓu * ηu))⁻¹ * ((B.W N : ℝ) * ℓu * ηu)⁻¹)))
        + J ^ 3 * (36 * ℓu * (((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹
          + (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)))
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2) :
    ‖MomentDuhamel.EEpath X E n N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (a₁ - a₂) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu then 1 else 0)
          + (Lemma57.cFar2 (B.W N : ℝ) ℓu + 72)
            * (ℓu / ℓs * √(ℓu / ℓs) * (√((B.W N : ℝ) * ℓu * ηu))⁻¹) * J ^ 3)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2) :=
  Lemma57.ee_le_paper (B.L N) (one_le_W B N) hℓu hℓs hηu hJ hA hr a₁ a₂ hρ
    (eeL6_nonneg X E N u ω σ c) hGsq h273 h564 h42sq h566 h572 hsym
    (norm_EEpath_le_W_sum X E u ω σ c)

/-- The first label of the `2`-loop carried by a doubled loop argument. -/
def lab₁ {L : ℕ} (c : LoopArg L (2 + 2)) : ZMod L := leftArg c 0

/-- The second label of the `2`-loop carried by a doubled loop argument. -/
def lab₂ {L : ℕ} (c : LoopArg L (2 + 2)) : ZMod L := leftArg c 1

/-- **(5.36) at loop length `2`, with `a₁`, `a₂` the loop's own labels.**

`RBM.EEDef.ee_le_EEpath` leaves `a₁`, `a₂` free; (5.36) is a statement about the `2`-loop
`L_{u,σ,(a₁,a₂)}`, so the normalization `T_{u,D}(‖a₁-a₂‖)` must be read off the argument `c`
of the `E ⊗ E` itself.  Here it is: `a₁ = c₀`, `a₂ = c₁`, the two labels of the first half of
the doubled argument (deviation 6 of `Lemma57.lean`: the second half is taken equal to the
first for the purposes of (5.36)).  Nothing else changes. -/
theorem ee_le_EEpath_labels (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (c : LoopArg (B.L N) ((0 + 2) + (0 + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    {Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {μ ρ : ℝ} (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hGsq : ∀ x y, 0 ≤ Gsq x y)
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
        < (zdist (B.L N) (lab₁ c - b) : ℝ) → eeL6 X E N u ω σ c b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (h566 : ∀ b, eeL6 X E N u ω σ c b ≤ Gsq (lab₁ c) (lab₂ c) * Gsq b (lab₂ c) * μ)
    (h572 : ∀ b, ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (lab₁ c - b) : ℝ) →
      eeL6 X E N u ω σ c b ≤ Gsq (lab₁ c) (lab₂ c) * Gsq b (lab₂ c)
        * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - b))))
    (hsym : (∑ b ∈ Finset.univ.filter (fun b : ZMod (B.L N) =>
        ¬ ((zdist (B.L N) (lab₁ c - b) : ℝ) ≤ (zdist (B.L N) (lab₂ c - b) : ℝ))),
          eeL6 X E N u ω σ c b) ≤
      ((2 * ellStar (B.W N : ℝ) ℓu + 2) * (J ^ 2 * Lemma57.loss1 (B.W N : ℝ) * μ)
        + J ^ 3 * (36 * ℓu * (((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹
          + (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)))
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
              then 1 else 0)
          + Lemma57.cFar2 (B.W N : ℝ) ℓu * (J ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * μ))
          + 72 * J ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * J ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2) :=
  ee_le_EEpath X E u ω σ c hℓu hℓs hηu hJ (lab₁ c) (lab₂ c) hμ hρ hGsq h273 h564 h42sq
    h566 h572 hsym

/-! ### The surviving hypotheses are consistent

A wiring theorem is worthless if the hypotheses it still carries cannot all hold at once: the
conclusion would then be vacuous and its "proof" would prove nothing.  T172's repo-wide scan
found one such collapsed hypothesis elsewhere (`MinorGood`), so the check is made here
explicitly rather than argued in prose.

The witness is uniform in everything: `ℓ_u = ℓ_s = 1`, `D = 0`, `η_u = (W(1+S))^{-1}` with
`S = ∑_b L^{(1)}(b)` — so that `A_u = W ℓ_u η_u = (1+S)^{-1}` and the (2.73) budget
`A_u^{-5} = (1+S)^5` is above `S` — and `Gsq` taken to saturate (4.2).  It is *not* the regime
of the paper (there `A_u → ∞`); it only certifies that the six hypotheses are jointly
satisfiable for the **concrete** `eeL6`, which is what could have broken when `L^{(1)}` stopped
being a parameter. -/
theorem ee_hyp_consistent (X : Sample B) (E : ℝ) {n N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2)))
    (a₁ a₂ : ZMod (B.L N)) :
    ∃ (ℓu ℓs ηu D J μ ρ : ℝ) (Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ),
      1 ≤ ℓu ∧ 0 < ℓs ∧ 0 < ηu ∧ 1 ≤ J ∧ 0 ≤ μ ∧ 0 ≤ ρ ∧ (∀ x y, 0 ≤ Gsq x y) ∧
      (∀ b, eeL6 X E N u ω σ c b
        ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2
            * ((B.W N : ℝ) * ℓu * ηu)⁻¹) ∧
      (∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
        eeL6 X E N u ω σ c b ≤ ρ) ∧
      (∀ x y : ZMod (B.L N), ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) ∧
      (∀ b, eeL6 X E N u ω σ c b ≤ Gsq a₁ a₂ * Gsq b a₂ * μ) ∧
      (∀ b, ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (a₁ - b) : ℝ) →
        eeL6 X E N u ω σ c b
          ≤ Gsq a₁ a₂ * Gsq b a₂ * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - b)))) ∧
      ((∑ b ∈ Finset.univ.filter (fun b : ZMod (B.L N) =>
          ¬ ((zdist (B.L N) (a₁ - b) : ℝ) ≤ (zdist (B.L N) (a₂ - b) : ℝ))),
            eeL6 X E N u ω σ c b) ≤
        ((2 * ellStar (B.W N : ℝ) ℓu + 2) * (J ^ 2 * Lemma57.loss1 (B.W N : ℝ) * μ)
          + J ^ 3 * (36 * ℓu * (((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹
            + (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (a₁ - a₂)) ^ 2) := by
  classical
  set W : ℝ := (B.W N : ℝ) with hWdef
  have hW1 : 1 ≤ W := one_le_W B N
  have hW0 : 0 < W := by linarith
  set S : ℝ := ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => eeL6_nonneg X E N u ω σ c b
  have hSb : ∀ b : ZMod (B.L N), eeL6 X E N u ω σ c b ≤ S := fun b =>
    Finset.single_le_sum (fun b _ => eeL6_nonneg X E N u ω σ c b) (Finset.mem_univ b)
  set ηu : ℝ := 1 / (W * (1 + S)) with hηdef
  have hη0 : 0 < ηu := by rw [hηdef]; positivity
  have hA : W * 1 * ηu = (1 + S)⁻¹ := by rw [hηdef]; field_simp
  have hA0 : (0 : ℝ) < W * 1 * ηu := by rw [hA]; positivity
  -- the `D = 0` floor of the tail function is `1`
  have hW0rpow : W ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
  have hT1 : ∀ d : ℝ, 1 ≤ tailT W 1 ηu 0 d := by
    intro d
    have h1 : (0 : ℝ) ≤ ((W * 1 * ηu) ^ 2)⁻¹ * Real.exp (-Real.sqrt (d / 1)) := by positivity
    rw [tailT, hW0rpow]; linarith
  have hp1 : (1 : ℝ) ≤ 1 + S := by linarith
  -- `Gsq` saturates (4.2); each factor is `≥ 1` because the `D = 0` tail floor is `1`
  have hfac : ∀ x : ℝ, 1 ≤ x → (1 : ℝ) ≤ (1 + S) * x := by
    intro x hx; nlinarith
  have hprod2 : ∀ x y : ℝ, 1 ≤ x → 1 ≤ y → (1 : ℝ) ≤ ((1 + S) * x) * ((1 + S) * y) := by
    intro x y hx hy
    have h1 := hfac x hx
    have h2 := hfac y hy
    nlinarith
  refine ⟨1, 1, ηu, 0, 1 + S, 1 + S, S,
    fun x y => (1 + S) * tailT W 1 ηu 0 (zdist (B.L N) (x - y)), le_refl 1, one_pos, hη0,
    by linarith, by linarith, hS0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have := hT1 ((zdist (B.L N) (x - y) : ℝ))
    nlinarith
  · -- (2.73): the budget is `A_u^{-5} = (1 + S)^5`
    intro b
    have hbudget : ((1 : ℝ) / 1) ^ 5 * (((W * 1 * ηu) ^ 2)⁻¹) ^ 2 * (W * 1 * ηu)⁻¹
        = (1 + S) ^ 5 := by
      rw [hA]; field_simp
    have h5 : (1 : ℝ) + S ≤ (1 + S) ^ 5 := by
      calc (1 : ℝ) + S = (1 + S) ^ 1 := (pow_one _).symm
        _ ≤ (1 + S) ^ 5 := pow_le_pow_right₀ hp1 (by norm_num)
    rw [hbudget]
    linarith [hSb b]
  · exact fun b _ => hSb b
  · exact fun x y _ => le_refl _
  · -- (5.66): the product of the two saturated `Gsq` is at least `1`, and `μ = 1 + S ≥ S`
    intro b
    have t1 := hT1 ((zdist (B.L N) (a₁ - a₂) : ℝ))
    have t2 := hT1 ((zdist (B.L N) (b - a₂) : ℝ))
    have h := mul_le_mul_of_nonneg_right (hprod2 _ _ t1 t2) (by linarith : (0 : ℝ) ≤ 1 + S)
    linarith [hSb b, h]
  · -- (5.72): the same, with `μ` replaced by `J T_{u,0}(‖a₁-b‖) ≥ 1 + S`
    intro b _
    have t1 := hT1 ((zdist (B.L N) (a₁ - a₂) : ℝ))
    have t2 := hT1 ((zdist (B.L N) (b - a₂) : ℝ))
    have t3 := hT1 ((zdist (B.L N) (a₁ - b) : ℝ))
    have hbig : (1 : ℝ) + S ≤ (1 + S) * tailT W 1 ηu 0 (zdist (B.L N) (a₁ - b)) := by
      nlinarith
    have h := mul_le_mul_of_nonneg_right (hprod2 _ _ t1 t2)
      (by linarith : (0 : ℝ) ≤ (1 + S) * tailT W 1 ηu 0 (zdist (B.L N) (a₁ - b)))
    linarith [hSb b, h, hbig]
  · -- the `k = 2` half is bounded by `S`, and the right-hand side is at least `L ≥ 3`
    have hsub : (∑ b ∈ Finset.univ.filter (fun b : ZMod (B.L N) =>
        ¬ ((zdist (B.L N) (a₁ - b) : ℝ) ≤ (zdist (B.L N) (a₂ - b) : ℝ))),
          eeL6 X E N u ω σ c b) ≤ S := by
      rw [hSdef]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun b _ _ => eeL6_nonneg X E N u ω σ c b
    have hstar : 0 ≤ ellStar W 1 := by
      unfold ellStar; have := Real.log_nonneg hW1; positivity
    have hloss : 0 ≤ Lemma57.loss1 W := le_of_lt (Lemma57.loss1_pos W)
    have hL3 : (3 : ℝ) ≤ (B.L N : ℝ) := by exact_mod_cast B.three_le_L N
    have hinv : (0 : ℝ) ≤ (((W * 1 * ηu) ^ 2)⁻¹) := by positivity
    have hT := hT1 ((zdist (B.L N) (a₁ - a₂) : ℝ))
    set Q : ℝ := (2 * ellStar W 1 + 2) * ((1 + S) ^ 2 * Lemma57.loss1 W * (1 + S))
        + (1 + S) ^ 3 * (36 * 1 * (((W * 1 * ηu) ^ 2)⁻¹) + (B.L N : ℝ) * W ^ (-(0 : ℝ)))
      with hQdef
    have hcube0 : (0 : ℝ) ≤ (1 + S) ^ 3 := by positivity
    have hcube : (1 : ℝ) + S ≤ (1 + S) ^ 3 := by
      calc (1 : ℝ) + S = (1 + S) ^ 1 := (pow_one _).symm
        _ ≤ (1 + S) ^ 3 := pow_le_pow_right₀ hp1 (by norm_num)
    have h1 : (0 : ℝ) ≤ (2 * ellStar W 1 + 2) * ((1 + S) ^ 2 * Lemma57.loss1 W * (1 + S)) := by
      positivity
    have h2 : S ≤ (1 + S) ^ 3 * ((B.L N : ℝ) * W ^ (-(0 : ℝ))) := by
      rw [hW0rpow, mul_one]
      have h3 : (1 + S) ^ 3 * 3 ≤ (1 + S) ^ 3 * (B.L N : ℝ) :=
        mul_le_mul_of_nonneg_left hL3 hcube0
      linarith
    have h3 : (0 : ℝ) ≤ (1 + S) ^ 3 * (36 * 1 * (((W * 1 * ηu) ^ 2)⁻¹)) := by positivity
    have hexp : (1 + S) ^ 3 * (36 * 1 * (((W * 1 * ηu) ^ 2)⁻¹) + (B.L N : ℝ) * W ^ (-(0 : ℝ)))
        = (1 + S) ^ 3 * (36 * 1 * (((W * 1 * ηu) ^ 2)⁻¹))
          + (1 + S) ^ 3 * ((B.L N : ℝ) * W ^ (-(0 : ℝ))) := by ring
    have hQS : S ≤ Q := by rw [hQdef, hexp]; linarith
    have hQ0 : (0 : ℝ) ≤ Q := le_trans hS0 hQS
    have hTsq : (1 : ℝ) ≤ tailT W 1 ηu 0 (zdist (B.L N) (a₁ - a₂)) ^ 2 := by nlinarith
    exact hsub.trans (le_trans hQS (le_mul_of_one_le_right hQ0 hTsq))

end Main


/-! ### (5.65)-(5.66) and (5.72) for the glued `6`-loop (T178)

`RBM.EEDef.eeL6` is by *definition* the sum over `k ∈ range m` of (5.22).  At `m = 2` — the
`2`-loop that (5.36) is about — that sum has the two terms of Figure 14, and
`RBM.EEDef.glueIdx_two_zero` / `glueIdx_two_one` compute them: the glued `(2n+2)`-loop of
(5.23) is the explicit `6`-loop

`k = 1 :  ⟨[σ₂, σ₁, σ₂, -σ₂, -σ₁, -σ₂], [a₂, a₁, b, a₁', a₂', b']⟩`
`k = 0 :  ⟨[σ₁, σ₂, σ₁, -σ₁, -σ₂, -σ₁], [a₁, a₂, b, a₂', a₁', b']⟩`

with `a₁ = leftArg c 0`, `a₂ = leftArg c 1`, `aᵢ' = rightArg c (i-1)`.  Feeding these to
`RBM.Lemma57.norm_gloop_six_le_schwarz` (= (5.65) + (5.66)) and
`RBM.Lemma57.norm_gloop_six_le_glue` (= (5.65) + (5.72)) gives the four estimates below.

## ⚠ What this says about the hypothesis `h566` of `RBM.EEDef.ee_le_EEpath`

Compare `eeL6k_two_one_le` with `eeL6k_two_zero_le`.  The two `G`-edges that touch the glue
label `b'` join it to **`a₂`** at `k = 1` and to **`a₁`** at `k = 0`; everything else is the
same.  `h566`'s right-hand side `Gsq a₁ a₂ * Gsq b a₂ * μ` is the `k = 1` pattern.

At the place where `RBM.Lemma57.case2a_pointwise` consumes `h566` — `‖a₁ - b‖ ≤ ℓ*_u` while
`‖a₁ - a₂‖ ≥ 4ℓ*_u` — the two patterns are *not* comparable: `Gsq b a₂` is forced small by
`h42sq` ((4.2)+(5.31), which applies because `‖b - a₂‖ ≥ 3ℓ*_u`), whereas the `k = 0`
summand's `Gsq b a₁` has no decay at all there, `b` being inside `I`'s own `ℓ*_u`-neighbourhood
of `a₁`.  So `h566`, as a statement about `eeL6` (the full `k`-sum), is **not** provable from
(5.65)/(5.66); it is provable for the `k = 1` summand, which is `eeL6k_two_one_le`.

This is `docs/paper-deltas.md` #113 ② seen from the other side: the `k = 0` summand *is* the
half that `hsym` is about, so `h566` and `hsym` are not independent hypotheses — discharging
`h566` for `eeL6` needs exactly the `k`-split that `hsym` needs.  Nothing here overturns the
recorded finding; it makes the `k`-dependence of the shape visible in Lean.

`h572` is different, and the two glue lemmas below show why: there the glued factor
`G(σ)E_bG(-σ)` is *also* bounded by a tail function rather than by Cauchy-Schwarz, and at
`k = 0` the pair `(edges to a₁, glue factor at a₂)` replaces `k = 1`'s
`(edges to a₂, glue factor at a₁)` — the same product `T_{u,D}(‖b-a₁‖) T_{u,D}(‖b-a₂‖)`.  Both
summands therefore satisfy the shape of `h572`, provided the caller's `Gsq` saturates (4.2)
(i.e. `Gsq x y = J*_{u,D} T_{u,D}(‖x-y‖)`); with a general `Gsq` the `k = 0` summand needs a
*lower* bound on `Gsq b a₂`, which `h42sq` does not give.
-/

section Six

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The `k`-th summand of `RBM.EEDef.eeL6`, i.e. the `k`-th term of the `k`-sum of (5.22). -/
noncomputable def eeL6k (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (k : ℕ) (b : ZMod (B.L N)) : ℝ :=
  ∑ b' : ZMod (B.L N),
    ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) k b b')‖

theorem eeL6_eq_sum_eeL6k (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (b : ZMod (B.L N)) :
    eeL6 X E N u ω σ c b = ∑ k ∈ Finset.range m, eeL6k X E N u ω σ c k b := rfl

theorem eeL6k_nonneg (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) (k : ℕ) (b : ZMod (B.L N)) :
    0 ≤ eeL6k X E N u ω σ c k b := by
  unfold eeL6k; positivity

/-- At `m = 2` — the `2`-loop of (5.36) — the `k`-sum of (5.22) has exactly the two terms of
Figure 14. -/
theorem eeL6_two_eq (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2)) (b : ZMod (B.L N)) :
    eeL6 X E N u ω σ c b = eeL6k X E N u ω σ c 0 b + eeL6k X E N u ω σ c 1 b := by
  rw [eeL6_eq_sum_eeL6k, Finset.sum_range_succ, Finset.sum_range_one]

/-! ### (5.23) at `n = 0`: the two glued `6`-loops of Figure 14 -/

/-- **Figure 14, right (`k = 0`)**: cutting the first edge of the `2`-loop. -/
theorem glueIdx_two_zero {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) :
    glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b'
      = ⟨[σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)],
         [leftArg c 0, leftArg c 1, b, rightArg c 1, rightArg c 0, b']⟩ := by
  simp [glueIdx, cutPairs, pairs, pairAt, ofPairs, LoopData.idx, List.ofFn_succ]

/-- **Figure 14, left (`k = 1`)**: cutting the second edge of the `2`-loop. -/
theorem glueIdx_two_one {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2))
    (b b' : ZMod L) :
    glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b'
      = ⟨[σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)],
         [leftArg c 1, leftArg c 0, b, rightArg c 0, rightArg c 1, b']⟩ := by
  simp [glueIdx, cutPairs, pairs, pairAt, ofPairs, LoopData.idx, List.ofFn_succ]


/-! ### (5.65) + (5.66) for the two glued `6`-loops -/

variable (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)

/-- **(5.65) + (5.66) for the `k = 1` term of (5.22)** (Figure 14, left).

The four `G`-edges of (5.65) are `(a₁', a₂')`, `(a₂', b')`, `(b', a₂)`, `(a₂, a₁)`, so the two
edges that touch the glue label `b'` are attached to `a₂`; `S` bounds the `4`-loop
`L_{(σ₂,-σ₂,σ₂,-σ₂),(b,a₁',b,a₁)}` of (5.66), which is what (2.73) at `n = 4` estimates. -/
theorem norm_gloop_glue_two_one_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 1, !(σ 1), σ 1, !(σ 1)], [b, rightArg c 0, b, leftArg c 0]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
      ≤ Gm (rightArg c 0) (rightArg c 1) * Gm (rightArg c 1) b'
        * Gm b' (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0) * √S := by
  rw [glueIdx_two_one]
  exact Lemma57.norm_gloop_six_le_schwarz (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 1) (σ 0) (σ 1) (!(σ 0)) (!(σ 1))
    (leftArg c 1) (leftArg c 0) b (rightArg c 0) (rightArg c 1) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS

/-- **(5.65) + (5.66) for the `k = 0` term of (5.22)** (Figure 14, right).

Identical to `norm_gloop_glue_two_one_le` except that the two `G`-edges that touch the glue
label `b'` are now attached to `a₁`, not `a₂`, and the `4`-loop of (5.66) is the one with
`a₂'`, `a₂` in place of `a₁'`, `a₁`.  This swap is the whole content of the `k = 1`/`k = 2`
symmetry of Figure 14. -/
theorem norm_gloop_glue_two_zero_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 0, !(σ 0), σ 0, !(σ 0)], [b, rightArg c 1, b, leftArg c 1]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
      ≤ Gm (rightArg c 1) (rightArg c 0) * Gm (rightArg c 0) b'
        * Gm b' (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1) * √S := by
  rw [glueIdx_two_zero]
  exact Lemma57.norm_gloop_six_le_schwarz (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 0) (σ 1) (σ 0) (!(σ 1)) (!(σ 0))
    (leftArg c 0) (leftArg c 1) b (rightArg c 1) (rightArg c 0) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS


/-! ### The `b'`-sum: (5.66) for the two summands of `eeL6` -/

/-- **(5.66) for the `k = 1` summand of `RBM.EEDef.eeL6`.**

The `b'`-sum is against `‖S^{(B)}_{bb'}‖`, whose row sums are `1`, so a bound `Kb` on the
product of the two `b'`-edges, valid on the (three-point) support of that row, passes through
unchanged.  `Kb` is the paper's `T_{u,D}(‖b - a₂‖)`-carrying factor of (5.67). -/
theorem eeL6k_two_one_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 1) b' * Gm b' (leftArg c 1) ≤ Kb)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 1, !(σ 1), σ 1, !(σ 1)], [b, rightArg c 0, b, leftArg c 0]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * √S := by
  classical
  set C : ℝ := Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * √S
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_gloop_glue_two_one_le X E N u ω σ c b b' hGm0 hGm hS).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have h2 : (0 : ℝ) ≤ √S := Real.sqrt_nonneg S
      have h3 := hGm0 (rightArg c 0) (rightArg c 1)
      have h4 := hGm0 (leftArg c 1) (leftArg c 0)
      have hexp : Gm (rightArg c 0) (rightArg c 1) * Gm (rightArg c 1) b'
          * Gm b' (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0) * √S
          = Gm (rightArg c 0) (rightArg c 1) * (Gm (rightArg c 1) b' * Gm b' (leftArg c 1))
            * Gm (leftArg c 1) (leftArg c 0) * √S := by ring
      rw [hexp]
      gcongr
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-- **(5.66) for the `k = 0` summand of `RBM.EEDef.eeL6`** — the mirror image, with the two
`b'`-edges attached to `a₁`. -/
theorem eeL6k_two_zero_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 0) b' * Gm b' (leftArg c 0) ≤ Kb)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 0, !(σ 0), σ 0, !(σ 0)], [b, rightArg c 1, b, leftArg c 1]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * √S := by
  classical
  set C : ℝ := Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * √S
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_gloop_glue_two_zero_le X E N u ω σ c b b' hGm0 hGm hS).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have h2 : (0 : ℝ) ≤ √S := Real.sqrt_nonneg S
      have h3 := hGm0 (rightArg c 1) (rightArg c 0)
      have h4 := hGm0 (leftArg c 0) (leftArg c 1)
      have hexp : Gm (rightArg c 1) (rightArg c 0) * Gm (rightArg c 0) b'
          * Gm b' (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1) * √S
          = Gm (rightArg c 1) (rightArg c 0) * (Gm (rightArg c 0) b' * Gm b' (leftArg c 0))
            * Gm (leftArg c 0) (leftArg c 1) * √S := by ring
      rw [hexp]
      gcongr
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]


/-! ### (5.65) + (5.72): the Case-2(1b) route, with `G†E_bG` bounded entrywise -/

/-- **(5.72) for the `k = 1` summand of `RBM.EEDef.eeL6`.**

`K` bounds the glued factor `(G(σ₂)E_bG(-σ₂))_{x₁x₁'}` entrywise, via
`RBM.Lemma57.norm_mul_Eblk_mul_apply_le` — that is the paper's
`(G†E_bG)_{x₁x₁'} ≤ max_{y∈I_b}|G_{x₁y}||G_{x₁'y}|` followed by (4.2)+(5.31).  At `k = 1`
the free ends of that factor lie in the blocks `a₁`, `a₁'`, so `K` is the paper's
`J*_{u,D} T_{u,D}(‖b - a₁‖)`. -/
theorem eeL6k_two_one_le_glue (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb K : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y) (hK : 0 ≤ K)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 1) b' * Gm b' (leftArg c 1) ≤ Kb)
    (hglue : ∀ p q y : ZMod (B.L N) × Fin (B.W N),
      p.1 = leftArg c 0 → q.1 = rightArg c 0 → y.1 = b →
      ‖Gsig (X.H N u ω) (zt E u) (σ 1) p y‖
        * ‖Gsig (X.H N u ω) (zt E u) (!(σ 1)) y q‖ ≤ K) :
    eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * K := by
  classical
  set C : ℝ := Gm (rightArg c 0) (rightArg c 1) * Kb * Gm (leftArg c 1) (leftArg c 0) * K
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [glueIdx_two_one]
      refine (Lemma57.norm_gloop_six_le_glue (B.L N) (B.W N)
        (σ 1) (σ 0) (σ 1) (!(σ 1)) (!(σ 0)) (!(σ 1))
        (leftArg c 1) (leftArg c 0) b (rightArg c 0) (rightArg c 1) b'
        (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) hK
        (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
        (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp)
        (fun p q y hp hq hy => hglue p q y hp hq hy)).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have hexp : Gm (rightArg c 0) (rightArg c 1) * Gm (rightArg c 1) b'
          * Gm b' (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0) * K
          = Gm (rightArg c 0) (rightArg c 1) * (Gm (rightArg c 1) b' * Gm b' (leftArg c 1))
            * Gm (leftArg c 1) (leftArg c 0) * K := by ring
      rw [hexp]
      gcongr <;> exact hGm0 _ _
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-- **(5.72) for the `k = 0` summand of `RBM.EEDef.eeL6`** — the mirror image: the free ends
of the glued factor lie in the blocks `a₂`, `a₂'`, so `K` is `J*_{u,D} T_{u,D}(‖b - a₂‖)`
while the `b'`-edges carry `‖b - a₁‖`.  The *product* of the two is the same as at `k = 1`,
which is why `h572` — unlike `h566` — has a shape that both summands of (5.22) satisfy. -/
theorem eeL6k_two_zero_le_glue (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb K : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y) (hK : 0 ≤ K)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb' : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 0) b' * Gm b' (leftArg c 0) ≤ Kb)
    (hglue : ∀ p q y : ZMod (B.L N) × Fin (B.W N),
      p.1 = leftArg c 1 → q.1 = rightArg c 1 → y.1 = b →
      ‖Gsig (X.H N u ω) (zt E u) (σ 0) p y‖
        * ‖Gsig (X.H N u ω) (zt E u) (!(σ 0)) y q‖ ≤ K) :
    eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * K := by
  classical
  set C : ℝ := Gm (rightArg c 1) (rightArg c 0) * Kb * Gm (leftArg c 0) (leftArg c 1) * K
    with hC
  have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
      ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
        ≤ ‖SB (B.L N) b b'‖ * C := by
    intro b' _
    by_cases h0 : SB (B.L N) b b' = 0
    · simp [h0]
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [glueIdx_two_zero]
      refine (Lemma57.norm_gloop_six_le_glue (B.L N) (B.W N)
        (σ 0) (σ 1) (σ 0) (!(σ 0)) (!(σ 1)) (!(σ 0))
        (leftArg c 0) (leftArg c 1) b (rightArg c 1) (rightArg c 0) b'
        (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) hK
        (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
        (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp)
        (fun p q y hp hq hy => hglue p q y hp hq hy)).trans ?_
      rw [hC]
      have h1 := hb' b' h0
      have hexp : Gm (rightArg c 1) (rightArg c 0) * Gm (rightArg c 0) b'
          * Gm b' (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1) * K
          = Gm (rightArg c 1) (rightArg c 0) * (Gm (rightArg c 0) b' * Gm b' (leftArg c 0))
            * Gm (leftArg c 0) (leftArg c 1) * K := by ring
      rw [hexp]
      gcongr <;> exact hGm0 _ _
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]


/-! ### The two summands together -/

/-- **(5.22) + (5.65) + (5.66) at `n = 0`**: both terms of the `k`-sum.

Adding `eeL6k_two_zero_le` and `eeL6k_two_one_le`.  The two bounds are *not* the same
expression: at `k = 1` the factor `Kb₁` controls the pair of `G`-edges joining the glue label
`b'` to `a₂ = leftArg c 1`, at `k = 0` the pair joining `b'` to `a₁ = leftArg c 0`. -/
theorem eeL6_two_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Kb₀ Kb₁ S₀ S₁ : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hb'₀ : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 0) b' * Gm b' (leftArg c 0) ≤ Kb₀)
    (hb'₁ : ∀ b' : ZMod (B.L N), SB (B.L N) b b' ≠ 0 →
      Gm (rightArg c 1) b' * Gm b' (leftArg c 1) ≤ Kb₁)
    (hS₀ : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 0, !(σ 0), σ 0, !(σ 0)], [b, rightArg c 1, b, leftArg c 1]⟩).re ≤ S₀)
    (hS₁ : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[σ 1, !(σ 1), σ 1, !(σ 1)], [b, rightArg c 0, b, leftArg c 0]⟩).re ≤ S₁) :
    eeL6 X E N u ω σ c b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Kb₀ * Gm (leftArg c 0) (leftArg c 1) * √S₀
        + Gm (rightArg c 0) (rightArg c 1) * Kb₁ * Gm (leftArg c 1) (leftArg c 0) * √S₁ := by
  rw [eeL6_two_eq]
  exact add_le_add (eeL6k_two_zero_le X E N u ω σ c b hGm0 hGm hb'₀ hS₀)
    (eeL6k_two_one_le X E N u ω σ c b hGm0 hGm hb'₁ hS₁)

end Six

/-! ### T190: the second cut, and (5.36) with `h566` *and* `hsym` both discharged

The `6`-loop of (5.23) has **two** glue labels, `b` and `b'`.  The section above opens it at
`b`; `RBM.Lemma57.norm_gloop_six_le_schwarz'` opens it at `b'`, and the two openings leave
*different* four-edge products behind:

| term | cut | the four surviving edges | glued pair |
|---|---|---|---|
| `k = 1` | `b`  | `a₁'–a₂'`, `a₂'–b'`, `b'–a₂`, `a₂–a₁` | `a₁–b–a₁'` |
| `k = 1` | `b'` | `a₂–a₁`, `a₁–b`, `b–a₁'`, `a₁'–a₂'` | `a₂'–b'–a₂` |
| `k = 0` | `b`  | `a₂'–a₁'`, `a₁'–b'`, `b'–a₁`, `a₁–a₂` | `a₂–b–a₂'` |
| `k = 0` | `b'` | `a₁–a₂`, `a₂–b`, `b–a₂'`, `a₂'–a₁'` | `a₁'–b'–a₁` |

In the `k = 1` loop the label `b` meets only `a₁`-blocks and `b'` only `a₂`-blocks; in the
`k = 0` loop it is the other way round.  That is the exact content of the `k=1`/`k=2`
symmetry of Figure 14, and it is why T178's obstruction dissolves:

* for `b` near `a₁` (so far from `a₂`) the pair of `G`-edges that decays is the one joining
  the glue label to `a₂`, which is the `b'`-pair at `k = 1` (cut at `b`) and the `b`-pair at
  `k = 0` (**cut at `b'`**);
* for `b` near `a₂` the mirror image: cut `k = 0` at `b` and `k = 1` at `b'`.

Both halves therefore land on the *same* shape `Gsq(a₁,a₂)·Gsq(b,aᵢ)·μ`, with `i = 2` on the
first half and `i = 1` on the second — the two hypotheses `hnear₁`, `hnear₂` of
`RBM.Lemma57.ee_le_sym`.  For `b` far from both labels either cut works and the product of
the four edges with the glued pair is symmetric, which is T178's observation about `h572`.

**The outcome is symmetric in the two labels**, as expected: nothing is short.  What the
argument costs beyond T178's machinery is one hypothesis, `hrow` below — the paper's "we can
treat `b = b'` for all practical purposes" — which is needed because in each loop one of the
two glue labels is reached only through `b'`.  `docs/paper-deltas.md` #113 ① already records
the `b' = b` identification; `hrow` is that identification made into an explicit hypothesis
rather than a silent step.
-/

section SixSym

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
variable (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)

/-- **(5.65) + (5.66) for the `k = 1` term of (5.22), cut at the second glue label `b'`**
(Figure 14, left, opened at the other side).  The four surviving `G`-edges are
`a₂–a₁`, `a₁–b`, `b–a₁'`, `a₁'–a₂'`, and the `4`-loop of (5.66) is the one on `b'` and the
`a₂`-blocks.  Compare `norm_gloop_glue_two_one_le`, which cuts at `b`. -/
theorem norm_gloop_glue_two_one'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 1), σ 1, !(σ 1), σ 1], [b', leftArg c 1, b', rightArg c 1]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 1 b b')‖
      ≤ Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b
        * Gm b (rightArg c 0) * Gm (rightArg c 0) (rightArg c 1) * √S := by
  rw [glueIdx_two_one]
  exact Lemma57.norm_gloop_six_le_schwarz' (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 1) (σ 0) (σ 1) (!(σ 1)) (!(σ 0))
    (leftArg c 1) (leftArg c 0) b (rightArg c 0) (rightArg c 1) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS

/-- **(5.65) + (5.66) for the `k = 0` term of (5.22), cut at the second glue label `b'`**
(Figure 14, right, opened at the other side).  The four surviving `G`-edges are
`a₁–a₂`, `a₂–b`, `b–a₂'`, `a₂'–a₁'`: they carry the pair `b–a₂` *directly*, with no `b'` in
it, which is what the half `‖b-a₁‖ ≤ ‖b-a₂‖` of the `b`-sum needs. -/
theorem norm_gloop_glue_two_zero'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b b' : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 0), σ 0, !(σ 0), σ 0], [b', leftArg c 0, b', rightArg c 0]⟩).re ≤ S) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (glueIdx (toIdx σ (leftArg c)) (toIdx σ (rightArg c)) 0 b b')‖
      ≤ Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b
        * Gm b (rightArg c 1) * Gm (rightArg c 1) (rightArg c 0) * √S := by
  rw [glueIdx_two_zero]
  exact Lemma57.norm_gloop_six_le_schwarz' (B.L N) (B.W N) (X.hermitian N u ω)
    (σ 0) (σ 1) (σ 0) (!(σ 0)) (!(σ 1))
    (leftArg c 0) (leftArg c 1) b (rightArg c 1) (rightArg c 0) b'
    (hGm0 _ _) (hGm0 _ _) (hGm0 _ _) (hGm0 _ _)
    (fun q p hq hp => hGm _ _ _ q p hq hp) (fun p r hp hr => hGm _ _ _ p r hp hr)
    (fun r t hr ht => hGm _ _ _ r t hr ht) (fun t p ht hp => hGm _ _ _ t p ht hp) hS

/-! ### The `b'`-sum for the second cut

When the loop is cut at `b'` the four surviving `G`-edges do **not** involve `b'` at all, so
the `b'`-sum against `‖S^{(B)}_{bb'}‖` only has to absorb the `4`-loop of (5.66); a bound `S`
uniform in `b'` passes straight through the row sum `∑_{b'} ‖S^{(B)}_{bb'}‖ = 1`. -/

/-- **(5.66) for the `k = 1` summand of `RBM.EEDef.eeL6`, cut at `b'`.** -/
theorem eeL6k_two_one'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : ∀ b' : ZMod (B.L N), (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 1), σ 1, !(σ 1), σ 1], [b', leftArg c 1, b', rightArg c 1]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 1 b
      ≤ Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b
        * Gm b (rightArg c 0) * Gm (rightArg c 0) (rightArg c 1) * √S := by
  classical
  refine (Finset.sum_le_sum (fun b' _ => mul_le_mul_of_nonneg_left
    (norm_gloop_glue_two_one'_le X E N u ω σ c b b' hGm0 hGm (hS b'))
    (norm_nonneg (SB (B.L N) b b')))).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-- **(5.66) for the `k = 0` summand of `RBM.EEDef.eeL6`, cut at `b'`.** -/
theorem eeL6k_two_zero'_le (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm : ZMod (B.L N) → ZMod (B.L N) → ℝ} {S : ℝ}
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hS : ∀ b' : ZMod (B.L N), (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[!(σ 0), σ 0, !(σ 0), σ 0], [b', leftArg c 0, b', rightArg c 0]⟩).re ≤ S) :
    eeL6k X E N u ω σ c 0 b
      ≤ Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b
        * Gm b (rightArg c 1) * Gm (rightArg c 1) (rightArg c 0) * √S := by
  classical
  refine (Finset.sum_le_sum (fun b' _ => mul_le_mul_of_nonneg_left
    (norm_gloop_glue_two_zero'_le X E N u ω σ c b b' hGm0 hGm (hS b'))
    (norm_nonneg (SB (B.L N) b b')))).trans ?_
  rw [← Finset.sum_mul, RBM.sum_norm_SB_row (B.three_le_L N) b, one_mul]

/-! ### The two halves of the `b`-sum, on `RBM.EEDef.eeL6` itself

`hrow` below is the paper's `b = b'`: in each of the two loops of Figure 14 one of the glue
labels is reached only through `b'`, so the pair of `G`-edges meeting it is
`Gm x b' · Gm b' x`, and the estimate needs it controlled by the `b`-indexed quantity the
`b`-sum is about.  `hSmax` is (2.73) at `n = 4`, uniform over the four `4`-loops that the two
cuts produce. -/

/-- **Case 2(1a) for `b` near `a₁`**, for *both* terms of (5.22): `k = 1` cut at `b`,
`k = 0` cut at `b'`.  This is the hypothesis `hnear₁` of `RBM.Lemma57.ee_le_sym`, and it is
`h566` at the granularity at which T178 showed it to be true — except that the `k = 0`
summand is now taken apart at the *other* glue label, which is what T178 was missing. -/
theorem eeL6_two_le_near₁ (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax : ℝ}
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax) :
    eeL6 X E N u ω σ c b
      ≤ Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * (2 * √Smax) := by
  classical
  have hs0 : (0 : ℝ) ≤ √Smax := Real.sqrt_nonneg _
  have h1 : eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Gsq b (leftArg c 1)
        * Gm (leftArg c 1) (leftArg c 0) * √Smax :=
    eeL6k_two_one_le X E N u ω σ c b hGm0 hGm
      (fun b' h0 => by rw [hc1]; exact hrow (leftArg c 1) b b' h0)
      (hSmax (σ 1) b (rightArg c 0) (leftArg c 0))
  have h0 : eeL6k X E N u ω σ c 0 b
      ≤ Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b
        * Gm b (rightArg c 1) * Gm (rightArg c 1) (rightArg c 0) * √Smax :=
    eeL6k_two_zero'_le X E N u ω σ c b hGm0 hGm
      (fun b' => by simpa using hSmax (!(σ 0)) b' (leftArg c 0) (rightArg c 0))
  have hA : Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0)
      ≤ Gsq (leftArg c 0) (leftArg c 1) := hGsq2 _ _
  have hB : Gm (leftArg c 1) b * Gm b (leftArg c 1) ≤ Gsq b (leftArg c 1) := by
    calc Gm (leftArg c 1) b * Gm b (leftArg c 1)
        = Gm b (leftArg c 1) * Gm (leftArg c 1) b := mul_comm _ _
      _ ≤ Gsq b (leftArg c 1) := hGsq2 b (leftArg c 1)
  have s1 : eeL6k X E N u ω σ c 1 b
      ≤ Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by
    refine h1.trans ?_
    rw [hc0, hc1]
    have hstep : (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
        * (Gsq b (leftArg c 1) * √Smax)
        ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg (hGsq0 _ _) hs0)
    calc Gm (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1)
          * Gm (leftArg c 1) (leftArg c 0) * √Smax
        = (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
            * (Gsq b (leftArg c 1) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) := hstep
      _ = Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by ring
  have s0 : eeL6k X E N u ω σ c 0 b
      ≤ Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by
    refine h0.trans ?_
    rw [hc1, hc0]
    have hstep : (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
        * ((Gm (leftArg c 1) b * Gm b (leftArg c 1)) * √Smax)
        ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) :=
      mul_le_mul hA (mul_le_mul_of_nonneg_right hB hs0)
        (mul_nonneg (mul_nonneg (hGm0 _ _) (hGm0 _ _)) hs0) (hGsq0 _ _)
    calc Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) b * Gm b (leftArg c 1)
          * Gm (leftArg c 1) (leftArg c 0) * √Smax
        = (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0))
            * ((Gm (leftArg c 1) b * Gm b (leftArg c 1)) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 0) (leftArg c 1) * (Gsq b (leftArg c 1) * √Smax) := hstep
      _ = Gsq (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1) * √Smax := by ring
  rw [eeL6_two_eq]
  exact (add_le_add s0 s1).trans (le_of_eq (by ring))

/-- **Case 2(1a) for `b` near `a₂`** — the mirror: `k = 0` cut at `b`, `k = 1` cut at `b'`.
This is `hnear₂` of `RBM.Lemma57.ee_le_sym`, i.e. the half the paper disposes of with "by
symmetry" and which T156 had to assume as `hsym`. -/
theorem eeL6_two_le_near₂ (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ} {Smax : ℝ}
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (hSmax : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax) :
    eeL6 X E N u ω σ c b
      ≤ Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * (2 * √Smax) := by
  classical
  have hs0 : (0 : ℝ) ≤ √Smax := Real.sqrt_nonneg _
  have h0 : eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Gsq b (leftArg c 0)
        * Gm (leftArg c 0) (leftArg c 1) * √Smax :=
    eeL6k_two_zero_le X E N u ω σ c b hGm0 hGm
      (fun b' hz => by rw [hc0]; exact hrow (leftArg c 0) b b' hz)
      (hSmax (σ 0) b (rightArg c 1) (leftArg c 1))
  have h1 : eeL6k X E N u ω σ c 1 b
      ≤ Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b
        * Gm b (rightArg c 0) * Gm (rightArg c 0) (rightArg c 1) * √Smax :=
    eeL6k_two_one'_le X E N u ω σ c b hGm0 hGm
      (fun b' => by simpa using hSmax (!(σ 1)) b' (leftArg c 1) (rightArg c 1))
  have hA : Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1)
      ≤ Gsq (leftArg c 1) (leftArg c 0) := hGsq2 _ _
  have hB : Gm (leftArg c 0) b * Gm b (leftArg c 0) ≤ Gsq b (leftArg c 0) := by
    calc Gm (leftArg c 0) b * Gm b (leftArg c 0)
        = Gm b (leftArg c 0) * Gm (leftArg c 0) b := mul_comm _ _
      _ ≤ Gsq b (leftArg c 0) := hGsq2 b (leftArg c 0)
  have s0 : eeL6k X E N u ω σ c 0 b
      ≤ Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by
    refine h0.trans ?_
    rw [hc1, hc0]
    have hstep : (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
        * (Gsq b (leftArg c 0) * √Smax)
        ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg (hGsq0 _ _) hs0)
    calc Gm (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0)
          * Gm (leftArg c 0) (leftArg c 1) * √Smax
        = (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
            * (Gsq b (leftArg c 0) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) := hstep
      _ = Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by ring
  have s1 : eeL6k X E N u ω σ c 1 b
      ≤ Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by
    refine h1.trans ?_
    rw [hc0, hc1]
    have hstep : (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
        * ((Gm (leftArg c 0) b * Gm b (leftArg c 0)) * √Smax)
        ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) :=
      mul_le_mul hA (mul_le_mul_of_nonneg_right hB hs0)
        (mul_nonneg (mul_nonneg (hGm0 _ _) (hGm0 _ _)) hs0) (hGsq0 _ _)
    calc Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) b * Gm b (leftArg c 0)
          * Gm (leftArg c 0) (leftArg c 1) * √Smax
        = (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1))
            * ((Gm (leftArg c 0) b * Gm b (leftArg c 0)) * √Smax) := by ring
      _ ≤ Gsq (leftArg c 1) (leftArg c 0) * (Gsq b (leftArg c 0) * √Smax) := hstep
      _ = Gsq (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0) * √Smax := by ring
  rw [eeL6_two_eq]
  exact (add_le_add s0 s1).trans (le_of_eq (by ring))

/-- **Case 2(1b) for `b` far from both labels**, for *both* terms of (5.22).  Here either cut
does; `eeL6k_two_one_le_glue` and `eeL6k_two_zero_le_glue` (the cut at `b`, T178) are used for
both, because the product of the four edges with the glued pair is the same
`T_{u,D}(‖a₁-a₂‖) T_{u,D}(‖a₁-b‖) T_{u,D}(‖a₂-b‖)` either way — T178's observation that
`h572`'s shape is symmetric in `k`.  The two summands cost a factor `2`, absorbed into
`(2J)³`. -/
theorem eeL6_two_le_far (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2))
    (b : ZMod (B.L N)) {ℓu ηu D J : ℝ}
    {Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ}
    (hℓu : 0 < ℓu) (hJ : 1 ≤ J)
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
    (hGm0 : ∀ x y, 0 ≤ Gm x y)
    (hGm : ∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
      p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y)
    (hGsq0 : ∀ x y, 0 ≤ Gsq x y)
    (hGsq2 : ∀ x y, Gm x y * Gm y x ≤ Gsq x y)
    (hrow : ∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
      Gm x bb' * Gm bb' x ≤ Gsq bb x)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)))
    (hfar : 4 * ellStar (B.W N : ℝ) ℓu
      ≤ (zdist (B.L N) (leftArg c 0 - leftArg c 1) : ℝ))
    (hb1 : ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (leftArg c 0 - b) : ℝ))
    (hb2 : ellStar (B.W N : ℝ) ℓu < (zdist (B.L N) (leftArg c 1 - b) : ℝ)) :
    eeL6 X E N u ω σ c b
      ≤ (2 * J) ^ 3
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
          * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by
  classical
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hstar : (0 : ℝ) ≤ ellStar (B.W N : ℝ) ℓu := by
    unfold ellStar; have := Real.log_nonneg hW; positivity
  have hT12 : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := tailT_nonneg hW0.le _
  have hT1b : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (leftArg c 0 - b)) := tailT_nonneg hW0.le _
  have hT2b : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D
      (zdist (B.L N) (leftArg c 1 - b)) := tailT_nonneg hW0.le _
  have hA12 : Gsq (leftArg c 0) (leftArg c 1)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1)) :=
    h42sq _ _ (by linarith)
  have hA21 : Gsq (leftArg c 1) (leftArg c 0)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := by
    have h := h42sq (leftArg c 1) (leftArg c 0)
      (by rw [Lemma57.zdist_sub_comm]; linarith)
    rwa [Lemma57.zdist_sub_comm] at h
  have hB1 : Gsq b (leftArg c 0)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)) := by
    have h := h42sq b (leftArg c 0) (by rw [Lemma57.zdist_sub_comm]; linarith)
    rwa [Lemma57.zdist_sub_comm] at h
  have hB2 : Gsq b (leftArg c 1)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)) := by
    have h := h42sq b (leftArg c 1) (by rw [Lemma57.zdist_sub_comm]; linarith)
    rwa [Lemma57.zdist_sub_comm] at h
  have hG1 : Gm (leftArg c 0) b * Gm b (leftArg c 0)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)) :=
    (hGsq2 _ _).trans (h42sq (leftArg c 0) b (by linarith))
  have hG2 : Gm (leftArg c 1) b * Gm b (leftArg c 1)
      ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)) :=
    (hGsq2 _ _).trans (h42sq (leftArg c 1) b (by linarith))
  have h1 : eeL6k X E N u ω σ c 1 b
      ≤ Gm (rightArg c 0) (rightArg c 1) * Gsq b (leftArg c 1)
        * Gm (leftArg c 1) (leftArg c 0)
        * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))) :=
    eeL6k_two_one_le_glue X E N u ω σ c b hGm0 (mul_nonneg hJ0 hT1b) hGm
      (fun b' hz => by rw [hc1]; exact hrow (leftArg c 1) b b' hz)
      (fun p q y hp hq hy => by
        rw [hc0] at hq
        exact (mul_le_mul (hGm (σ 1) (leftArg c 0) b p y hp hy)
          (hGm (!(σ 1)) b (leftArg c 0) y q hy hq) (norm_nonneg _) (hGm0 _ _)).trans hG1)
  have h0 : eeL6k X E N u ω σ c 0 b
      ≤ Gm (rightArg c 1) (rightArg c 0) * Gsq b (leftArg c 0)
        * Gm (leftArg c 0) (leftArg c 1)
        * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) :=
    eeL6k_two_zero_le_glue X E N u ω σ c b hGm0 (mul_nonneg hJ0 hT2b) hGm
      (fun b' hz => by rw [hc0]; exact hrow (leftArg c 0) b b' hz)
      (fun p q y hp hq hy => by
        rw [hc1] at hq
        exact (mul_le_mul (hGm (σ 0) (leftArg c 1) b p y hp hy)
          (hGm (!(σ 0)) b (leftArg c 1) y q hy hq) (norm_nonneg _) (hGm0 _ _)).trans hG2)
  have s1 : eeL6k X E N u ω σ c 1 b
      ≤ J ^ 3 * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
        * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by
    refine h1.trans ?_
    rw [hc0, hc1]
    have p1 : Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0)
        ≤ J * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := (hGsq2 _ _).trans hA12
    have q1 := mul_le_mul p1 hB2 (hGsq0 _ _) (mul_nonneg hJ0 hT12)
    have q2 := mul_le_mul_of_nonneg_right q1 (mul_nonneg hJ0 hT1b)
    calc Gm (leftArg c 0) (leftArg c 1) * Gsq b (leftArg c 1)
            * Gm (leftArg c 1) (leftArg c 0)
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b)))
        = (Gm (leftArg c 0) (leftArg c 1) * Gm (leftArg c 1) (leftArg c 0)
            * Gsq b (leftArg c 1))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))) := by ring
      _ ≤ (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))) := q2
      _ = _ := by ring
  have s0 : eeL6k X E N u ω σ c 0 b
      ≤ J ^ 3 * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
        * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by
    refine h0.trans ?_
    rw [hc1, hc0]
    have p1 : Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1)
        ≤ J * tailT (B.W N : ℝ) ℓu ηu D
            (zdist (B.L N) (leftArg c 0 - leftArg c 1)) := (hGsq2 _ _).trans hA21
    have q1 := mul_le_mul p1 hB1 (hGsq0 _ _) (mul_nonneg hJ0 hT12)
    have q2 := mul_le_mul_of_nonneg_right q1 (mul_nonneg hJ0 hT2b)
    calc Gm (leftArg c 1) (leftArg c 0) * Gsq b (leftArg c 0)
            * Gm (leftArg c 0) (leftArg c 1)
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)))
        = (Gm (leftArg c 1) (leftArg c 0) * Gm (leftArg c 0) (leftArg c 1)
            * Gsq b (leftArg c 0))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := by ring
      _ ≤ (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))))
            * (J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) := q2
      _ = _ := by ring
  have hP : (0 : ℝ) ≤ J ^ 3
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
      * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b))) :=
    mul_nonneg (mul_nonneg (pow_nonneg hJ0 3) hT12) (mul_nonneg hT1b hT2b)
  rw [eeL6_two_eq]
  have hsum := add_le_add s0 s1
  refine hsum.trans ?_
  have hexp : (2 * J) ^ 3
      * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
      * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)))
      = 8 * (J ^ 3
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - leftArg c 1))
        * (tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 0 - b))
          * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (leftArg c 1 - b)))) := by ring
  rw [hexp]
  linarith [hP]

/-! ### (5.36) for the pinned `E ⊗ E` with **no** `h566` and **no** `hsym` -/

/-- **(5.36) for `RBM.MomentDuhamel.EEpath` at loop length `2`, with `h566` and `hsym` both
discharged** (T190).

Compared with `RBM.EEDef.ee_le_EEpath_labels` the hypothesis list has lost `h566` and `hsym`
— the two T178 showed to be the same obligation — and has gained, in their place, only
quantities that are genuine inputs of the paper's proof:

* `hGm` — the entrywise `G`-bound of (4.2)/(5.31), as a function `Gm` of the two blocks;
* `hGsq2` — that `Gsq` dominates the squared `G`-pair `Gm_{xy} Gm_{yx}` (the honest index
  order: `G(z)` is not symmetric for complex Hermitian `H`, `docs/paper-deltas.md` #113 ⑦);
* `hrow` — the paper's "we can treat `b = b'` for all practical purposes" (#113 ①), needed
  because in each of the two loops of Figure 14 one glue label is reached only through `b'`;
* `hSmax` — (2.73) at `n = 4` for the four `4`-loops the two cuts produce, i.e. the
  `(max_a max_{σ∈{+,-}⁴} L_{u,σ,a})` of (5.66);
* `hc0`, `hc1` — `a' = a` (#113 ①, already the setting of `ee_le_EEpath`).

The constant is `2J*` rather than `J*`, and `μ = 2√(max L)` rather than `√(max L)`: the two
factors of `2` are the two terms of (5.22), which are now both estimated rather than one of
them being assumed away.  Constants are not optimised. -/
theorem ee_le_EEpath_sym (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (c : LoopArg (B.L N) ((0 + 2) + (0 + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
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
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (lab₁ c - b) : ℝ) → eeL6 X E N u ω σ c b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
              then 1 else 0)
          + Lemma57.cFar2 (B.W N : ℝ) ℓu
            * ((2 * J) ^ 2 * (((B.W N : ℝ) * ℓu * ηu) * (2 * √Smax)))
          + 72 * (2 * J) ^ 3 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2) := by
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hJ2 : (1 : ℝ) ≤ 2 * J := by linarith
  have hμ : (0 : ℝ) ≤ 2 * √Smax := by positivity
  have h42sq' : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ 2 * J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
    intro x y hxy
    have h := h42sq x y hxy
    have hT : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
      tailT_nonneg hW0.le _
    nlinarith
  exact Lemma57.ee_le_sym (B.L N) hW hℓu hℓs hηu hJ2 (lab₁ c) (lab₂ c) hμ hρ hGsq0
    h273 h564 h42sq'
    (fun b _ => eeL6_two_le_near₁ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2 hrow hSmax)
    (fun b _ => eeL6_two_le_near₂ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2 hrow hSmax)
    (fun b hfar hb1 hb2 => eeL6_two_le_far X E N u ω σ c b (by linarith) hJ hc0 hc1
      hGm0 hGm hGsq0 hGsq2 hrow h42sq hfar hb1 hb2)
    (norm_EEpath_le_W_sum X E u ω σ c)

/-! ### (5.36) in the paper's shape, with `h566` and `hsym` both discharged -/

/-- **(5.36) for `RBM.MomentDuhamel.EEpath` in the paper's literal shape** (T190): `μ` is
instantiated from (2.73) at `n = 4`, so it no longer occurs, and neither `h566` nor `hsym` is
assumed.  The right-hand side is

`η_u^{-1}[(ℓ_u/ℓ_s)^5 1(‖a₁-a₂‖ ≤ 4ℓ*_u) + (ℓ_u/ℓ_s)^{3/2} A_u^{-1/2} (2J*)³] T_{u,D}(‖a₁-a₂‖)²`

plus the two explicit remainders of deviation 5.  `hμbd` is (2.73) at `n = 4` in quantitative
form: twice the square root of the `4`-loop maximum of (5.66) is below
`(ℓ_u/ℓ_s)^{3/2} A_u^{-3/2}`; the factor `2` is the two terms of (5.22). -/
theorem ee_le_paper_EEpath_sym (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (c : LoopArg (B.L N) ((0 + 2) + (0 + 2)))
    {ℓu ℓs ηu D J : ℝ} (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (B.W N : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hc0 : rightArg c 0 = leftArg c 0) (hc1 : rightArg c 1 = leftArg c 1)
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
    (hμbd : 2 * √Smax ≤ ℓu / ℓs * √(ℓu / ℓs) *
      ((√((B.W N : ℝ) * ℓu * ηu))⁻¹ * ((B.W N : ℝ) * ℓu * ηu)⁻¹))
    (h273 : ∀ b, eeL6 X E N u ω σ c b
      ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2 * ((B.W N : ℝ) * ℓu * ηu)⁻¹)
    (h564 : ∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu
      < (zdist (B.L N) (lab₁ c - b) : ℝ) → eeL6 X E N u ω σ c b ≤ ρ)
    (h42sq : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ c‖
      ≤ ηu⁻¹ * (Lemma57.cNear2 (B.W N : ℝ) ℓu * (ℓu / ℓs) ^ 5 *
            (if (zdist (B.L N) (lab₁ c - lab₂ c) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
              then 1 else 0)
          + (Lemma57.cFar2 (B.W N : ℝ) ℓu + 72)
            * (ℓu / ℓs * √(ℓu / ℓs) * (√((B.W N : ℝ) * ℓu * ηu))⁻¹) * (2 * J) ^ 3)
        * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2
        + ((B.W N : ℝ) * (B.L N : ℝ) * ρ
          + 2 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) * (2 * J) ^ 3
            * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (lab₁ c - lab₂ c)) ^ 2) := by
  have hW : (1 : ℝ) ≤ (B.W N : ℝ) := one_le_W B N
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by linarith
  have hJ0 : (0 : ℝ) ≤ J := by linarith
  have hJ2 : (1 : ℝ) ≤ 2 * J := by linarith
  have h42sq' : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      Gsq x y ≤ 2 * J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) := by
    intro x y hxy
    have h := h42sq x y hxy
    have hT : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y)) :=
      tailT_nonneg hW0.le _
    nlinarith
  exact Lemma57.ee_le_paper_sym (B.L N) hW hℓu hℓs hηu hJ2 hA hr (lab₁ c) (lab₂ c) hρ hGsq0
    h273 h564 h42sq'
    (fun b _ => (eeL6_two_le_near₁ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2
        hrow hSmax).trans
      (mul_le_mul_of_nonneg_left hμbd (mul_nonneg (hGsq0 _ _) (hGsq0 _ _))))
    (fun b _ => (eeL6_two_le_near₂ X E N u ω σ c b hc0 hc1 hGm0 hGm hGsq0 hGsq2
        hrow hSmax).trans
      (mul_le_mul_of_nonneg_left hμbd (mul_nonneg (hGsq0 _ _) (hGsq0 _ _))))
    (fun b hfar hb1 hb2 => eeL6_two_le_far X E N u ω σ c b (by linarith) hJ hc0 hc1
      hGm0 hGm hGsq0 hGsq2 hrow h42sq hfar hb1 hb2)
    (norm_EEpath_le_W_sum X E u ω σ c)

/-! ### The hypotheses of `ee_le_EEpath_sym` and `ee_le_paper_EEpath_sym` are satisfiable

Seven vacuous-hypothesis incidents in this project (T145, T132b, T154, T164/T172, T180, T177,
and T172's `MinorGood`) make this check mandatory: a hypothesis list that cannot be satisfied
turns the theorem into a tautology and the compiler never complains.

The witness below covers **both** theorems at once — in particular `hA : 1 ≤ A_u` and
`hr : 1 ≤ ℓ_u/ℓ_s`, which `ee_hyp_consistent` did not have to produce (it only certified the
master form).  Take `ℓ_u = 1`, `η_u = W^{-1}` so that `A_u = W ℓ_u η_u = 1` exactly, `D = 0`
(the tail function then has floor `1` and is everywhere `≥ 1`), `ℓ_s = R^{-1}` with
`R = 1 + S + 4 max(S⁴, 0)`, `S = ∑_b L^{(1)}(b)` and `S⁴ = Smax` the maximum of the `4`-loops.
Then the (2.73) budget is `(ℓ_u/ℓ_s)^5 A_u^{-5} = R^5 ≥ S`, and `hμbd` holds because
`R^{3/2} ≥ R ≥ 1 + 4 Smax⁺ ≥ 2√Smax`.  `Gm` is the entrywise maximum of `|G|` over the
(finite) index set, `ρ = S`, and `J* = 1 + S + Gm²` — large enough that the saturated
`Gsq = J* T_{u,0}` dominates the squared `G`-pair, which is the only real tension in the list
(`hGm` pushes `Gm` up, `hGsq2`/`hrow` push it down, and `h42sq` caps `Gsq`).  It is not the
regime of the paper (there `A_u → ∞`); it certifies satisfiability only. -/

/-- A doubled loop argument with `a' = a` and prescribed labels — the setting (5.36) is
formalized in (`docs/paper-deltas.md` #113 ①), exhibited. -/
theorem exists_loopArg_diag {N : ℕ} (a₁ a₂ : ZMod (B.L N)) :
    ∃ c : LoopArg (B.L N) ((0 + 2) + (0 + 2)),
      leftArg c 0 = a₁ ∧ leftArg c 1 = a₂ ∧
      rightArg c 0 = leftArg c 0 ∧ rightArg c 1 = leftArg c 1 :=
  ⟨![a₁, a₂, a₁, a₂], rfl, rfl, rfl, rfl⟩

/-- **Joint satisfiability of every hypothesis of `RBM.EEDef.ee_le_EEpath_sym` and of
`RBM.EEDef.ee_le_paper_EEpath_sym`**, with the two labels `a₁`, `a₂` arbitrary and
`a' = a`. -/
theorem ee_sym_hyp_consistent (X : Sample B) (E : ℝ) {N : ℕ} (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a₁ a₂ : ZMod (B.L N)) :
    ∃ (c : LoopArg (B.L N) ((0 + 2) + (0 + 2))) (ℓu ℓs ηu D J Smax ρ : ℝ)
      (Gm Gsq : ZMod (B.L N) → ZMod (B.L N) → ℝ),
      leftArg c 0 = a₁ ∧ leftArg c 1 = a₂ ∧
      rightArg c 0 = leftArg c 0 ∧ rightArg c 1 = leftArg c 1 ∧
      1 ≤ ℓu ∧ 0 < ℓs ∧ 0 < ηu ∧ 1 ≤ J ∧
      1 ≤ (B.W N : ℝ) * ℓu * ηu ∧ 1 ≤ ℓu / ℓs ∧ 0 ≤ ρ ∧
      (∀ x y, 0 ≤ Gm x y) ∧
      (∀ (s : Bool) (x y : ZMod (B.L N)) (p q : ZMod (B.L N) × Fin (B.W N)),
        p.1 = x → q.1 = y → ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ Gm x y) ∧
      (∀ x y, 0 ≤ Gsq x y) ∧
      (∀ x y, Gm x y * Gm y x ≤ Gsq x y) ∧
      (∀ x bb bb' : ZMod (B.L N), SB (B.L N) bb bb' ≠ 0 →
        Gm x bb' * Gm bb' x ≤ Gsq bb x) ∧
      (∀ (s : Bool) (x y y' : ZMod (B.L N)),
        (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
          ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax) ∧
      (2 * √Smax ≤ ℓu / ℓs * √(ℓu / ℓs) *
        ((√((B.W N : ℝ) * ℓu * ηu))⁻¹ * ((B.W N : ℝ) * ℓu * ηu)⁻¹)) ∧
      (∀ b, eeL6 X E N u ω σ c b
        ≤ (ℓu / ℓs) ^ 5 * ((((B.W N : ℝ) * ℓu * ηu) ^ 2)⁻¹) ^ 2
            * ((B.W N : ℝ) * ℓu * ηu)⁻¹) ∧
      (∀ b, Lemma57.ellStarStar (B.W N : ℝ) ℓu < (zdist (B.L N) (lab₁ c - b) : ℝ) →
        eeL6 X E N u ω σ c b ≤ ρ) ∧
      (∀ x y : ZMod (B.L N), ellStar (B.W N : ℝ) ℓu / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
        Gsq x y ≤ J * tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (x - y))) := by
  classical
  obtain ⟨c, hl0, hl1, hr0, hr1⟩ := exists_loopArg_diag (B := B) a₁ a₂
  obtain ⟨M, hM⟩ := Finite.exists_le
    (fun t : Bool × (ZMod (B.L N) × Fin (B.W N)) × (ZMod (B.L N) × Fin (B.W N)) =>
      ‖Gsig (X.H N u ω) (zt E u) t.1 t.2.1 t.2.2‖)
  obtain ⟨Smax, hSm⟩ := Finite.exists_le
    (fun t : Bool × ZMod (B.L N) × ZMod (B.L N) × ZMod (B.L N) =>
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        ⟨[t.1, !t.1, t.1, !t.1], [t.2.1, t.2.2.1, t.2.1, t.2.2.2]⟩).re)
  set W : ℝ := (B.W N : ℝ) with hWdef
  have hW1 : 1 ≤ W := one_le_W B N
  have hW0 : 0 < W := by linarith
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM (true, (0, ⟨0, B.W_pos N⟩), (0, ⟨0, B.W_pos N⟩)))
  set S : ℝ := ∑ b : ZMod (B.L N), eeL6 X E N u ω σ c b with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun b _ => eeL6_nonneg X E N u ω σ c b
  have hSb : ∀ b : ZMod (B.L N), eeL6 X E N u ω σ c b ≤ S := fun b =>
    Finset.single_le_sum (fun b _ => eeL6_nonneg X E N u ω σ c b) (Finset.mem_univ b)
  -- the regime: `A_u = 1`, `ℓ_u = 1`, `ℓ_s = R⁻¹`, `D = 0`
  set Sp : ℝ := max Smax 0 with hSpdef
  have hSp0 : 0 ≤ Sp := le_max_right _ _
  set R : ℝ := 1 + S + 4 * Sp with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith
  have hR0 : 0 < R := by linarith
  set ηu : ℝ := 1 / W with hηdef
  have hη0 : 0 < ηu := by rw [hηdef]; positivity
  have hA1 : W * 1 * ηu = 1 := by rw [hηdef]; field_simp
  have hW0rpow : W ^ (-(0 : ℝ)) = 1 := by rw [neg_zero, Real.rpow_zero]
  have hT1 : ∀ d : ℝ, 1 ≤ tailT W 1 ηu 0 d := by
    intro d
    have h1 : (0 : ℝ) ≤ ((W * 1 * ηu) ^ 2)⁻¹ * Real.exp (-Real.sqrt (d / 1)) := by positivity
    rw [tailT, hW0rpow]; linarith
  have hratio : (1 : ℝ) / (1 / R) = R := by field_simp
  refine ⟨c, 1, 1 / R, ηu, 0, 1 + S + M * M, Smax, S, fun _ _ => M,
    fun x y => (1 + S + M * M) * tailT W 1 ηu 0 (zdist (B.L N) (x - y)),
    hl0, hl1, hr0, hr1, le_refl 1, by positivity, hη0, by nlinarith,
    by rw [hA1], by rw [hratio]; exact hR1, hS0,
    fun _ _ => hM0, fun s _ _ p q _ _ => hM (s, p, q),
    ?_, ?_, ?_, fun s x y y' => hSm (s, x, y, y'), ?_, ?_, ?_, fun x y _ => le_refl _⟩
  · intro x y
    dsimp only
    have h := hT1 ((zdist (B.L N) (x - y) : ℝ))
    nlinarith
  · intro x y
    dsimp only
    have h := hT1 ((zdist (B.L N) (x - y) : ℝ))
    nlinarith
  · intro x bb bb' _
    dsimp only
    have h := hT1 ((zdist (B.L N) (bb - x) : ℝ))
    nlinarith
  · -- `hμbd` : `2√Smax ≤ R √R`, because `R ≥ 1 + 4 Smax⁺` and `2t ≤ 1 + 4t²`
    rw [hratio, hA1]
    have hsq : √Smax ≤ √Sp := Real.sqrt_le_sqrt (le_max_left _ _)
    have ht2 : √Sp ^ 2 = Sp := Real.sq_sqrt hSp0
    have ht0 : 0 ≤ √Sp := Real.sqrt_nonneg _
    have hkey : 2 * √Sp ≤ 1 + 4 * Sp := by nlinarith [sq_nonneg (2 * √Sp - 1 / 2)]
    have hRle : (1 : ℝ) + 4 * Sp ≤ R := by rw [hRdef]; linarith
    have hsR : (1 : ℝ) ≤ √R := Real.one_le_sqrt.2 hR1
    have hfin : R ≤ R * √R := le_mul_of_one_le_right hR0.le hsR
    have hone : ((√(1 : ℝ))⁻¹ * (1 : ℝ)⁻¹) = 1 := by
      rw [Real.sqrt_one]; norm_num
    rw [hone, mul_one]
    linarith
  · -- (2.73): the budget is `(ℓ_u/ℓ_s)^5 A_u^{-5} = R^5`
    intro b
    have hbudget : ((1 : ℝ) / (1 / R)) ^ 5 * (((W * 1 * ηu) ^ 2)⁻¹) ^ 2 * (W * 1 * ηu)⁻¹
        = R ^ 5 := by rw [hratio, hA1]; norm_num
    have h5 : R ≤ R ^ 5 := by
      calc R = R ^ 1 := (pow_one _).symm
        _ ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
    rw [hbudget]
    have := hSb b
    rw [hRdef] at h5
    linarith
  · exact fun b _ => hSb b


end SixSym

end EEDef
end RBM
