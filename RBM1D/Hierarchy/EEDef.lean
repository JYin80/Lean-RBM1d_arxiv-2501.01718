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

end EEDef
end RBM
