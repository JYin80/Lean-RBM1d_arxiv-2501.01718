/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.MomentDuhamelQ

/-!
# Lemma 5.14 on the `Q_u` route: the assembly (T219)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5 — (5.91), (5.92), (5.99)–(5.103) — and §7, (7.16).

## What this file does

D14 ruled that the moment route to `RBM.Step3.Lemma514` changes its interface from
`RBM.MomentDuhamel.Hyp.momentDuhamel` (unprojected) to
`RBM.MomentDuhamel.Hyp.momentDuhamelQ` (every tensor under a `U` already carries a `Q_u`).
The reason is T195/T201: on the paper's own grid `1 - s_k = W^{-kτ'}` the `hkerC` slot of
`RBM.Gauss.hrhs_of_moment_inputs` — the (7.1) tier — has **no** `N`-independent constant
(`RBM.Gauss.no_const_hkerC_on_gridS`, a compiled `False`), so the plain route's `hrhs` is
unsatisfiable exactly on the window the six-step construction uses, and every theorem
downstream of it is vacuous there.  On the `Q_u` route the sum-zero premise of (7.16) is a
*theorem* for each of the five terms (T201), and (7.16) carries no `(η_s/η_v)` prefactor.

This file is the assembly.  It contains:

1. `RBM.Gauss.Rhs514QAt` — the `hrhs` slot of `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ`
   at the control `c_N (W ℓ_v η_v)^{-(n+2)}`, the `Q`-analogue of `RBM.Gauss.Rhs514At`;
2. `RBM.Gauss.stochDom_lkT_of_Qhalf_Phalf` — (5.101) at the level of `≺`: the `Q_v`-half and
   the `P`-half add up to the loop difference itself;
3. `RBM.Gauss.lemma514_of_momentDuhamelQ` and `RBM.Gauss.lemma514_forall_of_momentDuhamelQ` —
   `RBM.Step3.Lemma514` on the `Q` route, and
   `RBM.Gauss.lemma514Q_forall_of_hHol_flow` / `RBM.Gauss.flow_sharpLmK_Q_of_hHol_flow` — the
   same with the Hölder modulus discharged by `RBM.Gauss.hHol_flow` (T105/T203), i.e. the
   `Q`-twins of `RBM.Gauss.lemma514_forall_of_hHol_flow` /
   `RBM.Gauss.flow_sharpLmK_of_hHol_flow`;
4. `RBM.Gauss.rhs514QAt_of_kernel_inputs` — the producer of (1) out of T201's **five** kernel
   estimates `RBM.Gauss.momNorm_Uker_Qop_le`, `RBM.Gauss.momNorm_Uker_commS_le` (5.99),
   `RBM.Gauss.momNorm_Uker_PsumVarthetaDot_le` (5.100) and `RBM.Gauss.momNorm_Uker_QQ_le`
   (5.103), which until now had **no consumer** in the repository;
5. a satisfiability witness on the paper's own grid.

## What is **gone** from the hypothesis list

`hkerC` and `hker2C` — the (7.1)-tier `edgeKer` row sums, retired by T201 — do not occur
anywhere below.  The producer of §4 takes instead, for each of the five tensors, the
size envelope and the fast decay (7.13) that (7.16) asks for.

## The two hypotheses that are somebody else's

* **`hPhalf`** (T218).  `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` controls
  `‖Q_v ∘ (L-K)_v‖`, not `‖(L-K)_v‖`.  (5.101) is `A = Q_t A + (P A) ϑ_t`
  (`RBM.SumZeroDyn.norm_le_norm_Qop_add`), so the missing half is a `≺` for
  `‖P ∘ (L-K)_v‖ · ‖ϑ_v‖`; its deterministic input `RBM.SumZeroDyn.norm_Psum_lkT_le` (5.96) is
  a theorem, and the `Ξ^{(L-K)}_{u,n+1} ≺ Φ` it needs *is* one of the four premises of
  `RBM.Step3.Lemma514` (`RBM.Gauss.Lemma514Premises`, the slot `m = n + 1 < n + 2`).  It is a
  named hypothesis here in exactly the shape T218 has to produce.
* **`hGd…`**, the (7.13) fast decay along the flow (T220).  It is the one premise of (7.16)
  that is about the *model* and not about the kernel, and T201 records that it has no producer.

Both are genuine `≺`/decay statements about pinned objects; neither is a free tensor and
neither is an empty hypothesis.
-/

namespace RBM.Gauss

open MeasureTheory Filter MomentDuhamel

open scoped Matrix.Norms.L2Operator

/-! ### §1  The `Q`-route right-hand side -/

section RhsQ

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The `hrhs` slot of `RBM.MomentDuhamel.stochDom_of_momentDuhamelQ`, at the terminal time
`v` and the control `c_N (W ℓ_v η_v)^{-(n+2)}`.**

Written out once, as a `def`, so that the producer of §4 and the two theorems that consume it
cannot drift apart.  The five summands are, in order: the initial datum of (5.91), the drift,
the commutator `[Q_u, Θ_{u,σ}]` of (5.99), the `ϑ̇` term of (5.100), and the `(Q ⊗ Q)(E ⊗ E)`
term of (5.103) under its square root.

Compare `RBM.Gauss.Rhs514At`: there are two more terms, and — this is the point of D14 —
every tensor under a `U` carries a `Q_u`. -/
def Rhs514QAt (H : MomentDuhamel.Hyp X E s t n) (c v : ℕ → ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
    ∀ q : LoopData (B.L N) (n + 2),
      momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖)
        + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖))
        + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
                (SumZeroDyn.lkT X E N u ω q.1)) q.2‖))
        + 2 * (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
            ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
                * SumZeroDyn.varthetaDot (B.L N) u b) q.2‖))
        + (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
            ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
              (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
              (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
        ≤ C * ((N : ℝ) ^ (ε / 2) * (c N * (B.scale E N (v N) ^ (n + 2))⁻¹))

/-- **The `Q_v`-half of (5.101) at the level of `≺`**: `Rhs514QAt` feeds
`RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` by a bare application. -/
theorem stochDomQ_of_rhs514QAt (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (H : MomentDuhamel.Hyp X E s t n) (hQint : MomentDuhamel.QIntegrable X E s t n)
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Cv)
    {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N)
    (v : ℕ → ℝ) (hv : ∀ N, v N ∈ Set.Icc (s N) (t N)) (hrhs : Rhs514QAt H c v) :
    StochDom B.P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω q.1) q.2‖)
      (fun N _ _ => c N * (B.scale E N (v N) ^ (n + 2))⁻¹) :=
  MomentDuhamel.stochDom_of_momentDuhamelQ H hQint v (fun N => (hv N).1) (fun N => (hv N).2)
    hcard (Φ := fun N _ => c N * (B.scale E N (v N) ^ (n + 2))⁻¹)
    (fun N _ => by
      have h1 : 0 < B.scale E N (v N) ^ (n + 2) :=
        pow_pos (B.scale_pos' hE N ((hs0 N).trans (hv N).1) ((hv N).2.trans_lt (ht1 N))) _
      have := hc0 N
      positivity)
    hrhs

end RhsQ

/-! ### §2  (5.101): the `Q`-half and the `P`-half add up -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} {X : Sample B} {E : ℝ}

/-- **(5.101) at the level of `≺`.**  `RBM.SumZeroDyn.norm_le_norm_Qop_add` is the pointwise
identity `A = Q_t ∘ A + (P ∘ A) ϑ_t`; here it is pushed through `RBM.StochDom.add` and
`RBM.StochDom.of_le_left`.  The `P`-half is the input T218 produces.

Nothing about the two controls is assumed beyond their being the controls of the two halves;
the conclusion carries their sum, which is what the caller then absorbs into
`RBM.Step3.stochDom_mono`. -/
theorem stochDom_lkT_of_Qhalf_Phalf {P : Measure Ω} {n : ℕ} {v : ℕ → ℝ} {cQ cP : ℕ → ℝ}
    (hQ : StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω q.1) q.2‖)
      (fun N _ _ => cQ N))
    (hP : StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω q.1) (q.2 0)‖
          * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) q.2‖)
      (fun N _ _ => cP N)) :
    StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
      (fun N _ _ => cQ N + cP N) :=
  StochDom.of_le_left
    (fun N q ω => SumZeroDyn.norm_le_norm_Qop_add (B.L N) ((v N : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N (v N) ω q.1) q.2)
    (hQ.add hP)

end Split

/-! ### §3  `RBM.Step3.Lemma514` on the `Q` route -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The `P`-half of (5.101) in the shape the assembly consumes** (T218).

This is a `≺` for the second summand of `RBM.SumZeroDyn.norm_le_norm_Qop_add`, at every
terminal time of the window, with the same control `Φ (W ℓ_v η_v)^{-(n+2)}` the `Q`-half
carries.  Its deterministic input is (5.96), `RBM.SumZeroDyn.norm_Psum_lkT_le`, whose
hypothesis `Ξ^{(L-K)}_{v,n+1} ≺ Φ` is the premise of `RBM.Gauss.Lemma514Premises` at
`m = n + 1` — which is why the premises are passed in.

It is stated as a `def` so that the two theorems below and T218's producer cannot drift
apart. -/
def PHalf514 (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
    Lemma514Premises X E s t (n + 2) Λ Φ →
    ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω =>
          ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω q.1) (q.2 0)‖
            * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) q.2‖)
        (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * (B.scale E N (v N) ^ (n + 2))⁻¹)

/-- **`RBM.Step3.Lemma514` from `RBM.MomentDuhamel.Hyp.momentDuhamelQ`.**

The `Q`-route twin of `RBM.Gauss.lemma514_of_momentDuhamel`.  Three things differ:

* `hrhs` is `RBM.Gauss.Rhs514QAt` — five terms, every tensor projected — and **not**
  `RBM.Gauss.Rhs514At`.  Consequently the (7.1)-tier row sums `hkerC`/`hker2C`, which T201
  proved have no `N`-independent constant on the paper's grid, do not appear;
* one new hypothesis, `RBM.MomentDuhamel.QIntegrable`, which on the Gaussian model is the
  theorem `RBM.MomentDuhamel.qIntegrable_gauss` (paper-delta T214a);
* one new hypothesis, `RBM.Gauss.PHalf514` (T218), because (5.91) bounds `Q_v ∘ (L-K)_v` and
  the conclusion is about `(L-K)_v`.

The control is raised to `max (Λ^{1/2} + Φ) 1` inside the proof for the same reason as in the
plain route, and the two halves of (5.101) double it, whence `C = 2` in the final
`RBM.Step3.stochDom_mono`. -/
theorem lemma514_of_momentDuhamelQ (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    (H : MomentDuhamel.Hyp X E s t n) (hQint : MomentDuhamel.QIntegrable X E s t n)
    {Cv : ℝ} (hcard : ∀ᶠ N : ℕ in atTop,
      (Fintype.card (LoopData (B.L N) (n + 2)) : ℝ) ≤ (N : ℝ) ^ Cv)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) (n + 2),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ (n + 2) * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ (n + 2) * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hrhs : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514QAt H (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v)
    (hPhalf : PHalf514 X E s t n) :
    Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) (n + 2) := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1
  have hc1 : ∀ N : ℕ, (1 : ℝ) ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := fun N => le_max_right _ _
  have hc0 : ∀ N : ℕ, (0 : ℝ) ≤ 2 * max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := fun N => by
    have := hc1 N; linarith
  have hscale : ∀ (N : ℕ) (w : ℝ), w ∈ Set.Icc (s N) (t N) →
      0 < B.scale E N w ^ (n + 2) := fun N w hw =>
    pow_pos (B.scale_pos' hE N ((hs0 N).trans hw.1) (hw.2.trans_lt (ht1 N))) _
  have hseq : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
        (fun N _ _ => 2 * max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
          * (B.scale E N (v N) ^ (n + 2))⁻¹) := by
    intro v hv
    -- the `Q`-half, from (5.91)
    have hQ : StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω =>
          ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω q.1) q.2‖)
        (fun N _ _ => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
          * (B.scale E N (v N) ^ (n + 2))⁻¹) := by
      refine stochDomQ_of_rhs514QAt hE hs0 ht1 H hQint hcard
        (c := fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1)
        (fun N => lt_of_lt_of_le one_pos (hc1 N)) v hv ?_
      intro ε hε p hp
      obtain ⟨C, hC0, hCN⟩ := hrhs Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩ v hv ε hε p hp
      refine ⟨C, hC0, ?_⟩
      filter_upwards [hCN] with N hN q
      refine (hN q).trans ?_
      have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
      have hinv : (0 : ℝ) ≤ (B.scale E N (v N) ^ (n + 2))⁻¹ := (inv_pos.2 hsc).le
      have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      have hle : Λ N ^ ((1 : ℝ) / 2) + Φ N ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 :=
        le_max_left _ _
      gcongr
    -- the `P`-half (T218)
    have hP := hPhalf Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩ v hv
    have hPle : StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω =>
          ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω q.1) (q.2 0)‖
            * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) q.2‖)
        (fun N _ _ => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
          * (B.scale E N (v N) ^ (n + 2))⁻¹) := by
      refine Step3.stochDom_mono (fun N _ _ => ?_) 1 (Eventually.of_forall fun N _ _ => ?_) hP
      · have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
        have := hc1 N
        positivity
      · have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
        have hinv : (0 : ℝ) ≤ (B.scale E N (v N) ^ (n + 2))⁻¹ := (inv_pos.2 hsc).le
        have hle : Λ N ^ ((1 : ℝ) / 2) + Φ N ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 :=
          le_max_left _ _
        rw [one_mul]
        gcongr
    have hsum := stochDom_lkT_of_Qhalf_Phalf hQ hPle
    refine Step3.stochDom_mono (fun N _ _ => ?_) 1 (Eventually.of_forall fun N _ _ => ?_) hsum
    · have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
      have := hc1 N
      positivity
    · rw [one_mul]
      ring_nf
      exact le_rfl
  have hmain := stochDom_flowXiLK_of_seq X hE hs0 hst ht1 hcard hK hγ hΞ hc0
    (Eventually.of_forall fun N => by have := hc1 N; linarith) hHol hseq
  refine Step3.stochDom_mono (fun N _ _ => ?_) 2 ?_ hmain
  · have h1 : (0 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 N) _
    have := hΦ0 N
    linarith
  · filter_upwards [hΛ1] with N hN _ _
    have h1 : (1 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have := hΦ0 N
    have : max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 = Λ N ^ ((1 : ℝ) / 2) + Φ N :=
      max_eq_left (by linarith)
    rw [this]

/-- **The `∀ m, 2 ≤ m` form of Steps 3–5's `h514`, on the `Q` route.** -/
theorem lemma514_forall_of_momentDuhamelQ (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (H : ∀ n, MomentDuhamel.Hyp X E s t n)
    (hQint : ∀ n, MomentDuhamel.QIntegrable X E s t n)
    {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ)
    {Ξ : ℕ → Set Ω} (hΞ : HighProb B.P Ξ)
    (hHol : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : LoopData (B.L N) m,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |B.scale E N u ^ m * ‖SumZeroDyn.lkT X E N u ω q.1 q.2‖
            - B.scale E N v ^ m * ‖SumZeroDyn.lkT X E N v ω q.1 q.2‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ γ)
    (hrhs : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514QAt (H n) (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v)
    (hPhalf : ∀ n : ℕ, PHalf514 X E s t n) :
    ∀ m, 2 ≤ m → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) m := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact lemma514_of_momentDuhamelQ hE hs0 hst ht1 (H n) (hQint n) (card_loopData_le (n + 2))
    hK hγ hΞ (hHol (n + 2)) (hrhs n) (hPhalf n)

end Assembly

/-! ### §4  The flow: the Hölder modulus and (2.59) discharged -/

section Flow

/-- **`RBM.Step3.Lemma514` on the `Q` route with `hHol` discharged**, the `Q`-twin of
`RBM.Gauss.lemma514_forall_of_hHol_flow`.

The hypothesis list is: the model, the window, `H` (T180/T206/T212's
`RBM.MomentDuhamel.Hyp`), `QIntegrable` (T214; `RBM.MomentDuhamel.qIntegrable_gauss` on the
Gaussian model), the regime `hreg`/`hXΞ` on a high-probability `Ξ`, the `Q`-route right-hand
side `hrhs` (T201's five kernel estimates, §5 below) and the `P`-half `hPhalf` (T218).

`hHol` is `RBM.Gauss.hHol_flow`; `hKb` is `RBM.Gauss.hKb_flow` (2.59), T203.  **No `hkerC`,
no `hker2C`, no short-window condition, no `0 < s N`.** -/
theorem lemma514Q_forall_of_hHol_flow (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (H : ∀ n, MomentDuhamel.Hyp (sample d) E s t n)
    (hQint : ∀ n, MomentDuhamel.QIntegrable (sample d) E s t n)
    {Ξ : ℕ → Set (Ω d)} (hΞ : HighProb (band d).P Ξ) {c : ℝ} (hc1 : 1 ≤ c)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ c)
    (hXΞ : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ c)
    (hrhs : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises (sample d) E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514QAt (H n) (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v)
    (hPhalf : ∀ n : ℕ, PHalf514 (sample d) E s t n) :
    ∀ m, 2 ≤ m → Step3.Lemma514 (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowXiL (sample d) E s t) (Step3.flowA (band d) E s t) m := by
  have := (band d).isProbabilityMeasure
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hn2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hcc : c ≤ c * ((n + 2 : ℕ) : ℝ) + 1 := by nlinarith
  have hc1' : (1 : ℝ) ≤ c * ((n + 2 : ℕ) : ℝ) + 1 := by nlinarith
  have hXΞ' : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N,
      ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ (c * ((n + 2 : ℕ) : ℝ) + 1) := by
    filter_upwards [hXΞ, eventually_ge_atTop 1] with N hN hN1 ω hω
    exact (hN ω hω).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) hcc)
  exact lemma514_of_momentDuhamelQ hE hs0 hst ht1 (H n) (hQint n) (card_loopData_le (n + 2))
    (K := (c * ((n + 2 : ℕ) : ℝ) + 1) * (3 * ((n + 2 : ℕ) : ℝ) + 4) + 1) (γ := (1 : ℝ) / 2)
    (by nlinarith) (by norm_num) hΞ
    (hHol_flow d hE hs0 ht1 hc1' (show 1 ≤ n + 2 by omega)
      (eventually_le_rpow_mono hcc hreg) hXΞ'
      (hKb_flow (band d) hE ht1 hc0 (n + 2) hreg)) (hrhs n) (hPhalf n)

/-- **End-to-end probe on the `Q` route: Step 4's (2.78) with `hHol`, `hKb`, `hkerC` and
`hker2C` all gone.**

The `Q`-twin of `RBM.Gauss.flow_sharpLmK_of_hHol_flow`.  What is left open is exactly the two
blocks the T219 ticket names: `hrhs` — T201's five kernel estimates, whose remaining premise
is the (7.13) fast decay along the flow (T220) — and `hPhalf` (T218). -/
theorem flow_sharpLmK_Q_of_hHol_flow (d : Dims) {E : ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 (band d) E s t)
    (H : ∀ n, MomentDuhamel.Hyp (sample d) E s t n)
    (hQint : ∀ n, MomentDuhamel.QIntegrable (sample d) E s t n)
    {Ξ : ℕ → Set (Ω d)} (hΞ : HighProb (band d).P Ξ) {c : ℝ} (hc1 : 1 ≤ c)
    (hreg : ∀ᶠ N : ℕ in atTop, (etaT E (t N))⁻¹ ≤ (N : ℝ) ^ c)
    (hXΞ : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) ^ c)
    (hrhs : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises (sample d) E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        Rhs514QAt (H n) (fun N => Λ N ^ ((1 : ℝ) / 2) + Φ N) v)
    (hPhalf : ∀ n : ℕ, PHalf514 (sample d) E s t n)
    (h0 : ∀ m, 1 ≤ m → Step3.S (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t)
      (Step3.flowA (band d) E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 → Step3.S (band d).P (Step3.flowXiLK (sample d) E s t)
      (Step3.flowAs (band d) E s) (Step3.flowR (band d) s t)
      (Step3.flowA (band d) E s t) m l)
    (h1 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 1) fun _ _ _ => 1)
    (h2 : StochDom (band d).P (Step3.flowXiLK (sample d) E s t 2)
      fun N u _ => Step3.flowA (band d) E s t N u ^ ((1 : ℝ) / 4)) :
    ∀ n : ℕ, 1 ≤ n → StochDom (band d).P
      (fun N (p : RBM.TimeIcc s t N × LoopData ((band d).L N) n) ω =>
        (sample d).lkErr E N p.1 ω p.2.idx)
      (fun N p _ => ((band d).scale E N p.1)⁻¹ ^ n) :=
  Step45.flow_sharpLmK (sample d) hκ0 hκ1 hEκ hs0 hst ht1 hcond
    (lemma514Q_forall_of_hHol_flow d (by linarith) hs0 hst ht1 H hQint hΞ hc1 hreg hXΞ
      hrhs hPhalf)
    h0 h12 h1 h2

end Flow

/-! ### §5  The producer: T201's five kernel estimates, on the (7.16) tier

This is where the `Q_u` route pays off.  Each of the five tensors of (5.91) + (5.103) is
sum-zero **as a theorem** — `RBM.SumZero_Qop`, `RBM.SumZeroDyn.SumZero_commS` (5.90),
`RBM.SumZeroDyn.Psum_varthetaDot`, `RBM.SumZeroDyn.sumZeroAt_QQ` (5.104) — so (7.16) applies
and there is no `(η_s/η_v)` prefactor.  T201 packaged the four applications as
`RBM.Gauss.momNorm_Uker_Qop_le`, `RBM.Gauss.momNorm_Uker_commS_le`,
`RBM.Gauss.momNorm_Uker_PsumVarthetaDot_le` and `RBM.Gauss.momNorm_Uker_QQ_le`, and until now
they had no consumer.  Here they are consumed.

What is left open in the hypothesis list is exactly two things: the **size envelope** of each
tensor (Step 2's a priori bounds, in the shape (7.16) asks for) and the **fast decay** (7.13)
of each tensor along the flow — the latter is **T220** and is the one premise that is about
the model rather than about the kernel.  `hkerC`/`hker2C` do not appear. -/

section Producer

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- `C_m K^{2m}`, the multiplicative constant of (7.16) at loop length `m`. -/
noncomputable def cKer716 (m : ℕ) (Kd : ℝ) : ℝ := cKerSumZero m * Kd ^ (2 * m)

/-- The additive error of (7.16) at loop length `m`: the offset `ζ` of the size envelope and
the error `δ` of the fast decay (7.13), each carried across the window by `((1-s)/(1-v))^m`. -/
noncomputable def errKer716 (L m : ℕ) (Kd ζ δ s v : ℝ) : ℝ :=
  cKerSumZero m * Kd ^ (2 * m) * ((1 - s) / (1 - v)) ^ m * ζ
    + cKerSumZeroErr m * (L : ℝ) ^ m * ((1 - s) / (1 - v)) ^ m * δ

theorem cKerSumZero_nonneg (m : ℕ) : 0 ≤ cKerSumZero m := by
  unfold cKerSumZero
  have := cWin_nonneg
  have := cLip_nonneg
  positivity

theorem cKerSumZeroErr_nonneg (m : ℕ) : 0 ≤ cKerSumZeroErr m := by
  unfold cKerSumZeroErr
  have := cTwo52_pos
  positivity

theorem cKer716_nonneg (m : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd) : 0 ≤ cKer716 m Kd :=
  mul_nonneg (cKerSumZero_nonneg m) (pow_nonneg hKd _)

theorem errKer716_nonneg (L m : ℕ) {Kd ζ δ s v : ℝ} (hKd : 0 ≤ Kd) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    (hsv : s ≤ v) (hv1 : v < 1) : 0 ≤ errKer716 L m Kd ζ δ s v := by
  have h1 : (0 : ℝ) < 1 - v := by linarith
  have h2 : (0 : ℝ) ≤ (1 - s) / (1 - v) := div_nonneg (by linarith) h1.le
  have hr : (0 : ℝ) ≤ ((1 - s) / (1 - v)) ^ m := pow_nonneg h2 m
  have hc1 := cKerSumZero_nonneg m
  have hc2 := cKerSumZeroErr_nonneg m
  have hKm : (0 : ℝ) ≤ Kd ^ (2 * m) := pow_nonneg hKd _
  have hLm : (0 : ℝ) ≤ (L : ℝ) ^ m := by positivity
  have t1 : (0 : ℝ) ≤ cKerSumZero m * Kd ^ (2 * m) * ((1 - s) / (1 - v)) ^ m * ζ :=
    mul_nonneg (mul_nonneg (mul_nonneg hc1 hKm) hr) hζ
  have t2 : (0 : ℝ) ≤ cKerSumZeroErr m * (L : ℝ) ^ m * ((1 - s) / (1 - v)) ^ m * δ :=
    mul_nonneg (mul_nonneg (mul_nonneg hc2 hLm) hr) hδ
  unfold errKer716
  linarith

/-- `C M a + e ≤ (C+1) M (a+e)` for `M ≥ 1`: the additive error of (7.16) is absorbed into
the same constant as the main term, without touching the `N^{ε/2}` factor. -/
theorem affine_absorb {a e C M : ℝ} (ha : 0 ≤ a) (he : 0 ≤ e) (hC : 0 ≤ C) (hM : 1 ≤ M) :
    C * (M * a) + e ≤ (C + 1) * (M * (a + e)) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have h1 : (0 : ℝ) ≤ M * a := mul_nonneg hM0 ha
  have hCM : (1 : ℝ) ≤ (C + 1) * M := by nlinarith
  have h2 : 1 * e ≤ ((C + 1) * M) * e := mul_le_mul_of_nonneg_right hCM he
  linarith [h1, h2]

/-- **`κ_A (1-w) ℓ̂_w = W ℓ_w η_w`.**  The free constant `κ_A` of (7.16) is fixed once and for
all to `W Im m^{(E)}`, and then the normalization of (7.16) is *literally* the scale
`RBM.Band.scale` of Lemmas 2.18–2.20.  Nothing is lost or gained: `η_w = (1-w) Im m^{(E)}`. -/
theorem scale_eq_kappaA (B : Band Ω) (E : ℝ) (N : ℕ) (w : ℝ) :
    ((B.W N : ℝ) * (mE E).im) * ((1 - w) * ellHat (B.L N) ((w : ℝ) : ℂ))
      = B.scale E N w := by
  simp only [Band.scale, Band.ell, etaT]
  ring

/-- **The producer of `RBM.Gauss.Rhs514QAt` out of T201's five kernel estimates.**

Hypothesis table, with the owner of each row:

| row | what | owner |
|---|---|---|
| `hEnvI`, `hEnvF`, `hEnvC`, `hEnvD`, `hEnvE` | the size envelope `‖T‖ ≤ (W ℓ_u η_u)^{-m} ψ + ζ` of (7.16) | Step 2's a priori bounds |
| `hDecI`, `hDecF`, `hDecC`, `hDecD`, `hDecE` | the fast decay (7.13) of the same five tensors | **T220** |
| `hMψ`, `hMψE` | `‖ψ_u‖_{2p} ≺ Φ`, uniformly on the window | the drift/`E⊗E` moment bounds |
| `hnum` | the deterministic arithmetic of (5.24) | the caller |

`hkerC`/`hker2C` — the (7.1)-tier row sums — are **absent**: that is the whole point of D14.
The single `ψ` family serves the four `‖·‖_{2p}` terms (take the max of the four envelopes);
the `E ⊗ E` term has its own `ψE` because its moment order is `p`, not `2p`, and its loop
length is `2(n+2)`, which is why its contribution enters under a square root and still lands on
`(W ℓ_v η_v)^{-(n+2)}`. -/
theorem rhs514QAt_of_kernel_inputs (hE : |E| < 2) (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {Kd ζ δ : ℝ} (hKd : 1 ≤ Kd) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1) b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + ζ)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ)
    (hEnvC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ)
    (hEnvD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + ζ)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd) δ
        (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)))
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) δ
        (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)))
    (hDecC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) δ
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)))
    (hDecD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) δ
        (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b))
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) δ
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1)))
    {Phi PhiE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hPhi0 : ∀ N q, 0 ≤ Phi N q) (hPhiE0 : ∀ N q, 0 ≤ PhiE N q)
    (hMψ : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N q))
    (hMψE : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P p (ψE N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * PhiE N q))
    {c : ℕ → ℝ}
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
      (cKer716 (n + 2) Kd * (B.scale E N (v N))⁻¹ ^ (n + 2) * Phi N q
          + errKer716 (B.L N) (n + 2) Kd ζ δ (s N) (v N)) * (1 + 6 * (v N - s N))
        + ((v N - s N) * (cKer716 ((n + 2) + (n + 2)) Kd
              * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * PhiE N q
            + errKer716 (B.L N) ((n + 2) + (n + 2)) Kd ζ δ (s N) (v N))) ^ ((1 : ℝ) / 2)
        ≤ c N * (B.scale E N (v N) ^ (n + 2))⁻¹) :
    Rhs514QAt H c v := by
  intro ε hε p hp
  obtain ⟨C1, hC10, hA1⟩ := hMψ ε hε p hp
  obtain ⟨C3, hC30, hA3⟩ := hMψE ε hε p hp
  have hcMD := H.cMD_nonneg p
  have hKd0 : (0 : ℝ) ≤ Kd := by linarith
  set Csq : ℝ := (H.cMD p * (C3 + 1)) ^ ((1 : ℝ) / 2) with hCsqdef
  have hCsq0 : 0 ≤ Csq := Real.rpow_nonneg (by positivity) _
  refine ⟨C1 + Csq + 1, by positivity, ?_⟩
  filter_upwards [hA1, hA3, hnum, eventually_ge_atTop 1] with N h1 h3 hnumN hNge q
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have h2p : 2 * p ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  set Np : ℝ := (N : ℝ) ^ (ε / 2) with hNpdef
  have hNp1 : (1 : ℝ) ≤ Np := Real.one_le_rpow hNge1 (by positivity)
  have hNp0 : (0 : ℝ) < Np := lt_of_lt_of_le one_pos hNp1
  have hs0N := hs0 N
  have hsvN := hsv N
  have hv1 : v N < 1 := lt_of_le_of_lt (hvt N) (ht1 N)
  have hv0 : (0 : ℝ) ≤ v N := hs0N.trans hsvN
  have hκA : (0 : ℝ) < (B.W N : ℝ) * (mE E).im := by
    have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have := mE_im_pos hE
    positivity
  have hbr : ∀ w : ℝ, ((B.W N : ℝ) * (mE E).im) * ((1 - w) * ellHat (B.L N) ((w : ℝ) : ℂ))
      = B.scale E N w := fun w => scale_eq_kappaA B E N w
  -- the two normalizations and the two errors
  set Av : ℝ := (B.scale E N (v N))⁻¹ ^ (n + 2) with hAvdef
  set Av2 : ℝ := (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) with hAv2def
  set Eb : ℝ := errKer716 (B.L N) (n + 2) Kd ζ δ (s N) (v N) with hEbdef
  set Eb2 : ℝ := errKer716 (B.L N) ((n + 2) + (n + 2)) Kd ζ δ (s N) (v N) with hEb2def
  have hEb0 : (0 : ℝ) ≤ Eb := errKer716_nonneg _ _ hKd0 hζ hδ hsvN hv1
  have hEb20 : (0 : ℝ) ≤ Eb2 := errKer716_nonneg _ _ hKd0 hζ hδ hsvN hv1
  have hscale : (0 : ℝ) < B.scale E N (v N) := B.scale_pos' hE N hv0 hv1
  have hAv0 : (0 : ℝ) ≤ Av := by rw [hAvdef]; positivity
  have hAv20 : (0 : ℝ) ≤ Av2 := by rw [hAv2def]; positivity
  have hcK0 : (0 : ℝ) ≤ cKer716 (n + 2) Kd := cKer716_nonneg _ hKd0
  have hcK20 : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) Kd := cKer716_nonneg _ hKd0
  set Kmain : ℝ := cKer716 (n + 2) Kd * Av * Phi N q + Eb with hKmaindef
  set K3 : ℝ := (v N - s N) * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q + Eb2)
    with hK3def
  have hKmain0 : (0 : ℝ) ≤ Kmain := by
    rw [hKmaindef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716 (n + 2) Kd * Av * Phi N q := by positivity
    linarith
  have hvs : (0 : ℝ) ≤ v N - s N := by linarith
  have hK30 : (0 : ℝ) ≤ K3 := by
    rw [hK3def]
    have hPE := hPhiE0 N q
    have : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q := by positivity
    exact mul_nonneg hvs (by linarith)
  -- the per-time bound shared by the four `‖·‖_{2p}` terms
  set Mb : ℝ := cKer716 (n + 2) Kd * Av * (C1 * (Np * Phi N q)) + Eb with hMbdef
  have hMb0 : (0 : ℝ) ≤ Mb := by
    rw [hMbdef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716 (n + 2) Kd * Av * (C1 * (Np * Phi N q)) := by positivity
    linarith
  have hMbK : Mb ≤ (C1 + 1) * (Np * Kmain) := by
    rw [hMbdef, hKmaindef]
    have e1 : cKer716 (n + 2) Kd * Av * (C1 * (Np * Phi N q))
        = C1 * (Np * (cKer716 (n + 2) Kd * Av * Phi N q)) := by ring
    rw [e1]
    exact affine_absorb (mul_nonneg (mul_nonneg hcK0 hAv0) (hPhi0 N q)) hEb0 hC10.le hNp1
  -- Term 1: the initial datum of (5.91)
  have hT1 : momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖) ≤ Mb := by
    have key := momNorm_Uker_Qop_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := s N) (v := v N) hs0N le_rfl hsvN hv0 hv1 hκA hKd hζ hδ
      (A := fun ω => SumZeroDyn.lkT X E N (s N) ω q.1) (ψ := ψ N (s N) q)
      (fun ω => hψ0 N (s N) q ω) (hψint (2 * p) N (s N) q)
      (fun ω b => by rw [hbr]; exact hEnvI N q ω b) (fun ω => hDecI N q ω) q.2
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hnn : (0 : ℝ) ≤ cKerSumZero (n + 2) * Kd ^ (2 * (n + 2))
        * (B.scale E N (v N))⁻¹ ^ (n + 2) :=
      mul_nonneg (mul_nonneg (cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
        (pow_nonneg (inv_nonneg.2 hscale.le) _)
    have hstep := mul_le_mul_of_nonneg_left (h1 (s N) le_rfl hsvN q) hnn
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    linarith [hstep]
  -- Terms 2–4: the three time integrals of (5.91)
  have hI2 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_Qop_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA hKd hζ hδ
      (A := fun ω => H.F N u (X.H N u ω) q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvF N u hu.1 hu.2 q ω b)
      (fun ω => hDecF N u hu.1 hu.2 q ω) q.2
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hnn : (0 : ℝ) ≤ cKerSumZero (n + 2) * Kd ^ (2 * (n + 2))
        * (B.scale E N (v N))⁻¹ ^ (n + 2) :=
      mul_nonneg (mul_nonneg (cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
        (pow_nonneg (inv_nonneg.2 hscale.le) _)
    have hstep := mul_le_mul_of_nonneg_left (h1 u hu.1 hu.2 q) hnn
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    linarith [hstep]
  have hI3 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
            (SumZeroDyn.lkT X E N u ω q.1)) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_commS_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA hKd hζ hδ
      (A := fun ω => SumZeroDyn.lkT X E N u ω q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvC N u hu.1 hu.2 q ω b)
      (fun ω => hDecC N u hu.1 hu.2 q ω) q.2
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hnn : (0 : ℝ) ≤ cKerSumZero (n + 2) * Kd ^ (2 * (n + 2))
        * (B.scale E N (v N))⁻¹ ^ (n + 2) :=
      mul_nonneg (mul_nonneg (cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
        (pow_nonneg (inv_nonneg.2 hscale.le) _)
    have hstep := mul_le_mul_of_nonneg_left (h1 u hu.1 hu.2 q) hnn
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    linarith [hstep]
  have hI4 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) u b) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_PsumVarthetaDot_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA hKd hζ hδ
      (A := fun ω => SumZeroDyn.lkT X E N u ω q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvD N u hu.1 hu.2 q ω b)
      (fun ω => hDecD N u hu.1 hu.2 q ω) q.2
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hnn : (0 : ℝ) ≤ cKerSumZero (n + 2) * Kd ^ (2 * (n + 2))
        * (B.scale E N (v N))⁻¹ ^ (n + 2) :=
      mul_nonneg (mul_nonneg (cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
        (pow_nonneg (inv_nonneg.2 hscale.le) _)
    have hstep := mul_le_mul_of_nonneg_left (h1 u hu.1 hu.2 q) hnn
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    linarith [hstep]
  -- Term 5: the `(Q ⊗ Q)(E ⊗ E)` term of (5.103), under the square root
  have hI5nn : (0 : ℝ) ≤ ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
      ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
        (Fin.append q.2 q.2)‖) :=
    intervalIntegral.integral_nonneg hsvN fun u _ => momNorm_nonneg _ _ _
  have hI5 : (∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
          (Fin.append q.2 q.2)‖))
      ≤ (C3 + 1) * (Np * K3) := by
    have hconst : ∀ u ∈ Set.Icc (s N) (v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
          (Fin.append q.2 q.2)‖)
        ≤ cKer716 ((n + 2) + (n + 2)) Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2 := by
      intro u hu
      have key := momNorm_Uker_QQ_le (P := B.P) (B.L N) hL3 hp0 hE q.1
        (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA hKd hζ hδ
        (A := fun ω => eeFun B E N u (X.H N u ω) q.1) (ψ := ψE N u q)
        (fun ω => hψE0 N u q ω) (hψEint p N u q)
        (fun ω b => by rw [hbr]; exact hEnvE N u hu.1 hu.2 q ω b)
        (fun ω => hDecE N u hu.1 hu.2 q ω) (Fin.append q.2 q.2)
      rw [hbr (v N)] at key
      refine key.trans ?_
      have hnn : (0 : ℝ) ≤ cKerSumZero ((n + 2) + (n + 2)) * Kd ^ (2 * ((n + 2) + (n + 2)))
          * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) :=
        mul_nonneg (mul_nonneg (cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
          (pow_nonneg (inv_nonneg.2 hscale.le) _)
      have hstep := mul_le_mul_of_nonneg_left (h3 u hu.1 hu.2 q) hnn
      rw [hAv2def, cKer716, hEb2def, errKer716]
      linarith [hstep]
    have hbase : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q :=
      mul_nonneg (mul_nonneg hcK20 hAv20) (hPhiE0 N q)
    have hfac : cKer716 ((n + 2) + (n + 2)) Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2
        ≤ (C3 + 1) * (Np * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q + Eb2)) := by
      have e1 : cKer716 ((n + 2) + (n + 2)) Kd * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q)) := by ring
      rw [e1]
      exact affine_absorb hbase hEb20 hC30.le hNp1
    have hMnn : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2 := by
      have h0 : (0 : ℝ) ≤ C3 * (Np * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q)) :=
        mul_nonneg hC30.le (mul_nonneg hNp0.le hbase)
      have e1 : cKer716 ((n + 2) + (n + 2)) Kd * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q)) := by ring
      rw [e1]
      linarith
    refine (intervalIntegral_le_of_le_const hsvN hMnn hconst).trans ?_
    rw [hK3def]
    calc (v N - s N) * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * (C3 * (Np * PhiE N q)) + Eb2)
        ≤ (v N - s N)
            * ((C3 + 1) * (Np * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q + Eb2))) :=
          mul_le_mul_of_nonneg_left hfac hvs
      _ = (C3 + 1) * (Np * ((v N - s N)
            * (cKer716 ((n + 2) + (n + 2)) Kd * Av2 * PhiE N q + Eb2))) := by ring
  have hT5 : (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
        ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
          (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
      ≤ Csq * (Np * K3 ^ ((1 : ℝ) / 2)) := by
    have hstep : (H.cMD p * ∫ u in (s N)..(v N), momNorm B.P p (fun ω =>
          ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
            (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
            (Fin.append q.2 q.2)‖)) ^ ((1 : ℝ) / 2)
        ≤ ((H.cMD p * (C3 + 1)) * (Np * K3)) ^ ((1 : ℝ) / 2) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      calc H.cMD p * _ ≤ H.cMD p * ((C3 + 1) * (Np * K3)) :=
            mul_le_mul_of_nonneg_left hI5 hcMD
        _ = (H.cMD p * (C3 + 1)) * (Np * K3) := by ring
    refine hstep.trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hNp0.le hK30, ← hCsqdef]
    have hhalf : Np ^ ((1 : ℝ) / 2) ≤ Np := by
      calc Np ^ ((1 : ℝ) / 2) ≤ Np ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hNp1 (by norm_num)
        _ = Np := Real.rpow_one Np
    have hK3s : (0 : ℝ) ≤ K3 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hK30 _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhalf hK3s) hCsq0
  -- assemble
  have hK3s : (0 : ℝ) ≤ K3 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hK30 _
  have hfour : Mb + 2 * ((v N - s N) * Mb) + 2 * ((v N - s N) * Mb) + 2 * ((v N - s N) * Mb)
      ≤ (C1 + 1) * (Np * (Kmain * (1 + 6 * (v N - s N)))) := by
    have h6 : Mb * (1 + 6 * (v N - s N))
        ≤ ((C1 + 1) * (Np * Kmain)) * (1 + 6 * (v N - s N)) :=
      mul_le_mul_of_nonneg_right hMbK (by linarith)
    linarith [h6]
  have hmain : Mb + 2 * ((v N - s N) * Mb) + 2 * ((v N - s N) * Mb) + 2 * ((v N - s N) * Mb)
        + Csq * (Np * K3 ^ ((1 : ℝ) / 2))
      ≤ (C1 + Csq + 1) * (Np * (Kmain * (1 + 6 * (v N - s N)) + K3 ^ ((1 : ℝ) / 2))) := by
    have hpos : (0 : ℝ) ≤ Np * (Kmain * (1 + 6 * (v N - s N))) :=
      mul_nonneg hNp0.le (mul_nonneg hKmain0 (by linarith))
    have t1 : (0 : ℝ) ≤ Csq * (Np * (Kmain * (1 + 6 * (v N - s N)))) := mul_nonneg hCsq0 hpos
    have t2 : (0 : ℝ) ≤ (C1 + 1) * (Np * K3 ^ ((1 : ℝ) / 2)) :=
      mul_nonneg (by linarith) (mul_nonneg hNp0.le hK3s)
    linarith [hfour, t1, t2]
  refine le_trans (by linarith [hT1, hI2, hI3, hI4, hT5]) (hmain.trans ?_)
  have hfin := hnumN q
  rw [← hKmaindef, ← hK3def] at hfin
  have hC : (0 : ℝ) ≤ C1 + Csq + 1 := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin hNp0.le) hC

end Producer

end RBM.Gauss
