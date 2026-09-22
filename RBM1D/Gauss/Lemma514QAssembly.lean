/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Holder
import RBM1D.Gauss.MomentDuhamelQ
import RBM1D.Gauss.Lemma514QRoute
import RBM1D.Gauss.Lemma514NonAlt
import RBM1D.Gauss.LkGoodMeasurable
import RBM1D.Gauss.Step6EnvWindow
import RBM1D.Gauss.Lemma514XiPoly
import RBM1D.Hierarchy.DriftBound

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
2. `RBM.Gauss.stochDom_lkT_qGood_of_Qhalf_Phalf` and
   `RBM.Gauss.stochDom_lkT_of_qGood_nonAlt` — (5.101) at the level of `≺` on `QGood` charges,
   and §5.5's charge split that glues the two classes back together;
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
5. §6, the satisfiability witness on the paper's own p. 24 grid.

## What is **gone** from the hypothesis list

`hkerC` and `hker2C` — the (7.1)-tier `edgeKer` row sums, retired by T201 — do not occur
anywhere below.  The producer of §5 takes instead, for each of the five tensors, the
size envelope and the fast decay (7.13) that (7.16) asks for.  There is no short-window
hypothesis and no `0 < s N` on the `Q` side.

## Where (5.101) stops, and what replaces it

`RBM.MomentDuhamel.stochDom_of_momentDuhamelQ` controls `‖Q_v ∘ (L-K)_v‖`, not `‖(L-K)_v‖`, and
(5.101) is `A = Q_t A + (P A) ϑ_t` (`RBM.SumZeroDyn.norm_le_norm_Qop_add`).  The second summand
splits along §5.5's own charge classification:

* on `QGood` charges it is `RBM.Gauss.PHalf514`, and that is **a theorem**
  (`RBM.Gauss.pHalf514_of_wardP`, from T218's `RBM.Gauss.stochDom_Psum_vartheta_qGood`): its
  deterministic core is Ward's (5.96) `RBM.SumZeroDyn.norm_Psum_lkT_le` and (5.87)
  `RBM.SumZeroDyn.norm_vartheta_real_le`, and the only random input it needs is the
  `m = n + 1 < n + 2` slot of `RBM.Gauss.Lemma514Premises`.  Its price is `0 < s N`,
  `RBM.Cond272`, `RBM.SumZeroDyn.WardP` (a theorem) and `RBM.SumZeroDyn.LKDecay`;
* off `QGood` the `P` half **cannot** be used at all.  T218's
  `RBM.Gauss.pow_card_le_of_norm_Psum_le` proves that an unguarded slot-sum bound costs `L^n`
  and that this is attained, while the shared normalisation `A_v^{-(n+2)}` carries no positive
  power of `L`.  Those charges are non-alternating
  (`RBM.SumZeroDyn.eq_zero_of_not_nonAlt_not_qGood`) and go through (5.20) with (7.16) Case 1,
  which **T236** supplies from the unprojected `RBM.MomentDuhamel.Hyp.momentDuhamel` in
  `RBM1D/Gauss/Lemma514NonAlt.lean` (`RBM.Gauss.stochDom_lkT_nonAlt_of_momentDuhamel`, fed by
  `RBM.Gauss.RhsNonAltAt`).

## What used to be nobody's, and is not any more (T236)

The slot `RBM.Gauss.NonAlt514` — the `¬ QGood` branch whose only producer in the repository was
`RBM.SumZeroDyn.bound_nonAlt`, inside the forbidden `RBM.SumZeroDyn.Hierarchy` +
`RBM.SumZeroDyn.Lemma510` package — is **gone**.  `lemma514_of_momentDuhamelQ` now takes
`hrhsNA`, the (7.16) **Case 1** kernel-tier right-hand side `RBM.Gauss.RhsNonAltAt`, which is
the same kind of input as `hrhs` and has both a producer
(`RBM.Gauss.rhsNonAltAt_of_kernel_inputs`) and a satisfiability witness on the paper's grid
(`RBM.Gauss.gridS_short_witness`).  Neither `RBM.SumZeroDyn.Hierarchy` nor
`RBM.SumZeroDyn.Lemma510` occurs anywhere in this file's hypothesis lists.

## Deviations from the paper

Recorded in `docs/paper-deltas.md` as **`T219a`**: the five `hDec…` rows of
`RBM.Gauss.rhs514QAt_of_kernel_inputs` are quantified over **every** sample point `ω`, whereas
the paper's (7.13) and the a priori bounds behind (7.16) hold on a high-probability event.  For
the `hEnv…` rows this costs nothing — the right-hand side carries the random `ψ_u(ω)` and the
strength sits in the moment rows `hMψ`/`hMψE` — but for `hDec…` it is a real strengthening: at
a sample point where the loop does not decay, no small `δ` exists.

**T246 closes it.**  `RBM.Gauss.rhs514QAt_of_kernel_inputs'` (§5b) is the same producer with
every `hDec…` row restricted to `∀ ω ∈ Ξ N`, built on T237's
`RBM.Gauss.momNorm_Uker_Qop_event_untrunc_le` and its three siblings.  `Ξ` carries **no**
`MeasurableSet` hypothesis — T237 takes the measurable core `RBM.Gauss.measCore` internally
(`RBM.Gauss.measurableSet_measCore`, `RBM.Gauss.measCore_subset`,
`RBM.Gauss.measure_compl_measCore`), so `∀ ω ∈ Ξ` and `RBM.HighProb` are inherited verbatim and
no estimate changes.  `RBM.Gauss.rhs514QAt_of_kernel_inputs` is kept as the `∀ ω` variant: it
is a true theorem with a strictly stronger hypothesis table, and `…_zero_err` still uses it.

Nothing here is an `axiom` and nothing here is `sorry`.
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

/-- Spend half of the stochastic-domination exponent on an epsilon-dependent kernel
control. The remaining half is supplied by the existing moment producer. -/
theorem rhs514QAt_of_scaled_family (H : MomentDuhamel.Hyp X E s t n)
    (c v : ℕ → ℝ)
    (h : ∀ η > (0 : ℝ), ∃ C₀ > (0 : ℝ),
      Rhs514QAt H (fun N => C₀ * (N : ℝ) ^ (η / 2) * c N) v) :
    Rhs514QAt H c v := by
  intro ε hε p hp
  obtain ⟨C₀, hC₀, hR⟩ := h (ε / 2) (by linarith)
  obtain ⟨C, hC, hN⟩ := hR (ε / 2) (by linarith) p hp
  refine ⟨C * C₀, mul_pos hC hC₀, ?_⟩
  filter_upwards [hN, eventually_gt_atTop 0] with N hN hN0 q
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hpow : (N : ℝ) ^ ((ε / 2) / 2) * (N : ℝ) ^ ((ε / 2) / 2)
      = (N : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hNr]
    congr 1
    ring
  convert hN q using 1
  rw [← hpow]
  ring

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

/-- **(5.101) at the level of `≺`, on `QGood` charges.**
`RBM.SumZeroDyn.norm_le_norm_Qop_add` is the pointwise identity `A = Q_t ∘ A + (P ∘ A) ϑ_t`;
here it is pushed through `RBM.StochDom.add` and `RBM.StochDom.of_le_left`.

**The `QGood` guard on the `P`-half is not cosmetic.**  T218's
`RBM.Gauss.pow_card_le_of_norm_Psum_le` is a compiled proof that any constant `C` with
`‖(P ∘ A)_x‖ ≤ C · sup ‖A‖` for *every* tensor `A` satisfies `L^n ≤ C`, with equality at the
constant tensor; the normalisation `A_v^{-(n+2)}` that the two halves of (5.101) share carries
no positive power of `L`, so an unguarded `P`-half is **unsatisfiable**.  (This corrects the
unguarded `PHalf514` of the first draft of this file.)  Off `QGood` the assembly therefore does
**not** use (5.101) at all — it uses (5.20) + (7.16) Case 1, i.e. T236's
`RBM.Gauss.stochDom_lkT_nonAlt_of_momentDuhamel`.

The `Q`-half stays unguarded, because `RBM.MomentDuhamel.Hyp.momentDuhamelQ` is quantified over
every charge; guarding it only weakens it, which is the first `split_ifs` branch below. -/
theorem stochDom_lkT_qGood_of_Qhalf_Phalf {P : Measure Ω} {n : ℕ} {v : ℕ → ℝ} {cQ cP : ℕ → ℝ}
    (hQ : StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        ‖Qop (B.L N) ((v N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (v N) ω q.1) q.2‖)
      (fun N _ _ => cQ N))
    (hP : StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood q.1 then
          ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω q.1) (q.2 0)‖
            * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) q.2‖
        else 0)
      (fun N _ _ => cP N)) :
    StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood q.1 then ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0)
      (fun N _ _ => cQ N + cP N) := by
  classical
  refine StochDom.of_le_left (fun N q ω => ?_) (hQ.add hP)
  simp only [Pi.add_apply]
  split_ifs with h
  · exact SumZeroDyn.norm_le_norm_Qop_add (B.L N) ((v N : ℝ) : ℂ)
      (SumZeroDyn.lkT X E N (v N) ω q.1) q.2
  · rw [add_zero]; exact norm_nonneg _

/-- **The two charge classes add up to the whole of `Ξ^{(L-K)}`.**  `QGood` is decidable, so
`|A| ≤ (if QGood then |A| else 0) + (if QGood then 0 else |A|)` holds with equality; the point
of stating it is that the two summands have *different producers* — (5.101) for `QGood` and
(5.20) for the rest, exactly the split of `RBM.SumZeroDyn.lemma514_flow`. -/
theorem stochDom_lkT_of_qGood_nonAlt {P : Measure Ω} {n : ℕ} {v : ℕ → ℝ} {c1 c2 : ℕ → ℝ}
    (h1 : StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood q.1 then ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0)
      (fun N _ _ => c1 N))
    (h2 : StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω =>
        if SumZeroDyn.QGood q.1 then 0 else ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
      (fun N _ _ => c2 N)) :
    StochDom P
      (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
      (fun N _ _ => c1 N + c2 N) := by
  classical
  refine StochDom.of_le_left (fun N q ω => ?_) (h1.add h2)
  simp only [Pi.add_apply]
  split_ifs with h
  · rw [add_zero]
  · rw [zero_add]

end Split

/-! ### §3  `RBM.Step3.Lemma514` on the `Q` route -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The `P`-half of (5.101) in the shape the assembly consumes, on `QGood` charges** (T218).

This is a `≺` for the second summand of `RBM.SumZeroDyn.norm_le_norm_Qop_add`, at every
terminal time of the window, with the same control `(Λ^{1/2} + Φ) (W ℓ_v η_v)^{-(n+2)}` the
`Q`-half carries.  Its deterministic input is (5.96), `RBM.SumZeroDyn.norm_Psum_lkT_le`, whose
hypothesis `Ξ^{(L-K)}_{v,n+1} ≺ Φ` is the premise of `RBM.Gauss.Lemma514Premises` at
`m = n + 1` — which is why the premises are passed in.

**The `QGood` guard is mandatory** (T218, `RBM.Gauss.pow_card_le_of_norm_Psum_le`): unguarded,
the slot sum costs `L^n` and that is optimal, so the unguarded statement is unsatisfiable
against the `L`-free normalisation `A_v^{-(n+2)}`.  It is discharged by
`RBM.Gauss.pHalf514_of_wardP` below — it is **a theorem**, not an open slot. -/
def PHalf514 (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
    Lemma514Premises X E s t (n + 2) Λ Φ →
    ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω =>
          if SumZeroDyn.QGood q.1 then
            ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω q.1) (q.2 0)‖
              * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) q.2‖
          else 0)
        (fun N _ _ => (Λ N ^ ((1 : ℝ) / 2) + Φ N) * (B.scale E N (v N) ^ (n + 2))⁻¹)

omit [IsProbabilityMeasure B.P] in
/-- **`RBM.Gauss.PHalf514` is a theorem.**  It is T218's
`RBM.Gauss.stochDom_Psum_vartheta_qGood` applied at the `m = n + 1` slot of
`RBM.Gauss.Lemma514Premises` — the second conjunct, at `1 ≤ n + 1 < n + 2`.

Its price is the three inputs T218's `P`-half needs and this file's `Q`-half does not:
`0 < s N` (strict, where the `Q`-route only wants `0 ≤ s N`), `RBM.Cond272` (2.72), Ward's
identity `RBM.SumZeroDyn.WardP` (a theorem, `RBM.SumZeroDyn.wardP_holds`) and Lemma 5.9 (5.75)
`RBM.SumZeroDyn.LKDecay` (reducible to `RBM.LKDecayQuant.FlowInputs`). -/
theorem pHalf514_of_wardP (hE : |E| < 2) (hs0 : ∀ N, 0 < s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) (hW : SumZeroDyn.WardP X E n)
    (hdec : SumZeroDyn.LKDecay X E s t) : PHalf514 X E s t n := by
  intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
  exact stochDom_Psum_vartheta_qGood X hE hs0 hst ht1 hcond hW hdec hΛ0 hΦ0 hΛ1
    (hprem.2.1 (n + 1) (by omega) (by omega)) v hv

/-! **The non-alternating charges, the half of §5.5 that (5.101) does not reach.**

`RBM.Gauss.NonAlt514` — the `¬ QGood` slot this file used to carry, whose only producer was
`RBM.SumZeroDyn.bound_nonAlt` inside the forbidden `RBM.SumZeroDyn.Hierarchy` package — is
**gone** (T236).  In its place `lemma514_of_momentDuhamelQ` takes `hrhsNA`, the (7.16) **Case 1**
right-hand side `RBM.Gauss.RhsNonAltAt` of `RBM1D/Gauss/Lemma514NonAlt.lean`, which is the same
*kind* of input as `hrhs`: a kernel-tier estimate with a producer
(`RBM.Gauss.rhsNonAltAt_of_kernel_inputs`) and a satisfiability witness
(`RBM.Gauss.gridS_short_witness`).  The `≡` for the non-alternating charges is then the theorem
`RBM.Gauss.stochDom_lkT_nonAlt_of_momentDuhamel`, which uses only the **unprojected** field
`RBM.MomentDuhamel.Hyp.momentDuhamel`.

The length-`2` exception `σ = (-,+)` — neither `QGood` nor non-alternating — is folded in by
`RBM.Gauss.stochDom_lkT_of_qGood_nonAlt'`, exactly as `RBM.SumZeroDyn.lemma514_flow` folds it
in, through `RBM.SumZeroDyn.lkT_swap2` and `RBM.SumZeroDyn.qGood_swap2`. -/

/-- **`RBM.Step3.Lemma514` from `RBM.MomentDuhamel.Hyp.momentDuhamelQ`.**

The `Q`-route twin of `RBM.Gauss.lemma514_of_momentDuhamel`.  Three things differ:

* `hrhs` is `RBM.Gauss.Rhs514QAt` — five terms, every tensor projected — and **not**
  `RBM.Gauss.Rhs514At`.  Consequently the (7.1)-tier row sums `hkerC`/`hker2C`, which T201
  proved have no `N`-independent constant on the paper's grid, do not appear;
* one new hypothesis, `RBM.MomentDuhamel.QIntegrable`, which on the Gaussian model is the
  theorem `RBM.MomentDuhamel.qIntegrable_gauss` (paper-delta T214a);
* two new hypotheses, `RBM.Gauss.PHalf514` and `hrhsNA`, because (5.91) bounds `Q_v ∘ (L-K)_v`
  and the conclusion is about `(L-K)_v`.  The first is **a theorem**
  (`RBM.Gauss.pHalf514_of_wardP`, from T218); the second is the (7.16) **Case 1** right-hand
  side `RBM.Gauss.RhsNonAltAt` of `RBM1D/Gauss/Lemma514NonAlt.lean` (T236), the non-alternating
  branch of §5.5's charge split — a kernel-tier slot with a producer and a grid witness, **not**
  the old `RBM.Gauss.NonAlt514`, and in particular **not**
  `RBM.SumZeroDyn.Hierarchy`/`Lemma510`.

The control is raised to `max (Λ^{1/2} + Φ) 1` inside the proof for the same reason as in the
plain route.  The two halves of (5.101) double it on `QGood` charges, the `(-,+)` exception
doubles that again (`RBM.Gauss.stochDom_lkT_of_qGood_nonAlt'` reuses the `QGood` control at the
rotated charge), and the non-alternating branch adds one more, whence `C = 5` in the final
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
    (hPhalf : PHalf514 X E s t n)
    (hrhsNA : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) → (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) →
      Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        RhsNonAltAt H (fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1) v) :
    Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) (n + 2) := by
  classical
  intro Λ Φ hΛ0 hΦ0 hΛ1 hY hX1 hX2 hY1
  have hc1 : ∀ N : ℕ, (1 : ℝ) ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := fun N => le_max_right _ _
  have hc0 : ∀ N : ℕ, (0 : ℝ) ≤ 5 * max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 := fun N => by
    have := hc1 N; linarith
  have hscale : ∀ (N : ℕ) (w : ℝ), w ∈ Set.Icc (s N) (t N) →
      0 < B.scale E N w ^ (n + 2) := fun N w hw =>
    pow_pos (B.scale_pos' hE N ((hs0 N).trans hw.1) (hw.2.trans_lt (ht1 N))) _
  have hseq : ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω => ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖)
        (fun N _ _ => 5 * max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
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
    -- the `P`-half on `QGood` charges (T218, `RBM.Gauss.pHalf514_of_wardP`)
    have hP := hPhalf Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩ v hv
    have hmaxle : ∀ N : ℕ, (Λ N ^ ((1 : ℝ) / 2) + Φ N) * (B.scale E N (v N) ^ (n + 2))⁻¹
        ≤ 1 * (max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 * (B.scale E N (v N) ^ (n + 2))⁻¹) := by
      intro N
      have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
      have hinv : (0 : ℝ) ≤ (B.scale E N (v N) ^ (n + 2))⁻¹ := (inv_pos.2 hsc).le
      have hle : Λ N ^ ((1 : ℝ) / 2) + Φ N ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 :=
        le_max_left _ _
      rw [one_mul]
      gcongr
    have hcpos : ∀ N : ℕ, (0 : ℝ) ≤ max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
        * (B.scale E N (v N) ^ (n + 2))⁻¹ := by
      intro N
      have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
      have := hc1 N
      positivity
    have hPle : StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω =>
          if SumZeroDyn.QGood q.1 then
            ‖Psum (B.L N) (SumZeroDyn.lkT X E N (v N) ω q.1) (q.2 0)‖
              * ‖vartheta (B.L N) ((v N : ℝ) : ℂ) q.2‖
          else 0)
        (fun N _ _ => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
          * (B.scale E N (v N) ^ (n + 2))⁻¹) :=
      Step3.stochDom_mono (fun N _ _ => hcpos N) 1
        (Eventually.of_forall fun N _ _ => hmaxle N) hP
    -- the non-alternating charges: (5.20) + (7.16) Case 1, T236
    have hNAle : StochDom B.P
        (fun N (q : LoopData (B.L N) (n + 2)) ω =>
          if SumZeroDyn.NonAlt q.1 then ‖SumZeroDyn.lkT X E N (v N) ω q.1 q.2‖ else 0)
        (fun N _ _ => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1
          * (B.scale E N (v N) ^ (n + 2))⁻¹) :=
      stochDom_lkT_nonAlt_of_momentDuhamel hE hs0 ht1 H hcard
        (c := fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1)
        (fun N => lt_of_lt_of_le one_pos (hc1 N)) v hv
        (hrhsNA Λ Φ hΛ0 hΦ0 hΛ1 ⟨hY, hX1, hX2, hY1⟩ v hv)
    have hsum := stochDom_lkT_of_qGood_nonAlt' (X := X) hE
      (fun N => (hs0 N).trans (hv N).1) (fun N => ((hv N).2).trans_lt (ht1 N))
      (stochDom_lkT_qGood_of_Qhalf_Phalf hQ hPle) hNAle
    refine Step3.stochDom_mono (fun N _ _ => ?_) 1 (Eventually.of_forall fun N _ _ => ?_) hsum
    · have hsc : (0 : ℝ) < B.scale E N (v N) ^ (n + 2) := hscale N (v N) (hv N)
      have := hc1 N
      positivity
    · rw [one_mul]
      ring_nf
      exact le_rfl
  have hmain := stochDom_flowXiLK_of_seq X hE hs0 hst ht1 hcard hK hγ hΞ hc0
    (Eventually.of_forall fun N => by have := hc1 N; linarith) hHol hseq
  refine Step3.stochDom_mono (fun N _ _ => ?_) 5 ?_ hmain
  · have h1 : (0 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (hΛ0 N) _
    have := hΦ0 N
    linarith
  · filter_upwards [hΛ1] with N hN _ _
    have h1 : (1 : ℝ) ≤ Λ N ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN (by norm_num)
    have := hΦ0 N
    have : max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1 = Λ N ^ ((1 : ℝ) / 2) + Φ N :=
      max_eq_left (by linarith)
    rw [this]

/-- Assemble Lemma 5.14 from epsilon-dependent kernel producers on both charge classes.
The remaining hypotheses are the scaled producer outputs, with the kernel parameters
chosen after the exponent. -/
theorem lemma514_of_momentDuhamelQ_of_scaled_families (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
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
    (hrhsScaled : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      ∀ η > (0 : ℝ), ∃ C₀ > (0 : ℝ),
        Rhs514QAt H (fun N => C₀ * (N : ℝ) ^ (η / 2) *
          (Λ N ^ ((1 : ℝ) / 2) + Φ N)) v)
    (hPhalf : PHalf514 X E s t n)
    (hrhsNAScaled : ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
      ∀ η > (0 : ℝ), ∃ C₀ > (0 : ℝ),
        RhsNonAltAt H (fun N => C₀ * (N : ℝ) ^ (η / 2) *
          max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1) v) :
    Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) (n + 2) := by
  apply lemma514_of_momentDuhamelQ hE hs0 hst ht1 H hQint hcard hK hγ hΞ hHol
  · intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
    exact rhs514QAt_of_scaled_family H _ _
      (hrhsScaled Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv)
  · exact hPhalf
  · intro Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv
    exact rhsNonAltAt_of_scaled_family H _ _
      (hrhsNAScaled Λ Φ hΛ0 hΦ0 hΛ1 hprem v hv)

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
    (hPhalf : ∀ n : ℕ, PHalf514 X E s t n)
    (hrhsNA : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises X E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        RhsNonAltAt (H n) (fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1) v) :
    ∀ m, 2 ≤ m → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) m := by
  intro m hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact lemma514_of_momentDuhamelQ hE hs0 hst ht1 (H n) (hQint n) (card_loopData_le (n + 2))
    hK hγ hΞ (hHol (n + 2)) (hrhs n) (hPhalf n) (hrhsNA n)

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
no `hker2C` and no short-window condition**, and `0 ≤ s N` suffices here; discharging `hPhalf`
through `RBM.Gauss.pHalf514_of_wardP` does need the strict `0 < s N`. -/
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
    (hPhalf : ∀ n : ℕ, PHalf514 (sample d) E s t n)
    (hrhsNA : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises (sample d) E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        RhsNonAltAt (H n) (fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1) v) :
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
      (hKb_flow (band d) hE ht1 hc0 (n + 2) hreg)) (hrhs n) (hPhalf n) (hrhsNA n)

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
    (hrhsNA : ∀ n : ℕ, ∀ Λ Φ : ℕ → ℝ, (∀ N, 0 ≤ Λ N) → (∀ N, 0 ≤ Φ N) →
      (∀ᶠ N : ℕ in atTop, 1 ≤ Λ N) → Lemma514Premises (sample d) E s t (n + 2) Λ Φ →
      ∀ v : ℕ → ℝ, (∀ N, v N ∈ Set.Icc (s N) (t N)) →
        RhsNonAltAt (H n) (fun N => max (Λ N ^ ((1 : ℝ) / 2) + Φ N) 1) v)
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
      hrhs hPhalf hrhsNA)
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

theorem cKer716_nonneg (m : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd) : 0 ≤ cKer716 m Kd :=
  mul_nonneg (SumZeroDyn.cKerSumZero_nonneg m) (pow_nonneg hKd _)

/-- The Case-2 kernel coefficient consumes only `2m * τ` of the stochastic-domination
exponent when the undilated radius is at most `N^τ`. -/
theorem cKer716_four_le_rpow (m N : ℕ) {Kd τ η : ℝ}
    (hN : (1 : ℝ) ≤ N) (hKd : 0 ≤ Kd) (hKdN : Kd ≤ (N : ℝ) ^ τ)
    (hτη : τ * ((2 * m : ℕ) : ℝ) ≤ η) :
    cKer716 m (4 * Kd) ≤ cKerSumZero m * 4 ^ (2 * m) * (N : ℝ) ^ η := by
  have hfour : 4 * Kd ≤ 4 * (N : ℝ) ^ τ := by gcongr
  have hpow : (4 * Kd) ^ (2 * m) ≤ (4 * (N : ℝ) ^ τ) ^ (2 * m) := by gcongr
  have hc : 0 ≤ cKerSumZero m := SumZeroDyn.cKerSumZero_nonneg m
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by linarith
  calc
    cKer716 m (4 * Kd) = cKerSumZero m * (4 * Kd) ^ (2 * m) := rfl
    _ ≤ cKerSumZero m * (4 * (N : ℝ) ^ τ) ^ (2 * m) :=
      mul_le_mul_of_nonneg_left hpow hc
    _ = cKerSumZero m * 4 ^ (2 * m) * (N : ℝ) ^ (τ * ((2 * m : ℕ) : ℝ)) := by
      have hr : ((N : ℝ) ^ τ) ^ (2 * m) = (N : ℝ) ^ (τ * ((2 * m : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast ((N : ℝ) ^ τ) (2 * m), ← Real.rpow_mul hN0]
      rw [mul_pow, hr]
      ring
    _ ≤ cKerSumZero m * 4 ^ (2 * m) * (N : ℝ) ^ η := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hτη)
        (mul_nonneg hc (by positivity))

theorem errKer716_nonneg (L m : ℕ) {Kd ζ δ s v : ℝ} (hKd : 0 ≤ Kd) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    (hsv : s ≤ v) (hv1 : v < 1) : 0 ≤ errKer716 L m Kd ζ δ s v := by
  have h1 : (0 : ℝ) < 1 - v := by linarith
  have h2 : (0 : ℝ) ≤ (1 - s) / (1 - v) := div_nonneg (by linarith) h1.le
  have hr : (0 : ℝ) ≤ ((1 - s) / (1 - v)) ^ m := pow_nonneg h2 m
  have hc1 := SumZeroDyn.cKerSumZero_nonneg m
  have hc2 := SumZeroDyn.cKerSumZeroErr_nonneg m
  have hKm : (0 : ℝ) ≤ Kd ^ (2 * m) := pow_nonneg hKd _
  have hLm : (0 : ℝ) ≤ (L : ℝ) ^ m := by positivity
  have t1 : (0 : ℝ) ≤ cKerSumZero m * Kd ^ (2 * m) * ((1 - s) / (1 - v)) ^ m * ζ :=
    mul_nonneg (mul_nonneg (mul_nonneg hc1 hKm) hr) hζ
  have t2 : (0 : ℝ) ≤ cKerSumZeroErr m * (L : ℝ) ^ m * ((1 - s) / (1 - v)) ^ m * δ :=
    mul_nonneg (mul_nonneg (mul_nonneg hc2 hLm) hr) hδ
  unfold errKer716
  linarith

/-! `RBM.Gauss.affine_absorb` and `RBM.Gauss.scale_eq_kappaA` used to live here.  T236 needs
them verbatim for the Case-1 producer of `RBM1D/Gauss/Lemma514NonAlt.lean`, so they were
**moved** into that file (which this one imports) rather than copied. -/

/-- **The producer of `RBM.Gauss.Rhs514QAt` out of T201's five kernel estimates.**

Hypothesis table, with the owner of each row:

| row | what | owner |
|---|---|---|
| `hEnvI`…`hEnvE` | the size envelope of (7.16) | Step 2's a priori bounds |
| `hDecI`…`hDecE` | the fast decay (7.13) | **T220** (`FastDecayFlow`) |
| `hMψ`, `hMψE` | `‖ψ_u‖_{2p} ≺ Φ` on the window | the drift / `E⊗E` moment bounds |
| `hnum` | the arithmetic of (5.24) | **discharged**, §6 below |

The envelope row reads `‖T‖ ≤ (W ℓ_u η_u)^{-m} ψ_u + ζ` and the decay row is (7.13) for the
same five tensors.  ⚠ Both are quantified over **every** `ω`; that is the shape T201's
`hGM`/`hGd` slots have, and for `hGd` it is the pattern the project's satisfiability discipline
forbids (a deterministic decay bound cannot hold at a "large constant times the identity"
sample point with a small `δ`).

**Use `RBM.Gauss.rhs514QAt_of_kernel_inputs'` of §5b instead** — T246 — whose `hDec…` rows read
`∀ ω ∈ Ξ N`.  The `MeasurableSet (RBM.Gauss.lkGood …)` that T220 recorded as unproved is **not
needed**: T237 replaces `Ξ` by its measurable core `RBM.Gauss.measCore` inside the kernel
estimates (`RBM.Gauss.measurableSet_measCore` / `RBM.Gauss.measurableSet_lkGoodM`), a measurable
subset of `Ξ` with the same complement measure, so `∀ ω ∈ Ξ` and `RBM.HighProb` are inherited
verbatim and the estimates do not change.  This theorem is kept because it is true and because
`RBM.Gauss.rhs514QAt_of_kernel_inputs_zero_err` still consumes it.

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
      mul_nonneg (mul_nonneg (SumZeroDyn.cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
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
      mul_nonneg (mul_nonneg (SumZeroDyn.cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
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
      mul_nonneg (mul_nonneg (SumZeroDyn.cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
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
      mul_nonneg (mul_nonneg (SumZeroDyn.cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
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
        mul_nonneg (mul_nonneg (SumZeroDyn.cKerSumZero_nonneg _) (pow_nonneg hKd0 _))
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

/-! ### §5b  The same producer with (7.13) asked only on an event (T246)

§5 is the (7.16) tier as T201 packaged it: its `hDec…` rows are quantified over **every**
sample point `ω`.  That is the project's headline defect (`docs/paper-deltas.md` 160): at a
sample point where the loop does not decay no small `δ` exists, so a literal reading of those
rows is a statement no model satisfies.  T237 built the replacements —
`RBM.Gauss.momNorm_Uker_Qop_event_untrunc_le` and its three siblings — whose decay premise is
`∀ ω ∈ Ξ` for an event `Ξ` carrying **no** measurability hypothesis (the measurable core
`RBM.Gauss.measCore` is taken inside), and whose conclusion is still about the **untruncated**
tensor.  This section is the rewiring.

Three things change, and nothing else:

* every `hDec…` row becomes `∀ ω ∈ Ξ N`, and it is now the decay of the *tensor* `A` rather
  than of the composed `Q_u ∘ A` — which is what the model actually supplies
  (`RBM.FastDecayFlow.fastDecay_lkT_of_mem_lkGood`);
* the price of going back from `1_Ξ A` to `A` is one extra additive `Env_N · P(Ξᶜ)^{1/q}` per
  term.  It is absorbed by the single new row `cE`, whose two smallness hypotheses are stated
  in the order the moment route needs — `p` first, then `N → ∞` — and are discharged by
  `RBM.Gauss.eventually_env_mul_lkGood_le`;
* T237's error budgets are read at the radius `ℓ_u (4K)` for the three terms that go through
  Lemma 5.13 twice, so the multiplicative constant is `RBM.Gauss.cKer716 m (4 K)` throughout;
  for the two `Q_u` terms, where the radius is not widened, `K^{2m} ≤ (4K)^{2m}` absorbs the
  difference.

**No integrability of `u ↦ Env_N · pr_N^{1/(2p)}` is needed**: `Env` and `pr` do not depend on
`u`, and `RBM.Gauss.intervalIntegral_le_of_le_const` takes no integrability hypothesis at all.

`RBM.Gauss.rhs514QAt_of_kernel_inputs` is kept below it, unchanged: it is a true theorem with a
strictly stronger hypothesis table, and `RBM.Gauss.rhs514QAt_of_kernel_inputs_zero_err` still
consumes it. -/

section ProducerEvent

/-- Monotonicity of a four-factor product in its second and fourth factors.  Used five times
below to trade `K^{2m}` for `(4K)^{2m}` and the term-wise error budget for its uniform
dominant `δ'`. -/
theorem mul_four_le_mul_four {Xc a a' Av Mψ Mψ' : ℝ} (hX : 0 ≤ Xc) (ha : 0 ≤ a) (haa : a ≤ a')
    (hAv : 0 ≤ Av) (hM : 0 ≤ Mψ) (hMM : Mψ ≤ Mψ') :
    Xc * a * Av * Mψ ≤ Xc * a' * Av * Mψ' := by
  have ha'0 : (0 : ℝ) ≤ a' := ha.trans haa
  have h1 : Xc * a * Av ≤ Xc * a' * Av :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haa hX) hAv
  exact mul_le_mul h1 hMM hM (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **The producer of `RBM.Gauss.Rhs514QAt` with the fast decay (7.13) asked only on an
event.**

Hypothesis table, with the owner of each row:

| row | what | owner |
|---|---|---|
| `hEnvI`…`hEnvE` | the size envelope of (7.16), `∀ ω` | Step 2's a priori bounds |
| `hAMI`, `hAMF`, `hPsC`, `hAME` | the a priori sizes, **on `Ξ N`** | Step 2 on the good event |
| `hDecI`, `hDecF`, `hDecE` | the fast decay (7.13), **on `Ξ N`** | T220 / T237 |
| `hErrQ`…`hErrE` | one uniform dominant `δ'` for T237's four error budgets | deterministic |
| `hZI`…`hZEint` | a deterministic envelope `Env_N` for the kernel | `‖G‖ ≤ η⁻¹` |
| `hPr`, `hEnvPr`, `hEnvPrE` | the Markov price of the split | `RBM.HighProb` |
| `hMψ`, `hMψE` | `‖ψ_u‖_{2p} ≺ Φ` on the window | the drift / `E⊗E` moment bounds |
| `hnum` | the arithmetic of (5.24) | see §6 |

`Ξ` carries **no** `MeasurableSet` hypothesis: T237 takes its measurable core internally.
There is no row quantifying a decay statement over all `ω`, and no row quantifying anything
over a time outside `[s N, v N]`.

The four `hErr…` rows are deterministic inequalities between explicit elementary functions of
`u` on the closed window — `RBM.FastDecayFlow.qopErr1` does not depend on `u` at all, and the
other three depend on it only through `(1-u)⁻¹` and `ℓ̂_u`.  They are what replaces the single
symbol `δ` of §5: T237's estimates do not return the input error unchanged, they return the
budget of Lemma 5.13, and that budget is `u`-dependent. -/
theorem rhs514QAt_of_kernel_inputs' (hE : |E| < 2) (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {Kd ζ δ δ' Msz Pb esz : ℕ → ℝ} (hKd : ∀ N, 1 ≤ Kd N) (hζ : ∀ N, 0 ≤ ζ N)
    (hδ : ∀ N, 0 ≤ δ N) (hMsz : ∀ N, 0 ≤ Msz N) (hPb : ∀ N, 0 ≤ Pb N)
    (hesz : ∀ N, 0 ≤ esz N)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1) b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + ζ N)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + ζ N)
    {Ξ : ℕ → Set Ω}
    (hAMI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) (n + 2), ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖ ≤ Msz N)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd N) (δ N)
        (SumZeroDyn.lkT X E N (s N) ω q.1))
    (hAMF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) (n + 2), ‖H.F N u (X.H N u ω) q.1 b‖ ≤ Msz N)
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd N) (δ N) (H.F N u (X.H N u ω) q.1))
    (hPsC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N, ∀ x,
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) x‖ ≤ Pb N)
    (hAME : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)), ‖eeFun B E N u (X.H N u ω) q.1 b‖ ≤ esz N)
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd N) (δ N)
        (eeFun B E N u (X.H N u ω) q.1))
    (hErrQ : ∀ N : ℕ, FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N) ≤ δ' N)
    (hErrC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.commErr (B.L N) n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N)
        ≤ δ' N)
    (hErrD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.dotErr n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N) ≤ δ' N)
    (hErrE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.qqErr (B.L N) (n + 1) (ellHat (B.L N) ((u : ℝ) : ℂ)) (Kd N) (esz N) (δ N)
        ≤ δ' N)
    {Env pr cE : ℕ → ℝ} (hEnv0 : ∀ N, 0 ≤ Env N) (hpr0 : ∀ N, 0 ≤ pr N)
    (hcE0 : ∀ N, 0 ≤ cE N) (hPr : ∀ N, (B.P (Ξ N)ᶜ).toReal ≤ pr N)
    (hZI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖ ≤ Env N)
    (hZIint : ∀ (r N : ℕ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (Qop (B.L N) ((s N : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖ ^ r) B.P)
    (hZF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖ ≤ Env N)
    (hZFint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖ ^ r) B.P)
    (hZC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)) q.2‖ ≤ Env N)
    (hZCint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)) q.2‖ ^ r) B.P)
    (hZD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b) q.2‖ ≤ Env N)
    (hZDint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b) q.2‖ ^ r) B.P)
    (hZE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
        (Fin.append q.2 q.2)‖ ≤ Env N)
    (hZEint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1)) (Fin.append q.2 q.2)‖ ^ r) B.P)
    (hEnvPr : ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      Env N * pr N ^ ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) ≤ cE N)
    (hEnvPrE : ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      Env N * pr N ^ ((1 : ℝ) / ((p : ℕ) : ℝ)) ≤ cE N)
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
      (cKer716 (n + 2) (4 * Kd N) * (B.scale E N (v N))⁻¹ ^ (n + 2) * Phi N q
          + (errKer716 (B.L N) (n + 2) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N))
            * (1 + 6 * (v N - s N))
        + ((v N - s N) * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N)
              * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * PhiE N q
            + (errKer716 (B.L N) ((n + 2) + (n + 2)) (4 * Kd N) (ζ N) (δ' N) (s N) (v N)
              + cE N)))
              ^ ((1 : ℝ) / 2)
        ≤ c N * (B.scale E N (v N) ^ (n + 2))⁻¹) :
    Rhs514QAt H c v := by
  intro ε hε p hp
  obtain ⟨C1, hC10, hA1⟩ := hMψ ε hε p hp
  obtain ⟨C3, hC30, hA3⟩ := hMψE ε hε p hp
  have hcMD := H.cMD_nonneg p
  set Csq : ℝ := (H.cMD p * (C3 + 1)) ^ ((1 : ℝ) / 2) with hCsqdef
  have hCsq0 : 0 ≤ Csq := Real.rpow_nonneg (by positivity) _
  refine ⟨C1 + Csq + 1, by positivity, ?_⟩
  filter_upwards [hA1, hA3, hnum, hEnvPr p hp, hEnvPrE p hp, eventually_ge_atTop 1] with
    N h1 h3 hnumN hEP hEPE hNge q
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge
  have hKd0 : (0 : ℝ) ≤ Kd N := by linarith [hKd N]
  have hKd40 : (0 : ℝ) ≤ 4 * Kd N := by linarith
  have hδ'0 : (0 : ℝ) ≤ δ' N :=
    le_trans (FastDecayFlow.qopErr1_nonneg (B.L N) n hKd0 (hMsz N) (hδ N)) (hErrQ N)
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
  have hell : ∀ u : ℝ, s N ≤ u → u ≤ v N → (0 : ℝ) < ellHat (B.L N) ((u : ℝ) : ℂ) := by
    intro u hua hub
    have := half_le_ellHat_real (B.L N) hL3 (hs0N.trans hua) (lt_of_le_of_lt hub hv1)
    linarith
  have h1s : (0 : ℝ) < 1 - s N := by linarith
  have h1v : (0 : ℝ) < 1 - v N := by linarith
  have hrat : (0 : ℝ) ≤ (1 - s N) / (1 - v N) := (div_pos h1s h1v).le
  have hrm : (0 : ℝ) ≤ ((1 - s N) / (1 - v N)) ^ (n + 2) := pow_nonneg hrat _
  have hrm2 : (0 : ℝ) ≤ ((1 - s N) / (1 - v N)) ^ ((n + 2) + (n + 2)) := pow_nonneg hrat _
  have hscale : (0 : ℝ) < B.scale E N (v N) := B.scale_pos' hE N hv0 hv1
  -- the two normalizations and the two errors, now carrying the Markov price `cE N`
  set Av : ℝ := (B.scale E N (v N))⁻¹ ^ (n + 2) with hAvdef
  set Av2 : ℝ := (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) with hAv2def
  set Eb : ℝ := errKer716 (B.L N) (n + 2) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N with hEbdef
  set Eb2 : ℝ := errKer716 (B.L N) ((n + 2) + (n + 2)) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N
    with hEb2def
  have hEb0 : (0 : ℝ) ≤ Eb := by
    rw [hEbdef]
    have := errKer716_nonneg (B.L N) (n + 2) hKd40 (hζ N) hδ'0 hsvN hv1
    have := hcE0 N
    linarith
  have hEb20 : (0 : ℝ) ≤ Eb2 := by
    rw [hEb2def]
    have := errKer716_nonneg (B.L N) ((n + 2) + (n + 2)) hKd40 (hζ N) hδ'0 hsvN hv1
    have := hcE0 N
    linarith
  have hAv0 : (0 : ℝ) ≤ Av := by rw [hAvdef]; positivity
  have hAv20 : (0 : ℝ) ≤ Av2 := by rw [hAv2def]; positivity
  have hcK0 : (0 : ℝ) ≤ cKer716 (n + 2) (4 * Kd N) := cKer716_nonneg _ hKd40
  have hcK20 : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) := cKer716_nonneg _ hKd40
  set Kmain : ℝ := cKer716 (n + 2) (4 * Kd N) * Av * Phi N q + Eb with hKmaindef
  set K3 : ℝ := (v N - s N) * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2)
    with hK3def
  have hKmain0 : (0 : ℝ) ≤ Kmain := by
    rw [hKmaindef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716 (n + 2) (4 * Kd N) * Av * Phi N q := by positivity
    linarith
  have hvs : (0 : ℝ) ≤ v N - s N := by linarith
  have hK30 : (0 : ℝ) ≤ K3 := by
    rw [hK3def]
    have hPE := hPhiE0 N q
    have : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q := by positivity
    exact mul_nonneg hvs (by linarith)
  set Mb : ℝ := cKer716 (n + 2) (4 * Kd N) * Av * (C1 * (Np * Phi N q)) + Eb with hMbdef
  have hMb0 : (0 : ℝ) ≤ Mb := by
    rw [hMbdef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716 (n + 2) (4 * Kd N) * Av * (C1 * (Np * Phi N q)) := by positivity
    linarith
  have hMbK : Mb ≤ (C1 + 1) * (Np * Kmain) := by
    rw [hMbdef, hKmaindef]
    have e1 : cKer716 (n + 2) (4 * Kd N) * Av * (C1 * (Np * Phi N q))
        = C1 * (Np * (cKer716 (n + 2) (4 * Kd N) * Av * Phi N q)) := by ring
    rw [e1]
    exact affine_absorb (mul_nonneg (mul_nonneg hcK0 hAv0) (hPhi0 N q)) hEb0 hC10.le hNp1
  -- the shared comparison behind the four `‖·‖_{2p}` terms, in raw form
  have hcmp : ∀ a Mψ eT : ℝ, 0 ≤ a → a ≤ (4 * Kd N) ^ (2 * (n + 2)) →
      0 ≤ Mψ → Mψ ≤ C1 * (Np * Phi N q) → 0 ≤ eT → eT ≤ δ' N →
      cKerSumZero (n + 2) * a * (B.scale E N (v N))⁻¹ ^ (n + 2) * Mψ
        + (cKerSumZero (n + 2) * a * ((1 - s N) / (1 - v N)) ^ (n + 2) * ζ N
          + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
              * ((1 - s N) / (1 - v N)) ^ (n + 2) * eT)
        ≤ cKerSumZero (n + 2) * (4 * Kd N) ^ (2 * (n + 2))
              * (B.scale E N (v N))⁻¹ ^ (n + 2) * (C1 * (Np * Phi N q))
          + (cKerSumZero (n + 2) * (4 * Kd N) ^ (2 * (n + 2))
                * ((1 - s N) / (1 - v N)) ^ (n + 2) * ζ N
            + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
                * ((1 - s N) / (1 - v N)) ^ (n + 2) * δ' N) := by
    intro a Mψ eT ha haa hM0 hMle he0 hele
    have hinv : (0 : ℝ) ≤ (B.scale E N (v N))⁻¹ ^ (n + 2) := by positivity
    have p1 := mul_four_le_mul_four (SumZeroDyn.cKerSumZero_nonneg (n + 2)) ha haa hinv hM0 hMle
    have p2 := mul_four_le_mul_four (SumZeroDyn.cKerSumZero_nonneg (n + 2)) ha haa hrm (hζ N)
      (le_refl (ζ N))
    have p3 : cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
          * ((1 - s N) / (1 - v N)) ^ (n + 2) * eT
        ≤ cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
          * ((1 - s N) / (1 - v N)) ^ (n + 2) * δ' N :=
      mul_four_le_mul_four (SumZeroDyn.cKerSumZeroErr_nonneg (n + 2)) (by positivity) le_rfl
        hrm he0 hele
    linarith
  -- Term 1: the initial datum of (5.91)
  have hT1 : momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖) ≤ Mb := by
    have key := momNorm_Uker_Qop_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := s N) (v := v N) hs0N le_rfl hsvN hv0 hv1 hκA (hKd N) (hMsz N) (hζ N) (hδ N)
      (Ξ := Ξ N) (A := fun ω => SumZeroDyn.lkT X E N (s N) ω q.1) (ψ := ψ N (s N) q)
      (fun ω => hψ0 N (s N) q ω) (hψint (2 * p) N (s N) q)
      (fun ω b => by rw [hbr]; exact hEnvI N q ω b)
      (fun ω hω => hAMI N q ω hω) (fun ω hω => hDecI N q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZI N q ω) (hZIint (2 * p) N q) (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp (Kd N ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N (s N) q))
      (FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N)) (by positivity)
      (pow_le_pow_left₀ hKd0 (by linarith) _) (momNorm_nonneg _ _ _) (h1 (s N) le_rfl hsvN q)
      (FastDecayFlow.qopErr1_nonneg (B.L N) n hKd0 (hMsz N) (hδ N)) (hErrQ N)
    rw [hMbdef, hAvdef, hEbdef, cKer716, errKer716]
    linarith
  -- Terms 2–4: the three time integrals of (5.91)
  have hI2 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_Qop_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hMsz N) (hζ N) (hδ N)
      (Ξ := Ξ N) (A := fun ω => H.F N u (X.H N u ω) q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvF N u hu.1 hu.2 q ω b)
      (fun ω hω => hAMF N u hu.1 hu.2 q ω hω) (fun ω hω => hDecF N u hu.1 hu.2 q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZF N u hu.1 hu.2 q ω) (hZFint (2 * p) N u hu.1 hu.2 q)
      (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp (Kd N ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N u q))
      (FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N)) (by positivity)
      (pow_le_pow_left₀ hKd0 (by linarith) _) (momNorm_nonneg _ _ _) (h1 u hu.1 hu.2 q)
      (FastDecayFlow.qopErr1_nonneg (B.L N) n hKd0 (hMsz N) (hδ N)) (hErrQ N)
    rw [hMbdef, hAvdef, hEbdef, cKer716, errKer716]
    linarith
  have hI3 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
            (SumZeroDyn.lkT X E N u ω q.1)) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_commS_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hζ N) (hPb N)
      (Ξ := Ξ N) (A := fun ω => SumZeroDyn.lkT X E N u ω q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvC N u hu.1 hu.2 q ω b)
      (fun ω hω => hPsC N u hu.1 hu.2 q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZC N u hu.1 hu.2 q ω) (hZCint (2 * p) N u hu.1 hu.2 q)
      (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp ((4 * Kd N) ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N u q))
      (FastDecayFlow.commErr (B.L N) n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N))
      (by positivity) le_rfl (momNorm_nonneg _ _ _) (h1 u hu.1 hu.2 q)
      (FastDecayFlow.commErr_nonneg (B.L N) n (hell u hu.1 hu.2)
        (lt_of_le_of_lt hu.2 hv1) hKd0 (hPb N))
      (hErrC N u hu.1 hu.2)
    rw [hMbdef, hAvdef, hEbdef, cKer716, errKer716]
    linarith
  have hI4 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) u b) q.2‖))
      ≤ (v N - s N) * Mb := by
    refine intervalIntegral_le_of_le_const hsvN hMb0 fun u hu => ?_
    have key := momNorm_Uker_dot_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hζ N) (hPb N)
      (Ξ := Ξ N) (A := fun ω => SumZeroDyn.lkT X E N u ω q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvD N u hu.1 hu.2 q ω b)
      (fun ω hω => hPsC N u hu.1 hu.2 q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZD N u hu.1 hu.2 q ω) (hZDint (2 * p) N u hu.1 hu.2 q)
      (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp ((4 * Kd N) ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N u q))
      (FastDecayFlow.dotErr n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N))
      (by positivity) le_rfl (momNorm_nonneg _ _ _) (h1 u hu.1 hu.2 q)
      (FastDecayFlow.dotErr_nonneg n (hell u hu.1 hu.2)
        (lt_of_le_of_lt hu.2 hv1) (hPb N))
      (hErrD N u hu.1 hu.2)
    rw [hMbdef, hAvdef, hEbdef, cKer716, errKer716]
    linarith
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
        ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q)) + Eb2 := by
      intro u hu
      have key := momNorm_Uker_QQ_event_untrunc_le (P := B.P) (B.L N) hL3 hp0 hE q.1
        (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hζ N) (hesz N) (hδ N)
        (Ξ := Ξ N) (A := fun ω => eeFun B E N u (X.H N u ω) q.1) (ψ := ψE N u q)
        (fun ω => hψE0 N u q ω) (hψEint p N u q)
        (fun ω b => by rw [hbr]; exact hEnvE N u hu.1 hu.2 q ω b)
        (fun ω hω => hAME N u hu.1 hu.2 q ω hω) (fun ω hω => hDecE N u hu.1 hu.2 q ω hω)
        (Fin.append q.2 q.2)
        (hEnv0 N) (hpr0 N) (fun ω => hZE N u hu.1 hu.2 q ω) (hZEint p N u hu.1 hu.2 q)
        (hPr N)
      rw [hbr (v N)] at key
      refine key.trans ?_
      have hinv2 : (0 : ℝ) ≤ (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) := by positivity
      have p1 : cKerSumZero ((n + 2) + (n + 2)) * (4 * Kd N) ^ (2 * ((n + 2) + (n + 2)))
            * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * momNorm B.P p (ψE N u q)
          ≤ cKerSumZero ((n + 2) + (n + 2)) * (4 * Kd N) ^ (2 * ((n + 2) + (n + 2)))
            * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * (C3 * (Np * PhiE N q)) :=
        mul_four_le_mul_four (SumZeroDyn.cKerSumZero_nonneg ((n + 2) + (n + 2)))
          (by positivity) le_rfl hinv2 (momNorm_nonneg _ _ _) (h3 u hu.1 hu.2 q)
      have p3 : cKerSumZeroErr ((n + 2) + (n + 2)) * (B.L N : ℝ) ^ ((n + 2) + (n + 2))
            * ((1 - s N) / (1 - v N)) ^ ((n + 2) + (n + 2))
            * FastDecayFlow.qqErr (B.L N) (n + 1) (ellHat (B.L N) ((u : ℝ) : ℂ)) (Kd N)
                (esz N) (δ N)
          ≤ cKerSumZeroErr ((n + 2) + (n + 2)) * (B.L N : ℝ) ^ ((n + 2) + (n + 2))
            * ((1 - s N) / (1 - v N)) ^ ((n + 2) + (n + 2)) * δ' N :=
        mul_four_le_mul_four (SumZeroDyn.cKerSumZeroErr_nonneg ((n + 2) + (n + 2)))
          (by positivity) le_rfl hrm2
          (FastDecayFlow.qqErr_nonneg (B.L N) (n + 1) (hell u hu.1 hu.2) hKd0 (hesz N) (hδ N))
          (hErrE N u hu.1 hu.2)
      rw [hAv2def, hEb2def, cKer716, errKer716]
      linarith
    have hbase : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q :=
      mul_nonneg (mul_nonneg hcK20 hAv20) (hPhiE0 N q)
    have hfac : cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q)) + Eb2
        ≤ (C3 + 1) * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2)) := by
      have e1 : cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q)) := by ring
      rw [e1]
      exact affine_absorb hbase hEb20 hC30.le hNp1
    have hMnn : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q))
        + Eb2 := by
      have h0 : (0 : ℝ) ≤ C3 * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q)) :=
        mul_nonneg hC30.le (mul_nonneg hNp0.le hbase)
      have e1 : cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q)) := by ring
      rw [e1]
      linarith
    refine (intervalIntegral_le_of_le_const hsvN hMnn hconst).trans ?_
    rw [hK3def]
    calc (v N - s N)
          * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q)) + Eb2)
        ≤ (v N - s N) * ((C3 + 1)
            * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2))) :=
          mul_le_mul_of_nonneg_left hfac hvs
      _ = (C3 + 1) * (Np * ((v N - s N)
            * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2))) := by ring
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

/-- The event-restricted kernel producer with an epsilon-dependent kernel package.
The kernel parameters are bound after `η`. Its numeric row has the factor
`C₀ * N^(η/2)`, which is spent by `rhs514QAt_of_scaled_family` when `η` is
chosen after the target stochastic-domination exponent. -/
theorem rhs514QAt_of_kernel_inputs'' (η : ℝ) (hη : 0 < η) (hE : |E| < 2) (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {Kd ζ δ δ' Msz Pb esz : ℕ → ℝ} (hKd : ∀ N, 1 ≤ Kd N) (hζ : ∀ N, 0 ≤ ζ N)
    (hδ : ∀ N, 0 ≤ δ N) (hMsz : ∀ N, 0 ≤ Msz N) (hPb : ∀ N, 0 ≤ Pb N)
    (hesz : ∀ N, 0 ≤ esz N)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1) b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + ζ N)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + ζ N)
    {Ξ : ℕ → Set Ω}
    (hAMI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) (n + 2), ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖ ≤ Msz N)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd N) (δ N)
        (SumZeroDyn.lkT X E N (s N) ω q.1))
    (hAMF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) (n + 2), ‖H.F N u (X.H N u ω) q.1 b‖ ≤ Msz N)
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd N) (δ N) (H.F N u (X.H N u ω) q.1))
    (hPsC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N, ∀ x,
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) x‖ ≤ Pb N)
    (hAME : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)), ‖eeFun B E N u (X.H N u ω) q.1 b‖ ≤ esz N)
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd N) (δ N)
        (eeFun B E N u (X.H N u ω) q.1))
    (hErrQ : ∀ N : ℕ, FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N) ≤ δ' N)
    (hErrC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.commErr (B.L N) n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N)
        ≤ δ' N)
    (hErrD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.dotErr n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N) ≤ δ' N)
    (hErrE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.qqErr (B.L N) (n + 1) (ellHat (B.L N) ((u : ℝ) : ℂ)) (Kd N) (esz N) (δ N)
        ≤ δ' N)
    {Env pr cE : ℕ → ℝ} (hEnv0 : ∀ N, 0 ≤ Env N) (hpr0 : ∀ N, 0 ≤ pr N)
    (hcE0 : ∀ N, 0 ≤ cE N) (hPr : ∀ N, (B.P (Ξ N)ᶜ).toReal ≤ pr N)
    (hZI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖ ≤ Env N)
    (hZIint : ∀ (r N : ℕ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (Qop (B.L N) ((s N : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖ ^ r) B.P)
    (hZF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖ ≤ Env N)
    (hZFint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖ ^ r) B.P)
    (hZC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)) q.2‖ ≤ Env N)
    (hZCint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)) q.2‖ ^ r) B.P)
    (hZD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b) q.2‖ ≤ Env N)
    (hZDint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b) q.2‖ ^ r) B.P)
    (hZE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
        (Fin.append q.2 q.2)‖ ≤ Env N)
    (hZEint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1)) (Fin.append q.2 q.2)‖ ^ r) B.P)
    (hEnvPr : ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      Env N * pr N ^ ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) ≤ cE N)
    (hEnvPrE : ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      Env N * pr N ^ ((1 : ℝ) / ((p : ℕ) : ℝ)) ≤ cE N)
    {Phi PhiE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hPhi0 : ∀ N q, 0 ≤ Phi N q) (hPhiE0 : ∀ N q, 0 ≤ PhiE N q)
    (hMψ : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N q))
    (hMψE : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P p (ψE N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * PhiE N q))
    {c : ℕ → ℝ} (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
      (cKer716 (n + 2) (4 * Kd N) * (B.scale E N (v N))⁻¹ ^ (n + 2) * Phi N q
          + (errKer716 (B.L N) (n + 2) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N))
            * (1 + 6 * (v N - s N))
        + ((v N - s N) * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N)
              * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * PhiE N q
            + (errKer716 (B.L N) ((n + 2) + (n + 2)) (4 * Kd N) (ζ N) (δ' N) (s N) (v N)
              + cE N)))
              ^ ((1 : ℝ) / 2)
        ≤ (C₀ * (N : ℝ) ^ (η / 2) * c N) * (B.scale E N (v N) ^ (n + 2))⁻¹) :
    Rhs514QAt H (fun N => C₀ * (N : ℝ) ^ (η / 2) * c N) v := by
  exact rhs514QAt_of_kernel_inputs' (c := fun N => C₀ * (N : ℝ) ^ (η / 2) * c N) hE H hs0 hsv hvt ht1 hKd hζ hδ hMsz hPb hesz hψ0 hψE0 hψint hψEint hEnvI hEnvF hEnvC hEnvD hEnvE hAMI hDecI hAMF hDecF hPsC hAME hDecE hErrQ hErrC hErrD hErrE hEnv0 hpr0 hcE0 hPr hZI hZIint hZF hZFint hZC hZCint hZD hZDint hZE hZEint hEnvPr hEnvPrE hPhi0 hPhiE0 hMψ hMψE hnum

set_option maxHeartbeats 1600000 in
/-- Weighted-time Q-event producer; the uniform kernel coefficient is separated from ρ(u). -/
theorem rhs514QAt_of_kernel_inputs''' (η : ℝ) (hη : 0 < η) (hE : |E| < 2) (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {ρ : ℕ → ℝ → ℝ} (hρ : ∀ N u, s N ≤ u → u ≤ v N → 1 ≤ ρ N u)
    (hρint : ∀ N, IntervalIntegrable (ρ N) volume (s N) (v N))
    {Kd ζ δ δ' Msz Pb esz : ℕ → ℝ} (hKd : ∀ N, 1 ≤ Kd N) (hζ : ∀ N, 0 ≤ ζ N)
    (hδ : ∀ N, 0 ≤ δ N) (hMsz : ∀ N, 0 ≤ Msz N) (hPb : ∀ N, 0 ≤ Pb N)
    (hesz : ∀ N, 0 ≤ esz N)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1) b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + ζ N)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + ζ N)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + ζ N)
    {Ξ : ℕ → Set Ω}
    (hAMI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) (n + 2), ‖SumZeroDyn.lkT X E N (s N) ω q.1 b‖ ≤ Msz N)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd N) (δ N)
        (SumZeroDyn.lkT X E N (s N) ω q.1))
    (hAMF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) (n + 2), ‖H.F N u (X.H N u ω) q.1 b‖ ≤ Msz N)
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd N) (δ N) (H.F N u (X.H N u ω) q.1))
    (hPsC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N, ∀ x,
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) x‖ ≤ Pb N)
    (hAME : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      ∀ b : LoopArg (B.L N) ((n + 2) + (n + 2)), ‖eeFun B E N u (X.H N u ω) q.1 b‖ ≤ esz N)
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)), ∀ ω ∈ Ξ N,
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd N) (δ N)
        (eeFun B E N u (X.H N u ω) q.1))
    (hErrQ : ∀ N : ℕ, FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N) ≤ δ' N)
    (hErrC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.commErr (B.L N) n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N)
        ≤ δ' N)
    (hErrD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.dotErr n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N) ≤ δ' N)
    (hErrE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      FastDecayFlow.qqErr (B.L N) (n + 1) (ellHat (B.L N) ((u : ℝ) : ℂ)) (Kd N) (esz N) (δ N)
        ≤ δ' N)
    {Env pr cE : ℕ → ℝ} (hEnv0 : ∀ N, 0 ≤ Env N) (hpr0 : ∀ N, 0 ≤ pr N)
    (hcE0 : ∀ N, 0 ≤ cE N) (hPr : ∀ N, (B.P (Ξ N)ᶜ).toReal ≤ pr N)
    (hZI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖ ≤ Env N)
    (hZIint : ∀ (r N : ℕ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (Qop (B.L N) ((s N : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖ ^ r) B.P)
    (hZF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖ ≤ Env N)
    (hZFint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖ ^ r) B.P)
    (hZC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)) q.2‖ ≤ Env N)
    (hZCint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)) q.2‖ ^ r) B.P)
    (hZD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b) q.2‖ ≤ Env N)
    (hZDint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b) q.2‖ ^ r) B.P)
    (hZE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1))
        (Fin.append q.2 q.2)‖ ≤ Env N)
    (hZEint : ∀ (r N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ q : LoopData (B.L N) (n + 2),
      Integrable (fun ω => ‖Uker (B.L N) (SumZeroDyn.xi2 E q.1) ((u : ℝ) : ℂ)
        ((v N : ℝ) : ℂ) (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ)
          (eeFun B E N u (X.H N u ω) q.1)) (Fin.append q.2 q.2)‖ ^ r) B.P)
    (hEnvPr : ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      Env N * pr N ^ ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) ≤ cE N)
    (hEnvPrE : ∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
      Env N * pr N ^ ((1 : ℝ) / ((p : ℕ) : ℝ)) ≤ cE N)
    {Phi PhiE : ∀ N, LoopData (B.L N) (n + 2) → ℝ}
    (hPhi0 : ∀ N q, 0 ≤ Phi N q) (hPhiE0 : ∀ N q, 0 ≤ PhiE N q)
    (hMψI : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N (s N) q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N q))
    (hMψ : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N q) * ρ N u)
    (hMψE : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P p (ψE N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * PhiE N q) * ρ N u)
    {c : ℕ → ℝ} (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hnum : ∀ᶠ N : ℕ in atTop, ∀ q : LoopData (B.L N) (n + 2),
      (cKer716 (n + 2) (4 * Kd N) * (B.scale E N (v N))⁻¹ ^ (n + 2) * Phi N q
          + (errKer716 (B.L N) (n + 2) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N))
            * (1 + 6 * (∫ u in (s N)..(v N), ρ N u))
        + ((∫ u in (s N)..(v N), ρ N u) * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N)
              * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * PhiE N q
            + (errKer716 (B.L N) ((n + 2) + (n + 2)) (4 * Kd N) (ζ N) (δ' N) (s N) (v N)
              + cE N)))
              ^ ((1 : ℝ) / 2)
        ≤ (C₀ * (N : ℝ) ^ (η / 2) * c N) * (B.scale E N (v N) ^ (n + 2))⁻¹) :
    Rhs514QAt H (fun N => C₀ * (N : ℝ) ^ (η / 2) * c N) v := by
  intro ε hε p hp
  obtain ⟨C1I, hC1I, hA1I⟩ := hMψI ε hε p hp
  obtain ⟨C1W, hC1W, hA1W⟩ := hMψ ε hε p hp
  set C1 : ℝ := max C1I C1W with hC1def
  have hC10 : 0 < C1 := lt_of_lt_of_le hC1I (le_max_left _ _)
  have hA1 : ∀ᶠ N : ℕ in atTop,
      (∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N (s N) q) ≤ C1 * ((N : ℝ) ^ (ε / 2) * Phi N q)) ∧
      (∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C1 * ((N : ℝ) ^ (ε / 2) * Phi N q) * ρ N u) := by
    filter_upwards [hA1I, hA1W] with N hi hw
    constructor
    · intro q
      have hb : 0 ≤ (N : ℝ) ^ (ε / 2) * Phi N q :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hPhi0 N q)
      exact (hi q).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hb)
    · intro u hus huv q
      have hb : 0 ≤ (N : ℝ) ^ (ε / 2) * Phi N q :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hPhi0 N q)
      exact (hw u hus huv q).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hb)
          (zero_le_one.trans (hρ N u hus huv)))
  obtain ⟨C3, hC30, hA3⟩ := hMψE ε hε p hp
  have hcMD := H.cMD_nonneg p
  set Csq : ℝ := (H.cMD p * (C3 + 1)) ^ ((1 : ℝ) / 2) with hCsqdef
  have hCsq0 : 0 ≤ Csq := Real.rpow_nonneg (by positivity) _
  refine ⟨C1 + Csq + 1, by positivity, ?_⟩
  filter_upwards [hA1, hA3, hnum, hEnvPr p hp, hEnvPrE p hp, eventually_ge_atTop 1] with
    N h1 h3 hnumN hEP hEPE hNge q
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNge
  have hKd0 : (0 : ℝ) ≤ Kd N := by linarith [hKd N]
  have hKd40 : (0 : ℝ) ≤ 4 * Kd N := by linarith
  have hδ'0 : (0 : ℝ) ≤ δ' N :=
    le_trans (FastDecayFlow.qopErr1_nonneg (B.L N) n hKd0 (hMsz N) (hδ N)) (hErrQ N)
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
  have hell : ∀ u : ℝ, s N ≤ u → u ≤ v N → (0 : ℝ) < ellHat (B.L N) ((u : ℝ) : ℂ) := by
    intro u hua hub
    have := half_le_ellHat_real (B.L N) hL3 (hs0N.trans hua) (lt_of_le_of_lt hub hv1)
    linarith
  have h1s : (0 : ℝ) < 1 - s N := by linarith
  have h1v : (0 : ℝ) < 1 - v N := by linarith
  have hrat : (0 : ℝ) ≤ (1 - s N) / (1 - v N) := (div_pos h1s h1v).le
  have hrm : (0 : ℝ) ≤ ((1 - s N) / (1 - v N)) ^ (n + 2) := pow_nonneg hrat _
  have hrm2 : (0 : ℝ) ≤ ((1 - s N) / (1 - v N)) ^ ((n + 2) + (n + 2)) := pow_nonneg hrat _
  have hscale : (0 : ℝ) < B.scale E N (v N) := B.scale_pos' hE N hv0 hv1
  -- the two normalizations and the two errors, now carrying the Markov price `cE N`
  set Av : ℝ := (B.scale E N (v N))⁻¹ ^ (n + 2) with hAvdef
  set Av2 : ℝ := (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) with hAv2def
  set Eb : ℝ := errKer716 (B.L N) (n + 2) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N with hEbdef
  set Eb2 : ℝ := errKer716 (B.L N) ((n + 2) + (n + 2)) (4 * Kd N) (ζ N) (δ' N) (s N) (v N) + cE N
    with hEb2def
  have hEb0 : (0 : ℝ) ≤ Eb := by
    rw [hEbdef]
    have := errKer716_nonneg (B.L N) (n + 2) hKd40 (hζ N) hδ'0 hsvN hv1
    have := hcE0 N
    linarith
  have hEb20 : (0 : ℝ) ≤ Eb2 := by
    rw [hEb2def]
    have := errKer716_nonneg (B.L N) ((n + 2) + (n + 2)) hKd40 (hζ N) hδ'0 hsvN hv1
    have := hcE0 N
    linarith
  have hAv0 : (0 : ℝ) ≤ Av := by rw [hAvdef]; positivity
  have hAv20 : (0 : ℝ) ≤ Av2 := by rw [hAv2def]; positivity
  have hcK0 : (0 : ℝ) ≤ cKer716 (n + 2) (4 * Kd N) := cKer716_nonneg _ hKd40
  have hcK20 : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) := cKer716_nonneg _ hKd40
  set Iρ : ℝ := ∫ u in (s N)..(v N), ρ N u with hIρdef
  have hIρ0 : 0 ≤ Iρ := intervalIntegral.integral_nonneg hsvN
    (fun u hu => zero_le_one.trans (hρ N u hu.1 hu.2))
  set Kmain : ℝ := cKer716 (n + 2) (4 * Kd N) * Av * Phi N q + Eb with hKmaindef
  set K3 : ℝ := Iρ * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2)
    with hK3def
  have hKmain0 : (0 : ℝ) ≤ Kmain := by
    rw [hKmaindef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716 (n + 2) (4 * Kd N) * Av * Phi N q := by positivity
    linarith
  have hvs : (0 : ℝ) ≤ Iρ := hIρ0
  have hK30 : (0 : ℝ) ≤ K3 := by
    rw [hK3def]
    have hPE := hPhiE0 N q
    have : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q := by positivity
    exact mul_nonneg hvs (by linarith)
  set Mb : ℝ := cKer716 (n + 2) (4 * Kd N) * Av * (C1 * (Np * Phi N q)) + Eb with hMbdef
  have hMb0 : (0 : ℝ) ≤ Mb := by
    rw [hMbdef]
    have := hPhi0 N q
    have : (0 : ℝ) ≤ cKer716 (n + 2) (4 * Kd N) * Av * (C1 * (Np * Phi N q)) := by positivity
    linarith
  have hMbK : Mb ≤ (C1 + 1) * (Np * Kmain) := by
    rw [hMbdef, hKmaindef]
    have e1 : cKer716 (n + 2) (4 * Kd N) * Av * (C1 * (Np * Phi N q))
        = C1 * (Np * (cKer716 (n + 2) (4 * Kd N) * Av * Phi N q)) := by ring
    rw [e1]
    exact affine_absorb (mul_nonneg (mul_nonneg hcK0 hAv0) (hPhi0 N q)) hEb0 hC10.le hNp1
  -- the shared comparison behind the four `‖·‖_{2p}` terms, in raw form
  have hcmp : ∀ a Mψ eT w : ℝ, 0 ≤ a → a ≤ (4 * Kd N) ^ (2 * (n + 2)) →
      0 ≤ Mψ → Mψ ≤ C1 * (Np * Phi N q) * w → 0 ≤ eT → eT ≤ δ' N →
      cKerSumZero (n + 2) * a * (B.scale E N (v N))⁻¹ ^ (n + 2) * Mψ
        + (cKerSumZero (n + 2) * a * ((1 - s N) / (1 - v N)) ^ (n + 2) * ζ N
          + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
              * ((1 - s N) / (1 - v N)) ^ (n + 2) * eT)
        ≤ cKerSumZero (n + 2) * (4 * Kd N) ^ (2 * (n + 2))
              * (B.scale E N (v N))⁻¹ ^ (n + 2) * (C1 * (Np * Phi N q) * w)
          + (cKerSumZero (n + 2) * (4 * Kd N) ^ (2 * (n + 2))
                * ((1 - s N) / (1 - v N)) ^ (n + 2) * ζ N
            + cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
                * ((1 - s N) / (1 - v N)) ^ (n + 2) * δ' N) := by
    intro a Mψ eT w ha haa hM0 hMle he0 hele
    have hinv : (0 : ℝ) ≤ (B.scale E N (v N))⁻¹ ^ (n + 2) := by positivity
    have p1 := mul_four_le_mul_four (SumZeroDyn.cKerSumZero_nonneg (n + 2)) ha haa hinv hM0 hMle
    have p2 := mul_four_le_mul_four (SumZeroDyn.cKerSumZero_nonneg (n + 2)) ha haa hrm (hζ N)
      (le_refl (ζ N))
    have p3 : cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
          * ((1 - s N) / (1 - v N)) ^ (n + 2) * eT
        ≤ cKerSumZeroErr (n + 2) * (B.L N : ℝ) ^ (n + 2)
          * ((1 - s N) / (1 - v N)) ^ (n + 2) * δ' N :=
      mul_four_le_mul_four (SumZeroDyn.cKerSumZeroErr_nonneg (n + 2)) (by positivity) le_rfl
        hrm he0 hele
    linarith
  -- Term 1: the initial datum of (5.91)
  have hT1 : momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((s N : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)) q.2‖) ≤ Mb := by
    have key := momNorm_Uker_Qop_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := s N) (v := v N) hs0N le_rfl hsvN hv0 hv1 hκA (hKd N) (hMsz N) (hζ N) (hδ N)
      (Ξ := Ξ N) (A := fun ω => SumZeroDyn.lkT X E N (s N) ω q.1) (ψ := ψ N (s N) q)
      (fun ω => hψ0 N (s N) q ω) (hψint (2 * p) N (s N) q)
      (fun ω b => by rw [hbr]; exact hEnvI N q ω b)
      (fun ω hω => hAMI N q ω hω) (fun ω hω => hDecI N q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZI N q ω) (hZIint (2 * p) N q) (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp (Kd N ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N (s N) q))
      (FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N)) 1 (by positivity)
      (pow_le_pow_left₀ hKd0 (by linarith) _) (momNorm_nonneg _ _ _) (by simpa using h1.1 q)
      (FastDecayFlow.qopErr1_nonneg (B.L N) n hKd0 (hMsz N) (hδ N)) (hErrQ N)
    rw [hMbdef, hAvdef, hEbdef, cKer716, errKer716]
    nlinarith only [hle, hEP]
  -- Terms 2–4: the three time integrals of (5.91)
  have hI2 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)) q.2‖))
      ≤ Iρ * Mb := by
    refine intervalIntegral_le_of_le_weight hsvN hMb0 (hρint N)
      (fun u hu => zero_le_one.trans (hρ N u hu.1 hu.2)) fun u hu => ?_
    have key := momNorm_Uker_Qop_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hMsz N) (hζ N) (hδ N)
      (Ξ := Ξ N) (A := fun ω => H.F N u (X.H N u ω) q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvF N u hu.1 hu.2 q ω b)
      (fun ω hω => hAMF N u hu.1 hu.2 q ω hω) (fun ω hω => hDecF N u hu.1 hu.2 q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZF N u hu.1 hu.2 q ω) (hZFint (2 * p) N u hu.1 hu.2 q)
      (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp (Kd N ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N u q))
      (FastDecayFlow.qopErr1 (B.L N) n (Kd N) (Msz N) (δ N)) (ρ N u) (by positivity)
      (pow_le_pow_left₀ hKd0 (by linarith) _) (momNorm_nonneg _ _ _) (h1.2 u hu.1 hu.2 q)
      (FastDecayFlow.qopErr1_nonneg (B.L N) n hKd0 (hMsz N) (hδ N)) (hErrQ N)
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    have hEbρ : Eb ≤ Eb * ρ N u := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hρ N u hu.1 hu.2) hEb0
    rw [hEbdef, errKer716] at hEbρ
    nlinarith only [hle, hEP, hEbρ]
  have hI3 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
            (SumZeroDyn.lkT X E N u ω q.1)) q.2‖))
      ≤ Iρ * Mb := by
    refine intervalIntegral_le_of_le_weight hsvN hMb0 (hρint N)
      (fun u hu => zero_le_one.trans (hρ N u hu.1 hu.2)) fun u hu => ?_
    have key := momNorm_Uker_commS_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hζ N) (hPb N)
      (Ξ := Ξ N) (A := fun ω => SumZeroDyn.lkT X E N u ω q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvC N u hu.1 hu.2 q ω b)
      (fun ω hω => hPsC N u hu.1 hu.2 q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZC N u hu.1 hu.2 q ω) (hZCint (2 * p) N u hu.1 hu.2 q)
      (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp ((4 * Kd N) ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N u q))
      (FastDecayFlow.commErr (B.L N) n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N))
      (ρ N u) (by positivity) le_rfl (momNorm_nonneg _ _ _) (h1.2 u hu.1 hu.2 q)
      (FastDecayFlow.commErr_nonneg (B.L N) n (hell u hu.1 hu.2)
        (lt_of_le_of_lt hu.2 hv1) hKd0 (hPb N))
      (hErrC N u hu.1 hu.2)
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    have hEbρ : Eb ≤ Eb * ρ N u := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hρ N u hu.1 hu.2) hEb0
    rw [hEbdef, errKer716] at hEbρ
    nlinarith only [hle, hEP, hEbρ]
  have hI4 : (∫ u in (s N)..(v N), momNorm B.P (2 * p) (fun ω =>
        ‖Uker (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ) ((v N : ℝ) : ℂ)
          (fun b => Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) u b) q.2‖))
      ≤ Iρ * Mb := by
    refine intervalIntegral_le_of_le_weight hsvN hMb0 (hρint N)
      (fun u hu => zero_le_one.trans (hρ N u hu.1 hu.2)) fun u hu => ?_
    have key := momNorm_Uker_dot_event_untrunc_le (P := B.P) (B.L N) hL3 h2p hE.le q.1
      (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hζ N) (hPb N)
      (Ξ := Ξ N) (A := fun ω => SumZeroDyn.lkT X E N u ω q.1) (ψ := ψ N u q)
      (fun ω => hψ0 N u q ω) (hψint (2 * p) N u q)
      (fun ω b => by rw [hbr]; exact hEnvD N u hu.1 hu.2 q ω b)
      (fun ω hω => hPsC N u hu.1 hu.2 q ω hω) q.2
      (hEnv0 N) (hpr0 N) (fun ω => hZD N u hu.1 hu.2 q ω) (hZDint (2 * p) N u hu.1 hu.2 q)
      (hPr N)
    rw [hbr (v N)] at key
    refine key.trans ?_
    have hle := hcmp ((4 * Kd N) ^ (2 * (n + 2))) (momNorm B.P (2 * p) (ψ N u q))
      (FastDecayFlow.dotErr n (ellHat (B.L N) ((u : ℝ) : ℂ)) u (Kd N) (Pb N))
      (ρ N u) (by positivity) le_rfl (momNorm_nonneg _ _ _) (h1.2 u hu.1 hu.2 q)
      (FastDecayFlow.dotErr_nonneg n (hell u hu.1 hu.2)
        (lt_of_le_of_lt hu.2 hv1) (hPb N))
      (hErrD N u hu.1 hu.2)
    rw [hMbdef, hAvdef, cKer716, hEbdef, errKer716]
    have hEbρ : Eb ≤ Eb * ρ N u := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hρ N u hu.1 hu.2) hEb0
    rw [hEbdef, errKer716] at hEbρ
    nlinarith only [hle, hEP, hEbρ]
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
        ≤ (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q)) + Eb2) * ρ N u := by
      intro u hu
      have key := momNorm_Uker_QQ_event_untrunc_le (P := B.P) (B.L N) hL3 hp0 hE q.1
        (s := s N) (u := u) (v := v N) hs0N hu.1 hu.2 hv0 hv1 hκA (hKd N) (hζ N) (hesz N) (hδ N)
        (Ξ := Ξ N) (A := fun ω => eeFun B E N u (X.H N u ω) q.1) (ψ := ψE N u q)
        (fun ω => hψE0 N u q ω) (hψEint p N u q)
        (fun ω b => by rw [hbr]; exact hEnvE N u hu.1 hu.2 q ω b)
        (fun ω hω => hAME N u hu.1 hu.2 q ω hω) (fun ω hω => hDecE N u hu.1 hu.2 q ω hω)
        (Fin.append q.2 q.2)
        (hEnv0 N) (hpr0 N) (fun ω => hZE N u hu.1 hu.2 q ω) (hZEint p N u hu.1 hu.2 q)
        (hPr N)
      rw [hbr (v N)] at key
      refine key.trans ?_
      have hinv2 : (0 : ℝ) ≤ (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) := by positivity
      have p1 : cKerSumZero ((n + 2) + (n + 2)) * (4 * Kd N) ^ (2 * ((n + 2) + (n + 2)))
            * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * momNorm B.P p (ψE N u q)
          ≤ cKerSumZero ((n + 2) + (n + 2)) * (4 * Kd N) ^ (2 * ((n + 2) + (n + 2)))
            * (B.scale E N (v N))⁻¹ ^ ((n + 2) + (n + 2)) * (C3 * (Np * PhiE N q) * ρ N u) :=
        mul_four_le_mul_four (SumZeroDyn.cKerSumZero_nonneg ((n + 2) + (n + 2)))
          (by positivity) le_rfl hinv2 (momNorm_nonneg _ _ _) (h3 u hu.1 hu.2 q)
      have p3 : cKerSumZeroErr ((n + 2) + (n + 2)) * (B.L N : ℝ) ^ ((n + 2) + (n + 2))
            * ((1 - s N) / (1 - v N)) ^ ((n + 2) + (n + 2))
            * FastDecayFlow.qqErr (B.L N) (n + 1) (ellHat (B.L N) ((u : ℝ) : ℂ)) (Kd N)
                (esz N) (δ N)
          ≤ cKerSumZeroErr ((n + 2) + (n + 2)) * (B.L N : ℝ) ^ ((n + 2) + (n + 2))
            * ((1 - s N) / (1 - v N)) ^ ((n + 2) + (n + 2)) * δ' N :=
        mul_four_le_mul_four (SumZeroDyn.cKerSumZeroErr_nonneg ((n + 2) + (n + 2)))
          (by positivity) le_rfl hrm2
          (FastDecayFlow.qqErr_nonneg (B.L N) (n + 1) (hell u hu.1 hu.2) hKd0 (hesz N) (hδ N))
          (hErrE N u hu.1 hu.2)
      rw [hAv2def, hEb2def, cKer716, errKer716]
      have hEb2ρ : Eb2 ≤ Eb2 * ρ N u := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hρ N u hu.1 hu.2) hEb20
      rw [hEb2def, errKer716] at hEb2ρ
      nlinarith only [p1, p3, hEPE, hEb2ρ]
    have hbase : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q :=
      mul_nonneg (mul_nonneg hcK20 hAv20) (hPhiE0 N q)
    have hfac : cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q)) + Eb2
        ≤ (C3 + 1) * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2)) := by
      have e1 : cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q)) := by ring
      rw [e1]
      exact affine_absorb hbase hEb20 hC30.le hNp1
    have hMnn : (0 : ℝ) ≤ cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q))
        + Eb2 := by
      have h0 : (0 : ℝ) ≤ C3 * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q)) :=
        mul_nonneg hC30.le (mul_nonneg hNp0.le hbase)
      have e1 : cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q))
          = C3 * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q)) := by ring
      rw [e1]
      linarith
    refine (intervalIntegral_le_of_le_weight hsvN hMnn (hρint N)
      (fun u hu => zero_le_one.trans (hρ N u hu.1 hu.2)) hconst).trans ?_
    rw [hK3def]
    calc Iρ
          * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * (C3 * (Np * PhiE N q)) + Eb2)
        ≤ Iρ * ((C3 + 1)
            * (Np * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2))) :=
          mul_le_mul_of_nonneg_left hfac hvs
      _ = (C3 + 1) * (Np * (Iρ
            * (cKer716 ((n + 2) + (n + 2)) (4 * Kd N) * Av2 * PhiE N q + Eb2))) := by ring
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
  have hfour : Mb + 2 * (Iρ * Mb) + 2 * (Iρ * Mb) + 2 * (Iρ * Mb)
      ≤ (C1 + 1) * (Np * (Kmain * (1 + 6 * Iρ))) := by
    have h6 : Mb * (1 + 6 * Iρ)
        ≤ ((C1 + 1) * (Np * Kmain)) * (1 + 6 * Iρ) :=
      mul_le_mul_of_nonneg_right hMbK (by linarith)
    linarith [h6]
  have hmain : Mb + 2 * (Iρ * Mb) + 2 * (Iρ * Mb) + 2 * (Iρ * Mb)
        + Csq * (Np * K3 ^ ((1 : ℝ) / 2))
      ≤ (C1 + Csq + 1) * (Np * (Kmain * (1 + 6 * Iρ) + K3 ^ ((1 : ℝ) / 2))) := by
    have hpos : (0 : ℝ) ≤ Np * (Kmain * (1 + 6 * Iρ)) :=
      mul_nonneg hNp0.le (mul_nonneg hKmain0 (by linarith))
    have t1 : (0 : ℝ) ≤ Csq * (Np * (Kmain * (1 + 6 * Iρ))) := mul_nonneg hCsq0 hpos
    have t2 : (0 : ℝ) ≤ (C1 + 1) * (Np * K3 ^ ((1 : ℝ) / 2)) :=
      mul_nonneg (by linarith) (mul_nonneg hNp0.le hK3s)
    linarith [hfour, t1, t2]
  refine le_trans (by linarith [hT1, hI2, hI3, hI4, hT5]) (hmain.trans ?_)
  have hfin := hnumN q
  rw [← hKmaindef, ← hK3def] at hfin
  have hC : (0 : ℝ) ≤ C1 + Csq + 1 := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfin hNp0.le) hC


end ProducerEvent

/-! ### §6  Satisfiability on the paper's own grid

Three things have to be checked of a `Q`-route hypothesis bundle, and all three are checked
here, by compiled statements rather than by prose.

1. **The (7.16) tier really is available on the window the six-step construction uses.**  That
   is T201's `RBM.Gauss.gridS_Q716_witness`, on the grid `1 - s_k = W^{-kτ'}` of p. 24, with an
   `N`-independent constant.  `RBM.Gauss.gridS_Q716_nondegenerate` repackages it so that the
   two anti-vacuity clauses are visible: the tensor is **not zero** and `Q_u` **fixes** it, so
   the bound is not a statement about `0`.  No short-window hypothesis is used (`hτ'` is only
   `0 ≤ τ'`, `W` is arbitrary) and `v ↑ 1` is allowed.
2. **The `hnum` row of §5 is not an obstruction.**  `RBM.Gauss.hnum_le_of_zero_err` shows that
   once the two errors of (7.16) vanish, the arithmetic of (5.24) holds with *equality* at the
   constant `RBM.Gauss.cNum716` — and `RBM.Gauss.rhs514QAt_of_kernel_inputs_zero_err` is the
   producer with `hnum` gone.  So the row has no owner because it needs none.
3. **That constant is uniform along the grid.**  `RBM.Gauss.gridS_cNum716_le` bounds
   `cNum716` by `7 C_m K^{2m} Φ + (C_{2m} K^{4m} Φ_E)^{1/2}`, which mentions neither `L`, nor
   `N`, nor `W`, nor `τ'`, nor the grid index `k`.  This is exactly the quantity that
   `RBM.Gauss.no_const_hkerC_on_gridS` proves **cannot** exist on the (7.1) tier: there the
   constant is `(W^{τ'})^{m+2}`.  The contrast is the whole content of D14. -/

section Satisfiability

/-- The constant of (5.24) at which `hnum` holds with equality once `ζ = δ = 0`: the main term
of (7.16) at loop length `m`, carried across the window by `1 + 6(v-s)`, plus the square root
of the `E ⊗ E` term at loop length `2m`. -/
noncomputable def cNum716 (m : ℕ) (Kd Phi PhiE s v : ℝ) : ℝ :=
  cKer716 m Kd * Phi * (1 + 6 * (v - s))
    + ((v - s) * (cKer716 (m + m) Kd * PhiE)) ^ ((1 : ℝ) / 2)

theorem cNum716_nonneg (m : ℕ) {Kd Phi PhiE s v : ℝ} (hKd : 0 ≤ Kd) (hPhi : 0 ≤ Phi)
    (hPhiE : 0 ≤ PhiE) (hsv : s ≤ v) : 0 ≤ cNum716 m Kd Phi PhiE s v := by
  have hvs : (0 : ℝ) ≤ v - s := by linarith
  have h1 : (0 : ℝ) ≤ cKer716 m Kd * Phi * (1 + 6 * (v - s)) :=
    mul_nonneg (mul_nonneg (cKer716_nonneg m hKd) hPhi) (by linarith)
  have h2 : (0 : ℝ) ≤ ((v - s) * (cKer716 (m + m) Kd * PhiE)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (mul_nonneg hvs (mul_nonneg (cKer716_nonneg (m + m) hKd) hPhiE)) _
  rw [cNum716]; linarith

/-- The leading Case-2 kernel coefficient already exceeds the unit control at loop length
two.  The error budget of T253 can be arbitrarily small without changing this coefficient. -/
theorem one_lt_cKer716_two : (1 : ℝ) < cKer716 2 1 := by
  have hw : (0 : ℝ) ≤ cWin := cWin_nonneg
  have hl : (0 : ℝ) ≤ cLip := cLip_nonneg
  unfold cKer716 cKerSumZero
  norm_num
  nlinarith [sq_nonneg cWin]

/-- A positive additive error cannot repair the unit-control numeric row, even on a
zero-length window with unit scale and a positive leading envelope. -/
theorem not_hnum_unit_Q {e cE : ℝ} (he : 0 ≤ e) (hcE : 0 ≤ cE) :
    ¬ (cKer716 2 1 + (e + cE) ≤ 1) := by
  have h := one_lt_cKer716_two
  intro hnum
  linarith

/-- The same obstruction persists on the nonempty window of length `1/2`, with any
nonnegative square-root contribution. -/
theorem not_hnum_half_window_Q {e z : ℝ} (he : 0 ≤ e) (hz : 0 ≤ z) :
    ¬ ((cKer716 2 1 + e) * (1 + 6 * (1 / 2 : ℝ)) + z ≤ 1) := by
  have h := one_lt_cKer716_two
  intro hnum
  nlinarith

/-- The relaxed Case-2 numeric row on the concrete first grid cell of
`gridS_two_one_first`: positive moment envelopes, positive errors and a positive
bad-event payment.  Here `L = 3`, so this is an arithmetic witness, not a claim about a
growing-band model. -/
noncomputable def numHalfQ : ℝ :=
  (cKer716 2 4 + (errKer716 3 2 4 1 1 0 (1 / 2) + 1))
      * (1 + 6 * (1 / 2))
    + ((1 / 2) * (cKer716 4 4 +
        (errKer716 3 4 4 1 1 0 (1 / 2) + 1))) ^ ((1 : ℝ) / 2)

theorem numHalfQ_relaxed_witness (η : ℝ) (hη : 0 < η) :
    ∃ C₀ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      numHalfQ ≤ C₀ * (N : ℝ) ^ (η / 2) := by
  let C₀ := max numHalfQ 0 + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; have := le_max_right numHalfQ 0; linarith
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (η / 2) :=
    Real.one_le_rpow hN' (by linarith)
  have ha : numHalfQ ≤ C₀ := by dsimp [C₀]; have := le_max_left numHalfQ 0; linarith
  nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr hpow)]

/-- **`RBM.Gauss.cNum716` is uniform on any window of length at most `1`.**  The bound mentions
neither `L` nor the window, so in particular it is independent of the grid index. -/
theorem cNum716_le (m : ℕ) {Kd Phi PhiE s v : ℝ} (hKd : 0 ≤ Kd) (hPhi : 0 ≤ Phi)
    (hPhiE : 0 ≤ PhiE) (hsv : s ≤ v) (hvs1 : v - s ≤ 1) :
    cNum716 m Kd Phi PhiE s v
      ≤ 7 * (cKer716 m Kd * Phi) + (cKer716 (m + m) Kd * PhiE) ^ ((1 : ℝ) / 2) := by
  have hvs : (0 : ℝ) ≤ v - s := by linarith
  have hcK := cKer716_nonneg m hKd
  have hcK2 := cKer716_nonneg (m + m) hKd
  have h1 : cKer716 m Kd * Phi * (1 + 6 * (v - s)) ≤ 7 * (cKer716 m Kd * Phi) := by
    have hb : (0 : ℝ) ≤ cKer716 m Kd * Phi := mul_nonneg hcK hPhi
    nlinarith
  have h2 : ((v - s) * (cKer716 (m + m) Kd * PhiE)) ^ ((1 : ℝ) / 2)
      ≤ (cKer716 (m + m) Kd * PhiE) ^ ((1 : ℝ) / 2) := by
    refine Real.rpow_le_rpow (mul_nonneg hvs (mul_nonneg hcK2 hPhiE)) ?_ (by norm_num)
    have hb : (0 : ℝ) ≤ cKer716 (m + m) Kd * PhiE := mul_nonneg hcK2 hPhiE
    nlinarith
  rw [cNum716]; linarith

/-- **`RBM.Gauss.cNum716` on the paper's p. 24 grid**, uniformly in the index `k`, in `W` and in
`τ'`.  Contrast `RBM.Gauss.no_const_hkerC_on_gridS`: on the (7.1) tier no such constant
exists. -/
theorem gridS_cNum716_le (m : ℕ) {Kd Phi PhiE : ℝ} (hKd : 0 ≤ Kd) (hPhi : 0 ≤ Phi)
    (hPhiE : 0 ≤ PhiE) {W τ' : ℝ} (hW : 1 ≤ W) (hτ' : 0 ≤ τ') (k : ℕ) :
    cNum716 m Kd Phi PhiE (gridS W τ' k) (gridS W τ' (k + 1))
      ≤ 7 * (cKer716 m Kd * Phi) + (cKer716 (m + m) Kd * PhiE) ^ ((1 : ℝ) / 2) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  exact cNum716_le m hKd hPhi hPhiE (gridS_mono hW hτ' (Nat.le_succ k))
    (by have := gridS_nonneg hW hτ' k; have := gridS_lt_one (τ' := τ') hW0 (k + 1); linarith)

/-- **The `hnum` row of `RBM.Gauss.rhs514QAt_of_kernel_inputs` holds with equality** once the
offset `ζ` of the envelope and the error `δ` of (7.13) vanish.  Note where the `(1-s)/(1-v)`
factors went: they sit *only* inside `RBM.Gauss.errKer716`, so at `ζ = δ = 0` the estimate
carries **no** `η_s/η_v` prefactor — which is what (5.92) demands and what the (7.1) tier
cannot deliver. -/
theorem hnum_le_of_zero_err (L m : ℕ) {Kd A Phi PhiE s v : ℝ} (hKd : 0 ≤ Kd) (hA : 0 < A)
    (hPhiE : 0 ≤ PhiE) (hsv : s ≤ v) :
    (cKer716 m Kd * A⁻¹ ^ m * Phi + errKer716 L m Kd 0 0 s v) * (1 + 6 * (v - s))
        + ((v - s) * (cKer716 (m + m) Kd * A⁻¹ ^ (m + m) * PhiE
            + errKer716 L (m + m) Kd 0 0 s v)) ^ ((1 : ℝ) / 2)
      ≤ cNum716 m Kd Phi PhiE s v * (A ^ m)⁻¹ := by
  -- the algebra is `RBM.Gauss.num_zero_err_aux`, shared with Case 1 (T236): only the constant
  -- and the window weight `1 + 6(v-s)` differ.
  have herr : ∀ j : ℕ, errKer716 L j Kd 0 0 s v = 0 := by intro j; simp [errKer716]
  have hvs : (0 : ℝ) ≤ v - s := by linarith
  have hre : (v - s) * (cKer716 (m + m) Kd * A⁻¹ ^ (m + m) * PhiE)
      = cKer716 (m + m) Kd * A⁻¹ ^ (m + m) * ((v - s) * PhiE) := by ring
  have hre2 : (v - s) * (cKer716 (m + m) Kd * PhiE)
      = cKer716 (m + m) Kd * ((v - s) * PhiE) := by ring
  rw [herr, herr, add_zero, add_zero, hre, cNum716, hre2]
  have key := num_zero_err_aux m (cK := cKer716 m Kd) (cK2 := cKer716 (m + m) Kd)
    (A := A) (Phi := Phi) (PhiE := (v - s) * PhiE) (w := 1 + 6 * (v - s))
    (cKer716_nonneg (m + m) hKd) hA (mul_nonneg hvs hPhiE)
  calc (cKer716 m Kd * A⁻¹ ^ m * Phi) * (1 + 6 * (v - s))
        + (cKer716 (m + m) Kd * A⁻¹ ^ (m + m) * ((v - s) * PhiE)) ^ ((1 : ℝ) / 2)
      = cKer716 m Kd * A⁻¹ ^ m * Phi * (1 + 6 * (v - s))
        + (cKer716 (m + m) Kd * A⁻¹ ^ (m + m) * ((v - s) * PhiE)) ^ ((1 : ℝ) / 2) := by
        ring_nf
    _ ≤ _ := key

section WitnessModel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

/-- **`RBM.Gauss.rhs514QAt_of_kernel_inputs` with the `hnum` row discharged.**

Same producer, with `ζ = δ = 0` and the two moment controls constant in the charge — which is
the shape `RBM.Step3.Lemma514` hands down, its controls being `Λ N` and `Φ N`.  The output
control is `RBM.Gauss.cNum716`, and `RBM.Gauss.gridS_cNum716_le` says it is bounded uniformly
along the paper's grid. -/
theorem rhs514QAt_of_kernel_inputs_zero_err (hE : |E| < 2) (H : MomentDuhamel.Hyp X E s t n)
    {v : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hsv : ∀ N, s N ≤ v N) (hvt : ∀ N, v N ≤ t N)
    (ht1 : ∀ N, t N < 1)
    {Kd : ℝ} (hKd : 1 ≤ Kd)
    {ψ ψE : ∀ N, ℝ → LoopData (B.L N) (n + 2) → Ω → ℝ}
    (hψ0 : ∀ N u q ω, 0 ≤ ψ N u q ω) (hψE0 : ∀ N u q ω, 0 ≤ ψE N u q ω)
    (hψint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψ N u q ω ^ r) B.P)
    (hψEint : ∀ (r N : ℕ) (u : ℝ) (q : LoopData (B.L N) (n + 2)),
      Integrable (fun ω => ψE N u q ω ^ r) B.P)
    (hEnvI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1) b‖
        ≤ (B.scale E N (s N))⁻¹ ^ (n + 2) * ψ N (s N) q ω + 0)
    (hEnvF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + 0)
    (hEnvC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + 0)
    (hEnvD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)),
      ‖Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
          * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b‖
        ≤ (B.scale E N u)⁻¹ ^ (n + 2) * ψ N u q ω + 0)
    (hEnvE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω)
        (b : LoopArg (B.L N) ((n + 2) + (n + 2))),
      ‖SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1) b‖
        ≤ (B.scale E N u)⁻¹ ^ ((n + 2) + (n + 2)) * ψE N u q ω + 0)
    (hDecI : ∀ (N : ℕ) (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((s N : ℝ) : ℂ) * Kd) 0
        (Qop (B.L N) ((s N : ℝ) : ℂ) (SumZeroDyn.lkT X E N (s N) ω q.1)))
    (hDecF : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) 0
        (Qop (B.L N) ((u : ℝ) : ℂ) (H.F N u (X.H N u ω) q.1)))
    (hDecC : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) 0
        (SumZeroDyn.commS (B.L N) (xiOf (mSigma E) q.1) ((u : ℝ) : ℂ)
          (SumZeroDyn.lkT X E N u ω q.1)))
    (hDecD : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) 0
        (fun b : LoopArg (B.L N) (n + 2) =>
          Psum (B.L N) (SumZeroDyn.lkT X E N u ω q.1) (b 0)
            * SumZeroDyn.varthetaDot (B.L N) (n := n + 1) u b))
    (hDecE : ∀ (N : ℕ) (u : ℝ), s N ≤ u → u ≤ v N →
      ∀ (q : LoopData (B.L N) (n + 2)) (ω : Ω),
      FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) * Kd) 0
        (SumZeroDyn.QQ (B.L N) ((u : ℝ) : ℂ) (eeFun B E N u (X.H N u ω) q.1)))
    {Phi PhiE : ℕ → ℝ} (hPhi0 : ∀ N, 0 ≤ Phi N) (hPhiE0 : ∀ N, 0 ≤ PhiE N)
    (hMψ : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P (2 * p) (ψ N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * Phi N))
    (hMψE : ∀ ε > (0 : ℝ), ∀ p : ℕ, 1 ≤ p → ∃ C > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      ∀ (u : ℝ), s N ≤ u → u ≤ v N → ∀ q : LoopData (B.L N) (n + 2),
        momNorm B.P p (ψE N u q) ≤ C * ((N : ℝ) ^ (ε / 2) * PhiE N)) :
    Rhs514QAt H (fun N => cNum716 (n + 2) Kd (Phi N) (PhiE N) (s N) (v N)) v := by
  refine rhs514QAt_of_kernel_inputs hE H hs0 hsv hvt ht1 hKd le_rfl le_rfl
    hψ0 hψE0 hψint hψEint hEnvI hEnvF hEnvC hEnvD hEnvE hDecI hDecF hDecC hDecD hDecE
    (Phi := fun N _ => Phi N) (PhiE := fun N _ => PhiE N)
    (fun N _ => hPhi0 N) (fun N _ => hPhiE0 N) hMψ hMψE ?_
  refine Eventually.of_forall fun N q => ?_
  have hv0 : (0 : ℝ) ≤ v N := (hs0 N).trans (hsv N)
  have hv1 : v N < 1 := lt_of_le_of_lt (hvt N) (ht1 N)
  exact hnum_le_of_zero_err (B.L N) (n + 2) (by linarith) (B.scale_pos' hE N hv0 hv1)
    (hPhiE0 N) (hsv N)

end WitnessModel

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The (7.16) tier on the paper's own grid, with the two anti-vacuity clauses in front.**

`RBM.Gauss.gridS_Q716_witness` (T201), restated as an existential so that what it rules out is
explicit: there is a tensor `G` which is **not zero**, which `Q_u` **fixes** (so projecting does
not trivialise the bound), and whose evolved kernel obeys (7.16) across the grid step
`s_k → s_{k+1}` with the constant `C_{m+2} 3^{2(m+2)}` — no `N`, no `W^{τ'}`, no `k`. -/
theorem gridS_Q716_nondegenerate [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {m : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (m + 2) → Bool)
    {W τ' : ℝ} (hW : 1 ≤ W) (hτ' : 0 ≤ τ') (k : ℕ) {κA : ℝ} (hκA : 0 < κA)
    (a : LoopArg L (m + 2)) :
    ∃ G : LoopArg L (m + 2) → ℂ, G ≠ 0
      ∧ Qop L ((gridS W τ' k : ℝ) : ℂ) G = G
      ∧ momNorm P q (fun _ω : Ω => ‖Uker L (xiOf (mSigma E) σ) ((gridS W τ' k : ℝ) : ℂ)
            ((gridS W τ' (k + 1) : ℝ) : ℂ) G a‖)
          ≤ cKerSumZero (m + 2) * 3 ^ (2 * (m + 2))
              * (κA * ((1 - gridS W τ' (k + 1))
                  * ellHat L ((gridS W τ' (k + 1) : ℝ) : ℂ)))⁻¹ ^ (m + 2) := by
  obtain ⟨h1, h2, h3⟩ := gridS_Q716_witness (P := P) L hL hq hE σ hW hτ' k hκA a
  exact ⟨_, h1, h2, h3⟩

end GridWitness

section EventRowsWitness

variable {Ω : Type*} [MeasurableSpace Ω]
variable {B : Band Ω} [IsProbabilityMeasure B.P] {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **The rows that `RBM.Gauss.rhs514QAt_of_kernel_inputs'` adds on top of §5 are
simultaneously satisfiable**, at the model's own good event `RBM.FastDecayFlow.lkGood` of
(5.75) and with `pr` taken to be the event's own Markov price.

The five clauses are, in order, the `hpr0`, `hPr`, `hEnvPr`, `hEnvPrE` rows and the anti-vacuity
statement that the event is not eventually empty.  Nothing is re-proved: the two smallness
clauses are `RBM.Gauss.eventually_env_mul_lkGood_le` (T237, itself T218's
`RBM.Gauss.eventually_env_mul_prob_rpow_le` applied to `RBM.FastDecayFlow.highProb_lkGood`), and
the last is `RBM.FastDecayFlow.nonempty_of_highProb`.

**The quantifier order is the one the moment route needs** — `p` fixed, then `N → ∞`, never
`∀ p N` — which is the discipline `docs/paper-deltas.md` records at T188. -/
theorem rhs514QAt_event_rows_witness (hdec : SumZeroDyn.LKDecay X E s t) {m : ℕ} (hm : 1 ≤ m)
    {τ τ₁ D₀ : ℝ} (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hD₀ : 0 < D₀)
    {Env : ℕ → ℝ} {Cenv : ℝ} (hCenv : 0 ≤ Cenv)
    (hEnvle : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Cenv) {D : ℝ} (hD : 0 < D) :
    (∀ N : ℕ, (0 : ℝ) ≤ (B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N)ᶜ).toReal)
    ∧ (∀ N : ℕ, (B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N)ᶜ).toReal
        ≤ (B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N)ᶜ).toReal)
    ∧ (∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
        Env N * (B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N)ᶜ).toReal
            ^ ((1 : ℝ) / ((2 * p : ℕ) : ℝ)) ≤ (N : ℝ) ^ (-D))
    ∧ (∀ p : ℕ, 1 ≤ p → ∀ᶠ N : ℕ in atTop,
        Env N * (B.P (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N)ᶜ).toReal
            ^ ((1 : ℝ) / ((p : ℕ) : ℝ)) ≤ (N : ℝ) ^ (-D))
    ∧ (∀ᶠ N : ℕ in atTop, (FastDecayFlow.lkGood X E s t m τ τ₁ D₀ N).Nonempty) :=
  ⟨fun _ => ENNReal.toReal_nonneg, fun _ => le_rfl,
    fun p hp => eventually_env_mul_lkGood_le hdec hm hτ hτ₁ hD₀ (q := 2 * p) (by omega)
      hCenv hEnvle hD,
    fun p hp => eventually_env_mul_lkGood_le hdec hm hτ hτ₁ hD₀ (q := p) (by omega)
      hCenv hEnvle hD,
    FastDecayFlow.nonempty_of_highProb (FastDecayFlow.highProb_lkGood hdec hm hτ hτ₁ hD₀)⟩

/-- **The `hPr` row of `RBM.Gauss.rhs514QAt_of_kernel_inputs'` cannot be satisfied by making
the event empty.**  T237's gate: as soon as the Markov bound is below `1` the event has a
point, so the "truncate everything to `0`" route to a vacuously true hypothesis table is closed
syntactically.  (For the conclusion to say anything `pr N` has to be far below `1`.) -/
theorem nonempty_of_hPr {Ξ : ℕ → Set Ω} {pr : ℕ → ℝ}
    (hPr : ∀ N, (B.P (Ξ N)ᶜ).toReal ≤ pr N) {N : ℕ} (h1 : pr N < 1) : (Ξ N).Nonempty :=
  nonempty_of_measureReal_compl_lt_one h1 (hPr N)

end EventRowsWitness

end Satisfiability

/-! ### Deviations from the paper introduced by §5b (T246)

**`T246a`.**

*Paper location.*  §7, (7.13) and (7.16); the five terms are (5.91), (5.99), (5.100), (5.103).

*What deviates.*  The paper states (7.16) with a single error symbol: the input tensor is
`(ℓ_u K, δ)`-fast-decaying and the conclusion carries `δ` again.  The formal chain does not:
`RBM.SumZeroDyn.norm_Qop_le_of_fastDecay` (Lemma 5.13) and its `commS` / `ϑ̇` / `Q ⊗ Q`
analogues return the tensor's *own* budget — `RBM.FastDecayFlow.qopErr1`,
`RBM.FastDecayFlow.commErr`, `RBM.FastDecayFlow.dotErr`, `RBM.FastDecayFlow.qqErr` — and three
of those four depend on the time `u` (through `(1-u)⁻¹` and `ℓ̂_u`) as well as on `L` and on the
a priori sizes.  `RBM.Gauss.Rhs514QAt` is a *window*-level statement, so its `hnum` row needs
one number; §5b therefore asks for a dominating `δ' N`, in the four rows `hErrQ`, `hErrC`,
`hErrD`, `hErrE`.  Those four rows are **deterministic** inequalities between explicit
elementary functions on the closed window `[s N, v N] ⊆ [0,1)`; they are not model input, and
they are not quantified over `ω`.

*Is the paper changed?*  No.  This is an accounting device: on the paper's own scaling
`K = W^{τ}` all four budgets are `O(e^{-c K})` times a polynomial in `L` and in the a priori
sizes, so a `δ' N` below any `N^{-D}` exists; the paper simply never names it.

*Line count.*  About 430 lines (`RBM.Gauss.rhs514QAt_of_kernel_inputs'` and the two witnesses).

*Renumbering.*  None.  `RBM.Gauss.rhs514QAt_of_kernel_inputs` keeps its statement, its name and
its consumer `RBM.Gauss.rhs514QAt_of_kernel_inputs_zero_err`.

*What is not supplied.*  There is no `…_zero_err'` twin.  `RBM.Gauss.hnum_le_of_zero_err`
works by sending the error to `0`, and on this route `δ' N = 0` would force `Msz N = 0` — i.e.
the loop vanishing on the event — so the zero-error trick is degenerate here and was not
transplanted.  The `hnum` row of §5b is meant to be discharged asymptotically, with `δ' N`
superpolynomially small, not by an exact cancellation.  A uniform-in-`u` bound on the three
`u`-dependent budgets (compactness of the window plus monotonicity of `ℓ̂`) is likewise left
open; it is deterministic work in `RBM1D/Gauss/FastDecayFlow.lean`, not in this file. -/

end RBM.Gauss

namespace RBM.Gauss

/-! ### §17  The pointwise envelope for the projected drift (T278) -/

open RBM

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {X : Sample B} {E : ℝ}
  {s t : ℕ → ℝ} {n : ℕ}

/-- The normalized maximum of the projected drift at the current time. -/
noncomputable def psiF (H : MomentDuhamel.Hyp X E s t n) (N : ℕ) (u : ℝ)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω) : ℝ :=
  B.scale E N u ^ (n + 2) *
    (Finset.univ : Finset (LoopArg (B.L N) (n + 2))).sup' Finset.univ_nonempty
      (fun b => ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖)

theorem psiF_nonneg (H : MomentDuhamel.Hyp X E s t n) (N : ℕ) (u : ℝ)
    (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω) : 0 ≤ psiF H N u q ω := by
  unfold psiF
  apply mul_nonneg (pow_nonneg (B.scale_pos' hE N hu0 hu1).le _)
  exact le_trans (norm_nonneg _)
    (Finset.le_sup' (fun b => ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖)
      (Finset.mem_univ q.2))

/-- The `hEnvF` row with zero envelope offset, at every sample point. -/
theorem norm_Qop_F_le_psiF (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω) (b : LoopArg (B.L N) (n + 2)) :
    ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖
      ≤ (B.scale E N u)⁻¹ ^ (n + 2) * psiF H N u q ω := by
  have hA0 : 0 < B.scale E N u := B.scale_pos' hE N hu0 hu1
  have hAne : B.scale E N u ≠ 0 := ne_of_gt hA0
  have hmul : (B.scale E N u)⁻¹ ^ (n + 2) * B.scale E N u ^ (n + 2) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hAne, one_pow]
  calc
    ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) b‖
        ≤ (Finset.univ : Finset (LoopArg (B.L N) (n + 2))).sup' Finset.univ_nonempty
            (fun c => ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) c‖) :=
          Finset.le_sup'
            (fun c => ‖Qop (B.L N) (u : ℂ) (H.F N u (X.H N u ω) q.1) c‖)
            (Finset.mem_univ b)
    _ = (B.scale E N u)⁻¹ ^ (n + 2) * psiF H N u q ω := by
      unfold psiF
      rw [← mul_assoc, hmul, one_mul]

/-- Apply the deterministic fast-decay `Qop` bound to the normalized maximum, retaining
the size estimate at the current time `u`. -/
theorem psiF_le_of_fastDecay (H : MomentDuhamel.Hyp X E s t n)
    (N : ℕ) {u K M δF : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hK : 1 ≤ K) (hδF : 0 ≤ δF)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (hFM : ∀ b, ‖H.F N u (X.H N u ω) q.1 b‖ ≤ M)
    (hFD : FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * K) δF
      (H.F N u (X.H N u ω) q.1)) :
    psiF H N u q ω ≤ B.scale E N u ^ (n + 2) *
      ((1 + (6 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) * M
        + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hFM q.2)
  have hQ := SumZeroDyn.norm_Qop_le_of_fastDecay (B.L N) (B.three_le_L N)
    hu0 hu1 hK hM0 hδF hFM hFD
  unfold psiF
  exact mul_le_mul_of_nonneg_left
    (Finset.sup'_le _ _ (fun b _ => hQ b)) (pow_nonneg (B.scale_nonneg E N hu1.le) _)

/-- The projected drift estimate with the *pointwise* (5.77) size at `u`.  Its decay
input is precisely the drift `hDecF` row with `Kd = 4*K`; no uniform `Msz` appears. -/
theorem psiF_le_of_drift_inputs (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u K δ δF CK C1 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N)
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u)
    (hell : 1 / 2 ≤ B.ell N u) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hδF : 0 ≤ δF) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1)
    (hDecF : FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * (4 * K)) δF
      (H.F N u (X.H N u ω) q.1)) :
    psiF H N u q ω ≤ B.scale E N u ^ (n + 2) *
      ((1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) *
        ((B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ *
          ((K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
          + (B.W N : ℝ) * (B.L N : ℝ) * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
              DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1))
        + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF) := by
  let M : ℝ := (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ *
      ((K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
    + (B.W N : ℝ) * (B.L N : ℝ) * δ *
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
        DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1)
  have hFM : ∀ b, ‖H.F N u (X.H N u ω) q.1 b‖ ≤ M := by
    intro b
    exact DriftBound.norm_Hyp_F_le H ω q.1 b hE hu0 hu1 hsu hut
      hA hη hell hK hδ hCK hC10 hKb hKd hDd hLd hC1
  have hQ := psiF_le_of_fastDecay H N hu0 hu1 (by nlinarith : 1 ≤ 4 * K)
    hδF q ω hFM hDecF
  simpa only [M, show 6 * Real.exp 1 * cTwo52 * (4 * K) =
      24 * Real.exp 1 * cTwo52 * K by ring] using hQ

/-- The normalization cancels at the current time, leaving only the time weight
`eta_u⁻¹` on the main term. -/
theorem psiF_le_of_drift_inputs' (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u K δ δF CK C1 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N)
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u)
    (hell : 1 / 2 ≤ B.ell N u) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hδF : 0 ≤ δF) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1)
    (hDecF : FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * (4 * K)) δF
      (H.F N u (X.H N u ω) q.1)) :
    psiF H N u q ω ≤
      (etaT E u)⁻¹ * (1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) *
        (K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω
      + B.scale E N u ^ (n + 2) *
        ((1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) *
          ((B.W N : ℝ) * (B.L N : ℝ) * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
              DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1))
          + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF) := by
  have h := psiF_le_of_drift_inputs H hE N hu0 hu1 hsu hut hA hη hell hK hδ
    hδF hCK hC10 q ω hKb hKd hDd hLd hC1 hDecF
  have hA0 : 0 < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hcancel : B.scale E N u ^ (n + 2) * (B.scale E N u)⁻¹ ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hA0.ne', one_pow]
  let a : ℝ := B.scale E N u
  let c : ℝ := 1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)
  let x : ℝ := (etaT E u)⁻¹ *
    ((K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
  let e : ℝ := (B.W N : ℝ) * (B.L N : ℝ) * δ *
    ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
      DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1)
  let z : ℝ := (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF
  have hh : psiF H N u q ω ≤ a ^ (n + 2) * (c * (a⁻¹ ^ (n + 2) * x + e) + z) := by
    dsimp [a, c, x, e, z]
    convert h using 1 <;> ring
  have hc : a ^ (n + 2) * a⁻¹ ^ (n + 2) = 1 := hcancel
  have heq : a ^ (n + 2) * (c * (a⁻¹ ^ (n + 2) * x + e) + z)
      = c * x + a ^ (n + 2) * (c * e + z) := by
    calc
      _ = (a ^ (n + 2) * a⁻¹ ^ (n + 2)) * (c * x)
            + a ^ (n + 2) * (c * e + z) := by ring
      _ = _ := by rw [hc]; ring
  calc
    psiF H N u q ω ≤ a ^ (n + 2) * (c * (a⁻¹ ^ (n + 2) * x + e) + z) := hh
    _ = c * x + a ^ (n + 2) * (c * e + z) := heq
    _ = _ := by dsimp [a, c, x, e, z]; ring

/-- The §19 projected-drift bound with `K` controlled only at lengths `2 … n+2`. -/
theorem psiF_le_of_drift_inputs_bounded (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u K δ δF CK C1 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N)
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u)
    (hell : 1 / 2 ≤ B.ell N u) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hδF : 0 ≤ δF) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1)
    (hDecF : FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * (4 * K)) δF
      (H.F N u (X.H N u ω) q.1)) :
    psiF H N u q ω ≤ B.scale E N u ^ (n + 2) *
      ((1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) *
        ((B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ *
          ((K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
          + (B.W N : ℝ) * (B.L N : ℝ) * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
              DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1))
        + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF) := by
  let M : ℝ := (B.scale E N u)⁻¹ ^ (n + 2) * (etaT E u)⁻¹ *
      ((K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
    + (B.W N : ℝ) * (B.L N : ℝ) * δ *
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
        DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1)
  have hFM : ∀ b, ‖H.F N u (X.H N u ω) q.1 b‖ ≤ M := by
    intro b
    exact DriftBound.norm_Hyp_F_le' H ω q.1 b hE hu0 hu1 hsu hut
      hA hη hell hK hδ hCK hC10 hKb hKd hDd hLd hC1
  have hQ := psiF_le_of_fastDecay H N hu0 hu1 (by nlinarith : 1 ≤ 4 * K)
    hδF q ω hFM hDecF
  simpa only [M, show 6 * Real.exp 1 * cTwo52 * (4 * K) =
      24 * Real.exp 1 * cTwo52 * K by ring] using hQ

/-- The normalized §19 bound with bounded-length `K` input. -/
theorem psiF_le_of_drift_inputs'' (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (N : ℕ) {u K δ δF CK C1 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hsu : s N ≤ u) (hut : u ≤ t N)
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u)
    (hell : 1 / 2 ≤ B.ell N u) (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hδF : 0 ≤ δF) (hCK : 0 ≤ CK) (hC10 : 0 ≤ C1)
    (q : LoopData (B.L N) (n + 2)) (ω : Ω)
    (hKb : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
      ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1))
    (hKd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)))
    (hC1 : X.xiLK E N u ω 1 ≤ C1)
    (hDecF : FastDecay (B.L N) (ellHat (B.L N) (u : ℂ) * (4 * K)) δF
      (H.F N u (X.H N u ω) q.1)) :
    psiF H N u q ω ≤
      (etaT E u)⁻¹ * (1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) *
        (K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω
      + B.scale E N u ^ (n + 2) *
        ((1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)) *
          ((B.W N : ℝ) * (B.L N : ℝ) * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
              DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1))
          + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF) := by
  have h := psiF_le_of_drift_inputs_bounded H hE N hu0 hu1 hsu hut hA hη hell hK hδ
    hδF hCK hC10 q ω hKb hKd hDd hLd hC1 hDecF
  have hA0 : 0 < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hcancel : B.scale E N u ^ (n + 2) * (B.scale E N u)⁻¹ ^ (n + 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hA0.ne', one_pow]
  let a : ℝ := B.scale E N u
  let c : ℝ := 1 + (24 * Real.exp 1 * cTwo52 * K) ^ (n + 1)
  let x : ℝ := (etaT E u)⁻¹ *
    ((K + 2) * DriftBound.cDrift n CK C1 * SumZeroDyn.xiRhs X E (n + 2) N u ω)
  let e : ℝ := (B.W N : ℝ) * (B.L N : ℝ) * δ *
    ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
      DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * C1)
  let z : ℝ := (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δF
  have hh : psiF H N u q ω ≤ a ^ (n + 2) * (c * (a⁻¹ ^ (n + 2) * x + e) + z) := by
    dsimp [a, c, x, e, z]
    convert h using 1 <;> ring
  have hc : a ^ (n + 2) * a⁻¹ ^ (n + 2) = 1 := hcancel
  have heq : a ^ (n + 2) * (c * (a⁻¹ ^ (n + 2) * x + e) + z)
      = c * x + a ^ (n + 2) * (c * e + z) := by
    calc
      _ = (a ^ (n + 2) * a⁻¹ ^ (n + 2)) * (c * x)
            + a ^ (n + 2) * (c * e + z) := by ring
      _ = _ := by rw [hc]; ring
  calc
    psiF H N u q ω ≤ a ^ (n + 2) * (c * (a⁻¹ ^ (n + 2) * x + e) + z) := hh
    _ = c * x + a ^ (n + 2) * (c * e + z) := heq
    _ = _ := by dsimp [a, c, x, e, z]; ring

/-- The `K` size input required by the bounded-length drift chain, uniformly in `N` and `u`.
Both cut-and-glue factors have lengths in `2 … n+2`; no length-one or empty-loop case occurs. -/
theorem exists_Kval_bound_for_psiF (hE : |E| < 2) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
      ∀ J : LoopIdx (ZMod (B.L N)), J.WF → 2 ≤ J.length → J.length ≤ n + 2 →
        ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ (J.length - 1) :=
  exists_norm_Kval_le_upto B hE (n + 2)

/-- The finite error sum in the bounded drift estimate has the same stochastic size as
its finitely many constituents. -/
theorem xiSum_stochDom_of_flowXiLK
    (hxi : ∀ m ∈ Finset.Icc 1 (n + 2),
      StochDom B.P (Step3.flowXiLK X E s t m) (fun _ _ _ => (1 : ℝ))) :
    StochDom B.P
      (fun N (u : TimeIcc s t N) ω => DriftBound.xiSum X E (n + 2) N u ω)
      (fun _ _ _ => (n + 2 : ℝ)) := by
  have h := SumZeroDyn.stochDom_finset_sum (P := B.P) (Finset.Icc 1 (n + 2))
    (ξ := fun m => Step3.flowXiLK X E s t m)
    (ζ := fun _ _ _ => (1 : ℝ)) hxi
  convert h using 1
  · funext N u ω
    rfl
  · funext N u ω
    rw [Nat.card_Icc]
    push_cast
    ring

/-- The projected drift's main coefficient costs only `R^(n+4)` when its radius,
one-loop input and right-hand side are all at most `R`. -/
theorem psiF_main_coeff_le_rpow (n : ℕ) {CK R : ℝ} (hCK : 0 ≤ CK) (hR : 1 ≤ R) :
    (1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
      (R + 2) * DriftBound.cDrift n CK R * R ≤
      (3 * (1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
        DriftBound.cDrift n CK 1) * R ^ (n + 4) := by
  let C : ℝ := 24 * Real.exp 1 * cTwo52
  have hC : 0 ≤ C := by dsimp [C]; have := cTwo52_pos; positivity
  have hR0 : 0 ≤ R := by linarith
  have hRpow : 1 ≤ R ^ (n + 1) := one_le_pow₀ hR
  have hCpow : 0 ≤ C ^ (n + 1) := pow_nonneg hC _
  have hfac : 1 + (C * R) ^ (n + 1) ≤ (1 + C ^ (n + 1)) * R ^ (n + 1) := by
    rw [mul_pow]
    nlinarith [mul_nonneg hCpow (sub_nonneg.mpr hRpow)]
  have hrad : R + 2 ≤ 3 * R := by linarith
  have hdrift : DriftBound.cDrift n CK R ≤ DriftBound.cDrift n CK 1 * R := by
    unfold DriftBound.cDrift
    have he : 0 ≤ 4 * Real.exp 1 * ((n : ℝ) + 2) ^ 2 := by positivity
    have hnc : 0 ≤ (n : ℝ) * CK + 1 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) hnc]
  have hd0 : 0 ≤ DriftBound.cDrift n CK R := by unfold DriftBound.cDrift; positivity
  have hd1 : 0 ≤ DriftBound.cDrift n CK 1 := by unfold DriftBound.cDrift; positivity
  have hfac0 : 0 ≤ 1 + (C * R) ^ (n + 1) := by positivity
  have hfac1 : 0 ≤ (1 + C ^ (n + 1)) * R ^ (n + 1) := by positivity
  calc
    (1 + (C * R) ^ (n + 1)) * (R + 2) * DriftBound.cDrift n CK R * R
        ≤ ((1 + C ^ (n + 1)) * R ^ (n + 1)) * (3 * R) *
            (DriftBound.cDrift n CK 1 * R) * R := by
          gcongr
    _ = (3 * (1 + C ^ (n + 1)) * DriftBound.cDrift n CK 1) *
          R ^ (n + 4) := by
          rw [show n + 4 = (n + 1) + 3 by omega, pow_add]
          ring
    _ = _ := by dsimp [C]

/-- The two additive errors in the projected drift have polynomial degree at most
`2n+6` before the fast-decay factor is applied. -/
theorem psiF_error_coeff_le_rpow (n : ℕ) {A W L R N δ : ℝ}
    (hN : 1 ≤ N) (hA : 0 ≤ A) (hAN : A ≤ N) (hW : 0 ≤ W) (hWN : W ≤ N)
    (hL : 0 ≤ L) (hLN : L ≤ N) (hR : 1 ≤ R) (hRN : R ≤ N) (hδ : 0 ≤ δ)
    {S : ℝ} (hS : 0 ≤ S) (hSN : S ≤ (n + 2 : ℝ) * R) :
    A ^ (n + 2) *
      ((1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
        (W * L * δ *
          ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * S + ((n : ℝ) + 2) * R))
        + (2 * cTwo52) ^ (n + 1) * L ^ (n + 1) * δ) ≤
      ((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
          ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
        + (2 * cTwo52) ^ (n + 1)) * N ^ (2 * n + 6) * δ := by
  let C : ℝ := 24 * Real.exp 1 * cTwo52
  let c : ℝ := (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2)
  let d : ℝ := (2 * cTwo52) ^ (n + 1)
  have hC : 0 ≤ C := by dsimp [C]; have := cTwo52_pos; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; have := cTwo52_pos; positivity
  have hR0 : 0 ≤ R := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hRpow : 1 ≤ R ^ (n + 1) := one_le_pow₀ hR
  have hfac : 1 + (C * R) ^ (n + 1) ≤ (1 + C ^ (n + 1)) * N ^ (n + 1) := by
    calc
      _ ≤ (1 + C ^ (n + 1)) * R ^ (n + 1) := by
        rw [mul_pow]
        nlinarith [pow_nonneg hC (n + 1)]
      _ ≤ (1 + C ^ (n + 1)) * N ^ (n + 1) := by gcongr
  have hbr : (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * S + ((n : ℝ) + 2) * R
      ≤ c * N := by
    dsimp [c]
    have hq : 0 ≤ (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left hSN hq
    nlinarith [mul_nonneg (sub_nonneg.mpr hRN) (by positivity : (0 : ℝ) ≤
      (2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))]
  have hpow : A ^ (n + 2) ≤ N ^ (n + 2) := pow_le_pow_left₀ hA hAN _
  have hWL : W * L ≤ N ^ 2 := by
    have h := mul_le_mul hWN hLN hL hN0
    nlinarith
  have hLp : L ^ (n + 1) ≤ N ^ (n + 1) := pow_le_pow_left₀ hL hLN _
  have hsmall : N ^ (2 * n + 3) ≤ N ^ (2 * n + 6) := pow_le_pow_right₀ hN (by omega)
  have hlarge : N ^ (n + 2) *
      ((1 + C ^ (n + 1)) * N ^ (n + 1) *
        (N ^ 2 * δ * (c * N)) + d * N ^ (n + 1) * δ)
      ≤ ((1 + C ^ (n + 1)) * c + d) * N ^ (2 * n + 6) * δ := by
    have hp : 0 ≤ (1 + C ^ (n + 1)) * c := by positivity
    have hsmall' := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hd hδ)
    calc
      _ = (1 + C ^ (n + 1)) * c * N ^ (2 * n + 6) * δ +
            d * N ^ (2 * n + 3) * δ := by
          rw [show 2 * n + 6 = (n + 2) + (n + 1) + 2 + 1 by omega,
            show 2 * n + 3 = (n + 2) + (n + 1) by omega]
          simp only [pow_add]
          ring
      _ ≤ (1 + C ^ (n + 1)) * c * N ^ (2 * n + 6) * δ +
            d * N ^ (2 * n + 6) * δ := by linarith
      _ = _ := by ring
  calc
    A ^ (n + 2) *
        ((1 + (C * R) ^ (n + 1)) *
          (W * L * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * S + ((n : ℝ) + 2) * R))
          + d * L ^ (n + 1) * δ)
        ≤ N ^ (n + 2) *
          ((1 + C ^ (n + 1)) * N ^ (n + 1) * (N ^ 2 * δ * (c * N))
            + d * N ^ (n + 1) * δ) := by
          gcongr
    _ ≤ ((1 + C ^ (n + 1)) * c + d) * N ^ (2 * n + 6) * δ := hlarge
    _ = _ := by dsimp [C, c, d]

/-- The radius cost and both additive errors fit into arbitrary stochastic-domination
exponents after the decay exponent is chosen following the loop length. -/
theorem eventually_psiF_coeff_bounds (n : ℕ) (CK : ℝ) {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) :
    ∃ θ D₁ : ℝ, 0 < θ ∧ 0 < D₁ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        1 ≤ (N : ℝ) ∧ 1 ≤ (N : ℝ) ^ θ ∧ (N : ℝ) ^ θ ≤ N ∧
        (3 * (1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
            DriftBound.cDrift n CK 1) * (N : ℝ) ^ ((n + 4) * θ) ≤ (N : ℝ) ^ τ ∧
        (((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
          + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (2 * n + 6) *
            (N : ℝ) ^ (-D₁) ≤ (N : ℝ) ^ (-D)) := by
  let θ : ℝ := min (τ / ((n : ℝ) + 5)) (1 / 2)
  let D₁ : ℝ := D + 2 * (n : ℝ) + 8
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hD₁ : 0 < D₁ := by dsimp [D₁]; positivity
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [min_le_right (τ / ((n : ℝ) + 5)) (1 / 2)]
  have hmainexp : ((n : ℝ) + 4) * θ < τ := by
    have hn : 0 < (n : ℝ) + 5 := by positivity
    have hθle : θ ≤ τ / ((n : ℝ) + 5) := min_le_left _ _
    have hpos : 0 ≤ (n : ℝ) + 4 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hθle hpos
    have hstrict : ((n : ℝ) + 4) * (τ / ((n : ℝ) + 5)) < τ := by
      calc
        _ = (((n : ℝ) + 4) * τ) / ((n : ℝ) + 5) := by ring
        _ < τ := (div_lt_iff₀ hn).2 (by nlinarith [hτ])
    exact lt_of_le_of_lt hstep hstrict
  have herrExp : 2 * (n : ℝ) + 6 + -D₁ = -D - 2 := by dsimp [D₁]; ring
  have hmain := SumZeroDyn.eventually_const_mul_rpow_le
    (3 * (1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
      DriftBound.cDrift n CK 1) hmainexp
  have herr := SumZeroDyn.eventually_const_mul_rpow_le
    ((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
        ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
      + (2 * cTwo52) ^ (n + 1))
    (show -D - 2 < -D by linarith)
  refine ⟨θ, D₁, hθ, hD₁, ?_⟩
  filter_upwards [hmain, herr, Filter.eventually_ge_atTop 1] with N hm he hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hpowcast : (N : ℝ) ^ (2 * n + 6) =
      (N : ℝ) ^ (2 * (n : ℝ) + 6) := by
    calc
      _ = (N : ℝ) ^ (((2 * n + 6 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ = _ := by congr 1; push_cast; ring
  have heqpow : (N : ℝ) ^ (2 * n + 6) * (N : ℝ) ^ (-D₁) =
      (N : ℝ) ^ (-D - 2) := by
    calc
      _ = (N : ℝ) ^ (2 * (n : ℝ) + 6) * (N : ℝ) ^ (-D₁) := by rw [hpowcast]
      _ = (N : ℝ) ^ (2 * (n : ℝ) + 6 + -D₁) := by
        rw [Real.rpow_add hN0 (2 * (n : ℝ) + 6) (-D₁)]
      _ = _ := by rw [herrExp]
  refine ⟨hN1, Real.one_le_rpow hN1 hθ.le,
    (by simpa using Real.rpow_le_rpow_of_exponent_le hN1 hθ1), hm, ?_⟩
  calc
    ((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
          ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
        + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (2 * n + 6) *
          (N : ℝ) ^ (-D₁)
      = ((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
          ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
        + (2 * cTwo52) ^ (n + 1)) * (N : ℝ) ^ (-D - 2) := by
          rw [mul_assoc, heqpow]
    _ ≤ (N : ℝ) ^ (-D) := he

set_option maxHeartbeats 1600000 in
/-- The projected drift has the required inverse-time stochastic envelope. The decay
of the drift itself is supplied on the same event as the three loop-decay clauses. -/
theorem psiF_stochDom_etaT_inv_of_drift_inputs (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    (hxi : ∀ m ∈ Finset.Icc 1 (n + 2),
      StochDom B.P (Step3.flowXiLK X E s t m) (fun _ _ _ => (1 : ℝ)))
    (hRhs : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => SumZeroDyn.xiRhs X E (n + 2) N u ω)
      (fun _ _ _ => (1 : ℝ)))
    (hDecF : ∀ θ > (0 : ℝ), ∀ D > (0 : ℝ),
      HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
        ∀ q : LoopData (B.L N) (n + 2),
          FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) *
            (4 * (N : ℝ) ^ θ)) ((N : ℝ) ^ (-D))
            (H.F N (u : ℝ) (X.H N (u : ℝ) ω) q.1)})) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        psiF H N (p.1 : ℝ) p.2 ω)
      (fun N p _ => (etaT E (p.1 : ℝ))⁻¹) := by
  obtain ⟨CK, hCK, hKb⟩ := exists_Kval_bound_for_psiF (B := B) (n := n) hE
  have hxiS := xiSum_stochDom_of_flowXiLK (B := B) (X := X)
    (E := E) (s := s) (t := t) (n := n) hxi
  have hxi1 := hxi 1 (by simp)
  refine StochDom.of_highProb_add_rpow_neg (b := 0)
    (HighProb.of_eventually_univ ?_) ?_
  · filter_upwards with N ω p
    have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    simpa using one_le_etaT_inv hE hu0 hu1
  intro τ hτ D hD
  obtain ⟨θ, D₁, hθ, hD₁, hnum⟩ := eventually_psiF_coeff_bounds n CK hτ hD
  have hdec := highProb_driftInputs_decay X hE hs0 ht1 hFI n θ hθ D₁ hD₁
  have hxi1ev := highProb_flowXiLK_le X hxi1 hθ
  have hxiSev := hxiS.highProb hθ
  have hRhsev := hRhs.highProb hθ
  have hFev := hDecF θ hθ D₁ hD₁
  have hgood := ((((hdec.inter hxi1ev).inter hxiSev).inter hRhsev).inter hFev)
  refine HighProb.mono hgood ?_
  filter_upwards [hnum, SumZeroDyn.flow_crude hE hs0 hst ht1 hc,
    Filter.eventually_ge_atTop 1] with N hnumN hcr hN
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨⟨⟨⟨hdecN, hxi1N⟩, hxiSN⟩, hRhsN⟩, hFN⟩ := hω
  obtain ⟨hN1, hR1, hRN, hnumMain, hnumErr⟩ := hnumN
  obtain ⟨hLN, hWN, _, hscale⟩ := hcr
  have hN0 : 0 < (N : ℝ) := by linarith
  have hR0 : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg hN0.le _
  have hδ0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
  intro p
  let u : ℝ := (p.1 : ℝ)
  let R : ℝ := (N : ℝ) ^ θ
  let δ : ℝ := (N : ℝ) ^ (-D₁)
  have hu0 : 0 ≤ u := (hs0 N).trans p.1.2.1
  have hu1 : u < 1 := p.1.2.2.trans_lt (ht1 N)
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hA : 1 ≤ B.scale E N u := (hscale p.1).1
  have hAN : B.scale E N u ≤ N := (hscale p.1).2.1
  have hell : 1 / 2 ≤ B.ell N u := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]
    linarith
  have hpt := psiF_le_of_drift_inputs'' H hE N hu0 hu1 p.1.2.1 p.1.2.2
    hA hη hell hR1 hδ0 hδ0 hCK hR0 p.2 ω
    (fun J hJ h2 hlen => hKb N u hu0 hu1 J hJ h2 hlen)
    (hdecN p.1).1 (hdecN p.1).2.1 (hdecN p.1).2.2
    (hxi1N p.1) (hFN p.1 p.2)
  have hcoef0 : 0 ≤ (1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
      (R + 2) * DriftBound.cDrift n CK R := by
    have := cTwo52_pos
    unfold DriftBound.cDrift
    positivity
  have hmain0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.mpr hη.le
  have hmain : (etaT E u)⁻¹ *
      (1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
      (R + 2) * DriftBound.cDrift n CK R *
      SumZeroDyn.xiRhs X E (n + 2) N u ω ≤
        (N : ℝ) ^ τ * (etaT E u)⁻¹ := by
    have hRhs' : SumZeroDyn.xiRhs X E (n + 2) N u ω ≤ R := by
      simpa [R] using hRhsN p.1
    have h1 := mul_le_mul_of_nonneg_left hRhs' hcoef0
    have h2 := psiF_main_coeff_le_rpow n hCK hR1
    have hRpow : R ^ (n + 4) = (N : ℝ) ^ (((n : ℝ) + 4) * θ) := by
      dsimp [R]
      calc
        _ = ((N : ℝ) ^ θ) ^ (((n + 4 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
        _ = (N : ℝ) ^ (θ * (((n + 4 : ℕ) : ℝ))) := by rw [Real.rpow_mul hN0.le]
        _ = _ := by congr 1; push_cast; ring
    rw [hRpow] at h2
    have h3 := mul_le_mul_of_nonneg_left (h1.trans (h2.trans hnumMain)) hmain0
    dsimp [R] at h3
    convert h3 using 1 <;> ring
  have hS0 : 0 ≤ DriftBound.xiSum X E (n + 2) N u ω := by
    unfold DriftBound.xiSum
    exact Finset.sum_nonneg fun m _ => X.xiLK_nonneg (by linarith : 0 ≤ B.scale E N u)
  have hSN : DriftBound.xiSum X E (n + 2) N u ω ≤ (n + 2 : ℝ) * R := by
    simpa [R, mul_comm] using hxiSN p.1
  have herror := psiF_error_coeff_le_rpow n hN1 (by linarith : 0 ≤ B.scale E N u)
    hAN (Nat.cast_nonneg _) hWN (Nat.cast_nonneg _) hLN hR1 hRN hδ0 hS0
    hSN
  have herror' : B.scale E N u ^ (n + 2) *
        ((1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
          ((B.W N : ℝ) * (B.L N : ℝ) * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
              DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * R))
          + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δ)
        ≤ (N : ℝ) ^ (-D) := herror.trans hnumErr
  dsimp [R, δ] at hmain herror' hpt
  linarith

private theorem eventually_psiF_poly_error_bound (n : ℕ) (C : ℝ)
    {D : ℝ} (hD : 0 < D) :
    ∃ D₁ : ℝ, 0 < D₁ ∧ ∀ᶠ N : ℕ in Filter.atTop,
      1 ≤ (N : ℝ) ∧
      ((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
          ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
        + (2 * cTwo52) ^ (n + 1)) *
        ((1 + C) * (N : ℝ) ^ (3 * (n + 2) + 1)) ^ (2 * n + 6) *
          (N : ℝ) ^ (-D₁) ≤ (N : ℝ) ^ (-D) := by
  let k : ℕ := 3 * (n + 2) + 1
  let e : ℕ := k * (2 * n + 6)
  let D₁ : ℝ := D + (e : ℝ) + 1
  let c : ℝ := (1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2)) +
        (2 * cTwo52) ^ (n + 1)
  have hev := SumZeroDyn.eventually_const_mul_rpow_le
    (c * (1 + C) ^ (2 * n + 6)) (show -D - 1 < -D by linarith)
  refine ⟨D₁, by dsimp [D₁]; positivity, ?_⟩
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with N hnum hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨hN1, ?_⟩
  have hpow : ((1 + C) * (N : ℝ) ^ k) ^ (2 * n + 6) =
      (1 + C) ^ (2 * n + 6) * (N : ℝ) ^ e := by
    dsimp [e]
    rw [mul_pow, pow_mul]
  have htime : (N : ℝ) ^ e * (N : ℝ) ^ (-D₁) =
      (N : ℝ) ^ (-D - 1) := by
    calc
      _ = (N : ℝ) ^ (e : ℝ) * (N : ℝ) ^ (-D₁) := by rw [Real.rpow_natCast]
      _ = (N : ℝ) ^ ((e : ℝ) + -D₁) := by rw [Real.rpow_add hN0]
      _ = _ := by congr 1; dsimp [D₁]; ring
  change c * ((1 + C) * (N : ℝ) ^ k) ^ (2 * n + 6) *
      (N : ℝ) ^ (-D₁) ≤ (N : ℝ) ^ (-D)
  rw [hpow]
  calc
    c * ((1 + C) ^ (2 * n + 6) * (N : ℝ) ^ e) * (N : ℝ) ^ (-D₁)
        = (c * (1 + C) ^ (2 * n + 6)) * ((N : ℝ) ^ e * (N : ℝ) ^ (-D₁)) := by ring
    _ = (c * (1 + C) ^ (2 * n + 6)) * (N : ℝ) ^ (-D - 1) := by rw [htime]
    _ ≤ (N : ℝ) ^ (-D) := hnum

set_option maxHeartbeats 1600000 in
/-- The projected drift envelope with a deterministic polynomial bound for the finite
additive loop sum. Only the length-one loop needs stochastic domination. -/
theorem psiF_stochDom_etaT_inv_of_drift_inputs' (H : MomentDuhamel.Hyp X E s t n)
    (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hFI : LKDecayQuant.FlowInputs X E s t)
    (hxi1 : StochDom B.P (Step3.flowXiLK X E s t 1)
      (fun _ _ _ => (1 : ℝ)))
    (hRhs : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => SumZeroDyn.xiRhs X E (n + 2) N u ω)
      (fun _ _ _ => (1 : ℝ)))
    (hDecF : ∀ θ > (0 : ℝ), ∀ D > (0 : ℝ),
      HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N,
        ∀ q : LoopData (B.L N) (n + 2),
          FastDecay (B.L N) (ellHat (B.L N) ((u : ℝ) : ℂ) *
            (4 * (N : ℝ) ^ θ)) ((N : ℝ) ^ (-D))
            (H.F N (u : ℝ) (X.H N (u : ℝ) ω) q.1)})) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) (n + 2)) ω =>
        psiF H N (p.1 : ℝ) p.2 ω)
      (fun N p _ => (etaT E (p.1 : ℝ))⁻¹) := by
  obtain ⟨CK, hCK, hKb⟩ := exists_Kval_bound_for_psiF (B := B) (n := n) hE
  obtain ⟨Cpoly, hCpoly, hpoly⟩ :=
    exists_xiSum_poly_window X hE hs0 hst ht1 hc (n + 2)
  refine StochDom.of_highProb_add_rpow_neg (b := 0)
    (HighProb.of_eventually_univ ?_) ?_
  · filter_upwards with N ω p
    have hu0 : 0 ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    simpa using one_le_etaT_inv hE hu0 hu1
  intro τ hτ D hD
  obtain ⟨θ, _Dold, hθ, _hDold, hnum⟩ :=
    eventually_psiF_coeff_bounds n CK hτ hD
  obtain ⟨D₁, hD₁, hpolyNum⟩ :=
    eventually_psiF_poly_error_bound n Cpoly hD
  have hdec := highProb_driftInputs_decay X hE hs0 ht1 hFI n θ hθ D₁ hD₁
  have hxi1ev := highProb_flowXiLK_le X hxi1 hθ
  have hRhsev := hRhs.highProb hθ
  have hFev := hDecF θ hθ D₁ hD₁
  have hgood := (((hdec.inter hxi1ev).inter hRhsev).inter hFev)
  refine HighProb.mono hgood ?_
  filter_upwards [hnum, hpolyNum, hpoly,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc,
    Filter.eventually_ge_atTop 1] with N hnumN hpolyNumN hpolyN hcr hN
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨⟨⟨hdecN, hxi1N⟩, hRhsN⟩, hFN⟩ := hω
  obtain ⟨hN1, hR1, hRN, hnumMain, _hnumErr⟩ := hnumN
  obtain ⟨_hN1poly, hnumPoly⟩ := hpolyNumN
  obtain ⟨hLN, hWN, _, hscale⟩ := hcr
  have hN0 : 0 < (N : ℝ) := by linarith
  have hR0 : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg hN0.le _
  have hδ0 : 0 ≤ (N : ℝ) ^ (-D₁) := Real.rpow_nonneg hN0.le _
  intro p
  let u : ℝ := (p.1 : ℝ)
  let R : ℝ := (N : ℝ) ^ θ
  let δ : ℝ := (N : ℝ) ^ (-D₁)
  have hu0 : 0 ≤ u := (hs0 N).trans p.1.2.1
  have hu1 : u < 1 := p.1.2.2.trans_lt (ht1 N)
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hA : 1 ≤ B.scale E N u := (hscale p.1).1
  have hAN : B.scale E N u ≤ N := (hscale p.1).2.1
  have hell : 1 / 2 ≤ B.ell N u := by
    have h := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]
    linarith
  have hpt := psiF_le_of_drift_inputs'' H hE N hu0 hu1 p.1.2.1 p.1.2.2
    hA hη hell hR1 hδ0 hδ0 hCK hR0 p.2 ω
    (fun J hJ h2 hlen => hKb N u hu0 hu1 J hJ h2 hlen)
    (hdecN p.1).1 (hdecN p.1).2.1 (hdecN p.1).2.2
    (hxi1N p.1) (hFN p.1 p.2)
  have hcoef0 : 0 ≤ (1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
      (R + 2) * DriftBound.cDrift n CK R := by
    have := cTwo52_pos
    unfold DriftBound.cDrift
    positivity
  have hmain0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.mpr hη.le
  have hmain : (etaT E u)⁻¹ *
      (1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
      (R + 2) * DriftBound.cDrift n CK R *
      SumZeroDyn.xiRhs X E (n + 2) N u ω ≤
        (N : ℝ) ^ τ * (etaT E u)⁻¹ := by
    have hRhs' : SumZeroDyn.xiRhs X E (n + 2) N u ω ≤ R := by
      simpa [R] using hRhsN p.1
    have h1 := mul_le_mul_of_nonneg_left hRhs' hcoef0
    have h2 := psiF_main_coeff_le_rpow n hCK hR1
    have hRpow : R ^ (n + 4) = (N : ℝ) ^ (((n : ℝ) + 4) * θ) := by
      dsimp [R]
      calc
        _ = ((N : ℝ) ^ θ) ^ (((n + 4 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
        _ = (N : ℝ) ^ (θ * (((n + 4 : ℕ) : ℝ))) := by rw [Real.rpow_mul hN0.le]
        _ = _ := by congr 1; push_cast; ring
    rw [hRpow] at h2
    have h3 := mul_le_mul_of_nonneg_left (h1.trans (h2.trans hnumMain)) hmain0
    dsimp [R] at h3
    convert h3 using 1 <;> ring
  have hS0 : 0 ≤ DriftBound.xiSum X E (n + 2) N u ω := by
    unfold DriftBound.xiSum
    exact Finset.sum_nonneg fun m _ => X.xiLK_nonneg (by linarith : 0 ≤ B.scale E N u)
  have hSN : DriftBound.xiSum X E (n + 2) N u ω ≤
      Cpoly * (N : ℝ) ^ (3 * (n + 2) + 1) := by
    simpa [u] using hpolyN p.1 ω
  let Rbig : ℝ := (1 + Cpoly) * (N : ℝ) ^ (3 * (n + 2) + 1)
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (3 * (n + 2) + 1) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  have hNpow0 : 0 ≤ (N : ℝ) ^ (3 * (n + 2) + 1) := pow_nonneg hN0.le _
  have hNbig : (N : ℝ) ≤ Rbig := by
    dsimp [Rbig]
    nlinarith [mul_nonneg hCpoly hNpow0]
  have hRbig1 : 1 ≤ Rbig := hN1.trans hNbig
  have hRle : R ≤ Rbig := hRN.trans hNbig
  have hSbig : DriftBound.xiSum X E (n + 2) N u ω ≤ (n + 2 : ℝ) * Rbig := by
    have hn : (1 : ℝ) ≤ (n + 2 : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
    have hc : Cpoly ≤ (n + 2 : ℝ) * (1 + Cpoly) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) hCpoly]
    exact hSN.trans (by
      dsimp [Rbig]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hNpow0)
  have herrorBig := psiF_error_coeff_le_rpow n hRbig1
    (by linarith : 0 ≤ B.scale E N u) (hAN.trans hNbig)
    (Nat.cast_nonneg _) (hWN.trans hNbig)
    (Nat.cast_nonneg _) (hLN.trans hNbig)
    hRbig1 (le_refl Rbig) hδ0 hS0 hSbig
  have herror' : B.scale E N u ^ (n + 2) *
        ((1 + (24 * Real.exp 1 * cTwo52 * R) ^ (n + 1)) *
          ((B.W N : ℝ) * (B.L N : ℝ) * δ *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
              DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * R))
          + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δ)
        ≤ (N : ℝ) ^ (-D) := by
    calc
      _ ≤ B.scale E N u ^ (n + 2) *
          ((1 + (24 * Real.exp 1 * cTwo52 * Rbig) ^ (n + 1)) *
            ((B.W N : ℝ) * (B.L N : ℝ) * δ *
              ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 *
                DriftBound.xiSum X E (n + 2) N u ω + ((n : ℝ) + 2) * Rbig))
            + (2 * cTwo52) ^ (n + 1) * (B.L N : ℝ) ^ (n + 1) * δ) := by
          have hc0 : 0 ≤ 24 * Real.exp 1 * cTwo52 := by
            have := cTwo52_pos
            positivity
          gcongr
      _ ≤ (((1 + (24 * Real.exp 1 * cTwo52) ^ (n + 1)) *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 + ((n : ℝ) + 2))
          + (2 * cTwo52) ^ (n + 1)) * Rbig ^ (2 * n + 6) * δ) := herrorBig
      _ ≤ (N : ℝ) ^ (-D) := by simpa [Rbig, δ] using hnumPoly
  dsimp [R, δ] at hmain herror' hpt
  linarith

end RBM.Gauss
