/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma41Glue
import RBM1D.Hierarchy.StepGlue

/-!
# `RBM.StepGlue.Eq45Flow` for the Gaussian model — (4.5) along the flow (T121)

`RBM.StepGlue.Eq45Flow` (T115) is the last random-layer input of `RBM.StepGlue.flow_hs1`, i.e.
of Step 4's base case `Ξ^{(L-K)}_{u,1} ≺ 1`.  It asks for Lemma 4.1 (4.5) (p. 48)
**uniformly in `u ∈ [s_N, t_N]`**, as a bound transfer:

```
‖L_{u,(+,-),(a,b)}‖ ≺ Φ_u   (uniformly in (u,a,b))
  ⟹  |L_{u,(σ),(a)} - K_{u,(σ),(a)}| ≺ Φ_u   (uniformly in (u,σ,a)).
```

## Step 0: this is T108's case, not T116's — **no time net**

Both sides of the transfer are dominations that are **already uniform in the time**: `u` sits
inside the index set of `≺` on the hypothesis and on the conclusion alike.  This is exactly the
situation of `RBM.Step1.Lemma41Flow` (T108, `RBM1D/Gauss/Lemma41FlowGauss.lean`), and for the
same reason no `N^{-C}` net and no continuity in `u` are needed: every step below is a statement
about a single `(N, ω)` with an existential over the index set, hence insensitive to what the
index set is.

It is *not* T116's situation (`RBM.Gauss.NetLift`, `RBM1D/Gauss/Step1Hyp.lean`).  There the
hypothesis controlled **one time per `N`** while the conclusion needed the union over all
`u ∈ [s_N, t_N]` inside the probability (`RBM.badSet`), which is a genuinely uncountable union
and does need a net.  Here nothing of the sort happens.  The two further obstacles T116 found —
the discontinuous indicator `1(‖G_u‖_max ≤ 2)` and the slow variation of the control — are also
absent: `RBM.StepGlue.Eq45Flow` carries **no indicator at all**, and the control `Φ` is never
compared at two different times.

The uniformity in `u` is instead imported once, from the time-indexed forms of the three inputs
of (4.5) — `RBM.Gauss.IBPFlow`, `RBM.Gauss.FlucRowFlow`, `RBM.Gauss.FlucBlkFlow` — exactly as
T108 imports `RBM.Gauss.EntryBoundFlow` and `RBM.Gauss.DiagBoundFlow`.  These are the three
hypotheses `hIBP`, `hFArow`, `hFAblk` of `RBM.avg_bound_stochDom` with `TimeIcc s t N` prefixed
to each index set and the spectral parameter `z = z_u` following the index.

Consequently nothing here uses `‖X‖ ≺ 1` (T109), the deterministic modulus
`‖H_u - H_{u'}‖ = |√u - √u'| ‖X‖` (T69), the resolvent modulus of T106, or the high-probability
Hölder nets of T101 (`RBM1D/Gauss/DominationHolder.lean`).  They would be needed only to
*discharge* the three inputs from their fixed-time versions, which is a separate question and is
not attempted here.

## Why `RBM.avg_bound_stochDom` is not applied directly

`RBM.avg_bound_stochDom` fixes one real time `t` in `H` and in `z_t`, so it cannot receive a
time-dependent index.  Its proof, however, is `RBM.StochDom.of_det` on the deterministic lemma
`RBM.norm_trace_green_sub_mul_Eblk_le`, which *is* pointwise in `(N, ω, u)`.
`RBM.Gauss.stochDom_lkErr_one_Lmax` redoes that one `of_det` step with the enlarged index set;
no signature in `RBM1D/Green/EntryBound.lean` is touched.

## Main definitions

* `RBM.Gauss.IBPFlow`, `RBM.Gauss.FlucRowFlow`, `RBM.Gauss.FlucBlkFlow` — the three inputs of
  (4.5) with the time in the index set.

## Main results

* `RBM.Gauss.lkErr_one_eq_norm_trace` — the `1`-loop `L - K` **is** the block average
  `⟨(G_u - m) E_a⟩`, for **both** charges `σ` (for `σ = -` the two differ by a complex
  conjugation, which the norm does not see).  Deterministic, no hypotheses.
* `RBM.Gauss.stochDom_Lmax_timeIcc` — `L^max_u ≺ Φ_u` from the `(+,-)` two-loop hypothesis of
  `RBM.StepGlue.Eq45Flow`; the maximum over block pairs is attained.
* `RBM.Gauss.stochDom_lkErr_one_Lmax` — **(4.5) uniformly in `u`**, with control `L^max_u`.
* `RBM.Gauss.eq45Flow_of_inputs` — `RBM.StepGlue.Eq45Flow X E s t` for an arbitrary
  `X : RBM.Sample B` (nothing Gaussian is used by the transfer).
* `RBM.Gauss.eq45Flow_gauss` — the same for `RBM.Gauss.sample d`.

Compile-checked: `RBM.Gauss.eq45Flow_gauss` fills the `h45` slot of `RBM.StepGlue.flow_hs1`
with no coercion, no `convert` and no `RBM.StochDom.precomp_param`, producing
`Ξ^{(L-K)}_{u,1} ≺ 1` in the shape Step 4 consumes.
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset

section General

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- The `1`-loop `L - K` is the block average `⟨(G_u - m) E_a⟩`, for **both** charges. -/
theorem lkErr_one_eq_norm_trace (X : Sample B) {N : ℕ} {u : ℝ} {ω : Ω}
    (v : LoopData (B.L N) 1) :
    X.lkErr E N u ω v.idx
      = ‖Matrix.trace ((green (X.H N u ω) (zt E u)
          - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0))‖ := by
  set H := X.H N u ω with hHdef
  set z := zt E u with hzdef
  have hidx : v.idx = (⟨[v.1 0], [v.2 0]⟩ : LoopIdx (ZMod (B.L N))) := by simp [LoopData.idx]
  have hLK : X.Lval E N u ω v.idx - B.Kval E N u v.idx
      = Matrix.trace ((Gsig H z (v.1 0) - mSigma E (v.1 0) •
          (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0)) := by
    rw [hidx, Sample.Lval, Band.Kval, Kgen_one, gloop, gloopProd_cons, gloopProd_nil,
      Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, trace_Eblk, mul_one]
  rw [Sample.lkErr, hLK, trace_sub_mul_Eblk, trace_sub_mul_Eblk]
  cases hv : v.1 0 with
  | true => simp only [Gsig_true, mSigma_true]
  | false =>
    rw [mSigma_false]
    have hG : Gsig H z false = Matrix.conjTranspose (Gsig H z true) :=
      (Gsig_conjTranspose (X.hermitian N u ω) z true).symm
    have hconj : ∀ k : B.Idx N, Gsig H z false k k = (starRingEnd ℂ) (green H z k k) := by
      intro k
      rw [hG, Matrix.conjTranspose_apply, Gsig_true, Complex.star_def]
    have hsum : ∑ k, (blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
          (Gsig H z false k k - (starRingEnd ℂ) (mE E))
        = (starRingEnd ℂ) (∑ k, (blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
          (green H z k k - mE E)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, Complex.conj_ofReal, map_sub, hconj k]
    rw [hsum, Complex.norm_conj]

/-- **`L^max_u ≺ Φ_u` from the `(+,-)` two-loop hypothesis of `RBM.StepGlue.Eq45Flow`.**
The maximum over the (finitely many) block pairs is attained, and the time rides along in the
index set, so no time net and no continuity in `u` are involved. -/
theorem stochDom_Lmax_timeIcc {V : ℕ → Type*} (X : Sample B) {Φ : ∀ N, TimeIcc s t N → ℝ}
    (hΦ : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => Φ N p.1)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × V N) ω => Lmax (X.H N p.1 ω) (zt E p.1))
      (fun N p _ => Φ N p.1) := by
  refine StochDom.of_subset_union hΦ hΦ fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  refine Set.mem_union_left _ ?_
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty)
    (fun q : ZMod (B.L N) × ZMod (B.L N) => Lre (X.H N p.1 ω) (zt E p.1) q.1 q.2)
  have hval : ‖X.Lval E N p.1 ω (pmLoop q.1 q.2)‖
      = Lre (X.H N p.1 ω) (zt E p.1) q.1 q.2 :=
    norm_gloop_pm_eq_Lre (X.hermitian N p.1 ω) q.1 q.2
  refine ⟨(p.1, q), ?_⟩
  show (N : ℝ) ^ τ * Φ N p.1 < ‖X.Lval E N p.1 ω (pmLoop q.1 q.2)‖
  rw [hval]
  have hp' : (N : ℝ) ^ τ * Φ N p.1 < Lmax (X.H N p.1 ω) (zt E p.1) := hp
  unfold Lmax at hp'
  rwa [hq] at hp'

/-! ### The three inputs of (4.5), with the time in the index set -/

/-- **The Gaussian integration-by-parts display of p. 50, along the flow.**  `x N u ω i` stands
for `E_i(G_u(ii) - m)`. -/
def IBPFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ)
    (x : ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ) : Prop :=
  StochDom B.P
    (fun N (p : TimeIcc s t N × B.Idx N) ω =>
      ‖x N p.1 ω p.2 - ((p.1 : ℝ) : ℂ) * mE E ^ 2 *
        ∑ k, (Sblk (B.L N) (B.W N) p.2 k : ℂ)
          * (green (X.H N p.1 ω) (zt E p.1) k k - mE E)‖)
    (fun N p ω => Lmax (X.H N p.1 ω) (zt E p.1))

/-- **The fluctuation averaging (4.12) for `t_k = S_{ik}`, along the flow.** -/
def FlucRowFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ)
    (x : ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ) : Prop :=
  StochDom B.P
    (fun N (p : TimeIcc s t N × B.Idx N) ω =>
      ‖∑ k, (Sblk (B.L N) (B.W N) p.2 k : ℂ)
        * ((green (X.H N p.1 ω) (zt E p.1) k k - mE E) - x N p.1 ω k)‖)
    (fun N p ω => Lmax (X.H N p.1 ω) (zt E p.1))

/-- **The fluctuation averaging (4.12) for `t_k = W⁻¹ 1(k ∈ I_a)`, along the flow.** -/
def FlucBlkFlow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ)
    (x : ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ) : Prop :=
  StochDom B.P
    (fun N (p : TimeIcc s t N × ZMod (B.L N)) ω =>
      ‖∑ k, (blkCoef (B.L N) (B.W N) p.2 k : ℂ)
        * ((green (X.H N p.1 ω) (zt E p.1) k k - mE E) - x N p.1 ω k)‖)
    (fun N p ω => Lmax (X.H N p.1 ω) (zt E p.1))

/-! ### (4.5) along the flow -/

/-- **Lemma 4.1, (4.5), uniformly in `u ∈ [s,t]`**: `|L_{u,(σ),(a)} - K_{u,(σ),(a)}| ≺ L^max_u`.
This is `RBM.avg_bound_stochDom` with `TimeIcc s t N` prefixed to every index set; the proof is
the same `RBM.StochDom.of_det` on the same deterministic lemma
`RBM.norm_trace_green_sub_mul_Eblk_le`, which is pointwise in `(N, ω, u)`. -/
theorem stochDom_lkErr_one_Lmax (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {x : ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ}
    (hIBP : IBPFlow X E s t x) (hFArow : FlucRowFlow X E s t x)
    (hFAblk : FlucBlkFlow X E s t x) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 1) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p ω => Lmax (X.H N p.1 ω) (zt E p.1)) := by
  have hK0 : 0 ≤ Kstab κ := Kstab_nonneg
  refine StochDom.of_det ((hIBP.sumElim hFArow).sumElim hFAblk)
    (fun N p ω => Lmax_nonneg (X.hermitian N p.1 ω)) (δ := fun _ => 0) (fun _ => le_rfl) one_pos
    (Eventually.of_forall fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _) one_pos
    (1 + 2 * Kstab κ) 1 ?_
  intro N ω Φ hΦ1 _ _ hAB p
  obtain ⟨u, v⟩ := p
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : ((u : ℝ)) < 1 := lt_of_le_of_lt u.2.2 (ht1 N)
  have hL0 : (0 : ℝ) ≤ Lmax (X.H N u ω) (zt E u) := Lmax_nonneg (X.hermitian N u ω)
  have h := norm_trace_green_sub_mul_Eblk_le (B.three_le_L N) hκ0 hκ1 hE hu0 hu1
    (green (X.H N u ω) (zt E u)) (x N u ω)
    (A := Φ * Lmax (X.H N u ω) (zt E u)) (B := Φ * Lmax (X.H N u ω) (zt E u))
    (B' := Φ * Lmax (X.H N u ω) (zt E u))
    (fun i => hAB (Sum.inl (Sum.inl (u, i)))) (fun i => hAB (Sum.inl (Sum.inr (u, i))))
    (v.2 0) (hAB (Sum.inr (u, v.2 0)))
  rw [lkErr_one_eq_norm_trace X v]
  calc ‖Matrix.trace ((green (X.H N u ω) (zt E u)
        - mE E • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0))‖
      ≤ Φ * Lmax (X.H N u ω) (zt E u)
        + Kstab κ * (Φ * Lmax (X.H N u ω) (zt E u) + Φ * Lmax (X.H N u ω) (zt E u)) := h
    _ = (1 + 2 * Kstab κ) * Φ ^ 1 * Lmax (X.H N u ω) (zt E u) := by ring

/-! ### `RBM.StepGlue.Eq45Flow` -/

/-- **`RBM.StepGlue.Eq45Flow`**: (4.5) along the flow, in bound-transfer form.

The transfer is between two dominations that are **already uniform in `u`** — the hypothesis
`‖L_{u,(+,-),(a,b)}‖ ≺ Φ_u` and the conclusion `|L_{u,(σ),(a)} - K_{u,(σ),(a)}| ≺ Φ_u` both
carry the time inside the index set.  Hence, exactly as for `RBM.Step1.Lemma41Flow` (T108),
**no `N^{-C}` time net and no continuity in `u` are used**: the `u`-uniformity is imported once,
through the time-indexed forms `RBM.Gauss.IBPFlow`, `RBM.Gauss.FlucRowFlow`,
`RBM.Gauss.FlucBlkFlow` of the three inputs of (4.5). -/
theorem eq45Flow_of_inputs (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {x : ∀ N, TimeIcc s t N → Ω → B.Idx N → ℂ}
    (hIBP : IBPFlow X E s t x) (hFArow : FlucRowFlow X E s t x)
    (hFAblk : FlucBlkFlow X E s t x) :
    StepGlue.Eq45Flow X E s t := by
  intro Φ _ hΦ
  exact (stochDom_lkErr_one_Lmax X hκ0 hκ1 hE hs0 ht1 hIBP hFArow hFAblk).trans
    (stochDom_Lmax_timeIcc (V := fun N => LoopData (B.L N) 1) X hΦ)

end General

/-! ### The Gaussian model -/

section Gaussian

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

/-- **`RBM.StepGlue.Eq45Flow` for the Gaussian model.** -/
theorem eq45Flow_gauss {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {x : ∀ N, TimeIcc s t N → Ω d → d.Idx N → ℂ}
    (hIBP : IBPFlow (sample d) E s t x) (hFArow : FlucRowFlow (sample d) E s t x)
    (hFAblk : FlucBlkFlow (sample d) E s t x) :
    StepGlue.Eq45Flow (sample d) E s t :=
  eq45Flow_of_inputs (sample d) hκ0 hκ1 hE hs0 ht1 hIBP hFArow hFAblk

end Gaussian

end RBM.Gauss
