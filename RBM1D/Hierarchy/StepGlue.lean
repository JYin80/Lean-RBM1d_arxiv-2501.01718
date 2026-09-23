/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBound
import RBM1D.Hierarchy.Step2
import RBM1D.Hierarchy.Step2Moment
import RBM1D.Hierarchy.Step3FlowSharp
import RBM1D.Hierarchy.Step45

/-!
# The deterministic glue between Steps 1–2 and Steps 3–5 (T115)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, p. 70 ("with the bound (2.73) for `L`
and (3.46) for `K`, `S(m,l,s,u,t)` holds for `l = 0` and any `m ≥ 1`.  By (2.76),
`S(m,l,s,u,t)` holds for any `l` and `m ≤ 2`") and p. 72 ("by (2.76) and (4.5) for
`(L-K)`-loops of length 1 and 2 and the condition (2.72), we have `Ξ^{(L-K)}_{t,1} ≺ 1`,
`Ξ^{(L-K)}_{t,2} ≺ (W ℓ_t η_t)^{1/4}`").

These four sentences are exactly the hypotheses `h0`, `h12` of `RBM.Step3.flow_sharpLoop` and
`h0`, `h12`, `h1`, `h2` of `RBM.Step45.flow_steps45`, which had no producer anywhere in the
tree.  Everything here is deterministic bookkeeping on top of the fields of `RBM.Steps`; no
signature of `Flow/Hypotheses.lean` or of the six step files is touched.

## Main results

* `RBM.StepGlue.stochDom_flowXiLK` — the bridge: a loopwise bound `|L - K| ≺ f_u` gives
  `Ξ^{(L-K)}_{u,m} ≺ f_u (W ℓ_u η_u)^m`.
* `RBM.StepGlue.flow_S_zero` — **`h0`**: `S(m,0)` for every `m ≥ 1`, from (2.73)
  (`RBM.Steps.apriori`) and (2.59) (`RBM.Band.norm_Kval_le`).  **Unconditional.**
* `RBM.StepGlue.flow_S_one` — `S(1,l)` for every `l`, from (2.75) (`RBM.Steps.localLaw`).
  **Unconditional.**
* `RBM.StepGlue.flow_S_two`, `RBM.StepGlue.flow_S_le_two` — **`h12`**: `S(m,l)` for `m ≤ 2`,
  from `AprioriDecayAll` and (2.72) with a gain.
* `RBM.StepGlue.flow_hs2` — **`hs2`**: `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}`, from
  `AprioriDecayAll` and (2.72) with a gain.
* `RBM.StepGlue.flow_hs1` — **`hs1`**: `Ξ^{(L-K)}_{u,1} ≺ 1`, from `Eq45Flow` and (2.77) at
  `n = 2`.
* `RBM.StepGlue.flow_sharpLoop_glue`, `RBM.StepGlue.flow_steps45_glue` — (2.77), and (2.78) with
  (2.79), with `h0`/`h12`/`h1`/`h2` discharged, i.e. in exactly the shapes of the fields
  `RBM.Steps.sharpLoop`, `RBM.Steps.sharpLmK`, `RBM.Steps.sharpDecay`.

## The two remaining inputs, and why

* `RBM.StepGlue.AprioriDecayAll` — **(2.76) for every charge `σ ∈ {+,-}²`**.

  This is a real gap, not a formalization artefact.  `RBM.Steps.aprioriDecay` is (2.76)
  verbatim, and the paper states (2.76) **only for `σ = (+,-)`** (p. 24; §5.3 opens with "In
  this section, we focus on the `(+,-)` `2`-`G`-loop, i.e. `σ = (+,-)`.  The subscript `σ` will
  be dropped in this subsection").  But `Ξ^{(L-K)}_{u,2}` is defined in (5.76) as a maximum over
  **all** `σ ∈ {+,-}²`, and `S(2,l)` for large `l` needs `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}`,
  which is a factor `W ℓ_u η_u` better than what (2.73) or (2.75) give for any charge.  Of the
  four charges, `(+,-)` is covered by (2.76) (`RBM.StepGlue.aprioriDecay_pm`); `(-,+)` reduces
  to it by trace cyclicity (`RBM.gloop_rotate`), and `(-,-)` to `(+,+)` by conjugation; the
  **constant charges `(+,+)`, `(-,-)` have no source in Steps 1–2**.  What is missing is a
  `(+,+)` analogue of (2.76), i.e. `|L_{u,(+,+),a} - K_{u,(+,+),a}| ≺ (η_s/η_u)^4
  (W ℓ_u η_u)^{-2}` for `u ∈ [s,t]`.  See `docs/paper-deltas.md`.

  **Correction (T122).**  An earlier version of this paragraph offered as a corroborating point
  that the proof of Lemma 5.14 (p. 68) restricts (5.96), hence the whole Step-3 machinery, to
  *non-constant* `σ`.  That was a **misreading**: the "non-constant" condition occurs only
  inside the **alternating** branch of (5.96).  Constant charges are handled by Lemma 5.11
  (p. 65), which satisfies (5.82) and applies at `n = 2` as well — see
  `RBM1D/Hierarchy/Step2PP.lean`, where `RBM.Step2PP.flow_S_le_two_of` and
  `RBM.Step2PP.flow_hs2_of` replace the uses of `AprioriDecayAll` below.

* `RBM.StepGlue.Eq45Flow` — **(4.5) along the flow**, in bound-transfer form.  (4.5) itself is
  proved in `RBM1D/Green/EntryBound.lean` (`RBM.avg_bound_stochDom`) at a *fixed* spectral
  parameter; the flow needs it uniformly in `u ∈ [s,t]`, which is why it is a hypothesis here,
  exactly as `RBM.Step1.Lemma41Flow` is for (4.2)/(4.3).  This is a formalization artefact (the
  `N^{-C}`-net continuity argument of p. 51), not a gap in the paper.

## Deviations from the paper

* (2.76) is used with its decay profile dropped (`decayProf ≤ 2`), which is all Step 3 needs.
* `hregS`, "(2.72) with a gain" (`RBM.Step2.cond272_of_strict`), is the single regularity
  hypothesis: it implies (2.72) and, in `RBM.StepGlue.eventually_R4_le_rpow_quarter`, the
  sharper `(η_s/η_u)^4 ≤ (W ℓ_u η_u)^{1/4}` that Step 4's base case needs (the paper says only
  "the condition (2.72)").
-/

namespace RBM

open MeasureTheory Filter

namespace StepGlue

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **From a loopwise bound to `Ξ^{(L-K)}`.**  If `|L_{u,σ,a} - K_{u,σ,a}| ≺ f_u` uniformly in
`u ∈ [s,t]` and in the loop `(σ, a)` of length `m`, then `Ξ^{(L-K)}_{u,m} ≺ f_u (W ℓ_u η_u)^m`. -/
theorem stochDom_flowXiLK (X : Sample B) {m : ℕ} {f : ∀ N, TimeIcc s t N → ℝ}
    (hA : ∀ N (u : TimeIcc s t N), 0 ≤ B.scale E N u)
    (h : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => f N p.1)) :
    StochDom B.P (Step3.flowXiLK X E s t m)
      (fun N u _ => f N u * B.scale E N u ^ m) := by
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  by_cases h' : ∃ p : TimeIcc s t N × LoopData (B.L N) m,
      (N : ℝ) ^ τ * f N p.1 < X.lkErr E N p.1 ω p.2.idx
  · exact Or.inl h'
  · exfalso
    have hall : ∀ v : LoopData (B.L N) m, X.lkErr E N u ω v.idx ≤ (N : ℝ) ^ τ * f N u :=
      fun v => not_lt.1 fun hc => h' ⟨(u, v), hc⟩
    have hmax : X.lkMax E N u ω m ≤ (N : ℝ) ^ τ * f N u := ciSup_le hall
    have hApow : (0 : ℝ) ≤ B.scale E N u ^ m := pow_nonneg (hA N u) _
    have : Step3.flowXiLK X E s t m N u ω ≤ (N : ℝ) ^ τ * (f N u * B.scale E N u ^ m) := by
      show X.lkMax E N u ω m * B.scale E N u ^ m ≤ _
      calc X.lkMax E N u ω m * B.scale E N u ^ m
          ≤ ((N : ℝ) ^ τ * f N u) * B.scale E N u ^ m :=
            mul_le_mul_of_nonneg_right hmax hApow
        _ = (N : ℝ) ^ τ * (f N u * B.scale E N u ^ m) := by ring
    exact absurd hu (not_lt.2 this)

/-! ### The `1`-loop is controlled by `‖G_u - m‖_max` -/

/-- **The `1`-loop `L - K` is bounded by `‖G_u - m‖_max`.**  For a loop of length `1`,
`L_{u,(σ),(a)} - K_{u,(σ),(a)} = ⟨(G_u(σ) - m(σ)) E_a⟩` is an average of `W` diagonal entries
of `G_u(σ) - m(σ)`; for `σ = -` these are the complex conjugates of the entries of `G_u - m`
(`RBM.Gsig_conjTranspose`, `RBM.mSigma_false`), so **both charges** are covered. -/
theorem norm_lkErr_one_le (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}
    (v : LoopData (B.L N) 1) {c : ℝ}
    (h : ∀ ij : B.Idx N × B.Idx N, X.llErr E N u ω ij ≤ c) :
    X.lkErr E N u ω v.idx ≤ c := by
  set H := X.H N u ω with hHdef
  set z := zt E u with hzdef
  have hidx : v.idx = (⟨[v.1 0], [v.2 0]⟩ : LoopIdx (ZMod (B.L N))) := by simp [LoopData.idx]
  -- the diagonal entries of `G(σ) - m(σ)` have the norms of those of `G - m`
  have hdiag : ∀ p : B.Idx N, ‖(Gsig H z (v.1 0) - mSigma E (v.1 0) •
      (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) p p‖ ≤ c := by
    intro p
    have hbase := h (p, p)
    simp only [Sample.llErr, Sample.G, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, ← hHdef, ← hzdef] at hbase
    cases hv : v.1 0 with
    | true =>
      simpa [Gsig_true, mSigma_true, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
        using hbase
    | false =>
      have hG : Gsig H z false = Matrix.conjTranspose (Gsig H z true) :=
        (Gsig_conjTranspose (X.hermitian N u ω) z true).symm
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hG,
        mSigma_false, Matrix.conjTranspose_apply, Gsig_true]
      rw [Complex.star_def, ← map_sub (starRingEnd ℂ), Complex.norm_conj]
      exact hbase
  -- the average
  have hLK : X.Lval E N u ω v.idx - B.Kval E N u v.idx
      = Matrix.trace ((Gsig H z (v.1 0) - mSigma E (v.1 0) •
          (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) (v.2 0)) := by
    rw [hidx, Sample.Lval, Band.Kval, Kgen_one, gloop, gloopProd_cons, gloopProd_nil,
      Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, trace_Eblk, mul_one]
  rw [Sample.lkErr, hLK, trace_sub_mul_Eblk]
  calc ‖∑ k, (blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
        (Gsig H z (v.1 0) k k - mSigma E (v.1 0))‖
      ≤ ∑ k, ‖(blkCoef (B.L N) (B.W N) (v.2 0) k : ℂ) *
        (Gsig H z (v.1 0) k k - mSigma E (v.1 0))‖ := norm_sum_le _ _
    _ ≤ ∑ k, |blkCoef (B.L N) (B.W N) (v.2 0) k| * c := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have := hdiag k
        simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq] using this
    _ = c := by rw [← Finset.sum_mul, sum_abs_blkCoef, one_mul]

/-! ### Scale facts from (2.72) with a gain -/

/-- `(W ℓ_s η_s)^{1/2} ≤ Ψ(n,k)` for every `n`, `k`: the first summand of (5.108). -/
theorem rpow_half_le_psi {As R Au : ℝ} (hAs : 0 ≤ As) (hR : 0 ≤ R) (hAu : 0 ≤ Au) (n k : ℕ) :
    As ^ ((1 : ℝ) / 2) ≤ Step3.psi As R Au n k := by
  unfold Step3.psi Step3.Psi
  split_ifs
  · have : 0 ≤ R ^ (n - 1) * Au := by positivity
    linarith
  · have : 0 ≤ R ^ (n - 1) * As ^ (1 - (k : ℝ) / 4) := by positivity
    linarith

/-- **(2.72) with a gain gives `(η_s/η_u)⁴ ≤ (W ℓ_u η_u)^{1/4}`** for `u ∈ [s,t]`.
Sharper than `RBM.Step2.eventually_R4_le_scale` (which gives `(η_s/η_u)⁴ ≤ W ℓ_u η_u`) and
exactly what Step 4's base case `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` needs: `(η_s/η_u)^{16} ≤
(η_s/η_t)^{30} ≤ W ℓ_t η_t ≤ W ℓ_u η_u`, since `η_s/η_t ≥ 1` and `W ℓ η` is non-increasing. -/
theorem eventually_R4_le_rpow_quarter (hE : |E| < 2) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (s N) / etaT E u) ^ 4 ≤ B.scale E N u ^ ((1 : ℝ) / 4) := by
  filter_upwards [hregS, eventually_ge_atTop 1] with N hN hN1 u
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hcN : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hN1' hc0.le
  -- the ratios
  have hrt : etaT E (s N) / etaT E (t N) = (1 - s N) / (1 - t N) := Step2.etaT_ratio hE _ _
  have hru : etaT E (s N) / etaT E u = (1 - s N) / (1 - (u : ℝ)) := Step2.etaT_ratio hE _ _
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 0 < 1 - s N := by linarith [(hst N).trans (ht1 N).le]
  set r : ℝ := (1 - s N) / (1 - t N) with hrdef
  set ρ : ℝ := (1 - s N) / (1 - (u : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := le_of_lt (div_pos h1s h1u)
  have hρr : ρ ≤ r := by
    refine div_le_div_of_nonneg_left h1s.le h1t ?_
    linarith [u.2.2]
  have hr1 : (1 : ℝ) ≤ r := (one_le_div h1t).2 (by linarith [u.2.1, (hst N) ])
  -- `(η_s/η_t)^{30} ≤ W ℓ_t η_t ≤ W ℓ_u η_u`
  have hAt : r ^ 30 ≤ B.scale E N (t N) := by
    rw [hrt] at hN
    nlinarith [pow_pos (lt_of_lt_of_le one_pos hr1) 30]
  have hAv : B.scale E N (t N) ≤ B.scale E N u := flowScale_antitoneOn hW0 (B.L N) E
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  -- `(ρ^4)^4 = ρ^{16} ≤ r^{30} ≤ W ℓ_u η_u`
  have h16 : (ρ ^ 4) ^ 4 ≤ B.scale E N u := by
    have : ρ ^ 16 ≤ r ^ 16 := pow_le_pow_left₀ hρ0 hρr 16
    have hr16 : r ^ 16 ≤ r ^ 30 := pow_le_pow_right₀ hr1 (by norm_num)
    calc (ρ ^ 4) ^ 4 = ρ ^ 16 := by ring
      _ ≤ r ^ 16 := this
      _ ≤ r ^ 30 := hr16
      _ ≤ B.scale E N (t N) := hAt
      _ ≤ B.scale E N u := hAv
  have hkey := Real.rpow_le_rpow (by positivity) h16 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [hru]
  have he : ((ρ ^ 4) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = ρ ^ 4 := by
    rw [← Real.rpow_natCast (ρ ^ 4) 4, ← Real.rpow_mul (by positivity)]
    norm_num
  rwa [he] at hkey

/-! ### `S(m,0)` from (2.73) and (2.59) -/

/-- **`S(m,0)` for every `m ≥ 1`**, i.e. the hypothesis `h0` of `RBM.Step3.flow_sharpLoop`:
`Ξ^{(L-K)}_{u,m} ≺ (W ℓ_s η_s)^{1/2} + (ℓ_t/ℓ_s)^{m-1} (W ℓ_u η_u)`, uniformly in `u ∈ [s,t]`.

This is the paper's "with the bound (2.73) for `L` and (3.46) for `K`, `S(m,l,s,u,t)` holds for
`l = 0` and any `m ≥ 1`" (p. 70).  (2.73) is `RBM.Steps.apriori`; (3.46)/(2.59) is the proved
`RBM.Band.norm_Kval_le` (via `RBM.Step3.exists_norm_Kval_le`).  Note that (2.73) is a bound on
`max_{σ,a}`, so **all** charges `σ ∈ {+,-}^m` are covered. -/
theorem flow_S_zero' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hapriori : AprioriFlow X E s t) (m : ℕ) (hm : 1 ≤ m) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) m 0 := by
  have hE : |E| < 2 := by linarith
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hc
  obtain ⟨C, hC0, hC⟩ := Step3.exists_norm_Kval_le (B := B) hκ0 hκ1 hEκ hs0 ht1 hm
  set R : ℕ → ℝ := Step3.flowR B s t with hRdef
  -- (2.73): the a priori loop bound
  have hL := hapriori m hm
  -- (2.59): the deterministic bound on `K`
  have hKle : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) (_ : Ω) => ‖B.Kval E N p.1 p.2.idx‖)
      (fun N p _ => C * (B.scale E N p.1)⁻¹ ^ (m - 1)) :=
    StochDom.of_unifDetDom (UnifDetDom.of_eventually_le_const_mul
      (fun N p => mul_nonneg hC0 (pow_nonneg (inv_nonneg.2 (hA N p.1).le) _)) 1
      (Eventually.of_forall fun N p => by simpa using hC N p.1 p.2))
  -- `|L - K| ≤ |L| + |K|`
  have hsum : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.ell N p.1 / B.ell N (s N)) ^ (m - 1) * (B.scale E N p.1)⁻¹ ^ (m - 1)
        + C * (B.scale E N p.1)⁻¹ ^ (m - 1)) := by
    refine StochDom.of_le_left (fun N p ω => ?_) (hL.add hKle)
    exact norm_sub_le _ _
  -- collapse to `(1 + C) R^{m-1} (W ℓ_u η_u)^{-(m-1)}`
  have hcollapse : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => R N ^ (m - 1) * (B.scale E N p.1)⁻¹ ^ (m - 1)) := by
    refine Step3.stochDom_mono (fun N p _ => mul_nonneg (pow_nonneg (sc.R_nonneg N) _)
      (pow_nonneg (inv_nonneg.2 (hA N p.1).le) _)) (1 + C) ?_ hsum
    filter_upwards [sc.one_le_R] with N hR p _
    have hℓs : 0 < B.ell N (s N) :=
      Step3.ellHat_pos_of_lt_one (B.one_le_L N) ((hst N).trans_lt (ht1 N))
    have hℓu : B.ell N p.1 ≤ B.ell N (t N) := Step3.ellHat_mono p.1.2.2 (ht1 N)
    have hratio : B.ell N p.1 / B.ell N (s N) ≤ R N :=
      div_le_div_of_nonneg_right hℓu hℓs.le
    have hr0 : 0 ≤ B.ell N p.1 / B.ell N (s N) := by
      have := (Step3.ellHat_pos_of_lt_one (L := B.L N) (B.one_le_L N)
        (p.1.2.2.trans_lt (ht1 N))).le
      positivity
    have hpow : (B.ell N p.1 / B.ell N (s N)) ^ (m - 1) ≤ R N ^ (m - 1) :=
      pow_le_pow_left₀ hr0 hratio _
    have hR1 : (1 : ℝ) ≤ R N ^ (m - 1) := one_le_pow₀ hR
    have hinv : (0 : ℝ) ≤ (B.scale E N p.1)⁻¹ ^ (m - 1) :=
      pow_nonneg (inv_nonneg.2 (hA N p.1).le) _
    have h1 := mul_le_mul_of_nonneg_right hpow hinv
    have h2 : C * (B.scale E N p.1)⁻¹ ^ (m - 1)
        ≤ C * (R N ^ (m - 1) * (B.scale E N p.1)⁻¹ ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hinv hR1) hC0
    nlinarith
  -- pass to `Ξ^{(L-K)}`
  have hXi := stochDom_flowXiLK X (f := fun N (u : TimeIcc s t N) =>
    R N ^ (m - 1) * (B.scale E N u)⁻¹ ^ (m - 1)) (fun N u => (hA N u).le) hcollapse
  -- and compare with `Ψ(m,0)`
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le) 1 ?_ hXi
  filter_upwards with N u _
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hAu : (0 : ℝ) < B.scale E N u := hA N u
  have hkey : R N ^ (j + 1 - 1) * (B.scale E N u)⁻¹ ^ (j + 1 - 1) * B.scale E N u ^ (j + 1)
      = R N ^ j * B.scale E N u := by
    simp only [Nat.add_sub_cancel]
    rw [inv_pow, pow_succ, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hAu.ne')]
  rw [hkey, one_mul, Step3.psi_zero]
  have : (0 : ℝ) ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (sc.As_pos N).le _
  have hAs : Step3.flowAs B E s N ^ ((1 : ℝ) / 2) +
      R N ^ (j + 1 - 1) * Step3.flowA B E s t N u
      = Step3.flowAs B E s N ^ ((1 : ℝ) / 2) + R N ^ j * B.scale E N u := by
    simp [Step3.flowA]
  rw [hAs]
  linarith


/-! ### `S(1,l)` from (2.75) -/

/-- **The `1`-loop `L - K` is `≺ (W ℓ_u η_u)^{-1/2}`**, uniformly in `u ∈ [s,t]` and in the
charge, directly from (2.75) (`RBM.Steps.localLaw`). -/
theorem flow_lkErr_one_le' (X : Sample B) (hll : LocalLawFlow X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 1) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) := by
  refine StochDom.of_subset_union hll hll
    fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  by_cases h' : ∃ q : TimeIcc s t N × (B.Idx N × B.Idx N),
      (N : ℝ) ^ τ * (B.scale E N q.1)⁻¹ ^ ((1 : ℝ) / 2) < X.llErr E N q.1 ω q.2
  · exact Or.inl h'
  · exfalso
    have hall : ∀ ij : B.Idx N × B.Idx N,
        X.llErr E N p.1 ω ij ≤ (N : ℝ) ^ τ * (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2) :=
      fun ij => not_lt.1 fun hcon => h' ⟨(p.1, ij), hcon⟩
    exact absurd hp (not_lt.2 (norm_lkErr_one_le X p.2 hall))

/-- **`S(1,l)` for every `l`**: `Ξ^{(L-K)}_{u,1} ≺ (W ℓ_u η_u)^{1/2} ≤ (W ℓ_s η_s)^{1/2}`, from
(2.75).  This is the `m = 1` half of the paper's "by (2.76), `S(m,l)` holds for any `l` and
`m ≤ 2`" (p. 70) — for `m = 1` the local law (2.75) alone suffices. -/
theorem flow_S_one' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (hll : LocalLawFlow X E s t) (l : ℕ) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) 1 l := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hc
  have hXi := stochDom_flowXiLK X (f := fun N (u : TimeIcc s t N) =>
    (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 2)) (fun N u => (hA N u).le) (flow_lkErr_one_le' X hll)
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le) 1 ?_ hXi
  filter_upwards [sc.A_le_As] with N hle u _
  have hA0 : 0 < B.scale E N u := hA N u
  have hsq : B.scale E N u ^ ((1 : ℝ) / 2) * B.scale E N u ^ ((1 : ℝ) / 2) = B.scale E N u := by
    rw [← Real.rpow_add hA0]; norm_num
  have hval : (B.scale E N u)⁻¹ ^ ((1 : ℝ) / 2) * B.scale E N u ^ 1
      = B.scale E N u ^ ((1 : ℝ) / 2) := by
    rw [Real.inv_rpow hA0.le, pow_one,
      inv_mul_eq_iff_eq_mul₀ (Real.rpow_pos_of_pos hA0 _).ne']
    exact hsq.symm
  rw [hval, one_mul]
  refine le_trans ?_ (rpow_half_le_psi (sc.As_pos N).le (sc.R_nonneg N) (sc.A_pos N u).le 1 l)
  exact Real.rpow_le_rpow hA0.le (hle u) (by norm_num)

/-! ### The two missing random-layer inputs -/

/-- **(2.76) for every charge `σ ∈ {+,-}²`**, without the decay profile.

`RBM.Steps.aprioriDecay` is (2.76) exactly as the paper states it, i.e. **only for
`σ = (+,-)`** (§5.3 opens with "we focus on the `(+,-)` `2`-`G`-loop; the subscript `σ` will be
dropped").  Step 3 and Step 4 use it through `Ξ^{(L-K)}_{u,2}`, whose definition (5.76) is a
maximum over **all four** charges `σ ∈ {+,-}²`.  Nothing in Steps 1–2 supplies the constant
charges `σ = (+,+)`, `(-,-)` at this strength, so the statement is recorded here as a named
hypothesis rather than derived; `RBM.StepGlue.aprioriDecay_pm` shows that the `(+,-)` part of it
*is* free.

**Correction and status (T122).**  The remark, made when this definition was introduced, that
the proof of Lemma 5.14 (p. 68) excludes constant `σ` is a **misreading**: "non-constant"
occurs only inside the alternating branch of (5.96).  Constant charges are supplied by
Lemma 5.11 (p. 65) at `n = 2`, which is the route taken in `RBM1D/Hierarchy/Step2PP.lean`.
That route does **not** reproduce this statement — it gives the weaker, time-independent
`Ξ^{(L-K)}_{u,2} ≺ (W ℓ_s η_s)^{1/2}` — but it does discharge everything this statement is used
for here: see `RBM.Step2PP.flow_S_le_two_of`, `RBM.Step2PP.flow_hs2_of` and the packaged
`RBM.Step2PP.flow_sharpLoop_glue_of` / `RBM.Step2PP.flow_steps45_glue_of`. -/
def AprioriDecayAll (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  StochDom B.P
    (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => X.lkErr E N p.1 ω p.2.idx)
    (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2)

/-- **(4.5) along the flow**, in bound-transfer form: if the `(+,-)` `2`-loop is `≺ Φ_u`
uniformly in `u ∈ [s,t]`, then so is the `1`-loop `L - K`, i.e.
`max_a |⟨(G_u - m) E_a⟩| ≺ max_{a,b} L_{u,(+,-),(a,b)}` (Lemma 4.1, p. 48).

`RBM.avg_bound_stochDom` proves (4.5) at a *fixed* spectral parameter from the large-deviation
and fluctuation-averaging inputs; the flow needs it along `z = z_u`, `u ∈ [s,t]`, which is why
it is a hypothesis here (exactly as `RBM.Step1.Lemma41Flow` is for (4.2)/(4.3)). -/
def Eq45Flow (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ Φ : ∀ N, TimeIcc s t N → ℝ, (∀ N u, 0 ≤ Φ N u) →
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => Φ N p.1) →
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 1) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => Φ N p.1)

/-- **The `(+,-)` part of `AprioriDecayAll` is free**: it is (2.76) with the decay profile
`exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D} ≤ 2` dropped. -/
theorem aprioriDecay_pm' (X : Sample B) (ht1 : ∀ N, t N < 1)
    (hdecay : AprioriDecayFlow X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2) := by
  refine Step3.stochDom_mono (fun N p _ => by positivity) 2
    (Eventually.of_forall fun N p _ => ?_) (hdecay 1 one_pos)
  have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N p.1 := Step3.ellHat_pos_of_lt_one (B.one_le_L N) hu1
  have hdecay : B.decayProf N p.1 1 p.2.1 p.2.2 ≤ 2 := by
    have h1 : Real.exp (-(((zdist (B.L N) (p.2.1 - p.2.2) : ℝ) / B.ell N p.1) ^
        ((1 : ℝ) / 2))) ≤ 1 := by
      refine Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.rpow_nonneg ?_ _))
      positivity
    have h2 : (B.W N : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
    rw [Band.decayProf]
    linarith
  have hpre : (0 : ℝ) ≤ (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 := by
    positivity
  nlinarith

/-! ### `S(2,l)` and Step 4's base cases -/

/-- `Ξ^{(L-K)}_{u,2} ≺ (η_s/η_u)⁴` from (2.76) for all charges. -/
theorem flow_xiLK_two_le (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (h276 : AprioriDecayAll X E s t) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      (fun N (u : TimeIcc s t N) _ => (etaT E (s N) / etaT E u) ^ 4) := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hXi := stochDom_flowXiLK X (f := fun N (u : TimeIcc s t N) =>
    (etaT E (s N) / etaT E u) ^ 4 * (B.scale E N u)⁻¹ ^ 2) (fun N u => (hA N u).le) h276
  refine Step3.stochDom_mono (fun N u _ => by positivity) 1
    (Eventually.of_forall fun N u _ => ?_) hXi
  have hA0 : 0 < B.scale E N u := hA N u
  rw [one_mul, mul_assoc, inv_pow, inv_mul_cancel₀ (by positivity), mul_one]

/-- **Step 4's base case `hs2`**: `Ξ^{(L-K)}_{u,2} ≺ (W ℓ_u η_u)^{1/4}` (p. 72, "by (2.76) …
and the condition (2.72)"), in exactly the shape of the hypothesis `h2` of
`RBM.Step45.flow_steps45`. -/
theorem flow_hs2 (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) (h276 : AprioriDecayAll X E s t) :
    StochDom B.P (Step3.flowXiLK X E s t 2)
      fun N u _ => Step3.flowA B E s t N u ^ ((1 : ℝ) / 4) := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  refine Step3.stochDom_mono (fun N u _ => Real.rpow_nonneg (hA N u).le _) 1 ?_
    (flow_xiLK_two_le X hE hs0 ht1 h276)
  filter_upwards [eventually_R4_le_rpow_quarter hE hst ht1 hc0 hregS] with N hN u _
  rw [one_mul]
  exact hN u

/-- **`S(2,l)` for every `l`** from (2.76) for all charges and (2.72) with a gain:
`Ξ^{(L-K)}_{u,2} ≺ (η_s/η_u)⁴ ≤ (W ℓ_u η_u)^{1/4} ≤ (W ℓ_s η_s)^{1/2} ≤ Ψ(2,l)`. -/
theorem flow_S_two (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) (h276 : AprioriDecayAll X E s t) (l : ℕ) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) 2 l := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have sc := Step3.scales_flow (E := E) (s := s) (t := t) hE hs0 hst ht1 hcond
  refine Step3.stochDom_mono (fun N u _ => Step3.psi_nonneg (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le) 1 ?_ (flow_xiLK_two_le X hE hs0 ht1 h276)
  filter_upwards [eventually_R4_le_rpow_quarter hE hst ht1 hc0 hregS, sc.A_le_As,
    sc.one_le_As] with N h4 hle hAs1 u _
  rw [one_mul]
  refine le_trans (h4 u) (le_trans ?_ (rpow_half_le_psi (sc.As_pos N).le (sc.R_nonneg N)
    (sc.A_pos N u).le 2 l))
  calc B.scale E N u ^ ((1 : ℝ) / 4)
      ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (hA N u).le (hle u) (by norm_num)
    _ ≤ Step3.flowAs B E s N ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hAs1 (by norm_num)

/-- **`h12`**: `S(m,l)` for every `l` and `m ≤ 2`, in exactly the shape of the hypothesis `h12`
of `RBM.Step3.flow_sharpLoop` and `RBM.Step45.flow_steps45`. -/
theorem flow_S_le_two' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) (hll : LocalLawFlow X E s t) (h276 : AprioriDecayAll X E s t)
    (m l : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) m l := by
  interval_cases m
  · exact flow_S_one' X hE hs0 hst ht1 hcond hll l
  · exact flow_S_two X hE hs0 hst ht1 hcond hc0 hregS h276 l

/-- **Step 4's base case `hs1`**: `Ξ^{(L-K)}_{u,1} ≺ 1` (p. 72, "by (2.76) and (4.5) for
`(L-K)`-loops of length 1 and 2"), in exactly the shape of the hypothesis `h1` of
`RBM.Step45.flow_steps45`.  Inputs: (4.5) along the flow and (2.77) at `n = 2` (Step 3). -/
theorem flow_hs1 (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h45 : Eq45Flow X E s t)
    (h277 : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (2 - 1))) :
    StochDom B.P (Step3.flowXiLK X E s t 1) fun _ _ _ => 1 := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hpm : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        ‖X.Lval E N p.1 ω (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => (B.scale E N p.1)⁻¹) := by
    have h := h277.precomp_param (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      (p.1, Step45.pmData p.2.1 p.2.2))
    simpa [Step45.pmData_idx] using h
  have hone := h45 (fun N u => (B.scale E N u)⁻¹) (fun N u => (inv_pos.2 (hA N u)).le) hpm
  have hXi := stochDom_flowXiLK X (f := fun N (u : TimeIcc s t N) => (B.scale E N u)⁻¹)
    (fun N u => (hA N u).le) hone
  refine Step3.stochDom_mono (fun _ _ _ => zero_le_one) 1
    (Eventually.of_forall fun N u _ => ?_) hXi
  rw [pow_one, one_mul, inv_mul_cancel₀ (hA N u).ne']


/-! ### The packaged conclusions -/

/-- **(2.77) with `h0` and `h12` discharged**, in exactly the shape of the field
`RBM.Steps.sharpLoop`.  Remaining inputs: the fields of `RBM.Steps` produced by Steps 1–2,
`hregS` (2.72 with a gain), Lemma 5.14 (5.92) for `n ≥ 3`, and `AprioriDecayAll`. -/
theorem flow_sharpLoop_glue' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (h276 : AprioriDecayAll X E s t)
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 B E s t := Step2.cond272_of_strict hE hst ht1 hc0 hregS
  exact Step3.flow_sharpLoop X hκ0 hκ1 hEκ hs0 hst ht1 hcond h514
    (flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori)
    (flow_S_le_two' X hE hs0 hst ht1 hcond hc0 hregS hll h276) hn

/-! #### Steps 4–5 with the smoothed (5.48) (T233)

T228 replaced the sharp indicator `1(d ≤ 6ℓ*_u)` of (5.48) by a weight `w` vanishing beyond
`12ℓ*_u` (`RBM.Step45.FlowEq548W`), because read *uniformly in `u`* the indicator makes the
far-field functional jump in `u`.  `RBM.Step45.flow_steps45_W` proves (2.78)/(2.79) from the
smoothed form, with the **conclusion unchanged**.

The glue below is therefore stated on `RBM.Step45.FlowEq548W` and the unprimed
`flow_steps45_glue'` is a one-line specialization at `w = 1(d ≤ 6ℓ*_u)`, so that the proof
script exists **once**.  `RBM.Step45.flowEq548W_of_flowEq548` supplies the hypothesis and
`eventually_indicator_far_eq_zero` its far vanishing. -/

/-- The sharp indicator `1(‖a₁-a₂‖ ≤ 6ℓ*_u)` of (5.48) vanishes beyond `12ℓ*_u` — the side
condition `hwfar` of `RBM.Step45.flow_steps45_W` at the indicator weight.  Only `ℓ*_u ≥ 0` is
used (`ℓ*_u = (log W)^{3/2} ℓ_u`, and `W ≥ 1`, `ℓ_u > 0` for `u < 1`). -/
theorem eventually_indicator_far_eq_zero (B : Band Ω) {s t : ℕ → ℝ} (ht1 : ∀ N, t N < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N)),
      12 * ellStar (B.W N : ℝ) (B.ell N p.1) < (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) →
      (if (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) ≤ 6 * ellStar (B.W N : ℝ) (B.ell N p.1)
        then (1 : ℝ) else 0) = 0 := by
  refine Eventually.of_forall fun N p hp => ?_
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hℓ : 0 < B.ell N p.1 :=
    Step3.ellHat_pos_of_lt_one (by have := B.three_le_L N; omega) (p.1.2.2.trans_lt (ht1 N))
  have hstar : 0 ≤ ellStar (B.W N : ℝ) (B.ell N p.1) := by
    have hlog : (0 : ℝ) ≤ Real.log (B.W N : ℝ) := Real.log_nonneg hW1
    unfold ellStar
    positivity
  exact ite_eq_right (by linarith)

/-- **(2.78) and (2.79) with `h0`, `h12`, `h1`, `h2` discharged, from the smoothed (5.48)**
(T233), in exactly the shapes of the fields `RBM.Steps.sharpLmK` and `RBM.Steps.sharpDecay`.
Remaining inputs: the fields of `RBM.Steps` produced by Steps 1–2, `hregS`, Lemma 5.14 (5.92)
for `n ≥ 2`, `AprioriDecayAll`, `Eq45Flow` and `RBM.Step45.FlowEq548W`.  The conclusion is
verbatim that of `flow_steps45_glue'`. -/
theorem flow_steps45_glue_W' (X : Sample B) {κ : ℝ}
    {w : ∀ N, TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N)) → ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h276 : AprioriDecayAll X E s t) (h45 : Eq45Flow X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (hwfar : ∀ᶠ N : ℕ in atTop, ∀ p, 12 * ellStar (B.W N : ℝ) (B.ell N p.1)
      < (zdist (B.L N) (p.2.1 - p.2.2) : ℝ) → w N p = 0)
    (h548 : Step45.FlowEq548W X E s t w) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) := by
  have hE : |E| < 2 := by linarith
  have hcond : Cond272 B E s t := Step2.cond272_of_strict hE hst ht1 hc0 hregS
  exact Step45.flow_steps45_W X hκ0 hκ1 hEκ hs0 hst ht1 hcond h514
    (flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hcond hapriori)
    (flow_S_le_two' X hE hs0 hst ht1 hcond hc0 hregS hll h276)
    (flow_hs1 X hE hs0 ht1 h45 (hsharp 2 (by norm_num)))
    (flow_hs2 X hE hs0 hst ht1 hc0 hregS h276) hwfar h548

/-- **(2.78) and (2.79) with `h0`, `h12`, `h1`, `h2` discharged**, in exactly the shapes of the
fields `RBM.Steps.sharpLmK` and `RBM.Steps.sharpDecay`.  Remaining inputs: the fields of
`RBM.Steps` produced by Steps 1–2, `hregS`, Lemma 5.14 (5.92) for `n ≥ 2`, `AprioriDecayAll`,
`Eq45Flow` and (5.48).

**Signature unchanged** (T233); the proof is now `flow_steps45_glue_W'` at the sharp indicator
`w = 1(d ≤ 6ℓ*_u)`, which `RBM.Step45.flowEq548W_of_flowEq548` dominates by `le_rfl`. -/
theorem flow_steps45_glue' (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h276 : AprioriDecayAll X E s t) (h45 : Eq45Flow X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) :=
  flow_steps45_glue_W' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hsharp h276 h45 h514
    (eventually_indicator_far_eq_zero B ht1)
    (Step45.flowEq548W_of_flowEq548 X (fun _ _ => le_rfl) h548)

/-- **`rfl` probe (T233)**: the smoothed glue at the indicator weight and the unprimed
`flow_steps45_glue'` are the *same statement* — `Eq` forces the two conclusions to be one and
the same Prop, so nothing was reshaped when the (5.48) slot was replaced. -/
example (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hapriori : AprioriFlow X E s t) (hll : LocalLawFlow X E s t)
    (hsharp : SharpLoopFlow X E s t) (h276 : AprioriDecayAll X E s t) (h45 : Eq45Flow X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    flow_steps45_glue' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hsharp h276 h45 h514
        h548 =
      flow_steps45_glue_W' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hapriori hll hsharp h276 h45 h514
        (eventually_indicator_far_eq_zero B ht1)
        (Step45.flowEq548W_of_flowEq548 X (fun _ _ => le_rfl) h548) := rfl


/-! ### The bundle-shaped corollaries (kept for compatibility)

Each is the primed statement with the individual hypotheses replaced by the projections of a
`RBM.Steps`.  They are one-liners, so the two forms cannot drift apart; **they must not be used
to produce a field of `RBM.Steps`** (that is the circularity of T147 §0a). -/

theorem flow_S_zero (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (hSteps : Steps X E s t) (m : ℕ) (hm : 1 ≤ m) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) m 0 :=
  flow_S_zero' X hκ0 hκ1 hEκ hs0 hst ht1 hc hSteps.apriori m hm

theorem flow_lkErr_one_le (X : Sample B) (hSteps : Steps X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 1) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) :=
  flow_lkErr_one_le' X hSteps.localLaw

theorem flow_S_one (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t) (hSteps : Steps X E s t) (l : ℕ) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) 1 l :=
  flow_S_one' X hE hs0 hst ht1 hc hSteps.localLaw l

theorem aprioriDecay_pm (X : Sample B) (ht1 : ∀ N, t N < 1) (hSteps : Steps X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2) :=
  aprioriDecay_pm' X ht1 hSteps.aprioriDecay

theorem flow_S_le_two (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t) {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N)) (hSteps : Steps X E s t) (h276 : AprioriDecayAll X E s t)
    (m l : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2) :
    Step3.S B.P (Step3.flowXiLK X E s t) (Step3.flowAs B E s) (Step3.flowR B s t)
      (Step3.flowA B E s t) m l :=
  flow_S_le_two' X hE hs0 hst ht1 hcond hc0 hregS hSteps.localLaw h276 m l hm1 hm2

theorem flow_sharpLoop_glue (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hSteps : Steps X E s t) (h276 : AprioriDecayAll X E s t)
    (h514 : ∀ n, 3 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) :=
  flow_sharpLoop_glue' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hSteps.apriori hSteps.localLaw h276
    h514 hn

theorem flow_steps45_glue (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hregS : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c * (etaT E (s N) / etaT E (t N)) ^ 30 ≤
      B.scale E N (t N))
    (hSteps : Steps X E s t) (h276 : AprioriDecayAll X E s t) (h45 : Eq45Flow X E s t)
    (h514 : ∀ n, 2 ≤ n → Step3.Lemma514 B.P (Step3.flowXiLK X E s t) (Step3.flowXiL X E s t)
      (Step3.flowA B E s t) n)
    (h548 : Step45.FlowEq548 X E s t) :
    (∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr E N p.1 ω p.2.idx)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ n)) ∧
    (∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2)) :=
  flow_steps45_glue' X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hregS hSteps.apriori hSteps.localLaw
    hSteps.sharpLoop h276 h45 h514 h548


/-! ### The bare (2.72) plus the regime bound (T209)

D13 fixes the step condition of Theorem 2.21 to `RBM.Cond272Reg` (`Flow/Thm221Bare.lean`) —
(2.72) **exactly as printed** together with the regime bound `N^c ≤ W ℓ_t η_t` that Step 1
already carries.  Everything below this file consumes instead `hregS = RBM.Cond272'`, the
(2.72) *with* an `N^c` gain, and no bridge `RBM.Cond272Reg → RBM.Cond272'` exists: in
`RBM.rpow_mul_rpow_le_of_pow_thirty` the exponents `a = 1`, `b = 30` force `e ≤ 0` (T186).

The three lemmas here are the restatements the D13 shape needs.  They take the two components
of `RBM.Cond272Reg` separately — `RBM.Cond272` and `∀ᶠ N, N^c ≤ W ℓ_t η_t` — because
`RBM.Cond272Reg` is defined in `Flow/Thm221Bare.lean`, which is downstream of this file;
`Flow/Thm221NoEL.lean` supplies them as `h.1` and `h.2`.

Each is the `RBM.Cond272'`-shaped original with its use of `hregS` isolated:

* `RBM.StepGlue.eventually_R4_le_scale_of_cond272` — `RBM.Step2.eventually_R4_le_scale`.  The
  original derives `(η_s/η_u)^4 ≤ W ℓ_u η_u` from `N^c (η_s/η_t)^{30} ≤ W ℓ_t η_t`; only the
  exponent `4 ≤ 30` is used, so the bare (2.72) suffices, and the regime bound carries the
  second conjunct.
* `RBM.StepGlue.aprioriDecay_of_jS_of_cond272` — `RBM.Step2Moment.aprioriDecay_of_jS`, whose
  only use of `hregS` is `RBM.Step2.cond272_of_strict`, i.e. it only ever wanted
  `RBM.Cond272`.
* `RBM.StepGlue.localLaw_of_scale_facts` — `RBM.Step2.localLaw`, whose only use of `hregS` is
  the one line `hfacts := RBM.Step2.eventually_R4_le_scale …`, here promoted to a hypothesis.
  The proof script is copied unchanged.

T235 closed the loop: the proofs of the last two now live next to the statements they
generalize (`RBM.Step2.localLaw_of_scale_facts`, `RBM.Step2Moment.aprioriDecay_of_jS_of_cond272`),
the originals `RBM.Step2.localLaw` and `RBM.Step2Moment.aprioriDecay_of_jS` are one-line
corollaries of them, and what is left here are the one-line corollaries kept at the old names
for this file's consumers. -/

/-- **`(η_s/η_u)^4 ≤ W ℓ_u η_u` and `N^c ≤ W ℓ_u η_u` for every `u ∈ [s,t]`, from the bare
(2.72) plus the regime bound.**  Verbatim the conclusion of
`RBM.Step2.eventually_R4_le_scale`, with `hregS` replaced by the two components of
`RBM.Cond272Reg`.

(2.72) inverted is `((1-s)/(1-t))^{30} ≤ W ℓ_t η_t`; the ratio `η_s/η_u ≤ (1-s)/(1-t)` is at
least `1`, so its fourth power is below its thirtieth, and `W ℓ_t η_t ≤ W ℓ_u η_u`
(`RBM.flowScale_antitoneOn`) transports both conjuncts from `t` to `u`. -/
theorem eventually_R4_le_scale_of_cond272 (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ}
    (hcond : Cond272 B E s t)
    (hreg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ B.scale E N (t N)) :
    ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (s N) / etaT E u) ^ 4 ≤ B.scale E N u ∧ (N : ℝ) ^ c ≤ B.scale E N u := by
  filter_upwards [hcond, hreg] with N hN hNc u
  have hW0 : (0 : ℝ) ≤ B.W N := by positivity
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1t : 0 < 1 - t N := by linarith [ht1 N]
  have h1s : 0 < 1 - s N := by linarith
  have hAt0 : 0 < B.scale E N (t N) :=
    B.scale_pos' hE N ((hs0 N).trans (hst N)) (ht1 N)
  have hAv : B.scale E N (t N) ≤ B.scale E N u := flowScale_antitoneOn hW0 (B.L N) E
    (Set.mem_Iic.2 hu1.le) (Set.mem_Iic.2 (ht1 N).le) u.2.2
  -- (2.72), inverted
  have hQ30 : ((1 - s N) / (1 - t N)) ^ 30 ≤ B.scale E N (t N) := by
    have hinv := inv_anti₀ (inv_pos.2 hAt0) hN
    rw [inv_inv] at hinv
    have heq : ((1 - s N) / (1 - t N)) ^ 30 = (((1 - t N) / (1 - s N)) ^ 30)⁻¹ := by
      rw [← inv_pow, inv_div]
    rw [heq]; exact hinv
  have hR1 : 1 ≤ etaT E (s N) / etaT E u := by
    rw [Step2.etaT_ratio hE, le_div_iff₀ h1u]; linarith [u.2.1]
  have hRt : etaT E (s N) / etaT E u ≤ (1 - s N) / (1 - t N) := by
    rw [Step2.etaT_ratio hE]
    exact div_le_div_of_nonneg_left h1s.le h1t (by linarith [u.2.2])
  refine ⟨?_, hNc.trans hAv⟩
  calc (etaT E (s N) / etaT E u) ^ 4 ≤ ((1 - s N) / (1 - t N)) ^ 4 :=
        pow_le_pow_left₀ (by linarith) hRt 4
    _ ≤ ((1 - s N) / (1 - t N)) ^ 30 :=
        pow_le_pow_right₀ (hR1.trans hRt) (by norm_num)
    _ ≤ B.scale E N (t N) := hQ30
    _ ≤ B.scale E N u := hAv

/-- **(2.76) from (5.47), from the bare (2.72).**  `RBM.Step2Moment.aprioriDecay_of_jS` with
`hregS` replaced by `RBM.Cond272`: the original's only use of `hregS` is
`RBM.Step2.cond272_of_strict`, so no gain was ever needed here.

T235 moved the proof to `RBM.Step2Moment.aprioriDecay_of_jS_of_cond272`, next to the statement
it generalizes; this is the one-line corollary kept at the old name for its consumers. -/
theorem aprioriDecay_of_jS_of_cond272 (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hJ : ∀ D : ℝ, 60 ≤ D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4)) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2) :=
  Step2Moment.aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1 hcond hJ

/-- **(2.75), from the scale facts.**  `RBM.Step2.localLaw` with its single use of `hregS` —
the line `hfacts := RBM.Step2.eventually_R4_le_scale hE hst ht1 hc0 hreg` — promoted to a
hypothesis, so that either `RBM.Cond272'` (through `RBM.Step2.eventually_R4_le_scale`) or
`RBM.Cond272Reg` (through `RBM.StepGlue.eventually_R4_le_scale_of_cond272`) may discharge it.

`c` still occurs: the weak law (2.74) is upgraded on the event
`{‖G_u - m‖_max ≤ (W ℓ_u η_u)^{-1/6}}`, and the margin `N^{c/24}` of that upgrade comes from
the second conjunct of `hfacts`.

T235 moved the proof to `RBM.Step2.localLaw_of_scale_facts`, next to the statement it
generalizes; this is the one-line corollary kept at the old name for its consumers. -/
theorem localLaw_of_scale_facts (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hfacts : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (s N) / etaT E u) ^ 4 ≤ B.scale E N u ∧ (N : ℝ) ^ c ≤ B.scale E N u)
    (h276 : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2))
    (h274 : StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4)))
    (h41 : Step1.Lemma41Flow X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 2)) :=
  Step2.localLaw_of_scale_facts X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hfacts h276 h274 h41

/-! ### `rfl`-probes: the two T209 remainders are unchanged (T235)

The two theorems above are now the one-line corollaries of the versions that live next to the
statements they generalize.  Each probe type-checks only if the two sides are proofs of the
same `Prop`, i.e. only if the statement kept at the old name is *verbatim* the one that moved:
nothing here was strengthened or weakened by the move. -/

example (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hcond : Cond272 B E s t)
    (hJ : ∀ D : ℝ, 60 ≤ D → StochDom B.P
      (fun N (u : TimeIcc s t N) ω => Step2.jS X E D N u ω)
      (fun N u _ => (etaT E (s N) / etaT E u) ^ 4)) :
    aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1 hcond hJ =
      Step2Moment.aprioriDecay_of_jS_of_cond272 X hE hs0 hst ht1 hcond hJ := rfl

example (X : Sample B) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 < c)
    (hfacts : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT E (s N) / etaT E u) ^ 4 ≤ B.scale E N u ∧ (N : ℝ) ^ c ≤ B.scale E N u)
    (h276 : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr E N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT E (s N) / etaT E p.1) ^ 4 * (B.scale E N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2))
    (h274 : StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr E N p.1 ω p.2)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ ((1 : ℝ) / 4)))
    (h41 : Step1.Lemma41Flow X E s t) :
    localLaw_of_scale_facts X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hfacts h276 h274 h41 =
      Step2.localLaw_of_scale_facts X hκ0 hκ1 hEκ hs0 hst ht1 hc0 hfacts h276 h274 h41 := rfl

end StepGlue

end RBM

