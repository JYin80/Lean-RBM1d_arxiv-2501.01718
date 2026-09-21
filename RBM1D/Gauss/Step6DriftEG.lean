/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6DriftSplit

/-!
# T189: (5.134)–(5.135) for the pinned `E E^{(G̃)}`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8, (5.134)–(5.135) (p. 73), for the tensor `RBM.driftEG` that T182
(`RBM1D/Gauss/Step6DriftSplit.lean`) pinned.

T182 showed that the `E^{(G̃)}` half of the drift is, **pathwise**, exactly one factor
`A = W ℓ_u η_u` short of (5.133): the third line of (5.77) gives
`Ξ^{(L-K)}_{u,1} Ξ^{(L)}_{u,3} η_u^{-1} A^{-2}`, and the two `Ξ`'s are already spent.  What is
missing is recovered by writing `L = K + (L-K)` inside the `3`-loop of `E^{(G̃)}`, which is
(5.134).  Both halves of that splitting gain exactly one power of `A`, and for *different*
reasons:

* the `K` half: `K` is deterministic, so the expectation falls on the `1`-loop alone, and
  Lemma 5.15 (5.126) gives `|E⟨(G-m)E_a⟩| ≺ A^{-2}` where the pathwise `(L-K)_1` only gives
  `A^{-1}`.  **This is the cancellation inside the expectation.**
* the `L-K` half: it is pathwise, but the `3`-loop is now `(L-K)_3 ≺ A^{-3}` ((2.78)) instead
  of `L_3 ≺ A^{-2}` ((2.77)).

Both halves therefore land on `η_u^{-1} A^{-3}`, i.e. (5.135), and the `A^{-1}` is recovered in
full.

## Main results

* `RBM.gloop_one_conj`, `RBM.lkPath_one_conj`, `RBM.norm_integral_lkPath_one` — the `1`-loop at
  the charge `-` is the complex conjugate of the one at `+` (`G(σ)ᴴ = G(-σ)`, `m(-) = m(+)‾`),
  so Lemma 5.15, which is stated at `+`, controls **both** charges of `E(L-K)_{u,(σ),(a)}`.
  Without this, (5.134) would be missing three of the four charge patterns of `σ ∈ {+,-}²`.
* `RBM.eG_add_right`, `RBM.integral_eG_const_right`, `RBM.integrable_eG_const_right` —
  `E^{(G)}` is additive in its loop argument, and against a *deterministic* loop argument it
  commutes with `E`: this is what lets the expectation act on the `1`-loop alone.
* `RBM.norm_eG_two_le` — **(5.77), third line, at loop length `2`, in (5.133)'s own shape**
  `W ℓ_u (W ℓ_u η_u)^{-4}`, for an arbitrary pair of one-loop / three-loop budgets whose
  product carries one extra `A^{-1}`.  Both halves of (5.134) are instances of it.
* `RBM.driftEG_eq_add` — **(5.134)**: `E E^{(G̃)} = E[E^{(G)}(L-K, L-K)] + E^{(G)}(E(L-K), K)`.
* `RBM.unifDetDom_driftEG`, `RBM.driftBound_driftEG` — **(5.135)**.
* `RBM.exists_loopDecay_Kval`, `RBM.loopDecay_lkPath`, `RBM.mem_egInputs_of`,
  `RBM.scale_shape_check`, `RBM.pathwise_shape_is_one_power_weaker` — the satisfiability and
  shape checks (see below).
* `RBM.sharpExpect_step6_driftEG` — **(2.80)** with `hG` **gone**: the consumer is
  `RBM.Step6.sharpExpect_of_hierarchy`, fed with two *proved* `RBM.Step6.DriftBound`s.

## What `hG` in the shape of `RBM.Step6.sharpExpect_step6` cannot be

`RBM.Step6.sharpExpect_step6`'s field `hG` asks for `‖E E^{(G̃)}‖ ≤ C W ℓ_u Λ` from nothing but
a uniform bound `Λ` on `E[⟨(G-m)E_{a₁}⟩ L_{u,σ',a'}]`.  That implication is **false in that
form**: `E^{(G)}` is `W ∑_{a,b} S^{(B)}_{ab} X_a Y_b` and `∑_{a,b} S^{(B)}_{ab} = L`, so a
uniform bound gives `W · L · Λ` and nothing better.  The paper's `W · ℓ_u` comes from the
*decay* of the `3`-loop (`RBM.Decay.norm_sum_SB_le_right`: the `a`-sum is confined to a window
of `O(ℓ_u)` sites), which the hypothesis `hG` does not supply.  So this file does not prove
`hG`; it proves its consequence (5.135) directly, from the decay that Lemma 5.9 does supply.

## The satisfiability checks

Every hypothesis of `RBM.unifDetDom_driftEG` that is *not* already an input of T182's
`RBM.sharpExpect_step6_driftSplit` is checked here for satisfiability, before the bound is
proved:

* `hKd` (the decay of `K` at loop length `3`) — `RBM.exists_loopDecay_Kval`: Lemma 5.9's `K`
  side (`RBM.Decay.loopDecay_Kgen`) produces such a decay at **every** radius `ℓ > 0`.
* `RBM.EGInputs` (the decay of `L - K` at loop length `3`) — `RBM.mem_egInputs_of`: it follows
  from the *same* pathwise decay T182 already uses (`RBM.FDInputs`, which carries the length-`3`
  decay of `L`) together with `hKd`, at twice the budget.  So `hinG` asks for nothing Lemma 5.9
  does not already supply; only the power counts (5.76) at lengths `1` and `3` are new, and they
  are the same class of input as T182's `xiLK ... 2 ≤ Ψ`.
* `h526` — it is literally the conclusion of `RBM.Step6.lemma515`, and the final assembly
  produces it from `h527` and `hq11` rather than assuming it.
* The exponent bookkeeping — `RBM.scale_shape_check` checks `W ℓ A^{-4} = η^{-1} A^{-3}` at a
  numerical point, and `RBM.pathwise_shape_is_one_power_weaker` checks that the pathwise shape
  `η^{-1} A^{-2}` is exactly `A` times the target, i.e. that the gain claimed here is one power
  of `A` and not two.

## The fiat audit

`RBM.driftEG` is untouched — T182's definition is used verbatim and `RBM.driftEG_eq_add` is a
theorem about it, not a redefinition.  No hypothesis of `RBM.unifDetDom_driftEG` mentions the
drift except through that definition: they are Lemma 5.15 (itself produced by
`RBM.Step6.lemma515`), (2.59) (`RBM.Band.norm_Kval_le`, proved), the decay of `K` (with the
satisfiability witness `RBM.exists_loopDecay_Kval`), Lemma 5.9's decay of `L - K` and the power
counts (5.76) at lengths `1` and `3`, plus measurability, a crude envelope and integrability.
`RBM.SumZeroDyn.Hierarchy` is never instantiated and no field of `RBM.SumZeroDyn.Lemma510` is
used.  Nothing here is an `axiom` and no proof is left open.
-/

namespace RBM

open MeasureTheory Filter

/-! ### `E^{(G)}` is additive in the loop argument, and `E`-linear in the one-loop argument -/

section EGAlg

variable {L : ℕ} [NeZero L]

/-- **`E^{(G)}` is additive in its loop argument** (the `Y` of `RBM.Decay.eG`).  This is the
splitting `L = K + (L - K)` of (5.134). -/
theorem eG_add_right (W : ℕ) (Xf Y Z : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L)) :
    Decay.eG L W Xf (fun J => Y J + Z J) I
      = Decay.eG L W Xf Y I + Decay.eG L W Xf Z I := by
  simp only [Decay.eG]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E^{(G)}` against a deterministic loop argument is integrable as soon as the one-loops
are. -/
theorem integrable_eG_const_right (W : ℕ) {P : Measure Ω}
    (Xf : Ω → LoopIdx (ZMod L) → ℂ) (Y : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    (hint : ∀ (s : Bool) (a : ZMod L), Integrable (fun ω => Xf ω ⟨[s], [a]⟩) P) :
    Integrable (fun ω => Decay.eG L W (Xf ω) Y I) P := by
  simp only [Decay.eG]
  refine Integrable.const_mul ?_ _
  refine integrable_finsetSum _ fun k _ => ?_
  refine integrable_finsetSum _ fun a _ => ?_
  refine integrable_finsetSum _ fun b _ => ?_
  exact ((hint _ a).mul_const _).mul_const _

/-- **The expectation falls on the `1`-loop alone.**  Against a *deterministic* loop argument
`Y` (in (5.134): `Y = K`), `E^{(G)}` commutes with `E`, so `E E^{(G)}(L-K, K)` is
`E^{(G)}(E(L-K), K)` — and `E(L-K)` at a one-loop is the quantity Lemma 5.15 bounds. -/
theorem integral_eG_const_right (W : ℕ) {P : Measure Ω}
    (Xf : Ω → LoopIdx (ZMod L) → ℂ) (Y : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    (hint : ∀ (s : Bool) (a : ZMod L), Integrable (fun ω => Xf ω ⟨[s], [a]⟩) P) :
    (∫ ω, Decay.eG L W (Xf ω) Y I ∂P) = Decay.eG L W (fun J => ∫ ω, Xf ω J ∂P) Y I := by
  have hterm : ∀ (k : ℕ) (a b : ZMod L),
      (∫ ω, Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b) ∂P)
        = (∫ ω, Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ ∂P) * SB L a b * Y (I.cutGlue k b) := by
    intro k a b
    rw [show (fun ω => Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b))
        = (fun ω => Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ * (SB L a b * Y (I.cutGlue k b)))
        from funext fun ω => by ring, integral_mul_const]
    ring
  have hb : ∀ (k : ℕ) (a : ZMod L), ∀ b ∈ (Finset.univ : Finset (ZMod L)),
      Integrable (fun ω => Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b *
        Y (I.cutGlue k b)) P := fun k a b _ => ((hint _ a).mul_const _).mul_const _
  have ha : ∀ k : ℕ, ∀ a ∈ (Finset.univ : Finset (ZMod L)),
      Integrable (fun ω => ∑ b : ZMod L, Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b *
        Y (I.cutGlue k b)) P := fun k a _ => integrable_finsetSum _ (hb k a)
  have hk : ∀ k ∈ Finset.Icc 1 I.length,
      Integrable (fun ω => ∑ a : ZMod L, ∑ b : ZMod L,
        Xf ω ⟨[I.σ.getD (k - 1) true], [a]⟩ * SB L a b * Y (I.cutGlue k b)) P :=
    fun k _ => integrable_finsetSum _ (ha k)
  simp only [Decay.eG]
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ hk]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ (ha k)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (hb k a)]
  exact Finset.sum_congr rfl fun b _ => hterm k a b

end EGAlg

/-! ### Lemma 5.15 covers both charges of the `1`-loop -/

section Conj

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **Conjugating a `1`-loop flips its charge**: `G(σ)ᴴ = G(-σ)` and `E_aᴴ = E_a`, so
`⟨G(-σ)E_a⟩ = ⟨G(σ)E_a⟩‾`. -/
theorem gloop_one_conj {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hM : M.IsHermitian)
    (z : ℂ) (s : Bool) (x : ZMod L) :
    gloop L W M z ⟨[!s], [x]⟩ = (starRingEnd ℂ) (gloop L W M z ⟨[s], [x]⟩) := by
  have h1 : gloop L W M z ⟨[s], [x]⟩ = Matrix.trace (Gsig M z s * Eblk L W x) := by
    rw [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]
  have h2 : gloop L W M z ⟨[!s], [x]⟩ = Matrix.trace (Gsig M z (!s) * Eblk L W x) := by
    rw [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]
  have h3 : (Gsig M z s * Eblk L W x).conjTranspose = Eblk L W x * Gsig M z (!s) := by
    rw [Matrix.conjTranspose_mul, Eblk_conjTranspose, Gsig_conjTranspose hM]
  rw [h1, h2, Matrix.trace_mul_comm (Gsig M z (!s)) (Eblk L W x), ← h3,
    Matrix.trace_conjTranspose]
  rfl

/-- `m(-σ) = m(σ)‾`. -/
theorem mSigma_not (E : ℝ) (s : Bool) : mSigma E (!s) = (starRingEnd ℂ) (mSigma E s) := by
  cases s
  · rw [Bool.not_false, mSigma_true, mSigma_false, Complex.conj_conj]
  · rw [Bool.not_true, mSigma_false, mSigma_true]

end Conj

section ConjFlow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- The pathwise `1`-loop of `L - K` at the charge `-σ` is the conjugate of the one at `σ`. -/
theorem lkPath_one_conj (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω) (s : Bool)
    (x : ZMod (B.L N)) :
    lkPath X E N v ω ⟨[!s], [x]⟩ = (starRingEnd ℂ) (lkPath X E N v ω ⟨[s], [x]⟩) := by
  show gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) ⟨[!s], [x]⟩ - B.Kval E N v ⟨[!s], [x]⟩
      = (starRingEnd ℂ) (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) ⟨[s], [x]⟩
          - B.Kval E N v ⟨[s], [x]⟩)
  rw [map_sub, gloop_one_conj (X.hermitian N v ω), Band.Kval, Band.Kval, Kgen_one, Kgen_one,
    mSigma_not]

/-- `E(L-K)_{v,(+),(a)}` is `RBM.Step6.lk1`, the quantity of (5.126). -/
theorem integral_lkPath_one_true (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ)
    (x : ZMod (B.L N))
    (hint : Integrable (fun ω => X.Lval E N v ω ⟨[true], [x]⟩) B.P) :
    (∫ ω, lkPath X E N v ω ⟨[true], [x]⟩ ∂B.P) = Step6.lk1 X E N v x := by
  have := B.isProbabilityMeasure
  show (∫ ω, (X.Lval E N v ω ⟨[true], [x]⟩ - B.Kval E N v ⟨[true], [x]⟩) ∂B.P) = _
  rw [integral_sub hint (integrable_const _), integral_const]
  simp [Step6.lk1, Step6.oneLoop, Sample.ELval]

/-- **Lemma 5.15 covers both charges**: `|E(L-K)_{v,(σ),(a)}| = |E⟨(G_v - m)E_a⟩|` for
`σ ∈ {+,-}`.  Without this the `K` half of (5.134) would only be available for the charge `+`,
i.e. for one of the four `σ ∈ {+,-}²`. -/
theorem norm_integral_lkPath_one (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (s : Bool)
    (x : ZMod (B.L N))
    (hint : Integrable (fun ω => X.Lval E N v ω ⟨[true], [x]⟩) B.P) :
    ‖∫ ω, lkPath X E N v ω ⟨[s], [x]⟩ ∂B.P‖ = ‖Step6.lk1 X E N v x‖ := by
  cases s
  · have hpt : ∀ ω : Ω, lkPath X E N v ω ⟨[false], [x]⟩
        = (starRingEnd ℂ) (lkPath X E N v ω ⟨[true], [x]⟩) := by
      intro ω
      have := lkPath_one_conj X E N v ω true x
      rwa [Bool.not_true] at this
    rw [show (fun ω : Ω => lkPath X E N v ω ⟨[false], [x]⟩)
        = (fun ω : Ω => (starRingEnd ℂ) (lkPath X E N v ω ⟨[true], [x]⟩)) from funext hpt,
      integral_conj, RCLike.norm_conj, integral_lkPath_one_true X E N v x hint]
  · rw [integral_lkPath_one_true X E N v x hint]

end ConjFlow

/-! ### (5.77), third line, at loop length `2`, in (5.133)'s shape -/

section Pointwise

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The third line of (5.77) at `n = 0`, in (5.133)'s own shape** `W ℓ_u (W ℓ_u η_u)^{-4}`.

`RBM.DriftBound.norm_driftF_le` applies the third line with `Ξ = Ξ^{(L-K)}_{u,1}`,
`Φ = Ξ^{(L)}_{u,3}`, whose product carries **no** extra `A^{-1}`; the result is then one factor
`A` weaker than (5.133) (T182).  Here the product `Ξ · Φ` is only assumed to be `≤ C A^{-1}`,
which is exactly the gain that the two halves of (5.134) supply — the `K` half through (5.126)
(`Ξ = |E(L-K)_1| A ≤ Ψ A^{-1}`), the `L-K` half through (2.78) at length `3`
(`Φ = Ξ^{(L-K)}_{u,3} A^{-1}`).  The single identity spent is `RBM.Decay.mul_add_one_div_le`,
`W(ℓ_u Krad + 1)/A ≤ (Krad + 2)/η_u`. -/
theorem norm_eG_two_le {E : ℝ} (N : ℕ) {u : ℝ}
    (Xf Yf : LoopIdx (ZMod (B.L N)) → ℂ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2)
    {Krad δ Ξ Φ C Ξb : ℝ}
    (hE : |E| < 2) (hu1 : u < 1) (hA : 1 ≤ B.scale E N u) (hell : 1 / 2 ≤ B.ell N u)
    (hKrad : 1 ≤ Krad) (hδ : 0 ≤ δ) (hΞ0 : 0 ≤ Ξ) (hC0 : 0 ≤ C)
    (hX : ∀ (s : Bool) (x : ZMod (B.L N)), ‖Xf ⟨[s], [x]⟩‖ ≤ Ξ * (B.scale E N u)⁻¹)
    (hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
      ‖Yf J‖ ≤ Φ * (B.scale E N u)⁻¹ ^ 2)
    (hYd : Decay.LoopDecay (B.L N) 3 (B.ell N u * Krad) δ Yf)
    (hCΦ : Ξ * Φ ≤ C * (B.scale E N u)⁻¹) (hΞb : Ξ ≤ Ξb) :
    ‖Decay.eG (B.L N) (B.W N) Xf Yf (LoopData.idx (σ, a))‖
      ≤ 4 * Real.exp 1 * (Krad + 2) * C
          * ((B.W N : ℝ) * B.ell N u * (B.scale E N u)⁻¹ ^ 4)
        + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Ξb := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hW : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hℓ0 : (0 : ℝ) < B.ell N u * Krad := by nlinarith
  set A := B.scale E N u with hAdef
  have hAi0 : (0 : ℝ) ≤ A⁻¹ := inv_nonneg.2 hA0.le
  have hbase := Decay.norm_loopTensor_eG_le (B.L N) hL3 (B.W N) (n := 2) (X := Xf) (Y := Yf) σ
    (A := A) (ℓ := B.ell N u * Krad) (δ := δ) (Ξ₂ := Ξ) (Φ := Φ) hA hℓ0 hδ hΞ0 hX hY hYd a
  have hLT : ‖Decay.eG (B.L N) (B.W N) Xf Yf (LoopData.idx (σ, a))‖
      = ‖Decay.loopTensor (B.L N) (Decay.eG (B.L N) (B.W N) Xf Yf) σ a‖ := rfl
  have hfrac : (B.W N : ℝ) * (B.ell N u * Krad + 1) / A ≤ (Krad + 2) * (etaT E u)⁻¹ := by
    rw [hAdef, show B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u from rfl,
      ← div_eq_mul_inv]
    exact Decay.mul_add_one_div_le hW hell hη
  have hid : (B.W N : ℝ) * B.ell N u * A⁻¹ ^ 4 = (etaT E u)⁻¹ * A⁻¹ ^ 3 :=
    Step6.W_mul_ell_mul_scale_inv_pow_four hE N hu1
  set fr : ℝ := (B.W N : ℝ) * (B.ell N u * Krad + 1) / A with hfrdef
  have hfr0 : 0 ≤ fr :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hA0.le
  have hcoef1 : (0 : ℝ) ≤ 4 * Real.exp 1 * fr * A⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hfr0) (by positivity)
  have hcoef2 : (0 : ℝ) ≤ 4 * Real.exp 1 * C * A⁻¹ * A⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC0) hAi0) (by positivity)
  have hmain : 2 * Real.exp 1 * (2 : ℝ) * Ξ * Φ * fr * A⁻¹ ^ 2
      ≤ 4 * Real.exp 1 * (Krad + 2) * C * ((B.W N : ℝ) * B.ell N u * A⁻¹ ^ 4) := by
    rw [hid]
    calc 2 * Real.exp 1 * (2 : ℝ) * Ξ * Φ * fr * A⁻¹ ^ 2
        = (Ξ * Φ) * (4 * Real.exp 1 * fr * A⁻¹ ^ 2) := by ring
      _ ≤ (C * A⁻¹) * (4 * Real.exp 1 * fr * A⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_right hCΦ hcoef1
      _ = fr * (4 * Real.exp 1 * C * A⁻¹ * A⁻¹ ^ 2) := by ring
      _ ≤ ((Krad + 2) * (etaT E u)⁻¹) * (4 * Real.exp 1 * C * A⁻¹ * A⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_right hfrac hcoef2
      _ = 4 * Real.exp 1 * (Krad + 2) * C * ((etaT E u)⁻¹ * A⁻¹ ^ 3) := by ring
  have herr : (2 : ℝ) * (B.W N : ℝ) * (B.L N : ℝ) * δ * Ξ
      ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Ξb := by
    have h0 : (0 : ℝ) ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) := by
      have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
      have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
      positivity
    calc (2 : ℝ) * (B.W N : ℝ) * (B.L N : ℝ) * δ * Ξ
        = 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Ξ := by ring
      _ ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Ξb := mul_le_mul_of_nonneg_left hΞb h0
  rw [hLT]
  push_cast at hbase
  linarith [hbase]

end Pointwise

/-! ### (5.134): the splitting `L = K + (L - K)` inside `E^{(G̃)}` -/

section Split134

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

theorem integrable_lkPath_one (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (b : Bool)
    (x : ZMod (B.L N)) (h : Integrable (fun ω => X.Lval E N v ω ⟨[b], [x]⟩) B.P) :
    Integrable (fun ω => lkPath X E N v ω ⟨[b], [x]⟩) B.P := by
  have := B.isProbabilityMeasure
  show Integrable (fun ω => X.Lval E N v ω ⟨[b], [x]⟩ - B.Kval E N v ⟨[b], [x]⟩) B.P
  exact h.sub (integrable_const _)

/-- **The splitting `L = K + (L-K)` of (5.134)**, pathwise. -/
theorem eG_gloop_eq_add (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω)
    (I : LoopIdx (ZMod (B.L N))) :
    Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) I
      = Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω) I
        + Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (B.Kval E N v) I := by
  have hfun : (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v))
      = (fun J => lkPath X E N v ω J + B.Kval E N v J) := by
    funext J
    show _ = (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) J - B.Kval E N v J) + B.Kval E N v J
    ring
  rw [hfun, eG_add_right]

/-- **(5.134)**: `E E^{(G̃)}_{v,σ,a} = E[E^{(G)}(L-K, L-K)] + E^{(G)}(E(L-K), K)`.  The second
summand is where the cancellation lives: `K` is deterministic, so the expectation acts on the
`1`-loop alone, and Lemma 5.15 gives it one power of `A` more than the pathwise bound. -/
theorem driftEG_eq_add (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool)
    (a : LoopArg (B.L N) 2)
    (hint1 : ∀ (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => lkPath X E N v ω ⟨[b], [x]⟩) B.P)
    (hintLK : Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
      (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P) :
    driftEG X E N v σ a
      = (∫ ω, Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
          (LoopData.idx (σ, a)) ∂B.P)
        + Decay.eG (B.L N) (B.W N) (fun J => ∫ ω, lkPath X E N v ω J ∂B.P) (B.Kval E N v)
            (LoopData.idx (σ, a)) := by
  have hintK := integrable_eG_const_right (B.W N) (fun ω => lkPath X E N v ω) (B.Kval E N v)
    (LoopData.idx (σ, a)) hint1
  show (∫ ω, Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
      (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a)) ∂B.P) = _
  rw [show (fun ω : Ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
          (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a)))
        = (fun ω : Ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
              (LoopData.idx (σ, a))
            + Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (B.Kval E N v)
              (LoopData.idx (σ, a)))
        from funext fun ω => eG_gloop_eq_add X E N v ω (LoopData.idx (σ, a)),
    integral_add hintLK hintK,
    integral_eG_const_right (B.W N) (fun ω => lkPath X E N v ω) (B.Kval E N v) _ hint1]

end Split134

/-! ### The decay of `K` at loop length `3` is satisfiable -/

section KDecay

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The satisfiability witness for `hKd`.**  `RBM.Decay.loopDecay_Kgen` (Lemma 5.9, `K`
side) gives the decay of `K` at every radius `ℓ > 0`, with the gap `δ = 1 - v`; so the
hypothesis `hKd` of `RBM.unifDetDom_driftEG` — the only deterministic decay demand of this
file — is not vacuous.  Turning this into the `(ℓ_v N^τ, N^{-D})` form that the flow needs is
the quantitative part of Lemma 5.9, which lives with `RBM.DriftBound.DriftInputs`. -/
theorem exists_loopDecay_Kval (B : Band Ω) {E : ℝ} (hE : |E| ≤ 2) (N : ℕ) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ δ : ℝ, 0 ≤ δ ∧ Decay.LoopDecay (B.L N) 3 ℓ δ (B.Kval E N v) := by
  have hm1 : ∀ s, ‖mSigma E s‖ ≤ 1 := fun s => le_of_eq (norm_mSigma hE s)
  have hgap : ∀ s s', 1 - v ≤ ‖1 - (v : ℂ) * (mSigma E s * mSigma E s')‖ := by
    intro s s'
    refine one_sub_le_norm_one_sub_mul hv0 ?_
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, mul_one]
  refine ⟨Decay.cKdecay 3 (1 - v) * Real.exp (-(cor35Rate (1 - v) * ℓ)), ?_,
    Decay.loopDecay_Kgen (B.L N) (B.three_le_L N) (B.W N) hm1 hv0 hv1 (by linarith) hgap 3 hℓ⟩
  have h1 : (0 : ℝ) ≤ Decay.cKdecay 3 (1 - v) := by
    rw [Decay.cKdecay]
    have h2 : (0 : ℝ) ≤ ∑ n ∈ Finset.range (3 + 1), cor35Const n (1 - v) :=
      Finset.sum_nonneg fun n _ => cor35Const_nonneg n (by linarith)
    have h3 := cTwo52_pos
    have : (0 : ℝ) ≤ 2 * cTwo52 / (1 - v) := by positivity
    linarith
  positivity

end KDecay

/-! ### (5.135) for the pinned `E E^{(G̃)}` -/

section Arith

/-- `k + c ≤ k(1 + c)` for `k ≥ 1`, `c ≥ 0`. -/
theorem add_le_mul_one_add {k c : ℝ} (hk : 1 ≤ k) (hc : 0 ≤ c) : k + c ≤ k * (1 + c) := by
  nlinarith

/-- `a + a ≤ a x` for `a ≥ 0`, `x ≥ 2`. -/
theorem add_self_le_mul_two_le {a x : ℝ} (ha : 0 ≤ a) (hx : 2 ≤ x) : a + a ≤ a * x := by
  nlinarith

/-- `aG + G ≤ bG` from `a + 1 ≤ b`, `G ≥ 0`. -/
theorem mul_add_le_mul_of_add_one_le {a b G : ℝ} (h : a + 1 ≤ b) (hG : 0 ≤ G) :
    a * G + G ≤ b * G := by nlinarith

/-- `2wk + 2wk ≤ 4(zk)` from `w ≤ z`, `k ≥ 0`. -/
theorem two_mul_add_two_mul_le {w z k : ℝ} (hk : 0 ≤ k) (hw : w ≤ z) :
    2 * w * k + 2 * w * k ≤ 4 * (z * k) := by nlinarith

/-- The final bookkeeping of (5.135): one main term, two error terms, the target. -/
theorem final_arith_eg {m₁ m₂ e₁ e₂ envd f Gt half full : ℝ}
    (hmain : m₁ + m₂ ≤ half) (herr : e₁ + e₂ ≤ f) (henv : envd ≤ f)
    (hsum : f + f ≤ Gt) (hfin : half + Gt ≤ full) :
    m₁ + e₁ + envd + (m₂ + e₂) ≤ full := by linarith

end Arith

section EGDom

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The pathwise inputs of (5.135) at one `N`**: Lemma 5.9's `(Krad, δ)` decay of `L - K` at
the `3`-loops and the power counts (5.76) = (2.78) at lengths `1` and `3`, uniformly in
`u ∈ [s_N, t_N]`.  Neither mentions the drift.  Length `3` is where the extra `A^{-1}` of the
`L-K` half of (5.134) comes from: `(L-K)_3 ≺ A^{-3}` where `L_3` is only `≺ A^{-2}`. -/
def EGInputs (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) (Krad δ Ψ : ℝ) : Set Ω :=
  {ω | ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * Krad) δ (lkPath X E N (v : ℝ) ω)
    ∧ X.xiLK E N (v : ℝ) ω 1 ≤ Ψ
    ∧ X.xiLK E N (v : ℝ) ω 3 ≤ Ψ}

open Real in
set_option maxHeartbeats 1000000 in
/-- **(5.135) for `RBM.driftEG`**: `E E^{(G̃)}_{u,σ} ≺ W ℓ_u (W ℓ_u η_u)^{-4}`, which is
`η_u^{-1}(W ℓ_u η_u)^{-3}`.

The proof is (5.134) and nothing else:

* `RBM.driftEG_eq_add` splits `E E^{(G̃)}` into `E[E^{(G)}(L-K, L-K)]` and `E^{(G)}(E(L-K), K)`;
* the second is deterministic and uses **(5.126)** (`h526`, Lemma 5.15) for the `1`-loop and
  **(2.59)** (`RBM.Band.norm_Kval_le`) for the `3`-loop — this is the cancellation inside the
  expectation, and it is where the `A^{-1}` that T182 showed is unavailable pathwise comes
  from;
* the first is pathwise, and uses **(2.78)** at lengths `1` and `3` (`RBM.EGInputs`) — the
  `3`-loop being `L - K` rather than `L` is where *its* `A^{-1}` comes from;
* both are instances of `RBM.norm_eG_two_le`, and the first passes through the first-moment
  bookkeeping outside the good set (`RBM.norm_integral_le_add_measure_compl`).

`hKd` is the decay of `K`; `RBM.exists_loopDecay_Kval` is its satisfiability witness. -/
theorem unifDetDom_driftEG (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv : ℝ}
    (hmeasLK : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (henvLK : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hintL : ∀ (N : ℕ) (v : ℝ) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω ⟨[b], [x]⟩) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖Step6.lk1 X E N p.1 p.2‖)
      (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) =>
        ‖driftEG X E N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale E N p.1)⁻¹ ^ 4) := by
  have hP := B.isProbabilityMeasure
  have hE : |E| < 2 := by linarith
  obtain ⟨CK, hCK0, hCK⟩ := B.norm_Kval_le hκ0 hκ1 hEκ (n := 3) (by norm_num)
  intro τ hτ
  set τ₁ : ℝ := τ / 8 with hτ₁def
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; linarith
  set D₁ : ℝ := 3 + Kenv + τ₁ + 4 with hD₁def
  have hD₁ : 0 < D₁ := by rw [hD₁def]; linarith
  filter_upwards [hin τ₁ hτ₁ D₁ hD₁ D₁ hD₁, h526 τ₁ hτ₁, hKd τ₁ hτ₁ D₁ hD₁,
    SumZeroDyn.flow_crude hE hs0 hst ht1 hc, hEnvpoly,
    eventually_rpow_neg_three_le_drift_target B hE hs0 hst ht1 hc,
    SumZeroDyn.eventually_const_mul_rpow_le (12 * exp 1 * (1 + CK))
      (show 3 * τ₁ < τ / 2 by rw [hτ₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 4
      (show 2 + τ₁ - D₁ < -(3 : ℝ) - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 1
      (show Kenv - D₁ < -(3 : ℝ) - 1 by rw [hD₁def]; linarith),
    SumZeroDyn.eventually_const_mul_rpow_le 2 (show τ / 2 < τ by linarith),
    eventually_ge_atTop 2] with
    N hgood h526N hKdN hcr hEnvN hlowN hmainN herr1N herr2N hfinN hN2
  obtain ⟨hLN, hWN, _, hu⟩ := hcr
  rintro ⟨v, q⟩
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set u : ℝ := (v : ℝ) with hudef
  have hu0 : 0 ≤ u := (hs0 N).trans v.2.1
  have hu1 : u < 1 := v.2.2.trans_lt (ht1 N)
  have hA : 1 ≤ B.scale E N u := (hu v).1
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hAi1 : (B.scale E N u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have hAi0 : (0 : ℝ) ≤ (B.scale E N u)⁻¹ := inv_nonneg.2 hA0.le
  have hell : (1 : ℝ) / 2 ≤ B.ell N u := by
    have := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
    rw [Band.ell]; linarith
  set Gt : ℝ := (B.W N : ℝ) * B.ell N u * (B.scale E N u)⁻¹ ^ 4 with hGtdef
  have hGt0 : 0 ≤ Gt := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hℓ0 : (0 : ℝ) ≤ B.ell N u := by linarith
    rw [hGtdef]; positivity
  have hGtlow : (N : ℝ) ^ (-(3 : ℝ)) ≤ Gt := hlowN v
  set Krad : ℝ := (N : ℝ) ^ τ₁ with hKraddef
  set δ : ℝ := (N : ℝ) ^ (-D₁) with hδdef
  have hKrad1 : (1 : ℝ) ≤ Krad := Real.one_le_rpow hN1' hτ₁.le
  have hKrad0 : (0 : ℝ) ≤ Krad := by linarith
  have hδ0 : (0 : ℝ) ≤ δ := Real.rpow_nonneg hN0.le _
  have hWLδ0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) * δ := by
    have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    positivity
  -- the two integrability facts
  have hint1 : ∀ (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => lkPath X E N u ω ⟨[b], [x]⟩) B.P :=
    fun b x => integrable_lkPath_one X E N u b x (hintL N u b x)
  have hintLK : Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N u ω)
      (lkPath X E N u ω) (LoopData.idx (q.1, q.2))) B.P :=
    Integrable.mono' (integrable_const (Env N)) (hmeasLK N u q.1 q.2)
      (Filter.Eventually.of_forall fun ω => henvLK N u q.1 q.2 ω)
  -- the `L - K` half, pathwise on the good set
  set c₁ : ℝ := 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
    + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad with hc₁def
  have hc₁0 : 0 ≤ c₁ := by
    have h1 : (0 : ℝ) ≤ 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt := by positivity
    have h2 : (0 : ℝ) ≤ 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad := by positivity
    rw [hc₁def]; linarith
  have hptLK : ∀ ω ∈ EGInputs X E s t N Krad δ Krad,
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2))‖ ≤ c₁ := by
    intro ω hω
    obtain ⟨hDd, hΨ1, hΨ3⟩ := hω v
    have hxi1 : 0 ≤ X.xiLK E N u ω 1 := X.xiLK_nonneg hA0.le
    have hxi3 : 0 ≤ X.xiLK E N u ω 3 := X.xiLK_nonneg hA0.le
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖lkPath X E N u ω ⟨[b], [x]⟩‖ ≤ X.xiLK E N u ω 1 * (B.scale E N u)⁻¹ := by
      intro b x
      have := DriftBound.norm_lk_le X E N u ω hA0.ne' (⟨[b], [x]⟩ : LoopIdx (ZMod (B.L N)))
        rfl (j := 1) rfl
      rwa [pow_one] at this
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
        ‖lkPath X E N u ω J‖ ≤ (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
          * (B.scale E N u)⁻¹ ^ 2 := by
      intro J hJ hlen
      have := DriftBound.norm_lk_le X E N u ω hA0.ne' J hJ hlen
      calc ‖lkPath X E N u ω J‖ ≤ X.xiLK E N u ω 3 * (B.scale E N u)⁻¹ ^ 3 := this
        _ = (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹) * (B.scale E N u)⁻¹ ^ 2 := by ring
    have hCΦ : X.xiLK E N u ω 1 * (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
        ≤ (Krad * Krad) * (B.scale E N u)⁻¹ := by
      have h1 : X.xiLK E N u ω 1 * X.xiLK E N u ω 3 ≤ Krad * Krad :=
        mul_le_mul hΨ1 hΨ3 hxi3 hKrad0
      calc X.xiLK E N u ω 1 * (X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
          = (X.xiLK E N u ω 1 * X.xiLK E N u ω 3) * (B.scale E N u)⁻¹ := by ring
        _ ≤ (Krad * Krad) * (B.scale E N u)⁻¹ := mul_le_mul_of_nonneg_right h1 hAi0
    exact norm_eG_two_le N (lkPath X E N u ω) (lkPath X E N u ω) q.1 q.2
      (Ξ := X.xiLK E N u ω 1) (Φ := X.xiLK E N u ω 3 * (B.scale E N u)⁻¹)
      (C := Krad * Krad) (Ξb := Krad)
      hE hu1 hA hell hKrad1 hδ0 hxi1 (by positivity) hX hY hDd hCΦ hΨ1
  have hbad : (B.P (EGInputs X E s t N Krad δ Krad)ᶜ).toReal ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hδ0 hgood
  have hLKbound : ‖∫ ω, Decay.eG (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
      (LoopData.idx (q.1, q.2)) ∂B.P‖ ≤ c₁ + Env N * δ := by
    have := norm_integral_le_add_measure_compl (P := B.P)
      (f := fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N u ω) (lkPath X E N u ω)
        (LoopData.idx (q.1, q.2)))
      (hmeasLK N u q.1 q.2) (G := EGInputs X E s t N Krad δ Krad) hc₁0 hptLK
      (fun ω => henvLK N u q.1 q.2 ω)
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbad (hEnv0 N)
    linarith
  -- the `K` half, deterministic
  set c₂ : ℝ := 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt
    + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad with hc₂def
  have hKbound : ‖Decay.eG (B.L N) (B.W N) (fun J => ∫ ω, lkPath X E N u ω J ∂B.P)
      (B.Kval E N u) (LoopData.idx (q.1, q.2))‖ ≤ c₂ := by
    have hX : ∀ (b : Bool) (x : ZMod (B.L N)),
        ‖(fun J => ∫ ω, lkPath X E N u ω J ∂B.P) ⟨[b], [x]⟩‖
          ≤ (Krad * (B.scale E N u)⁻¹) * (B.scale E N u)⁻¹ := by
      intro b x
      have heq := norm_integral_lkPath_one X E N u b x (hintL N u true x)
      have hle : ‖Step6.lk1 X E N u x‖ ≤ Krad * (B.scale E N u)⁻¹ ^ 2 := h526N (v, x)
      calc ‖(fun J => ∫ ω, lkPath X E N u ω J ∂B.P) ⟨[b], [x]⟩‖
          = ‖Step6.lk1 X E N u x‖ := heq
        _ ≤ Krad * (B.scale E N u)⁻¹ ^ 2 := hle
        _ = (Krad * (B.scale E N u)⁻¹) * (B.scale E N u)⁻¹ := by ring
    have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 3 →
        ‖B.Kval E N u J‖ ≤ CK * (B.scale E N u)⁻¹ ^ 2 := by
      intro J hJ hlen
      have := hCK N u hu0 hu1 J hJ hlen
      simpa using this
    exact norm_eG_two_le N (fun J => ∫ ω, lkPath X E N u ω J ∂B.P) (B.Kval E N u) q.1 q.2
      (Ξ := Krad * (B.scale E N u)⁻¹) (Φ := CK) (C := Krad * CK) (Ξb := Krad)
      hE hu1 hA hell hKrad1 hδ0 (by positivity) (by positivity) hX hY (hKdN v)
      (le_of_eq (by ring)) (mul_le_of_le_one_right hKrad0 hAi1)
  -- assemble
  have hsplit := driftEG_eq_add X E N u q.1 q.2 hint1 hintLK
  have htot : ‖driftEG X E N v q.1 q.2‖ ≤ (c₁ + Env N * δ) + c₂ := by
    rw [show driftEG X E N v q.1 q.2 = driftEG X E N u q.1 q.2 from rfl, hsplit]
    exact (norm_add_le _ _).trans (add_le_add hLKbound hKbound)
  refine htot.trans ?_
  -- the `Ξ`-bookkeeping: one main term, two errors
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
    have h2 : (N : ℝ) ^ (2 : ℝ) = (N : ℝ) * (N : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hW0 : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ B.L N := Nat.cast_nonneg _
    rw [h2]
    exact mul_le_mul hWN hLN hL0 (hW0.trans hWN)
  have hmain : 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
      + 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt ≤ (N : ℝ) ^ (τ / 2) * Gt := by
    have hk3 : Krad ^ 3 = (N : ℝ) ^ (3 * τ₁) := by
      rw [hKraddef, ← Real.rpow_natCast ((N : ℝ) ^ τ₁) 3, ← Real.rpow_mul hN0.le]
      norm_num [mul_comm]
    have hstep : 4 * exp 1 * (Krad + 2) * (Krad * Krad)
        + 4 * exp 1 * (Krad + 2) * (Krad * CK)
        ≤ 12 * exp 1 * (1 + CK) * (N : ℝ) ^ (3 * τ₁) := by
      rw [← hk3]
      have he : (0 : ℝ) ≤ exp 1 := (exp_pos 1).le
      have h1 : Krad + 2 ≤ 3 * Krad := by linarith
      have h2 : Krad + CK ≤ Krad * (1 + CK) := add_le_mul_one_add hKrad1 hCK0
      have hn1 : (0 : ℝ) ≤ Krad * (Krad + CK) := mul_nonneg hKrad0 (by linarith)
      have hinner : (Krad + 2) * (Krad * (Krad + CK))
          ≤ (3 * Krad) * (Krad * (Krad * (1 + CK))) := by
        calc (Krad + 2) * (Krad * (Krad + CK)) ≤ (3 * Krad) * (Krad * (Krad + CK)) :=
              mul_le_mul_of_nonneg_right h1 hn1
          _ ≤ (3 * Krad) * (Krad * (Krad * (1 + CK))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              exact mul_le_mul_of_nonneg_left h2 hKrad0
      calc 4 * exp 1 * (Krad + 2) * (Krad * Krad)
            + 4 * exp 1 * (Krad + 2) * (Krad * CK)
          = (4 * exp 1) * ((Krad + 2) * (Krad * (Krad + CK))) := by ring
        _ ≤ (4 * exp 1) * ((3 * Krad) * (Krad * (Krad * (1 + CK)))) :=
            mul_le_mul_of_nonneg_left hinner (by positivity)
        _ = 12 * exp 1 * (1 + CK) * Krad ^ 3 := by ring
    calc 4 * exp 1 * (Krad + 2) * (Krad * Krad) * Gt
          + 4 * exp 1 * (Krad + 2) * (Krad * CK) * Gt
        = (4 * exp 1 * (Krad + 2) * (Krad * Krad)
            + 4 * exp 1 * (Krad + 2) * (Krad * CK)) * Gt := by ring
      _ ≤ (12 * exp 1 * (1 + CK) * (N : ℝ) ^ (3 * τ₁)) * Gt :=
          mul_le_mul_of_nonneg_right hstep hGt0
      _ ≤ (N : ℝ) ^ (τ / 2) * Gt := mul_le_mul_of_nonneg_right hmainN hGt0
  have herr1 : 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
      + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := by
    have he : (N : ℝ) ^ (2 : ℝ) * δ * Krad = (N : ℝ) ^ (2 + τ₁ - D₁) := by
      rw [hδdef, hKraddef, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hmono : 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad
        + 2 * ((B.W N : ℝ) * (B.L N : ℝ) * δ) * Krad ≤ 4 * ((N : ℝ) ^ (2 : ℝ) * δ * Krad) := by
      have h1 : (B.W N : ℝ) * (B.L N : ℝ) * δ ≤ (N : ℝ) ^ (2 : ℝ) * δ :=
        mul_le_mul_of_nonneg_right hWL hδ0
      exact two_mul_add_two_mul_le hKrad0 h1
    refine hmono.trans ?_
    rw [he]
    exact herr1N
  have herr2 : Env N * δ ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := by
    have h1 : Env N * δ ≤ (N : ℝ) ^ Kenv * δ := mul_le_mul_of_nonneg_right hEnvN hδ0
    have he : (N : ℝ) ^ Kenv * δ = (N : ℝ) ^ (Kenv - D₁) := by
      rw [hδdef, ← Real.rpow_add hN0, sub_eq_add_neg]
    refine h1.trans ?_
    rw [he]
    calc (N : ℝ) ^ (Kenv - D₁) = 1 * (N : ℝ) ^ (Kenv - D₁) := by ring
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := herr2N
  have hsumerr : (N : ℝ) ^ (-(3 : ℝ) - 1) + (N : ℝ) ^ (-(3 : ℝ) - 1) ≤ Gt := by
    have hmul : (N : ℝ) ^ (-(3 : ℝ) - 1) * (N : ℝ) ^ (1 : ℝ) = (N : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(3 : ℝ) - 1) := Real.rpow_nonneg hN0.le _
    have h2 : (N : ℝ) ^ (-(3 : ℝ) - 1) + (N : ℝ) ^ (-(3 : ℝ) - 1) ≤ (N : ℝ) ^ (-(3 : ℝ)) := by
      rw [← hmul, Real.rpow_one]
      exact add_self_le_mul_two_le hp hN2'
    exact h2.trans hGtlow
  have hfin : (N : ℝ) ^ (τ / 2) * Gt + Gt ≤ (N : ℝ) ^ τ * Gt := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (by linarith)
    have h2 : (N : ℝ) ^ (τ / 2) + 1 ≤ (N : ℝ) ^ τ := by linarith [hfinN]
    exact mul_add_le_mul_of_add_one_le h2 hGt0
  rw [hc₁def, hc₂def]
  exact final_arith_eg hmain herr1 herr2 hsumerr hfin

/-- **(5.135)** in the shape `RBM.Step6.DriftBound` demands: `E E^{(G̃)} ≺ η_u^{-1} A_u^{-3}`. -/
theorem driftBound_driftEG (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {Env : ℕ → ℝ} {Kenv : ℝ}
    (hmeasLK : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (henvLK : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    (hintL : ∀ (N : ℕ) (v : ℝ) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω ⟨[b], [x]⟩) B.P)
    (h526 : UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖Step6.lk1 X E N p.1 p.2‖)
      (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    (hin : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ))) :
    Step6.DriftBound B E s t (driftEG X E) :=
  Step6.driftBound_of_5133 (by linarith : |E| < 2) ht1
    (unifDetDom_driftEG X hκ0 hκ1 hEκ hs0 hst ht1 hc hmeasLK henvLK hEnv0 hKenv hEnvpoly
      hintL h526 hKd hin)

/-! ### Satisfiability and shape checks -/

/-- `L - K` decays wherever `L` and `K` do, at twice the budget. -/
theorem loopDecay_lkPath (X : Sample B) (E : ℝ) (N : ℕ) (v : ℝ) (ω : Ω) {n : ℕ} {ℓ δ : ℝ}
    (hL : Decay.LoopDecay (B.L N) n ℓ δ (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)))
    (hK : Decay.LoopDecay (B.L N) n ℓ δ (B.Kval E N v)) :
    Decay.LoopDecay (B.L N) n ℓ (δ + δ) (lkPath X E N v ω) := by
  intro J hJ hJn x hx y hy hxy
  have h1 := hL J hJ hJn x hx y hy hxy
  have h2 := hK J hJ hJn x hx y hy hxy
  calc ‖lkPath X E N v ω J‖
      = ‖gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) J - B.Kval E N v J‖ := rfl
    _ ≤ ‖gloop (B.L N) (B.W N) (X.H N v ω) (zt E v) J‖ + ‖B.Kval E N v J‖ := norm_sub_le _ _
    _ ≤ δ + δ := add_le_add h1 h2

/-- **The satisfiability check for `RBM.EGInputs`.**  Its decay conjunct is *implied* by the
decay T182 already assumes (`RBM.FDInputs` carries the length-`3` decay of `L`) together with
the decay of `K` (`hKd`, whose own witness is `RBM.exists_loopDecay_Kval`); only the power
counts (5.76) at lengths `1` and `3` are new, and those are the same class of input as T182's
`X.xiLK ... 2 ≤ Ψ` in `RBM.QuadInputs`.  So `hinG` of `RBM.unifDetDom_driftEG` does not ask for
anything Lemma 5.9 fails to supply, and in particular `RBM.EGInputs` is not empty by
construction. -/
theorem mem_egInputs_of (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (N : ℕ) {Krad δ M Ψ : ℝ} {ω : Ω}
    (hFD : ω ∈ FDInputs X E s t N Krad δ M)
    (hK : ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * Krad) δ (B.Kval E N (v : ℝ)))
    (hx1 : ∀ v : TimeIcc s t N, X.xiLK E N (v : ℝ) ω 1 ≤ Ψ)
    (hx3 : ∀ v : TimeIcc s t N, X.xiLK E N (v : ℝ) ω 3 ≤ Ψ) :
    ω ∈ EGInputs X E s t N Krad (δ + δ) Ψ := by
  intro v
  exact ⟨loopDecay_lkPath X E N (v : ℝ) ω (hFD v).2.1 (hK v), hx1 v, hx3 v⟩

/-- **The exponent check for (5.135)'s shape**: with `A = W ℓ η`, `W ℓ A^{-4} = η^{-1} A^{-3}`.
Checked at `W = 4`, `ℓ = 5`, `η = 1/10` (so `A = 2`), where both sides are `5/4`; the general
statement is `RBM.Step6.W_mul_ell_mul_scale_inv_pow_four`. -/
theorem scale_shape_check :
    (4 : ℝ) * 5 * ((4 : ℝ) * 5 * (1 / 10))⁻¹ ^ 4 = ((1 : ℝ) / 10)⁻¹ * ((4 : ℝ) * 5 * (1 / 10))⁻¹ ^ 3
      ∧ (4 : ℝ) * 5 * ((4 : ℝ) * 5 * (1 / 10))⁻¹ ^ 4 = 5 / 4 := by
  norm_num

/-- **The check that the gain is exactly one power of `A`.**  T182's pathwise shape is
`η^{-1} A^{-2}`; the target (5.133)/(5.135) is `η^{-1} A^{-3}`.  At the same numerical point
(`A = 2`) the pathwise shape is `5/2`, which is `A = 2` times `5/4`.  So (5.134) has to gain
one factor `A` — and not two. -/
theorem pathwise_shape_is_one_power_weaker :
    ((1 : ℝ) / 10)⁻¹ * ((4 : ℝ) * 5 * (1 / 10))⁻¹ ^ 2
      = ((4 : ℝ) * 5 * (1 / 10)) * (((1 : ℝ) / 10)⁻¹ * ((4 : ℝ) * 5 * (1 / 10))⁻¹ ^ 3)
    ∧ ((1 : ℝ) / 10)⁻¹ * ((4 : ℝ) * 5 * (1 / 10))⁻¹ ^ 2 = 5 / 2 := by
  norm_num

end EGDom

/-! ### Step 6 with both drift tensors pinned and **all** their size obligations discharged -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

set_option maxHeartbeats 1000000 in
/-- **(2.80) for the pinned drift pair, with `hG` discharged.**

Compared with `RBM.sharpExpect_step6_driftSplit` (T182), the last hypothesis that was still a
statement *about the drift* is gone: (5.134)'s `hG` is replaced by the proved (5.135)
`RBM.driftBound_driftEG`, so the consumer is `RBM.Step6.sharpExpect_of_hierarchy` rather than
`RBM.Step6.sharpExpect_step6`.  Two of T182's hypotheses disappear with it — `hq13`
(`E[(L-K)_1(L-K)_3] ≺ A^{-4}`) and `hint2` — because the route through (5.134) does not need
the mixed second moment: the `L-K` half of (5.134) is pathwise.

What remains never mentions the drift: (5.132), (5.127) and `hq11` (which produce Lemma 5.15
through `RBM.Step6.lemma515`), Lemma 5.9's decay and the power counts (5.76), the crude
envelope with its measurability, and integrability. -/
theorem sharpExpect_step6_driftEG (X : Sample B) {E κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : |E| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    -- the analytic inputs of the hierarchy (T140/T141/T70)
    (hcont : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      ContinuousOn (fun q : ℝ => Step6.lkT X E N q σ b) (Set.Icc (s N) ((u : ℝ))))
    (hintL2 : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => X.Lval E N v ω (LoopData.idx (σ, b))) B.P)
    (hintQ : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, b))) B.P)
    (hintG : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      Integrable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, b))) B.P)
    (hEL : ∀ N (v : ℝ), 0 < v → v < 1 → ∀ (σ : Fin 2 → Bool) (b : LoopArg (B.L N) 2),
      HasDerivAt (fun q : ℝ => X.ELval E N q (LoopData.idx (σ, b)))
        (∫ ω, (Gauss.eGterm (B.L N) (B.W N) (mSigma E) (X.H N v ω) (zt E v)
            (LoopData.idx (σ, b))
          + primRhs (B.L N) (B.W N) (X.Lval E N v ω) (LoopData.idx (σ, b))) ∂B.P) v)
    (hintU1 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftELK X E N v σ) a) volume (s N) (u : ℝ))
    (hintU2 : ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      IntervalIntegrable (fun v : ℝ => Uker (B.L N) (xiOf (mSigma E) σ) ((v : ℝ) : ℂ)
        (((u : ℝ)) : ℂ) (driftEG X E N v σ) a) volume (s N) (u : ℝ))
    -- measurability and the crude envelope
    {Env : ℕ → ℝ} {Kenv KM : ℝ}
    (hmeasQ : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => primBil (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (hmeasG : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))) B.P)
    (hmeasLK : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
      AEStronglyMeasurable (fun ω => Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (lkPath X E N v ω) (LoopData.idx (σ, a))) B.P)
    (henvQ : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖primBil (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvG : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω)
        (gloop (B.L N) (B.W N) (X.H N v ω) (zt E v)) (LoopData.idx (σ, a))‖ ≤ Env N)
    (henvLK : ∀ (N : ℕ) (v : ℝ) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2) (ω : Ω),
      ‖Decay.eG (B.L N) (B.W N) (lkPath X E N v ω) (lkPath X E N v ω)
        (LoopData.idx (σ, a))‖ ≤ Env N)
    (hEnv0 : ∀ N, 0 ≤ Env N) (hKenv : 0 ≤ Kenv) (hKM : 0 ≤ KM)
    (hEnvpoly : ∀ᶠ N : ℕ in atTop, Env N ≤ (N : ℝ) ^ Kenv)
    -- Lemma 5.9 and the counts (5.76)
    (hlk : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
      FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (Step6.lkT X E N (s N) σ))
    (hin59 : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      (B.P (FDInputs X E s t N ((B.W N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ KM))ᶜ).toReal
        ≤ (N : ℝ) ^ (-D))
    (hinQ : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      QuadInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hinG : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (fun N =>
      EGInputs X E s t N ((N : ℝ) ^ τ) ((N : ℝ) ^ (-D)) ((N : ℝ) ^ τ)))
    (hKd : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ v : TimeIcc s t N,
      Decay.LoopDecay (B.L N) 3 (B.ell N (v : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
        (B.Kval E N (v : ℝ)))
    -- (5.132), (5.127), `quad11`, and the `1`-loop integrability
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr E N (s N) u.idx)
      (fun N _ => (B.scale E N (s N))⁻¹ ^ 3))
    (h527 : Step6.Eq527 X E s t)
    (hq11 : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X E N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale E N p.1)⁻¹ ^ 2))
    (hintL1 : ∀ (N : ℕ) (v : ℝ) (b : Bool) (x : ZMod (B.L N)),
      Integrable (fun ω => X.Lval E N v ω ⟨[b], [x]⟩) B.P) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr E N p.1 p.2.idx)
      (fun N _ => (B.scale E N (t N))⁻¹ ^ 3) := by
  have hE : |E| < 2 := by linarith
  have hE2 : |E| ≤ 2 := by linarith
  exact Step6.sharpExpect_of_hierarchy X hE hs0 hst ht1 hc
    (hierarchy_driftSplit X hE2 hs0 ht1 hcont hintL2 hintQ hintG hEL hintU1 hintU2)
    (fastDecayHyp_driftSplit X hE hs0 hst ht1 hc hmeasQ hmeasG henvQ henvG hEnv0 hKenv
      hEnvpoly hKM hlk hin59)
    h5132
    (Step6.driftBound_of_5133 hE ht1
      (unifDetDom_driftELK X hE hs0 hst ht1 hc hmeasQ henvQ hEnv0 hKenv hEnvpoly
        (by norm_num) (eventually_rpow_neg_three_le_drift_target B hE hs0 hst ht1 hc) hinQ))
    (driftBound_driftEG X hκ0 hκ1 hEκ hs0 hst ht1 hc hmeasLK henvLK hEnv0 hKenv hEnvpoly
      hintL1 (Step6.lemma515 X hκ0 hκ1 hEκ hs0 ht1 h527 hq11) hKd hinG)

end Assembly

end RBM

