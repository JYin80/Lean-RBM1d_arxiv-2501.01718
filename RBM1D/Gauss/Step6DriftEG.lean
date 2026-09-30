/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6DriftSplit

/-!
# (5.134)–(5.135) for the pinned `E E^{(G̃)}`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.8, (5.134)–(5.135), for the tensor `RBM.driftEG` defined in
`RBM1D/Gauss/Step6DriftSplit.lean`.

`RBM1D/Gauss/Step6DriftSplit.lean` shows that the `E^{(G̃)}` half of the drift is, **pathwise**,
exactly one factor `A = W ℓ_u η_u` short of (5.133): the third line of (5.77) gives
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
full.  This file proves the algebraic and pointwise ingredients of that splitting.

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

## No free data

`RBM.driftEG` is untouched — the definition is used verbatim and `RBM.driftEG_eq_add` is a
theorem about it, not a redefinition.  Nothing here is an `axiom` and no proof is left open.
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

Applied with `Ξ = Ξ^{(L-K)}_{u,1}`, `Φ = Ξ^{(L)}_{u,3}`, whose product carries **no** extra
`A^{-1}`, the third line is one factor `A` weaker than (5.133).  Here the product `Ξ · Φ` is only
assumed to be `≤ C A^{-1}`, which is exactly the gain that the two halves of (5.134) supply — the
`K` half through (5.126) (`Ξ = |E(L-K)_1| A ≤ Ψ A^{-1}`), the `L-K` half through (2.78) at length
`3` (`Φ = Ξ^{(L-K)}_{u,3} A^{-1}`).  The single identity spent is `RBM.Decay.mul_add_one_div_le`,
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

/-! ### Satisfiability and shape checks -/

end EGDom

/-! ### Step 6 with both drift tensors pinned and **all** their size obligations discharged -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

end Assembly

end RBM

