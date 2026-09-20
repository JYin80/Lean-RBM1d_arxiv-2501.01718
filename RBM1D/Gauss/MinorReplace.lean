/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.EntryBound
import RBM1D.Flow.Hypotheses

/-!
# The minor replacement error `|G_{ll} - G^{(k)}_{ll}| ≺ Ψ²`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*: the cost of replacing `G` by the minor `G^{(k)}` in an entry with indices different
from `k`.  This is the error term of the vanishing lemma of §4 (the self-contained proof of the
fluctuation averaging (4.12)).

Everything rests on **(4.9)**, which is already proved in `RBM1D/Green/Minor.lean`
(`RBM.inv_minorMat`) and restated on the full index set in `RBM1D/Green/EntryBound.lean`
(`RBM.greenMinor`, `RBM.greenMinor_sub`):

  `G^{(k)}_{jl} - G_{jl} = - G_{jk} G_{kl} / G_{kk}`.

So the replacement error is *exactly* a product of two entries divided by a diagonal entry.
The two probabilistic inputs are therefore

* `|G_{jk}| ≺ Ψ` for `j ≠ k` — the off-diagonal part of the local law (2.75) of Step 2
  (`RBM.Steps.localLaw`, `RBM.Hierarchy.Step2.localLaw`), converted to the shape used here by
  `RBM.Gauss.stochDom_offdiag_of_localLaw`;
* a lower bound `|G_{kk}| ≥ 1/2`, which is *not* taken as a separate hypothesis: it is already
  contained in the event `Ω(t,c) = {‖G - m‖_max ≤ δ}` of (4.1) (`RBM.goodSet`), through
  `RBM.GoodEvent.half_le_norm_diag`.  Every statement below therefore comes in two forms, one
  with the indicator `1_Ω` and one without it, the latter under
  `hΩ : RBM.HighProb P (RBM.goodSet H z m δ)` — exactly the pattern of Lemma 4.1 in
  `RBM1D/Green/EntryBound.lean` (`RBM.entry_bound_stochDom_of_highProb`).

## What is proved

The general statement is for a **triple** `(k, j, l)` with `j ≠ k` and `l ≠ k`
(`RBM.Gauss.MinorTriple`); the diagonal case `j = l` of the ticket is the specialization
`RBM.Gauss.minorReplace_diag_stochDom`.

* `RBM.Gauss.norm_greenMinor_sub_le_sq` — the deterministic core: on the event `Ω`,
  `|G^{(k)}_{jl} - G_{jl}| ≤ 2 Ψ²` as soon as `|G_{jk}|, |G_{kl}| ≤ Ψ`.
* `RBM.Gauss.minorReplace_indicator_stochDom`, `RBM.Gauss.minorReplace_stochDom` —
  `|G^{(k)}_{jl} - G_{jl}| ≺ Ψ²`, with and without the indicator.
* `RBM.Gauss.minorReplace_diag_stochDom` — `|G_{ll} - G^{(k)}_{ll}| ≺ Ψ²` for `l ≠ k`, the
  statement of the ticket.
* `RBM.Gauss.minorGreen_localLaw_indicator_stochDom`,
  `RBM.Gauss.minorGreen_localLaw_stochDom` — the **local law for the minor**,
  `|G^{(k)}_{jl} - m δ_{jl}| ≺ Ψ² + Ψ`.  This is what the vanishing lemma needs after it has
  replaced `Z_{k_i} = (1 - E_{k_i})(G_{k_i k_i} - m)` by its `G^{(k₁)}` version: the replaced
  factors obey the same bound as the original ones.  (The right-hand side is `Ψ² + Ψ` and not
  `Ψ`: no hypothesis `Ψ ≤ 1` is assumed here, and `Ψ² + Ψ ≤ 2 Ψ` whenever it holds.)

## Deviation from the paper

None in the statements: (4.9) is an identity and the two inputs are the paper's own.  The only
choice is bookkeeping — the lower bound on `|G_{kk}|` is read off the event (4.1) rather than
assumed separately, which is how the paper uses it too (p. 49-50).
-/

namespace RBM.Gauss

open Filter MeasureTheory Matrix

/-! ### The deterministic layer -/

section Det

variable {n : Type*} [DecidableEq n]

/-- Entries of `G - m` are `G_{ij} - m δ_{ij}`: the bridge between the `‖G - m • 1‖_max` shape
of the local law (2.75) (`RBM.Sample.llErr`) and the `if`-shape of `RBM.GoodEvent`. -/
theorem sub_smul_one_apply (A : Matrix n n ℂ) (m : ℂ) (i j : n) :
    (A - m • (1 : Matrix n n ℂ)) i j = A i j - (if i = j then m else 0) := by
  by_cases h : i = j
  · subst h
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, h]

omit [DecidableEq n] in
/-- **(4.9) for a diagonal entry**: the replacement error is exactly `G_{lk} G_{kl} / G_{kk}`.
This is `RBM.greenMinor_sub` at `j = l`, recorded for readability. -/
theorem greenMinor_diag_sub (G : Matrix n n ℂ) (k l : n) :
    greenMinor G k l l - G l l = -(G l k * G k l / G k k) :=
  greenMinor_sub G k l l

/-- **The deterministic core of the replacement estimate.**  On the event `Ω(t,c)` of (4.1)
(which supplies `|G_{kk}| ≥ 1/2`), the error of replacing `G` by the minor `G^{(k)}` in the entry
`(j, l)` is at most `2 Ψ²`, where `Ψ` bounds the two entries `G_{jk}` and `G_{kl}` that (4.9)
produces.  Both of those are off-diagonal when `j ≠ k` and `l ≠ k`, so the local law gives
`Ψ`. -/
theorem norm_greenMinor_sub_le_sq {G : Matrix n n ℂ} {m : ℂ} {δ Ψ : ℝ} (h : GoodEvent G m δ)
    (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2) (k j l : n) (hjk : ‖G j k‖ ≤ Ψ) (hkl : ‖G k l‖ ≤ Ψ) :
    ‖greenMinor G k j l - G j l‖ ≤ 2 * Ψ ^ 2 := by
  have h0 : (0 : ℝ) ≤ ‖G k l‖ := norm_nonneg _
  have hΨ : (0 : ℝ) ≤ Ψ := le_trans (norm_nonneg _) hjk
  have h3 : ‖G j k‖ * ‖G k l‖ ≤ Ψ * Ψ := mul_le_mul hjk hkl h0 hΨ
  have hb := h.norm_greenMinor_sub_le hm hδ k j l
  nlinarith

end Det

/-! ### The stochastic layer -/

section Stoch

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {L W : ℕ → ℕ} [∀ N, NeZero (L N)]

/-- Triples `(k, j, l)` of indices with `j ≠ k` and `l ≠ k`: the row/column `k` removed by the
minor, and the two indices of the entry `G^{(k)}_{jl}`.  The diagonal case of the vanishing
lemma is `j = l`. -/
abbrev MinorTriple (L W : ℕ → ℕ) (N : ℕ) : Type :=
  {p : BIdx L W N × BIdx L W N × BIdx L W N // p.2.1 ≠ p.1 ∧ p.2.2 ≠ p.1}

/-- **From the local law to the off-diagonal input.**  The local law (2.75) of Step 2 bounds
`‖G - m‖_max`, i.e. `|G_{ij} - m δ_{ij}|`, uniformly over *all* pairs; off the diagonal the
subtracted term vanishes, which is the hypothesis `hoff` of everything below. -/
theorem stochDom_offdiag_of_localLaw (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (z m : ℂ)
    {Ψ : ℕ → ℝ}
    (hll : StochDom P
      (fun N (ij : BIdx L W N × BIdx L W N) ω =>
        ‖green (H N ω) z ij.1 ij.2 - (if ij.1 = ij.2 then m else 0)‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N) := by
  refine StochDom.of_le_left (fun N v ω => ?_)
    (hll.precomp_param fun N (v : OffPair L W N) => (v.1.1, v.1.2))
  exact le_of_eq (by rw [ite_eq_right v.2, sub_zero])

/-- **The replacement error, with the indicator of the event (4.1).**

`1_Ω |G^{(k)}_{jl} - G_{jl}| ≺ Ψ²`, uniformly over triples `(k, j, l)` with `j ≠ k`, `l ≠ k`.

The only probabilistic input is `hoff`, the off-diagonal local law `|G_{ij}| ≺ Ψ` for `i ≠ j`
(from (2.75), see `RBM.Gauss.stochDom_offdiag_of_localLaw`); the lower bound on `|G_{kk}|` comes
from the event `Ω(t,c)` itself. -/
theorem minorReplace_indicator_stochDom (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    {z m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {Ψ : ℕ → ℝ}
    (hoff : StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (u : MinorTriple L W N) ω => (goodSet H z m δ N).indicator
        (fun ω => ‖greenMinor (green (H N ω) z) u.1.1 u.1.2.1 u.1.2.2
          - green (H N ω) z u.1.2.1 u.1.2.2‖) ω)
      (fun N _ _ => Ψ N ^ 2) := by
  refine StochDom.of_det hoff (fun N _ _ => sq_nonneg _) hδ0 hc₀ hδ
    (by norm_num : (0 : ℝ) < 1 / 2) 2 2 ?_
  intro N ω Φ hΦ1 _ hδε hAB u
  obtain ⟨⟨k, j, l⟩, hjk, hlk⟩ := u
  have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
  by_cases hω : ω ∈ goodSet H z m δ N
  · rw [Set.indicator_of_mem hω]
    have hG : GoodEvent (green (H N ω) z) m (δ N) := hω
    have h1 : ‖green (H N ω) z j k‖ ≤ Φ * Ψ N := hAB ⟨(j, k), hjk⟩
    have h2 : ‖green (H N ω) z k l‖ ≤ Φ * Ψ N := hAB ⟨(k, l), hlk.symm⟩
    calc ‖greenMinor (green (H N ω) z) k j l - green (H N ω) z j l‖
        ≤ 2 * (Φ * Ψ N) ^ 2 := norm_greenMinor_sub_le_sq hG hm hδε k j l h1 h2
      _ = 2 * Φ ^ 2 * Ψ N ^ 2 := by ring
  · rw [Set.indicator_of_notMem hω]
    positivity

/-- **The replacement error** (4.9), without the indicator, under (4.4): if the event `Ω(t,c)`
of (4.1) holds with high probability, then

  `|G^{(k)}_{jl} - G_{jl}| ≺ Ψ²`  uniformly over `j ≠ k`, `l ≠ k`. -/
theorem minorReplace_stochDom (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    {z m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) (hΩ : HighProb P (goodSet H z m δ))
    {Ψ : ℕ → ℝ}
    (hoff : StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (u : MinorTriple L W N) ω =>
        ‖greenMinor (green (H N ω) z) u.1.1 u.1.2.1 u.1.2.2
          - green (H N ω) z u.1.2.1 u.1.2.2‖)
      (fun N _ _ => Ψ N ^ 2) :=
  StochDom.of_indicator hΩ (minorReplace_indicator_stochDom H hm hδ0 hc₀ hδ hoff)

/-- **The statement of the ticket**: `|G_{ll} - G^{(k)}_{ll}| ≺ Ψ²` for `l ≠ k`.

The parameter is a pair `(l, k)` with `l ≠ k` (`RBM.OffPair`); the quantity dominated is
`|G^{(k)}_{ll} - G_{ll}|`, which has the same modulus. -/
theorem minorReplace_diag_stochDom (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    {z m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) (hΩ : HighProb P (goodSet H z m δ))
    {Ψ : ℕ → ℝ}
    (hoff : StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (v : OffPair L W N) ω =>
        ‖greenMinor (green (H N ω) z) v.1.2 v.1.1 v.1.1 - green (H N ω) z v.1.1 v.1.1‖)
      (fun N _ _ => Ψ N ^ 2) :=
  (minorReplace_stochDom H hm hδ0 hc₀ hδ hΩ hoff).precomp_param
    fun N (v : OffPair L W N) => ⟨(v.1.2, v.1.1, v.1.1), v.2, v.2⟩

/-- **The local law for the minor**, with the indicator of the event (4.1):

  `1_Ω |G^{(k)}_{jl} - m δ_{jl}| ≺ Ψ² + Ψ`  uniformly over `j ≠ k`, `l ≠ k`.

This is the second half of what the vanishing lemma consumes.  After replacing each factor
`Z_{k_i} = (1 - E_{k_i})(G_{k_i k_i} - m)` by the one built from `G^{(k₁)}`, the replaced factors
must still obey the local law; by (4.9) they do, at the cost of the replacement error. -/
theorem minorGreen_localLaw_indicator_stochDom
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    {z m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {Ψ : ℕ → ℝ} (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hoff : StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N))
    (hll : StochDom P
      (fun N (ij : BIdx L W N × BIdx L W N) ω =>
        ‖green (H N ω) z ij.1 ij.2 - (if ij.1 = ij.2 then m else 0)‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (u : MinorTriple L W N) ω => (goodSet H z m δ N).indicator
        (fun ω => ‖greenMinor (green (H N ω) z) u.1.1 u.1.2.1 u.1.2.2
          - (if u.1.2.1 = u.1.2.2 then m else 0)‖) ω)
      (fun N _ _ => Ψ N ^ 2 + Ψ N) := by
  refine StochDom.of_det (hoff.sumElim hll) (fun N _ _ => add_nonneg (sq_nonneg _) (hΨ0 N))
    hδ0 hc₀ hδ (by norm_num : (0 : ℝ) < 1 / 2) 2 2 ?_
  intro N ω Φ hΦ1 _ hδε hAB u
  obtain ⟨⟨k, j, l⟩, hjk, hlk⟩ := u
  have hΦ0 : (0 : ℝ) ≤ Φ := by linarith
  have hΨ := hΨ0 N
  by_cases hω : ω ∈ goodSet H z m δ N
  · rw [Set.indicator_of_mem hω]
    have hG : GoodEvent (green (H N ω) z) m (δ N) := hω
    have h1 : ‖green (H N ω) z j k‖ ≤ Φ * Ψ N := hAB (Sum.inl ⟨(j, k), hjk⟩)
    have h2 : ‖green (H N ω) z k l‖ ≤ Φ * Ψ N := hAB (Sum.inl ⟨(k, l), hlk.symm⟩)
    have h3 : ‖green (H N ω) z j l - (if j = l then m else 0)‖ ≤ Φ * Ψ N := hAB (Sum.inr (j, l))
    have hb := norm_greenMinor_sub_le_sq hG hm hδε k j l h1 h2
    have hmid : Φ * Ψ N ≤ 2 * Φ ^ 2 * Ψ N := by
      nlinarith [mul_nonneg (mul_nonneg hΦ0 hΨ) (by linarith : (0 : ℝ) ≤ 2 * Φ - 1)]
    calc ‖greenMinor (green (H N ω) z) k j l - (if j = l then m else 0)‖
        ≤ ‖greenMinor (green (H N ω) z) k j l - green (H N ω) z j l‖
          + ‖green (H N ω) z j l - (if j = l then m else 0)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (Φ * Ψ N) ^ 2 + Φ * Ψ N := add_le_add hb h3
      _ = 2 * Φ ^ 2 * Ψ N ^ 2 + Φ * Ψ N := by ring
      _ ≤ 2 * Φ ^ 2 * Ψ N ^ 2 + 2 * Φ ^ 2 * Ψ N := by linarith
      _ = 2 * Φ ^ 2 * (Ψ N ^ 2 + Ψ N) := by ring
  · rw [Set.indicator_of_notMem hω]
    have h4 : (0 : ℝ) ≤ Ψ N ^ 2 + Ψ N := add_nonneg (sq_nonneg _) hΨ
    nlinarith [sq_nonneg Φ]

/-- **The local law for the minor**, without the indicator, under (4.4):

  `|G^{(k)}_{jl} - m δ_{jl}| ≺ Ψ² + Ψ`  uniformly over `j ≠ k`, `l ≠ k`. -/
theorem minorGreen_localLaw_stochDom (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    {z m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) (hΩ : HighProb P (goodSet H z m δ))
    {Ψ : ℕ → ℝ} (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hoff : StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N))
    (hll : StochDom P
      (fun N (ij : BIdx L W N × BIdx L W N) ω =>
        ‖green (H N ω) z ij.1 ij.2 - (if ij.1 = ij.2 then m else 0)‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (u : MinorTriple L W N) ω =>
        ‖greenMinor (green (H N ω) z) u.1.1 u.1.2.1 u.1.2.2
          - (if u.1.2.1 = u.1.2.2 then m else 0)‖)
      (fun N _ _ => Ψ N ^ 2 + Ψ N) :=
  StochDom.of_indicator hΩ
    (minorGreen_localLaw_indicator_stochDom H hm hδ0 hc₀ hδ hΨ0 hoff hll)

/-- The diagonal case of the previous statement: `|G^{(k)}_{ll} - m| ≺ Ψ² + Ψ` for `l ≠ k`. -/
theorem minorGreen_localLaw_diag_stochDom (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ)
    {z m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) (hΩ : HighProb P (goodSet H z m δ))
    {Ψ : ℕ → ℝ} (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hoff : StochDom P
      (fun N (v : OffPair L W N) ω => ‖green (H N ω) z v.1.1 v.1.2‖)
      (fun N _ _ => Ψ N))
    (hll : StochDom P
      (fun N (ij : BIdx L W N × BIdx L W N) ω =>
        ‖green (H N ω) z ij.1 ij.2 - (if ij.1 = ij.2 then m else 0)‖)
      (fun N _ _ => Ψ N)) :
    StochDom P
      (fun N (v : OffPair L W N) ω =>
        ‖greenMinor (green (H N ω) z) v.1.2 v.1.1 v.1.1 - m‖)
      (fun N _ _ => Ψ N ^ 2 + Ψ N) := by
  have h := (minorGreen_localLaw_stochDom H hm hδ0 hc₀ hδ hΩ hΨ0 hoff hll).precomp_param
    fun N (v : OffPair L W N) => (⟨(v.1.2, v.1.1, v.1.1), v.2, v.2⟩ : MinorTriple L W N)
  refine StochDom.of_le_left (fun N v ω => ?_) h
  exact le_of_eq (by rw [ite_eq_left rfl])

end Stoch

end RBM.Gauss
