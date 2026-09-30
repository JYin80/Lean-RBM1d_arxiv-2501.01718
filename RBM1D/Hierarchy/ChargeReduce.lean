/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.StepGlue

/-!
# Reducing the four charges of (5.76) to the single charge `(+,+)`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, (2.76) and (5.76).

The a priori bound (2.76) is needed for **every** charge `σ ∈ {+,-}²`.  The definition (5.76)
of `Ξ^{(L-K)}_{t,2}` is a maximum over all `σ`, so Steps 3 and 4 need the bound at every charge,
while (2.76) is stated **only for `σ = (+,-)`** (in the paper the other charges at `m = 2` come
from the continuity argument in the proof of (2.77), §5.6).  This file reduces the four charges
to the two charges `(+,-)` and `(+,+)`.

Three of the four charges are free, by deterministic identities:

* `σ = (+,-)` is (2.76) itself;
* `σ = (-,+)` reduces to `(+,-)` by cyclicity of the trace (`RBM.gloop_rotate` for `L`,
  `RBM.kTwo_rotate` for `K`) — `RBM.ChargeReduce.lkErr_two_flip`;
* `σ = (-,-)` reduces to `(+,+)` by conjugation (`RBM.Gsig_conjTranspose`,
  `RBM.mSigma_false`) — `RBM.ChargeReduce.lkErr_two_const`.

## Main results

* `RBM.ChargeReduce.conj_Theta_apply` — `conj (Θ_ξ)_{ab} = (Θ_{conj ξ})_{ab}`: the propagator has
  real (indeed rational) matrix entries as a function of `ξ`.
* `RBM.ChargeReduce.conj_kTwo_const`, `RBM.ChargeReduce.conj_Kval_const` — `conj K_{u,(-,-),(a,b)}
  = K_{u,(+,+),(a,b)}`, from (2.57) `K = W⁻¹ m₁m₂ (Θ_{u m₁m₂})_{a₁a₂}` and `m(-) = conj m(+)`.
* `RBM.ChargeReduce.conj_Lval_const` — `conj L_{u,(-,-),(a,b)} = L_{u,(+,+),(a,b)}`, from
  `G(-)ᴴ = G(+)` at the *same* spectral parameter and cyclicity of the trace.
* `RBM.ChargeReduce.Lval_two_flip`, `RBM.ChargeReduce.Kval_two_flip` — reading a `2`-loop from
  the other end.
* `RBM.ChargeReduce.lkErr_two_flip`, `RBM.ChargeReduce.lkErr_two_const` — the two reductions at
  the level of `|L - K|`.

## Notes on the three reductions

All three go through, and each needs only hypotheses that are already available where the
all-charge bound is used (`|E| ≤ 2`, `0 ≤ s N`, `t N < 1`):

* Conjugation does **not** move the spectral parameter.  `RBM.Gsig` already encodes the charge as
  `z ↦ conj z`, so `(G_u(-))ᴴ = G_u(+)` holds at one and the same `z_u` (`RBM.Gsig_conjTranspose`),
  and likewise `conj (u · m(-)²) = u · m(+)²` since `u` is real.
* Cyclicity needs no hypothesis on the `L` side (`RBM.gloop_rotate` is an identity of traces); on
  the `K` side `RBM.kTwo_rotate` needs `‖u · m(σ₁)m(σ₂)‖ < 1`, which `RBM.norm_mul_mSigma_lt_one`
  supplies from `|E| ≤ 2`, `0 ≤ u`, `u < 1`.

## The `K` side of `L - K` at the constant charges

`K` is *not* missing at `(+,+)`: `RBM.Band.Kval` is a definition (`RBM.Kgen`, via (2.57)
`RBM.kTwo` at length `2`) available at every charge, and the bound (2.59) that Step 3 uses,
`RBM.Band.norm_Kval_two_le`, is stated for an arbitrary `I : LoopIdx` of length `2`, hence covers
all four charges with no change.  The only hypothesis is the *fluctuation* bound on `L - K` at
`(+,+)`.
-/

namespace RBM

open Matrix Filter MeasureTheory

namespace ChargeReduce

/-! ### The propagator under complex conjugation -/

/-- `S^(B)` has real entries. -/
theorem conj_SB_apply (L : ℕ) (a b : ZMod L) : (starRingEnd ℂ) (SB L a b) = SB L a b := by
  rw [SB_apply, sbKernel]
  split_ifs
  · rw [map_inv₀, Complex.conj_eq_iff_re.mpr rfl]
  · simp

/-- **`conj (Θ_ξ)_{ab} = (Θ_{conj ξ})_{ab}`.**  `Θ_ξ = (1 - ξ S^(B))⁻¹` and `S^(B)` is real, so
complex conjugation acts on `Θ` only through `ξ`.  This is what turns the charge flip
`m(+) ↦ m(-)` into a conjugation of `K` (2.57). -/
theorem conj_Theta_apply (L : ℕ) [NeZero L] (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1)
    (a b : ZMod L) :
    (starRingEnd ℂ) (Theta L ξ a b) = Theta L ((starRingEnd ℂ) ξ) a b := by
  have hmap : (Theta L ξ).map (starRingEnd ℂ) = Theta L ((starRingEnd ℂ) ξ) := by
    refine eq_Theta_of_mul L hL (by rwa [Complex.norm_conj]) ?_
    have hone : (1 - (starRingEnd ℂ) ξ • SB L) = (1 - ξ • SB L).map (starRingEnd ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, map_sub, map_mul, conj_SB_apply, apply_ite (starRingEnd ℂ), map_one,
        map_zero]
    rw [hone, ← Matrix.map_mul, Theta_mul L hL hξ]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact congrFun (congrFun hmap a) b

/-! ### The primitive `2`-loop `K` under the two symmetries -/

/-- **Conjugation swaps the two constant charges of (2.57).**  `K_{u,σ,(a,b)} =
W⁻¹ m(σ₁)m(σ₂) (Θ_{u m(σ₁)m(σ₂)})_{ab}` and `m(-) = conj m(+)`, so with `u` real
`conj K_{u,(-,-),(a,b)} = K_{u,(+,+),(a,b)}`. -/
theorem conj_kTwo_const (L : ℕ) [NeZero L] (hL : 3 ≤ L) (W : ℕ) {E u : ℝ} (hE : |E| ≤ 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (a b : ZMod L) :
    (starRingEnd ℂ) (kTwo L W (mSigma E) u false false a b)
      = kTwo L W (mSigma E) u true true a b := by
  have hξ : ‖(u : ℂ) * (mSigma E false * mSigma E false)‖ < 1 :=
    norm_mul_mSigma_lt_one hE hu0 hu1 false false
  have hm : (starRingEnd ℂ) (mSigma E false * mSigma E false)
      = mSigma E true * mSigma E true := by
    rw [mSigma_false, mSigma_true, map_mul, Complex.conj_conj]
  have harg : (starRingEnd ℂ) ((u : ℂ) * (mSigma E false * mSigma E false))
      = (u : ℂ) * (mSigma E true * mSigma E true) := by
    rw [map_mul, Complex.conj_ofReal, hm]
  rw [kTwo, kTwo, map_mul, conj_Theta_apply L hL hξ, harg, map_mul, map_inv₀,
    Complex.conj_natCast, hm]

/-- **Reading the `2`-loop from the other end leaves `K` unchanged** (2.57):
`K_{u,(σ₁,σ₂),(a,b)} = K_{u,(σ₂,σ₁),(b,a)}`.  This is `RBM.kTwo_rotate`, i.e. the symmetry of
`Θ` (Lemma 2.14 (1)). -/
theorem Kval_two_flip {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} (hE : |E| ≤ 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (σ₁ σ₂ : Bool) (a b : ZMod (B.L N)) :
    B.Kval E N u ⟨[σ₁, σ₂], [a, b]⟩ = B.Kval E N u ⟨[σ₂, σ₁], [b, a]⟩ := by
  rw [Band.Kval, Band.Kval, Kgen_two, Kgen_two,
    kTwo_rotate (B.W N) (mSigma E) u (B.three_le_L N) σ₁ σ₂
      (norm_mul_mSigma_lt_one hE hu0 hu1 σ₁ σ₂) a b]

/-- `conj K_{u,(-,-),(a,b)} = K_{u,(+,+),(a,b)}`, on the band model. -/
theorem conj_Kval_const {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} (hE : |E| ≤ 2)
    (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (a b : ZMod (B.L N)) :
    (starRingEnd ℂ) (B.Kval E N u ⟨[false, false], [a, b]⟩)
      = B.Kval E N u ⟨[true, true], [a, b]⟩ := by
  rw [Band.Kval, Band.Kval, Kgen_two, Kgen_two,
    conj_kTwo_const (B.L N) (B.three_le_L N) (B.W N) hE hu0 hu1 a b]

/-! ### The `G`-loop `L` under the two symmetries -/

/-- **Cyclicity of the trace**: `L_{u,(σ₁,σ₂),(a,b)} = L_{u,(σ₂,σ₁),(b,a)}` (2.41).  No hypothesis
is needed: this is `RBM.gloop_rotate`. -/
theorem Lval_two_flip {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) (E : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω) (σ₁ σ₂ : Bool) (a b : ZMod (B.L N)) :
    X.Lval E N u ω ⟨[σ₁, σ₂], [a, b]⟩ = X.Lval E N u ω ⟨[σ₂, σ₁], [b, a]⟩ :=
  gloop_rotate σ₁ a (σ := [σ₂]) (a := [b]) rfl

/-- **Conjugation swaps the two constant charges of (2.41)**:
`conj L_{u,(-,-),(a,b)} = L_{u,(+,+),(a,b)}`.

The spectral parameter does **not** move: `RBM.Gsig` encodes the charge as `z ↦ conj z`, so
`(G_u(-))ᴴ = G_u(+)` at the same `z_u` (`RBM.Gsig_conjTranspose`, using that `H_u` is Hermitian),
and `E_a` is Hermitian (`RBM.Eblk_conjTranspose`).  Conjugating the trace reverses the product,
and one rotation puts it back. -/
theorem conj_Lval_const {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) (E : ℝ)
    (N : ℕ) (u : ℝ) (ω : Ω) (a b : ZMod (B.L N)) :
    (starRingEnd ℂ) (X.Lval E N u ω ⟨[false, false], [a, b]⟩)
      = X.Lval E N u ω ⟨[true, true], [a, b]⟩ := by
  set H := X.H N u ω with hHdef
  set z := zt E u with hzdef
  have hH : H.IsHermitian := X.hermitian N u ω
  have hG : (Gsig H z false)ᴴ = Gsig H z true := by
    simpa using Gsig_conjTranspose hH z false
  rw [Sample.Lval, Sample.Lval, ← hHdef, ← hzdef, gloop_two, gloop_two, ← Complex.star_def,
    ← Matrix.trace_conjTranspose]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Eblk_conjTranspose, Eblk_conjTranspose, hG]
  rw [show Eblk (B.L N) (B.W N) b * Gsig H z true *
        (Eblk (B.L N) (B.W N) a * Gsig H z true)
      = Eblk (B.L N) (B.W N) b *
        (Gsig H z true * Eblk (B.L N) (B.W N) a * Gsig H z true) by
    simp [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

/-! ### The two reductions at the level of `|L - K|` -/

/-- **Reduction by cyclicity**: `|L - K|_{u,(σ₁,σ₂),(a,b)} = |L - K|_{u,(σ₂,σ₁),(b,a)}`.
In particular the charge `(-,+)` is covered by the charge `(+,-)`. -/
theorem lkErr_two_flip {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}
    (hE : |E| ≤ 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω) (σ₁ σ₂ : Bool)
    (a b : ZMod (B.L N)) :
    X.lkErr E N u ω ⟨[σ₁, σ₂], [a, b]⟩ = X.lkErr E N u ω ⟨[σ₂, σ₁], [b, a]⟩ := by
  rw [Sample.lkErr, Sample.lkErr, Lval_two_flip X E N u ω σ₁ σ₂ a b,
    Kval_two_flip hE N hu0 hu1 σ₁ σ₂ a b]

/-- **Reduction by conjugation**: `|L - K|_{u,(-,-),(a,b)} = |L - K|_{u,(+,+),(a,b)}`.
The charge `(-,-)` is covered by the charge `(+,+)`. -/
theorem lkErr_two_const {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ}
    (hE : |E| ≤ 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : Ω)
    (a b : ZMod (B.L N)) :
    X.lkErr E N u ω ⟨[false, false], [a, b]⟩ = X.lkErr E N u ω ⟨[true, true], [a, b]⟩ := by
  rw [Sample.lkErr, Sample.lkErr, ← conj_Lval_const X E N u ω a b,
    ← conj_Kval_const hE N hu0 hu1 a b, ← map_sub, Complex.norm_conj]

/-! ### The single remaining charge -/

end ChargeReduce

end RBM
