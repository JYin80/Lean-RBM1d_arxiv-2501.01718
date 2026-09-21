/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.LoopIto

/-!
# `E^{(G̃)}` at loop length two, and (5.52) (T163)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, p. 59, (5.51)–(5.52).

`RBM1D/Hierarchy/Lemma57.lean` (T155) proves **(5.35)** for an *abstract* real number `EG`
constrained only by the hypothesis `hEG`, i.e. by (5.52).  This file supplies the object:
`RBM.EGDef.eGpm` is `E^{(G̃)}_{σ = (+,-), a = (a₁,a₂)}` written out from (5.51) in the Green
function of a Hermitian matrix, and `RBM.EGDef.norm_eGpm_le` is (5.52) for it.

`eGpm` is a **definition**, not a field of a structure.  Its every ingredient unfolds to
`RBM.green`, `RBM.Eblk`, `RBM.SB` and `RBM.gloop` of the matrix `M`; there is no value an
instance may choose.  This is the point of the ticket: the left-hand side of (5.35) is now
pinned, and `RBM.EGDef.eGpm_le_reduced` applies `RBM.Lemma57.eG_le_reduced` to it directly.

## Main results

* `RBM.EGDef.eGpm`, `RBM.EGDef.eGpm_eq_eGterm` — **(5.51)**, and its identification with
  `RBM.Gauss.eGterm`, the `Ẽ` of (2.47) that `RBM.Gauss.generator_add_zMotion_gauss` puts in
  the drift of the loop hierarchy.
* `RBM.EGDef.norm_eGpm_le` — **(5.52)** for `eGpm`.
* `RBM.EGDef.eGpm_le_reduced` — **(5.35)**, shape 2, with `EG := ‖eGpm …‖`.
* `RBM.EGDef.F_eq_eGpm_add_quadGlue` — **the identity T163 asks for**:
  the drift `F` that `RBM.MomentDuhamel.Hyp.drift` pins (`Hyp.F_unique`) is, at loop length
  `2`, `E^{(G̃)} + E^{((L-K)×(L-K))}` — and nothing else.  `RBM.EGDef.drift_split` is the
  underlying (5.15) computation and `RBM.EGDef.primBil_two_eq` writes the quadratic term as
  the (5.49) display.
* `RBM.EGDef.genLK_eq_split` — a by-product T132b needs: `RBM.MomentDuhamel.genLK` (which
  differentiates the *raw* `RBM.gloop` in the matrix) is the cut-and-glue right-hand side of
  `RBM.Gauss.loopIto_second_frozen` (which is stated for `RBM.Gauss.loopObs`, the version
  pre-composed with the Hermitian projection).  The bridge is `RBM.EGDef.fderiv2_comp_clm`.

## Why there is no third term at `n = 2`

(5.15) reads `∂_u(L-K) = Ẽ + Θ_{u,σ}∘(L-K) + ∑_{l_K > 2}[K ∼ (L-K)]^{l_K} + E^{((L-K)×(L-K))}`.
At `n = 2` the only cut is `(k,l) = (1,2)` and both loops it produces have length `2`, so the
whole coupling is its `l_K = 2` piece (`RBM.EGDef.couplingLen_two_of_len_two`) and the sum
over `l_K > 2` is empty.  By (5.19) (`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`) that piece is
`Θ_{u,σ}∘(L-K)`, which is the `RBM.SumZeroDyn.genS` already on the left of `Hyp.drift`.

## Deviations from the literal paper statement

1. `RBM.EGDef.eGpm_le_reduced` carries the hypothesis `hκ : 2 * κ ≤ ℓ_u/ℓ_s`.  The `2` is the
   paper's "`+ c.c.`" in (5.51), which its `≺` absorbs but the constant-free `hEG` of
   `RBM.Lemma57.eG_le_reduced` does not.
2. The paper's (5.51) names the `3`-loop `L_{u,(-,+,+),(a₁,b₂,a₂)}`; the two loops that
   `RBM.LoopIdx.cutGlue` actually produces are `(+,+,-)` at `(b,a₁,a₂)` and `(+,-,-)` at
   `(a₁,b,a₂)`, i.e. the `(-,+,+)` loop at `(a₂,b,a₁)` — the labels exchanged.  Accordingly
   `eGpm_le_reduced` reads the tail function at `zdist (a₂ - a₁)`.
-/

namespace RBM
namespace EGDef

open Matrix Finset

variable (L W : ℕ) [NeZero L] [NeZero W]

/-! ### The definition, (5.51) -/

/-- **(5.51)**: `E^{(G̃)}_{u,σ,a}` at `σ = (+,-)` and `a = (a₁,a₂)`, written out.

The paper's display is

`E^{(G̃)}_{u,σ,a} = W ∑_{b₁,b₂} ⟨G̃_u E_{b₁}⟩ · S^{(B)}_{b₁b₂} · L_{u,(-,+,+),(a₁,b₂,a₂)} + c.c.`,
`G̃ = G - m`,

which is (2.47) (`RBM.Gauss.eGterm`) at `n = 2`: the two summands are its `k = 1` and `k = 2`
terms, and the second is the complex conjugate of the first — that is the paper's "`+ c.c.`".
The `3`-loops that `RBM.LoopIdx.cutGlue` produces are `(+,+,-)` at `(b,a₁,a₂)` and `(+,-,-)`
at `(a₁,b,a₂)`; the first is a double rotation of the `(-,+,+)` loop at `(a₂,b,a₁)`
(`RBM.EGDef.gloop_k1_eq`) and the second is that loop's conjugate
(`RBM.EGDef.norm_gloop_k2_eq`).  **Note the labels**: the loop is `(a₂,b,a₁)`, whereas the
paper's (5.51) prints `(a₁,b₂,a₂)`; `RBM.Lemma57.eG_le_reduced` is therefore invoked with its
two labels exchanged. -/
noncomputable def eGpm (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (a₁ a₂ : ZMod L) : ℂ :=
  (W : ℂ) * ∑ b₁ : ZMod L, ∑ b₂ : ZMod L,
      Matrix.trace ((Gsig M z true - m true • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W b₁)
        * SB L b₁ b₂ * gloop L W M z ⟨[true, true, false], [b₂, a₁, a₂]⟩
    + (W : ℂ) * ∑ b₁ : ZMod L, ∑ b₂ : ZMod L,
      Matrix.trace ((Gsig M z false - m false • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
          * Eblk L W b₁)
        * SB L b₁ b₂ * gloop L W M z ⟨[true, false, false], [a₁, b₂, a₂]⟩

variable {L W}

/-- **`eGpm` is (2.47) at the `(+,-)` `2`-loop**, i.e. it is the `Ẽ` term that
`RBM.Gauss.generator_add_zMotion_gauss` puts in the drift of the loop hierarchy — the
identification the ticket calls for.  Pure index bookkeeping: `RBM.LoopIdx.cutGlue 1 b` and
`cutGlue 2 b` of `⟨[+,-],[a₁,a₂]⟩` are the two `3`-loops of `eGpm`. -/
theorem eGpm_eq_eGterm (m : Bool → ℂ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (a₁ a₂ : ZMod L) :
    eGpm L W m M z a₁ a₂
      = Gauss.eGterm L W m M z ⟨[true, false], [a₁, a₂]⟩ := by
  have hlen : (⟨[true, false], [a₁, a₂]⟩ : LoopIdx (ZMod L)).length = 2 := rfl
  rw [Gauss.eGterm, hlen]
  have h12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [h12, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
  rw [eGpm, mul_add]
  rfl

/-! ### The three `3`-loops of (5.51) are one loop

`RBM.Lemma57.eG_le_reduced` is stated for the `(-,+,+)` loop at `(a₁,b,a₂)`.  The two loops
that `RBM.LoopIdx.cutGlue` produces at the `(+,-)` `2`-loop are `(+,+,-)` at `(b,a₁,a₂)` — a
double rotation of it (with `a₁`, `a₂` exchanged) — and `(+,-,-)` at `(a₁,b,a₂)`, its complex
conjugate.  This is the content of the paper's "`+ c.c.`" in (5.51). -/

section Loops

variable {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

omit [NeZero W] in
/-- Conjugating a `3`-loop reverses it and flips every charge (`G(σ)ᴴ = G(-σ)`,
`E_aᴴ = E_a`, trace cyclicity). -/
theorem gloop_three_conj (hM : M.IsHermitian) (s₁ s₂ s₃ : Bool) (x y w : ZMod L) :
    (starRingEnd ℂ) (gloop L W M z ⟨[s₁, s₂, s₃], [x, y, w]⟩)
      = gloop L W M z ⟨[!s₃, !s₂, !s₁], [y, x, w]⟩ := by
  set A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
    Gsig M z (!s₃) * Eblk L W y * (Gsig M z (!s₂) * Eblk L W x * Gsig M z (!s₁)) with hA
  have hP : (gloopProd L W M z ⟨[s₁, s₂, s₃], [x, y, w]⟩)ᴴ = Eblk L W w * A := by
    show (Gsig M z s₁ * Eblk L W x *
        (Gsig M z s₂ * Eblk L W y * (Gsig M z s₃ * Eblk L W w * 1)))ᴴ = _
    rw [hA]
    simp only [Matrix.mul_one, Matrix.conjTranspose_mul, Gsig_conjTranspose hM,
      Eblk_conjTranspose, Matrix.mul_assoc]
  have hQ : gloopProd L W M z ⟨[!s₃, !s₂, !s₁], [y, x, w]⟩ = A * Eblk L W w := by
    show Gsig M z (!s₃) * Eblk L W y *
        (Gsig M z (!s₂) * Eblk L W x * (Gsig M z (!s₁) * Eblk L W w * 1)) = _
    rw [hA]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [gloop, gloop, hQ, Matrix.trace_mul_comm, ← hP, Matrix.trace_conjTranspose]
  rfl

/-- The `k = 1` loop of (5.51) is the `(-,+,+)` loop of (5.35), by trace cyclicity. -/
theorem gloop_k1_eq (b a₁ a₂ : ZMod L) :
    gloop L W M z ⟨[true, true, false], [b, a₁, a₂]⟩
      = gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩ := by
  have h1 := gloop_rotate (L := L) (W := W) (H := M) (z := z) true b
    (σ := [true, false]) (a := [a₁, a₂]) (by simp)
  have h2 := gloop_rotate (L := L) (W := W) (H := M) (z := z) true a₁
    (σ := [false, true]) (a := [a₂, b]) (by simp)
  simp only [List.cons_append, List.nil_append] at h1 h2
  rw [h1, h2]

/-- The `k = 2` loop of (5.51) has the same modulus, by conjugation. -/
theorem norm_gloop_k2_eq (hM : M.IsHermitian) (b a₁ a₂ : ZMod L) :
    ‖gloop L W M z ⟨[true, false, false], [a₁, b, a₂]⟩‖
      = ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ := by
  have h := gloop_three_conj (L := L) (W := W) (M := M) (z := z) hM true false false a₁ b a₂
  simp only [Bool.not_false, Bool.not_true] at h
  rw [← gloop_k1_eq, ← h, RCLike.norm_conj]

end Loops

/-! ### (5.52) -/

/-- Each **column** of `S^{(B)}` has entries of total modulus `1`. -/
theorem sum_norm_SB_col (hL : 3 ≤ L) (b₂ : ZMod L) : ∑ b₁ : ZMod L, ‖SB L b₁ b₂‖ = 1 := by
  have hcast : ∀ a b : ZMod L, ((‖SB L a b‖ : ℝ) : ℂ) = SB L a b := by
    intro a b
    rw [SB_apply, sbKernel]
    split_ifs <;> simp
  have hC : ((∑ b₁ : ZMod L, ‖SB L b₁ b₂‖ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun b₁ _ => hcast b₁ b₂)]
    have hsymm : ∀ b₁ : ZMod L, SB L b₁ b₂ = SB L b₂ b₁ := fun b₁ =>
      congrFun (congrFun (SB_transpose L) b₂) b₁
    rw [Finset.sum_congr rfl (fun b₁ _ => hsymm b₁), sum_SB_row L hL b₂]
  exact_mod_cast hC

variable {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

omit [NeZero W] in
/-- One of the two blocks of (5.51), bounded by the one-loop factor times the `3`-loop sum. -/
theorem norm_block_le (hL : 3 ≤ L) {c : ℝ} (T g : ZMod L → ℂ) (hT : ∀ b, ‖T b‖ ≤ c) :
    ‖(W : ℂ) * ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, T b₁ * SB L b₁ b₂ * g b₂‖
      ≤ (W : ℝ) * c * ∑ b : ZMod L, ‖g b‖ := by
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (hT 0)
  have hstep : ‖∑ b₁ : ZMod L, ∑ b₂ : ZMod L, T b₁ * SB L b₁ b₂ * g b₂‖
      ≤ c * ∑ b : ZMod L, ‖g b‖ := by
    calc ‖∑ b₁ : ZMod L, ∑ b₂ : ZMod L, T b₁ * SB L b₁ b₂ * g b₂‖
        ≤ ∑ b₁ : ZMod L, ‖∑ b₂ : ZMod L, T b₁ * SB L b₁ b₂ * g b₂‖ := norm_sum_le _ _
      _ ≤ ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, ‖T b₁ * SB L b₁ b₂ * g b₂‖ :=
          Finset.sum_le_sum fun b₁ _ => norm_sum_le _ _
      _ ≤ ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, c * (‖SB L b₁ b₂‖ * ‖g b₂‖) := by
          refine Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
          rw [norm_mul, norm_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_right (hT b₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ∑ b₂ : ZMod L, ∑ b₁ : ZMod L, c * (‖SB L b₁ b₂‖ * ‖g b₂‖) := Finset.sum_comm
      _ = ∑ b₂ : ZMod L, c * ((∑ b₁ : ZMod L, ‖SB L b₁ b₂‖) * ‖g b₂‖) :=
          Finset.sum_congr rfl fun b₂ _ => by rw [← Finset.mul_sum, ← Finset.sum_mul]
      _ = ∑ b₂ : ZMod L, c * ‖g b₂‖ :=
          Finset.sum_congr rfl fun b₂ _ => by rw [sum_norm_SB_col hL b₂, one_mul]
      _ = c * ∑ b : ZMod L, ‖g b‖ := by rw [Finset.mul_sum]
  calc ‖(W : ℂ) * ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, T b₁ * SB L b₁ b₂ * g b₂‖
      = (W : ℝ) * ‖∑ b₁ : ZMod L, ∑ b₂ : ZMod L, T b₁ * SB L b₁ b₂ * g b₂‖ := by
        rw [norm_mul]; simp
    _ ≤ (W : ℝ) * (c * ∑ b : ZMod L, ‖g b‖) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (W : ℝ) * c * ∑ b : ZMod L, ‖g b‖ := by ring

/-- **(5.52)**: `max_a E^{(G̃)}_{u,σ,a} ≺ (ℓ_u η_u)^{-1} ∑_b |L_{u,(-,+,+),(a₁,b,a₂)}|
(1 + J* (W ℓ_u η_u)^{-1})`, for the concrete `RBM.EGDef.eGpm`.

The hypothesis `hone` is the paper's `⟨G̃_u E_{b₁}⟩ ≺ Ξ^{(L)}_{u,2} (W ℓ_u η_u)^{-1}` — (4.5)
with (2.74) — and it is a statement about the Green function of `M`, not about a datum.  The
factor `2` on the right is the paper's "`+ c.c.`". -/
theorem norm_eGpm_le (hL : 3 ≤ L) (hM : M.IsHermitian) (m : Bool → ℂ) {c : ℝ}
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M z σ
        - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)‖ ≤ c)
    (a₁ a₂ : ZMod L) :
    ‖eGpm L W m M z a₁ a₂‖
      ≤ 2 * (W : ℝ) * c * ∑ b : ZMod L, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ := by
  have h1 := norm_block_le (L := L) (W := W) hL
    (fun b₁ => Matrix.trace ((Gsig M z true
        - m true • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b₁))
    (fun b₂ => gloop L W M z ⟨[true, true, false], [b₂, a₁, a₂]⟩) (hone true)
  have h2 := norm_block_le (L := L) (W := W) hL
    (fun b₁ => Matrix.trace ((Gsig M z false
        - m false • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b₁))
    (fun b₂ => gloop L W M z ⟨[true, false, false], [a₁, b₂, a₂]⟩) (hone false)
  have hg1 : ∀ b : ZMod L, ‖gloop L W M z ⟨[true, true, false], [b, a₁, a₂]⟩‖
      = ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ := fun b => by
    rw [gloop_k1_eq]
  have hg2 : ∀ b : ZMod L, ‖gloop L W M z ⟨[true, false, false], [a₁, b, a₂]⟩‖
      = ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ := fun b =>
    norm_gloop_k2_eq hM b a₁ a₂
  rw [Finset.sum_congr rfl fun b _ => hg1 b] at h1
  rw [Finset.sum_congr rfl fun b _ => hg2 b] at h2
  refine le_trans (norm_add_le _ _) ?_
  have := add_le_add h1 h2
  linarith [this]

/-! ### (5.35) applied to the pinned object

`RBM.Lemma57.eG_le_reduced` is (5.35) for an abstract real `EG` constrained by (5.52); here
`EG` is `‖RBM.EGDef.eGpm …‖`, which unfolds to the Green function of `M`.  Every hypothesis
below is a statement about `RBM.gloop` / `RBM.green` of `M` — there is no structure field on
either side. -/

/-- **(5.35) for `E^{(G̃)}` itself**, the `(2.73)`-reduced shape.

The charge-`(+,-)` `2`-loop carries `a = (a₁,a₂)`; the `3`-loop that (5.51) produces is the
`(-,+,+)` loop at `(a₂,b,a₁)`, so `RBM.Lemma57.eG_le_reduced` is invoked with its two labels
exchanged and the tail function is read at `zdist (a₂ - a₁)` (`RBM.zdist` is symmetric).

`hone` is (4.5)+(2.74) for the one-loop factor of (5.51), and `hκ` absorbs the factor `2` of
the paper's "`+ c.c.`" into the `W^{o(1)}` prefactor `r = ℓ_u/ℓ_s` of shape 2. -/
theorem eGpm_le_reduced {ℓu ℓs ηu D J : ℝ} (hM : M.IsHermitian) (hL : 3 ≤ L)
    (hW : 1 ≤ (W : ℝ)) (hℓu : 1 ≤ ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hJ : 1 ≤ J)
    (hA : 1 ≤ (W : ℝ) * ℓu * ηu) (hr : 1 ≤ ℓu / ℓs)
    (hD : (L : ℝ) * Real.sqrt ((W : ℝ) ^ (-D)) ≤ ℓu * ((W : ℝ) * ℓu * ηu)⁻¹)
    (a₁ a₂ : ZMod L) {Gm : ZMod L → ZMod L → ℝ} {ρ κ : ℝ}
    (hρ : 0 ≤ ρ) (hGm : ∀ x y, 0 ≤ Gm x y)
    (h273 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      (ℓu / ℓs) ^ 2 * (((W : ℝ) * ℓu * ηu) ^ 2)⁻¹)
    (h554 : ∀ b, Lemma57.ellStarStar (W : ℝ) ℓu < (zdist L (a₂ - b) : ℝ) →
      ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤ ρ)
    (h531 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      (gloop L W M z ⟨[true, false], [x, y]⟩).re ≤
        J * tailT (W : ℝ) ℓu ηu D (zdist L (x - y)))
    (h42 : ∀ x y : ZMod L, ellStar (W : ℝ) ℓu / 2 ≤ (zdist L (x - y) : ℝ) →
      Gm x y ≤ Real.sqrt J * Real.sqrt (tailT (W : ℝ) ℓu ηu D (zdist L (x - y))))
    (h557C : ∀ (x y : ZMod L) (p : ZMod L × Fin W), p.1 = y →
      ∑ r : ZMod L × Fin W, Lemma57.blkW L W r x * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h557R : ∀ (x y : ZMod L) (r : ZMod L × Fin W), r.1 = x →
      ∑ p : ZMod L × Fin W, Lemma57.blkW L W p y * ‖green M z r p‖ ≤
        Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹)
    (h560 : ∀ b, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ ≤
      Gm a₂ b * Gm a₁ b * Gm a₂ a₁)
    (m : Bool → ℂ)
    (hone : ∀ σ b, ‖Matrix.trace ((Gsig M z σ
        - m σ • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) * Eblk L W b)‖
      ≤ κ * ((W : ℝ) * ℓu * ηu)⁻¹)
    (hκ : 2 * κ ≤ ℓu / ℓs) :
    ‖eGpm L W m M z a₁ a₂‖
      ≤ ηu⁻¹ * (Lemma57.cNear (W : ℝ) ℓu * (ℓu / ℓs) ^ 3 *
            (if (zdist L (a₂ - a₁) : ℝ) ≤ ellStar (W : ℝ) ℓu then 1 else 0)
          + Lemma57.cFar (W : ℝ) ℓu *
              ((ℓu / ℓs) * Real.sqrt (ℓu / ℓs) * (Real.sqrt ((W : ℝ) * ℓu * ηu))⁻¹ * J)
          + 169 * ((ℓu / ℓs) * ((W : ℝ) * ℓu * ηu)⁻¹ * (J * Real.sqrt J)))
        * tailT (W : ℝ) ℓu ηu D (zdist L (a₂ - a₁))
        + (ℓu / ℓs) * (ℓu * ηu)⁻¹ * (L : ℝ) * ρ := by
  have hW0 : (0 : ℝ) < W := by linarith
  have hℓ0 : (0 : ℝ) < ℓu := by linarith
  have hS0 : (0 : ℝ) ≤ ∑ b : ZMod L, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbase := norm_eGpm_le (L := L) (W := W) hL hM m (c := κ * ((W : ℝ) * ℓu * ηu)⁻¹)
    hone a₁ a₂
  have hcoef : 2 * (W : ℝ) * (κ * ((W : ℝ) * ℓu * ηu)⁻¹) ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ := by
    have hEq : 2 * (W : ℝ) * (κ * ((W : ℝ) * ℓu * ηu)⁻¹) = (2 * κ) * (ℓu * ηu)⁻¹ := by
      field_simp
    rw [hEq]
    exact mul_le_mul_of_nonneg_right hκ (by positivity)
  have hEG : ‖eGpm L W m M z a₁ a₂‖
      ≤ (ℓu / ℓs) * (ℓu * ηu)⁻¹ *
        ∑ b : ZMod L, ‖gloop L W M z ⟨[false, true, true], [a₂, b, a₁]⟩‖ :=
    hbase.trans (mul_le_mul_of_nonneg_right hcoef hS0)
  exact Lemma57.eG_le_reduced L W hM hW hℓu hℓs hηu hJ hA hr hD a₂ a₁ hρ hGm
    h273 h554 h531 h42 h557C h557R h560 hEG

/-! ### The drift of `L - K` at loop length two

The remaining sections identify the drift `F` of `RBM.MomentDuhamel.Hyp` — the one the
*moment* route pins by the pointwise identity (5.15) (`RBM.MomentDuhamel.Hyp.drift`,
`F_unique`) — at loop length `2`:

`F = E^{(G̃)} + E^{((L-K)×(L-K))}`,   (`RBM.EGDef.F_eq_eGpm_add_quadGlue`)

with `E^{(G̃)}` the `RBM.EGDef.eGpm` above and `E^{((L-K)×(L-K))}` the quadratic gluing term
(5.49) that (5.34) governs.  **There is no third term**: at `n = 2` every cut of the loop
produces two `2`-loops, so the graded coupling `[K ∼ (L-K)]^{l_K}` is concentrated at
`l_K = 2` (`RBM.EGDef.couplingLen_two_of_len_two`), and (5.19)
(`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`) turns that piece into the generator
`Θ_{u,σ} ∘ (L-K)`, which is the `RBM.SumZeroDyn.genS` already on the left of `Hyp.drift`.
So the `∑_{l_K > 2}` of (5.15) is empty here.  This is the "list every term" part of T163. -/

section Drift

open Gauss
open scoped Matrix.Norms.L2Operator

/-! #### A second derivative along directions fixed by a projection

`RBM.MomentDuhamel.genLK` differentiates the *raw* `RBM.gloop` in the matrix, while
`RBM.Gauss.loopIto_second_frozen` is stated for `RBM.Gauss.loopObs`, which pre-composes with
the Hermitian projection `RBM.Gauss.hermCLM` (T71's device for global definedness).  The two
agree at a Hermitian matrix and along a Hermitian direction, which is the only place either is
evaluated: that is the content of `RBM.EGDef.fderiv2_comp_clm`. -/

/-- If a continuous linear `T` fixes both the base point `M` and the direction `B`, the second
directional derivative of `Ψ ∘ T` along `B` at `M` is that of `Ψ`. -/
theorem fderiv2_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Ψ : E → F} {T : E →L[ℝ] E} {M B : E}
    (hΨ : ContDiffAt ℝ 2 Ψ M) (hTM : T M = M) (hTB : T B = B) :
    fderiv ℝ (fderiv ℝ (Ψ ∘ T)) M B B = fderiv ℝ (fderiv ℝ Ψ) M B B := by
  have hne : (2 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hev : ∀ᶠ y in nhds M, ContDiffAt ℝ 2 Ψ y := hΨ.eventually hne
  have hTc : Filter.Tendsto T (nhds M) (nhds M) := by
    have h := T.continuous.tendsto M
    rwa [hTM] at h
  have hevT : ∀ᶠ y in nhds M, DifferentiableAt ℝ Ψ (T y) :=
    hTc.eventually (hev.mono fun y hy => hy.differentiableAt (by norm_num))
  set C : (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) := (ContinuousLinearMap.compL ℝ E E F).flip T with hC
  have hCapp : ∀ A : E →L[ℝ] F, C A = A.comp T := fun A => rfl
  have h1 : (fderiv ℝ (Ψ ∘ T)) =ᶠ[nhds M] (fun M' => C (fderiv ℝ Ψ (T M'))) := by
    filter_upwards [hevT] with M' hM'
    rw [fderiv_comp M' hM' T.differentiableAt, T.fderiv, hCapp]
  have hgd : DifferentiableAt ℝ (fderiv ℝ Ψ) (T M) := by
    rw [hTM]
    exact (hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (Ψ ∘ T)) M
      = C.comp ((fderiv ℝ (fderiv ℝ Ψ) (T M)).comp T) := by
    rw [h1.fderiv_eq]
    have hcomp : (fun M' => C (fderiv ℝ Ψ (T M'))) = (C ∘ ((fderiv ℝ Ψ) ∘ T)) := rfl
    rw [hcomp, fderiv_comp M C.differentiableAt (hgd.comp M T.differentiableAt),
      C.fderiv, fderiv_comp M hgd T.differentiableAt, T.fderiv]
  rw [h2]
  simp only [ContinuousLinearMap.comp_apply, hCapp, hTM, hTB]

/-! #### The loop is `C²` in the matrix at a Hermitian point

Not globally: at a non-Hermitian `M` the resolvent need not exist.  `RBM.Gauss.loopObs` is
globally `C²` precisely because it pre-composes with `hermCLM`. -/

/-- `M' ↦ G(σ)(M', z)` is `C^k` at a Hermitian `M`, by `RBM.Gauss.contDiffAt_green_comp`. -/
theorem contDiffAt_Gsig_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ℂ}
    {M : Matrix ι ι ℂ} {k : WithTop ℕ∞} (hM : M.IsHermitian) (hz : z.im ≠ 0) (σ : Bool) :
    ContDiffAt ℝ k (fun M' : Matrix ι ι ℂ => Gsig M' z σ) M :=
  contDiffAt_green_comp contDiffAt_id contDiffAt_const
    (isUnit_sub_smul_one_of_im_ne_zero hM (im_charge_ne_zero hz σ))

omit [NeZero W] in
theorem contDiffAt_gloopProd_matrix {z : ℂ}
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {k : WithTop ℕ∞}
    (hM : M.IsHermitian) (hz : z.im ≠ 0) :
    ∀ (σ : List Bool) (a : List (ZMod L)),
      ContDiffAt ℝ k (fun M' => gloopProd L W M' z ⟨σ, a⟩) M := by
  intro σ
  induction σ with
  | nil => intro a; exact contDiffAt_const
  | cons σ₀ σ ih =>
      intro a
      cases a with
      | nil => exact contDiffAt_const
      | cons c a' =>
          have hfun : (fun M' => gloopProd L W M' z (⟨σ₀ :: σ, c :: a'⟩ : LoopIdx (ZMod L)))
              = fun M' => Gsig M' z σ₀ * Eblk L W c * gloopProd L W M' z ⟨σ, a'⟩ := rfl
          rw [hfun]
          exact ((contDiffAt_Gsig_matrix hM hz σ₀).mul contDiffAt_const).mul (ih a')

omit [NeZero W] in
/-- `M' ↦ L_{σ,a}(M', z)` is `C^k` at a Hermitian `M`. -/
theorem contDiffAt_gloop_matrix {z : ℂ}
    {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {k : WithTop ℕ∞}
    (hM : M.IsHermitian) (hz : z.im ≠ 0) (I : LoopIdx (ZMod L)) :
    ContDiffAt ℝ k (fun M' => gloop L W M' z I) M := by
  set T : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((Matrix.traceLinearMap (ZMod L × Fin W) ℂ ℂ).restrictScalars ℝ) with hTdef
  have hfun : (fun M' => gloop L W M' z I) = T ∘ fun M' => gloopProd L W M' z I := rfl
  rw [hfun]
  exact (T.contDiff (n := k)).contDiffAt.comp M
    (contDiffAt_gloopProd_matrix (L := L) (W := W) hM hz I.σ I.a)

/-! #### `RBM.MomentDuhamel.genLK` is the cut-and-glue right-hand side -/

section Wirt

variable {d : Dims} {N : ℕ}

/-- The Hermitian projection is invisible to `RBM.Gauss.coordD2` at a Hermitian matrix. -/
theorem coordD2_gloop_eq {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (I : LoopIdx (ZMod (d.L N)))
    (i j : d.Idx N) (bb : Bool) (hb : i ≠ j ∨ bb = true) :
    coordD2 d N (loopObs d N z I) M (i, j, bb)
      = coordD2 d N (fun M' => gloop (d.L N) (d.W N) M' z I) M (i, j, bb) := by
  have hTM : hermCLM (d.Idx N) M = M := hermCLM_of_isHermitian hM
  have hTB : hermCLM (d.Idx N) (Bmat d N i j bb) = Bmat d N i j bb :=
    hermCLM_of_isHermitian (isHermitian_Bmat_of i j bb hb)
  have hPsi : ContDiffAt ℝ 2 (fun M' => gloop (d.L N) (d.W N) M' z I) M :=
    contDiffAt_gloop_matrix (L := d.L N) (W := d.W N) hM hz I
  have hfun : loopObs d N z I
      = (fun M' => gloop (d.L N) (d.W N) M' z I) ∘ (hermCLM (d.Idx N)) := rfl
  simp only [coordD2, hfun]
  exact fderiv2_comp_clm hPsi hTM hTB

theorem wirtSecond_gloop_eq {z : ℂ} (hz : z.im ≠ 0)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) (I : LoopIdx (ZMod (d.L N)))
    (i j : d.Idx N) :
    wirtSecond d N (loopObs d N z I) M i j
      = wirtSecond d N (fun M' => gloop (d.L N) (d.W N) M' z I) M i j := by
  unfold wirtSecond
  split_ifs with h
  · subst h
    exact coordD2_gloop_eq hz hM I i i true (Or.inr rfl)
  · rw [coordD2_gloop_eq hz hM I i j true (Or.inl h),
      coordD2_gloop_eq hz hM I i j false (Or.inl h)]

/-- A constant is invisible to the second derivative. -/
theorem coordD2_sub_const (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (c : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (p : d.Idx N × d.Idx N × Bool) :
    coordD2 d N (fun M' => Φ M' - c) M p = coordD2 d N Φ M p := by
  have h : (fderiv ℝ fun M' => Φ M' - c) = fderiv ℝ Φ := by
    funext M'; exact fderiv_sub_const c
  simp only [coordD2, h]

theorem wirtSecond_sub_const (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (c : ℂ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (i j : d.Idx N) :
    wirtSecond d N (fun M' => Φ M' - c) M i j = wirtSecond d N Φ M i j := by
  unfold wirtSecond
  simp only [coordD2_sub_const]

end Wirt

section Band

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`RBM.MomentDuhamel.genLK` is (2.47) at `m = 0` plus the quadratic term (2.48)**, at every
Hermitian matrix.  This is `RBM.Gauss.loopIto_second_frozen` transported across the two
cosmetic differences between the `Band`-level `genLK` and the `Dims`-level generator: the
`RBM.Gauss.hermCLM` of `RBM.Gauss.loopObs`, and the `K`-subtraction inside
`RBM.MomentDuhamel.lkFun`. -/
theorem genLK_eq_split (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    {m : ℕ} (sg : Fin m → Bool) (a : LoopArg (B.L N) m) :
    MomentDuhamel.genLK B E N u M sg a
      = eGterm (B.L N) (B.W N) 0 M (zt E u) (LoopData.idx (sg, a))
        + primRhs (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u)) (LoopData.idx (sg, a)) := by
  have hwf : (LoopData.idx (sg, a)).WF := LoopData.idx_wf _
  have hkey := loopIto_second_frozen_of_im_ne_zero (d := B.toDims) (N := N) hz M hM
    (LoopData.idx (sg, a)) hwf
  have hW : ∀ i j : B.Idx N,
      wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' sg a) M i j
        = wirtSecond B.toDims N (loopObs B.toDims N (zt E u) (LoopData.idx (sg, a))) M i j := by
    intro i j
    have h1 : wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' sg a) M i j
        = wirtSecond B.toDims N
            (fun M' => gloop (B.L N) (B.W N) M' (zt E u) (LoopData.idx (sg, a))) M i j :=
      wirtSecond_sub_const (d := B.toDims) (N := N)
        (fun M' => gloop (B.L N) (B.W N) M' (zt E u) (LoopData.idx (sg, a)))
        (B.Kval E N u (LoopData.idx (sg, a))) M i j
    rw [h1]
    exact (wirtSecond_gloop_eq (d := B.toDims) (N := N) hz hM (LoopData.idx (sg, a)) i j).symm
  have hsum : ∑ i : B.Idx N, ∑ j : B.Idx N, ((Sblk (B.L N) (B.W N) i j : ℝ) : ℂ)
        * wirtSecond B.toDims N (fun M' => MomentDuhamel.lkFun B E N u M' sg a) M i j
      = ∑ i : B.Idx N, ∑ j : B.Idx N, ((Sblk (B.L N) (B.W N) i j : ℝ) : ℂ)
        * wirtSecond B.toDims N (loopObs B.toDims N (zt E u) (LoopData.idx (sg, a))) M i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hW i j]
  have hconv : (2 : ℂ)⁻¹ * ∑ i : B.Idx N, ∑ j : B.Idx N, ((Sblk (B.L N) (B.W N) i j : ℝ) : ℂ)
        * wirtSecond B.toDims N (loopObs B.toDims N (zt E u) (LoopData.idx (sg, a))) M i j
      = (1 / 2 : ℝ) • ∑ i : B.Idx N, ∑ j : B.Idx N,
          Sblk (B.L N) (B.W N) i j •
            wirtSecond B.toDims N (loopObs B.toDims N (zt E u) (LoopData.idx (sg, a))) M i j := by
    simp only [Complex.real_smul]
    norm_num
  rw [MomentDuhamel.genLK, hsum, hconv]
  exact hkey

/-! #### The primitive `K` and its equation at a `2`-loop -/

theorem kTwoLoop_eq_Kval (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (s1 s2 : Bool) (x y : ZMod (B.L N)) :
    kTwoLoop (B.L N) (B.W N) (mSigma E) u ⟨[s1, s2], [x, y]⟩
      = B.Kval E N u ⟨[s1, s2], [x, y]⟩ := by
  rw [Band.Kval, Kgen_two]
  rfl

/-- **(2.48) at `n = 2` for `RBM.Band.Kval`** (Example 2.15 transported). -/
theorem hasDerivAt_Kval_two (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (hL : 3 ≤ B.L N) (s1 s2 : Bool) (x y : ZMod (B.L N))
    (hxi : ‖(u : ℂ) * (mSigma E s1 * mSigma E s2)‖ < 1) :
    HasDerivAt (fun v : ℝ => B.Kval E N v ⟨[s1, s2], [x, y]⟩)
      (primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨[s1, s2], [x, y]⟩) u := by
  have hfun : (fun v : ℝ => B.Kval E N v (⟨[s1, s2], [x, y]⟩ : LoopIdx (ZMod (B.L N))))
      = fun v : ℝ => kTwoLoop (B.L N) (B.W N) (mSigma E) v ⟨[s1, s2], [x, y]⟩ := by
    funext v; exact (kTwoLoop_eq_Kval B E N v s1 s2 x y).symm
  have hpr : primRhs (B.L N) (B.W N) (kTwoLoop (B.L N) (B.W N) (mSigma E) u)
        (⟨[s1, s2], [x, y]⟩ : LoopIdx (ZMod (B.L N)))
      = primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨[s1, s2], [x, y]⟩ := by
    rw [primRhs_two, primRhs_two]
    refine congrArg _ (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
    rw [kTwoLoop_eq_Kval B E N u s1 s2 x p, kTwoLoop_eq_Kval B E N u s1 s2 q y]
  rw [hfun, ← hpr]
  exact hasDerivAt_kTwoLoop (B.L N) hL (B.W N) (mSigma E) s1 s2 hxi x y

end Band

/-! #### At `n = 2` the coupling is concentrated at `l_K = 2`

Cutting a `2`-loop at `1 ≤ k < l ≤ 2` leaves `(k,l) = (1,2)`, and both resulting loops have
length `2`.  So `[K ∼ (L-K)]^{l_K}` vanishes for `l_K ≠ 2` and the whole coupling is the
`l_K = 2` piece that (5.19) identifies with the generator. -/

section Coupling

variable (L₁ W₁ : ℕ) [NeZero L₁]

theorem primBilLen_two_of_len_two (K D : LoopIdx (ZMod L₁) → ℂ) (I : LoopIdx (ZMod L₁))
    (h2 : I.length = 2) : primBilLen L₁ W₁ 2 K D I = primBil L₁ W₁ K D I := by
  rw [primBilLen, primBil]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hcond : (I.cutGlueL k l p).length = 2 := by
    rw [LoopIdx.length_cutGlueL I p hk.1 hl.1 hl.2, h2]
    rw [h2] at hk hl
    omega
  rw [hcond]
  simp

theorem primBilLenR_two_of_len_two (D K : LoopIdx (ZMod L₁) → ℂ) (I : LoopIdx (ZMod L₁))
    (h2 : I.length = 2) : Decay.primBilLenR L₁ W₁ 2 D K I = primBil L₁ W₁ D K I := by
  rw [Decay.primBilLenR, primBil]
  refine congrArg _ (Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have hcond : (I.cutGlueR k l q).length = 2 := by
    rw [LoopIdx.length_cutGlueR I q hk.1 hl.1 hl.2]
    rw [h2] at hk hl
    omega
  rw [hcond]
  simp

/-- **The whole coupling `[K ∼ (L-K)]` sits at `l_K = 2`** when the loop has length `2`. -/
theorem couplingLen_two_of_len_two (K D : LoopIdx (ZMod L₁) → ℂ) (I : LoopIdx (ZMod L₁))
    (h2 : I.length = 2) :
    Decay.couplingLen L₁ W₁ 2 K D I = primBil L₁ W₁ K D I + primBil L₁ W₁ D K I := by
  rw [Decay.couplingLen, primBilLen_two_of_len_two L₁ W₁ K D I h2,
    primBilLenR_two_of_len_two L₁ W₁ D K I h2]

end Coupling

/-! #### The drift identity -/

section DriftMain

variable {Ω : Type*} [MeasurableSpace Ω]

theorem ofFn_two {α : Type*} (a : Fin 2 → α) : List.ofFn a = [a 0, a 1] := rfl

/-- The `LoopArg`-side generator of `RBM.MomentDuhamel.Hyp.drift` is the `LoopIdx`-side
`RBM.Gauss.thetaGenLoop` of (5.19). -/
theorem genS_eq_thetaGenLoop (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (s1 s2 : Bool) (a : LoopArg (B.L N) 2) :
    SumZeroDyn.genS (B.L N) (xiOf (mSigma E) ![s1, s2]) ((u : ℝ) : ℂ)
        (MomentDuhamel.lkFun B E N u M ![s1, s2]) a
      = thetaGenLoop (B.L N) (mSigma E) u
          (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨[s1, s2], List.ofFn a⟩ := by
  rw [thetaGenLoop_ofFn (L := B.L N) (mSigma E) u
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) [s1, s2] a]
  have hxi : (fun i : Fin 2 => mSigma E (([s1, s2] : List Bool).getD (i : ℕ) true)
        * mSigma E (([s1, s2] : List Bool).getD (((i : ℕ) + 1) % 2) true))
      = xiOf (mSigma E) ![s1, s2] := by
    funext i; fin_cases i <;> rfl
  rw [hxi]
  rfl

/-- **(5.15) at `n = 2`, with the drift identified.**  The derivative that
`RBM.MomentDuhamel.Hyp.drift` asserts exists is exhibited, and the drift it leaves abstract is

`E^{(G̃)}_{u,σ,a} + E^{((L-K)×(L-K))}_{u,σ,a}`,

with `E^{(G̃)}` the `Ẽ` of (2.47) (`RBM.Gauss.eGterm`) and `E^{((L-K)×(L-K))}` the quadratic
gluing term (5.49) (`RBM.primBil` of `L - K` with itself).  Nothing else appears. -/
theorem drift_split (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    (s1 s2 : Bool) (a : LoopArg (B.L N) 2)
    (hxi : ‖(u : ℂ) * (mSigma E s1 * mSigma E s2)‖ < 1)
    (hxi2 : ‖(u : ℂ) * (mSigma E s2 * mSigma E s1)‖ < 1) :
    ∃ dv : ℂ, HasDerivAt (fun v : ℝ => MomentDuhamel.lkFun B E N v M ![s1, s2] a) dv u ∧
      dv + MomentDuhamel.genLK B E N u M ![s1, s2] a
        = SumZeroDyn.genS (B.L N) (xiOf (mSigma E) ![s1, s2]) ((u : ℝ) : ℂ)
            (MomentDuhamel.lkFun B E N u M ![s1, s2]) a
          + (eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[s1, s2], List.ofFn a⟩
            + primBil (B.L N) (B.W N)
                (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
                (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
                ⟨[s1, s2], List.ofFn a⟩) := by
  have hIdx : LoopData.idx (![s1, s2], a)
      = (⟨[s1, s2], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) := rfl
  set I : LoopIdx (ZMod (B.L N)) := ⟨[s1, s2], List.ofFn a⟩ with hI
  have hwf : I.WF := rfl
  have hlen : I.length = 2 := rfl
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hgl := hasDerivAt_gloop_zt_eGterm (L := B.L N) (W := B.W N) hL3 hM hz I hwf
  have hKd : HasDerivAt (fun v : ℝ => B.Kval E N v I)
      (primRhs (B.L N) (B.W N) (B.Kval E N u) I) u := by
    rw [hI, ofFn_two]
    exact hasDerivAt_Kval_two B E N u hL3 s1 s2 (a 0) (a 1) hxi
  refine ⟨_, hgl.sub hKd, ?_⟩
  rw [genLK_eq_split B E N u hM hz ![s1, s2] a, genS_eq_thetaGenLoop B E N u s1 s2 a]
  have hxiL : xiLoop (mSigma E) I (2 - 1) = mSigma E s2 * mSigma E s1 := by
    rw [hI]; simp [xiLoop, LoopIdx.length]
  have hK : ∀ (t1 t2 : Bool) (x y : ZMod (B.L N)),
      B.Kval E N u ⟨[t1, t2], [x, y]⟩ = kTwo (B.L N) (B.W N) (mSigma E) u t1 t2 x y := by
    intro t1 t2 x y; rw [Band.Kval, Kgen_two]
  have hcoup := couplingLen_two_eq_thetaGenLoop (L := B.L N) (B.W N) (mSigma E) u
    (B.Kval E N u) (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) hL3 hK I hwf
    (by rw [hlen]) (by rw [hlen, hxiL]; exact hxi2)
  have hsplit := couplingLen_two_of_len_two (B.L N) (B.W N) (B.Kval E N u)
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) I hlen
  have hps := primRhs_sub (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u)) (B.Kval E N u) I
  rw [hIdx, ← hcoup, hsplit]
  linear_combination hps

variable {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

/-- **The drift of `RBM.MomentDuhamel.Hyp` at loop length `2`, identified.**

`RBM.MomentDuhamel.Hyp.F` is pinned by the field `drift` (`Hyp.F_unique`); this theorem says
what it is.  Both summands on the right are definitions in the Green function of `M`: no
structure field occurs on either side. -/
theorem F_eq_eGterm_add_quadGlue (H : MomentDuhamel.Hyp X E s t 0) {N : ℕ} {u : ℝ}
    (hsu : s N ≤ u) (hut : u ≤ t N)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    (s1 s2 : Bool) (a : LoopArg (B.L N) 2)
    (hxi : ‖(u : ℂ) * (mSigma E s1 * mSigma E s2)‖ < 1)
    (hxi2 : ‖(u : ℂ) * (mSigma E s2 * mSigma E s1)‖ < 1) :
    H.F N u M ![s1, s2] a
      = eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[s1, s2], List.ofFn a⟩
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨[s1, s2], List.ofFn a⟩ := by
  obtain ⟨dv, hdv, heq⟩ := H.drift N u hsu hut M hM ![s1, s2] a
  obtain ⟨dv', hdv', heq'⟩ := drift_split B E N u hM hz s1 s2 a hxi hxi2
  have hd : dv = dv' := hdv.unique hdv'
  rw [hd] at heq
  exact add_left_cancel (heq.symm.trans heq')

/-- **The headline identity of T163**, at the charge `σ = (+,-)` of §5.3:

`F_{u,(+,-),(a₁,a₂)} = E^{(G̃)}_{u,(+,-),(a₁,a₂)} + E^{((L-K)×(L-K))}_{u,(+,-),(a₁,a₂)}`,

with `E^{(G̃)}` the `RBM.EGDef.eGpm` of (5.51) and the second summand the (5.49) gluing term
(written out by `RBM.EGDef.primBil_two_eq`). -/
theorem F_eq_eGpm_add_quadGlue (H : MomentDuhamel.Hyp X E s t 0) {N : ℕ} {u : ℝ}
    (hsu : s N ≤ u) (hut : u ≤ t N)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    (a₁ a₂ : ZMod (B.L N))
    (hxi : ‖(u : ℂ) * (mSigma E true * mSigma E false)‖ < 1)
    (hxi2 : ‖(u : ℂ) * (mSigma E false * mSigma E true)‖ < 1) :
    H.F N u M ![true, false] ![a₁, a₂]
      = eGpm (B.L N) (B.W N) (mSigma E) M (zt E u) a₁ a₂
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) ⟨[true, false], [a₁, a₂]⟩ := by
  have h := F_eq_eGterm_add_quadGlue H hsu hut hM hz true false ![a₁, a₂] hxi hxi2
  rw [eGpm_eq_eGterm]
  exact h

end DriftMain

/-! #### The quadratic term is (5.49) -/

omit [NeZero W] in
/-- **(5.49)**: at a `2`-loop the gluing term `E^{((L-K)×(L-K))}` of (5.13) is
`W ∑_{b₁,b₂} (L-K)_{σ,(a₁,b₁)} S^{(B)}_{b₁b₂} (L-K)_{σ,(b₂,a₂)}` — the expression the proof of
(5.34) is about, and, transported from `RBM.LoopIdx` to `RBM.LoopArg`, the `RBM.Step2.eLL` of
`RBM1D/Hierarchy/Step2.lean`. -/
theorem primBil_two_eq (D : LoopIdx (ZMod L) → ℂ) (s1 s2 : Bool) (a₁ a₂ : ZMod L) :
    primBil L W D D ⟨[s1, s2], [a₁, a₂]⟩
      = (W : ℂ) * ∑ b₁ : ZMod L, ∑ b₂ : ZMod L,
          D ⟨[s1, s2], [a₁, b₁]⟩ * SB L b₁ b₂ * D ⟨[s1, s2], [b₂, a₂]⟩ := by
  rw [primBil_self, primRhs_two]

end Drift

end EGDef
end RBM
