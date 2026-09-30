/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Lemma57
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Gauss.LoopIto

/-!
# `E^{(G̃)}` at loop length two, and (5.52)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.51)–(5.52).

`RBM1D/Hierarchy/Lemma57.lean` proves **(5.35)** (the near field `RBM.Lemma57.eG_near_le`, the
far field `RBM.Lemma57.eG_far_le`) for an *abstract* real number `EG` constrained only by the
hypothesis `hEG`, i.e. by (5.52).  This file supplies the object:
`RBM.EGDef.eGpm` is `E^{(G̃)}_{σ = (+,-), a = (a₁,a₂)}` written out from (5.51) in the Green
function of a Hermitian matrix, and `RBM.EGDef.norm_eGpm_le` is (5.52) for it.

`eGpm` is a **definition**, not a field of a structure.  Its every ingredient unfolds to
`RBM.green`, `RBM.Eblk`, `RBM.SB` and `RBM.gloop` of the matrix `M`; there is no value an
instance may choose.  So the left-hand side of (5.35) is a concrete object.

## Main results

* `RBM.EGDef.eGpm`, `RBM.EGDef.eGpm_eq_eGterm` — **(5.51)**, and its identification with
  `RBM.Gauss.eGterm`, the `Ẽ` of (2.47) that `RBM.Gauss.generator_add_zMotion_gauss` puts in
  the drift of the loop hierarchy.
* `RBM.EGDef.norm_eGpm_le` — **(5.52)** for `eGpm`.
* `RBM.EGDef.couplingLen_two_of_len_two` — at loop length `2` the whole coupling
  `[K ∼ (L-K)]^{l_K}` sits at `l_K = 2`.
* `RBM.EGDef.primBil_two_eq` — the quadratic term `E^{((L-K)×(L-K))}` at a `2`-loop is the
  (5.49) display.

## Why there is no third term at `n = 2`

(5.15) reads `∂_u(L-K) = Ẽ + Θ_{u,σ}∘(L-K) + ∑_{l_K > 2}[K ∼ (L-K)]^{l_K} + E^{((L-K)×(L-K))}`.
At `n = 2` the only cut is `(k,l) = (1,2)` and both loops it produces have length `2`, so the
whole coupling is its `l_K = 2` piece (`RBM.EGDef.couplingLen_two_of_len_two`) and the sum
over `l_K > 2` is empty.  By (5.19) (`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`) that piece is
`Θ_{u,σ}∘(L-K)`, the generator term of (5.15) (`RBM.SumZeroDyn.genS`).

## Deviation from the literal paper statement

(5.51) contains the `3`-loop `L_{u,(-,+,+),(a₂,b₂,a₁)}`; the two loops that
`RBM.LoopIdx.cutGlue` produces are `(+,+,-)` at `(b,a₁,a₂)` and `(+,-,-)` at `(a₁,b,a₂)`,
i.e. this `(-,+,+)` loop at `(a₂,b,a₁)`.  Accordingly the tail function of (5.35) is read at
`zdist (a₂ - a₁)`.
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
paper's (5.51) prints `(a₁,b₂,a₂)`; (5.35) is therefore applied with its two labels
exchanged. -/
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
`RBM.Gauss.generator_add_zMotion_gauss` puts in the drift of the loop hierarchy.  Pure index
bookkeeping: `RBM.LoopIdx.cutGlue 1 b` and
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

(5.35) is stated for the `(-,+,+)` loop at `(a₁,b,a₂)`.  The two loops
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

`RBM1D/Hierarchy/Lemma57.lean` proves (5.35) for an abstract real `EG` constrained by (5.52);
here `EG` is `‖RBM.EGDef.eGpm …‖`, which unfolds to the Green function of `M`.  Every hypothesis
below is a statement about `RBM.gloop` / `RBM.green` of `M` — there is no structure field on
either side. -/

/-! ### The drift of `L - K` at loop length two

The remaining sections identify the drift `F` of the pointwise identity (5.15) at loop
length `2`:

`F = E^{(G̃)} + E^{((L-K)×(L-K))}`,

with `E^{(G̃)}` the `RBM.EGDef.eGpm` above and `E^{((L-K)×(L-K))}` the quadratic gluing term
(5.49) that (5.34) governs.  **There is no third term**: at `n = 2` every cut of the loop
produces two `2`-loops, so the graded coupling `[K ∼ (L-K)]^{l_K}` is concentrated at
`l_K = 2` (`RBM.EGDef.couplingLen_two_of_len_two`), and (5.19)
(`RBM.Gauss.couplingLen_two_eq_thetaGenLoop`) turns that piece into the generator
`Θ_{u,σ} ∘ (L-K)`, the generator term of (5.15) (`RBM.SumZeroDyn.genS`).
So the `∑_{l_K > 2}` of (5.15) is empty here. -/

section Drift

open Gauss
open scoped Matrix.Norms.L2Operator

/-! #### A second derivative along directions fixed by a projection

The second derivative of the *raw* `RBM.gloop` in the matrix and
`RBM.Gauss.loopIto_second_frozen`, which is stated for `RBM.Gauss.loopObs` (it pre-composes with
the Hermitian projection `RBM.Gauss.hermCLM`, which makes it globally defined), agree at a
Hermitian matrix and along a Hermitian direction, which is the only place either is
evaluated. -/

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

/-! #### The second derivative of the loop is the cut-and-glue right-hand side -/

section Wirt

variable {d : Dims} {N : ℕ}

end Wirt

section Band

variable {Ω : Type*} [MeasurableSpace Ω]

/-! #### The primitive `K` and its equation at a `2`-loop -/

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

variable {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ}

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
