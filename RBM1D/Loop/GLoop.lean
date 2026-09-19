/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Model
import RBM1D.Delocalization
import RBM1D.Loop.Index

/-!
# The `G`-loops of Definition 2.9

For a **fixed deterministic Hermitian** `H` we define

  `G(σ) = (H - z)⁻¹` for `σ = +` and `(H - z̄)⁻¹` for `σ = -`,   (Definition 2.9)
  `L_{σ,a} = ⟨∏_i G(σ_i) E_{a_i}⟩`,  `⟨A⟩ = Tr A`.               (2.41)

Nothing here is probabilistic: the expectation and the Itô calculus of the paper
act on top of this layer, but the definition of the loop and its algebra are
deterministic, and that is what this file provides.

## Main results

* `Gsig_conjTranspose` : `G(σ)† = G(-σ)`, the paper's `G_{t,+}† = G_{t,-}`.
* `green_sub_green` : the resolvent identity `G(z) - G(w) = (z-w) G(z) G(w)`,
  the source of every Ward identity downstream.
* `gloopProd_append`, `gloop_rotate` : the loop is invariant under rotating its
  index data, which is the algebraic content of "loop" in the paper.
-/

namespace RBM

open Matrix

section Gsig

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `G(σ)`: the resolvent at `z` for `σ = true` (the paper's `+`) and at `conj z`
for `σ = false`. -/
noncomputable def Gsig (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  green H (if σ then z else (starRingEnd ℂ) z)

@[simp] theorem Gsig_true (H : Matrix n n ℂ) (z : ℂ) : Gsig H z true = green H z := rfl

@[simp] theorem Gsig_false (H : Matrix n n ℂ) (z : ℂ) :
    Gsig H z false = green H ((starRingEnd ℂ) z) := rfl

/-- `(H - z)ᴴ = H - z̄` for Hermitian `H`. -/
theorem conjTranspose_sub_smul {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) :
    (H - z • (1 : Matrix n n ℂ))ᴴ = H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ) := by
  rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
  rfl

/-- **`G(+)† = G(-)`** (Definition 2.9). -/
theorem Gsig_conjTranspose {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gsig H z σ)ᴴ = Gsig H z (!σ) := by
  cases σ
  · show (green H ((starRingEnd ℂ) z))ᴴ = green H z
    rw [green, green, conjTranspose_nonsing_inv, conjTranspose_sub_smul hH, Complex.conj_conj]
  · show (green H z)ᴴ = green H ((starRingEnd ℂ) z)
    rw [green, green, conjTranspose_nonsing_inv, conjTranspose_sub_smul hH]

/-- **The resolvent identity** `G(z) - G(w) = (z - w) • (G(z) * G(w))`.
Every Ward identity in the paper descends from this one line. -/
theorem green_sub_green {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ))) (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z - green H w = (z - w) • (green H z * green H w) := by
  have hz' : green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hz)
  have hw' : (H - w • (1 : Matrix n n ℂ)) * green H w = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hw)
  calc green H z - green H w
      = green H z * ((H - w • (1 : Matrix n n ℂ)) * green H w)
        - (green H z * (H - z • (1 : Matrix n n ℂ))) * green H w := by
        rw [hz', hw', Matrix.one_mul, Matrix.mul_one]
    _ = green H z * ((H - w • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ)))
        * green H w := by
        noncomm_ring
    _ = green H z * ((z - w) • (1 : Matrix n n ℂ)) * green H w := by
        congr 2
        module
    _ = (z - w) • (green H z * green H w) := by
        simp [mul_smul_comm, smul_mul_assoc]

/-- **The Ward identity in resolvent form.**  With `z = E + iη`,
`G(z) - G(z̄) = 2iη · G(z)G(z̄)`, i.e. `Im G = η G G†`.  This is the special case
`w = z̄` of `green_sub_green`, and it is the form used throughout the paper. -/
theorem green_sub_green_conj {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ)) • (green H z * green H ((starRingEnd ℂ) z)) := by
  rw [green_sub_green hz hz']
  congr 1
  rw [Complex.sub_conj]
  push_cast
  ring

/-- **The Ward identity, traced against an observable.**  For `z = E + iη`,
\[ \operatorname{Tr}(G(z)A) - \operatorname{Tr}(G(\bar z)A) = 2i\eta\,
   \operatorname{Tr}(G(z)G(\bar z)A) , \]
which is the self-improving identity behind the local law: the left-hand side is
`2i` times the imaginary part of a single resolvent, while the right-hand side is a
positive quadratic form. -/
theorem trace_green_sub_trace_green_conj {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) (A : Matrix n n ℂ) :
    Matrix.trace (green H z * A) - Matrix.trace (green H ((starRingEnd ℂ) z) * A)
      = (2 * Complex.I * (z.im : ℂ))
          * Matrix.trace (green H z * green H ((starRingEnd ℂ) z) * A) := by
  have h := congrArg (fun M : Matrix n n ℂ => Matrix.trace (M * A)) (green_sub_green_conj hz hz')
  simpa [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc] using h

/-- The Ward identity with the two resolvents in the other order.  `G(z)` and
`G(\bar z)` commute (both are functions of `H`), but it is cheaper to get the second
order from `green_sub_green` with the arguments swapped than to prove commutation. -/
theorem green_sub_green_conj' {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) :
    green H z - green H ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ)) • (green H ((starRingEnd ℂ) z) * green H z) := by
  have h := green_sub_green hz' hz
  have hc : (2 * Complex.I * (z.im : ℂ)) = -((starRingEnd ℂ) z - z) := by
    have h0 := Complex.sub_conj z
    push_cast at h0
    linear_combination -h0
  rw [hc, neg_smul, ← h]
  abel

/-- The traced Ward identity, with the resolvents in the order `G(\bar z)G(z)`. -/
theorem trace_green_sub_trace_green_conj' {H : Matrix n n ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) (A : Matrix n n ℂ) :
    Matrix.trace (green H z * A) - Matrix.trace (green H ((starRingEnd ℂ) z) * A)
      = (2 * Complex.I * (z.im : ℂ))
          * Matrix.trace (green H ((starRingEnd ℂ) z) * green H z * A) := by
  have h := congrArg (fun M : Matrix n n ℂ => Matrix.trace (M * A)) (green_sub_green_conj' hz hz')
  simpa [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.mul_assoc] using h

/-- **The Ward identity in its most usable form**: for Hermitian `H` and `z = E + iη`,
\[ \operatorname{Im} G_{qq} \;=\; \eta \sum_p |G_{pq}|^2 . \]
The whole column of the Green's function is controlled by one diagonal entry, which is
what makes `|ψ_k(x)|² ≤ η\,\operatorname{Im}G_{xx}` (equation (2.10)) useful. -/
theorem im_green_apply_eq_mul_sum_normSq {H : Matrix n n ℂ} {z : ℂ} (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) (q : n) :
    (green H z q q).im = z.im * ∑ p : n, Complex.normSq (green H z p q) := by
  have hG : green H ((starRingEnd ℂ) z) = (green H z)ᴴ := (Gsig_conjTranspose hH z true).symm
  have h := green_sub_green_conj' hz hz'
  rw [hG] at h
  have hqq : (green H z - (green H z)ᴴ) q q
      = ((2 * Complex.I * (z.im : ℂ)) • ((green H z)ᴴ * green H z)) q q := by rw [h]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    smul_eq_mul, Complex.star_def] at hqq
  have hterm : ∀ r : n, (starRingEnd ℂ) (green H z r q) * green H z r q
      = (Complex.normSq (green H z r q) : ℂ) := by
    intro r
    rw [mul_comm]
    exact Complex.mul_conj _
  simp only [hterm] at hqq
  rw [Complex.sub_conj] at hqq
  have hcast : ((green H z q q).im : ℂ)
      = ((z.im * ∑ p : n, Complex.normSq (green H z p q) : ℝ) : ℂ) := by
    have h2I : (2 : ℂ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero]
    refine mul_left_cancel₀ h2I ?_
    push_cast at hqq ⊢
    linear_combination hqq
  exact_mod_cast hcast

/-- Each entry of a column is bounded by the diagonal entry: `η|G_{pq}|² ≤ Im G_{qq}`. -/
theorem normSq_green_le_im_green {H : Matrix n n ℂ} {z : ℂ} (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix n n ℂ))) (hη : 0 < z.im) (p q : n) :
    z.im * Complex.normSq (green H z p q) ≤ (green H z q q).im := by
  rw [im_green_apply_eq_mul_sum_normSq hH hz hz' q]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun r _ => Complex.normSq_nonneg (green H z r q)) (Finset.mem_univ p))
    hη.le

end Gsig

section Loop

variable (L W : ℕ) [NeZero L] [NeZero W]

/-- The matrix product `∏_i G(σ_i) E_{a_i}` of (2.41). -/
noncomputable def gloopProd (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  (I.σ.zip I.a).foldr (fun p M => Gsig H z p.1 * Eblk L W p.2 * M) 1

/-- **The `n`-`G` loop of (2.41)**, `L_{σ,a} = ⟨∏_i G(σ_i) E_{a_i}⟩`. -/
noncomputable def gloop (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) : ℂ :=
  Matrix.trace (gloopProd L W H z I)

variable {L W} {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

@[simp] theorem gloopProd_nil : gloopProd L W H z ⟨[], []⟩ = 1 := rfl

@[simp] theorem gloopProd_cons (s : Bool) (b : ZMod L) (σ : List Bool) (a : List (ZMod L)) :
    gloopProd L W H z ⟨s :: σ, b :: a⟩
      = Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩ := rfl

/-- The loop product of a concatenation is the product of the loop products.
Requires the two blocks to be well formed, so that `zip` distributes. -/
theorem gloopProd_append {σ₁ : List Bool} {a₁ : List (ZMod L)} (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (ZMod L)) :
    gloopProd L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩
      = gloopProd L W H z ⟨σ₁, a₁⟩ * gloopProd L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, gloopProd_cons, ih h, Matrix.mul_assoc]

/-- **The loop is a loop**: rotating the index data by one place does not change it.
This is the trace cyclicity behind every "loop" statement in the paper. -/
theorem gloop_rotate (s : Bool) (b : ZMod L) {σ : List Bool} {a : List (ZMod L)}
    (h : σ.length = a.length) :
    gloop L W H z ⟨s :: σ, b :: a⟩ = gloop L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [gloop, gloop, gloopProd_cons, gloopProd_append h [s] [b]]
  rw [Matrix.trace_mul_comm]
  simp only [gloopProd_cons, gloopProd_nil, Matrix.mul_one]

/-- **Summing one block index.**  Because `∑_a E_a = W⁻¹ I` (`sum_Eblk`), summing a
loop over one of its labels deletes that `E` and produces a factor `W⁻¹`.
This is the first step of the paper's Ward identity for loops. -/
theorem sum_gloop_head (s : Bool) (σ : List Bool) (a : List (ZMod L)) :
    ∑ b : ZMod L, gloop L W H z ⟨s :: σ, b :: a⟩
      = (W : ℂ)⁻¹ * Matrix.trace (Gsig H z s * gloopProd L W H z ⟨σ, a⟩) := by
  have hterm : ∀ b : ZMod L, gloop L W H z ⟨s :: σ, b :: a⟩
      = Matrix.trace (Gsig H z s * Eblk L W b * gloopProd L W H z ⟨σ, a⟩) := fun _ => rfl
  simp_rw [hterm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, ← Finset.mul_sum, sum_Eblk L W]
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The `2`-loop, unfolded.  This is the quantity `Tr(G(z)E_a G^†(z)E_b)` of
Theorem 2.4, which the paper writes as `L_{(+,-),(a,b)}`. -/
theorem gloop_two (s₁ s₂ : Bool) (b₁ b₂ : ZMod L) :
    gloop L W H z ⟨[s₁, s₂], [b₁, b₂]⟩
      = Matrix.trace (Gsig H z s₁ * Eblk L W b₁ * (Gsig H z s₂ * Eblk L W b₂)) := by
  simp [gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one]

/-- **The Ward identity for the `2`-loop.**  Summing `L_{(+,-),(a,b)}` over the free
label `b` and multiplying by `2i\eta` gives the imaginary part of a *single* resolvent:
\[ 2i\eta \sum_b \mathcal L_{(+,-),(a,b)}
   = W^{-1}\bigl(\operatorname{Tr}(G(z)E_a) - \operatorname{Tr}(G(\bar z)E_a)\bigr). \]
This is the identity that makes the local law self-improving: a quadratic quantity on
the left, a linear one on the right.  Both ingredients are already here --- rotation
invariance moves `b` to the head, `sum_gloop_head` deletes its `E`, and the traced
Ward identity collapses the product of resolvents. -/
theorem sum_gloop_two_ward {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (a : ZMod L) :
    (2 * Complex.I * (z.im : ℂ)) * ∑ b : ZMod L, gloop L W H z ⟨[true, false], [a, b]⟩
      = (W : ℂ)⁻¹ * (Matrix.trace (green H z * Eblk L W a)
          - Matrix.trace (green H ((starRingEnd ℂ) z) * Eblk L W a)) := by
  have hrot : ∀ b : ZMod L, gloop L W H z ⟨[true, false], [a, b]⟩
      = gloop L W H z ⟨[false, true], [b, a]⟩ := fun b => gloop_rotate true a rfl
  simp_rw [hrot]
  rw [sum_gloop_head, trace_green_sub_trace_green_conj' hz hz' (Eblk L W a)]
  have hprod : gloopProd L W H z ⟨[true], [a]⟩ = green H z * Eblk L W a := by
    simp [gloopProd_cons, gloopProd_nil]
  rw [hprod]
  show (2 * Complex.I * (z.im : ℂ)) * ((W : ℂ)⁻¹ *
      Matrix.trace (green H ((starRingEnd ℂ) z) * (green H z * Eblk L W a))) = _
  rw [← Matrix.mul_assoc]
  ring

/-- **The `(+,-)` `2`-loop is a sum of squared Green's function entries.**
\[ \mathcal L_{(+,-),(a,b)}
   = W^{-2}\sum_{p \in I_b}\sum_{q \in I_a} \bigl|G_{pq}\bigr|^2 . \]
This is the bridge between the loop layer and delocalization: the left-hand side is
what the loop hierarchy evolves, the right-hand side is the mass of the Green's
function between the blocks `I_b` and `I_a`.  In particular the loop is a nonnegative
real. -/
theorem gloop_two_plus_minus {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (a b : ZMod L) :
    gloop L W H z ⟨[true, false], [a, b]⟩
      = ((W : ℂ)⁻¹) ^ 2 * ∑ p : ZMod L × Fin W, ∑ q : ZMod L × Fin W,
          (if p.1 = b then if q.1 = a then (Complex.normSq (green H z p q) : ℂ) else 0
            else 0) := by
  have hG : green H ((starRingEnd ℂ) z) = (green H z)ᴴ := (Gsig_conjTranspose hH z true).symm
  have hdiag : ∀ p : ZMod L × Fin W,
      Matrix.diag (green H z * Eblk L W a * ((green H z)ᴴ * Eblk L W b)) p
        = ∑ q : ZMod L × Fin W,
            (green H z p q * (if q.1 = a then (W : ℂ)⁻¹ else 0))
              * ((starRingEnd ℂ) (green H z p q) * (if p.1 = b then (W : ℂ)⁻¹ else 0)) := by
    intro p
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    · simp only [Eblk, Matrix.mul_diagonal]
    · simp only [Eblk, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def]
  have hterm : ∀ p q : ZMod L × Fin W,
      (green H z p q * (if q.1 = a then (W : ℂ)⁻¹ else 0))
          * ((starRingEnd ℂ) (green H z p q) * (if p.1 = b then (W : ℂ)⁻¹ else 0))
        = ((W : ℂ)⁻¹) ^ 2
            * (if p.1 = b then if q.1 = a then (Complex.normSq (green H z p q) : ℂ) else 0
                else 0) := by
    intro p q
    rw [mul_mul_mul_comm, Complex.mul_conj]
    split_ifs <;> ring
  rw [gloop_two]
  simp only [Gsig_true, Gsig_false, hG]
  rw [Matrix.trace]
  simp only [hdiag, hterm, ← Finset.mul_sum]

/-- Collapsing the two block indicators: a double sum over `Z_L × Fin W` restricted to
the blocks `I_b` and `I_a` is a double sum over `Fin W`. -/
theorem sum_block_ite (f : ZMod L × Fin W → ZMod L × Fin W → ℂ) (a b : ZMod L) :
    (∑ p : ZMod L × Fin W, ∑ q : ZMod L × Fin W,
        (if p.1 = b then if q.1 = a then f p q else 0 else 0))
      = ∑ β : Fin W, ∑ α : Fin W, f (b, β) (a, α) := by
  have hq : ∀ p : ZMod L × Fin W,
      (∑ q : ZMod L × Fin W, (if p.1 = b then if q.1 = a then f p q else 0 else 0))
        = if p.1 = b then ∑ α : Fin W, f p (a, α) else 0 := by
    intro p
    by_cases hp : p.1 = b
    · simp only [if_pos hp, Fintype.sum_prod_type]
      refine (Finset.sum_eq_single a ?_ ?_).trans ?_
      · intro q₁ _ hne
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ a) h
      · simp
    · simp [hp]
  simp_rw [hq]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_eq_single b ?_ ?_).trans ?_
  · intro p₁ _ hne
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ b) h
  · simp

/-- `L_{(+,-),(a,b)} = W^{-2} ∑_{β,α} |G_{(b,β),(a,α)}|²`, with the sums over the two
blocks written out. -/
theorem gloop_two_plus_minus_blocks {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (a b : ZMod L) :
    gloop L W H z ⟨[true, false], [a, b]⟩
      = ((W : ℂ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W,
          (Complex.normSq (green H z (b, β) (a, α)) : ℂ) := by
  rw [gloop_two_plus_minus hH a b, sum_block_ite]

/-- **The `(+,-)` `2`-loop is a nonnegative real.**  It is `W^{-2}` times the mass of
the Green's function between the blocks `I_b` and `I_a`. -/
theorem gloop_two_plus_minus_nonneg {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) (a b : ZMod L) :
    ∃ r : ℝ, 0 ≤ r ∧ gloop L W H z ⟨[true, false], [a, b]⟩ = (r : ℂ) := by
  refine ⟨((W : ℝ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W,
      Complex.normSq (green H z (b, β) (a, α)), ?_, ?_⟩
  · have : (0 : ℝ) ≤ ∑ β : Fin W, ∑ α : Fin W,
        Complex.normSq (green H z (b, β) (a, α)) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    positivity
  · rw [gloop_two_plus_minus_blocks hH a b]
    push_cast
    ring

end Loop

end RBM
