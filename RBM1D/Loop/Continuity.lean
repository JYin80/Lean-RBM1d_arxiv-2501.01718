/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Chain
import RBM1D.Loop.Ward
import Mathlib.Algebra.Order.Chebyshev

/-!
# The deterministic skeleton of §6 (continuity estimates on loops)

Section 6 of the paper proves Lemma 5.1 by comparing the loops at time `t₂` with loops
whose resolvent is `G̃ = (H_{t₂} - z̃_{t₁})⁻¹`, `z̃_{t₁} := (t₂/t₁)^{1/2} z_{t₁}`.  This file
collects everything in that argument that is deterministic linear algebra or arithmetic:
a fixed Hermitian `H` throughout, no expectation and no `≺`.

## Main results

* `isUnit_sub_smul_one_of_im_ne_zero` : `H - z` is invertible for Hermitian `H`, `Im z ≠ 0`.
* `green_eq_add_smul_mul`, `Gsig_eq_add_smul_mul` : **(6.3)** `G = G̃ + (z - z̃) G G̃`.
* `list_prod_add_eq` : **(6.7)** the telescoping identity for noncommuting products.
* `gchain_eq_add_sum_gchainMixed` : **(6.8)** the chain expansion.
* `norm_gchain_apply_sq_le` : **(6.9)** the termwise Cauchy–Schwarz bound (`C_m = m + 1`).
* `gloop_symm_eq_trace` : **(6.5)** the symmetric loop `⟨E_{a₀} C E_{a_m} C†⟩`.
* `ward_chain_row`, `ward_chain_row'` : **(6.12)** the Ward step
  `W⁻¹ ∑_{i∈I_{a₀}} ‖v^{(l)}‖² = (2i Im z)⁻¹ (L_{σ^{(1)}} - L_{σ^{(2)}})`.
* `ztTilde`, `ztTilde_arith` : the arithmetic of `z̃_{t₁}` quoted in §6:
  `|z_{t₂} - z̃_{t₁}| ≤ C(1-t₁)`, `|z_{t₂} - z̃_{t₁}|² ≤ Cη_{t₁}²`,
  `|z_{t₂} - z̃_{t₁}|²/Im z̃_{t₁} ≤ Cη_{t₁}`, `η_{t₁} ≤ Im z̃_{t₁} ≤ Cη_{t₁}`.

## Deviations from the paper

* (6.3) is stated for one Hermitian `H` and two spectral parameters; that the paper's `H`
  is `H_{t₂}` for both `G` and `G̃` is a matter of instantiation.
* (6.8) is proved by direct induction on the chain rather than by substituting into (6.7);
  both are here.  Indices are counted from `0`; the scalar in front of the `l`-th term is
  `z_{σ_l} - z̃_{σ_l}` (`z̄ - \bar{z̃}` for a `-` charge), whose modulus is `|z - z̃|`.
* (6.9): the unspecified `C_m` is `m + 1`, `m` the number of resolvents in the chain.
* (6.12): the loop labels are `(a_1, …, a_{l-1}, a_{l-1}, …, a_1, a_0)`, a cyclic rotation
  of the paper's `(a_0, a_1, …, a_{l-1}, a_{l-1}, …, a_1)`; the loop value is the same.
* `z̃` arithmetic: the paper assumes `c < t₁ ≤ t₂ ≤ 1`; we assume `c ≤ t₁ ≤ t₂ ≤ 1`.  The
  bounds in terms of `η_{t₁}` need `Im m^{(E)} ≳ 1`, i.e. a bulk hypothesis `|E| ≤ 2 - κ`
  (implicit in the paper, where `E` is fixed in the bulk).  The bound
  `|z_{t₂} - z̃_{t₁}| ≤ C(1-t₁)` needs only `|E| ≤ 2`, and we prove the sharper
  `≤ C(t₂ - t₁)` (`norm_zt_sub_ztTilde_le`), as the paper's `≤ C|t₂ - t₁|` indicates.
-/

namespace RBM

open Matrix

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral parameter carried by the charge `s`: `z` for `+`, `z̄` for `-`.
By definition `Gsig H z s = green H (zSig z s)`. -/
def zSig (z : ℂ) (s : Bool) : ℂ := if s then z else (starRingEnd ℂ) z

@[simp] theorem zSig_true (z : ℂ) : zSig z true = z := rfl

@[simp] theorem zSig_false (z : ℂ) : zSig z false = (starRingEnd ℂ) z := rfl

theorem Gsig_eq_green_zSig (H : Matrix n n ℂ) (z : ℂ) (s : Bool) :
    Gsig H z s = green H (zSig z s) := rfl

theorem norm_zSig_sub_zSig (z w : ℂ) (s : Bool) : ‖zSig z s - zSig w s‖ = ‖z - w‖ := by
  cases s
  · simp only [zSig_false, ← map_sub, Complex.norm_conj]
  · rfl

theorem im_zSig (z : ℂ) (s : Bool) : (zSig z s).im = if s then z.im else -z.im := by
  cases s <;> simp

/-- A Hermitian matrix minus a non-real multiple of the identity is invertible. -/
theorem isUnit_sub_smul_one_of_im_ne_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix n n ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hHv : H *ᵥ v = z • v := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  have him := hH.im_star_dotProduct_mulVec_self v
  rw [hHv, dotProduct_smul, smul_eq_mul] at him
  have hd : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, Complex.mul_conj]
  have hpos : (∑ i, Complex.normSq (v i) : ℝ) ≠ 0 := by
    intro h0
    apply hv0
    funext i
    exact Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (v j))).mp h0 i (Finset.mem_univ i))
  rw [hd, RCLike.im_to_complex, Complex.im_mul_ofReal] at him
  exact hz ((mul_eq_zero.mp him).resolve_right hpos)

theorem isUnit_sub_zSig {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (s : Bool) : IsUnit (H - zSig z s • (1 : Matrix n n ℂ)) := by
  refine isUnit_sub_smul_one_of_im_ne_zero hH ?_
  rw [im_zSig]
  split_ifs
  · exact hz
  · exact neg_ne_zero.mpr hz

/-- **(6.3)**, the two-parameter resolvent identity `G = G̃ + (z - z̃)·G·G̃`, where
`G = (H - z)⁻¹` and `G̃ = (H - z̃)⁻¹` share the same matrix `H`. -/
theorem green_eq_add_smul_mul {H : Matrix n n ℂ} {z w : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix n n ℂ))) (hw : IsUnit (H - w • (1 : Matrix n n ℂ))) :
    green H z = green H w + (z - w) • (green H z * green H w) := by
  rw [← green_sub_green hz hw]
  abel

/-- **(6.3) with charges**: `G(σ) = G̃(σ) + (z_σ - z̃_σ)·G(σ)·G̃(σ)`, where `z_+ = z` and
`z_- = z̄`. -/
theorem Gsig_eq_add_smul_mul {H : Matrix n n ℂ} {z w : ℂ} {s : Bool}
    (hz : IsUnit (H - zSig z s • (1 : Matrix n n ℂ)))
    (hw : IsUnit (H - zSig w s • (1 : Matrix n n ℂ))) :
    Gsig H z s = Gsig H w s + (zSig z s - zSig w s) • (Gsig H z s * Gsig H w s) :=
  green_eq_add_smul_mul hz hw

end Spectral

section Telescope

variable {R : Type*} [Ring R]

/-- **(6.7)**, the telescoping product identity for noncommuting factors:
\[ \prod_{k<m}(a_k+b_k) = \prod_{k<m}a_k
    + \sum_{l<m}\Bigl(\prod_{j<l}(a_j+b_j)\Bigr)\,b_l\,\Bigl(\prod_{l<j<m}a_j\Bigr), \]
all products taken in increasing order of the index. -/
theorem list_prod_add_eq (a b : ℕ → R) (m : ℕ) :
    ((List.range m).map fun k => a k + b k).prod
      = ((List.range m).map a).prod
        + ∑ l ∈ Finset.range m, ((List.range l).map fun k => a k + b k).prod * b l
            * ((List.range' (l + 1) (m - (l + 1))).map a).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsuf : ∀ l ∈ Finset.range m,
        ((List.range' (l + 1) (m + 1 - (l + 1))).map a).prod
          = ((List.range' (l + 1) (m - (l + 1))).map a).prod * a m := by
      intro l hl
      have hl' : l < m := Finset.mem_range.mp hl
      have h1 : m + 1 - (l + 1) = (m - (l + 1)) + 1 := by omega
      have h2 : l + 1 + 1 * (m - (l + 1)) = m := by omega
      rw [h1, List.range'_concat, h2, List.map_append, List.prod_append]
      simp
    have hsum : ∑ l ∈ Finset.range m, ((List.range l).map fun k => a k + b k).prod * b l
            * ((List.range' (l + 1) (m + 1 - (l + 1))).map a).prod
          = (∑ l ∈ Finset.range m, ((List.range l).map fun k => a k + b k).prod * b l
            * ((List.range' (l + 1) (m - (l + 1))).map a).prod) * a m := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l hl => ?_
      rw [hsuf l hl]; simp only [mul_assoc]
    rw [Finset.sum_range_succ, hsum, List.range_succ, List.map_append, List.prod_append,
      List.map_append, List.prod_append, Nat.sub_self]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.range'_zero]
    rw [mul_add, ih, add_mul, add_mul]
    abel

end Telescope

section ChainExpansion

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}

/-- The `l`-th term of the chain expansion (6.8): the mixed chain
`G_1 E_{a_1} ⋯ E_{a_{l-1}} G_l · G̃_l E_{a_l} G̃_{l+1} ⋯ E_{a_{m-1}} G̃_m`
(indices counted from `0` here), with `l+1` resolvents at `z` and `m-l` at `w = z̃`, and
no `E` between `G_l` and `G̃_l`. -/
noncomputable def gchainMixed (L W : ℕ) [NeZero L] [NeZero W]
    (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z w : ℂ) (τ : List Bool)
    (a : List (ZMod L)) (l : ℕ) : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ :=
  gchain L W H z (τ.take (l + 1)) (a.take l) * gchain L W H w (τ.drop l) (a.drop l)

/-- **(6.8)**, the chain expansion.  If every resolvent of the chain at `z` is expanded
around `w = z̃` by (6.3), then
\[ C_z = C_w + \sum_{l} (z_{σ_l} - w_{σ_l})\,
      G_1E_{a_1}\cdots G_l\cdot\tilde G_lE_{a_l}\cdots\tilde G_m . \]
This is (6.7) with `a_k + b_k ↦ G_k E_{a_k}`, `a_k ↦ G̃_k E_{a_k}`; we prove it directly
by induction on the chain. -/
theorem gchain_eq_add_sum_gchainMixed {z w : ℂ}
    (hz : ∀ s, IsUnit (H - zSig z s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (hw : ∀ s, IsUnit (H - zSig w s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    {τ : List Bool} {a : List (ZMod L)} (h : τ.length = a.length + 1) :
    gchain L W H z τ a = gchain L W H w τ a
      + ∑ l ∈ Finset.range τ.length,
          (zSig z (τ.getD l true) - zSig w (τ.getD l true)) • gchainMixed L W H z w τ a l := by
  induction τ generalizing a with
  | nil => simp at h
  | cons s τ ih =>
    cases a with
    | nil =>
      have hτ : τ = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst hτ
      simp only [gchainMixed, List.length_singleton, Finset.sum_range_one, List.getD_cons_zero,
        List.drop_zero, gchain_single, List.take_succ_cons, List.take_nil]
      exact Gsig_eq_add_smul_mul (hz s) (hw s)
    | cons c a =>
      have h' : τ.length = a.length + 1 := by simpa using h
      have key : Gsig H z s * Eblk L W c * gchain L W H w τ a
          = gchain L W H w (s :: τ) (c :: a)
            + (zSig z s - zSig w s) • (Gsig H z s * gchain L W H w (s :: τ) (c :: a)) := by
        rw [gchain_cons]
        nth_rewrite 1 [Gsig_eq_add_smul_mul (hz s) (hw s)]
        simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]
      rw [gchain_cons, ih h', Matrix.mul_add, key, List.length_cons, Finset.sum_range_succ']
      simp only [gchainMixed, gchain_cons, List.take_succ_cons, List.drop_succ_cons,
        List.getD_cons_succ, List.getD_cons_zero, List.take_zero, List.drop_zero, gchain_single]
      simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.mul_assoc]
      abel

/-- The elementary Cauchy–Schwarz step behind (6.9):
`‖x + ∑_{l<m} y_l‖² ≤ (m+1)(‖x‖² + ∑_{l<m} ‖y_l‖²)`. -/
theorem norm_add_sum_sq_le {E : Type*} [SeminormedAddCommGroup E] (x : E) (y : ℕ → E)
    (m : ℕ) :
    ‖x + ∑ l ∈ Finset.range m, y l‖ ^ 2
      ≤ (m + 1 : ℝ) * (‖x‖ ^ 2 + ∑ l ∈ Finset.range m, ‖y l‖ ^ 2) := by
  set f : ℕ → ℝ := fun k => if k = 0 then ‖x‖ else ‖y (k - 1)‖ with hf
  have hsum : ∑ k ∈ Finset.range (m + 1), f k = ‖x‖ + ∑ l ∈ Finset.range m, ‖y l‖ := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hf]
  have hsum2 : ∑ k ∈ Finset.range (m + 1), f k ^ 2
      = ‖x‖ ^ 2 + ∑ l ∈ Finset.range m, ‖y l‖ ^ 2 := by
    rw [Finset.sum_range_succ', add_comm]
    simp [hf]
  have h1 : ‖x + ∑ l ∈ Finset.range m, y l‖ ≤ ∑ k ∈ Finset.range (m + 1), f k := by
    rw [hsum]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1)) (f := f)
  rw [Finset.card_range, hsum2] at h2
  push_cast at h2
  calc ‖x + ∑ l ∈ Finset.range m, y l‖ ^ 2 ≤ (∑ k ∈ Finset.range (m + 1), f k) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- **(6.9)**, the termwise Cauchy–Schwarz bound: for every entry `(i, j)`,
\[ |(C_z)_{ij}|^2 \le (m+1)\Bigl(|(C_{w})_{ij}|^2
      + |z-w|^2\sum_{l<m}\bigl|(G_1E_{a_1}\cdots G_l\tilde G_l\cdots\tilde G_m)_{ij}\bigr|^2\Bigr),
\]
`m` the number of resolvents in the chain.  The paper's `C_m` is `m + 1` here. -/
theorem norm_gchain_apply_sq_le {z w : ℂ}
    (hz : ∀ s, IsUnit (H - zSig z s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (hw : ∀ s, IsUnit (H - zSig w s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    {τ : List Bool} {a : List (ZMod L)} (h : τ.length = a.length + 1)
    (i j : ZMod L × Fin W) :
    ‖gchain L W H z τ a i j‖ ^ 2
      ≤ (τ.length + 1 : ℝ) * (‖gchain L W H w τ a i j‖ ^ 2
          + ‖z - w‖ ^ 2 * ∑ l ∈ Finset.range τ.length, ‖gchainMixed L W H z w τ a l i j‖ ^ 2) := by
  have hij := congrFun (congrFun (gchain_eq_add_sum_gchainMixed hz hw h) i) j
  rw [Matrix.add_apply, Matrix.sum_apply] at hij
  rw [hij]
  refine (norm_add_sum_sq_le _ _ _).trans_eq ?_
  congr 2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_zSig_sub_zSig, mul_pow]

end ChainExpansion

section SymmetricLoop

variable {L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
  {z : ℂ}

/-- **(6.5)**, the symmetric loop in normal form:
\[ \mathcal L_{σ',a'} = \langle E_{a_0}\,C_{σ,a}\,E_{a_m}\,C_{σ,a}^\dagger\rangle, \]
with `σ' = (σ_1, …, σ_m, \bar σ_m, …, \bar σ_1)` and
`a' = (a_1, …, a_{m-1}, a_m, a_{m-1}, …, a_1, a_0)`. -/
theorem gloop_symm_eq_trace (hH : H.IsHermitian) {τ : List Bool} {a : List (ZMod L)}
    (h : τ.length = a.length + 1) (am a0 : ZMod L) :
    gloop L W H z ⟨τ ++ (τ.map (!·)).reverse, (a ++ [am]) ++ (a.reverse ++ [a0])⟩
      = Matrix.trace (Eblk L W a0 * gchain L W H z τ a * Eblk L W am
          * (gchain L W H z τ a)ᴴ) := by
  have h' : (τ.map (!·)).reverse.length = a.reverse.length + 1 := by simpa using h
  have hlen : τ.length = (a ++ [am]).length := by simpa using h
  rw [gchain_conjTranspose hH h, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (Eblk L W a0), gchain_mul_Eblk h,
    gchain_mul_Eblk h', gloop, gloopProd_append hlen]

/-- A chain ending in `G(s)` is the loop product of its first blocks times `G(s)`. -/
theorem gchain_append_singleton {ρ : List Bool} {b : List (ZMod L)} (h : ρ.length = b.length)
    (s : Bool) :
    gchain L W H z (ρ ++ [s]) b = gloopProd L W H z ⟨ρ, b⟩ * Gsig H z s := by
  induction ρ generalizing b with
  | nil =>
    obtain rfl : b = [] := List.eq_nil_of_length_eq_zero h.symm
    simp
  | cons r ρ ih =>
    cases b with
    | nil => simp at h
    | cons c b =>
      have h' : ρ.length = b.length := by simpa using h
      rw [List.cons_append, gchain_cons, ih h', gloopProd_cons]
      simp only [Matrix.mul_assoc]

omit [NeZero W] in
/-- `2iη·G(σ)G(σ)† = G(+) - G(-)` for either charge `σ`: the resolvent form of Ward's
identity `G G† = (G - G†)/(2i Im z)` used twice in §6. -/
theorem Gsig_mul_conjTranspose (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (s : Bool) :
    (2 * Complex.I * (z.im : ℂ)) • (Gsig H z s * (Gsig H z s)ᴴ)
      = Gsig H z true - Gsig H z false := by
  rw [Gsig_conjTranspose hH]
  cases s
  · exact (green_sub_green_conj' hz hz').symm
  · exact (green_sub_green_conj hz hz').symm

omit [NeZero W] in
/-- `⟨E_{a₀} P P†⟩ = W⁻¹ ∑_{i ∈ I_{a₀}} ‖P_{i·}‖²`: the trace against a block projection
is the averaged squared row norm. -/
theorem trace_Eblk_mul_mul_conjTranspose (P : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (a0 : ZMod L) :
    Matrix.trace (Eblk L W a0 * P * Pᴴ)
      = (W : ℂ)⁻¹ * ∑ α : Fin W, ∑ k : ZMod L × Fin W, (Complex.normSq (P (a0, α) k) : ℂ) := by
  have hdiag : ∀ p : ZMod L × Fin W, (Eblk L W a0 * P * Pᴴ) p p
      = if p.1 = a0 then (W : ℂ)⁻¹ * ∑ k, (Complex.normSq (P p k) : ℂ) else 0 := by
    intro p
    rw [Matrix.mul_assoc, Eblk, Matrix.diagonal_mul]
    split_ifs
    · congr 1
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj]
    · simp
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, hdiag]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a0]
  · simp [Finset.mul_sum]
  · intro b _ hb
    simp [hb]
  · intro h; exact absurd (Finset.mem_univ a0) h

/-- Closing a half-chain around `G(s')` gives a symmetric loop of odd length:
`⟨E_{a₀} Q G(s') Q†⟩ = L_{(ρ, s', \bar ρ^{rev}), (b, b^{rev}, a₀)}` with
`Q = G_1E_{b_1}⋯G_kE_{b_k}`. -/
theorem trace_Eblk_gloopProd_Gsig_conjTranspose (hH : H.IsHermitian) {ρ : List Bool}
    {b : List (ZMod L)} (h : ρ.length = b.length) (s : Bool) (a0 : ZMod L) :
    Matrix.trace (Eblk L W a0 * gloopProd L W H z ⟨ρ, b⟩ * Gsig H z s
        * (gloopProd L W H z ⟨ρ, b⟩)ᴴ)
      = gloop L W H z ⟨ρ ++ s :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  have hG : Gsig H z s * (gloopProd L W H z ⟨ρ, b⟩)ᴴ
      = gchain L W H z (s :: (ρ.map (!·)).reverse) b.reverse := by
    have hc := gchain_conjTranspose (H := H) (z := z) (L := L) (W := W) hH
      (tau := ρ ++ [!s]) (a := b) (by simpa using h)
    rw [gchain_append_singleton h, Matrix.conjTranspose_mul, Gsig_conjTranspose hH,
      Bool.not_not] at hc
    rw [hc]
    simp
  have h' : (s :: (ρ.map (!·)).reverse).length = b.reverse.length + 1 := by simpa using h
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.trace_mul_comm, Matrix.mul_assoc,
    gchain_mul_Eblk h', gloop, gloopProd_append h]

/-- **(6.12)**, the Ward step.  With `v^{(l)}_k = (G_1E_{a_1}⋯E_{a_{l-1}}G_l)_{ik}`,
\[ 2i\operatorname{Im}z\cdot W^{-1}\sum_{i\in I_{a_0}}\|v^{(l)}\|_2^2
    = \mathcal L_{σ^{(1)}_l, \mathbf a_l} - \mathcal L_{σ^{(2)}_l, \mathbf a_l}, \]
where `σ^{(1,2)}_l = (σ_1, …, σ_{l-1}, ±, \bar σ_{l-1}, …, \bar σ_1)` and
`a_l = (a_1, …, a_{l-1}, a_{l-1}, …, a_1, a_0)` (a rotation of the paper's labelling).
Here the chain is `gchain (ρ ++ [s]) b` with `ρ = (σ_1, …, σ_{l-1})`, `s = σ_l`,
`b = (a_1, …, a_{l-1})`; the right side does not depend on `s`. -/
theorem ward_chain_row (hH : H.IsHermitian)
    (hz : IsUnit (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    {ρ : List Bool} {b : List (ZMod L)} (h : ρ.length = b.length) (s : Bool) (a0 : ZMod L) :
    (2 * Complex.I * (z.im : ℂ)) * ((W : ℂ)⁻¹ * ∑ α : Fin W, ∑ k : ZMod L × Fin W,
        (Complex.normSq (gchain L W H z (ρ ++ [s]) b (a0, α) k) : ℂ))
      = gloop L W H z ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
        - gloop L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩ := by
  rw [← trace_Eblk_mul_mul_conjTranspose, ← trace_Eblk_gloopProd_Gsig_conjTranspose hH h,
    ← trace_Eblk_gloopProd_Gsig_conjTranspose hH h, ← Matrix.trace_sub, ← smul_eq_mul, ← Matrix.trace_smul,
    gchain_append_singleton h, Matrix.conjTranspose_mul]
  congr 1
  set Q := gloopProd L W H z ⟨ρ, b⟩
  have hW := Gsig_mul_conjTranspose hH hz hz' s
  calc (2 * Complex.I * (z.im : ℂ)) • (Eblk L W a0 * (Q * Gsig H z s) * ((Gsig H z s)ᴴ * Qᴴ))
      = Eblk L W a0 * Q * ((2 * Complex.I * (z.im : ℂ)) • (Gsig H z s * (Gsig H z s)ᴴ))
          * Qᴴ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by
        rw [hW, Matrix.mul_sub, Matrix.sub_mul]

/-- **(6.12)** in the paper's form, solved for the row norms:
`W⁻¹ ∑_{i ∈ I_{a₀}} ‖v^{(l)}‖² = (2i Im z)⁻¹ (L_{σ^{(1)}} - L_{σ^{(2)}})`. -/
theorem ward_chain_row' (hH : H.IsHermitian) (hη : z.im ≠ 0)
    {ρ : List Bool} {b : List (ZMod L)} (h : ρ.length = b.length) (s : Bool) (a0 : ZMod L) :
    (W : ℂ)⁻¹ * ∑ α : Fin W, ∑ k : ZMod L × Fin W,
        (Complex.normSq (gchain L W H z (ρ ++ [s]) b (a0, α) k) : ℂ)
      = (2 * Complex.I * (z.im : ℂ))⁻¹
        * (gloop L W H z ⟨ρ ++ true :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩
          - gloop L W H z ⟨ρ ++ false :: (ρ.map (!·)).reverse, b ++ (b.reverse ++ [a0])⟩) := by
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    simp [Complex.I_ne_zero, hη]
  rw [eq_inv_mul_iff_mul_eq₀ hc]
  exact ward_chain_row hH (isUnit_sub_smul_one_of_im_ne_zero hH hη)
    (isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hη)) h s a0

end SymmetricLoop

section Arithmetic

/-- The shifted spectral parameter of §6: `z̃_{t₁} := (t₂/t₁)^{1/2} z_{t₁}`. -/
noncomputable def ztTilde (E t₁ t₂ : ℝ) : ℂ := (Real.sqrt (t₂ / t₁) : ℂ) * zt E t₁

theorem ztTilde_im (E t₁ t₂ : ℝ) :
    (ztTilde E t₁ t₂).im = Real.sqrt (t₂ / t₁) * etaT E t₁ := by
  rw [ztTilde, Complex.im_ofReal_mul, etaT_eq_zt_im]

theorem etaT_nonneg (E : ℝ) {t : ℝ} (ht : t ≤ 1) : 0 ≤ etaT E t := by
  rw [etaT, mE_im]
  have : 0 ≤ 1 - t := by linarith
  positivity

/-- In the bulk `|E| ≤ 2 - κ`, `Im m^{(E)} ≥ κ/2`. -/
theorem half_le_mE_im {E κ : ℝ} (hκ : 0 ≤ κ) (hE : |E| ≤ 2 - κ) : κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg E) hE 2
  have : κ ≤ Real.sqrt (4 - E ^ 2) := by
    rw [Real.le_sqrt hκ (by nlinarith)]
    nlinarith
  linarith

variable {c E t₁ t₂ : ℝ}

/-- `1 ≤ (t₂/t₁)^{1/2} ≤ t₂/t₁ ≤ c⁻¹` and `(t₂/t₁)^{1/2} - 1 ≤ (t₂-t₁)/c`. -/
theorem sqrt_div_bounds (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) :
    1 ≤ Real.sqrt (t₂ / t₁) ∧ Real.sqrt (t₂ / t₁) ≤ c⁻¹
      ∧ Real.sqrt (t₂ / t₁) - 1 ≤ (t₂ - t₁) / c := by
  have ht₁ : 0 < t₁ := lt_of_lt_of_le hc h₁
  have hq : 1 ≤ t₂ / t₁ := (one_le_div ht₁).mpr h₁₂
  have hs1 : 1 ≤ Real.sqrt (t₂ / t₁) := Real.one_le_sqrt.mpr hq
  have hsq : Real.sqrt (t₂ / t₁) ^ 2 = t₂ / t₁ := Real.sq_sqrt (by linarith)
  have hle : Real.sqrt (t₂ / t₁) ≤ t₂ / t₁ := by nlinarith
  have hq' : t₂ / t₁ ≤ c⁻¹ := by
    rw [div_le_iff₀ ht₁]
    calc t₂ ≤ 1 := h₂
      _ = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ c⁻¹ * t₁ := mul_le_mul_of_nonneg_left h₁ (inv_nonneg.mpr hc.le)
  refine ⟨hs1, hle.trans hq', ?_⟩
  have h1 : Real.sqrt (t₂ / t₁) - 1 ≤ t₂ / t₁ - 1 := by linarith
  have h2 : t₂ / t₁ - 1 = (t₂ - t₁) / t₁ := by field_simp
  have h3 : (t₂ - t₁) / t₁ ≤ (t₂ - t₁) / c :=
    div_le_div_of_nonneg_left (by linarith) hc h₁
  linarith

/-- `Im z̃_{t₁} ≍ Im z_{t₁}`: `η_{t₁} ≤ Im z̃_{t₁} ≤ c⁻¹ η_{t₁}`. -/
theorem etaT_le_ztTilde_im (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) :
    etaT E t₁ ≤ (ztTilde E t₁ t₂).im ∧ (ztTilde E t₁ t₂).im ≤ c⁻¹ * etaT E t₁ := by
  obtain ⟨hs1, hsc, -⟩ := sqrt_div_bounds hc h₁ h₁₂ h₂
  have hη := etaT_nonneg E (h₁₂.trans h₂)
  rw [ztTilde_im]
  constructor
  · nlinarith
  · exact mul_le_mul_of_nonneg_right hsc hη

/-- `|z_{t₂} - z̃_{t₁}| ≤ C (t₂ - t₁)` with `C = 3/c + 1`. -/
theorem norm_zt_sub_ztTilde_le (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1)
    (hE : |E| ≤ 2) : ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (t₂ - t₁) := by
  obtain ⟨hs1, -, hs⟩ := sqrt_div_bounds hc h₁ h₁₂ h₂
  set s := Real.sqrt (t₂ / t₁)
  have hm := norm_mE hE
  have hkey : zt E t₂ - ztTilde E t₁ t₂
      = ((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E)
        - ((t₂ - t₁ : ℝ) : ℂ) * mE E := by
    simp only [zt, ztTilde, s]
    push_cast
    ring
  have ht₁ : 1 - t₁ ≤ 1 := by linarith [lt_of_lt_of_le hc h₁]
  have ht₁' : 0 ≤ 1 - t₁ := by linarith
  have hin : ‖(E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E‖ ≤ 3 := by
    calc ‖(E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E‖
        ≤ ‖(E : ℂ)‖ + ‖((1 - t₁ : ℝ) : ℂ) * mE E‖ := norm_add_le _ _
      _ = |E| + (1 - t₁) := by
          rw [norm_mul, hm, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_of_nonneg ht₁', mul_one]
      _ ≤ 3 := by linarith
  rw [hkey]
  calc ‖((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E)
        - ((t₂ - t₁ : ℝ) : ℂ) * mE E‖
      ≤ ‖((1 - s : ℝ) : ℂ) * ((E : ℂ) + ((1 - t₁ : ℝ) : ℂ) * mE E)‖
        + ‖((t₂ - t₁ : ℝ) : ℂ) * mE E‖ := norm_sub_le _ _
    _ ≤ (s - 1) * 3 + (t₂ - t₁) := by
        rw [norm_mul, norm_mul, hm, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonpos (by linarith), Real.norm_of_nonneg (by linarith), mul_one]
        have := mul_le_mul_of_nonneg_left hin (by linarith : 0 ≤ -(1 - s))
        linarith
    _ ≤ 3 * ((t₂ - t₁) / c) + (t₂ - t₁) := by linarith
    _ = (3 / c + 1) * (t₂ - t₁) := by ring

/-- `|z_{t₂} - z̃_{t₁}| ≤ C (1 - t₁)`, the form stated in §6. -/
theorem norm_zt_sub_ztTilde_le_one_sub (hc : 0 < c) (h₁ : c ≤ t₁) (h₁₂ : t₁ ≤ t₂)
    (h₂ : t₂ ≤ 1) (hE : |E| ≤ 2) :
    ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (1 - t₁) := by
  refine (norm_zt_sub_ztTilde_le hc h₁ h₁₂ h₂ hE).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- In the bulk, `|z_{t₂} - z̃_{t₁}| ≤ C η_{t₁}` with `C = (3/c + 1)·(2/κ)`. -/
theorem norm_zt_sub_ztTilde_le_etaT {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (h₁ : c ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) (h₂ : t₂ ≤ 1) (hE : |E| ≤ 2 - κ) :
    ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ (3 / c + 1) * (2 / κ) * etaT E t₁ := by
  refine (norm_zt_sub_ztTilde_le_one_sub hc h₁ h₁₂ h₂ (by linarith)).trans ?_
  have hm := half_le_mE_im hκ.le hE
  have ht : 0 ≤ 1 - t₁ := by linarith
  have h1 : 1 - t₁ ≤ 2 / κ * etaT E t₁ := by
    rw [etaT, div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **The arithmetic of `z̃_{t₁}` in §6.**  For `c ≤ t₁ ≤ t₂ ≤ 1` and `|E| ≤ 2 - κ`:
\[ |z_{t_2}-\tilde z_{t_1}| \le C(1-t_1),\quad |z_{t_2}-\tilde z_{t_1}|^2 \le C\eta_{t_1}^2,
    \quad \frac{|z_{t_2}-\tilde z_{t_1}|^2}{\operatorname{Im}\tilde z_{t_1}} \le C\eta_{t_1},
    \quad \eta_{t_1}\le\operatorname{Im}\tilde z_{t_1}\le C\eta_{t_1}. \]
The constant depends only on `c` and `κ`. -/
theorem ztTilde_arith {κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    ∃ C > 0, ∀ E t₁ t₂ : ℝ, c ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ 1 → |E| ≤ 2 - κ →
      ‖zt E t₂ - ztTilde E t₁ t₂‖ ≤ C * (1 - t₁)
      ∧ ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ C * etaT E t₁ ^ 2
      ∧ ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 / (ztTilde E t₁ t₂).im ≤ C * etaT E t₁
      ∧ etaT E t₁ ≤ (ztTilde E t₁ t₂).im
      ∧ (ztTilde E t₁ t₂).im ≤ C * etaT E t₁ := by
  set K := (3 / c + 1) * (2 / κ) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(3 / c + 1) + K ^ 2 + c⁻¹, by positivity, ?_⟩
  intro E t₁ t₂ h₁ h₁₂ h₂ hE
  have hη := etaT_nonneg E (h₁₂.trans h₂)
  have hd := norm_zt_sub_ztTilde_le_etaT hc hκ h₁ h₁₂ h₂ hE
  have hd' := norm_zt_sub_ztTilde_le_one_sub hc h₁ h₁₂ h₂ (by linarith)
  obtain ⟨hIm1, hIm2⟩ := etaT_le_ztTilde_im (E := E) hc h₁ h₁₂ h₂
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have ht : 0 ≤ 1 - t₁ := by linarith
  have h3 : 0 ≤ 3 / c + 1 := by positivity
  have hC1 : K ^ 2 ≤ (3 / c + 1) + K ^ 2 + c⁻¹ := by linarith
  have hC2 : c⁻¹ ≤ (3 / c + 1) + K ^ 2 + c⁻¹ := by linarith
  have hsq : ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ K ^ 2 * etaT E t₁ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  refine ⟨?_, ?_, ?_, hIm1, ?_⟩
  · refine hd'.trans ?_
    nlinarith
  · exact hsq.trans (mul_le_mul_of_nonneg_right hC1 (sq_nonneg _))
  · refine div_le_of_le_mul₀ (hη.trans hIm1) (by positivity) ?_
    calc ‖zt E t₂ - ztTilde E t₁ t₂‖ ^ 2 ≤ K ^ 2 * etaT E t₁ ^ 2 := hsq
      _ = (K ^ 2 * etaT E t₁) * etaT E t₁ := by ring
      _ ≤ ((3 / c + 1) + K ^ 2 + c⁻¹) * etaT E t₁ * (ztTilde E t₁ t₂).im := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hC1 hη) hIm1 hη (by positivity)
  · exact hIm2.trans (mul_le_mul_of_nonneg_right hC2 hη)

end Arithmetic

end RBM
