/-
Copyright (c) 2026. All rights reserved.
-/
import RBM1D.Hierarchy.Step2FarInputs

/-!
# T1499: a compiled necessary condition for `h560`

`RBM.Step2FarInputs.eGpm_le_rhs535_of_jS` and `RBM.Step2FarInputs.h535_of_jS` assume

  `h560 : ‖L_{(-,+,+),(a₂,b,a₁)}‖ ≤ gm(a₂,b) · gm(a₁,b) · gm(a₂,a₁)`,
  `gm x y = √(J*) · √(T(‖x-y‖))` (`RBM.Step2FarInputs.gmOfJS`).

This file proves, for an **arbitrary** Hermitian matrix, that the instances
`(a₁, b) = (a, a)`, `a₂` arbitrary, of such an inequality force

  `(Im ⟨G E_a⟩)² ≤ η W² ∑_{a₂} gm(a₂,a)² gm(a,a)`,

and, for `gm = gmOfJS` together with the 1-loop bound `hone`,

  `(Im m - κ A⁻¹)² ≤ η W² J*^{3/2} (A⁻² + W^{-D}) (168 ℓ A⁻¹ + L √(W^{-D}))`.

The right side is `≈ 168 J*^{3/2} / (W ℓ² η²)`.  So `h560` is false whenever
`(Im m - κ/A)² W ℓ² η² > 168 J*^{3/2}` (up to `W^{-D}` terms), for every Hermitian `H`.

The proof is the Ward identity
`2iηW ∑_{a₂} L_{(-,+,+),(a₂,a,a)} = L_{(+,+),(a,a)} - L_{(-,+),(a,a)}`
and the entrywise inequality
`Re (L_{(-,+),(a,a)} - L_{(+,+),(a,a)}) = ½ W⁻² ∑_{p,q ∈ I_a} |G_{pq} - conj G_{qp}|²
  ≥ 2 W⁻¹ (Im ⟨G E_a⟩)²`.

This is a statement about the hypothesis `h560`; nothing here is used as an input elsewhere.
-/

open Real Matrix Finset

namespace RBM
namespace H560Check

section Det

variable {L W : ℕ} [NeZero L]

/-- The real block weight `w_p = W⁻¹ 1(p ∈ I_a)`, the diagonal of `E_a`. -/
noncomputable def wt (L W : ℕ) (a : ZMod L) (p : ZMod L × Fin W) : ℝ :=
  if p.1 = a then (W : ℝ)⁻¹ else 0

omit [NeZero L] in
theorem wt_nonneg (a : ZMod L) (p : ZMod L × Fin W) : 0 ≤ wt L W a p := by
  unfold wt; split_ifs <;> positivity

omit [NeZero L] in
theorem Eblk_eq_diagonal_wt (a : ZMod L) :
    Eblk L W a = diagonal fun p => ((wt L W a p : ℝ) : ℂ) := by
  unfold Eblk wt
  congr 1
  funext p
  split_ifs <;> simp

/-- A `2`-loop at the diagonal pair `(a,a)`, entrywise. -/
theorem trace_mul_Eblk_mul_Eblk (A B : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)
    (a : ZMod L) :
    Matrix.trace (A * Eblk L W a * (B * Eblk L W a))
      = ∑ p, ∑ q, ((wt L W a p * wt L W a q : ℝ) : ℂ) * (A p q * B q p) := by
  rw [Eblk_eq_diagonal_wt]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  push_cast
  ring

/-- `⟨G E_a⟩ = ∑_p w_p G_{pp}`. -/
theorem trace_mul_Eblk (A : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (a : ZMod L) :
    Matrix.trace (A * Eblk L W a) = ∑ p, ((wt L W a p : ℝ) : ℂ) * A p p := by
  rw [Eblk_eq_diagonal_wt]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

variable [NeZero W]

/-- **The Ward identity for the `(-,+,+)` `3`-loop, summed over its first label.**
`2iη ∑_b L_{(-,+,+),(b,a,a)} = W⁻¹ (L_{(+,+),(a,a)} - L_{(-,+),(a,a)})`. -/
theorem sum_gloop3_ward {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}
    (hz : IsUnit (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (hz' : IsUnit (H - ((starRingEnd ℂ) z) •
      (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)))
    (a : ZMod L) :
    (2 * Complex.I * (z.im : ℂ))
        * ∑ b : ZMod L, gloop L W H z ⟨[false, true, true], [b, a, a]⟩
      = (W : ℂ)⁻¹ * (gloop L W H z ⟨[true, true], [a, a]⟩
          - gloop L W H z ⟨[false, true], [a, a]⟩) := by
  rw [sum_gloop_head]
  have hprod : gloopProd L W H z ⟨[true, true], [a, a]⟩
      = green H z * (Eblk L W a * (green H z * Eblk L W a)) := by
    simp [gloopProd_cons, gloopProd_nil, Matrix.mul_assoc]
  have hw := trace_green_sub_trace_green_conj' hz hz' (Eblk L W a * (green H z * Eblk L W a))
  have h1 : gloop L W H z ⟨[true, true], [a, a]⟩
      = Matrix.trace (green H z * (Eblk L W a * (green H z * Eblk L W a))) := by
    rw [gloop_two]; simp [Matrix.mul_assoc]
  have h2 : gloop L W H z ⟨[false, true], [a, a]⟩
      = Matrix.trace (green H ((starRingEnd ℂ) z) * (Eblk L W a * (green H z * Eblk L W a))) := by
    rw [gloop_two]; simp [Matrix.mul_assoc]
  rw [h1, h2, hw, hprod, Gsig_false, ← Matrix.mul_assoc (green H ((starRingEnd ℂ) z))]
  ring

omit [NeZero W] in
/-- `normSq (u - conj v) = normSq u + normSq v - 2 Re (u v)`. -/
theorem normSq_sub_conj (u v : ℂ) :
    Complex.normSq (u - (starRingEnd ℂ) v)
      = Complex.normSq u + Complex.normSq v - 2 * (u * v).re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_re]
  ring

omit [NeZero W] in
/-- `normSq (u - conj u) = 4 (Im u)²`. -/
theorem normSq_sub_conj_self (u : ℂ) :
    Complex.normSq (u - (starRingEnd ℂ) u) = 4 * u.im ^ 2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  ring

omit [NeZero W] in
/-- `∑_p 1(p ∈ I_a)² = W`. -/
theorem sum_ind_sq (a : ZMod L) :
    ∑ p : ZMod L × Fin W, (if p.1 = a then (1 : ℝ) else 0) ^ 2 = W := by
  rw [Fintype.sum_prod_type]
  simp

omit [NeZero W] in
/-- **Cauchy–Schwarz on one block**: `(∑_p w_p x_p)² ≤ W ∑_p w_p² x_p²`. -/
theorem sq_sum_wt_mul_le (a : ZMod L) (x : ZMod L × Fin W → ℝ) :
    (∑ p, wt L W a p * x p) ^ 2 ≤ (W : ℝ) * ∑ p, (wt L W a p * x p) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod L × Fin W))
    (fun p => if p.1 = a then (1 : ℝ) else 0) (fun p => wt L W a p * x p)
  have hf : ∀ p : ZMod L × Fin W,
      (if p.1 = a then (1 : ℝ) else 0) * (wt L W a p * x p) = wt L W a p * x p := by
    intro p; unfold wt; split_ifs <;> simp
  simp only [hf] at h
  rwa [sum_ind_sq] at h

/-- **The deterministic lower bound.**  For Hermitian `H`,
`2 W⁻¹ (Im ⟨G E_a⟩)² ≤ Re (L_{(-,+),(a,a)} - L_{(+,+),(a,a)})`. -/
theorem two_inv_W_mul_sq_im_trace_le_re {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (a : ZMod L) :
    2 * (W : ℝ)⁻¹ * (Matrix.trace (green H z * Eblk L W a)).im ^ 2
      ≤ (gloop L W H z ⟨[false, true], [a, a]⟩
          - gloop L W H z ⟨[true, true], [a, a]⟩).re := by
  set g := green H z with hg
  have hG : green H ((starRingEnd ℂ) z) = gᴴ := (Gsig_conjTranspose hH z true).symm
  set w := wt L W a with hw
  have hw0 : ∀ p, 0 ≤ w p := wt_nonneg a
  -- the two loops, entrywise
  have hmp : gloop L W H z ⟨[false, true], [a, a]⟩
      = ∑ p, ∑ q, ((w p * w q : ℝ) : ℂ) * (gᴴ p q * g q p) := by
    rw [gloop_two, Gsig_false, Gsig_true, hG]
    exact trace_mul_Eblk_mul_Eblk _ _ a
  have hpp : gloop L W H z ⟨[true, true], [a, a]⟩
      = ∑ p, ∑ q, ((w p * w q : ℝ) : ℂ) * (g p q * g q p) := by
    rw [gloop_two, Gsig_true]
    exact trace_mul_Eblk_mul_Eblk _ _ a
  have hre : (gloop L W H z ⟨[false, true], [a, a]⟩
      - gloop L W H z ⟨[true, true], [a, a]⟩).re
      = ∑ p, ∑ q, w p * w q * (Complex.normSq (g q p) - (g p q * g q p).re) := by
    rw [hmp, hpp, ← Finset.sum_sub_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_sub, Complex.re_ofReal_mul, Matrix.conjTranspose_apply]
    congr 1
    have : star (g q p) * g q p = (Complex.normSq (g q p) : ℂ) := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    rw [this, Complex.sub_re, Complex.ofReal_re]
  -- symmetrization
  have hswap : ∑ p, ∑ q, w p * w q * Complex.normSq (g q p)
      = ∑ p, ∑ q, w p * w q * Complex.normSq (g p q) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  have hsym : ∑ p, ∑ q, w p * w q * (Complex.normSq (g q p) - (g p q * g q p).re)
      = ∑ p, ∑ q, w p * w q * (Complex.normSq (g p q - (starRingEnd ℂ) (g q p)) / 2) := by
    have e1 : ∀ p q, w p * w q * (Complex.normSq (g p q - (starRingEnd ℂ) (g q p)) / 2)
        = (w p * w q * Complex.normSq (g q p) + w p * w q * Complex.normSq (g p q)) / 2
          - w p * w q * (g p q * g q p).re := by
      intro p q; rw [normSq_sub_conj]; ring
    simp only [e1, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hswap]
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hswap]
    ring
  -- drop the off-diagonal terms
  have hdiag : ∑ p, 2 * (w p * (g p p).im) ^ 2
      ≤ ∑ p, ∑ q, w p * w q * (Complex.normSq (g p q - (starRingEnd ℂ) (g q p)) / 2) := by
    refine Finset.sum_le_sum fun p _ => ?_
    have hnn : ∀ q ∈ (Finset.univ : Finset (ZMod L × Fin W)),
        0 ≤ w p * w q * (Complex.normSq (g p q - (starRingEnd ℂ) (g q p)) / 2) := by
      intro q _
      have := Complex.normSq_nonneg (g p q - (starRingEnd ℂ) (g q p))
      have := hw0 p; have := hw0 q
      positivity
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn (Finset.mem_univ p))
    rw [normSq_sub_conj_self]
    ring
  -- Cauchy–Schwarz
  have htr : (Matrix.trace (g * Eblk L W a)).im = ∑ p, w p * (g p p).im := by
    rw [trace_mul_Eblk, Complex.im_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.im_ofReal_mul]
  have hcs := sq_sum_wt_mul_le a (fun p => (g p p).im)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  rw [hre, hsym, htr]
  refine le_trans ?_ hdiag
  rw [← Finset.mul_sum]
  have : (W : ℝ)⁻¹ * (∑ p, w p * (g p p).im) ^ 2 ≤ ∑ p, (w p * (g p p).im) ^ 2 := by
    rw [inv_mul_le_iff₀ hWpos]
    exact hcs
  linarith

/-- **The necessary condition, in loop form.**  For Hermitian `H` and `Im z > 0`,
`(Im ⟨G E_a⟩)² ≤ η W² ∑_b ‖L_{(-,+,+),(b,a,a)}‖`. -/
theorem sq_im_trace_le_sum_norm_gloop3 {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (a : ZMod L) :
    (Matrix.trace (green H z * Eblk L W a)).im ^ 2
      ≤ z.im * (W : ℝ) ^ 2
          * ∑ b : ZMod L, ‖gloop L W H z ⟨[false, true, true], [b, a, a]⟩‖ := by
  have hu := isUnit_sub_smul_one_of_im_ne_zero hH (ne_of_gt hz)
  have hu' := isUnit_sub_smul_one_of_im_ne_zero hH
    (z := (starRingEnd ℂ) z) (by rw [Complex.conj_im]; exact neg_ne_zero.2 (ne_of_gt hz))
  have hward := sum_gloop3_ward hu hu' a
  set S := ∑ b : ZMod L, gloop L W H z ⟨[false, true, true], [b, a, a]⟩ with hS
  set Lmp := gloop L W H z ⟨[false, true], [a, a]⟩
  set Lpp := gloop L W H z ⟨[true, true], [a, a]⟩
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hlow := two_inv_W_mul_sq_im_trace_le_re (L := L) (W := W) hH z a
  -- norms of the Ward identity
  have hn : 2 * z.im * ‖S‖ = (W : ℝ)⁻¹ * ‖Lmp - Lpp‖ := by
    have := congrArg norm hward
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_inv, Complex.norm_natCast,
      norm_sub_rev] at this
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hη : ‖((z.im : ℝ) : ℂ)‖ = z.im := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
    rw [h2, hη] at this
    linarith
  have hre : (Lmp - Lpp).re ≤ ‖Lmp - Lpp‖ := Complex.re_le_norm _
  have hsum :
      ‖S‖ ≤ ∑ b : ZMod L, ‖gloop L W H z ⟨[false, true, true], [b, a, a]⟩‖ :=
    norm_sum_le _ _
  -- combine
  have h1 : 2 * (W : ℝ)⁻¹ * (Matrix.trace (green H z * Eblk L W a)).im ^ 2
      ≤ (W : ℝ) * (2 * z.im * ‖S‖) := by
    rw [hn, ← mul_assoc, mul_inv_cancel₀ hWpos.ne', one_mul]
    exact hlow.trans hre
  have h2 : (Matrix.trace (green H z * Eblk L W a)).im ^ 2 ≤ z.im * (W : ℝ) ^ 2 * ‖S‖ := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (W : ℝ) / 2)
    have e1 : (W : ℝ) / 2 * (2 * (W : ℝ)⁻¹ * (Matrix.trace (green H z * Eblk L W a)).im ^ 2)
        = (Matrix.trace (green H z * Eblk L W a)).im ^ 2 := by
      field_simp
    have e2 :
        (W : ℝ) / 2 * ((W : ℝ) * (2 * z.im * ‖S‖)) = z.im * (W : ℝ) ^ 2 * ‖S‖ := by
      ring
    linarith
  exact h2.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- **`h560` at the instances `(a₂, b, a₁) = (b, a, a)` forces a lower bound on `∑ Gm`**,
for any function `Gm` and any Hermitian `H`.  This is the form in which `h560`
appears in `RBM.Step2FarInputs.eGpm_le_rhs535` (pairs `(a, b)`, internal label `a`) and in
`RBM.Step2FarInputs.h535_of_jS` (`b := ![a, b₁]`, `c := a`). -/
theorem h560_diag_forces {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (a : ZMod L) (Gm : ZMod L → ZMod L → ℝ)
    (h560 : ∀ b, ‖gloop L W H z ⟨[false, true, true], [b, a, a]⟩‖
      ≤ Gm b a * Gm a a * Gm b a) :
    (Matrix.trace (green H z * Eblk L W a)).im ^ 2
      ≤ z.im * (W : ℝ) ^ 2 * ∑ b : ZMod L, Gm b a * Gm a a * Gm b a := by
  refine (sq_im_trace_le_sum_norm_gloop3 hH hz a).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => h560 b) (by positivity)

end Det

section Sample

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- `∑_{b} gm(b,a)² gm(a,a) ≤ J*^{3/2} T(0) (168 ℓ A⁻¹ + L √(W^{-D}))` for
`gm = RBM.Step2FarInputs.gmOfJS`, with `T(0) = A⁻² + W^{-D}`. -/
theorem sum_gmOfJS_diag_le (X : Sample B) {E D' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω}
    (hηu : 0 < etaT E u) (hℓu : 1 ≤ B.ell N u) (a : ZMod (B.L N)) :
    ∑ b : ZMod (B.L N), Step2FarInputs.gmOfJS X E D' N u ω b a
        * Step2FarInputs.gmOfJS X E D' N u ω a a * Step2FarInputs.gmOfJS X E D' N u ω b a
      ≤ Step2.jS X E D' N u ω * √(Step2.jS X E D' N u ω)
        * ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ + (B.W N : ℝ) ^ (-D'))
        * (168 * B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
            + (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))) := by
  set J := Step2.jS X E D' N u ω with hJ
  set T : ℝ → ℝ := fun d => tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D' d with hT
  have hWpos : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hJ0 : 0 ≤ J := le_trans zero_le_one (Step2Moment.one_le_jS X N u ω)
  have hT0 : ∀ d, 0 ≤ T d := fun d => tailT_nonneg hWpos.le d
  have hTzero :
      T 0 = ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ + (B.W N : ℝ) ^ (-D')) := by
    simp [hT, tailT]
  have hterm : ∀ b : ZMod (B.L N), Step2FarInputs.gmOfJS X E D' N u ω b a
      * Step2FarInputs.gmOfJS X E D' N u ω a a * Step2FarInputs.gmOfJS X E D' N u ω b a
      = J * √J * √(T 0) * (√(T (zdist (B.L N) (a - b))) * √(T (zdist (B.L N) (a - b)))) := by
    intro b
    simp only [Step2FarInputs.gmOfJS, sub_self, zdist_zero, Nat.cast_zero]
    rw [Lemma57.zdist_sub_comm (B.L N) b a]
    have hsJ : √J * √J = J := Real.mul_self_sqrt hJ0
    rw [← hJ]
    set t := √(T (zdist (B.L N) (a - b)))
    calc √J * t * (√J * √(T 0)) * (√J * t) = (√J * √J) * √J * √(T 0) * (t * t) := by ring
      _ = _ := by rw [hsJ]
  simp only [hterm]
  rw [← Finset.mul_sum]
  have hconv := Lemma57.sum_sqrt_tailT_mul_le (B.L N) hWpos hℓu hηu D' a a
  simp only [sub_self, zdist_zero, Nat.cast_zero] at hconv
  have hc0 : (0 : ℝ) ≤ J * √J * √(T 0) := by positivity
  have := mul_le_mul_of_nonneg_left hconv hc0
  refine this.trans (le_of_eq ?_)
  have hsq : √(T 0) * √(T 0) = T 0 := Real.mul_self_sqrt (hT0 0)
  rw [← hTzero]
  calc J * √J * √(T 0) * ((168 * B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
          + (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))) * √(T 0))
      = J * √J * (√(T 0) * √(T 0))
          * (168 * B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
            + (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))) := by ring
    _ = _ := by rw [hsq]

/-- **`h560` of `RBM.Step2FarInputs.h535_of_jS` (at one time `u`) and the `(4.5)` hypothesis
`hone` at one block force `J*` to be large.**  For every sample, time and block `a`, with
`A = W ℓ_u η_u`:

  `(Im m - κ A⁻¹)² ≤ η_u W² J*^{3/2} (A⁻² + W^{-D}) (168 ℓ_u A⁻¹ + L √(W^{-D}))`.

The right side is `168 J*^{3/2}/(W ℓ_u² η_u²)` up to `W^{-D}` terms.  Hence the hypothesis
`h560` of `h535_of_jS` (and the corresponding family of instances of the `h560` of
`eGpm_le_rhs535_of_jS`) is **false** whenever
`(Im m - κ A⁻¹)² W ℓ_u² η_u² > 168 J*^{3/2} (1 + W^{-D}-terms)`,
for every Hermitian flow. -/
theorem h535_h560_forces (X : Sample B) {E D' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} {κ : ℝ}
    (hηu : 0 < etaT E u) (hℓu : 1 ≤ B.ell N u) (a : ZMod (B.L N))
    (h560 : ∀ (b : LoopArg (B.L N) 2) (c : ZMod (B.L N)),
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[false, true, true], [b 1, c, b 0]⟩‖
        ≤ Step2FarInputs.gmOfJS X E D' N u ω (b 1) c
            * Step2FarInputs.gmOfJS X E D' N u ω (b 0) c
            * Step2FarInputs.gmOfJS X E D' N u ω (b 1) (b 0))
    (hone : ‖Matrix.trace ((Gsig (X.H N u ω) (zt E u) true
        - mSigma E true • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) a)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ ≤ (mE E).im) :
    ((mE E).im - κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹) ^ 2
      ≤ etaT E u * (B.W N : ℝ) ^ 2 * (Step2.jS X E D' N u ω * √(Step2.jS X E D' N u ω)
        * ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ + (B.W N : ℝ) ^ (-D'))
        * (168 * B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
            + (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D')))) := by
  have hz : 0 < (zt E u).im := by rw [← etaT_eq_zt_im]; exact hηu
  -- the instances `(b, c) = (![a, b₁], a)`
  have h560' : ∀ b₁ : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[false, true, true], [b₁, a, a]⟩‖
        ≤ Step2FarInputs.gmOfJS X E D' N u ω b₁ a * Step2FarInputs.gmOfJS X E D' N u ω a a
            * Step2FarInputs.gmOfJS X E D' N u ω b₁ a := by
    intro b₁
    have := h560 ![a, b₁] a
    simpa using this
  have hmain := h560_diag_forces (X.hermitian N u ω) hz a _ h560'
  rw [← etaT_eq_zt_im] at hmain
  have hsum := sum_gmOfJS_diag_le X (D' := D') (ω := ω) hηu hℓu a
  -- the 1-loop bound gives `Im ⟨G E_a⟩ ≥ Im m - κ A⁻¹`
  have htr : Matrix.trace ((Gsig (X.H N u ω) (zt E u) true
        - mSigma E true • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) a)
      = Matrix.trace (green (X.H N u ω) (zt E u) * Eblk (B.L N) (B.W N) a) - mE E := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      trace_Eblk, Gsig_true, mSigma_true, smul_eq_mul, mul_one]
  rw [htr] at hone
  have him : (mE E).im - κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
      ≤ (Matrix.trace (green (X.H N u ω) (zt E u) * Eblk (B.L N) (B.W N) a)).im := by
    have h1 := Complex.abs_im_le_norm
      (Matrix.trace (green (X.H N u ω) (zt E u) * Eblk (B.L N) (B.W N) a) - mE E)
    rw [Complex.sub_im] at h1
    have h2 := neg_abs_le ((Matrix.trace (green (X.H N u ω) (zt E u)
      * Eblk (B.L N) (B.W N) a)).im - (mE E).im)
    linarith
  have hsq : ((mE E).im - κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹) ^ 2
      ≤ (Matrix.trace (green (X.H N u ω) (zt E u) * Eblk (B.L N) (B.W N) a)).im ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.2 hκ) him 2
  have hpos : (0 : ℝ) ≤ etaT E u * (B.W N : ℝ) ^ 2 := by positivity
  exact hsq.trans (hmain.trans (mul_le_mul_of_nonneg_left hsum hpos))

/-- **`¬ h560`** (the hypothesis of `RBM.Step2FarInputs.h535_of_jS` at one time `u`) in the
deterministic regime: whenever the `(4.5)` bound `hone` holds at one block `a` and
`η_u W² J*^{3/2} (A⁻² + W^{-D}) (168 ℓ_u A⁻¹ + L √(W^{-D})) < (Im m - κ A⁻¹)²`. -/
theorem not_h535_h560 (X : Sample B) {E D' : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} {κ : ℝ}
    (hηu : 0 < etaT E u) (hℓu : 1 ≤ B.ell N u) (a : ZMod (B.L N))
    (hone : ‖Matrix.trace ((Gsig (X.H N u ω) (zt E u) true
        - mSigma E true • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) * Eblk (B.L N) (B.W N) a)‖
      ≤ κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹)
    (hκ : κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹ ≤ (mE E).im)
    (hgt : etaT E u * (B.W N : ℝ) ^ 2 * (Step2.jS X E D' N u ω * √(Step2.jS X E D' N u ω)
        * ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹ + (B.W N : ℝ) ^ (-D'))
        * (168 * B.ell N u * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
            + (B.L N : ℝ) * √((B.W N : ℝ) ^ (-D'))))
      < ((mE E).im - κ * ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹) ^ 2) :
    ¬ (∀ (b : LoopArg (B.L N) 2) (c : ZMod (B.L N)),
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[false, true, true], [b 1, c, b 0]⟩‖
        ≤ Step2FarInputs.gmOfJS X E D' N u ω (b 1) c
            * Step2FarInputs.gmOfJS X E D' N u ω (b 0) c
            * Step2FarInputs.gmOfJS X E D' N u ω (b 1) (b 0)) := fun h560 =>
  absurd (h535_h560_forces X hηu hℓu a h560 hone hκ) (not_le.2 hgt)

end Sample

end H560Check
end RBM
