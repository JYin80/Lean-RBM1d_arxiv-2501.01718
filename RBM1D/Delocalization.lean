/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Delocalization from a bound on the Green's function

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, the spectral part of the
proof of Theorem 2.2, i.e. (2.10).

Let `H` be Hermitian with eigenvalues `λ_l` and orthonormal eigenvectors `ψ_l`, and
`G(z) = (H - z)⁻¹`.  For `η > 0`,
`|ψ_k(x)|² ≤ ∑_l η² |ψ_l(x)|² / ((λ_k - λ_l)² + η²) = η · Im G_xx(λ_k + iη)`.   (2.10)

Consequently a bound `|G_xx(λ_k + iη)| ≤ C` gives `|ψ_k(x)|² ≤ C η`.  In the paper the
bound on `G` comes from the local law (Theorem 2.3) with high probability and
`η = N^{-1+τ}`; here it is a hypothesis, and everything is deterministic.

## Main results

* `RBM.green_eq_spectral`       : `G(z) = U diag((λ - z)⁻¹) U*`
* `RBM.im_green_apply_self`     : `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)`
* `RBM.sq_norm_eigenvector_le_sum`, `RBM.sq_norm_eigenvector_le_im_green` : (2.10)
* `RBM.sq_norm_eigenvector_le_of_norm_green_le` : `|G_xx| ≤ C ⇒ |ψ_k(x)|² ≤ C η`

## The energy is random, the local law is not

The spectral parameter in (2.10) is `λ_k(ω) + iη`, which moves with `ω`, while the local law
(Theorem 2.3) is a statement about a *deterministic* sequence of spectral parameters.  The gap
is closed by a net of deterministic energies together with the **deterministic Lipschitz
continuity of `G` in the energy**, proved here:

* `RBM.sum_sq_norm_eigenvectorBasis` : `∑_l |ψ_l(x)|² = 1` (the rows of the eigenvector matrix
  are unit vectors);
* `RBM.im_green_lipschitz_energy` : `|Im G_xx(E + iη) - Im G_xx(E' + iη)| ≤ |E - E'| / η²`;
* `RBM.sq_norm_eigenvector_le_of_norm_green_le_near` : (2.10) evaluated at a *nearby*
  deterministic energy — `|λ_k - E| ≤ d` and `|G_xx(E + iη)| ≤ C` give
  `|ψ_k(x)|² ≤ η C + d / η`.

`RBM.delocalization_of_Thm221N` in `RBM1D/Flow/EnergyUniform.lean` is the probabilistic half
(Theorem 2.2 itself); it consumes exactly the last of these.
-/

namespace RBM

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Green's function `G(z) = (H - z)⁻¹`. -/
noncomputable def green (H : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ := (H - z • 1)⁻¹

variable {H : Matrix n n ℂ} (hH : H.IsHermitian)

/-- Spectral decomposition of the Green's function. -/
theorem green_eq_spectral {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) :
    green H z = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hz1 : (z • 1 : Matrix n n ℂ) = U * diagonal (fun _ => z) * star U := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU']
  have hsub : H - z • 1 = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U := by
    rw [hz1]
    conv_lhs => rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - z) * ((hH.eigenvalues l : ℂ) - z)⁻¹)
            = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- Diagonal entries of the Green's function: `G_xx(z) = ∑_l |ψ_l(x)|² / (λ_l - z)`. -/
theorem green_apply_self {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) (x : n) :
    green H z x x
      = ∑ l, (Complex.normSq (hH.eigenvectorBasis l x) : ℂ) / ((hH.eigenvalues l : ℂ) - z) := by
  rw [green_eq_spectral hH hz, mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_diagonal, star_apply, IsHermitian.eigenvectorUnitary_apply,
    Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

/-- `Im G_xx(E + iη) = ∑_l η |ψ_l(x)|² / ((λ_l - E)² + η²)`. -/
theorem im_green_apply_self (E : ℝ) {η : ℝ} (hη : η ≠ 0) (x : n) :
    (green H (E + η * Complex.I) x x).im
      = ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x)
          / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
  have hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ E + η * Complex.I := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact hη this.symm
  rw [green_apply_self hH hz, Complex.im_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I))
      = (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  have him : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
  have hpos : 0 < (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by positivity
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im, hn, him]
  field_simp

/-- (2.10), first inequality: the `l = k` term of the sum is `|ψ_k(x)|²`. -/
theorem sq_norm_eigenvector_le_sum {η : ℝ} (hη : 0 < η) (k x : n) :
    ‖hH.eigenvectorBasis k x‖ ^ 2
      ≤ ∑ l, η ^ 2 * ‖hH.eigenvectorBasis l x‖ ^ 2
          / ((hH.eigenvalues k - hH.eigenvalues l) ^ 2 + η ^ 2) := by
  have hk : η ^ 2 * ‖hH.eigenvectorBasis k x‖ ^ 2
      / ((hH.eigenvalues k - hH.eigenvalues k) ^ 2 + η ^ 2) = ‖hH.eigenvectorBasis k x‖ ^ 2 := by
    rw [sub_self]
    field_simp
    ring
  rw [← hk]
  refine Finset.single_le_sum (f := fun l => η ^ 2 * ‖hH.eigenvectorBasis l x‖ ^ 2
    / ((hH.eigenvalues k - hH.eigenvalues l) ^ 2 + η ^ 2)) (fun l _ => ?_) (Finset.mem_univ k)
  positivity

/-- (2.10), second step: the sum equals `η Im G_xx(λ_k + iη)`. -/
theorem sum_eq_mul_im_green {η : ℝ} (hη : 0 < η) (k x : n) :
    ∑ l, η ^ 2 * ‖hH.eigenvectorBasis l x‖ ^ 2
        / ((hH.eigenvalues k - hH.eigenvalues l) ^ 2 + η ^ 2)
      = η * (green H (hH.eigenvalues k + η * Complex.I) x x).im := by
  rw [im_green_apply_self hH _ hη.ne', Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.normSq_eq_norm_sq]
  have hpos : 0 < (hH.eigenvalues l - hH.eigenvalues k) ^ 2 + η ^ 2 := by positivity
  rw [show (hH.eigenvalues k - hH.eigenvalues l) ^ 2 = (hH.eigenvalues l - hH.eigenvalues k) ^ 2
    by ring]
  field_simp

/-- **(2.10)**: `|ψ_k(x)|² ≤ η Im G_xx(λ_k + iη)`. -/
theorem sq_norm_eigenvector_le_im_green {η : ℝ} (hη : 0 < η) (k x : n) :
    ‖hH.eigenvectorBasis k x‖ ^ 2
      ≤ η * (green H (hH.eigenvalues k + η * Complex.I) x x).im :=
  (sq_norm_eigenvector_le_sum hH hη k x).trans_eq (sum_eq_mul_im_green hH hη k x)

/-- The deterministic core of Theorem 2.2: a bound `|G_xx(λ_k + iη)| ≤ C` on the Green's
function gives `|ψ_k(x)|² ≤ C η`. -/
theorem sq_norm_eigenvector_le_of_norm_green_le {η C : ℝ} (hη : 0 < η) (k x : n)
    (hG : ‖green H (hH.eigenvalues k + η * Complex.I) x x‖ ≤ C) :
    ‖hH.eigenvectorBasis k x‖ ^ 2 ≤ C * η := by
  refine (sq_norm_eigenvector_le_im_green hH hη k x).trans ?_
  rw [mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  exact (Complex.im_le_norm _).trans hG

/-! ### Lipschitz continuity in the energy

The local law is available only at *deterministic* spectral parameters, whereas (2.10) is
evaluated at `λ_k(ω) + iη`.  The bridge is a net of deterministic energies plus the bound
`|Im G_xx(E + iη) - Im G_xx(E' + iη)| ≤ |E - E'| η^{-2}` of `RBM.im_green_lipschitz_energy`,
which is proved here from the spectral decomposition alone — no operator norm, no resolvent
identity, so it stays inside this file's imports. -/

/-- **The rows of the eigenvector matrix are unit vectors**: `∑_l |ψ_l(x)|² = 1`.  This is the
normalization that makes the Lipschitz constant in `RBM.im_green_lipschitz_energy` exactly
`η^{-2}`. -/
theorem sum_sq_norm_eigenvectorBasis (x : n) : ∑ l, ‖hH.eigenvectorBasis l x‖ ^ 2 = 1 := by
  have hUU' : (hH.eigenvectorUnitary : Matrix n n ℂ) *
      star (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self _
  have h := congrArg (fun M : Matrix n n ℂ => M x x) hUU'
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq,
    IsHermitian.eigenvectorUnitary_apply, RCLike.star_def] at h
  have h2 : ∑ l, ((‖hH.eigenvectorBasis l x‖ ^ 2 : ℝ) : ℂ) = (1 : ℂ) := by
    rw [← h]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h2

/-- The single-eigenvalue Lipschitz estimate behind `RBM.im_green_lipschitz_energy`: the Poisson
kernel `E ↦ η w / ((a - E)² + η²)` is `w η^{-2}`-Lipschitz.

The proof is the elementary chain `|Q - P| = |E - E'| |2a - E - E'|`,
`η |2a - E - E'| ≤ (P + Q)/2` (two applications of `2ηu ≤ u² + η²`) and
`(P + Q) η² / 2 ≤ P Q` (from `η² ≤ P`, `η² ≤ Q`). -/
theorem abs_poisson_sub_le {η : ℝ} (hη : 0 < η) (a E E' w : ℝ) (hw : 0 ≤ w) :
    |η * w / ((a - E) ^ 2 + η ^ 2) - η * w / ((a - E') ^ 2 + η ^ 2)|
      ≤ w * |E - E'| / η ^ 2 := by
  set P : ℝ := (a - E) ^ 2 + η ^ 2 with hPdef
  set Q : ℝ := (a - E') ^ 2 + η ^ 2 with hQdef
  have hη2 : 0 < η ^ 2 := by positivity
  have hP : η ^ 2 ≤ P := by rw [hPdef]; nlinarith [sq_nonneg (a - E)]
  have hQ : η ^ 2 ≤ Q := by rw [hQdef]; nlinarith [sq_nonneg (a - E')]
  have hP0 : 0 < P := lt_of_lt_of_le hη2 hP
  have hQ0 : 0 < Q := lt_of_lt_of_le hη2 hQ
  have hsub : η * w / P - η * w / Q = η * w * (Q - P) / (P * Q) := by
    field_simp
  rw [hsub, abs_div, abs_of_pos (mul_pos hP0 hQ0), div_le_div_iff₀ (mul_pos hP0 hQ0) hη2]
  have hQP : Q - P = (E - E') * (2 * a - E - E') := by rw [hPdef, hQdef]; ring
  have habs : |η * w * (Q - P)| = η * w * (|E - E'| * |2 * a - E - E'|) := by
    rw [hQP]
    simp only [abs_mul, abs_of_pos hη, abs_of_nonneg hw, mul_assoc]
  rw [habs]
  have hkey : η * |2 * a - E - E'| ≤ (P + Q) / 2 := by
    have h1 : |2 * a - E - E'| ≤ |a - E| + |a - E'| := by
      have h : 2 * a - E - E' = (a - E) + (a - E') := by ring
      rw [h]; exact abs_add_le _ _
    have h2 : 2 * (η * |a - E|) ≤ (a - E) ^ 2 + η ^ 2 := by
      nlinarith [sq_nonneg (|a - E| - η), sq_abs (a - E), abs_nonneg (a - E)]
    have h3 : 2 * (η * |a - E'|) ≤ (a - E') ^ 2 + η ^ 2 := by
      nlinarith [sq_nonneg (|a - E'| - η), sq_abs (a - E'), abs_nonneg (a - E')]
    rw [hPdef, hQdef]
    nlinarith [hη.le, h1]
  have hE : 0 ≤ |E - E'| := abs_nonneg _
  have hPQ : (P + Q) / 2 * η ^ 2 ≤ P * Q := by nlinarith
  calc η * w * (|E - E'| * |2 * a - E - E'|) * η ^ 2
      = w * |E - E'| * ((η * |2 * a - E - E'|) * η ^ 2) := by ring
    _ ≤ w * |E - E'| * ((P + Q) / 2 * η ^ 2) := by gcongr
    _ ≤ w * |E - E'| * (P * Q) := by gcongr

include hH in
/-- **`Im G_xx` is `η^{-2}`-Lipschitz in the energy**:
`|Im G_xx(E + iη) - Im G_xx(E' + iη)| ≤ |E - E'| / η²`.

This is what lets a local law proved at a net of *deterministic* energies be evaluated at the
*random* energy `λ_k(ω)` of (2.10). -/
theorem im_green_lipschitz_energy {η : ℝ} (hη : 0 < η) (E E' : ℝ) (x : n) :
    |(green H (E + η * Complex.I) x x).im - (green H (E' + η * Complex.I) x x).im|
      ≤ |E - E'| / η ^ 2 := by
  rw [im_green_apply_self hH E hη.ne' x, im_green_apply_self hH E' hη.ne' x,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbd : ∀ l ∈ Finset.univ,
      |η * Complex.normSq (hH.eigenvectorBasis l x) / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)
        - η * Complex.normSq (hH.eigenvectorBasis l x) / ((hH.eigenvalues l - E') ^ 2 + η ^ 2)|
      ≤ ‖hH.eigenvectorBasis l x‖ ^ 2 * (|E - E'| / η ^ 2) := by
    intro l _
    have h := abs_poisson_sub_le hη (hH.eigenvalues l) E E' (‖hH.eigenvectorBasis l x‖ ^ 2)
      (by positivity)
    rw [Complex.normSq_eq_norm_sq]
    calc _ ≤ ‖hH.eigenvectorBasis l x‖ ^ 2 * |E - E'| / η ^ 2 := h
      _ = _ := by ring
  refine (Finset.sum_le_sum hbd).trans ?_
  rw [← Finset.sum_mul, sum_sq_norm_eigenvectorBasis hH x, one_mul]

/-- **The deterministic core of Theorem 2.2, at a nearby deterministic energy.**  If the
deterministic energy `E` is within `d` of the eigenvalue `λ_k` and `|G_xx(E + iη)| ≤ C`, then
`|ψ_k(x)|² ≤ η C + d / η`.

`RBM.sq_norm_eigenvector_le_of_norm_green_le` is the case `E = λ_k`, `d = 0`.  With
`η = N^{-1+θ}`, `d = N^{-A}` for `A` large and `C = O(1)` from the local law, the right-hand
side is `O(N^{-1+θ})`, which is the bound of Theorem 2.2. -/
theorem sq_norm_eigenvector_le_of_norm_green_le_near {η C d : ℝ} (hη : 0 < η) (k x : n) (E : ℝ)
    (hd : |hH.eigenvalues k - E| ≤ d)
    (hG : ‖green H (E + η * Complex.I) x x‖ ≤ C) :
    ‖hH.eigenvectorBasis k x‖ ^ 2 ≤ η * C + d / η := by
  have h1 := sq_norm_eigenvector_le_im_green hH hη k x
  have h2 := im_green_lipschitz_energy hH hη (hH.eigenvalues k) E x
  have h3 : (green H (E + η * Complex.I) x x).im ≤ C := (Complex.im_le_norm _).trans hG
  have h4 : |hH.eigenvalues k - E| / η ^ 2 ≤ d / η ^ 2 := by gcongr
  have h5 : (green H ((hH.eigenvalues k : ℝ) + η * Complex.I) x x).im ≤ C + d / η ^ 2 := by
    have h := (abs_le.1 h2).2
    linarith
  have hfin : η * (C + d / η ^ 2) = η * C + d / η := by field_simp
  calc ‖hH.eigenvectorBasis k x‖ ^ 2
      ≤ η * (green H ((hH.eigenvalues k : ℝ) + η * Complex.I) x x).im := h1
    _ ≤ η * (C + d / η ^ 2) := by gcongr
    _ = η * C + d / η := hfin

end RBM
