/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MomentDuhamel

/-!
# M7a: Cauchy–Schwarz for the `E ⊗ E` kernel off the diagonal (T1494)

`RBM.Gauss.eeTens` (`Gauss/DischargeBDG.lean`) is, by its very definition, a finite Gram-type
kernel: `eeTens I I' = ∑_k ∑_{i,j} e_k(I)_{ij} · conj(e_k(I')_{ij})`, where `e_k = emartEdge`
(the second argument's second factor is explicitly conjugated by `starRingEnd ℂ` in `eeEdge`).
Consequently the off-diagonal value `eeTens I I'` is controlled by the two diagonal values
`eeTens I I`, `eeTens I' I'` through the ordinary Cauchy–Schwarz inequality for finite sums —
no positive-semidefiniteness hypothesis needs to be added.

This module proves that inequality (`RBM.Gauss.norm_eeTens_sq_le`), the fact that the diagonal
is real and nonnegative (`RBM.Gauss.eeTens_self_nonneg`), and the doubled-argument form needed
by target M7a, `RBM.Gauss.norm_EEpath_offDiag_sq_le`, reached from `EEpath` through
`RBM.EEBridge.eeArg_append` (`Hierarchy/EEBridgeArgCore.lean`).

## Main declarations

* `RBM.Gauss.finset_inner_cauchy_schwarz` — the elementary finite complex Cauchy–Schwarz
  inequality `‖∑ i ∈ s, F i · conj (G i)‖² ≤ (∑ ‖F i‖²) · (∑ ‖G i‖²)`, proved from the triangle
  inequality plus the real Cauchy–Schwarz inequality for finsets
  (`Finset.sum_mul_sq_le_sq_mul_sq`); no inner-product-space machinery is needed.
* `RBM.Gauss.eeTens_eq_sum_flat` — `eeTens d N z M I I'` flattened into a single `Finset` sum
  over `ℕ × d.Idx N × d.Idx N`, so the elementary inequality above applies to it directly.
* `RBM.Gauss.eeTens_self_nonneg` — target M7a's (T2): `eeTens I I` is real and nonnegative.
* `RBM.Gauss.norm_eeTens_sq_le` — Cauchy–Schwarz for `eeTens` at `I.length = I'.length`.
* `RBM.Gauss.norm_EEpath_offDiag_sq_le` — target M7a's (T1), the doubled-argument form for
  `RBM.MomentDuhamel.EEpath` at `n = 0`.
-/

namespace RBM
namespace Gauss

open Matrix

/-! ### The elementary finite complex Cauchy–Schwarz inequality -/

/-- **Finite complex Cauchy–Schwarz**: for a `Finset`-indexed family `F, G : ι → ℂ`, the norm of
the finite "inner product" `∑ i ∈ s, F i · conj (G i)` is controlled by the two "diagonal" sums
`∑ ‖F i‖²`, `∑ ‖G i‖²`. Proved by the triangle inequality (`norm_sum_le`) followed by the real
Cauchy–Schwarz inequality for finsets (`Finset.sum_mul_sq_le_sq_mul_sq`); no
positive-semidefiniteness or inner-product-space hypothesis is used. -/
theorem finset_inner_cauchy_schwarz {ι : Type*} (s : Finset ι) (F G : ι → ℂ) :
    ‖∑ i ∈ s, F i * (starRingEnd ℂ) (G i)‖ ^ 2
      ≤ (∑ i ∈ s, ‖F i‖ ^ 2) * (∑ i ∈ s, ‖G i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, F i * (starRingEnd ℂ) (G i)‖ ≤ ∑ i ∈ s, ‖F i‖ * ‖G i‖ := by
    calc ‖∑ i ∈ s, F i * (starRingEnd ℂ) (G i)‖
        ≤ ∑ i ∈ s, ‖F i * (starRingEnd ℂ) (G i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖F i‖ * ‖G i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, Complex.norm_conj]
  have h2 : (∑ i ∈ s, ‖F i‖ * ‖G i‖) ^ 2 ≤ (∑ i ∈ s, ‖F i‖ ^ 2) * ∑ i ∈ s, ‖G i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖F i‖) (fun i => ‖G i‖)
  have h3 : ‖∑ i ∈ s, F i * (starRingEnd ℂ) (G i)‖ ^ 2 ≤ (∑ i ∈ s, ‖F i‖ * ‖G i‖) ^ 2 := by
    gcongr
  exact h3.trans h2

/-! ### Flattening `eeTens` into a single `Finset` sum -/

variable (d : Dims) (N : ℕ)

/-- **`eeTens d N z M I I'` flattened**: the triple sum of Definition 5.4
(`k` over the edges, then `i, j` over the matrix index) rewritten as a single `Finset` sum over
`ℕ × d.Idx N × d.Idx N`, via `Finset.sum_product'`. -/
theorem eeTens_eq_sum_flat (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) :
    eeTens d N z M I I'
      = ∑ p ∈ (Finset.range I.length) ×ˢ ((Finset.univ : Finset (d.Idx N)) ×ˢ Finset.univ),
          emartEdge d N z I M p.1 p.2.1 p.2.2
            * (starRingEnd ℂ) (emartEdge d N z I' M p.1 p.2.1 p.2.2) := by
  have step2 : ∀ k : ℕ, eeEdge d N z M I I' k
      = ∑ q ∈ (Finset.univ : Finset (d.Idx N)) ×ˢ (Finset.univ : Finset (d.Idx N)),
          emartEdge d N z I M k q.1 q.2 * (starRingEnd ℂ) (emartEdge d N z I' M k q.1 q.2) := by
    intro k
    rw [eeEdge]
    exact (Finset.sum_product' Finset.univ Finset.univ
      (fun i j => emartEdge d N z I M k i j * (starRingEnd ℂ) (emartEdge d N z I' M k i j))).symm
  calc eeTens d N z M I I'
      = ∑ k ∈ Finset.range I.length, eeEdge d N z M I I' k := rfl
    _ = ∑ k ∈ Finset.range I.length,
          ∑ q ∈ (Finset.univ : Finset (d.Idx N)) ×ˢ (Finset.univ : Finset (d.Idx N)),
            emartEdge d N z I M k q.1 q.2 * (starRingEnd ℂ) (emartEdge d N z I' M k q.1 q.2) :=
        Finset.sum_congr rfl fun k _ => step2 k
    _ = ∑ p ∈ (Finset.range I.length) ×ˢ ((Finset.univ : Finset (d.Idx N)) ×ˢ Finset.univ),
          emartEdge d N z I M p.1 p.2.1 p.2.2
            * (starRingEnd ℂ) (emartEdge d N z I' M p.1 p.2.1 p.2.2) :=
        (Finset.sum_product' (Finset.range I.length)
          ((Finset.univ : Finset (d.Idx N)) ×ˢ (Finset.univ : Finset (d.Idx N)))
          (fun k q => emartEdge d N z I M k q.1 q.2
            * (starRingEnd ℂ) (emartEdge d N z I' M k q.1 q.2))).symm

/-! ### M7a (T2): the diagonal is real and nonnegative -/

/-- **M7a's (T2)**, `RBM.Gauss.eeTens_self_nonneg`: `eeTens I I` is real and nonnegative — it is
a finite sum of squared norms, `∑_k ∑_{i,j} ‖e_k(I)_{ij}‖²`. -/
theorem eeTens_self_nonneg (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I : LoopIdx (ZMod (d.L N))) :
    ∃ r : ℝ, 0 ≤ r ∧ eeTens d N z M I I = (r : ℂ) := by
  refine ⟨∑ p ∈ (Finset.range I.length) ×ˢ ((Finset.univ : Finset (d.Idx N)) ×ˢ Finset.univ),
      ‖emartEdge d N z I M p.1 p.2.1 p.2.2‖ ^ 2, Finset.sum_nonneg fun p _ => sq_nonneg _, ?_⟩
  rw [eeTens_eq_sum_flat, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun p _ => mul_conj_eq _

/-! ### M7a (T1): Cauchy–Schwarz for `eeTens`, then for `EEpath` -/

/-- **Cauchy–Schwarz for the `eeTens` Gram kernel**, at `I.length = I'.length` (so the two
loops range over the same edge index set, `eeTens`'s definition already forcing `eeTens I I'`
to sum over `I`'s edges): the off-diagonal value's norm is controlled by the two diagonal
values, with no positive-semidefiniteness hypothesis. -/
theorem norm_eeTens_sq_le (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (I I' : LoopIdx (ZMod (d.L N))) (hlen : I.length = I'.length) :
    ‖eeTens d N z M I I'‖ ^ 2 ≤ ‖eeTens d N z M I I‖ * ‖eeTens d N z M I' I'‖ := by
  set s : Finset (ℕ × d.Idx N × d.Idx N) :=
    (Finset.range I.length) ×ˢ ((Finset.univ : Finset (d.Idx N)) ×ˢ Finset.univ) with hs
  set F : ℕ × d.Idx N × d.Idx N → ℂ := fun p => emartEdge d N z I M p.1 p.2.1 p.2.2 with hF
  set G : ℕ × d.Idx N × d.Idx N → ℂ := fun p => emartEdge d N z I' M p.1 p.2.1 p.2.2 with hG
  have h1 : eeTens d N z M I I' = ∑ p ∈ s, F p * (starRingEnd ℂ) (G p) :=
    eeTens_eq_sum_flat d N z M I I'
  have h2 : eeTens d N z M I I = ((∑ p ∈ s, ‖F p‖ ^ 2 : ℝ) : ℂ) := by
    have h := eeTens_eq_sum_flat d N z M I I
    rw [h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p _ => mul_conj_eq _
  have h3 : eeTens d N z M I' I' = ((∑ p ∈ s, ‖G p‖ ^ 2 : ℝ) : ℂ) := by
    have h := eeTens_eq_sum_flat d N z M I' I'
    rw [← hlen] at h
    rw [h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p _ => mul_conj_eq _
  have hn2 : (0 : ℝ) ≤ ∑ p ∈ s, ‖F p‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hn3 : (0 : ℝ) ≤ ∑ p ∈ s, ‖G p‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  rw [h1, h2, h3, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hn2, abs_of_nonneg hn3]
  exact finset_inner_cauchy_schwarz s F G

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **M7a's (T1)**, `RBM.Gauss.norm_EEpath_offDiag_sq_le`: Cauchy–Schwarz for the doubled
`E ⊗ E` argument of `RBM.MomentDuhamel.EEpath` at `n = 0`, for the Gaussian sample or for
whatever `X` `EEpath` is defined for — the definition of `EEpath` puts no further hypothesis on
`X`. Reached from `EEpath` via `eeFun`/`eeArg` (`rfl`) and `RBM.EEBridge.eeArg_append`. -/
theorem norm_EEpath_offDiag_sq_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (σ : Fin (0 + 2) → Bool) (a a' : LoopArg (B.L N) (0 + 2)) :
    ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a')‖ ^ 2
      ≤ ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a a)‖
        * ‖MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append a' a')‖ := by
  have hEq : ∀ b b' : LoopArg (B.L N) (0 + 2),
      MomentDuhamel.EEpath X E 0 N u ω σ (Fin.append b b')
        = eeTens B.toDims N (zt E u) (X.H N u ω) (toIdx σ b) (toIdx σ b') := by
    intro b b'
    change EEBridge.eeArg B.toDims N (zt E u) (X.H N u ω) σ (Fin.append b b') = _
    exact EEBridge.eeArg_append B.toDims N (zt E u) (X.H N u ω) σ b b'
  have hlen : (toIdx σ a).length = (toIdx σ a').length := by
    rw [toIdx_length, toIdx_length]
  rw [hEq a a', hEq a a, hEq a' a']
  exact norm_eeTens_sq_le B.toDims N (zt E u) (X.H N u ω) (toIdx σ a) (toIdx σ a') hlen

end Gauss
end RBM
