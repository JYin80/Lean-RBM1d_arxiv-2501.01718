/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucVanish

/-!
# The multi-index expansion of the fluctuation averaging (4.12)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*: the counting step of the self-contained proof of (4.12).

Write `Z_k := (1 - E_k)(G_{kk} - m)` (`RBM.Gauss.flucDiag`) and, for a weight `t`,

  `flucAvg t := ∑_k t_k Z_k`   (`RBM.Gauss.flucAvg`).

The moment `E |∑_k t_k Z_k|^{2p}` is expanded as a sum over multi-indices.

## The expansion

1. `|w|^{2p} = w^p · conj(w)^p = ∏_{i : Fin p ⊕ Fin p} e_i(w)`, where `e_i` is the identity on
   the left summand and complex conjugation on the right (`RBM.Gauss.epsHom`,
   `RBM.Gauss.prod_epsHom`).  Because the abstract layer of `RBM1D/Gauss/FlucVanish.lean`
   treats the `2p` factors as an
   *arbitrary* family, the conjugated slots cost nothing.
2. Expanding each `e_i(∑_k t_k Z_k) = ∑_k t_k e_i(Z_k)` and multiplying out
   (`Finset.prod_univ_sum`) gives
   `|∑_k t_k Z_k|^{2p} = ∑_{v : Fin p ⊕ Fin p → Idx} (∏_i t_{v i}) ∏_i e_i(Z_{v i})`
   (`RBM.Gauss.prod_epsHom_sum_eq`): a sum over multi-indices `v`, exactly the shape
   `RBM1D/Gauss/FlucVanish.lean` consumes.

The counting step stratifies this sum by **whether some index occurs exactly once**.  A lone
index makes the expectation a pure replacement error (`RBM1D/Gauss/FlucVanish.lean`); without a
lone index the multi-index takes at most `p` distinct values, and for a uniform weight the
weights then produce the extra factor `c^p ≲ Ψ^{2p}`.

## Which weights

The **uniform** weights `t_k = c · 1(k ∈ A)` with `c · #A ≤ 1` (`RBM.Gauss.UniformWeight`).
This covers both coefficient families that (4.12) is actually applied to: `t_k = W^{-1} 1(k ∈ I_a)`
(`RBM.Gauss.uniformWeight_blockAvg`, with `A` the block `I_a`, `c = W^{-1}`, `#A = W`) and
`t_k = S_{ik} = RBM.Sblk` (`RBM.Gauss.uniformWeight_Sblk`, with `A` the three neighbouring blocks,
`c = (3W)^{-1}`, `#A = 3W`).  For a general weight there is a genuine loss: the "image inside a
`p`-set" over-count costs `binom(N, p)` instead of `binom(#A, p)`, which is *not* compensated
unless `#A ≈ c^{-1}`.

## Main results

* `RBM.Gauss.epsHom`, `RBM.Gauss.prod_epsHom` — `|w|^{2p}` as a product of `2p` ring-hom images.
* `RBM.Gauss.prod_epsHom_sum_eq` — the multi-index expansion.
* `RBM.Gauss.flucAvg` — the weighted fluctuation average `∑_k t_k Z_k`.
* `RBM.Gauss.UniformWeight`, `RBM.Gauss.uniformWeight_blockAvg`, `RBM.Gauss.uniformWeight_Sblk`
  — the two coefficient families of (4.12) are uniform weights.

## Deviation from the paper

None in substance.  The `2p` slots are indexed by `Fin p ⊕ Fin p` rather than `1, …, 2p` (so that
"the first half is conjugated" is a case split, not an inequality on `Fin`).
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Finset

/-! ### Multi-indices with a lone slot -/

section Counting

variable {ι κ : Type*}

/-- **A uniform weight**: `t_k = c` on a set `A` and `0` off it, with total mass `c · #A ≤ 1`.
Both coefficient families of (4.12) are of this shape. -/
structure UniformWeight (t : κ → ℝ) (c : ℝ) (A : Finset κ) : Prop where
  /-- The common value is nonnegative. -/
  nonneg : 0 ≤ c
  /-- `t` is `c` on `A` … -/
  mem : ∀ k ∈ A, t k = c
  /-- … and `0` off it. -/
  not_mem : ∀ k ∉ A, t k = 0
  /-- Total mass at most one, the normalization `∑_k |t_k| ≤ 1` of (4.5). -/
  mass : c * A.card ≤ 1

end Counting

/-! ### The conjugation pattern

`|w|^{2p} = w^p · conj(w)^p`.  Indexing the `2p` factors by `Fin p ⊕ Fin p` makes "identity on
the left, conjugation on the right" a case split rather than an inequality on `Fin (2p)`. -/

section Eps

/-- The ring homomorphism attached to the slot `i`: the identity on the left summand, complex
conjugation on the right. -/
def epsHom (p : ℕ) : (Fin p ⊕ Fin p) → (ℂ →+* ℂ) :=
  Sum.elim (fun _ => RingHom.id ℂ) fun _ => starRingEnd ℂ

@[simp] theorem epsHom_inl (p : ℕ) (i : Fin p) (w : ℂ) : epsHom p (Sum.inl i) w = w := rfl

@[simp] theorem epsHom_inr (p : ℕ) (i : Fin p) (w : ℂ) :
    epsHom p (Sum.inr i) w = (starRingEnd ℂ) w := rfl

@[simp] theorem norm_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) (w : ℂ) : ‖epsHom p i w‖ = ‖w‖ := by
  cases i <;> simp

@[simp] theorem epsHom_ofReal (p : ℕ) (i : Fin p ⊕ Fin p) (r : ℝ) :
    epsHom p i (r : ℂ) = (r : ℂ) := by
  cases i <;> simp

theorem measurable_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) : Measurable (epsHom p i) := by
  cases i with
  | inl _ => exact measurable_id
  | inr _ => exact Complex.continuous_conj.measurable

/-- **`|w|^{2p}` as a product of `2p` factors**, `p` of them conjugated. -/
theorem prod_epsHom (p : ℕ) (w : ℂ) : ∏ i, epsHom p i w = ((‖w‖ ^ (2 * p) : ℝ) : ℂ) := by
  rw [Fintype.prod_sum_type]
  simp only [epsHom_inl, epsHom_inr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj', ← pow_mul]
  push_cast
  ring

/-- **The multi-index expansion.**  Multiplying out the `2p` copies of `∑_k t_k Z_k` (with the
last `p` conjugated) gives a sum over multi-indices `v : Fin p ⊕ Fin p → κ`, with the weight
`∏_i t_{v i}` factored out.  The real weights `t_k` are untouched by the conjugations. -/
theorem prod_epsHom_sum_eq (p : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (Z : κ → ℂ) :
    ((‖∑ k, (t k : ℂ) * Z k‖ ^ (2 * p) : ℝ) : ℂ)
      = ∑ v : (Fin p ⊕ Fin p) → κ,
          (∏ i, (t (v i) : ℂ)) * ∏ i, epsHom p i (Z (v i)) := by
  classical
  rw [← prod_epsHom]
  have h1 : ∀ i : Fin p ⊕ Fin p, epsHom p i (∑ k, (t k : ℂ) * Z k)
      = ∑ k, (t k : ℂ) * epsHom p i (Z k) := by
    intro i
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, epsHom_ofReal]
  simp_rw [h1]
  rw [Finset.prod_univ_sum (fun _ : Fin p ⊕ Fin p => (univ : Finset κ))
      fun (i : Fin p ⊕ Fin p) (k : κ) => (t k : ℂ) * epsHom p i (Z k),
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun v _ => Finset.prod_mul_distrib

end Eps

/-! ### `E_k` and conjugation -/

variable {d : Dims} {N : ℕ}

/-! ### The weighted fluctuation average -/

/-- `∑_k t_k Z_k` with `Z_k = (1 - E_k)(G_{kk} - m)`: the quantity (4.12) bounds, in the shape
`RBM1D/Green/EntryBound.lean` consumes it (`norm_sum_coef_green_sub_le`'s `hFA'`, with real
coefficients `t` satisfying `∑_k |t_k| ≤ 1`). -/
noncomputable def flucAvg (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (t : d.Idx N → ℝ) :
    Ω d → ℂ := fun ω => ∑ k, (t k : ℂ) * flucDiag d N u z m k ω

/-! ### The stratified moment bound -/

section Moment

variable (p : ℕ) (u : ℝ) (z m : ℂ) (t : d.Idx N → ℝ)

variable {p u z m t}

end Moment

/-! ### The two coefficient families of (4.12) -/

section Families

variable {d : Dims} {N : ℕ}

/-- For a set `T` of blocks, the index set `{k | k.1 ∈ T}` has `#T · W` elements. -/
theorem card_filter_fst_mem (T : Finset (ZMod (d.L N))) :
    ((univ : Finset (d.Idx N)).filter fun k => k.1 ∈ T).card = T.card * d.W N := by
  classical
  have : ((univ : Finset (d.Idx N)).filter fun k => k.1 ∈ T)
      = T ×ˢ (univ : Finset (Fin (d.W N))) := by
    ext k
    simp [Finset.mem_filter, Finset.mem_product]
  rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- **The block average `t_k = W^{-1} · 1(k ∈ I_a)`** is a uniform weight. -/
theorem uniformWeight_blockAvg (a : ZMod (d.L N)) :
    UniformWeight (fun k : d.Idx N => if k.1 = a then (d.W N : ℝ)⁻¹ else 0)
      ((d.W N : ℝ)⁻¹) ((univ : Finset (d.Idx N)).filter fun k => k.1 = a) := by
  classical
  have hW : (0 : ℝ) < d.W N := Nat.cast_pos.2 (d.W_pos N)
  refine ⟨by positivity, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · simp [(Finset.mem_filter.1 hk).2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp [hk]
  have hcard : ((univ : Finset (d.Idx N)).filter fun k => k.1 = a).card = d.W N := by
    have := card_filter_fst_mem (d := d) (N := N) {a}
    simpa using this
  rw [hcard, inv_mul_cancel₀ hW.ne']

/-- The block-neighbourhood of `a`: the blocks `b` with `a - b ∈ {0, 1, -1}`, three of them. -/
theorem card_filter_sub_mem_sbSupport (a : ZMod (d.L N)) :
    ((univ : Finset (ZMod (d.L N))).filter fun b => a - b ∈ sbSupport (d.L N)).card = 3 := by
  classical
  have hset : ((univ : Finset (ZMod (d.L N))).filter fun b => a - b ∈ sbSupport (d.L N))
      = (sbSupport (d.L N)).image fun s => a - s := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun h => ⟨a - b, h, by ring⟩, ?_⟩
    rintro ⟨s, hs, rfl⟩
    simpa using hs
  rw [hset, Finset.card_image_of_injective _ fun x y h => sub_right_inj.1 h,
    card_sbSupport _ (d.three_le_L N)]

/-- **The variance-profile row `t_k = S_{ik}` (`RBM.Sblk`)** is a uniform weight: it is
`(3W)^{-1}` on the `3W` indices in the three blocks neighbouring the block of `i`, and `0`
elsewhere. -/
theorem uniformWeight_Sblk (i : d.Idx N) :
    UniformWeight (fun j : d.Idx N => Sblk (d.L N) (d.W N) i j)
      ((3 * d.W N : ℝ)⁻¹)
      ((univ : Finset (d.Idx N)).filter fun j => i.1 - j.1 ∈ sbSupport (d.L N)) := by
  classical
  have hW : (0 : ℝ) < d.W N := Nat.cast_pos.2 (d.W_pos N)
  have hcard : ((univ : Finset (d.Idx N)).filter
      fun j => i.1 - j.1 ∈ sbSupport (d.L N)).card = 3 * d.W N := by
    have hset : ((univ : Finset (d.Idx N)).filter fun j => i.1 - j.1 ∈ sbSupport (d.L N))
        = (univ : Finset (d.Idx N)).filter
            fun j => j.1 ∈ (univ : Finset (ZMod (d.L N))).filter
              fun b => i.1 - b ∈ sbSupport (d.L N) := by
      ext j; simp
    rw [hset, card_filter_fst_mem, card_filter_sub_mem_sbSupport]
  refine ⟨by positivity, fun j hj => ?_, fun j hj => ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hk : sbKre (d.L N) (i.1 - j.1) = 1 / 3 := by simp [sbKre, hj]
    rw [Sblk, hk, div_div]
    norm_num
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hk : sbKre (d.L N) (i.1 - j.1) = 0 := by simp [sbKre, hj]
    rw [Sblk, hk, zero_div]
  · rw [hcard]
    push_cast
    rw [inv_mul_cancel₀ (by positivity)]

end Families

end RBM.Gauss

