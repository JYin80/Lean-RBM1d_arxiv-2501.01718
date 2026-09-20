/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucVanish

/-!
# The counting step of the fluctuation averaging (4.12)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*: the second half of the self-contained proof of (4.12).

Write `Z_k := (1 - E_k)(G_{kk} - m)` (`RBM.Gauss.flucDiag`, T86) and, for a weight `t`,

  `flucAvg t := ∑_k t_k Z_k`.

This file expands `E |∑_k t_k Z_k|^{2p}` as a sum over multi-indices and stratifies the sum by
**whether some index occurs exactly once**.

## The argument

1. `|w|^{2p} = w^p · conj(w)^p = ∏_{i : Fin p ⊕ Fin p} e_i(w)`, where `e_i` is the identity on
   the left summand and complex conjugation on the right (`RBM.Gauss.epsHom`,
   `RBM.Gauss.prod_epsHom`).  Because T86's abstract layer treats the `2p` factors as an
   *arbitrary* family, the conjugated slots cost nothing.
2. Expanding each `e_i(∑_k t_k Z_k) = ∑_k t_k e_i(Z_k)` and multiplying out
   (`Finset.prod_univ_sum`) gives
   `|∑_k t_k Z_k|^{2p} = ∑_{v : Fin p ⊕ Fin p → Idx} (∏_i t_{v i}) ∏_i e_i(Z_{v i})`
   (`RBM.Gauss.prod_epsHom_sum_eq`): a sum over multi-indices `v`, exactly the shape T86
   consumes.
3. **Stratum with a lone slot** (`RBM.Gauss.HasLoneSlot v`, i.e. `∃ i₀, ∀ i ≠ i₀, v i ≠ v i₀`):
   T86's `RBM.Gauss.norm_integral_prod_le` bounds the expectation by the pure replacement error
   `(2p - 1) · ε · B^{2p-1}`.  Summing the weights over *all* `v` costs only
   `(∑_k |t_k|)^{2p} ≤ 1`.
4. **The other strata**: every index occurs at least twice, so the multi-index takes at most
   `p` distinct values (`RBM.Gauss.two_mul_card_image_le`).  The expectation is bounded
   trivially by `B^{2p}`, and the *weights* now produce the extra factor: a multi-index with at
   most `p` distinct values has its image inside a `p`-element subset of the support, so there
   are at most `binom(#A, p) · p^{2p} ≤ (#A)^p p^{2p}` of them
   (`RBM.Gauss.card_filter_not_hasLoneSlot_le`), whence
   `∑_{v} ∏_i |t_{v i}| ≤ c^p p^{2p}` (`RBM.Gauss.sum_prod_not_hasLoneSlot_le`).

Altogether (`RBM.Gauss.integral_norm_flucAvg_pow_le_uniform`)

  `E|∑_k t_k Z_k|^{2p} ≤ (2p - 1) ε B^{2p-1} + c^p p^{2p} B^{2p}`,

which with `B ≈ N^ε Ψ`, `c ≤ C/W ≲ Ψ²` and a replacement error `ε ≲ Ψ²` is
`≲ (N^ε Ψ²)^{2p}`: the `c^p` is precisely "the extra factor `Ψ^{2p}`" of the ticket.

## Which weights

Only the **uniform** weights `t_k = c · 1(k ∈ A)` with `c · #A ≤ 1` are done, not general `t`.
This is the escape hatch the ticket grants, and it covers both coefficient families that (4.12)
is actually applied to: `t_k = W^{-1} 1(k ∈ I_a)` (`RBM.Gauss.uniformWeight_blockAvg`, with
`A` the block `I_a`, `c = W^{-1}`, `#A = W`) and `t_k = S_{ik} = RBM.Sblk` (
`RBM.Gauss.uniformWeight_Sblk`, with `A` the three neighbouring blocks, `c = (3W)^{-1}`,
`#A = 3W`).  The reason to stop here is not laziness about `Finset` bookkeeping but a genuine
loss: for a general weight the "image inside a `p`-set" over-count costs `binom(N, p)` instead
of `binom(#A, p)`, which is *not* compensated unless `#A ≈ c^{-1}` — the honest general
statement needs the partition-of-slots stratification, several hundred lines of `Finset`
combinatorics for a case the paper never uses.  The general stratified bound
`RBM.Gauss.integral_norm_flucAvg_pow_le` **is** proved for arbitrary real `t` with
`∑_k |t_k| ≤ 1`; what is specialized is only the final weight count.

## The `≺` / pointwise seam with T85

T86 left this to T87/T88 and it is **not closed here**: the parameters `B` (a uniform bound on
every factor) and `ε` (a uniform bound on the replacement error) are still hypotheses of
`RBM.Gauss.integral_norm_flucAvg_pow_le`, exactly as in T86.  Closing the seam means producing
them from T85's `RBM.Gauss.minorReplace_diag_stochDom`, which is a bound on a high-probability
event; that is the indicator/truncation step, and it belongs to T88 together with the passage
back to `≺` through T73's `RBM.Gauss.stochDom_of_momentDom`.  What this file adds is that the
truncation now has a *single* interface to hit: the six uniform hypotheses `hZmeas`, `hYmeas`,
`hrow`, `hZB`, `hYB`, `hεb` below, each quantified over the index set only.

## Main results

* `RBM.Gauss.HasLoneSlot` — "some slot's value is taken by no other slot".
* `RBM.Gauss.two_mul_card_image_le` — no lone slot ⟹ at most `p` distinct values.
* `RBM.Gauss.card_filter_not_hasLoneSlot_le` — the count of such multi-indices.
* `RBM.Gauss.sum_prod_not_hasLoneSlot_le` — the weight of those strata, `≤ c^p p^{2p}`.
* `RBM.Gauss.epsHom`, `RBM.Gauss.prod_epsHom` — `|w|^{2p}` as a product of `2p` ring-hom images.
* `RBM.Gauss.prod_epsHom_sum_eq` — the multi-index expansion.
* `RBM.Gauss.integral_norm_flucAvg_pow_le` — **the stratified moment bound**, general `t`.
* `RBM.Gauss.integral_norm_flucAvg_pow_le_uniform` — the same with the weight count carried
  out, for uniform `t`.
* `RBM.Gauss.uniformWeight_blockAvg`, `RBM.Gauss.uniformWeight_Sblk` — the two coefficient
  families of (4.12) are uniform weights.

## Deviation from the paper

None in substance; three bookkeeping choices, recorded in `docs/paper-deltas.md`:
the `2p` slots are indexed by `Fin p ⊕ Fin p` rather than `1, …, 2p` (so that "the first half
is conjugated" is a case split, not an inequality on `Fin`); the stratification is by the
*predicate* `HasLoneSlot` rather than by the number of distinct indices (the two agree, and the
count of distinct indices enters only through `two_mul_card_image_le`); and the final weight
count is done for uniform weights only, as discussed above.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Finset

/-! ### Multi-indices with a lone slot -/

section Counting

variable {ι κ : Type*}

/-- The multi-index `v` has a **lone slot**: some slot `i₀` whose value `v i₀` is taken by no
other slot.  This is the hypothesis `hone` of T86's
`RBM.Gauss.norm_integral_prod_flucDiag_le`, packaged as a predicate so that the sum over
multi-indices can be split on it. -/
def HasLoneSlot (v : ι → κ) : Prop := ∃ i₀, ∀ i, i ≠ i₀ → v i ≠ v i₀

instance decidableHasLoneSlot [Fintype ι] [DecidableEq ι] [DecidableEq κ] (v : ι → κ) :
    Decidable (HasLoneSlot v) := by
  unfold HasLoneSlot; infer_instance

/-- If no slot is lone, then **every** value of `v` is taken at least twice. -/
theorem two_le_card_fiber [Fintype ι] [DecidableEq ι] [DecidableEq κ] {v : ι → κ}
    (hv : ¬ HasLoneSlot v) (i₀ : ι) :
    2 ≤ ((univ : Finset ι).filter fun i => v i = v i₀).card := by
  have hex : ∃ i, i ≠ i₀ ∧ v i = v i₀ := by
    by_contra hcon
    exact hv ⟨i₀, fun i hi hvi => hcon ⟨i, hi, hvi⟩⟩
  obtain ⟨i, hi, hvi⟩ := hex
  refine Finset.one_lt_card.2 ⟨i, ?_, i₀, ?_, hi⟩ <;>
    simp [Finset.mem_filter, hvi]

/-- **No lone slot ⟹ at most `p` distinct indices.**  Each of the `#(image v)` values uses up
at least two of the `#ι = 2p` slots. -/
theorem two_mul_card_image_le [Fintype ι] [DecidableEq ι] [DecidableEq κ] {v : ι → κ}
    (hv : ¬ HasLoneSlot v) : 2 * ((univ : Finset ι).image v).card ≤ Fintype.card ι := by
  classical
  have hfib : (univ : Finset ι).card
      = ∑ b ∈ (univ : Finset ι).image v, ((univ : Finset ι).filter fun i => v i = b).card :=
    Finset.card_eq_sum_card_fiberwise fun i _ => Finset.mem_coe.2
      (Finset.mem_image_of_mem v (Finset.mem_univ i))
  have hge : ∑ _b ∈ (univ : Finset ι).image v, 2
      ≤ ∑ b ∈ (univ : Finset ι).image v, ((univ : Finset ι).filter fun i => v i = b).card := by
    refine Finset.sum_le_sum fun b hb => ?_
    obtain ⟨i₀, _, rfl⟩ := Finset.mem_image.1 hb
    exact two_le_card_fiber hv i₀
  rw [Finset.sum_const, smul_eq_mul, mul_comm] at hge
  rw [Finset.card_univ] at hfib
  omega

/-- **The number of multi-indices without a lone slot.**  Such a `v` takes at most `p` distinct
values, all inside `A`, so its image is contained in a `p`-element subset `S ⊆ A`, and `v` is
then one of the `p^{2p}` functions into `S`.  Over-counting `S` costs `binom(#A, p) ≤ (#A)^p`.

This is where "at most `p` distinct indices" becomes a number. -/
theorem card_filter_not_hasLoneSlot_le [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (A : Finset κ) (p : ℕ) (hcard : Fintype.card ι = 2 * p) (hp : p ≤ A.card) :
    ((Fintype.piFinset fun _ : ι => A).filter fun v => ¬ HasLoneSlot v).card
      ≤ A.card ^ p * p ^ (2 * p) := by
  classical
  have hsub : ((Fintype.piFinset fun _ : ι => A).filter fun v => ¬ HasLoneSlot v)
      ⊆ (A.powersetCard p).biUnion fun S => Fintype.piFinset fun _ : ι => S := by
    intro v hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
    obtain ⟨hvA, hvL⟩ := hv
    have h1 : (univ : Finset ι).image v ⊆ A := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha
      exact hvA i
    have h2 : ((univ : Finset ι).image v).card ≤ p := by
      have := two_mul_card_image_le hvL
      omega
    obtain ⟨S, hS1, hS2, hS3⟩ := Finset.exists_subsuperset_card_eq h1 h2 hp
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨hS2, hS3⟩,
      Fintype.mem_piFinset.2 fun i => hS1 (Finset.mem_image_of_mem v (Finset.mem_univ i))⟩
  calc ((Fintype.piFinset fun _ : ι => A).filter fun v => ¬ HasLoneSlot v).card
      ≤ ((A.powersetCard p).biUnion fun S => Fintype.piFinset fun _ : ι => S).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ S ∈ A.powersetCard p, (Fintype.piFinset fun _ : ι => S).card := Finset.card_biUnion_le
    _ = ∑ _S ∈ A.powersetCard p, p ^ (2 * p) := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, hcard,
          (Finset.mem_powersetCard.1 hS).2]
    _ = (A.card).choose p * p ^ (2 * p) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    _ ≤ A.card ^ p * p ^ (2 * p) := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

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

theorem UniformWeight.sum_abs_le [Fintype κ] [DecidableEq κ] {t : κ → ℝ} {c : ℝ} {A : Finset κ}
    (h : UniformWeight t c A) : ∑ k, |t k| ≤ 1 := by
  classical
  have hsplit : ∑ k, |t k| = ∑ k ∈ A, |t k| := by
    refine (Finset.sum_subset (Finset.subset_univ A) ?_).symm
    intro k _ hk
    rw [h.not_mem k hk, abs_zero]
  have hval : ∑ k ∈ A, |t k| = c * A.card := by
    rw [Finset.sum_congr rfl fun k hk => (by
        rw [h.mem k hk, abs_of_nonneg h.nonneg] : |t k| = c), Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  rw [hsplit, hval]
  exact h.mass

/-- **The weight of the strata without a lone slot**, for a uniform weight.

`∑_{v : no lone slot} ∏_i |t_{v i}| ≤ c^p · p^{2p}` — the extra factor `c^p` (with `c ≤ C/W`)
is the whole point of the counting step: the trivial bound over *all* multi-indices would only
give `(∑_k |t_k|)^{2p} ≤ 1`. -/
theorem sum_prod_not_hasLoneSlot_le [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : UniformWeight t c A)
    (p : ℕ) (hcard : Fintype.card ι = 2 * p) (hp : p ≤ A.card) :
    ∑ v ∈ (univ : Finset (ι → κ)).filter (fun v => ¬ HasLoneSlot v), ∏ i, |t (v i)|
      ≤ c ^ p * (p : ℝ) ^ (2 * p) := by
  classical
  -- only multi-indices with values in `A` contribute
  have hrestrict : ∑ v ∈ (univ : Finset (ι → κ)).filter (fun v => ¬ HasLoneSlot v),
        ∏ i, |t (v i)|
      = ∑ v ∈ ((Fintype.piFinset fun _ : ι => A).filter fun v => ¬ HasLoneSlot v),
        ∏ i, |t (v i)| := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨Finset.mem_univ _, hv.2⟩
    · intro v hv hv'
      rw [Finset.mem_filter] at hv
      have : ∃ i, v i ∉ A := by
        by_contra hcon
        refine hv' (Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, hv.2⟩)
        by_contra hi
        exact hcon ⟨i, hi⟩
      obtain ⟨i, hi⟩ := this
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hw.not_mem (v i) hi, abs_zero]
  -- on those, the product is `c^{2p}`
  have hval : ∀ v ∈ ((Fintype.piFinset fun _ : ι => A).filter fun v => ¬ HasLoneSlot v),
      ∏ i, |t (v i)| = c ^ (2 * p) := by
    intro v hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
    have hone : ∀ i : ι, |t (v i)| = c := fun i => by
      rw [hw.mem (v i) (hv.1 i), abs_of_nonneg hw.nonneg]
    simp_rw [hone]
    rw [Finset.prod_const, Finset.card_univ, hcard]
  have hc2p : (0 : ℝ) ≤ c ^ (2 * p) := pow_nonneg hw.nonneg _
  have hcount := card_filter_not_hasLoneSlot_le (ι := ι) A p hcard hp
  calc ∑ v ∈ (univ : Finset (ι → κ)).filter (fun v => ¬ HasLoneSlot v), ∏ i, |t (v i)|
      = (((Fintype.piFinset fun _ : ι => A).filter fun v => ¬ HasLoneSlot v).card : ℝ)
          * c ^ (2 * p) := by
        rw [hrestrict, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((A.card ^ p * p ^ (2 * p) : ℕ) : ℝ) * c ^ (2 * p) := by
        refine mul_le_mul_of_nonneg_right ?_ hc2p
        exact_mod_cast hcount
    _ = (c * A.card) ^ p * (c ^ p * (p : ℝ) ^ (2 * p)) := by
        push_cast
        rw [two_mul, pow_add, mul_pow]
        ring
    _ ≤ 1 * (c ^ p * (p : ℝ) ^ (2 * p)) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (pow_nonneg hw.nonneg _) (by positivity))
        exact pow_le_one₀ (mul_nonneg hw.nonneg (Nat.cast_nonneg _)) hw.mass
    _ = c ^ p * (p : ℝ) ^ (2 * p) := one_mul _

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

/-- `E_k` commutes with the slot homomorphisms: it is the identity on the left slots and, being
an integral, commutes with complex conjugation on the right ones (`integral_conj`). -/
theorem condRow_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) (k : d.Idx N) (X : Ω d → ℂ) :
    condRow d N k (fun ω => epsHom p i (X ω)) = fun ω => epsHom p i (condRow d N k X ω) := by
  cases i with
  | inl j => simp only [epsHom_inl]
  | inr j =>
      funext ω
      simp only [epsHom_inr, condRow_apply]
      exact integral_conj

/-! ### The weighted fluctuation average -/

/-- `∑_k t_k Z_k` with `Z_k = (1 - E_k)(G_{kk} - m)`: the quantity (4.12) bounds, in the shape
`RBM1D/Green/EntryBound.lean` consumes it (`norm_sum_coef_green_sub_le`'s `hFA'`, with real
coefficients `t` satisfying `∑_k |t_k| ≤ 1`). -/
noncomputable def flucAvg (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (t : d.Idx N → ℝ) :
    Ω d → ℂ := fun ω => ∑ k, (t k : ℂ) * flucDiag d N u z m k ω

/-! ### The stratified moment bound -/

section Moment

variable (p : ℕ) (u : ℝ) (z m : ℂ) (t : d.Idx N → ℝ)

/-- The `2p`-fold product attached to a multi-index `v`, with the last `p` slots conjugated. -/
private noncomputable def slotFac (v : (Fin p ⊕ Fin p) → d.Idx N) (i : Fin p ⊕ Fin p) :
    Ω d → ℂ := fun ω => epsHom p i (flucDiag d N u z m (v i) ω)

variable {p u z m t}

/-- **The stratified moment bound for `∑_k t_k Z_k`.**

The strata with a lone slot are killed by T86 down to the pure replacement error `ε`; the
remaining strata are bounded trivially by `B^{2p}` and pay for themselves through their
*weight*, which is left here as the explicit sum over multi-indices without a lone slot
(`RBM.Gauss.sum_prod_not_hasLoneSlot_le` evaluates it for uniform weights).

The hypotheses `hZB`, `hYB`, `hεb` are the *uniform* (pointwise) bounds of T86; producing them
from T85's `≺` estimates is the truncation step left to T88. -/
theorem integral_norm_flucAvg_pow_le {B ε : ℝ} (hB : 0 ≤ B) (hε0 : 0 ≤ ε)
    (hZmeas : ∀ k, Measurable (flucDiag d N u z m k))
    (hYmeas : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}),
      Measurable (flucDiagMinor d N u z m κ k))
    (hrow : ∀ k, RowIntegrable d N k (greenDiagCentered d N u z m k))
    (hZB : ∀ k, ∀ ω, ‖flucDiag d N u z m k ω‖ ≤ B)
    (hYB : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}), ∀ ω,
      ‖flucDiagMinor d N u z m κ k ω‖ ≤ B)
    (hεb : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}), ∀ ω,
      ‖flucDiag d N u z m k.1 ω - flucDiagMinor d N u z m κ k ω‖ ≤ ε)
    (ht : ∑ k, |t k| ≤ 1) :
    ∫ ω, ‖flucAvg d N u z m t ω‖ ^ (2 * p) ∂(P d)
      ≤ ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)
        + (∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter
              (fun v => ¬ HasLoneSlot v), ∏ i, |t (v i)|) * B ^ (2 * p) := by
  classical
  have hcardι : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    simp [Fintype.card_sum, two_mul]
  -- the pointwise expansion
  have hexp : ∀ ω : Ω d, ((‖flucAvg d N u z m t ω‖ ^ (2 * p) : ℝ) : ℂ)
      = ∑ v : (Fin p ⊕ Fin p) → d.Idx N,
          (∏ i, (t (v i) : ℂ)) * ∏ i, slotFac p u z m v i ω :=
    fun ω => prod_epsHom_sum_eq p t fun k => flucDiag d N u z m k ω
  -- measurability and the uniform bound of each stratum's integrand
  have hmeas : ∀ (v : (Fin p ⊕ Fin p) → d.Idx N) (i : Fin p ⊕ Fin p),
      Measurable (slotFac p u z m v i) := fun v i =>
    (measurable_epsHom p i).comp (hZmeas (v i))
  have hprodbd : ∀ (v : (Fin p ⊕ Fin p) → d.Idx N) (ω : Ω d),
      ‖∏ i, slotFac p u z m v i ω‖ ≤ B ^ (2 * p) := by
    intro v ω
    calc ‖∏ i, slotFac p u z m v i ω‖ = ∏ i, ‖slotFac p u z m v i ω‖ := norm_prod _ _
      _ ≤ ∏ _i : Fin p ⊕ Fin p, B := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
          simpa [slotFac] using hZB (v i) ω
      _ = B ^ (2 * p) := by rw [Finset.prod_const, Finset.card_univ, hcardι]
  have hint : ∀ v : (Fin p ⊕ Fin p) → d.Idx N,
      Integrable (fun ω => (∏ i, (t (v i) : ℂ)) * ∏ i, slotFac p u z m v i ω) (P d) := by
    intro v
    refine integrable_P_of_measurable_of_bound
      (measurable_const.mul (Finset.measurable_prod _ fun i _ => hmeas v i))
      (C := ‖∏ i, (t (v i) : ℂ)‖ * B ^ (2 * p)) fun ω => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hprodbd v ω) (norm_nonneg _)
  -- the integral of the expansion
  have hI : ∫ ω, ((‖flucAvg d N u z m t ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d)
      = ∑ v : (Fin p ⊕ Fin p) → d.Idx N,
          (∏ i, (t (v i) : ℂ)) * ∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun v _ => hint v]
    exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
  -- the trivial bound, valid on every stratum
  have hall : ∀ v : (Fin p ⊕ Fin p) → d.Idx N,
      ‖∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖ ≤ B ^ (2 * p) := by
    intro v
    simpa using norm_integral_le_of_norm_le_const (μ := P d)
      (f := fun ω => ∏ i, slotFac p u z m v i ω) (C := B ^ (2 * p))
      (Filter.Eventually.of_forall (hprodbd v))
  -- the vanishing bound on the strata with a lone slot
  have hlone : ∀ v : (Fin p ⊕ Fin p) → d.Idx N, HasLoneSlot v →
      ‖∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖
        ≤ ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1) := by
    rintro v ⟨i₀, hone⟩
    have key := norm_integral_prod_le (d := d) (N := N) (κ := v i₀) (i₀ := i₀)
      (Z := slotFac p u z m v)
      (Y := fun i ω => epsHom p i (flucDiagMinorFam d N u z m i₀ v hone i ω))
      (B := B) (ε := ε) hB (hmeas v)
      (fun i hi => (measurable_epsHom p i).comp (by
        rw [flucDiagMinorFam_of_ne d N u z m hone hi]
        exact hYmeas (v i₀) ⟨v i, hone i hi⟩))
      (by
        rw [show slotFac p u z m v i₀ = fun ω => epsHom p i₀ (flucDiag d N u z m (v i₀) ω) from
          rfl, condRow_epsHom, condRow_flucDiag u z m (v i₀) (hrow (v i₀))]
        funext ω
        simp)
      (fun i hi => (finDepOffRow_flucDiagMinorFam d N u z m hone hi).comp (epsHom p i))
      (fun i ω => by simpa [slotFac] using hZB (v i) ω)
      (fun i hi ω => by
        rw [norm_epsHom, flucDiagMinorFam_of_ne d N u z m hone hi]
        exact hYB (v i₀) ⟨v i, hone i hi⟩ ω)
      (fun i hi ω => by
        rw [show slotFac p u z m v i ω = epsHom p i (flucDiag d N u z m (v i) ω) from rfl,
          ← map_sub, norm_epsHom, flucDiagMinorFam_of_ne d N u z m hone hi]
        exact hεb (v i₀) ⟨v i, hone i hi⟩ ω)
    rwa [hcardι] at key
  -- assemble
  have hnonneg : (0 : ℝ) ≤ ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1) := by positivity
  have hweightall : ∑ v : (Fin p ⊕ Fin p) → d.Idx N, ∏ i, |t (v i)| = (∑ k, |t k|) ^ (2 * p) := by
    have h := Finset.sum_prod_piFinset (ι := Fin p ⊕ Fin p) (univ : Finset (d.Idx N))
      fun (_ : Fin p ⊕ Fin p) (k : d.Idx N) => |t k|
    rw [Fintype.piFinset_univ] at h
    rw [h, Finset.prod_const, Finset.card_univ, hcardι]
  have habs : (0 : ℝ) ≤ ∑ k, |t k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  -- the norm of the whole expansion
  have hbound : ‖∫ ω, ((‖flucAvg d N u z m t ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d)‖
      ≤ ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)
        + (∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter
              (fun v => ¬ HasLoneSlot v), ∏ i, |t (v i)|) * B ^ (2 * p) := by
    rw [hI]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ v : (Fin p ⊕ Fin p) → d.Idx N,
        ‖(∏ i, (t (v i) : ℂ)) * ∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖
          = (∏ i, |t (v i)|) * ‖∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖ := by
      intro v
      rw [norm_mul, norm_prod]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by
        rw [Complex.norm_real, Real.norm_eq_abs]
    simp_rw [hterm]
    rw [← Finset.sum_filter_add_sum_filter_not (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N))
      (fun v => HasLoneSlot v)]
    have h1 : ∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter (fun v => HasLoneSlot v),
          (∏ i, |t (v i)|) * ‖∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖
        ≤ ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1) := by
      calc ∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter (fun v => HasLoneSlot v),
              (∏ i, |t (v i)|) * ‖∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖
          ≤ ∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter (fun v => HasLoneSlot v),
              (∏ i, |t (v i)|) * (((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)) := by
            refine Finset.sum_le_sum fun v hv => ?_
            exact mul_le_mul_of_nonneg_left (hlone v (Finset.mem_filter.1 hv).2)
              (Finset.prod_nonneg fun i _ => abs_nonneg _)
        _ = (∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter
              (fun v => HasLoneSlot v), ∏ i, |t (v i)|)
            * (((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)) := by rw [Finset.sum_mul]
        _ ≤ (∑ v : (Fin p ⊕ Fin p) → d.Idx N, ∏ i, |t (v i)|)
            * (((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun v _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _
        _ ≤ 1 * (((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)) := by
            refine mul_le_mul_of_nonneg_right ?_ hnonneg
            rw [hweightall]
            exact pow_le_one₀ habs ht
        _ = ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1) := one_mul _
    have h2 : ∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter
            (fun v => ¬ HasLoneSlot v),
          (∏ i, |t (v i)|) * ‖∫ ω, ∏ i, slotFac p u z m v i ω ∂(P d)‖
        ≤ (∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter
              (fun v => ¬ HasLoneSlot v), ∏ i, |t (v i)|) * B ^ (2 * p) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun v _ => ?_
      exact mul_le_mul_of_nonneg_left (hall v) (Finset.prod_nonneg fun i _ => abs_nonneg _)
    linarith
  -- and back to the real integral
  have hofR : (∫ ω, ((‖flucAvg d N u z m t ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d))
      = ((∫ ω, ‖flucAvg d N u z m t ω‖ ^ (2 * p) ∂(P d) : ℝ) : ℂ) := integral_complex_ofReal
  have hreal : ∫ ω, ‖flucAvg d N u z m t ω‖ ^ (2 * p) ∂(P d)
      = ‖∫ ω, ((‖flucAvg d N u z m t ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d)‖ := by
    rw [hofR, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun ω => by positivity)]
  rw [hreal]
  exact hbound

/-- **The moment bound for a uniform weight**, the form (4.12) needs.

`E|∑_k t_k Z_k|^{2p} ≤ (2p - 1) ε B^{2p-1} + c^p p^{2p} B^{2p}` for `t_k = c · 1(k ∈ A)` with
`c · #A ≤ 1`.  The second term carries the extra `c^p`: with `c ≤ C W^{-1} ≲ Ψ²` and
`B ≈ N^δ Ψ` it is `≲ (N^δ Ψ²)^{2p}`. -/
theorem integral_norm_flucAvg_pow_le_uniform {B ε c : ℝ} {A : Finset (d.Idx N)}
    (hw : UniformWeight t c A) (hp : p ≤ A.card) (hB : 0 ≤ B) (hε0 : 0 ≤ ε)
    (hZmeas : ∀ k, Measurable (flucDiag d N u z m k))
    (hYmeas : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}),
      Measurable (flucDiagMinor d N u z m κ k))
    (hrow : ∀ k, RowIntegrable d N k (greenDiagCentered d N u z m k))
    (hZB : ∀ k, ∀ ω, ‖flucDiag d N u z m k ω‖ ≤ B)
    (hYB : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}), ∀ ω,
      ‖flucDiagMinor d N u z m κ k ω‖ ≤ B)
    (hεb : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}), ∀ ω,
      ‖flucDiag d N u z m k.1 ω - flucDiagMinor d N u z m κ k ω‖ ≤ ε) :
    ∫ ω, ‖flucAvg d N u z m t ω‖ ^ (2 * p) ∂(P d)
      ≤ ((2 * p - 1 : ℕ) : ℝ) * ε * B ^ (2 * p - 1)
        + c ^ p * (p : ℝ) ^ (2 * p) * B ^ (2 * p) := by
  classical
  have hcardι : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    simp [Fintype.card_sum, two_mul]
  have hmain := integral_norm_flucAvg_pow_le (p := p) (u := u) (z := z) (m := m) (t := t)
    hB hε0 hZmeas hYmeas hrow hZB hYB hεb hw.sum_abs_le
  have hcount : (∑ v ∈ (univ : Finset ((Fin p ⊕ Fin p) → d.Idx N)).filter
        (fun v => ¬ HasLoneSlot v), ∏ i, |t (v i)|) * B ^ (2 * p)
      ≤ c ^ p * (p : ℝ) ^ (2 * p) * B ^ (2 * p) :=
    mul_le_mul_of_nonneg_right
      (sum_prod_not_hasLoneSlot_le (ι := Fin p ⊕ Fin p) hw p hcardι hp) (pow_nonneg hB _)
  linarith

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

