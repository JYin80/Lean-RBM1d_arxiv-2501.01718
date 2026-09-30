/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondRow
import RBM1D.Gauss.MinorReplace

/-!
# The vanishing lemma: an index occurring **once** makes the expectation an error term

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*: the first half of the self-contained proof of the fluctuation averaging (4.12).

Write `Z_k := (1 - E_k)(G_{kk} - m)`.  If in a product `Z_{k_1} ⋯ Z_{k_n}` some index — say
`k_{i₀}` — occurs **exactly once**, then `E[∏_i Z_{k_i}]` is not merely small, it is *pure
replacement error*:

  `|E[∏_i Z_{k_i}]| ≤ (n - 1) · ε · B^(n-1)`,

where `B` bounds every factor and `ε` bounds the error of replacing a factor `Z_{k_i}`
(`i ≠ i₀`) by the one built from the minor `G^{(k_{i₀})}`.

## The argument, and where each step lives

1. Replace each factor `Z_{k_i}`, `i ≠ i₀`, by `Z^{(k_{i₀})}_{k_i}`, built from `G^{(k_{i₀})}`.
   After the replacement those factors are **strictly independent of row `k_{i₀}`**
   (`RBM.Gauss.FinDepOffRow`), and the cost is the replacement error of
   `RBM1D/Gauss/MinorReplace.lean`.
2. `E_{k_{i₀}}` then passes through all of them
   (`RBM.Gauss.condRow_mul_of_finDepOffRow'`) and lands on `Z_{k_{i₀}}`, where it gives **zero**
   (`RBM.Gauss.condRow_sub_condRow`, `E_k ∘ (1 - E_k) = 0`).  Combined with the tower property
   `E[E_k X] = E[X]` (`RBM.Gauss.integral_condRow`) this is
   `RBM.Gauss.integral_mul_prod_eq_zero`.
3. The replacement error is estimated term by term by a telescoping bound: replacing every
   factor of a product by a nearby one costs the sum of the individual replacement errors, times
   one power of the uniform bound less.

## Moment form, not `≺` — and why

The conclusion is stated as an **inequality between real numbers**,
`‖∫ ω, ∏ i, Z i ω ∂P‖ ≤ …`, not as a stochastic domination `≺`.  This is forced:
`E[∏_i Z_{k_i}]` *is* a number, there is no random variable left to dominate.
`RBM1D/Gauss/FlucCount.lean` consumes it inside the expansion of `E|∑_k t_k Z_k|^{2p}` into
`∑_{(k_1,…,k_{2p})} (∏ t) E[∏_i Z_{k_i}]`, stratified by the number of distinct indices; every
summand there is a number of exactly this shape, and the `≺` is recovered only at the very end
(`RBM1D/Gauss/FlucAvg.lean`) by `RBM.Gauss.stochDom_of_momentDom`.

## How the product is indexed

The product runs over an arbitrary `Fintype ι` — in `RBM1D/Gauss/FlucCount.lean`,
`ι = Fin (2p)` — with a
**distinguished element `i₀ : ι`**, the slot whose index occurs once.  The multi-index itself is
a function `k : ι → RBM.Gauss.Dims.Idx d N`, and "the index `k i₀` occurs exactly once" is the
hypothesis

  `hone : ∀ i, i ≠ i₀ → k i ≠ k i₀`.

The product is `∏ i, Z i ω` over `Finset.univ`, split as
`Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Z i ω` by `Finset.mul_prod_erase`.  Nothing forces the
`Z i` to be *equal* whenever the `k i` are equal, so the abstract layer applies verbatim to
products with conjugated factors as well (the moment expansion needs `Z̄` in half the slots).

## Main results

* `RBM.Gauss.finDepOffRow_prod`, `RBM.Gauss.finDepOffRow_condRow` — the two closure properties
  of `FinDepOffRow` this needs and `RBM1D/Gauss/CondRow.lean` does not have.
* `RBM.Gauss.integral_mul_prod_eq_zero` — **the vanishing itself**: once the other factors are
  independent of row `k`, the expectation is exactly `0`.
* `RBM.Gauss.flucDiag`, `RBM.Gauss.flucDiagMinor` — the concrete
  `Z_k = (1 - E_k)(G_{kk} - m)` and its `G^{(κ)}` replacement.
* `RBM.Gauss.norm_flucDiag_sub_flucDiagMinor_le` — the replacement error of a **factor**, in
  terms of the replacement error of a Green function entry: the factor of `2` is the price of
  the `(1 - E_k)`.
* `RBM.Gauss.norm_sub_condRow_le`, `RBM.Gauss.norm_flucDiag_le`,
  `RBM.Gauss.norm_flucDiagMinor_le` — the mirror-image statement for the *size* of a factor: a
  uniform bound `b` on `G_{kk} - m` gives `2 b` on `Z_k`.

## Hypotheses that are taken rather than proved

Two kinds, both flagged in the statements:

* **Measurability and integrability.**  `Measurable (Z i)` and `RBM.Gauss.RowIntegrable` are
  hypotheses here; they are proved in `RBM1D/Gauss/FlucAvg.lean`
  (`RBM.Gauss.measurable_green_apply`, `RBM.Gauss.measurable_condRow`) and follow from
  measurability and boundedness (`RBM.Gauss.rowIntegrable_of_measurable_of_bound`).
* **The pointwise bounds `B` and `ε`.**  `RBM1D/Gauss/MinorReplace.lean` gives the replacement
  error as a `≺`, which is a statement on a high-probability event and *not* a pointwise bound;
  `B` and `ε` are therefore parameters, in the shape
  `|E[∏]| ≲ (replacement error) × (bound on the remaining factors)`.

## Deviation from the paper

None in substance.  Two bookkeeping choices: the product is indexed by an abstract `Fintype`
with a distinguished element rather than by `1, …, 2p` with `k_1` singled out (the paper's
convention); and the two error parameters are carried explicitly instead of being inlined as
`Ψ²` and `Ψ`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix Finset

variable {d : Dims} {N : ℕ}

/-! ### Closure properties of `FinDepOffRow`

`RBM1D/Gauss/CondRow.lean` supplies `FinDepOffRow.comp`.  The
vanishing lemma needs two more: the family of replaced factors must be closed under finite
products, and each replaced factor itself carries a `condRow` (the `(1 - E_{k_i})` in
`Z^{(κ)}_{k_i}`), which must not destroy independence of row `κ`. -/

theorem finDepOffRow_const (k : d.Idx N) {V : Type*} (v : V) :
    FinDepOffRow d N k (fun _ : Ω d => v) :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem FinDepOffRow.mul {k : d.Idx N} {X Y : Ω d → ℂ} (hX : FinDepOffRow d N k X)
    (hY : FinDepOffRow d N k Y) : FinDepOffRow d N k fun ω => X ω * Y ω := by
  classical
  obtain ⟨I, hI, hX'⟩ := hX
  obtain ⟨J, hJ, hY'⟩ := hY
  refine ⟨I ∪ J, ?_, fun ω ω' hω => ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact hI c h
    · exact hJ c h
  · show X ω * Y ω = X ω' * Y ω'
    rw [hX' ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
      hY' ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

theorem FinDepOffRow.sub {k : d.Idx N} {X Y : Ω d → ℂ} (hX : FinDepOffRow d N k X)
    (hY : FinDepOffRow d N k Y) : FinDepOffRow d N k fun ω => X ω - Y ω := by
  classical
  obtain ⟨I, hI, hX'⟩ := hX
  obtain ⟨J, hJ, hY'⟩ := hY
  refine ⟨I ∪ J, ?_, fun ω ω' hω => ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact hI c h
    · exact hJ c h
  · show X ω - Y ω = X ω' - Y ω'
    rw [hX' ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
      hY' ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

/-- **A finite product of factors independent of row `k` is independent of row `k`.**  This is
what lets `E_k` be pulled through *all* the replaced factors at once. -/
theorem finDepOffRow_prod {k : d.Idx N} {ι : Type*} (s : Finset ι) {f : ι → Ω d → ℂ}
    (hf : ∀ i ∈ s, FinDepOffRow d N k (f i)) :
    FinDepOffRow d N k fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simpa using finDepOffRow_const k (1 : ℂ)
  | cons j t hj ih =>
      have hjf : FinDepOffRow d N k (f j) := hf j (Finset.mem_cons_self _ _)
      have ht : FinDepOffRow d N k fun ω => ∏ i ∈ t, f i ω :=
        ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
      have := hjf.mul ht
      simpa only [Finset.prod_cons] using this

/-- **`E_{k'}` preserves independence of row `k`.**  A factor `Z^{(κ)}_{k_i} =
(1 - E_{k_i})(G^{(κ)}_{k_i k_i} - m)` carries a conditional expectation over a *different* row
`k_i`; this lemma says that this does not reintroduce a dependence on row `κ`. -/
theorem finDepOffRow_condRow {k k' : d.Idx N} {X : Ω d → ℂ} (h : FinDepOffRow d N k X) :
    FinDepOffRow d N k (condRow d N k' X) := by
  classical
  obtain ⟨I, hI, hX⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord d N k' c, fun c hc => hI c (Finset.mem_filter.1 hc).1,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hX _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord d N k' c
  · rw [rowSplit_apply_of_isRowCoord k' ω ω'' hcr, rowSplit_apply_of_isRowCoord k' ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k' ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k' ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

/-! ### The telescoping product estimate

Purely deterministic: replacing every factor of a product by a nearby one costs the sum of the
individual replacement errors, times one power of the uniform bound less. -/

/-! ### Integrability from measurability and a uniform bound

`P d` is a probability measure, so a bounded measurable function is integrable. -/

/-- A bounded measurable function on the Gaussian product space is integrable. -/
theorem integrable_P_of_measurable_of_bound {f : Ω d → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (P d) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-! ### The vanishing lemma, abstract form -/

section Vanish

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The vanishing itself.**  If every factor other than the distinguished one is strictly
independent of row `κ`, and the distinguished factor is killed by `E_κ`, then the expectation
of the product is exactly `0`.

This is the whole point of the argument: `E_κ` passes through the independent factors
(`condRow_mul_of_finDepOffRow'`) and annihilates `Z_{i₀}` (`condRow_sub_condRow`, supplied here
as `hZ0`); the tower property `integral_condRow` then converts `E_κ[·] = 0` into `E[·] = 0`. -/
theorem integral_mul_prod_eq_zero {κ : d.Idx N} {i₀ : ι} {Z Y : ι → Ω d → ℂ}
    (hZ0 : condRow d N κ (Z i₀) = 0)
    (hY : ∀ i ∈ Finset.univ.erase i₀, FinDepOffRow d N κ (Y i))
    (hint : Integrable (fun ω => Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Y i ω) (P d)) :
    ∫ ω, Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Y i ω ∂(P d) = 0 := by
  have hprod : FinDepOffRow d N κ fun ω => ∏ i ∈ Finset.univ.erase i₀, Y i ω :=
    finDepOffRow_prod _ hY
  have hpull := condRow_mul_of_finDepOffRow' (X := Z i₀)
    (Y := fun ω => ∏ i ∈ Finset.univ.erase i₀, Y i ω) hprod
  rw [← integral_condRow κ hint, hpull]
  simp [hZ0]

end Vanish

/-! ### The concrete fluctuation `Z_k = (1 - E_k)(G_{kk} - m)` -/

/-- The centred diagonal Green function entry, `G_{kk} - m`. -/
noncomputable def greenDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) :
    Ω d → ℂ := fun ω => green (Hflow d N u ω) z k k - m

/-- **`Z_k := (1 - E_k)(G_{kk} - m)`**, the fluctuation of §4. -/
noncomputable def flucDiag (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) : Ω d → ℂ :=
  fun ω => greenDiagCentered d N u z m k ω - condRow d N k (greenDiagCentered d N u z m k) ω

/-- The centred diagonal entry of the **minor** resolvent, `G^{(κ)}_{kk} - m`. -/
noncomputable def greenMinorDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (κ : d.Idx N)
    (k : {a : d.Idx N // a ≠ κ}) : Ω d → ℂ :=
  fun ω => greenMinorMat d N u z κ ω k k - m

/-- **`Z^{(κ)}_k := (1 - E_k)(G^{(κ)}_{kk} - m)`**, the replaced fluctuation. -/
noncomputable def flucDiagMinor (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (κ : d.Idx N)
    (k : {a : d.Idx N // a ≠ κ}) : Ω d → ℂ :=
  fun ω => greenMinorDiagCentered d N u z m κ k ω
    - condRow d N k.1 (greenMinorDiagCentered d N u z m κ k) ω

/-- **The replacement error of a factor**, in terms of the replacement error of the Green
function entry.  The factor `2` is the price of the `(1 - E_k)`: the error is transported
unchanged through the identity part and, being uniform, survives the integration in `E_k`. -/
theorem norm_flucDiag_sub_flucDiagMinor_le {u : ℝ} {z m : ℂ} {κ : d.Idx N}
    {k : {a : d.Idx N // a ≠ κ}} {e : ℝ}
    (hrow : RowIntegrable d N k.1 (greenDiagCentered d N u z m k.1))
    (hrow' : RowIntegrable d N k.1 (greenMinorDiagCentered d N u z m κ k))
    (he : ∀ ω, ‖green (Hflow d N u ω) z k.1 k.1 - greenMinorMat d N u z κ ω k k‖ ≤ e)
    (ω : Ω d) :
    ‖flucDiag d N u z m k.1 ω - flucDiagMinor d N u z m κ k ω‖ ≤ 2 * e := by
  have hD : ∀ ω' : Ω d, greenDiagCentered d N u z m k.1 ω'
      - greenMinorDiagCentered d N u z m κ k ω'
      = green (Hflow d N u ω') z k.1 k.1 - greenMinorMat d N u z κ ω' k k := by
    intro ω'
    simp only [greenDiagCentered, greenMinorDiagCentered]
    ring
  have hcond := condRow_sub k.1 hrow hrow'
  have hcondpt : condRow d N k.1 (greenDiagCentered d N u z m k.1) ω
      - condRow d N k.1 (greenMinorDiagCentered d N u z m κ k) ω
      = condRow d N k.1 (fun ω' => green (Hflow d N u ω') z k.1 k.1
          - greenMinorMat d N u z κ ω' k k) ω := by
    have := congrFun hcond ω
    rw [← this]
    simp only [condRow_apply, hD]
  have hbound : ‖condRow d N k.1 (fun ω' => green (Hflow d N u ω') z k.1 k.1
      - greenMinorMat d N u z κ ω' k k) ω‖ ≤ e := by
    rw [condRow_apply]
    have := norm_integral_le_of_norm_le_const (μ := P d)
      (f := fun ω' => green (Hflow d N u (rowSplit d N k.1 ω ω')) z k.1 k.1
        - greenMinorMat d N u z κ (rowSplit d N k.1 ω ω') k k)
      (C := e) (Filter.Eventually.of_forall fun ω' => he _)
    simpa using this
  have hsplit : flucDiag d N u z m k.1 ω - flucDiagMinor d N u z m κ k ω
      = (green (Hflow d N u ω) z k.1 k.1 - greenMinorMat d N u z κ ω k k)
        - condRow d N k.1 (fun ω' => green (Hflow d N u ω') z k.1 k.1
            - greenMinorMat d N u z κ ω' k k) ω := by
    rw [← hcondpt, ← hD ω]
    simp only [flucDiag, flucDiagMinor]
    ring
  rw [hsplit]
  calc ‖(green (Hflow d N u ω) z k.1 k.1 - greenMinorMat d N u z κ ω k k)
        - condRow d N k.1 (fun ω' => green (Hflow d N u ω') z k.1 k.1
            - greenMinorMat d N u z κ ω' k k) ω‖
      ≤ ‖green (Hflow d N u ω) z k.1 k.1 - greenMinorMat d N u z κ ω k k‖
        + ‖condRow d N k.1 (fun ω' => green (Hflow d N u ω') z k.1 k.1
            - greenMinorMat d N u z κ ω' k k) ω‖ := norm_sub_le _ _
    _ ≤ e + e := add_le_add (he ω) hbound
    _ = 2 * e := by ring

/-- **A uniform bound survives `(1 - E_k)`, at the cost of a factor `2`.**  `E_k` is an average,
so it cannot exceed the uniform bound; the triangle inequality then gives `2 b`.  This turns an
entry bound on `G_{kk} - m` into the parameter `B` of the vanishing lemma. -/
theorem norm_sub_condRow_le {k : d.Idx N} {X : Ω d → ℂ} {b : ℝ} (hX : ∀ ω, ‖X ω‖ ≤ b)
    (ω : Ω d) : ‖X ω - condRow d N k X ω‖ ≤ 2 * b := by
  have h1 : ‖condRow d N k X ω‖ ≤ b := by
    rw [condRow_apply]
    simpa using norm_integral_le_of_norm_le_const (μ := P d)
      (f := fun ω' => X (rowSplit d N k ω ω')) (C := b)
      (Filter.Eventually.of_forall fun ω' => hX _)
  calc ‖X ω - condRow d N k X ω‖ ≤ ‖X ω‖ + ‖condRow d N k X ω‖ := norm_sub_le _ _
    _ ≤ b + b := add_le_add (hX ω) h1
    _ = 2 * b := by ring

/-- `‖Z_k‖ ≤ 2 b` as soon as `‖G_{kk} - m‖ ≤ b` uniformly. -/
theorem norm_flucDiag_le {u : ℝ} {z m : ℂ} {k : d.Idx N} {b : ℝ}
    (hb : ∀ ω, ‖greenDiagCentered d N u z m k ω‖ ≤ b) (ω : Ω d) :
    ‖flucDiag d N u z m k ω‖ ≤ 2 * b :=
  norm_sub_condRow_le hb ω

/-- `‖Z^{(κ)}_k‖ ≤ 2 b` as soon as `‖G^{(κ)}_{kk} - m‖ ≤ b` uniformly. -/
theorem norm_flucDiagMinor_le {u : ℝ} {z m : ℂ} {κ : d.Idx N} {k : {a : d.Idx N // a ≠ κ}}
    {b : ℝ} (hb : ∀ ω, ‖greenMinorDiagCentered d N u z m κ k ω‖ ≤ b) (ω : Ω d) :
    ‖flucDiagMinor d N u z m κ k ω‖ ≤ 2 * b :=
  norm_sub_condRow_le hb ω

/-! ### The vanishing lemma in the form of the moment expansion -/

section Concrete

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end Concrete

end RBM.Gauss
