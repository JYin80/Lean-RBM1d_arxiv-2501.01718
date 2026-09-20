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
   (`RBM.Gauss.FinDepOffRow`, T84), and the cost is the replacement error of T85.
2. `E_{k_{i₀}}` then passes through all of them
   (`RBM.Gauss.condRow_mul_of_finDepOffRow'`) and lands on `Z_{k_{i₀}}`, where it gives **zero**
   (`RBM.Gauss.condRow_sub_condRow`, `E_k ∘ (1 - E_k) = 0`).  Combined with the tower property
   `E[E_k X] = E[X]` (`RBM.Gauss.integral_condRow`) this is
   `RBM.Gauss.integral_mul_prod_eq_zero`.
3. The replacement error is estimated term by term by the telescoping bound
   `RBM.Gauss.norm_prod_sub_prod_le`.

## Moment form, not `≺` — and why

The conclusion is stated as an **inequality between real numbers**,
`‖∫ ω, ∏ i, Z i ω ∂P‖ ≤ …`, not as a stochastic domination `≺`.  This is forced:
`E[∏_i Z_{k_i}]` *is* a number, there is no random variable left to dominate.  T87 consumes it
inside the expansion of `E|∑_k t_k Z_k|^{2p}` into `∑_{(k_1,…,k_{2p})} (∏ t) E[∏_i Z_{k_i}]`,
stratified by the number of distinct indices; every summand there is a number of exactly this
shape, and the `≺` is recovered only at the very end of T88 by
`RBM.Gauss.stochDom_of_momentDom` (T73).  Stating T86 as `≺` would force an artificial
random variable and then immediately destroy it again.

## How the product is indexed (what T87 iterates over)

The product runs over an arbitrary `Fintype ι` — for T87, `ι = Fin (2p)` — with a
**distinguished element `i₀ : ι`**, the slot whose index occurs once.  The multi-index itself is
a function `k : ι → RBM.Gauss.Dims.Idx d N`, and "the index `k i₀` occurs exactly once" is the
hypothesis

  `hone : ∀ i, i ≠ i₀ → k i ≠ k i₀`.

The product is `∏ i, Z i ω` over `Finset.univ`, split as
`Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Z i ω` by `Finset.mul_prod_erase`.  Nothing forces the
`Z i` to be *equal* whenever the `k i` are equal, so the abstract layer applies verbatim to
products with conjugated factors as well (T87 needs `Z̄` in half the slots).

## Main results

* `RBM.Gauss.norm_prod_sub_prod_le` — the telescoping product estimate (deterministic).
* `RBM.Gauss.finDepOffRow_prod`, `RBM.Gauss.finDepOffRow_condRow` — the two closure properties
  of `FinDepOffRow` this needs and `RBM1D/Gauss/CondRow.lean` does not have.
* `RBM.Gauss.integral_mul_prod_eq_zero` — **the vanishing itself**: once the other factors are
  independent of row `k`, the expectation is exactly `0`.
* `RBM.Gauss.norm_integral_prod_le` — **the abstract vanishing lemma**.
* `RBM.Gauss.flucDiag`, `RBM.Gauss.flucDiagMinor`, `RBM.Gauss.flucDiagMinorFam` — the concrete
  `Z_k = (1 - E_k)(G_{kk} - m)` and its `G^{(κ)}` replacement.
* `RBM.Gauss.norm_flucDiag_sub_flucDiagMinor_le`,
  `RBM.Gauss.norm_flucDiag_sub_flucDiagMinorFam_le` — the replacement error of a **factor**, in
  terms of the replacement error of a Green function entry: the factor of `2` is the price of
  the `(1 - E_k)`.
* `RBM.Gauss.norm_sub_condRow_le`, `RBM.Gauss.norm_flucDiag_le`,
  `RBM.Gauss.norm_flucDiagMinor_le`, `RBM.Gauss.norm_flucDiagMinorFam_le` — the mirror-image
  statement for the *size* of a factor: a uniform bound `b` on `G_{kk} - m` gives `2 b` on
  `Z_k`.  These three are what T87 feeds into `B`.
* `RBM.Gauss.norm_integral_prod_flucDiag_le` — **the vanishing lemma in the form T87
  consumes**.
* `RBM.Gauss.greenMinorMat_apply_eq_greenMinor` — the bridge from T84's total `greenMinorMat`
  to T85's `RBM.greenMinor`, so that `RBM.Gauss.minorReplace_diag_stochDom` bounds exactly the
  quantity appearing in `norm_flucDiag_sub_flucDiagMinor_le`.

## Hypotheses that are taken rather than proved

Two kinds, both flagged in the statements:

* **Measurability and integrability.**  `RBM1D/Gauss/CondRow.lean` deliberately does not prove
  `Measurable (condRow d N k X)` (see `docs/paper-deltas.md` #56), and there is no
  measurability statement for `ω ↦ green (Hflow d N u ω) z k k` in the repository either.  So
  `Measurable (Z i)` and `RBM.Gauss.RowIntegrable` are hypotheses here.  They are *not* deep:
  for the truncated integrands of T87/T88 they follow from continuity and boundedness
  (`RBM.Gauss.rowIntegrable_of_continuous_of_bound`).
* **The pointwise bounds `B` and `ε`.**  T85 delivers the replacement error as a `≺`, which is
  a statement on a high-probability event and *not* a pointwise bound; converting it into the
  uniform `ε` used here is the indicator/truncation bookkeeping of T87/T88.  Keeping `B` and
  `ε` as parameters is exactly the shape of the ticket
  (`|E[∏]| ≲ (replacement error) × (bound on the remaining factors)`).

## Deviation from the paper

None in substance.  Two bookkeeping choices: the product is indexed by an abstract `Fintype`
with a distinguished element rather than by `1, …, 2p` with `k_1` singled out (the paper's
convention); and the two error parameters are carried explicitly instead of being inlined as
`Ψ²` and `Ψ`.  Both are recorded in `docs/paper-deltas.md`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix Finset

variable {d : Dims} {N : ℕ}

/-! ### Closure properties of `FinDepOffRow`

`RBM1D/Gauss/CondRow.lean` supplies `FinDepOffRow.comp` and `FinDepOffRow.finDep`.  The
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

/-- **The telescoping bound.**  If `‖a i‖, ‖b i‖ ≤ B` on `s`, then

  `‖∏_{i ∈ s} a i - ∏_{i ∈ s} b i‖ ≤ (∑_{i ∈ s} ‖a i - b i‖) · B^(#s - 1)`.

The truncated `#s - 1` is harmless: for `s = ∅` both sides are `0`. -/
theorem norm_prod_sub_prod_le {ι : Type*} {B : ℝ} (hB : 0 ≤ B) (a b : ι → ℂ) :
    ∀ s : Finset ι, (∀ i ∈ s, ‖a i‖ ≤ B) → (∀ i ∈ s, ‖b i‖ ≤ B) →
      ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ (∑ i ∈ s, ‖a i - b i‖) * B ^ (s.card - 1) := by
  classical
  intro s
  induction s using Finset.cons_induction_on with
  | empty => intro _ _; simp
  | cons j t hj ih =>
      intro ha hb
      have haj : ‖a j‖ ≤ B := ha j (Finset.mem_cons_self _ _)
      have hbj : ‖b j‖ ≤ B := hb j (Finset.mem_cons_self _ _)
      have hat : ∀ i ∈ t, ‖a i‖ ≤ B := fun i hi => ha i (Finset.mem_cons_of_mem hi)
      have hbt : ∀ i ∈ t, ‖b i‖ ≤ B := fun i hi => hb i (Finset.mem_cons_of_mem hi)
      have hpa : ‖∏ i ∈ t, a i‖ ≤ B ^ t.card := by
        calc ‖∏ i ∈ t, a i‖ = ∏ i ∈ t, ‖a i‖ := norm_prod _ _
          _ ≤ ∏ _i ∈ t, B := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hat
          _ = B ^ t.card := by rw [Finset.prod_const]
      have hkey : ∏ i ∈ Finset.cons j t hj, a i - ∏ i ∈ Finset.cons j t hj, b i
          = (a j - b j) * ∏ i ∈ t, a i + b j * (∏ i ∈ t, a i - ∏ i ∈ t, b i) := by
        rw [Finset.prod_cons, Finset.prod_cons]; ring
      have hcard : (Finset.cons j t hj).card - 1 = t.card := by
        rw [Finset.card_cons]; omega
      have hsum : (0 : ℝ) ≤ ∑ i ∈ t, ‖a i - b i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      have hstep : B * ((∑ i ∈ t, ‖a i - b i‖) * B ^ (t.card - 1))
          ≤ (∑ i ∈ t, ‖a i - b i‖) * B ^ t.card := by
        rcases Nat.eq_zero_or_pos t.card with h0 | hpos
        · have : t = ∅ := Finset.card_eq_zero.1 h0
          subst this
          simp
        · obtain ⟨c, hc⟩ : ∃ c, t.card = c + 1 := ⟨t.card - 1, by omega⟩
          rw [hc]
          simp only [Nat.add_sub_cancel]
          rw [pow_succ]
          ring_nf
          exact le_of_eq rfl
      rw [hkey, Finset.sum_cons, hcard]
      calc ‖(a j - b j) * ∏ i ∈ t, a i + b j * (∏ i ∈ t, a i - ∏ i ∈ t, b i)‖
          ≤ ‖(a j - b j) * ∏ i ∈ t, a i‖ + ‖b j * (∏ i ∈ t, a i - ∏ i ∈ t, b i)‖ :=
            norm_add_le _ _
        _ = ‖a j - b j‖ * ‖∏ i ∈ t, a i‖ + ‖b j‖ * ‖∏ i ∈ t, a i - ∏ i ∈ t, b i‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ ‖a j - b j‖ * B ^ t.card
              + B * ((∑ i ∈ t, ‖a i - b i‖) * B ^ (t.card - 1)) :=
            add_le_add (mul_le_mul_of_nonneg_left hpa (norm_nonneg _))
              (mul_le_mul hbj (ih hat hbt) (norm_nonneg _) hB)
        _ ≤ ‖a j - b j‖ * B ^ t.card + (∑ i ∈ t, ‖a i - b i‖) * B ^ t.card :=
            by linarith
        _ = (‖a j - b j‖ + ∑ i ∈ t, ‖a i - b i‖) * B ^ t.card := by ring

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

/-- **The vanishing lemma (abstract form).**

Let the product run over `ι` with a distinguished slot `i₀`.  Suppose

* the distinguished factor is a fluctuation: `E_κ[Z i₀] = 0`;
* every other factor `Z i` admits a replacement `Y i` that is strictly independent of row `κ`,
  within `ε` of `Z i` pointwise;
* all the `Z i` and all the `Y i` (`i ≠ i₀`) are bounded by `B` pointwise.

Then

  `‖E[∏_i Z i]‖ ≤ (#ι - 1) · ε · B^(#ι - 1)`.

The right-hand side is exactly "(replacement error) × (bound on the remaining factors)":
`#ι - 1` terms, each costing `ε`, each multiplied by the remaining `#ι - 1` factors. -/
theorem norm_integral_prod_le {κ : d.Idx N} {i₀ : ι} {Z Y : ι → Ω d → ℂ} {B ε : ℝ}
    (hB : 0 ≤ B)
    (hZmeas : ∀ i, Measurable (Z i)) (hYmeas : ∀ i, i ≠ i₀ → Measurable (Y i))
    (hZ0 : condRow d N κ (Z i₀) = 0)
    (hY : ∀ i, i ≠ i₀ → FinDepOffRow d N κ (Y i))
    (hZB : ∀ i, ∀ ω, ‖Z i ω‖ ≤ B) (hYB : ∀ i, i ≠ i₀ → ∀ ω, ‖Y i ω‖ ≤ B)
    (hε : ∀ i, i ≠ i₀ → ∀ ω, ‖Z i ω - Y i ω‖ ≤ ε) :
    ‖∫ ω, ∏ i, Z i ω ∂(P d)‖
      ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) * ε * B ^ (Fintype.card ι - 1) := by
  classical
  set s : Finset ι := Finset.univ.erase i₀ with hs
  have hmem : ∀ {i : ι}, i ∈ s → i ≠ i₀ := fun hi => (Finset.mem_erase.1 hi).1
  have hscard : s.card = Fintype.card ι - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
  -- the two integrands
  have hsplit : ∀ ω : Ω d, ∏ i, Z i ω = Z i₀ ω * ∏ i ∈ s, Z i ω := fun ω =>
    (Finset.mul_prod_erase Finset.univ (fun i => Z i ω) (Finset.mem_univ i₀)).symm
  have hZprod : ∀ ω : Ω d, ‖∏ i ∈ s, Z i ω‖ ≤ B ^ s.card := fun ω => by
    calc ‖∏ i ∈ s, Z i ω‖ = ∏ i ∈ s, ‖Z i ω‖ := norm_prod _ _
      _ ≤ ∏ _i ∈ s, B := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hZB i ω
      _ = B ^ s.card := by rw [Finset.prod_const]
  have hYprod : ∀ ω : Ω d, ‖∏ i ∈ s, Y i ω‖ ≤ B ^ s.card := fun ω => by
    calc ‖∏ i ∈ s, Y i ω‖ = ∏ i ∈ s, ‖Y i ω‖ := norm_prod _ _
      _ ≤ ∏ _i ∈ s, B :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i hi => hYB i (hmem hi) ω
      _ = B ^ s.card := by rw [Finset.prod_const]
  have hmeasZ : Measurable fun ω : Ω d => Z i₀ ω * ∏ i ∈ s, Z i ω :=
    (hZmeas i₀).mul (Finset.measurable_prod s fun i _ => hZmeas i)
  have hmeasY : Measurable fun ω : Ω d => Z i₀ ω * ∏ i ∈ s, Y i ω :=
    (hZmeas i₀).mul (Finset.measurable_prod s fun i hi => hYmeas i (hmem hi))
  have hbZ : ∀ ω : Ω d, ‖Z i₀ ω * ∏ i ∈ s, Z i ω‖ ≤ B * B ^ s.card := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (hZB i₀ ω) (hZprod ω) (norm_nonneg _) hB
  have hbY : ∀ ω : Ω d, ‖Z i₀ ω * ∏ i ∈ s, Y i ω‖ ≤ B * B ^ s.card := fun ω => by
    rw [norm_mul]
    exact mul_le_mul (hZB i₀ ω) (hYprod ω) (norm_nonneg _) hB
  have hintZ : Integrable (fun ω => Z i₀ ω * ∏ i ∈ s, Z i ω) (P d) :=
    integrable_P_of_measurable_of_bound hmeasZ hbZ
  have hintY : Integrable (fun ω => Z i₀ ω * ∏ i ∈ s, Y i ω) (P d) :=
    integrable_P_of_measurable_of_bound hmeasY hbY
  -- the replaced product has zero expectation
  have hzero : ∫ ω, Z i₀ ω * ∏ i ∈ s, Y i ω ∂(P d) = 0 :=
    integral_mul_prod_eq_zero hZ0 (fun i hi => hY i (hmem hi)) hintY
  -- so the whole expectation is the replacement error
  have hrewrite : ∫ ω, ∏ i, Z i ω ∂(P d)
      = ∫ ω, (Z i₀ ω * ∏ i ∈ s, Z i ω - Z i₀ ω * ∏ i ∈ s, Y i ω) ∂(P d) := by
    rw [integral_sub hintZ hintY, hzero, sub_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  -- pointwise bound on the replacement error
  have hpt : ∀ ω : Ω d, ‖Z i₀ ω * ∏ i ∈ s, Z i ω - Z i₀ ω * ∏ i ∈ s, Y i ω‖
      ≤ B * ((s.card : ℝ) * ε * B ^ (s.card - 1)) := by
    intro ω
    have htel : ‖∏ i ∈ s, Z i ω - ∏ i ∈ s, Y i ω‖
        ≤ (∑ i ∈ s, ‖Z i ω - Y i ω‖) * B ^ (s.card - 1) :=
      norm_prod_sub_prod_le hB (fun i => Z i ω) (fun i => Y i ω) s
        (fun i _ => hZB i ω) (fun i hi => hYB i (hmem hi) ω)
    have hsum : (∑ i ∈ s, ‖Z i ω - Y i ω‖) ≤ (s.card : ℝ) * ε := by
      calc (∑ i ∈ s, ‖Z i ω - Y i ω‖) ≤ ∑ _i ∈ s, ε :=
            Finset.sum_le_sum fun i hi => hε i (hmem hi) ω
        _ = (s.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    have hpow : (0 : ℝ) ≤ B ^ (s.card - 1) := pow_nonneg hB _
    calc ‖Z i₀ ω * ∏ i ∈ s, Z i ω - Z i₀ ω * ∏ i ∈ s, Y i ω‖
        = ‖Z i₀ ω‖ * ‖∏ i ∈ s, Z i ω - ∏ i ∈ s, Y i ω‖ := by
          rw [← mul_sub, norm_mul]
      _ ≤ B * ((∑ i ∈ s, ‖Z i ω - Y i ω‖) * B ^ (s.card - 1)) := by
          refine mul_le_mul (hZB i₀ ω) htel (norm_nonneg _) hB
      _ ≤ B * ((s.card : ℝ) * ε * B ^ (s.card - 1)) := by
          have : (∑ i ∈ s, ‖Z i ω - Y i ω‖) * B ^ (s.card - 1)
              ≤ (s.card : ℝ) * ε * B ^ (s.card - 1) := by
            exact mul_le_mul_of_nonneg_right hsum hpow
          exact mul_le_mul_of_nonneg_left this hB
  -- collapse `B * B^(#s - 1)` to `B^#s`
  have hcollapse : B * ((s.card : ℝ) * ε * B ^ (s.card - 1))
      = (s.card : ℝ) * ε * B ^ s.card := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨c, hc⟩ : ∃ c, s.card = c + 1 := ⟨s.card - 1, by omega⟩
      rw [hc]
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
  rw [hrewrite, ← hscard]
  have := norm_integral_le_of_norm_le_const (μ := P d)
    (f := fun ω => Z i₀ ω * ∏ i ∈ s, Z i ω - Z i₀ ω * ∏ i ∈ s, Y i ω)
    (C := B * ((s.card : ℝ) * ε * B ^ (s.card - 1))) (Filter.Eventually.of_forall hpt)
  rw [hcollapse] at this
  simpa using this

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

/-- `E_k[Z_k] = 0` — this is `RBM.Gauss.condRow_sub_condRow`, i.e. `E_k ∘ (1 - E_k) = 0`. -/
theorem condRow_flucDiag (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (hrow : RowIntegrable d N k (greenDiagCentered d N u z m k)) :
    condRow d N k (flucDiag d N u z m k) = 0 :=
  condRow_sub_condRow k hrow

/-- `G^{(κ)}_{kk} - m` is strictly independent of row `κ` (T84's
`finDepOffRow_greenMinorMat_apply`). -/
theorem finDepOffRow_greenMinorDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ)
    (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}) :
    FinDepOffRow d N κ (greenMinorDiagCentered d N u z m κ k) :=
  (finDepOffRow_greenMinorMat_apply d N u z κ k k).comp fun c => c - m

/-- **The replaced factor is strictly independent of row `κ`.**  This is the step that makes
`E_κ` pass through the product: the `(1 - E_k)` in front of `G^{(κ)}_{kk} - m` is a conditional
expectation over a *different* row and does not reintroduce a dependence on row `κ`
(`finDepOffRow_condRow`). -/
theorem finDepOffRow_flucDiagMinor (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (κ : d.Idx N)
    (k : {a : d.Idx N // a ≠ κ}) : FinDepOffRow d N κ (flucDiagMinor d N u z m κ k) :=
  (finDepOffRow_greenMinorDiagCentered d N u z m κ k).sub
    (finDepOffRow_condRow (finDepOffRow_greenMinorDiagCentered d N u z m κ k))

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
so it cannot exceed the uniform bound; the triangle inequality then gives `2 b`.  This is how
T87 turns an entry bound on `G_{kk} - m` into the parameter `B` of the vanishing lemma. -/
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

/-- **Bridge to T85.**  Where the full resolvent exists and `G_{κκ} ≠ 0`, the total function
`greenMinorMat` of T84 is the entry `RBM.greenMinor` that T85's
`RBM.Gauss.minorReplace_diag_stochDom` estimates.  So the hypothesis `he` of
`norm_flucDiag_sub_flucDiagMinor_le` is exactly the quantity T85 dominates by `Ψ²`. -/
theorem greenMinorMat_apply_eq_greenMinor (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (κ : d.Idx N)
    (ω : Ω d) (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGκκ : green (Hflow d N u ω) z κ κ ≠ 0) (a b : {a : d.Idx N // a ≠ κ}) :
    greenMinorMat d N u z κ ω a b = greenMinor (green (Hflow d N u ω) z) κ a.1 b.1 := by
  rw [greenMinorMat_eq_minorGreen d N u z κ ω hdet hGκκ, minorGreen_eq_greenMinor]

/-! ### The vanishing lemma in the form T87 consumes -/

section Concrete

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The family of replaced factors, made total in `i` (the value at the distinguished slot
`i₀` is never read).  T87 iterates over multi-indices `k : ι → d.Idx N`; this is the family
`Z^{(k i₀)}_{k i}`. -/
noncomputable def flucDiagMinorFam (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (i₀ : ι)
    (k : ι → d.Idx N) (hone : ∀ i, i ≠ i₀ → k i ≠ k i₀) (i : ι) : Ω d → ℂ :=
  if h : i = i₀ then 0 else flucDiagMinor d N u z m (k i₀) ⟨k i, hone i h⟩

omit [Fintype ι] in
@[simp] theorem flucDiagMinorFam_of_ne (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) {i₀ : ι}
    {k : ι → d.Idx N} (hone : ∀ i, i ≠ i₀ → k i ≠ k i₀) {i : ι} (h : i ≠ i₀) :
    flucDiagMinorFam d N u z m i₀ k hone i = flucDiagMinor d N u z m (k i₀) ⟨k i, hone i h⟩ :=
  dite_eq_right h

omit [Fintype ι] in
/-- `‖Z^{(k i₀)}_{k i}‖ ≤ 2 b` for the total family, at the slots that matter. -/
theorem norm_flucDiagMinorFam_le (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) {i₀ : ι}
    {k : ι → d.Idx N} (hone : ∀ i, i ≠ i₀ → k i ≠ k i₀) {i : ι} (h : i ≠ i₀) {b : ℝ}
    (hb : ∀ ω, ‖greenMinorDiagCentered d N u z m (k i₀) ⟨k i, hone i h⟩ ω‖ ≤ b) (ω : Ω d) :
    ‖flucDiagMinorFam d N u z m i₀ k hone i ω‖ ≤ 2 * b := by
  rw [flucDiagMinorFam_of_ne d N u z m hone h]
  exact norm_flucDiagMinor_le hb ω

omit [Fintype ι] in
/-- The replacement error at a slot of the total family: `2 e` if the Green function entries
differ by at most `e`.  This is the hypothesis `hε` of `norm_integral_prod_flucDiag_le`. -/
theorem norm_flucDiag_sub_flucDiagMinorFam_le (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) {i₀ : ι}
    {k : ι → d.Idx N} (hone : ∀ i, i ≠ i₀ → k i ≠ k i₀) {i : ι} (h : i ≠ i₀) {e : ℝ}
    (hrow : RowIntegrable d N (k i) (greenDiagCentered d N u z m (k i)))
    (hrow' : RowIntegrable d N (k i)
      (greenMinorDiagCentered d N u z m (k i₀) ⟨k i, hone i h⟩))
    (he : ∀ ω, ‖green (Hflow d N u ω) z (k i) (k i)
      - greenMinorMat d N u z (k i₀) ω ⟨k i, hone i h⟩ ⟨k i, hone i h⟩‖ ≤ e) (ω : Ω d) :
    ‖flucDiag d N u z m (k i) ω - flucDiagMinorFam d N u z m i₀ k hone i ω‖ ≤ 2 * e := by
  rw [flucDiagMinorFam_of_ne d N u z m hone h]
  exact norm_flucDiag_sub_flucDiagMinor_le (k := ⟨k i, hone i h⟩) hrow hrow' he ω

omit [Fintype ι] in
theorem finDepOffRow_flucDiagMinorFam (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) {i₀ : ι}
    {k : ι → d.Idx N} (hone : ∀ i, i ≠ i₀ → k i ≠ k i₀) {i : ι} (h : i ≠ i₀) :
    FinDepOffRow d N (k i₀) (flucDiagMinorFam d N u z m i₀ k hone i) := by
  rw [flucDiagMinorFam_of_ne d N u z m hone h]
  exact finDepOffRow_flucDiagMinor d N u z m (k i₀) ⟨k i, hone i h⟩

/-- **The vanishing lemma of T86.**

Let `Z_k = (1 - E_k)(G_{kk} - m)` and let `k : ι → Idx` be a multi-index in which the value
`k i₀` occurs **exactly once** (`hone`).  If every factor and every replaced factor is bounded
by `B`, and every replacement `Z_{k i} ↦ Z^{(k i₀)}_{k i}` (`i ≠ i₀`) costs at most `ε`, then

  `‖E[∏_i Z_{k i}]‖ ≤ (#ι - 1) · ε · B^(#ι - 1)`.

Without the replacement the expectation is *not* small — the point of `hone` is that after the
replacement `E_{k i₀}` sees a product of factors that do not read row `k i₀` times `Z_{k i₀}`,
whose `E_{k i₀}` is `0`. -/
theorem norm_integral_prod_flucDiag_le {i₀ : ι} {k : ι → d.Idx N}
    (hone : ∀ i, i ≠ i₀ → k i ≠ k i₀) (u : ℝ) (z m : ℂ) {B ε : ℝ} (hB : 0 ≤ B)
    (hZmeas : ∀ i, Measurable (flucDiag d N u z m (k i)))
    (hYmeas : ∀ i, i ≠ i₀ → Measurable (flucDiagMinorFam d N u z m i₀ k hone i))
    (hrow : RowIntegrable d N (k i₀) (greenDiagCentered d N u z m (k i₀)))
    (hZB : ∀ i, ∀ ω, ‖flucDiag d N u z m (k i) ω‖ ≤ B)
    (hYB : ∀ i, i ≠ i₀ → ∀ ω, ‖flucDiagMinorFam d N u z m i₀ k hone i ω‖ ≤ B)
    (hε : ∀ i, i ≠ i₀ → ∀ ω,
      ‖flucDiag d N u z m (k i) ω - flucDiagMinorFam d N u z m i₀ k hone i ω‖ ≤ ε) :
    ‖∫ ω, ∏ i, flucDiag d N u z m (k i) ω ∂(P d)‖
      ≤ ((Fintype.card ι - 1 : ℕ) : ℝ) * ε * B ^ (Fintype.card ι - 1) :=
  norm_integral_prod_le (κ := k i₀) (i₀ := i₀)
    (Z := fun i => flucDiag d N u z m (k i))
    (Y := flucDiagMinorFam d N u z m i₀ k hone)
    hB hZmeas hYmeas (condRow_flucDiag u z m (k i₀) hrow)
    (fun _ h => finDepOffRow_flucDiagMinorFam d N u z m hone h) hZB hYB hε

end Concrete

end RBM.Gauss
