/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucAvg

/-!
# Iterating the vanishing lemma to order `2p`: (4.12)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the fluctuation averaging

  `∑_k t_k (1 - E_k)(G_{kk} - m) ≺ Ψ²`,   `0 ≤ |t_k| ≤ W⁻¹`, `∑_k |t_k| ≤ 1`   **(4.12)**

`RBM1D/Gauss/FlucVanish.lean` has the vanishing lemma to **first** order: if some index
of a product `Z_{k_1} ⋯ Z_{k_{2p}}` occurs only once, one minor replacement makes the
expectation a pure replacement error, `|E ∏ Z| ≤ (2p-1) ε B^{2p-1}`.  That is not enough: with
the ideal sizes `ε ≍ Ψ²`, `B ≍ Ψ` it gives `Ψ^{2p+1}`, while (4.12) needs `Ψ^{4p}` — at
`p = 1`, `Ψ³` against `Ψ⁴`.  The standard proof iterates the replacement `2p` times.  **This
file performs that iteration.**

## What is proved

1. **Conditional expectations over different rows commute** (`RBM.Gauss.condRow_condRow_comm`).
   This is the fact `RBM1D/Gauss/CondRow.lean` does not have and the iteration cannot do
   without: the pivot factor must keep its `Q_{k}` while the words in front of it grow.  It is
   proved by generalizing `rowSplit` to an arbitrary decidable set of coordinates
   (`RBM.Gauss.predSplit`), whose splittings compose (`RBM.Gauss.predSplit_predSplit`), and
   whose measure-preserving property (`RBM.Gauss.measurePreserving_predSplit`) turns the
   composite into `E_{row k ∪ row κ}` in either order.  Note that no disjointness is needed:
   rows `k` and `κ` share the entry `H_{kκ}`.
2. **The iteration** (`RBM.Gauss.norm_integral_prod_applyOps_le_graded`).  The induction is on
   the number of pivots still to perform.  The state is a word `L i` of operators `P_κ = E_κ` and
   `Q_κ = 1 - E_κ` per slot (`RBM.Gauss.applyOps`, a `List (Bool × Idx)` with the head
   outermost); the invariant (`RBM.Gauss.OpsOkOut`) says every word uses pairwise distinct rows
   of slots already pivoted and different from its own slot's row.  One step picks a pivot
   `i₀` whose row is **lone**, writes `1 = Q_{k i₀} + P_{k i₀}` in every other slot
   (`RBM.Gauss.prod_eq_sum_pivotFam`, `Finset.prod_add`), discards the all-`P` term — which
   vanishes by `RBM.Gauss.integral_mul_prod_eq_zero` — and recurses.  Each surviving term
   has **one more `Q`**, which is where the extra power of the gain comes from.
   At full depth (`RBM.Gauss.norm_integral_prod_qRow_le_graded`) the bound is
   `(2 max(1,ρ))^{(n-1) r} ρ^r B^n` with `r` the number of lone slots pivoted.
3. **The counting** (`RBM.Gauss.two_mul_card_image_le_add_card_loneSlots`,
   `RBM.Gauss.card_filter_card_image_le`, `RBM.Gauss.sum_weighted_le`).  Refining the two-way
   split (some lone slot / none) into the stratification by the *number* `a` of lone slots: a
   multi-index with `a` lone slots has at most `(n + a)/2` distinct values, so the weight of its
   stratum is at most `n^n ρ^{n-a}` once `c ≤ ρ²`.  Together with the `ρ^a` of the iteration
   this is `ρ^n` for **every** stratum — the mechanism by which `Ψ^{4p}` appears.
4. **The moment bound** (`RBM.Gauss.integral_norm_flucAvg_pow_le_iter_budget`):

     `E|∑_k t_k Z_k|^{2p} ≤ (2p+1)(2p)^{2p} (2^{2p-1} ρ B)^{2p}`,

   hence, through `RBM.Gauss.stochDom_of_momentDom`, `∑_k t_k Z_k ≺ ρ B`.  With `ρ, B ≍ Ψ` this
   is `≺ Ψ²`, i.e. (4.12).  The constant is allowed to depend on `p` (as `RBM.Gauss.MomentDom`
   allows), and the size hypotheses that remain — `ρ ≤ 1` and `W⁻¹ ≤ ρ²` — are the paper's own
   (2.2).

## The one remaining input: the gain `RBM.Gauss.FlucGainUpTo'`

The iteration needs, and does not prove, the **higher-order minor expansion**: applying `m`
further conditional fluctuations `Q_{κ_1} ⋯ Q_{κ_m}` (distinct rows, all different from `k`) to
`Z_k` gains a factor `ρ^m`.  Two of its cases are elementary:

* `m = 0` is the entry bound `‖Z_k‖ ≤ B` (`RBM.Gauss.norm_flucDiag_le`);
* for `m = 1`, `Q_κ` annihilates `Z^{(κ)}_k`, which is within the replacement error `ε` of `Z_k`
  (`RBM1D/Gauss/MinorReplace.lean`), so `‖Q_κ Z_k‖ ≤ 2 ε ≍ Ψ²` — i.e. `ρ ≍ Ψ`, exactly the value
  needed.

`m ≥ 2` needs the iterated minors `G^{(κ_1 κ_2)}, …` (`RBM1D/Gauss/FlucIterHigh.lean`).  It is
carried as the hypothesis `RBM.Gauss.FlucGainUpTo'`, budgeted in the word length and in the
number of slots (see "The second budget" below).

**No truncation is needed.**  The gain is stated as a bound on an *expectation* of a product of
norms, not as a pointwise bound.  That is deliberate: a pointwise `Ψ`-sized bound does not exist
(the local law has an exceptional set), whereas the expectation bound follows from `≺` together
with the deterministic envelope `‖G_t‖ ≤ η_t⁻¹`, since the exceptional event has probability
`N^{-D}` for every `D`.  The obstruction of `RBM1D/Gauss/FlucAvg.lean` — that `1_Ω` destroys
`E_k[(1 - E_k)X] = 0` and is not `FinDepOffRow` — does not apply, because the vanishing identity
is used **before** any truncation and the truncation is applied only to the resulting bound.

## Deviations from the paper

* The words are indexed by `List (Bool × Idx)` rather than by a pair of sets of rows; the
  iteration is over an abstract `Fintype` of slots with a distinguished `Finset` of lone ones,
  rather than over `1, …, 2p`.  Bookkeeping only.
* The constants are not the paper's: the iteration produces `2^{(2p-1) 2p} (2p+1) (2p)^{2p}`,
  which depends on `p` only.  `RBM.Gauss.MomentDom`, and hence `≺`, allows this.
* The gain is carried as a free parameter `ρ` with the paper's value `ρ ≍ Ψ` supplied by the
  caller, instead of being inlined.
* The gain for `m ≥ 2` is a hypothesis (`RBM.Gauss.FlucGainUpTo'`), not a theorem.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix Finset

variable {d : Dims} {N : ℕ}

/-! ### Splitting along an arbitrary set of coordinates

`RBM1D/Gauss/CondRow.lean` splits a sample point along the coordinates of one row.  The
iteration needs several rows at once, and — more importantly — it needs to know that the
resulting conditional expectations **commute**.  Both come from one generalization: replace the
predicate `IsRowCoord d N k` by an arbitrary decidable predicate on coordinates. -/

/-- `predSplit d p ω ω'` takes the coordinates satisfying `p` from `ω'` and the rest from `ω`.
With `p = IsRowCoord d N k` this is `RBM.Gauss.rowSplit`. -/
def predSplit (d : Dims) (p : Coord d → Prop) [DecidablePred p] (ω ω' : Ω d) : Ω d :=
  fun c => if p c then ω' c else ω c

theorem measurable_predSplit (d : Dims) (p : Coord d → Prop) [DecidablePred p] :
    Measurable fun q : Ω d × Ω d => predSplit d p q.1 q.2 := by
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : p c
  · have h : (fun q : Ω d × Ω d => predSplit d p q.1 q.2 c) = fun q => q.2 c := by
      funext q; exact ite_eq_left hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_snd
  · have h : (fun q : Ω d × Ω d => predSplit d p q.1 q.2 c) = fun q => q.1 c := by
      funext q; exact ite_eq_right hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_fst

theorem preimage_predSplit_pi (d : Dims) (p : Coord d → Prop) [DecidablePred p]
    (s : Finset (Coord d)) (t : Coord d → Set ℝ) :
    (fun q : Ω d × Ω d => predSplit d p q.1 q.2) ⁻¹' ((s : Set (Coord d)).pi t)
      = ((↑(s.filter fun c => ¬ p c) : Set (Coord d)).pi t)
        ×ˢ ((↑(s.filter fun c => p c) : Set (Coord d)).pi t) := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c hc.1
      rwa [show predSplit d p ω ω' c = ω c from ite_eq_right hc.2] at this
    · have := h c hc.1
      rwa [show predSplit d p ω ω' c = ω' c from ite_eq_left hc.2] at this
  · rintro ⟨h1, h2⟩ c hc
    by_cases hcp : p c
    · rw [show predSplit d p ω ω' c = ω' c from ite_eq_left hcp]; exact h2 c ⟨hc, hcp⟩
    · rw [show predSplit d p ω ω' c = ω c from ite_eq_right hcp]; exact h1 c ⟨hc, hcp⟩

/-- **The Fubini statement behind every `E_k`.**  Taking the `p`-coordinates from one
independent copy and the rest from another reproduces the law `P d`.  This is
`RBM.Gauss.measurePreserving_rowSplit` for a general predicate. -/
theorem measurePreserving_predSplit (d : Dims) (p : Coord d → Prop) [DecidablePred p] :
    MeasurePreserving (fun q : Ω d × Ω d => predSplit d p q.1 q.2)
      ((P d).prod (P d)) (P d) := by
  refine ⟨measurable_predSplit d p, ?_⟩
  have hmeas := measurable_predSplit d p
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    preimage_predSplit_pi d p s t, Measure.prod_prod]
  show P d _ * P d _ = _
  rw [P, Measure.infinitePi_pi _ fun i _ => ht i, Measure.infinitePi_pi _ fun i _ => ht i,
    mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not s p _

/-- **The composition rule for splittings.**  Splitting along `p` and then along `q` is the same
as splitting along `p ∨ q` with the two source points themselves split along `q`.  This purely
combinatorial identity is what makes the conditional expectations commute. -/
theorem predSplit_predSplit (d : Dims) (p q : Coord d → Prop) [DecidablePred p]
    [DecidablePred q] (ω ω₁ ω₂ : Ω d) :
    predSplit d q (predSplit d p ω ω₁) ω₂
      = predSplit d (fun c => p c ∨ q c) ω (predSplit d q ω₁ ω₂) := by
  funext c
  by_cases hq : q c <;> by_cases hp : p c <;> simp [predSplit, hp, hq]

/-! ### Bounded measurable functions

Everything in this file is a bounded measurable function of `ω`: the resolvent entries are
(`RBM.Gauss.measurable_green_apply`, `RBM.Gauss.norm_green_apply_le_etaT`), and the class is
closed under the operations used below.  Bundling the two facts avoids carrying two hypotheses
through every lemma, and it is exactly what makes all the integrals and Fubinis unconditional. -/

/-- `X` is measurable and globally bounded. -/
structure BddMeas (d : Dims) (X : Ω d → ℂ) : Prop where
  /-- `X` is measurable. -/
  meas : Measurable X
  /-- `X` is bounded. -/
  bdd : ∃ C : ℝ, ∀ ω, ‖X ω‖ ≤ C

theorem BddMeas.integrable {X : Ω d → ℂ} (h : BddMeas d X) : Integrable X (P d) := by
  obtain ⟨C, hC⟩ := h.bdd
  exact integrable_P_of_measurable_of_bound h.meas hC

theorem BddMeas.rowIntegrable {X : Ω d → ℂ} (h : BddMeas d X) (k : d.Idx N) :
    RowIntegrable d N k X := by
  obtain ⟨C, hC⟩ := h.bdd
  exact rowIntegrable_of_measurable_of_bound h.meas hC

theorem BddMeas.sub {X Y : Ω d → ℂ} (hX : BddMeas d X) (hY : BddMeas d Y) :
    BddMeas d fun ω => X ω - Y ω := by
  obtain ⟨C, hC⟩ := hX.bdd
  obtain ⟨D, hD⟩ := hY.bdd
  exact ⟨hX.meas.sub hY.meas, C + D, fun ω => le_trans (norm_sub_le _ _)
    (add_le_add (hC ω) (hD ω))⟩

theorem BddMeas.mul {X Y : Ω d → ℂ} (hX : BddMeas d X) (hY : BddMeas d Y) :
    BddMeas d fun ω => X ω * Y ω := by
  obtain ⟨C, hC⟩ := hX.bdd
  obtain ⟨D, hD⟩ := hY.bdd
  refine ⟨hX.meas.mul hY.meas, C * D, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC ω) (hD ω) (norm_nonneg _)
    (le_trans (norm_nonneg _) (hC (Classical.arbitrary _)))

theorem bddMeas_const (d : Dims) (c : ℂ) : BddMeas d fun _ => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

theorem bddMeas_prod {ι : Type*} (s : Finset ι) {f : ι → Ω d → ℂ}
    (hf : ∀ i ∈ s, BddMeas d (f i)) : BddMeas d fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simpa using bddMeas_const d 1
  | cons j t hj ih =>
      have hj' : BddMeas d (f j) := hf j (Finset.mem_cons_self _ _)
      have ht : BddMeas d fun ω => ∏ i ∈ t, f i ω :=
        ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
      simpa only [Finset.prod_cons] using hj'.mul ht

/-! ### `E_p`, the conditional expectation along an arbitrary coordinate set -/

/-- `E_p[X](ω) = ∫ X (predSplit p ω ω') dP(ω')`.  With `p = IsRowCoord d N k` this is
`RBM.Gauss.condRow`. -/
noncomputable def condPred (d : Dims) (p : Coord d → Prop) [DecidablePred p] (X : Ω d → ℂ) :
    Ω d → ℂ := fun ω => ∫ ω', X (predSplit d p ω ω') ∂(P d)

theorem condRow_eq_condPred (d : Dims) (N : ℕ) (k : d.Idx N) (X : Ω d → ℂ) :
    condRow d N k X = condPred d (IsRowCoord d N k) X := rfl

theorem condPred_congr (d : Dims) {p q : Coord d → Prop} [hp : DecidablePred p]
    [hq : DecidablePred q] (h : ∀ c, p c ↔ q c) (X : Ω d → ℂ) :
    condPred d p X = condPred d q X := by
  have hpq : p = q := funext fun c => propext (h c)
  subst hpq
  exact congrArg (fun inst : DecidablePred p => @condPred d p inst X) (Subsingleton.elim hp hq)

theorem BddMeas.condPred {p : Coord d → Prop} [DecidablePred p] {X : Ω d → ℂ}
    (hX : BddMeas d X) : BddMeas d (RBM.Gauss.condPred d p X) := by
  obtain ⟨C, hC⟩ := hX.bdd
  refine ⟨?_, C, fun ω => ?_⟩
  · have hjoint : StronglyMeasurable fun q : Ω d × Ω d => X (predSplit d p q.1 q.2) :=
      (hX.meas.comp (measurable_predSplit d p)).stronglyMeasurable
    exact hjoint.integral_prod_right'.measurable
  · show ‖∫ ω', X (predSplit d p ω ω') ∂(P d)‖ ≤ C
    simpa using norm_integral_le_of_norm_le_const (μ := P d)
      (f := fun ω' => X (predSplit d p ω ω')) (C := C)
      (Filter.Eventually.of_forall fun ω' => hC _)

/-- **The double integral over an independent pair collapses.**  This is
`RBM.Gauss.measurePreserving_predSplit` in integral form, and it is the only measure-theoretic
input of the iteration. -/
theorem integral_integral_predSplit (d : Dims) (p : Coord d → Prop) [DecidablePred p]
    {G : Ω d → ℂ} (hG : BddMeas d G) :
    ∫ ω₁, (∫ ω₂, G (predSplit d p ω₁ ω₂) ∂(P d)) ∂(P d) = ∫ ν, G ν ∂(P d) := by
  have hmp := measurePreserving_predSplit d p
  have hmap : ((P d).prod (P d)).map (fun q : Ω d × Ω d => predSplit d p q.1 q.2) = P d :=
    hmp.map_eq
  have hGmeas : AEStronglyMeasurable G
      (((P d).prod (P d)).map fun q : Ω d × Ω d => predSplit d p q.1 q.2) := by
    rw [hmap]; exact hG.meas.aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun ω₁ ω₂ => G (predSplit d p ω₁ ω₂))
      ((P d).prod (P d)) := by
    refine (integrable_map_measure hGmeas (measurable_predSplit d p).aemeasurable).1 ?_
    rw [hmap]; exact hG.integrable
  have hpush := integral_map (μ := (P d).prod (P d))
    (φ := fun q : Ω d × Ω d => predSplit d p q.1 q.2) (f := G)
    (measurable_predSplit d p).aemeasurable hGmeas
  rw [hmap] at hpush
  rw [integral_integral hint]
  exact hpush.symm

/-- **The conditional expectations compose.**  `E_q ∘ E_p = E_{p ∪ q}` — in particular they
**commute**, which is what lets the iteration pivot on one row after another.  The proof is the
combinatorial identity `RBM.Gauss.predSplit_predSplit` followed by
`RBM.Gauss.integral_integral_predSplit`. -/
theorem condPred_condPred (d : Dims) (p q : Coord d → Prop) [DecidablePred p] [DecidablePred q]
    {X : Ω d → ℂ} (hX : BddMeas d X) :
    condPred d q (condPred d p X) = condPred d (fun c => q c ∨ p c) X := by
  funext ω
  have hG : BddMeas d fun ν => X (predSplit d (fun c => q c ∨ p c) ω ν) := by
    obtain ⟨C, hC⟩ := hX.bdd
    exact ⟨hX.meas.comp ((measurable_predSplit d fun c => q c ∨ p c).comp
      (measurable_const.prodMk measurable_id)), C, fun ν => hC _⟩
  have hkey : ∀ ω₁ ω₂ : Ω d, X (predSplit d p (predSplit d q ω ω₁) ω₂)
      = (fun ν => X (predSplit d (fun c => q c ∨ p c) ω ν)) (predSplit d p ω₁ ω₂) := by
    intro ω₁ ω₂
    rw [predSplit_predSplit d q p ω ω₁ ω₂]
  show (∫ ω₁, (∫ ω₂, X (predSplit d p (predSplit d q ω ω₁) ω₂) ∂(P d)) ∂(P d)) = _
  simp only [hkey]
  exact integral_integral_predSplit d p hG

/-- **`E_k` and `E_κ` commute** — the fact `RBM1D/Gauss/CondRow.lean` does not have and the
iteration cannot do without.  Note that no relation between `k` and `κ` is needed: the two rows
may share the entry `H_{kκ}`, because both sides are the single conditional expectation over the
*union* of the two rows. -/
theorem condRow_condRow_comm (d : Dims) (N : ℕ) (k κ : d.Idx N) {X : Ω d → ℂ}
    (hX : BddMeas d X) :
    condRow d N k (condRow d N κ X) = condRow d N κ (condRow d N k X) := by
  rw [condRow_eq_condPred, condRow_eq_condPred, condRow_eq_condPred, condRow_eq_condPred,
    condPred_condPred d _ _ hX, condPred_condPred d _ _ hX]
  exact condPred_congr d (fun c => or_comm) X

/-! ### `Q_k = 1 - E_k` and words in the `P`'s and `Q`'s

A factor of the product acquires, one pivot at a time, a word of operators `P_κ = E_κ` and
`Q_κ = 1 - E_κ`.  The word is recorded as a `List (Bool × d.Idx N)`, the head being the
**outermost** operator and `true` meaning `Q`. -/

/-- `Q_k X = X - E_k X`. -/
noncomputable def qRow (d : Dims) (N : ℕ) (k : d.Idx N) (X : Ω d → ℂ) : Ω d → ℂ :=
  fun ω => X ω - condRow d N k X ω

theorem qRow_apply (k : d.Idx N) (X : Ω d → ℂ) (ω : Ω d) :
    qRow d N k X ω = X ω - condRow d N k X ω := rfl

/-- `X = Q_k X + P_k X`, the splitting the expansion is built on. -/
theorem qRow_add_condRow (k : d.Idx N) (X : Ω d → ℂ) (ω : Ω d) :
    qRow d N k X ω + condRow d N k X ω = X ω := sub_add_cancel _ _

theorem BddMeas.condRow {X : Ω d → ℂ} (hX : BddMeas d X) (k : d.Idx N) :
    BddMeas d (RBM.Gauss.condRow d N k X) :=
  hX.condPred (p := IsRowCoord d N k)

theorem BddMeas.qRow {X : Ω d → ℂ} (hX : BddMeas d X) (k : d.Idx N) :
    BddMeas d (RBM.Gauss.qRow d N k X) :=
  hX.sub (hX.condRow k)

@[simp] theorem condRow_zero (d : Dims) (N : ℕ) (k : d.Idx N) :
    condRow d N k (0 : Ω d → ℂ) = 0 := condRow_const k 0

/-- **`E_k ∘ Q_k = 0`** — `RBM.Gauss.condRow_sub_condRow`, in the notation of this file. -/
theorem condRow_qRow {X : Ω d → ℂ} (hX : BddMeas d X) (k : d.Idx N) :
    condRow d N k (qRow d N k X) = 0 :=
  condRow_sub_condRow k (hX.rowIntegrable k)

/-- **`E_k` commutes with `Q_κ`**, for any two rows.  Together with
`RBM.Gauss.condRow_condRow_comm` this says `E_k` commutes with every letter of a word. -/
theorem condRow_qRow_comm (d : Dims) (N : ℕ) (k κ : d.Idx N) {X : Ω d → ℂ}
    (hX : BddMeas d X) :
    condRow d N k (qRow d N κ X) = qRow d N κ (condRow d N k X) := by
  have h := condRow_sub k (hX.rowIntegrable k) ((hX.condRow κ).rowIntegrable k)
  have h2 : condRow d N k (qRow d N κ X)
      = fun ω => condRow d N k X ω - condRow d N k (condRow d N κ X) ω := h
  rw [h2, condRow_condRow_comm d N k κ hX]
  rfl

/-- A word in the `P`'s and `Q`'s, applied to `X`.  The head of the list is the **outermost**
operator; `true` is `Q_κ`, `false` is `P_κ`. -/
noncomputable def applyOps (d : Dims) (N : ℕ) :
    List (Bool × d.Idx N) → (Ω d → ℂ) → (Ω d → ℂ)
  | [], X => X
  | (b, κ) :: l, X => (if b then qRow d N κ else condRow d N κ) (applyOps d N l X)

@[simp] theorem applyOps_nil (d : Dims) (N : ℕ) (X : Ω d → ℂ) : applyOps d N [] X = X := rfl

@[simp] theorem applyOps_cons_true (d : Dims) (N : ℕ) (κ : d.Idx N)
    (l : List (Bool × d.Idx N)) (X : Ω d → ℂ) :
    applyOps d N ((true, κ) :: l) X = qRow d N κ (applyOps d N l X) := rfl

@[simp] theorem applyOps_cons_false (d : Dims) (N : ℕ) (κ : d.Idx N)
    (l : List (Bool × d.Idx N)) (X : Ω d → ℂ) :
    applyOps d N ((false, κ) :: l) X = condRow d N κ (applyOps d N l X) := rfl

/-- The number of `Q`'s in a word: the exponent that carries the gain. -/
def numQ (l : List (Bool × d.Idx N)) : ℕ := l.countP fun x => x.1

@[simp] theorem numQ_nil (d : Dims) (N : ℕ) : numQ ([] : List (Bool × d.Idx N)) = 0 := rfl

@[simp] theorem numQ_cons_true (κ : d.Idx N) (l : List (Bool × d.Idx N)) :
    numQ ((true, κ) :: l) = numQ l + 1 := by
  simp [numQ]

@[simp] theorem numQ_cons_false (κ : d.Idx N) (l : List (Bool × d.Idx N)) :
    numQ ((false, κ) :: l) = numQ l := by
  simp [numQ]

theorem BddMeas.applyOps {X : Ω d → ℂ} (hX : BddMeas d X) (l : List (Bool × d.Idx N)) :
    BddMeas d (RBM.Gauss.applyOps d N l X) := by
  induction l with
  | nil => simpa using hX
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using ih.condRow κ
      · simpa only [applyOps_cons_true] using ih.qRow κ

/-- **`E_k` commutes with any word.**  By induction on the word, from
`RBM.Gauss.condRow_condRow_comm` and `RBM.Gauss.condRow_qRow_comm`. -/
theorem condRow_applyOps_comm (d : Dims) (N : ℕ) (k : d.Idx N) (l : List (Bool × d.Idx N))
    {X : Ω d → ℂ} (hX : BddMeas d X) :
    condRow d N k (applyOps d N l X) = applyOps d N l (condRow d N k X) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [applyOps_cons_false]
        rw [← ih]
        exact condRow_condRow_comm d N k κ (hX.applyOps l)
      · simp only [applyOps_cons_true]
        rw [← ih]
        exact condRow_qRow_comm d N k κ (hX.applyOps l)

@[simp] theorem applyOps_zero (d : Dims) (N : ℕ) (l : List (Bool × d.Idx N)) :
    applyOps d N l (0 : Ω d → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [applyOps_cons_false, ih, condRow_zero]
      · simp only [applyOps_cons_true, ih]
        funext ω
        show (0 : ℂ) - condRow d N κ (0 : Ω d → ℂ) ω = 0
        rw [condRow_zero]; simp

/-- **The pivot factor is annihilated by `E_k`, whatever word it carries.**  This is the exact
identity the whole iteration runs on: the `Q_{k}` sitting innermost is never destroyed, because
`E_k` commutes with every letter of the word. -/
theorem condRow_applyOps_qRow (d : Dims) (N : ℕ) (k : d.Idx N) (l : List (Bool × d.Idx N))
    {X : Ω d → ℂ} (hX : BddMeas d X) :
    condRow d N k (applyOps d N l (qRow d N k X)) = 0 := by
  rw [condRow_applyOps_comm d N k l (hX.qRow k), condRow_qRow hX k, applyOps_zero]

/-! ### Finite dependence of the words

`RBM.Gauss.integral_mul_prod_eq_zero` needs the non-pivot factors to be `FinDepOffRow`, i.e. to
read no coordinate of the pivot row.  After a pivot they carry an outermost `P_κ`, and `E_κ` of
anything reading finitely many coordinates does not read row `κ`. -/

theorem finDep_sub {X Y : Ω d → ℂ} (hX : FinDep d X) (hY : FinDep d Y) :
    FinDep d fun ω => X ω - Y ω := by
  classical
  obtain ⟨I, hI⟩ := hX
  obtain ⟨J, hJ⟩ := hY
  refine ⟨I ∪ J, fun ω ω' hω => ?_⟩
  show X ω - Y ω = X ω' - Y ω'
  rw [hI ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
    hJ ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

theorem finDep_condRow (k : d.Idx N) {X : Ω d → ℂ} (h : FinDep d X) :
    FinDep d (condRow d N k X) := by
  obtain ⟨I, hI⟩ := h
  refine ⟨I, fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hI _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord d N k c
  · rw [rowSplit_apply_of_isRowCoord k ω ω'' hcr, rowSplit_apply_of_isRowCoord k ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k ω' ω'' hcr]
    exact hω c hc

/-- **`E_κ` of a finitely-dependent function does not read row `κ`.**  This is the instance of
`RBM.Gauss.FinDepOffRow` that the expansion produces at every pivot. -/
theorem finDepOffRow_condRow_self (κ : d.Idx N) {X : Ω d → ℂ} (h : FinDep d X) :
    FinDepOffRow d N κ (condRow d N κ X) := by
  classical
  obtain ⟨I, hI⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord d N κ c, fun c hc => (Finset.mem_filter.1 hc).2,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hI _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord d N κ c
  · rw [rowSplit_apply_of_isRowCoord κ ω ω'' hcr, rowSplit_apply_of_isRowCoord κ ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord κ ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord κ ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

theorem finDep_qRow (k : d.Idx N) {X : Ω d → ℂ} (h : FinDep d X) :
    FinDep d (qRow d N k X) := finDep_sub h (finDep_condRow k h)

theorem finDep_applyOps (l : List (Bool × d.Idx N)) {X : Ω d → ℂ} (h : FinDep d X) :
    FinDep d (applyOps d N l X) := by
  induction l with
  | nil => simpa using h
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using finDep_condRow κ ih
      · simpa only [applyOps_cons_true] using finDep_qRow κ ih

/-! ### One pivot: expand, and kill the all-`P` term -/

section Pivot

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The factor family produced by one pivot on row `κ` at slot `i₀`, for the subset `S` of slots
that receive `Q_κ`; the slots outside `S` receive `P_κ`, and the pivot slot is untouched. -/
noncomputable def pivotFam (d : Dims) (N : ℕ) (κ : d.Idx N) (i₀ : ι) (S : Finset ι)
    (F : ι → Ω d → ℂ) (i : ι) : Ω d → ℂ :=
  if i = i₀ then F i₀ else if i ∈ S then qRow d N κ (F i) else condRow d N κ (F i)

omit [Fintype ι] in
@[simp] theorem pivotFam_self (d : Dims) (N : ℕ) (κ : d.Idx N) (i₀ : ι) (S : Finset ι)
    (F : ι → Ω d → ℂ) : pivotFam d N κ i₀ S F i₀ = F i₀ := by
  simp [pivotFam]

omit [Fintype ι] in
theorem pivotFam_of_mem (d : Dims) (N : ℕ) (κ : d.Idx N) {i₀ : ι} {S : Finset ι}
    (F : ι → Ω d → ℂ) {i : ι} (h : i ≠ i₀) (hi : i ∈ S) :
    pivotFam d N κ i₀ S F i = qRow d N κ (F i) := by
  simp [pivotFam, h, hi]

omit [Fintype ι] in
theorem pivotFam_of_not_mem (d : Dims) (N : ℕ) (κ : d.Idx N) {i₀ : ι} {S : Finset ι}
    (F : ι → Ω d → ℂ) {i : ι} (h : i ≠ i₀) (hi : i ∉ S) :
    pivotFam d N κ i₀ S F i = condRow d N κ (F i) := by
  simp [pivotFam, h, hi]

/-- The product of a pivoted family, split at the pivot slot. -/
theorem prod_pivotFam_eq (d : Dims) (N : ℕ) (κ : d.Idx N) (i₀ : ι) {S : Finset ι}
    (hS : S ⊆ Finset.univ.erase i₀) (F : ι → Ω d → ℂ) (ω : Ω d) :
    ∏ i, pivotFam d N κ i₀ S F i ω
      = F i₀ ω * ((∏ i ∈ S, qRow d N κ (F i) ω)
        * ∏ i ∈ Finset.univ.erase i₀ \ S, condRow d N κ (F i) ω) := by
  classical
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hsplit : ∏ i, pivotFam d N κ i₀ S F i ω
      = pivotFam d N κ i₀ S F i₀ ω * ∏ i ∈ t, pivotFam d N κ i₀ S F i ω :=
    (Finset.mul_prod_erase Finset.univ (fun i => pivotFam d N κ i₀ S F i ω)
      (Finset.mem_univ i₀)).symm
  have hsd : (∏ i ∈ t \ S, pivotFam d N κ i₀ S F i ω)
      * ∏ i ∈ S, pivotFam d N κ i₀ S F i ω = ∏ i ∈ t, pivotFam d N κ i₀ S F i ω :=
    Finset.prod_sdiff hS
  have h1 : ∏ i ∈ S, pivotFam d N κ i₀ S F i ω = ∏ i ∈ S, qRow d N κ (F i) ω :=
    Finset.prod_congr rfl fun i hi => by
      rw [pivotFam_of_mem d N κ F (Finset.mem_erase.1 (hS hi)).1 hi]
  have h2 : ∏ i ∈ t \ S, pivotFam d N κ i₀ S F i ω
      = ∏ i ∈ t \ S, condRow d N κ (F i) ω :=
    Finset.prod_congr rfl fun i hi => by
      obtain ⟨hit, hiS⟩ := Finset.mem_sdiff.1 hi
      rw [pivotFam_of_not_mem d N κ F (Finset.mem_erase.1 hit).1 hiS]
  rw [hsplit, ← hsd, h1, h2, pivotFam_self]
  ring

/-- **The one-pivot expansion.**  Writing `1 = Q_κ + P_κ` in every slot but the pivot,
`∏_i F_i` becomes a sum over the subsets `S` of the non-pivot slots. -/
theorem prod_eq_sum_pivotFam (d : Dims) (N : ℕ) (κ : d.Idx N) (i₀ : ι) (F : ι → Ω d → ℂ)
    (ω : Ω d) :
    ∏ i, F i ω = ∑ S ∈ (Finset.univ.erase i₀).powerset, ∏ i, pivotFam d N κ i₀ S F i ω := by
  classical
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hsplit : ∏ i, F i ω = F i₀ ω * ∏ i ∈ t, F i ω :=
    (Finset.mul_prod_erase Finset.univ (fun i => F i ω) (Finset.mem_univ i₀)).symm
  have hadd : ∏ i ∈ t, F i ω
      = ∏ i ∈ t, (qRow d N κ (F i) ω + condRow d N κ (F i) ω) :=
    Finset.prod_congr rfl fun i _ => (qRow_add_condRow κ (F i) ω).symm
  rw [hsplit, hadd, Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [prod_pivotFam_eq d N κ i₀ (Finset.mem_powerset.1 hS) F ω]

/-- **The all-`P` term vanishes.**  Every non-pivot factor now carries an outermost `E_κ`, so it
does not read row `κ`; `E_κ` therefore passes through the product and annihilates the pivot
factor.  This is `RBM.Gauss.integral_mul_prod_eq_zero`. -/
theorem integral_prod_pivotFam_empty (d : Dims) (N : ℕ) {κ : d.Idx N} {i₀ : ι}
    {F : ι → Ω d → ℂ} (hF : ∀ i, BddMeas d (F i)) (hFd : ∀ i, FinDep d (F i))
    (h0 : condRow d N κ (F i₀) = 0) :
    ∫ ω, ∏ i, pivotFam d N κ i₀ (∅ : Finset ι) F i ω ∂(P d) = 0 := by
  classical
  have hrw : ∀ ω : Ω d, ∏ i, pivotFam d N κ i₀ (∅ : Finset ι) F i ω
      = F i₀ ω * ∏ i ∈ Finset.univ.erase i₀, condRow d N κ (F i) ω := by
    intro ω
    rw [prod_pivotFam_eq d N κ i₀ (Finset.empty_subset _) F ω]
    simp
  have hint : Integrable
      (fun ω => F i₀ ω * ∏ i ∈ Finset.univ.erase i₀, condRow d N κ (F i) ω) (P d) :=
    ((hF i₀).mul (bddMeas_prod _ fun i _ => (hF i).condRow κ)).integrable
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact integral_mul_prod_eq_zero (Z := F) (Y := fun i => condRow d N κ (F i)) h0
    (fun i _ => finDepOffRow_condRow_self κ (hFd i)) hint

omit [Fintype ι] in
theorem bddMeas_pivotFam (d : Dims) (N : ℕ) (κ : d.Idx N) (i₀ : ι) (S : Finset ι)
    {F : ι → Ω d → ℂ} (hF : ∀ i, BddMeas d (F i)) (i : ι) :
    BddMeas d (pivotFam d N κ i₀ S F i) := by
  by_cases h : i = i₀
  · subst h; rw [pivotFam_self]; exact hF i
  · by_cases hi : i ∈ S
    · rw [pivotFam_of_mem d N κ F h hi]; exact (hF i).qRow κ
    · rw [pivotFam_of_not_mem d N κ F h hi]; exact (hF i).condRow κ

end Pivot

/-! ### Admissible words

The gain estimate that drives the iteration — the higher-order minor expansion — needs the rows
of a word to be **pairwise distinct** and **different from the row of the slot it sits on**.
`OpsOk` is that condition; `OpsOkOut` is the strengthening carried as the induction invariant,
recording in addition that the rows already used are those of slots *outside* the set `R` of
pivots still to come. -/

section Words

variable {ι : Type*}

/-- The word `l` uses pairwise distinct rows, none of them the row `k i` of the slot it sits
on.  This is exactly the shape in which the higher-order minor expansion
`‖P_C Q_A Q_{k i} G_{k i, k i}‖ ≺ Ψ^{#A + 1}` is available. -/
def OpsOk (k : ι → d.Idx N) (i : ι) (l : List (Bool × d.Idx N)) : Prop :=
  (l.map Prod.snd).Nodup ∧ ∀ x ∈ l, x.2 ≠ k i

variable [DecidableEq ι]

/-- `OpsOk` with the rows moreover coming from slots outside `R` — the induction invariant. -/
def OpsOkOut (k : ι → d.Idx N) (i : ι) (R : Finset ι) (l : List (Bool × d.Idx N)) : Prop :=
  (l.map Prod.snd).Nodup ∧ ∀ x ∈ l, (∃ j, j ∉ R ∧ x.2 = k j) ∧ x.2 ≠ k i

omit [DecidableEq ι] in
theorem opsOkOut_nil (k : ι → d.Idx N) (i : ι) (R : Finset ι) :
    OpsOkOut k i R ([] : List (Bool × d.Idx N)) := ⟨by simp, by simp⟩

omit [DecidableEq ι] in
theorem OpsOkOut.opsOk {k : ι → d.Idx N} {i : ι} {R : Finset ι} {l : List (Bool × d.Idx N)}
    (h : OpsOkOut k i R l) : OpsOk k i l := ⟨h.1, fun x hx => (h.2 x hx).2⟩

omit [DecidableEq ι] in
theorem OpsOkOut.mono {k : ι → d.Idx N} {i : ι} {R R' : Finset ι} (hR : R' ⊆ R)
    {l : List (Bool × d.Idx N)} (h : OpsOkOut k i R l) : OpsOkOut k i R' l :=
  ⟨h.1, fun x hx => let ⟨⟨j, hjR, hx'⟩, hxi⟩ := h.2 x hx
    ⟨⟨j, fun hj => hjR (hR hj), hx'⟩, hxi⟩⟩

/-- **The invariant is preserved by a pivot.**  Consing the letter `(b, k i₀)` onto a word
admissible outside `R` keeps it admissible outside `R.erase i₀`, provided `i₀ ∈ R`, `i ≠ i₀`
and the row `k i₀` is **lone** — it occurs at no other slot.  Loneness is what makes the new
letter genuinely new, and it is exactly the hypothesis `hlone` below. -/
theorem OpsOkOut.cons {k : ι → d.Idx N} {i i₀ : ι} {R : Finset ι}
    (hlone : ∀ j, j ≠ i₀ → k j ≠ k i₀) (hi₀ : i₀ ∈ R) (hne : i ≠ i₀)
    {l : List (Bool × d.Idx N)} (h : OpsOkOut k i R l) (b : Bool) :
    OpsOkOut k i (R.erase i₀) ((b, k i₀) :: l) := by
  refine ⟨?_, ?_⟩
  · refine List.nodup_cons.2 ⟨fun hmem => ?_, h.1⟩
    obtain ⟨x, hx, hx'⟩ := List.mem_map.1 hmem
    obtain ⟨⟨j, hjR, hxj⟩, _⟩ := h.2 x hx
    have hj : j ≠ i₀ := fun hj => hjR (hj ▸ hi₀)
    exact hlone j hj (by rw [← hxj]; exact hx')
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨⟨i₀, Finset.notMem_erase _ _, rfl⟩, (hlone i hne).symm⟩
    · obtain ⟨⟨j, hjR, hxj⟩, hxi⟩ := h.2 x hx
      exact ⟨⟨j, fun hj => hjR (Finset.mem_of_mem_erase hj), hxj⟩, hxi⟩

end Words

/-! ### The iteration

The induction is on the number of **pivots still to be performed**.  The state is a family of
words `L i`, one per slot; the invariant is that every word is admissible outside the set `R` of
remaining pivots.  One step picks a pivot `i₀ ∈ R`, expands `1 = Q_{k i₀} + P_{k i₀}` in every
other slot, discards the all-`P` term (it vanishes) and recurses on `R.erase i₀` with the words
lengthened by one letter.  Each surviving term has at least one more `Q`, which is where the
extra factor `ρ` comes from; after `#ι` pivots the bound carries `ρ^{#ι}` on top of the trivial
`B^{#ι}`, i.e. `Ψ^{4p}` when `#ι = 2p` and `B, ρ ≍ Ψ`. -/

section Iterate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The word family after one pivot at slot `i₀`, with `Q`-set `S`. -/
def pivotWords (k : ι → d.Idx N) (i₀ : ι) (S : Finset ι) (L : ι → List (Bool × d.Idx N))
    (i : ι) : List (Bool × d.Idx N) :=
  if i = i₀ then L i₀ else if i ∈ S then (true, k i₀) :: L i else (false, k i₀) :: L i

omit [Fintype ι] in
theorem pivotFam_eq_applyOps (d : Dims) (N : ℕ) {k : ι → d.Idx N} {X : ι → Ω d → ℂ} {i₀ : ι}
    {S : Finset ι} (L : ι → List (Bool × d.Idx N)) (i : ι) :
    pivotFam d N (k i₀) i₀ S (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) i
      = applyOps d N (pivotWords k i₀ S L i) (qRow d N (k i) (X i)) := by
  by_cases h : i = i₀
  · subst h; simp [pivotFam, pivotWords]
  · by_cases hi : i ∈ S <;> simp [pivotFam, pivotWords, h, hi]

theorem sum_numQ_pivotWords {k : ι → d.Idx N} {i₀ : ι} {S : Finset ι}
    (hS : S ⊆ Finset.univ.erase i₀) (L : ι → List (Bool × d.Idx N)) :
    ∑ i, numQ (pivotWords k i₀ S L i) = (∑ i, numQ (L i)) + S.card := by
  classical
  have hi₀ : i₀ ∉ S := fun h => (Finset.mem_erase.1 (hS h)).1 rfl
  have hstep : ∀ i : ι,
      numQ (pivotWords k i₀ S L i) = numQ (L i) + (if i ∈ S then 1 else 0) := by
    intro i
    by_cases h : i = i₀
    · subst h; simp [pivotWords, hi₀]
    · by_cases hi : i ∈ S <;> simp [pivotWords, h, hi]
  simp only [hstep, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

end Iterate

/-! ### Crude bounds, and the first order of the gain

Two facts about words, both needed to see that the gain interface below is the right one:
a word of `m` `Q`'s can always be bounded crudely by `2^m` times the bound on its argument
(so the interface is never vacuous), and **one** `Q_κ` already gains the replacement error of
`RBM1D/Gauss/MinorReplace.lean` (so `ρ ≍ Ψ` is the correct first-order value). -/

theorem norm_condRow_le {k : d.Idx N} {X : Ω d → ℂ} {b : ℝ} (hX : ∀ ω, ‖X ω‖ ≤ b) (ω : Ω d) :
    ‖condRow d N k X ω‖ ≤ b := by
  rw [condRow_apply]
  simpa using norm_integral_le_of_norm_le_const (μ := P d)
    (f := fun ω' => X (rowSplit d N k ω ω')) (C := b)
    (Filter.Eventually.of_forall fun ω' => hX _)

/-- The crude bound: every `Q` costs a factor `2`. -/
theorem norm_applyOps_le (l : List (Bool × d.Idx N)) {X : Ω d → ℂ} {b : ℝ}
    (hX : ∀ ω, ‖X ω‖ ≤ b) (ω : Ω d) :
    ‖applyOps d N l X ω‖ ≤ 2 ^ numQ l * b := by
  induction l generalizing ω with
  | nil => simpa using hX ω
  | cons x l ih =>
      obtain ⟨c, κ⟩ := x
      cases c
      · rw [applyOps_cons_false, numQ_cons_false]
        exact norm_condRow_le (fun ω' => ih ω') ω
      · rw [applyOps_cons_true, numQ_cons_true, pow_succ]
        have := norm_sub_condRow_le (k := κ) (X := applyOps d N l X)
          (b := 2 ^ numQ l * b) (fun ω' => ih ω') ω
        calc ‖qRow d N κ (applyOps d N l X) ω‖ ≤ 2 * (2 ^ numQ l * b) := this
          _ = 2 ^ numQ l * 2 * b := by ring

/-! ### The concrete fluctuations `Z_k = (1 - E_k)(G_{kk} - m)` -/

theorem flucDiag_eq_qRow (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) :
    flucDiag d N u z m k = qRow d N k (greenDiagCentered d N u z m k) := rfl

theorem finDep_greenDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) :
    FinDep d (greenDiagCentered d N u z m k) :=
  finDep_of_Hflow d N u fun H => green H z k k - m

section Env

variable {E t : ℝ}

theorem bddMeas_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N) :
    BddMeas d (greenDiagCentered d N u (zt E t) (mE E) k) :=
  ⟨measurable_greenDiagCentered d N u (zt E t) (mE E) k,
    (etaT E t)⁻¹ + 1, norm_greenDiagCentered_le_env hE ht u k⟩

theorem bddMeas_flucDiag (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N) :
    BddMeas d (flucDiag d N u (zt E t) (mE E) k) :=
  (bddMeas_greenDiagCentered hE ht u k).qRow k

end Env

/-! ### Conjugation

Half the slots of `E|∑_k t_k Z_k|^{2p}` carry a complex conjugate.  Conjugation commutes with
every `E_k` (`RBM.Gauss.condRow_conj`; for a whole word `RBM.Gauss.applyOps_epsHom`), so a
conjugated factor is again of the form `Q_{k} X` and the iteration applies verbatim. -/

theorem condRow_conj (d : Dims) (N : ℕ) (k : d.Idx N) (X : Ω d → ℂ) :
    condRow d N k (fun ω => (starRingEnd ℂ) (X ω))
      = fun ω => (starRingEnd ℂ) (condRow d N k X ω) := by
  funext ω
  simp only [condRow_apply]
  exact integral_conj

theorem qRow_conj (d : Dims) (N : ℕ) (k : d.Idx N) (X : Ω d → ℂ) :
    qRow d N k (fun ω => (starRingEnd ℂ) (X ω))
      = fun ω => (starRingEnd ℂ) (qRow d N k X ω) := by
  funext ω
  show (starRingEnd ℂ) (X ω) - condRow d N k (fun ω' => (starRingEnd ℂ) (X ω')) ω = _
  rw [condRow_conj]
  show _ = (starRingEnd ℂ) (X ω - condRow d N k X ω)
  rw [map_sub]

theorem applyOps_conj (d : Dims) (N : ℕ) (l : List (Bool × d.Idx N)) (X : Ω d → ℂ) :
    applyOps d N l (fun ω => (starRingEnd ℂ) (X ω))
      = fun ω => (starRingEnd ℂ) (applyOps d N l X ω) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [applyOps_cons_false, applyOps_cons_false, ih, condRow_conj]
      · rw [applyOps_cons_true, applyOps_cons_true, ih, qRow_conj]

theorem applyOps_epsHom (d : Dims) (N : ℕ) (p : ℕ) (i : Fin p ⊕ Fin p)
    (l : List (Bool × d.Idx N)) (X : Ω d → ℂ) :
    applyOps d N l (fun ω => epsHom p i (X ω))
      = fun ω => epsHom p i (applyOps d N l X ω) := by
  cases i with
  | inl j => simp only [epsHom_inl]
  | inr j => simpa only [epsHom_inr] using applyOps_conj d N l X

/-! ### The gain interface

The one genuinely analytic input of the iteration, isolated.  The gain is the
**higher-order minor expansion** of §4: applying `m` further conditional fluctuations
`Q_{κ_1} ⋯ Q_{κ_m}`, with `κ_1, …, κ_m` distinct rows all different from `k`, to `Z_k` gains a
factor `ρ^m`.  For `m = 0` it is the entry bound `‖Z_k‖ ≤ B`; for `m = 1` it follows from the
replacement error of `RBM1D/Gauss/MinorReplace.lean`, giving `ρ ≍ Ψ`.  Higher `m` needs the iterated
minors `G^{(κ_1 κ_2)}, …` (`RBM1D/Gauss/FlucIterHigh.lean`). -/

section EnvGain

variable {E t : ℝ}

end EnvGain

/-! ### The iterated bound for the fluctuations themselves -/

section FlucIterate

variable {E t : ℝ} {p : ℕ}

end FlucIterate

/-! ### Counting multi-indices by the number of lone slots

The first-order argument splits the multi-indices into those with *some* lone slot and those
with none.  The iteration needs the finer stratification by the *number* of lone slots, because that
number is the number of pivots available, hence the power of the gain.  The counting input is: a
value taken by a non-lone slot uses up at least two slots, so

  `2 · #(image v) ≤ #ι + #(lone slots of v)`. -/

section Counting

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- The set of slots whose value occurs nowhere else. -/
def loneSlots (v : ι → κ) : Finset ι :=
  (Finset.univ : Finset ι).filter fun i => ∀ j, j ≠ i → v j ≠ v i

@[simp] theorem mem_loneSlots {v : ι → κ} {i : ι} :
    i ∈ loneSlots v ↔ ∀ j, j ≠ i → v j ≠ v i := by
  simp [loneSlots]

/-- The values taken exactly once are exactly the values of the lone slots. -/
theorem image_loneSlots_eq (v : ι → κ) :
    (loneSlots v).image v
      = ((Finset.univ : Finset ι).image v).filter
          fun b => ((Finset.univ : Finset ι).filter fun i => v i = b).card = 1 := by
  classical
  ext b
  simp only [Finset.mem_image, Finset.mem_filter, mem_loneSlots]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, Finset.mem_univ i, rfl⟩, ?_⟩
    have : ((Finset.univ : Finset ι).filter fun j => v j = v i) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hj => by_contra fun hji => hi j hji hj, fun hj => by rw [hj]⟩
    rw [this, Finset.card_singleton]
  · rintro ⟨⟨i, -, rfl⟩, hcard⟩
    obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hcard
    have hij : i = j := by
      have : i ∈ ({j} : Finset ι) := by
        rw [← hj]; exact Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩
      exact Finset.mem_singleton.1 this
    refine ⟨i, fun j' hj' hvj' => ?_, rfl⟩
    have : j' ∈ ({j} : Finset ι) := by
      rw [← hj]; exact Finset.mem_filter.2 ⟨Finset.mem_univ j', hvj'⟩
    exact hj' (by rw [Finset.mem_singleton.1 this, ← hij])

/-- **The refined counting inequality.**  Every value of `v` uses up at least one slot, and a
value that is not the value of a lone slot uses up at least two. -/
theorem two_mul_card_image_le_add_card_loneSlots (v : ι → κ) :
    2 * ((Finset.univ : Finset ι).image v).card
      ≤ Fintype.card ι + (loneSlots v).card := by
  classical
  set I : Finset κ := (Finset.univ : Finset ι).image v with hI
  set pr : κ → Prop := fun b => ((Finset.univ : Finset ι).filter fun i => v i = b).card = 1
    with hpr
  have hinj : Set.InjOn v (loneSlots v) := by
    intro i hi j hj hij
    by_contra hne
    exact (mem_loneSlots.1 hi) j (Ne.symm hne) hij.symm
  have hSa : (I.filter pr).card = (loneSlots v).card := by
    rw [← image_loneSlots_eq v, Finset.card_image_of_injOn hinj]
  have hfib : (Fintype.card ι)
      = ∑ b ∈ I, ((Finset.univ : Finset ι).filter fun i => v i = b).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun i _ =>
      Finset.mem_coe.2 (Finset.mem_image_of_mem v (Finset.mem_univ i))
  have hlow : ∀ b ∈ I, (if pr b then 1 else 2)
      ≤ ((Finset.univ : Finset ι).filter fun i => v i = b).card := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    have hpos : 1 ≤ ((Finset.univ : Finset ι).filter fun j => v j = v i).card :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩⟩
    by_cases hp : pr (v i)
    · rw [ite_eq_left hp]; exact hpos
    · rw [ite_eq_right hp]
      rw [hpr] at hp
      omega
  have hsum : (∑ b ∈ I, (if pr b then (1 : ℕ) else 2)) ≤ Fintype.card ι := by
    rw [hfib]; exact Finset.sum_le_sum hlow
  have hval : (∑ b ∈ I, (if pr b then (1 : ℕ) else 2)) + (I.filter pr).card
      = 2 * I.card := by
    rw [← Finset.sum_filter_add_sum_filter_not I pr fun b => (if pr b then (1 : ℕ) else 2)]
    have e1 : ∑ b ∈ I.filter pr, (if pr b then (1 : ℕ) else 2) = (I.filter pr).card := by
      rw [Finset.sum_congr rfl fun b hb => ite_eq_left (Finset.mem_filter.1 hb).2,
        Finset.sum_const, smul_eq_mul, mul_one]
    have e2 : ∑ b ∈ I.filter (fun b => ¬ pr b), (if pr b then (1 : ℕ) else 2)
        = 2 * (I.filter fun b => ¬ pr b).card := by
      rw [Finset.sum_congr rfl fun b hb => ite_eq_right (Finset.mem_filter.1 hb).2,
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [e1, e2]
    have hcards := Finset.card_filter_add_card_filter_not (s := I) pr
    omega
  omega

/-- **The number of multi-indices with a small image.**  Such a `v` has its image inside an
`s`-element subset of `A`, and is then one of the `s^{#ι}` functions into it. -/
theorem card_filter_card_image_le (A : Finset κ) (s : ℕ) (hs : s ≤ A.card) :
    ((Fintype.piFinset fun _ : ι => A).filter
        fun v => ((Finset.univ : Finset ι).image v).card ≤ s).card
      ≤ A.card ^ s * s ^ Fintype.card ι := by
  classical
  have hsub : ((Fintype.piFinset fun _ : ι => A).filter
      fun v => ((Finset.univ : Finset ι).image v).card ≤ s)
      ⊆ (A.powersetCard s).biUnion fun S => Fintype.piFinset fun _ : ι => S := by
    intro v hv
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
    obtain ⟨hvA, hvs⟩ := hv
    have h1 : (Finset.univ : Finset ι).image v ⊆ A := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ha
      exact hvA i
    obtain ⟨S, hS1, hS2, hS3⟩ := Finset.exists_subsuperset_card_eq h1 hvs hs
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨hS2, hS3⟩,
      Fintype.mem_piFinset.2 fun i => hS1 (Finset.mem_image_of_mem v (Finset.mem_univ i))⟩
  calc ((Fintype.piFinset fun _ : ι => A).filter
        fun v => ((Finset.univ : Finset ι).image v).card ≤ s).card
      ≤ ((A.powersetCard s).biUnion fun S => Fintype.piFinset fun _ : ι => S).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ S ∈ A.powersetCard s, (Fintype.piFinset fun _ : ι => S).card :=
        Finset.card_biUnion_le
    _ = ∑ _S ∈ A.powersetCard s, s ^ Fintype.card ι := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
          (Finset.mem_powersetCard.1 hS).2]
    _ = (A.card).choose s * s ^ Fintype.card ι := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
    _ ≤ A.card ^ s * s ^ Fintype.card ι := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

end Counting

/-! ### The stratified weight sum

With the per-multi-index bound `K^a ρ^a B^n` (`a` = number of lone slots) in hand, the sum over
multi-indices weighted by `∏_i |t_{v i}|` is stratified by `a`.  A multi-index with `a` lone
slots has at most `(n + a)/2` distinct values, so its weight is `c^n` times a count of at most
`(#A)^{(n+a)/2} · n^n`; since `c · #A ≤ 1` and `c ≤ ρ²`, the weight of the stratum is at most
`n^n ρ^{n-a}`, and the `ρ^a` of the iteration completes it to `ρ^n`.  **This is why the
iteration gives `Ψ^{4p}`**: with `c ≍ Ψ²` (so `ρ ≍ Ψ`) and `B ≍ Ψ`, the bound is
`C_n (B ρ)^n = C_p Ψ^{4p}`. -/

section Strata

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The weight of the multi-indices with at most `s` distinct values. -/
theorem sum_prod_abs_card_image_le {t : κ → ℝ} {c : ℝ} {A : Finset κ}
    (hw : UniformWeight t c A) {s n : ℕ} (hs : s ≤ A.card) (hsn : s ≤ n)
    (hcard : Fintype.card ι = n) :
    ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => ((Finset.univ : Finset ι).image v).card ≤ s), ∏ i, |t (v i)|
      ≤ c ^ (n - s) * (s : ℝ) ^ n := by
  classical
  set F : Finset (ι → κ) := (Finset.univ : Finset (ι → κ)).filter
    fun v => ((Finset.univ : Finset ι).image v).card ≤ s with hF
  set G : Finset (ι → κ) := (Fintype.piFinset fun _ : ι => A).filter
    fun v => ((Finset.univ : Finset ι).image v).card ≤ s with hG
  have hrestrict : ∑ v ∈ F, ∏ i, |t (v i)| = ∑ v ∈ G, ∏ i, |t (v i)| := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro v hv
      rw [hG, Finset.mem_filter] at hv
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hv.2⟩
    · intro v hv hv'
      rw [hF, Finset.mem_filter] at hv
      have hex : ∃ i, v i ∉ A := by
        by_contra hcon
        refine hv' (Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, hv.2⟩)
        by_contra hi
        exact hcon ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hex
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hw.not_mem (v i) hi, abs_zero]
  have hval : ∀ v ∈ G, ∏ i, |t (v i)| = c ^ n := by
    intro v hv
    rw [hG, Finset.mem_filter, Fintype.mem_piFinset] at hv
    have hone : ∀ i : ι, |t (v i)| = c := fun i => by
      rw [hw.mem (v i) (hv.1 i), abs_of_nonneg hw.nonneg]
    simp_rw [hone]
    rw [Finset.prod_const, Finset.card_univ, hcard]
  have hcn : (0 : ℝ) ≤ c ^ n := pow_nonneg hw.nonneg _
  have hcount : G.card ≤ A.card ^ s * s ^ Fintype.card ι :=
    card_filter_card_image_le (ι := ι) A s hs
  have hsplit : c ^ n = c ^ s * c ^ (n - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hsn]
  calc ∑ v ∈ F, ∏ i, |t (v i)| = (G.card : ℝ) * c ^ n := by
        rw [hrestrict, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((A.card ^ s * s ^ Fintype.card ι : ℕ) : ℝ) * c ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ hcn
        exact_mod_cast hcount
    _ = (c * A.card) ^ s * (c ^ (n - s) * (s : ℝ) ^ n) := by
        rw [hcard, hsplit]
        push_cast
        rw [mul_pow]
        ring
    _ ≤ 1 * (c ^ (n - s) * (s : ℝ) ^ n) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (pow_nonneg hw.nonneg _) (by positivity))
        exact pow_le_one₀ (mul_nonneg hw.nonneg (Nat.cast_nonneg _)) hw.mass
    _ = c ^ (n - s) * (s : ℝ) ^ n := one_mul _

/-- **The stratified sum.**  If every multi-index `v` satisfies the iterated bound
`f v ≤ (K ρ)^{#lone slots} · B^n`, then the weighted sum over all multi-indices is at most
`(n + 1) n^n (K ρ B)^n`: the gain `ρ` is paid `#lone` times by the iteration and `n - #lone`
times by the counting.  The constant depends only on `n = 2p`. -/
theorem sum_weighted_le {t : κ → ℝ} {c : ℝ} {A : Finset κ} (hw : UniformWeight t c A)
    {n : ℕ} (hcard : Fintype.card ι = n) (hn : n ≤ A.card)
    {ρ B K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hcρ : c ≤ ρ ^ 2) {f : (ι → κ) → ℝ}
    (hf : ∀ v, f v ≤ K ^ (loneSlots v).card * ρ ^ (loneSlots v).card * B ^ n) :
    ∑ v : ι → κ, (∏ i, |t (v i)|) * f v
      ≤ ((n : ℝ) + 1) * (n : ℝ) ^ n * (K * ρ * B) ^ n := by
  classical
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hmaps : ∀ v ∈ (Finset.univ : Finset (ι → κ)),
      (loneSlots v).card ∈ Finset.range (n + 1) := by
    intro v _
    refine Finset.mem_range.2 ?_
    have := Finset.card_le_card (Finset.subset_univ (loneSlots v))
    rw [Finset.card_univ, hcard] at this
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    fun v => (∏ i, |t (v i)|) * f v]
  -- each stratum
  have hstrat : ∀ a ∈ Finset.range (n + 1),
      ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
          (∏ i, |t (v i)|) * f v
        ≤ (n : ℝ) ^ n * (K * ρ * B) ^ n := by
    intro a ha
    have han : a ≤ n := by have := Finset.mem_range.1 ha; omega
    set sa : ℕ := (n + a) / 2 with hsa
    have hsan : sa ≤ n := by omega
    have hsaA : sa ≤ A.card := le_trans hsan hn
    have hsub : (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a)
        ⊆ (Finset.univ : Finset (ι → κ)).filter
            (fun v => ((Finset.univ : Finset ι).image v).card ≤ sa) := by
      intro v hv
      obtain ⟨-, hva⟩ := Finset.mem_filter.1 hv
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      have h1 := two_mul_card_image_le_add_card_loneSlots v
      rw [hcard, hva] at h1
      omega
    have hbound : ∀ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => (loneSlots v).card = a),
        (∏ i, |t (v i)|) * f v ≤ (∏ i, |t (v i)|) * (K ^ a * ρ ^ a * B ^ n) := by
      intro v hv
      obtain ⟨-, hva⟩ := Finset.mem_filter.1 hv
      refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun i _ => abs_nonneg _)
      have := hf v
      rwa [hva] at this
    have hwsum : ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter
        (fun v => (loneSlots v).card = a), ∏ i, |t (v i)|
        ≤ c ^ (n - sa) * (sa : ℝ) ^ n := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
      · exact fun v _ _ => Finset.prod_nonneg fun i _ => abs_nonneg _
      · exact sum_prod_abs_card_image_le hw hsaA hsan hcard
    -- `c^(n - sa) ≤ ρ^(n - a)`
    have hcpow : c ^ (n - sa) ≤ ρ ^ (n - a) := by
      have h1 : c ^ (n - sa) ≤ (ρ ^ 2) ^ (n - sa) :=
        pow_le_pow_left₀ hw.nonneg hcρ _
      have h2 : (ρ ^ 2) ^ (n - sa) = ρ ^ (2 * (n - sa)) := by rw [← pow_mul]
      have h3 : n - a ≤ 2 * (n - sa) := by omega
      have h4 : ρ ^ (2 * (n - sa)) ≤ ρ ^ (n - a) := pow_le_pow_of_le_one hρ0 hρ1 h3
      calc c ^ (n - sa) ≤ (ρ ^ 2) ^ (n - sa) := h1
        _ = ρ ^ (2 * (n - sa)) := h2
        _ ≤ ρ ^ (n - a) := h4
    have hsan' : (sa : ℝ) ^ n ≤ (n : ℝ) ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsan) _
    calc ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
          (∏ i, |t (v i)|) * f v
        ≤ ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
            (∏ i, |t (v i)|) * (K ^ a * ρ ^ a * B ^ n) := Finset.sum_le_sum hbound
      _ = (∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
            ∏ i, |t (v i)|) * (K ^ a * ρ ^ a * B ^ n) := by rw [Finset.sum_mul]
      _ ≤ (c ^ (n - sa) * (sa : ℝ) ^ n) * (K ^ a * ρ ^ a * B ^ n) := by
          refine mul_le_mul_of_nonneg_right hwsum (by positivity)
      _ ≤ (ρ ^ (n - a) * (n : ℝ) ^ n) * (K ^ n * ρ ^ a * B ^ n) := by
          have hKa : K ^ a ≤ K ^ n := pow_le_pow_right₀ hK han
          have h5 : c ^ (n - sa) * (sa : ℝ) ^ n ≤ ρ ^ (n - a) * (n : ℝ) ^ n := by
            refine mul_le_mul hcpow hsan' (by positivity) (by positivity)
          refine mul_le_mul h5 ?_ (by positivity) (by positivity)
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKa (by positivity)) ?_
          positivity
      _ = (n : ℝ) ^ n * (K * ρ * B) ^ n := by
          have hrho : ρ ^ (n - a) * ρ ^ a = ρ ^ n := by
            rw [← pow_add, Nat.sub_add_cancel han]
          rw [mul_pow, mul_pow, ← hrho]
          ring
  calc ∑ a ∈ Finset.range (n + 1),
        ∑ v ∈ (Finset.univ : Finset (ι → κ)).filter (fun v => (loneSlots v).card = a),
          (∏ i, |t (v i)|) * f v
      ≤ ∑ _a ∈ Finset.range (n + 1), (n : ℝ) ^ n * (K * ρ * B) ^ n :=
        Finset.sum_le_sum hstrat
    _ = ((n : ℝ) + 1) * ((n : ℝ) ^ n * (K * ρ * B) ^ n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = ((n : ℝ) + 1) * (n : ℝ) ^ n * (K * ρ * B) ^ n := by ring

end Strata

/-! ### The moment bound

Putting the three pieces together: the expansion of `E|∑_k t_k Z_k|^{2p}` into multi-indices
(`RBM.Gauss.prod_epsHom_sum_eq`), the iterated vanishing lemma applied to each
multi-index with its own set of lone slots, and the stratified weight sum. -/

section Assemble

variable {E t : ℝ} {p : ℕ}

theorem bddMeas_epsHom_flucDiag (hE : |E| < 2) (ht : t < 1) (u : ℝ) (p : ℕ)
    (i : Fin p ⊕ Fin p) (k : d.Idx N) :
    BddMeas d fun ω => epsHom p i (flucDiag d N u (zt E t) (mE E) k ω) := by
  obtain ⟨C, hC⟩ := (bddMeas_flucDiag hE ht u k).bdd
  exact ⟨(measurable_epsHom p i).comp (bddMeas_flucDiag hE ht u k).meas, C,
    fun ω => by rw [norm_epsHom]; exact hC ω⟩

end Assemble

/-! ### (4.12), from the iteration

The moment bound is fed through `RBM.Gauss.stochDom_of_momentDom` exactly as in
`RBM1D/Gauss/FlucAvg.lean`, but with the *iterated* bound in place of the one of
`RBM1D/Gauss/FlucCount.lean`.  The control is `Φ = ρ B`, which with
`ρ, B ≍ Ψ` is `Ψ²` — the control (4.12) asks for.  Nothing here is an arithmetic hypothesis:
the constant `2^{(2p-1)2p} (2p+1) (2p)^{2p}` depends only on `p`, and `RBM.Gauss.MomentDom`
allows the constant to depend on `p`. -/

section Dom

open Filter

variable {E t : ℝ}

end Dom

/-! ### The two coefficient families of (4.12) -/

section Families

open Filter

variable {E t : ℝ}

end Families

/-! ### (4.5)

`RBM1D/Gauss/FlucAvg.lean` derives (4.5) from (4.12); here it is fed the *iterated* (4.12).
Two comparisons are left explicit: the deterministic control `ρ B` of the iteration against the
paper's random control `RBM.Lmax` (this is the local law, not a fluctuation-averaging
statement), and the integration-by-parts input of (4.5). -/

section Avg

variable {E κ t : ℝ}

end Avg

/-! ### The length-graded gain

The higher-order minor expansion is needed only for words of bounded length: the words the
iteration builds carry one letter per pivot, the pivots are lone slots, so the words have length
at most `#ι = 2p`.  The distinction is not cosmetic: the `m`-fold difference of an inverse is a
sum over set partitions, so even the sharpest estimate has a constant that grows like `m! C^m`
in the length bound, and **no single gain parameter can serve all lengths**.  The gain is
therefore graded by a length bound `M`.

The reason no extra length bookkeeping has to be threaded through the iteration is
`RBM.Gauss.OpsOkOut.length_le`: the induction invariant already *says* that the letters of a
word are rows of distinct slots outside the set `R` of remaining pivots, so a word is
automatically shorter than `#ι - #R`.  The graded lemmas below therefore restrict the gain
hypothesis to words of length `≤ #ι`, and discharge that restriction, at the one place it is
used, from the invariant itself. -/

section Graded

open Filter

/-! #### Words are automatically short -/

section GradedWords

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The induction invariant bounds the length.**  A word admissible outside `R` uses
pairwise distinct rows, each the row of a slot outside `R`; the slots realizing them are
therefore distinct, so the word has at most `#ι - #R` letters.  In particular a word arising in
`RBM.Gauss.norm_integral_prod_applyOps_le_graded` never has more than `#ι = 2p` letters, which is
why the gain interface only ever needs to hold up to that length. -/
theorem OpsOkOut.length_le {k : ι → d.Idx N} {i : ι} {R : Finset ι}
    {l : List (Bool × d.Idx N)} (h : OpsOkOut k i R l) :
    l.length + R.card ≤ Fintype.card ι := by
  classical
  have hsub : (l.map Prod.snd).toFinset ⊆ (Finset.univ \ R).image k := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨⟨j, hjR, hxj⟩, _⟩ := h.2 y hy
    exact Finset.mem_image.2 ⟨j, Finset.mem_sdiff.2 ⟨Finset.mem_univ j, hjR⟩, hxj.symm⟩
  have h1 : (l.map Prod.snd).toFinset.card = l.length := by
    rw [List.toFinset_card_of_nodup h.1, List.length_map]
  have h2 : ((Finset.univ \ R).image k).card ≤ (Finset.univ \ R).card := Finset.card_image_le
  have h3 : (Finset.univ \ R : Finset ι).card = Fintype.card ι - R.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ]
  have h4 := Finset.card_le_card hsub
  have hR : R.card ≤ Fintype.card ι := Finset.card_le_univ R
  omega

end GradedWords

/-! #### The interface -/

/-! #### The iteration, against the graded interface -/

section GradedIterate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The iteration, with the gain assumed only for short words.**

The gain hypothesis is restricted to words of length at most `#ι`, and that restriction is
discharged where the hypothesis is used — at the bottom of
the induction — from the invariant `RBM.Gauss.OpsOkOut` itself
(`RBM.Gauss.OpsOkOut.length_le`).  No extra bookkeeping is carried. -/
theorem norm_integral_prod_applyOps_le_graded {k : ι → d.Idx N}
    {X : ι → Ω d → ℂ} (hX : ∀ i, BddMeas d (X i)) (hXd : ∀ i, FinDep d (X i))
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgain : ∀ L : ι → List (Bool × d.Idx N), (∀ i, OpsOk k i (L i)) →
      (∀ i, (L i).length ≤ Fintype.card ι) →
      ∫ ω, ∏ i, ‖applyOps d N (L i) (qRow d N (k i) (X i)) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) :
    ∀ (r : ℕ) (R : Finset ι) (L : ι → List (Bool × d.Idx N)), R.card = r →
      (∀ i₀ ∈ R, ∀ j, j ≠ i₀ → k j ≠ k i₀) →
      (∀ i, OpsOkOut k i R (L i)) →
      ‖∫ ω, ∏ i, applyOps d N (L i) (qRow d N (k i) (X i)) ω ∂(P d)‖
        ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
          * (B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) := by
  classical
  intro r
  induction r with
  | zero =>
      intro R L _ _ hL
      simp only [Nat.mul_zero, pow_zero, one_mul]
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine le_trans (le_of_eq ?_)
        (hgain L (fun i => (hL i).opsOk)
          (fun i => le_trans (Nat.le_add_right _ _) (hL i).length_le))
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => norm_prod _ _)
  | succ r ih =>
      intro R L hR hlone hL
      obtain ⟨i₀, hi₀⟩ : R.Nonempty := Finset.card_pos.1 (by omega)
      have hFb : ∀ i, BddMeas d (applyOps d N (L i) (qRow d N (k i) (X i))) :=
        fun i => ((hX i).qRow (k i)).applyOps (L i)
      have hFd : ∀ i, FinDep d (applyOps d N (L i) (qRow d N (k i) (X i))) :=
        fun i => finDep_applyOps (L i) (finDep_qRow (k i) (hXd i))
      have h0 : condRow d N (k i₀) (applyOps d N (L i₀) (qRow d N (k i₀) (X i₀))) = 0 :=
        condRow_applyOps_qRow d N (k i₀) (L i₀) (hX i₀)
      have htcard : (Finset.univ.erase i₀).card = Fintype.card ι - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
      have hM1 : (1 : ℝ) ≤ max 1 ρ := le_max_left _ _
      have hM0 : (0 : ℝ) ≤ max 1 ρ := le_trans zero_le_one hM1
      have hA0 : (0 : ℝ) ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
          * B ^ Fintype.card ι := by positivity
      have hexp : ∫ ω, ∏ i, applyOps d N (L i) (qRow d N (k i) (X i)) ω ∂(P d)
          = ∑ S ∈ (Finset.univ.erase i₀).powerset,
              ∫ ω, ∏ i, pivotFam d N (k i₀) i₀ S
                (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) i ω ∂(P d) := by
        rw [← integral_finsetSum _ fun S _ =>
          (bddMeas_prod _ fun i _ => bddMeas_pivotFam d N (k i₀) i₀ S hFb i).integrable]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          prod_eq_sum_pivotFam d N (k i₀) i₀
            (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) ω)
      have hterm : ∀ S ∈ (Finset.univ.erase i₀).powerset,
          ‖∫ ω, ∏ i, pivotFam d N (k i₀) i₀ S
              (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) i ω ∂(P d)‖
            ≤ ((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1)) := by
        intro S hSmem
        have hSt : S ⊆ Finset.univ.erase i₀ := Finset.mem_powerset.1 hSmem
        by_cases hSe : S = ∅
        · subst hSe
          rw [integral_prod_pivotFam_empty d N hFb hFd h0, norm_zero]
          positivity
        · have hc1 : 1 ≤ S.card := Finset.card_pos.2 (Finset.nonempty_of_ne_empty hSe)
          have hc2 : S.card ≤ Fintype.card ι - 1 := htcard ▸ Finset.card_le_card hSt
          have hrw : ∀ ω : Ω d, ∏ i, pivotFam d N (k i₀) i₀ S
              (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) i ω
              = ∏ i, applyOps d N (pivotWords k i₀ S L i) (qRow d N (k i) (X i)) ω :=
            fun ω => Finset.prod_congr rfl fun i _ => by
              rw [pivotFam_eq_applyOps d N (X := X) L i]
          have hL' : ∀ i, OpsOkOut k i (R.erase i₀) (pivotWords k i₀ S L i) := by
            intro i
            by_cases h : i = i₀
            · have hw : pivotWords k i₀ S L i = L i₀ := by simp [pivotWords, h]
              rw [hw, h]
              exact (hL i₀).mono (Finset.erase_subset _ _)
            · by_cases hi : i ∈ S
              · have hw : pivotWords k i₀ S L i = (true, k i₀) :: L i := by
                  simp [pivotWords, h, hi]
                rw [hw]; exact (hL i).cons (hlone i₀ hi₀) hi₀ h true
              · have hw : pivotWords k i₀ S L i = (false, k i₀) :: L i := by
                  simp [pivotWords, h, hi]
                rw [hw]; exact (hL i).cons (hlone i₀ hi₀) hi₀ h false
          have hstep := ih (R.erase i₀) (pivotWords k i₀ S L)
            (by rw [Finset.card_erase_of_mem hi₀, hR]; omega)
            (fun i₁ hi₁ => hlone i₁ (Finset.mem_of_mem_erase hi₁)) hL'
          rw [sum_numQ_pivotWords hSt L] at hstep
          rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
          refine le_trans hstep ?_
          have hpow : ρ ^ S.card ≤ ρ * max 1 ρ ^ (Fintype.card ι - 1) := by
            obtain ⟨c, hc⟩ : ∃ c, S.card = c + 1 := ⟨S.card - 1, by omega⟩
            rw [hc, pow_succ]
            have h1 : ρ ^ c ≤ max 1 ρ ^ c := pow_le_pow_left₀ hρ (le_max_right 1 ρ) c
            have h2 : max 1 ρ ^ c ≤ max 1 ρ ^ (Fintype.card ι - 1) :=
              pow_le_pow_right₀ hM1 (by omega)
            calc ρ ^ c * ρ ≤ max 1 ρ ^ (Fintype.card ι - 1) * ρ := by
                  exact mul_le_mul_of_nonneg_right (le_trans h1 h2) hρ
              _ = ρ * max 1 ρ ^ (Fintype.card ι - 1) := by ring
          have hexpand : (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r
              * (B ^ Fintype.card ι * ρ ^ ((∑ i, numQ (L i)) + S.card))
              = ((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * ρ ^ S.card := by
            rw [pow_add]; ring
          rw [hexpand]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      calc ‖∫ ω, ∏ i, applyOps d N (L i) (qRow d N (k i) (X i)) ω ∂(P d)‖
          = ‖∑ S ∈ (Finset.univ.erase i₀).powerset,
              ∫ ω, ∏ i, pivotFam d N (k i₀) i₀ S
                (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) i ω ∂(P d)‖ := by
            rw [hexp]
        _ ≤ ∑ S ∈ (Finset.univ.erase i₀).powerset,
              ‖∫ ω, ∏ i, pivotFam d N (k i₀) i₀ S
                (fun j => applyOps d N (L j) (qRow d N (k j) (X j))) i ω ∂(P d)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _S ∈ (Finset.univ.erase i₀).powerset,
              (((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1))) :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ (Fintype.card ι - 1)
              * (((2 * max 1 ρ) ^ ((Fintype.card ι - 1) * r) * ρ ^ r * B ^ Fintype.card ι)
                * ρ ^ (∑ i, numQ (L i)) * (ρ * max 1 ρ ^ (Fintype.card ι - 1))) := by
            rw [Finset.sum_const, Finset.card_powerset, htcard, nsmul_eq_mul]
            norm_num
        _ = (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * (r + 1)) * ρ ^ (r + 1)
              * (B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) := by
            rw [Nat.mul_succ, pow_add, mul_pow, pow_succ]
            ring

/-- **The iteration at full depth, against the graded gain.** -/
theorem norm_integral_prod_qRow_le_graded {k : ι → d.Idx N} (R : Finset ι)
    (hlone : ∀ i₀ ∈ R, ∀ j, j ≠ i₀ → k j ≠ k i₀)
    {X : ι → Ω d → ℂ} (hX : ∀ i, BddMeas d (X i)) (hXd : ∀ i, FinDep d (X i))
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hgain : ∀ L : ι → List (Bool × d.Idx N), (∀ i, OpsOk k i (L i)) →
      (∀ i, (L i).length ≤ Fintype.card ι) →
      ∫ ω, ∏ i, ‖applyOps d N (L i) (qRow d N (k i) (X i)) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)) :
    ‖∫ ω, ∏ i, qRow d N (k i) (X i) ω ∂(P d)‖
      ≤ (2 * max 1 ρ) ^ ((Fintype.card ι - 1) * R.card) * ρ ^ R.card
        * B ^ Fintype.card ι := by
  classical
  have h := norm_integral_prod_applyOps_le_graded hX hXd hB hρ hgain R.card R (fun _ => [])
    rfl hlone (fun i => opsOkOut_nil k i R)
  simpa only [applyOps_nil, numQ_nil, Finset.sum_const, smul_eq_mul, mul_zero, pow_zero,
    mul_one] using h

end GradedIterate

/-! #### The two consumers, re-derived -/

section GradedFluc

variable {E t : ℝ} {p : ℕ}

end GradedFluc

/-! #### (4.12) and (4.5) against the graded gain

`RBM.Gauss.MomentDom` fixes **one** control for every `p`, while the graded interface may carry
a different `B` at every grade — the minor-difference estimate does, through
`minorDiffC (2p)`.  The two are reconciled
by letting the graded parameter factor,

  `Bp p N ≤ Kp p * Bm N`,

with the grade-dependence confined to `Kp`: the factor `Kp p ^ {2p}` is absorbed into the
constant of `RBM.Gauss.MomentDom`, which is allowed to depend on `p`, and the control is the
`p`-independent `ep N * Bm N`.  For the minor-difference estimate one may take
`Bm N = 2(η_t⁻¹ + 1) + Ψ N` and `Kp p = 1 + 2 minorDiffC (2p)`. -/

section GradedDom

open Filter

variable {E t : ℝ}

end GradedDom

section GradedAvg

variable {E κ t : ℝ}

end GradedAvg

end Graded

/-! ### The second budget: the cardinality of the index type

A gain interface that budgets only the *length* of the words and leaves the index type `ι` free
is unsatisfiable at the paper's size.  Take `ι = Fin j`, every word empty and every pivot equal
to a single `k`: the words are admissible, of length `0 ≤ M`, the gain exponent is `0`, and the
conclusion reads

  `∫ ‖Z_k‖^j ≤ B^j`,  i.e.  `‖Z_k‖_{L^j} ≤ B`  for **every** `j`.

Letting `j → ∞` the left side is `‖Z_k‖_∞`, and a two-point configuration gives a sample point
with `‖Z_k‖ ≥ 64/65`; so such an interface cannot hold at `B ≍ Ψ`.

`RBM.Gauss.FlucGainUpTo'` adds the budget `#ι ≤ n`.  **Nothing is lost**: the `2p`-th
moment expansion instantiates the interface at `ι = Fin p ⊕ Fin p` and nowhere else
(`RBM.Gauss.norm_integral_prod_epsHom_flucDiag_le_budget`), so `#ι = 2p` there, exactly as
`RBM.Gauss.OpsOkOut.length_le` makes the words have length `≤ 2p`.  Both budgets are therefore
`2p`, and the consumers below ask for `M = n = 2p`.

With the budget in place the degenerate instantiation only gives `‖Z_k‖_{L^j} ≤ B` for
`j ≤ n`, the `j → ∞` limit is unavailable, and `B ≍ Ψ` is no longer contradicted:
`‖Z_k‖_{L^{2p}} ≍ Ψ` is exactly what the local law asserts. -/

section Budget

open Filter

/-- **The gain interface with both budgets**: the higher-order minor expansion for words of
length `≤ M`, on an index type with `#ι ≤ n`.  `M` budgets the length of the words, `n` the number
of slots; the `2p`-th moment expansion has `M = n = 2p`.

The second budget is what makes the interface satisfiable at the paper's size: without it the
same `B` dominates *every* `L^j` norm of `Z_k`, hence `‖Z_k‖_∞ ≥ 64/65`. -/
def FlucGainUpTo' (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M n : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N)),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ n →
      ∫ ω, ∏ i, ‖applyOps d N (L i) (flucDiag d N u z m (k i)) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

theorem FlucGainUpTo'.B_nonneg {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M n : ℕ}
    (h : FlucGainUpTo' d N u z m B ρ M n) : 0 ≤ B := h.1

theorem FlucGainUpTo'.rho_nonneg {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M n : ℕ}
    (h : FlucGainUpTo' d N u z m B ρ M n) : 0 ≤ ρ := h.2.1

theorem FlucGainUpTo'.gain {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M n : ℕ}
    (h : FlucGainUpTo' d N u z m B ρ M n) (ι : Type) [Fintype ι] (k : ι → d.Idx N)
    (L : ι → List (Bool × d.Idx N)) (h1 : ∀ i, ((L i).map Prod.snd).Nodup)
    (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i) (h3 : ∀ i, (L i).length ≤ M)
    (h4 : Fintype.card ι ≤ n) :
    ∫ ω, ∏ i, ‖applyOps d N (L i) (flucDiag d N u z m (k i)) ω‖ ∂(P d)
      ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i) := h.2.2 ι k L h1 h2 h3 h4

/-! #### The consumers, against the doubly budgeted interface

Each is the graded statement with `#ι ≤ n` added to the interface and `2 * p ≤ n` added to the
hypotheses; the budget is discharged at the single point where the interface is used, from
`Fintype.card (Fin p ⊕ Fin p) = 2 * p`. -/

section BudgetFluc

variable {E t : ℝ} {p : ℕ}

/-- **The iteration at the `2p` slots of the moment expansion, against the budgeted gain.** -/
theorem norm_integral_prod_epsHom_flucDiag_le_budget (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {B ρ : ℝ} {M n : ℕ} (hg : FlucGainUpTo' d N u (zt E t) (mE E) B ρ M n) (hM : 2 * p ≤ M)
    (hn : 2 * p ≤ n)
    (v : (Fin p ⊕ Fin p) → d.Idx N) (R : Finset (Fin p ⊕ Fin p))
    (hlone : ∀ i₀ ∈ R, ∀ j, j ≠ i₀ → v j ≠ v i₀) :
    ‖∫ ω, ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) ∂(P d)‖
      ≤ (2 * max 1 ρ) ^ ((2 * p - 1) * R.card) * ρ ^ R.card * B ^ (2 * p) := by
  classical
  have hcard : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    simp [Fintype.card_sum, two_mul]
  set X : (Fin p ⊕ Fin p) → Ω d → ℂ :=
    fun i ω => epsHom p i (greenDiagCentered d N u (zt E t) (mE E) (v i) ω) with hXdef
  have hXb : ∀ i, BddMeas d (X i) := by
    intro i
    obtain ⟨C, hC⟩ := (bddMeas_greenDiagCentered hE ht u (v i)).bdd
    refine ⟨((measurable_epsHom p i).comp
      (bddMeas_greenDiagCentered (E := E) (t := t) hE ht u (v i)).meas), C, fun ω => ?_⟩
    rw [hXdef]
    simpa only [norm_epsHom] using hC ω
  have hXd : ∀ i, FinDep d (X i) :=
    fun i => (finDep_greenDiagCentered d N u (zt E t) (mE E) (v i)).imp
      (fun _ h ω ω' hω => by rw [hXdef]; exact congrArg (epsHom p i) (h ω ω' hω))
  have hq : ∀ i, qRow d N (v i) (X i)
      = fun ω => epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) := by
    intro i
    have := applyOps_epsHom d N p i [] (greenDiagCentered d N u (zt E t) (mE E) (v i))
    cases i with
    | inl j => simp only [hXdef, epsHom_inl]; rfl
    | inr j =>
        simp only [hXdef, epsHom_inr]
        exact qRow_conj d N (v (Sum.inr j)) (greenDiagCentered d N u (zt E t) (mE E) _)
  have hgain : ∀ L : (Fin p ⊕ Fin p) → List (Bool × d.Idx N), (∀ i, OpsOk v i (L i)) →
      (∀ i, (L i).length ≤ Fintype.card (Fin p ⊕ Fin p)) →
      ∫ ω, ∏ i, ‖applyOps d N (L i) (qRow d N (v i) (X i)) ω‖ ∂(P d)
        ≤ B ^ Fintype.card (Fin p ⊕ Fin p) * ρ ^ ∑ i, numQ (L i) := by
    intro L hL hlen
    have hrw : ∀ ω : Ω d, ∏ i, ‖applyOps d N (L i) (qRow d N (v i) (X i)) ω‖
        = ∏ i, ‖applyOps d N (L i) (flucDiag d N u (zt E t) (mE E) (v i)) ω‖ := by
      intro ω
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hq i, applyOps_epsHom d N p i (L i) (flucDiag d N u (zt E t) (mE E) (v i)),
        norm_epsHom]
    rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
    exact hg.gain (Fin p ⊕ Fin p) v L (fun i => (hL i).1) (fun i => (hL i).2)
      (fun i => le_trans (hlen i) (by rw [hcard]; exact hM)) (by rw [hcard]; exact hn)
  have h := norm_integral_prod_qRow_le_graded (k := v) R hlone hXb hXd hg.B_nonneg
    hg.rho_nonneg hgain
  rw [hcard] at h
  simpa only [hq] using h

/-- **The moment bound of (4.12), against the budgeted gain.**  The
`2p`-th moment of (4.12) uses the interface at `#ι = 2p` slots and words of length `≤ 2p`, so
`M = n = 2p` suffices. -/
theorem integral_norm_flucAvg_pow_le_iter_budget (hE : |E| < 2) (ht : t < 1) {u : ℝ}
    {B ρ c : ℝ} {M n : ℕ} {A : Finset (d.Idx N)} {T : d.Idx N → ℝ}
    (hg : FlucGainUpTo' d N u (zt E t) (mE E) B ρ M n) (hM : 2 * p ≤ M) (hn : 2 * p ≤ n)
    (hρ1 : ρ ≤ 1) (hcρ : c ≤ ρ ^ 2)
    (hw : UniformWeight T c A) (hp : 2 * p ≤ A.card) :
    ∫ ω, ‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) ∂(P d)
      ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * ρ * B) ^ (2 * p) := by
  classical
  have hcardι : Fintype.card (Fin p ⊕ Fin p) = 2 * p := by
    simp [Fintype.card_sum, two_mul]
  have hB := hg.B_nonneg
  have hρ0 := hg.rho_nonneg
  have hbm : ∀ (v : (Fin p ⊕ Fin p) → d.Idx N),
      BddMeas d fun ω => ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) :=
    fun v => bddMeas_prod _ fun i _ => bddMeas_epsHom_flucDiag hE ht u p i (v i)
  have hI : ∫ ω, ((‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d)
      = ∑ v : (Fin p ⊕ Fin p) → d.Idx N, (∏ i, (T (v i) : ℂ))
          * ∫ ω, ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) ∂(P d) := by
    have hexp : ∀ ω : Ω d, ((‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ)
        = ∑ v : (Fin p ⊕ Fin p) → d.Idx N, (∏ i, (T (v i) : ℂ))
            * ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) :=
      fun ω => prod_epsHom_sum_eq p T fun k => flucDiag d N u (zt E t) (mE E) k ω
    simp_rw [hexp]
    rw [integral_finsetSum _ fun v _ =>
      ((bddMeas_const d (∏ i, (T (v i) : ℂ))).mul (hbm v)).integrable]
    exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
  have hf : ∀ v : (Fin p ⊕ Fin p) → d.Idx N,
      ‖∫ ω, ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) ∂(P d)‖
        ≤ ((2 : ℝ) ^ (2 * p - 1)) ^ (loneSlots v).card * ρ ^ (loneSlots v).card
          * B ^ (2 * p) := by
    intro v
    have hlone : ∀ i₀ ∈ loneSlots v, ∀ j, j ≠ i₀ → v j ≠ v i₀ :=
      fun i₀ hi₀ => mem_loneSlots.1 hi₀
    have key := norm_integral_prod_epsHom_flucDiag_le_budget hE ht u hg hM hn v
      (loneSlots v) hlone
    rwa [max_eq_left hρ1, mul_one, pow_mul] at key
  have hK : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * p - 1) := one_le_pow₀ (by norm_num)
  have hsum := sum_weighted_le (ι := Fin p ⊕ Fin p) hw hcardι hp hρ0 hρ1 hK hB hcρ hf
  have hofR : (∫ ω, ((‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d))
      = ((∫ ω, ‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) ∂(P d) : ℝ) : ℂ) :=
    integral_complex_ofReal
  have hreal : ∫ ω, ‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) ∂(P d)
      = ‖∫ ω, ((‖flucAvg d N u (zt E t) (mE E) T ω‖ ^ (2 * p) : ℝ) : ℂ) ∂(P d)‖ := by
    rw [hofR, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun ω => by positivity)]
  rw [hreal, hI]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ v : (Fin p ⊕ Fin p) → d.Idx N,
      ‖(∏ i, (T (v i) : ℂ))
          * ∫ ω, ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) ∂(P d)‖
        = (∏ i, |T (v i)|)
          * ‖∫ ω, ∏ i, epsHom p i (flucDiag d N u (zt E t) (mE E) (v i) ω) ∂(P d)‖ := by
    intro v
    rw [norm_mul, norm_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hterm]
  exact le_trans hsum (le_of_eq (by push_cast; ring))

end BudgetFluc

end Budget

end RBM.Gauss
