/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MinorDiffGain
import RBM1D.Gauss.Eq45FlowInputs
import RBM1D.Gauss.CondStableFlow

/-!
# Conditionalizing the minor-difference gain on the good event

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the size of the iterated minor differences, **on the event `Ω(t,c)` of (4.1)**
rather than at every sample point.

## What was wrong upstream

`RBM1D/Gauss/MinorDiffGain.lean` proves its estimates from a hypothesis
`hgood : ∀ ω, MinorGoodLe d N u z m ω Ψ M`.  That hypothesis is **false** (T164, T172): at
`ω = 0` and `E = 0` one has `‖G^{(S)}_{aa} - m‖ = u/(1-u)` for every `N`, and at
`ω = Function.update 0 ⟨N,k,k,true⟩ 40` the field `inv_le` fails outright.  T169/T170 repaired
the *level* quantifier (the budget `M`); what remains, and is done here, is the *sample point*
quantifier.  The paper never states a pointwise form: (4.2)/(4.3) always carry `1_Ω` and are
always `≺`.

## Why an indicator does not work, and what does

`flucDiagSet` **is** `qRow k (…)`, i.e. a conditional expectation, and `applyOps` stacks
further `E_κ` on top of it.  Multiplying the integrand by `1_Ω` therefore does not commute past
the operators and splitting the integral naively is illegitimate.  The legitimate tool is
`RBM.Gauss.norm_condRow_le_split` (`RBM1D/Gauss/CondDom.lean`): off the exceptional set the
integrand obeys the sharp bound, on the whole space the deterministic envelope, and `E_κ` splits
into the two contributions, the second weighted by the probability of the **row section** of the
exceptional set.

## The tower, and why a single exceptional set is not enough

The shape proposed in T164 carries a hypothesis
`hslice : ∀ κ ω, (P d).real (rowSlice d N κ Bad ω) ≤ ε` for a single `Bad`.  That is again a
`∀ ω` statement, and for the good event it is **false**: freeze a row `j ≠ κ` at a huge
diagonal value; then `G_{jj}` is small for *every* configuration of row `κ`, the good event
fails on the whole section, and `(P d).real (rowSlice d N κ Bad ω) = 1`.  Markov
(`RBM.Gauss.meas_measure_rowSlice_ge`) does not repair this, because enlarging `Bad` by the
frozen configurations with a fat section changes the sections again.

What *is* true is the statement one level at a time: `RBM.Gauss.badStep` enlarges a set by the
frozen configurations whose sections are not `ε`-small, and `RBM.Gauss.badTower` iterates it.
`RBM.Gauss.BadFamily` is the resulting interface — monotone, measurable, and `ε`-small sections
of the `j`-th member off the `(j+1)`-st — and `RBM.Gauss.badFamily_badTower` **produces** it for
any measurable base.  `RBM.Gauss.meas_badTower_le` is the price: one factor `(ε + #rows)/ε` per
letter, which is `N^{O(1)}` against a super-polynomially small base, i.e. free for `≺`.

## The estimates

* `RBM.Gauss.norm_applyOps_le_badFamily` — a word of `n` letters applied to a function that is
  sharp off `Bad 0` and enveloped everywhere is sharp off `Bad n`, up to `n · Env · ε`.
* `RBM.Gauss.norm_minorDiff_qList_greenSetDiagCentered_le` — the sharp size of the word's minor
  difference, at **one** sample point (empty word: (4.3); non-empty: the `Δ_κ` calculus).
* `RBM.Gauss.norm_applyOps_minorDiff_flucDiagSet_le_badFamily` — the two combined, using that
  `Δ` commutes with `Q_k`, so the whole factor is the single word `L ++ [(true, k)]` applied to
  a *deterministic* family.
* `RBM.Gauss.integral_prod_applyOps_minorDiff_le_on` — the moment bound, with no `∀ ω`
  hypothesis.  It costs `RBM.Gauss.condCost` on the constant and an additive remainder
  `RBM.Gauss.condEnv ^ #ι · P(Bad_{M+1})`.
* `RBM.Gauss.integral_prod_applyOps_minorDiff_le_goodSetFlow` — the same with every hypothesis
  discharged from `RBM.Gauss.goodSetFlow`, the flow form of (4.1).

## The ceiling, and how T177 breaks it

`RBM.Gauss.integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo` shows that the `B` of
`RBM.Gauss.MinorDiffGainUpTo` dominates every `L^n` norm of `Z_k`, since the index type `ι` of
that interface is unrestricted.  By T172's two-point argument `‖Z_k‖_∞ ≥ 64/65`, so
`B ≍ Ψ` is unattainable there — exactly the ceiling T172 found for `RBM.Gauss.FlucBound`, and
`RBM.Gauss.integral_pow_norm_flucDiag_le_of_flucGainUpTo` (`RBM1D/Gauss/FlucIter.lean`) is the
same statement one level up, for the interface the flow form of (4.5) actually consumes.

**T177 supplies the missing budget** `#ι ≤ n`: `RBM.Gauss.MinorDiffGainUpTo'` and
`RBM.Gauss.FlucGainUpTo'`.  With it the degenerate instantiation stops at `j = n`
(`RBM.Gauss.integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo'`), so `B ≍ Ψ` is no longer
contradicted, and the additive remainder of this file **is** absorbable:
`RBM.Gauss.minorDiffGainUpTo'_of_le_on` packages the conditionalized estimate as an interface,
`RBM.Gauss.flucGainUpTo'_goodSetFlow` produces it from (4.1) alone, and
`RBM.Gauss.eq45Flow_of_goodSetFlow_budget` carries it to `RBM.StepGlue.Eq45Flow`.
`RBM.Gauss.minorDiffGain_budget_hyps_consistent` exhibits explicit parameters at which every
numeric side condition holds at once, at `B ≍ Ψ`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

variable {d : Dims} {N : ℕ}

/-! ### The tower of exceptional sets -/

/-- One step of the tower: enlarge `S` by the frozen configurations whose row-`κ` section of
`S` is not `ε`-small, for some row `κ`. -/
def badStep (d : Dims) (N : ℕ) (ε : ℝ) (S : Set (Ω d)) : Set (Ω d) :=
  S ∪ ⋃ κ : d.Idx N, {ω | ε < (P d).real (rowSlice d N κ S ω)}

theorem subset_badStep (d : Dims) (N : ℕ) (ε : ℝ) (S : Set (Ω d)) : S ⊆ badStep d N ε S :=
  Set.subset_union_left

theorem measurable_measureReal_rowSlice (d : Dims) (N : ℕ) (κ : d.Idx N) {S : Set (Ω d)}
    (hS : MeasurableSet S) : Measurable fun ω => (P d).real (rowSlice d N κ S ω) :=
  (measurable_measure_rowSlice d N κ hS).ennreal_toReal

theorem measurableSet_badStep {ε : ℝ} {S : Set (Ω d)} (hS : MeasurableSet S) :
    MeasurableSet (badStep d N ε S) :=
  hS.union (MeasurableSet.iUnion fun κ =>
    measurableSet_lt measurable_const (measurable_measureReal_rowSlice d N κ hS))

/-- Off `badStep`, every row section of `S` is `ε`-small. -/
theorem measureReal_rowSlice_le_of_notMem_badStep {ε : ℝ} {S : Set (Ω d)} (κ : d.Idx N)
    {ω : Ω d} (hω : ω ∉ badStep d N ε S) : (P d).real (rowSlice d N κ S ω) ≤ ε := by
  by_contra h
  exact hω (Or.inr (Set.mem_iUnion.2 ⟨κ, not_le.1 h⟩))

/-- **The tower.**  `badTower ε S n` is `S` enlarged `n` times. -/
def badTower (d : Dims) (N : ℕ) (ε : ℝ) (S : Set (Ω d)) : ℕ → Set (Ω d)
  | 0 => S
  | j + 1 => badStep d N ε (badTower d N ε S j)

@[simp] theorem badTower_zero (d : Dims) (N : ℕ) (ε : ℝ) (S : Set (Ω d)) :
    badTower d N ε S 0 = S := rfl

@[simp] theorem badTower_succ (d : Dims) (N : ℕ) (ε : ℝ) (S : Set (Ω d)) (j : ℕ) :
    badTower d N ε S (j + 1) = badStep d N ε (badTower d N ε S j) := rfl

/-- **The interface the word estimate consumes.**  A monotone measurable family whose `j`-th
member has `ε`-small row sections off the `(j+1)`-st.

This is the *correct* replacement for a hypothesis `∀ κ ω, (P d).real (rowSlice κ Bad ω) ≤ ε`
with a single set `Bad`: the latter is a `∀ ω` statement of exactly the kind T172 audits, and
for the good event of (4.1) it is false — conditionally on a catastrophic configuration of the
rows other than `κ`, the good event fails with probability one, so its row section is the whole
space.  Enlarging the set by the frozen configurations where that happens is
`RBM.Gauss.badStep`, and it must be done once per letter of the word. -/
structure BadFamily (d : Dims) (N : ℕ) (ε : ℝ) (Bad : ℕ → Set (Ω d)) : Prop where
  /-- Every member is measurable. -/
  meas : ∀ j, MeasurableSet (Bad j)
  /-- The family increases. -/
  mono : ∀ j, Bad j ⊆ Bad (j + 1)
  /-- Off the next member, the row sections of the current one are `ε`-small. -/
  slice : ∀ (j : ℕ) (κ : d.Idx N) {ω : Ω d}, ω ∉ Bad (j + 1) →
    (P d).real (rowSlice d N κ (Bad j) ω) ≤ ε

theorem BadFamily.mono_le {ε : ℝ} {Bad : ℕ → Set (Ω d)} (h : BadFamily d N ε Bad) :
    ∀ {j j' : ℕ}, j ≤ j' → Bad j ⊆ Bad j' := by
  intro j j' hjj'
  induction j' with
  | zero => rw [Nat.le_zero.1 hjj']
  | succ n ih =>
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.1 hlt)).trans (h.mono n)
      · rw [le_antisymm hjj' hge]

/-- **The tower is a `RBM.Gauss.BadFamily`.**  Nothing is assumed about `S` beyond
measurability, so the hypothesis of the word estimate is *produced*, not postulated. -/
theorem badFamily_badTower (d : Dims) (N : ℕ) (ε : ℝ) {S : Set (Ω d)} (hS : MeasurableSet S) :
    BadFamily d N ε (badTower d N ε S) where
  meas := by
    intro j
    induction j with
    | zero => exact hS
    | succ n ih => exact measurableSet_badStep ih
  mono := fun j => subset_badStep d N ε _
  slice := fun j κ _ hω => measureReal_rowSlice_le_of_notMem_badStep κ hω

/-! ### The measure of the tower -/

/-- **One step costs a factor `1 + #rows / ε`**, by Fubini and Markov for the row section
(`RBM.Gauss.meas_measure_rowSlice_ge`).  Stated multiplicatively to avoid division in
`ℝ≥0∞`. -/
theorem meas_badStep_le (d : Dims) (N : ℕ) {ε : ℝ} {S : Set (Ω d)} (hS : MeasurableSet S) :
    ENNReal.ofReal ε * (P d) (badStep d N ε S)
      ≤ (ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞)) * (P d) S := by
  classical
  have hsub : ∀ κ : d.Idx N,
      {ω : Ω d | ε < (P d).real (rowSlice d N κ S ω)}
        ⊆ {ω : Ω d | ENNReal.ofReal ε ≤ (P d) (rowSlice d N κ S ω)} := by
    intro κ ω hω
    exact ENNReal.ofReal_le_of_le_toReal hω.le
  have hstep : ∀ κ : d.Idx N,
      ENNReal.ofReal ε * (P d) {ω : Ω d | ε < (P d).real (rowSlice d N κ S ω)} ≤ (P d) S := by
    intro κ
    refine le_trans (mul_le_mul_right (measure_mono (hsub κ)) _) ?_
    exact meas_measure_rowSlice_ge d N κ hS (ENNReal.ofReal ε)
  have hunion : (P d) (badStep d N ε S)
      ≤ (P d) S + ∑ κ : d.Idx N, (P d) {ω : Ω d | ε < (P d).real (rowSlice d N κ S ω)} := by
    refine le_trans (measure_union_le _ _) (add_le_add_right ?_ _)
    exact measure_iUnion_fintype_le _ _
  calc ENNReal.ofReal ε * (P d) (badStep d N ε S)
      ≤ ENNReal.ofReal ε * ((P d) S
          + ∑ κ : d.Idx N, (P d) {ω : Ω d | ε < (P d).real (rowSlice d N κ S ω)}) :=
        mul_le_mul_right hunion _
    _ = ENNReal.ofReal ε * (P d) S
          + ∑ κ : d.Idx N,
              ENNReal.ofReal ε * (P d) {ω : Ω d | ε < (P d).real (rowSlice d N κ S ω)} := by
        rw [mul_add, Finset.mul_sum]
    _ ≤ ENNReal.ofReal ε * (P d) S + ∑ _κ : d.Idx N, (P d) S :=
        add_le_add_right (Finset.sum_le_sum fun κ _ => hstep κ) _
    _ = (ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞)) * (P d) S := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_mul]

/-- **The tower's measure**: `ε^n P(Bad_n) ≤ (ε + #rows)^n P(Bad_0)`.  Since `P(Bad_0)` is
super-polynomially small (it is the complement of (4.1)) while `#rows ≤ N²` and `ε` is a fixed
negative power of `N`, the whole tower is still super-polynomially small for every fixed
number `n` of letters. -/
theorem meas_badTower_le (d : Dims) (N : ℕ) {ε : ℝ} {S : Set (Ω d)} (hS : MeasurableSet S)
    (n : ℕ) :
    ENNReal.ofReal ε ^ n * (P d) (badTower d N ε S n)
      ≤ (ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ n * (P d) S := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmeas : MeasurableSet (badTower d N ε S n) :=
        (badFamily_badTower d N ε hS).meas n
      calc ENNReal.ofReal ε ^ (n + 1) * (P d) (badTower d N ε S (n + 1))
          = ENNReal.ofReal ε ^ n * (ENNReal.ofReal ε
              * (P d) (badStep d N ε (badTower d N ε S n))) := by
            rw [badTower_succ, pow_succ]; ring
        _ ≤ ENNReal.ofReal ε ^ n
              * ((ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞))
                  * (P d) (badTower d N ε S n)) :=
            mul_le_mul_right (meas_badStep_le d N hmeas) _
        _ = (ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞))
              * (ENNReal.ofReal ε ^ n * (P d) (badTower d N ε S n)) := by ring
        _ ≤ (ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞))
              * ((ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ n * (P d) S) :=
            mul_le_mul_right ih _
        _ = (ENNReal.ofReal ε + (Fintype.card (d.Idx N) : ℝ≥0∞)) ^ (n + 1) * (P d) S := by
            rw [pow_succ]; ring

/-! ### A word applied to a function that is good off the tower -/

/-- Words concatenate. -/
theorem applyOps_append (d : Dims) (N : ℕ) (l₁ l₂ : List (Bool × d.Idx N)) (X : Ω d → ℂ) :
    applyOps d N (l₁ ++ l₂) X = applyOps d N l₁ (applyOps d N l₂ X) := by
  induction l₁ with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [List.cons_append, applyOps_cons_false, ih]
      · simp only [List.cons_append, applyOps_cons_true, ih]

/-- **The conditionalized word estimate.**

If `X` obeys the sharp bound `c` off `Bad 0` and the deterministic envelope `Env` everywhere,
then a word of `n` letters obeys the sharp bound off `Bad n`, up to the additive loss
`n · Env · ε` from the `n` row sections that the conditional expectations integrate over.

This is the tool `RBM.Gauss.MinorDiffGain` was missing.  Multiplying the integrand by an
indicator is *not* available: `RBM.Gauss.flucDiagSet` is itself a `RBM.Gauss.qRow`, and
`RBM.Gauss.applyOps` stacks further `E_κ` on top of it, so an indicator does not commute past
the conditional expectations.  What does pass is `RBM.Gauss.norm_condRow_le_split`: on the good
set the integrand obeys the sharp bound, on the whole space the envelope, and `E_κ` splits
accordingly — at the price of one further enlargement of the exceptional set per letter. -/
theorem norm_applyOps_le_badFamily {X : Ω d → ℂ} (hX : BddMeas d X)
    {Bad : ℕ → Set (Ω d)} {ε Env c : ℝ} (hfam : BadFamily d N ε Bad)
    (hEnv : ∀ ω, ‖X ω‖ ≤ Env) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hgood : ∀ ω ∉ Bad 0, ‖X ω‖ ≤ c) :
    ∀ (l : List (Bool × d.Idx N)) (ω : Ω d), ω ∉ Bad l.length →
      ‖applyOps d N l X ω‖ ≤ 2 ^ numQ l * (c + l.length * Env * ε) := by
  have hEnv0 : 0 ≤ Env := le_trans (norm_nonneg _) (hEnv 0)
  intro l
  induction l with
  | nil => intro ω hω; simpa using hgood ω hω
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      intro ω hω
      have hωl : ω ∉ Bad l.length := fun h => hω (hfam.mono l.length h)
      set A : ℝ := 2 ^ numQ l * (c + l.length * Env * ε) with hA
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hinner : ∀ σ ∉ Bad l.length, ‖applyOps d N l X σ‖ ≤ A * (1 : ℝ) := by
        intro σ hσ; rw [mul_one]; exact ih σ hσ
      have hEnvl : ∀ σ, ‖applyOps d N l X σ‖ ≤ 2 ^ numQ l * Env := fun σ =>
        norm_applyOps_le l hEnv σ
      have hsplit := norm_condRow_le_split (k := κ) (X := applyOps d N l X)
        (hX.applyOps l).meas (f := fun _ : Ω d => (1 : ℝ)) (fun _ => zero_le_one)
        (fun _ => integrable_const 1) hEnvl hA0 (hfam.meas l.length) hinner ω
      have hcr : condRowReal d N κ (fun _ : Ω d => (1 : ℝ)) ω = 1 := by
        rw [condRowReal_const]
      rw [hcr, mul_one] at hsplit
      have hsl := hfam.slice l.length κ hω
      have hEnvpos : (0 : ℝ) ≤ 2 ^ numQ l * Env := by positivity
      have hterm : 2 ^ numQ l * Env * (P d).real (rowSlice d N κ (Bad l.length) ω)
          ≤ 2 ^ numQ l * Env * ε := mul_le_mul_of_nonneg_left hsl hEnvpos
      have hcond : ‖condRow d N κ (applyOps d N l X) ω‖ ≤ A + 2 ^ numQ l * Env * ε := by
        linarith
      have hEe : (0 : ℝ) ≤ 2 ^ numQ l * Env * ε := by positivity
      cases b
      · rw [applyOps_cons_false, numQ_cons_false]
        refine hcond.trans (le_of_eq ?_)
        rw [hA, List.length_cons]
        push_cast
        ring
      · rw [applyOps_cons_true, numQ_cons_true]
        have htri : ‖qRow d N κ (applyOps d N l X) ω‖
            ≤ ‖applyOps d N l X ω‖ + ‖condRow d N κ (applyOps d N l X) ω‖ := by
          rw [qRow_apply]; exact norm_sub_le _ _
        have hgoal : 2 ^ (numQ l + 1) * (c + ((l.length : ℝ) + 1) * Env * ε)
            = 2 * A + 2 * (2 ^ numQ l * Env * ε) := by
          rw [hA]; ring
        have h1 := ih ω hωl
        rw [List.length_cons]
        push_cast
        rw [hgoal]
        linarith

/-! ### The sharp size of the word's minor difference, at one sample point -/

section Words

variable {u : ℝ} {z m : ℂ} {Ψ : ℝ} {M : ℕ}

theorem numQ_append_true (L : List (Bool × d.Idx N)) (k : d.Idx N) :
    numQ (L ++ [(true, k)]) = numQ L + 1 := by
  simp [numQ, List.countP_append]

/-- **Both grades of the gain in one statement**, at a *single* sample point: the word's minor
difference of `G^{(·)}_{kk} - m` is at most `C_M Ψ^{#Q + 1}`.

The empty word is (4.3) itself (`RBM.Gauss.norm_greenSetDiagCentered_le`) and a non-empty word
is the `Δ_κ` calculus (`RBM.Gauss.norm_minorDiff_greenSetDiagCentered_le`).  `ω` appears only
as the point at which the hypothesis and the conclusion are read — no `∀ ω`. -/
theorem norm_minorDiff_qList_greenSetDiagCentered_le {ω : Ω d}
    (hg : MinorGoodLe d N u z m ω Ψ M) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (k : d.Idx N)
    (L : List (Bool × d.Idx N)) (h1 : ((L.map Prod.snd)).Nodup) (h2 : ∀ x ∈ L, x.2 ≠ k)
    (hM : L.length ≤ M) :
    ‖minorDiff d N (qList L) (greenSetDiagCentered d N u z m k) ω‖
      ≤ minorDiffC M * Ψ ^ (numQ L + 1) := by
  classical
  have hlenq : (qList L).length = numQ L := length_qList L
  have hnodup : (qList L).Nodup := qList_nodup h1
  have hne : ∀ y ∈ qList L, y ≠ k := fun y hy => mem_qList_ne h2 hy
  have hCM := one_le_minorDiffC M
  cases hqs : qList L with
  | nil =>
      have hzero : numQ L = 0 := by rw [← hlenq, hqs]; rfl
      rw [hzero, pow_one]
      have hb := norm_greenSetDiagCentered_le hg hΨ0 k ∅ (by simp)
      simp only [minorDiff_nil]
      nlinarith
  | cons κ l' =>
      have hκmem : κ ∈ qList L := by rw [hqs]; exact List.mem_cons_self
      have hkκ : k ≠ κ := Ne.symm (hne κ hκmem)
      have hnd' : (κ :: l').Nodup := by rw [← hqs]; exact hnodup
      have hkl : ∀ x ∈ l', x ≠ k := by
        intro x hx
        exact hne x (by rw [hqs]; exact List.mem_cons_of_mem _ hx)
      have hm : numQ L = l'.length + 1 := by rw [← hlenq, hqs]; simp [List.length_cons]
      have hq : numQ L ≤ L.length := List.countP_le_length
      have hlM1 : l'.length + 1 ≤ M := by omega
      have hlM : l'.length ≤ M := by omega
      rw [hm]
      refine le_trans (norm_minorDiff_greenSetDiagCentered_le hg hΨ0 hΨ1 k κ l'
        hkκ hnd' hkl hlM1) ?_
      have hmono := minorDiffC_mono hlM
      have hpow : (0 : ℝ) ≤ Ψ ^ (l'.length + 2) := pow_nonneg hΨ0 _
      have : l'.length + 1 + 1 = l'.length + 2 := by omega
      rw [this]
      exact mul_le_mul_of_nonneg_right hmono hpow

end Words

/-! ### The conditionalized estimate for one factor -/

section Factor

variable {E t : ℝ}

/-- **One factor of the `2p`-th moment, conditionalized.**

The object is `applyOps L (Δ_{qList L} Z^{(·)}_k)`.  Since `Z^{(S)}_k = Q_k (G^{(S)}_{kk} - m)`
and `Δ` commutes with `Q_k` (`RBM.Gauss.minorDiff_flucDiagSet_eq`), the whole object is the
*single* word `L ++ [(true, k)]` applied to the **deterministic** family
`Δ_{qList L} (G^{(·)}_{kk} - m)`, which is where the good event enters pointwise.
`RBM.Gauss.norm_applyOps_le_badFamily` then carries it through the `#L + 1` conditional
expectations. -/
theorem norm_applyOps_minorDiff_flucDiagSet_le_badFamily
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hε : 0 ≤ ε)
    {M : ℕ} {Bad : ℕ → Set (Ω d)} (hfam : BadFamily d N ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d N u (zt E t) (mE E) ω Ψ M)
    (k : d.Idx N) (L : List (Bool × d.Idx N))
    (h1 : ((L.map Prod.snd)).Nodup) (h2 : ∀ x ∈ L, x.2 ≠ k) (hM : L.length ≤ M)
    (ω : Ω d) (hω : ω ∉ Bad (L.length + 1)) :
    ‖applyOps d N L (minorDiff d N (qList L) (flucDiagSet d N u (zt E t) (mE E) k)) ω‖
      ≤ 2 ^ (numQ L + 1)
        * (minorDiffC M * Ψ ^ (numQ L + 1)
            + ((L.length : ℝ) + 1) * (2 ^ numQ L * ((etaT E t)⁻¹ + 1)) * ε) := by
  classical
  set Y : Ω d → ℂ :=
    minorDiff d N (qList L) (greenSetDiagCentered d N u (zt E t) (mE E) k) with hY
  have hrw : applyOps d N L (minorDiff d N (qList L) (flucDiagSet d N u (zt E t) (mE E) k))
      = applyOps d N (L ++ [(true, k)]) Y := by
    rw [minorDiff_flucDiagSet_eq hE ht u k (qList L), applyOps_append, hY]
    rfl
  have hYbdd : BddMeas d Y :=
    bddMeas_minorDiff _ _ fun S => bddMeas_greenSetDiagCentered hE ht u k S
  have hYenv : ∀ ω', ‖Y ω'‖ ≤ 2 ^ numQ L * ((etaT E t)⁻¹ + 1) := by
    intro ω'
    have hb := norm_minorDiff_le (qList L) (greenSetDiagCentered d N u (zt E t) (mE E) k)
      (fun S ω'' => norm_greenSetDiagCentered_le_env hE ht u k S ω'') ω'
    rwa [length_qList] at hb
  have hYgood : ∀ ω' ∉ Bad 0, ‖Y ω'‖ ≤ minorDiffC M * Ψ ^ (numQ L + 1) := fun ω' hω' =>
    norm_minorDiff_qList_greenSetDiagCentered_le (hgood ω' hω') hΨ0 hΨ1 k L h1 h2 hM
  have hc0 : 0 ≤ minorDiffC M * Ψ ^ (numQ L + 1) :=
    mul_nonneg (minorDiffC_nonneg M) (pow_nonneg hΨ0 _)
  have hlen : (L ++ [(true, k)]).length = L.length + 1 := by simp
  have hωa : ω ∉ Bad ((L ++ [(true, k)]).length) := by rwa [hlen]
  have hkey := norm_applyOps_le_badFamily hYbdd hfam hYenv hc0 hε hYgood
    (L ++ [(true, k)]) ω hωa
  rw [numQ_append_true, hlen] at hkey
  rw [hrw]
  refine hkey.trans (le_of_eq ?_)
  push_cast
  ring

end Factor

/-! ### The conditionalized moment bound -/

section Moment

variable {E t : ℝ}

/-- A pointwise family of bounds **valid only off a measurable set** gives the expectation
bound, with the set's probability charged at the deterministic envelope. -/
theorem integral_prod_norm_le_of_bounds_on {ι : Type*} [Fintype ι] {F : ι → Ω d → ℂ}
    (hF : ∀ i, BddMeas d (F i)) {b : ι → ℝ} {Genv : ℝ} {S : Set (Ω d)}
    (hS : MeasurableSet S) (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ ω ∉ S, ∀ i, ‖F i ω‖ ≤ b i) (hG : ∀ ω, ∏ i, ‖F i ω‖ ≤ Genv) :
    ∫ ω, ∏ i, ‖F i ω‖ ∂(P d) ≤ (∏ i, b i) + Genv * (P d).real S := by
  classical
  have hnorm : (fun ω : Ω d => ∏ i, ‖F i ω‖) = fun ω => ‖∏ i, F i ω‖ :=
    funext fun ω => (norm_prod _ _).symm
  have hint : Integrable (fun ω : Ω d => ∏ i, ‖F i ω‖) (P d) := by
    rw [hnorm]; exact (bddMeas_prod Finset.univ fun i _ => hF i).integrable.norm
  have hindint : Integrable (S.indicator fun _ : Ω d => Genv) (P d) :=
    (integrable_const Genv).indicator hS
  have hb0' : (0 : ℝ) ≤ ∏ i, b i := Finset.prod_nonneg fun i _ => hb0 i
  have hpt : ∀ ω : Ω d, ∏ i, ‖F i ω‖ ≤ (∏ i, b i) + S.indicator (fun _ => Genv) ω := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      linarith [hG ω]
    · rw [Set.indicator_of_notMem hω, add_zero]
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hb ω hω i
  calc ∫ ω, ∏ i, ‖F i ω‖ ∂(P d)
      ≤ ∫ ω, ((∏ i, b i) + S.indicator (fun _ => Genv) ω) ∂(P d) :=
        integral_mono hint ((integrable_const _).add hindint) hpt
    _ = (∏ i, b i) + Genv * (P d).real S := by
        rw [integral_add (integrable_const _) hindint, integral_indicator_const _ hS,
          smul_eq_mul, mul_comm ((P d).real S) Genv]
        simp

/-- The deterministic envelope of one factor, for words of length at most `M`:
`2^{2M+1}(η_u⁻¹ + 1)`. -/
noncomputable def condEnv (E t : ℝ) (M : ℕ) : ℝ := 2 ^ (2 * M + 1) * ((etaT E t)⁻¹ + 1)

theorem condEnv_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) : 0 ≤ condEnv E t M := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  unfold condEnv
  positivity

/-- **The price of conditionalizing**, per factor: the `#L + 1` conditional expectations each
integrate over a row section of the exceptional set, and each such section is only `ε`-small.
Dividing by `(2Ψ)^M` is what puts the loss into the *constant* `B` of the graded interface
rather than into the gain `ρ`. -/
noncomputable def condCost (E t : ℝ) (M : ℕ) (Ψ ε : ℝ) : ℝ :=
  ((M : ℝ) + 1) * condEnv E t M * ε * ((2 * Ψ) ^ M)⁻¹

theorem condCost_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ ε : ℝ} (hΨ0 : 0 ≤ Ψ)
    (hε : 0 ≤ ε) : 0 ≤ condCost E t M Ψ ε := by
  have := condEnv_nonneg hE ht (E := E) (t := t) M
  unfold condCost
  have h2 : (0 : ℝ) ≤ ((2 * Ψ) ^ M)⁻¹ := by positivity
  have h3 : (0 : ℝ) ≤ ((M : ℝ) + 1) := by positivity
  positivity

theorem norm_applyOps_minorDiff_flucDiagSet_le_condEnv (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {M : ℕ} (k : d.Idx N) (L : List (Bool × d.Idx N)) (hM : (L).length ≤ M) (ω : Ω d) :
    ‖applyOps d N L (minorDiff d N (qList L) (flucDiagSet d N u (zt E t) (mE E) k)) ω‖
      ≤ condEnv E t M := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have hq : numQ L ≤ M := le_trans List.countP_le_length hM
  have hdiff : ∀ ω', ‖minorDiff d N (qList L)
      (flucDiagSet d N u (zt E t) (mE E) k) ω'‖ ≤ 2 ^ numQ L * (2 * ((etaT E t)⁻¹ + 1)) := by
    intro ω'
    have hb := norm_minorDiff_le (qList L) (flucDiagSet d N u (zt E t) (mE E) k)
      (fun S ω'' => norm_flucDiagSet_le_env hE ht u k S ω'') ω'
    rwa [length_qList] at hb
  refine le_trans (norm_applyOps_le L hdiff ω) ?_
  have hpow : (2 : ℝ) ^ numQ L * (2 ^ numQ L * (2 * ((etaT E t)⁻¹ + 1)))
      = 2 ^ (2 * numQ L + 1) * ((etaT E t)⁻¹ + 1) := by
    rw [show 2 * numQ L + 1 = numQ L + numQ L + 1 by omega, pow_succ, pow_add]
    ring
  rw [hpow]
  unfold condEnv
  have hmono : (2 : ℝ) ^ (2 * numQ L + 1) ≤ 2 ^ (2 * M + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnn : (0 : ℝ) ≤ (etaT E t)⁻¹ + 1 := by positivity
  exact mul_le_mul_of_nonneg_right hmono hnn

/-- **(4.12)'s last input, conditionalized on the good event.**

`hgood` is read at one sample point at a time and only *off* `Bad 0`; there is no hypothesis
quantified over all `ω`.  The price is the two explicit terms:

* the per-factor constant grows from `2 C_M Ψ` to `2 C_M Ψ + `
  `RBM.Gauss.condCost`, i.e. by `(M+1) 2^{2M+1}(η_u⁻¹+1) ε (2Ψ)^{-M}`, where `ε` is the
  row-section threshold of the `RBM.Gauss.BadFamily`;
* an additive remainder `(2^{2M+1}(η_u⁻¹+1))^{#slots} P(Bad_{M+1})`.

The additive remainder is *not* removable inside `RBM.Gauss.MinorDiffGainUpTo`, whose index
type `ι` is unrestricted — see the note at the end of this file. -/
theorem integral_prod_applyOps_minorDiff_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M : ℕ} {Bad : ℕ → Set (Ω d)} (hfam : BadFamily d N ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d N u (zt E t) (mE E) ω Ψ M)
    (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N))
    (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i)
    (hM : ∀ i, (L i).length ≤ M) :
    ∫ ω, ∏ i, ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖ ∂(P d)
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ Fintype.card ι
          * (2 * Ψ) ^ ∑ i, numQ (L i)
        + condEnv E t M ^ Fintype.card ι * (P d).real (Bad (M + 1)) := by
  classical
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have hΨ0' : (0 : ℝ) ≤ Ψ := hΨ0.le
  have hΨ1 : Ψ ≤ 1 := by linarith
  have hEnv0 : 0 ≤ condEnv E t M := condEnv_nonneg hE ht M
  have hcost0 : 0 ≤ condCost E t M Ψ ε := condCost_nonneg hE ht M hΨ0' hε
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  set B : ℝ := 2 * minorDiffC M * Ψ + condCost E t M Ψ ε with hB
  have hB0 : 0 ≤ B := by
    have := minorDiffC_nonneg M
    rw [hB]
    have : (0:ℝ) ≤ 2 * minorDiffC M * Ψ := by positivity
    linarith
  -- the per-factor bound off the exceptional set
  have hb : ∀ ω ∉ Bad (M + 1), ∀ i : ι,
      ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖
        ≤ B * (2 * Ψ) ^ numQ (L i) := by
    intro ω hω i
    have hωi : ω ∉ Bad ((L i).length + 1) := by
      intro hmem
      exact hω (hfam.mono_le (by have := hM i; omega) hmem)
    have hkey := norm_applyOps_minorDiff_flucDiagSet_le_badFamily hE ht u hΨ0' hΨ1 hε hfam
      hgood (k i) (L i) (h1 i) (h2 i) (hM i) ω hωi
    refine hkey.trans ?_
    set q : ℕ := numQ (L i) with hq
    have hqM : q ≤ M := le_trans List.countP_le_length (hM i)
    -- the gain term is exact
    have hgain : (2 : ℝ) ^ (q + 1) * (minorDiffC M * Ψ ^ (q + 1))
        = (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ) := by
      rw [mul_pow, pow_succ, pow_succ]
      ring
    -- the exceptional term is charged to `condCost`
    have hpowle : ((2 * Ψ) ^ M : ℝ) ≤ (2 * Ψ) ^ q :=
      pow_le_pow_of_le_one h2Ψ0.le hΨhalf hqM
    have hexact : (2 * Ψ) ^ M * condCost E t M Ψ ε = ((M : ℝ) + 1) * condEnv E t M * ε := by
      unfold condCost
      field_simp
    have hlen : ((L i).length : ℝ) + 1 ≤ (M : ℝ) + 1 := by
      have : ((L i).length : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM i
      linarith
    have h2q : (2 : ℝ) ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) ≤ condEnv E t M := by
      unfold condEnv
      have hrw : (2 : ℝ) ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1))
          = 2 ^ (2 * q + 1) * ((etaT E t)⁻¹ + 1) := by
        rw [show 2 * q + 1 = q + q + 1 by omega, pow_succ, pow_add]
        ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    have hexc : (2 : ℝ) ^ (q + 1)
        * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
        ≤ (2 * Ψ) ^ q * condCost E t M Ψ ε := by
      have hstep : (2 : ℝ) ^ (q + 1)
          * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
          = (((L i).length : ℝ) + 1) * (2 ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1))) * ε := by
        ring
      rw [hstep]
      have hA : (((L i).length : ℝ) + 1) * (2 ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1))) * ε
          ≤ ((M : ℝ) + 1) * condEnv E t M * ε := by
        have hnn1 : (0 : ℝ) ≤ ((L i).length : ℝ) + 1 := by positivity
        have hnn2 : (0 : ℝ) ≤ (2 : ℝ) ^ (q + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) := by
          positivity
        have := mul_le_mul hlen h2q hnn2 (by positivity)
        exact mul_le_mul_of_nonneg_right this hε
      refine hA.trans ?_
      rw [← hexact]
      exact mul_le_mul_of_nonneg_right hpowle hcost0
    have hsplit : (2 : ℝ) ^ (q + 1)
        * (minorDiffC M * Ψ ^ (q + 1)
            + ((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
        = 2 ^ (q + 1) * (minorDiffC M * Ψ ^ (q + 1))
          + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε) := by
      ring
    rw [hsplit, hgain, hB]
    calc (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ)
          + 2 ^ (q + 1) * (((L i).length + 1) * (2 ^ q * ((etaT E t)⁻¹ + 1)) * ε)
        ≤ (2 * Ψ) ^ q * (2 * minorDiffC M * Ψ) + (2 * Ψ) ^ q * condCost E t M Ψ ε := by
          linarith
      _ = (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) * (2 * Ψ) ^ q := by ring
  -- the global envelope
  have hG : ∀ ω : Ω d, ∏ i, ‖applyOps d N (L i)
      (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖
      ≤ condEnv E t M ^ Fintype.card ι := by
    intro ω
    calc ∏ i, ‖applyOps d N (L i)
          (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖
        ≤ ∏ _i : ι, condEnv E t M :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ =>
            norm_applyOps_minorDiff_flucDiagSet_le_condEnv hE ht u (k i) (L i) (hM i) ω
      _ = condEnv E t M ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]
  have hbm : ∀ i : ι, BddMeas d (applyOps d N (L i)
      (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)))) :=
    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
  have hb0 : ∀ i : ι, 0 ≤ B * (2 * Ψ) ^ numQ (L i) := fun i => by positivity
  refine le_trans (integral_prod_norm_le_of_bounds_on hbm (hfam.meas (M + 1)) hb0 hb hG) ?_
  have heq : (∏ i : ι, B * (2 * Ψ) ^ numQ (L i))
      = B ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
      Finset.card_univ]
  rw [heq]

end Moment

/-! ### The hypothesis is produced from (4.1), not postulated -/

section Bridge

variable {E : ℝ} {s t δ : ℕ → ℝ}

/-- The base of the tower: a **measurable** hull of the complement of the flow good event
`RBM.Gauss.goodSetFlow` (= the paper's `Ω(t,c)` of (4.1)).  Measures in Mathlib are outer
measures, so the hull has exactly the same measure as the complement itself, and
`RBM.Gauss.highProb_goodSetFlow_of_localLaw` bounds that. -/
noncomputable def badBase (d : Dims) (E : ℝ) (s t δ : ℕ → ℝ) (N : ℕ) : Set (Ω d) :=
  toMeasurable (P d) (goodSetFlow d E s t δ N)ᶜ

theorem measurableSet_badBase (d : Dims) (E : ℝ) (s t δ : ℕ → ℝ) (N : ℕ) :
    MeasurableSet (badBase d E s t δ N) := measurableSet_toMeasurable _ _

theorem meas_badBase (d : Dims) (E : ℝ) (s t δ : ℕ → ℝ) (N : ℕ) :
    (P d) (badBase d E s t δ N) = (P d) (goodSetFlow d E s t δ N)ᶜ :=
  measure_toMeasurable _

/-- **`hgood` is a theorem.**  Off the hull of the complement of (4.1), the level-budgeted good
event holds at threshold `2 δ_N`, at every time of the flow interval.  This is T169's one-line
bridge `RBM.Gauss.minorGoodLe_of_goodEvent_flow` composed with the definition of
`RBM.Gauss.goodSetFlow`. -/
theorem minorGoodLe_of_notMem_badBase {N : ℕ} (hE : |E| ≤ 2) {v : ℝ}
    (hv : v ∈ Set.Icc (s N) (t N)) (hz : (zt E v).im ≠ 0) {M : ℕ}
    (hδ0 : 0 ≤ δ N) (hδ4 : δ N ≤ 1 / 4) (hMδ : 8 * M * δ N ≤ 1)
    {ω : Ω d} (hω : ω ∉ badBase d E s t δ N) :
    MinorGoodLe d N v (zt E v) (mE E) ω (2 * δ N) M := by
  have hmem : ω ∈ goodSetFlow d E s t δ N := by
    by_contra h
    exact hω (subset_toMeasurable (P d) _ h)
  exact minorGoodLe_of_goodEvent_flow hE hz hδ0 hδ4 hMδ (hmem v hv)

/-- **The conditionalized (4.12) input, with every hypothesis produced.**

The only probabilistic input is the flow good event (4.1) of
`RBM.Gauss.highProb_goodSetFlow_of_localLaw`; there is **no** hypothesis quantified over all
sample points.  The exceptional set that the bound charges is the tower
`RBM.Gauss.badTower` over the hull of its complement, whose measure
`RBM.Gauss.meas_badTower_le` controls by `((ε + #rows)/ε)^{M+1} P(Ω(t,c)ᶜ)`. -/
theorem integral_prod_applyOps_minorDiff_le_goodSetFlow {N : ℕ}
    (hE : |E| < 2) {v : ℝ} (hv1 : v < 1) (hv : v ∈ Set.Icc (s N) (t N))
    {ε : ℝ} (hε : 0 ≤ ε) {M : ℕ} (hδ0 : 0 < δ N) (hδ4 : δ N ≤ 1 / 4)
    (hMδ : 8 * M * δ N ≤ 1)
    (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N))
    (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i)
    (hM : ∀ i, (L i).length ≤ M) :
    ∫ ω, ∏ i, ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N v (zt E v) (mE E) (k i))) ω‖ ∂(P d)
      ≤ (2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε) ^ Fintype.card ι
          * (2 * (2 * δ N)) ^ ∑ i, numQ (L i)
        + condEnv E v M ^ Fintype.card ι
            * (P d).real (badTower d N ε (badBase d E s t δ N) (M + 1)) := by
  have hz : (zt E v).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact ne_of_gt (etaT_pos_of_lt_one hE hv1)
  refine integral_prod_applyOps_minorDiff_le_on hE hv1 v (Ψ := 2 * δ N) (by linarith)
    (by linarith) hε (badFamily_badTower d N ε (measurableSet_badBase d E s t δ N))
    (fun ω hω => minorGoodLe_of_notMem_badBase hE.le hv hz hδ0.le hδ4 hMδ hω)
    ι k L h1 h2 hM

end Bridge

/-! ### Why the remainder cannot be absorbed into `RBM.Gauss.MinorDiffGainUpTo` -/

section Ceiling

variable {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M : ℕ}

/-- **`RBM.Gauss.MinorDiffGainUpTo` controls every `L^n` norm of `Z_k` by the *same* `B`.**

Take the index type to be `Fin n`, every word empty and every pivot equal to `k`: the words are
admissible, of length `0 ≤ M`, the gain exponent is `0`, and the integrand is `‖Z_k‖^n`.

This is the obstruction to conditionalizing *inside* that interface.  The index type `ι` of
`RBM.Gauss.MinorDiffGainUpTo` is unrestricted, so an additive remainder
`Env^{#ι} P(Bad)` — with `Env ≍ η_u⁻¹` the deterministic envelope, necessarily larger than a
`B ≍ Ψ` — cannot be absorbed into `B^{#ι}`: letting `n → ∞` the left side of the conclusion
below tends to `‖Z_k‖_∞`, and T172's two-point argument exhibits a sample point with
`‖Z_k‖ ≥ 64/65`.  The `B` of `RBM.Gauss.MinorDiffGainUpTo` therefore has an absolute lower
bound of the same kind as `RBM.Gauss.FlucBound`'s, and the conditionalized estimate must be
stated with the remainder kept explicit — as
`RBM.Gauss.integral_prod_applyOps_minorDiff_le_on` does — or with a budget on `#ι` as well. -/
theorem integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo
    (h : MinorDiffGainUpTo d N u z m B ρ M) (k : d.Idx N) (n : ℕ) :
    ∫ ω, ‖flucDiag d N u z m k ω‖ ^ n ∂(P d) ≤ B ^ n := by
  classical
  have hkey := h.2.2 (Fin n) (fun _ => k) (fun _ => ([] : List (Bool × d.Idx N)))
    (by intro i; simp) (by intro i x hx; simp at hx) (by intro i; simp)
  simp only [qList_nil, minorDiff_nil, applyOps_nil, numQ_nil, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_zero, pow_zero, mul_one,
    Finset.prod_const] at hkey
  rw [flucDiagSet_empty] at hkey
  exact hkey

/-- **With the cardinality budget the same instantiation stops at `j = n`** — T177.

`RBM.Gauss.MinorDiffGainUpTo'` restricts the index type to `#ι ≤ n`, so the degenerate
instantiation above is only available for `j ≤ n`.  The hypothesis `hj` is not removable: it
is precisely what the budget buys, and without the `j → ∞` limit the conclusion
`‖Z_k‖_{L^j} ≤ B` for `j ≤ n = 2p` is what the local law asserts, not a contradiction with
it.  Compare `RBM.Gauss.integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo` above and
`RBM.Gauss.integral_pow_norm_flucDiag_le_of_flucGainUpTo` /
`RBM.Gauss.integral_pow_norm_flucDiag_le_of_flucGainUpTo'` in `RBM1D/Gauss/FlucIter.lean`,
which are the same pair one level up, on the live path. -/
theorem integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo' {n : ℕ}
    (h : MinorDiffGainUpTo' d N u z m B ρ M n) (k : d.Idx N) {j : ℕ} (hj : j ≤ n) :
    ∫ ω, ‖flucDiag d N u z m k ω‖ ^ j ∂(P d) ≤ B ^ j := by
  classical
  have hkey := h.2.2 (Fin j) (fun _ => k) (fun _ => ([] : List (Bool × d.Idx N)))
    (by intro i; simp) (by intro i x hx; simp at hx) (by intro i; simp) (by simpa using hj)
  simp only [qList_nil, minorDiff_nil, applyOps_nil, numQ_nil, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_zero, pow_zero, mul_one,
    Finset.prod_const] at hkey
  rw [flucDiagSet_empty] at hkey
  exact hkey

end Ceiling

/-! ### The conditionalized estimate, packaged as a budgeted interface — T177

With the cardinality budget `#ι ≤ n` the additive remainder of
`RBM.Gauss.integral_prod_applyOps_minorDiff_le_on` **is** absorbable, and the conditionalized
(4.12) input becomes an interface again rather than an inequality with a tail.  The arithmetic
is the one the budget was introduced for:

  `condEnv^{#ι} P(Bad) ≤ condEnv^n P(Bad) ≤ B₀^n (2Ψ)^{nM} ≤ B₀^{#ι} (2Ψ)^{∑ q}`,

using `1 ≤ condEnv`, `#ι ≤ n`, `B₀ ≤ 1`, `2Ψ ≤ 1` and `∑ q ≤ #ι M ≤ n M`; the middle step is
the one genuine hypothesis, a smallness condition on the measure of the tower.  Adding the
remainder to the main term then costs a factor `2 ≤ 2^{#ι}`, i.e. `B = 2 B₀`, and the gain
`ρ = 2Ψ` is untouched.

At `#ι = 0` the bound `1 + P(Bad) ≤ 1` would be false, so that case is not routed through the
remainder at all: the integrand is an empty product, the integral of `1` against a probability
measure, and the conclusion is `1 ≤ 1`.

`RBM.Gauss.minorDiffGain_budget_hyps_consistent` exhibits explicit parameters satisfying the
whole numeric bundle at `B ≍ Ψ` with a *strictly positive* exceptional measure, which is what
`RBM.Gauss.integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo` shows to be impossible without
the budget. -/

section Budget

variable {E t : ℝ}

theorem one_le_condEnv (hE : |E| < 2) (ht : t < 1) (M : ℕ) : 1 ≤ condEnv E t M := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * M + 1) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (etaT E t)⁻¹ + 1 := by
    have := inv_nonneg.2 hη.le
    linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 2 ^ (2 * M + 1) * ((etaT E t)⁻¹ + 1) := by
        exact mul_le_mul h1 h2 zero_le_one (by positivity)
    _ = condEnv E t M := rfl

/-- **The row-section threshold that makes the conditionalization cost exactly `Ψ`.**

`RBM.Gauss.condCost` is linear in `ε`, so there is one choice of the `RBM.Gauss.BadFamily`
threshold for which the price of conditionalizing is the same `Ψ` as the gain itself; with it
the constant of the budgeted interface is `2(2 minorDiffC M + 1) Ψ`, i.e. `≍ Ψ`, which is the
paper's size. -/
noncomputable def condEps (E t : ℝ) (M : ℕ) (Ψ : ℝ) : ℝ :=
  Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹

theorem condEps_nonneg (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ : ℝ} (hΨ : 0 ≤ Ψ) :
    0 ≤ condEps E t M Ψ := by
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one (one_le_condEnv hE ht M)
  unfold condEps
  positivity

theorem condCost_condEps (hE : |E| < 2) (ht : t < 1) (M : ℕ) {Ψ : ℝ} (hΨ : 0 < Ψ) :
    condCost E t M Ψ (condEps E t M Ψ) = Ψ := by
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one (one_le_condEnv hE ht M)
  have hMEnv : (0 : ℝ) < ((M : ℝ) + 1) * condEnv E t M := by positivity
  have h1 : ((2 * Ψ) ^ M : ℝ) ≠ 0 := by positivity
  have h2 : (((M : ℝ) + 1) * condEnv E t M) ≠ 0 := ne_of_gt hMEnv
  unfold condCost condEps
  calc ((M : ℝ) + 1) * condEnv E t M
          * (Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹) * ((2 * Ψ) ^ M)⁻¹
      = (((M : ℝ) + 1) * condEnv E t M * (((M : ℝ) + 1) * condEnv E t M)⁻¹)
          * ((2 * Ψ) ^ M * ((2 * Ψ) ^ M)⁻¹) * Ψ := by ring
    _ = Ψ := by rw [mul_inv_cancel₀ h2, mul_inv_cancel₀ h1, mul_one, one_mul]

/-- **The conditionalized (4.12) input, as a budgeted interface.**

The hypotheses are those of `RBM.Gauss.integral_prod_applyOps_minorDiff_le_on` plus the two
that the absorption needs: `hB1`, that the per-factor constant is at most `1` (automatic at
`B₀ ≍ Ψ → 0`), and `hsmall`, that the tower is small enough at the two budgets.  Neither is a
`∀ ω` hypothesis, and neither involves the index type: the interface is now satisfiable at the
paper's size — see `RBM.Gauss.minorDiffGain_budget_hyps_consistent`.

The constant doubles, `B = 2 B₀`; the gain is exactly the `ρ = 2Ψ` of
`RBM.Gauss.integral_prod_applyOps_minorDiff_le_on`, unchanged. -/
theorem minorDiffGainUpTo'_of_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M n : ℕ} {Bad : ℕ → Set (Ω d)} (hfam : BadFamily d N ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d N u (zt E t) (mE E) ω Ψ M)
    (hB1 : 2 * minorDiffC M * Ψ + condCost E t M Ψ ε ≤ 1)
    (hsmall : condEnv E t M ^ n * (P d).real (Bad (M + 1))
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ n * (2 * Ψ) ^ (n * M)) :
    MinorDiffGainUpTo' d N u (zt E t) (mE E)
      (2 * (2 * minorDiffC M * Ψ + condCost E t M Ψ ε)) (2 * Ψ) M n := by
  classical
  have hΨ0' : (0 : ℝ) ≤ Ψ := hΨ0.le
  have h2Ψ0 : (0 : ℝ) < 2 * Ψ := by linarith
  have hcost0 : 0 ≤ condCost E t M Ψ ε := condCost_nonneg hE ht M hΨ0' hε
  have hC := minorDiffC_nonneg M
  set B₀ : ℝ := 2 * minorDiffC M * Ψ + condCost E t M Ψ ε with hB₀def
  have hB₀0 : 0 ≤ B₀ := by
    have : (0 : ℝ) ≤ 2 * minorDiffC M * Ψ := by positivity
    rw [hB₀def]; linarith
  refine ⟨by positivity, by positivity, fun ι _ k L h1 h2 hlen hcard => ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have hemp : IsEmpty ι := Fintype.card_eq_zero_iff.1 h0
    simp [Finset.univ_eq_empty]
  · have hmain := integral_prod_applyOps_minorDiff_le_on hE ht u hΨ0 hΨhalf hε hfam hgood
      ι k L h1 h2 hlen
    refine hmain.trans ?_
    -- the sum of the gain exponents is at most `n * M`
    have hq : (∑ i, numQ (L i)) ≤ n * M := by
      have hstep : (∑ i, numQ (L i)) ≤ ∑ _i : ι, M :=
        Finset.sum_le_sum fun i _ => le_trans List.countP_le_length (hlen i)
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hstep
      exact le_trans hstep (Nat.mul_le_mul_right M hcard)
    have hEnv1 : 1 ≤ condEnv E t M := one_le_condEnv hE ht M
    have hPnn : 0 ≤ (P d).real (Bad (M + 1)) := measureReal_nonneg
    have hmainnn : 0 ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by positivity
    -- the remainder is dominated by the main term
    have hrem : condEnv E t M ^ Fintype.card ι * (P d).real (Bad (M + 1))
        ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
      calc condEnv E t M ^ Fintype.card ι * (P d).real (Bad (M + 1))
          ≤ condEnv E t M ^ n * (P d).real (Bad (M + 1)) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hEnv1 hcard) hPnn
        _ ≤ B₀ ^ n * (2 * Ψ) ^ (n * M) := hsmall
        _ ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
            refine mul_le_mul (pow_le_pow_of_le_one hB₀0 hB1 hcard)
              (pow_le_pow_of_le_one h2Ψ0.le hΨhalf hq) (by positivity) (by positivity)
    -- and the doubling is paid by `2 ≤ 2 ^ #ι`
    have hdouble : (2 : ℝ) ≤ 2 ^ Fintype.card ι := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Fintype.card ι := pow_le_pow_right₀ one_le_two hpos
    calc B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)
            + condEnv E t M ^ Fintype.card ι * (P d).real (Bad (M + 1))
        ≤ B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)
            + B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by linarith
      _ = 2 * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) := by ring
      _ ≤ 2 ^ Fintype.card ι * (B₀ ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i)) :=
          mul_le_mul_of_nonneg_right hdouble hmainnn
      _ = (2 * B₀) ^ Fintype.card ι * (2 * Ψ) ^ ∑ i, numQ (L i) := by
          rw [mul_pow (2 : ℝ) B₀ (Fintype.card ι)]; ring

/-- **The budgeted gain interface of `RBM1D/Gauss/FlucIter.lean`, from the same input.**
The annihilation identity carries both budgets across
(`RBM.Gauss.flucGainUpTo'_of_minorDiffGainUpTo'`), so this is the form
`RBM.Gauss.integral_norm_flucAvg_pow_le_iter_budget` consumes, with `M = n = 2p`. -/
theorem flucGainUpTo'_of_le_on
    (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ ε : ℝ} (hΨ0 : 0 < Ψ) (hΨhalf : 2 * Ψ ≤ 1)
    (hε : 0 ≤ ε) {M n : ℕ} {Bad : ℕ → Set (Ω d)} (hfam : BadFamily d N ε Bad)
    (hgood : ∀ ω ∉ Bad 0, MinorGoodLe d N u (zt E t) (mE E) ω Ψ M)
    (hB1 : 2 * minorDiffC M * Ψ + condCost E t M Ψ ε ≤ 1)
    (hsmall : condEnv E t M ^ n * (P d).real (Bad (M + 1))
      ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ n * (2 * Ψ) ^ (n * M)) :
    FlucGainUpTo' d N u (zt E t) (mE E)
      (2 * (2 * minorDiffC M * Ψ + condCost E t M Ψ ε)) (2 * Ψ) M n :=
  flucGainUpTo'_of_minorDiffGainUpTo' hE ht u
    (minorDiffGainUpTo'_of_le_on hE ht u hΨ0 hΨhalf hε hfam hgood hB1 hsmall)

end Budget

/-! ### The budgeted interface, produced from (4.1) — T177

The composition of `RBM.Gauss.minorDiffGainUpTo'_of_le_on` with the bridge of the previous
section: the *only* probabilistic input is the flow good event `RBM.Gauss.goodSetFlow`
(the paper's `Ω(t,c)` of (4.1)), there is **no** hypothesis quantified over all sample points,
and the exceptional set charged is the explicit tower `RBM.Gauss.badTower` over the measurable
hull of its complement.  The residual hypothesis `hsmall` is a statement about the *measure* of
that tower, which `RBM.Gauss.meas_badTower_le` bounds by `((ε + #rows)/ε)^{M+1} P(Ω(t,c)ᶜ)` —
super-polynomially small for each fixed pair of budgets. -/

section BudgetFlow

variable {E : ℝ} {s t δ : ℕ → ℝ}

/-- **`RBM.Gauss.MinorDiffGainUpTo'` from the flow good event (4.1).** -/
theorem minorDiffGainUpTo'_goodSetFlow {N : ℕ} (hE : |E| < 2) {v : ℝ} (hv1 : v < 1)
    (hv : v ∈ Set.Icc (s N) (t N)) {ε : ℝ} (hε : 0 ≤ ε) {M n : ℕ}
    (hδ0 : 0 < δ N) (hδ4 : δ N ≤ 1 / 4) (hMδ : 8 * M * δ N ≤ 1)
    (hB1 : 2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε ≤ 1)
    (hsmall : condEnv E v M ^ n
        * (P d).real (badTower d N ε (badBase d E s t δ N) (M + 1))
      ≤ (2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε) ^ n
          * (2 * (2 * δ N)) ^ (n * M)) :
    MinorDiffGainUpTo' d N v (zt E v) (mE E)
      (2 * (2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε))
      (2 * (2 * δ N)) M n := by
  have hz : (zt E v).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact ne_of_gt (etaT_pos_of_lt_one hE hv1)
  exact minorDiffGainUpTo'_of_le_on (E := E) (t := v) hE hv1 v (Ψ := 2 * δ N)
    (by linarith) (by linarith) hε
    (badFamily_badTower d N ε (measurableSet_badBase d E s t δ N))
    (fun ω hω => minorGoodLe_of_notMem_badBase hE.le hv hz hδ0.le hδ4 hMδ hω) hB1 hsmall

/-- **`RBM.Gauss.FlucGainUpTo'` from the flow good event (4.1)** — the interface that
`RBM.Gauss.eq45Flow_of_localLaw_gain_budget` consumes, with every hypothesis produced from
(4.1) and explicit numeric side conditions. -/
theorem flucGainUpTo'_goodSetFlow {N : ℕ} (hE : |E| < 2) {v : ℝ} (hv1 : v < 1)
    (hv : v ∈ Set.Icc (s N) (t N)) {ε : ℝ} (hε : 0 ≤ ε) {M n : ℕ}
    (hδ0 : 0 < δ N) (hδ4 : δ N ≤ 1 / 4) (hMδ : 8 * M * δ N ≤ 1)
    (hB1 : 2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε ≤ 1)
    (hsmall : condEnv E v M ^ n
        * (P d).real (badTower d N ε (badBase d E s t δ N) (M + 1))
      ≤ (2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε) ^ n
          * (2 * (2 * δ N)) ^ (n * M)) :
    FlucGainUpTo' d N v (zt E v) (mE E)
      (2 * (2 * minorDiffC M * (2 * δ N) + condCost E v M (2 * δ N) ε))
      (2 * (2 * δ N)) M n :=
  flucGainUpTo'_of_minorDiffGainUpTo' (E := E) (t := v) hE hv1 v
    (minorDiffGainUpTo'_goodSetFlow hE hv1 hv hε hδ0 hδ4 hMδ hB1 hsmall)

end BudgetFlow

/-! ### The numeric bundle is satisfiable — T177's acceptance check

`RBM.Gauss.integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo` shows that the *unbudgeted*
interface forces `B ≥ ‖Z_k‖_{L^j}` for every `j`, hence `B ≥ 64/65` by T172: no choice of
parameters makes it hold at `B ≍ Ψ`.  The budgeted one has no such obstruction, and the
statement below is the positive check: for every `E`, `t`, and every pair of budgets `M`, `n`,
there are explicit `Ψ`, `ε` and an exceptional measure `pBad` — **strictly positive**, so the
witness is not the degenerate one — satisfying simultaneously every numeric hypothesis of
`RBM.Gauss.minorDiffGainUpTo'_of_le_on`, together with `B = K Ψ` for the explicit
`K = 2(2 minorDiffC M + 1)`, i.e. at the paper's size. -/

section Consistency

variable {E t : ℝ}

/-- **All the numeric hypotheses of `RBM.Gauss.minorDiffGainUpTo'_of_le_on` hold at once, at
`B ≍ Ψ`, with a strictly positive exceptional measure.** -/
theorem minorDiffGain_budget_hyps_consistent (hE : |E| < 2) (ht : t < 1) (M n : ℕ) :
    ∃ Ψ > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ pBad > (0 : ℝ),
      2 * Ψ ≤ 1 ∧ pBad ≤ 1 ∧
      2 * minorDiffC M * Ψ + condCost E t M Ψ ε ≤ 1 ∧
      condEnv E t M ^ n * pBad
        ≤ (2 * minorDiffC M * Ψ + condCost E t M Ψ ε) ^ n * (2 * Ψ) ^ (n * M) ∧
      2 * (2 * minorDiffC M * Ψ + condCost E t M Ψ ε)
        = (2 * (2 * minorDiffC M + 1)) * Ψ := by
  have hC := minorDiffC_nonneg M
  have hEnv1 : 1 ≤ condEnv E t M := one_le_condEnv hE ht M
  have hEnv0 : 0 < condEnv E t M := lt_of_lt_of_le zero_lt_one hEnv1
  have hEnvne : (condEnv E t M : ℝ) ≠ 0 := ne_of_gt hEnv0
  -- `Ψ` small enough that `2 minorDiffC M Ψ ≤ 1/4` and `2 Ψ ≤ 1`
  set Ψ : ℝ := (8 * (minorDiffC M + 1))⁻¹ with hΨdef
  have hden : (0 : ℝ) < 8 * (minorDiffC M + 1) := by positivity
  have hΨpos : 0 < Ψ := by rw [hΨdef]; positivity
  have hmul : (8 * (minorDiffC M + 1)) * Ψ = 1 := by
    rw [hΨdef]; exact mul_inv_cancel₀ (ne_of_gt hden)
  have hCΨ0 : 0 ≤ minorDiffC M * Ψ := mul_nonneg hC hΨpos.le
  have hΨle : Ψ ≤ 1 / 8 := by nlinarith
  have hΨhalf : 2 * Ψ ≤ 1 := by linarith
  have h2Ψpos : (0 : ℝ) < 2 * Ψ := by linarith
  have hCΨ : 2 * minorDiffC M * Ψ ≤ 1 / 4 := by nlinarith
  -- `ε` chosen so that the conditionalization cost is exactly `Ψ`
  set ε : ℝ := Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹ with hεdef
  have hMEnv : (0 : ℝ) < ((M : ℝ) + 1) * condEnv E t M := by positivity
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hcost : condCost E t M Ψ ε = Ψ := by
    have h1 : ((2 * Ψ) ^ M : ℝ) ≠ 0 := by positivity
    have h2 : (((M : ℝ) + 1) * condEnv E t M) ≠ 0 := ne_of_gt hMEnv
    unfold condCost
    rw [hεdef]
    calc ((M : ℝ) + 1) * condEnv E t M
            * (Ψ * (2 * Ψ) ^ M * (((M : ℝ) + 1) * condEnv E t M)⁻¹) * ((2 * Ψ) ^ M)⁻¹
        = (((M : ℝ) + 1) * condEnv E t M * (((M : ℝ) + 1) * condEnv E t M)⁻¹)
            * ((2 * Ψ) ^ M * ((2 * Ψ) ^ M)⁻¹) * Ψ := by ring
      _ = Ψ := by rw [mul_inv_cancel₀ h2, mul_inv_cancel₀ h1, mul_one, one_mul]
  refine ⟨Ψ, hΨpos, ε, hεpos,
    (2 * minorDiffC M * Ψ + Ψ) ^ n * (2 * Ψ) ^ (n * M) / condEnv E t M ^ n,
    by positivity, hΨhalf, ?_, ?_, ?_, ?_⟩
  · -- `pBad ≤ 1`
    have h1 : (2 * minorDiffC M * Ψ + Ψ) ^ n ≤ 1 :=
      pow_le_one₀ (by positivity) (by linarith)
    have h2 : ((2 : ℝ) * Ψ) ^ (n * M) ≤ 1 := pow_le_one₀ (by positivity) hΨhalf
    have h3 : (1 : ℝ) ≤ condEnv E t M ^ n := one_le_pow₀ hEnv1
    have hnum : (2 * minorDiffC M * Ψ + Ψ) ^ n * (2 * Ψ) ^ (n * M) ≤ 1 := by
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 2 * minorDiffC M * Ψ + Ψ) n,
        pow_nonneg h2Ψpos.le (n * M)]
    rw [div_le_one (by positivity)]
    linarith
  · rw [hcost]; linarith
  · rw [hcost, ← mul_div_assoc, mul_div_cancel_left₀ _ (pow_ne_zero n hEnvne)]
  · rw [hcost]; ring

end Consistency

/-! ### (4.12) and (4.5) along the flow, against the budgeted interface — T177

`RBM.Gauss.eq45Flow_of_localLaw_gain'` (`RBM1D/Gauss/CondStableFlow.lean`) consumes
`RBM.Gauss.FlucGainUpTo` in its `hg` slot, and by
`RBM.Gauss.integral_pow_norm_flucDiag_le_of_flucGainUpTo` that interface is unsatisfiable at
`B ≍ Ψ`: the theorem is true but vacuous, so (4.5) had no supply.  This block re-derives the
whole chain from `RBM.Gauss.FlucGainUpTo'`, whose budgets `M = n = 2p` are exactly what the
`2p`-th moment expansion provides.

Every statement below has **verbatim** the conclusion of its unprimed ancestor in
`RBM1D/Gauss/Eq45FlowInputs.lean` / `RBM1D/Gauss/CondStableFlow.lean`, and the hypothesis
lists differ in one place only: `RBM.Gauss.FlucGainUpTo` becomes
`RBM.Gauss.FlucGainUpTo' … (2 * p) (2 * p)`.  The unprimed versions are untouched and remain
reachable through `RBM.Gauss.FlucGainUpTo.budget`, so nothing that already had a supply loses
it; what changes is that the budgeted chain *can* be supplied, by
`RBM.Gauss.flucGainUpTo'_of_le_on` above. -/

section Eq45Budget

open Filter

variable {E K : ℝ} {s t : ℕ → ℝ}

/-- **(4.12) at every time of the flow interval, from the budgeted gain.**  The budgeted form
of `RBM.Gauss.unifDomIcc_flucAvg_iter'`. -/
theorem unifDomIcc_flucAvg_iter_budget {V : ℕ → Type*} (d : Dims) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1)
    {Tw : ∀ N, V N → d.Idx N → ℝ} {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (d.Idx N)}
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1) (hcρ : ∀ N, cw N ≤ ep N ^ 2)
    (hw : ∀ N (a : V N), UniformWeight (Tw N a) (cw N) (Aw N a))
    (hcardA : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ a : V N, 2 * p ≤ (Aw N a).card) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖)
      (fun N _ _ _ => ep N * Bm N) := by
  refine unifDomIcc_of_moment (fun N => hpos N) (fun p N u hu a => ?_) ?_
  · exact integrable_norm_flucAvg_pow
      (flucBound_env hE (lt_of_le_of_lt hu.2 (ht1 N)) d N u).flucDiag_le p
  · intro ε hε p
    have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) :=
      pow_nonneg (mul_nonneg (by positivity) (hKp p)) _
    have hc1 : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) := by positivity
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) := mul_nonneg hc1 hK0
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
      * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [hcardA p, eventually_ge_atTop 1] with N h2 hN1 u hu a
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hrw : (fun ω => |‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖| ^ (2 * p))
        = fun ω => ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) := by
      funext ω; rw [abs_norm]
    rw [hrw]
    have hmain := integral_norm_flucAvg_pow_le_iter_budget hE hu1 (hg p N u hu) le_rfl le_rfl
      (hρ1 N) (hcρ N) (hw N a) (h2 a)
    have hep0 : (0 : ℝ) ≤ ep N := (hg p N u hu).rho_nonneg
    have hBp0 : (0 : ℝ) ≤ Bp p N := (hg p N u hu).B_nonneg
    have hstep1 : ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
        ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N
          ≤ (2 : ℝ) ^ (2 * p - 1) * ep N * (Kp p * Bm N) :=
            mul_le_mul_of_nonneg_left (hBK p N) (by positivity)
        _ = ((2 : ℝ) ^ (2 * p - 1) * Kp p) * (ep N * Bm N) := by ring
    have hmain2 : ∫ ω, ‖flucAvg d N u (zt E u) (mE E) (Tw N a) ω‖ ^ (2 * p) ∂(P d)
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
            * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p)) * (ep N * Bm N) ^ (2 * p) := by
      refine le_trans hmain ?_
      calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * (((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p)) :=
            mul_le_mul_of_nonneg_left hstep1 hc1
        _ = _ := by ring
    have hNe : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
    have hpow : (0 : ℝ) ≤ (ep N * Bm N) ^ (2 * p) :=
      pow_nonneg (mul_nonneg hep0 (hBm N)) _
    refine le_trans hmain2 ?_
    nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]

/-- **(4.12) for the block average, from the budgeted gain.** -/
theorem unifDomIcc_flucAvg_blockAvg_iter_budget (d : Dims) (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ ep N ^ 2) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖)
      (fun N _ _ _ => ep N * Bm N) :=
  unifDomIcc_flucAvg_iter_budget (V := fun N => ZMod (d.L N)) d hE ht1 hg hKp hBm hBK hpos
    hρ1 hcρ (fun N a => uniformWeight_blockAvg a)
    (fun p => by
      filter_upwards [eventually_le_W d (2 * p)] with N hN a
      rw [card_blockAvg_support]; exact hN)

/-- **(4.12) for the variance-profile row, from the budgeted gain.** -/
theorem unifDomIcc_flucAvg_Sblk_iter_budget (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (ep N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N) (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ ep N ^ 2) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖flucAvg d N u (zt E u) (mE E) (fun j => Sblk (d.L N) (d.W N) i j) ω‖)
      (fun N _ _ _ => ep N * Bm N) :=
  unifDomIcc_flucAvg_iter_budget (V := fun N => d.Idx N) d hE ht1 hg hKp hBm hBK hpos hρ1 hcρ
    (fun N i => uniformWeight_Sblk i)
    (fun p => by
      filter_upwards [eventually_le_W d (2 * p)] with N hN i
      rw [card_Sblk_support]
      omega)

/-- **`hfixRow` from the budgeted gain, at the paper's size.**  The budgeted form of
`RBM.Gauss.unifDomIcc_flucRow_condExpDiag_psi`; the conclusion is literally the same. -/
theorem unifDomIcc_flucRow_condExpDiag_psi_budget (d : Dims) {δ Ψ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨlow : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
  have hW : ∀ N, (0 : ℝ) < (d.W N : ℝ) := fun N => by exact_mod_cast d.W_pos N
  have hpos : ∀ N, (0 : ℝ) < 2 * Ψ N * Ψ N := fun N => by nlinarith [hΨpos N]
  have hcρ : ∀ N, ((3 * d.W N : ℝ))⁻¹ ≤ (2 * Ψ N) ^ 2 := by
    intro N
    have h3 : ((3 * d.W N : ℝ))⁻¹ ≤ ((d.W N : ℝ))⁻¹ := by
      have hw := hW N
      rw [inv_le_inv₀ (by linarith) hw]
      linarith
    have hl := hΨlow N
    nlinarith [hl, h3]
  have hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (2 * Ψ N * Ψ N) ≤ (N : ℝ) ^ τ := flucPhiW_of_psiW d hΨW
  exact (unifDomIcc_flucAvg_Sblk_iter_budget (Bm := Ψ) (Kp := Kp) (ep := fun N => 2 * Ψ N)
    d hE ht1 hg hKp (fun N => (hΨpos N).le) hBK hpos hΨhalf hcρ).trans
    (unifDomIcc_const_Lmax (V := fun N => d.Idx N) d hE.le hδ1 hΩ hΦW)

/-- **`hfixBlk` from the budgeted gain, at the paper's size.** -/
theorem unifDomIcc_flucBlk_condExpDiag_psi_budget (d : Dims) {δ Ψ : ℕ → ℝ} (hE : |E| < 2)
    (ht1 : ∀ N, t N < 1) {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨlow : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ) :
    UnifDomIcc (P d) s t
      (fun N u (a : ZMod (d.L N)) ω =>
        ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
          * ((green (Hflow d N u ω) (zt E u) k k - mE E)
              - condExpDiag d N u (zt E u) (mE E) k ω)‖)
      (fun N u _ ω => Lmax (Hflow d N u ω) (zt E u)) := by
  have hpos : ∀ N, (0 : ℝ) < 2 * Ψ N * Ψ N := fun N => by nlinarith [hΨpos N]
  have hcρ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ (2 * Ψ N) ^ 2 := fun N => by nlinarith [hΨlow N]
  have hΦW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (2 * Ψ N * Ψ N) ≤ (N : ℝ) ^ τ := flucPhiW_of_psiW d hΨW
  exact (unifDomIcc_flucAvg_blockAvg_iter_budget (Bm := Ψ) (Kp := Kp) (ep := fun N => 2 * Ψ N)
    d hE ht1 hg hKp (fun N => (hΨpos N).le) hBK hpos hΨhalf hcρ).trans
    (unifDomIcc_const_Lmax (V := fun N => ZMod (d.L N)) d hE.le hδ1 hΩ hΦW)

/-- **(4.5) along the flow, against the *budgeted* gain interface** — T177.

Word for word `RBM.Gauss.eq45Flow_of_localLaw_gain'` (`RBM1D/Gauss/CondStableFlow.lean`), with
the one interface that was unsatisfiable replaced by its budgeted form: `hg` now asks for
`RBM.Gauss.FlucGainUpTo' … (2 * p) (2 * p)`, both budgets being exactly what the `2p`-th
moment expansion provides.  **The conclusion is verbatim `RBM.StepGlue.Eq45Flow`**, and the
unprimed versions are untouched.

This is the statement `RBM.Gauss.flucGainUpTo'_of_le_on` can feed: that theorem produces the
budgeted gain from the flow good event (4.1) alone, with no hypothesis quantified over all
sample points, and `RBM.Gauss.minorDiffGain_budget_hyps_consistent` exhibits explicit
parameters making its numeric side conditions hold at `B ≍ Ψ`. -/
theorem eq45Flow_of_localLaw_gain_budget (d : Dims) {δ Ψ : ℕ → ℝ} {Kenv B : ℝ} {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N)
    (hK : 0 ≤ K) (hδ0 : ∀ N, 0 ≤ δ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * (Ψ N * Ψ N) ≤ (N : ℝ) ^ τ)
    (hll : LocalLawUnifIcc d E s t Ψ)
    {Bp : ℕ → ℕ → ℝ} {Kp : ℕ → ℝ}
    (hg : ∀ p N, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E) (Bp p N) (2 * Ψ N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBK : ∀ p N, Bp p N ≤ Kp p * Ψ N)
    (hΨpos : ∀ N, 0 < Ψ N) (hΨhalf : ∀ N, 2 * Ψ N ≤ 1)
    (hΨW' : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * Ψ N ^ 2)
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖condExpDiag d N u (zt E u) (mE E) i ω
              - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖condExpDiag d N v (zt E v) (mE E) i ω
              - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    StepGlue.Eq45Flow (sample d) E s t :=
  eq45Flow_of_unifDom_ibp d hκ0 hκ1 hEκ hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ hΨ0 hKenv hB
    hEnv hΨlow hΨ1 hΨW hll hHolIBP hHolRow
    (unifDomIcc_flucRow_condExpDiag_psi_budget d hE ht1 hg hKp hBK hΨpos hΨhalf hΨW' hδ1 hΩ
      hΨW)
    hHolBlk
    (unifDomIcc_flucBlk_condExpDiag_psi_budget d hE ht1 hg hKp hBK hΨpos hΨhalf hΨW' hδ1 hΩ
      hΨW)

/-! #### The end-to-end probe — T177's acceptance criterion

From the flow good event (4.1) to `RBM.StepGlue.Eq45Flow`, through T169/T170 (the level
budget), T171 (the conditionalization) and T177 (the cardinality budget).  **The hypothesis
list contains no statement quantified over all sample points**: the only probabilistic inputs
are `hΩ` — (4.1) itself — and `hsmall`, a bound on the *measure* of the explicit tower
`RBM.Gauss.badTower`, which `RBM.Gauss.meas_badTower_le` reduces to `P(Ω(t,c)ᶜ)` times a fixed
power of `(ε + #rows)/ε`.

The size is the paper's: the local-law threshold is `Ψ_N = 2 δ_N`, the gain is `ρ = 2 Ψ_N` and
the constant is `B_p = 2(2 minorDiffC(2p) + 1) Ψ_N`, so the control of (4.12) is `ρ B ≍ Ψ²` with
the `p`-dependence confined to `Kp`.  `RBM.Gauss.minorDiffGain_budget_hyps_consistent` gives
explicit parameters at which the numeric conditions hold simultaneously. -/
theorem eq45Flow_of_goodSetFlow_budget (d : Dims) {δ : ℕ → ℝ} {Kenv Bx κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ) (hE : |E| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K)
    (hδpos : ∀ N, 0 < δ N) (hδ4 : ∀ N, δ N ≤ 1 / 4)
    (hδnet : ∀ᶠ N : ℕ in atTop, 1 / (N : ℝ) ^ ((K + 2 + 1) / ((1 : ℝ) / 2)) ≤ δ N)
    (hfine : ∀ᶠ N : ℕ in atTop,
      4 * ((etaT E (t N))⁻¹) ^ 3 * (N : ℝ) ^ (3 : ℕ) * δ N ^ ((1 : ℝ) / 2) ≤ 1)
    (hΩ : HighProb (P d) (goodSetFlow d E s t δ))
    (hKenv : 0 ≤ Kenv) (hBx : 0 ≤ Bx)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT E (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-Bx) ≤ (2 * δ N) * (2 * δ N))
    (hΨ1 : ∀ᶠ N : ℕ in atTop, (2 * δ N) * (2 * δ N) ≤ 1)
    (hΨW : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * ((2 * δ N) * (2 * δ N)) ≤ (N : ℝ) ^ τ)
    (hll : LocalLawUnifIcc d E s t (fun N => 2 * δ N))
    (hMδ : ∀ p N : ℕ, 8 * (2 * p) * δ N ≤ 1)
    (hδC : ∀ p N : ℕ, 2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N ≤ 1)
    (hWδ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ 4 * (2 * δ N) ^ 2)
    (hsmall : ∀ p N : ℕ, ∀ u ∈ Set.Icc (s N) (t N),
      condEnv E u (2 * p) ^ (2 * p)
          * (P d).real (badTower d N (condEps E u (2 * p) (2 * δ N))
              (badBase d E s t δ N) (2 * p + 1))
        ≤ (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N) ^ (2 * p)
            * (2 * (2 * δ N)) ^ (2 * p * (2 * p)))
    (hHolIBP : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖condExpDiag d N u (zt E u) (mE E) i ω
              - (u : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N u ω) (zt E u) k k - mE E)‖
          - ‖condExpDiag d N v (zt E v) (mE E) i ω
              - (v : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * (green (Hflow d N v ω) (zt E v) k k - mE E)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolRow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ i : d.Idx N,
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2))
    (hHolBlk : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ flowNetEvent d E s t δ N, ∀ a : ZMod (d.L N),
      ∀ u ∈ Set.Icc (s N) (t N), ∀ v ∈ Set.Icc (s N) (t N),
        |‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N u ω) (zt E u) k k - mE E)
                - condExpDiag d N u (zt E u) (mE E) k ω)‖
          - ‖∑ k, (blkCoef (d.L N) (d.W N) a k : ℂ)
              * ((green (Hflow d N v ω) (zt E v) k k - mE E)
                - condExpDiag d N v (zt E v) (mE E) k ω)‖|
          ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2)) :
    StepGlue.Eq45Flow (sample d) E s t := by
  have hδ0 : ∀ N, 0 ≤ δ N := fun N => (hδpos N).le
  have hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2 :=
    Filter.Eventually.of_forall fun N => by linarith [hδ4 N]
  have hg : ∀ p N : ℕ, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt E u) (mE E)
        (2 * (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N)) (2 * (2 * δ N))
        (2 * p) (2 * p) := by
    intro p N u hu
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hΨ : (0 : ℝ) < 2 * δ N := by linarith [hδpos N]
    have hcc : condCost E u (2 * p) (2 * δ N) (condEps E u (2 * p) (2 * δ N)) = 2 * δ N :=
      condCost_condEps hE hu1 (2 * p) hΨ
    have h := flucGainUpTo'_goodSetFlow (E := E) (s := s) (t := t) (δ := δ)
      (M := 2 * p) (n := 2 * p)
      hE hu1 hu (condEps_nonneg hE hu1 (2 * p) hΨ.le) (hδpos N) (hδ4 N)
      (by push_cast; linarith [hMδ p N])
      (by rw [hcc]; exact hδC p N) (by rw [hcc]; exact hsmall p N u hu)
    rwa [hcc] at h
  exact eq45Flow_of_localLaw_gain_budget (Ψ := fun N => 2 * δ N)
    (Bp := fun p N => 2 * (2 * minorDiffC (2 * p) * (2 * δ N) + 2 * δ N))
    (Kp := fun p => 2 * (2 * minorDiffC (2 * p) + 1))
    d hκ0 hκ1 hEκ hE hs0 ht1 hst hK hδ0 hδ1 hδnet hfine hΩ
    (fun N => by linarith [hδpos N]) hKenv hBx hEnv hΨlow hΨ1 hΨW hll hg
    (fun p => by have := minorDiffC_nonneg (2 * p); linarith)
    (fun p N => le_of_eq (by ring))
    (fun N => by linarith [hδpos N]) (fun N => by linarith [hδ4 N]) hWδ
    hHolIBP hHolRow hHolBlk

end Eq45Budget

end RBM.Gauss
