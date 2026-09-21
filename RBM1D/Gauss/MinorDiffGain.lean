/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucIterHigh

/-!
# The size of the iterated minor differences: the Leibniz calculus for `Δ_κ`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the size of the `m`-fold minor difference, which is the last input of the
fluctuation averaging (4.12).

T110 (`RBM1D/Gauss/FlucIterHigh.lean`) reduced `RBM.Gauss.FlucGain` to
`RBM.Gauss.MinorDiffGain` by an *identity*: the `m` conditional fluctuations
`Q_{κ_1} ⋯ Q_{κ_m}` compose into the `m`-fold minor difference `Δ_{κ_1} ⋯ Δ_{κ_m}`, so the
probabilistic half is already discharged and only Green's function estimates remain.  T110 did
`m ≤ 2` by hand.  This file does every `m`.

## The calculus

Differences are taken of a whole *family* of minors, `Y : Finset (Idx) → ℂ` (the level `S` is
the set of removed rows), by `Δ_κ Y^{(S)} = Y^{(S)} - Y^{(S ∪ {κ})}`
(`RBM.Gauss.deltaFam`), iterated along a list (`RBM.Gauss.iterDeltaFam`).  The two Leibniz rules
are exact:

* `RBM.Gauss.deltaFam_mul`       : `Δ_κ(Y Z) = (Δ_κ Y) Z + Y^{(κ)} (Δ_κ Z)`;
* `RBM.Gauss.deltaFam_inv_apply` : `Δ_κ(1/Y) = -(Δ_κ Y)/(Y · Y^{(κ)})`, where neither value
  vanishes.

`RBM.Gauss.minorDiff_eq_iterDeltaFam` identifies T110's `RBM.Gauss.minorDiff` with this calculus
at level `∅`, and `RBM.Gauss.deltaFam_shiftFam` / `RBM.Gauss.iterDeltaFam_shiftFam` transport
the level, which is the subtype bookkeeping of the minors done once and for all.

## The atoms and the grading

The class of families closed under `Δ_κ` consists of the *entries* `S ↦ G^{(S ∪ T)}_{ab}`
(`RBM.Gauss.gFam`) and the *inverse diagonal entries* `S ↦ (G^{(S ∪ T)}_{aa})⁻¹`
(`RBM.Gauss.gInvFam`), extended by `0` to the levels that have removed `a` or `b`
(`RBM.Gauss.gEnt`) so that no side condition travels with the recursion.  Carrying the base
level `T` is what makes the class closed under the shift.  Over it, (4.9) and the reciprocal
rule read

* `RBM.Gauss.deltaFam_gFam`    : `Δ_κ G_{ab} = G_{aκ} G_{κb} (G_{κκ})⁻¹`   — three atoms;
* `RBM.Gauss.deltaFam_gInvFam` : `Δ_κ (G_{aa})⁻¹ = -G_{aκ}G_{κa}(G_{κκ})⁻¹ (G_{aa})⁻¹
  (G^{(κ)}_{aa})⁻¹`                                                        — five atoms.

Both are proved from `RBM1D/Green/Minor.lean` (T40) through T110's
`RBM.Gauss.greenSetMat_insert_apply`, and both hold at *every* level, including the degenerate
ones where an index has already been removed.

The size is tracked by `RBM.Gauss.DiffBd Ψ I n c p Y`: "`m ≤ n` further differences along rows
outside `I` leave `‖Δ_{κ_1} ⋯ Δ_{κ_m} Y^{(S)}‖ ≤ c Ψ^{p+m}`", i.e. *each difference gains one
power of `Ψ`*.  Its closure properties — `RBM.Gauss.DiffBd.delta` (a difference raises the order
by one and locks the row out), `RBM.Gauss.DiffBd.shift`, and the product rule
`RBM.Gauss.DiffBd.mul` (orders add; the `2^m` terms of the Leibniz expansion cost `2^n`) — feed
the simultaneous induction `RBM.Gauss.diffBd_atom`, which grades the entries at order `1` and
the inverse diagonals at order `0`.

The rows must be distinct from each other and from every index the atom mentions: `Δ_κ` applied
to an entry that carries the index `κ` has *no* gain, since the shifted entry is the extension
by `0`.  That is exactly the `Nodup` hypothesis of `RBM.Gauss.MinorDiffGain`.

## What is proved

1. **The general estimate** `RBM.Gauss.norm_minorDiff_greenSetDiagCentered_le`:
   `‖Δ_{κ_1} ⋯ Δ_{κ_m}(G^{(·)}_{kk} - m)‖ ≤ C_m Ψ^{m+1}` on the good event, for every `m ≥ 1`.
   The first difference is the (4.9) triple product (order `2`) and each further difference
   gains one more `Ψ` — the gain is multiplicative at every order, as T110's identity requires.
2. **`m = 3`** `RBM.Gauss.norm_minorDiff_triple_le`: `≤ 2^91 Ψ⁴`, to be read against T110's
   `10 Ψ³` at `m = 2` and T85's `Ψ²` at `m = 1`.  The power is the point; the constant is not.
3. **The fluctuation passes through** `RBM.Gauss.minorDiff_qRow` /
   `RBM.Gauss.minorDiff_flucDiagSet_eq`: `Δ_{κ_1} ⋯ Δ_{κ_m} Q_k = Q_k Δ_{κ_1} ⋯ Δ_{κ_m}`, so
   the whole of `RBM.Gauss.MinorDiffGain` reduces to the deterministic family
   `RBM.Gauss.greenSetDiagCentered` at the price of one factor `2`.
4. **The gain for words of bounded length**
   `RBM.Gauss.integral_prod_applyOps_minorDiff_le`: the expectation bound of
   `RBM.Gauss.MinorDiffGain` with `B ≍ 1` and `ρ = 2Ψ`, for words of length at most `M`.
5. **The last probabilistic step** `RBM.Gauss.minorDiffGain_of_pointwise`: pointwise bounds on
   the words give `RBM.Gauss.MinorDiffGain` itself.
6. **The same gain at the paper's size** `RBM.Gauss.integral_prod_applyOps_minorDiff_le'`, with
   `B ≍ Ψ` instead of the deterministic envelope, and the bridges
   `RBM.Gauss.flucGainUpTo_of_minorDiff` / `RBM.Gauss.flucGainUpTo_of_minorDiff'` into the
   graded consumers of `RBM1D/Gauss/FlucIter.lean`.  See below.

## (4.2), and the size of (4.12)

`RBM.Gauss.MinorGood` carries (4.1) and (4.3), which is everything the `Δ_κ` calculus needs:
every atom it differences is an off-diagonal entry or an inverse diagonal entry.  It says
nothing about the *undifferenced* `G^{(S)}_{kk} - m`, which is the `m = 0` grade of the
expansion — the empty word — and that grade therefore had to be bounded by the deterministic
envelope `2(η_u⁻¹ + 1)`.  The gain `ρ B` delivered to (4.12) was then `Ψ η_u⁻¹`, not the
paper's `Ψ²`.

`RBM.Gauss.MinorGood'` adds the missing field, which is (4.2):
`|G^{(S)}_{aa} - m| ≤ Ψ` at every minor level.  It enters at exactly one place —
`RBM.Gauss.norm_flucDiagSet_le`, the empty-word branch of
`RBM.Gauss.integral_prod_applyOps_minorDiff_le'` — and turns `B` into `2Ψ + 2 C_M Ψ`.  The
`2p`-th moment iteration of `RBM1D/Gauss/FlucIter.lean` then delivers (4.12) with control
`ρ B ≍ Ψ²`, uniformly in `u`, with no `η_u⁻¹` anywhere.  (4.2) is not an extra burden on the
producer: at `Ψ ≤ 1/2` it *implies* (4.1), since `|m_E| = 1`
(`RBM.Gauss.minorGood'_of_local_law`).

## What is *not* proved, and why

`RBM.Gauss.MinorDiffGain` is **not** discharged, so (4.12) is **not** yet hypothesis-free.  Two
inputs are carried by `RBM.Gauss.integral_prod_applyOps_minorDiff_le` and neither is cosmetic:

* **The exceptional set.**  The estimate is conditional on `RBM.Gauss.MinorGood` holding at
  *every* sample point: the local law (4.2)–(4.3) and the lower bound (4.1) on the diagonal
  entries, at every minor level.  It holds only off an exceptional event.  Removing that
  hypothesis means splitting the integral and paying the deterministic envelope `η_t⁻¹` on the
  exceptional part — legitimate here (there are no conditional expectations left inside
  `RBM.Gauss.MinorDiffGain`, so no indicator is ever multiplied into a `Q_κ`), but it needs a
  quantitative local law, which the repository does not yet have in this form.  No indicator is
  introduced in this file.
* **Uniformity in `m`.**  `RBM.Gauss.MinorDiffGain` asks for a *single* `ρ` valid for every
  word, and the constants produced here grow with `m`: the recursion of `RBM.Gauss.atomC` is
  `c_{m+1} = 16^m c_m^5`.  This is not merely a lazy bound — differencing a reciprocal `m`
  times produces a sum over set partitions, so even the sharpest form of this argument grows
  like `m!C^m`, and no fixed `ρ ≍ Ψ` can dominate `m! C^m Ψ^{m+1}` for all `m ≤ N`.  The
  `2p`-th moment expansion that consumes (4.12) only ever uses `numQ (L i) ≤ (L i).length ≤ 2p`,
  which is why the bounded-length form proved here is the useful statement.  Recorded in
  `docs/paper-deltas.md`.

## Deviations from the paper

* The constants are not the paper's `C^m`; see above.  Only their finiteness at each fixed `m`
  is used.
* The good event is packaged as `RBM.Gauss.MinorGood`, a hypothesis at *all* levels `S` rather
  than at the levels actually reached (subsets of the differenced rows).  This is stronger than
  needed but is what the local law gives for all minors simultaneously.
* `RBM.Gauss.MinorGood.inv_le` fixes the constant `2` for `|G^{(S)}_{aa}|⁻¹`, matching T110's
  `RBM.Gauss.norm_minorDiff_pair_greenSetDiagCentered_le`.
* (4.1)–(4.3) are split across two structures: `RBM.Gauss.MinorGood` (what the difference
  calculus uses) and `RBM.Gauss.MinorGood'` (that plus (4.2), what the size of (4.12) uses).
  The paper states them together.  Both bounds are written with the *same* `Ψ`; the paper's
  (4.2) and (4.3) have the same order but are not literally the same quantity.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix Finset

/-! ### The difference calculus on families of minors -/

section Calculus

variable {α : Type*} [DecidableEq α]

/-- `Δ_κ Y`, the minor difference of the family `Y` along the row `κ`. -/
def deltaFam (κ : α) (Y : Finset α → ℂ) : Finset α → ℂ := fun S => Y S - Y (insert κ S)

/-- `Y^{(κ)}`, the family `Y` with the row `κ` removed at every level. -/
def shiftFam (κ : α) (Y : Finset α → ℂ) : Finset α → ℂ := fun S => Y (insert κ S)

/-- `Δ_{κ_1} ⋯ Δ_{κ_m} Y`, as a family (the level `S` is still free). -/
def iterDeltaFam : List α → (Finset α → ℂ) → (Finset α → ℂ)
  | [], Y => Y
  | κ :: l, Y => iterDeltaFam l (deltaFam κ Y)

@[simp] theorem deltaFam_apply (κ : α) (Y : Finset α → ℂ) (S : Finset α) :
    deltaFam κ Y S = Y S - Y (insert κ S) := rfl

@[simp] theorem shiftFam_apply (κ : α) (Y : Finset α → ℂ) (S : Finset α) :
    shiftFam κ Y S = Y (insert κ S) := rfl

@[simp] theorem iterDeltaFam_nil (Y : Finset α → ℂ) : iterDeltaFam ([] : List α) Y = Y := rfl

@[simp] theorem iterDeltaFam_cons (κ : α) (l : List α) (Y : Finset α → ℂ) :
    iterDeltaFam (κ :: l) Y = iterDeltaFam l (deltaFam κ Y) := rfl

/-- `Δ_κ` is additive. -/
theorem deltaFam_add (κ : α) (Y Z : Finset α → ℂ) :
    deltaFam κ (fun S => Y S + Z S) = fun S => deltaFam κ Y S + deltaFam κ Z S := by
  funext S; simp only [deltaFam_apply]; ring

theorem deltaFam_neg (κ : α) (Y : Finset α → ℂ) :
    deltaFam κ (fun S => -Y S) = fun S => -deltaFam κ Y S := by
  funext S; simp only [deltaFam_apply]; ring

/-- The iterated difference is additive. -/
theorem iterDeltaFam_add (l : List α) (Y Z : Finset α → ℂ) :
    iterDeltaFam l (fun S => Y S + Z S) = fun S => iterDeltaFam l Y S + iterDeltaFam l Z S := by
  induction l generalizing Y Z with
  | nil => rfl
  | cons κ l ih => rw [iterDeltaFam_cons, deltaFam_add, ih, iterDeltaFam_cons, iterDeltaFam_cons]

theorem iterDeltaFam_neg (l : List α) (Y : Finset α → ℂ) :
    iterDeltaFam l (fun S => -Y S) = fun S => -iterDeltaFam l Y S := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ l ih => rw [iterDeltaFam_cons, deltaFam_neg, ih, iterDeltaFam_cons]

/-- `Δ_κ` and the shift `·^{(κ')}` commute. -/
theorem deltaFam_shiftFam (κ κ' : α) (Y : Finset α → ℂ) :
    deltaFam κ (shiftFam κ' Y) = shiftFam κ' (deltaFam κ Y) := by
  funext S
  simp only [deltaFam_apply, shiftFam_apply, Finset.insert_comm]

/-- The iterated difference commutes with the shift. -/
theorem iterDeltaFam_shiftFam (l : List α) (κ : α) (Y : Finset α → ℂ) :
    iterDeltaFam l (shiftFam κ Y) = shiftFam κ (iterDeltaFam l Y) := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ' l ih => rw [iterDeltaFam_cons, deltaFam_shiftFam, ih, iterDeltaFam_cons]

/-- **The Leibniz rule for `Δ_κ`**: `Δ_κ(Y Z) = (Δ_κ Y) Z + Y^{(κ)} (Δ_κ Z)`. -/
theorem deltaFam_mul (κ : α) (Y Z : Finset α → ℂ) :
    deltaFam κ (fun S => Y S * Z S)
      = fun S => deltaFam κ Y S * Z S + shiftFam κ Y S * deltaFam κ Z S := by
  funext S
  simp only [deltaFam_apply, shiftFam_apply]
  ring

/-- **The Leibniz rule for the reciprocal**: `Δ_κ(1/Y) = -(Δ_κ Y)/(Y · Y^{(κ)})`.  Both values
must be non-zero: with Lean's `0⁻¹ = 0` the identity is false at a vanishing level. -/
theorem deltaFam_inv_apply (κ : α) (Y : Finset α → ℂ) (S : Finset α)
    (h : Y S ≠ 0) (h' : Y (insert κ S) ≠ 0) :
    deltaFam κ (fun S => (Y S)⁻¹) S
      = -(deltaFam κ Y S * (Y S)⁻¹ * (Y (insert κ S))⁻¹) := by
  simp only [deltaFam_apply]
  field_simp
  ring

end Calculus


/-! ### The graded bound: one power of `Ψ` per difference -/

section Graded

variable {α : Type*} [DecidableEq α]

/-- **`Y` is of order `p` with constant `c`, up to `n` differences.**  Taking `m ≤ n` further
differences along rows *outside* `I` gains `m` powers of `Ψ`:

  `‖Δ_{κ_1} ⋯ Δ_{κ_m} Y^{(S)}‖ ≤ c Ψ^{p + m}`.

The rows must be distinct (`l.Nodup`) and must avoid `I`, the set of indices the family already
mentions: `Δ_κ` applied to a Green's function entry carrying the index `κ` has no gain. -/
def DiffBd (Ψ : ℝ) (I : Finset α) (n : ℕ) (c : ℝ) (p : ℕ) (Y : Finset α → ℂ) : Prop :=
  ∀ (l : List α) (S : Finset α), l.Nodup → (∀ κ ∈ l, κ ∉ I) → l.length ≤ n →
    ‖iterDeltaFam l Y S‖ ≤ c * Ψ ^ (p + l.length)

theorem DiffBd.le_self {Ψ : ℝ} {I : Finset α} {n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) (S : Finset α) : ‖Y S‖ ≤ c * Ψ ^ p := by
  simpa using h [] S (by simp) (by simp) (by simp)

/-- No differences at all: a plain bound. -/
theorem diffBd_zero {Ψ : ℝ} {I : Finset α} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : ∀ S, ‖Y S‖ ≤ c * Ψ ^ p) : DiffBd Ψ I 0 c p Y := by
  intro l S _ _ hlen
  have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
  subst hl
  simpa using h S

theorem DiffBd.mono_I {Ψ : ℝ} {I I' : Finset α} {n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) (hII : I ⊆ I') : DiffBd Ψ I' n c p Y :=
  fun l S hnd hav hlen => h l S hnd (fun κ hκ => fun hmem => hav κ hκ (hII hmem)) hlen

theorem DiffBd.mono_n {Ψ : ℝ} {I : Finset α} {n n' : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) (hn : n' ≤ n) : DiffBd Ψ I n' c p Y :=
  fun l S hnd hav hlen => h l S hnd hav (le_trans hlen hn)

theorem DiffBd.mono_c {Ψ : ℝ} {I : Finset α} {n : ℕ} {c c' : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) (hΨ : 0 ≤ Ψ) (hc : c ≤ c') : DiffBd Ψ I n c' p Y := by
  intro l S hnd hav hlen
  exact le_trans (h l S hnd hav hlen) (by
    have : (0:ℝ) ≤ Ψ ^ (p + l.length) := pow_nonneg hΨ _
    nlinarith)

/-- A lower order is a weaker statement, as `Ψ ≤ 1`. -/
theorem DiffBd.mono_p {Ψ : ℝ} {I : Finset α} {n : ℕ} {c : ℝ} {p p' : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hc : 0 ≤ c) (hp : p' ≤ p) :
    DiffBd Ψ I n c p' Y := by
  intro l S hnd hav hlen
  refine le_trans (h l S hnd hav hlen) ?_
  have : Ψ ^ (p + l.length) ≤ Ψ ^ (p' + l.length) :=
    pow_le_pow_of_le_one hΨ0 hΨ1 (by omega)
  nlinarith

/-- **One difference raises the order by one** (and locks the row out of later differences). -/
theorem DiffBd.delta {Ψ : ℝ} {I : Finset α} {n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    {κ : α} (hκ : κ ∉ I) (h : DiffBd Ψ I (n + 1) c p Y) :
    DiffBd Ψ (insert κ I) n c (p + 1) (deltaFam κ Y) := by
  intro l S hnd hav hlen
  have hκl : κ ∉ l := fun hm => (hav κ hm) (Finset.mem_insert_self κ I)
  have hnd' : (κ :: l).Nodup := List.nodup_cons.2 ⟨hκl, hnd⟩
  have hav' : ∀ κ' ∈ (κ :: l), κ' ∉ I := by
    intro κ' hκ'
    rcases List.mem_cons.1 hκ' with h1 | h1
    · exact h1 ▸ hκ
    · exact fun hm => hav κ' h1 (Finset.mem_insert_of_mem hm)
  have := h (κ :: l) S hnd' hav' (by simp [List.length_cons]; omega)
  rw [iterDeltaFam_cons] at this
  have hexp : p + (κ :: l).length = p + 1 + l.length := by simp [List.length_cons]; omega
  rwa [hexp] at this

/-- The shift is free: it only moves the level. -/
theorem DiffBd.shift {Ψ : ℝ} {I : Finset α} {n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) (κ : α) : DiffBd Ψ I n c p (shiftFam κ Y) := by
  intro l S hnd hav hlen
  rw [iterDeltaFam_shiftFam, shiftFam_apply]
  exact h l (insert κ S) hnd hav hlen

theorem DiffBd.neg {Ψ : ℝ} {I : Finset α} {n : ℕ} {c : ℝ} {p : ℕ} {Y : Finset α → ℂ}
    (h : DiffBd Ψ I n c p Y) : DiffBd Ψ I n c p (fun S => -Y S) := by
  intro l S hnd hav hlen
  rw [iterDeltaFam_neg]
  simpa using h l S hnd hav hlen

/-- **The product rule for the graded bound.**  Orders add; the price of the `2^{m}` terms of
the `m`-fold Leibniz expansion is the factor `2^n`. -/
theorem DiffBd.mul {Ψ : ℝ} (hΨ : 0 ≤ Ψ) :
    ∀ (n : ℕ) {I : Finset α} {c₁ c₂ : ℝ} {p q : ℕ} {Y Z : Finset α → ℂ},
      0 ≤ c₁ → 0 ≤ c₂ → DiffBd Ψ I n c₁ p Y → DiffBd Ψ I n c₂ q Z →
      DiffBd Ψ I n (2 ^ n * (c₁ * c₂)) (p + q) (fun S => Y S * Z S) := by
  intro n
  induction n with
  | zero =>
      intro I c₁ c₂ p q Y Z hc₁ hc₂ hY hZ l S hnd hav hlen
      have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst hl
      have h1 := hY.le_self S
      have h2 := hZ.le_self S
      have hp1 : (0:ℝ) ≤ Ψ ^ p := pow_nonneg hΨ _
      have hp2 : (0:ℝ) ≤ Ψ ^ q := pow_nonneg hΨ _
      have : ‖Y S * Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := by
        rw [norm_mul]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      simpa [pow_add] using le_trans this (le_of_eq (by ring))
  | succ n ih =>
      intro I c₁ c₂ p q Y Z hc₁ hc₂ hY hZ l S hnd hav hlen
      match l with
      | [] =>
          have h1 := hY.le_self S
          have h2 := hZ.le_self S
          have hp1 : (0:ℝ) ≤ Ψ ^ p := pow_nonneg hΨ _
          have hp2 : (0:ℝ) ≤ Ψ ^ q := pow_nonneg hΨ _
          have hmul : ‖Y S * Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := by
            rw [norm_mul]
            exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          have hpow : (1:ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
          simp only [iterDeltaFam_nil, List.length_nil, Nat.add_zero]
          have : (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) = (c₁ * c₂) * Ψ ^ (p + q) := by
            rw [pow_add]; ring
          rw [this] at hmul
          refine le_trans hmul ?_
          have hnn : (0:ℝ) ≤ (c₁ * c₂) * Ψ ^ (p + q) := by positivity
          nlinarith [pow_nonneg hΨ (p + q)]
      | κ :: l' =>
          have hκI : κ ∉ I := hav κ (List.mem_cons_self ..)
          have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
          have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
          have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
            intro κ' hκ' hmem
            rcases Finset.mem_insert.1 hmem with h1 | h1
            · exact hκl' (h1 ▸ hκ')
            · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
          have hlen' : l'.length ≤ n := by
            simp only [List.length_cons] at hlen; omega
          have hδY : DiffBd Ψ (insert κ I) n c₁ (p + 1) (deltaFam κ Y) := hY.delta hκI
          have hδZ : DiffBd Ψ (insert κ I) n c₂ (q + 1) (deltaFam κ Z) := hZ.delta hκI
          have hYs : DiffBd Ψ (insert κ I) n c₁ p (shiftFam κ Y) :=
            ((hY.mono_n (Nat.le_succ n)).mono_I (Finset.subset_insert κ I)).shift κ
          have hZ' : DiffBd Ψ (insert κ I) n c₂ q Z :=
            (hZ.mono_n (Nat.le_succ n)).mono_I (Finset.subset_insert κ I)
          have hA := ih hc₁ hc₂ hδY hZ' l' S hnd' hav' hlen'
          have hB := ih hc₁ hc₂ hYs hδZ l' S hnd' hav' hlen'
          have hsplit : iterDeltaFam (κ :: l') (fun S => Y S * Z S) S
              = iterDeltaFam l' (fun S => deltaFam κ Y S * Z S) S
                + iterDeltaFam l' (fun S => shiftFam κ Y S * deltaFam κ Z S) S := by
            rw [iterDeltaFam_cons, deltaFam_mul, iterDeltaFam_add]
          rw [hsplit]
          have htri := norm_add_le (iterDeltaFam l' (fun S => deltaFam κ Y S * Z S) S)
            (iterDeltaFam l' (fun S => shiftFam κ Y S * deltaFam κ Z S) S)
          have he1 : p + 1 + q + l'.length = p + q + (κ :: l').length := by
            simp [List.length_cons]; omega
          have he2 : p + (q + 1) + l'.length = p + q + (κ :: l').length := by
            simp [List.length_cons]; omega
          rw [he1] at hA
          rw [he2] at hB
          have hfin : 2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length)
              + 2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length)
              ≤ 2 ^ (n + 1) * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length) := by
            rw [pow_succ]; ring_nf; nlinarith [pow_nonneg hΨ (p + q + (κ :: l').length)]
          linarith

end Graded

/-! ### The bridge to `RBM.Gauss.minorDiff` -/

variable {d : Dims} {N : ℕ}

/-- `RBM.Gauss.minorDiff` is the iterated difference of the family, evaluated at level `∅`. -/
theorem minorDiff_eq_iterDeltaFam (l : List (d.Idx N)) (Y : Finset (d.Idx N) → Ω d → ℂ)
    (ω : Ω d) : minorDiff d N l Y ω = iterDeltaFam l (fun S => Y S ω) ∅ := by
  induction l generalizing Y with
  | nil => rfl
  | cons κ l ih =>
      rw [minorDiff_cons, ih, iterDeltaFam_cons]
      rfl


/-! ### The Green's function atoms -/

section Atoms

/-- `G^{(S)}_{ab}`, extended by `0` to the levels that have removed `a` or `b`.  The extension is
what makes the difference calculus total: no side condition is carried along the recursion. -/
noncomputable def gEnt (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d) (a b : d.Idx N)
    (S : Finset (d.Idx N)) : ℂ :=
  if ha : a ∉ S then (if hb : b ∉ S then greenSetMat d N u z S ω ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0

variable {u : ℝ} {z : ℂ} {ω : Ω d} {a b κ : d.Idx N} {S T : Finset (d.Idx N)}

theorem gEnt_apply (ha : a ∉ S) (hb : b ∉ S) :
    gEnt d N u z ω a b S = greenSetMat d N u z S ω ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [gEnt, dite_eq_left ha, dite_eq_left hb]

theorem gEnt_eq_zero_left (h : a ∈ S) : gEnt d N u z ω a b S = 0 := by
  rw [gEnt, dite_eq_right (not_not_intro h)]

theorem gEnt_eq_zero_right (h : b ∈ S) : gEnt d N u z ω a b S = 0 := by
  rw [gEnt]
  by_cases ha : a ∉ S
  · rw [dite_eq_left ha, dite_eq_right (not_not_intro h)]
  · rw [dite_eq_right ha]

/-- The family `S ↦ G^{(S ∪ T)}_{ab}`: an *atom* of the calculus.  Carrying the base level `T`
is what makes the class of atoms closed under the shift `Y ↦ Y^{(κ)}`. -/
noncomputable def gFam (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d) (a b : d.Idx N)
    (T : Finset (d.Idx N)) : Finset (d.Idx N) → ℂ := fun S => gEnt d N u z ω a b (S ∪ T)

/-- The family `S ↦ (G^{(S ∪ T)}_{aa})⁻¹`, the second kind of atom. -/
noncomputable def gInvFam (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d) (a : d.Idx N)
    (T : Finset (d.Idx N)) : Finset (d.Idx N) → ℂ := fun S => (gEnt d N u z ω a a (S ∪ T))⁻¹

@[simp] theorem gFam_apply (a b : d.Idx N) (T S : Finset (d.Idx N)) :
    gFam d N u z ω a b T S = gEnt d N u z ω a b (S ∪ T) := rfl

@[simp] theorem gInvFam_apply (a : d.Idx N) (T S : Finset (d.Idx N)) :
    gInvFam d N u z ω a T S = (gEnt d N u z ω a a (S ∪ T))⁻¹ := rfl

theorem shiftFam_gFam (a b κ : d.Idx N) (T : Finset (d.Idx N)) :
    shiftFam κ (gFam d N u z ω a b T) = gFam d N u z ω a b (insert κ T) := by
  funext S
  simp only [shiftFam_apply, gFam_apply, Finset.insert_union, Finset.union_insert]

theorem shiftFam_gInvFam (a κ : d.Idx N) (T : Finset (d.Idx N)) :
    shiftFam κ (gInvFam d N u z ω a T) = gInvFam d N u z ω a (insert κ T) := by
  funext S
  simp only [shiftFam_apply, gInvFam_apply, Finset.insert_union, Finset.union_insert]

/-- **The local law on the good event, at every minor level.**  This is (4.1) together with
(4.2)–(4.3) for the sample point `ω`, read off all the minors at once: every minor is
invertible, its diagonal entries are non-zero with bounded inverses, and its off-diagonal
entries are at most `Ψ`.  Everything below is conditional on it — no indicator is ever
introduced, the hypothesis is simply carried. -/
structure MinorGood (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d) (Ψ : ℝ) : Prop where
  /-- Every minor of `H_u - z` is invertible. -/
  det : ∀ S : Finset (d.Idx N), IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det
  /-- The diagonal entries of every minor are non-zero -- (4.1). -/
  diag_ne : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), a ∉ S → gEnt d N u z ω a a S ≠ 0
  /-- `|G^{(S)}_{aa}|⁻¹ ≤ 2` -- the quantitative form of (4.1). -/
  inv_le : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), ‖(gEnt d N u z ω a a S)⁻¹‖ ≤ 2
  /-- `|G^{(S)}_{ab}| ≤ Ψ` for `a ≠ b` -- (4.3). -/
  off_le : ∀ (S : Finset (d.Idx N)) (a b : d.Idx N), a ≠ b → ‖gEnt d N u z ω a b S‖ ≤ Ψ

/-- **The shape in which the good event (4.1) actually arrives.**  `1/2 ≤ |G^{(S)}_{aa}|` is
`RBM.GoodEvent.half_le_norm_diag` applied to every minor; it gives both the non-vanishing and
the bound `2` on the inverse. -/
theorem minorGood_of_half_le
    (hdet : ∀ S : Finset (d.Idx N), IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det)
    (hhalf : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), a ∉ S → 1 / 2 ≤ ‖gEnt d N u z ω a a S‖)
    (hoff : ∀ (S : Finset (d.Idx N)) (a b : d.Idx N), a ≠ b → ‖gEnt d N u z ω a b S‖ ≤ Ψ) :
    MinorGood d N u z ω Ψ where
  det := hdet
  diag_ne := by
    intro S a ha h0
    have := hhalf S a ha
    rw [h0, norm_zero] at this
    norm_num at this
  inv_le := by
    intro S a
    by_cases ha : a ∉ S
    · have h := hhalf S a ha
      rw [norm_inv]
      have hpos : (0 : ℝ) < ‖gEnt d N u z ω a a S‖ := by linarith
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    · rw [gEnt_eq_zero_left (not_not.1 ha), _root_.inv_zero, norm_zero]
      norm_num
  off_le := hoff

/-- **`RBM.Gauss.MinorGood` together with the diagonal half of the local law, (4.2).**

`RBM.Gauss.MinorGood` carries (4.1) and (4.3) only, which is all the Leibniz calculus of the
`Δ_κ`'s needs: every atom it differences is either an off-diagonal entry or an inverse
diagonal entry.  The *undifferenced* entry `G^{(S)}_{aa} - m` — the `m = 0` grade of the
expansion, i.e. the empty word — is not an atom of that calculus, and `RBM.Gauss.MinorGood`
says nothing about it beyond `|G^{(S)}_{aa}|⁻¹ ≤ 2`.  Adding (4.2) is what turns the constant
`B` of the gain from the deterministic envelope `2(η_u⁻¹ + 1)` into `≍ Ψ`, and hence (4.12)
from `Ψ η_u⁻¹` into the paper's `Ψ²`.

The extra field is stated only at the levels `S` that do not remove `a`; at the others
`RBM.Gauss.gEnt` is `0` by convention and `‖0 - m‖ = |m|` is of course not `≤ Ψ`. -/
structure MinorGood' (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (ω : Ω d) (Ψ : ℝ)
    : Prop extends MinorGood d N u z ω Ψ where
  /-- `|G^{(S)}_{aa} - m| ≤ Ψ` at every minor level -- (4.2). -/
  diag_sub_le : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), a ∉ S →
    ‖gEnt d N u z ω a a S - m‖ ≤ Ψ

/-- **The shape in which (4.1)–(4.3) actually arrive**, with the diagonal half added.  The
bound `2` on `|G^{(S)}_{aa}|⁻¹` is not assumed separately: it follows from
`|G^{(S)}_{aa} - m| ≤ Ψ` and `1/2 ≤ |G^{(S)}_{aa}|`, exactly as in
`RBM.Gauss.minorGood_of_half_le`. -/
theorem minorGood'_of_half_le {m : ℂ}
    (hdet : ∀ S : Finset (d.Idx N), IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det)
    (hhalf : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), a ∉ S → 1 / 2 ≤ ‖gEnt d N u z ω a a S‖)
    (hoff : ∀ (S : Finset (d.Idx N)) (a b : d.Idx N), a ≠ b → ‖gEnt d N u z ω a b S‖ ≤ Ψ)
    (hdiag : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), a ∉ S →
      ‖gEnt d N u z ω a a S - m‖ ≤ Ψ) :
    MinorGood' d N u z m ω Ψ where
  toMinorGood := minorGood_of_half_le hdet hhalf hoff
  diag_sub_le := hdiag

/-- **(4.9) for the extended entries.** -/
theorem gEnt_insert (hg : MinorGood d N u z ω Ψ) (hκ : κ ∉ S)
    (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt d N u z ω a b (insert κ S)
      = gEnt d N u z ω a b S - gEnt d N u z ω a κ S * gEnt d N u z ω κ b S
          * (gEnt d N u z ω κ κ S)⁻¹ := by
  have ha' : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
  have hb' : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
  have hne : greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0 := by
    have := hg.diag_ne S κ hκ
    rwa [gEnt_apply hκ hκ] at this
  rw [gEnt_apply ha hb, gEnt_apply ha' hb', gEnt_apply ha' hκ, gEnt_apply hκ hb',
    gEnt_apply hκ hκ,
    greenSetMat_insert_apply d N u z S ω hκ (hg.det S) hne ha hb, div_eq_mul_inv, mul_assoc]

/-- **The difference of an entry atom is a product of three atoms** -- (4.9) in the form the
calculus uses.  Two off-diagonal entries and one inverse diagonal entry: order `1 + 1 + 0 = 2`,
one more than the order `1` of what was differenced.  This is the gain, and it is exact. -/
theorem deltaFam_gFam (hg : MinorGood d N u z ω Ψ) (a b κ : d.Idx N) (T : Finset (d.Idx N)) :
    deltaFam κ (gFam d N u z ω a b T)
      = fun S => gFam d N u z ω a κ T S * gFam d N u z ω κ b T S
          * gInvFam d N u z ω κ T S := by
  funext S
  set U := S ∪ T with hU
  have hins : insert κ S ∪ T = insert κ U := by rw [hU, Finset.insert_union]
  simp only [deltaFam_apply, gFam_apply, gInvFam_apply, ← hU, hins]
  by_cases hκU : κ ∈ U
  · rw [Finset.insert_eq_self.2 hκU, gEnt_eq_zero_right hκU]
    ring
  · by_cases haU : a ∈ U
    · rw [gEnt_eq_zero_left haU, gEnt_eq_zero_left (Finset.mem_insert_of_mem haU),
        gEnt_eq_zero_left haU]
      ring
    · by_cases hbU : b ∈ U
      · rw [gEnt_eq_zero_right hbU, gEnt_eq_zero_right (Finset.mem_insert_of_mem hbU),
          gEnt_eq_zero_right hbU]
        ring
      · have hdiag : gEnt d N u z ω κ κ U ≠ 0 := hg.diag_ne U κ hκU
        by_cases hak : a = κ
        · subst hak
          rw [gEnt_eq_zero_left (Finset.mem_insert_self a U), sub_zero]
          field_simp
        · by_cases hbk : b = κ
          · subst hbk
            rw [gEnt_eq_zero_right (Finset.mem_insert_self b U), sub_zero]
            field_simp
          · have ha' : a ∉ insert κ U := by
              simp only [Finset.mem_insert, not_or]
              exact ⟨hak, haU⟩
            have hb' : b ∉ insert κ U := by
              simp only [Finset.mem_insert, not_or]
              exact ⟨hbk, hbU⟩
            rw [gEnt_insert hg hκU ha' hb']
            ring

/-- **The difference of an inverse-diagonal atom is a product of five atoms.**  It gains *two*
powers of `Ψ`, one more than required, because the numerator is itself a first difference. -/
theorem deltaFam_gInvFam (hg : MinorGood d N u z ω Ψ) (a κ : d.Idx N) (hak : a ≠ κ)
    (T : Finset (d.Idx N)) :
    deltaFam κ (gInvFam d N u z ω a T)
      = fun S => -(gFam d N u z ω a κ T S * gFam d N u z ω κ a T S
          * gInvFam d N u z ω κ T S * gInvFam d N u z ω a T S
          * shiftFam κ (gInvFam d N u z ω a T) S) := by
  funext S
  by_cases haU : a ∈ S ∪ T
  · have h1 : gEnt d N u z ω a a (S ∪ T) = 0 := gEnt_eq_zero_left haU
    have h2 : gEnt d N u z ω a a (insert κ S ∪ T) = 0 := by
      rw [Finset.insert_union]
      exact gEnt_eq_zero_left (Finset.mem_insert_of_mem haU)
    have h3 : gEnt d N u z ω a κ (S ∪ T) = 0 := gEnt_eq_zero_left haU
    simp only [deltaFam_apply, gInvFam_apply, gFam_apply, shiftFam_apply, h1, h2, h3]
    simp
  · have haU' : a ∉ insert κ S ∪ T := by
      rw [Finset.insert_union]
      simp only [Finset.mem_insert, not_or]
      exact ⟨hak, haU⟩
    have h1 : gFam d N u z ω a a T S ≠ 0 := hg.diag_ne _ a haU
    have h2 : gFam d N u z ω a a T (insert κ S) ≠ 0 := hg.diag_ne _ a haU'
    have hinv := deltaFam_inv_apply κ (gFam d N u z ω a a T) S h1 h2
    have hdel := congrFun (deltaFam_gFam hg a a κ T) S
    show deltaFam κ (fun S => (gFam d N u z ω a a T S)⁻¹) S = _
    rw [hinv, hdel]
    simp only [shiftFam_apply, gInvFam_apply, gFam_apply, Finset.insert_union]

end Atoms


/-! ### The `n`-fold estimate for the atoms -/

section AtomInduction

/-- The constant of the `n`-fold difference estimate.  It is not the paper's: the recursion is
`c_{n+1} = 16^n c_n^5`, coming from the five atoms of the reciprocal rule and the `2^n` terms of
each Leibniz expansion.  Only its finiteness for each fixed `n` is used. -/
noncomputable def atomC : ℕ → ℝ
  | 0 => 2
  | n + 1 => 16 ^ n * atomC n ^ 5

@[simp] theorem atomC_zero : atomC 0 = 2 := rfl

@[simp] theorem atomC_succ (n : ℕ) : atomC (n + 1) = 16 ^ n * atomC n ^ 5 := rfl

theorem two_le_atomC : ∀ n : ℕ, (2 : ℝ) ≤ atomC n
  | 0 => le_of_eq atomC_zero.symm
  | n + 1 => by
      have h := two_le_atomC n
      have h5 : (2 : ℝ) ^ 5 ≤ atomC n ^ 5 := pow_le_pow_left₀ (by norm_num) h 5
      have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
      rw [atomC_succ]
      nlinarith

theorem one_le_atomC (n : ℕ) : (1 : ℝ) ≤ atomC n := le_trans (by norm_num) (two_le_atomC n)

theorem atomC_nonneg (n : ℕ) : (0 : ℝ) ≤ atomC n := le_trans (by norm_num) (one_le_atomC n)

variable {u : ℝ} {z : ℂ} {ω : Ω d} {Ψ : ℝ}

/-- **The `n`-fold difference estimate for the two kinds of atom, proved together.**

For rows `κ_1, …, κ_m` distinct from each other and from every index the atom mentions,

  `‖Δ_{κ_1} ⋯ Δ_{κ_m} G^{(·)}_{ab}‖ ≤ c_m Ψ^{m+1}`   (`a ≠ b`),
  `‖Δ_{κ_1} ⋯ Δ_{κ_m} (G^{(·)}_{aa})⁻¹‖ ≤ c_m Ψ^{m}`.

Each difference gains a power of `Ψ`; the two rules that drive the induction are (4.9)
(`RBM.Gauss.deltaFam_gFam`, three atoms, order `2`) and the reciprocal rule
(`RBM.Gauss.deltaFam_gInvFam`, five atoms, order `2`), combined by the Leibniz product rule
`RBM.Gauss.DiffBd.mul`. -/
theorem diffBd_atom (hg : MinorGood d N u z ω Ψ) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) :
    ∀ (n : ℕ) (I T : Finset (d.Idx N)),
      (∀ a b : d.Idx N, a ∈ I → b ∈ I → a ≠ b →
        DiffBd Ψ I n (atomC n) 1 (gFam d N u z ω a b T))
      ∧ (∀ a : d.Idx N, a ∈ I → DiffBd Ψ I n (atomC n) 0 (gInvFam d N u z ω a T)) := by
  intro n
  induction n with
  | zero =>
      intro I T
      refine ⟨fun a b _ _ hab => diffBd_zero fun S => ?_, fun a _ => diffBd_zero fun S => ?_⟩
      · have h := hg.off_le (S ∪ T) a b hab
        simp only [gFam_apply, atomC_zero, pow_one]
        linarith
      · have h := hg.inv_le (S ∪ T) a
        simpa using h
  | succ n ih =>
      intro I T
      have hc0 : (0 : ℝ) ≤ atomC n := atomC_nonneg n
      have hc1 : (1 : ℝ) ≤ atomC n := one_le_atomC n
      have hCsucc : (1 : ℝ) ≤ atomC (n + 1) := one_le_atomC (n + 1)
      have hCsucc0 : (0 : ℝ) ≤ atomC (n + 1) := atomC_nonneg (n + 1)
      constructor
      · intro a b ha hb hab l S hnd hav hlen
        match l with
        | [] =>
            have h := hg.off_le (S ∪ T) a b hab
            simp only [iterDeltaFam_nil, List.length_nil, gFam_apply, Nat.add_zero, pow_one]
            nlinarith
        | κ :: l' =>
            have hκI : κ ∉ I := hav κ List.mem_cons_self
            have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
            have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
            have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
              intro κ' hκ' hmem
              rcases Finset.mem_insert.1 hmem with h1 | h1
              · exact hκl' (h1 ▸ hκ')
              · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
            have hlen' : l'.length ≤ n := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨ihoff, ihinv⟩ := ih (insert κ I) T
            have haκ : a ≠ κ := fun h => hκI (h ▸ ha)
            have hκb : κ ≠ b := fun h => hκI (h ▸ hb)
            have hA := ihoff a κ (Finset.mem_insert_of_mem ha) (Finset.mem_insert_self κ I) haκ
            have hB := ihoff κ b (Finset.mem_insert_self κ I) (Finset.mem_insert_of_mem hb) hκb
            have hC := ihinv κ (Finset.mem_insert_self κ I)
            have hAB := DiffBd.mul hΨ0 n hc0 hc0 hA hB
            have hABC := DiffBd.mul hΨ0 n (by positivity) hc0 hAB hC
            have hle : (2 : ℝ) ^ n * (2 ^ n * (atomC n * atomC n) * atomC n) ≤ atomC (n + 1) := by
              have hexp : (2 : ℝ) ^ n * (2 ^ n * (atomC n * atomC n) * atomC n)
                  = (2 ^ n * 2 ^ n) * atomC n ^ 3 := by ring
              have h4 : (2 : ℝ) ^ n * 2 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
              have hc3 : atomC n ^ 3 ≤ atomC n ^ 5 := pow_le_pow_right₀ hc1 (by norm_num)
              have h416 : (4 : ℝ) ^ n ≤ 16 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
              rw [hexp, h4, atomC_succ]
              exact mul_le_mul h416 hc3 (pow_nonneg hc0 3) (pow_nonneg (by norm_num) n)
            have hkey : DiffBd Ψ (insert κ I) n (atomC (n + 1)) 2
                (deltaFam κ (gFam d N u z ω a b T)) := by
              rw [deltaFam_gFam hg a b κ T]
              exact hABC.mono_c hΨ0 hle
            have hres := hkey l' S hnd' hav' hlen'
            rw [iterDeltaFam_cons]
            have hexp2 : 2 + l'.length = 1 + (κ :: l').length := by
              simp only [List.length_cons]; omega
            rwa [hexp2] at hres
      · intro a ha l S hnd hav hlen
        match l with
        | [] =>
            have h := hg.inv_le (S ∪ T) a
            simp only [iterDeltaFam_nil, List.length_nil, gInvFam_apply, Nat.add_zero, pow_zero,
              mul_one]
            exact le_trans h (two_le_atomC (n + 1))
        | κ :: l' =>
            have hκI : κ ∉ I := hav κ List.mem_cons_self
            have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
            have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
            have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
              intro κ' hκ' hmem
              rcases Finset.mem_insert.1 hmem with h1 | h1
              · exact hκl' (h1 ▸ hκ')
              · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
            have hlen' : l'.length ≤ n := by
              simp only [List.length_cons] at hlen; omega
            obtain ⟨ihoff, ihinv⟩ := ih (insert κ I) T
            have haκ : a ≠ κ := fun h => hκI (h ▸ ha)
            have hA := ihoff a κ (Finset.mem_insert_of_mem ha) (Finset.mem_insert_self κ I) haκ
            have hB := ihoff κ a (Finset.mem_insert_self κ I) (Finset.mem_insert_of_mem ha)
              (fun h => haκ h.symm)
            have hC := ihinv κ (Finset.mem_insert_self κ I)
            have hD := ihinv a (Finset.mem_insert_of_mem ha)
            have hE := hD.shift κ
            have h1 := DiffBd.mul hΨ0 n hc0 hc0 hA hB
            have h2 := DiffBd.mul hΨ0 n (by positivity) hc0 h1 hC
            have h3 := DiffBd.mul hΨ0 n (by positivity) hc0 h2 hD
            have h4 := DiffBd.mul hΨ0 n (by positivity) hc0 h3 hE
            have hle : (2 : ℝ) ^ n * (2 ^ n * (2 ^ n * (2 ^ n * (atomC n * atomC n) * atomC n)
                * atomC n) * atomC n) ≤ atomC (n + 1) := by
              have hexp : (2 : ℝ) ^ n * (2 ^ n * (2 ^ n * (2 ^ n * (atomC n * atomC n) * atomC n)
                  * atomC n) * atomC n) = (2 ^ n * 2 ^ n * 2 ^ n * 2 ^ n) * atomC n ^ 5 := by ring
              have h16 : (2 : ℝ) ^ n * 2 ^ n * 2 ^ n * 2 ^ n = 16 ^ n := by
                rw [← mul_pow, ← mul_pow, ← mul_pow]; norm_num
              rw [hexp, h16, atomC_succ]
            have hkey : DiffBd Ψ (insert κ I) n (atomC (n + 1)) 1
                (deltaFam κ (gInvFam d N u z ω a T)) := by
              rw [deltaFam_gInvFam hg a κ haκ T]
              exact ((h4.mono_c hΨ0 hle).neg).mono_p hΨ0 hΨ1 hCsucc0 (by norm_num)
            have hres := hkey l' S hnd' hav' hlen'
            rw [iterDeltaFam_cons]
            have hexp2 : 1 + l'.length = 0 + (κ :: l').length := by
              simp only [List.length_cons]; omega
            rwa [hexp2] at hres

end AtomInduction


/-! ### The `m`-fold difference of the centred diagonal entry -/

section TopLevel

variable {u : ℝ} {z m : ℂ} {ω : Ω d} {Ψ : ℝ}

/-- **The first difference of `G^{(·)}_{kk} - m` is the (4.9) triple product.**  The centring
constant `m` cancels, and the extension by `0` at the levels containing `k` is harmless. -/
theorem deltaFam_greenSetDiagCentered (hg : MinorGood d N u z ω Ψ) (k κ : d.Idx N)
    (hkκ : k ≠ κ) :
    deltaFam κ (fun S => greenSetDiagCentered d N u z m k S ω)
      = fun S => gFam d N u z ω k κ ∅ S * gFam d N u z ω κ k ∅ S
          * gInvFam d N u z ω κ ∅ S := by
  rw [← deltaFam_gFam hg k k κ ∅]
  funext S
  simp only [deltaFam_apply, gFam_apply, Finset.union_empty, greenSetDiagCentered]
  by_cases hk : k ∉ S
  · have hk' : k ∉ insert κ S := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hkκ, hk⟩
    rw [dite_eq_left hk, dite_eq_left hk', gEnt_apply hk hk, gEnt_apply hk' hk']
    ring
  · have hkS : k ∈ S := not_not.1 hk
    have hk' : k ∈ insert κ S := Finset.mem_insert_of_mem hkS
    rw [dite_eq_right hk, dite_eq_right (not_not_intro hk'), gEnt_eq_zero_left hkS,
      gEnt_eq_zero_left hk']

/-- The constant of the `m`-fold estimate: three atoms, each carried through `m - 1`
differences. -/
noncomputable def minorDiffC (n : ℕ) : ℝ := 4 ^ n * atomC n ^ 3

theorem minorDiffC_nonneg (n : ℕ) : (0 : ℝ) ≤ minorDiffC n := by
  unfold minorDiffC
  have := atomC_nonneg n
  positivity

theorem one_le_minorDiffC (n : ℕ) : (1 : ℝ) ≤ minorDiffC n := by
  unfold minorDiffC
  have h1 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ atomC n ^ 3 := one_le_pow₀ (one_le_atomC n)
  nlinarith

theorem atomC_le_succ (n : ℕ) : atomC n ≤ atomC (n + 1) := by
  have h1 : (1 : ℝ) ≤ atomC n := one_le_atomC n
  have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
  have h5 : atomC n ≤ atomC n ^ 5 := by
    calc atomC n = atomC n ^ 1 := (pow_one _).symm
      _ ≤ atomC n ^ 5 := pow_le_pow_right₀ h1 (by norm_num)
  rw [atomC_succ]
  nlinarith [pow_nonneg (atomC_nonneg n) 5]

theorem atomC_mono {a b : ℕ} (h : a ≤ b) : atomC a ≤ atomC b := by
  induction b with
  | zero => simp only [Nat.le_zero.1 h]; exact le_rfl
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h1 | h1
      · exact le_trans (ih (Nat.lt_succ_iff.1 h1)) (atomC_le_succ b)
      · have : a = b + 1 := le_antisymm h h1
        subst this; exact le_rfl

theorem minorDiffC_mono {a b : ℕ} (h : a ≤ b) : minorDiffC a ≤ minorDiffC b := by
  unfold minorDiffC
  have h4 : (4 : ℝ) ^ a ≤ 4 ^ b := pow_le_pow_right₀ (by norm_num) h
  have hc : atomC a ^ 3 ≤ atomC b ^ 3 :=
    pow_le_pow_left₀ (atomC_nonneg a) (atomC_mono h) 3
  have hc0 : (0 : ℝ) ≤ atomC a ^ 3 := pow_nonneg (atomC_nonneg a) 3
  exact mul_le_mul h4 hc hc0 (by positivity)

/-- **The size of the `m`-fold minor difference, `m ≥ 1`.**

  `‖Δ_{κ_1} ⋯ Δ_{κ_m} (G^{(·)}_{kk} - m)‖ ≤ C_m Ψ^{m+1}`

on the good event, for distinct rows `κ_i ≠ k`.  The first difference is the (4.9) triple
product (order `2`), and each of the remaining `m - 1` differences gains one more power of `Ψ`
by `RBM.Gauss.diffBd_atom`.  At `m = 1` this is T85's replacement error `Ψ²`, at `m = 2` it is
T110's `Ψ³`, and the exponent `m + 1` is the multiplicativity of the gain at every order. -/
theorem norm_minorDiff_greenSetDiagCentered_le (hg : MinorGood d N u z ω Ψ) (hΨ0 : 0 ≤ Ψ)
    (hΨ1 : Ψ ≤ 1) (k κ : d.Idx N) (l : List (d.Idx N)) (hkκ : k ≠ κ)
    (hnd : (κ :: l).Nodup) (hkl : ∀ x ∈ l, x ≠ k) :
    ‖minorDiff d N (κ :: l) (greenSetDiagCentered d N u z m k) ω‖
      ≤ minorDiffC l.length * Ψ ^ (l.length + 2) := by
  classical
  rw [minorDiff_eq_iterDeltaFam, iterDeltaFam_cons, deltaFam_greenSetDiagCentered hg k κ hkκ]
  obtain ⟨ihoff, ihinv⟩ :=
    diffBd_atom hg hΨ0 hΨ1 l.length ({k, κ} : Finset (d.Idx N)) ∅
  have hkI : k ∈ ({k, κ} : Finset (d.Idx N)) := Finset.mem_insert_self _ _
  have hκI : κ ∈ ({k, κ} : Finset (d.Idx N)) := by simp
  have hA := ihoff k κ hkI hκI hkκ
  have hB := ihoff κ k hκI hkI (Ne.symm hkκ)
  have hC := ihinv κ hκI
  have hAB := DiffBd.mul hΨ0 l.length (atomC_nonneg _) (atomC_nonneg _) hA hB
  have hABC := DiffBd.mul hΨ0 l.length
    (by have := atomC_nonneg l.length; positivity) (atomC_nonneg _) hAB hC
  have hav : ∀ κ' ∈ l, κ' ∉ ({k, κ} : Finset (d.Idx N)) := by
    intro κ' hκ' hmem
    rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact hkl κ' hκ' h1
    · exact (List.nodup_cons.1 hnd).1 (by rw [← Finset.mem_singleton.1 h1]; exact hκ')
  have hres := hABC l ∅ (List.nodup_cons.1 hnd).2 hav le_rfl
  refine le_trans hres (le_of_eq ?_)
  unfold minorDiffC
  have hexp : 1 + 1 + 0 + l.length = l.length + 2 := by omega
  rw [hexp]
  have h4 : (2 : ℝ) ^ l.length * 2 ^ l.length = 4 ^ l.length := by
    rw [← mul_pow]; norm_num
  have : (2 : ℝ) ^ l.length * (2 ^ l.length * (atomC l.length * atomC l.length)
      * atomC l.length) = (2 ^ l.length * 2 ^ l.length) * atomC l.length ^ 3 := by ring
  rw [this, h4]

/-- **`m = 3`, the constant check.**  The three-fold difference is `Ψ⁴`, one order better than
the `Ψ³` of `m = 2` (T110) and two better than the `Ψ²` of a single replacement (T85).  The
constant `2^91` is the crude one produced by the recursion of `RBM.Gauss.atomC`; the paper's is
`C^m`, and no attempt is made here to recover it. -/
theorem norm_minorDiff_triple_le (hg : MinorGood d N u z ω Ψ) (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1)
    (k κ₁ κ₂ κ₃ : d.Idx N) (hkκ : k ≠ κ₁) (hnd : [κ₁, κ₂, κ₃].Nodup)
    (hk2 : κ₂ ≠ k) (hk3 : κ₃ ≠ k) :
    ‖minorDiff d N [κ₁, κ₂, κ₃] (greenSetDiagCentered d N u z m k) ω‖ ≤ 2 ^ 91 * Ψ ^ 4 := by
  have h := norm_minorDiff_greenSetDiagCentered_le (m := m) hg hΨ0 hΨ1 k κ₁ [κ₂, κ₃] hkκ hnd
    (by intro x hx; rcases List.mem_cons.1 hx with h1 | h1
        · exact h1 ▸ hk2
        · rcases List.mem_cons.1 h1 with h2 | h2
          · exact h2 ▸ hk3
          · exact absurd h2 (by simp))
  have hC : minorDiffC 2 = 2 ^ 91 := by
    unfold minorDiffC
    rw [atomC_succ, atomC_succ, atomC_zero]
    norm_num
  simpa [hC] using h

/-! #### The undifferenced entry: the `m = 0` grade

The empty word is the one grade of the expansion that the `Δ_κ` calculus never touches, and it
is where the deterministic envelope `η_u⁻¹ + 1` used to enter.  (4.2), carried by
`RBM.Gauss.MinorGood'`, replaces it by `Ψ`. -/

/-- **(4.2) at every minor level**: `|G^{(S)}_{kk} - m| ≤ Ψ`, including the levels that remove
`k`, where the family is `0` by convention. -/
theorem norm_greenSetDiagCentered_le (hg : MinorGood' d N u z m ω Ψ) (hΨ0 : 0 ≤ Ψ)
    (k : d.Idx N) (S : Finset (d.Idx N)) :
    ‖greenSetDiagCentered d N u z m k S ω‖ ≤ Ψ := by
  show ‖if h : k ∉ S then greenSetMat d N u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0‖ ≤ Ψ
  by_cases hk : k ∉ S
  · rw [dite_eq_left hk, ← gEnt_apply hk hk]
    exact hg.diag_sub_le S k hk
  · rw [dite_eq_right hk, norm_zero]
    exact hΨ0

/-- **The `m = 0` grade of the gain is `Ψ`, not the deterministic envelope.**  `Z^{(S)}_k` is a
fluctuation of `G^{(S)}_{kk} - m`, so (4.2) bounds it up to the factor `2` that `1 - E_k` costs.
This is the one place where `RBM.Gauss.MinorGood'` is stronger than `RBM.Gauss.MinorGood`, and
it is what upgrades (4.12) from `Ψ η_u⁻¹` to `Ψ²`. -/
theorem norm_flucDiagSet_le (hg : ∀ ω' : Ω d, MinorGood' d N u z m ω' Ψ) (hΨ0 : 0 ≤ Ψ)
    (k : d.Idx N) (S : Finset (d.Idx N)) :
    ‖flucDiagSet d N u z m k S ω‖ ≤ 2 * Ψ := by
  have hrw : flucDiagSet d N u z m k S ω
      = greenSetDiagCentered d N u z m k S ω
        - condRow d N k (greenSetDiagCentered d N u z m k S) ω := qRow_apply _ _ _
  rw [hrw]
  exact norm_sub_condRow_le (fun ω' => norm_greenSetDiagCentered_le (hg ω') hΨ0 k S) ω

end TopLevel


/-! ### The fluctuation passes through the difference -/

section Assembly

variable {E t : ℝ}

/-- **`Δ_{κ_1} ⋯ Δ_{κ_m}` commutes with `Q_k = 1 - E_k`.**  The difference is a linear
combination with constant coefficients, and `E_k` is linear, so the whole `m`-fold difference of
the *fluctuations* is the fluctuation of the `m`-fold difference.  This is what reduces
`RBM.Gauss.MinorDiffGain` to the deterministic family `RBM.Gauss.greenSetDiagCentered`. -/
theorem minorDiff_qRow (k : d.Idx N) : ∀ (l : List (d.Idx N)) (Y : Finset (d.Idx N) → Ω d → ℂ),
    (∀ S, BddMeas d (Y S)) →
    minorDiff d N l (fun S => qRow d N k (Y S)) = qRow d N k (minorDiff d N l Y) := by
  intro l
  induction l with
  | nil => intro Y _; rfl
  | cons κ l ih =>
      intro Y hY
      simp only [minorDiff_cons]
      have hstep : (fun (S : Finset (d.Idx N)) (ω : Ω d) =>
            qRow d N k (Y S) ω - qRow d N k (Y (insert κ S)) ω)
          = fun S => qRow d N k (fun ω => Y S ω - Y (insert κ S) ω) := by
        funext S
        rw [qRow_sub k (hY S) (hY (insert κ S))]
      rw [hstep]
      exact ih _ fun S => (hY S).sub (hY _)

theorem minorDiff_flucDiagSet_eq (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N)
    (l : List (d.Idx N)) :
    minorDiff d N l (flucDiagSet d N u (zt E t) (mE E) k)
      = qRow d N k (minorDiff d N l (greenSetDiagCentered d N u (zt E t) (mE E) k)) :=
  minorDiff_qRow k l _ fun S => bddMeas_greenSetDiagCentered hE ht u k S

/-- The `m`-fold difference of the fluctuation is `Ψ^{m+1}` on the good event, at the price of
one further factor `2` for the conditional expectation. -/
theorem norm_minorDiff_flucDiagSet_le (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hg : ∀ ω, MinorGood d N u (zt E t) ω Ψ)
    (k κ : d.Idx N) (l : List (d.Idx N)) (hkκ : k ≠ κ) (hnd : (κ :: l).Nodup)
    (hkl : ∀ x ∈ l, x ≠ k) (ω : Ω d) :
    ‖minorDiff d N (κ :: l) (flucDiagSet d N u (zt E t) (mE E) k) ω‖
      ≤ 2 * (minorDiffC l.length * Ψ ^ (l.length + 2)) := by
  rw [minorDiff_flucDiagSet_eq hE ht u k (κ :: l), qRow_apply]
  exact norm_sub_condRow_le
    (fun ω' => norm_minorDiff_greenSetDiagCentered_le (hg ω') hΨ0 hΨ1 k κ l hkκ hnd hkl) ω

theorem qList_nodup {L : List (Bool × d.Idx N)} (h : (L.map Prod.snd).Nodup) :
    (qList L).Nodup :=
  List.Nodup.sublist (List.Sublist.map Prod.snd List.filter_sublist) h

theorem mem_qList_ne {L : List (Bool × d.Idx N)} {k : d.Idx N} (h : ∀ x ∈ L, x.2 ≠ k)
    {y : d.Idx N} (hy : y ∈ qList L) : y ≠ k := by
  have hsub := (List.Sublist.map Prod.snd (List.filter_sublist (p := fun x : Bool × d.Idx N => x.1)
    (l := L))).subset hy
  obtain ⟨p, hp, hpy⟩ := List.mem_map.1 hsub
  exact hpy ▸ h p hp

theorem bddMeas_minorDiff (l : List (d.Idx N)) (Y : Finset (d.Idx N) → Ω d → ℂ)
    (hY : ∀ S, BddMeas d (Y S)) : BddMeas d (minorDiff d N l Y) := by
  induction l generalizing Y with
  | nil => simpa using hY ∅
  | cons κ l ih =>
      rw [minorDiff_cons]
      exact ih _ fun S => (hY S).sub (hY _)

theorem bddMeas_applyOps_minorDiff_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : d.Idx N) (L : List (Bool × d.Idx N)) :
    BddMeas d (applyOps d N L
      (minorDiff d N (qList L) (flucDiagSet d N u (zt E t) (mE E) k))) :=
  BddMeas.applyOps (bddMeas_minorDiff _ _ fun S => bddMeas_flucDiagSet hE ht u k S) L

/-- **The gain `ρ ≍ Ψ`, for words of bounded length.**

This is `RBM.Gauss.MinorDiffGain` restricted to words of length at most `M`, which is all the
`2p`-th moment expansion of (4.12) ever uses (`numQ (L i) ≤ (L i).length ≤ 2p`).  On the good
event the gain is multiplicative at every order: `B ≍ 1` and `ρ = 2Ψ`.

Two inputs are carried: the local law holds at *every* sample point (`hgood`), and the word is
short (`hM`).  Neither can be dropped in the form `RBM.Gauss.MinorDiffGain` demands -- see the
module docstring. -/
theorem integral_prod_applyOps_minorDiff_le (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hgood : ∀ ω, MinorGood d N u (zt E t) ω Ψ) (M : ℕ)
    (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N))
    (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i)
    (hM : ∀ i, (L i).length ≤ M) :
    ∫ ω, ∏ i, ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖ ∂(P d)
      ≤ (2 * ((etaT E t)⁻¹ + 1) + 2 * minorDiffC M * Ψ) ^ Fintype.card ι
        * (2 * Ψ) ^ ∑ i, numQ (L i) := by
  classical
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  set Benv : ℝ := 2 * ((etaT E t)⁻¹ + 1) with hBenv
  set B : ℝ := Benv + 2 * minorDiffC M * Ψ with hB
  have hBenv0 : 0 ≤ Benv := by rw [hBenv]; positivity
  have hextra0 : 0 ≤ 2 * minorDiffC M * Ψ := by
    have := minorDiffC_nonneg M
    positivity
  have hb : ∀ (i : ι) (ω : Ω d),
      ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖
        ≤ B * (2 * Ψ) ^ numQ (L i) := by
    intro i ω
    have hlenq : (qList (L i)).length = numQ (L i) := length_qList (L i)
    have hnodup : (qList (L i)).Nodup := qList_nodup (h1 i)
    have hne : ∀ y ∈ qList (L i), y ≠ k i := fun y hy => mem_qList_ne (h2 i) hy
    cases hqs : qList (L i) with
    | nil =>
        have hzero : numQ (L i) = 0 := by rw [← hlenq, hqs]; rfl
        have hpt : ∀ ω' : Ω d,
            ‖minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)) ω'‖
              ≤ Benv := by
          intro ω'
          rw [hqs]
          simpa using norm_flucDiagSet_le_env hE ht u (k i) ∅ ω'
        have happ := norm_applyOps_le (L i) hpt ω
        rw [hqs] at happ
        rw [hzero] at happ ⊢
        rw [pow_zero, one_mul] at happ
        rw [pow_zero, mul_one]
        linarith
    | cons κ l' =>
        have hκmem : κ ∈ qList (L i) := by rw [hqs]; exact List.mem_cons_self
        have hkκ : k i ≠ κ := Ne.symm (hne κ hκmem)
        have hnd' : (κ :: l').Nodup := by rw [← hqs]; exact hnodup
        have hkl : ∀ x ∈ l', x ≠ k i := by
          intro x hx
          exact hne x (by rw [hqs]; exact List.mem_cons_of_mem _ hx)
        have hm : numQ (L i) = l'.length + 1 := by
          rw [← hlenq, hqs]; simp [List.length_cons]
        have hlM : l'.length ≤ M := by
          have h3 : numQ (L i) ≤ (L i).length := List.countP_le_length
          have := hM i
          omega
        have hpt : ∀ ω' : Ω d,
            ‖minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)) ω'‖
              ≤ 2 * (minorDiffC M * Ψ ^ (l'.length + 2)) := by
          intro ω'
          rw [hqs]
          refine le_trans (norm_minorDiff_flucDiagSet_le hE ht u hΨ0 hΨ1 hgood (k i) κ l'
            hkκ hnd' hkl ω') ?_
          have hmono := minorDiffC_mono hlM
          have hpow : (0 : ℝ) ≤ Ψ ^ (l'.length + 2) := pow_nonneg hΨ0 _
          nlinarith
        have happ := norm_applyOps_le (L i) hpt ω
        rw [hqs] at happ
        refine le_trans happ ?_
        rw [hm, mul_pow]
        have hΨpow : Ψ ^ (l'.length + 2) = Ψ ^ (l'.length + 1) * Ψ := by rw [← pow_succ]
        rw [hΨpow]
        have hkey : 2 * minorDiffC M * Ψ ≤ B := by rw [hB]; linarith
        calc 2 ^ (l'.length + 1) * (2 * (minorDiffC M * (Ψ ^ (l'.length + 1) * Ψ)))
            = (2 * minorDiffC M * Ψ) * (2 ^ (l'.length + 1) * Ψ ^ (l'.length + 1)) := by ring
          _ ≤ B * (2 ^ (l'.length + 1) * Ψ ^ (l'.length + 1)) :=
              mul_le_mul_of_nonneg_right hkey
                (mul_nonneg (by positivity) (pow_nonneg hΨ0 _))
  have hbm : ∀ i : ι, BddMeas d (applyOps d N (L i)
      (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)))) :=
    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
  refine le_trans (integral_prod_norm_le_of_bounds hbm hb) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]

/-- **(4.2) subsumes (4.1)**, so the extra field of `RBM.Gauss.MinorGood'` does not have to be
produced alongside a separate lower bound on the diagonal: `|m_E| = 1`
(`RBM.norm_mE`), so `|G^{(S)}_{aa} - m| ≤ Ψ ≤ 1/2` already gives `1/2 ≤ |G^{(S)}_{aa}|`, which
is the shape `RBM.Gauss.minorGood_of_half_le` consumes.  Only (4.2) and (4.3) are assumed
here. -/
theorem minorGood'_of_local_law (hE : |E| < 2) {u : ℝ} {ω : Ω d} {Ψ : ℝ} (hΨ : Ψ ≤ 1 / 2)
    (hdet : ∀ S : Finset (d.Idx N), IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
      - (zt E t) • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det)
    (hoff : ∀ (S : Finset (d.Idx N)) (a b : d.Idx N), a ≠ b →
      ‖gEnt d N u (zt E t) ω a b S‖ ≤ Ψ)
    (hdiag : ∀ (S : Finset (d.Idx N)) (a : d.Idx N), a ∉ S →
      ‖gEnt d N u (zt E t) ω a a S - mE E‖ ≤ Ψ) :
    MinorGood' d N u (zt E t) (mE E) ω Ψ := by
  refine minorGood'_of_half_le hdet (fun S a ha => ?_) hoff hdiag
  have h1 := hdiag S a ha
  have h2 : ‖mE E‖ - ‖gEnt d N u (zt E t) ω a a S‖
      ≤ ‖mE E - gEnt d N u (zt E t) ω a a S‖ := norm_sub_norm_le _ _
  rw [norm_sub_rev] at h2
  rw [norm_mE hE.le] at h2
  linarith

/-- **The gain `ρ ≍ Ψ` with `B ≍ Ψ`, for words of bounded length** — the paper's size of
(4.12).

Identical to `RBM.Gauss.integral_prod_applyOps_minorDiff_le` except in the *empty-word* branch,
where `RBM.Gauss.norm_flucDiagSet_le` (i.e. (4.2), carried by `RBM.Gauss.MinorGood'`) replaces
the deterministic envelope `RBM.Gauss.norm_flucDiagSet_le_env`.  The constant therefore drops
from `2(η_u⁻¹ + 1) + 2 C_M Ψ` to `2Ψ + 2 C_M Ψ`, and the `2p`-th moment iteration converts
`B ρ` into (4.12)'s control: `2Ψ · (2Ψ + 2 C_M Ψ) ≍ Ψ²` instead of `2Ψ · η_u⁻¹`.

No other branch changes: for a non-empty word the estimate already came from the `Δ_κ`
calculus, which never sees the undifferenced entry. -/
theorem integral_prod_applyOps_minorDiff_le' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hgood : ∀ ω, MinorGood' d N u (zt E t) (mE E) ω Ψ) (M : ℕ)
    (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N))
    (h1 : ∀ i, ((L i).map Prod.snd).Nodup) (h2 : ∀ i, ∀ x ∈ L i, x.2 ≠ k i)
    (hM : ∀ i, (L i).length ≤ M) :
    ∫ ω, ∏ i, ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖ ∂(P d)
      ≤ (2 * Ψ + 2 * minorDiffC M * Ψ) ^ Fintype.card ι
        * (2 * Ψ) ^ ∑ i, numQ (L i) := by
  classical
  set B : ℝ := 2 * Ψ + 2 * minorDiffC M * Ψ with hB
  have hextra0 : 0 ≤ 2 * minorDiffC M * Ψ := by
    have := minorDiffC_nonneg M
    positivity
  have hb : ∀ (i : ι) (ω : Ω d),
      ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖
        ≤ B * (2 * Ψ) ^ numQ (L i) := by
    intro i ω
    have hlenq : (qList (L i)).length = numQ (L i) := length_qList (L i)
    have hnodup : (qList (L i)).Nodup := qList_nodup (h1 i)
    have hne : ∀ y ∈ qList (L i), y ≠ k i := fun y hy => mem_qList_ne (h2 i) hy
    cases hqs : qList (L i) with
    | nil =>
        have hzero : numQ (L i) = 0 := by rw [← hlenq, hqs]; rfl
        have hpt : ∀ ω' : Ω d,
            ‖minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)) ω'‖
              ≤ 2 * Ψ := by
          intro ω'
          rw [hqs]
          simpa using norm_flucDiagSet_le (ω := ω') hgood hΨ0 (k i) ∅
        have happ := norm_applyOps_le (L i) hpt ω
        rw [hqs] at happ
        rw [hzero] at happ ⊢
        rw [pow_zero, one_mul] at happ
        rw [pow_zero, mul_one]
        linarith
    | cons κ l' =>
        have hκmem : κ ∈ qList (L i) := by rw [hqs]; exact List.mem_cons_self
        have hkκ : k i ≠ κ := Ne.symm (hne κ hκmem)
        have hnd' : (κ :: l').Nodup := by rw [← hqs]; exact hnodup
        have hkl : ∀ x ∈ l', x ≠ k i := by
          intro x hx
          exact hne x (by rw [hqs]; exact List.mem_cons_of_mem _ hx)
        have hm : numQ (L i) = l'.length + 1 := by
          rw [← hlenq, hqs]; simp [List.length_cons]
        have hlM : l'.length ≤ M := by
          have h3 : numQ (L i) ≤ (L i).length := List.countP_le_length
          have := hM i
          omega
        have hpt : ∀ ω' : Ω d,
            ‖minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)) ω'‖
              ≤ 2 * (minorDiffC M * Ψ ^ (l'.length + 2)) := by
          intro ω'
          rw [hqs]
          refine le_trans (norm_minorDiff_flucDiagSet_le hE ht u hΨ0 hΨ1
            (fun ω'' => (hgood ω'').toMinorGood) (k i) κ l' hkκ hnd' hkl ω') ?_
          have hmono := minorDiffC_mono hlM
          have hpow : (0 : ℝ) ≤ Ψ ^ (l'.length + 2) := pow_nonneg hΨ0 _
          nlinarith
        have happ := norm_applyOps_le (L i) hpt ω
        rw [hqs] at happ
        refine le_trans happ ?_
        rw [hm, mul_pow]
        have hΨpow : Ψ ^ (l'.length + 2) = Ψ ^ (l'.length + 1) * Ψ := by rw [← pow_succ]
        rw [hΨpow]
        have hkey : 2 * minorDiffC M * Ψ ≤ B := by rw [hB]; nlinarith
        calc 2 ^ (l'.length + 1) * (2 * (minorDiffC M * (Ψ ^ (l'.length + 1) * Ψ)))
            = (2 * minorDiffC M * Ψ) * (2 ^ (l'.length + 1) * Ψ ^ (l'.length + 1)) := by ring
          _ ≤ B * (2 ^ (l'.length + 1) * Ψ ^ (l'.length + 1)) :=
              mul_le_mul_of_nonneg_right hkey
                (mul_nonneg (by positivity) (pow_nonneg hΨ0 _))
  have hbm : ∀ i : ι, BddMeas d (applyOps d N (L i)
      (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)))) :=
    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
  refine le_trans (integral_prod_norm_le_of_bounds hbm hb) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]

/-! ### The graded interface, and the bridge to (4.12) -/

/-- **T113 packaged as `RBM.Gauss.MinorDiffGainUpTo`**: the bounded-length estimate *is* the
graded reduced interface, with `B` the deterministic envelope. -/
theorem minorDiffGainUpTo_of_minorGood (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hgood : ∀ ω, MinorGood d N u (zt E t) ω Ψ) (M : ℕ) :
    MinorDiffGainUpTo d N u (zt E t) (mE E)
      (2 * ((etaT E t)⁻¹ + 1) + 2 * minorDiffC M * Ψ) (2 * Ψ) M := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  have hC := minorDiffC_nonneg M
  exact ⟨by positivity, by positivity,
    fun ι _ k L h1 h2 h3 => integral_prod_applyOps_minorDiff_le hE ht u hΨ0 hΨ1 hgood M
      ι k L h1 h2 h3⟩

/-- **The same, with (4.2): `B ≍ Ψ`.** -/
theorem minorDiffGainUpTo_of_minorGood' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hgood : ∀ ω, MinorGood' d N u (zt E t) (mE E) ω Ψ) (M : ℕ) :
    MinorDiffGainUpTo d N u (zt E t) (mE E)
      (2 * Ψ + 2 * minorDiffC M * Ψ) (2 * Ψ) M := by
  have hC := minorDiffC_nonneg M
  exact ⟨by positivity, by positivity,
    fun ι _ k L h1 h2 h3 => integral_prod_applyOps_minorDiff_le' hE ht u hΨ0 hΨ1 hgood M
      ι k L h1 h2 h3⟩

/-- **T113 feeds the graded consumers of (4.12) directly** (T137's bridge).  The gain interface
of `RBM1D/Gauss/FlucIter.lean` at word length `≤ M` is a *theorem* on the good event; the
constant is the deterministic envelope, because `RBM.Gauss.MinorGood` does not carry (4.2). -/
theorem flucGainUpTo_of_minorDiff (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hgood : ∀ ω, MinorGood d N u (zt E t) ω Ψ) (M : ℕ) :
    FlucGainUpTo d N u (zt E t) (mE E)
      (2 * ((etaT E t)⁻¹ + 1) + 2 * minorDiffC M * Ψ) (2 * Ψ) M :=
  flucGainUpTo_of_minorDiffGainUpTo hE ht u
    (minorDiffGainUpTo_of_minorGood hE ht u hΨ0 hΨ1 hgood M)

/-- **The same bridge at the paper's size.**  With (4.2) the constant is `≍ Ψ`, so the
`2p`-th moment iteration of `RBM1D/Gauss/FlucIter.lean` delivers (4.12) with control
`ρ B ≍ Ψ²` — see `RBM.Gauss.stochDom_flucAvg_blockAvg_iter_graded`. -/
theorem flucGainUpTo_of_minorDiff' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {Ψ : ℝ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hgood : ∀ ω, MinorGood' d N u (zt E t) (mE E) ω Ψ) (M : ℕ) :
    FlucGainUpTo d N u (zt E t) (mE E) (2 * Ψ + 2 * minorDiffC M * Ψ) (2 * Ψ) M :=
  flucGainUpTo_of_minorDiffGainUpTo hE ht u
    (minorDiffGainUpTo_of_minorGood' hE ht u hΨ0 hΨ1 hgood M)

/-- **Pointwise bounds on the words give `RBM.Gauss.MinorDiffGain`.**  This is the only step of
the interface that is still probabilistic, and it is Jensen plus Fubini: the integrand is a
product of bounded measurable functions and `P d` is a probability measure.  Everything else has
been reduced to Green's function minors.

`RBM.Gauss.integral_prod_applyOps_minorDiff_le` supplies the hypothesis for words of bounded
length; the missing input is uniformity in the length, and the exceptional set. -/
theorem minorDiffGain_of_pointwise (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (h : ∀ (k : d.Idx N) (L : List (Bool × d.Idx N)), (L.map Prod.snd).Nodup →
        (∀ x ∈ L, x.2 ≠ k) → ∀ ω : Ω d,
        ‖applyOps d N L (minorDiff d N (qList L) (flucDiagSet d N u (zt E t) (mE E) k)) ω‖
          ≤ B * ρ ^ numQ L) :
    MinorDiffGain d N u (zt E t) (mE E) B ρ := by
  classical
  refine ⟨hB, hρ, fun ι _ k L h1 h2 => ?_⟩
  have hbm : ∀ i : ι, BddMeas d (applyOps d N (L i)
      (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)))) :=
    fun i => bddMeas_applyOps_minorDiff_flucDiagSet hE ht u (k i) (L i)
  refine le_trans (integral_prod_norm_le_of_bounds hbm
    (b := fun i => B * ρ ^ numQ (L i)) fun i ω => h (k i) (L i) (h1 i) (h2 i) ω)
    (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]

end Assembly

end RBM.Gauss
