/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucIter

/-!
# The higher-order minor expansion: `RBM.Gauss.FlucGain` for `m ≥ 2`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the last interface of the fluctuation averaging (4.12).

T94 (`RBM1D/Gauss/FlucIter.lean`) reduces (4.12) to one hypothesis, `RBM.Gauss.FlucGain`: that
applying `m` conditional fluctuations `Q_{κ_1} ⋯ Q_{κ_m}` (distinct rows, all different from
`k`) to `Z_k = (1 - E_k)(G_{kk} - m)` gains a factor `ρ^m` with `ρ ≍ Ψ`.  There it is a theorem
for `m = 0` and `m = 1` only.

## The question this file answers

Is the gain **multiplicative** (`‖Q_{κ₂} Q_{κ₁} Z_k‖ ≲ Ψ³`) or merely **additive** (each
replacement earning its own `Ψ²`, `≲ 2Ψ²`)?  It is multiplicative, and the mechanism is an
exact identity rather than an estimate:

  `RBM.Gauss.applyOps_eq_applyOps_minorDiff` :
      `applyOps L (Z_k) = applyOps L (Δ_{κ_1} ⋯ Δ_{κ_m} Z^{(·)}_k)`

where `κ_1, …, κ_m` are the rows carrying a `Q` in the word `L` and `Δ_κ X^{(S)} :=
X^{(S)} - X^{(S ∪ {κ})}` is the minor difference.  The proof peels the outermost `Q_κ`,
replaces the whole family of minors `Y` by `Z S := Y S - Y (S ∪ {κ})`, and observes that the
subtracted piece `Y {κ}` is annihilated outright, being strictly independent of row `κ`.  So
the `m` fluctuations do **not** act independently: they compose into the `m`-fold difference,
whose size is `Ψ^{m+1}` because each difference is one order smaller than what it differences.

At `m = 2` this is made concrete and unconditional:

* `RBM.Gauss.greenSetMat_insert_apply` — (4.9) between `G^{(S)}` and `G^{(S ∪ {κ})}`, the
  iteration of `RBM1D/Green/Minor.lean` (T40) to `Finset`-indexed minors;
* `RBM.Gauss.minorDiff_pair_greenSetDiagCentered` — the second difference of `G_{kk}` is the
  difference of the two triple products `G_{kκ₁} G_{κ₁k} / G_{κ₁κ₁}` at levels `∅` and `{κ₂}`;
* `RBM.Gauss.norm_mul_three_sub_le`, `RBM.Gauss.norm_minorDiff_pair_greenSetDiagCentered_le` —
  with off-diagonal entries `≤ Ψ`, inverse diagonal entries `≤ 2` and each *first* difference
  `≤ Ψ²`, the second difference is `≤ 10 Ψ³`, i.e. `Ψ³` and not `2 Ψ²`.

## What is proved

1. **`Finset`-indexed minors.**  `RBM.Gauss.greenSetMat d N u z S` is the resolvent on
   `{a ∉ S}`; `RBM.Gauss.FinDepOffRows` generalizes T84's `RBM.Gauss.FinDepOffRow` to a whole
   `Finset` of rows, `RBM.Gauss.finDepOffRows_of_minorSet` is the master independence lemma,
   and `RBM.Gauss.qRow_of_finDepOffRows` is the annihilation.  `S = ∅` is the full resolvent
   (`RBM.Gauss.greenSetMat_empty_apply`) and `S = {κ}` is T84's `RBM.Gauss.greenMinorMat`
   (`RBM.Gauss.greenSetMat_singleton_apply`), so `m = 1` is literally T86's
   `RBM.Gauss.flucDiagMinor` (`RBM.Gauss.flucDiagSet_singleton`) and inherits T85's `ε ≍ Ψ²`.
2. **The annihilation identity** `RBM.Gauss.applyOps_eq_applyOps_minorDiff`, and its estimate
   form `RBM.Gauss.norm_applyOps_le_minorDiff` / `RBM.Gauss.norm_applyOps_flucDiag_le_of_minorDiff`.
   Unconditional; `P` letters pass through, each `Q` letter costs a factor `2` and buys one
   difference.
3. **One step of (4.9) for iterated minors** (`RBM.Gauss.greenSetMat_insert_apply`,
   `RBM.Gauss.greenSetDiagCentered_sub_insert`).
4. **`RBM.Gauss.FlucGain` for every `m`** from `RBM.Gauss.MinorDiffGain`
   (`RBM.Gauss.flucGain_of_minorDiffGain`), with `RBM.Gauss.minorDiffGain_env` an
   unconditional (gain-free, `ρ = 4`) instance showing the reduced interface is not vacuous.
5. **The same, graded by word length** (T137's grading of `RBM.Gauss.FlucGain`, applied to the
   reduced interface): `RBM.Gauss.MinorDiffGainUpTo`, `RBM.Gauss.MinorDiffGain.upTo` and
   `RBM.Gauss.flucGainUpTo_of_minorDiffGainUpTo`.  The annihilation identity does not touch the
   words, so the length restriction passes through it unchanged.  This is the form in which
   §4's estimate of the minor differences (`RBM1D/Gauss/MinorDiffGain.lean`) is available, and
   the form the `2p`-th moment expansion consumes.

## What is *not* done, and why the interface is not empty

`RBM.Gauss.MinorDiffGain` — the **size** of the iterated minor differences, in expectation —
is not discharged.  It is strictly weaker than `RBM.Gauss.FlucGain`: every conditional
expectation has been removed from its content, and what remains is a statement about Green's
function minors and the local law only.  The general-`m` size estimate needs a Leibniz calculus
for `Δ_κ` over the factorization of (4.9) (`Δ_κ(XY) = (Δ_κ X) Y + X^{(κ)} (Δ_κ Y)`,
`Δ_κ (1/X) = (Δ_κ X)/(X X^{(κ)})`), which is a separate piece of work; `m = 2` is done here in
full.

It is stated, like `RBM.Gauss.FlucGain`, as a bound on an *expectation*.  This is deliberate
and the ticket's constraint: a pointwise `Ψ`-sized bound is **false** (the local law has an
exceptional set), and no indicator is introduced anywhere — the annihilation identity is used
before any truncation, so the obstruction recorded in `docs/STATUS.md` (that `1_Ω` destroys
`E_κ[(1 - E_κ)X] = 0` and is not `FinDepOffRow`) never arises.

## Deviations from the paper

* The `m`-fold difference is presented as a recursion on a *list* of rows acting on a family
  indexed by `Finset`s (`RBM.Gauss.minorDiff`), rather than as the inclusion–exclusion sum
  `∑_{T ⊆ {κ_1,…,κ_m}} (-1)^{#T} G^{(T)}`.  The two agree; the recursion is what matches the
  peeling of the word.
* Constants are not the paper's: each `Q` costs `2` and each difference costs `2`, so the
  gain-free envelope instance has `ρ = 4`, and the `m = 2` estimate carries `10` rather than
  an optimized constant.
* `RBM.Gauss.MinorDiffGain` is a hypothesis, not a theorem, for `m ≥ 3`.  See
  `docs/paper-deltas.md`.
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Matrix Finset

variable {d : Dims} {N : ℕ}

/-! ### Sample points that agree off a `Finset` of rows -/

/-- Two sample points **agree off the rows in `S`**: every coordinate at size `N` whose index
pair avoids `S` carries the same value.  The `S = {i}` case is `RBM.Gauss.AgreeOffRow`. -/
def AgreeOffRows (d : Dims) (N : ℕ) (S : Finset (d.Idx N)) (ω ω' : Ω d) : Prop :=
  ∀ (k l : d.Idx N) (b : Bool), k ∉ S → l ∉ S → ω ⟨N, k, l, b⟩ = ω' ⟨N, k, l, b⟩

/-- The entries of `X` away from the rows and columns in `S` read only coordinates that
avoid `S`. -/
theorem Xentry_congr_of_not_mem {S : Finset (d.Idx N)} {ω ω' : Ω d}
    (h : AgreeOffRows d N S ω ω') {k l : d.Idx N} (hk : k ∉ S) (hl : l ∉ S) :
    Xentry d N ω k l = Xentry d N ω' k l := by
  unfold Xentry
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` on `{a ∉ S}` reads only coordinates that avoid `S`. -/
theorem Hflow_submatrix_set_congr (u : ℝ) {S : Finset (d.Idx N)} {ω ω' : Ω d}
    (h : AgreeOffRows d N S ω ω') :
    (Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
      = (Hflow d N u ω').submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N) := by
  ext k l
  simp only [Matrix.submatrix_apply, Hflow_apply]
  rw [Xentry_congr_of_not_mem h k.2 l.2]

/-! ### `FinDepOffRows`: strict independence of a whole `Finset` of rows -/

/-- **`g` is strictly independent of every row in `S`**: it reads finitely many Gaussian
coordinates, none of which is a row-`κ` coordinate for any `κ ∈ S`.  This is T84's
`RBM.Gauss.FinDepOffRow` with the witness set constrained to avoid all of `S` at once. -/
def FinDepOffRows (d : Dims) (N : ℕ) (S : Finset (d.Idx N)) {V : Type*} (g : Ω d → V) : Prop :=
  ∃ I : Finset (Coord d), (∀ c ∈ I, ∀ κ ∈ S, ¬ IsRowCoord d N κ c) ∧
    ∀ ω ω' : Ω d, (∀ c ∈ I, ω c = ω' c) → g ω = g ω'

/-- **The annihilation half, in one line**: `FinDepOffRows S` gives `FinDepOffRow κ` for every
`κ ∈ S`, hence `E_κ` fixes `g` and `Q_κ g = 0`. -/
theorem FinDepOffRows.finDepOffRow {S : Finset (d.Idx N)} {V : Type*} {g : Ω d → V}
    (h : FinDepOffRows d N S g) {κ : d.Idx N} (hκ : κ ∈ S) : FinDepOffRow d N κ g :=
  let ⟨I, hI, hg⟩ := h; ⟨I, fun c hc => hI c hc κ hκ, hg⟩

/-- **Any `Q_κ` with `κ ∈ S` annihilates a `FinDepOffRows S` function.** -/
theorem qRow_of_finDepOffRows {S : Finset (d.Idx N)} {X : Ω d → ℂ}
    (h : FinDepOffRows d N S X) {κ : d.Idx N} (hκ : κ ∈ S) : qRow d N κ X = 0 := by
  funext ω
  show X ω - condRow d N κ X ω = 0
  rw [congrFun (condRow_of_finDepOffRow (h.finDepOffRow hκ)) ω, sub_self]

theorem FinDepOffRows.comp {S : Finset (d.Idx N)} {V W : Type*} {g : Ω d → V}
    (h : FinDepOffRows d N S g) (F : V → W) : FinDepOffRows d N S fun ω => F (g ω) :=
  let ⟨I, hI, hg⟩ := h
  ⟨I, hI, fun ω ω' hω => show F (g ω) = F (g ω') by rw [hg ω ω' hω]⟩

theorem FinDepOffRows.sub {S : Finset (d.Idx N)} {X Y : Ω d → ℂ}
    (hX : FinDepOffRows d N S X) (hY : FinDepOffRows d N S Y) :
    FinDepOffRows d N S fun ω => X ω - Y ω := by
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

/-- **`E_{k}` preserves independence of every row in `S`** — the `Finset` version of T86's
`RBM.Gauss.finDepOffRow_condRow`.  It is what keeps the `(1 - E_k)` in `Z^{(S)}_k` harmless. -/
theorem finDepOffRows_condRow {S : Finset (d.Idx N)} {k : d.Idx N} {X : Ω d → ℂ}
    (h : FinDepOffRows d N S X) : FinDepOffRows d N S (condRow d N k X) := by
  classical
  obtain ⟨I, hI, hX⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord d N k c, fun c hc => hI c (Finset.mem_filter.1 hc).1,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hX _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord d N k c
  · rw [rowSplit_apply_of_isRowCoord k ω ω'' hcr, rowSplit_apply_of_isRowCoord k ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

theorem finDepOffRows_qRow {S : Finset (d.Idx N)} {k : d.Idx N} {X : Ω d → ℂ}
    (h : FinDepOffRows d N S X) : FinDepOffRows d N S (qRow d N k X) :=
  h.sub (finDepOffRows_condRow h)

/-- The witness set: every coordinate at size `N` whose index pair avoids `S`. -/
def offRowsCoords (d : Dims) (N : ℕ) (S : Finset (d.Idx N)) : Finset (Coord d) :=
  (Finset.univ.image fun p : d.Idx N × d.Idx N × Bool => (⟨N, p⟩ : Coord d)).filter
    fun c => ∀ κ ∈ S, ¬ IsRowCoord d N κ c

theorem forall_not_isRowCoord_of_mem_offRowsCoords {S : Finset (d.Idx N)} {c : Coord d}
    (hc : c ∈ offRowsCoords d N S) : ∀ κ ∈ S, ¬ IsRowCoord d N κ c :=
  (Finset.mem_filter.1 hc).2

theorem mem_offRowsCoords {S : Finset (d.Idx N)} {i j : d.Idx N} {b : Bool}
    (hi : i ∉ S) (hj : j ∉ S) : (⟨N, i, j, b⟩ : Coord d) ∈ offRowsCoords d N S := by
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(i, j, b), Finset.mem_univ _, rfl⟩, ?_⟩
  intro κ hκ
  simp only [isRowCoord_mk]
  rintro (h | h)
  · exact hi (h ▸ hκ)
  · exact hj (h ▸ hκ)

/-- **The master row-independence lemma for a `Finset` of rows.**  Anything read off the minor
matrix `H_u^{(S)}` is strictly independent of every row in `S`. -/
theorem finDepOffRows_of_minorSet (d : Dims) (N : ℕ) (u : ℝ) (S : Finset (d.Idx N)) {V : Type*}
    (F : Matrix {a : d.Idx N // a ∉ S} {a : d.Idx N // a ∉ S} ℂ → V) :
    FinDepOffRows d N S fun ω =>
      F ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)) := by
  refine ⟨offRowsCoords d N S, fun c hc => forall_not_isRowCoord_of_mem_offRowsCoords hc,
    fun ω ω' hω => ?_⟩
  have hagree : AgreeOffRows d N S ω ω' := fun i j b hi hj => hω _ (mem_offRowsCoords hi hj)
  show F _ = F _
  rw [Hflow_submatrix_set_congr u hagree]

/-! ### The iterated minor resolvent `G^{(S)}` -/

/-- **`G^{(S)} = (H_u^{(S)} - z)⁻¹`**, the resolvent on `{a ∉ S}`, as a *total* function of `ω`
(`Matrix.inv` is total, so no invertibility hypothesis is carried).  For `S = {κ}` this is
T84's `RBM.Gauss.greenMinorMat`, and for `S = ∅` it is the full resolvent. -/
noncomputable def greenSetMat (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (S : Finset (d.Idx N))
    (ω : Ω d) : Matrix {a : d.Idx N // a ∉ S} {a : d.Idx N // a ∉ S} ℂ :=
  ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
    (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
      - z • (1 : Matrix {a : d.Idx N // a ∉ S} {a : d.Idx N // a ∉ S} ℂ))⁻¹

theorem greenSetMat_eq_green_submatrix (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    greenSetMat d N u z S ω
      = green ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
          (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)) z := rfl

theorem finDepOffRows_greenSetMat (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (S : Finset (d.Idx N)) :
    FinDepOffRows d N S (greenSetMat d N u z S) :=
  finDepOffRows_of_minorSet d N u S fun M => (M - z • 1)⁻¹

theorem finDepOffRows_greenSetMat_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (a b : {a : d.Idx N // a ∉ S}) :
    FinDepOffRows d N S fun ω => greenSetMat d N u z S ω a b :=
  (finDepOffRows_greenSetMat d N u z S).comp fun M => M a b

theorem measurable_greenSetMat_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (a b : {a : d.Idx N // a ∉ S}) :
    Measurable fun ω => greenSetMat d N u z S ω a b := by
  refine measurable_matrix_inv_apply (M := fun ω : Ω d =>
    (Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
      (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
      - z • (1 : Matrix {a : d.Idx N // a ∉ S} {a : d.Idx N // a ∉ S} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  have h : (fun ω : Ω d =>
      ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ∉ S} → d.Idx N)
        - z • (1 : Matrix {a : d.Idx N // a ∉ S} {a : d.Idx N // a ∉ S} ℂ)) p q)
      = fun ω => Hflow d N u ω p.1 q.1
          - z * (1 : Matrix {a : d.Idx N // a ∉ S} {a : d.Idx N // a ∉ S} ℂ) p q := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (measurable_Hflow d N u p.1 q.1).sub measurable_const

/-! ### The entries of the iterated minor, extended by `0`

`RBM.Gauss.greenSetMat` lives on the subtype `{a // a ∉ S}`, so its entries carry a proof that
the index has not been removed.  `RBM.Gauss.gEnt` erases that proof by extending the entry by
`0` to the levels that *have* removed `a` or `b`.  This is what makes the difference calculus of
`RBM1D/Gauss/MinorDiffGain.lean` total: no side condition travels with the recursion.

It is stated here, below both `RBM1D/Gauss/MinorDiffGain.lean` and
`RBM1D/Gauss/MinorGoodLe.lean`, so that the latter — which needs `gEnt` to phrase the
level-budgeted good event — does not have to import the former, which consumes that event. -/

section GEnt

variable {u : ℝ} {z : ℂ} {ω : Ω d} {a b : d.Idx N} {S : Finset (d.Idx N)}

/-- `G^{(S)}_{ab}`, extended by `0` to the levels that have removed `a` or `b`.  The extension is
what makes the difference calculus total: no side condition is carried along the recursion. -/
noncomputable def gEnt (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d) (a b : d.Idx N)
    (S : Finset (d.Idx N)) : ℂ :=
  if ha : a ∉ S then (if hb : b ∉ S then greenSetMat d N u z S ω ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0

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

end GEnt

/-! ### The `m`-fold minor difference

The gain comes from the *iterated* difference operator `Δ_{κ_1} ⋯ Δ_{κ_m}`, where
`Δ_κ X^{(S)} := X^{(S)} - X^{(S ∪ {κ})}`.  It is presented as a recursion on the list of rows,
acting on a whole *family* `Y : Finset (Idx) → Ω → ℂ` of minor versions; unfolded, it is the
inclusion–exclusion sum `∑_{T ⊆ {κ_1,…,κ_m}} (-1)^{#T} Y T`. -/

/-- `minorDiff d N [κ_1, …, κ_m] Y = Δ_{κ_1} ⋯ Δ_{κ_m} Y`, the `m`-fold minor difference of
the family `Y`. -/
noncomputable def minorDiff (d : Dims) (N : ℕ) :
    List (d.Idx N) → (Finset (d.Idx N) → Ω d → ℂ) → (Ω d → ℂ)
  | [], Y => Y ∅
  | κ :: l, Y => minorDiff d N l fun S ω => Y S ω - Y (insert κ S) ω

@[simp] theorem minorDiff_nil (d : Dims) (N : ℕ) (Y : Finset (d.Idx N) → Ω d → ℂ) :
    minorDiff d N [] Y = Y ∅ := rfl

@[simp] theorem minorDiff_cons (d : Dims) (N : ℕ) (κ : d.Idx N) (l : List (d.Idx N))
    (Y : Finset (d.Idx N) → Ω d → ℂ) :
    minorDiff d N (κ :: l) Y = minorDiff d N l fun S ω => Y S ω - Y (insert κ S) ω := rfl

/-- The rows carrying a `Q` in a word, in order.  These are exactly the rows along which the
minor difference is taken. -/
def qList (L : List (Bool × d.Idx N)) : List (d.Idx N) := (L.filter (·.1)).map Prod.snd

@[simp] theorem qList_nil (d : Dims) (N : ℕ) : qList ([] : List (Bool × d.Idx N)) = [] := rfl

@[simp] theorem qList_cons_true (κ : d.Idx N) (l : List (Bool × d.Idx N)) :
    qList ((true, κ) :: l) = κ :: qList l := rfl

@[simp] theorem qList_cons_false (κ : d.Idx N) (l : List (Bool × d.Idx N)) :
    qList ((false, κ) :: l) = qList l := rfl

theorem length_qList (L : List (Bool × d.Idx N)) : (qList L).length = numQ L := by
  simp [qList, numQ, List.countP_eq_length_filter]

/-! ### Linearity of the words, and their independence -/

theorem qRow_sub (k : d.Idx N) {X Y : Ω d → ℂ} (hX : BddMeas d X) (hY : BddMeas d Y) :
    qRow d N k (fun ω => X ω - Y ω) = fun ω => qRow d N k X ω - qRow d N k Y ω := by
  funext ω
  show X ω - Y ω - condRow d N k (fun ω' => X ω' - Y ω') ω
    = (X ω - condRow d N k X ω) - (Y ω - condRow d N k Y ω)
  rw [condRow_sub k (hX.rowIntegrable k) (hY.rowIntegrable k)]
  ring

/-- **The words are linear.** -/
theorem applyOps_sub (l : List (Bool × d.Idx N)) {X Y : Ω d → ℂ}
    (hX : BddMeas d X) (hY : BddMeas d Y) :
    applyOps d N l (fun ω => X ω - Y ω)
      = fun ω => applyOps d N l X ω - applyOps d N l Y ω := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [applyOps_cons_false, ih]
        exact condRow_sub κ ((hX.applyOps l).rowIntegrable κ)
          ((hY.applyOps l).rowIntegrable κ)
      · rw [applyOps_cons_true, ih]
        exact qRow_sub κ (hX.applyOps l) (hY.applyOps l)

/-- **A word preserves strict independence of row `κ`.** -/
theorem finDepOffRow_applyOps {κ : d.Idx N} (l : List (Bool × d.Idx N)) {X : Ω d → ℂ}
    (h : FinDepOffRow d N κ X) : FinDepOffRow d N κ (applyOps d N l X) := by
  induction l with
  | nil => simpa using h
  | cons x l ih =>
      obtain ⟨b, ν⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using finDepOffRow_condRow (k' := ν) ih
      · rw [applyOps_cons_true]
        exact ih.sub (finDepOffRow_condRow (k' := ν) ih)

/-! ### The annihilation identity

This is the whole content of the higher-order expansion on the probabilistic side, and it is an
**exact identity**, not an estimate: a word may be applied to the `m`-fold minor difference
instead of to the function itself, where `m` is the number of `Q`'s in the word.  The `m = 1`
case is the mechanism of `RBM.Gauss.norm_qRow_le_of_near`, here iterated. -/

/-- **`applyOps L (Y ∅) = applyOps L (Δ_{κ_1} ⋯ Δ_{κ_m} Y)`**, where `κ_1, …, κ_m` are the rows
carrying a `Q` in `L`.

The proof peels the outermost letter.  A `P` letter passes through by the inductive hypothesis.
For a `Q_κ` letter, replace the family `Y` by `Z S := Y S - Y (S ∪ {κ})`: by linearity of the
word, `applyOps l (Z ∅) = applyOps l (Y ∅) - applyOps l (Y {κ})`, and the subtracted term is
killed outright by `Q_κ`, because `Y {κ}` is strictly independent of row `κ` and a word
preserves that.  No estimate, no truncation, no `1_Ω`. -/
theorem applyOps_eq_applyOps_minorDiff (L : List (Bool × d.Idx N))
    (Y : Finset (d.Idx N) → Ω d → ℂ) (hbdd : ∀ S, BddMeas d (Y S))
    (hind : ∀ (S : Finset (d.Idx N)), ∀ κ ∈ S, FinDepOffRow d N κ (Y S)) :
    applyOps d N L (Y ∅) = applyOps d N L (minorDiff d N (qList L) Y) := by
  induction L generalizing Y with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [qList_cons_false, applyOps_cons_false, applyOps_cons_false, ih Y hbdd hind]
      · set Z : Finset (d.Idx N) → Ω d → ℂ := fun S ω => Y S ω - Y (insert κ S) ω with hZ
        have hbddZ : ∀ S, BddMeas d (Z S) := fun S => (hbdd S).sub (hbdd _)
        have hindZ : ∀ (S : Finset (d.Idx N)), ∀ ν ∈ S, FinDepOffRow d N ν (Z S) :=
          fun S ν hν => (hind S ν hν).sub (hind _ ν (Finset.mem_insert_of_mem hν))
        have hkey : applyOps d N l (Z ∅)
            = fun ω => applyOps d N l (Y ∅) ω - applyOps d N l (Y {κ}) ω := by
          have hins : insert κ (∅ : Finset (d.Idx N)) = {κ} := rfl
          rw [hZ]
          simpa only [hins] using applyOps_sub l (hbdd ∅) (hbdd {κ})
        have hann : qRow d N κ (applyOps d N l (Y {κ})) = 0 := by
          funext ω
          have hf : FinDepOffRow d N κ (applyOps d N l (Y {κ})) :=
            finDepOffRow_applyOps l (hind {κ} κ (Finset.mem_singleton_self κ))
          show applyOps d N l (Y {κ}) ω - condRow d N κ (applyOps d N l (Y {κ})) ω = 0
          rw [congrFun (condRow_of_finDepOffRow hf) ω, sub_self]
        rw [qList_cons_true, minorDiff_cons, applyOps_cons_true, applyOps_cons_true,
          ← hZ, ← ih Z hbddZ hindZ, hkey,
          qRow_sub κ ((hbdd ∅).applyOps l) ((hbdd {κ}).applyOps l), hann]
        funext ω
        show qRow d N κ (applyOps d N l (Y ∅)) ω
          = qRow d N κ (applyOps d N l (Y ∅)) ω - (0 : Ω d → ℂ) ω
        simp

/-- **The higher-order gain, in sup form.**  A word of `m` `Q`'s applied to `Y ∅` is at most
`2^m` times any uniform bound on the `m`-fold minor difference.  With `m = 1` and T85's
replacement error this is `RBM.Gauss.norm_qRow_le_of_near`. -/
theorem norm_applyOps_le_minorDiff (L : List (Bool × d.Idx N))
    (Y : Finset (d.Idx N) → Ω d → ℂ) (hbdd : ∀ S, BddMeas d (Y S))
    (hind : ∀ (S : Finset (d.Idx N)), ∀ κ ∈ S, FinDepOffRow d N κ (Y S))
    {δ : ℝ} (hδ : ∀ ω, ‖minorDiff d N (qList L) Y ω‖ ≤ δ) (ω : Ω d) :
    ‖applyOps d N L (Y ∅) ω‖ ≤ 2 ^ numQ L * δ := by
  rw [applyOps_eq_applyOps_minorDiff L Y hbdd hind]
  exact norm_applyOps_le L hδ ω

/-! ### The concrete family of iterated minors of `Z_k` -/

/-- `G^{(S)}_{kk} - m`, extended by `0` to the (never used) subsets containing `k`. -/
noncomputable def greenSetDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : Ω d → ℂ :=
  fun ω => if h : k ∉ S then greenSetMat d N u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0

/-- **`Z^{(S)}_k := (1 - E_k)(G^{(S)}_{kk} - m)`**, the `S`-minor version of the fluctuation.
`S = ∅` is `RBM.Gauss.flucDiag` and `S = {κ}` is T86's `RBM.Gauss.flucDiagMinor`. -/
noncomputable def flucDiagSet (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : Ω d → ℂ :=
  qRow d N k (greenSetDiagCentered d N u z m k S)

theorem finDepOffRows_greenSetDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : FinDepOffRows d N S (greenSetDiagCentered d N u z m k S) := by
  unfold greenSetDiagCentered
  by_cases h : k ∉ S
  · simp only [dite_eq_left h]
    exact (finDepOffRows_greenSetMat_apply d N u z S ⟨k, h⟩ ⟨k, h⟩).comp fun c => c - m
  · simp only [dite_eq_right h]
    exact ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem finDepOffRows_flucDiagSet (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : FinDepOffRows d N S (flucDiagSet d N u z m k S) :=
  finDepOffRows_qRow (finDepOffRows_greenSetDiagCentered d N u z m k S)

/-- The hypothesis `hind` of `RBM.Gauss.applyOps_eq_applyOps_minorDiff`, for the concrete
family. -/
theorem finDepOffRow_flucDiagSet (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) {κ : d.Idx N} (hκ : κ ∈ S) :
    FinDepOffRow d N κ (flucDiagSet d N u z m k S) :=
  (finDepOffRows_flucDiagSet d N u z m k S).finDepOffRow hκ

/-! #### `S = ∅` is the full resolvent -/

theorem greenSetMat_empty_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (ω : Ω d)
    (a b : {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))}) :
    greenSetMat d N u z ∅ ω a b = green (Hflow d N u ω) z a.1 b.1 := by
  classical
  set e : {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} ≃ d.Idx N :=
    Equiv.subtypeUnivEquiv fun x => Finset.notMem_empty x with he
  have hone : ∀ i j : {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))},
      (1 : Matrix {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))}
        {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} ℂ) i j
        = (1 : Matrix (d.Idx N) (d.Idx N) ℂ) i.1 j.1 := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · have h' : i.1 ≠ j.1 := fun hh => h (Subtype.ext hh)
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']
  have hsub : (Hflow d N u ω).submatrix
        (Subtype.val : {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))}
          {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} ℂ)
      = (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).submatrix ⇑e ⇑e := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, he,
      Equiv.subtypeUnivEquiv_apply]
    rw [hone i j]
  show (_ : Matrix _ _ ℂ)⁻¹ a b = _
  rw [hsub, Matrix.inv_submatrix_equiv]
  simp [green, he]

theorem flucDiagSet_empty (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) :
    flucDiagSet d N u z m k ∅ = flucDiag d N u z m k := by
  have hg : greenSetDiagCentered d N u z m k ∅ = greenDiagCentered d N u z m k := by
    funext ω
    have hk : k ∉ (∅ : Finset (d.Idx N)) := Finset.notMem_empty k
    show (if h : k ∉ (∅ : Finset (d.Idx N)) then
        greenSetMat d N u z ∅ ω ⟨k, h⟩ ⟨k, h⟩ - m else 0) = _
    rw [dite_eq_left hk, greenSetMat_empty_apply]
    rfl
  rw [flucDiagSet, hg, flucDiag_eq_qRow]

/-- `S = {κ}` is T84's single-row minor `G^{(κ)}`, so the `m = 1` case of the family below is
literally T86's `RBM.Gauss.flucDiagMinor` and inherits T85's replacement error. -/
theorem greenSetMat_singleton_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (κ : d.Idx N) (ω : Ω d)
    (a b : {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))}) :
    greenSetMat d N u z {κ} ω a b
      = greenMinorMat d N u z κ ω ⟨a.1, fun h => a.2 (Finset.mem_singleton.2 h)⟩
          ⟨b.1, fun h => b.2 (Finset.mem_singleton.2 h)⟩ := by
  classical
  set e : {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))} ≃ {x : d.Idx N // x ≠ κ} :=
    Equiv.subtypeEquivRight (fun x => by simp) with he
  set A : Matrix {x : d.Idx N // x ≠ κ} {x : d.Idx N // x ≠ κ} ℂ :=
    (Hflow d N u ω).submatrix (Subtype.val : {x : d.Idx N // x ≠ κ} → d.Idx N) Subtype.val
      - z • 1 with hA
  have hone : ∀ y w : {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))},
      (1 : Matrix {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))}
        {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))} ℂ) y w
        = (1 : Matrix {x : d.Idx N // x ≠ κ} {x : d.Idx N // x ≠ κ} ℂ) (e y) (e w) := by
    intro y w
    by_cases h : y.1 = w.1
    · have h1 : y = w := Subtype.ext h
      subst h1
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · have h1 : y ≠ w := fun hh => h (congrArg Subtype.val hh)
      have h2 : e y ≠ e w := fun hh =>
        h (congrArg (fun x : {x : d.Idx N // x ≠ κ} => x.1) hh)
      rw [Matrix.one_apply_ne h1, Matrix.one_apply_ne h2]
  have hsub : (Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))} → d.Idx N) Subtype.val
      - z • (1 : Matrix {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))}
          {x : d.Idx N // x ∉ ({κ} : Finset (d.Idx N))} ℂ)
      = A.submatrix ⇑e ⇑e := by
    ext y w
    simp only [hA, Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul]
    rw [hone y w]
    rfl
  show (_ : Matrix _ _ ℂ)⁻¹ a b = _
  rw [hsub, Matrix.inv_submatrix_equiv]
  rfl

/-- **`Z^{({κ})}_k = Z^{(κ)}_k`**: the `m = 1` member of the family is T86's replaced
fluctuation, so the gain at `m = 1` is T85's `ε ≍ Ψ²`, as `RBM.Gauss.norm_qRow_flucDiag_le`
already records. -/
theorem flucDiagSet_singleton (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) {k κ : d.Idx N}
    (hkκ : k ≠ κ) : flucDiagSet d N u z m k {κ} = flucDiagMinor d N u z m κ ⟨k, hkκ⟩ := by
  classical
  have hk : k ∉ ({κ} : Finset (d.Idx N)) := fun h => hkκ (Finset.mem_singleton.1 h)
  have hg : greenSetDiagCentered d N u z m k {κ}
      = greenMinorDiagCentered d N u z m κ ⟨k, hkκ⟩ := by
    funext ω
    show (if h : k ∉ ({κ} : Finset (d.Idx N)) then
        greenSetMat d N u z {κ} ω ⟨k, h⟩ ⟨k, h⟩ - m else 0) = _
    rw [dite_eq_left hk, greenSetMat_singleton_apply]
    rfl
  rw [flucDiagSet, hg]
  rfl

/-! ### One step of (4.9) between consecutive iterated minors

`RBM1D/Green/Minor.lean` (T40) proves (4.9) for an arbitrary `Fintype` index, so it iterates:
removing one more row `κ` from `G^{(S)}` gives `G^{(S ∪ {κ})}`, and the two differ by the rank-one
term `G^{(S)}_{aκ} G^{(S)}_{κb} / G^{(S)}_{κκ}`.  The only work is the index bookkeeping. -/

/-- Removing `κ` from `{a ∉ S}` is passing to `{a ∉ insert κ S}`. -/
def insertRowEquiv (d : Dims) (N : ℕ) {S : Finset (d.Idx N)} {κ : d.Idx N} (hκ : κ ∉ S) :
    {y : {x : d.Idx N // x ∉ S} // y ≠ ⟨κ, hκ⟩} ≃ {x : d.Idx N // x ∉ insert κ S} where
  toFun y := ⟨y.1.1, by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
  invFun x := ⟨⟨x.1, fun h => x.2 (Finset.mem_insert_of_mem h)⟩, by
    intro h
    exact x.2 (by rw [show x.1 = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

@[simp] theorem insertRowEquiv_apply (d : Dims) (N : ℕ) {S : Finset (d.Idx N)} {κ : d.Idx N}
    (hκ : κ ∉ S) (y : {y : {x : d.Idx N // x ∉ S} // y ≠ ⟨κ, hκ⟩}) :
    (insertRowEquiv d N hκ y).1 = y.1.1 := rfl

/-- **(4.9) between `G^{(S)}` and `G^{(S ∪ {κ})}`.**  The hypotheses are the ones (4.9) itself
needs: the `S`-minor is invertible and its `κκ` entry does not vanish — on the event (4.1) the
latter is `≥ 1/2` (`RBM.GoodEvent.half_le_norm_diag`). -/
theorem greenSetMat_insert_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (S : Finset (d.Idx N))
    (ω : Ω d) {κ : d.Idx N} (hκ : κ ∉ S)
    (hdet : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det)
    (hGκκ : greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0)
    {a b : d.Idx N} (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    greenSetMat d N u z (insert κ S) ω ⟨a, ha⟩ ⟨b, hb⟩
      = greenSetMat d N u z S ω ⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩
            ⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩
        - greenSetMat d N u z S ω ⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩ ⟨κ, hκ⟩
            * greenSetMat d N u z S ω ⟨κ, hκ⟩
              ⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩
            / greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ := by
  classical
  set n := {x : d.Idx N // x ∉ S}
  set M : Matrix n n ℂ := (Hflow d N u ω).submatrix (Subtype.val : n → d.Idx N) Subtype.val
      - z • (1 : Matrix n n ℂ) with hM
  set G : Matrix n n ℂ := greenSetMat d N u z S ω with hG
  have hGM : G * M = 1 := Matrix.nonsing_inv_mul M hdet
  set i : n := ⟨κ, hκ⟩ with hi
  set e := insertRowEquiv d N hκ with he
  set A : Matrix {x : d.Idx N // x ∉ insert κ S} {x : d.Idx N // x ∉ insert κ S} ℂ :=
    (Hflow d N u ω).submatrix (Subtype.val : {x : d.Idx N // x ∉ insert κ S} → d.Idx N)
      Subtype.val - z • 1 with hA
  have hminor : minorMat M i = A.submatrix ⇑e ⇑e := by
    ext y w
    have hone : (1 : Matrix n n ℂ) y.1 w.1
        = (1 : Matrix {x : d.Idx N // x ∉ insert κ S} {x : d.Idx N // x ∉ insert κ S} ℂ)
            (e y) (e w) := by
      by_cases h : y.1.1 = w.1.1
      · have h1 : y.1 = w.1 := Subtype.ext h
        have h2 : e y = e w := Subtype.ext h
        rw [h1, h2, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h1 : y.1 ≠ w.1 := fun hh => h (congrArg Subtype.val hh)
        have h2 : e y ≠ e w := fun hh =>
          h (congrArg (fun x : {x : d.Idx N // x ∉ insert κ S} => x.1) hh)
        rw [Matrix.one_apply_ne h1, Matrix.one_apply_ne h2]
    simp only [minorMat_apply, hM, hA, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, smul_eq_mul]
    rw [hone]
    rfl
  have hinv : minorGreen G i = (greenSetMat d N u z (insert κ S) ω).submatrix ⇑e ⇑e := by
    rw [← inv_minorMat hGM i hGκκ, hminor, Matrix.inv_submatrix_equiv]
    rfl
  have hane : (⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩ : n) ≠ i := by
    intro h
    exact ha (by rw [show a = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have hbne : (⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩ : n) ≠ i := by
    intro h
    exact hb (by rw [show b = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have := congrFun (congrFun hinv ⟨_, hane⟩) ⟨_, hbne⟩
  simp only [minorGreen_apply, Matrix.submatrix_apply] at this
  rw [show (e ⟨_, hane⟩ : {x : d.Idx N // x ∉ insert κ S}) = ⟨a, ha⟩ from Subtype.ext rfl,
    show (e ⟨_, hbne⟩ : {x : d.Idx N // x ∉ insert κ S}) = ⟨b, hb⟩ from Subtype.ext rfl] at this
  exact this.symm

/-- **The first minor difference of the centred diagonal entry factorises** — (4.9) at the
level of `S`.  This is the `m = 1` gain: two off-diagonal entries (each `≺ Ψ`) over one
diagonal entry (bounded below on the event (4.1)), so `≺ Ψ²`. -/
theorem greenSetDiagCentered_sub_insert (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) (ω : Ω d) (hk : k ∉ S) {κ : d.Idx N} (hκ : κ ∉ S) (hkκ : k ≠ κ)
    (hdet : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ S} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ S} {x : d.Idx N // x ∉ S} ℂ)).det)
    (hGκκ : greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0) :
    greenSetDiagCentered d N u z m k S ω
        - greenSetDiagCentered d N u z m k (insert κ S) ω
      = greenSetMat d N u z S ω ⟨k, hk⟩ ⟨κ, hκ⟩ * greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨k, hk⟩
          / greenSetMat d N u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ := by
  classical
  have hk' : k ∉ insert κ S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hkκ, hk⟩
  show (if h : k ∉ S then greenSetMat d N u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0)
      - (if h : k ∉ insert κ S then
          greenSetMat d N u z (insert κ S) ω ⟨k, h⟩ ⟨k, h⟩ - m else 0) = _
  rw [dite_eq_left hk, dite_eq_left hk',
    greenSetMat_insert_apply d N u z S ω hκ hdet hGκκ hk' hk']
  ring

/-- **Step 0 of the ticket, in algebra**: a difference of two triple products, each factor of
which is itself close to its partner, is *one order smaller* than the products themselves.

With the sizes of §4 — `a, b ≍ Ψ` the two off-diagonal entries, `c ≍ 1` the inverse diagonal
entry, and every first difference `≍ Ψ²` — this gives `Ψ³`, **not** `2 Ψ²`.  This is precisely
the multiplicativity of the gain: the second `Q` acts on the first replacement error and earns
another `Ψ`, rather than merely earning its own `Ψ²` independently. -/
theorem norm_mul_three_sub_le {a b c a' b' c' : ℂ} {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1)
    (ha' : ‖a'‖ ≤ Ψ) (hb' : ‖b'‖ ≤ Ψ) (hc : ‖c‖ ≤ 2)
    (haa : ‖a - a'‖ ≤ Ψ ^ 2) (hbb : ‖b - b'‖ ≤ Ψ ^ 2) (hcc : ‖c - c'‖ ≤ 4 * Ψ ^ 2) :
    ‖a * b * c - a' * b' * c'‖ ≤ 10 * Ψ ^ 3 := by
  have hsq : Ψ ^ 2 ≤ Ψ := by nlinarith
  have hb : ‖b‖ ≤ 2 * Ψ := by
    have h2 : ‖b‖ ≤ ‖b - b'‖ + ‖b'‖ := by
      have : b = (b - b') + b' := by ring
      calc ‖b‖ = ‖(b - b') + b'‖ := by rw [← this]
        _ ≤ ‖b - b'‖ + ‖b'‖ := norm_add_le _ _
    linarith
  have hdec : a * b * c - a' * b' * c'
      = (a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c') := by ring
  have h1 : ‖(a - a') * b * c‖ ≤ Ψ ^ 2 * (2 * Ψ) * 2 := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul haa hb (norm_nonneg _) (by positivity)) hc
      (norm_nonneg _) (by positivity)
  have h2 : ‖a' * (b - b') * c‖ ≤ Ψ * Ψ ^ 2 * 2 := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul ha' hbb (norm_nonneg _) hΨ0) hc
      (norm_nonneg _) (by positivity)
  have h3 : ‖a' * b' * (c - c')‖ ≤ Ψ * Ψ * (4 * Ψ ^ 2) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul ha' hb' (norm_nonneg _) hΨ0) hcc (norm_nonneg _)
      (by positivity)
  have hsum : ‖(a - a') * b * c + a' * (b - b') * c + a' * b' * (c - c')‖
      ≤ ‖(a - a') * b * c‖ + ‖a' * (b - b') * c‖ + ‖a' * b' * (c - c')‖ := by
    have hA := norm_add_le ((a - a') * b * c + a' * (b - b') * c) (a' * b' * (c - c'))
    have hB := norm_add_le ((a - a') * b * c) (a' * (b - b') * c)
    linarith
  have hpow : Ψ ^ 4 ≤ Ψ ^ 3 := by nlinarith [pow_nonneg hΨ0 3]
  rw [hdec]
  nlinarith [hsum, h1, h2, h3, hpow, pow_nonneg hΨ0 3]

/-- **The second minor difference, expanded.**  The two first differences of
`RBM.Gauss.greenSetDiagCentered_sub_insert`, at level `∅` and at level `{κ₂}`.  Feeding this to
`RBM.Gauss.norm_mul_three_sub_le` is the `m = 2` case of the gain. -/
theorem minorDiff_pair_greenSetDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ)
    {k κ₁ κ₂ : d.Idx N} (ω : Ω d) (hk1 : k ≠ κ₁) (hk2 : k ∉ ({κ₂} : Finset (d.Idx N)))
    (h12 : κ₁ ∉ ({κ₂} : Finset (d.Idx N)))
    (hdet₀ : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))}
            {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} ℂ)).det)
    (hdet₂ : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ ({κ₂} : Finset (d.Idx N))} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ ({κ₂} : Finset (d.Idx N))}
            {x : d.Idx N // x ∉ ({κ₂} : Finset (d.Idx N))} ℂ)).det)
    (hG₀ : greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩ ⟨κ₁, Finset.notMem_empty κ₁⟩ ≠ 0)
    (hG₂ : greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨κ₁, h12⟩ ≠ 0) :
    minorDiff d N [κ₁, κ₂] (greenSetDiagCentered d N u z m k) ω
      = (greenSetMat d N u z ∅ ω ⟨k, Finset.notMem_empty k⟩ ⟨κ₁, Finset.notMem_empty κ₁⟩
            * greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩ ⟨k, Finset.notMem_empty k⟩)
          * (greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩
              ⟨κ₁, Finset.notMem_empty κ₁⟩)⁻¹
        - (greenSetMat d N u z {κ₂} ω ⟨k, hk2⟩ ⟨κ₁, h12⟩
              * greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨k, hk2⟩)
          * (greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨κ₁, h12⟩)⁻¹ := by
  classical
  have h₀ := greenSetDiagCentered_sub_insert d N u z m k ∅ ω (Finset.notMem_empty k)
    (Finset.notMem_empty κ₁) hk1 hdet₀ hG₀
  have h₂ := greenSetDiagCentered_sub_insert d N u z m k {κ₂} ω hk2 h12 hk1 hdet₂ hG₂
  show (greenSetDiagCentered d N u z m k ∅ ω
      - greenSetDiagCentered d N u z m k (insert κ₁ ∅) ω)
    - (greenSetDiagCentered d N u z m k {κ₂} ω
      - greenSetDiagCentered d N u z m k (insert κ₁ {κ₂}) ω) = _
  rw [show insert κ₁ (∅ : Finset (d.Idx N)) = insert κ₁ ∅ from rfl, h₀, h₂]
  rw [div_eq_mul_inv, div_eq_mul_inv]

/-- **`m = 2`: the gain is multiplicative, `Ψ³` and not `2 Ψ²`.**

Combining the expansion `RBM.Gauss.minorDiff_pair_greenSetDiagCentered` of the second minor
difference with the algebraic estimate `RBM.Gauss.norm_mul_three_sub_le`: with the paper's
sizes — off-diagonal entries `≤ Ψ`, inverse diagonal entries `≤ 2` (the event (4.1) gives
`|G_{κκ}| ≥ 1/2`), and every *first* difference `≤ Ψ²` — the **second** difference is `≤ 10 Ψ³`.

Two independent first-order replacements would only give `O(Ψ²)`.  The extra `Ψ` is bought by
the second `Q_{κ₂}` acting on the *replacement error* of the first, which is exactly the
mechanism `RBM.Gauss.applyOps_eq_applyOps_minorDiff` iterates to all orders. -/
theorem norm_minorDiff_pair_greenSetDiagCentered_le (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ)
    {k κ₁ κ₂ : d.Idx N} (ω : Ω d) (hk1 : k ≠ κ₁) (hk2 : k ∉ ({κ₂} : Finset (d.Idx N)))
    (h12 : κ₁ ∉ ({κ₂} : Finset (d.Idx N)))
    (hdet₀ : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))}
            {x : d.Idx N // x ∉ (∅ : Finset (d.Idx N))} ℂ)).det)
    (hdet₂ : IsUnit ((Hflow d N u ω).submatrix
      (Subtype.val : {x : d.Idx N // x ∉ ({κ₂} : Finset (d.Idx N))} → d.Idx N) Subtype.val
        - z • (1 : Matrix {x : d.Idx N // x ∉ ({κ₂} : Finset (d.Idx N))}
            {x : d.Idx N // x ∉ ({κ₂} : Finset (d.Idx N))} ℂ)).det)
    (hG₀ : greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩ ⟨κ₁, Finset.notMem_empty κ₁⟩ ≠ 0)
    (hG₂ : greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨κ₁, h12⟩ ≠ 0)
    {Ψ : ℝ} (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1)
    (hoff₁ : ‖greenSetMat d N u z {κ₂} ω ⟨k, hk2⟩ ⟨κ₁, h12⟩‖ ≤ Ψ)
    (hoff₂ : ‖greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨k, hk2⟩‖ ≤ Ψ)
    (hdiag : ‖(greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩
      ⟨κ₁, Finset.notMem_empty κ₁⟩)⁻¹‖ ≤ 2)
    (hd₁ : ‖greenSetMat d N u z ∅ ω ⟨k, Finset.notMem_empty k⟩ ⟨κ₁, Finset.notMem_empty κ₁⟩
      - greenSetMat d N u z {κ₂} ω ⟨k, hk2⟩ ⟨κ₁, h12⟩‖ ≤ Ψ ^ 2)
    (hd₂ : ‖greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩ ⟨k, Finset.notMem_empty k⟩
      - greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨k, hk2⟩‖ ≤ Ψ ^ 2)
    (hd₃ : ‖(greenSetMat d N u z ∅ ω ⟨κ₁, Finset.notMem_empty κ₁⟩
        ⟨κ₁, Finset.notMem_empty κ₁⟩)⁻¹
      - (greenSetMat d N u z {κ₂} ω ⟨κ₁, h12⟩ ⟨κ₁, h12⟩)⁻¹‖ ≤ 4 * Ψ ^ 2) :
    ‖minorDiff d N [κ₁, κ₂] (greenSetDiagCentered d N u z m k) ω‖ ≤ 10 * Ψ ^ 3 := by
  rw [minorDiff_pair_greenSetDiagCentered d N u z m ω hk1 hk2 h12 hdet₀ hdet₂ hG₀ hG₂]
  exact norm_mul_three_sub_le hΨ0 hΨ1 hoff₁ hoff₂ hdiag hd₁ hd₂ hd₃

/-! ### Crude bounds on the difference, and the deterministic envelope -/

/-- Each difference at most doubles a uniform bound. -/
theorem norm_minorDiff_le (l : List (d.Idx N)) (Y : Finset (d.Idx N) → Ω d → ℂ) {b : ℝ}
    (hb : ∀ S ω, ‖Y S ω‖ ≤ b) (ω : Ω d) :
    ‖minorDiff d N l Y ω‖ ≤ 2 ^ l.length * b := by
  induction l generalizing Y b with
  | nil => simpa using hb ∅ ω
  | cons κ l ih =>
      have hb' : ∀ (S : Finset (d.Idx N)) (ω' : Ω d),
          ‖(fun S ω => Y S ω - Y (insert κ S) ω) S ω'‖ ≤ 2 * b := fun S ω' =>
        le_trans (norm_sub_le _ _) (by linarith [hb S ω', hb (insert κ S) ω'])
      have := ih (fun S ω => Y S ω - Y (insert κ S) ω) hb'
      rw [minorDiff_cons]
      calc ‖minorDiff d N l (fun S ω => Y S ω - Y (insert κ S) ω) ω‖
          ≤ 2 ^ l.length * (2 * b) := this
        _ = 2 ^ (κ :: l).length * b := by rw [List.length_cons, pow_succ]; ring

section Env

open scoped Matrix.Norms.L2Operator

variable {E t : ℝ}

/-- `|G^{(S)}_{ab}| ≤ η_t⁻¹` for every `ω`: `H^{(S)}` is a minor of a Hermitian matrix. -/
theorem norm_greenSetMat_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {S : Finset (d.Idx N)} (a b : {x : d.Idx N // x ∉ S}) (ω : Ω d) :
    ‖greenSetMat d N u (zt E t) S ω a b‖ ≤ (etaT E t)⁻¹ := by
  have : Nonempty {x : d.Idx N // x ∉ S} := ⟨a⟩
  rw [greenSetMat_eq_green_submatrix]
  exact le_trans (norm_apply_le_l2_opNorm _ a b)
    (norm_green_zt_le ((Hflow_isHermitian d N u ω).submatrix _) hE ht)

theorem measurable_greenSetDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : Measurable (greenSetDiagCentered d N u z m k S) := by
  unfold greenSetDiagCentered
  by_cases h : k ∉ S
  · simp only [dite_eq_left h]
    exact (measurable_greenSetMat_apply d N u z S ⟨k, h⟩ ⟨k, h⟩).sub measurable_const
  · simp only [dite_eq_right h]
    exact measurable_const

theorem norm_greenSetDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    ‖greenSetDiagCentered d N u (zt E t) (mE E) k S ω‖ ≤ (etaT E t)⁻¹ + 1 := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  show ‖if h : k ∉ S then greenSetMat d N u (zt E t) S ω ⟨k, h⟩ ⟨k, h⟩ - mE E else 0‖ ≤ _
  by_cases h : k ∉ S
  · rw [dite_eq_left h]
    refine le_trans (norm_sub_le _ _)
      (add_le_add (norm_greenSetMat_apply_le_etaT hE ht u ⟨k, h⟩ ⟨k, h⟩ ω) ?_)
    exact le_of_eq (norm_mE hE.le)
  · rw [dite_eq_right h, norm_zero]
    positivity

theorem bddMeas_greenSetDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N)
    (S : Finset (d.Idx N)) :
    BddMeas d (greenSetDiagCentered d N u (zt E t) (mE E) k S) :=
  ⟨measurable_greenSetDiagCentered d N u (zt E t) (mE E) k S, (etaT E t)⁻¹ + 1,
    norm_greenSetDiagCentered_le_env hE ht u k S⟩

theorem bddMeas_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : BddMeas d (flucDiagSet d N u (zt E t) (mE E) k S) :=
  (bddMeas_greenSetDiagCentered hE ht u k S).qRow k

theorem norm_flucDiagSet_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    ‖flucDiagSet d N u (zt E t) (mE E) k S ω‖ ≤ 2 * ((etaT E t)⁻¹ + 1) := by
  have h := norm_sub_condRow_le (k := k)
    (X := greenSetDiagCentered d N u (zt E t) (mE E) k S)
    (b := (etaT E t)⁻¹ + 1) (norm_greenSetDiagCentered_le_env hE ht u k S) ω
  exact h

/-- **The `m`-th order analogue of `RBM.Gauss.norm_qRow_flucDiag_le`.**  Whatever word `L`
carries, the fluctuation `Z_k` under it is controlled by the minor difference along the rows
of `L` that carry a `Q`.  At `numQ L = 1` this is T85's replacement error `ε` (up to the
factor `2`); at `numQ L = m` it is the `m`-fold difference, whose size is `ρ^m B`. -/
theorem norm_applyOps_flucDiag_le_of_minorDiff (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (L : List (Bool × d.Idx N)) (k : d.Idx N) {δ : ℝ}
    (hδ : ∀ ω, ‖minorDiff d N (qList L) (flucDiagSet d N u (zt E t) (mE E) k) ω‖ ≤ δ)
    (ω : Ω d) :
    ‖applyOps d N L (flucDiag d N u (zt E t) (mE E) k) ω‖ ≤ 2 ^ numQ L * δ := by
  rw [← flucDiagSet_empty d N u (zt E t) (mE E) k]
  exact norm_applyOps_le_minorDiff L _ (fun S => bddMeas_flucDiagSet hE ht u k S)
    (fun S κ hκ => finDepOffRow_flucDiagSet d N u (zt E t) (mE E) k S hκ) hδ ω

/-! ### The interface, reduced to the iterated minors

`RBM.Gauss.applyOps_eq_applyOps_minorDiff` turns `RBM.Gauss.FlucGain` — a statement about the
effect of `m` conditional fluctuations — into a statement about the `m`-fold minor difference
alone.  The conditional expectations survive only as the outer word, which costs at most
`2^m` and no longer has to *produce* anything. -/

/-- **The remaining input of (4.12), with the probabilistic half removed.**  Same shape as
`RBM.Gauss.FlucGain`, with `Z_{k}` replaced by the `m`-fold minor difference
`Δ_{κ_1} ⋯ Δ_{κ_m} Z^{(·)}_{k}` along the rows carrying a `Q`.

Stated, like `RBM.Gauss.FlucGain`, as a bound on an *expectation*: a pointwise `Ψ`-sized bound
on the minor differences does not exist, since the local law has an exceptional set.  No
indicator is introduced anywhere. -/
def MinorDiffGain (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N)),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      ∫ ω, ∏ i, ‖applyOps d N (L i)
          (minorDiff d N (qList (L i)) (flucDiagSet d N u z m (k i))) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- **`RBM.Gauss.FlucGain` for every `m`, from the size of the iterated minor differences.**

This is the step-0 mechanism of the ticket, for all `m` at once: the `m` conditional
fluctuations `Q_{κ_1} ⋯ Q_{κ_m}` do not merely each contribute their own replacement error —
they compose into the `m`-fold difference `Δ_{κ_1} ⋯ Δ_{κ_m}`, so the gains **multiply**.  The
identity `RBM.Gauss.applyOps_eq_applyOps_minorDiff` is exact, so nothing is lost. -/
theorem flucGain_of_minorDiffGain (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ}
    (h : MinorDiffGain d N u (zt E t) (mE E) B ρ) :
    FlucGain d N u (zt E t) (mE E) B ρ := by
  refine ⟨h.1, h.2.1, fun ι _ k L h1 h2 => ?_⟩
  have hrw : ∀ i : ι, applyOps d N (L i) (flucDiag d N u (zt E t) (mE E) (k i))
      = applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) := by
    intro i
    rw [← flucDiagSet_empty d N u (zt E t) (mE E) (k i)]
    exact applyOps_eq_applyOps_minorDiff (L i) _
      (fun S => bddMeas_flucDiagSet hE ht u (k i) S)
      (fun S κ hκ => finDepOffRow_flucDiagSet d N u (zt E t) (mE E) (k i) S hκ)
  simp only [hrw]
  exact h.2.2 ι k L h1 h2

/-! #### The same interface, graded by word length

T137 graded `RBM.Gauss.FlucGain` by the length of the word, because the constants of the
`m`-fold minor difference grow with `m` and the ungraded statement is therefore unavailable at
`ρ ≍ Ψ`, while the `2p`-th moment expansion only ever builds words of length `≤ 2p`
(`RBM.Gauss.OpsOkOut.length_le`).  `RBM.Gauss.MinorDiffGainUpTo` is the same grading applied to
the reduced interface, and `RBM.Gauss.flucGainUpTo_of_minorDiffGainUpTo` is the graded
analogue of `RBM.Gauss.flucGain_of_minorDiffGain`: the annihilation identity is an identity,
so the length restriction passes straight through it. -/

/-- **`RBM.Gauss.MinorDiffGain` restricted to words of length at most `M`.**  This is the form
in which §4 actually proves the size of the iterated minor differences
(`RBM.Gauss.minorDiffGainUpTo_of_minorGood`), the `M`-dependence of `B` and `ρ` being exactly
what makes the bounded-length statement available where the unbounded one is not. -/
def MinorDiffGainUpTo (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N)),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) →
      ∫ ω, ∏ i, ‖applyOps d N (L i)
          (minorDiff d N (qList (L i)) (flucDiagSet d N u z m (k i))) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- The ungraded reduced interface implies every graded one; in particular
`RBM.Gauss.minorDiffGain_env` still witnesses non-vacuity at every grade. -/
theorem MinorDiffGain.upTo {u : ℝ} {z m : ℂ} {B ρ : ℝ}
    (h : MinorDiffGain d N u z m B ρ) (M : ℕ) : MinorDiffGainUpTo d N u z m B ρ M :=
  ⟨h.1, h.2.1, fun ι _ k L h1 h2 _ => h.2.2 ι k L h1 h2⟩

/-- **`RBM.Gauss.FlucGainUpTo` from `RBM.Gauss.MinorDiffGainUpTo`** — the graded analogue of
`RBM.Gauss.flucGain_of_minorDiffGain`, with the same proof: the rewriting step is the exact
identity `RBM.Gauss.applyOps_eq_applyOps_minorDiff`, which does not touch the words, so the
length hypothesis is simply handed on. -/
theorem flucGainUpTo_of_minorDiffGainUpTo (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ} {M : ℕ}
    (h : MinorDiffGainUpTo d N u (zt E t) (mE E) B ρ M) :
    FlucGainUpTo d N u (zt E t) (mE E) B ρ M := by
  refine ⟨h.1, h.2.1, fun ι _ k L h1 h2 h3 => ?_⟩
  have hrw : ∀ i : ι, applyOps d N (L i) (flucDiag d N u (zt E t) (mE E) (k i))
      = applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) := by
    intro i
    rw [← flucDiagSet_empty d N u (zt E t) (mE E) (k i)]
    exact applyOps_eq_applyOps_minorDiff (L i) _
      (fun S => bddMeas_flucDiagSet hE ht u (k i) S)
      (fun S κ hκ => finDepOffRow_flucDiagSet d N u (zt E t) (mE E) (k i) S hκ)
  simp only [hrw]
  exact h.2.2 ι k L h1 h2 h3

/-! #### The cardinality budget on the reduced interface — T177

`RBM.Gauss.MinorDiffGainUpTo` has the same defect as `RBM.Gauss.FlucGainUpTo`: its index type
`ι` is unbudgeted, so `RBM.Gauss.integral_pow_norm_flucDiag_le_of_minorDiffGainUpTo`
(`RBM1D/Gauss/MinorDiffCond.lean`) derives `‖Z_k‖_{L^j} ≤ B` for every `j`, hence
`‖Z_k‖_∞ ≤ B`, which T172 contradicts at `B ≍ Ψ`.  `RBM.Gauss.MinorDiffGainUpTo'` adds the
budget `#ι ≤ n`, and `RBM.Gauss.flucGainUpTo'_of_minorDiffGainUpTo'` carries it across the
annihilation identity, which does not touch the index type.

The budget is what lets the conditionalized estimate of `RBM1D/Gauss/MinorDiffCond.lean` be
*packaged* as an interface rather than carried with its additive remainder forever: with
`#ι ≤ n` the remainder `condEnv^{#ι} P(Bad)` is dominated by `B₀^{#ι} (2Ψ)^{∑ q}` as soon as
`condEnv^n P(Bad) ≤ B₀^n (2Ψ)^{n M}`, a condition on the *measure of the exceptional set* that
`RBM.Gauss.HighProb` makes true for every fixed pair of budgets. -/

/-- **`RBM.Gauss.MinorDiffGainUpTo` with the cardinality budget `#ι ≤ n`.** -/
def MinorDiffGainUpTo' (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M n : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N)),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ n →
      ∫ ω, ∏ i, ‖applyOps d N (L i)
          (minorDiff d N (qList (L i)) (flucDiagSet d N u z m (k i))) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

theorem MinorDiffGainUpTo'.B_nonneg {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M n : ℕ}
    (h : MinorDiffGainUpTo' d N u z m B ρ M n) : 0 ≤ B := h.1

theorem MinorDiffGainUpTo'.rho_nonneg {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M n : ℕ}
    (h : MinorDiffGainUpTo' d N u z m B ρ M n) : 0 ≤ ρ := h.2.1

/-- The unbudgeted graded interface implies the budgeted one at every `n`. -/
theorem MinorDiffGainUpTo.budget {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M : ℕ}
    (h : MinorDiffGainUpTo d N u z m B ρ M) (n : ℕ) :
    MinorDiffGainUpTo' d N u z m B ρ M n :=
  ⟨h.1, h.2.1, fun ι _ k L h1 h2 h3 _ => h.2.2 ι k L h1 h2 h3⟩

/-- The ungraded reduced interface implies every budgeted one. -/
theorem MinorDiffGain.upTo' {u : ℝ} {z m : ℂ} {B ρ : ℝ} (h : MinorDiffGain d N u z m B ρ)
    (M n : ℕ) : MinorDiffGainUpTo' d N u z m B ρ M n := (h.upTo M).budget n

/-- Both budgets may be lowered. -/
theorem MinorDiffGainUpTo'.mono {u : ℝ} {z m : ℂ} {B ρ : ℝ} {M M' n n' : ℕ} (hM : M' ≤ M)
    (hn : n' ≤ n) (h : MinorDiffGainUpTo' d N u z m B ρ M n) :
    MinorDiffGainUpTo' d N u z m B ρ M' n' :=
  ⟨h.1, h.2.1, fun ι _ k L h1 h2 hlen hcard =>
    h.2.2 ι k L h1 h2 (fun i => le_trans (hlen i) hM) (le_trans hcard hn)⟩

/-- Relaxing the size parameters. -/
theorem MinorDiffGainUpTo'.mono_params {u : ℝ} {z m : ℂ} {B ρ B' ρ' : ℝ} {M n : ℕ}
    (hB : B ≤ B') (hρ : ρ ≤ ρ') (h : MinorDiffGainUpTo' d N u z m B ρ M n) :
    MinorDiffGainUpTo' d N u z m B' ρ' M n := by
  refine ⟨le_trans h.1 hB, le_trans h.2.1 hρ, fun ι _ k L h1 h2 hlen hcard => ?_⟩
  refine le_trans (h.2.2 ι k L h1 h2 hlen hcard) ?_
  exact mul_le_mul (pow_le_pow_left₀ h.1 hB _) (pow_le_pow_left₀ h.2.1 hρ _)
    (pow_nonneg h.2.1 _) (pow_nonneg (le_trans h.1 hB) _)

/-- **`RBM.Gauss.FlucGainUpTo'` from `RBM.Gauss.MinorDiffGainUpTo'`** — the budgeted analogue
of `RBM.Gauss.flucGainUpTo_of_minorDiffGainUpTo`, with the same proof: the rewriting step is
the exact identity `RBM.Gauss.applyOps_eq_applyOps_minorDiff`, which touches neither the words
nor the index type, so both budgets are handed on unchanged. -/
theorem flucGainUpTo'_of_minorDiffGainUpTo' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ}
    {M n : ℕ} (h : MinorDiffGainUpTo' d N u (zt E t) (mE E) B ρ M n) :
    FlucGainUpTo' d N u (zt E t) (mE E) B ρ M n := by
  refine ⟨h.1, h.2.1, fun ι _ k L h1 h2 h3 h4 => ?_⟩
  have hrw : ∀ i : ι, applyOps d N (L i) (flucDiag d N u (zt E t) (mE E) (k i))
      = applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) := by
    intro i
    rw [← flucDiagSet_empty d N u (zt E t) (mE E) (k i)]
    exact applyOps_eq_applyOps_minorDiff (L i) _
      (fun S => bddMeas_flucDiagSet hE ht u (k i) S)
      (fun S κ hκ => finDepOffRow_flucDiagSet d N u (zt E t) (mE E) (k i) S hκ)
  simp only [hrw]
  exact h.2.2 ι k L h1 h2 h3 h4

/-- **The reduced interface is not vacuous**: the deterministic envelope gives it
unconditionally with `ρ = 4` (no gain), exactly as `RBM.Gauss.flucGain_env` does for
`RBM.Gauss.FlucGain`.  The content of §4 is the same statement with `ρ ≍ Ψ`. -/
theorem minorDiffGain_env (hE : |E| < 2) (ht : t < 1) (d : Dims) (N : ℕ) (u : ℝ) :
    MinorDiffGain d N u (zt E t) (mE E) (2 * ((etaT E t)⁻¹ + 1)) 4 := by
  classical
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  refine ⟨by positivity, by norm_num, fun ι _ k L _ _ => ?_⟩
  set B : ℝ := 2 * ((etaT E t)⁻¹ + 1) with hB
  have hB0 : 0 ≤ B := by positivity
  have hb : ∀ (i : ι) (ω : Ω d),
      ‖applyOps d N (L i)
        (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))) ω‖
        ≤ 4 ^ numQ (L i) * B := by
    intro i ω
    have hdiff : ∀ ω', ‖minorDiff d N (qList (L i))
        (flucDiagSet d N u (zt E t) (mE E) (k i)) ω'‖ ≤ 2 ^ numQ (L i) * B := by
      intro ω'
      have := norm_minorDiff_le (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i))
        (fun S ω'' => norm_flucDiagSet_le_env hE ht u (k i) S ω'') ω'
      rwa [length_qList] at this
    refine le_trans (norm_applyOps_le (L i) hdiff ω) (le_of_eq ?_)
    rw [← mul_assoc, ← pow_add, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  have hbm : ∀ i : ι, BddMeas d (applyOps d N (L i)
      (minorDiff d N (qList (L i)) (flucDiagSet d N u (zt E t) (mE E) (k i)))) := by
    intro i
    refine BddMeas.applyOps ?_ (L i)
    have hmd : ∀ l : List (d.Idx N), ∀ Y : Finset (d.Idx N) → Ω d → ℂ,
        (∀ S, BddMeas d (Y S)) → BddMeas d (minorDiff d N l Y) := by
      intro l
      induction l with
      | nil => intro Y hY; simpa using hY ∅
      | cons κ l ih =>
          intro Y hY
          rw [minorDiff_cons]
          exact ih _ fun S => (hY S).sub (hY _)
    exact hmd _ _ fun S => bddMeas_flucDiagSet hE ht u (k i) S
  refine le_trans (integral_prod_norm_le_of_bounds hbm hb) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]
  ring

end Env

end RBM.Gauss
