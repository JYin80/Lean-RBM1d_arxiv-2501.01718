/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucIter

/-!
# The higher-order minor expansion: the gain for `m ≥ 2`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4: the last interface of the fluctuation averaging (4.12).

`RBM1D/Gauss/FlucIter.lean` reduces (4.12) to one hypothesis, the gain
`RBM.Gauss.FlucGainUpTo'`: that applying `m` conditional fluctuations `Q_{κ_1} ⋯ Q_{κ_m}`
(distinct rows, all different from `k`) to `Z_k = (1 - E_k)(G_{kk} - m)` gains a factor `ρ^m`
with `ρ ≍ Ψ`.  For `m = 0` and `m = 1` this is elementary.

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

At `m = 2`: by (4.9) between `G^{(S)}` and `G^{(S ∪ {κ})}` (`RBM.Gauss.greenSetMat_insert_apply`,
the iteration of `RBM1D/Green/Minor.lean` to `Finset`-indexed minors), the second difference of
`G_{kk}` is the difference of the two triple products `G_{kκ₁} G_{κ₁k} / G_{κ₁κ₁}` at levels `∅`
and `{κ₂}`; with off-diagonal entries `≤ Ψ`, inverse diagonal entries `≤ 2` and each *first*
difference `≤ Ψ²`, it is of order `Ψ³` and not `2 Ψ²`.

## What is proved

1. **`Finset`-indexed minors.**  `RBM.Gauss.greenSetMat d N u z S` is the resolvent on
   `{a ∉ S}`; `RBM.Gauss.FinDepOffRows` generalizes `RBM.Gauss.FinDepOffRow` to a whole
   `Finset` of rows, and `RBM.Gauss.finDepOffRows_of_minorSet` is the master independence
   lemma.  `S = ∅` is the full resolvent (`RBM.Gauss.greenSetMat_empty_apply`), and `S = {κ}`
   is the minor resolvent of `RBM1D/Gauss/CondRow.lean`, so `m = 1` is the first-order
   replacement and inherits `ε ≍ Ψ²`.
2. **The annihilation identity** `RBM.Gauss.applyOps_eq_applyOps_minorDiff`.  Unconditional;
   `P` letters pass through, each `Q` letter costs a factor `2` and buys one difference.
3. **One step of (4.9) for iterated minors** (`RBM.Gauss.greenSetMat_insert_apply`).
4. **The gain from the reduced interface** (`RBM.Gauss.flucGainUpTo'_of_minorDiffGainUpTo'`):
   `RBM.Gauss.FlucGainUpTo'` follows from `RBM.Gauss.MinorDiffGainUpTo'`, a statement about the
   size of the iterated minor differences only, budgeted in the word length and in the number
   of slots.  The annihilation identity touches neither the words nor the index type, so both
   budgets pass through it unchanged.  This is the form in which §4's estimate of the minor
   differences (`RBM1D/Gauss/MinorDiffGain.lean`) is available, and the form the `2p`-th moment
   expansion consumes.

## What is *not* done, and why the interface is not empty

`RBM.Gauss.MinorDiffGainUpTo'` — the **size** of the iterated minor differences, in
expectation — is not discharged here.  It is strictly weaker than the gain: every conditional
expectation has been removed from its content, and what remains is a statement about Green's
function minors and the local law only.  The general-`m` size estimate needs a Leibniz calculus
for `Δ_κ` over the factorization of (4.9) (`Δ_κ(XY) = (Δ_κ X) Y + X^{(κ)} (Δ_κ Y)`,
`Δ_κ (1/X) = (Δ_κ X)/(X X^{(κ)})`), which is a separate piece of work.

It is stated, like the gain, as a bound on an *expectation*.  This is deliberate: a
pointwise `Ψ`-sized bound is **false** (the local law has an exceptional set), and no indicator
is introduced anywhere — the annihilation identity is used before any truncation, so the
obstruction that `1_Ω` destroys `E_κ[(1 - E_κ)X] = 0` and is not `FinDepOffRow` never arises.

## Deviations from the paper

* The `m`-fold difference is presented as a recursion on a *list* of rows acting on a family
  indexed by `Finset`s (`RBM.Gauss.minorDiff`), rather than as the inclusion–exclusion sum
  `∑_{T ⊆ {κ_1,…,κ_m}} (-1)^{#T} G^{(T)}`.  The two agree; the recursion is what matches the
  peeling of the word.
* Constants are not the paper's: each `Q` costs `2` and each difference costs `2`.
* `RBM.Gauss.MinorDiffGainUpTo'` is a hypothesis, not a theorem.
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
coordinates, none of which is a row-`κ` coordinate for any `κ ∈ S`.  This is
`RBM.Gauss.FinDepOffRow` with the witness set constrained to avoid all of `S` at once. -/
def FinDepOffRows (d : Dims) (N : ℕ) (S : Finset (d.Idx N)) {V : Type*} (g : Ω d → V) : Prop :=
  ∃ I : Finset (Coord d), (∀ c ∈ I, ∀ κ ∈ S, ¬ IsRowCoord d N κ c) ∧
    ∀ ω ω' : Ω d, (∀ c ∈ I, ω c = ω' c) → g ω = g ω'

/-- **The annihilation half, in one line**: `FinDepOffRows S` gives `FinDepOffRow κ` for every
`κ ∈ S`, hence `E_κ` fixes `g` and `Q_κ g = 0`. -/
theorem FinDepOffRows.finDepOffRow {S : Finset (d.Idx N)} {V : Type*} {g : Ω d → V}
    (h : FinDepOffRows d N S g) {κ : d.Idx N} (hκ : κ ∈ S) : FinDepOffRow d N κ g :=
  let ⟨I, hI, hg⟩ := h; ⟨I, fun c hc => hI c hc κ hκ, hg⟩

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

/-- **`E_{k}` preserves independence of every row in `S`** — the `Finset` version of
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
`RBM.Gauss.greenMinorMat`, and for `S = ∅` it is the full resolvent. -/
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
case is the first-order replacement, here iterated. -/

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

/-! ### The concrete family of iterated minors of `Z_k` -/

/-- `G^{(S)}_{kk} - m`, extended by `0` to the (never used) subsets containing `k`. -/
noncomputable def greenSetDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N)
    (S : Finset (d.Idx N)) : Ω d → ℂ :=
  fun ω => if h : k ∉ S then greenSetMat d N u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0

/-- **`Z^{(S)}_k := (1 - E_k)(G^{(S)}_{kk} - m)`**, the `S`-minor version of the fluctuation.
`S = ∅` is `RBM.Gauss.flucDiag` and `S = {κ}` is `RBM.Gauss.flucDiagMinor`. -/
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

/-! ### One step of (4.9) between consecutive iterated minors

`RBM1D/Green/Minor.lean` proves (4.9) for an arbitrary `Fintype` index, so it iterates:
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

/-! ### The interface, reduced to the iterated minors

`RBM.Gauss.applyOps_eq_applyOps_minorDiff` turns the gain — a statement about the
effect of `m` conditional fluctuations — into a statement about the `m`-fold minor difference
alone.  The conditional expectations survive only as the outer word, which costs at most
`2^m` and no longer has to *produce* anything. -/

/-! #### The same interface, graded by word length

`RBM1D/Gauss/FlucIter.lean` grades the gain by the length of the word, because the constants of
the `m`-fold minor difference grow with `m` and an ungraded statement is therefore unavailable
at `ρ ≍ Ψ`, while the `2p`-th moment expansion only ever builds words of length `≤ 2p`
(`RBM.Gauss.OpsOkOut.length_le`).  The same grading applies to the reduced interface: the
annihilation identity is an identity, so the length restriction passes straight through it. -/

/-! #### The cardinality budget on the reduced interface

A reduced interface graded only by the word length has the same defect as a gain interface
without a slot budget (`RBM1D/Gauss/FlucIter.lean`): with its index type `ι` unbudgeted it
yields `‖Z_k‖_{L^j} ≤ B` for every `j`, hence `‖Z_k‖_∞ ≤ B`, which fails at `B ≍ Ψ`.
`RBM.Gauss.MinorDiffGainUpTo'` adds the budget `#ι ≤ n`, and
`RBM.Gauss.flucGainUpTo'_of_minorDiffGainUpTo'` carries it across the annihilation identity,
which does not touch the index type.

The budget is what lets the conditionalized estimate of `RBM1D/Gauss/MinorDiffCond.lean` be
*packaged* as an interface rather than carried with its additive remainder forever: with
`#ι ≤ n` the remainder `condEnv^{#ι} P(Bad)` is dominated by `B₀^{#ι} (2Ψ)^{∑ q}` as soon as
`condEnv^n P(Bad) ≤ B₀^n (2Ψ)^{n M}`, a condition on the *measure of the exceptional set* that
`RBM.HighProb` makes true for every fixed pair of budgets. -/

/-- **The reduced gain interface**, with the word-length budget `M` and the cardinality budget
`#ι ≤ n`. -/
def MinorDiffGainUpTo' (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M n : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → d.Idx N) (L : ι → List (Bool × d.Idx N)),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ n →
      ∫ ω, ∏ i, ‖applyOps d N (L i)
          (minorDiff d N (qList (L i)) (flucDiagSet d N u z m (k i))) ω‖ ∂(P d)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- **`RBM.Gauss.FlucGainUpTo'` from `RBM.Gauss.MinorDiffGainUpTo'`.**  The rewriting step is
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

end Env

end RBM.Gauss
