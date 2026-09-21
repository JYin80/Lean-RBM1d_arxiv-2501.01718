/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DischargeBDG
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Hierarchy.Decay

/-!
# T127: `E ⊗ E` of Definition 5.4 is the `eTens` of Lemma 5.10

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2 (5.22)–(5.23) and §5.4 (5.77), fourth line.

`RBM1D/Gauss/DischargeBDG.lean` (T74) *defines* `E ⊗ E` as `RBM.Gauss.eeTens`, and
`RBM1D/Hierarchy/Decay.lean` (T59) *bounds* an abstract `RBM.Decay.eTens`, whose gluing
`J k b b'` is a parameter standing for the `(2n+2)`-loop (5.23).  T118 found three pieces of
plumbing missing between them; this file supplies all three, and nothing else.  In particular
it defines **no** `RBM.SumZeroDyn.Hierarchy` instance and **no** `F`, `EE`, `mart` field of
one: that is T58's deliverable, and (see the warning in `Gauss/DischargeBDG.lean`)
`RBM.SumZeroDyn.Lemma510` is the only structural guard against a `duhamel` satisfied by fiat,
so it is not made easier to discharge here.

## (a) `glueLoop = gloop (J k b b')` — T74's open item, now closed

T74 left open that the glued trace `RBM.Gauss.glueLoop` of (5.23) "equals `gloop` of a
`LoopIdx` of length `2n+2`", noting it needs `L_{σ̄,a'} = conj L_{σ,a'}` up to a cyclic
reversal.  That is exactly what `RBM.Gsig_conjTranspose` (`G(σ)ᴴ = G(!σ)` at the *same*
spectral parameter — the observation T120 used in `Hierarchy/ChargeReduce.lean`) and
`RBM.Eblk_conjTranspose` give, once the reversal is made explicit on the index data:

* `RBM.EEBridge.rflip` — reverse a chain of `(charge, label)` pairs and flip its charges;
* `RBM.EEBridge.Gsig_mul_conjTranspose_prodList_mul` — `G(t) · (∏ G(σ_i)E_{a_i})ᴴ · E_c` is
  the chain product over `rflip t l c`.  **This is the missing conjugation identity**, and it
  holds for every Hermitian `M`: the second factor of `E ⊗ E` is a genuine loop, read
  backwards with flipped charges;
* `RBM.EEBridge.glueLoop_prodList`, `RBM.EEBridge.glueLoop_loopCut` — the gluing identity
  itself, `⟨E_b R_k E_a (R'_k)ᴴ⟩ = L_{J}` for the explicit `J = RBM.EEBridge.glueIdx`;
* `RBM.EEBridge.eeTens_eq_eTens` — `RBM.Gauss.eeTens = RBM.Decay.eTens` at that `J`.

The three properties `Decay.norm_eTens_le` assumes of its abstract gluing are then *proved*
for `glueIdx`: `glueIdx_wf`, `glueIdx_length` (`= 2n+2`), `mem_glueIdx` (`b` occurs) and
`anchor_mem_glueIdx` (the label `a_k`, independent of `b, b'`, occurs).

## (b) `LoopIdx` ↔ `LoopArg L (m + m)`

`RBM.Gauss.eeTens` is indexed by two `LoopIdx`; `RBM.SumZeroDyn.Hierarchy.EE` is indexed by a
charge vector `σ : Fin m → Bool` and a single doubled argument `LoopArg L (m + m)`.  The
adapter is `RBM.EEBridge.leftArg` / `RBM.EEBridge.rightArg` (the two halves that
`RBM.SumZeroDyn.QQ` and the `bdg` field already use, matching `Fin.append`) composed with
T74's `RBM.Gauss.toIdx`: `RBM.EEBridge.eeArg`.

## (c) `Band → Dims`

`RBM.Gauss.Dims` is `RBM.Band` without the measure, field for field, but no coercion existed
anywhere in the repository, so no `Gauss` result could be applied to a `Band`.
`RBM.Band.toDims` is that coercion, with `Idx`, `W`, `L` transported by `rfl`.  It is general
infrastructure: every `Gauss → Hierarchy` handoff needs it.

## What this unlocks

`RBM.EEBridge.norm_eeBand_le` is the fourth line of (5.77) for the *concrete* `E ⊗ E` of
Definition 5.4 evaluated on the flow:

`‖(E⊗E)_{u,σ,a,a'}‖ ≤ 2e·m·(K+2) · Ξ^{(L)}_{u,2m+2} · η_u⁻¹ · (Wℓ_uη_u)^{-2m} + m·W·L·δ`,

which is *literally* the control of `RBM.SumZeroDyn.Lemma510.EE_le`,
`(Wℓ_uη_u)^{-2m} η_u^{-1} Ξ^{(L)}_{u,2m+2}`, times the constant `2e·m·(K+2)` and up to the
decay error `δ`.  What remains between this and the field `EE_le` is only the passage from a
pathwise inequality to `≺` — the same wrapper as `RBM.DecayBridge.lkDecay_of_highProb`, with
`K = N^τ` and `δ = N^{-D}` — plus, of course, T58's decision to *define* `H.EE` as
`RBM.EEBridge.eeBand`.  Neither is done here, deliberately.

`RBM.EEBridge.norm_eeBand_le_of_decay` is the same bound with the decay hypothesis in the
`(u, τ, D)` form of Definition 5.8, ready for that wrapper, and
`RBM.EEBridge.norm_eeField_le` is it at `m = n + 2` — the integrand and the control of
`EE_le` verbatim, for the term `RBM.EEBridge.eeField`, which has exactly the type of the field
`RBM.SumZeroDyn.Hierarchy.EE`.

Two things are therefore still owed before `EE_le` is a theorem, and neither belongs here:

1. T58 must *define* `H.EE := RBM.EEBridge.eeField` (and with it `F`, `mart`, `duhamel`,
   `bdg`).  Nothing in this file does that, on purpose.
2. The passage from the pathwise bound to `≺` must absorb the prefactor `N^τ` **and** the
   additive decay error `m W L N^{-D}`.  The first is free; the second needs a *polynomial
   lower bound* on the control `Ξ^{(L)}_{u,2m+2} η_u⁻¹ (Wℓ_uη_u)^{-2m}`, which no file in the
   repository currently supplies (`RBM.StochDom.of_det` has no additive slack, and
   `RBM.Step1.stochDom_of_highProb` needs the bound with no prefactor at all).  This is the
   same shape as the polynomial lower bounds T123/T125 had to produce
   (`RBM.Gauss.rpow_neg_le_aprioriRhs`), and it is a genuine missing input, not bookkeeping.

**Update (T135).**  Item 2 is now settled, in the last section of this file: the general
absorption lemma is `RBM.StochDom.of_highProb_add_rpow_neg` (`RBM1D/Defs/StochDom.lean`), the
deterministic half of the polynomial lower bound is `RBM.EEBridge.rpow_neg_le_eeControl`, and
`RBM.EEBridge.stochDom_norm_eeField` is the resulting `≺` statement, *literally* the field
`EE_le` with `H.EE := RBM.EEBridge.eeField`.  What survives of item 2 is only the **random**
half of the lower bound — a lower bound on `Ξ^{(L)}_{u,2m+2}` itself — which is carried as the
named hypothesis `RBM.EEBridge.xiLowEvent`; see that section's header for why it is not
provable here.  Item 1 is untouched: `H.EE` is still not defined anywhere.

## Deviations

* `RBM.Decay.eTens` takes its gluing as a *total* function `J : ℕ → ZMod L → ZMod L → LoopIdx`
  and demands the length `2n+2` at **every** `k`, while (5.23) and `RBM.Gauss.eeTens` only use
  `1 ≤ k ≤ n`.  `RBM.EEBridge.glueJ` therefore clamps, `k ↦ min (k-1) (n-1)`; on `Icc 1 n`
  this is `k - 1` (`glueJ_of_mem_Icc`), which is what the index shift between
  `Finset.range n` and `Finset.Icc 1 n` needs.  No mathematical content.
* As in T74, the second factor of `E ⊗ E` is read as a complex conjugate rather than as the
  `σ̄`-loop (`docs/paper-deltas.md`).  Here that reading is *justified*, not merely adopted:
  `glueLoop_prodList` shows the conjugated chain is the same chain reversed with flipped
  charges, so the glued object really is a `(2n+2)`-loop with the charges of (5.23).
-/

namespace RBM

/-! ### (c) `Band → Dims` -/

namespace Band

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The `Band → Dims` coercion.**  `RBM.Gauss.Dims` is `RBM.Band` with the probability
measure removed; the fields are copied one for one.  Every transfer of a `RBM1D/Gauss/`
result to a `RBM.Band` goes through this. -/
def toDims (B : Band Ω) : Gauss.Dims where
  W := B.W
  L := B.L
  W_pos := B.W_pos
  three_le_L := B.three_le_L
  dim := B.dim
  c := B.c
  c_pos := B.c_pos
  bandwidth := B.bandwidth

@[simp] theorem toDims_W (B : Band Ω) (N : ℕ) : B.toDims.W N = B.W N := rfl

@[simp] theorem toDims_L (B : Band Ω) (N : ℕ) : B.toDims.L N = B.L N := rfl

@[simp] theorem toDims_c (B : Band Ω) : B.toDims.c = B.c := rfl

/-- The index types agree definitionally. -/
theorem toDims_Idx (B : Band Ω) (N : ℕ) : B.toDims.Idx N = B.Idx N := rfl

end Band

namespace EEBridge

open Matrix RBM.Gauss

/-! ### Loop index data as a list of `(charge, label)` pairs -/

section OfPairs

variable {L : ℕ}

/-- A list of `(charge, label)` pairs read as a `RBM.LoopIdx`. -/
def ofPairs (l : List (Bool × ZMod L)) : LoopIdx (ZMod L) := ⟨l.map Prod.fst, l.map Prod.snd⟩

@[simp] theorem ofPairs_zip (l : List (Bool × ZMod L)) :
    (ofPairs l).σ.zip (ofPairs l).a = l := by
  show (l.map Prod.fst).zip (l.map Prod.snd) = l
  rw [List.zip_map']
  simp

@[simp] theorem ofPairs_wf (l : List (Bool × ZMod L)) : (ofPairs l).WF := by
  simp [ofPairs, LoopIdx.WF]

@[simp] theorem ofPairs_length (l : List (Bool × ZMod L)) :
    (ofPairs l).length = l.length := by simp [ofPairs, LoopIdx.length]

@[simp] theorem ofPairs_a (l : List (Bool × ZMod L)) :
    (ofPairs l).a = l.map Prod.snd := rfl

/-- **Reverse a chain and flip its charges.**  `rflip t l c` is the chain obtained from `l` by
reading it backwards with every charge flipped, prefixed by the charge `t` and closed by the
label `c`.  It is the index data of the conjugate-transposed chain; see
`RBM.EEBridge.Gsig_mul_conjTranspose_prodList_mul`. -/
def rflip (t : Bool) : List (Bool × ZMod L) → ZMod L → List (Bool × ZMod L)
  | [], c => [(t, c)]
  | p :: l, c => rflip t l p.2 ++ [(!p.1, c)]

@[simp] theorem rflip_nil (t : Bool) (c : ZMod L) :
    rflip t ([] : List (Bool × ZMod L)) c = [(t, c)] := rfl

@[simp] theorem rflip_cons (t : Bool) (p : Bool × ZMod L) (l : List (Bool × ZMod L))
    (c : ZMod L) : rflip t (p :: l) c = rflip t l p.2 ++ [(!p.1, c)] := rfl

@[simp] theorem rflip_length (t : Bool) (l : List (Bool × ZMod L)) (c : ZMod L) :
    (rflip t l c).length = l.length + 1 := by
  induction l generalizing c with
  | nil => simp
  | cons p l ih => simp [ih]

end OfPairs

/-! ### Chains of `G E` factors -/

section Chain

variable {L W : ℕ} [NeZero L] {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

theorem gloop_ofPairs (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (l : List (Bool × ZMod L)) :
    gloop L W M z (ofPairs l) = Matrix.trace (prodList L W M z l) := by
  rw [gloop, gloopProd_eq_prodList, ofPairs_zip]

@[simp] theorem prodList_nil : prodList L W M z [] = 1 := rfl

@[simp] theorem prodList_cons (p : Bool × ZMod L) (l : List (Bool × ZMod L)) :
    prodList L W M z (p :: l) = Gsig M z p.1 * Eblk L W p.2 * prodList L W M z l := rfl

theorem prodList_append (l₁ l₂ : List (Bool × ZMod L)) :
    prodList L W M z (l₁ ++ l₂) = prodList L W M z l₁ * prodList L W M z l₂ := by
  induction l₁ with
  | nil => simp
  | cons p l ih => simp [ih, Matrix.mul_assoc]

/-- **The conjugate-transposed chain is a chain again**, read backwards with flipped charges:
`G(t) · (∏_i G(σ_i) E_{a_i})ᴴ · E_c = ∏ over rflip t l c`.

This is the identity T74 was missing (`L_{σ̄,a'} = conj L_{σ,a'}` up to a cyclic reversal).  It
uses only `RBM.Gsig_conjTranspose` — the charge flip does **not** move the spectral parameter —
and `RBM.Eblk_conjTranspose`. -/
theorem Gsig_mul_conjTranspose_prodList_mul (hM : M.IsHermitian) (t : Bool)
    (l : List (Bool × ZMod L)) (c : ZMod L) :
    Gsig M z t * (prodList L W M z l)ᴴ * Eblk L W c = prodList L W M z (rflip t l c) := by
  induction l generalizing c with
  | nil => simp
  | cons p l ih =>
    rw [rflip_cons, prodList_append, ← ih p.2, prodList_cons, prodList_cons,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Eblk_conjTranspose,
      Gsig_conjTranspose hM]
    simp [Matrix.mul_assoc]

/-- **The gluing identity (5.23) for two chains**: the glued trace of `RBM.Gauss.glueLoop` is a
single `(|m| + |m'| + 2)`-loop. -/
theorem glueLoop_prodList (hM : M.IsHermitian) (m m' : List (Bool × ZMod L)) (s s' : Bool)
    (a b : ZMod L) :
    glueLoop L W (prodList L W M z m * Gsig M z s) (prodList L W M z m' * Gsig M z s') a b
      = gloop L W M z (ofPairs (m ++ (s, a) :: rflip (!s') m' b)) := by
  rw [gloop_ofPairs, glueLoop, prodList_append, prodList_cons,
    Matrix.conjTranspose_mul, Gsig_conjTranspose hM,
    ← Gsig_mul_conjTranspose_prodList_mul hM (!s') m' b]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (Eblk L W b)]
  simp only [Matrix.mul_assoc]

end Chain

/-! ### The cut chain of `RBM.Gauss.loopCut` -/

section Cut

variable {L : ℕ}

/-- The `(charge, label)` pairs of a loop index. -/
def pairs (I : LoopIdx (ZMod L)) : List (Bool × ZMod L) := I.σ.zip I.a

theorem pairs_length {I : LoopIdx (ZMod L)} (hI : I.WF) : (pairs I).length = I.length := by
  have h : I.σ.length = I.a.length := hI
  simp [pairs, List.length_zip, h, LoopIdx.length]

/-- The `k`-th `(charge, label)` pair of a loop (the edge that is cut). -/
def pairAt (I : LoopIdx (ZMod L)) (k : ℕ) : Bool × ZMod L := (pairs I).getD k (true, 0)

/-- **The chain left after cutting the `k`-th `G` edge**, without its two loose `G` ends:
`(σ_k, a_k), (σ_{k+1}, a_{k+1}), …, (σ_{n-1}, a_{n-1}), (σ_0, a_0), …, (σ_{k-1}, a_{k-1})`. -/
def cutPairs (I : LoopIdx (ZMod L)) (k : ℕ) : List (Bool × ZMod L) :=
  pairAt I k :: ((pairs I).drop (k + 1) ++ (pairs I).take k)

theorem cutPairs_length {I : LoopIdx (ZMod L)} (hI : I.WF) {k : ℕ} (hk : k < I.length) :
    (cutPairs I k).length = I.length := by
  have hp := pairs_length hI
  simp only [cutPairs, List.length_cons, List.length_append, List.length_drop,
    List.length_take, hp]
  omega

theorem anchor_mem_cutPairs (I : LoopIdx (ZMod L)) (k : ℕ) :
    (pairAt I k).2 ∈ (cutPairs I k).map Prod.snd := by
  simp [cutPairs]

variable {W : ℕ} [NeZero L] {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- `RBM.Gauss.loopCut` is the chain over `cutPairs` with one loose `G` end on the right. -/
theorem loopCut_eq (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ)
    (I : LoopIdx (ZMod L)) (k : ℕ) :
    loopCut L W M z I k = prodList L W M z (cutPairs I k) * Gsig M z (pairAt I k).1 := by
  rw [loopCut, cutPairs, prodList_cons, prodList_append]
  simp only [pairAt, pairs, Matrix.mul_assoc]

end Cut

/-! ### The glued `(2n+2)`-loop of (5.23) -/

section GlueIdx

variable {L : ℕ}

/-- **The glued loop (5.23)**: cut the `k`-th `G` edge of `I` and of `I'`, reverse and flip the
second chain, and close the two new ends with `E_b` and `E_{b'}`. -/
def glueIdx (I I' : LoopIdx (ZMod L)) (k : ℕ) (b b' : ZMod L) : LoopIdx (ZMod L) :=
  ofPairs (cutPairs I k ++ ((pairAt I k).1, b) :: rflip (!(pairAt I' k).1) (cutPairs I' k) b')

theorem glueIdx_wf (I I' : LoopIdx (ZMod L)) (k : ℕ) (b b' : ZMod L) :
    (glueIdx I I' k b b').WF := ofPairs_wf _

theorem glueIdx_length {I I' : LoopIdx (ZMod L)} (hI : I.WF) (hI' : I'.WF) {n k : ℕ}
    (hn : I.length = n) (hn' : I'.length = n) (hk : k < n) (b b' : ZMod L) :
    (glueIdx I I' k b b').length = 2 * n + 2 := by
  rw [glueIdx, ofPairs_length, List.length_append, List.length_cons, rflip_length,
    cutPairs_length hI (by omega), cutPairs_length hI' (by omega), hn, hn']
  omega

theorem mem_glueIdx (I I' : LoopIdx (ZMod L)) (k : ℕ) (b b' : ZMod L) :
    b ∈ (glueIdx I I' k b b').a := by
  simp [glueIdx]

theorem anchor_mem_glueIdx (I I' : LoopIdx (ZMod L)) (k : ℕ) (b b' : ZMod L) :
    (pairAt I k).2 ∈ (glueIdx I I' k b b').a := by
  have := anchor_mem_cutPairs I k
  simp only [glueIdx, ofPairs_a, List.map_append, List.mem_append]
  exact Or.inl this

/-- **The gluing `J` of `RBM.Decay.eTens`.**  `Decay.eTens` sums over `k ∈ Icc 1 n` and demands
its gluing to be a `(2n+2)`-loop at *every* `k : ℕ`, while `RBM.Gauss.eeTens` sums over
`k ∈ range n`.  `glueJ` is `glueIdx` at `k - 1`, clamped so as to be total; on `Icc 1 n` the
clamp is inert (`glueJ_of_mem_Icc`). -/
def glueJ (I I' : LoopIdx (ZMod L)) (n k : ℕ) (b b' : ZMod L) : LoopIdx (ZMod L) :=
  glueIdx I I' (min (k - 1) (n - 1)) b b'

theorem glueJ_of_mem_Icc (I I' : LoopIdx (ZMod L)) {n k : ℕ} (hk : k ∈ Finset.Icc 1 n)
    (b b' : ZMod L) : glueJ I I' n k b b' = glueIdx I I' (k - 1) b b' := by
  rw [Finset.mem_Icc] at hk
  rw [glueJ, min_eq_left (by omega)]

end GlueIdx

/-! ### (a) `RBM.Gauss.eeTens` is `RBM.Decay.eTens` -/

section EeTens

variable {d : Gauss.Dims} {N : ℕ} {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}

/-- **The gluing identity of (5.23)**, with the two cut blocks of `RBM.Gauss.loopCut`: the
glued trace of Definition 5.4 is the `G`-loop of `RBM.EEBridge.glueIdx`. -/
theorem glueLoop_loopCut (hM : M.IsHermitian) (I I' : LoopIdx (ZMod (d.L N))) (k : ℕ)
    (b b' : ZMod (d.L N)) :
    glueLoop (d.L N) (d.W N) (loopCut (d.L N) (d.W N) M z I k)
        (loopCut (d.L N) (d.W N) M z I' k) b b'
      = gloop (d.L N) (d.W N) M z (glueIdx I I' k b b') := by
  rw [loopCut_eq, loopCut_eq, glueLoop_prodList hM, glueIdx]

/-- **(5.22) with the glued loop made explicit.** -/
theorem eeEdge_eq_sum_gloop (hM : M.IsHermitian) (I I' : LoopIdx (ZMod (d.L N))) (k : ℕ) :
    eeEdge d N z M I I' k
      = (d.W N : ℂ) * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
          SB (d.L N) b b' * gloop (d.L N) (d.W N) M z (glueIdx I I' k b b') := by
  rw [eeEdge_eq_sum_SB]
  exact congrArg _ (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
    congrArg _ (glueLoop_loopCut hM I I' k b b'))

/-- **`E ⊗ E` of Definition 5.4 is the `eTens` of Lemma 5.10**, at the gluing
`RBM.EEBridge.glueJ` and the loop function `RBM.gloop`. -/
theorem eeTens_eq_eTens (hM : M.IsHermitian) (I I' : LoopIdx (ZMod (d.L N))) :
    eeTens d N z M I I'
      = Decay.eTens (d.L N) (d.W N) (gloop (d.L N) (d.W N) M z) I.length
          (glueJ I I' I.length) := by
  have key : ∀ k ∈ Finset.Icc 1 I.length,
      (d.W N : ℂ) * ∑ b : ZMod (d.L N), ∑ b' : ZMod (d.L N),
          SB (d.L N) b b' * gloop (d.L N) (d.W N) M z (glueJ I I' I.length k b b')
        = eeEdge d N z M I I' (k - 1) := by
    intro k hk
    simp only [glueJ_of_mem_Icc I I' hk]
    exact (eeEdge_eq_sum_gloop hM I I' (k - 1)).symm
  have hshift : ∑ k ∈ Finset.Icc 1 I.length, eeEdge d N z M I I' (k - 1)
      = ∑ k ∈ Finset.range I.length, eeEdge d N z M I I' k := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [Decay.eTens, Finset.mul_sum (Finset.Icc 1 I.length), Finset.sum_congr rfl key, hshift,
    eeTens]

/-- **(5.77), fourth line, for the concrete `E ⊗ E` of Definition 5.4.**

With `Ξ^{(L)}_{2n+2} ≤ Φ` (i.e. `|L_J| ≤ Φ A^{-(2n+1)}` on loops of length `2n+2`) and `L`
having `(ℓ, δ)` decay,
`‖(E⊗E)_{σ,a,a'}‖ ≤ 2e n Φ (W(ℓ+1)/A) A^{-2n} + n W L δ`. -/
theorem norm_eeTens_le (hM : M.IsHermitian) {n : ℕ} (hn1 : 1 ≤ n)
    {I I' : LoopIdx (ZMod (d.L N))} (hI : I.WF) (hI' : I'.WF)
    (hn : I.length = n) (hn' : I'.length = n)
    {A ℓ δ Φ : ℝ} (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ)
    (hY : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length = 2 * n + 2 →
      ‖gloop (d.L N) (d.W N) M z J‖ ≤ Φ * A⁻¹ ^ (2 * n + 1))
    (hYd : Decay.LoopDecay (d.L N) (2 * n + 2) ℓ δ (gloop (d.L N) (d.W N) M z)) :
    ‖eeTens d N z M I I'‖
      ≤ 2 * Real.exp 1 * n * Φ * ((d.W N : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ (2 * n)
        + n * (d.W N : ℝ) * (d.L N : ℝ) * δ := by
  have hclamp : ∀ k : ℕ, min (k - 1) (n - 1) < n := fun k => by
    have : min (k - 1) (n - 1) ≤ n - 1 := min_le_right _ _
    omega
  rw [eeTens_eq_eTens hM, hn]
  refine Decay.norm_eTens_le (d.L N) (d.three_le_L N) (d.W N) n hA hℓ hδ
    (fun k b b' => ⟨glueIdx_wf _ _ _ _ _, glueIdx_length hI hI' hn hn' (hclamp k) b b'⟩)
    (fun k b b' => mem_glueIdx _ _ _ _ _)
    (fun k => ⟨(pairAt I (min (k - 1) (n - 1))).2, fun b b' => anchor_mem_glueIdx _ _ _ _ _⟩)
    hY hYd

end EeTens

/-! ### (b) The type adaptation `LoopIdx` ↔ `LoopArg L (m + m)` -/

section Arg

variable {L : ℕ}

/-- The first half of a doubled loop argument (the convention of `RBM.SumZeroDyn.QQ` and of the
`bdg` field, i.e. the left inverse of `Fin.append`). -/
def leftArg {n : ℕ} (c : LoopArg L (n + n)) : LoopArg L n := fun i => c (Fin.castAdd n i)

/-- The second half of a doubled loop argument. -/
def rightArg {n : ℕ} (c : LoopArg L (n + n)) : LoopArg L n := fun i => c (Fin.natAdd n i)

@[simp] theorem leftArg_append {n : ℕ} (a a' : LoopArg L n) : leftArg (Fin.append a a') = a := by
  funext i; rw [leftArg, Fin.append_left]

@[simp] theorem rightArg_append {n : ℕ} (a a' : LoopArg L n) :
    rightArg (Fin.append a a') = a' := by
  funext i; rw [rightArg, Fin.append_right]

end Arg

section EeArg

/-- **`E ⊗ E` in the shape of `RBM.SumZeroDyn.Hierarchy.EE`**: a charge vector `σ : Fin n → Bool`
and a single doubled argument `LoopArg L (n + n)`, the two halves being the labels `a`, `a'` of
the two factors of Definition 5.4.  The charges of the second factor are again `σ`; it is read
as the complex conjugate (T74's convention, `docs/paper-deltas.md`), which
`RBM.EEBridge.glueLoop_prodList` shows is the `σ`-loop reversed with flipped charges. -/
noncomputable def eeArg (d : Gauss.Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {n : ℕ} (σ : Fin n → Bool) (c : LoopArg (d.L N) (n + n)) : ℂ :=
  eeTens d N z M (toIdx σ (leftArg c)) (toIdx σ (rightArg c))

theorem eeArg_append (d : Gauss.Dims) (N : ℕ) (z : ℂ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    {n : ℕ} (σ : Fin n → Bool) (a a' : LoopArg (d.L N) n) :
    eeArg d N z M σ (Fin.append a a') = eeTens d N z M (toIdx σ a) (toIdx σ a') := by
  rw [eeArg, leftArg_append, rightArg_append]

/-- (5.77), fourth line, in the `LoopArg` shape. -/
theorem norm_eeArg_le {d : Gauss.Dims} {N : ℕ} {z : ℂ} {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) {n : ℕ} (hn1 : 1 ≤ n) (σ : Fin n → Bool)
    (c : LoopArg (d.L N) (n + n)) {A ℓ δ Φ : ℝ} (hA : 1 ≤ A) (hℓ : 0 < ℓ) (hδ : 0 ≤ δ)
    (hY : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length = 2 * n + 2 →
      ‖gloop (d.L N) (d.W N) M z J‖ ≤ Φ * A⁻¹ ^ (2 * n + 1))
    (hYd : Decay.LoopDecay (d.L N) (2 * n + 2) ℓ δ (gloop (d.L N) (d.W N) M z)) :
    ‖eeArg d N z M σ c‖
      ≤ 2 * Real.exp 1 * n * Φ * ((d.W N : ℝ) * (ℓ + 1) / A) * A⁻¹ ^ (2 * n)
        + n * (d.W N : ℝ) * (d.L N : ℝ) * δ :=
  norm_eeTens_le hM hn1 (toIdx_wf _ _) (toIdx_wf _ _) (toIdx_length _ _) (toIdx_length _ _)
    hA hℓ hδ hY hYd

end EeArg

/-! ### `E ⊗ E` along the flow, and (5.77) in the shape of `Lemma510.EE_le` -/

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`E ⊗ E` of Definition 5.4 evaluated on the flow** `H_u`, at the spectral parameter `z_u`.
This is the term that `RBM.SumZeroDyn.Hierarchy.EE` stands for; it is *not* installed as that
field here (T58). -/
noncomputable def eeBand (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {n : ℕ}
    (σ : Fin n → Bool) (c : LoopArg (B.L N) (n + n)) : ℂ :=
  eeArg B.toDims N (zt E u) (X.H N u ω) σ c

/-- The `G`-loops of the flow are bounded by `Ξ^{(L)}` of (5.76). -/
theorem norm_gloop_le_xiL (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {m : ℕ}
    (hA : 0 < B.scale E N u) (J : LoopIdx (ZMod (B.L N))) (hJ : J.WF) (hlen : J.length = m) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) J‖
      ≤ X.xiL E N u ω m * (B.scale E N u)⁻¹ ^ (m - 1) := by
  have hσ : J.σ.length = m := by rw [show J.σ.length = J.a.length from hJ]; exact hlen
  have h := norm_gloop_le_loopMax (L := B.L N) (W := B.W N) (H := X.H N u ω)
    (z := zt E u) J hσ hlen
  rw [Sample.xiL, loopXi, mul_assoc, ← mul_pow, mul_inv_cancel₀ hA.ne', one_pow, mul_one]
  exact h

/-- **(5.77), fourth line, for the concrete `E ⊗ E` along the flow.**

With the decay radius of Definition 5.8 written `ℓ_u K` (the paper's `ℓ_u W^τ`) and the decay
error `δ` (the paper's `O(W^{-D})`),

`‖(E⊗E)_{u,σ,a,a'}‖ ≤ 2e·m·(K+2) · Ξ^{(L)}_{u,2m+2} η_u⁻¹ (Wℓ_uη_u)^{-2m} + m·W·L·δ`.

The middle factor `Ξ^{(L)}_{u,2m+2} η_u⁻¹ (Wℓ_uη_u)^{-2m}` is *exactly* the control of
`RBM.SumZeroDyn.Lemma510.EE_le` (at `m = n + 2`); the prefactor `2e·m·(K+2)` and the error
`m W L δ` are what the passage to `≺` absorbs, with `K = N^τ` and `δ = N^{-D}`. -/
theorem norm_eeBand_le (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} {m : ℕ} (hm1 : 1 ≤ m)
    (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 ≤ δ)
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u) (hell : 1 / 2 ≤ B.ell N u)
    (hYd : Decay.LoopDecay (B.L N) (2 * m + 2) (B.ell N u * K) δ
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u))) :
    ‖eeBand X E N u ω σ c‖
      ≤ 2 * Real.exp 1 * m * (K + 2)
          * ((B.scale E N u)⁻¹ ^ (2 * m) * (etaT E u)⁻¹ * X.xiL E N u ω (2 * m + 2))
        + m * (B.W N : ℝ) * (B.L N : ℝ) * δ := by
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hell0 : (0 : ℝ) < B.ell N u := lt_of_lt_of_le (by norm_num) hell
  have hΦ0 : 0 ≤ X.xiL E N u ω (2 * m + 2) := X.xiL_nonneg hA0.le
  have hℓ0 : (0 : ℝ) < B.ell N u * K := mul_pos hell0 (lt_of_lt_of_le zero_lt_one hK)
  have hY : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length = 2 * m + 2 →
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) J‖
        ≤ X.xiL E N u ω (2 * m + 2) * (B.scale E N u)⁻¹ ^ (2 * m + 1) := by
    intro J hJ hlen
    have := norm_gloop_le_xiL X E N u ω hA0 J hJ hlen
    simpa using this
  have hbase := norm_eeArg_le (d := B.toDims) (N := N) (z := zt E u) (M := X.H N u ω)
    (X.hermitian N u ω) hm1 σ c hA hℓ0 hδ hY hYd
  refine le_trans hbase ?_
  have hscale : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
  have hkey : (B.W N : ℝ) * (B.ell N u * K + 1) / (B.scale E N u) ≤ (K + 2) / etaT E u := by
    rw [hscale]
    exact Decay.mul_add_one_div_le hW0 hell hη
  have hmono : 2 * Real.exp 1 * m * X.xiL E N u ω (2 * m + 2)
        * ((B.W N : ℝ) * (B.ell N u * K + 1) / B.scale E N u) * (B.scale E N u)⁻¹ ^ (2 * m)
      ≤ 2 * Real.exp 1 * m * X.xiL E N u ω (2 * m + 2) * ((K + 2) / etaT E u)
        * (B.scale E N u)⁻¹ ^ (2 * m) := by
    have h0 : 0 ≤ 2 * Real.exp 1 * m * X.xiL E N u ω (2 * m + 2) := by positivity
    have h1 : 0 ≤ ((B.scale E N u)⁻¹ : ℝ) ^ (2 * m) := by positivity
    gcongr
  refine add_le_add (le_trans hmono (le_of_eq ?_)) le_rfl
  rw [div_eq_mul_inv]
  ring

/-- The same bound with the paper's `(u, τ, D)` decay parameters, in the exact shape of the
control of `RBM.SumZeroDyn.Lemma510.EE_le`. -/
theorem norm_eeBand_le_of_decay (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} {m : ℕ}
    (hm1 : 1 ≤ m) (σ : Fin m → Bool) (c : LoopArg (B.L N) (m + m)) {τ D : ℝ}
    (hN : 1 ≤ (N : ℝ) ^ τ) (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u)
    (hell : 1 / 2 ≤ B.ell N u)
    (hYd : Decay.LoopDecay (B.L N) (2 * m + 2) (B.ell N u * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
      (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u))) :
    ‖eeBand X E N u ω σ c‖
      ≤ 2 * Real.exp 1 * m * ((N : ℝ) ^ τ + 2)
          * ((B.scale E N u)⁻¹ ^ (2 * m) * (etaT E u)⁻¹ * X.xiL E N u ω (2 * m + 2))
        + m * (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D) :=
  norm_eeBand_le X hm1 σ c hN (Real.rpow_nonneg (Nat.cast_nonneg N) _) hA hη hell hYd

/-! ### The shape of the field `RBM.SumZeroDyn.Hierarchy.EE`

`eeField` is a term of *exactly* the type of that field, and `norm_eeField_le` is exactly the
integrand/control pair of `RBM.SumZeroDyn.Lemma510.EE_le`, pathwise.  Nothing here installs
`eeField` as the field: that is T58's decision, and with it come `duhamel`, `bdg` and the rest
of `Lemma510`, which are the reason `Lemma510` must stay hard (see the file header). -/

/-- **The candidate for `RBM.SumZeroDyn.Hierarchy.EE` at loop length `n + 2`.**  Its type is
literally the type of that field; only the type and the bound below are asserted here. -/
noncomputable def eeField (X : Sample B) (E : ℝ) (n : ℕ) :
    ∀ N, ℝ → Ω → (Fin (n + 2) → Bool) → LoopArg (B.L N) ((n + 2) + (n + 2)) → ℂ :=
  fun N u ω σ c => eeBand X E N u ω σ c

/-- **The pathwise form of `RBM.SumZeroDyn.Lemma510.EE_le`.**  The right-hand side is the
control of that field, `(Wℓ_uη_u)^{-2(n+2)} η_u^{-1} Ξ^{(L)}_{u,2(n+2)+2}`, times `2e(n+2)`
and the decay radius `N^τ + 2`, plus the decay error.  Turning this into `≺` is the passage
that `RBM.DecayBridge.lkDecay_of_highProb` performs for Lemma 5.9; here it additionally needs
the multiplicative `N^τ` and the additive `N^{-D}` to be absorbed, i.e. a polynomial lower
bound on the control — see the file header. -/
theorem norm_eeField_le (X : Sample B) {E : ℝ} {n N : ℕ} {u : ℝ} {ω : Ω}
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2))) {τ D : ℝ}
    (hN : 1 ≤ (N : ℝ) ^ τ) (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u)
    (hell : 1 / 2 ≤ B.ell N u)
    (hYd : Decay.LoopDecay (B.L N) (2 * (n + 2) + 2) (B.ell N u * (N : ℝ) ^ τ)
      ((N : ℝ) ^ (-D)) (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u))) :
    ‖eeField X E n N u ω σ c‖
      ≤ 2 * Real.exp 1 * (n + 2) * ((N : ℝ) ^ τ + 2)
          * ((B.scale E N u)⁻¹ ^ (2 * (n + 2)) * (etaT E u)⁻¹
              * X.xiL E N u ω (2 * (n + 2) + 2))
        + (n + 2) * (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-D) := by
  have := norm_eeBand_le_of_decay X (m := n + 2) (by omega) σ c hN hA hη hell hYd
  rw [eeField]
  simpa using this

/-! ### T135: the passage from the pathwise bound to `≺`

The two things the file header lists as owed before `EE_le` is a theorem are settled here for
the **second** of them (the passage to `≺`); the first (T58's decision to *define*
`H.EE := eeField`) is still deliberately not taken, and nothing below constructs a
`RBM.SumZeroDyn.Hierarchy` or weakens `RBM.SumZeroDyn.Lemma510`.

The general tool is `RBM.StochDom.of_highProb_add_rpow_neg` (T135, `RBM1D/Defs/StochDom.lean`):
a pathwise bound `ξ ≤ N^τ ζ + N^{-D}`, holding with high probability for every `τ, D > 0`,
gives `ξ ≺ ζ` **provided** the control has a polynomial lower bound `N^{-b} ≤ ζ`, itself only
needed with high probability.

For the control `ζ = Ξ^{(L)}_{u,2m+2} η_u^{-1} (Wℓ_uη_u)^{-2m}` of `EE_le`, that lower bound
splits into a deterministic and a genuinely random half:

* the deterministic half **is** provable from the standing regime, exactly as in T123/T125's
  `RBM.Gauss.rpow_neg_le_aprioriRhs`: `ℓ_u ≤ L`, `η_u ≤ 1` and `W L ≤ N` give
  `Wℓ_uη_u ≤ N`, hence `(Wℓ_uη_u)^{-2m} ≥ N^{-2m}`, while `η_u ≤ 1` gives `η_u^{-1} ≥ 1`.
  This is `RBM.EEBridge.rpow_neg_le_eeControl`.
* the random half, a lower bound on `Ξ^{(L)}_{u,2m+2}` itself, **is not** available: `Ξ^{(L)}`
  is a maximum of `|L_{σ,a}|` over loops, and its positivity is a spectral fact
  (`Im G_{xx} ≥ η/(‖H-E‖² + η²)`) which needs a bound on `‖H‖`, and `‖H‖` has no deterministic
  bound for unbounded entry distributions.  It is therefore **carried as a named hypothesis**,
  `RBM.EEBridge.xiLowEvent`, in the weakest usable form: a *high-probability* lower bound
  `N^{-C} ≤ Ξ^{(L)}_{u,2(n+2)+2}` uniform in `u ∈ [s_N, t_N]`, for some `C`.  See
  `docs/paper-deltas.md`. -/

/-- **The pathwise input at the parameters `(τ, D)`**: at every `u ∈ [s_N, t_N]` the `G`-loops
of the flow of length `2(n+2)+2` have the `(ℓ_u N^τ, N^{-D})` decay of Definition 5.8.  This is
the shape produced by `RBM.Decay.lemma59`-style deterministic results, exactly as
`RBM.DecayBridge.LKDecayEvent` is for Lemma 5.9. -/
def eeDecayEvent (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) (τ D : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N, Decay.LoopDecay (B.L N) (2 * (n + 2) + 2)
    (B.ell N (u : ℝ) * (N : ℝ) ^ τ) ((N : ℝ) ^ (-D))
    (gloop (B.L N) (B.W N) (X.H N (u : ℝ) ω) (zt E (u : ℝ)))}

/-- **The polynomial lower bound on `Ξ^{(L)}_{u,2(n+2)+2}`**, as an event.  This is the one
input of `RBM.EEBridge.stochDom_norm_eeField` that is *not* proved: see the section header. -/
def xiLowEvent (X : Sample B) (E : ℝ) (s t : ℕ → ℝ) (n : ℕ) (C : ℝ) (N : ℕ) : Set Ω :=
  {ω | ∀ u : TimeIcc s t N, (N : ℝ) ^ (-C) ≤ X.xiL E N (u : ℝ) ω (2 * (n + 2) + 2)}

/-- The elementary facts about the scales at a time `u ∈ [s_N, t_N]` with `0 < s_N` and
`t_N < 1`: the scale is positive, `0 < η_u ≤ 1` and `1 ≤ ℓ_u ≤ L`. -/
theorem eeFacts (B : Band Ω) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (N : ℕ) (u : TimeIcc s t N) :
    0 < B.scale E N (u : ℝ) ∧ 0 < etaT E (u : ℝ) ∧ etaT E (u : ℝ) ≤ 1 ∧
      1 ≤ B.ell N (u : ℝ) ∧ B.ell N (u : ℝ) ≤ (B.L N : ℝ) := by
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) u.2.1
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 N)
  exact ⟨B.scale_pos' hE N hu0 hu1, etaT_pos hE hu1, etaT_le_one hE hu0,
    one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1, min_le_right _ _⟩

/-- **The deterministic half of the polynomial lower bound on the control of `EE_le`.**  With
`ℓ_u ≤ L`, `η_u ≤ 1` and `W L ≤ N` the scale satisfies `Wℓ_uη_u ≤ N`, so
`(Wℓ_uη_u)^{-2(n+2)} ≥ N^{-2(n+2)}`, and `η_u^{-1} ≥ 1`; a lower bound `N^{-C}` on
`Ξ^{(L)}_{u,2(n+2)+2}` therefore gives `N^{-(C + 2(n+2))}` on the whole control.

This is the same argument as `RBM.Gauss.rpow_neg_le_aprioriRhs` (T125), and the only part of
the lower bound that the standing regime supplies. -/
theorem rpow_neg_le_eeControl (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} {n : ℕ} {C : ℝ}
    (hN1 : 1 ≤ N) (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ)) (hA0 : 0 < B.scale E N u)
    (hη0 : 0 < etaT E u) (hη1 : etaT E u ≤ 1) (hellL : B.ell N u ≤ (B.L N : ℝ))
    (hxi : (N : ℝ) ^ (-C) ≤ X.xiL E N u ω (2 * (n + 2) + 2)) :
    (N : ℝ) ^ (-(C + ((2 * (n + 2) : ℕ) : ℝ)))
      ≤ (B.scale E N u)⁻¹ ^ (2 * (n + 2)) * (etaT E u)⁻¹
          * X.xiL E N u ω (2 * (n + 2) + 2) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN0' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hscN : B.scale E N u ≤ (N : ℝ) := by
    have hdef : B.scale E N u = (B.W N : ℝ) * B.ell N u * etaT E u := rfl
    rw [hdef]
    calc (B.W N : ℝ) * B.ell N u * etaT E u ≤ (B.W N : ℝ) * (B.L N : ℝ) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hellL hW0.le) hη1 hη0.le (by positivity)
      _ = (B.W N : ℝ) * (B.L N : ℝ) := mul_one _
      _ ≤ (N : ℝ) := hWL
  have hinv : (N : ℝ)⁻¹ ≤ (B.scale E N u)⁻¹ := inv_anti₀ hA0 hscN
  have hpow : ((N : ℝ)⁻¹) ^ (2 * (n + 2)) ≤ ((B.scale E N u)⁻¹) ^ (2 * (n + 2)) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have hrpow : (N : ℝ) ^ (-((2 * (n + 2) : ℕ) : ℝ)) = ((N : ℝ)⁻¹) ^ (2 * (n + 2)) := by
    rw [Real.rpow_neg hN0, Real.rpow_natCast, inv_pow]
  have hηinv : (1 : ℝ) ≤ (etaT E u)⁻¹ := by
    have hmul : etaT E u * (etaT E u)⁻¹ = 1 := mul_inv_cancel₀ hη0.ne'
    nlinarith [inv_pos.2 hη0]
  have hxi0 : (0 : ℝ) ≤ X.xiL E N u ω (2 * (n + 2) + 2) :=
    le_trans (Real.rpow_nonneg hN0 _) hxi
  have hright : (N : ℝ) ^ (-C) ≤ (etaT E u)⁻¹ * X.xiL E N u ω (2 * (n + 2) + 2) := by
    nlinarith
  have hsplit : (N : ℝ) ^ (-(C + ((2 * (n + 2) : ℕ) : ℝ)))
      = (N : ℝ) ^ (-((2 * (n + 2) : ℕ) : ℝ)) * (N : ℝ) ^ (-C) := by
    rw [← Real.rpow_add hN0']
    ring_nf
  rw [hsplit, mul_assoc]
  refine mul_le_mul ?_ hright (Real.rpow_nonneg hN0 _) (by positivity)
  rw [hrpow]
  exact hpow

/-- **The pathwise bound of `RBM.EEBridge.norm_eeField_le` with the parameters already matched
to `≺`**: the prefactor `2e(n+2)(N^{τ/2}+2)` is folded into `N^τ` (this costs `6e(n+2) ≤
N^{τ/2}`, which is eventually true), and the decay error `(n+2) W L N^{-(D+2)}` into `N^{-D}`
(this costs `n + 2 ≤ N` and `W L ≤ N`). -/
theorem norm_eeField_le_param (X : Sample B) {E : ℝ} {n N : ℕ} {u : ℝ} {ω : Ω}
    (σ : Fin (n + 2) → Bool) (c : LoopArg (B.L N) ((n + 2) + (n + 2))) {τ D : ℝ}
    (hτ : 0 < τ) (hN1 : 1 ≤ N)
    (hbig : 6 * Real.exp 1 * ((n : ℝ) + 2) ≤ (N : ℝ) ^ (τ / 2))
    (hNn : (n : ℝ) + 2 ≤ (N : ℝ)) (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ))
    (hA : 1 ≤ B.scale E N u) (hη : 0 < etaT E u) (hell : 1 / 2 ≤ B.ell N u)
    (hYd : Decay.LoopDecay (B.L N) (2 * (n + 2) + 2) (B.ell N u * (N : ℝ) ^ (τ / 2))
      ((N : ℝ) ^ (-(D + 2))) (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u))) :
    ‖eeField X E n N u ω σ c‖
      ≤ (N : ℝ) ^ τ * ((B.scale E N u)⁻¹ ^ (2 * (n + 2)) * (etaT E u)⁻¹
            * X.xiL E N u ω (2 * (n + 2) + 2))
        + (N : ℝ) ^ (-D) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN0' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hhalf : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ :=
    UnifDetDom.rpow_half_mul_rpow_half N hτ
  have hr1 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1' (half_pos hτ).le
  have hA0 : (0 : ℝ) < B.scale E N u := lt_of_lt_of_le zero_lt_one hA
  have hbase := norm_eeField_le X σ c hr1 hA hη hell hYd
  have hZ0 : (0 : ℝ) ≤ (B.scale E N u)⁻¹ ^ (2 * (n + 2)) * (etaT E u)⁻¹
      * X.xiL E N u ω (2 * (n + 2) + 2) := by
    have hxi0 := X.xiL_nonneg (E := E) (N := N) (t := u) (ω := ω)
      (m := 2 * (n + 2) + 2) hA0.le
    exact mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 hA0.le) _)
      (inv_nonneg.2 hη.le)) hxi0
  have hmul : 2 * Real.exp 1 * ((n : ℝ) + 2) * ((N : ℝ) ^ (τ / 2) + 2) ≤ (N : ℝ) ^ τ := by
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
    have h3 : (N : ℝ) ^ (τ / 2) + 2 ≤ 3 * (N : ℝ) ^ (τ / 2) := by linarith
    have hK0 : (0 : ℝ) ≤ 2 * Real.exp 1 * ((n : ℝ) + 2) := by positivity
    calc 2 * Real.exp 1 * ((n : ℝ) + 2) * ((N : ℝ) ^ (τ / 2) + 2)
        ≤ 6 * Real.exp 1 * ((n : ℝ) + 2) * (N : ℝ) ^ (τ / 2) := by
          nlinarith [mul_nonneg hK0 (sub_nonneg.2 hr1)]
      _ ≤ (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_right hbig (le_trans zero_le_one hr1)
      _ = (N : ℝ) ^ τ := hhalf
  have hadd : ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-(D + 2))
      ≤ (N : ℝ) ^ (-D) := by
    have hWL0 : (0 : ℝ) ≤ (B.W N : ℝ) * (B.L N : ℝ) := by positivity
    have hprod : ((n : ℝ) + 2) * ((B.W N : ℝ) * (B.L N : ℝ)) ≤ (N : ℝ) * (N : ℝ) :=
      mul_le_mul hNn hWL hWL0 hN0
    have hid : (N : ℝ) * (N : ℝ) * (N : ℝ) ^ (-(D + 2)) = (N : ℝ) ^ (-D) := by
      rw [show (N : ℝ) * (N : ℝ) = (N : ℝ) ^ (((2 : ℕ) : ℝ)) by
        rw [Real.rpow_natCast]; ring, ← Real.rpow_add hN0']
      norm_num
    have hrp0 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hN0 _
    calc ((n : ℝ) + 2) * (B.W N : ℝ) * (B.L N : ℝ) * (N : ℝ) ^ (-(D + 2))
        = (((n : ℝ) + 2) * ((B.W N : ℝ) * (B.L N : ℝ))) * (N : ℝ) ^ (-(D + 2)) := by ring
      _ ≤ ((N : ℝ) * (N : ℝ)) * (N : ℝ) ^ (-(D + 2)) :=
          mul_le_mul_of_nonneg_right hprod hrp0
      _ = (N : ℝ) ^ (-D) := hid
  refine hbase.trans (add_le_add ?_ hadd)
  exact mul_le_mul_of_nonneg_right hmul hZ0

/-- **(5.77), fourth line, as the `≺` statement of `RBM.SumZeroDyn.Lemma510.EE_le`.**

`‖(E⊗E)_{u,σ,a,a'}‖ ≺ Ξ^{(L)}_{u,2(n+2)+2} η_u^{-1} (Wℓ_uη_u)^{-2(n+2)}`, uniformly in
`u ∈ [s_N, t_N]` and in the loop data, for the concrete `E ⊗ E` of Definition 5.4 along the
flow (`RBM.EEBridge.eeField`).  The conclusion is *literally* the `EE_le` field with
`H.EE := eeField X E n`.

The inputs are:

* `hdec`, the `(u, τ, D)` decay of Definition 5.8 for the `G`-loops of length `2(n+2)+2`,
  with high probability at every `(τ, D)` — the analogue for `E ⊗ E` of what
  `RBM.DecayBridge.lkDecay_of_highProb` consumes for Lemma 5.9;
* the standing regime `|E| < 2`, `0 < s_N ≤ t_N < 1` and **(2.72)** (`RBM.Cond272`), which
  supply `1 ≤ W ℓ_u η_u` on `[s_N, t_N]` through `RBM.SumZeroDyn.flow_crude`;
* `hxi`, the polynomial lower bound on `Ξ^{(L)}_{u,2(n+2)+2}`, **carried, not proved**: see the
  section header and `docs/paper-deltas.md`.

Nothing here defines `H.EE`, so `RBM.SumZeroDyn.Lemma510` is not made easier to discharge:
installing `eeField` as the field still drags `duhamel` and `bdg` along with it. -/
theorem stochDom_norm_eeField (X : Sample B) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hc : Cond272 B E s t) {n : ℕ} {C : ℝ}
    (hxi : HighProb B.P (xiLowEvent X E s t n C))
    (hdec : ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), HighProb B.P (eeDecayEvent X E s t n τ D)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × ((Fin (n + 2) → Bool) × LoopArg (B.L N) ((n + 2) + (n + 2))))
          ω => ‖eeField X E n N (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun N p ω => (B.scale E N (p.1 : ℝ))⁻¹ ^ (2 * (n + 2)) * (etaT E (p.1 : ℝ))⁻¹
        * X.xiL E N (p.1 : ℝ) ω (2 * (n + 2) + 2)) := by
  have hcrude := SumZeroDyn.flow_crude (B := B) (E := E) hE hs0 hst ht1 hc
  refine StochDom.of_highProb_add_rpow_neg (b := C + ((2 * (n + 2) : ℕ) : ℝ)) ?_ ?_
  · refine HighProb.mono hxi ?_
    filter_upwards [B.dim, Filter.eventually_ge_atTop 1] with N hdim hN1
    intro ω hω p
    obtain ⟨hA0, hη0, hη1, -, hellL⟩ := eeFacts B hE hs0 ht1 N p.1
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
    exact rpow_neg_le_eeControl X hN1 hWL hA0 hη0 hη1 hellL (hω p.1)
  · intro τ hτ D hD
    refine HighProb.mono (hdec (τ / 2) (half_pos hτ) (D + 2) (by linarith)) ?_
    filter_upwards [B.dim, hcrude, Filter.eventually_ge_atTop 1,
      eventually_le_rpow (6 * Real.exp 1 * ((n : ℝ) + 2)) (half_pos hτ),
      Filter.eventually_ge_atTop (n + 2)] with N hdim hcr hN1 hbig hNn
    intro ω hω p
    obtain ⟨-, hη0, -, hell1, -⟩ := eeFacts B hE hs0 ht1 N p.1
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
    have hNn' : ((n : ℝ) + 2) ≤ (N : ℝ) := by exact_mod_cast hNn
    exact norm_eeField_le_param X p.2.1 p.2.2 hτ hN1 hbig hNn' hWL (hcr.2.2.2 p.1).1 hη0
      (by linarith) (hω p.1)

end Flow

end EEBridge

end RBM
