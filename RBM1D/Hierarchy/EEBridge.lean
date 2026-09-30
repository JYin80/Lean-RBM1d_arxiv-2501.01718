/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEBridgeArgCore
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Hierarchy.Decay

/-!
# The glued `(2n+2)`-loop of `E ⊗ E`, (5.23)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2 (5.22)–(5.23).

`RBM1D/Gauss/DischargeBDG.lean` *defines* `E ⊗ E` as `RBM.Gauss.eeTens`, and
`RBM1D/Hierarchy/Decay.lean` *bounds* an abstract `RBM.Decay.eTens`, whose gluing
`J k b b'` is a parameter standing for the `(2n+2)`-loop (5.23).  This file makes that gluing
explicit, (a)–(c) below.

## (a) `glueLoop = gloop (J k b b')`

The glued trace `RBM.Gauss.glueLoop` of (5.23) is `gloop` of a `LoopIdx` of length `2n+2`.
This needs `L_{σ̄,a'} = conj L_{σ,a'}` up to a cyclic reversal, which is what
`RBM.Gsig_conjTranspose` (`G(σ)ᴴ = G(!σ)` at the *same* spectral parameter, also used in
`Hierarchy/ChargeReduce.lean`) and `RBM.Eblk_conjTranspose` give, once the reversal is made
explicit on the index data:

* `RBM.EEBridge.rflip` — reverse a chain of `(charge, label)` pairs and flip its charges;
* `RBM.EEBridge.Gsig_mul_conjTranspose_prodList_mul` — `G(t) · (∏ G(σ_i)E_{a_i})ᴴ · E_c` is
  the chain product over `rflip t l c`.  **This is the conjugation identity**, and it
  holds for every Hermitian `M`: the second factor of `E ⊗ E` is a genuine loop, read
  backwards with flipped charges;
* `RBM.EEBridge.glueLoop_prodList`, `RBM.EEBridge.glueLoop_loopCut` — the gluing identity
  itself, `⟨E_b R_k E_a (R'_k)ᴴ⟩ = L_{J}` for the explicit `J = RBM.EEBridge.glueIdx`;
* `RBM.EEBridge.eeEdge_eq_sum_gloop` — (5.22) with the glued loop made explicit.

## (b) `LoopIdx` ↔ `LoopArg L (m + m)`

`RBM.Gauss.eeTens` is indexed by two `LoopIdx`; the sum-zero dynamics of §5.5 index `E ⊗ E` by
a charge vector `σ : Fin m → Bool` and a single doubled argument `LoopArg L (m + m)`.  The
adapter is `RBM.EEBridge.leftArg` / `RBM.EEBridge.rightArg` (the two halves that
`RBM.SumZeroDyn.QQ` uses, matching `Fin.append`) composed with `RBM.Gauss.toIdx`:
`RBM.EEBridge.eeArg`, in `RBM1D/Hierarchy/EEBridgeArgCore.lean`.

## (c) `Band → Dims`

`RBM.Gauss.Dims` is `RBM.Band` without the measure, field for field.  `RBM.Band.toDims` is the
coercion, with `Idx`, `W`, `L` transported by `rfl`; every `Gauss → Hierarchy` handoff uses it.

## Deviation

As in `RBM1D/Gauss/DischargeBDG.lean`, the second factor of `E ⊗ E` is read as a complex
conjugate rather than as the `σ̄`-loop.  The reading is justified by `glueLoop_prodList`: the
conjugated chain is the same chain reversed with flipped charges, so the glued object is a
`(2n+2)`-loop with the charges of (5.23).
-/

namespace RBM

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

This gives `L_{σ̄,a'} = conj L_{σ,a'}` up to a cyclic reversal.  It
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

end GlueIdx

/-! ### (a) The gluing identity -/

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

end EeTens

/-! ### (b) The doubled-argument adapter is re-exported from `EEBridgeArgCore`. -/

section EeArg

end EeArg

/-! ### `E ⊗ E` along the flow -/

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

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

end Flow

end EEBridge

end RBM
