/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EGDef

/-!
# The drift of (5.15) at every loop length

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, (5.12)-(5.15), (5.19), (5.49) and (2.47).

`RBM1D/Hierarchy/EGDef.lean` treats the drift `F` of (5.15) at loop length `2`: there it is
`E^{(G̃)} + E^{((L-K)×(L-K))}` and nothing else.  This file is the general-length analogue: the
length-`2` identity generalizes, with exactly one further summand, the one that is empty at
length `2`:

`F_{u,σ,a} = Ẽ_{u,σ,a} + ∑_{l_K ≥ 3} [K ∼ (L-K)]^{l_K}_{u,σ,a} + E^{((L-K)×(L-K))}_{u,σ,a}`.

This is `RBM.DriftDef.driftF`, a **definition** in the Green function of the matrix; no
structure field occurs in it.

## Main results

* `RBM.DriftDef.driftF` — the drift, defined.
* `RBM.DriftDef.driftF_eq_eG_add` — `driftF` is the sum of the three objects that Lemma 5.10
  bounds.
* `RBM.DriftDef.couplingLen_eq_zero_of_lt_two`,
  `RBM.DriftDef.couplingLen_eq_zero_of_length_lt`,
  `RBM.DriftDef.sum_couplingLen_erase_two` — the coupling is carried by `2 ≤ l_K ≤ n`, so the
  `∑_{l_K ≠ 2}` of (5.15) is the paper's `∑_{l_K > 2}` and is a sum over `Finset.Icc 3 n`.
  This is what lets `RBM.Decay.norm_couplingLen_le'`, whose hypothesis is `3 ≤ l_K`, be applied
  to every summand.
* `RBM.DriftDef.eGterm_eq_eG` — `RBM.Gauss.eGterm` of (2.47) **is** `RBM.Decay.eG`, with its
  one-loop argument `X` the `(L - K)` of a one-loop and its loop argument `Y` the `G`-loop.
  Without this the third line of (5.77) (`RBM.Decay.norm_eG_le`) is a statement about a
  different object than the drift.
* `RBM.DriftDef.fastDecay_driftF` — the decay of Definition 5.8 for the drift, pathwise:
  term by term, from Lemma 5.9's decay of `K`, `L` and `L - K`.
-/

namespace RBM
namespace DriftDef

open Matrix Finset

/-! ### The coupling is carried by `2 ≤ l_K ≤ n`

`RBM.LoopIdx.cutGlueL` and `cutGlueR` produce loops of length between `2` and `I.length`
(`RBM.LoopIdx.two_le_length_cutGlueL`, `RBM.LoopIdx.length_cutGlueL_le`), so the graded
coupling `[K ∼ (L-K)]^{l_K}` vanishes outside that range.  In particular the `∑_{l_K ≠ 2}`
that (5.15) leaves over is the paper's `∑_{l_K > 2}`. -/

section Range

variable (L W : ℕ) [NeZero L]

theorem primBilLen_eq_zero_of_lt_two {lK : ℕ} (hlK : lK < 2) (K K' : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) : primBilLen L W lK K K' I = 0 := by
  rw [primBilLen]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have h2 := LoopIdx.two_le_length_cutGlueL I a hk.1 hl.1 hl.2
  rw [ite_eq_right (by omega)]

theorem primBilLenR_eq_zero_of_lt_two {lK : ℕ} (hlK : lK < 2) (F G : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) : Decay.primBilLenR L W lK F G I = 0 := by
  rw [Decay.primBilLenR]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have h2 := LoopIdx.two_le_length_cutGlueR I b hk.1 hl.1 hl.2
  rw [ite_eq_right (by omega)]

/-- **A loop of length `< 2` has no coupling at all**: cutting always leaves two loops of
length `≥ 2`. -/
theorem couplingLen_eq_zero_of_lt_two {lK : ℕ} (hlK : lK < 2) (K D : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) : Decay.couplingLen L W lK K D I = 0 := by
  rw [Decay.couplingLen, primBilLen_eq_zero_of_lt_two L W hlK K D I,
    primBilLenR_eq_zero_of_lt_two L W hlK D K I, add_zero]

theorem primBilLen_eq_zero_of_length_lt {lK : ℕ} (K K' : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hlK : I.length < lK) : primBilLen L W lK K K' I = 0 := by
  rw [primBilLen]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have h2 := LoopIdx.length_cutGlueL_le I a hk.1 hl.1 hl.2
  rw [ite_eq_right (by omega)]

theorem primBilLenR_eq_zero_of_length_lt {lK : ℕ} (F G : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hlK : I.length < lK) : Decay.primBilLenR L W lK F G I = 0 := by
  rw [Decay.primBilLenR]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl =>
    Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ioc] at hl
  have h2 := LoopIdx.length_cutGlueR_le I b hk.1 hl.1 hl.2
  rw [ite_eq_right (by omega)]

/-- **The coupling stops at `l_K = I.length`**: neither cut loop is longer than the original. -/
theorem couplingLen_eq_zero_of_length_lt {lK : ℕ} (K D : LoopIdx (ZMod L) → ℂ)
    (I : LoopIdx (ZMod L)) (hlK : I.length < lK) : Decay.couplingLen L W lK K D I = 0 := by
  rw [Decay.couplingLen, primBilLen_eq_zero_of_length_lt L W K D I hlK,
    primBilLenR_eq_zero_of_length_lt L W D K I hlK, add_zero]

/-- **The `∑_{l_K ≠ 2}` of (5.15) is the paper's `∑_{l_K > 2}`, a sum over `Icc 3 n`.**  Both
the lower and the upper truncation are theorems, not conventions: `RBM.LoopIdx.cutGlueL` and
`cutGlueR` always produce loops of length between `2` and `I.length`. -/
theorem sum_couplingLen_erase_two (K D : LoopIdx (ZMod L) → ℂ) (I : LoopIdx (ZMod L))
    {n : ℕ} (hn : I.length + 2 ≤ n) :
    ∑ lK ∈ (Finset.range n).erase 2, Decay.couplingLen L W lK K D I
      = ∑ lK ∈ Finset.Icc 3 I.length, Decay.couplingLen L W lK K D I := by
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_Icc] at hx
    exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  · intro x hx hx'
    rw [Finset.mem_erase, Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hx'
    rcases Nat.lt_or_ge x 2 with h | h
    · exact couplingLen_eq_zero_of_lt_two L W h K D I
    · exact couplingLen_eq_zero_of_length_lt L W K D I (by omega)

end Range

/-! ### (2.47) is `RBM.Decay.eG`

`RBM.Gauss.eGterm` writes the `Ẽ` term with the one-loop spelled out as a trace,
`⟨(G(σ_k) - m(σ_k)) E_a⟩`; `RBM.Decay.eG`, whose bound is the third line of (5.77), takes that
one-loop as an abstract argument `X`.  They are the same object with
`X = L - K` and `Y = L`, because `K` at a one-loop is `m(σ)` (`RBM.Kgen_one`) and
`⟨E_a⟩ = 1` (`RBM.trace_Eblk`).  Without this identification `RBM.Decay.norm_eG_le` and
`RBM.Decay.fastDecay_eG` are statements about a different function than the drift. -/

section EGBridge

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- The one-loop `(L - K)_{(s),(a)}` is the trace `⟨(G(s) - m(s)) E_a⟩` of (2.47). -/
theorem trace_sub_eq_gloop_sub_Kgen (m : Bool → ℂ) (t : ℝ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (s : Bool) (a : ZMod L) :
    Matrix.trace ((Gsig M z s - m s • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ))
        * Eblk L W a)
      = (gloop L W M z - Kgen L W m t) ⟨[s], [a]⟩ := by
  rw [Pi.sub_apply, Kgen_one, gloop, gloopProd_cons, gloopProd_nil, Matrix.mul_one,
    Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    smul_eq_mul, trace_Eblk, mul_one]

/-- **(2.47) is `RBM.Decay.eG`.**  The `X` of `RBM.Decay.eG` is the one-loop `L - K` and its
`Y` is the `G`-loop `L`; note that the `t` of `K` is immaterial, `K` at a one-loop being
`m(σ)` at every time. -/
theorem eGterm_eq_eG (m : Bool → ℂ) (t : ℝ)
    (M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (I : LoopIdx (ZMod L)) :
    Gauss.eGterm L W m M z I
      = Decay.eG L W (gloop L W M z - Kgen L W m t) (gloop L W M z) I := by
  rw [Gauss.eGterm, Decay.eG]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_)
  rw [trace_sub_eq_gloop_sub_Kgen m t M z (I.σ.getD (k - 1) true) a]

end EGBridge

/-! ### The drift, defined, and (5.15) at every loop length -/

section Drift

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The drift of (5.15) other than the `l_K = 2` term, written out.**

`Ẽ_{u,σ,a} + ∑_{l_K ≥ 3} [K ∼ (L-K)]^{l_K}_{u,σ,a} + E^{((L-K)×(L-K))}_{u,σ,a}`,

with `Ẽ` the (2.47) term (`RBM.Gauss.eGterm`, which is `RBM.Decay.eG` by
`RBM.DriftDef.eGterm_eq_eG`), `[K ∼ (L-K)]^{l_K}` the graded coupling (5.14)
(`RBM.Decay.couplingLen`) and the last summand the quadratic gluing term (5.13)/(5.49)
(`RBM.primBil` of `L - K` with itself).

Every ingredient is a definition in the Green function of `M` at `z_u`. -/
noncomputable def driftF (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) : ℂ :=
  Gauss.eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) (LoopData.idx (σ, a))
    + (∑ lK ∈ Finset.Icc 3 (n + 2),
        Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u)
          (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) (LoopData.idx (σ, a)))
    + primBil (B.L N) (B.W N)
        (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
        (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) (LoopData.idx (σ, a))

/-- The `LoopArg`-side generator `RBM.SumZeroDyn.genS` of (5.19) is the `LoopIdx`-side
`RBM.Gauss.thetaGenLoop`, at every loop length. -/
theorem genS_eq_thetaGenLoop_gen (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) :
    SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
        (MomentDuhamel.lkFun B E N u M σ) a
      = Gauss.thetaGenLoop (B.L N) (mSigma E) u
          (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) (LoopData.idx (σ, a)) := by
  have hget : ∀ (j : ℕ) (hj : j < n + 2), (List.ofFn σ).getD j true = σ ⟨j, hj⟩ := by
    intro j hj
    rw [List.getD_eq_getElem (List.ofFn σ) true (by rw [List.length_ofFn]; exact hj),
      List.getElem_ofFn]
  have hxi : (fun i : Fin (n + 2) => mSigma E ((List.ofFn σ).getD (i : ℕ) true)
        * mSigma E ((List.ofFn σ).getD (((i : ℕ) + 1) % (n + 2)) true))
      = xiOf (mSigma E) σ := by
    funext i
    have h1 : (List.ofFn σ).getD (i : ℕ) true = σ i := by
      rw [hget (i : ℕ) i.isLt]
    have h2 : (List.ofFn σ).getD (((i : ℕ) + 1) % (n + 2)) true = σ (i + 1) := by
      rw [hget _ (Nat.mod_lt _ (Nat.succ_pos _))]
      congr 1
    rw [h1, h2]
    rfl
  show SumZeroDyn.genS (B.L N) (xiOf (mSigma E) σ) ((u : ℝ) : ℂ)
      (MomentDuhamel.lkFun B E N u M σ) a = _
  rw [LoopData.idx, Gauss.thetaGenLoop_ofFn (L := B.L N) (mSigma E) u
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) (List.ofFn σ) a, hxi]
  rfl

variable {B : Band Ω} {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {n : ℕ}

end Drift

/-! ### `driftF` in the vocabulary of Lemma 5.10

Rewriting the `Ẽ` term as `RBM.Decay.eG` (`RBM.DriftDef.eGterm_eq_eG`) puts all three
summands in the vocabulary of `RBM1D/Hierarchy/Decay.lean`, where each has its bound: the
first line of (5.77) is `RBM.Decay.norm_couplingLen_le'` (whose `3 ≤ l_K` is met by every
summand of the sum), the second `RBM.Decay.norm_primBil_sub_le` and the third
`RBM.Decay.norm_eG_le`. -/

section Decomposition

variable {Ω : Type*} [MeasurableSpace Ω]

theorem Kval_eq_Kgen (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) :
    B.Kval E N u = Kgen (B.L N) (B.W N) (mSigma E) u := rfl

/-- **`driftF` is the sum of the three objects Lemma 5.10 bounds.** -/
theorem driftF_eq_eG_add (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (a : LoopArg (B.L N) (n + 2)) :
    driftF B E N u M σ a
      = Decay.eG (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) M (zt E u)) (LoopData.idx (σ, a))
        + (∑ lK ∈ Finset.Icc 3 (n + 2),
            Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) (LoopData.idx (σ, a)))
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) (LoopData.idx (σ, a)) := by
  rw [driftF, eGterm_eq_eG (mSigma E) u M (zt E u) (LoopData.idx (σ, a)), Kval_eq_Kgen]

end Decomposition

/-! ### The decay of the drift, pathwise

The `(u, τ, D)` decay of Definition 5.8 for the drift is a term-by-term consequence of
`RBM.Decay`'s three fast-decay lemmas, and needs nothing stochastic: the inputs are Lemma 5.9's
decay of `K`, of `L` and of `L - K`, plus their sup bounds.  (The `≺` form then follows by the
usual high-probability closing.) -/

section FDecay

variable {L : ℕ}

/-- A finite sum of uniformly fast-decaying tensors decays, with the budget multiplied by the
number of summands. -/
theorem fastDecay_finsetSum {ι : Type*} {m : ℕ} {R δ : ℝ} {s : Finset ι}
    {A : ι → LoopArg L m → ℂ} (h : ∀ i ∈ s, FastDecay L R δ (A i)) :
    FastDecay L R (s.card * δ) (fun a => ∑ i ∈ s, A i a) := by
  intro a ha
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ s, ‖A i a‖ ≤ ∑ _i ∈ s, δ := Finset.sum_le_sum fun i hi => h i hi a ha
    _ = s.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The drift decays** (Definition 5.8 for `F`), pathwise and deterministically.

The three summands of `RBM.DriftDef.driftF_eq_eG_add` are handled by
`RBM.Decay.fastDecay_eG`, `RBM.Decay.fastDecay_couplingLen` (the `n` summands of
`Finset.Icc 3 (n+2)`) and `RBM.Decay.fastDecay_primBil`; the first has radius `ℓ` and the
other two `2ℓ + 1`, so all three are read at the common radius `2ℓ + 1`.

The hypotheses are exactly Lemma 5.9's outputs — the `(ℓ, δ)` decay of `K`, of `L` and of
`L - K`, and their sup bounds — and nothing stochastic enters. -/
theorem fastDecay_driftF (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {n : ℕ} (σ : Fin (n + 2) → Bool)
    {ℓ δ MK MD δF : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hKd : Decay.LoopDecay (B.L N) (n + 2) ℓ δ (B.Kval E N u))
    (hDd : Decay.LoopDecay (B.L N) (n + 2) ℓ δ
      (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u))
    (hLd : Decay.LoopDecay (B.L N) (n + 3) ℓ δ (gloop (B.L N) (B.W N) M (zt E u)))
    (hK : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 → ‖B.Kval E N u J‖ ≤ MK)
    (hD : ∀ J : LoopIdx (ZMod (B.L N)), J.WF → J.length ≤ n + 2 →
      ‖(gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) J‖ ≤ MD)
    (hδF : (B.W N : ℝ) * ((n : ℝ) + 2) * ((B.L N : ℝ) * (MD * δ))
        + (n : ℝ) * (2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * (MK + MD))
        + 2 * (B.W N : ℝ) * ((n : ℝ) + 2) ^ 2 * (B.L N : ℝ) * δ * MD ≤ δF) :
    FastDecay (B.L N) (2 * ℓ + 1) δF (fun a => driftF B E N u M σ a) := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hσ : (List.ofFn σ).length = n + 2 := List.length_ofFn
  have hℓ' : ℓ ≤ 2 * ℓ + 1 := by linarith
  set D : LoopIdx (ZMod (B.L N)) → ℂ :=
    gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u with hD'
  have heG := SumZeroDyn.FastDecay.mono (B.L N) (Decay.fastDecay_eG (B.L N) (B.W N) hL3 hσ
    (fun b c => hD ⟨[b], [c]⟩ rfl (by show (1 : ℕ) ≤ n + 2; omega)) hLd) hℓ' (le_refl _)
  have hcoup := fastDecay_finsetSum (L := B.L N) (s := Finset.Icc 3 (n + 2))
    (A := fun lK (a : LoopArg (B.L N) (n + 2)) =>
      Decay.couplingLen (B.L N) (B.W N) lK (B.Kval E N u) D ⟨List.ofFn σ, List.ofFn a⟩)
    (fun lK _ =>
      Decay.fastDecay_couplingLen (B.L N) hL3 (B.W N) lK hσ hδ hMK hMD hKd hDd hK hD)
  have hquad := Decay.fastDecay_primBil (B.L N) hL3 (B.W N) hσ hδ hMD hDd hD
  have hcard : ((Finset.Icc 3 (n + 2)).card : ℝ) = (n : ℝ) := by
    rw [Nat.card_Icc]; congr 1
  rw [hcard] at hcoup
  intro a ha
  show ‖driftF B E N u M σ a‖ ≤ δF
  rw [driftF_eq_eG_add]
  simp only [LoopData.idx]
  refine le_trans ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (heG a ha) (hcoup a ha))) (hquad a ha))) ?_
  push_cast at hδF ⊢
  linarith

end FDecay


end DriftDef
end RBM
