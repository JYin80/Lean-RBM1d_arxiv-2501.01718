/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.GLoop
import RBM1D.Loop.TreeRepGeneral

/-!
# The initial condition of the flow, (2.67)

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Section 2.7, the display
before (2.67):

  `G_0(+) = m · I_{N×N}`,   `L_{0,σ,a} = K_{0,σ,a}`   for all `σ, a`.

At `t = 0` the flow starts from `H_0 = 0` and `z_0 = E + m^{(E)}` (Definition 2.7 with
`t = 0`).  Since `m (m + E) = -1`, the resolvent is `G_0(σ) = (-z_0(σ))⁻¹ I = m(σ) I`.
With `E_a E_b = δ_{ab} W⁻¹ E_a` and `Tr E_a = 1` every loop collapses to
`L_{0,σ,a} = W^{-n+1} ∏_k m(σ_k) 1(a_1 = ⋯ = a_n)`, which is the initial value of
Definition 2.12, and hence also the tree representation `Kgen` at `t = 0`.  This is the
base case of the induction of Section 2.7 and it needs no hypothesis besides `|E| ≤ 2`
(which is what makes `m^{(E)}` the root of `m (m + E) = -1`).

## Main results

* `RBM.green_zero_eq_smul` : `G(0, E + m) = m I` whenever `m (m + E) = -1`
* `RBM.Gsig_zero_zt_zero`  : **(2.67), first half**, `G_0(σ) = m(σ) I`
* `RBM.Gsig_zero_zt_zero_apply`, `RBM.Gsig_zero_zt_zero_sub` : the local law (2.64) at
  `t = 0` holds with no error
* `RBM.trace_Eblk` : `Tr E_a = 1`
* `RBM.prod_map_Eblk_cons` : `E_{a_1} ⋯ E_{a_n} = W^{-n+1} 1(a_1 = ⋯ = a_n) E_{a_1}`
* `RBM.gloop_zero_zt_zero` : `L_{0,σ,a} = W^{-n+1} ∏_k m(σ_k) 1(a_1 = ⋯ = a_n)`
* `RBM.gloop_zero_zt_zero_eq_Kgen` : **(2.67), second half**, `L_{0,σ,a} = K_{0,σ,a}`

## Deviations from the paper

* The flow `H_t` itself is not formalized (it is random); `H_0 = 0` is substituted
  directly, and `G_0(σ)` is `Gsig 0 (zt E 0) σ`.
* `L_{0,σ,a} = K_{0,σ,a}` is stated for well-formed loops of length `n ≥ 1`.  At `n = 0`
  the empty loop is `Tr I = N` in `gloop`, which the paper never considers.
* The statement "(2.68)–(2.71) hold at `t = 0` with no error" is recorded as exact
  equalities (`L_0 = K_0`, `G_0 - m = 0`); since `H_0` is deterministic, `E L_0 = L_0`
  and nothing probabilistic is needed.
-/

namespace RBM

open Matrix

section Green

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The resolvent of the zero matrix: `G(0, z) = (-z)⁻¹ I`. -/
theorem green_zero {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix n n ℂ) z = (-z)⁻¹ • (1 : Matrix n n ℂ) := by
  rw [green]
  refine Matrix.inv_eq_right_inv ?_
  rw [zero_sub, ← neg_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
    mul_inv_cancel₀ (neg_ne_zero.mpr hz), one_smul]

/-- If `m (m + E) = -1` then `G(0, E + m) = m I`: the resolvent of `H_0 = 0` at the
spectral parameter `z_0 = E + m`. -/
theorem green_zero_eq_smul {E : ℝ} {m : ℂ} (hm : m * (m + E) = -1) :
    green (0 : Matrix n n ℂ) ((E : ℂ) + m) = m • (1 : Matrix n n ℂ) := by
  have hz : (E : ℂ) + m ≠ 0 := by
    intro h
    rw [add_comm, h, mul_zero] at hm
    exact zero_ne_one (neg_eq_zero.mp hm.symm).symm
  rw [green_zero hz]
  congr 1
  have hm' : m = -((E : ℂ) + m)⁻¹ := by
    rw [eq_neg_iff_add_eq_zero, ← mul_right_inj' hz, mul_add, mul_inv_cancel₀ hz, mul_zero]
    linear_combination hm
  rw [inv_neg, ← hm']

/-- `z_0 = E + m^{(E)}` (Definition 2.7 at `t = 0`). -/
theorem zt_zero (E : ℝ) : zt E 0 = (E : ℂ) + mE E := by
  simp [zt]

/-- `z̄_0 = E + m(-)`. -/
theorem conj_zt_zero (E : ℝ) :
    (starRingEnd ℂ) (zt E 0) = (E : ℂ) + (starRingEnd ℂ) (mE E) := by
  rw [zt_zero, map_add, Complex.conj_ofReal]

/-- `m(σ) (m(σ) + E) = -1` for both charges. -/
theorem mSigma_mul {E : ℝ} (hE : |E| ≤ 2) (s : Bool) : mSigma E s * (mSigma E s + E) = -1 := by
  cases s
  · have h := congrArg (starRingEnd ℂ) (mE_mul hE)
    simpa [mSigma, map_mul, map_add, Complex.conj_ofReal] using h
  · exact mE_mul hE

/-- **(2.67), first half**: `G_0(σ) = m(σ) I`, where `G_0(σ)` is the resolvent of `H_0 = 0`
at `z_0 = E + m^{(E)}` (or its conjugate). -/
theorem Gsig_zero_zt_zero {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    Gsig (0 : Matrix n n ℂ) (zt E 0) s = mSigma E s • (1 : Matrix n n ℂ) := by
  cases s
  · rw [Gsig_false, conj_zt_zero]
    exact green_zero_eq_smul (mSigma_mul hE false)
  · rw [Gsig_true, zt_zero]
    exact green_zero_eq_smul (mSigma_mul hE true)

/-- `G_0(σ)` entrywise: `(G_0(σ))_{ij} = m(σ) δ_{ij}`. -/
theorem Gsig_zero_zt_zero_apply {E : ℝ} (hE : |E| ≤ 2) (s : Bool) (i j : n) :
    Gsig (0 : Matrix n n ℂ) (zt E 0) s i j = if i = j then mSigma E s else 0 := by
  rw [Gsig_zero_zt_zero hE, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

/-- The local law (2.64) at `t = 0` holds with no error: `G_0(+) - m = 0`. -/
theorem Gsig_zero_zt_zero_sub {E : ℝ} (hE : |E| ≤ 2) :
    Gsig (0 : Matrix n n ℂ) (zt E 0) true - mE E • (1 : Matrix n n ℂ) = 0 := by
  rw [Gsig_zero_zt_zero hE, show mSigma E true = mE E from rfl, sub_self]

end Green

section Loop

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- `Tr E_a = 1`. -/
theorem trace_Eblk (a : ZMod L) : Matrix.trace (Eblk L W a) = 1 := by
  rw [Eblk, Matrix.trace_diagonal, Fintype.sum_prod_type]
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  change ∑ x : ZMod L, ∑ _y : Fin W, (if x = a then (W : ℂ)⁻¹ else 0) = 1
  simp [hW]

omit [NeZero W] in
/-- **Products of block projections.**  From `E_a E_b = δ_{ab} W⁻¹ E_a`:
`E_b E_{a_2} ⋯ E_{a_n} = W^{-(n-1)} 1(a_2 = ⋯ = a_n = b) E_b`. -/
theorem prod_map_Eblk_cons (b : ZMod L) (a : List (ZMod L)) :
    ((b :: a).map (Eblk L W)).prod
      = if ∀ x ∈ a, x = b then ((W : ℂ)⁻¹ ^ a.length) • Eblk L W b else 0 := by
  induction a generalizing b with
  | nil => simp
  | cons c a ih =>
    rw [List.map_cons, List.prod_cons, ih c]
    by_cases hcb : c = b
    · subst hcb
      simp only [List.mem_cons, forall_eq_or_imp, true_and, List.length_cons]
      split_ifs
      · rw [Matrix.mul_smul, Eblk_mul_Eblk, ite_eq_left rfl, smul_smul, pow_succ]
      · rw [Matrix.mul_zero]
    · have hno : ¬∀ x ∈ c :: a, x = b := fun h => hcb (h c List.mem_cons_self)
      rw [ite_eq_right hno]
      split_ifs
      · rw [Matrix.mul_smul, Eblk_mul_Eblk, ite_eq_right (Ne.symm hcb), smul_zero]
      · rw [Matrix.mul_zero]

/-- The loop product at `H = 0` factorizes when every `G(σ)` is a scalar:
`∏_k G(σ_k) E_{a_k} = (∏_k m(σ_k)) · ∏_k E_{a_k}`. -/
theorem gloopProd_of_Gsig_eq_smul {z : ℂ} {m : Bool → ℂ}
    (hG : ∀ s, Gsig (0 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) z s = m s • 1)
    {σ : List Bool} {a : List (ZMod L)} (h : σ.length = a.length) :
    gloopProd L W 0 z ⟨σ, a⟩ = (σ.map m).prod • (a.map (Eblk L W)).prod := by
  induction σ generalizing a with
  | nil =>
    obtain rfl : a = [] := List.eq_nil_of_length_eq_zero h.symm
    simp
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a', a = b :: a' := by
      cases a with
      | nil => simp at h
      | cons b a => exact ⟨b, a, rfl⟩
    have h' : σ.length = a.length := by simpa using h
    rw [gloopProd_cons, ih h', hG, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    congr 1
    ring

omit [NeZero L] [NeZero W] in
/-- On a nonempty list, "all labels agree" is "all labels agree with the first one". -/
theorem forall_mem_cons_eq_iff (b : ZMod L) (a : List (ZMod L)) :
    (∀ x ∈ b :: a, ∀ y ∈ b :: a, x = y) ↔ ∀ x ∈ a, x = b := by
  constructor
  · intro h x hx
    exact h x (List.mem_cons_of_mem b hx) b List.mem_cons_self
  · intro h x hx y hy
    have hx' : x = b := by
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact h x hx
    have hy' : y = b := by
      rcases List.mem_cons.mp hy with rfl | hy
      · rfl
      · exact h y hy
    rw [hx', hy']

/-- **The loops at `t = 0`**: with `H_0 = 0` and `z_0 = E + m^{(E)}`,
`L_{0,σ,a} = W^{-n+1} ∏_k m(σ_k) 1(a_1 = ⋯ = a_n)`, i.e. the initial value `primInit` of
Definition 2.12, for every well-formed loop of length `n ≥ 1`. -/
theorem gloop_zero_zt_zero {E : ℝ} (hE : |E| ≤ 2) (I : LoopIdx (ZMod L)) (hI : I.WF)
    (h1 : 1 ≤ I.length) :
    gloop L W 0 (zt E 0) I = primInit L W (mSigma E) I := by
  obtain ⟨σ, a⟩ := I
  obtain ⟨b, a, rfl⟩ : ∃ b a', a = b :: a' := by
    cases a with
    | nil => exact absurd h1 (by simp [LoopIdx.length])
    | cons b a => exact ⟨b, a, rfl⟩
  rw [gloop, gloopProd_of_Gsig_eq_smul (fun s => Gsig_zero_zt_zero hE s) hI,
    prod_map_Eblk_cons, primInit]
  have hlen : (LoopIdx.mk σ (b :: a)).length - 1 = a.length := by
    simp [LoopIdx.length]
  rw [hlen]
  by_cases hc : ∀ x ∈ a, x = b
  · rw [ite_eq_left hc, ite_eq_left ((forall_mem_cons_eq_iff b a).2 hc), Matrix.trace_smul,
      Matrix.trace_smul, trace_Eblk, smul_eq_mul, smul_eq_mul]
    ring
  · rw [ite_eq_right hc, ite_eq_right (mt (forall_mem_cons_eq_iff b a).1 hc), smul_zero,
      Matrix.trace_zero, mul_zero]

/-- **(2.67), second half**: `L_{0,σ,a} = K_{0,σ,a}` for every well-formed loop of length
`n ≥ 1`, where `K` is the tree representation `Kgen` (the solution of Definition 2.12). -/
theorem gloop_zero_zt_zero_eq_Kgen {E : ℝ} (hE : |E| ≤ 2) (I : LoopIdx (ZMod L))
    (hI : I.WF) (h1 : 1 ≤ I.length) :
    gloop L W 0 (zt E 0) I = Kgen L W (mSigma E) 0 I := by
  rcases Nat.lt_or_ge I.length 2 with h | h
  · obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := by
      change a.length < 2 at h
      change 1 ≤ a.length at h1
      omega
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    rw [Kgen_one, gloop_zero_zt_zero hE _ hI h1, primInit]
    simp [LoopIdx.length]
  · rw [gloop_zero_zt_zero hE I hI h1, Kgen_zero W (mSigma E) I hI h]

/-- The same for any solution `K` of Definition 2.12 with `m = m(σ)`: its value at `t = 0`
is the loop at `t = 0`.  (For `n = 1` this uses the third clause of `IsPrimitive`, so
`0 ∈ T` is needed.) -/
theorem gloop_zero_zt_zero_eq_of_isPrimitive {E : ℝ} (hE : |E| ≤ 2) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W (mSigma E) T K) (hT : (0 : ℝ) ∈ T)
    (I : LoopIdx (ZMod L)) (hI : I.WF) (h1 : 1 ≤ I.length) :
    gloop L W 0 (zt E 0) I = K 0 I := by
  rcases Nat.lt_or_ge I.length 2 with h | h
  · rw [gloop_zero_zt_zero_eq_Kgen hE I hI h1]
    obtain ⟨σ, a⟩ := I
    have ha : a.length = 1 := by
      change a.length < 2 at h
      change 1 ≤ a.length at h1
      omega
    have hσ : σ.length = 1 := hI.trans ha
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 ha
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.1 hσ
    rw [Kgen_one, hK.2.2 0 hT s x]
  · rw [gloop_zero_zt_zero hE I hI h1, hK.2.1 I hI h]

end Loop

end RBM
