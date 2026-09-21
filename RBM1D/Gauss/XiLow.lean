/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEBridge
import RBM1D.Gauss.TraceMoment

/-!
# T144(b): a polynomial lower bound on `Ξ^{(L)}_{u,m}`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.4 (5.76).

`RBM.EEBridge.stochDom_norm_eeField` (T135) is the `≺` form of `RBM.SumZeroDyn.Lemma510.EE_le`
for the concrete `E ⊗ E` of Definition 5.4.  It has two named inputs; this file produces the
second, `RBM.EEBridge.xiLowEvent`: a high-probability, `u`-uniform polynomial lower bound

`N^{-C} ≤ Ξ^{(L)}_{u,2(n+2)+2}`.

T135 recorded why this cannot be proved for an arbitrary `RBM.Sample`: `Ξ^{(L)}` is a maximum
of `|L_{σ,a}|` over loops, and its positivity is a spectral fact about `H_u`, which for
unbounded entry distributions holds only with high probability.  The Gaussian input is
therefore `RBM.Gauss.stochDom_norm_Xmat_gauss` (T109, `‖X‖ ≺ 1`, unconditional), and it is the
*only* probabilistic input used here.

## The route: sum the labels, do not maximise them

T135's sketch was "alternating-charge loop with equal labels, `tr((QQᴴ)^{m+1}) > 0`, plus
`‖X‖ ≺ 1`".  Carried out literally, that route needs `tr(M^k) ≥ λ_max(M)^k ≥ (M_{xx})^k` for
a positive semidefinite `M` — a Jensen/power-mean inequality over the spectrum of `M`, which
Mathlib does not have in a usable matrix form, and which is *not* provable by the elementary
"`(N²)_{xx} ≥ (N_{xx})²`" induction except along powers of two.

The route taken instead avoids the spectrum entirely.  Since `∑_a E_a = W⁻¹ I`
(`RBM.sum_Eblk`), summing a loop over **all** of its labels deletes every `E` and leaves a bare
resolvent trace (`RBM.Gauss.sum_gloop_ofFn`):

`∑_{a ∈ ℤ_L^m} L_{σ,a} = W^{-m} · Tr(∏_i G(σ_i))`,

so a *lower* bound on one trace of resolvents gives a lower bound on the maximum over labels,
at the cost of the harmless factor `L^m` (there are `L^m` label choices).  At the alternating
charge `σ = (+,-,+,-,…)` of length `m = 2k` the product is `(G Gᴴ)^k`, and `G` commutes with
`Gᴴ` (both are inverses of polynomials in `H`, `RBM.Gauss.commute_green`), so

`Tr((G Gᴴ)^k) = Tr(G^k (G^k)ᴴ) = ∑_{x,y} |(G^k)_{xy}|² ≥ (max_{x,y} |(G^k)_{xy}|)²`,

which is manifestly positive.  The quantitative lower bound on `max |(G^k)_{xy}|` is then pure
bookkeeping with the entrywise maximum `RBM.Gauss.entryMax`, which is submultiplicative after
one factor of the dimension (`RBM.Gauss.entryMax_mul_le`):

`card = |Tr(G^k (H-z)^k)| ≤ card² · max|G^k| · max|(H-z)^k| ≤ card · max|G^k| · (card·Θ)^k`

with `Θ` any bound on `max |(H-z)_{xy}|`, whence `max|G^k| ≥ (card·Θ)^{-k}`.  Collecting the
factors gives `RBM.Gauss.inv_le_loopMax`:

`(card² Θ)^{-2k} ≤ max_{σ,a} |L_{σ,a}|` over loops of length `2k`.

## What is random, and what is not

Everything above is deterministic and holds for **any** Hermitian `H` with `H - z` invertible;
only `Θ` is random, and only through `max_{xy}|H_{xy}| ≤ ‖H‖` (`RBM.norm_apply_le_l2_opNorm`).
For the Gaussian flow `H_u = √u X` this is `√u ‖X‖ ≤ ‖X‖`, and `‖X‖ ≺ 1` is T109.  The
standing regime supplies `|z_u| ≤ 3` and `1 ≤ W ℓ_u η_u` (the latter through
`RBM.SumZeroDyn.flow_crude`, so that the factor `(Wℓ_uη_u)^{m-1}` of `Ξ^{(L)}` only helps).

## Main results

* `RBM.Gauss.entryMax` and its arithmetic — `norm_le_entryMax`, `entryMax_mul_le`,
  `norm_trace_mul_le`, `card_mul_entryMax_pow_le`.
* `RBM.Gauss.sum_gloop_ofFn` — the label sum `∑_a L_{σ,a} = W^{-m} Tr(∏ G(σ_i))`.
* `RBM.Gauss.inv_le_loopMax` — the deterministic lower bound on `max_{σ,a}|L_{σ,a}|`.
* `RBM.Gauss.rpow_neg_le_xiL` — the same in the shape of `RBM.EEBridge.xiLowEvent`, for a
  general `RBM.Sample`, with `max_{xy}|(H_u)_{xy}| + |z_u| ≤ N` and `1 ≤ W ℓ_u η_u` as
  hypotheses.
* `RBM.Gauss.highProb_xiLowEvent` — **T144(b)**: `RBM.EEBridge.xiLowEvent` holds with high
  probability for the Gaussian flow, at `C = 6(n+3)`.

## Deviations

* The exponent `C` is not optimal and is not meant to be: `EE_le` only needs *some* polynomial
  lower bound (`RBM.StochDom.of_highProb_add_rpow_neg` quantifies over it).  The value
  produced, `C = 6(n+3)`, comes from `card ≤ N`, `Θ ≤ N`, and `loopMax ≥ (card²Θ)^{-2k}`.
* The lower bound is on the loop maximum, hence on `Ξ^{(L)}` only once `1 ≤ W ℓ_u η_u`; that
  is (2.72) through `RBM.SumZeroDyn.flow_crude`, the same input `EE_le` already uses.
* This file is **not** imported by `RBM1D.lean`, so it is outside the reach of
  `#assert_rbm_axioms`; its declarations were audited by hand (`propext`, `Classical.choice`,
  `Quot.sound` only).  Adding the import belongs to whoever next edits `RBM1D.lean`.
-/

namespace RBM.Gauss

open Matrix MeasureTheory Filter

/-! ### The entrywise maximum of a matrix -/

section EntryMax

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- `max_{x,y} |M_{xy}|`, the entrywise maximum. -/
noncomputable def entryMax (M : Matrix ι ι ℂ) : ℝ := ⨆ p : ι × ι, ‖M p.1 p.2‖

omit [DecidableEq ι] [Nonempty ι] in
theorem norm_le_entryMax (M : Matrix ι ι ℂ) (x y : ι) : ‖M x y‖ ≤ entryMax M :=
  le_ciSup (f := fun p : ι × ι => ‖M p.1 p.2‖) (Set.finite_range _).bddAbove (x, y)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem entryMax_nonneg (M : Matrix ι ι ℂ) : 0 ≤ entryMax M :=
  Real.iSup_nonneg fun _ => norm_nonneg _

omit [Fintype ι] [DecidableEq ι] in
theorem entryMax_le {M : Matrix ι ι ℂ} {C : ℝ} (h : ∀ x y, ‖M x y‖ ≤ C) : entryMax M ≤ C :=
  ciSup_le fun p => h p.1 p.2

omit [DecidableEq ι] in
/-- The entrywise maximum is attained. -/
theorem exists_eq_entryMax (M : Matrix ι ι ℂ) : ∃ p : ι × ι, entryMax M = ‖M p.1 p.2‖ := by
  obtain ⟨p, hp⟩ := Finite.exists_max (fun p : ι × ι => ‖M p.1 p.2‖)
  exact ⟨p, le_antisymm (ciSup_le hp) (norm_le_entryMax M p.1 p.2)⟩

omit [DecidableEq ι] in
/-- **The entrywise maximum is submultiplicative up to one factor of the dimension.** -/
theorem entryMax_mul_le (A B : Matrix ι ι ℂ) :
    entryMax (A * B) ≤ (Fintype.card ι : ℝ) * entryMax A * entryMax B := by
  refine entryMax_le fun x y => ?_
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ r ∈ (Finset.univ : Finset ι), ‖A x r * B r y‖ ≤ entryMax A * entryMax B := by
    intro r _
    rw [norm_mul]
    exact mul_le_mul (norm_le_entryMax A x r) (norm_le_entryMax B r y) (norm_nonneg _)
      (entryMax_nonneg A)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

omit [DecidableEq ι] in
/-- `|Tr(A B)| ≤ card² · max|A| · max|B|`. -/
theorem norm_trace_mul_le (A B : Matrix ι ι ℂ) :
    ‖Matrix.trace (A * B)‖ ≤ (Fintype.card ι : ℝ) ^ 2 * entryMax A * entryMax B := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x ∈ (Finset.univ : Finset ι),
      ‖(A * B).diag x‖ ≤ (Fintype.card ι : ℝ) * entryMax A * entryMax B := by
    intro x _
    exact le_trans (norm_le_entryMax (A * B) x x) (entryMax_mul_le A B)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h0 : (0 : ℝ) ≤ entryMax A * entryMax B :=
    mul_nonneg (entryMax_nonneg A) (entryMax_nonneg B)
  have hc : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg ((Fintype.card ι : ℝ))]

/-- **`card · max|M^k| ≤ (card · max|M|)^k`**, for `k ≥ 1`: the dimension-corrected entrywise
maximum is submultiplicative, hence supermultiplicative-free on powers. -/
theorem card_mul_entryMax_pow_le (M : Matrix ι ι ℂ) {k : ℕ} (hk : 1 ≤ k) :
    (Fintype.card ι : ℝ) * entryMax (M ^ k) ≤ ((Fintype.card ι : ℝ) * entryMax M) ^ k := by
  induction k with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    have hjle := ih hj
    have hc : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    have hMe : (0 : ℝ) ≤ entryMax M := entryMax_nonneg M
    have hstep : entryMax (M ^ (j + 1)) ≤ (Fintype.card ι : ℝ) * entryMax (M ^ j) * entryMax M := by
      rw [pow_succ]
      exact entryMax_mul_le _ _
    calc (Fintype.card ι : ℝ) * entryMax (M ^ (j + 1))
        ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * entryMax (M ^ j) * entryMax M) :=
          mul_le_mul_of_nonneg_left hstep hc
      _ = ((Fintype.card ι : ℝ) * entryMax (M ^ j)) * ((Fintype.card ι : ℝ) * entryMax M) := by
          ring
      _ ≤ ((Fintype.card ι : ℝ) * entryMax M) ^ j * ((Fintype.card ι : ℝ) * entryMax M) :=
          mul_le_mul_of_nonneg_right hjle (by positivity)
      _ = ((Fintype.card ι : ℝ) * entryMax M) ^ (j + 1) := (pow_succ _ _).symm

omit [DecidableEq ι] in
/-- `max|A - B| ≤ max|A| + max|B|`. -/
theorem entryMax_sub_le (A B : Matrix ι ι ℂ) :
    entryMax (A - B) ≤ entryMax A + entryMax B := by
  refine entryMax_le fun x y => ?_
  rw [Matrix.sub_apply]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_le_entryMax A x y) (norm_le_entryMax B x y))

omit [Fintype ι] in
/-- `max|z • 1| ≤ |z|`. -/
theorem entryMax_smul_one_le (z : ℂ) :
    entryMax (z • (1 : Matrix ι ι ℂ)) ≤ ‖z‖ := by
  refine entryMax_le fun x y => ?_
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  by_cases h : x = y
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

end EntryMax

/-! ### Summing a loop over all of its labels -/

section LabelSum

variable {L W : ℕ} [NeZero L] [NeZero W]
  {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- **Summing a loop product over all of its labels deletes every `E`.**  Because
`∑_a E_a = W⁻¹ I` (`RBM.sum_Eblk`), the `m`-fold label sum of `∏_i G(σ_i) E_{a_i}` is
`W^{-m} ∏_i G(σ_i)`.  This is `RBM.sum_gloop_head` iterated, at the level of the matrix
product rather than of its trace. -/
theorem sum_gloopProd_ofFn (σ : List Bool) :
    ∑ a : Fin σ.length → ZMod L, gloopProd L W H z ⟨σ, List.ofFn a⟩
      = (((W : ℂ)⁻¹) ^ σ.length) • (σ.map (Gsig H z)).prod := by
  induction σ with
  | nil => simp
  | cons s σ' ih =>
    show ∑ a : Fin (σ'.length + 1) → ZMod L, gloopProd L W H z ⟨s :: σ', List.ofFn a⟩
        = (((W : ℂ)⁻¹) ^ (σ'.length + 1)) • ((s :: σ').map (Gsig H z)).prod
    have key : ∀ a : Fin (σ'.length + 1) → ZMod L,
        gloopProd L W H z ⟨s :: σ', List.ofFn a⟩
          = (Gsig H z s * Eblk L W (a 0))
              * gloopProd L W H z ⟨σ', List.ofFn fun i => a i.succ⟩ := by
      intro a
      rw [show List.ofFn a = a 0 :: List.ofFn (fun i => a i.succ) from List.ofFn_succ]
      exact gloopProd_cons _ _ _ _
    have hre : ∑ a : Fin (σ'.length + 1) → ZMod L, gloopProd L W H z ⟨s :: σ', List.ofFn a⟩
        = ∑ p : ZMod L × (Fin σ'.length → ZMod L),
            (Gsig H z s * Eblk L W p.1) * gloopProd L W H z ⟨σ', List.ofFn p.2⟩ := by
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (σ'.length + 1) => ZMod L)
        (fun a => gloopProd L W H z ⟨s :: σ', List.ofFn a⟩)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [key]
      simp [Fin.consEquiv]
    rw [hre, Fintype.sum_prod_type]
    have hsplit : ∑ b : ZMod L, ∑ a' : Fin σ'.length → ZMod L,
          (Gsig H z s * Eblk L W b) * gloopProd L W H z ⟨σ', List.ofFn a'⟩
        = (∑ b : ZMod L, Gsig H z s * Eblk L W b)
            * ∑ a' : Fin σ'.length → ZMod L, gloopProd L W H z ⟨σ', List.ofFn a'⟩ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    rw [hsplit, ih, ← Finset.mul_sum, sum_Eblk L W, List.map_cons, List.prod_cons, pow_succ]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_smul]

/-- The same, traced: `∑_{a ∈ ℤ_L^m} L_{σ,a} = W^{-m} Tr(∏_i G(σ_i))`. -/
theorem sum_gloop_ofFn (σ : List Bool) :
    ∑ a : Fin σ.length → ZMod L, gloop L W H z ⟨σ, List.ofFn a⟩
      = (((W : ℂ)⁻¹) ^ σ.length) * Matrix.trace ((σ.map (Gsig H z)).prod) := by
  rw [show (∑ a : Fin σ.length → ZMod L, gloop L W H z ⟨σ, List.ofFn a⟩)
      = Matrix.trace (∑ a : Fin σ.length → ZMod L, gloopProd L W H z ⟨σ, List.ofFn a⟩) from
    (Matrix.trace_sum _ _).symm, sum_gloopProd_ofFn, Matrix.trace_smul, smul_eq_mul]

end LabelSum

/-! ### The alternating loop, and the two trace identities -/

section Alternating

/-- The alternating charge word `(+,-,+,-,…)` of length `2k`. -/
def altCharges : ℕ → List Bool
  | 0 => []
  | k + 1 => true :: false :: altCharges k

@[simp] theorem altCharges_length (k : ℕ) : (altCharges k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [altCharges, List.length_cons, List.length_cons, ih]
    omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {z : ℂ}

/-- The chain of the alternating word is `(G Gᴴ)^k`. -/
theorem prod_map_Gsig_altCharges (H : Matrix ι ι ℂ) (z : ℂ) (k : ℕ) :
    ((altCharges k).map (Gsig H z)).prod = (Gsig H z true * Gsig H z false) ^ k := by
  induction k with
  | zero => simp [altCharges]
  | succ j ih =>
    rw [altCharges, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih,
      ← mul_assoc, ← pow_succ']

/-- `H - z` and `H - w` commute: both are polynomials in `H`. -/
theorem sub_smul_comm (H : Matrix ι ι ℂ) (z w : ℂ) :
    (H - z • (1 : Matrix ι ι ℂ)) * (H - w • (1 : Matrix ι ι ℂ))
      = (H - w • (1 : Matrix ι ι ℂ)) * (H - z • (1 : Matrix ι ι ℂ)) := by
  have key : ∀ a b : ℂ, (H - a • (1 : Matrix ι ι ℂ)) * (H - b • (1 : Matrix ι ι ℂ))
      = H * H - (a • H + b • H) + (a * b) • (1 : Matrix ι ι ℂ) := by
    intro a b
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul, smul_sub, smul_smul]
    abel
  rw [key, key, add_comm (w • H) (z • H), mul_comm w z]

/-- **`G(z)` and `G(w)` commute.**  They are inverses of two commuting matrices, and
`Matrix.mul_inv_rev` needs no invertibility. -/
theorem commute_green (H : Matrix ι ι ℂ) (z w : ℂ) : Commute (green H z) (green H w) := by
  show green H z * green H w = green H w * green H z
  rw [green, green, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, sub_smul_comm]

/-- **The alternating loop is `Tr(G^k (G^k)ᴴ)`.** -/
theorem trace_alt_eq (hH : H.IsHermitian) (z : ℂ) (k : ℕ) :
    Matrix.trace ((Gsig H z true * Gsig H z false) ^ k)
      = Matrix.trace ((green H z) ^ k * ((green H z) ^ k)ᴴ) := by
  have hcomm : Commute (Gsig H z true) (Gsig H z false) := commute_green H z _
  have hGF : Gsig H z false = (Gsig H z true)ᴴ := by
    simpa using (Gsig_conjTranspose hH z true).symm
  rw [hcomm.mul_pow, hGF, ← Matrix.conjTranspose_pow]
  rfl

omit [DecidableEq ι] in
/-- `Tr(M Mᴴ) = ∑_{x,y} |M_{xy}|²`. -/
theorem trace_mul_conjTranspose (M : Matrix ι ι ℂ) :
    Matrix.trace (M * Mᴴ) = ((∑ x, ∑ y, ‖M x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj']

omit [DecidableEq ι] in
/-- `(max_{x,y}|M_{xy}|)² ≤ ∑_{x,y} |M_{xy}|²`. -/
theorem sq_entryMax_le_sum [Nonempty ι] (M : Matrix ι ι ℂ) :
    entryMax M ^ 2 ≤ ∑ x, ∑ y, ‖M x y‖ ^ 2 := by
  obtain ⟨p, hp⟩ := exists_eq_entryMax M
  rw [hp]
  calc ‖M p.1 p.2‖ ^ 2 ≤ ∑ y, ‖M p.1 y‖ ^ 2 :=
        Finset.single_le_sum (f := fun y => ‖M p.1 y‖ ^ 2)
          (fun y _ => by positivity) (Finset.mem_univ p.2)
    _ ≤ ∑ x, ∑ y, ‖M x y‖ ^ 2 :=
        Finset.single_le_sum (f := fun x => ∑ y, ‖M x y‖ ^ 2)
          (fun x _ => Finset.sum_nonneg fun y _ => by positivity) (Finset.mem_univ p.1)

/-- **`Tr(G^k (H-z)^k) = card`**: `G` and `H - z` commute and their product is `1`. -/
theorem trace_green_pow_mul_sub_pow (hz : IsUnit (H - z • (1 : Matrix ι ι ℂ)).det) (k : ℕ) :
    Matrix.trace ((green H z) ^ k * (H - z • (1 : Matrix ι ι ℂ)) ^ k)
      = (Fintype.card ι : ℂ) := by
  have hcomm : Commute (green H z) (H - z • (1 : Matrix ι ι ℂ)) := by
    show green H z * _ = _ * green H z
    rw [green_mul_self hz, self_mul_green hz]
  rw [← hcomm.mul_pow, green_mul_self hz, one_pow, Matrix.trace_one]

end Alternating

/-! ### The deterministic lower bound on the loop maximum -/

section LowerBound

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- **The lower bound `max_{σ,a}|L_{σ,a}| ≥ ((LW)²Θ)^{-2k}` on loops of length `2k`**, for any
Hermitian `H` with `H - z` invertible and any bound `Θ` on the entries of `H - z`.

Summing the alternating-charge loop over all `L^{2k}` label choices gives
`W^{-2k} Tr((G Gᴴ)^k) = W^{-2k} ∑_{x,y}|(G^k)_{xy}|²` (`RBM.Gauss.sum_gloop_ofFn`,
`RBM.Gauss.trace_alt_eq`, `RBM.Gauss.trace_mul_conjTranspose`), and
`Tr(G^k (H-z)^k) = LW` bounds `max|G^k|` from below (`RBM.Gauss.entryMax_mul_le`). -/
theorem inv_le_loopMax {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : IsUnit (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)).det)
    {k : ℕ} (hk : 1 ≤ k) {Θ : ℝ} (hΘ0 : 0 < Θ)
    (hΘ : entryMax (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) ≤ Θ) :
    ((((L : ℝ) * (W : ℝ)) ^ 2 * Θ) ^ (2 * k))⁻¹ ≤ loopMax L W H z (2 * k) := by
  classical
  have hL0 : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hW0 : (0 : ℝ) < (W : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set c : ℝ := (L : ℝ) * (W : ℝ) with hcdef
  have hc0 : (0 : ℝ) < c := mul_pos hL0 hW0
  have hcard : (Fintype.card (ZMod L × Fin W) : ℝ) = c := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin, hcdef]
    push_cast
    ring
  set Gk : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ := (green H z) ^ k with hGkdef
  set e : ℝ := entryMax Gk with hedef
  have he0 : 0 ≤ e := entryMax_nonneg _
  -- Step 1: `max |G^k| ≥ ((c Θ)^k)⁻¹`
  have hP0 : (0 : ℝ) < (c * Θ) ^ k := by positivity
  have h1 : c ≤ c ^ 2 * e * entryMax ((H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) ^ k) := by
    have hnt := norm_trace_mul_le Gk
      ((H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) ^ k)
    rw [trace_green_pow_mul_sub_pow hz k, hcard] at hnt
    rw [Complex.norm_natCast] at hnt
    rw [hcard] at hnt
    exact hnt
  have h2 : c * entryMax ((H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) ^ k)
      ≤ (c * Θ) ^ k := by
    have hstep := card_mul_entryMax_pow_le
      (H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) hk
    rw [hcard] at hstep
    refine hstep.trans (pow_le_pow_left₀ ?_ ?_ k)
    · exact mul_nonneg hc0.le (entryMax_nonneg _)
    · exact mul_le_mul_of_nonneg_left hΘ hc0.le
  have h3 : 1 ≤ e * (c * Θ) ^ k := by
    have hce : 0 ≤ c * e := mul_nonneg hc0.le he0
    have hcomb : c ≤ (c * e) * ((c * Θ) ^ k) := by
      refine le_trans h1 ?_
      calc c ^ 2 * e * entryMax ((H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) ^ k)
          = (c * e) * (c * entryMax
              ((H - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) ^ k)) := by ring
        _ ≤ (c * e) * (c * Θ) ^ k := mul_le_mul_of_nonneg_left h2 hce
    nlinarith
  have h4 : ((c * Θ) ^ (2 * k))⁻¹ ≤ e ^ 2 := by
    have hinv : ((c * Θ) ^ k)⁻¹ ≤ e := by
      rw [inv_le_iff_one_le_mul₀ hP0]
      linarith [h3]
    have hsq : (((c * Θ) ^ k)⁻¹) ^ 2 ≤ e ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hid : (((c * Θ) ^ k)⁻¹) ^ 2 = ((c * Θ) ^ (2 * k))⁻¹ := by
      rw [← inv_pow, ← pow_mul]
      ring_nf
    rwa [hid] at hsq
  -- Step 2: the label sum of the alternating loop
  have hlen : (altCharges k).length = 2 * k := altCharges_length k
  have hsum := sum_gloop_ofFn (L := L) (W := W) (H := H) (z := z) (altCharges k)
  rw [prod_map_Gsig_altCharges, trace_alt_eq hH, ← hGkdef, trace_mul_conjTranspose] at hsum
  set S : ℝ := ∑ x, ∑ y, ‖Gk x y‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hSe : e ^ 2 ≤ S := sq_entryMax_le_sum Gk
  have hbound : ‖∑ a : Fin (altCharges k).length → ZMod L,
        gloop L W H z ⟨altCharges k, List.ofFn a⟩‖
      ≤ (L : ℝ) ^ (2 * k) * loopMax L W H z (2 * k) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ a ∈ (Finset.univ : Finset (Fin (altCharges k).length → ZMod L)),
        ‖gloop L W H z ⟨altCharges k, List.ofFn a⟩‖ ≤ loopMax L W H z (2 * k) := by
      intro a _
      exact norm_gloop_le_loopMax _ hlen (by rw [List.length_ofFn, hlen])
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcf : (Fintype.card (Fin (altCharges k).length → ZMod L) : ℝ) = (L : ℝ) ^ (2 * k) := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, hlen]
      push_cast
      ring
    rw [hcf]
  rw [hsum] at hbound
  have hnorm : ‖((W : ℂ)⁻¹) ^ (altCharges k).length * ((S : ℝ) : ℂ)‖
      = ((W : ℝ)⁻¹) ^ (2 * k) * S := by
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hS0, hlen]
  rw [hnorm] at hbound
  -- Step 3: collect
  have hLpow : (0 : ℝ) < (L : ℝ) ^ (2 * k) := by positivity
  have hlow : ((L : ℝ) ^ (2 * k))⁻¹ * (((W : ℝ)⁻¹) ^ (2 * k) * S) ≤ loopMax L W H z (2 * k) := by
    rw [inv_mul_le_iff₀ hLpow]
    linarith [hbound]
  refine le_trans ?_ hlow
  have hSge : ((c * Θ) ^ (2 * k))⁻¹ ≤ S := le_trans h4 hSe
  have hfac : ((L : ℝ) ^ (2 * k))⁻¹ * ((W : ℝ)⁻¹) ^ (2 * k) = (c ^ (2 * k))⁻¹ := by
    rw [hcdef, mul_pow, ← inv_pow, mul_inv]
    ring
  have hid2' : ∀ x y : ℝ, (x ^ 2 * y) ^ (2 * k) = x ^ (2 * k) * (x * y) ^ (2 * k) := by
    intro x y; ring
  have hid2 : (c ^ 2 * Θ) ^ (2 * k) = c ^ (2 * k) * (c * Θ) ^ (2 * k) := hid2' c Θ
  have hpos1 : (0 : ℝ) < c ^ (2 * k) := by positivity
  have hpos2 : (0 : ℝ) < (c * Θ) ^ (2 * k) := by positivity
  calc ((c ^ 2 * Θ) ^ (2 * k))⁻¹ = (c ^ (2 * k))⁻¹ * ((c * Θ) ^ (2 * k))⁻¹ := by
        rw [hid2, mul_inv]
    _ ≤ (c ^ (2 * k))⁻¹ * S := by
        exact mul_le_mul_of_nonneg_left hSge (by positivity)
    _ = ((L : ℝ) ^ (2 * k))⁻¹ * (((W : ℝ)⁻¹) ^ (2 * k) * S) := by
        rw [← mul_assoc, hfac]

end LowerBound

/-! ### The bound along a flow, for a general `RBM.Sample` -/

section SampleFlow

open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- Every entry is bounded by the `ℓ² → ℓ²` operator norm. -/
theorem entryMax_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) : entryMax M ≤ ‖M‖ :=
  entryMax_le fun x y => norm_apply_le_l2_opNorm M x y

/-- **The polynomial lower bound on `Ξ^{(L)}_{u,2k}`, deterministically.**

The only hypotheses beyond the standing regime are `1 ≤ W ℓ_u η_u` (so that the factor
`(Wℓ_uη_u)^{2k-1}` of `Ξ^{(L)}` only helps) and the *entrywise* bound
`max_{xy}|(H_u)_{xy}| + |z_u| ≤ N`, which is where the randomness of `H` enters. -/
theorem rpow_neg_le_xiL (X : Sample B) {E : ℝ} {N : ℕ} {u : ℝ} {ω : Ω} {k : ℕ} (hk : 1 ≤ k)
    (hN1 : (1 : ℝ) ≤ (N : ℝ)) (hz : (zt E u).im ≠ 0)
    (hLW : (B.L N : ℝ) * (B.W N : ℝ) ≤ (N : ℝ)) (hA : 1 ≤ B.scale E N u)
    (hΘ : entryMax (X.H N u ω) + ‖zt E u‖ ≤ (N : ℝ)) :
    (((N : ℝ)) ^ (6 * k))⁻¹ ≤ X.xiL E N u ω (2 * k) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hunit : IsUnit (X.H N u ω
      - zt E u • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_sub_smul_one_of_im_ne_zero (X.hermitian N u ω) hz)
  have hent : entryMax (X.H N u ω - zt E u • (1 : Matrix (B.Idx N) (B.Idx N) ℂ)) ≤ (N : ℝ) := by
    have h1 := entryMax_sub_le (X.H N u ω) (zt E u • (1 : Matrix (B.Idx N) (B.Idx N) ℂ))
    have h2 := entryMax_smul_one_le (ι := B.Idx N) (zt E u)
    linarith
  have hmain := inv_le_loopMax (L := B.L N) (W := B.W N) (X.hermitian N u ω) hunit hk hN0 hent
  -- the crude scale bound `L W ≤ N` turns `(c²N)^{2k}` into `N^{6k}`
  have hL0 : (0 : ℝ) < (B.L N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (B.L N))
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  have hcN : ((B.L N : ℝ) * (B.W N : ℝ)) ^ 2 * (N : ℝ) ≤ ((N : ℝ)) ^ 3 := by
    have h0 : (0 : ℝ) ≤ (B.L N : ℝ) * (B.W N : ℝ) := by positivity
    nlinarith [mul_le_mul hLW hLW h0 (le_trans h0 hLW)]
  have hpow : (((B.L N : ℝ) * (B.W N : ℝ)) ^ 2 * (N : ℝ)) ^ (2 * k) ≤ ((N : ℝ) ^ 3) ^ (2 * k) :=
    pow_le_pow_left₀ (by positivity) hcN _
  have hid : ((N : ℝ) ^ 3) ^ (2 * k) = (N : ℝ) ^ (6 * k) := by
    rw [← pow_mul]
    ring_nf
  rw [hid] at hpow
  have hposc : (0 : ℝ) < (((B.L N : ℝ) * (B.W N : ℝ)) ^ 2 * (N : ℝ)) ^ (2 * k) := by positivity
  have hstep : ((N : ℝ) ^ (6 * k))⁻¹ ≤ loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) (2 * k) :=
    le_trans (inv_anti₀ hposc hpow) hmain
  -- `Ξ^{(L)} = loopMax · (W ℓ_u η_u)^{2k-1} ≥ loopMax`
  have hxi : X.xiL E N u ω (2 * k)
      = loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) (2 * k) * B.scale E N u ^ (2 * k - 1) :=
    rfl
  have hscale : (1 : ℝ) ≤ B.scale E N u ^ (2 * k - 1) := one_le_pow₀ hA
  have hlm0 : (0 : ℝ) ≤ loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) (2 * k) := loopMax_nonneg _
  rw [hxi]
  nlinarith [hstep, hscale, hlm0]

end SampleFlow

/-! ### T144(b): `RBM.EEBridge.xiLowEvent` for the Gaussian flow -/

section Gaussian

open scoped Matrix.Norms.L2Operator

/-- `max_{x,y} |(H_u)_{xy}| ≤ ‖X‖` for `0 ≤ u ≤ 1`: the flow is `√u • X`. -/
theorem entryMax_Hflow_le (d : Dims) (N : ℕ) {u : ℝ} (hu1 : u ≤ 1) (ω : Ω d) :
    entryMax (Hflow d N u ω) ≤ ‖Xmat d N ω‖ := by
  refine entryMax_le fun x y => ?_
  rw [Hflow_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u)]
  have h1 : Real.sqrt u ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hu1
  have h2 : ‖Xentry d N ω x y‖ ≤ ‖Xmat d N ω‖ := norm_apply_le_l2_opNorm _ x y
  nlinarith [norm_nonneg (Xentry d N ω x y), Real.sqrt_nonneg u, norm_nonneg (Xmat d N ω)]

/-- `|z_u| ≤ 3` on `[0,1]`. -/
theorem norm_zt_le_three {E : ℝ} (hE : |E| < 2) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖zt E u‖ ≤ 3 := by
  have hz : zt E u = ((E : ℝ) : ℂ) + (((1 - u : ℝ)) : ℂ) * mE E := by
    rw [zt]; push_cast; ring
  rw [hz]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    norm_mE hE.le, mul_one]
  have h2 : |1 - u| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  linarith [hE.le]

/-- **T144(b).**  `RBM.EEBridge.xiLowEvent` — the `u`-uniform polynomial lower bound
`N^{-C} ≤ Ξ^{(L)}_{u,2(n+2)+2}` — holds with high probability for the Gaussian flow, at
`C = 6(n+3)`.

The only probabilistic input is T109's `RBM.Gauss.stochDom_norm_Xmat_gauss` (`‖X‖ ≺ 1`,
unconditional), used at the single exponent `τ = 1/2`; everything else is the standing regime
plus (2.72), through `RBM.SumZeroDyn.flow_crude`. -/
theorem highProb_xiLowEvent (d : Dims) {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1)
    (hcond : Cond272 (band d) E s t) (n : ℕ) :
    HighProb (band d).P
      (EEBridge.xiLowEvent (sample d) E s t n ((6 * (n + 3) : ℕ) : ℝ)) := by
  have hcrude := SumZeroDyn.flow_crude (B := band d) (E := E) hE hs0 hst ht1 hcond
  refine (((stochDom_norm_Xmat_gauss d).highProb (τ := 1 / 2) (by norm_num)).mono ?_)
  filter_upwards [hcrude, (band d).dim, Filter.eventually_ge_atTop 1,
    SumZeroDyn.eventually_const_mul_rpow_le 4 (show (1 : ℝ) / 2 < 1 by norm_num)]
    with N hcr hdim hN1 hbig
  intro ω hω u
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0' : (0 : ℝ) < (N : ℝ) := by linarith
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) u.2.1
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_lt u.2.2 (ht1 N)
  -- the spectral parameter is off the real axis
  have hz : (zt E (u : ℝ)).im ≠ 0 := by
    rw [zt_im]
    have := mE_im_pos hE
    positivity
  -- the scales
  have hA : 1 ≤ (band d).scale E N (u : ℝ) := (hcr.2.2.2 u).1
  have hLW : ((band d).L N : ℝ) * ((band d).W N : ℝ) ≤ (N : ℝ) := by
    have : ((band d).W N : ℝ) * ((band d).L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
    linarith [this, mul_comm ((band d).L N : ℝ) ((band d).W N : ℝ)]
  -- the entrywise bound, from `‖X‖ ≺ 1`
  have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    simpa using hω ()
  have hr1 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hN1' (by norm_num)
  have hbig' : 4 * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) := by
    simpa using hbig
  have hΘ : entryMax ((sample d).H N (u : ℝ) ω) + ‖zt E (u : ℝ)‖ ≤ (N : ℝ) := by
    have h1 : entryMax ((sample d).H N (u : ℝ) ω) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      le_trans (entryMax_Hflow_le d N hu1.le ω) hX
    have h2 : ‖zt E (u : ℝ)‖ ≤ 3 := norm_zt_le_three hE hu0 hu1.le
    have h3 : (3 : ℝ) ≤ 3 * (N : ℝ) ^ ((1 : ℝ) / 2) := by linarith
    calc entryMax ((sample d).H N (u : ℝ) ω) + ‖zt E (u : ℝ)‖
        ≤ (N : ℝ) ^ ((1 : ℝ) / 2) + 3 * (N : ℝ) ^ ((1 : ℝ) / 2) := by linarith
      _ = 4 * (N : ℝ) ^ ((1 : ℝ) / 2) := by ring
      _ ≤ (N : ℝ) := hbig'
  have hmain := rpow_neg_le_xiL (sample d) (E := E) (N := N) (u := (u : ℝ)) (ω := ω)
    (k := n + 3) (by omega) hN1' hz hLW hA hΘ
  have hlen : 2 * (n + 3) = 2 * (n + 2) + 2 := by ring
  rw [hlen] at hmain
  have hcast : (N : ℝ) ^ (-((6 * (n + 3) : ℕ) : ℝ)) = ((N : ℝ) ^ (6 * (n + 3)))⁻¹ := by
    rw [Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast]
  rw [hcast]
  exact hmain

end Gaussian

end RBM.Gauss
