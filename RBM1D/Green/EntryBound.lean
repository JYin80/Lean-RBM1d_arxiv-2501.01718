/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Green.Minor
import RBM1D.Loop.GLoop
import RBM1D.Defs.StochDom
import RBM1D.Propagator.Edges

/-!
# Lemma 4.1: entry estimates for the Green's function

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random
Band Matrices*, Lemma 4.1 (pp. 48--50): the bounds (4.2), (4.3), (4.5), through the
intermediate steps (4.10), (4.11) and the self-consistent equation for `G_{ii}`.

## Formulation

The proof of Lemma 4.1 uses two external probabilistic inputs, the large deviation bound
`[39, Lemma 3.3]` and the fluctuation averaging (4.12) `= [40, (4.11)]`, plus one Gaussian
integration by parts computation.  None of these is formalized; each enters as an **explicit
hypothesis**, never as an axiom.  The file has two layers.

* **Deterministic core.**  For one fixed matrix `H`, `G = (H - z)⁻¹`, one fixed event
  `GoodEvent G m δ` (`‖G - m‖_max ≤ δ`, the paper's `Ω(t,c)` with `δ = W^{-c}`), and the
  LDE *conclusions* for the specific vectors the paper feeds into it, with an explicit
  factor `Φ` in place of `≺` (`RBM.LDERow`, `RBM.LDECol`, `RBM.LDEQuad`), we prove
  explicit inequalities: (4.10) `RBM.norm_sq_green_le_row` (and its column form),
  (4.11) `RBM.norm_sq_green_le_two_sided`, (4.3) `RBM.norm_sq_green_diag_sub_le`, and the
  (4.5) algebra `RBM.norm_sum_coef_green_sub_le`, over an arbitrary finite index set and
  variance profile `S`.  They are then specialized to the block model `S = S^(B) ⊗ S_W`
  (`RBM.Sblk`), with the right-hand sides written as `2`-loops (`RBM.Lre`, `RBM.Lmax`):
  `RBM.norm_sq_green_le_blk` (4.2), `RBM.norm_sq_green_diag_sub_le_blk` (4.3),
  `RBM.norm_trace_green_sub_mul_Eblk_le` (4.5).  The stability
  `‖(1 - t m² S)⁻¹‖_{max→max} = O_κ(1)` is *proved* (`RBM.stable_Sblk_short_edge`) from the
  short-edge bound (3.36) on `Θ_{t m²}`.
* **Stochastic domination layer.**  For a random family `H N ω`, the hypotheses are
  `StochDom` statements (uniform in the indices) and the conclusions are `StochDom`
  statements: `RBM.entry_bound_stochDom` (4.2), `RBM.diag_bound_stochDom` (4.3),
  `RBM.avg_bound_stochDom` (4.5), and the indicator-free versions under (4.4).  The bridge
  is the general lemma `RBM.StochDom.of_det` (a deterministic implication with `Φ = N^τ`
  transfers `≺`).

## Deviations from the paper

* (4.2) is stated for `i ≠ j`.  For `i = j` the left side is `|G_{ii}|² ≈ |m|² = 1`, which is
  not bounded by the right side; the paper's `max_{i ∈ I_a, j ∈ I_b}` tacitly means `i ≠ j`.
* The right side of (4.2) comes out as `L_{(+,-),(b',a')}`, with `a' ∈ [i] + {0,±1}`,
  `b' ∈ [j] + {0,±1}`: `L_{(+,-),(a,b)} = W⁻² ∑_{p ∈ I_b, q ∈ I_a} |G_{pq}|²`
  (`RBM.gloop_two_plus_minus_blocks`), so the pair `(a',b')` of the paper is swapped.
* The LDE is used in squared form, `|∑ H X|² ≺ ∑ S |X|²`, with `S` rather than `t S` on the
  right (a weaker hypothesis).  It is assumed for the row sum of (4.8), for its column form
  (used by the paper in "iterating the process"), and for the quadratic form of (4.7).
  The paper drops `H_{ii}` from (4.7) silently; we assume `|H_{ii}|² ≺ S_{ii}`.
* `δ_N ≤ N^{-c₀}` replaces `δ = W^{-c}`: this is where `W ≥ N^c` (the paper assumes
  `W ≥ N^{1/2+c}`) is used.  `|E| ≤ 2 - κ` with `0 < κ ≤ 1` replaces `|E| < 2 - κ`.
* (4.5): the Gaussian integration by parts display of p. 50 is a hypothesis (`hIBP`), and
  (4.12) is assumed only for the two coefficient families the paper uses
  (`t_k = S_{ik}` and `t_k = W⁻¹ 1(k ∈ I_a)`), not uniformly over all admissible `t_k`.
  The conditional expectations `E_k(G_{kk} - m)` are an arbitrary family `x`.
* "(4.2), (4.3) hold without `1_Ω` under (4.4)" is proved with "`Ω(t,c)` holds with high
  probability" as the hypothesis (`RBM.StochDom.of_indicator`).
-/

namespace RBM

open Matrix Finset

section Core

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entries `G^(i)_{kl}` of the Green's function of the minor, written through the
right-hand side of (4.9) on the full index set.  For `k, l ≠ i` this is
`minorGreen G i k l` (`RBM.minorGreen_apply`). -/
noncomputable def greenMinor (G : Matrix n n ℂ) (i k l : n) : ℂ :=
  G k l - G k i * G i l / G i i

omit [Fintype n] [DecidableEq n] in
theorem minorGreen_eq_greenMinor (G : Matrix n n ℂ) (i : n) (k l : {a : n // a ≠ i}) :
    minorGreen G i k l = greenMinor G i k.1 l.1 := rfl

omit [Fintype n] [DecidableEq n] in
theorem greenMinor_sub (G : Matrix n n ℂ) (i k l : n) :
    greenMinor G i k l - G k l = -(G k i * G i l / G i i) := by
  rw [greenMinor]; ring

variable {M G : Matrix n n ℂ}

/-- Row identity from `M G = 1`, with the `i`-th term removed. -/
theorem sum_erase_mul_green (hMG : M * G = 1) (i a b : n) :
    ∑ k ∈ univ.erase i, M a k * G k b = (if a = b then (1 : ℂ) else 0) - M a i * G i b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have h := congrArg (fun X : Matrix n n ℂ => X a b) hMG
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- Column identity from `G M = 1`, with the `j`-th term removed. -/
theorem sum_erase_green_mul (hGM : G * M = 1) (j a b : n) :
    ∑ l ∈ univ.erase j, G a l * M l b = (if a = b then (1 : ℂ) else 0) - G a j * M j b := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ j)]
  have h := congrArg (fun X : Matrix n n ℂ => X a b) hGM
  simp only [Matrix.mul_apply, Matrix.one_apply] at h
  rw [h]

/-- The row sum in **(4.8)**, on the full index set. -/
theorem sum_erase_mul_greenMinor (hMG : M * G = 1) {i j : n} (hGii : G i i ≠ 0) (hij : i ≠ j) :
    ∑ k ∈ univ.erase i, M i k * greenMinor G i k j = -(G i j / G i i) := by
  have hsplit : ∑ k ∈ univ.erase i, M i k * greenMinor G i k j
      = (∑ k ∈ univ.erase i, M i k * G k j)
        - (G i j / G i i) * ∑ k ∈ univ.erase i, M i k * G k i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, sum_erase_mul_green hMG, sum_erase_mul_green hMG, ite_eq_right hij, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8)** on the full index set (with our sign, see `RBM.green_off_diag_eq`):
`G_{ij} = -G_{ii} ∑_{k ≠ i} M_{ik} G^(i)_{kj}`. -/
theorem green_eq_neg_mul_sum_row (hMG : M * G = 1) {i j : n} (hGii : G i i ≠ 0) (hij : i ≠ j) :
    G i j = -G i i * ∑ k ∈ univ.erase i, M i k * greenMinor G i k j := by
  rw [sum_erase_mul_greenMinor hMG hGii hij]
  field_simp

/-- The column analogue of the sum in (4.8). -/
theorem sum_erase_greenMinor_mul (hGM : G * M = 1) {k j : n} (hGjj : G j j ≠ 0) (hkj : k ≠ j) :
    ∑ l ∈ univ.erase j, greenMinor G j k l * M l j = -(G k j / G j j) := by
  have hsplit : ∑ l ∈ univ.erase j, greenMinor G j k l * M l j
      = (∑ l ∈ univ.erase j, G k l * M l j)
        - (G k j / G j j) * ∑ l ∈ univ.erase j, G j l * M l j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [greenMinor]; ring
  rw [hsplit, sum_erase_green_mul hGM, sum_erase_green_mul hGM, ite_eq_right hkj, ite_eq_left rfl]
  field_simp
  ring

/-- **(4.8), column form**: `G_{kj} = -G_{jj} ∑_{l ≠ j} G^(j)_{kl} M_{lj}`. -/
theorem green_eq_neg_mul_sum_col (hGM : G * M = 1) {k j : n} (hGjj : G j j ≠ 0) (hkj : k ≠ j) :
    G k j = -G j j * ∑ l ∈ univ.erase j, greenMinor G j k l * M l j := by
  rw [sum_erase_greenMinor_mul hGM hGjj hkj]
  field_simp

/-- **(4.7)** on the full index set:
`G_{ii}⁻¹ = M_{ii} - ∑_{k, l ≠ i} M_{ik} G^(i)_{kl} M_{li}`. -/
theorem inv_green_diag_eq (hGM : G * M = 1) (hMG : M * G = 1) {i : n} (hGii : G i i ≠ 0) :
    (G i i)⁻¹ = M i i - ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
      M i k * greenMinor G i k l * M l i := by
  have hinner : ∀ k ∈ univ.erase i, ∑ l ∈ univ.erase i, M i k * greenMinor G i k l * M l i
      = M i k * -(G k i / G i i) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [← sum_erase_greenMinor_mul hGM hGii hki, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
  rw [Finset.sum_congr rfl hinner]
  have hcol : ∑ k ∈ univ.erase i, M i k * G k i = 1 - M i i * G i i := by
    rw [sum_erase_mul_green hMG, ite_eq_left rfl]
  have houter : ∑ k ∈ univ.erase i, M i k * -(G k i / G i i)
      = -(1 / G i i) * (1 - M i i * G i i) := by
    rw [← hcol, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [houter]
  field_simp
  ring

/-- Off-diagonal entries of `H - z` are those of `H`: the row sum in (4.8). -/
theorem sum_erase_sub_smul_row (H G : Matrix n n ℂ) (z : ℂ) (i j : n) :
    ∑ k ∈ univ.erase i, (H - z • (1 : Matrix n n ℂ)) i k * greenMinor G i k j
      = ∑ k ∈ univ.erase i, H i k * greenMinor G i k j := by
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk).symm]

/-- Off-diagonal entries of `H - z` are those of `H`: the column sum in (4.8). -/
theorem sum_erase_sub_smul_col (H G : Matrix n n ℂ) (z : ℂ) (k j : n) :
    ∑ l ∈ univ.erase j, greenMinor G j k l * (H - z • (1 : Matrix n n ℂ)) l j
      = ∑ l ∈ univ.erase j, greenMinor G j k l * H l j := by
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl)]

/-- Off-diagonal entries of `H - z` are those of `H`: the quadratic form in (4.7). -/
theorem sum_erase_sub_smul_quad (H G : Matrix n n ℂ) (z : ℂ) (i : n) :
    ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
        (H - z • (1 : Matrix n n ℂ)) i k * greenMinor G i k l * (H - z • (1 : Matrix n n ℂ)) l i
      = ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i := by
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
  rw [sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hk).symm,
    sub_smul_one_apply_ne H z (Finset.ne_of_mem_erase hl)]

end Core

section Event

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The event `Ω(t,c)` of (4.1), for one fixed matrix: `‖G - m‖_max ≤ δ`.  The paper takes
`δ = W^{-c}`. -/
def GoodEvent (G : Matrix n n ℂ) (m : ℂ) (δ : ℝ) : Prop :=
  ∀ x y, ‖G x y - (if x = y then m else 0)‖ ≤ δ

variable {G : Matrix n n ℂ} {m : ℂ} {δ : ℝ}

omit [Fintype n] in
theorem GoodEvent.norm_offdiag_le (h : GoodEvent G m δ) {x y : n} (hxy : x ≠ y) :
    ‖G x y‖ ≤ δ := by
  simpa [hxy] using h x y

omit [Fintype n] in
theorem GoodEvent.norm_diag_sub_le (h : GoodEvent G m δ) (x : n) : ‖G x x - m‖ ≤ δ := by
  simpa using h x x

omit [Fintype n] in
theorem GoodEvent.norm_diag_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x : n) :
    ‖G x x‖ ≤ 1 + δ := by
  calc ‖G x x‖ = ‖m + (G x x - m)‖ := by rw [add_sub_cancel]
    _ ≤ ‖m‖ + ‖G x x - m‖ := norm_add_le _ _
    _ ≤ 1 + δ := by rw [hm]; linarith [h.norm_diag_sub_le x]

omit [Fintype n] in
theorem GoodEvent.one_sub_le_norm_diag (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (x : n) :
    1 - δ ≤ ‖G x x‖ := by
  have h1 : ‖m‖ ≤ ‖G x x‖ + ‖m - G x x‖ := by
    calc ‖m‖ = ‖G x x + (m - G x x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G x x‖ + ‖m - G x x‖ := norm_add_le _ _
  rw [norm_sub_rev, hm] at h1
  linarith [h.norm_diag_sub_le x]

omit [Fintype n] in
theorem GoodEvent.half_le_norm_diag (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : 1 / 2 ≤ ‖G x x‖ := by
  linarith [h.one_sub_le_norm_diag hm x]

omit [Fintype n] in
theorem GoodEvent.diag_ne_zero (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : G x x ≠ 0 := by
  intro h0
  have := h.half_le_norm_diag hm hδ x
  rw [h0, norm_zero] at this
  norm_num at this

omit [Fintype n] in
theorem GoodEvent.norm_sq_diag_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1) (hδ : δ ≤ 1 / 2)
    (x : n) : ‖G x x‖ ^ 2 ≤ 9 / 4 := by
  have h1 := h.norm_diag_le hm x
  have h0 := norm_nonneg (G x x)
  nlinarith

omit [Fintype n] in
/-- On the event, removing the `(i)` superscript costs `2 |G_{ki}| |G_{il}|`: this is (4.9). -/
theorem GoodEvent.norm_greenMinor_sub_le (h : GoodEvent G m δ) (hm : ‖m‖ = 1)
    (hδ : δ ≤ 1 / 2) (i k l : n) :
    ‖greenMinor G i k l - G k l‖ ≤ 2 * (‖G k i‖ * ‖G i l‖) := by
  rw [greenMinor_sub, norm_neg, norm_div, norm_mul]
  have h1 := h.half_le_norm_diag hm hδ i
  rw [div_le_iff₀ (by linarith)]
  have h2 : 0 ≤ ‖G k i‖ * ‖G i l‖ := by positivity
  nlinarith

end Event

section Absorb

/-- The absorption step at the end of (4.10). -/
theorem absorb_le {x Y Φ δ : ℝ} (hx : 0 ≤ x) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (h : x ≤ 9 / 4 * (Φ * (2 * Y + 8 * δ ^ 2 * x))) : x ≤ 9 * Φ * Y := by
  have h1 : 36 * Φ * δ ^ 2 * x ≤ x := by nlinarith
  nlinarith

variable {n : Type*} [Fintype n]

/-- A weighted sum of squares of perturbed quantities. -/
theorem sum_mul_sq_le_of_le_add (s : Finset n) {w a b : n → ℝ} {ε : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k, w k ≤ 1) (ha : ∀ k, 0 ≤ a k) (hab : ∀ k ∈ s, a k ≤ b k + ε) :
    ∑ k ∈ s, w k * a k ^ 2 ≤ 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 := by
  have hpt : ∀ k ∈ s, w k * a k ^ 2 ≤ w k * (2 * b k ^ 2 + 2 * ε ^ 2) := by
    intro k hk
    have h1 := hab k hk
    have h2 : a k ^ 2 ≤ 2 * b k ^ 2 + 2 * ε ^ 2 := by nlinarith [ha k, sq_nonneg (b k - ε)]
    exact mul_le_mul_of_nonneg_left h2 (hw k)
  calc ∑ k ∈ s, w k * a k ^ 2 ≤ ∑ k ∈ s, w k * (2 * b k ^ 2 + 2 * ε ^ 2) := sum_le_sum hpt
    _ ≤ ∑ k, w k * (2 * b k ^ 2 + 2 * ε ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          fun k _ _ => mul_nonneg (hw k) (by positivity)
    _ = 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 * ∑ k, w k := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 2 * ∑ k, w k * b k ^ 2 + 2 * ε ^ 2 := by
        have : 2 * ε ^ 2 * ∑ k, w k ≤ 2 * ε ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hw1 (by positivity)
        linarith

end Absorb

section EntryBound

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The large deviation input `[39, Lemma 3.3]`

We do not formalize the large deviation bound; we take its *conclusion*, for the vectors
where the paper applies it, as a hypothesis with an explicit factor `Φ` (in the stochastic
domination layer `Φ = N^τ`).  All three are stated for squared moduli, i.e.
`|∑ H X|² ≤ Φ ∑ S |X|²` is the paper's `|∑ H X| ≺ (∑ S |X|²)^{1/2}`. -/

/-- Left-hand side of the LDE for the row sum in (4.8): `|∑_{k≠i} H_{ik} G^(i)_{kj}|²`. -/
noncomputable def ldeRowLHS (H G : Matrix n n ℂ) (i j : n) : ℝ :=
  ‖∑ k ∈ univ.erase i, H i k * greenMinor G i k j‖ ^ 2

/-- Right-hand side of the LDE for the row sum in (4.8): `∑_{k≠i} S_{ik} |G^(i)_{kj}|²`. -/
noncomputable def ldeRowRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (i j : n) : ℝ :=
  ∑ k ∈ univ.erase i, S i k * ‖greenMinor G i k j‖ ^ 2

/-- Left-hand side of the LDE for the column sum: `|∑_{l≠j} G^(j)_{kl} H_{lj}|²`. -/
noncomputable def ldeColLHS (H G : Matrix n n ℂ) (k j : n) : ℝ :=
  ‖∑ l ∈ univ.erase j, greenMinor G j k l * H l j‖ ^ 2

/-- Right-hand side of the LDE for the column sum: `∑_{l≠j} |G^(j)_{kl}|² S_{lj}`. -/
noncomputable def ldeColRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (k j : n) : ℝ :=
  ∑ l ∈ univ.erase j, ‖greenMinor G j k l‖ ^ 2 * S l j

/-- Left-hand side of the LDE for the quadratic form in (4.7):
`|∑_{k,l≠i} H_{ik} G^(i)_{kl} H_{li} - t ∑_{k≠i} S_{ik} G^(i)_{kk}|²`. -/
noncomputable def ldeQuadLHS (H G : Matrix n n ℂ) (S : n → n → ℝ) (t : ℝ) (i : n) : ℝ :=
  ‖∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i
    - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k‖ ^ 2

/-- Right-hand side of the LDE for the quadratic form in (4.7):
`∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li}`. -/
noncomputable def ldeQuadRHS (S : n → n → ℝ) (G : Matrix n n ℂ) (i : n) : ℝ :=
  ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, S i k * ‖greenMinor G i k l‖ ^ 2 * S l i

/-- The row LDE, with factor `Φ`, for all `i ≠ j`. -/
def LDERow (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
  ∀ i j, i ≠ j → ldeRowLHS H G i j ≤ Φ * ldeRowRHS S G i j

/-- The column LDE, with factor `Φ`, for all `k ≠ j`. -/
def LDECol (H G : Matrix n n ℂ) (S : n → n → ℝ) (Φ : ℝ) : Prop :=
  ∀ k j, k ≠ j → ldeColLHS H G k j ≤ Φ * ldeColRHS S G k j

/-- The quadratic LDE, with factor `Φ`, for all `i`. -/
def LDEQuad (H G : Matrix n n ℂ) (S : n → n → ℝ) (t Φ : ℝ) : Prop :=
  ∀ i, ldeQuadLHS H G S t i ≤ Φ * ldeQuadRHS S G i

variable {H G : Matrix n n ℂ} {z m : ℂ} {δ Φ : ℝ} {S : n → n → ℝ}

/-- **(4.10)**: on the event `Ω`, `|G_{ij}|² ≤ 9 Φ ∑_k S_{ik} |G_{kj}|²` for `i ≠ j`. -/
theorem norm_sq_green_le_row (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ i, ∑ k, S i k ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLDE : LDERow H G S Φ) {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 9 * Φ * ∑ k, S i k * ‖G k j‖ ^ 2 := by
  have hGii := hΩ.diag_ne_zero hm hδ i
  have h48 := green_eq_neg_mul_sum_row hMG hGii hij
  rw [sum_erase_sub_smul_row] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := by
    rw [hnorm, ldeRowLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ i) (sq_nonneg _)
  have hrhs : ldeRowRHS S G i j ≤ 2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2 := by
    refine sum_mul_sq_le_of_le_add _ (hS0 i) (hS1 i) (fun _ => norm_nonneg _) ?_
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k j
    have h2 := hΩ.norm_offdiag_le hki
    have h3 : ‖greenMinor G i k j‖ ≤ ‖G k j‖ + ‖greenMinor G i k j - G k j‖ := by
      calc ‖greenMinor G i k j‖ = ‖G k j + (greenMinor G i k j - G k j)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i j‖ ≤ δ * ‖G i j‖ :=
      mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    linarith
  have hlde := hLDE i j hij
  refine absorb_le (sq_nonneg _) hΦδ ?_
  calc ‖G i j‖ ^ 2 ≤ 9 / 4 * ldeRowLHS H G i j := hsq
    _ ≤ 9 / 4 * (Φ * ldeRowRHS S G i j) := by linarith
    _ ≤ 9 / 4 * (Φ * (2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 2 * (2 * δ * ‖G i j‖) ^ 2)) := by
        gcongr
    _ = 9 / 4 * (Φ * (2 * ∑ k, S i k * ‖G k j‖ ^ 2 + 8 * δ ^ 2 * ‖G i j‖ ^ 2)) := by ring

/-- **(4.10), column form**: on the event `Ω`, `|G_{kj}|² ≤ 9 Φ ∑_l |G_{kl}|² S_{lj}` for
`k ≠ j`.  The paper uses this (the same estimate, expanded along the column) in the
iteration leading to (4.11). -/
theorem norm_sq_green_le_col (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hS1 : ∀ j, ∑ l, S l j ≤ 1) (hΦ : 0 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLDE : LDECol H G S Φ) {k j : n} (hkj : k ≠ j) :
    ‖G k j‖ ^ 2 ≤ 9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 := by
  have hGjj := hΩ.diag_ne_zero hm hδ j
  have h48 := green_eq_neg_mul_sum_col hGM hGjj hkj
  rw [sum_erase_sub_smul_col] at h48
  have hnorm := congrArg norm h48
  rw [norm_mul, norm_neg] at hnorm
  have hsq : ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := by
    rw [hnorm, ldeColLHS, mul_pow]
    exact mul_le_mul_of_nonneg_right (hΩ.norm_sq_diag_le hm hδ j) (sq_nonneg _)
  have hrhs : ldeColRHS S G k j ≤ 2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2 := by
    have hre : ldeColRHS S G k j = ∑ l ∈ univ.erase j, S l j * ‖greenMinor G j k l‖ ^ 2 := by
      rw [ldeColRHS]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hre]
    refine sum_mul_sq_le_of_le_add _ (fun l => hS0 l j) (hS1 j) (fun _ => norm_nonneg _) ?_
    intro l hl
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ j k l
    have h2 := hΩ.norm_offdiag_le hlj.symm
    have h3 : ‖greenMinor G j k l‖ ≤ ‖G k l‖ + ‖greenMinor G j k l - G k l‖ := by
      calc ‖greenMinor G j k l‖ = ‖G k l + (greenMinor G j k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k j‖ * ‖G j l‖ ≤ ‖G k j‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    linarith
  have hlde := hLDE k j hkj
  refine absorb_le (sq_nonneg _) hΦδ ?_
  calc ‖G k j‖ ^ 2 ≤ 9 / 4 * ldeColLHS H G k j := hsq
    _ ≤ 9 / 4 * (Φ * ldeColRHS S G k j) := by linarith
    _ ≤ 9 / 4 * (Φ * (2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 2 * (2 * δ * ‖G k j‖) ^ 2)) := by
        gcongr
    _ = 9 / 4 * (Φ * (2 * ∑ l, S l j * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k j‖ ^ 2)) := by ring

/-- **(4.11)**: iterating (4.10) once along the row and once along the column,
`|G_{ij}|² ≤ 81 Φ² (∑_{k,l} S_{ik} |G_{kl}|² S_{lj} + S_{ij})` for `i ≠ j`.
The term `S_{ij}` is the contribution `k = j` of the paper, where `|G_{jj}|² = O(1)`. -/
theorem norm_sq_green_le_two_sided (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ)
    {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := by
  have hΦ : 0 ≤ Φ := by linarith
  have h1 := norm_sq_green_le_row hMG hm hΩ hδ hS0 hSrow hΦ hΦδ hLrow hij
  have hk : ∀ k, ‖G k j‖ ^ 2
      ≤ 9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 + (if k = j then 9 / 4 else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_left rfl]
      have h2 := hΩ.norm_sq_diag_le hm hδ k
      have h3 : 0 ≤ 9 * Φ * ∑ l, S l k * ‖G k l‖ ^ 2 :=
        mul_nonneg (by linarith) (Finset.sum_nonneg fun l _ =>
          mul_nonneg (hS0 l k) (sq_nonneg _))
      linarith
    · rw [ite_eq_right hkj, add_zero]
      exact norm_sq_green_le_col hGM hm hΩ hδ hS0 hScol hΦ hΦδ hLcol hkj
  have hsum : ∑ k, S i k * ‖G k j‖ ^ 2
      ≤ 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j := by
    calc ∑ k, S i k * ‖G k j‖ ^ 2
        ≤ ∑ k, S i k * (9 * Φ * ∑ l, S l j * ‖G k l‖ ^ 2 + (if k = j then 9 / 4 else 0)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hk k) (hS0 i k)
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j)
            + ∑ k, S i k * (if k = j then 9 / 4 else 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = 9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j := by
          congr 1
          simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
          ring
  have hX : 0 ≤ ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hS0 i k) (sq_nonneg _)) (hS0 l j)
  have hSij := hS0 i j
  have hΦ2 : Φ ≤ Φ ^ 2 := by nlinarith
  calc ‖G i j‖ ^ 2 ≤ 9 * Φ * ∑ k, S i k * ‖G k j‖ ^ 2 := h1
    _ ≤ 9 * Φ * (9 * Φ * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j) + 9 / 4 * S i j) :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := by
        nlinarith [mul_le_mul_of_nonneg_right hΦ2 hSij]

/-- (4.11) in the form used below: with `Λ` bounding both terms on the right,
`|G_{ij}|² ≤ 162 Φ² Λ` for `i ≠ j`. -/
theorem norm_sq_green_offdiag_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    {i j : n} (hij : i ≠ j) :
    ‖G i j‖ ^ 2 ≤ 162 * Φ ^ 2 * Λ := by
  have h := norm_sq_green_le_two_sided hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol hij
  have h2 : ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j ≤ 2 * Λ := by
    linarith [hΛ1 i j, hΛ2 i j]
  have hΦ2 : 0 ≤ 81 * Φ ^ 2 := by positivity
  calc ‖G i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j + S i j) := h
    _ ≤ 81 * Φ ^ 2 * (2 * Λ) := mul_le_mul_of_nonneg_left h2 hΦ2
    _ = 162 * Φ ^ 2 * Λ := by ring

omit [DecidableEq n] in
/-- A double sum over a subset is bounded by the full double sum, for non-negative terms. -/
theorem sum_sum_le_sum_sum (s : Finset n) {f : n → n → ℝ} (hf : ∀ k l, 0 ≤ f k l) :
    ∑ k ∈ s, ∑ l ∈ s, f k l ≤ ∑ k, ∑ l, f k l := by
  calc ∑ k ∈ s, ∑ l ∈ s, f k l ≤ ∑ k ∈ s, ∑ l, f k l :=
        Finset.sum_le_sum fun k _ =>
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun l _ _ => hf k l
    _ ≤ ∑ k, ∑ l, f k l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun k _ _ =>
          Finset.sum_nonneg fun l _ => hf k l

/-- The right-hand side of the quadratic LDE, after removing the `(i)` superscript with
(4.9) and using (4.11): `∑_{k,l≠i} S_{ik} |G^(i)_{kl}|² S_{li} ≤ 38 Φ Λ`. -/
theorem ldeQuadRHS_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1)
    (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (i : n) :
    ldeQuadRHS S G i ≤ 38 * Φ * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hpt : ∀ k ∈ univ.erase i, ∀ l ∈ univ.erase i,
      S i k * ‖greenMinor G i k l‖ ^ 2 * S l i
        ≤ S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i := by
    intro k hk l hl
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hli : l ≠ i := Finset.ne_of_mem_erase hl
    have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k l
    have h2 := hΩ.norm_offdiag_le hli.symm
    have h3 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + ‖greenMinor G i k l - G k l‖ := by
      calc ‖greenMinor G i k l‖ = ‖G k l + (greenMinor G i k l - G k l)‖ := by
            rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖G k i‖ * ‖G i l‖ ≤ ‖G k i‖ * δ :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have h5 : ‖greenMinor G i k l‖ ≤ ‖G k l‖ + 2 * δ * ‖G k i‖ := by linarith
    have h6 := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol
      hΛ1 hΛ2 hki
    have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
    have h7 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 8 * δ ^ 2 * ‖G k i‖ ^ 2 := by
      have := norm_nonneg (greenMinor G i k l)
      nlinarith [sq_nonneg (‖G k l‖ - 2 * δ * ‖G k i‖), norm_nonneg (G k i),
        norm_nonneg (G k l)]
    have h8 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 36 * Φ * Λ := by
      have h9 : 8 * δ ^ 2 * ‖G k i‖ ^ 2 ≤ 8 * δ ^ 2 * (162 * Φ ^ 2 * Λ) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h10 : 8 * δ ^ 2 * (162 * Φ ^ 2 * Λ) = 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h11 : 36 * (36 * Φ * δ ^ 2) * (Φ * Λ) ≤ 36 * 1 * (Φ * Λ) := by
        have : 0 ≤ Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
      linarith
    have h12 : ‖greenMinor G i k l‖ ^ 2 ≤ 2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h12 (hS0 i k)) (hS0 l i)
  have hnn : ∀ k l, 0 ≤ S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i := by
    intro k l
    have : 0 ≤ 36 * Φ * Λ := mul_nonneg (by linarith) hΛ0
    exact mul_nonneg (mul_nonneg (hS0 i k) (by positivity)) (hS0 l i)
  calc ldeQuadRHS S G i
      ≤ ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i,
          S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hpt k hk l hl
    _ ≤ ∑ k, ∑ l, S i k * (2 * ‖G k l‖ ^ 2 + 36 * Φ * Λ) * S l i :=
        sum_sum_le_sum_sum _ hnn
    _ = 2 * ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l i
          + 36 * Φ * Λ * ((∑ k, S i k) * ∑ l, S l i) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ 2 * Λ + 36 * Φ * Λ * (1 * 1) := by
        have h1 := hΛ1 i i
        have h2 : (∑ k, S i k) * ∑ l, S l i ≤ 1 * 1 :=
          mul_le_mul (hSrow i) (hScol i) (Finset.sum_nonneg fun l _ => hS0 l i) zero_le_one
        have h3 : 0 ≤ 36 * Φ * Λ := mul_nonneg (by linarith) hΛ0
        nlinarith
    _ ≤ 38 * Φ * Λ := by nlinarith

/-- **The self-consistent equation behind (4.3).**  On the event, (4.7), the quadratic LDE,
(4.9) and (4.11) give
`G_{ii}⁻¹ = -z - t ∑_k S_{ik} G_{kk} + e_i` with `|e_i|² ≤ 240 Φ² Λ`. -/
theorem norm_sq_selfEnergy_err_le (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ) (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k)
    (hSrow : ∀ i, ∑ k, S i k ≤ 1) (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ)
    (hLquad : LDEQuad H G S t Φ) (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    (i : n) :
    ‖(G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k‖ ^ 2 ≤ 240 * Φ ^ 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i i) (hΛ2 i i)
  have hΦ : 0 ≤ Φ := by linarith
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i i)
  have hGii := hΩ.diag_ne_zero hm hδ i
  have hinv := inv_green_diag_eq hGM hMG hGii
  rw [sum_erase_sub_smul_quad, sub_smul_one_apply_self] at hinv
  set Q := ∑ k ∈ univ.erase i, ∑ l ∈ univ.erase i, H i k * greenMinor G i k l * H l i with hQ
  set A2 := Q - (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k with hA2
  set A3 := (t : ℂ) * ((S i i : ℂ) * G i i) with hA3
  set A4 := (t : ℂ) * ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) with hA4
  have hsplit : ∑ k, (S i k : ℂ) * G k k
      = (S i i : ℂ) * G i i + ∑ k ∈ univ.erase i, (S i k : ℂ) * greenMinor G i k k
        + ∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have heq : (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k = H i i - A2 + A3 + A4 := by
    rw [hinv, hsplit, hA2, hA3, hA4]
    ring
  rw [heq]
  -- the four pieces
  have hb1 : ‖H i i‖ ^ 2 ≤ Φ * Λ :=
    (hLdiag i).trans (mul_le_mul_of_nonneg_left (hΛ2 i i) hΦ)
  have hb2 : ‖A2‖ ^ 2 ≤ 38 * Φ ^ 2 * Λ := by
    have h1 := hLquad i
    have h2 := ldeQuadRHS_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol hΛ1 hΛ2 i
    have h3 : ‖A2‖ ^ 2 = ldeQuadLHS H G S t i := rfl
    calc ‖A2‖ ^ 2 ≤ Φ * ldeQuadRHS S G i := h3 ▸ h1
      _ ≤ Φ * (38 * Φ * Λ) := mul_le_mul_of_nonneg_left h2 hΦ
      _ = 38 * Φ ^ 2 * Λ := by ring
  have hSii1 : S i i ≤ 1 :=
    le_trans (Finset.single_le_sum (fun k _ => hS0 i k) (Finset.mem_univ i)) (hSrow i)
  have hb3 : ‖A3‖ ^ 2 ≤ 9 / 4 * Λ := by
    have hn : ‖A3‖ = t * (S i i * ‖G i i‖) := by
      rw [hA3, norm_mul, norm_mul, Complex.norm_of_nonneg ht0, Complex.norm_of_nonneg (hS0 i i)]
    have h1 := hΩ.norm_sq_diag_le hm hδ i
    have h2 : ‖A3‖ ^ 2 ≤ S i i ^ 2 * ‖G i i‖ ^ 2 := by
      have h0 : 0 ≤ S i i * ‖G i i‖ := mul_nonneg (hS0 i i) (norm_nonneg _)
      have h5 : t * (S i i * ‖G i i‖) ≤ S i i * ‖G i i‖ := by nlinarith
      calc ‖A3‖ ^ 2 = (t * (S i i * ‖G i i‖)) ^ 2 := by rw [hn]
        _ ≤ (S i i * ‖G i i‖) ^ 2 := pow_le_pow_left₀ (mul_nonneg ht0 h0) h5 2
        _ = S i i ^ 2 * ‖G i i‖ ^ 2 := by ring
    have h3 : S i i ^ 2 ≤ Λ := by nlinarith [hS0 i i, hΛ2 i i]
    have h4 : S i i ^ 2 * ‖G i i‖ ^ 2 ≤ Λ * (9 / 4) :=
      mul_le_mul h3 h1 (sq_nonneg _) hΛ0
    linarith
  have hb4 : ‖A4‖ ^ 2 ≤ 18 * Φ * Λ := by
    have hpt : ∀ k ∈ univ.erase i,
        ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ ≤ S i k * (2 * δ * ‖G i k‖) := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      rw [norm_mul, Complex.norm_of_nonneg (hS0 i k), norm_sub_rev]
      refine mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have h1 := hΩ.norm_greenMinor_sub_le hm hδ i k k
      have h2 := hΩ.norm_offdiag_le hki
      have h3 : ‖G k i‖ * ‖G i k‖ ≤ δ * ‖G i k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      linarith
    have hA4le : ‖A4‖ ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) := by
      rw [hA4, norm_mul, Complex.norm_of_nonneg ht0]
      calc t * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖
          ≤ 1 * ‖∑ k ∈ univ.erase i, (S i k : ℂ) * (G k k - greenMinor G i k k)‖ :=
            mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ ≤ ∑ k ∈ univ.erase i, ‖(S i k : ℂ) * (G k k - greenMinor G i k k)‖ := by
            rw [one_mul]; exact norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum hpt
    have hCS : (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2
        ≤ (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 := by
      refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => hS0 i k)
        (fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)) fun k _ => le_of_eq (by ring)
    have hE1 : ∑ k ∈ univ.erase i, S i k ≤ 1 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i univ)
        fun k _ _ => hS0 i k) (hSrow i)
    have hE2 : ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (162 * Φ ^ 2 * Λ)) := by
      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hS0 i k)
      have hki : i ≠ k := (Finset.ne_of_mem_erase hk).symm
      have h1 := norm_sq_green_offdiag_le hGM hMG hm hΩ hδ hS0 hSrow hScol hΦ1 hΦδ hLrow hLcol
        hΛ1 hΛ2 hki
      calc (2 * δ * ‖G i k‖) ^ 2 = 4 * δ ^ 2 * ‖G i k‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hE3 : ∑ k ∈ univ.erase i, S i k * (4 * δ ^ 2 * (162 * Φ ^ 2 * Λ))
        ≤ 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) := by
      rw [← Finset.sum_mul]
      have : 0 ≤ 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) := by positivity
      nlinarith
    have hE4 : 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) ≤ 18 * Φ * Λ := by
      have h1 : 4 * δ ^ 2 * (162 * Φ ^ 2 * Λ) = 18 * (36 * Φ * δ ^ 2) * (Φ * Λ) := by ring
      have h2 : 0 ≤ Φ * Λ := mul_nonneg hΦ hΛ0
      nlinarith
    have hS : 0 ≤ ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hS0 i k) (sq_nonneg _)
    have hA4sq : ‖A4‖ ^ 2 ≤ (∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hA4le 2
    have hE5 : (∑ k ∈ univ.erase i, S i k) * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2
        ≤ 1 * ∑ k ∈ univ.erase i, S i k * (2 * δ * ‖G i k‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hE1 hS
    linarith
  -- assemble
  have htri : ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by
    calc ‖H i i - A2 + A3 + A4‖ ≤ ‖H i i - A2 + A3‖ + ‖A4‖ := norm_add_le _ _
      _ ≤ ‖H i i - A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_add_le (H i i - A2) A3]
      _ ≤ ‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖ := by linarith [norm_sub_le (H i i) A2]
  have hsq : ‖H i i - A2 + A3 + A4‖ ^ 2
      ≤ 4 * (‖H i i‖ ^ 2 + ‖A2‖ ^ 2 + ‖A3‖ ^ 2 + ‖A4‖ ^ 2) := by
    have h0 := norm_nonneg (H i i - A2 + A3 + A4)
    have h1 : ‖H i i - A2 + A3 + A4‖ ^ 2 ≤ (‖H i i‖ + ‖A2‖ + ‖A3‖ + ‖A4‖) ^ 2 :=
      pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖H i i‖ - ‖A2‖), sq_nonneg (‖H i i‖ - ‖A3‖),
      sq_nonneg (‖H i i‖ - ‖A4‖), sq_nonneg (‖A2‖ - ‖A3‖), sq_nonneg (‖A2‖ - ‖A4‖),
      sq_nonneg (‖A3‖ - ‖A4‖)]
  have hΦΛ : Φ * Λ ≤ Φ ^ 2 * Λ := by
    have : Φ ≤ Φ ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hΛ0
  have hΛΦ : Λ ≤ Φ ^ 2 * Λ := by
    have : 1 ≤ Φ ^ 2 := by nlinarith
    nlinarith
  nlinarith

/-- **Stability of `1 - ξ S` in `max → max` norm**, with constant `K`: whenever
`|v_i - ξ (S v)_i| ≤ B` for all `i`, then `|v_i| ≤ K B` for all `i`.  This is the paper's
`‖(1 - t m² S)⁻¹‖_{max→max} = O(1)`, stated without forming the inverse. -/
def Stable (S : n → n → ℝ) (ξ : ℂ) (K : ℝ) : Prop :=
  ∀ (v : n → ℂ) (B : ℝ), (∀ i, ‖v i - ξ * ∑ k, (S i k : ℂ) * v k‖ ≤ B) → ∀ i, ‖v i‖ ≤ K * B

/-- **(4.3)**, deterministic form.  On the event `Ω`, given the three LDE inputs, the bound
`|H_{ii}|² ≤ Φ S_{ii}` and stability of `1 - t m² S` with constant `K`,
`|G_{ii} - m|² ≤ 2160 K² Φ² Λ`, where `Λ` bounds `∑_{k,l} S_{ik}|G_{kl}|²S_{lj}` and `S_{ij}`
(in the block model `Λ = 2 max_{a,b} L_{(+,-),(a,b)}`, see `RBM.norm_sq_green_diag_sub_le_blk`). -/
theorem norm_sq_green_diag_sub_le [Nonempty n] (hGM : G * (H - z • (1 : Matrix n n ℂ)) = 1)
    (hMG : (H - z • (1 : Matrix n n ℂ)) * G = 1) (hm : ‖m‖ = 1) {t : ℝ}
    (hmz : m * ((t : ℂ) * m + z) = -1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hΩ : GoodEvent G m δ)
    (hδ : δ ≤ 1 / 2) (hS0 : ∀ i k, 0 ≤ S i k) (hSrow : ∀ i, ∑ k, S i k = 1)
    (hScol : ∀ j, ∑ l, S l j ≤ 1) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hLrow : LDERow H G S Φ) (hLcol : LDECol H G S Φ) (hLquad : LDEQuad H G S t Φ)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * S i i) {Λ : ℝ}
    (hΛ1 : ∀ i j, ∑ k, ∑ l, S i k * ‖G k l‖ ^ 2 * S l j ≤ Λ) (hΛ2 : ∀ i j, S i j ≤ Λ)
    {K : ℝ} (hKδ : K * δ ≤ 1 / 2) (hStab : Stable S ((t : ℂ) * m ^ 2) K)
    (i : n) :
    ‖G i i - m‖ ^ 2 ≤ 2160 * K ^ 2 * Φ ^ 2 * Λ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hΛ0 : 0 ≤ Λ := le_trans (hS0 i₀ i₀) (hΛ2 i₀ i₀)
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) (hΩ i₀ i₀)
  have hSrow' : ∀ i, ∑ k, S i k ≤ 1 := fun i => (hSrow i).le
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  set ε := Real.sqrt (240 * Φ ^ 2 * Λ) with hε
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  set e : n → ℂ := fun i => (G i i)⁻¹ + z + (t : ℂ) * ∑ k, (S i k : ℂ) * G k k with he
  have heb : ∀ i, ‖e i‖ ≤ ε := by
    intro i
    rw [hε, Real.le_sqrt (norm_nonneg _) (by positivity)]
    exact norm_sq_selfEnergy_err_le hGM hMG hm ht0 ht1 hΩ hδ hS0 hSrow' hScol hΦ1 hΦδ hLrow
      hLcol hLquad hLdiag hΛ1 hΛ2 i
  set v : n → ℂ := fun k => G k k - m with hv
  have hvδ : ∀ k, ‖v k‖ ≤ δ := fun k => hΩ.norm_diag_sub_le k
  obtain ⟨k₀, hk₀⟩ := Finite.exists_max fun k => ‖v k‖
  set V := ‖v k₀‖ with hV
  -- the exact identity `v_i - t m² (S v)_i = -m² e_i + m v_i x_i`
  have hident : ∀ i, v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k
      = -(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
    intro i
    have hGii := hΩ.diag_ne_zero hm hδ i
    have hSv : ∑ k, (S i k : ℂ) * G k k = ∑ k, (S i k : ℂ) * v k + m := by
      have h1 : ∑ k, (S i k : ℂ) * v k = ∑ k, (S i k : ℂ) * G k k - m := by
        have h2 : ∑ k, (S i k : ℂ) = 1 := by exact_mod_cast hSrow i
        rw [hv]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h2, one_mul]
      rw [h1]; ring
    have hinv : (G i i)⁻¹ = m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i) := by
      have hz : z = -m⁻¹ - (t : ℂ) * m := by
        field_simp
        linear_combination hmz
      simp only [he, hSv, hz]
      ring
    have h1 : G i i * (m⁻¹ - ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)) = 1 := by
      rw [← hinv]; exact mul_inv_cancel₀ hGii
    have hmm : m * m⁻¹ = 1 := mul_inv_cancel₀ hm0
    simp only [hv]
    linear_combination m * h1 - G i i * hmm
  -- bound on the right-hand side
  have hSvb : ∀ i, ‖∑ k, (S i k : ℂ) * v k‖ ≤ V := by
    intro i
    calc ‖∑ k, (S i k : ℂ) * v k‖ ≤ ∑ k, ‖(S i k : ℂ) * v k‖ := norm_sum_le _ _
      _ ≤ ∑ k, S i k * V := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_of_nonneg (hS0 i k)]
          exact mul_le_mul_of_nonneg_left (hk₀ k) (hS0 i k)
      _ = V := by rw [← Finset.sum_mul, hSrow i, one_mul]
  have hBi : ∀ i, ‖v i - (t : ℂ) * m ^ 2 * ∑ k, (S i k : ℂ) * v k‖ ≤ 3 / 2 * ε + δ * V := by
    intro i
    rw [hident i]
    have hx : ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ ≤ V + ε := by
      calc ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖
          ≤ ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k‖ + ‖e i‖ := norm_sub_le _ _
        _ ≤ V + ε := by
          rw [norm_mul, Complex.norm_of_nonneg ht0]
          have h1 := hSvb i
          have h2 : t * ‖∑ k, (S i k : ℂ) * v k‖ ≤ 1 * V :=
            mul_le_mul ht1 h1 (norm_nonneg _) zero_le_one
          linarith [heb i]
    have hV0 : 0 ≤ V := norm_nonneg _
    calc ‖-(m ^ 2 * e i) + m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖
        ≤ ‖-(m ^ 2 * e i)‖ + ‖m * v i * ((t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i)‖ :=
          norm_add_le _ _
      _ = ‖e i‖ + ‖v i‖ * ‖(t : ℂ) * ∑ k, (S i k : ℂ) * v k - e i‖ := by
          rw [norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, hm]; ring
      _ ≤ ε + δ * (V + ε) := by
          have := mul_le_mul (hvδ i) hx (norm_nonneg _) hδ0
          linarith [heb i]
      _ ≤ 3 / 2 * ε + δ * V := by nlinarith
  have hst := hStab v (3 / 2 * ε + δ * V) hBi
  have hVb : V ≤ 3 * K * ε := by
    have h1 := hst k₀
    have h2 : K * (δ * V) ≤ 1 / 2 * V := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hKδ (norm_nonneg _)
    rw [← hV] at h1
    nlinarith
  have hvi : ‖v i‖ ≤ 3 * K * ε := (hk₀ i).trans hVb
  have hsq : ‖v i‖ ^ 2 ≤ (3 * K * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvi 2
  have hε2 : ε ^ 2 = 240 * Φ ^ 2 * Λ := Real.sq_sqrt (by positivity)
  calc ‖G i i - m‖ ^ 2 = ‖v i‖ ^ 2 := rfl
    _ ≤ (3 * K * ε) ^ 2 := hsq
    _ = 9 * K ^ 2 * ε ^ 2 := by ring
    _ = 2160 * K ^ 2 * Φ ^ 2 * Λ := by rw [hε2]; ring

end EntryBound

section Averaged

variable {n : Type*} [Fintype n]

/-- **The self-consistent step of (4.5).**  Let `x_i` stand for `E_i(G_{ii} - m)`.  If
`x_i = ξ ∑_k S_{ik}(G_{kk} - m) + O(A)` (the Gaussian integration by parts display on p. 50)
and `∑_k S_{ik}(1 - E_k)(G_{kk} - m) = O(B)` (the fluctuation averaging (4.12) with
`t_k = S_{ik}`), then stability of `1 - ξS` gives `|x_i| ≤ K (A + B)`. -/
theorem norm_condExp_le {S : n → n → ℝ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ} (x : n → ℂ) {A B : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B) (i : n) :
    ‖x i‖ ≤ K * (A + B) := by
  refine hStab x (A + B) (fun j => ?_) i
  have hsplit : x j - ξ * ∑ k, (S j k : ℂ) * x k
      = (x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m))
        + ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  calc ‖(x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m))
        + ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k)‖
      ≤ ‖x j - ξ * ∑ k, (S j k : ℂ) * (G k k - m)‖
        + ‖ξ * ∑ k, (S j k : ℂ) * ((G k k - m) - x k)‖ := norm_add_le _ _
    _ ≤ A + 1 * B := by
        rw [norm_mul]
        have := mul_le_mul hξ (hFA j) (norm_nonneg _) zero_le_one
        linarith [hIBP j]
    _ = A + B := by ring

/-- **(4.5)**, deterministic form: for coefficients with `∑_k |c_k| ≤ 1`, if
`∑_k c_k (1 - E_k)(G_{kk} - m) = O(B')` (fluctuation averaging (4.12)) then
`|∑_k c_k (G_{kk} - m)| ≤ B' + K (A + B)`. -/
theorem norm_sum_coef_green_sub_le [Nonempty n] {S : n → n → ℝ}
    {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {K : ℝ} (hStab : Stable S ξ K) {G : Matrix n n ℂ} {m : ℂ}
    (x : n → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - ξ * ∑ k, (S i k : ℂ) * (G k k - m)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (S i k : ℂ) * ((G k k - m) - x k)‖ ≤ B)
    {c : n → ℝ} (hc : ∑ k, |c k| ≤ 1)
    (hFA' : ‖∑ k, (c k : ℂ) * ((G k k - m) - x k)‖ ≤ B') :
    ‖∑ k, (c k : ℂ) * (G k k - m)‖ ≤ B' + K * (A + B) := by
  have hx := norm_condExp_le hξ hStab x hIBP hFA
  obtain ⟨i₀⟩ := (inferInstance : Nonempty n)
  have hX0 : 0 ≤ K * (A + B) := le_trans (norm_nonneg _) (hx i₀)
  have hsplit : ∑ k, (c k : ℂ) * (G k k - m)
      = ∑ k, (c k : ℂ) * ((G k k - m) - x k) + ∑ k, (c k : ℂ) * x k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit]
  have hcx : ‖∑ k, (c k : ℂ) * x k‖ ≤ K * (A + B) := by
    calc ‖∑ k, (c k : ℂ) * x k‖ ≤ ∑ k, ‖(c k : ℂ) * x k‖ := norm_sum_le _ _
      _ ≤ ∑ k, |c k| * (K * (A + B)) := Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
      _ = (∑ k, |c k|) * (K * (A + B)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (K * (A + B)) := mul_le_mul_of_nonneg_right hc hX0
      _ = K * (A + B) := one_mul _
  linarith [norm_add_le (∑ k, (c k : ℂ) * ((G k k - m) - x k)) (∑ k, (c k : ℂ) * x k)]

end Averaged

section Resolvent

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For Hermitian `H` and `Im z ≠ 0`, `H - z` is invertible. -/
theorem isUnit_det_sub_smul_one {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix n n ℂ)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  set u := v - w with hu
  have hu0 : (H - z • (1 : Matrix n n ℂ)) *ᵥ u = 0 := by
    rw [hu, Matrix.mulVec_sub, hvw, sub_self]
  have hHu : H *ᵥ u = z • u := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hu0
    exact hu0
  have him := hH.im_star_dotProduct_mulVec_self u
  rw [hHu, dotProduct_smul, smul_eq_mul] at him
  have hreal : star u ⬝ᵥ u = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  rw [hreal] at him
  have h1 : z.im * (∑ i, Complex.normSq (u i)) = 0 := by
    have : RCLike.im (z * ((∑ i, Complex.normSq (u i) : ℝ) : ℂ))
        = z.im * ∑ i, Complex.normSq (u i) := by
      rw [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_add]
    rw [← this]; exact him
  have h2 : ∑ i, Complex.normSq (u i) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hz
    · exact h
  have h3 : ∀ i, u i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (u j))).mp h2 i
      (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp this
  have : u = 0 := funext h3
  rw [hu] at this
  exact sub_eq_zero.mp this

theorem green_mul_sub_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    green H z * (H - z • (1 : Matrix n n ℂ)) = 1 :=
  green_mul_self (isUnit_det_sub_smul_one hH hz)

theorem sub_mul_green_of_im {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    (H - z • (1 : Matrix n n ℂ)) * green H z = 1 :=
  self_mul_green (isUnit_det_sub_smul_one hH hz)

end Resolvent

section Block

variable (L W : ℕ)

/-- The kernel of `S^(B)` as a real function: `1/3` on `{0, 1, -1}`, zero elsewhere. -/
noncomputable def sbKre (u : ZMod L) : ℝ := if u ∈ sbSupport L then 1 / 3 else 0

/-- The variance profile `S = S^(B) ⊗ S_W` of Section 2.1 as a real matrix on the
block/offset index: `S_{(a,α),(b,β)} = S^(B)_{ab} / W`. -/
noncomputable def Sblk (i j : ZMod L × Fin W) : ℝ := sbKre L (i.1 - j.1) / W

variable {L W}

theorem sbKre_nonneg (u : ZMod L) : 0 ≤ sbKre L u := by
  unfold sbKre; split_ifs <;> norm_num

theorem sbKre_le (u : ZMod L) : sbKre L u ≤ 1 / 3 := by
  unfold sbKre; split_ifs <;> norm_num

theorem sbKre_neg (u : ZMod L) : sbKre L (-u) = sbKre L u := by
  unfold sbKre
  exact if_congr (neg_mem_sbSupport L) rfl rfl

theorem sbKernel_eq_ofReal (u : ZMod L) : sbKernel L u = (sbKre L u : ℂ) := by
  unfold sbKernel sbKre
  split_ifs <;> push_cast <;> ring

theorem SB_eq_ofReal (a b : ZMod L) : SB L a b = (sbKre L (a - b) : ℂ) := by
  rw [SB_apply, sbKernel_eq_ofReal]

theorem Svar_eq_ofReal (i j : ZMod L × Fin W) : Svar L W i j = (Sblk L W i j : ℂ) := by
  obtain ⟨a, α⟩ := i
  obtain ⟨b, β⟩ := j
  rw [Svar_apply, SB_eq_ofReal, Sblk]
  push_cast
  ring

variable [NeZero L]

theorem sum_sbKre (hL : 3 ≤ L) : ∑ u : ZMod L, sbKre L u = 1 := by
  have h := sum_sbKernel L hL
  simp only [sbKernel_eq_ofReal] at h
  exact_mod_cast h

theorem sum_sbKre_sub_left (hL : 3 ≤ L) (a : ZMod L) : ∑ b : ZMod L, sbKre L (a - b) = 1 := by
  rw [← sum_sbKre hL]
  exact Fintype.sum_equiv (Equiv.subLeft a) _ _ fun b => rfl

theorem sum_sbKre_sub_right (hL : 3 ≤ L) (b : ZMod L) : ∑ a : ZMod L, sbKre L (a - b) = 1 := by
  rw [← sum_sbKre hL]
  exact Fintype.sum_equiv (Equiv.subRight b) _ _ fun a => rfl

/-- `∑_{a'} S^(B)_{a a'} f(a') = 3⁻¹ ∑_{u ∈ {0,1,-1}} f(a + u)`. -/
theorem sum_sbKre_sub_mul (a : ZMod L) (f : ZMod L → ℝ) :
    ∑ a' : ZMod L, sbKre L (a - a') * f a' = 1 / 3 * ∑ u ∈ sbSupport L, f (a + u) := by
  have h1 : ∑ a' : ZMod L, sbKre L (a - a') * f a' = ∑ u : ZMod L, sbKre L u * f (a + u) := by
    refine (Fintype.sum_equiv (Equiv.addLeft a) (fun u => sbKre L u * f (a + u)) _ ?_).symm
    intro u
    simp only [Equiv.coe_addLeft, sub_add_cancel_left, sbKre_neg]
  rw [h1, Finset.mul_sum]
  unfold sbKre
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- `∑_{b'} f(b') S^(B)_{b' b} = 3⁻¹ ∑_{v ∈ {0,1,-1}} f(b + v)`. -/
theorem sum_sbKre_sub_mul' (b : ZMod L) (f : ZMod L → ℝ) :
    ∑ b' : ZMod L, sbKre L (b' - b) * f b' = 1 / 3 * ∑ v ∈ sbSupport L, f (b + v) := by
  have h1 : ∑ b' : ZMod L, sbKre L (b' - b) * f b' = ∑ v : ZMod L, sbKre L v * f (b + v) := by
    refine (Fintype.sum_equiv (Equiv.addLeft b) (fun v => sbKre L v * f (b + v)) _ ?_).symm
    intro v
    simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [h1, Finset.mul_sum]
  unfold sbKre
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

variable [NeZero W]

omit [NeZero L] [NeZero W] in
theorem Sblk_nonneg (i j : ZMod L × Fin W) : 0 ≤ Sblk L W i j :=
  div_nonneg (sbKre_nonneg _) (Nat.cast_nonneg _)

omit [NeZero L] in
theorem Sblk_le (i j : ZMod L × Fin W) :
    Sblk L W i j ≤ if i.1 - j.1 ∈ sbSupport L then (W : ℝ)⁻¹ else 0 := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  unfold Sblk sbKre
  split_ifs
  · rw [div_le_iff₀ hW, inv_mul_cancel₀ hW.ne']; norm_num
  · simp

theorem sum_Sblk_row (hL : 3 ≤ L) (i : ZMod L × Fin W) : ∑ j, Sblk L W i j = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type]
  simp only [Sblk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ b : ZMod L, (W : ℝ) * (sbKre L (i.1 - b) / W) = sbKre L (i.1 - b) := fun b => by
    field_simp
  simp only [this]
  exact sum_sbKre_sub_left hL i.1

theorem sum_Sblk_col (hL : 3 ≤ L) (j : ZMod L × Fin W) : ∑ i, Sblk L W i j = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type]
  simp only [Sblk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ a : ZMod L, (W : ℝ) * (sbKre L (a - j.1) / W) = sbKre L (a - j.1) := fun a => by
    field_simp
  simp only [this]
  exact sum_sbKre_sub_right hL j.1

/-- The `(+,-)` `2`-loop `L_{(+,-),(a,b)} = Tr(G E_a G† E_b)` of (2.41), as a real number
(it is real and non-negative, `RBM.gloop_two_plus_minus_nonneg`). -/
noncomputable def Lre (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) (a b : ZMod L) : ℝ :=
  (gloop L W H z ⟨[true, false], [a, b]⟩).re

variable {H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

/-- `L_{(+,-),(a,b)} = W⁻² ∑_{β,α} |G_{(b,β),(a,α)}|²`. -/
theorem Lre_eq (hH : H.IsHermitian) (a b : ZMod L) :
    Lre H z a b = ((W : ℝ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W, ‖green H z (b, β) (a, α)‖ ^ 2 := by
  rw [Lre, gloop_two_plus_minus_blocks hH]
  have h : ((W : ℂ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W,
        (Complex.normSq (green H z (b, β) (a, α)) : ℂ)
      = ((((W : ℝ)⁻¹) ^ 2 * ∑ β : Fin W, ∑ α : Fin W,
          Complex.normSq (green H z (b, β) (a, α)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.ofReal_re]
  simp_rw [Complex.normSq_eq_norm_sq]

theorem Lre_nonneg (hH : H.IsHermitian) (a b : ZMod L) : 0 ≤ Lre H z a b := by
  rw [Lre_eq hH]
  have : 0 ≤ ∑ β : Fin W, ∑ α : Fin W, ‖green H z (b, β) (a, α)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

/-- The two-sided sum in (4.11) is a weighted sum of `2`-loops:
`∑_{k,l} S_{ik}|G_{kl}|²S_{lj} = ∑_{a',b'} S^(B)_{[i]a'} S^(B)_{b'[j]} L_{(+,-),(b',a')}`. -/
theorem sum_sum_Sblk_eq (hH : H.IsHermitian) (i j : ZMod L × Fin W) :
    ∑ k, ∑ l, Sblk L W i k * ‖green H z k l‖ ^ 2 * Sblk L W l j
      = ∑ a' : ZMod L, ∑ b' : ZMod L, sbKre L (i.1 - a') * sbKre L (b' - j.1) * Lre H z b' a' := by
  simp only [Sblk]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [Lre_eq hH, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  field_simp

/-- The same sum written over nearest neighbours, as in (4.2):
`∑_{k,l} S_{ik}|G_{kl}|²S_{lj} = 9⁻¹ ∑_{u,v ∈ {0,±1}} L_{(+,-),([j]+v,[i]+u)}`. -/
theorem sum_sum_Sblk_eq_nbr (hH : H.IsHermitian) (i j : ZMod L × Fin W) :
    ∑ k, ∑ l, Sblk L W i k * ‖green H z k l‖ ^ 2 * Sblk L W l j
      = 1 / 9 * ∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L, Lre H z (j.1 + v) (i.1 + u) := by
  rw [sum_sum_Sblk_eq hH]
  have h1 : ∀ a' : ZMod L, ∑ b' : ZMod L, sbKre L (i.1 - a') * sbKre L (b' - j.1) * Lre H z b' a'
      = sbKre L (i.1 - a') * (1 / 3 * ∑ v ∈ sbSupport L, Lre H z (j.1 + v) a') := by
    intro a'
    rw [← sum_sbKre_sub_mul' j.1 (fun b' => Lre H z b' a'), Finset.mul_sum]
    exact Finset.sum_congr rfl fun b' _ => by ring
  simp_rw [h1]
  rw [sum_sbKre_sub_mul i.1 (fun a' => 1 / 3 * ∑ v ∈ sbSupport L, Lre H z (j.1 + v) a'),
    ← Finset.mul_sum]
  ring

/-- **(4.2)**, deterministic form: on the event `Ω`, for `i ≠ j`,
`|G_{ij}|² ≤ 81 Φ² (∑_{u,v∈{0,±1}} L_{(+,-),([j]+v,[i]+u)} + W⁻¹ 1(|[i]-[j]| ≤ 1))`. -/
theorem norm_sq_green_le_blk (hL : 3 ≤ L) (hH : H.IsHermitian) (hz : z.im ≠ 0) {m : ℂ}
    (hm : ‖m‖ = 1) {δ : ℝ} (hΩ : GoodEvent (green H z) m δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ}
    (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hLrow : LDERow H (green H z) (Sblk L W) Φ)
    (hLcol : LDECol H (green H z) (Sblk L W) Φ) {i j : ZMod L × Fin W} (hij : i ≠ j) :
    ‖green H z i j‖ ^ 2 ≤ 81 * Φ ^ 2 * (∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L,
        Lre H z (j.1 + v) (i.1 + u) + if i.1 - j.1 ∈ sbSupport L then (W : ℝ)⁻¹ else 0) := by
  have h := norm_sq_green_le_two_sided (green_mul_sub_of_im hH hz) (sub_mul_green_of_im hH hz)
    hm hΩ hδ Sblk_nonneg (fun i => (sum_Sblk_row hL i).le) (fun j => (sum_Sblk_col hL j).le)
    hΦ1 hΦδ hLrow hLcol hij
  rw [sum_sum_Sblk_eq_nbr hH] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 : 0 ≤ ∑ u ∈ sbSupport L, ∑ v ∈ sbSupport L, Lre H z (j.1 + v) (i.1 + u) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Lre_nonneg hH _ _
  have h2 := Sblk_le (L := L) (W := W) i j
  linarith

/-- `max_{a,b} L_{(+,-),(a,b)}`. -/
noncomputable def Lmax (H : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (z : ℂ) : ℝ :=
  (Finset.univ : Finset (ZMod L × ZMod L)).sup' Finset.univ_nonempty fun p => Lre H z p.1 p.2

omit [NeZero W] in
theorem Lre_le_Lmax (a b : ZMod L) : Lre H z a b ≤ Lmax H z :=
  Finset.le_sup' (fun p : ZMod L × ZMod L => Lre H z p.1 p.2) (Finset.mem_univ (a, b))

theorem Lmax_nonneg (hH : H.IsHermitian) : 0 ≤ Lmax H z :=
  le_trans (Lre_nonneg hH 0 0) (Lre_le_Lmax 0 0)

/-- `∑_{k,l} S_{ik}|G_{kl}|²S_{lj} ≤ max_{a,b} L_{(+,-),(a,b)}`. -/
theorem sum_sum_Sblk_le_Lmax (hL : 3 ≤ L) (hH : H.IsHermitian) (i j : ZMod L × Fin W) :
    ∑ k, ∑ l, Sblk L W i k * ‖green H z k l‖ ^ 2 * Sblk L W l j ≤ Lmax H z := by
  rw [sum_sum_Sblk_eq hH]
  calc ∑ a' : ZMod L, ∑ b' : ZMod L, sbKre L (i.1 - a') * sbKre L (b' - j.1) * Lre H z b' a'
      ≤ ∑ a' : ZMod L, ∑ b' : ZMod L, sbKre L (i.1 - a') * sbKre L (b' - j.1) * Lmax H z :=
        Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ =>
          mul_le_mul_of_nonneg_left (Lre_le_Lmax b' a')
            (mul_nonneg (sbKre_nonneg _) (sbKre_nonneg _))
    _ = (∑ a' : ZMod L, sbKre L (i.1 - a')) * (∑ b' : ZMod L, sbKre L (b' - j.1)) * Lmax H z := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.sum_mul]
    _ = Lmax H z := by rw [sum_sbKre_sub_left hL, sum_sbKre_sub_right hL]; ring

/-- On the event `Ω`, `W⁻¹ ≤ 4 max_{a,b} L_{(+,-),(a,b)}` (the lower bound `c W⁻¹ ≤ max L`
on p. 50): the diagonal entries alone contribute `≥ W⁻¹/4` to `L_{(+,-),(a,a)}`. -/
theorem inv_W_le_Lmax (hH : H.IsHermitian) {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ}
    (hΩ : GoodEvent (green H z) m δ) (hδ : δ ≤ 1 / 2) : (W : ℝ)⁻¹ ≤ 4 * Lmax H z := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h1 : (W : ℝ)⁻¹ / 4 ≤ Lre H z 0 0 := by
    rw [Lre_eq hH]
    have hdiag : ∀ β : Fin W, (1 : ℝ) / 4 ≤ ∑ α : Fin W, ‖green H z (0, β) (0, α)‖ ^ 2 := by
      intro β
      have h2 := hΩ.half_le_norm_diag hm hδ (0, β)
      have h3 : (1 : ℝ) / 4 ≤ ‖green H z (0, β) (0, β)‖ ^ 2 := by nlinarith
      exact h3.trans (Finset.single_le_sum (f := fun α => ‖green H z (0, β) (0, α)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ β))
    have h4 : (W : ℝ) * (1 / 4) ≤ ∑ β : Fin W, ∑ α : Fin W, ‖green H z (0, β) (0, α)‖ ^ 2 := by
      calc (W : ℝ) * (1 / 4) = ∑ _β : Fin W, (1 : ℝ) / 4 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun β _ => hdiag β
    calc (W : ℝ)⁻¹ / 4 = ((W : ℝ)⁻¹) ^ 2 * ((W : ℝ) * (1 / 4)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  linarith [Lre_le_Lmax (H := H) (z := z) 0 0]

theorem Sblk_le_Lmax (hH : H.IsHermitian) {m : ℂ} (hm : ‖m‖ = 1) {δ : ℝ}
    (hΩ : GoodEvent (green H z) m δ) (hδ : δ ≤ 1 / 2) (i j : ZMod L × Fin W) :
    Sblk L W i j ≤ 2 * Lmax H z := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have h1 : Sblk L W i j ≤ 1 / 3 * (W : ℝ)⁻¹ := by
    rw [Sblk, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (sbKre_le _) (by positivity)
  have h2 := inv_W_le_Lmax hH hm hΩ hδ
  have h3 := Lmax_nonneg (H := H) (z := z) hH
  linarith

/-- **`‖(1 - ξ S)⁻¹‖_{max→max} ≤ 1 + max_a ∑_b |(Θ_ξ)_{ab}|`** on the full index set.
`S = S^(B) ⊗ S_W` acts on block averages only, so a solution of `v - ξ S v = r` has block
averages `Θ_ξ r̃` and is recovered from them up to `r` itself. -/
theorem stable_Sblk (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) {KΘ : ℝ}
    (hΘ : ∀ a, ∑ b, ‖Theta L ξ a b‖ ≤ KΘ) : Stable (Sblk L W) ξ (1 + KΘ) := by
  intro v B hB
  have hW : (W : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne W
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (0, ⟨0, Nat.pos_of_ne_zero (NeZero.ne W)⟩))
  set vt : ZMod L → ℂ := fun a => (W : ℂ)⁻¹ * ∑ α : Fin W, v (a, α) with hvt
  have hSv : ∀ i : ZMod L × Fin W,
      ∑ k, (Sblk L W i k : ℂ) * v k = ∑ b, SB L i.1 b * vt b := by
    intro i
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [SB_eq_ofReal]
    simp only [hvt]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [Sblk]
    push_cast
    ring
  set r : ZMod L × Fin W → ℂ := fun i => v i - ξ * ∑ k, (Sblk L W i k : ℂ) * v k with hr
  set rt : ZMod L → ℂ := fun a => (W : ℂ)⁻¹ * ∑ α : Fin W, r (a, α) with hrt
  have hrt_le : ∀ a, ‖rt a‖ ≤ B := by
    intro a
    rw [hrt]
    simp only
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (W : ℝ)⁻¹ * ‖∑ α : Fin W, r (a, α)‖ ≤ (W : ℝ)⁻¹ * ∑ α : Fin W, ‖r (a, α)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (W : ℝ)⁻¹ * ∑ _α : Fin W, B :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun α _ => hB (a, α)) (by positivity)
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hmv : (1 - ξ • SB L) *ᵥ vt = rt := by
    funext a
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    have h1 : (SB L *ᵥ vt) a = ∑ b, SB L a b * vt b := rfl
    rw [h1, hrt]
    simp only [hr]
    have h2 : ∀ α : Fin W, ∑ k, (Sblk L W (a, α) k : ℂ) * v k = ∑ b, SB L a b * vt b :=
      fun α => hSv (a, α)
    simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [hvt]
    field_simp
  have hvt_eq : vt = Theta L ξ *ᵥ rt := by
    rw [← hmv, Matrix.mulVec_mulVec, Theta_mul L hL hξ, Matrix.one_mulVec]
  have hvt_le : ∀ b, ‖vt b‖ ≤ KΘ * B := by
    intro b
    rw [hvt_eq]
    calc ‖(Theta L ξ *ᵥ rt) b‖ = ‖∑ c, Theta L ξ b c * rt c‖ := rfl
      _ ≤ ∑ c, ‖Theta L ξ b c * rt c‖ := norm_sum_le _ _
      _ ≤ ∑ c, ‖Theta L ξ b c‖ * B := Finset.sum_le_sum fun c _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hrt_le c) (norm_nonneg _)
      _ = (∑ c, ‖Theta L ξ b c‖) * B := by rw [Finset.sum_mul]
      _ ≤ KΘ * B := mul_le_mul_of_nonneg_right (hΘ b) hB0
  intro i
  have hvi : v i = r i + ξ * ∑ b, SB L i.1 b * vt b := by
    rw [hr]; simp only; rw [hSv i]; ring
  rw [hvi]
  have hsum : ‖∑ b, SB L i.1 b * vt b‖ ≤ KΘ * B := by
    calc ‖∑ b, SB L i.1 b * vt b‖ ≤ ∑ b, ‖SB L i.1 b * vt b‖ := norm_sum_le _ _
      _ ≤ ∑ b, sbKre L (i.1 - b) * (KΘ * B) := Finset.sum_le_sum fun b _ => by
          rw [norm_mul, SB_eq_ofReal, Complex.norm_of_nonneg (sbKre_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hvt_le b) (sbKre_nonneg _)
      _ = KΘ * B := by rw [← Finset.sum_mul, sum_sbKre_sub_left hL, one_mul]
  calc ‖r i + ξ * ∑ b, SB L i.1 b * vt b‖ ≤ ‖r i‖ + ‖ξ‖ * ‖∑ b, SB L i.1 b * vt b‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ B + 1 * (KΘ * B) := by
        have := mul_le_mul hξ.le hsum (norm_nonneg _) zero_le_one
        linarith [hB i]
    _ = (1 + KΘ) * B := by ring

/-- The stability constant of `1 - t m² S` on the short edge: `1 + C/√κ`, with `C/√κ`
the `O_κ(1)` row-sum bound (3.36) of `Θ_{t m²}` (`RBM.sum_norm_Theta_short_edge_le`). -/
noncomputable def Kstab (κ : ℝ) : ℝ := 1 + 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ

omit [NeZero W] in
theorem Kstab_nonneg {κ : ℝ} : 0 ≤ Kstab κ := by
  have h1 := cTwo52_pos
  have h2 := cZero_pos
  unfold Kstab
  positivity

/-- **`‖(1 - t m² S)⁻¹‖_{max→max} = O_κ(1)`** (p. 50), uniformly in `t ∈ [0,1)`, `L`, `W`. -/
theorem stable_Sblk_short_edge (hL : 3 ≤ L) {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Stable (Sblk L W) ((t : ℂ) * mE E ^ 2) (Kstab κ) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hξ : ‖(t : ℂ) * mE E ^ 2‖ < 1 := by rw [norm_short_edge hE2 ht0]; exact ht1
  exact stable_Sblk hL hξ (sum_norm_Theta_short_edge_le L hL hκ0 hκ1 hE ht0 ht1)

omit [NeZero L] [NeZero W] in
theorem zt_im_ne_zero {E κ t : ℝ} (hκ0 : 0 < κ) (hE : |E| ≤ 2 - κ) (ht1 : t < 1) :
    (zt E t).im ≠ 0 := by
  rw [zt_im]
  have h := mE_im_pos (E := E) (by linarith)
  have : 0 < 1 - t := by linarith
  positivity

omit [NeZero L] [NeZero W] in
/-- `m = -(t m + z_t)⁻¹` (p. 50). -/
theorem mE_mul_add_zt {E : ℝ} (hE : |E| ≤ 2) (t : ℝ) :
    mE E * ((t : ℂ) * mE E + zt E t) = -1 := by
  have h := mE_mul hE
  rw [zt]
  linear_combination h

/-- **(4.3)**, deterministic block form: on the event `Ω`, given the LDE inputs,
`|G_{ii} - m|² ≤ 4320 K_κ² Φ² max_{a,b} L_{(+,-),(a,b)}`. -/
theorem norm_sq_green_diag_sub_le_blk (hL : 3 ≤ L) (hH : H.IsHermitian) {E κ t : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) {δ : ℝ}
    (hΩ : GoodEvent (green H (zt E t)) (mE E) δ) (hδ : δ ≤ 1 / 2) {Φ : ℝ} (hΦ1 : 1 ≤ Φ)
    (hΦδ : 36 * Φ * δ ^ 2 ≤ 1) (hKδ : Kstab κ * δ ≤ 1 / 2)
    (hLrow : LDERow H (green H (zt E t)) (Sblk L W) Φ)
    (hLcol : LDECol H (green H (zt E t)) (Sblk L W) Φ)
    (hLquad : LDEQuad H (green H (zt E t)) (Sblk L W) t Φ)
    (hLdiag : ∀ i, ‖H i i‖ ^ 2 ≤ Φ * Sblk L W i i) (i : ZMod L × Fin W) :
    ‖green H (zt E t) i i - mE E‖ ^ 2 ≤ 4320 * Kstab κ ^ 2 * Φ ^ 2 * Lmax H (zt E t) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hz := zt_im_ne_zero hκ0 hE ht1
  have hm := norm_mE hE2
  have hL0 := Lmax_nonneg (z := zt E t) hH
  have h := norm_sq_green_diag_sub_le (green_mul_sub_of_im hH hz) (sub_mul_green_of_im hH hz)
    hm (mE_mul_add_zt hE2 t) ht0 ht1.le hΩ hδ Sblk_nonneg (sum_Sblk_row hL)
    (fun j => (sum_Sblk_col hL j).le) hΦ1 hΦδ hLrow hLcol hLquad hLdiag (Λ := 2 * Lmax H (zt E t))
    (fun i j => (sum_sum_Sblk_le_Lmax hL hH i j).trans (by linarith))
    (Sblk_le_Lmax hH hm hΩ hδ) hKδ (stable_Sblk_short_edge hL hκ0 hκ1 hE ht0 ht1) i
  linarith

/-- The coefficients `t_k = W⁻¹ 1(k ∈ I_a)` used for (4.5). -/
noncomputable def blkCoef (L W : ℕ) (a : ZMod L) (k : ZMod L × Fin W) : ℝ :=
  if k.1 = a then (W : ℝ)⁻¹ else 0

omit [NeZero L] [NeZero W] in
theorem abs_blkCoef_le (a : ZMod L) (k : ZMod L × Fin W) : |blkCoef L W a k| ≤ (W : ℝ)⁻¹ := by
  unfold blkCoef
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
  · simp

theorem sum_abs_blkCoef (a : ZMod L) : ∑ k, |blkCoef L W a k| = 1 := by
  have hW : (W : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne W
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp only [blkCoef, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [abs_of_nonneg (by positivity)]
    field_simp
  · intro b _ hb
    simp [blkCoef, hb]
  · intro h; exact absurd (Finset.mem_univ a) h

omit [NeZero W] in
/-- `⟨(G - m) E_a⟩ = ∑_k t_k (G_{kk} - m)` with `t_k = W⁻¹ 1(k ∈ I_a)`. -/
theorem trace_sub_mul_Eblk (G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (m : ℂ)
    (a : ZMod L) :
    Matrix.trace ((G - m • (1 : Matrix _ _ ℂ)) * Eblk L W a)
      = ∑ k, (blkCoef L W a k : ℂ) * (G k k - m) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Eblk, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, blkCoef]
  split_ifs <;> push_cast <;> ring

/-- **(4.5)**, deterministic block form.  With `x_k` standing for `E_k(G_{kk} - m)`: if
`x_i = t m² ∑_k S_{ik} (G_{kk} - m) + O(A)` (Gaussian integration by parts, p. 50) and the
fluctuation averaging (4.12) holds with error `B` for `t_k = S_{ik}` and `B'` for
`t_k = W⁻¹ 1(k ∈ I_a)`, then `|⟨(G - m)E_a⟩| ≤ B' + K_κ (A + B)`. -/
theorem norm_trace_green_sub_mul_Eblk_le (hL : 3 ≤ L) {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (G : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ) (x : ZMod L × Fin W → ℂ) {A B B' : ℝ}
    (hIBP : ∀ i, ‖x i - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk L W i k : ℂ) * (G k k - mE E)‖ ≤ A)
    (hFA : ∀ i, ‖∑ k, (Sblk L W i k : ℂ) * ((G k k - mE E) - x k)‖ ≤ B) (a : ZMod L)
    (hFA' : ‖∑ k, (blkCoef L W a k : ℂ) * ((G k k - mE E) - x k)‖ ≤ B') :
    ‖Matrix.trace ((G - mE E • (1 : Matrix _ _ ℂ)) * Eblk L W a)‖ ≤ B' + Kstab κ * (A + B) := by
  have hE2 : |E| ≤ 2 := le_trans hE (by linarith)
  have hξ : ‖(t : ℂ) * mE E ^ 2‖ ≤ 1 := by rw [norm_short_edge hE2 ht0]; exact ht1.le
  rw [trace_sub_mul_Eblk]
  exact norm_sum_coef_green_sub_le hξ (stable_Sblk_short_edge hL hκ0 hκ1 hE ht0 ht1) x hIBP
    hFA (sum_abs_blkCoef a).le hFA'

end Block

section Stoch

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

namespace StochDom

/-- Two stochastic dominations, over parameter sets `U₁(N)` and `U₂(N)`, hold jointly over
`U₁(N) ⊕ U₂(N)`. -/
theorem sumElim {U₁ U₂ : ℕ → Type*} {A₁ B₁ : ∀ N, U₁ N → Ω → ℝ} {A₂ B₂ : ∀ N, U₂ N → Ω → ℝ}
    (h₁ : StochDom P A₁ B₁) (h₂ : StochDom P A₂ B₂) :
    StochDom P (U := fun N => U₁ N ⊕ U₂ N)
      (fun N v ω => Sum.elim (fun u => A₁ N u ω) (fun u => A₂ N u ω) v)
      (fun N v ω => Sum.elim (fun u => B₁ N u ω) (fun u => B₂ N u ω) v) := by
  refine of_subset_union h₁ h₂ fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨v, hv⟩
  cases v with
  | inl u => exact Or.inl ⟨u, hv⟩
  | inr u => exact Or.inr ⟨u, hv⟩

/-- **From a deterministic implication to stochastic domination.**  Suppose that for every
`Φ ≥ 1` with `36 Φ δ_N² ≤ 1` and `δ_N ≤ ε₀`, the bounds `A ≤ Φ B` (for all `v`) imply
`ξ ≤ C Φ^k ζ` (for all `u`).  If `A ≺ B` and `δ_N ≤ N^{-c₀}`, then `ξ ≺ ζ`.
(Take `Φ = N^{τ'}` with `τ'` small.) -/
theorem of_det {U V : ℕ → Type*} {A B : ∀ N, V N → Ω → ℝ} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (hAB : StochDom P A B) (hζ : ∀ N u ω, 0 ≤ ζ N u ω) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀)) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (C : ℝ) (k : ℕ)
    (hdet : ∀ N ω (Φ : ℝ), 1 ≤ Φ → 36 * Φ * δ N ^ 2 ≤ 1 → δ N ≤ ε₀ →
      (∀ v, A N v ω ≤ Φ * B N v ω) → ∀ u, ξ N u ω ≤ C * Φ ^ k * ζ N u ω) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  set τ' := min (τ / (2 * ((k : ℝ) + 1))) c₀ with hτ'
  have hk0 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have hτ'0 : 0 < τ' := lt_min (div_pos hτ hk0) hc₀
  have hτ'c : τ' ≤ c₀ := min_le_right _ _
  have hτ'k : τ' * k ≤ τ / 2 := by
    have h1 : τ' ≤ τ / (2 * ((k : ℝ) + 1)) := min_le_left _ _
    have h2 : τ' * (2 * ((k : ℝ) + 1)) ≤ τ := by rwa [le_div_iff₀ hk0] at h1
    nlinarith [hτ'0]
  filter_upwards [hAB τ' hτ'0 D hD, eventually_ge_atTop 1, hδ,
    eventually_le_rpow C (half_pos hτ), eventually_le_rpow 36 hc₀,
    eventually_le_rpow ε₀⁻¹ hc₀] with N hP hN1 hδN hCN h36 hε
  refine (measure_mono ?_).trans hP
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hNc : 0 < (N : ℝ) ^ c₀ := Real.rpow_pos_of_pos hN0 c₀
  have hNneg : (N : ℝ) ^ (-c₀) = ((N : ℝ) ^ c₀)⁻¹ := Real.rpow_neg hN0.le c₀
  intro ω hω
  by_contra hno
  simp only [badSet, Set.mem_ofPred_eq, not_exists, not_lt] at hno hω
  obtain ⟨u, hu⟩ := hω
  set Φ := (N : ℝ) ^ τ' with hΦ
  have hΦ1 : 1 ≤ Φ := Real.one_le_rpow hN hτ'0.le
  have hΦc : Φ ≤ (N : ℝ) ^ c₀ := Real.rpow_le_rpow_of_exponent_le hN hτ'c
  have hδε : δ N ≤ ε₀ := by
    have h1 : (N : ℝ) ^ (-c₀) ≤ ε₀ := by
      rw [hNneg, inv_le_comm₀ hNc hε₀]; exact hε
    linarith
  have hΦδ : 36 * Φ * δ N ^ 2 ≤ 1 := by
    have h1 : δ N ^ 2 ≤ ((N : ℝ) ^ (-c₀)) ^ 2 := pow_le_pow_left₀ (hδ0 N) hδN 2
    have h2 : Φ * ((N : ℝ) ^ (-c₀)) ^ 2 ≤ (N : ℝ) ^ (-c₀) := by
      rw [hNneg]
      have h3 : Φ * ((N : ℝ) ^ c₀)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hNc, one_mul]; exact hΦc
      calc Φ * (((N : ℝ) ^ c₀)⁻¹) ^ 2 = (Φ * ((N : ℝ) ^ c₀)⁻¹) * ((N : ℝ) ^ c₀)⁻¹ := by ring
        _ ≤ 1 * ((N : ℝ) ^ c₀)⁻¹ := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = ((N : ℝ) ^ c₀)⁻¹ := one_mul _
    have h4 : 36 * (N : ℝ) ^ (-c₀) ≤ 1 := by
      rw [hNneg, ← div_eq_mul_inv, div_le_one hNc]; exact h36
    have h5 : 0 ≤ Φ := by linarith
    calc 36 * Φ * δ N ^ 2 ≤ 36 * (Φ * ((N : ℝ) ^ (-c₀)) ^ 2) := by
          have := mul_le_mul_of_nonneg_left h1 h5
          linarith
      _ ≤ 36 * (N : ℝ) ^ (-c₀) := by linarith
      _ ≤ 1 := h4
  have hbound := hdet N ω Φ hΦ1 hΦδ hδε hno u
  have hΦk : Φ ^ k ≤ (N : ℝ) ^ (τ / 2) := by
    rw [hΦ, ← Real.rpow_mul_natCast hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN hτ'k
  have hζu := hζ N u ω
  have hΦk0 : 0 ≤ Φ ^ k := pow_nonneg (by linarith) k
  have hfin : C * Φ ^ k * ζ N u ω ≤ (N : ℝ) ^ τ * ζ N u ω := by
    have e1 : C * Φ ^ k * ζ N u ω ≤ (N : ℝ) ^ (τ / 2) * (Φ ^ k * ζ N u ω) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hCN (mul_nonneg hΦk0 hζu)
    have e2 : (N : ℝ) ^ (τ / 2) * (Φ ^ k * ζ N u ω)
        ≤ (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ζ N u ω) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦk hζu)
        (Real.rpow_nonneg hN0.le _)
    have e3 : (N : ℝ) ^ (τ / 2) * ((N : ℝ) ^ (τ / 2) * ζ N u ω) = (N : ℝ) ^ τ * ζ N u ω := by
      rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]
    linarith
  linarith

/-- **Removing the indicator.**  If `1_{Ω_N} ξ ≺ ζ` and `Ω_N` holds with high probability,
then `ξ ≺ ζ` (the "in particular" of Lemma 4.1, with `Ω_N` given by (4.4)). -/
theorem of_indicator {U : ℕ → Type*} {Ωs : ℕ → Set Ω} (hΩ : HighProb P Ωs)
    {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : StochDom P (fun N u ω => (Ωs N).indicator (fun ω => ξ N u ω) ω) ζ) :
    StochDom P ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ (D + 1) (by linarith), hΩ (D + 1) (by linarith),
    eventually_two_mul_rpow_le D] with N h1 h2 h3
  have hsub : badSet ξ ζ τ N
      ⊆ badSet (fun N u ω => (Ωs N).indicator (fun ω => ξ N u ω) ω) ζ τ N ∪ (Ωs N)ᶜ := by
    rintro ω ⟨u, hu⟩
    by_cases hω : ω ∈ Ωs N
    · left
      refine ⟨u, ?_⟩
      simp only [Set.indicator_of_mem hω]
      exact hu
    · right; exact hω
  have hp : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc P (badSet ξ ζ τ N)
      ≤ P (badSet (fun N u ω => (Ωs N).indicator (fun ω => ξ N u ω) ω) ζ τ N ∪ (Ωs N)ᶜ) :=
        measure_mono hsub
    _ ≤ P (badSet (fun N u ω => (Ωs N).indicator (fun ω => ξ N u ω) ω) ζ τ N) + P (Ωs N)ᶜ :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((N : ℝ) ^ (-(D + 1))) :=
        add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (N : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

end StochDom

end Stoch

section RandomModel

/-! ### Lemma 4.1 in the language of stochastic domination

A random band matrix is a family `H N ω` of Hermitian matrices on the block/offset index
`ZMod (L N) × Fin (W N)`, on a fixed probability space (`RBM.StochDom`).  Everything
probabilistic enters through hypotheses stated with `≺`; the conclusions follow from the
deterministic block lemmas above via `RBM.StochDom.of_det`. -/

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
variable {L W : ℕ → ℕ} [∀ N, NeZero (L N)] [∀ N, NeZero (W N)]

/-- The index set `ZMod L × Fin W` at level `N`. -/
abbrev BIdx (L W : ℕ → ℕ) (N : ℕ) : Type := ZMod (L N) × Fin (W N)

/-- Ordered pairs of distinct indices at level `N`. -/
abbrev OffPair (L W : ℕ → ℕ) (N : ℕ) : Type := {p : BIdx L W N × BIdx L W N // p.1 ≠ p.2}

/-- The event `Ω(t,c) = {‖G - m‖_max ≤ δ_N}` of (4.1) (the paper takes `δ_N = W^{-c}`). -/
def goodSet (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (z m : ℂ) (δ : ℕ → ℝ)
    (N : ℕ) : Set Ω :=
  {ω | GoodEvent (green (H N ω) z) m (δ N)}

/-- **Lemma 4.1, (4.2)**:
`1_Ω |G_{ij}|² ≺ ∑_{u,v ∈ {0,±1}} L_{(+,-),([j]+v,[i]+u)} + W⁻¹ 1(|[i]-[j]| ≤ 1)`,
uniformly in `i ≠ j`, given the large deviation bound `[39, Lemma 3.3]` for the row and
column sums of (4.8) (hypotheses `hLrow`, `hLcol`). -/
theorem entry_bound_stochDom (hL : ∀ N, 3 ≤ L N)
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) {m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hLrow : StochDom P
      (fun N (u : OffPair L W N) ω => ldeRowLHS (H N ω) (green (H N ω) z) u.1.1 u.1.2)
      (fun N u ω => ldeRowRHS (Sblk (L N) (W N)) (green (H N ω) z) u.1.1 u.1.2))
    (hLcol : StochDom P
      (fun N (u : OffPair L W N) ω => ldeColLHS (H N ω) (green (H N ω) z) u.1.1 u.1.2)
      (fun N u ω => ldeColRHS (Sblk (L N) (W N)) (green (H N ω) z) u.1.1 u.1.2)) :
    StochDom P
      (fun N (u : OffPair L W N) ω =>
        (goodSet H z m δ N).indicator (fun ω => ‖green (H N ω) z u.1.1 u.1.2‖ ^ 2) ω)
      (fun N u ω => (∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
          Lre (H N ω) z (u.1.2.1 + b) (u.1.1.1 + a))
        + if u.1.1.1 - u.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0) := by
  refine StochDom.of_det (hLrow.sumElim hLcol) ?_ hδ0 hc₀ hδ (by norm_num : (0 : ℝ) < 1 / 2)
    81 2 ?_
  · intro N u ω
    have h1 : 0 ≤ ∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
        Lre (H N ω) z (u.1.2.1 + b) (u.1.1.1 + a) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Lre_nonneg (hH N ω) _ _
    have h2 : (0 : ℝ) ≤ if u.1.1.1 - u.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0 := by
      split_ifs <;> positivity
    linarith
  · intro N ω Φ hΦ1 hΦδ hδε hAB u
    by_cases hω : ω ∈ goodSet H z m δ N
    · rw [Set.indicator_of_mem hω]
      have hLr : LDERow (H N ω) (green (H N ω) z) (Sblk (L N) (W N)) Φ :=
        fun i j hij => hAB (Sum.inl ⟨(i, j), hij⟩)
      have hLc : LDECol (H N ω) (green (H N ω) z) (Sblk (L N) (W N)) Φ :=
        fun k j hkj => hAB (Sum.inr ⟨(k, j), hkj⟩)
      exact norm_sq_green_le_blk (hL N) (hH N ω) hz hm hω hδε hΦ1 hΦδ hLr hLc u.2
    · rw [Set.indicator_of_notMem hω]
      have h1 : 0 ≤ ∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
          Lre (H N ω) z (u.1.2.1 + b) (u.1.1.1 + a) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Lre_nonneg (hH N ω) _ _
      have h2 : (0 : ℝ) ≤ if u.1.1.1 - u.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0 := by
        split_ifs <;> positivity
      have hΦ0 : 0 ≤ Φ := by linarith
      positivity

omit [∀ N, NeZero (W N)] in
theorem one_le_Kstab {κ : ℝ} : 1 ≤ Kstab κ := by
  have h1 := cTwo52_pos
  have h2 := cZero_pos
  unfold Kstab
  have : 0 ≤ 2 * cTwo52 * (1 / cZero + 2) / Real.sqrt κ := by positivity
  linarith

/-- **Lemma 4.1, (4.3)**: `1_Ω |G_{ii} - m|² ≺ max_{a,b} L_{(+,-),(a,b)}`, uniformly in `i`,
for `z = z_t`, `m = m(E)`, `|E| ≤ 2 - κ`, `0 ≤ t < 1`.  Inputs: the large deviation bound
`[39, Lemma 3.3]` for the row and column sums of (4.8) and for the quadratic form of (4.7)
(`hLrow`, `hLcol`, `hLquad`), and `|H_{ii}|² ≺ S_{ii}` (`hLdiag`). -/
theorem diag_bound_stochDom (hL : ∀ N, 3 ≤ L N)
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hLrow : StochDom P
      (fun N (u : OffPair L W N) ω =>
        ldeRowLHS (H N ω) (green (H N ω) (zt E t)) u.1.1 u.1.2)
      (fun N u ω => ldeRowRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) u.1.1 u.1.2))
    (hLcol : StochDom P
      (fun N (u : OffPair L W N) ω =>
        ldeColLHS (H N ω) (green (H N ω) (zt E t)) u.1.1 u.1.2)
      (fun N u ω => ldeColRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) u.1.1 u.1.2))
    (hLquad : StochDom P
      (fun N (i : BIdx L W N) ω =>
        ldeQuadLHS (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) t i)
      (fun N i ω => ldeQuadRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) i))
    (hLdiag : StochDom P (fun N (i : BIdx L W N) ω => ‖H N ω i i‖ ^ 2)
      (fun N i _ => Sblk (L N) (W N) i i)) :
    StochDom P
      (fun N (i : BIdx L W N) ω =>
        (goodSet H (zt E t) (mE E) δ N).indicator
          (fun ω => ‖green (H N ω) (zt E t) i i - mE E‖ ^ 2) ω)
      (fun N _ ω => Lmax (H N ω) (zt E t)) := by
  have hK1 : 1 ≤ Kstab κ := one_le_Kstab
  have hK0 : 0 < Kstab κ := by linarith
  have hε₀ : (0 : ℝ) < 1 / (2 * Kstab κ) := by positivity
  refine StochDom.of_det (((hLrow.sumElim hLcol).sumElim hLquad).sumElim hLdiag)
    (fun N _ ω => Lmax_nonneg (hH N ω)) hδ0 hc₀ hδ hε₀ (4320 * Kstab κ ^ 2) 2 ?_
  intro N ω Φ hΦ1 hΦδ hδε hAB i
  have hL0 := Lmax_nonneg (z := zt E t) (hH N ω)
  by_cases hω : ω ∈ goodSet H (zt E t) (mE E) δ N
  · rw [Set.indicator_of_mem hω]
    have hδ12 : δ N ≤ 1 / 2 := by
      refine hδε.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hKδ : Kstab κ * δ N ≤ 1 / 2 := by
      have := mul_le_mul_of_nonneg_left hδε hK0.le
      rwa [show Kstab κ * (1 / (2 * Kstab κ)) = 1 / 2 by field_simp] at this
    have hLr : LDERow (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) Φ :=
      fun i j hij => hAB (Sum.inl (Sum.inl (Sum.inl ⟨(i, j), hij⟩)))
    have hLc : LDECol (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) Φ :=
      fun k j hkj => hAB (Sum.inl (Sum.inl (Sum.inr ⟨(k, j), hkj⟩)))
    have hLq : LDEQuad (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) t Φ :=
      fun i => hAB (Sum.inl (Sum.inr i))
    have hLd : ∀ i, ‖H N ω i i‖ ^ 2 ≤ Φ * Sblk (L N) (W N) i i :=
      fun i => hAB (Sum.inr i)
    exact norm_sq_green_diag_sub_le_blk (hL N) (hH N ω) hκ0 hκ1 hE ht0 ht1 hω hδ12 hΦ1 hΦδ hKδ
      hLr hLc hLq hLd i
  · rw [Set.indicator_of_notMem hω]
    have hΦ0 : 0 ≤ Φ := by linarith
    positivity

/-- **Lemma 4.1, (4.5)**: `|⟨(G - m) E_a⟩| ≺ max_{a,b} L_{(+,-),(a,b)}`, uniformly in `a`.
Here `x N ω k` stands for `E_k(G_{kk} - m)` (conditional expectation in the `k`-th row and
column).  Inputs, all with error `Ψ² = max L`:
* `hIBP`: the Gaussian integration by parts display on p. 50,
  `E_i(G_{ii} - m) = t m² ∑_k S_{ik} (G_{kk} - m) + O≺(Ψ²)`;
* `hFArow`, `hFAblk`: the fluctuation averaging (4.12) = `[40, (4.11)]`,
  `∑_k t_k (1 - E_k)(G_{kk} - m) ≺ Ψ²`, for the two families of coefficients the paper uses,
  `t_k = S_{ik}` and `t_k = W⁻¹ 1(k ∈ I_a)` (both satisfy `|t_k| ≤ W⁻¹`, `∑_k |t_k| ≤ 1`). -/
theorem avg_bound_stochDom (hL : ∀ N, 3 ≤ L N)
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x : ∀ N, Ω → BIdx L W N → ℂ)
    (hIBP : StochDom P
      (fun N (i : BIdx L W N) ω => ‖x N ω i - (t : ℂ) * mE E ^ 2 *
        ∑ k, (Sblk (L N) (W N) i k : ℂ) * (green (H N ω) (zt E t) k k - mE E)‖)
      (fun N _ ω => Lmax (H N ω) (zt E t)))
    (hFArow : StochDom P
      (fun N (i : BIdx L W N) ω => ‖∑ k, (Sblk (L N) (W N) i k : ℂ) *
        ((green (H N ω) (zt E t) k k - mE E) - x N ω k)‖)
      (fun N _ ω => Lmax (H N ω) (zt E t)))
    (hFAblk : StochDom P
      (fun N (a : ZMod (L N)) ω => ‖∑ k, (blkCoef (L N) (W N) a k : ℂ) *
        ((green (H N ω) (zt E t) k k - mE E) - x N ω k)‖)
      (fun N _ ω => Lmax (H N ω) (zt E t))) :
    StochDom P
      (fun N (a : ZMod (L N)) ω => ‖Matrix.trace
        ((green (H N ω) (zt E t) - mE E • (1 : Matrix (BIdx L W N) (BIdx L W N) ℂ))
          * Eblk (L N) (W N) a)‖)
      (fun N _ ω => Lmax (H N ω) (zt E t)) := by
  have hK0 : 0 ≤ Kstab κ := Kstab_nonneg
  refine StochDom.of_det ((hIBP.sumElim hFArow).sumElim hFAblk)
    (fun N _ ω => Lmax_nonneg (hH N ω)) (δ := fun _ => 0) (fun _ => le_rfl) one_pos
    (Eventually.of_forall fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _) one_pos
    (1 + 2 * Kstab κ) 1 ?_
  intro N ω Φ hΦ1 _ _ hAB a
  have hL0 := Lmax_nonneg (z := zt E t) (hH N ω)
  have h := norm_trace_green_sub_mul_Eblk_le (hL N) hκ0 hκ1 hE ht0 ht1
    (green (H N ω) (zt E t)) (x N ω) (A := Φ * Lmax (H N ω) (zt E t))
    (B := Φ * Lmax (H N ω) (zt E t)) (B' := Φ * Lmax (H N ω) (zt E t))
    (fun i => hAB (Sum.inl (Sum.inl i))) (fun i => hAB (Sum.inl (Sum.inr i))) a
    (hAB (Sum.inr a))
  calc _ ≤ Φ * Lmax (H N ω) (zt E t)
        + Kstab κ * (Φ * Lmax (H N ω) (zt E t) + Φ * Lmax (H N ω) (zt E t)) := h
    _ = (1 + 2 * Kstab κ) * Φ ^ 1 * Lmax (H N ω) (zt E t) := by ring

/-- **(4.2) without the indicator**, under (4.4): if `Ω(t,c)` holds with high probability. -/
theorem entry_bound_stochDom_of_highProb (hL : ∀ N, 3 ≤ L N)
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) {m : ℂ} (hm : ‖m‖ = 1) {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb P (goodSet H z m δ))
    (hLrow : StochDom P
      (fun N (u : OffPair L W N) ω => ldeRowLHS (H N ω) (green (H N ω) z) u.1.1 u.1.2)
      (fun N u ω => ldeRowRHS (Sblk (L N) (W N)) (green (H N ω) z) u.1.1 u.1.2))
    (hLcol : StochDom P
      (fun N (u : OffPair L W N) ω => ldeColLHS (H N ω) (green (H N ω) z) u.1.1 u.1.2)
      (fun N u ω => ldeColRHS (Sblk (L N) (W N)) (green (H N ω) z) u.1.1 u.1.2)) :
    StochDom P
      (fun N (u : OffPair L W N) ω => ‖green (H N ω) z u.1.1 u.1.2‖ ^ 2)
      (fun N u ω => (∑ a ∈ sbSupport (L N), ∑ b ∈ sbSupport (L N),
          Lre (H N ω) z (u.1.2.1 + b) (u.1.1.1 + a))
        + if u.1.1.1 - u.1.2.1 ∈ sbSupport (L N) then ((W N : ℕ) : ℝ)⁻¹ else 0) :=
  StochDom.of_indicator hΩ
    (entry_bound_stochDom P hL H hH hz hm hδ0 hc₀ hδ hLrow hLcol)

/-- **(4.3) without the indicator**, under (4.4): if `Ω(t,c)` holds with high probability. -/
theorem diag_bound_stochDom_of_highProb (hL : ∀ N, 3 ≤ L N)
    (H : ∀ N, Ω → Matrix (BIdx L W N) (BIdx L W N) ℂ) (hH : ∀ N ω, (H N ω).IsHermitian)
    {E κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {δ : ℕ → ℝ} (hδ0 : ∀ N, 0 ≤ δ N) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hδ : ∀ᶠ N : ℕ in atTop, δ N ≤ (N : ℝ) ^ (-c₀))
    (hΩ : HighProb P (goodSet H (zt E t) (mE E) δ))
    (hLrow : StochDom P
      (fun N (u : OffPair L W N) ω =>
        ldeRowLHS (H N ω) (green (H N ω) (zt E t)) u.1.1 u.1.2)
      (fun N u ω => ldeRowRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) u.1.1 u.1.2))
    (hLcol : StochDom P
      (fun N (u : OffPair L W N) ω =>
        ldeColLHS (H N ω) (green (H N ω) (zt E t)) u.1.1 u.1.2)
      (fun N u ω => ldeColRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) u.1.1 u.1.2))
    (hLquad : StochDom P
      (fun N (i : BIdx L W N) ω =>
        ldeQuadLHS (H N ω) (green (H N ω) (zt E t)) (Sblk (L N) (W N)) t i)
      (fun N i ω => ldeQuadRHS (Sblk (L N) (W N)) (green (H N ω) (zt E t)) i))
    (hLdiag : StochDom P (fun N (i : BIdx L W N) ω => ‖H N ω i i‖ ^ 2)
      (fun N i _ => Sblk (L N) (W N) i i)) :
    StochDom P
      (fun N (i : BIdx L W N) ω => ‖green (H N ω) (zt E t) i i - mE E‖ ^ 2)
      (fun N _ ω => Lmax (H N ω) (zt E t)) :=
  StochDom.of_indicator hΩ
    (diag_bound_stochDom P hL H hH hκ0 hκ1 hE ht0 ht1 hδ0 hc₀ hδ hLrow hLcol hLquad hLdiag)

end RandomModel

end RBM
