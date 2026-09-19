/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.Crossing
import RBM1D.Loop.Primitive

/-!
# Tree values: the star graph and the case `n = 4`

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Definition 3.3 and the
`n = 4` formula after Lemma 3.4, for the trees that are needed to pin down the conventions.

Indices are `0`-based: the polygon vertex `a i` (the paper's `a_{i+1}`) lies between the
regions `i` and `i + 1` (mod `n`), so the boundary edge at `a i` carries
`f_t = Θ_{t m(σ_i) m(σ_{i+1})}` (Definition 3.3, item 1).

## Two corrections, both checked against the primitive equation

* **Boundary indices in the `n = 4` display.** The display after Figure 6 writes the
  boundary factor at `a_i` as `Θ_{t m_{i-1} m_i}`, whereas Definition 3.3 (item 1) and the
  worked example after it give `Θ_{t m_i m_{i+1}}`.  Only the latter solves (2.48): a
  finite-difference check at `n = 3, 4` (`L = 5`, several `σ`, `a`) matches (2.48) to
  `10⁻¹¹` with `Θ_{t m_i m_{i+1}}` and misses by `10⁻²` with `Θ_{t m_{i-1} m_i}`.  The internal
  edges of the display are correct.  `RBM.gammaFour` uses the corrected boundary factors.
* **`n = 2`.** The star formula gives `(Θ²)_{a₁a₂}`, but the solution of (2.55) is
  `Θ_{a₁a₂}` (Example 2.15, `RBM.hasDerivAt_kTwo`).  `RBM.not_hasDerivAt_starK_two` proves that
  the star value does *not* solve (2.55).  For the `2`-gon the tree is the single edge
  `a₁ — a₂` with no internal vertex, and then Lemma 3.4 holds (`RBM.kTwo_eq_edge`).

See `docs/paper-deltas.md`.

## Main definitions

* `RBM.thetaEdge` : `Θ_{t m(s) m(s')}`
* `RBM.starGamma` : the star graph, `∑_b ∏_i (Θ_{t m_i m_{i+1}})_{a_i b}`
* `RBM.gammaFour`  : the `n = 4` display, with corrected boundary factors
* `RBM.splitGamma₀₂`, `RBM.splitGamma₁₃` : the two trees with one internal edge
* `RBM.polyVal`, `RBM.treeVal`, `RBM.treeSum` : the general tree value of Definition 3.3,
  by recursion on the pairing set, and the sum over `T_{SP}` in (3.5)

## Main results

* `RBM.noncrossing_split`, `RBM.isDiag_split_lt` : a pair not crossing a diagonal lies on one
  side of it, and both sides are smaller polygons (well-definedness and termination)
* `RBM.treeSum_four` : **acceptance**, the general definition reduces to `RBM.gammaFour`
* `RBM.kTwo_eq_treeSum` : Lemma 3.4 at `n = 2`
-/

namespace RBM

open Finset

variable (L : ℕ) [NeZero L]

/-- `Θ_{t m(s) m(s')}`, the value of an edge between regions with charges `s`, `s'`. -/
noncomputable def thetaEdge (m : Bool → ℂ) (t : ℝ) (s s' : Bool) : Matrix (ZMod L) (ZMod L) ℂ :=
  Theta L (t * (m s * m s'))

theorem thetaEdge_comm (m : Bool → ℂ) (t : ℝ) (s s' : Bool) :
    thetaEdge L m t s s' = thetaEdge L m t s' s := by
  rw [thetaEdge, thetaEdge, mul_comm (m s)]

/-- The star graph (`F = ∅`): `∑_b ∏_i (Θ_{t m_i m_{i+1}})_{a_i b}`, indices mod `n`. -/
noncomputable def starGamma {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → ZMod L) : ℂ :=
  ∑ b : ZMod L, ∏ i : Fin n, thetaEdge L m t (σ i) (σ (i + 1)) (a i) b

section Two

/-- At `n = 2` the star formula gives `(Θ²)_{a₀a₁}`, not `Θ_{a₀a₁}`. -/
theorem starGamma_two (hL : 3 ≤ L) (m : Bool → ℂ) (t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → ZMod L) (ht : ‖(t : ℂ) * (m (σ 0) * m (σ 1))‖ < 1) :
    starGamma L m t σ a
      = (thetaEdge L m t (σ 0) (σ 1) * thetaEdge L m t (σ 0) (σ 1)) (a 0) (a 1) := by
  rw [starGamma, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fin.prod_univ_two]
  have h11 : (1 : Fin 2) + 1 = 0 := rfl
  have h01 : (0 : Fin 2) + 1 = 1 := rfl
  rw [h11, h01, thetaEdge_comm L m t (σ 1) (σ 0)]
  congr 1
  exact (congrFun (congrFun (Theta_transpose L hL ht) (a 1)) b).symm

/-- (3.5) with the star value at `n = 2`: `W⁻¹ m₁ m₂ (Θ²)_{a₀a₁}`. -/
noncomputable def starKTwo (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (x y : ZMod L) : ℂ :=
  (W : ℂ)⁻¹ * (m σ₁ * m σ₂) * (Theta L (t * (m σ₁ * m σ₂)) * Theta L (t * (m σ₁ * m σ₂))) x y

/-- **The star value does not solve the primitive equation at `n = 2`.**  At `t = 0` its
derivative is `2 W⁻¹ μ² S_{a₁a₂}` (`μ = m₁m₂`) while (2.55) demands `W⁻¹ μ² S_{a₁a₂}`. -/
theorem not_hasDerivAt_starK_two (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ)
    (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) (hμ : m σ₁ * m σ₂ ≠ 0) (hS : SB L a₁ a₂ ≠ 0) :
    ¬ HasDerivAt (fun s => starKTwo L W m s σ₁ σ₂ a₁ a₂)
        ((W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
          starKTwo L W m 0 σ₁ σ₂ a₁ a * SB L a b * starKTwo L W m 0 σ₁ σ₂ b a₂) 0 := by
  intro h
  set μ := m σ₁ * m σ₂ with hμdef
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have h0 : ‖((0 : ℝ) : ℂ) * μ‖ < 1 := by simp
  -- derivative of each entry `s ↦ Θ(sμ)_{xy}` at `0` is `μ S_{xy}`
  have hent : ∀ x y : ZMod L, HasDerivAt (fun s : ℝ => Theta L ((s : ℂ) * μ) x y)
      (μ * SB L x y) 0 := by
    intro x y
    have h1 := hasDerivAt_Theta_apply L hL h0 x y
    have h2 : HasDerivAt (fun ζ : ℂ => ζ * μ) μ ((0 : ℝ) : ℂ) := by
      simpa using (hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const μ
    have h3 := (h1.comp ((0 : ℝ) : ℂ) h2).comp_ofReal
    refine h3.congr_deriv ?_
    simp [Theta_zero, mul_comm]
  -- derivative of the star value at `0`
  have hstar : HasDerivAt (fun s => starKTwo L W m s σ₁ σ₂ a₁ a₂)
      ((W : ℂ)⁻¹ * μ * (2 * (μ * SB L a₁ a₂))) 0 := by
    have hsum : HasDerivAt
        (fun s : ℝ => ∑ b : ZMod L, Theta L ((s : ℂ) * μ) a₁ b * Theta L ((s : ℂ) * μ) b a₂)
        (∑ b : ZMod L, ((μ * SB L a₁ b) * (1 : Matrix (ZMod L) (ZMod L) ℂ) b a₂
          + (1 : Matrix (ZMod L) (ZMod L) ℂ) a₁ b * (μ * SB L b a₂))) 0 := by
      refine HasDerivAt.fun_sum fun b _ => ?_
      refine ((hent a₁ b).mul (hent b a₂)).congr_deriv ?_
      simp [Theta_zero]
    have hval : ∑ b : ZMod L, ((μ * SB L a₁ b) * (1 : Matrix (ZMod L) (ZMod L) ℂ) b a₂
          + (1 : Matrix (ZMod L) (ZMod L) ℂ) a₁ b * (μ * SB L b a₂)) = 2 * (μ * SB L a₁ a₂) := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      ring
    rw [hval] at hsum
    have := hsum.const_mul ((W : ℂ)⁻¹ * μ)
    refine this.congr_deriv rfl |>.congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun s => by
      simp only [starKTwo, Matrix.mul_apply, ← hμdef]
  have huniq := h.unique hstar
  -- the right-hand side of (2.55) at `t = 0`
  have hrhs : (W : ℂ) * ∑ a : ZMod L, ∑ b : ZMod L,
      starKTwo L W m 0 σ₁ σ₂ a₁ a * SB L a b * starKTwo L W m 0 σ₁ σ₂ b a₂
      = (W : ℂ)⁻¹ * μ * (μ * SB L a₁ a₂) := by
    simp only [starKTwo, Complex.ofReal_zero, zero_mul, Theta_zero, mul_one, ← hμdef,
      Matrix.one_apply]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    field_simp
  rw [hrhs] at huniq
  have : (W : ℂ)⁻¹ * μ * (μ * SB L a₁ a₂) = 0 := by linear_combination -1 * huniq
  simp [hW, hμ, hS] at this

/-- The correct tree for the `2`-gon is the single edge `a₀ — a₁`; with it, (3.5) is
Example 2.15: `m_σ W⁻¹ Θ_{a₀a₁} = K_{t,σ,(a₀,a₁)}`. -/
theorem kTwo_eq_edge (W : ℕ) (m : Bool → ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    kTwo L W m t σ₁ σ₂ a₁ a₂ = (m σ₁ * m σ₂) * (W : ℂ)⁻¹ * thetaEdge L m t σ₁ σ₂ a₁ a₂ := by
  rw [kTwo, thetaEdge]
  ring

end Two

section Four

variable (m : Bool → ℂ) (t : ℝ) (σ : Fin 4 → Bool) (a : Fin 4 → ZMod L)

/-- The boundary edge at `a i`: `Θ_{t m(σ_i) m(σ_{i+1})}`. -/
noncomputable abbrev bd (i : Fin 4) : Matrix (ZMod L) (ZMod L) ℂ :=
  thetaEdge L m t (σ i) (σ (i + 1))

/-- The `n = 4` formula after Figure 6, with the boundary factors corrected to
`Θ_{t m_i m_{i+1}}` (see the module docstring):
`∑_{b} ∏_i (Θ_{t m_i m_{i+1}})_{a_i b_i} (δ_{b₀b₁b₂b₃} + δ_{b₀b₁}δ_{b₂b₃}(Θ_{t m₀m₂} - 1)_{b₀b₂}
  + δ_{b₀b₃}δ_{b₁b₂}(Θ_{t m₁m₃} - 1)_{b₀b₁})`. -/
noncomputable def gammaFour : ℂ :=
  ∑ b₀ : ZMod L, ∑ b₁ : ZMod L, ∑ b₂ : ZMod L, ∑ b₃ : ZMod L,
    bd L m t σ 0 (a 0) b₀ * bd L m t σ 1 (a 1) b₁ * bd L m t σ 2 (a 2) b₂ *
      bd L m t σ 3 (a 3) b₃ *
    ((if b₁ = b₀ then if b₂ = b₀ then if b₃ = b₀ then 1 else 0 else 0 else 0)
      + (if b₁ = b₀ then if b₃ = b₂ then
          (thetaEdge L m t (σ 0) (σ 2) - 1) b₀ b₂ else 0 else 0)
      + (if b₃ = b₀ then if b₂ = b₁ then
          (thetaEdge L m t (σ 1) (σ 3) - 1) b₀ b₁ else 0 else 0))

/-- The tree `{(0, 2)}` of `TSP 4` (the paper's pairing `{1, 3}`): `a₀, a₁` hang on `x`,
`a₂, a₃` on `y`, and the internal edge `x — y` separates regions `0` and `2`. -/
noncomputable def splitGamma₀₂ : ℂ :=
  ∑ x : ZMod L, ∑ y : ZMod L,
    bd L m t σ 0 (a 0) x * bd L m t σ 1 (a 1) x * bd L m t σ 2 (a 2) y * bd L m t σ 3 (a 3) y *
      (thetaEdge L m t (σ 0) (σ 2) - 1) x y

/-- The tree `{(1, 3)}` of `TSP 4` (the paper's pairing `{2, 4}`): `a₀, a₃` hang on `x`,
`a₁, a₂` on `y`, and the internal edge separates regions `1` and `3`. -/
noncomputable def splitGamma₁₃ : ℂ :=
  ∑ x : ZMod L, ∑ y : ZMod L,
    bd L m t σ 0 (a 0) x * bd L m t σ 1 (a 1) y * bd L m t σ 2 (a 2) y * bd L m t σ 3 (a 3) x *
      (thetaEdge L m t (σ 1) (σ 3) - 1) x y

/-- **Acceptance criterion for the general tree value.**  The `n = 4` display is the sum of
the values of the three trees of `TSP 4 = {∅, {(0,2)}, {(1,3)}}` (`RBM.TSP_four`). -/
theorem gammaFour_eq :
    gammaFour L m t σ a
      = starGamma L m t σ a + splitGamma₀₂ L m t σ a + splitGamma₁₃ L m t σ a := by
  simp only [gammaFour, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [starGamma, splitGamma₀₂, splitGamma₁₃]
  simp only [Fin.prod_univ_four]

end Four

section General

/-!
### The general tree value (Definition 3.3)

Following the proof of Lemma 3.2, the value of the tree with pairing set `F` is defined by
recursion on `F` rather than by building the tree.  A polygon is stored as its region charges
`rs` (region `k` holds the `k`-th polygon edge) and its vertices `vs`, each with a label and a
boundary matrix; vertex `k` lies between regions `k` and `k + 1` (mod `n`).

* `F = []`: the star, `∑_b ∏_k (M_k)_{a_k b}`.
* `(i, j) :: F` with `(i, j)` a diagonal: the internal edge between regions `i` and `j`
  splits the polygon into the left piece (regions `i, …, j`, vertices `i, …, j - 1`) and the
  right piece (regions `j, …, n - 1, 0, …, i`, vertices `j, …, n - 1, 0, …, i - 1`), each
  closed up by a new vertex with the summed label `y`.  On the left the new vertex carries
  `(Θ_{t m_i m_j} - 1)ᵀ` and on the right the identity, which pins the right centre to `y`;
  together they produce the single internal edge `(Θ_{t m_i m_j} - 1)` between the centres.
  The remaining pairs go to the piece containing them (`RBM.noncrossing_split`).
* A head `(i, j)` that is not a diagonal is skipped.

**Termination.**  A diagonal has `j - i ≥ 2` and is not `(0, n - 1)` (`RBM.IsDiag` excludes
adjacent regions, including the wrap-around pair).  Hence the pieces have `j - i + 1 ≤ n - 1`
and `n - (j - i) + 1 ≤ n - 1` regions, and `n + |F|` decreases.  This is the entire
termination argument, and the reason adjacent pairs are not diagonals.

**Choice of pivot.**  The pivot is the head of the list; `RBM.diagList` lists a `Finset` of
diagonals in lexicographic order, so the value of a `Finset` is well defined without proving
independence of the pivot.  Independence (needed later, e.g. to expand along another
diagonal) is not proved here.
-/

/-- **Non-crossing ⇒ separable.**  A pair `f` that does not cross the diagonal `e = (i, j)`
lies entirely in the left arc `[i, j]` or entirely in the right arc `[j, n - 1] ∪ [0, i]`.
This is what makes the split of `F` in `RBM.polyVal` well defined for crossing-free `F`. -/
theorem noncrossing_split {n : ℕ} {e f : Fin n × Fin n} (h : ¬Crossing e f) :
    (e.1 ≤ f.1 ∧ f.2 ≤ e.2) ∨ (f.2 ≤ e.1 ∨ e.2 ≤ f.1 ∨ (f.1 ≤ e.1 ∧ e.2 ≤ f.2)) := by
  simp only [Crossing, not_or, not_and, not_lt] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Fin.le_def, Fin.lt_def] at h1 h2 ⊢
  omega

/-- Both pieces of a split along a diagonal are smaller polygons: `j - i + 1 < n` and
`n - (j - i) + 1 < n`. -/
theorem isDiag_split_lt {n : ℕ} {i j : Fin n} (h : IsDiag n i j) :
    j.val - i.val + 1 < n ∧ n - (j.val - i.val) + 1 < n := by
  obtain ⟨hij, hadj, hwrap⟩ := h
  have := j.isLt
  rw [Fin.lt_def] at hij
  omega

/-- Re-index a region of the right piece: `r ↦ (r - j) mod n`. -/
def reindexR (n j : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  let k := (p.1 + n - j) % n
  let l := (p.2 + n - j) % n
  (min k l, max k l)

/-- The pairs that go to the left piece of the split at `(i, j)`, re-indexed. -/
def leftPairs (i j : ℕ) (F : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (F.filter fun p => i ≤ p.1 ∧ p.2 ≤ j).map fun p => (p.1 - i, p.2 - i)

/-- The pairs that go to the right piece of the split at `(i, j)`, re-indexed. -/
def rightPairs (n i j : ℕ) (F : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (F.filter fun p => ¬(i ≤ p.1 ∧ p.2 ≤ j)).map (reindexR n j)

theorem length_leftPairs_le (i j : ℕ) (F : List (ℕ × ℕ)) : (leftPairs i j F).length ≤ F.length := by
  rw [leftPairs, List.length_map]
  exact List.length_filter_le _ _

theorem length_rightPairs_le (n i j : ℕ) (F : List (ℕ × ℕ)) :
    (rightPairs n i j F).length ≤ F.length := by
  rw [rightPairs, List.length_map]
  exact List.length_filter_le _ _

/-- The value of a polygon with region charges `rs`, labelled vertices with boundary matrices
`vs`, and pairing list `F`. -/
noncomputable def polyVal (m : Bool → ℂ) (t : ℝ) :
    List Bool → List (ZMod L × Matrix (ZMod L) (ZMod L) ℂ) → List (ℕ × ℕ) → ℂ
  | _, vs, [] => ∑ b : ZMod L, (vs.map fun v => v.2 v.1 b).prod
  | rs, vs, (i, j) :: F =>
    if h : i + 2 ≤ j ∧ j < rs.length ∧ ¬(i = 0 ∧ j = rs.length - 1) then
      ∑ y : ZMod L,
        polyVal m t ((rs.drop i).take (j - i + 1))
          ((vs.drop i).take (j - i) ++
            [(y, (thetaEdge L m t (rs.getD i false) (rs.getD j false) - 1).transpose)])
          (leftPairs i j F) *
        polyVal m t (rs.drop j ++ rs.take (i + 1)) (vs.drop j ++ vs.take i ++ [(y, 1)])
          (rightPairs rs.length i j F)
    else polyVal m t rs vs F
termination_by rs _ F => rs.length + F.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_append,
    List.length_cons]
  · have := length_leftPairs_le i j F
    omega
  · have := length_rightPairs_le rs.length i j F
    omega
  · omega

/-- The polygon of Definition 3.3: vertex `k` has label `a_k` and boundary matrix
`Θ_{t m(σ_k) m(σ_{k+1})}`. -/
noncomputable def bdList (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (ZMod L)) :
    List (ZMod L × Matrix (ZMod L) (ZMod L) ℂ) :=
  (List.range σ.length).map fun k =>
    (a.getD k 0, thetaEdge L m t (σ.getD k false) (σ.getD ((k + 1) % σ.length) false))

/-- **Definition 3.3**: the value `Γ_a(t, σ)` of the tree with pairing list `F`.  For `n ≤ 2`
the tree is the single edge `a₀ — a₁` (see `RBM.not_hasDerivAt_starK_two`). -/
noncomputable def treeVal (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (ZMod L))
    (F : List (ℕ × ℕ)) : ℂ :=
  if σ.length ≤ 2 then
    thetaEdge L m t (σ.getD 0 false) (σ.getD 1 false) (a.getD 0 0) (a.getD 1 0)
  else polyVal L m t σ (bdList L m t σ a) F

/-- The diagonals of `F`, in lexicographic order, as pairs of natural numbers. -/
def diagList {n : ℕ} (F : Finset (Fin n × Fin n)) : List (ℕ × ℕ) :=
  ((F.image fun p => p.1.val * n + p.2.val).sort (· ≤ ·)).map fun c => (c / n, c % n)

/-- `∑_{Γ ∈ T_{SP}(P_a)} Γ_a(t, σ)`, the sum in (3.5). -/
noncomputable def treeSum (m : Bool → ℂ) (t : ℝ) (σ : List Bool) (a : List (ZMod L)) : ℂ :=
  ∑ F ∈ TSP σ.length, treeVal L m t σ a (diagList F)

end General

section Acceptance

variable (m : Bool → ℂ) (t : ℝ) (σ : Fin 4 → Bool) (a : Fin 4 → ZMod L)

theorem bdList_four :
    bdList L m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3]
      = [(a 0, bd L m t σ 0), (a 1, bd L m t σ 1), (a 2, bd L m t σ 2), (a 3, bd L m t σ 3)] := by
  simp only [bdList, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil]
  rfl

theorem treeVal_four_nil :
    treeVal L m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3] [] = starGamma L m t σ a := by
  rw [treeVal, ite_eq_right (by simp), bdList_four, polyVal, starGamma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Fin.prod_univ_four, mul_assoc]

theorem treeVal_four_02 :
    treeVal L m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3] [(0, 2)] = splitGamma₀₂ L m t σ a := by
  rw [treeVal, ite_eq_right (by simp), bdList_four, polyVal, dite_eq_left (by simp)]
  simp only [leftPairs, rightPairs, List.filter_nil, List.map_nil, polyVal]
  simp only [List.drop, List.take, List.getD_cons_zero, List.getD_cons_succ, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Matrix.one_apply, Matrix.transpose_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [splitGamma₀₂, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The `{(1, 3)}` tree.  The display after Figure 6 orients this internal edge from the
centre of `a₀, a₃` to that of `a₁, a₂`, the recursion the other way; they agree because `Θ`
is symmetric. -/
theorem treeVal_four_13 (hL : 3 ≤ L) (h13 : ‖(t : ℂ) * (m (σ 1) * m (σ 3))‖ < 1) :
    treeVal L m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3] [(1, 3)] = splitGamma₁₃ L m t σ a := by
  rw [treeVal, ite_eq_right (by simp), bdList_four, polyVal, dite_eq_left (by simp)]
  simp only [leftPairs, rightPairs, List.filter_nil, List.map_nil, polyVal]
  simp only [List.drop, List.take, List.getD_cons_zero, List.getD_cons_succ, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Matrix.one_apply, Matrix.transpose_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  have hsym : ∀ x y : ZMod L, (thetaEdge L m t (σ 1) (σ 3) - 1) y x
      = (thetaEdge L m t (σ 1) (σ 3) - 1) x y := by
    intro x y
    have h := congrFun (congrFun (Theta_transpose L hL h13) x) y
    simp only [Matrix.sub_apply, Matrix.one_apply, thetaEdge]
    rw [← h]
    simp only [Matrix.transpose_apply, eq_comm (a := y)]
  rw [splitGamma₁₃]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hsym]
  ring

theorem diagList_empty {n : ℕ} : diagList (∅ : Finset (Fin n × Fin n)) = [] := by
  simp [diagList]

theorem diagList_four_02 : diagList ({(0, 2)} : Finset (Fin 4 × Fin 4)) = [(0, 2)] := by
  simp [diagList]

theorem diagList_four_13 : diagList ({(1, 3)} : Finset (Fin 4 × Fin 4)) = [(1, 3)] := by
  simp [diagList]

/-- **Acceptance.**  The general tree sum `∑_{F ∈ T_{SP}(4)} Γ_F` is the `n = 4` display
(`RBM.gammaFour`, with corrected boundary indices). -/
theorem treeSum_four (hL : 3 ≤ L) (h13 : ‖(t : ℂ) * (m (σ 1) * m (σ 3))‖ < 1) :
    treeSum L m t [σ 0, σ 1, σ 2, σ 3] [a 0, a 1, a 2, a 3] = gammaFour L m t σ a := by
  have hlen : [σ 0, σ 1, σ 2, σ 3].length = 4 := rfl
  rw [gammaFour_eq, treeSum, hlen, TSP_four, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, diagList_empty, diagList_four_02,
    diagList_four_13, treeVal_four_nil, treeVal_four_02, treeVal_four_13 L m t σ a hL h13,
    add_assoc]

/-- **Lemma 3.4 at `n = 2`.**  `T_{SP}(2) = {∅}` and the general tree sum is the single edge,
so `m_σ W⁻¹ ∑_Γ Γ_a(t, σ)` is Example 2.15. -/
theorem kTwo_eq_treeSum (W : ℕ) (σ₁ σ₂ : Bool) (a₁ a₂ : ZMod L) :
    kTwo L W m t σ₁ σ₂ a₁ a₂ = (m σ₁ * m σ₂) * (W : ℂ)⁻¹ * treeSum L m t [σ₁, σ₂] [a₁, a₂] := by
  have hTSP : TSP 2 = {∅} := by decide
  have hlen : [σ₁, σ₂].length = 2 := rfl
  rw [treeSum, hlen, hTSP, Finset.sum_singleton, treeVal, ite_eq_left (by simp),
    kTwo_eq_edge]
  rfl

end Acceptance

end RBM
