/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Flow.GUEPhaseStep
import RBM1D.Flow.GUEPhaseMarkov
import RBM1D.Gauss.GridAzuma
import RBM1D.Gauss.GridStop
import RBM1D.Gauss.LoopC2
import RBM1D.Gauss.GridStepDecomp

/-!
# The loop Duhamel tail of the GUE phase

Formalizes the quadratic-variation bound (7.38)/(7.43) of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §7.2, for the constant GUE-phase profile
`S_GUE = 1/S` (`S = L W`), on the GUE-phase grid `RBM.Gauss.GUEGrid.gueH` under
`RBM.Gauss.GUEGrid.Pgue` (the Brownian increment is realized by `K N` independent unit-GUE
draws).

## Main result

* `RBM.Gauss.GUEGrid.gueGrid_loop_duhamel`: for `1 ≤ n ≤ 2 n₀`, uniformly in the grid step
  `k ≤ K = gueGridK n₀ N` and the loop `x`,
  `‖L_k − L_0 − Δ Σ_{j<k} loopDriftGUE(u_j, H_j)‖ ≺
    √(u_k − t₁) · max_{j<k} √(S⁻¹ η_{u_j}^{-2} L^{(2n)}_j) + (S η_{u_k})^{-n}`.
  The statement is unstopped: no stopping time enters.

## Route

* Pathwise, each step `L_{j+1} − L_j − Δ drift_j` is `Z_j + Ỹ_j − B_j + r_j` on the truncation
  set of the new increment (§5, §10): `Z_j = DΦ_j(H_j)[√(Δ/S) X_{j+1}]` is exactly linear,
  `Ỹ_j` is the truncated second-order Taylor remainder recentred by its frozen mean, `B_j` the
  (deterministic, super-polynomially small) truncation bias (§6), `r_j` the remainder of
  `condExp_loop_drift_gue`, bounded almost surely through complex freezing (§7).
* **Dyadic levels.** `Var(Z_j | F_j) ≤ 8 n² (Δ/S) η_{j+1}^{-2} L^{(2n)}(H_j, z_{j+1})`
  (§2–§3: `vGue ≤ 8 ‖·‖_F²` and the Ward identity `G G† = (G − G*)/(2iη)` twice, which turns
  `‖loopCut‖_F²` into four `2n`-loops); the shift `z_{j+1} → z_j` costs `N^{O(n₀)} Δ` (§4, §11).
  For each level `λ_ℓ = 2^ℓ N^{-(40n₀+80)}`, `ℓ ≤ N`, the linear part stopped at
  `firstHit(V, λ_ℓ, K)` has the deterministic conditional proxy `λ_ℓ`
  (`gueHasCondSubgaussianMGF_linear`), and `azuma_complex` applies (§8). The least level above
  the path's proxy recovers the full sum (§10, `gpd_exists_level`).
* **Adapted truncation.** `Ỹ_j` is bounded by `2 b`, `b = O(N^{6n₀+5} Δ)`, has frozen mean
  zero, and Mathlib's Hoeffding lemma plus `gueHasCondSubgaussianMGF_of_frozen` give its
  conditional proxy (§9).
* §14–§16: the exponent bookkeeping, the union bounds (`HighProb.biInter`), and §17 the absorption
  into the control's `(S η)^{-n}` line.

All helpers are `private` (prefix `gpd`). The last `example` is a concrete nondegenerate instance
of every hypothesis of the theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

noncomputable section

namespace RBM.Gauss.GUEGrid

/-! ### 1. The unit-GUE variance of a linear functional is bounded by the Frobenius norm -/

section VGue

open scoped Matrix.Norms.L2Operator

variable {d : Dims}

private theorem gpd_Xmat_single (N : ℕ) (p : d.Idx N × d.Idx N × Bool) :
    Xmat d N (Pi.single (⟨N, p⟩ : Coord d) 1) =
      if p ∈ usedCoord d N then Bmat d N p.1 p.2.1 p.2.2 else 0 := by
  classical
  rw [Xmat_eq_sum]
  have hsingle : ∀ q : d.Idx N × d.Idx N × Bool,
      (Pi.single (⟨N, p⟩ : Coord d) (1 : ℝ) : Ω d) (crd d N q) = if q = p then 1 else 0 := by
    intro q
    by_cases hq : q = p
    · subst hq; simp [crd]
    · have hne : (crd d N q) ≠ (⟨N, p⟩ : Coord d) := by
        intro h
        apply hq
        simpa [crd] using h
      rw [ite_eq_right_iff.2 (fun h => absurd h hq), Pi.single_apply, ite_eq_right_iff.2
        (fun h => absurd h hne)]
  simp only [hsingle, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']

private theorem gpd_norm_trace_Bmat_le (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ)
    {p : d.Idx N × d.Idx N × Bool} (hp : p ∈ usedCoord d N) :
    ‖Matrix.trace (A * Bmat d N p.1 p.2.1 p.2.2)‖ ≤ ‖A p.1 p.2.1‖ + ‖A p.2.1 p.1‖ := by
  obtain ⟨i, j, b⟩ := p
  rw [Matrix.trace_mul_comm]
  by_cases hij : i = j
  · subst hij
    have hb : b = true := by
      rcases mem_usedCoord.1 hp with h | h
      · exact absurd h (lt_irrefl _)
      · exact h.2
    subst hb
    rw [trace_Bmat_mul_diag]
    simp only
    linarith [norm_nonneg (A i i)]
  · rw [trace_Bmat_mul_of_ne hij]
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul]
    have h1 : ‖(if b then (1 : ℂ) else Complex.I)‖ = 1 := by split_ifs <;> simp
    have h2 : ‖(if b then (1 : ℂ) else -Complex.I)‖ = 1 := by split_ifs <;> simp
    rw [h1, h2]
    linarith

private theorem gpd_lin_single_sq_le (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ)
    (p : d.Idx N × d.Idx N × Bool) :
    (Grid.lin (d := d) N A (Xmat d N (Pi.single (⟨N, p⟩ : Coord d) 1))) ^ 2
      ≤ 2 * (‖A p.1 p.2.1‖ ^ 2 + ‖A p.2.1 p.1‖ ^ 2) := by
  rw [gpd_Xmat_single]
  split_ifs with hp
  · have h1 : |Grid.lin (d := d) N A (Bmat d N p.1 p.2.1 p.2.2)|
        ≤ ‖A p.1 p.2.1‖ + ‖A p.2.1 p.1‖ :=
      (Complex.abs_re_le_norm _).trans (gpd_norm_trace_Bmat_le N A hp)
    have h2 : (Grid.lin (d := d) N A (Bmat d N p.1 p.2.1 p.2.2)) ^ 2
        ≤ (‖A p.1 p.2.1‖ + ‖A p.2.1 p.1‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (‖A p.1 p.2.1‖ - ‖A p.2.1 p.1‖)]
  · have h0 : Grid.lin (d := d) N A (0 : Matrix (d.Idx N) (d.Idx N) ℂ) = 0 := by
      simp [Grid.lin]
    rw [h0]
    nlinarith [sq_nonneg ‖A p.1 p.2.1‖, sq_nonneg ‖A p.2.1 p.1‖]

/-- **`vGue A ≤ 8 ‖A‖_F²`.** -/
private theorem gpd_vGue_le (N : ℕ) (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (vGue d N A : ℝ) ≤ 8 * frobSq A := by
  classical
  have hvar : ∀ c : Coord d, (gueUnitVar d c : ℝ) ≤ 1 := by
    intro c; unfold gueUnitVar; split_ifs <;> norm_num
  have hsum : (vGue d N A : ℝ) = ∑ p : d.Idx N × d.Idx N × Bool,
      (Grid.lin (d := d) N A (Xmat d N (Pi.single (⟨N, p⟩ : Coord d) 1))) ^ 2
        * (gueUnitVar d ⟨N, p⟩ : ℝ) := by
    unfold vGue linVar
    push_cast [NNReal.coe_mk]
    unfold Grid.coordFinset
    rw [Finset.sum_map]
    rfl
  rw [hsum]
  have hterm : ∀ p : d.Idx N × d.Idx N × Bool,
      (Grid.lin (d := d) N A (Xmat d N (Pi.single (⟨N, p⟩ : Coord d) 1))) ^ 2
        * (gueUnitVar d ⟨N, p⟩ : ℝ) ≤ 2 * (‖A p.1 p.2.1‖ ^ 2 + ‖A p.2.1 p.1‖ ^ 2) := by
    intro p
    have h0 : (0 : ℝ) ≤ (gueUnitVar d ⟨N, p⟩ : ℝ) := NNReal.coe_nonneg _
    calc (Grid.lin (d := d) N A (Xmat d N (Pi.single (⟨N, p⟩ : Coord d) 1))) ^ 2
          * (gueUnitVar d ⟨N, p⟩ : ℝ)
        ≤ (Grid.lin (d := d) N A (Xmat d N (Pi.single (⟨N, p⟩ : Coord d) 1))) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (hvar _) (sq_nonneg _)
      _ ≤ 2 * (‖A p.1 p.2.1‖ ^ 2 + ‖A p.2.1 p.1‖ ^ 2) := by
          rw [mul_one]; exact gpd_lin_single_sq_le N A p
  refine (Finset.sum_le_sum fun p _ => hterm p).trans (le_of_eq ?_)
  have hsplit : ∑ p : d.Idx N × d.Idx N × Bool, 2 * (‖A p.1 p.2.1‖ ^ 2 + ‖A p.2.1 p.1‖ ^ 2)
      = ∑ i : d.Idx N, ∑ j : d.Idx N, (4 * ‖A i j‖ ^ 2 + 4 * ‖A j i‖ ^ 2) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_bool]
    ring
  rw [hsplit]
  have hswap : ∑ i : d.Idx N, ∑ j : d.Idx N, ‖A j i‖ ^ 2 = frobSq A := by
    unfold frobSq; exact Finset.sum_comm
  have hfrob : ∑ i : d.Idx N, ∑ j : d.Idx N, ‖A i j‖ ^ 2 = frobSq A := rfl
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap, hfrob]
  ring

end VGue

/-! ### 2. The Ward bound of the quadratic variation ((7.43) with `S_GUE = 1/S`) -/

section Ward

open scoped Matrix.Norms.L2Operator
open Matrix

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
/-- The two Ward products `G G†` and `G† G` are both `(2iη)⁻¹ (G(z) - G(z̄))`. -/
private theorem gpd_Gsig_mul_conj {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : Bool) :
    Gsig M z s * (Gsig M z s)ᴴ
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) ∧
      (Gsig M z s)ᴴ * Gsig M z s
        = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
  have hu : IsUnit (M - z • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hM hz
  have hu' : IsUnit (M - ((starRingEnd ℂ) z) • (1 : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hM (by simpa using hz)
  have hc : (2 * Complex.I * (z.im : ℂ)) ≠ 0 := by
    have : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) this
  have h1 : green M z * green M ((starRingEnd ℂ) z)
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
    rw [green_sub_green_conj hu hu', smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : green M ((starRingEnd ℂ) z) * green M z
      = (2 * Complex.I * (z.im : ℂ))⁻¹ • (green M z - green M ((starRingEnd ℂ) z)) := by
    rw [green_sub_green_conj' hu hu', smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [Gsig_conjTranspose hM]
  cases s
  · exact ⟨h2, h1⟩
  · exact ⟨h1, h2⟩

omit [NeZero W] in
/-- A glued trace `tr(E P G_x Pᴴ E G_y)` is a `2n`-loop. -/
private theorem gpd_trace_glue_eq {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (rest : List (Bool × ZMod L)) (a : ZMod L) (x y : Bool) :
    Matrix.trace (Eblk L W a * prodList L W M z rest * Gsig M z x
        * (prodList L W M z rest)ᴴ * Eblk L W a * Gsig M z y)
      = gloop L W M z (EEBridge.ofPairs ((y, a) :: rest ++ EEBridge.rflip x rest a)) := by
  rw [EEBridge.gloop_ofPairs, EEBridge.prodList_append, EEBridge.prodList_cons,
    ← EEBridge.Gsig_mul_conjTranspose_prodList_mul hM x rest a]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

omit [NeZero W] in
private theorem gpd_norm_glue_le {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) (z : ℂ) (rest : List (Bool × ZMod L)) (a : ZMod L) (x y : Bool)
    {m : ℕ} (hm : rest.length + 1 = m) :
    ‖Matrix.trace (Eblk L W a * prodList L W M z rest * Gsig M z x
        * (prodList L W M z rest)ᴴ * Eblk L W a * Gsig M z y)‖ ≤ loopMax L W M z (2 * m) := by
  rw [gpd_trace_glue_eq hM]
  refine norm_gloop_le_loopMax _ ?_ ?_
  · simp [EEBridge.ofPairs, EEBridge.rflip_length]; omega
  · simp [EEBridge.ofPairs, EEBridge.rflip_length]; omega

omit [NeZero W] in
/-- **Ward, for one cut block**: `‖R_k‖_F² ≤ |Im z|⁻² L^{(2n)}`. -/
private theorem gpd_frobSq_loopCut_le {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (ZMod L)} (hI : I.WF) {k : ℕ}
    (hk : k < I.length) :
    frobSq (loopCut L W M z I k) ≤ (|z.im|⁻¹) ^ 2 * loopMax L W M z (2 * I.length) := by
  set s := (EEBridge.pairAt I k).1 with hs
  set a := (EEBridge.pairAt I k).2 with ha
  set rest := (EEBridge.pairs I).drop (k + 1) ++ (EEBridge.pairs I).take k with hrest
  set P := prodList L W M z rest with hP
  set G := Gsig M z s with hG
  set Dl := green M z - green M ((starRingEnd ℂ) z) with hDl
  set c := (2 * Complex.I * (z.im : ℂ))⁻¹ with hcdef
  have hlen : rest.length + 1 = I.length := by
    have h := EEBridge.cutPairs_length hI hk
    simp only [EEBridge.cutPairs, List.length_cons] at h
    rw [hrest]; exact h
  have hR : loopCut L W M z I k = G * Eblk L W a * P * G := by
    rw [EEBridge.loopCut_eq, EEBridge.cutPairs, EEBridge.prodList_cons]
  obtain ⟨hGG, hGG'⟩ := gpd_Gsig_mul_conj hM hz s
  -- the Frobenius norm is the trace of `R Rᴴ`
  have hfrob : ∀ R : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ,
      ((frobSq R : ℝ) : ℂ) = Matrix.trace (R * Rᴴ) := by
    intro R
    unfold frobSq
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have htr : Matrix.trace (loopCut L W M z I k * (loopCut L W M z I k)ᴴ)
      = c * c * Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl) := by
    rw [hR]
    simp only [Matrix.conjTranspose_mul, Eblk_conjTranspose]
    have e1 : G * Eblk L W a * P * G * (Gᴴ * (Pᴴ * (Eblk L W a * Gᴴ)))
        = G * (Eblk L W a * P * (G * Gᴴ) * Pᴴ * Eblk L W a * Gᴴ) := by
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm, hGG]
    have e2 : Eblk L W a * P * (c • Dl) * Pᴴ * Eblk L W a * Gᴴ * G
        = Eblk L W a * P * (c • Dl) * Pᴴ * Eblk L W a * (Gᴴ * G) := by
      simp only [Matrix.mul_assoc]
    rw [e2, hGG']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    ring
  -- expand `Dl = G₊ - G₋` in both slots
  have hexp : Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl)
      = Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z true)
        - Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z false)
        - Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a * Gsig M z true)
        + Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a * Gsig M z false) := by
    rw [hDl, Gsig_true, Gsig_false]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    ring
  have hb : ∀ x y : Bool,
      ‖Matrix.trace (Eblk L W a * P * Gsig M z x * Pᴴ * Eblk L W a * Gsig M z y)‖
        ≤ loopMax L W M z (2 * I.length) := fun x y => gpd_norm_glue_le hM z rest a x y hlen
  have hsum : ‖Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl)‖
      ≤ 4 * loopMax L W M z (2 * I.length) := by
    rw [hexp]
    have := hb true true; have := hb true false; have := hb false true; have := hb false false
    calc _ ≤ ‖Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z true)‖
          + ‖Matrix.trace (Eblk L W a * P * Gsig M z true * Pᴴ * Eblk L W a * Gsig M z false)‖
          + ‖Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a * Gsig M z true)‖
          + ‖Matrix.trace (Eblk L W a * P * Gsig M z false * Pᴴ * Eblk L W a
              * Gsig M z false)‖ := by
          refine (norm_add_le _ _).trans ?_
          refine add_le_add_left ?_ _
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add_left ?_ _
          exact norm_sub_le _ _
      _ ≤ _ := by linarith
  have hcnorm : ‖c * c‖ = (|z.im|⁻¹) ^ 2 / 4 := by
    rw [hcdef, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs]
    norm_num
    field_simp
    rw [sq_abs]; ring
  have hre : frobSq (loopCut L W M z I k)
      = (Matrix.trace (loopCut L W M z I k * (loopCut L W M z I k)ᴴ)).re := by
    rw [← hfrob]; simp
  rw [hre]
  refine (Complex.re_le_norm _).trans ?_
  rw [htr, norm_mul, hcnorm]
  have h0 : 0 ≤ (|z.im|⁻¹) ^ 2 / 4 := by positivity
  calc (|z.im|⁻¹) ^ 2 / 4 * ‖Matrix.trace (Eblk L W a * P * Dl * Pᴴ * Eblk L W a * Dl)‖
      ≤ (|z.im|⁻¹) ^ 2 / 4 * (4 * loopMax L W M z (2 * I.length)) :=
        mul_le_mul_of_nonneg_left hsum h0
    _ = _ := by ring

end Ward

/-! ### 3. The conditional variance of the linear part of one step -/

section QV

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ}

/-- `gradMat` of a loop observable is minus the sum of its cut blocks. -/
private theorem gpd_gradMat_loopObs {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (ZMod (d.L N))}
    (hwf : I.WF) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    Grid.gradMat (loopObs d N z I) M
      = -∑ k ∈ Finset.range I.a.length, loopCut (d.L N) (d.W N) M z I k := by
  ext i j
  rw [Grid.gradMat, Matrix.of_apply, wirtFirst_loopObs_eq hz hM hwf j i, Matrix.neg_apply,
    Matrix.sum_apply]

private theorem gpd_frobSq_neg (A : Matrix (d.Idx N) (d.Idx N) ℂ) : frobSq (-A) = frobSq A := by
  unfold frobSq; simp

private theorem gpd_frobSq_negI (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    frobSq (-Complex.I • A) = frobSq A := by
  unfold frobSq; simp

private theorem gpd_frobSq_sum_le (s : Finset ℕ) (R : ℕ → Matrix (d.Idx N) (d.Idx N) ℂ) :
    frobSq (∑ k ∈ s, R k) ≤ (s.card : ℝ) * ∑ k ∈ s, frobSq (R k) := by
  unfold frobSq
  have key : ∀ i j : d.Idx N, ‖(∑ k ∈ s, R k) i j‖ ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 := by
    intro i j
    rw [Matrix.sum_apply]
    have h1 : ‖∑ k ∈ s, R k i j‖ ≤ ∑ k ∈ s, ‖R k i j‖ := norm_sum_le _ _
    have h2 : (∑ k ∈ s, ‖R k i j‖) ^ 2 ≤ (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  calc ∑ i, ∑ j, ‖(∑ k ∈ s, R k) i j‖ ^ 2
      ≤ ∑ i, ∑ j, (s.card : ℝ) * ∑ k ∈ s, ‖R k i j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (s.card : ℝ) * ∑ i, ∑ j, ∑ k ∈ s, ‖R k i j‖ ^ 2 := by simp only [Finset.mul_sum]
    _ = (s.card : ℝ) * ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := by
        congr 1
        calc ∑ i, ∑ j, ∑ k ∈ s, ‖R k i j‖ ^ 2 = ∑ i, ∑ k ∈ s, ∑ j, ‖R k i j‖ ^ 2 :=
              Finset.sum_congr rfl fun i _ => Finset.sum_comm
          _ = ∑ k ∈ s, ∑ i, ∑ j, ‖R k i j‖ ^ 2 := Finset.sum_comm

/-- **(7.43) for the constant profile**: the unit-GUE variance of the gradient of an `n`-loop
is bounded by `8 n² |Im z|⁻² L^{(2n)}`. -/
private theorem gpd_frobSq_gradMat_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (ZMod (d.L N))}
    (hwf : I.WF) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    frobSq (Grid.gradMat (loopObs d N z I) M)
      ≤ (I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2 * loopMax (d.L N) (d.W N) M z (2 * I.length) := by
  rw [gpd_gradMat_loopObs hz hwf hM, gpd_frobSq_neg]
  refine (gpd_frobSq_sum_le _ _).trans ?_
  rw [Finset.card_range]
  have hk : ∀ k ∈ Finset.range I.a.length, frobSq (loopCut (d.L N) (d.W N) M z I k)
      ≤ (|z.im|⁻¹) ^ 2 * loopMax (d.L N) (d.W N) M z (2 * I.length) :=
    fun k hk => gpd_frobSq_loopCut_le hM hz hwf (Finset.mem_range.1 hk)
  have h1 := Finset.sum_le_sum hk
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
  have hlen : (I.length : ℝ) = (I.a.length : ℝ) := rfl
  rw [hlen]
  have h0 : (0 : ℝ) ≤ (I.a.length : ℝ) := Nat.cast_nonneg _
  calc (I.a.length : ℝ) * ∑ k ∈ Finset.range I.a.length, frobSq (loopCut (d.L N) (d.W N) M z I k)
      ≤ (I.a.length : ℝ) * ((I.a.length : ℝ) * ((|z.im|⁻¹) ^ 2
          * loopMax (d.L N) (d.W N) M z (2 * I.length))) := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

private theorem gpd_vGue_gradMat_le {z : ℂ} (hz : z.im ≠ 0) {I : LoopIdx (ZMod (d.L N))}
    (hwf : I.WF) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    max (vGue d N (Grid.gradMat (loopObs d N z I) M) : ℝ)
        (vGue d N (-Complex.I • Grid.gradMat (loopObs d N z I) M) : ℝ)
      ≤ 8 * ((I.length : ℝ) ^ 2 * (|z.im|⁻¹) ^ 2
          * loopMax (d.L N) (d.W N) M z (2 * I.length)) := by
  have h := gpd_frobSq_gradMat_le hz hwf hM (d := d)
  refine max_le ?_ ?_
  · exact (gpd_vGue_le N _).trans (by linarith)
  · refine (gpd_vGue_le N _).trans ?_
    rw [gpd_frobSq_negI]
    linarith

end QV

/-! ### 4. Crude and Lipschitz bounds on `loopMax` -/

section LoopMaxBounds

open scoped Matrix.Norms.L2Operator

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero W] in
private theorem gpd_card_idx : (Fintype.card (ZMod L × Fin W) : ℝ) = (L : ℝ) * (W : ℝ) := by
  rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]; push_cast; ring

/-- `|L_{σ,a}| ≤ LW |Im z|^{-m}`, hence `L^{(m)} ≤ LW |Im z|^{-m}` (row M2). -/
private theorem gpd_loopMax_le_crude {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    loopMax L W M z m ≤ (L : ℝ) * (W : ℝ) * (|z.im|⁻¹) ^ m := by
  refine loopMax_le fun I hσ ha => ?_
  obtain ⟨σ, a⟩ := I
  simp only at hσ ha
  have hG : ∀ s, ‖Gsig M z s‖ ≤ |z.im|⁻¹ :=
    fun s => norm_Gsig_le_of_green hM (RBM.norm_green_le hM hz) s
  have hp := norm_gloopProd_le_pow (W := W) (H₁ := M) (z₁ := z) (by positivity) hG σ a
    (by rw [hσ, ha])
  rw [gloop]
  refine (norm_trace_le_card_mul _).trans ?_
  rw [gpd_card_idx, ← hσ]
  have h0 : (0 : ℝ) ≤ (L : ℝ) * (W : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left hp h0

/-- The Lipschitz bound of `loopMax` in the spectral parameter. -/
private theorem gpd_loopMax_shift_le {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
    (hM : M.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {K : ℝ} (hK : 1 ≤ K)
    (hGz : ‖green M z‖ ≤ K) (hGz' : ‖green M z'‖ ≤ K) (m : ℕ) :
    loopMax L W M z' m
      ≤ loopMax L W M z m + (L : ℝ) * (W : ℝ) * m * K ^ m * (‖z' - z‖ * K ^ 2) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hsub : ‖green M z' - green M z‖ ≤ ‖z' - z‖ * K ^ 2 := by
    rw [green_sub_green (isUnit_sub_smul_one_of_im_ne_zero hM hz')
      (isUnit_sub_smul_one_of_im_ne_zero hM hz), norm_smul]
    have h1 : ‖green M z' * green M z‖ ≤ K ^ 2 := by
      refine (norm_mul_le _ _).trans ?_
      rw [sq]
      exact mul_le_mul hGz' hGz (norm_nonneg _) hK0
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  refine loopMax_le fun I hσ ha => ?_
  have hwf : I.WF := by unfold LoopIdx.WF; rw [hσ, ha]
  have hd := norm_gloop_sub_le (L := L) (W := W) hK (by positivity) hM hM hGz' hGz hsub I hwf
  rw [hσ] at hd
  have hle : ‖gloop L W M z I‖ ≤ loopMax L W M z m := norm_gloop_le_loopMax I hσ ha
  calc ‖gloop L W M z' I‖ ≤ ‖gloop L W M z I‖ + ‖gloop L W M z' I - gloop L W M z I‖ := by
        have := norm_add_le (gloop L W M z I) (gloop L W M z' I - gloop L W M z I)
        simpa using this
    _ ≤ _ := add_le_add hle hd

end LoopMaxBounds

/-! ### 5. One step: the linear part, the Taylor remainder, its truncation -/

section Step

open scoped Matrix.Norms.L2Operator

variable (d : Dims) (N : ℕ)

/-- **Row Y1**: the truncation set `{|X_{il}| ≤ N}` of one increment. -/
private def gpdGood : Set (Ω d) := {y | ∀ i l : d.Idx N, ‖Xmat d N y i l‖ ≤ N}

/-- The linear part `DΦ(M)[h(y)]` of one step. -/
private def gpdZ (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (v : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) : ℂ :=
  fderiv ℝ Φ M (Hflow d N v y)

/-- The Taylor remainder of one step. -/
private def gpdR (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (v : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) : ℂ :=
  Φ (M + Hflow d N v y) - Φ M - gpdZ d N Φ v M y

/-- The truncated remainder. -/
private def gpdT (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (v : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) : ℂ :=
  (gpdGood d N).indicator (gpdR d N Φ v M) y

/-- The truncation bias (row Y3). -/
private def gpdB (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (v : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  ∫ y, (gpdGood d N)ᶜ.indicator (gpdR d N Φ v M) y ∂(gueUnit d)

variable {d N}

private theorem gpd_measurableSet_good : MeasurableSet (gpdGood d N) := by
  have h : gpdGood d N = ⋂ i : d.Idx N, ⋂ l : d.Idx N, {y | ‖Xmat d N y i l‖ ≤ N} := by
    ext y; simp [gpdGood]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun l => ?_
  exact measurableSet_le (measurable_Xentry d N i l).norm measurable_const

private theorem gpd_lin_eq_im (A X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Grid.lin (d := d) N (-Complex.I • A) X = (Matrix.trace (A * X)).im := by
  unfold Grid.lin
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  ring

/-- `Re Z = √v lin(A, X)`, `Im Z = √v lin(-iA, X)`, `A = gradMat Φ M`. -/
private theorem gpd_Z_re_im (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) {v : ℝ}
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) :
    (gpdZ d N Φ v M y).re = Real.sqrt v * Grid.lin (d := d) N (Grid.gradMat Φ M) (Xmat d N y) ∧
      (gpdZ d N Φ v M y).im
        = Real.sqrt v * Grid.lin (d := d) N (-Complex.I • Grid.gradMat Φ M) (Xmat d N y) := by
  have h : gpdZ d N Φ v M y
      = (Real.sqrt v : ℂ) * Matrix.trace (Grid.gradMat Φ M * Xmat d N y) := by
    unfold gpdZ
    rw [Hflow_eq_realSmul, map_smul, Grid.fderiv_eq_trace_gradMat M (Xmat_isHermitian d N y),
      Complex.real_smul]
  rw [h, gpd_lin_eq_im]
  constructor
  · rw [Complex.re_ofReal_mul]; rfl
  · rw [Complex.im_ofReal_mul]

private theorem gpd_integrable_lin (A : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Integrable (fun y => Grid.lin (d := d) N A (Xmat d N y)) (gueUnit d) ∧
      ∫ y, Grid.lin (d := d) N A (Xmat d N y) ∂(gueUnit d) = 0 := by
  have hmeas : Measurable (fun y : Ω d => Grid.lin (d := d) N A (Xmat d N y)) := by
    unfold Grid.lin
    exact Complex.measurable_re.comp
      ((Continuous.matrix_trace (continuous_const.matrix_mul continuous_id)).measurable.comp
        (measurable_Xmat d N))
  have hmap := gueMap_lin_Xmat (d := d) N A
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 (vGue d N A)) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  refine ⟨?_, ?_⟩
  · rw [← hmap] at hid
    exact (integrable_map_measure hid.aestronglyMeasurable hmeas.aemeasurable).1 hid
  · have h := integral_map (μ := gueUnit d) hmeas.aemeasurable
      (f := fun x : ℝ => x) (measurable_id.aestronglyMeasurable)
    rw [hmap, integral_id_gaussianReal] at h
    exact h.symm

private theorem gpd_integrable_Z (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) (v : ℝ)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Integrable (gpdZ d N Φ v M) (gueUnit d) ∧ ∫ y, gpdZ d N Φ v M y ∂(gueUnit d) = 0 := by
  obtain ⟨h1, h1'⟩ := gpd_integrable_lin (d := d) (N := N) (Grid.gradMat Φ M)
  obtain ⟨h2, h2'⟩ := gpd_integrable_lin (d := d) (N := N) (-Complex.I • Grid.gradMat Φ M)
  have hre : (fun y => RCLike.re (gpdZ d N Φ v M y))
      = fun y => Real.sqrt v * Grid.lin (d := d) N (Grid.gradMat Φ M) (Xmat d N y) :=
    funext fun y => (gpd_Z_re_im Φ M y).1
  have him : (fun y => RCLike.im (gpdZ d N Φ v M y))
      = fun y => Real.sqrt v * Grid.lin (d := d) N (-Complex.I • Grid.gradMat Φ M) (Xmat d N y) :=
    funext fun y => (gpd_Z_re_im Φ M y).2
  have hint : Integrable (gpdZ d N Φ v M) (gueUnit d) := by
    rw [← Integrable.re_im_iff, hre, him]
    exact ⟨h1.const_mul _, h2.const_mul _⟩
  refine ⟨hint, ?_⟩
  apply Complex.ext
  · have := integral_re hint
    rw [hre, integral_const_mul, h1', mul_zero] at this
    simpa using this.symm
  · have := integral_im hint
    rw [him, integral_const_mul, h2', mul_zero] at this
    simpa using this.symm

/-- The pathwise Taylor remainder bound: `‖R‖ ≤ (C₂/2) v ‖X‖²`. -/
private theorem gpd_norm_R_le {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C Φ C₀ C₁ C₂) {v : ℝ} (hv : 0 ≤ v) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (y : Ω d) : ‖gpdR d N Φ v M y‖ ≤ C₂ / 2 * v * ‖Xmat d N y‖ ^ 2 := by
  have hT : TestFun d N Φ := ⟨hΦ.contDiff, ⟨C₀, hΦ.bdd₀⟩, ⟨C₁, hΦ.bdd₁⟩, ⟨C₂, hΦ.bdd₂⟩⟩
  have h := Grid.norm_taylor_remainder_le hT hΦ.bdd₂ M (Xmat d N y) (Real.sqrt_nonneg v)
  have e : gpdR d N Φ v M y = Φ (M + Real.sqrt v • Xmat d N y) - Φ M
      - Real.sqrt v • fderiv ℝ Φ M (Xmat d N y) := by
    unfold gpdR gpdZ
    rw [Hflow_eq_realSmul, map_smul]
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Real.sq_sqrt hv]

private theorem gpd_continuous_R {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C Φ C₀ C₁ C₂) (v : ℝ) :
    Continuous (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => gpdR d N Φ v p.1 p.2) := by
  have hc : Continuous Φ := hΦ.contDiff.continuous
  have hf : Continuous (fderiv ℝ Φ) := hΦ.contDiff.continuous_fderiv (by norm_num)
  have hH : Continuous (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d => Hflow d N v p.2) :=
    (continuous_Hflow d N v).comp continuous_snd
  unfold gpdR gpdZ
  exact ((hc.comp (continuous_fst.add hH)).sub (hc.comp continuous_fst)).sub
    ((hf.comp continuous_fst).clm_apply hH)

private theorem gpd_integrable_R {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C Φ C₀ C₁ C₂) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Integrable (gpdR d N Φ v M) (gueUnit d) ∧
      Integrable (fun y => Φ (M + Hflow d N v y)) (gueUnit d) := by
  have hc : Continuous Φ := hΦ.contDiff.continuous
  have hΦint : Integrable (fun y => Φ (M + Hflow d N v y)) (gueUnit d) := by
    refine (memLp_top_of_bound ?_ C₀ (Eventually.of_forall fun y => hΦ.bdd₀ _)).integrable le_top
    exact (hc.comp (continuous_const.add (continuous_Hflow d N v))).aestronglyMeasurable
  refine ⟨?_, hΦint⟩
  have e : gpdR d N Φ v M = fun y => Φ (M + Hflow d N v y) - Φ M - gpdZ d N Φ v M y := rfl
  rw [e]
  exact (hΦint.sub (integrable_const _)).sub (gpd_integrable_Z Φ v M).1

/-- **The frozen mean of one step**: `∫ Φ(M + h) = Φ(M) + ∫ T + B`. -/
private theorem gpd_integral_step {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C Φ C₀ C₁ C₂) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ∫ y, Φ (M + Hflow d N v y) ∂(gueUnit d)
      = Φ M + ∫ y, gpdT d N Φ v M y ∂(gueUnit d) + gpdB d N Φ v M := by
  obtain ⟨hR, hΦint⟩ := gpd_integrable_R hΦ v M
  obtain ⟨hZ, hZ0⟩ := gpd_integrable_Z Φ v M
  have hpt : (fun y => Φ (M + Hflow d N v y))
      = fun y => Φ M + (gpdZ d N Φ v M y + gpdR d N Φ v M y) := by
    funext y; unfold gpdR; ring
  have hZR : Integrable (fun y => gpdZ d N Φ v M y + gpdR d N Φ v M y) (gueUnit d) := hZ.add hR
  rw [hpt, integral_add (integrable_const _) hZR, integral_add hZ hR, hZ0,
    integral_const, probReal_univ, one_smul, zero_add]
  have hsplit : gpdR d N Φ v M
      = fun y => gpdT d N Φ v M y + (gpdGood d N)ᶜ.indicator (gpdR d N Φ v M) y := by
    funext y; unfold gpdT; rw [Set.indicator_self_add_compl_apply]
  have hT : Integrable (gpdT d N Φ v M) (gueUnit d) := hR.indicator gpd_measurableSet_good
  have hB : Integrable ((gpdGood d N)ᶜ.indicator (gpdR d N Φ v M)) (gueUnit d) :=
    hR.indicator gpd_measurableSet_good.compl
  conv_lhs => rw [hsplit]
  rw [integral_add hT hB]
  unfold gpdB
  ring

/-- On the truncation set, `‖T‖ ≤ (C₂/2) v S² N²` (row Y2). -/
private theorem gpd_norm_T_le {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C Φ C₀ C₁ C₂) {v : ℝ} (hv : 0 ≤ v) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (y : Ω d) :
    ‖gpdT d N Φ v M y‖ ≤ C₂ / 2 * v * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
  have hC2 : 0 ≤ C₂ := hΦ.nonneg₂
  unfold gpdT
  by_cases hy : y ∈ gpdGood d N
  · rw [Set.indicator_of_mem hy]
    refine (gpd_norm_R_le hΦ hv M y).trans ?_
    have hX : ‖Xmat d N y‖ ^ 2 ≤ (Fintype.card (d.Idx N) : ℝ) ^ 2 * (N : ℝ) ^ 2 := by
      refine (l2_opNorm_sq_le_frobSq _).trans ?_
      unfold frobSq
      have hb : ∀ i l : d.Idx N, ‖Xmat d N y i l‖ ^ 2 ≤ (N : ℝ) ^ 2 := fun i l =>
        pow_le_pow_left₀ (norm_nonneg _) (hy i l) 2
      calc ∑ i, ∑ l, ‖Xmat d N y i l‖ ^ 2 ≤ ∑ _i : d.Idx N, ∑ _l : d.Idx N, (N : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hb i l
        _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
    have h0 : 0 ≤ C₂ / 2 * v := by positivity
    exact mul_le_mul_of_nonneg_left hX h0
  · rw [Set.indicator_of_notMem hy, norm_zero]
    have : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) ^ 2 * (N : ℝ) ^ 2 := by positivity
    positivity

end Step

/-! ### 6. The truncation bias (row Y3) -/

section Tail

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ}

private theorem gpd_exp_coord (c : ℝ) (t : d.Idx N × d.Idx N × Bool) :
    Integrable (fun y : Ω d => Real.exp (c * y ⟨N, t⟩)) (gueUnit d) ∧
      ∫ y, Real.exp (c * y ⟨N, t⟩) ∂(gueUnit d) ≤ Real.exp (c ^ 2 / 2) := by
  have hmeas : Measurable (fun y : Ω d => y ⟨N, t⟩) := measurable_pi_apply _
  have hmap : (gueUnit d).map (fun y : Ω d => y ⟨N, t⟩) = gaussianReal 0 (gueUnitVar d ⟨N, t⟩) :=
    Measure.infinitePi_map_eval _ _
  have hlaw : HasLaw (fun y : Ω d => y ⟨N, t⟩) (gaussianReal 0 (gueUnitVar d ⟨N, t⟩))
      (gueUnit d) := ⟨hmeas.aemeasurable, hmap⟩
  have hv : (gueUnitVar d ⟨N, t⟩ : ℝ) ≤ 1 := by unfold gueUnitVar; split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · have h := integrable_exp_mul_gaussianReal (μ := 0) (v := gueUnitVar d ⟨N, t⟩) c
    rw [← hmap] at h
    exact (integrable_map_measure h.aestronglyMeasurable hmeas.aemeasurable).1 h
  · have h := mgf_gaussianReal hlaw c
    have e : ∫ y, Real.exp (c * y ⟨N, t⟩) ∂(gueUnit d)
        = mgf (fun y : Ω d => y ⟨N, t⟩) (gueUnit d) c :=
      rfl
    rw [e, h]
    apply Real.exp_le_exp.2
    have : (gueUnitVar d ⟨N, t⟩ : ℝ) * c ^ 2 ≤ c ^ 2 := by
      nlinarith [sq_nonneg c, NNReal.coe_nonneg (gueUnitVar d ⟨N, t⟩)]
    linarith

/-- `ψ(t,t') = e^{2y_t} + e^{-2y_t} + e^{2y_{t'}} + e^{-2y_{t'}}`. -/
private def gpdPsi (N : ℕ) (y : Ω d) (t t' : d.Idx N × d.Idx N × Bool) : ℝ :=
  Real.exp (2 * y ⟨N, t⟩) + Real.exp (-2 * y ⟨N, t⟩)
    + Real.exp (2 * y ⟨N, t'⟩) + Real.exp (-2 * y ⟨N, t'⟩)

private theorem gpd_psi_nonneg (y : Ω d) (t t' : d.Idx N × d.Idx N × Bool) :
    0 ≤ gpdPsi N y t t' := by unfold gpdPsi; positivity

private theorem gpd_exp_two_abs_le (x : ℝ) :
    Real.exp (2 * |x|) ≤ Real.exp (2 * x) + Real.exp (-2 * x) := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-2 * x)]
  · rw [abs_of_nonpos h, show 2 * -x = -2 * x by ring]; linarith [Real.exp_pos (2 * x)]

/-- `x² ≤ 2 e^{|x|}`. -/
private theorem gpd_sq_le_two_exp (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  rw [sq_abs] at h
  nlinarith [abs_nonneg x]

/-- The entry of `X` is bounded by its (at most four) raw coordinates. -/
private theorem gpd_norm_Xentry_le (y : Ω d) (i l : d.Idx N) :
    ‖Xmat d N y i l‖ ≤ |y ⟨N, (i, l, true)⟩| + |y ⟨N, (i, l, false)⟩|
      + (|y ⟨N, (l, i, true)⟩| + |y ⟨N, (l, i, false)⟩|) := by
  rw [Xmat_apply]
  unfold Xentry
  have h1 := abs_nonneg (y ⟨N, (i, l, true)⟩)
  have h2 := abs_nonneg (y ⟨N, (i, l, false)⟩)
  have h3 := abs_nonneg (y ⟨N, (l, i, true)⟩)
  have h4 := abs_nonneg (y ⟨N, (l, i, false)⟩)
  split_ifs
  · refine (norm_add_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith
  · refine (norm_sub_le _ _).trans ?_
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith
  · simp only [Complex.norm_real, Real.norm_eq_abs]
    linarith

/-- Off the truncation set, `2 Σ_t y_t² ≤ 2 e^{-N/4} Σ_{t,t'} ψ(t,t')`. -/
private theorem gpd_coordSq_le_of_not_good {y : Ω d} (hy : y ∉ gpdGood d N) :
    coordSq d N y ≤ Real.exp (-(N : ℝ) / 4) * ∑ t, ∑ t', gpdPsi N y t t' := by
  simp only [gpdGood, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨i, l, hil⟩ := hy
  have hent := gpd_norm_Xentry_le y i l
  -- one of the four coordinates exceeds `N/4`
  obtain ⟨t', ht'⟩ : ∃ t' : d.Idx N × d.Idx N × Bool, (N : ℝ) / 4 < |y ⟨N, t'⟩| := by
    by_contra hno
    push Not at hno
    have := hno (i, l, true); have := hno (i, l, false); have := hno (l, i, true)
    have := hno (l, i, false)
    linarith
  have hone : 1 ≤ Real.exp (|y ⟨N, t'⟩| - (N : ℝ) / 4) := Real.one_le_exp (by linarith)
  have hterm : ∀ t : d.Idx N × d.Idx N × Bool,
      (y ⟨N, t⟩) ^ 2 ≤ Real.exp (-(N : ℝ) / 4) * gpdPsi N y t t' := by
    intro t
    have h1 := gpd_sq_le_two_exp (y ⟨N, t⟩)
    have h2 : 2 * Real.exp |y ⟨N, t⟩| ≤ 2 * Real.exp |y ⟨N, t⟩|
        * Real.exp (|y ⟨N, t'⟩| - (N : ℝ) / 4) := by
      have : 0 ≤ 2 * Real.exp |y ⟨N, t⟩| := by positivity
      nlinarith
    have h3 : 2 * Real.exp |y ⟨N, t⟩| * Real.exp (|y ⟨N, t'⟩| - (N : ℝ) / 4)
        = Real.exp (-(N : ℝ) / 4) * (2 * (Real.exp |y ⟨N, t⟩| * Real.exp |y ⟨N, t'⟩|)) := by
      rw [Real.exp_sub]
      have : Real.exp ((N : ℝ) / 4) ≠ 0 := (Real.exp_pos _).ne'
      rw [show -(N : ℝ) / 4 = -((N : ℝ) / 4) by ring, Real.exp_neg]
      field_simp
    have h4 : 2 * (Real.exp |y ⟨N, t⟩| * Real.exp |y ⟨N, t'⟩|)
        ≤ Real.exp (2 * |y ⟨N, t⟩|) + Real.exp (2 * |y ⟨N, t'⟩|) := by
      have e1 : Real.exp (2 * |y ⟨N, t⟩|) = Real.exp |y ⟨N, t⟩| ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      have e2 : Real.exp (2 * |y ⟨N, t'⟩|) = Real.exp |y ⟨N, t'⟩| ^ 2 := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rw [e1, e2]
      nlinarith [sq_nonneg (Real.exp |y ⟨N, t⟩| - Real.exp |y ⟨N, t'⟩|)]
    have h5 : Real.exp (2 * |y ⟨N, t⟩|) + Real.exp (2 * |y ⟨N, t'⟩|) ≤ gpdPsi N y t t' := by
      unfold gpdPsi
      have := gpd_exp_two_abs_le (y ⟨N, t⟩)
      have := gpd_exp_two_abs_le (y ⟨N, t'⟩)
      linarith
    have hE : 0 ≤ Real.exp (-(N : ℝ) / 4) := (Real.exp_pos _).le
    calc (y ⟨N, t⟩) ^ 2 ≤ 2 * Real.exp |y ⟨N, t⟩| := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ Real.exp (-(N : ℝ) / 4) * gpdPsi N y t t' :=
          mul_le_mul_of_nonneg_left (h4.trans h5) hE
  unfold coordSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => (hterm t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  exact Finset.single_le_sum (f := fun t'' => gpdPsi N y t t'') (fun _ _ => gpd_psi_nonneg y t _)
    (Finset.mem_univ t')

private theorem gpd_integrable_psi (t t' : d.Idx N × d.Idx N × Bool) :
    Integrable (fun y : Ω d => gpdPsi N y t t') (gueUnit d) ∧
      ∫ y, gpdPsi N y t t' ∂(gueUnit d) ≤ 4 * Real.exp 2 := by
  obtain ⟨i1, j1⟩ := gpd_exp_coord (d := d) (N := N) 2 t
  obtain ⟨i2, j2⟩ := gpd_exp_coord (d := d) (N := N) (-2) t
  obtain ⟨i3, j3⟩ := gpd_exp_coord (d := d) (N := N) 2 t'
  obtain ⟨i4, j4⟩ := gpd_exp_coord (d := d) (N := N) (-2) t'
  have hint : Integrable (fun y : Ω d => gpdPsi N y t t') (gueUnit d) :=
    ((i1.add i2).add i3).add i4
  refine ⟨hint, ?_⟩
  unfold gpdPsi
  have i12 : Integrable (fun y : Ω d => Real.exp (2 * y ⟨N, t⟩) + Real.exp (-2 * y ⟨N, t⟩))
      (gueUnit d) := i1.add i2
  have i123 : Integrable (fun y : Ω d => Real.exp (2 * y ⟨N, t⟩) + Real.exp (-2 * y ⟨N, t⟩)
      + Real.exp (2 * y ⟨N, t'⟩)) (gueUnit d) := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2]
  have e : Real.exp ((2 : ℝ) ^ 2 / 2) = Real.exp 2 := by norm_num
  have e' : Real.exp ((-2 : ℝ) ^ 2 / 2) = Real.exp 2 := by norm_num
  rw [e] at j1 j3; rw [e'] at j2 j4
  linarith

/-- **Row Y3**: `‖B‖ ≤ 16 e² C₂ v S⁴ e^{-N/4}`. -/
private theorem gpd_norm_B_le {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C Φ C₀ C₁ C₂) {v : ℝ} (hv : 0 ≤ v) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖gpdB d N Φ v M‖ ≤ 16 * Real.exp 2 * C₂ * v * (Fintype.card (d.Idx N) : ℝ) ^ 4
      * Real.exp (-(N : ℝ) / 4) := by
  have hC2 : 0 ≤ C₂ := hΦ.nonneg₂
  set g : Ω d → ℝ := fun y => C₂ / 2 * v * (2 * (Real.exp (-(N : ℝ) / 4)
      * ∑ t, ∑ t', gpdPsi N y t t')) with hg
  have hgint : Integrable g (gueUnit d) := by
    refine ((integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
      (gpd_integrable_psi t t').1).const_mul _).const_mul _ |>.const_mul _
  have hpt : ∀ y, ‖(gpdGood d N)ᶜ.indicator (gpdR d N Φ v M) y‖ ≤ g y := by
    intro y
    have hg0 : 0 ≤ g y := by
      simp only [hg]
      have : 0 ≤ ∑ t, ∑ t', gpdPsi N y t t' :=
        Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun t' _ => gpd_psi_nonneg y t t'
      positivity
    by_cases hy : y ∈ gpdGood d N
    · rw [Set.indicator_of_notMem (by simpa using hy), norm_zero]; exact hg0
    · rw [Set.indicator_of_mem (by simpa using hy)]
      refine (gpd_norm_R_le hΦ hv M y).trans ?_
      have hX : ‖Xmat d N y‖ ^ 2 ≤ 2 * coordSq d N y :=
        (l2_opNorm_sq_le_frobSq _).trans (frobSq_Xmat_le y)
      have hc := gpd_coordSq_le_of_not_good hy
      have h0 : 0 ≤ C₂ / 2 * v := by positivity
      simp only [hg]
      exact mul_le_mul_of_nonneg_left (by linarith) h0
  refine (norm_integral_le_of_norm_le hgint (Eventually.of_forall hpt)).trans ?_
  have hsum : ∫ y, ∑ t, ∑ t', gpdPsi N y t t' ∂(gueUnit d)
      ≤ ((Fintype.card (d.Idx N × d.Idx N × Bool) : ℝ)) ^ 2 * (4 * Real.exp 2) := by
    rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun t' _ =>
      (gpd_integrable_psi t t').1]
    calc ∑ t, ∫ y, ∑ t', gpdPsi N y t t' ∂(gueUnit d)
        = ∑ t : d.Idx N × d.Idx N × Bool, ∑ t' : d.Idx N × d.Idx N × Bool,
            ∫ y, gpdPsi N y t t' ∂(gueUnit d) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact integral_finsetSum _ fun t' _ => (gpd_integrable_psi t t').1
      _ ≤ ∑ _t : d.Idx N × d.Idx N × Bool, ∑ _t' : d.Idx N × d.Idx N × Bool, 4 * Real.exp 2 :=
          Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun t' _ => (gpd_integrable_psi t t').2
      _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
  have hcard : ((Fintype.card (d.Idx N × d.Idx N × Bool) : ℕ) : ℝ)
      = 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 := by
    rw [Fintype.card_prod (d.Idx N) (d.Idx N × Bool), Fintype.card_prod (d.Idx N) Bool,
      Fintype.card_bool]; push_cast; ring
  rw [hcard] at hsum
  simp only [hg]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have hE : 0 ≤ Real.exp (-(N : ℝ) / 4) := (Real.exp_pos _).le
  have h0 : 0 ≤ C₂ / 2 * v := by positivity
  calc C₂ / 2 * v * (2 * (Real.exp (-(N : ℝ) / 4)
        * ∫ y, ∑ t, ∑ t', gpdPsi N y t t' ∂(gueUnit d)))
      ≤ C₂ / 2 * v * (2 * (Real.exp (-(N : ℝ) / 4)
        * ((2 * (Fintype.card (d.Idx N) : ℝ) ^ 2) ^ 2 * (4 * Real.exp 2)))) := by
        gcongr
    _ = _ := by ring

end Tail

/-! ### 7. The grid: measurability, freezing, and the D3 remainder

D3 is the remainder `r_j` of `condExp_loop_drift_gue` in the step `j → j+1`, bounded almost
surely through complex freezing. -/

section Grid

open scoped Matrix.Norms.L2Operator

variable {d : Dims}

private instance gpdStandardBorelMatrix (N : ℕ) :
    StandardBorelSpace (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  inferInstanceAs (StandardBorelSpace (d.Idx N → d.Idx N → ℂ))

private theorem gpd_measurable_coord {i k : ℕ} (h : i ≤ k) :
    Measurable[Grid.filt d k] (fun ω : Grid.Ωg d => ω i) := by
  have : (fun ω : Grid.Ωg d => ω i)
      = (fun g : Set.Iic k → Ω d => g ⟨i, h⟩) ∘ (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) :=
    rfl
  rw [this]
  exact (measurable_pi_apply (⟨i, h⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k))

private theorem gpd_gueH_measurable_filt (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) :
    Measurable[Grid.filt d k] (gueH d t1 t0 K N k) :=
  (@Matrix.measurable_iff (d.Idx N) (d.Idx N) ℂ _ (Grid.Ωg d) (Grid.filt d k)
      (fun ω => gueH d t1 t0 K N k ω)).mpr
    (fun i j => stronglyMeasurable_iff_measurable.mp (gueH_adapted d t1 t0 K N k i j))

private theorem gpd_gueH_succ (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (ω : Grid.Ωg d) :
    gueH d t1 t0 K N (k + 1) ω = gueH d t1 t0 K N k ω
      + Hflow d N (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) (ω (k + 1)) := by
  have hnotmem : (k + 1) ∉ Finset.Icc 1 k := by simp
  have hins : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  change gueH d t1 t0 K N (k + 1) ω = gueH d t1 t0 K N k ω
    + (Real.sqrt (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) : ℂ) • Xmat d N (ω (k + 1))
  unfold gueH
  rw [hins, Finset.sum_insert hnotmem, smul_add]
  abel

/-- Complex freezing under `Pgue` (real and imaginary parts of `gueCondExp_freeze`). -/
private theorem gpd_condExp_freezeC {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    (k : ℕ) {Y : Grid.Ωg d → β} (hY : Measurable[Grid.filt d k] Y)
    {F : β → Ω d → ℂ} (hF : Measurable (fun p : β × Ω d => F p.1 p.2))
    (hFInt : ∀ p, Integrable (F p) (gueUnit d))
    (hInt : Integrable (fun ω => F (Y ω) (ω (k + 1))) (Pgue d)) :
    (Pgue d)[fun ω => F (Y ω) (ω (k + 1)) | Grid.filt d k]
      =ᵐ[Pgue d] fun ω => ∫ x, F (Y ω) x ∂(gueUnit d) := by
  classical
  set f : Grid.Ωg d → ℂ := fun ω => F (Y ω) (ω (k + 1)) with hfdef
  set Fre : β → Ω d → ℝ := fun p x => RCLike.re (F p x) with hFredef
  set Fim : β → Ω d → ℝ := fun p x => RCLike.im (F p x) with hFimdef
  have hFre : Measurable (fun p : β × Ω d => Fre p.1 p.2) :=
    RCLike.continuous_re.measurable.comp hF
  have hFim : Measurable (fun p : β × Ω d => Fim p.1 p.2) :=
    RCLike.continuous_im.measurable.comp hF
  have hIntRe : Integrable (fun ω => Fre (Y ω) (ω (k + 1))) (Pgue d) := hInt.re
  have hIntIm : Integrable (fun ω => Fim (Y ω) (ω (k + 1))) (Pgue d) := hInt.im
  have hfreezeRe := gueCondExp_freeze k hY hFre hIntRe
  have hfreezeIm := gueCondExp_freeze k hY hFim hIntIm
  have hRe := (RCLike.reCLM (K := ℂ)).comp_condExp_comm (m := Grid.filt d k) hInt
  have hIm := (RCLike.imCLM (K := ℂ)).comp_condExp_comm (m := Grid.filt d k) hInt
  have hReComb : (fun ω => RCLike.re ((Pgue d)[f | Grid.filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fre (Y ω) x ∂(gueUnit d) := by
    have hRe' : (fun ω => RCLike.re ((Pgue d)[f | Grid.filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fre (Y ω) (ω (k + 1)) | Grid.filt d k] := hRe
    exact hRe'.trans hfreezeRe
  have hImComb : (fun ω => RCLike.im ((Pgue d)[f | Grid.filt d k] ω))
      =ᵐ[Pgue d] fun ω => ∫ x, Fim (Y ω) x ∂(gueUnit d) := by
    have hIm' : (fun ω => RCLike.im ((Pgue d)[f | Grid.filt d k] ω))
        =ᵐ[Pgue d] (Pgue d)[fun ω => Fim (Y ω) (ω (k + 1)) | Grid.filt d k] := hIm
    exact hIm'.trans hfreezeIm
  have hreEq : ∀ p, ∫ x, Fre p x ∂(gueUnit d) = RCLike.re (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_re (hFInt p)
  have himEq : ∀ p, ∫ x, Fim p x ∂(gueUnit d) = RCLike.im (∫ x, F p x ∂(gueUnit d)) :=
    fun p => integral_im (hFInt p)
  filter_upwards [hReComb, hImComb] with ω hωre hωim
  refine Complex.ext ?_ ?_
  · change RCLike.re ((Pgue d)[f | Grid.filt d k] ω) = RCLike.re (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωre, hreEq]
  · change RCLike.im ((Pgue d)[f | Grid.filt d k] ω) = RCLike.im (∫ x, F (Y ω) x ∂(gueUnit d))
    rw [hωim, himEq]

/-- The frozen conditional mean of the next loop minus the loop and its drift is
bounded by the remainder of `condExp_loop_drift_gue`, almost surely. -/
private theorem gpd_drift_remainder_ae (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (e : ℝ)
    (he : |e| < 2) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) (hn : 1 ≤ I.a.length)
    (ht1 : 0 ≤ t1 N) (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hk : k < K N) :
    ∀ᵐ ω ∂(Pgue d),
      ‖(∫ y, loopObs d N (zt e (Grid.time t1 t0 K N (k + 1))) I
            (gueH d t1 t0 K N k ω + Hflow d N (Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)) y)
            ∂(gueUnit d))
          - gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt e (Grid.time t1 t0 K N k)) I
          - (Grid.step t1 t0 K N : ℂ) *
              loopDriftGUE d e (Grid.time t1 t0 K N k) N I (gueH d t1 t0 K N k ω)‖
        ≤ (2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4) *
            (1 + ((zt e (Grid.time t1 t0 K N (k + 1))).im)⁻¹) ^ (I.length + 4) *
            Grid.step t1 t0 K N ^ ((3 : ℝ) / 2) := by
  set z1 := zt e (Grid.time t1 t0 K N (k + 1)) with hz1
  set v := Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ) with hv
  have hu1lt : Grid.time t1 t0 K N (k + 1) < 1 := by
    have hKpos : (0 : ℝ) < (K N : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
    have hk1 : (k : ℝ) + 1 ≤ (K N : ℝ) := by exact_mod_cast hk
    have hΔ0 : 0 ≤ Grid.step t1 t0 K N := by
      unfold Grid.step; exact div_nonneg (by linarith) hKpos.le
    have hKΔ : (K N : ℝ) * Grid.step t1 t0 K N = t0 N - t1 N := by unfold Grid.step; field_simp
    have h : Grid.time t1 t0 K N (k + 1) = t1 N + ((k : ℝ) + 1) * Grid.step t1 t0 K N := by
      unfold Grid.time; push_cast; ring
    rw [h]; nlinarith
  have hz1ne : z1.im ≠ 0 := zt_im_ne_zero_of_lt_one he hu1lt
  have hTF : TestFun d N (loopObs d N z1 I) :=
    testFun_loopObs_of_im_le hz1ne (abs_pos.mpr hz1ne) le_rfl hwf hn
  obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
  have hYmeas := gpd_gueH_measurable_filt (d := d) t1 t0 K N k
  have hFmeas : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      loopObs d N z1 I (p.1 + Hflow d N v p.2)) :=
    (hTF.contDiff.continuous.comp
      (continuous_fst.add ((continuous_Hflow d N v).comp continuous_snd))).measurable
  have hFInt : ∀ p : Matrix (d.Idx N) (d.Idx N) ℂ,
      Integrable (fun x => loopObs d N z1 I (p + Hflow d N v x)) (gueUnit d) := fun p =>
    (memLp_top_of_bound ((hTF.contDiff.continuous.comp
      (continuous_const.add (continuous_Hflow d N v))).aestronglyMeasurable) C₀
      (Eventually.of_forall fun x => hC₀ _)).integrable le_top
  have hIntTarget : Integrable
      (fun ω : Grid.Ωg d => loopObs d N z1 I (gueH d t1 t0 K N k ω + Hflow d N v (ω (k + 1))))
      (Pgue d) :=
    (memLp_top_of_bound ((hTF.contDiff.continuous.measurable.comp
      ((gueH_measurable d t1 t0 K N k).add
        ((continuous_Hflow d N v).measurable.comp
          (measurable_pi_apply (k + 1))))).aestronglyMeasurable)
      C₀ (Eventually.of_forall fun ω => hC₀ _)).integrable le_top
  have hfreeze := gpd_condExp_freezeC k hYmeas hFmeas hFInt hIntTarget
  have hEq : (fun ω' : Grid.Ωg d => loopObs d N z1 I (gueH d t1 t0 K N (k + 1) ω'))
      = fun ω => loopObs d N z1 I (gueH d t1 t0 K N k ω + Hflow d N v (ω (k + 1))) := by
    funext ω; rw [gpd_gueH_succ]
  have hD3 := condExp_loop_drift_gue d t1 t0 K N k e he hwf hn ht1 hst ht0 hk
  rw [hEq] at hD3
  filter_upwards [hD3, hfreeze] with ω h1 h2
  rw [h2] at h1
  rw [← loopObs_of_isHermitian (gueH_isHermitian d t1 t0 K N k ω)]
  rw [← smul_eq_mul]
  exact h1

end Grid

/-! ### 8. The linear part: dyadic stopping levels and Azuma (N1, rows M1–M4) -/

section AzumaZ

open scoped Matrix.Norms.L2Operator

variable {d : Dims}

private theorem gpd_measurable_gradMat (N : ℕ) (Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ) :
    Measurable (Grid.gradMat Φ) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  simp only [Grid.gradMat, Matrix.of_apply, wirtFirst, coordD1]
  split_ifs
  · exact measurable_fderiv_apply_const ℝ Φ _
  · exact (measurable_const.mul ((measurable_fderiv_apply_const ℝ Φ _).sub
      (measurable_const.mul (measurable_fderiv_apply_const ℝ Φ _))))

private theorem gpd_lin_eq_sum (A X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    Grid.lin (d := d) N A X = ∑ i : d.Idx N, ∑ k : d.Idx N, (A i k * X k i).re := by
  unfold Grid.lin
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]

private theorem gpd_measurable_lin (N : ℕ) :
    Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      Grid.lin (d := d) N p.1 p.2) := by
  have heq : (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Matrix (d.Idx N) (d.Idx N) ℂ =>
        Grid.lin (d := d) N p.1 p.2)
      = fun p => ∑ i : d.Idx N, ∑ k : d.Idx N, (p.1 i k * p.2 k i).re :=
    funext fun p => gpd_lin_eq_sum p.1 p.2
  rw [heq]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hM : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      p.1 i k) := Measurable.eval_matrix (i := i) (j := k) measurable_fst
  have hX : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      p.2 k i) := Measurable.eval_matrix (i := k) (j := i) measurable_snd
  exact Complex.measurable_re.comp (hM.mul hX)

private theorem gpd_measurable_vGue (N : ℕ) :
    Measurable (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => (vGue d N A : ℝ)) := by
  have heq : (fun A : Matrix (d.Idx N) (d.Idx N) ℂ => (vGue d N A : ℝ))
      = fun A => ∑ c ∈ Grid.coordFinset (d := d) N,
          (Grid.lin (d := d) N A (Xmat d N (Pi.single c 1))) ^ 2 * (gueUnitVar d c : ℝ) := by
    funext A; unfold vGue linVar; push_cast [NNReal.coe_mk]; rfl
  rw [heq]
  refine Finset.measurable_sum _ fun c _ => ?_
  have h1 : Measurable (fun A : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (A, Xmat d N (Pi.single c 1))) := measurable_id.prodMk measurable_const
  have h2 := (gpd_measurable_lin (d := d) N).comp h1
  exact (h2.pow_const 2).mul_const _

variable (d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (e : ℝ) (I : LoopIdx (ZMod (d.L N)))

/-- The observable of the step `j → j+1` (at the spectral parameter of time `u_{j+1}`). -/
private def gpdPhi (j : ℕ) : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
  loopObs d N (zt e (Grid.time t1 t0 K N (j + 1))) I

/-- The variance `Δ/S` of one GUE increment. -/
private def gpdv : ℝ := Grid.step t1 t0 K N / (ouMatrixSize d N : ℝ)

/-- The `F_j`-measurable gradient direction. -/
private def gpdA (j : ℕ) (ω : Grid.Ωg d) : Matrix (d.Idx N) (d.Idx N) ℂ :=
  Grid.gradMat (gpdPhi d t1 t0 K N e I j) (gueH d t1 t0 K N j ω)

/-- **Row M1**: the conditional variance proxy of the linear part. -/
private def gpdVp (j : ℕ) (ω : Grid.Ωg d) : ℝ :=
  gpdv d t1 t0 K N * max (vGue d N (gpdA d t1 t0 K N e I j ω) : ℝ)
    (vGue d N (-Complex.I • gpdA d t1 t0 K N e I j ω) : ℝ)

/-- The linear part of the step `j → j+1`. -/
private def gpdZinc (j : ℕ) (ω : Grid.Ωg d) : ℂ :=
  gpdZ d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) (gueH d t1 t0 K N j ω) (ω (j + 1))

/-- The linear part, stopped at the dyadic level `lam` (index `0` carries `0`). -/
private def gpdZst (lam : ℝ) : ℕ → Grid.Ωg d → ℂ
  | 0 => fun _ => 0
  | j + 1 => {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
      (gpdZinc d t1 t0 K N e I j)

variable {d t1 t0 K N e I}

private theorem gpd_adapted_Vp :
    Adapted (Grid.filt d) (gpdVp d t1 t0 K N e I) := by
  intro j
  have hA : Measurable[Grid.filt d j] (gpdA d t1 t0 K N e I j) :=
    (gpd_measurable_gradMat N _).comp (gpd_gueH_measurable_filt t1 t0 K N j)
  have hA' : Measurable[Grid.filt d j] (fun ω => -Complex.I • gpdA d t1 t0 K N e I j ω) := by
    change Measurable[Grid.filt d j] ((-Complex.I) • gpdA d t1 t0 K N e I j)
    exact hA.const_smul _
  exact (measurable_const.mul (((gpd_measurable_vGue N).comp hA).max
    ((gpd_measurable_vGue N).comp hA')))

private theorem gpd_Zst_re_im (lam : ℝ) (j : ℕ) (ω : Grid.Ωg d) :
    (gpdZst d t1 t0 K N e I lam (j + 1) ω).re
        = {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
          (fun ω => Real.sqrt (gpdv d t1 t0 K N) * Grid.lin (d := d) N
            (gpdA d t1 t0 K N e I j ω) (Xmat d N (ω (j + 1)))) ω ∧
      (gpdZst d t1 t0 K N e I lam (j + 1) ω).im
        = {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
          (fun ω => Real.sqrt (gpdv d t1 t0 K N) * Grid.lin (d := d) N
            (-Complex.I • gpdA d t1 t0 K N e I j ω) (Xmat d N (ω (j + 1)))) ω := by
  simp only [gpdZst, Set.indicator]
  split_ifs
  · exact gpd_Z_re_im _ _ _
  · simp

/-- A stopped linear increment is `F_{j+1}`-measurable. -/
private theorem gpd_sm_indicator_lin {j : ℕ} {E : Set (Grid.Ωg d)}
    (hE : MeasurableSet[Grid.filt d j] E) {A : Grid.Ωg d → Matrix (d.Idx N) (d.Idx N) ℂ}
    (hA : Measurable[Grid.filt d j] A) (s : ℝ) :
    StronglyMeasurable[Grid.filt d (j + 1)]
      (E.indicator (fun ω => s * Grid.lin (d := d) N (A ω) (Xmat d N (ω (j + 1))))) := by
  have hle : Grid.filt d j ≤ Grid.filt d (j + 1) := (Grid.filt d).mono (Nat.le_succ j)
  have hX : Measurable[Grid.filt d (j + 1)] (fun ω : Grid.Ωg d => Xmat d N (ω (j + 1))) :=
    (measurable_Xmat d N).comp (gpd_measurable_coord le_rfl)
  have hA1 : Measurable[Grid.filt d (j + 1)] A := hA.mono hle le_rfl
  have hp := hA1.prodMk hX
  have hl := (gpd_measurable_lin (d := d) N).comp hp
  have hm : Measurable[Grid.filt d (j + 1)]
      (fun ω : Grid.Ωg d => s * Grid.lin (d := d) N (A ω) (Xmat d N (ω (j + 1)))) :=
    measurable_const.mul hl
  have hE1 : MeasurableSet[Grid.filt d (j + 1)] E := hle _ hE
  exact (hm.indicator hE1).stronglyMeasurable

private theorem gpd_stronglyAdapted_Zst (lam : ℝ) :
    StronglyAdapted (Grid.filt d) (fun i ω => (gpdZst d t1 t0 K N e I lam i ω).re) ∧
      StronglyAdapted (Grid.filt d) (fun i ω => (gpdZst d t1 t0 K N e I lam i ω).im) := by
  have hE : ∀ j, MeasurableSet[Grid.filt d j]
      {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω} :=
    fun j => Grid.lt_firstHit_measurableSet _ lam (K N) gpd_adapted_Vp j
  have hA : ∀ j, Measurable[Grid.filt d j] (gpdA d t1 t0 K N e I j) := fun j =>
    (gpd_measurable_gradMat N _).comp (gpd_gueH_measurable_filt t1 t0 K N j)
  have hA' : ∀ j, Measurable[Grid.filt d j] (fun ω => -Complex.I • gpdA d t1 t0 K N e I j ω) :=
    fun j => by
      change Measurable[Grid.filt d j] ((-Complex.I) • gpdA d t1 t0 K N e I j)
      exact (hA j).const_smul _
  constructor
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · have heq : (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).re)
          = {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
            (fun ω => Real.sqrt (gpdv d t1 t0 K N) * Grid.lin (d := d) N
              (gpdA d t1 t0 K N e I j ω) (Xmat d N (ω (j + 1)))) :=
        funext fun ω => (gpd_Zst_re_im lam j ω).1
      change StronglyMeasurable[Grid.filt d (j + 1)]
        (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).re)
      rw [heq]
      exact gpd_sm_indicator_lin (hE j) (hA j) _
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · have heq : (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).im)
          = {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
            (fun ω => Real.sqrt (gpdv d t1 t0 K N) * Grid.lin (d := d) N
              (-Complex.I • gpdA d t1 t0 K N e I j ω) (Xmat d N (ω (j + 1)))) :=
        funext fun ω => (gpd_Zst_re_im lam j ω).2
      change StronglyMeasurable[Grid.filt d (j + 1)]
        (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).im)
      rw [heq]
      exact gpd_sm_indicator_lin (hE j) (hA' j) _

private theorem gpd_condSubG_Zst {lam : ℝ} (hlam : 0 ≤ lam) (hv : 0 ≤ gpdv d t1 t0 K N)
    (j : ℕ) :
    HasCondSubgaussianMGF (Grid.filt d j) ((Grid.filt d).le j)
        (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).re) ⟨lam, hlam⟩ (Pgue d) ∧
      HasCondSubgaussianMGF (Grid.filt d j) ((Grid.filt d).le j)
        (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).im) ⟨lam, hlam⟩ (Pgue d) := by
  have hE : MeasurableSet[Grid.filt d j]
      {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω} :=
    Grid.lt_firstHit_measurableSet _ lam (K N) gpd_adapted_Vp j
  have hA : Measurable[Grid.filt d j] (gpdA d t1 t0 K N e I j) :=
    (gpd_measurable_gradMat N _).comp (gpd_gueH_measurable_filt t1 t0 K N j)
  have hsq : Real.sqrt (gpdv d t1 t0 K N) ^ 2 = gpdv d t1 t0 K N := Real.sq_sqrt hv
  have hb1 : ∀ ω ∈ {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω},
      Real.sqrt (gpdv d t1 t0 K N) ^ 2 * (vGue d N (gpdA d t1 t0 K N e I j ω) : ℝ)
        ≤ ((⟨lam, hlam⟩ : ℝ≥0) : ℝ) := by
    intro ω hω
    have h := Grid.lt_firstHit_imp (gpdVp d t1 t0 K N e I) lam (K N) hω
    rw [hsq]
    refine le_trans ?_ h.le
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hv
  have hb2 : ∀ ω ∈ {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω},
      Real.sqrt (gpdv d t1 t0 K N) ^ 2 * (vGue d N (-Complex.I • gpdA d t1 t0 K N e I j ω) : ℝ)
        ≤ ((⟨lam, hlam⟩ : ℝ≥0) : ℝ) := by
    intro ω hω
    have h := Grid.lt_firstHit_imp (gpdVp d t1 t0 K N e I) lam (K N) hω
    rw [hsq]
    refine le_trans ?_ h.le
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hv
  have h1 := gueHasCondSubgaussianMGF_linear N j (Real.sqrt (gpdv d t1 t0 K N)) hA _ hE _ hb1
  have hA' : Measurable[Grid.filt d j] (fun ω => -Complex.I • gpdA d t1 t0 K N e I j ω) := by
    change Measurable[Grid.filt d j] ((-Complex.I) • gpdA d t1 t0 K N e I j)
    exact hA.const_smul _
  have h2 := gueHasCondSubgaussianMGF_linear N j (Real.sqrt (gpdv d t1 t0 K N)) hA' _ hE _ hb2
  constructor
  · have heq : (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).re)
        = fun ω => {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
            (fun ω => Real.sqrt (gpdv d t1 t0 K N) * Grid.lin (d := d) N
              (gpdA d t1 t0 K N e I j ω) (Xmat d N (ω (j + 1)))) ω :=
      funext fun ω => (gpd_Zst_re_im lam j ω).1
    rw [heq]; exact h1
  · have heq : (fun ω => (gpdZst d t1 t0 K N e I lam (j + 1) ω).im)
        = fun ω => {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I) lam (K N) ω}.indicator
            (fun ω => Real.sqrt (gpdv d t1 t0 K N) * Grid.lin (d := d) N
              (-Complex.I • gpdA d t1 t0 K N e I j ω) (Xmat d N (ω (j + 1)))) ω :=
      funext fun ω => (gpd_Zst_re_im lam j ω).2
    rw [heq]; exact h2

/-- **Azuma at one dyadic level** (row M4). -/
private theorem gpd_azuma_Z {lam : ℝ} (hlam : 0 < lam) (hv : 0 ≤ gpdv d t1 t0 K N) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue d).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, gpdZst d t1 t0 K N e I lam (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * lam))) := by
  set c : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else ⟨lam, hlam.le⟩ with hc
  obtain ⟨hR, hI⟩ := gpd_stronglyAdapted_Zst (d := d) (t1 := t1) (t0 := t0) (K := K) (N := N)
    (e := e) (I := I) lam
  have h0 : HasSubgaussianMGF (fun ω => (gpdZst d t1 t0 K N e I lam 0 ω).re) (c 0) (Pgue d) := by
    simp only [hc, gpdZst, Complex.zero_re]
    exact HasSubgaussianMGF.zero
  have h0' : HasSubgaussianMGF (fun ω => (gpdZst d t1 t0 K N e I lam 0 ω).im) (c 0) (Pgue d) := by
    simp only [hc, gpdZst, Complex.zero_im]
    exact HasSubgaussianMGF.zero
  have hCR : ∀ i < (k + 1) - 1, HasCondSubgaussianMGF (Grid.filt d i) ((Grid.filt d).le i)
      (fun ω => (gpdZst d t1 t0 K N e I lam (i + 1) ω).re) (c (i + 1)) (Pgue d) := by
    intro i _
    simp only [hc, Nat.succ_ne_zero]
    exact (gpd_condSubG_Zst hlam.le hv i).1
  have hCI : ∀ i < (k + 1) - 1, HasCondSubgaussianMGF (Grid.filt d i) ((Grid.filt d).le i)
      (fun ω => (gpdZst d t1 t0 K N e I lam (i + 1) ω).im) (c (i + 1)) (Pgue d) := by
    intro i _
    simp only [hc, Nat.succ_ne_zero]
    exact (gpd_condSubG_Zst hlam.le hv i).2
  have haz := Grid.azuma_complex (μ := Pgue d) (ℱ := Grid.filt d)
    (Z := gpdZst d t1 t0 K N e I lam) (c := c) hR hI (k + 1) h0 h0' hCR hCI hε
  have hsumZ : ∀ ω, ∑ i ∈ Finset.range (k + 1), gpdZst d t1 t0 K N e I lam i ω
      = ∑ j ∈ Finset.range k, gpdZst d t1 t0 K N e I lam (j + 1) ω := by
    intro ω
    rw [Finset.sum_range_succ']
    simp [gpdZst]
  have hsumc : ((∑ i ∈ Finset.range (k + 1), c i : ℝ≥0) : ℝ) = k * lam := by
    rw [NNReal.coe_sum, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range k, (c (i + 1) : ℝ) = lam := fun i _ => by simp [hc]; rfl
    rw [Finset.sum_congr rfl this]
    simp [hc]
  simp only [hsumZ, hsumc] at haz
  exact haz

end AzumaZ

/-! ### 9. The remainder part: adapted truncation and conditional Hoeffding (rows Y1–Y2) -/

section AzumaY

open scoped Matrix.Norms.L2Operator

variable {d : Dims}

/-- The loop observable of a step before the horizon is `C²` with explicit constants. -/
private theorem gpd_bddC2C_Phi {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} {e : ℝ}
    {I : LoopIdx (ZMod (d.L N))} (he : |e| < 2) (hwf : I.WF)
    (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) {j : ℕ} (hj : j < K N) :
    (zt e (Grid.time t1 t0 K N (j + 1))).im ≠ 0 ∧
      BddC2C (gpdPhi d t1 t0 K N e I j)
        ((Fintype.card (d.Idx N) : ℝ) *
          (2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3) ^ I.a.length)
        ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) *
          (2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3) ^ I.a.length))
        ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2 *
          (2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3) ^ I.a.length)) := by
  have hu1lt : Grid.time t1 t0 K N (j + 1) < 1 := by
    have hKpos : (0 : ℝ) < (K N : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le j) hj)
    have hk1 : (j : ℝ) + 1 ≤ (K N : ℝ) := by exact_mod_cast hj
    have hΔ0 : 0 ≤ Grid.step t1 t0 K N := by
      unfold Grid.step; exact div_nonneg (by linarith) hKpos.le
    have hKΔ : (K N : ℝ) * Grid.step t1 t0 K N = t0 N - t1 N := by unfold Grid.step; field_simp
    have h : Grid.time t1 t0 K N (j + 1) = t1 N + ((j : ℝ) + 1) * Grid.step t1 t0 K N := by
      unfold Grid.time; push_cast; ring
    rw [h]; nlinarith
  have hz : (zt e (Grid.time t1 t0 K N (j + 1))).im ≠ 0 := zt_im_ne_zero_of_lt_one he hu1lt
  have hη : 0 < |(zt e (Grid.time t1 t0 K N (j + 1))).im| := abs_pos.mpr hz
  obtain ⟨hBa, hBb, hBc⟩ := le_two_mul_one_add_inv_cube hη
  exact ⟨hz, bddC2C_loopObs hz hη le_rfl hBa hBb hBc hwf⟩

variable (d) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (e : ℝ) (I : LoopIdx (ZMod (d.L N)))

/-- The frozen, recentred, truncated remainder of the step `j → j+1`. -/
private def gpdFY (j : ℕ) (M : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) : ℂ :=
  gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y
    - ∫ y', gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y' ∂(gueUnit d)

/-- The martingale increments `Ỹ` (cut off after the grid horizon). -/
private def gpdYst : ℕ → Grid.Ωg d → ℂ
  | 0 => fun _ => 0
  | j + 1 => fun ω => if j < K N then
      gpdFY d t1 t0 K N e I j (gueH d t1 t0 K N j ω) (ω (j + 1)) else 0

variable {d t1 t0 K N e I}

private theorem gpd_measurable_FY {j : ℕ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C (gpdPhi d t1 t0 K N e I j) C₀ C₁ C₂) :
    Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      gpdFY d t1 t0 K N e I j p.1 p.2) := by
  have hR := gpd_continuous_R (d := d) (N := N) hΦ (gpdv d t1 t0 K N)
  have hTeq : (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
        gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) p.1 p.2)
      = (Set.univ ×ˢ gpdGood d N).indicator
          (fun p => gpdR d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) p.1 p.2) := by
    funext p
    by_cases h : p.2 ∈ gpdGood d N
    · have h' : p ∈ (Set.univ : Set (Matrix (d.Idx N) (d.Idx N) ℂ)) ×ˢ gpdGood d N :=
        Set.mk_mem_prod (Set.mem_univ _) h
      simp only [gpdT, Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : p ∉ (Set.univ : Set (Matrix (d.Idx N) (d.Idx N) ℂ)) ×ˢ gpdGood d N :=
        fun hp => h (Set.mem_prod.1 hp).2
      simp only [gpdT, Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hT : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) p.1 p.2) := by
    rw [hTeq]
    exact hR.measurable.indicator (MeasurableSet.univ.prod gpd_measurableSet_good)
  have hInt : StronglyMeasurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      ∫ y', gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y' ∂(gueUnit d)) :=
    hT.stronglyMeasurable.integral_prod_right'
  exact hT.sub (hInt.measurable.comp measurable_fst)

private theorem gpd_bound_FY {j : ℕ} {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C (gpdPhi d t1 t0 K N e I j) C₀ C₁ C₂) {b : ℝ}
    (hb : ∀ M y, ‖gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y‖ ≤ b)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    (∀ y, ‖gpdFY d t1 t0 K N e I j M y‖ ≤ 2 * b) ∧
      ∫ y, gpdFY d t1 t0 K N e I j M y ∂(gueUnit d) = 0 ∧
      Integrable (gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M) (gueUnit d) := by
  have hTmeas := (gpd_measurable_FY (N := N) hΦ)
  have hTm : Measurable (gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M) := by
    have hR := (gpd_continuous_R (d := d) (N := N) hΦ (gpdv d t1 t0 K N)).comp
      (continuous_const.prodMk continuous_id : Continuous fun y : Ω d => (M, y))
    exact hR.measurable.indicator gpd_measurableSet_good
  have hTint : Integrable (gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M)
      (gueUnit d) :=
    (memLp_top_of_bound hTm.aestronglyMeasurable b
      (Eventually.of_forall fun y => hb M y)).integrable le_top
  have hI : ‖∫ y', gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y' ∂(gueUnit d)‖
      ≤ b := by
    have h := norm_integral_le_of_norm_le_const (μ := gueUnit d)
      (Eventually.of_forall fun y => hb M y)
    simpa using h
  refine ⟨fun y => ?_, ?_, hTint⟩
  · unfold gpdFY
    refine (norm_sub_le _ _).trans ?_
    linarith [hb M y]
  · unfold gpdFY
    rw [integral_sub hTint (integrable_const _), integral_const]
    simp

/-- **Conditional Hoeffding for `Ỹ`** (row Y2). -/
private theorem gpd_condSubG_Yst {j : ℕ} (hj : j < K N) {C₀ C₁ C₂ : ℝ}
    (hΦ : BddC2C (gpdPhi d t1 t0 K N e I j) C₀ C₁ C₂) {b : ℝ}
    (hb : ∀ M y, ‖gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y‖ ≤ b) :
    HasCondSubgaussianMGF (Grid.filt d j) ((Grid.filt d).le j)
        (fun ω => (gpdYst d t1 t0 K N e I (j + 1) ω).re) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue d) ∧
      HasCondSubgaussianMGF (Grid.filt d j) ((Grid.filt d).le j)
        (fun ω => (gpdYst d t1 t0 K N e I (j + 1) ω).im) ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2)
        (Pgue d) := by
  have hF := gpd_measurable_FY (N := N) hΦ
  have hY := gpd_gueH_measurable_filt (d := d) t1 t0 K N j
  have hsub : ∀ (g : ℂ → ℝ), Continuous g → (∀ w : ℂ, |g w| ≤ ‖w‖) →
      (∀ M, ∫ y, g (gpdFY d t1 t0 K N e I j M y) ∂(gueUnit d) = 0) →
      ∀ M, HasSubgaussianMGF (fun y => g (gpdFY d t1 t0 K N e I j M y))
        ((‖2 * b - -(2 * b)‖₊ / 2) ^ 2) (gueUnit d) := by
    intro g hg hgb h0 M
    obtain ⟨hB, _, _⟩ := gpd_bound_FY hΦ hb M
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero ?_ ?_ (h0 M)
    · exact (hg.measurable.comp (hF.comp (measurable_const.prodMk measurable_id))).aemeasurable
    · refine Eventually.of_forall fun y => ?_
      have h1 := (hgb _).trans (hB y)
      exact ⟨by linarith [neg_abs_le (g (gpdFY d t1 t0 K N e I j M y))],
        by linarith [le_abs_self (g (gpdFY d t1 t0 K N e I j M y))]⟩
  have hre0 : ∀ M, ∫ y, (gpdFY d t1 t0 K N e I j M y).re ∂(gueUnit d) = 0 := by
    intro M
    obtain ⟨_, hint0, hTint⟩ := gpd_bound_FY hΦ hb M
    have hFint : Integrable (gpdFY d t1 t0 K N e I j M) (gueUnit d) :=
      hTint.sub (integrable_const _)
    have := integral_re hFint
    rw [hint0] at this
    simpa using this
  have him0 : ∀ M, ∫ y, (gpdFY d t1 t0 K N e I j M y).im ∂(gueUnit d) = 0 := by
    intro M
    obtain ⟨_, hint0, hTint⟩ := gpd_bound_FY hΦ hb M
    have hFint : Integrable (gpdFY d t1 t0 K N e I j M) (gueUnit d) :=
      hTint.sub (integrable_const _)
    have := integral_im hFint
    rw [hint0] at this
    simpa using this
  have hsre := hsub Complex.re Complex.continuous_re Complex.abs_re_le_norm hre0
  have hsim := hsub Complex.im Complex.continuous_im Complex.abs_im_le_norm him0
  have hFre : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      (gpdFY d t1 t0 K N e I j p.1 p.2).re) := Complex.measurable_re.comp hF
  have hFim : Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Ω d =>
      (gpdFY d t1 t0 K N e I j p.1 p.2).im) := Complex.measurable_im.comp hF
  have h1 := gueHasCondSubgaussianMGF_of_frozen j hY hFre hsre
  have h2 := gueHasCondSubgaussianMGF_of_frozen j hY hFim hsim
  have heq1 : (fun ω => (gpdYst d t1 t0 K N e I (j + 1) ω).re)
      = fun ω => (gpdFY d t1 t0 K N e I j (gueH d t1 t0 K N j ω) (ω (j + 1))).re := by
    funext ω; simp [gpdYst, hj]
  have heq2 : (fun ω => (gpdYst d t1 t0 K N e I (j + 1) ω).im)
      = fun ω => (gpdFY d t1 t0 K N e I j (gueH d t1 t0 K N j ω) (ω (j + 1))).im := by
    funext ω; simp [gpdYst, hj]
  rw [heq1, heq2]
  exact ⟨h1, h2⟩

private theorem gpd_stronglyAdapted_Yst (he : |e| < 2) (hwf : I.WF) (hst : t1 N ≤ t0 N)
    (ht0 : t0 N < 1) :
    StronglyAdapted (Grid.filt d) (fun i ω => (gpdYst d t1 t0 K N e I i ω).re) ∧
      StronglyAdapted (Grid.filt d) (fun i ω => (gpdYst d t1 t0 K N e I i ω).im) := by
  have key : ∀ j, Measurable[Grid.filt d (j + 1)] (gpdYst d t1 t0 K N e I (j + 1)) := by
    intro j
    by_cases hj : j < K N
    · obtain ⟨_, hΦ⟩ := gpd_bddC2C_Phi (d := d) (t1 := t1) (t0 := t0) (K := K) he hwf hst ht0 hj
      have hF := gpd_measurable_FY (N := N) (e := e) (I := I) hΦ
      have hle : Grid.filt d j ≤ Grid.filt d (j + 1) := (Grid.filt d).mono (Nat.le_succ j)
      have hY : Measurable[Grid.filt d (j + 1)] (gueH d t1 t0 K N j) :=
        (gpd_gueH_measurable_filt t1 t0 K N j).mono hle le_rfl
      have hc : Measurable[Grid.filt d (j + 1)] (fun ω : Grid.Ωg d => ω (j + 1)) :=
        gpd_measurable_coord le_rfl
      have hp := hY.prodMk hc
      have hcomp := hF.comp hp
      have heq : gpdYst d t1 t0 K N e I (j + 1)
          = fun ω => gpdFY d t1 t0 K N e I j (gueH d t1 t0 K N j ω) (ω (j + 1)) := by
        funext ω; simp [gpdYst, hj]
      rw [heq]; exact hcomp
    · have heq : gpdYst d t1 t0 K N e I (j + 1) = fun _ => 0 := by
        funext ω; simp [gpdYst, hj]
      rw [heq]; exact measurable_const
  constructor
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · exact (Complex.measurable_re.comp (key j)).stronglyMeasurable
  · intro i
    rcases i with _ | j
    · exact stronglyMeasurable_const
    · exact (Complex.measurable_im.comp (key j)).stronglyMeasurable

/-- **Azuma for `Ỹ`** (row Y2). -/
private theorem gpd_azuma_Y (he : |e| < 2) (hwf : I.WF) (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1)
    {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j < K N, ∀ M y,
      ‖gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y‖ ≤ b)
    {k : ℕ} (hk : k ≤ K N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue d).real {ω | ε ≤ ‖∑ j ∈ Finset.range k, gpdYst d t1 t0 K N e I (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * (4 * b ^ 2)))) := by
  set P : ℝ≥0 := (‖2 * b - -(2 * b)‖₊ / 2) ^ 2 with hP
  have hPval : (P : ℝ) = 4 * b ^ 2 := by
    rw [hP]
    push_cast
    rw [Real.norm_eq_abs, show 2 * b - -(2 * b) = 4 * b by ring,
      abs_of_nonneg (by linarith)]
    ring
  set c : ℕ → ℝ≥0 := fun i => if i = 0 then 0 else P with hc
  obtain ⟨hR, hI⟩ := gpd_stronglyAdapted_Yst (d := d) (t1 := t1) (t0 := t0) (K := K) (N := N)
    (e := e) (I := I) he hwf hst ht0
  have h0 : HasSubgaussianMGF (fun ω => (gpdYst d t1 t0 K N e I 0 ω).re) (c 0) (Pgue d) := by
    simp only [hc, gpdYst, Complex.zero_re]
    exact HasSubgaussianMGF.zero
  have h0' : HasSubgaussianMGF (fun ω => (gpdYst d t1 t0 K N e I 0 ω).im) (c 0) (Pgue d) := by
    simp only [hc, gpdYst, Complex.zero_im]
    exact HasSubgaussianMGF.zero
  have hsub : ∀ i < (k + 1) - 1,
      HasCondSubgaussianMGF (Grid.filt d i) ((Grid.filt d).le i)
        (fun ω => (gpdYst d t1 t0 K N e I (i + 1) ω).re) (c (i + 1)) (Pgue d) ∧
      HasCondSubgaussianMGF (Grid.filt d i) ((Grid.filt d).le i)
        (fun ω => (gpdYst d t1 t0 K N e I (i + 1) ω).im) (c (i + 1)) (Pgue d) := by
    intro i hi
    have hiK : i < K N := by omega
    obtain ⟨_, hΦ⟩ := gpd_bddC2C_Phi (d := d) (t1 := t1) (t0 := t0) (K := K) he hwf hst ht0 hiK
    simp only [hc, Nat.succ_ne_zero]
    exact gpd_condSubG_Yst hiK hΦ (hb i hiK)
  have haz := Grid.azuma_complex (μ := Pgue d) (ℱ := Grid.filt d)
    (Z := gpdYst d t1 t0 K N e I) (c := c) hR hI (k + 1) h0 h0'
    (fun i hi => (hsub i hi).1) (fun i hi => (hsub i hi).2) hε
  have hsumZ : ∀ ω, ∑ i ∈ Finset.range (k + 1), gpdYst d t1 t0 K N e I i ω
      = ∑ j ∈ Finset.range k, gpdYst d t1 t0 K N e I (j + 1) ω := by
    intro ω
    rw [Finset.sum_range_succ']
    simp [gpdYst]
  have hsumc : ((∑ i ∈ Finset.range (k + 1), c i : ℝ≥0) : ℝ) = k * (4 * b ^ 2) := by
    rw [NNReal.coe_sum, Finset.sum_range_succ']
    have : ∀ i ∈ Finset.range k, (c (i + 1) : ℝ) = 4 * b ^ 2 := fun i _ => by
      simp only [hc, Nat.succ_ne_zero, ite_false]; exact hPval
    rw [Finset.sum_congr rfl this]
    simp [hc]
  simp only [hsumZ, hsumc] at haz
  exact haz

end AzumaY

/-! ### 10. The pathwise decomposition of one step, and the dyadic level choice -/

section Decomp

open scoped Matrix.Norms.L2Operator

variable (d : Dims) (t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (e : ℝ) (I : LoopIdx (ZMod (d.L N)))

/-- The D3 remainder of the step `j → j+1`. -/
private def gpdr (j : ℕ) (ω : Grid.Ωg d) : ℂ :=
  (∫ y, gpdPhi d t1 t0 K N e I j (gueH d t1 t0 K N j ω + Hflow d N (gpdv d t1 t0 K N) y)
      ∂(gueUnit d))
    - gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j)) I
    - (Grid.step t1 t0 K N : ℂ) * loopDriftGUE d e (Grid.time t1 t0 K N j) N I
        (gueH d t1 t0 K N j ω)

variable {d t1 t0 K N e I}

/-- **One step, pathwise**, on the truncation set of the new increment. -/
private theorem gpd_step_decomp (he : |e| < 2) (hwf : I.WF) (hst : t1 N ≤ t0 N)
    (ht0 : t0 N < 1) {j : ℕ} (hj : j < K N) (ω : Grid.Ωg d) (hgood : ω (j + 1) ∈ gpdGood d N) :
    gloop (d.L N) (d.W N) (gueH d t1 t0 K N (j + 1) ω) (zt e (Grid.time t1 t0 K N (j + 1))) I
        - gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j)) I
        - (Grid.step t1 t0 K N : ℂ) * loopDriftGUE d e (Grid.time t1 t0 K N j) N I
            (gueH d t1 t0 K N j ω)
      = gpdZinc d t1 t0 K N e I j ω + gpdYst d t1 t0 K N e I (j + 1) ω
        - gpdB d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) (gueH d t1 t0 K N j ω)
        + gpdr d t1 t0 K N e I j ω := by
  obtain ⟨_, hΦ⟩ := gpd_bddC2C_Phi (d := d) (t1 := t1) (t0 := t0) (K := K) (N := N) (e := e)
    (I := I) he hwf hst ht0 hj
  set Φ := gpdPhi d t1 t0 K N e I j with hΦdef
  set v := gpdv d t1 t0 K N with hvdef
  set M := gueH d t1 t0 K N j ω with hMdef
  set X := ω (j + 1) with hXdef
  have hsucc : gueH d t1 t0 K N (j + 1) ω = M + Hflow d N v X := gpd_gueH_succ t1 t0 K N j ω
  have hL1 : gloop (d.L N) (d.W N) (gueH d t1 t0 K N (j + 1) ω)
      (zt e (Grid.time t1 t0 K N (j + 1))) I = Φ (M + Hflow d N v X) := by
    rw [hΦdef, gpdPhi, ← hsucc, loopObs_of_isHermitian (gueH_isHermitian d t1 t0 K N (j + 1) ω)]
  have hint := gpd_integral_step (d := d) (N := N) hΦ v M
  have hRdef : Φ (M + Hflow d N v X) = Φ M + gpdZ d N Φ v M X + gpdR d N Φ v M X := by
    unfold gpdR; ring
  have hT : gpdT d N Φ v M X = gpdR d N Φ v M X := by
    unfold gpdT; rw [Set.indicator_of_mem hgood]
  have hY : gpdYst d t1 t0 K N e I (j + 1) ω
      = gpdT d N Φ v M X - ∫ y, gpdT d N Φ v M y ∂(gueUnit d) := by
    simp only [gpdYst, hj, ite_true, gpdFY]
    rfl
  have hZ : gpdZinc d t1 t0 K N e I j ω = gpdZ d N Φ v M X := rfl
  have hr : gpdr d t1 t0 K N e I j ω
      = (∫ y, Φ (M + Hflow d N v y) ∂(gueUnit d))
        - gloop (d.L N) (d.W N) M (zt e (Grid.time t1 t0 K N j)) I
        - (Grid.step t1 t0 K N : ℂ) * loopDriftGUE d e (Grid.time t1 t0 K N j) N I M := rfl
  rw [hL1, hY, hZ, hr, hint, hRdef, hT]
  ring

/-- `firstHit` has not stopped before `k` if the process stays below the threshold. -/
private theorem gpd_le_firstHit {Ω' : Type*} {J : ℕ → Ω' → ℝ} {θ : ℝ} {K' k : ℕ} {ω : Ω'}
    (hk : k ≤ K') (h : ∀ j < k, J j ω < θ) : k ≤ Grid.firstHit J θ K' ω := by
  by_contra hlt
  push Not at hlt
  have := (MeasureTheory.hittingBtwn_lt_iff (u := J) (s := Set.Ici θ) (n := 0) (ω := ω) k hk).1 hlt
  obtain ⟨j, hj, hjs⟩ := this
  exact absurd (h j hj.2) (not_lt.2 hjs)

/-- **The dyadic level** (N1): some `ℓ ≤ L₀` has `σ_ℓ ≥ k` and `λ_ℓ ≤ λ₀ + 2Q`. -/
private theorem gpd_exists_level {Ω' : Type*} {J : ℕ → Ω' → ℝ} {K' k L₀ : ℕ} {ω : Ω'}
    {lam0 Q : ℝ} (hlam0 : 0 < lam0) (hQ : 0 ≤ Q) (hQL : Q < 2 ^ L₀ * lam0) (hk : k ≤ K')
    (hJ : ∀ j < k, J j ω ≤ Q) :
    ∃ ℓ : ℕ, ℓ ≤ L₀ ∧ k ≤ Grid.firstHit J (2 ^ ℓ * lam0) K' ω ∧ 2 ^ ℓ * lam0 ≤ lam0 + 2 * Q := by
  classical
  have hex : ∃ ℓ : ℕ, Q < 2 ^ ℓ * lam0 := ⟨L₀, hQL⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hQL, ?_, ?_⟩
  · exact gpd_le_firstHit hk fun j hj => (hJ j hj).trans_lt (Nat.find_spec hex)
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp; linarith
    · have hmin := Nat.find_min hex (Nat.sub_lt hpos one_pos)
      push Not at hmin
      have e : (2 : ℝ) ^ Nat.find hex = 2 * 2 ^ (Nat.find hex - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e]
      nlinarith

end Decomp

/-! ### 11. Deterministic bounds on the variance proxy (rows M1, M2 and the shift) -/

section ProxyBounds

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {N : ℕ}

/-- **Rows M1 + shift**: the variance proxy of the step `j → j+1` is controlled by the
quadratic variation proxy at time `u_j`. -/
private theorem gpd_Vp_le {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) {z z' : ℂ}
    (hz'pos : 0 < z'.im) (hzz' : z'.im ≤ z.im) (hz2 : z.im ≤ 2 * z'.im) (hz'1 : z'.im ≤ 1)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) (hzd : ‖z' - z‖ ≤ Δ) {I : LoopIdx (ZMod (d.L N))} (hwf : I.WF) :
    Δ / (((d.L N * d.W N : ℕ)) : ℝ) * max (vGue d N (Grid.gradMat (loopObs d N z' I) M) : ℝ)
        (vGue d N (-Complex.I • Grid.gradMat (loopObs d N z' I) M) : ℝ)
      ≤ 32 * (I.length : ℝ) ^ 2 * Δ * ((((d.L N * d.W N : ℕ)) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2
          * loopMax (d.L N) (d.W N) M z (2 * I.length)
          + 2 * I.length * (z'.im)⁻¹ ^ (2 * I.length + 4) * Δ) := by
  set S : ℝ := (((d.L N * d.W N : ℕ)) : ℝ) with hS
  set n : ℕ := I.length with hn
  have hzpos : 0 < z.im := lt_of_lt_of_le hz'pos hzz'
  have hS1 : 1 ≤ S := by
    rw [hS]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (NeZero.ne _) (d.W_pos N).ne')
  have hS0 : 0 < S := by linarith
  set K' : ℝ := (z'.im)⁻¹ with hK'
  have hK'1 : 1 ≤ K' := by rw [hK']; exact one_le_inv₀ hz'pos |>.2 hz'1
  have hK'0 : 0 ≤ K' := by linarith
  have hzinv : (z.im)⁻¹ ≤ K' := inv_anti₀ hz'pos hzz'
  have hz'ne : z'.im ≠ 0 := hz'pos.ne'
  have hzne : z.im ≠ 0 := hzpos.ne'
  -- the variance bound at `z'`
  have hv := gpd_vGue_gradMat_le hz'ne hwf hM (d := d)
  rw [abs_of_pos hz'pos] at hv
  -- the shift of `loopMax`
  have hG : ‖green M z‖ ≤ K' :=
    (RBM.norm_green_le hM hzne).trans (by rw [abs_of_pos hzpos]; exact hzinv)
  have hG' : ‖green M z'‖ ≤ K' := (RBM.norm_green_le hM hz'ne).trans (by rw [abs_of_pos hz'pos])
  have hsh := gpd_loopMax_shift_le (L := d.L N) (W := d.W N) hM hzne hz'ne hK'1 hG hG' (2 * n)
  have hLW : (d.L N : ℝ) * (d.W N : ℝ) = S := by rw [hS]; push_cast; ring
  rw [hLW] at hsh
  have hsh' : loopMax (d.L N) (d.W N) M z' (2 * n)
      ≤ loopMax (d.L N) (d.W N) M z (2 * n) + S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2) := by
    refine hsh.trans (add_le_add le_rfl ?_)
    have : (0 : ℝ) ≤ S * ((2 * n : ℕ) : ℝ) * K' ^ (2 * n) := by positivity
    have h2 : ‖z' - z‖ * K' ^ 2 ≤ Δ * K' ^ 2 := mul_le_mul_of_nonneg_right hzd (by positivity)
    calc S * ((2 * n : ℕ) : ℝ) * K' ^ (2 * n) * (‖z' - z‖ * K' ^ 2)
        ≤ S * ((2 * n : ℕ) : ℝ) * K' ^ (2 * n) * (Δ * K' ^ 2) := mul_le_mul_of_nonneg_left h2 this
      _ = _ := by push_cast; ring
  have hratio : K' ^ 2 ≤ 4 * (z.im)⁻¹ ^ 2 := by
    rw [hK']
    have : (z'.im)⁻¹ ≤ 2 * (z.im)⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hz'pos]
      have : z.im * (z.im)⁻¹ = 1 := mul_inv_cancel₀ hzne
      nlinarith [inv_pos.2 hzpos]
    have h0 : 0 ≤ (z'.im)⁻¹ := by positivity
    nlinarith
  have hLM0 : 0 ≤ loopMax (d.L N) (d.W N) M z (2 * n) := loopMax_nonneg _
  have hLM'0 : 0 ≤ loopMax (d.L N) (d.W N) M z' (2 * n) := loopMax_nonneg _
  have hzinv2 : (z.im)⁻¹ ^ 2 ≤ K' ^ 2 := pow_le_pow_left₀ (by positivity) hzinv 2
  set LM := loopMax (d.L N) (d.W N) M z (2 * n) with hLM
  set LM' := loopMax (d.L N) (d.W N) M z' (2 * n) with hLM'
  set V := max (vGue d N (Grid.gradMat (loopObs d N z' I) M) : ℝ)
      (vGue d N (-Complex.I • Grid.gradMat (loopObs d N z' I) M) : ℝ) with hVdef
  set a := (z.im)⁻¹ with ha
  have ha0 : 0 ≤ a := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hE0 : 0 ≤ S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2) := by positivity
  have step1 : V ≤ 8 * ((n : ℝ) ^ 2 * (4 * a ^ 2)
      * (LM + S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2))) := by
    refine hv.trans ?_
    have h1 : (n : ℝ) ^ 2 * K' ^ 2 ≤ (n : ℝ) ^ 2 * (4 * a ^ 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have h2 : (n : ℝ) ^ 2 * K' ^ 2 * LM' ≤ (n : ℝ) ^ 2 * (4 * a ^ 2)
        * (LM + S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2)) :=
      mul_le_mul h1 hsh' hLM'0 (by positivity)
    linarith
  have hΔS : 0 ≤ Δ / S := div_nonneg hΔ hS0.le
  have step2 : Δ / S * V ≤ Δ / S * (8 * ((n : ℝ) ^ 2 * (4 * a ^ 2)
      * (LM + S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2)))) :=
    mul_le_mul_of_nonneg_left step1 hΔS
  have step3 : Δ / S * (8 * ((n : ℝ) ^ 2 * (4 * a ^ 2)
      * (LM + S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2))))
      = 32 * (n : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM + 2 * n * (a ^ 2 * K' ^ (2 * n + 2)) * Δ) := by
    have hSne : S ≠ 0 := hS0.ne'
    rw [div_eq_mul_inv]
    have e1 : K' ^ (2 * n) * K' ^ 2 = K' ^ (2 * n + 2) := by rw [← pow_add]
    calc Δ * S⁻¹ * (8 * ((n : ℝ) ^ 2 * (4 * a ^ 2)
          * (LM + S * (2 * n) * K' ^ (2 * n) * (Δ * K' ^ 2))))
        = 32 * (n : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM
            + 2 * n * (a ^ 2 * (K' ^ (2 * n) * K' ^ 2)) * Δ * (S⁻¹ * S)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hSne, e1, mul_one]
  have h4 : a ^ 2 * K' ^ (2 * n + 2) ≤ K' ^ (2 * n + 4) := by
    calc a ^ 2 * K' ^ (2 * n + 2) ≤ K' ^ 2 * K' ^ (2 * n + 2) :=
          mul_le_mul_of_nonneg_right hzinv2 (by positivity)
      _ = K' ^ (2 * n + 4) := by rw [← pow_add]; congr 1; ring
  have step4 : 32 * (n : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM + 2 * n * (a ^ 2 * K' ^ (2 * n + 2)) * Δ)
      ≤ 32 * (n : ℝ) ^ 2 * Δ * (S⁻¹ * a ^ 2 * LM + 2 * n * K' ^ (2 * n + 4) * Δ) := by
    have h5 : 2 * n * (a ^ 2 * K' ^ (2 * n + 2)) * Δ ≤ 2 * n * K' ^ (2 * n + 4) * Δ := by
      have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * n)
      exact mul_le_mul_of_nonneg_right this hΔ
    have h6 : 0 ≤ 32 * (n : ℝ) ^ 2 * Δ := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h6
  calc Δ / S * V ≤ _ := step2
    _ = _ := step3
    _ ≤ _ := step4

/-- **Row M2**: the crude bound `S⁻¹ η⁻² L^{(2n)} ≤ η^{-(2n+2)}`. -/
private theorem gpd_qv_le_crude {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) {z : ℂ}
    (hz : 0 < z.im) (m : ℕ) :
    (((d.L N * d.W N : ℕ)) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2 * loopMax (d.L N) (d.W N) M z m
      ≤ (z.im)⁻¹ ^ (m + 2) := by
  have h := gpd_loopMax_le_crude (L := d.L N) (W := d.W N) hM hz.ne' m
  rw [abs_of_pos hz] at h
  have hS : (0 : ℝ) < (((d.L N * d.W N : ℕ)) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos N)
  have hLW : (d.L N : ℝ) * (d.W N : ℝ) = (((d.L N * d.W N : ℕ)) : ℝ) := by push_cast; ring
  rw [hLW] at h
  calc (((d.L N * d.W N : ℕ)) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2 * loopMax (d.L N) (d.W N) M z m
      ≤ (((d.L N * d.W N : ℕ)) : ℝ)⁻¹ * (z.im)⁻¹ ^ 2
          * ((((d.L N * d.W N : ℕ)) : ℝ) * (z.im)⁻¹ ^ m) := by gcongr
    _ = ((((d.L N * d.W N : ℕ)) : ℝ)⁻¹ * (((d.L N * d.W N : ℕ)) : ℝ))
          * ((z.im)⁻¹ ^ 2 * (z.im)⁻¹ ^ m) := by ring
    _ = (z.im)⁻¹ ^ (m + 2) := by rw [inv_mul_cancel₀ hS.ne', one_mul, ← pow_add, add_comm]

end ProxyBounds

/-! ### 12. Grid bookkeeping (rows G1, T1/T2) -/

section GridFacts

private theorem gpd_grid_facts {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} {e : ℝ} (he : |e| < 2)
    (ht1 : 0 ≤ t1 N) (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hK : 0 < K N)
    {x : ℝ} (heta : x⁻¹ ≤ etaT e (t0 N)) :
    0 ≤ Grid.step t1 t0 K N ∧ (K N : ℝ) * Grid.step t1 t0 K N ≤ 1 ∧
      (∀ j ≤ K N, x⁻¹ ≤ (zt e (Grid.time t1 t0 K N j)).im ∧
        (zt e (Grid.time t1 t0 K N j)).im ≤ 1) ∧
      (∀ j, ‖zt e (Grid.time t1 t0 K N (j + 1)) - zt e (Grid.time t1 t0 K N j)‖
        = Grid.step t1 t0 K N) ∧
      (∀ j, (zt e (Grid.time t1 t0 K N (j + 1))).im ≤ (zt e (Grid.time t1 t0 K N j)).im ∧
        (zt e (Grid.time t1 t0 K N j)).im
          ≤ (zt e (Grid.time t1 t0 K N (j + 1))).im + Grid.step t1 t0 K N) ∧
      (∀ k, Grid.time t1 t0 K N k - t1 N = k * Grid.step t1 t0 K N) := by
  have hKpos : (0 : ℝ) < (K N : ℝ) := by exact_mod_cast hK
  set Δ := Grid.step t1 t0 K N with hΔdef
  have hΔ0 : 0 ≤ Δ := by rw [hΔdef]; unfold Grid.step; exact div_nonneg (by linarith) hKpos.le
  have hKΔ : (K N : ℝ) * Δ = t0 N - t1 N := by rw [hΔdef]; unfold Grid.step; field_simp
  have htime : ∀ j, Grid.time t1 t0 K N j = t1 N + j * Δ := fun j => by
    rw [hΔdef]; rfl
  have hm0 : 0 < (mE e).im := mE_im_pos he
  have hm1 : (mE e).im ≤ 1 := le_of_abs_le ((Complex.abs_im_le_norm _).trans (norm_mE he.le).le)
  have hmn : ‖mE e‖ = 1 := norm_mE he.le
  refine ⟨hΔ0, by linarith, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : (j : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hj
    have hle : Grid.time t1 t0 K N j ≤ t0 N := by
      rw [htime]; nlinarith
    have hge : t1 N ≤ Grid.time t1 t0 K N j := by
      rw [htime]; have : (0 : ℝ) ≤ j * Δ := by positivity
      linarith
    rw [zt_im]
    constructor
    · refine heta.trans ?_
      unfold etaT
      exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
    · have h1 : 1 - Grid.time t1 t0 K N j ≤ 1 := by linarith
      have h0 : 0 ≤ 1 - Grid.time t1 t0 K N j := by linarith
      nlinarith
  · intro j
    unfold zt
    rw [htime, htime]
    push_cast
    have : (↑e + (1 - (↑(t1 N) + (↑(j + 1 : ℕ) : ℂ) * ↑Δ)) * mE e
        - (↑e + (1 - (↑(t1 N) + (↑j : ℂ) * ↑Δ)) * mE e)) = -((Δ : ℂ) * mE e) := by
      push_cast; ring
    rw [show ((↑e : ℂ) + (1 - (↑(t1 N) + ((j : ℂ) + 1) * ↑Δ)) * mE e
        - (↑e + (1 - (↑(t1 N) + (j : ℂ) * ↑Δ)) * mE e)) = -((Δ : ℂ) * mE e) by ring]
    rw [norm_neg, norm_mul, hmn, mul_one, Complex.norm_real, Real.norm_of_nonneg hΔ0]
  · intro j
    rw [zt_im, zt_im, htime, htime]
    push_cast
    constructor
    · nlinarith
    · nlinarith
  · intro k; rw [htime]; ring

end GridFacts

/-! ### 13. The pathwise assembly on the good event -/

section Pathwise

open scoped Matrix.Norms.L2Operator

variable {d : Dims} {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} {e : ℝ} {I : LoopIdx (ZMod (d.L N))}

/-- **Telescoping** the pathwise one-step decomposition. -/
private theorem gpd_telescope (he : |e| < 2) (hwf : I.WF) (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1)
    {ω : Grid.Ωg d} (htr : ∀ j < K N, ω (j + 1) ∈ gpdGood d N) {k : ℕ} (hk : k ≤ K N) :
    gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt e (Grid.time t1 t0 K N k)) I
        - gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) (zt e (Grid.time t1 t0 K N 0)) I
        - (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
            loopDriftGUE d e (Grid.time t1 t0 K N j) N I (gueH d t1 t0 K N j ω)
      = ∑ j ∈ Finset.range k, gpdZinc d t1 t0 K N e I j ω
        + ∑ j ∈ Finset.range k, gpdYst d t1 t0 K N e I (j + 1) ω
        - ∑ j ∈ Finset.range k,
            gpdB d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) (gueH d t1 t0 K N j ω)
        + ∑ j ∈ Finset.range k, gpdr d t1 t0 K N e I j ω := by
  set L : ℕ → ℂ := fun j =>
    gloop (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j)) I with hL
  have htel : L k - L 0 = ∑ j ∈ Finset.range k, (L (j + 1) - L j) :=
    (Finset.sum_range_sub L k).symm
  have hstep : ∀ j ∈ Finset.range k, L (j + 1) - L j
      - (Grid.step t1 t0 K N : ℂ) * loopDriftGUE d e (Grid.time t1 t0 K N j) N I
          (gueH d t1 t0 K N j ω)
      = gpdZinc d t1 t0 K N e I j ω + gpdYst d t1 t0 K N e I (j + 1) ω
        - gpdB d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) (gueH d t1 t0 K N j ω)
        + gpdr d t1 t0 K N e I j ω := by
    intro j hj
    have hjK : j < K N := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    exact gpd_step_decomp he hwf hst ht0 hjK ω (htr j hjK)
  change L k - L 0 - _ = _
  rw [htel, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hstep]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

private theorem gpd_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a)
      (Real.sqrt_nonneg b)]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq (by positivity)

/-- **The linear part on the good event** (N1 + rows M1–M3). -/
private theorem gpd_Z_bound (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 N) (hst : t1 N ≤ t0 N)
    (ht0 : t0 N < 1) (hK : 0 < K N) {lam0 : ℝ} (hlam0 : 0 < lam0) {x : ℝ} (hx1 : 1 ≤ x)
    (heta : x⁻¹ ≤ etaT e (t0 N)) (hxΔ : x * Grid.step t1 t0 K N ≤ 1)
    (hQ : 32 * (I.length : ℝ) ^ 2 * Grid.step t1 t0 K N * (x ^ (2 * I.length + 2)
      + 2 * I.length * x ^ (2 * I.length + 4) * Grid.step t1 t0 K N) < 2 ^ N * lam0)
    {c : ℝ} (hc : 0 ≤ c) {ω : Grid.Ωg d} {k : ℕ} (hk : k ≤ K N)
    (hZ : ∀ ℓ ≤ N, ‖∑ j ∈ Finset.range k, gpdZst d t1 t0 K N e I (2 ^ ℓ * lam0) (j + 1) ω‖
      ≤ c * Real.sqrt (k * (2 ^ ℓ * lam0))) :
    ‖∑ j ∈ Finset.range k, gpdZinc d t1 t0 K N e I j ω‖
      ≤ c * Real.sqrt (k * lam0)
        + 8 * I.length * c * Real.sqrt (Grid.time t1 t0 K N k - t1 N)
          * (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ)) : ℝ)⁻¹
              * (etaT e (Grid.time t1 t0 K N j))⁻¹ ^ 2
              * loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j))
                  (2 * I.length)))
        + 8 * I.length * c * Real.sqrt (2 * I.length * x ^ (2 * I.length + 4)
            * Grid.step t1 t0 K N) := by
  classical
  obtain ⟨hΔ0, hKΔ, hη, hzd, hmono, htk⟩ := gpd_grid_facts (K := K) (N := N) he ht1 hst ht0 hK heta
  set n : ℕ := I.length with hn
  set S : ℝ := (((d.L N * d.W N : ℕ)) : ℝ) with hS
  set Δ := Grid.step t1 t0 K N with hΔ
  have hx0 : 0 < x := by linarith
  have hΔx : Δ ≤ x⁻¹ := by
    calc Δ = x⁻¹ * (x * Δ) := by field_simp
      _ ≤ x⁻¹ * 1 := mul_le_mul_of_nonneg_left hxΔ (by positivity)
      _ = x⁻¹ := mul_one _
  set a : ℕ → ℝ := fun j => Real.sqrt (S⁻¹ * (etaT e (Grid.time t1 t0 K N j))⁻¹ ^ 2
    * loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j)) (2 * n))
    with ha
  set Mk : ℝ := ⨆ j : Fin k, a j with hMk
  have hsum0 : 0 ≤ c * Real.sqrt (k * lam0) := by positivity
  have hlast0 : 0 ≤ 8 * (n : ℝ) * c * Real.sqrt (2 * n * x ^ (2 * n + 4) * Δ) := by positivity
  have hMk0 : 0 ≤ Mk := Real.iSup_nonneg fun j => Real.sqrt_nonneg _
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    have : 0 ≤ 8 * (n : ℝ) * c * Real.sqrt (Grid.time t1 t0 K N 0 - t1 N) * Mk := by positivity
    linarith
  -- deterministic facts for `j < k`
  have hkK : ∀ j < k, j < K N := fun j hj => lt_of_lt_of_le hj hk
  have hηj : ∀ j < k, x⁻¹ ≤ (zt e (Grid.time t1 t0 K N j)).im ∧
      (zt e (Grid.time t1 t0 K N (j + 1))).im ≥ x⁻¹ ∧ (zt e (Grid.time t1 t0 K N (j + 1))).im ≤ 1 :=
    fun j hj => ⟨(hη j (le_of_lt (hkK j hj))).1, (hη (j + 1) (hkK j hj)).1,
      (hη (j + 1) (hkK j hj)).2⟩
  have hinvx : ∀ {y : ℝ}, x⁻¹ ≤ y → y⁻¹ ≤ x := fun {y} hy => by
    have hy0 : 0 < y := lt_of_lt_of_le (inv_pos.2 hx0) hy
    rw [inv_le_comm₀ hy0 hx0]; exact hy
  -- `a j ≤ M_k` and `a j ≤ x^{n+1}`
  have haM : ∀ j < k, a j ≤ Mk := fun j hj =>
    le_ciSup (f := fun j : Fin k => a j) (Set.finite_range _).bddAbove ⟨j, hj⟩
  have hsqa : ∀ j < k, a j ^ 2 = S⁻¹ * (etaT e (Grid.time t1 t0 K N j))⁻¹ ^ 2
      * loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j)) (2 * n) := by
    intro j hj
    rw [ha]; dsimp only
    rw [Real.sq_sqrt]
    have : 0 ≤ loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j))
        (2 * n) := loopMax_nonneg _
    positivity
  have haX : ∀ j < k, a j ≤ x ^ (n + 1) := by
    intro j hj
    have hpos : 0 < (zt e (Grid.time t1 t0 K N j)).im :=
      lt_of_lt_of_le (inv_pos.2 hx0) (hηj j hj).1
    have hc := gpd_qv_le_crude (d := d) (N := N) (gueH_isHermitian d t1 t0 K N j ω) hpos (2 * n)
    rw [← etaT_eq_zt_im] at hc
    have h1 : (etaT e (Grid.time t1 t0 K N j))⁻¹ ≤ x := by
      rw [etaT_eq_zt_im]; exact hinvx (hηj j hj).1
    have h2 : (etaT e (Grid.time t1 t0 K N j))⁻¹ ^ (2 * n + 2) ≤ x ^ (2 * n + 2) :=
      pow_le_pow_left₀ (by rw [etaT_eq_zt_im]; positivity) h1 _
    have h3 : a j ^ 2 ≤ (x ^ (n + 1)) ^ 2 := by
      rw [hsqa j hj, ← pow_mul]
      calc _ ≤ _ := hc
        _ ≤ x ^ (2 * n + 2) := h2
        _ = x ^ ((n + 1) * 2) := by ring_nf
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) two_ne_zero).1 h3
  have hMX : Mk ≤ x ^ (n + 1) := by
    have : Nonempty (Fin k) := ⟨⟨0, hkpos⟩⟩
    exact ciSup_le fun j => haX j j.2
  -- the proxy bound `V_j ≤ Q`
  set esh : ℝ := 2 * n * x ^ (2 * n + 4) * Δ with hesh
  have hesh0 : 0 ≤ esh := mul_nonneg (by positivity) hΔ0
  set Q : ℝ := 32 * (n : ℝ) ^ 2 * Δ * (Mk ^ 2 + esh) with hQdef
  have h32 : 0 ≤ 32 * (n : ℝ) ^ 2 * Δ := mul_nonneg (by positivity) hΔ0
  have hQ0 : 0 ≤ Q := mul_nonneg h32 (by positivity)
  have hVQ : ∀ j < k, gpdVp d t1 t0 K N e I j ω ≤ Q := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := hηj j hj
    have hz'pos : 0 < (zt e (Grid.time t1 t0 K N (j + 1))).im := lt_of_lt_of_le (inv_pos.2 hx0) h2
    have hz2 : (zt e (Grid.time t1 t0 K N j)).im ≤ 2 * (zt e (Grid.time t1 t0 K N (j + 1))).im := by
      have := (hmono j).2
      have hΔle : Δ ≤ (zt e (Grid.time t1 t0 K N (j + 1))).im := le_trans hΔx h2
      linarith
    have hV := gpd_Vp_le (gueH_isHermitian d t1 t0 K N j ω) hz'pos (hmono j).1 hz2 h3 hΔ0
      (le_of_eq (hzd j)) hwf (N := N)
    have hVeq : gpdVp d t1 t0 K N e I j ω
        = Δ / S * max (vGue d N (Grid.gradMat (loopObs d N (zt e (Grid.time t1 t0 K N (j + 1))) I)
            (gueH d t1 t0 K N j ω)) : ℝ)
          (vGue d N (-Complex.I • Grid.gradMat (loopObs d N (zt e (Grid.time t1 t0 K N (j + 1))) I)
            (gueH d t1 t0 K N j ω)) : ℝ) := rfl
    rw [hVeq]
    refine hV.trans ?_
    have hinv' : ((zt e (Grid.time t1 t0 K N (j + 1))).im)⁻¹ ^ (2 * n + 4) ≤ x ^ (2 * n + 4) :=
      pow_le_pow_left₀ (by positivity) (hinvx h2) _
    have ha2 : S⁻¹ * ((zt e (Grid.time t1 t0 K N j)).im)⁻¹ ^ 2
        * loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j)) (2 * n)
        ≤ Mk ^ 2 := by
      rw [← etaT_eq_zt_im, ← hsqa j hj]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (haM j hj) 2
    refine mul_le_mul_of_nonneg_left (add_le_add ha2 ?_) h32
    have : (0 : ℝ) ≤ 2 * n := by positivity
    have := mul_le_mul_of_nonneg_left hinv' this
    exact mul_le_mul_of_nonneg_right this hΔ0
  have hQlt : Q < 2 ^ N * lam0 := by
    refine lt_of_le_of_lt ?_ hQ
    have hM2 : Mk ^ 2 ≤ x ^ (2 * n + 2) := by
      calc Mk ^ 2 ≤ (x ^ (n + 1)) ^ 2 := pow_le_pow_left₀ hMk0 hMX 2
        _ = x ^ (2 * n + 2) := by rw [← pow_mul]; ring_nf
    exact mul_le_mul_of_nonneg_left (by linarith) h32
  obtain ⟨ℓ, hℓN, hσ, hlam⟩ := gpd_exists_level (J := gpdVp d t1 t0 K N e I) (K' := K N)
    (L₀ := N) (ω := ω) hlam0 hQ0 hQlt hk hVQ
  -- the stopped sum is the full sum
  have hfull : ∑ j ∈ Finset.range k, gpdZst d t1 t0 K N e I (2 ^ ℓ * lam0) (j + 1) ω
      = ∑ j ∈ Finset.range k, gpdZinc d t1 t0 K N e I j ω := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjs : j < Grid.firstHit (gpdVp d t1 t0 K N e I) (2 ^ ℓ * lam0) (K N) ω :=
      lt_of_lt_of_le (Finset.mem_range.1 hj) hσ
    simp only [gpdZst]
    rw [Set.indicator_of_mem (show ω ∈ {ω | j < Grid.firstHit (gpdVp d t1 t0 K N e I)
      (2 ^ ℓ * lam0) (K N) ω} from hjs)]
  have hmain := hZ ℓ hℓN
  rw [hfull] at hmain
  refine hmain.trans ?_
  -- `√(k λ_ℓ) ≤ √(kλ₀) + 8n √(kΔ) M_k + 8n √(esh)`
  have hkΔ : (k : ℝ) * Δ = Grid.time t1 t0 K N k - t1 N := (htk k).symm
  have hkΔ1 : (k : ℝ) * Δ ≤ 1 := by
    have : (k : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hk
    nlinarith
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg k) hΔ0
  have hsq1 : Real.sqrt (k * (2 ^ ℓ * lam0))
      ≤ Real.sqrt (k * lam0) + 8 * n * Real.sqrt (k * Δ) * Mk + 8 * n * Real.sqrt esh := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hb1 : k * (2 ^ ℓ * lam0) ≤ k * lam0 + (64 * n ^ 2 * (k * Δ) * Mk ^ 2
        + 64 * n ^ 2 * (k * Δ) * esh) := by
      have := mul_le_mul_of_nonneg_left hlam hk0
      rw [hQdef] at this
      nlinarith
    have hA : 0 ≤ (k : ℝ) * lam0 := by positivity
    have hB : 0 ≤ 64 * (n : ℝ) ^ 2 * (k * Δ) * Mk ^ 2 :=
      mul_nonneg (mul_nonneg (by positivity) hkΔ0) (sq_nonneg _)
    have hC : 0 ≤ 64 * (n : ℝ) ^ 2 * (k * Δ) * esh :=
      mul_nonneg (mul_nonneg (by positivity) hkΔ0) hesh0
    have e1 : Real.sqrt (64 * (n : ℝ) ^ 2 * (k * Δ) * Mk ^ 2) = 8 * n * Real.sqrt (k * Δ) * Mk := by
      rw [show 64 * (n : ℝ) ^ 2 * (k * Δ) * Mk ^ 2 = (8 * n * Mk) ^ 2 * (k * Δ) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      ring
    have e2 : Real.sqrt (64 * (n : ℝ) ^ 2 * (k * Δ) * esh)
        = 8 * n * Real.sqrt (k * Δ) * Real.sqrt esh := by
      rw [show 64 * (n : ℝ) ^ 2 * (k * Δ) * esh = (8 * n) ^ 2 * ((k * Δ) * esh) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hkΔ0]
      ring
    have hsk : Real.sqrt (k * Δ) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hkΔ1
    calc Real.sqrt (k * (2 ^ ℓ * lam0))
        ≤ Real.sqrt (k * lam0 + (64 * n ^ 2 * (k * Δ) * Mk ^ 2 + 64 * n ^ 2 * (k * Δ) * esh)) :=
          Real.sqrt_le_sqrt hb1
      _ ≤ Real.sqrt (k * lam0) + (Real.sqrt (64 * n ^ 2 * (k * Δ) * Mk ^ 2)
            + Real.sqrt (64 * n ^ 2 * (k * Δ) * esh)) := by
          refine (gpd_sqrt_add_le hA (by positivity)).trans (add_le_add le_rfl ?_)
          exact gpd_sqrt_add_le hB hC
      _ = Real.sqrt (k * lam0) + 8 * n * Real.sqrt (k * Δ) * Mk
            + 8 * n * Real.sqrt (k * Δ) * Real.sqrt esh := by rw [e1, e2]; ring
      _ ≤ _ := by
          have : 8 * (n : ℝ) * Real.sqrt (k * Δ) * Real.sqrt esh ≤ 8 * n * 1 * Real.sqrt esh := by
            have h0 : 0 ≤ 8 * (n : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left hsk h0
            exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
          linarith
  rw [← hkΔ]
  calc c * Real.sqrt (k * (2 ^ ℓ * lam0))
      ≤ c * (Real.sqrt (k * lam0) + 8 * n * Real.sqrt (k * Δ) * Mk + 8 * n * Real.sqrt esh) :=
        mul_le_mul_of_nonneg_left hsq1 hc
    _ = _ := by rw [hesh]; ring

/-- **The pathwise bound on the good event** (Y2, Y3 and N1 combined). -/
private theorem gpd_pathwise (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 N) (hst : t1 N ≤ t0 N)
    (ht0 : t0 N < 1) (hK : 0 < K N) {lam0 : ℝ} (hlam0 : 0 < lam0) (hN1 : 1 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT e (t0 N)) (hNΔ : (N : ℝ) * Grid.step t1 t0 K N ≤ 1)
    (hQ : 32 * (I.length : ℝ) ^ 2 * Grid.step t1 t0 K N * ((N : ℝ) ^ (2 * I.length + 2)
      + 2 * I.length * (N : ℝ) ^ (2 * I.length + 4) * Grid.step t1 t0 K N) < 2 ^ N * lam0)
    {c epsY : ℝ} (hc : 0 ≤ c) {ω : Grid.Ωg d}
    (htr : ∀ j < K N, ω (j + 1) ∈ gpdGood d N)
    (hr : ∀ j < K N, ‖gpdr d t1 t0 K N e I j ω‖
      ≤ (2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4) *
          (1 + ((zt e (Grid.time t1 t0 K N (j + 1))).im)⁻¹) ^ (I.length + 4) *
          Grid.step t1 t0 K N ^ ((3 : ℝ) / 2))
    {k : ℕ} (hk : k ≤ K N)
    (hZ : ∀ ℓ ≤ N, ‖∑ j ∈ Finset.range k, gpdZst d t1 t0 K N e I (2 ^ ℓ * lam0) (j + 1) ω‖
      ≤ c * Real.sqrt (k * (2 ^ ℓ * lam0)))
    (hY : ‖∑ j ∈ Finset.range k, gpdYst d t1 t0 K N e I (j + 1) ω‖ ≤ epsY) :
    ‖gloop (d.L N) (d.W N) (gueH d t1 t0 K N k ω) (zt e (Grid.time t1 t0 K N k)) I
        - gloop (d.L N) (d.W N) (gueH d t1 t0 K N 0 ω) (zt e (Grid.time t1 t0 K N 0)) I
        - (Grid.step t1 t0 K N : ℂ) * ∑ j ∈ Finset.range k,
            loopDriftGUE d e (Grid.time t1 t0 K N j) N I (gueH d t1 t0 K N j ω)‖
      ≤ c * Real.sqrt (k * lam0)
        + 8 * I.length * c * Real.sqrt (Grid.time t1 t0 K N k - t1 N)
          * (⨆ j : Fin k, Real.sqrt ((((d.L N * d.W N : ℕ)) : ℝ)⁻¹
              * (etaT e (Grid.time t1 t0 K N j))⁻¹ ^ 2
              * loopMax (d.L N) (d.W N) (gueH d t1 t0 K N j ω) (zt e (Grid.time t1 t0 K N j))
                  (2 * I.length)))
        + 8 * I.length * c * Real.sqrt (2 * I.length * (N : ℝ) ^ (2 * I.length + 4)
            * Grid.step t1 t0 K N)
        + epsY
        + (K N : ℝ) * (16 * Real.exp 2 * ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2
            * (2 * (1 + (N : ℝ)) ^ 3) ^ I.a.length)) * gpdv d t1 t0 K N
            * (Fintype.card (d.Idx N) : ℝ) ^ 4 * Real.exp (-(N : ℝ) / 4))
        + (K N : ℝ) * ((2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4)
            * (1 + (N : ℝ)) ^ (I.length + 4) * Grid.step t1 t0 K N ^ ((3 : ℝ) / 2)) := by
  obtain ⟨hΔ0, hKΔ, hη, _, _, _⟩ := gpd_grid_facts (K := K) (N := N) he ht1 hst ht0 hK heta
  have hN0 : (0 : ℝ) < N := by linarith
  have htrk : ∀ j < K N, ω (j + 1) ∈ gpdGood d N := htr
  rw [gpd_telescope he hwf hst ht0 htrk hk]
  have hZb := gpd_Z_bound (I := I) he hwf ht1 hst ht0 hK hlam0 hN1 heta hNΔ hQ hc hk hZ
  have hkK : (k : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hk
  have hinvN : ∀ j < K N, ((zt e (Grid.time t1 t0 K N (j + 1))).im)⁻¹ ≤ N := by
    intro j hj
    have h := (hη (j + 1) hj).1
    have hpos : 0 < (zt e (Grid.time t1 t0 K N (j + 1))).im := lt_of_lt_of_le (by positivity) h
    rw [inv_le_comm₀ hpos hN0]; exact h
  -- the bias sum (row Y3)
  set EBt : ℝ := 16 * Real.exp 2 * ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2
      * (2 * (1 + (N : ℝ)) ^ 3) ^ I.a.length)) * gpdv d t1 t0 K N
      * (Fintype.card (d.Idx N) : ℝ) ^ 4 * Real.exp (-(N : ℝ) / 4) with hEBt
  have hv0 : 0 ≤ gpdv d t1 t0 K N := div_nonneg hΔ0 (Nat.cast_nonneg _)
  have hB : ∀ j ∈ Finset.range k, ‖gpdB d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N)
      (gueH d t1 t0 K N j ω)‖ ≤ EBt := by
    intro j hj
    have hjK : j < K N := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    obtain ⟨hz, hΦ⟩ := gpd_bddC2C_Phi (d := d) (t1 := t1) (t0 := t0) (K := K) (N := N) (e := e)
      (I := I) he hwf hst ht0 hjK
    refine (gpd_norm_B_le hΦ hv0 _).trans ?_
    rw [hEBt]
    have hBj : 2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3
        ≤ 2 * (1 + (N : ℝ)) ^ 3 := by
      have hpos : 0 < (zt e (Grid.time t1 t0 K N (j + 1))).im :=
        lt_of_lt_of_le (by positivity) (hη (j + 1) hjK).1
      rw [abs_of_pos hpos]
      have := hinvN j hjK
      have h0 : 0 ≤ 1 + ((zt e (Grid.time t1 t0 K N (j + 1))).im)⁻¹ := by positivity
      gcongr
    have hC : (Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2
        * (2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3) ^ I.a.length)
        ≤ (Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2
          * (2 * (1 + (N : ℝ)) ^ 3) ^ I.a.length) := by
      gcongr
    have hE : 0 ≤ Real.exp (-(N : ℝ) / 4) := (Real.exp_pos _).le
    have hc4 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hC (by positivity : (0 : ℝ) ≤ 16 * Real.exp 2)
    have := mul_le_mul_of_nonneg_right this hv0
    have := mul_le_mul_of_nonneg_right this hc4
    exact mul_le_mul_of_nonneg_right this hE
  have hBsum : ‖∑ j ∈ Finset.range k, gpdB d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N)
      (gueH d t1 t0 K N j ω)‖ ≤ (K N : ℝ) * EBt := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hB).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hEBt0 : 0 ≤ EBt := by
      rw [hEBt]
      have := Nat.cast_nonneg (α := ℝ) (Fintype.card (d.Idx N))
      have h1 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2
          * (2 * (1 + (N : ℝ)) ^ 3) ^ I.a.length) := by positivity
      have h2 := (Real.exp_pos (-(N : ℝ) / 4)).le
      have h3 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) ^ 4 := by positivity
      have h16 : (0 : ℝ) ≤ 16 * Real.exp 2 := by positivity
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h16 h1) hv0) h3) h2
      exact this
    exact mul_le_mul_of_nonneg_right hkK hEBt0
  -- the D3 remainder sum
  set ERt : ℝ := (2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4)
      * (1 + (N : ℝ)) ^ (I.length + 4) * Grid.step t1 t0 K N ^ ((3 : ℝ) / 2) with hERt
  have hr' : ∀ j ∈ Finset.range k, ‖gpdr d t1 t0 K N e I j ω‖ ≤ ERt := by
    intro j hj
    have hjK : j < K N := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
    refine (hr j hjK).trans ?_
    rw [hERt]
    have hpos : 0 < (zt e (Grid.time t1 t0 K N (j + 1))).im :=
      lt_of_lt_of_le (by positivity) (hη (j + 1) hjK).1
    have h1 : (1 + ((zt e (Grid.time t1 t0 K N (j + 1))).im)⁻¹) ^ (I.length + 4)
        ≤ (1 + (N : ℝ)) ^ (I.length + 4) := by
      have := hinvN j hjK
      have : 0 ≤ 1 + ((zt e (Grid.time t1 t0 K N (j + 1))).im)⁻¹ := by positivity
      gcongr
    have h2 : 0 ≤ Grid.step t1 t0 K N ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hΔ0 _
    have h3 : 0 ≤ (2 : ℝ) ^ (4 * I.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (I.length + 4) := by
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h3) h2
  have hrsum : ‖∑ j ∈ Finset.range k, gpdr d t1 t0 K N e I j ω‖ ≤ (K N : ℝ) * ERt := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hr').trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hERt0 : 0 ≤ ERt := by
      rw [hERt]
      have := Real.rpow_nonneg hΔ0 ((3 : ℝ) / 2)
      positivity
    exact mul_le_mul_of_nonneg_right hkK hERt0
  -- combine
  set SZ := ∑ j ∈ Finset.range k, gpdZinc d t1 t0 K N e I j ω
  set SY := ∑ j ∈ Finset.range k, gpdYst d t1 t0 K N e I (j + 1) ω
  set SB := ∑ j ∈ Finset.range k, gpdB d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N)
      (gueH d t1 t0 K N j ω)
  set SR := ∑ j ∈ Finset.range k, gpdr d t1 t0 K N e I j ω
  have htri : ‖SZ + SY - SB + SR‖ ≤ ‖SZ‖ + ‖SY‖ + ‖SB‖ + ‖SR‖ := by
    calc ‖SZ + SY - SB + SR‖ ≤ ‖SZ + SY - SB‖ + ‖SR‖ := norm_add_le _ _
      _ ≤ ‖SZ + SY‖ + ‖SB‖ + ‖SR‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖SZ‖ + ‖SY‖ + ‖SB‖ + ‖SR‖ := by gcongr; exact norm_add_le _ _
  refine htri.trans ?_
  linarith

end Pathwise

/-! ### 14. Elementary eventual inequalities -/

section Eventually

private theorem gpd_ev_poly (C : ℝ) {a b : ℕ} (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a ≤ (N : ℝ) ^ b := by
  filter_upwards [eventually_ge_atTop (⌈|C|⌉₊ + 1)] with N hN
  have hC : C ≤ (N : ℝ) := by
    have h1 : (⌈|C|⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : |C| ≤ (⌈|C|⌉₊ : ℝ) := Nat.le_ceil _
    linarith [le_abs_self C]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h1 : (⌈|C|⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) ≤ ⌈|C|⌉₊ := Nat.cast_nonneg _
    linarith
  calc C * (N : ℝ) ^ a ≤ (N : ℝ) * (N : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ = (N : ℝ) ^ (a + 1) := by ring
    _ ≤ (N : ℝ) ^ b := pow_le_pow_right₀ hN1 hab

private theorem gpd_ev_exp (C : ℝ) (a : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ a * Real.exp (-(c * (N : ℝ))) ≤ 1 := by
  have h := SumZeroDyn.eventually_exp_small C (a : ℝ) c hc one_pos
  filter_upwards [h] with N hN
  simp only [Real.rpow_natCast, Real.rpow_one] at hN
  exact hN

private theorem gpd_ev_two_pow (a : ℕ) : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ 2 ^ N := by
  have h := gpd_ev_exp 1 a (c := Real.log 2) (Real.log_pos one_lt_two)
  filter_upwards [h] with N hN
  have e : Real.exp (-(Real.log 2 * (N : ℝ))) = ((2 : ℝ) ^ N)⁻¹ := by
    rw [Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log two_pos]
  rw [e, one_mul] at hN
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rwa [mul_inv_le_iff₀ h2, one_mul] at hN

/-- `4 e^{-N^a} ≤ N^{-D}` (row M4). -/
private theorem gpd_ev_exp_rpow {a : ℝ} (ha : 0 < a) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 * Real.exp (-(N : ℝ) ^ a) ≤ (N : ℝ) ^ (-D) := by
  have h := SumZeroDyn.eventually_exp_small 4 D 1 one_pos ha
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [one_mul] at hN
  have hD : (0 : ℝ) < (N : ℝ) ^ D := Real.rpow_pos_of_pos hN0 D
  rw [Real.rpow_neg hN0.le, inv_eq_one_div, le_div_iff₀ hD]
  have e : 4 * Real.exp (-(N : ℝ) ^ a) * (N : ℝ) ^ D
      = 4 * (N : ℝ) ^ D * Real.exp (-(N : ℝ) ^ a) := by ring
  rw [e]
  simpa using hN

/-- `4 e^{-N} ≤ N^{-D}`. -/
private theorem gpd_ev_exp_lin (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 * Real.exp (-(N : ℝ)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [gpd_ev_exp_rpow one_pos D] with N hN
  simpa using hN

end Eventually

/-! ### 15. The exponent bookkeeping -/

section Numeric

private theorem gpd_le_inv_div {x C c : ℝ} (hx : 0 < x) (hc : 0 < c) {m p : ℕ}
    (h : c * C * x ^ p ≤ x ^ m) : C * (x ^ m)⁻¹ ≤ (x ^ p)⁻¹ / c := by
  have hm : 0 < x ^ m := by positivity
  have hp : 0 < x ^ p := by positivity
  rw [show C * (x ^ m)⁻¹ = C / x ^ m by ring, show (x ^ p)⁻¹ / c = 1 / (c * x ^ p) by
    field_simp, div_le_div_iff₀ hm (by positivity)]
  linarith

/-- Row G1: `Δ ≤ N^{-(32n₀+64)}` and `NΔ ≤ 1`. -/
private theorem gpd_num_step (n0 : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ →
    ((N : ℝ) + 1) ^ (32 * n0 + 64) * Δ ≤ 1 →
      Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ ∧ (N : ℝ) * Δ ≤ 1 := by
  filter_upwards [eventually_ge_atTop 1] with N hN Δ hΔ hKΔ
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxa : (N : ℝ) ^ (32 * n0 + 64) ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpos : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
  have h1 : Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by
    rw [← one_div, le_div_iff₀ hpos]; nlinarith
  refine ⟨h1, ?_⟩
  have h2 : (N : ℝ) ≤ (N : ℝ) ^ (32 * n0 + 64) := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hx (by omega)
  nlinarith

/-- Row M2: the top dyadic level exceeds every proxy. -/
private theorem gpd_num_Q {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ →
      32 * (n : ℝ) ^ 2 * Δ * ((N : ℝ) ^ (2 * n + 2) + 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
        < 2 ^ N * ((N : ℝ) ^ (40 * n0 + 80))⁻¹ := by
  filter_upwards [gpd_ev_poly (32 * (n : ℝ) ^ 2 * (1 + 2 * n)) (a := 2 * n + 4)
      (b := 32 * n0 + 64) (by omega), gpd_ev_two_pow (40 * n0 + 81), eventually_ge_atTop 2]
    with N h1 h2 hN Δ hΔ hΔa
  have hx : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : (1 : ℝ) ≤ N := by linarith
  have hpos : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
  have hΔ1 : Δ ≤ 1 := hΔa.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hx1))
  have hin : (N : ℝ) ^ (2 * n + 2) + 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ
      ≤ (1 + 2 * n) * (N : ℝ) ^ (2 * n + 4) := by
    have : (N : ℝ) ^ (2 * n + 2) ≤ (N : ℝ) ^ (2 * n + 4) := pow_le_pow_right₀ hx1 (by omega)
    have : 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ ≤ 2 * n * (N : ℝ) ^ (2 * n + 4) := by
      have h0 : 0 ≤ 2 * (n : ℝ) * (N : ℝ) ^ (2 * n + 4) := by positivity
      nlinarith
    linarith
  have hL : 32 * (n : ℝ) ^ 2 * Δ * ((N : ℝ) ^ (2 * n + 2) + 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
      ≤ 1 := by
    calc _ ≤ 32 * (n : ℝ) ^ 2 * Δ * ((1 + 2 * n) * (N : ℝ) ^ (2 * n + 4)) := by gcongr
      _ = Δ * (32 * (n : ℝ) ^ 2 * (1 + 2 * n) * (N : ℝ) ^ (2 * n + 4)) := by ring
      _ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ * (N : ℝ) ^ (32 * n0 + 64) := by gcongr
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hR : 1 < 2 ^ N * ((N : ℝ) ^ (40 * n0 + 80))⁻¹ := by
    have hp : 0 < (N : ℝ) ^ (40 * n0 + 80) := by positivity
    rw [← div_eq_mul_inv, lt_div_iff₀ hp, one_mul]
    calc (N : ℝ) ^ (40 * n0 + 80) < (N : ℝ) ^ (40 * n0 + 81) :=
          pow_lt_pow_right₀ (by linarith) (by omega)
      _ ≤ 2 ^ N := h2
  linarith

private theorem gpd_rpow_quarter_le {x τ : ℝ} (hx : 1 ≤ x) (hτ1 : τ ≤ 1) :
    x ^ (τ / 4) ≤ x := by
  calc x ^ (τ / 4) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = x := Real.rpow_one x

private theorem gpd_one_add_pow_le {x : ℝ} (hx : 1 ≤ x) (a : ℕ) :
    (x + 1) ^ a ≤ 2 ^ a * x ^ a := by
  rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) a

/-- Row M3, the dyadic floor. -/
private theorem gpd_num_E1 {n0 n : ℕ} (hn : n ≤ 2 * n0) {τ : ℝ} (hτ1 : τ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, 2 * (N : ℝ) ^ (τ / 4)
      * Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹)
        ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [gpd_ev_poly ((2 : ℝ) ^ (32 * n0 + 64)) (a := 40 * n0 + 78) (b := 40 * n0 + 80)
      (by omega), gpd_ev_poly 10 (a := n + 1) (b := 4 * n0 + 7) (by omega),
      eventually_ge_atTop 1] with N h1 h2 hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hq := gpd_rpow_quarter_le hx hτ1
  have hsq : Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹)
      ≤ ((N : ℝ) ^ (4 * n0 + 7))⁻¹ := by
    rw [Real.sqrt_le_left (by positivity)]
    have hb := gpd_one_add_pow_le hx (32 * n0 + 64)
    have hp1 : 0 < (N : ℝ) ^ (40 * n0 + 80) := by positivity
    rw [inv_pow, ← pow_mul, ← div_eq_mul_inv, div_le_iff₀ hp1, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    calc ((N : ℝ) + 1) ^ (32 * n0 + 64) * (N : ℝ) ^ ((4 * n0 + 7) * 2)
        ≤ 2 ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64) * (N : ℝ) ^ ((4 * n0 + 7) * 2) := by
          gcongr
      _ = 2 ^ (32 * n0 + 64) * (N : ℝ) ^ (40 * n0 + 78) := by
          rw [mul_assoc, ← pow_add]; ring_nf
      _ ≤ (N : ℝ) ^ (40 * n0 + 80) := h1
  have hstep : 2 * (N : ℝ) * ((N : ℝ) ^ (4 * n0 + 7))⁻¹ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
    refine gpd_le_inv_div hx0 (by norm_num) ?_
    calc 5 * (2 * (N : ℝ)) * (N : ℝ) ^ n = 10 * (N : ℝ) ^ (n + 1) := by ring
      _ ≤ _ := h2
  calc 2 * (N : ℝ) ^ (τ / 4)
        * Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹)
      ≤ 2 * (N : ℝ) * ((N : ℝ) ^ (4 * n0 + 7))⁻¹ := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_nonneg hx0.le _
        gcongr
    _ ≤ _ := hstep

/-- The shift term of row M1. -/
private theorem gpd_num_E2 {n0 n : ℕ} (hn : n ≤ 2 * n0) {τ : ℝ} (hτ1 : τ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ →
      16 * n * (N : ℝ) ^ (τ / 4) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
        ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [gpd_ev_poly (2 * (n : ℝ)) (a := 8 * n0 + 10) (b := 32 * n0 + 64) (by omega),
      gpd_ev_poly (80 * (n : ℝ)) (a := n + 1) (b := 2 * n0 + 3) (by omega),
      eventually_ge_atTop 1] with N h1 h2 hN Δ hΔ hΔa
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hq := gpd_rpow_quarter_le hx hτ1
  have hsq : Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ) ≤ ((N : ℝ) ^ (2 * n0 + 3))⁻¹ := by
    rw [Real.sqrt_le_left (by positivity)]
    have hpa : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
    have hpow : (N : ℝ) ^ (2 * n + 4) * (N : ℝ) ^ ((2 * n0 + 3) * 2) ≤ (N : ℝ) ^ (8 * n0 + 10) := by
      rw [← pow_add]; exact pow_le_pow_right₀ hx (by omega)
    rw [inv_pow, ← pow_mul]
    calc 2 * n * (N : ℝ) ^ (2 * n + 4) * Δ
        ≤ 2 * n * (N : ℝ) ^ (2 * n + 4) * ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by gcongr
      _ ≤ ((N : ℝ) ^ ((2 * n0 + 3) * 2))⁻¹ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpa, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
          calc 2 * n * (N : ℝ) ^ (2 * n + 4) * (N : ℝ) ^ ((2 * n0 + 3) * 2)
              = 2 * n * ((N : ℝ) ^ (2 * n + 4) * (N : ℝ) ^ ((2 * n0 + 3) * 2)) := by ring
            _ ≤ 2 * n * (N : ℝ) ^ (8 * n0 + 10) := by gcongr
            _ ≤ _ := h1
  have hstep : 16 * n * (N : ℝ) * ((N : ℝ) ^ (2 * n0 + 3))⁻¹ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
    refine gpd_le_inv_div hx0 (by norm_num) ?_
    calc 5 * (16 * n * (N : ℝ)) * (N : ℝ) ^ n = 80 * n * (N : ℝ) ^ (n + 1) := by ring
      _ ≤ _ := h2
  calc 16 * n * (N : ℝ) ^ (τ / 4) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
      ≤ 16 * n * (N : ℝ) * ((N : ℝ) ^ (2 * n0 + 3))⁻¹ := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 4) := Real.rpow_nonneg hx0.le _
        gcongr
    _ ≤ _ := hstep

/-- The truncation level of `Ỹ` (row Y2). -/
private theorem gpd_num_E3 {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ((N : ℝ) ^ (2 * n0 + 2))⁻¹ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [gpd_ev_poly 5 (a := n) (b := 2 * n0 + 2) (by omega), eventually_ge_atTop 1]
    with N h1 hN
  have hx0 : (0 : ℝ) < N := by exact_mod_cast hN
  have := gpd_le_inv_div (C := 1) hx0 (by norm_num : (0 : ℝ) < 5) (m := 2 * n0 + 2) (p := n)
    (by linarith)
  simpa using this

/-- Row Y3, the truncation bias. -/
private theorem gpd_num_E4 {n : ℕ} :
    ∀ᶠ N : ℕ in atTop, ∀ S Δ K : ℝ, 1 ≤ S → S ≤ N → 0 ≤ Δ → 0 ≤ K → K * Δ ≤ 1 →
      K * (16 * Real.exp 2 * (S * ((n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n)) * (Δ / S)
        * S ^ 4 * Real.exp (-(N : ℝ) / 4)) ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [gpd_ev_exp (80 * Real.exp 2 * (n : ℝ) ^ 2 * 16 ^ n) (4 * n + 4)
      (c := 1 / 4) (by norm_num), eventually_ge_atTop 1] with N h1 hN S Δ K hS1 hSN hΔ hK hKΔ
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hS0 : 0 < S := by linarith
  have hB : (2 * (1 + (N : ℝ)) ^ 3) ^ n ≤ 16 ^ n * (N : ℝ) ^ (3 * n) := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (N : ℝ)]
  have hE : Real.exp (-(N : ℝ) / 4) = Real.exp (-(1 / 4 * (N : ℝ))) := by ring_nf
  have hS4 : S ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hS0.le hSN 4
  have heq : K * (16 * Real.exp 2 * (S * ((n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n)) * (Δ / S)
        * S ^ 4 * Real.exp (-(N : ℝ) / 4))
      = (K * Δ) * (16 * Real.exp 2 * (n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n * S ^ 4
        * Real.exp (-(N : ℝ) / 4)) := by
    field_simp
  rw [heq]
  have h0 : 0 ≤ 16 * Real.exp 2 * (n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n * S ^ 4
      * Real.exp (-(N : ℝ) / 4) := by positivity
  calc (K * Δ) * (16 * Real.exp 2 * (n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n * S ^ 4
        * Real.exp (-(N : ℝ) / 4))
      ≤ 1 * (16 * Real.exp 2 * (n : ℝ) ^ 2 * (16 ^ n * (N : ℝ) ^ (3 * n)) * (N : ℝ) ^ 4
        * Real.exp (-(N : ℝ) / 4)) := by
        gcongr
    _ = (80 * Real.exp 2 * (n : ℝ) ^ 2 * 16 ^ n * (N : ℝ) ^ (4 * n + 4)
          * Real.exp (-(1 / 4 * (N : ℝ)))) * ((N : ℝ) ^ n)⁻¹ / 5 := by
        rw [hE]
        have hpn : (N : ℝ) ^ n ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ 1 * ((N : ℝ) ^ n)⁻¹ / 5 := by
        have : 0 ≤ ((N : ℝ) ^ n)⁻¹ := by positivity
        gcongr
    _ = _ := by ring

/-- Row R1, the D3 remainder. -/
private theorem gpd_num_E5 {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ∀ S Δ K : ℝ, 1 ≤ S → S ≤ N → 0 ≤ Δ → 0 ≤ K → K * Δ ≤ 1 →
      Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ →
      K * ((2 : ℝ) ^ (4 * n + 8) * S ^ (n + 4) * (1 + (N : ℝ)) ^ (n + 4) * Δ ^ ((3 : ℝ) / 2))
        ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
  filter_upwards [gpd_ev_poly (5 * (2 : ℝ) ^ (5 * n + 12)) (a := 3 * n + 8) (b := 16 * n0 + 32)
      (by omega), eventually_ge_atTop 1] with N h1 hN S Δ K hS1 hSN hΔ hK hKΔ hΔa
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hS0 : 0 < S := by linarith
  have hsqrt : Δ ^ ((3 : ℝ) / 2) = Δ * Real.sqrt Δ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hΔ (by norm_num)]; norm_num
  have hsΔ : Real.sqrt Δ ≤ ((N : ℝ) ^ (16 * n0 + 32))⁻¹ := by
    rw [Real.sqrt_le_left (by positivity), inv_pow, ← pow_mul]
    exact hΔa.trans (le_of_eq (by ring_nf))
  have hSp : S ^ (n + 4) ≤ (N : ℝ) ^ (n + 4) := pow_le_pow_left₀ hS0.le hSN _
  have h1N : (1 + (N : ℝ)) ^ (n + 4) ≤ 2 ^ (n + 4) * (N : ℝ) ^ (n + 4) := by
    rw [add_comm]; exact gpd_one_add_pow_le hx _
  rw [hsqrt]
  have heq : K * ((2 : ℝ) ^ (4 * n + 8) * S ^ (n + 4) * (1 + (N : ℝ)) ^ (n + 4) * (Δ * Real.sqrt Δ))
      = (K * Δ) * ((2 : ℝ) ^ (4 * n + 8) * S ^ (n + 4) * (1 + (N : ℝ)) ^ (n + 4)
        * Real.sqrt Δ) := by ring
  rw [heq]
  calc (K * Δ) * ((2 : ℝ) ^ (4 * n + 8) * S ^ (n + 4) * (1 + (N : ℝ)) ^ (n + 4) * Real.sqrt Δ)
      ≤ 1 * ((2 : ℝ) ^ (4 * n + 8) * (N : ℝ) ^ (n + 4) * (2 ^ (n + 4) * (N : ℝ) ^ (n + 4))
          * ((N : ℝ) ^ (16 * n0 + 32))⁻¹) := by
        have : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
        gcongr
    _ = (2 : ℝ) ^ (5 * n + 12) * (N : ℝ) ^ (2 * n + 8) * ((N : ℝ) ^ (16 * n0 + 32))⁻¹ := by
        rw [one_mul, show (5 * n + 12) = (4 * n + 8) + (n + 4) by ring, pow_add,
          show (2 * n + 8) = (n + 4) + (n + 4) by ring, pow_add]
        ring
    _ ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
        refine gpd_le_inv_div hx0 (by norm_num) ?_
        calc 5 * ((2 : ℝ) ^ (5 * n + 12) * (N : ℝ) ^ (2 * n + 8)) * (N : ℝ) ^ n
            = 5 * (2 : ℝ) ^ (5 * n + 12) * (N : ℝ) ^ (3 * n + 8) := by
              rw [show 3 * n + 8 = (2 * n + 8) + n by ring, pow_add]; ring
          _ ≤ _ := h1

/-- Row Y2: the Hoeffding proxy of `Ỹ` is tiny against the level `N^{-2n₀-2}`. -/
private theorem gpd_num_Y {n0 n : ℕ} (hn : n ≤ 2 * n0) :
    ∀ᶠ N : ℕ in atTop, ∀ S Δ K : ℝ, 1 ≤ S → S ≤ N → 0 ≤ Δ → 0 ≤ K → K * Δ ≤ 1 →
      Δ ≤ ((N : ℝ) ^ (32 * n0 + 64))⁻¹ → K ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) →
      16 * K * ((S * ((n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n)) / 2 * (Δ / S)
          * (S ^ 2 * (N : ℝ) ^ 2) + ((N : ℝ) ^ (40 * n0 + 80))⁻¹) ^ 2
        ≤ (((N : ℝ) ^ (2 * n0 + 2))⁻¹) ^ 2 / N := by
  filter_upwards [gpd_ev_poly (16 * (n : ℝ) ^ 4 * 256 ^ n) (a := 16 * n0 + 13)
      (b := 32 * n0 + 64) (by omega),
      gpd_ev_poly (64 * (2 : ℝ) ^ (32 * n0 + 64)) (a := 36 * n0 + 69) (b := 80 * n0 + 160)
        (by omega), eventually_ge_atTop 1] with N h1 h2 hN S Δ K hS1 hSN hΔ hK hKΔ hΔa hKa
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hS0 : 0 < S := by linarith
  set bT := (S * ((n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n)) / 2 * (Δ / S)
      * (S ^ 2 * (N : ℝ) ^ 2) with hbT
  set l0 := ((N : ℝ) ^ (40 * n0 + 80))⁻¹ with hl0
  have hbT0 : 0 ≤ bT := by positivity
  have hB : (2 * (1 + (N : ℝ)) ^ 3) ^ n ≤ 16 ^ n * (N : ℝ) ^ (3 * n) := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (N : ℝ)]
  have hbT1 : bT ≤ (n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4) * Δ := by
    have e : bT = (n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n / 2 * S ^ 2 * (N : ℝ) ^ 2 * Δ := by
      rw [hbT]; field_simp
    rw [e]
    have hS2 : S ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hS0.le hSN 2
    calc (n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n / 2 * S ^ 2 * (N : ℝ) ^ 2 * Δ
        ≤ (n : ℝ) ^ 2 * (16 ^ n * (N : ℝ) ^ (3 * n)) / 2 * (N : ℝ) ^ 2 * (N : ℝ) ^ 2 * Δ := by
          gcongr
      _ = _ := by rw [show 3 * n + 4 = 3 * n + 2 + 2 by ring, pow_add, pow_add]; ring
  have hsq : (bT + l0) ^ 2 ≤ 2 * bT ^ 2 + 2 * l0 ^ 2 := by nlinarith [sq_nonneg (bT - l0)]
  have hpa : 0 < (N : ℝ) ^ (32 * n0 + 64) := by positivity
  -- the `bT` part
  have hA : 32 * K * bT ^ 2 ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
    have hc : (0 : ℝ) ≤ (n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4) := by positivity
    have h1' : bT ^ 2 ≤ ((n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4)) ^ 2 * Δ * Δ := by
      have := pow_le_pow_left₀ hbT0 hbT1 2
      calc bT ^ 2 ≤ ((n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4) * Δ) ^ 2 := this
        _ = _ := by ring
    have hKΔΔ : K * (Δ * Δ) ≤ Δ := by nlinarith
    calc 32 * K * bT ^ 2
        ≤ 32 * K * (((n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4)) ^ 2 * Δ * Δ) := by gcongr
      _ = 32 * ((n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4)) ^ 2 * (K * (Δ * Δ)) := by ring
      _ ≤ 32 * ((n : ℝ) ^ 2 * 16 ^ n / 2 * (N : ℝ) ^ (3 * n + 4)) ^ 2
          * ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by
          gcongr; exact hKΔΔ.trans hΔa
      _ = (8 * (n : ℝ) ^ 4 * 256 ^ n * (N : ℝ) ^ (6 * n + 8)) * ((N : ℝ) ^ (32 * n0 + 64))⁻¹ := by
          rw [show (256 : ℝ) ^ n = (16 ^ n) ^ 2 by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num,
            show 6 * n + 8 = (3 * n + 4) * 2 by ring, pow_mul]
          ring
      _ ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
          refine gpd_le_inv_div hx0 (by norm_num) ?_
          calc 2 * (8 * (n : ℝ) ^ 4 * 256 ^ n * (N : ℝ) ^ (6 * n + 8)) * (N : ℝ) ^ (4 * n0 + 5)
              = 16 * (n : ℝ) ^ 4 * 256 ^ n * ((N : ℝ) ^ (6 * n + 8) * (N : ℝ) ^ (4 * n0 + 5)) := by
                ring
            _ ≤ 16 * (n : ℝ) ^ 4 * 256 ^ n * (N : ℝ) ^ (16 * n0 + 13) := by
                gcongr
                rw [← pow_add]; exact pow_le_pow_right₀ hx (by omega)
            _ ≤ _ := h1
  -- the floor part
  have hB2 : 32 * K * l0 ^ 2 ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
    have hKb := hKa.trans (gpd_one_add_pow_le hx (32 * n0 + 64))
    have hl2 : l0 ^ 2 = ((N : ℝ) ^ (80 * n0 + 160))⁻¹ := by
      rw [hl0, inv_pow, ← pow_mul]; ring_nf
    rw [hl2]
    calc 32 * K * ((N : ℝ) ^ (80 * n0 + 160))⁻¹
        ≤ 32 * (2 ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64)) * ((N : ℝ) ^ (80 * n0 + 160))⁻¹ := by
          gcongr
      _ ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := by
          refine gpd_le_inv_div hx0 (by norm_num) ?_
          calc 2 * (32 * (2 ^ (32 * n0 + 64) * (N : ℝ) ^ (32 * n0 + 64))) * (N : ℝ) ^ (4 * n0 + 5)
              = 64 * (2 : ℝ) ^ (32 * n0 + 64) * (N : ℝ) ^ (36 * n0 + 69) := by
                rw [show 36 * n0 + 69 = (32 * n0 + 64) + (4 * n0 + 5) by ring, pow_add]; ring
            _ ≤ _ := h2
  have hR : (((N : ℝ) ^ (2 * n0 + 2))⁻¹) ^ 2 / N = ((N : ℝ) ^ (4 * n0 + 5))⁻¹ := by
    rw [inv_pow, ← pow_mul, div_eq_mul_inv, ← mul_inv, ← pow_succ]; ring_nf
  rw [hR]
  calc 16 * K * (bT + l0) ^ 2 ≤ 16 * K * (2 * bT ^ 2 + 2 * l0 ^ 2) := by gcongr
    _ = 32 * K * bT ^ 2 + 32 * K * l0 ^ 2 := by ring
    _ ≤ ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 + ((N : ℝ) ^ (4 * n0 + 5))⁻¹ / 2 := add_le_add hA hB2
    _ = _ := by ring

/-- The polynomial prefactor of the absorption. -/
private theorem gpd_num_tau (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, 16 * (n : ℝ) * (N : ℝ) ^ (τ / 4) ≤ (N : ℝ) ^ τ := by
  filter_upwards [eventually_le_rpow (16 * (n : ℝ)) (show 0 < 3 * τ / 4 by linarith),
    eventually_ge_atTop 1] with N h1 hN
  have hx0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : (N : ℝ) ^ τ = (N : ℝ) ^ (3 * τ / 4) * (N : ℝ) ^ (τ / 4) := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx0.le _)

end Numeric

/-! ### 16. The good events hold with high probability (rows Y1, M4, Y2, R1) -/

section Events

open scoped Matrix.Norms.L2Operator

variable (d : Dims)

/-- The dyadic floor `λ₀ = N^{-(40 n₀ + 80)}` (row M3). -/
private def gpdLam0 (n0 N : ℕ) : ℝ := ((N : ℝ) ^ (40 * n0 + 80))⁻¹

/-- The level `N^{-(2n₀+2)}` of the `Ỹ` martingale (row Y2). -/
private def gpdEpsY (n0 N : ℕ) : ℝ := ((N : ℝ) ^ (2 * n0 + 2))⁻¹

private theorem gpd_card_le (n0 n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (N + 1) × Fin (gueGridK n0 N + 1) × LoopData (d.L N) n) : ℝ)
        ≤ (N : ℝ) ^ (((2 * (32 * n0 + 64) + 2 * n + 3 : ℕ)) : ℝ) := by
  filter_upwards [d.dim, eventually_ge_atTop 2] with N hdim hN
  have hL : d.L N ≤ N := by
    have := hdim.1
    have hW := d.W_pos N
    nlinarith
  have hLD : Fintype.card (LoopData (d.L N) n) = 2 ^ n * d.L N ^ n := by
    change Fintype.card ((Fin n → Bool) × (Fin n → ZMod (d.L N))) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ZMod.card,
      Fintype.card_fin]
  have hcard : Fintype.card (Fin (N + 1) × Fin (gueGridK n0 N + 1) × LoopData (d.L N) n)
      = (N + 1) * (((N + 1) ^ (32 * n0 + 64) + 1) * (2 ^ n * d.L N ^ n)) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hLD]
    rfl
  have h1 : N + 1 ≤ N ^ 2 := by nlinarith
  have h2 : (N + 1) ^ (32 * n0 + 64) + 1 ≤ N ^ (2 * (32 * n0 + 64) + 1) := by
    have ha : (N + 1) ^ (32 * n0 + 64) ≤ N ^ (2 * (32 * n0 + 64)) := by
      calc (N + 1) ^ (32 * n0 + 64) ≤ (N ^ 2) ^ (32 * n0 + 64) := Nat.pow_le_pow_left h1 _
        _ = N ^ (2 * (32 * n0 + 64)) := by rw [← pow_mul]
    have hb : 1 ≤ N ^ (2 * (32 * n0 + 64)) := Nat.one_le_pow _ _ (by omega)
    have hc : N ^ (2 * (32 * n0 + 64) + 1) = N ^ (2 * (32 * n0 + 64)) * N := pow_succ _ _
    rw [hc]
    nlinarith
  have h3 : 2 ^ n * d.L N ^ n ≤ N ^ (2 * n) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hN _) (Nat.pow_le_pow_left hL _)
  have hnat : Fintype.card (Fin (N + 1) × Fin (gueGridK n0 N + 1) × LoopData (d.L N) n)
      ≤ N ^ (2 * (32 * n0 + 64) + 2 * n + 3) := by
    rw [hcard]
    calc (N + 1) * (((N + 1) ^ (32 * n0 + 64) + 1) * (2 ^ n * d.L N ^ n))
        ≤ N ^ 2 * (N ^ (2 * (32 * n0 + 64) + 1) * N ^ (2 * n)) := by gcongr
      _ = N ^ (2 * (32 * n0 + 64) + 2 * n + 3) := by
          rw [← pow_add, ← pow_add]; congr 1; ring
  rw [Real.rpow_natCast]
  exact_mod_cast hnat

private theorem gpd_lam0_pos (n0 N : ℕ) (hN : 1 ≤ N) : 0 < gpdLam0 n0 N := by
  unfold gpdLam0
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- **Rows M4**: all the dyadic Azuma events hold simultaneously, w.h.p. -/
private theorem gpd_highProb_Z {E t1 t0 : ℕ → ℝ} (ht10 : ∀ N, t1 N ≤ t0 N) (n0 n : ℕ) {τ : ℝ}
    (hτ : 0 < τ) :
    HighProb (Pgue d) (fun N => ⋂ u : Fin (N + 1) × Fin (gueGridK n0 N + 1) × LoopData (d.L N) n,
      {ω | ‖∑ j ∈ Finset.range (u.2.1 : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N) u.2.2.idx
          (2 ^ (u.1 : ℕ) * gpdLam0 n0 N) (j + 1) ω‖
        ≤ 2 * (N : ℝ) ^ (τ / 4) * Real.sqrt ((u.2.1 : ℕ) * (2 ^ (u.1 : ℕ) * gpdLam0 n0 N))}) := by
  refine HighProb.biInter (C := ((2 * (32 * n0 + 64) + 2 * n + 3 : ℕ) : ℝ)) (by positivity)
    (gpd_card_le d n0 n) ?_
  intro D hD
  filter_upwards [gpd_ev_exp_rpow (a := τ / 2) (by positivity) D, eventually_ge_atTop 1]
    with N hN hN1
  intro u
  obtain ⟨ℓ, k, x⟩ := u
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set lam := 2 ^ (ℓ : ℕ) * gpdLam0 n0 N with hlamdef
  have hlam : 0 < lam := mul_pos (by positivity) (gpd_lam0_pos n0 N hN1)
  have hv : 0 ≤ gpdv d t1 t0 (gueGridK n0) N := by
    unfold gpdv Grid.step
    exact div_nonneg (div_nonneg (by linarith [ht10 N]) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have huniv : {ω | ‖∑ j ∈ Finset.range (k : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N) x.idx
          lam (j + 1) ω‖ ≤ 2 * (N : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * lam)} = Set.univ := by
      ext ω; simp [hk0]
    simp only [hlamdef] at huniv
    rw [huniv, Set.compl_univ, measure_empty]; exact zero_le
  · set ε := 2 * (N : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * lam) with hεdef
    have hε0 : 0 ≤ ε := by positivity
    have hsub : {ω | ‖∑ j ∈ Finset.range (k : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N) x.idx
          lam (j + 1) ω‖ ≤ ε}ᶜ
        ⊆ {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N) x.idx
          lam (j + 1) ω‖} := fun ω hω => le_of_lt (not_le.1 (by simpa using hω))
    have haz := gpd_azuma_Z (d := d) (t1 := t1) (t0 := t0) (K := gueGridK n0) (N := N)
      (e := E N) (I := x.idx) hlam hv (k : ℕ) hε0
    have hkl : (0 : ℝ) < (k : ℕ) * lam := mul_pos (by exact_mod_cast hkpos) hlam
    have hexp : -ε ^ 2 / (4 * ((k : ℕ) * lam)) = -(N : ℝ) ^ (τ / 2) := by
      have hq : ((N : ℝ) ^ (τ / 4)) ^ 2 = (N : ℝ) ^ (τ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
      rw [hεdef, mul_pow, mul_pow, hq, Real.sq_sqrt hkl.le]
      field_simp
      ring
    rw [hexp] at haz
    calc (Pgue d) {ω | ‖∑ j ∈ Finset.range (k : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N) x.idx
          lam (j + 1) ω‖ ≤ ε}ᶜ
        ≤ (Pgue d) {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N)
          x.idx lam (j + 1) ω‖} := measure_mono hsub
      _ = ENNReal.ofReal ((Pgue d).real {ω | ε ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          gpdZst d t1 t0 (gueGridK n0) N (E N) x.idx lam (j + 1) ω‖}) :=
          (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(N : ℝ) ^ (τ / 2))) := ENNReal.ofReal_le_ofReal haz
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hN

private theorem gpd_card_le' (n0 n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (Fintype.card (Fin (gueGridK n0 N + 1) × LoopData (d.L N) n) : ℝ)
        ≤ (N : ℝ) ^ (((2 * (32 * n0 + 64) + 2 * n + 3 : ℕ)) : ℝ) := by
  filter_upwards [gpd_card_le d n0 n] with N hN
  refine le_trans ?_ hN
  have : Fintype.card (Fin (gueGridK n0 N + 1) × LoopData (d.L N) n)
      ≤ Fintype.card (Fin (N + 1) × Fin (gueGridK n0 N + 1) × LoopData (d.L N) n) := by
    rw [Fintype.card_prod (Fin (N + 1))]
    exact Nat.le_mul_of_pos_left _ (by simp)
  exact_mod_cast this

private theorem gpd_card_idx_real (N : ℕ) :
    (Fintype.card (d.Idx N) : ℝ) = (ouMatrixSize d N : ℝ) := by
  have : Fintype.card (d.Idx N) = ouMatrixSize d N := by
    change Fintype.card (ZMod (d.L N) × Fin (d.W N)) = d.L N * d.W N
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
  rw [this]

private theorem gpd_gueGridK_cast (n0 N : ℕ) :
    (gueGridK n0 N : ℝ) = ((N : ℝ) + 1) ^ (32 * n0 + 64) := by
  unfold gueGridK; push_cast; ring

/-- **The uniform truncation bound** of `T` along the grid (row Y2). -/
private theorem gpd_T_le_uniform {t1 t0 : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} {e : ℝ}
    {I : LoopIdx (ZMod (d.L N))} (he : |e| < 2) (hwf : I.WF) (ht1 : 0 ≤ t1 N)
    (hst : t1 N ≤ t0 N) (ht0 : t0 N < 1) (hK : 0 < K N) (hN0 : (0 : ℝ) < N)
    (heta : (N : ℝ)⁻¹ ≤ etaT e (t0 N)) {j : ℕ} (hj : j < K N)
    (M : Matrix (d.Idx N) (d.Idx N) ℂ) (y : Ω d) :
    ‖gpdT d N (gpdPhi d t1 t0 K N e I j) (gpdv d t1 t0 K N) M y‖
      ≤ ((Fintype.card (d.Idx N) : ℝ) * ((I.a.length : ℝ) ^ 2
          * (2 * (1 + (N : ℝ)) ^ 3) ^ I.a.length)) / 2 * gpdv d t1 t0 K N
          * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (N : ℝ) ^ 2) := by
  obtain ⟨hΔ0, _, hη, _, _, _⟩ := gpd_grid_facts (K := K) (N := N) he ht1 hst ht0 hK heta
  obtain ⟨hz, hΦ⟩ := gpd_bddC2C_Phi (d := d) (t1 := t1) (t0 := t0) (K := K) (N := N) (e := e)
    (I := I) he hwf hst ht0 hj
  have hv : 0 ≤ gpdv d t1 t0 K N := div_nonneg hΔ0 (Nat.cast_nonneg _)
  refine (gpd_norm_T_le hΦ hv M y).trans ?_
  have hpos : 0 < (zt e (Grid.time t1 t0 K N (j + 1))).im :=
    lt_of_lt_of_le (by positivity) (hη (j + 1) hj).1
  have hinv : |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹ ≤ N := by
    rw [abs_of_pos hpos, inv_le_comm₀ hpos hN0]; exact (hη (j + 1) hj).1
  have hB : 2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3 ≤ 2 * (1 + (N : ℝ)) ^ 3 := by
    have : 0 ≤ 1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹ := by positivity
    gcongr
  have : 0 ≤ 2 * (1 + |(zt e (Grid.time t1 t0 K N (j + 1))).im|⁻¹) ^ 3 := by positivity
  gcongr

set_option maxHeartbeats 1000000 in
-- many local abbreviations and `ENNReal` coercions in one assembly
/-- **Row Y2**: the `Ỹ` Azuma events hold simultaneously, w.h.p. -/
private theorem gpd_highProb_Y {κ : ℝ} (hκ : 0 < κ) (n0 n : ℕ) (hn : n ≤ 2 * n0)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (heta : ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ ≤ etaT (E N) (t0 N)) :
    HighProb (Pgue d) (fun N => ⋂ u : Fin (gueGridK n0 N + 1) × LoopData (d.L N) n,
      {ω | ‖∑ j ∈ Finset.range (u.1 : ℕ), gpdYst d t1 t0 (gueGridK n0) N (E N) u.2.idx (j + 1) ω‖
        ≤ gpdEpsY n0 N}) := by
  refine HighProb.biInter (C := ((2 * (32 * n0 + 64) + 2 * n + 3 : ℕ) : ℝ)) (by positivity)
    (gpd_card_le' d n0 n) ?_
  intro D hD
  filter_upwards [heta, gpd_num_step n0, gpd_num_Y (n := n) hn, gpd_ev_exp_lin D, d.dim,
    eventually_ge_atTop 1] with N hηN hstep hY hexpN hdim hN1
  intro u
  obtain ⟨k, x⟩ := u
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have he : |E N| < 2 := by linarith [hE N]
  have hwf : x.idx.WF := LoopData.idx_wf x
  have hlen : x.idx.a.length = n := LoopData.idx_length x
  have hK : 0 < gueGridK n0 N := Nat.pos_of_ne_zero (gueGridK_ne_zero n0 N)
  obtain ⟨hΔ0, hKΔ, _, _, _, _⟩ := gpd_grid_facts (K := gueGridK n0) (N := N) he (ht1 N)
    (ht10 N) (ht0 N) hK hηN
  set S : ℝ := (Fintype.card (d.Idx N) : ℝ) with hSdef
  set Δ := Grid.step t1 t0 (gueGridK n0) N with hΔdef
  have hvS : gpdv d t1 t0 (gueGridK n0) N = Δ / S := by
    rw [hSdef, gpd_card_idx_real]; rfl
  have hS1 : 1 ≤ S := by
    rw [hSdef]; exact_mod_cast Fintype.card_pos
  have hSN : S ≤ N := by
    rw [hSdef, gpd_card_idx_real]
    have : ouMatrixSize d N ≤ N := by unfold ouMatrixSize; rw [Nat.mul_comm]; exact hdim.1
    exact_mod_cast this
  have hKcast := gpd_gueGridK_cast n0 N
  have hTu := fun j (hj : j < gueGridK n0 N) M y =>
    gpd_T_le_uniform d (I := x.idx) he hwf (ht1 N) (ht10 N) (ht0 N) hK hN0 hηN hj M y
  rw [← hSdef, hlen] at hTu
  clear_value S Δ
  have hl0 := gpd_lam0_pos n0 N hN1
  set l0 := gpdLam0 n0 N with hl0def
  clear_value l0
  set b := (S * ((n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n)) / 2 * (Δ / S)
      * (S ^ 2 * (N : ℝ) ^ 2) + l0 with hbdef
  have hb0 : 0 < b := by
    have h1 : 0 ≤ Δ / S := div_nonneg hΔ0 (by linarith)
    have h2 : 0 ≤ (S * ((n : ℝ) ^ 2 * (2 * (1 + (N : ℝ)) ^ 3) ^ n)) / 2 := by
      have h4 : 0 ≤ (2 * (1 + (N : ℝ)) ^ 3) ^ n := pow_nonneg (by positivity) _
      exact div_nonneg (mul_nonneg (by linarith) (mul_nonneg (sq_nonneg _) h4)) zero_le_two
    have h3 : 0 ≤ S ^ 2 * (N : ℝ) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have := mul_nonneg (mul_nonneg h2 h1) h3
    rw [hbdef]; linarith
  have hb : ∀ j < gueGridK n0 N, ∀ M y, ‖gpdT d N (gpdPhi d t1 t0 (gueGridK n0) N (E N) x.idx j)
      (gpdv d t1 t0 (gueGridK n0) N) M y‖ ≤ b := by
    intro j hj M y
    refine (hTu j hj M y).trans ?_
    rw [hvS, hbdef]; linarith
  clear_value b
  have hεY : 0 ≤ gpdEpsY n0 N := by unfold gpdEpsY; positivity
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have huniv : {ω | ‖∑ j ∈ Finset.range (k : ℕ), gpdYst d t1 t0 (gueGridK n0) N (E N) x.idx
          (j + 1) ω‖ ≤ gpdEpsY n0 N} = Set.univ := by
      ext ω; simp [hk0, hεY]
    rw [huniv, Set.compl_univ, measure_empty]; exact zero_le
  · have hkK : (k : ℕ) ≤ gueGridK n0 N := Nat.lt_succ_iff.1 k.2
    have haz := gpd_azuma_Y (d := d) (t1 := t1) (t0 := t0) (K := gueGridK n0) (N := N)
      (e := E N) (I := x.idx) he hwf (ht10 N) (ht0 N) hb0.le hb hkK hεY
    have hkR : ((k : ℕ) : ℝ) ≤ (gueGridK n0 N : ℝ) := by exact_mod_cast hkK
    have hΔa := (hstep Δ hΔ0 (by rw [← hKcast]; exact hKΔ)).1
    have hkΔ : ((k : ℕ) : ℝ) * Δ ≤ 1 := le_trans (mul_le_mul_of_nonneg_right hkR hΔ0) hKΔ
    have hY' := hY S Δ ((k : ℕ) : ℝ) hS1 hSN hΔ0 (Nat.cast_nonneg _) hkΔ hΔa
      (by rw [← hKcast]; exact hkR)
    have hden : 0 < 16 * ((k : ℕ) : ℝ) * b ^ 2 := by
      have : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hkpos
      exact mul_pos (mul_pos (by norm_num) this) (pow_pos hb0 2)
    have hexp : -(gpdEpsY n0 N) ^ 2 / (4 * (((k : ℕ) : ℝ) * (4 * b ^ 2))) ≤ -(N : ℝ) := by
      have e : 4 * (((k : ℕ) : ℝ) * (4 * b ^ 2)) = 16 * ((k : ℕ) : ℝ) * b ^ 2 := by ring
      rw [e, neg_div, neg_le_neg_iff, le_div_iff₀ hden]
      have h1 := hY'
      rw [show ((N : ℝ) ^ (40 * n0 + 80))⁻¹ = l0 by rw [hl0def]; rfl, ← hbdef] at h1
      unfold gpdEpsY
      rw [le_div_iff₀ hN0] at h1
      linarith
    have hsub : {ω | ‖∑ j ∈ Finset.range (k : ℕ), gpdYst d t1 t0 (gueGridK n0) N (E N) x.idx
          (j + 1) ω‖ ≤ gpdEpsY n0 N}ᶜ
        ⊆ {ω | gpdEpsY n0 N ≤ ‖∑ j ∈ Finset.range (k : ℕ), gpdYst d t1 t0 (gueGridK n0) N (E N)
          x.idx (j + 1) ω‖} := fun ω hω => le_of_lt (not_le.1 (by simpa using hω))
    calc (Pgue d) {ω | ‖∑ j ∈ Finset.range (k : ℕ), gpdYst d t1 t0 (gueGridK n0) N (E N) x.idx
          (j + 1) ω‖ ≤ gpdEpsY n0 N}ᶜ
        ≤ (Pgue d) {ω | gpdEpsY n0 N ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          gpdYst d t1 t0 (gueGridK n0) N (E N) x.idx (j + 1) ω‖} := measure_mono hsub
      _ = ENNReal.ofReal ((Pgue d).real {ω | gpdEpsY n0 N ≤ ‖∑ j ∈ Finset.range (k : ℕ),
          gpdYst d t1 t0 (gueGridK n0) N (E N) x.idx (j + 1) ω‖}) := (ofReal_measureReal).symm
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(gpdEpsY n0 N) ^ 2
          / (4 * (((k : ℕ) : ℝ) * (4 * b ^ 2))))) := ENNReal.ofReal_le_ofReal haz
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(N : ℝ))) := by
          apply ENNReal.ofReal_le_ofReal
          have := Real.exp_le_exp.2 hexp
          linarith
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hexpN

/-- **Row R1**: the D3 remainder bounds hold almost surely, hence w.h.p. -/
private theorem gpd_highProb_AE {κ : ℝ} (hκ : 0 < κ) (n0 n : ℕ) (hn1 : 1 ≤ n)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1) :
    HighProb (Pgue d) (fun N => {ω | ∀ j < gueGridK n0 N, ∀ x : LoopData (d.L N) n,
      ‖gpdr d t1 t0 (gueGridK n0) N (E N) x.idx j ω‖
        ≤ (2 : ℝ) ^ (4 * x.idx.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (x.idx.length + 4) *
          (1 + ((zt (E N) (Grid.time t1 t0 (gueGridK n0) N (j + 1))).im)⁻¹) ^ (x.idx.length + 4) *
          Grid.step t1 t0 (gueGridK n0) N ^ ((3 : ℝ) / 2)}) := by
  intro D _
  refine Eventually.of_forall fun N => ?_
  have he : |E N| < 2 := by linarith [hE N]
  have hae : ∀ᵐ ω ∂(Pgue d), ∀ j : Fin (gueGridK n0 N), ∀ x : LoopData (d.L N) n,
      ‖gpdr d t1 t0 (gueGridK n0) N (E N) x.idx j ω‖
        ≤ (2 : ℝ) ^ (4 * x.idx.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (x.idx.length + 4) *
          (1 + ((zt (E N) (Grid.time t1 t0 (gueGridK n0) N (j + 1))).im)⁻¹) ^ (x.idx.length + 4) *
          Grid.step t1 t0 (gueGridK n0) N ^ ((3 : ℝ) / 2) := by
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro x
    have hlen : 1 ≤ x.idx.a.length := by
      have := LoopData.idx_length x
      unfold LoopIdx.length at this; omega
    exact gpd_drift_remainder_ae t1 t0 (gueGridK n0) N j (E N) he (LoopData.idx_wf x) hlen
      (ht1 N) (ht10 N) (ht0 N) j.2
  have hnull : (Pgue d) {ω | ∀ j < gueGridK n0 N, ∀ x : LoopData (d.L N) n,
      ‖gpdr d t1 t0 (gueGridK n0) N (E N) x.idx j ω‖
        ≤ (2 : ℝ) ^ (4 * x.idx.length + 8) * ((ouMatrixSize d N : ℕ) : ℝ) ^ (x.idx.length + 4) *
          (1 + ((zt (E N) (Grid.time t1 t0 (gueGridK n0) N (j + 1))).im)⁻¹) ^ (x.idx.length + 4) *
          Grid.step t1 t0 (gueGridK n0) N ^ ((3 : ℝ) / 2)}ᶜ = 0 := by
    rw [ae_iff] at hae
    refine measure_mono_null (fun ω hω => ?_) hae
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hω ⊢
    intro hall
    exact hω fun j hj x => hall ⟨j, hj⟩ x
  rw [hnull]; exact zero_le

end Events

/-! ### 17. The main theorem -/

section Main

variable (d : Dims)

set_option maxHeartbeats 1000000 in
-- the assembly of the four good events and the six exponent rows
/-- **The discrete Duhamel remainder of the GUE-phase loops** (martingale part and D3
remainders), with the random quadratic-variation control of (7.38)/(7.43), uniformly in the
grid step and the loop. Unstopped. -/
theorem gueGrid_loop_duhamel {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ)
    {E t1 t0 : ℕ → ℝ} (hE : ∀ N, |E N| ≤ 2 - κ) (ht1 : ∀ N, 0 ≤ t1 N)
    (ht10 : ∀ N, t1 N ≤ t0 N) (ht0 : ∀ N, t0 N < 1)
    (hscale : ∀ᶠ N : ℕ in atTop, (gueScale d E N (t0 N))⁻¹ ≤ (N : ℝ) ^ (-τU))
    (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 * n0) :
    StochDom (Pgue d)
      (fun N (p : Fin (gueGridK n0 N + 1) × LoopData (d.L N) n) ω =>
        ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) p.2.idx
          - gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N 0 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N 0)) p.2.idx
          - (Grid.step t1 t0 (gueGridK n0) N : ℂ) * ∑ j ∈ Finset.range p.1,
              loopDriftGUE d (E N) (Grid.time t1 t0 (gueGridK n0) N j) N p.2.idx
                (gueH d t1 t0 (gueGridK n0) N j ω)‖)
      (fun N p ω => Real.sqrt (Grid.time t1 t0 (gueGridK n0) N p.1 - t1 N) *
          (⨆ j : Fin p.1, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
              (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)))
        + (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹ ^ n) := by
  have hEb : ∀ N, |E N| < 2 := fun N => by linarith [hE N]
  have hKpos : ∀ N, 0 < gueGridK n0 N := fun N => Nat.pos_of_ne_zero (gueGridK_ne_zero n0 N)
  -- row T1: `η_{t₀} ≥ N⁻¹`
  have heta : ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ ≤ etaT (E N) (t0 N) := by
    filter_upwards [hscale, d.dim, eventually_ge_atTop 1] with N hs hdim hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hη0 : 0 < etaT (E N) (t0 N) := etaT_pos_of_lt_one (hEb N) (ht0 N)
    have hS0 : (0 : ℝ) < (((d.L N * d.W N : ℕ)) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos N)
    have hSN : (((d.L N * d.W N : ℕ)) : ℝ) ≤ N := by
      have : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact hdim.1
      exact_mod_cast this
    have hpow : (N : ℝ) ^ (-τU) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
    have h1 : 1 ≤ (((d.L N * d.W N : ℕ)) : ℝ) * etaT (E N) (t0 N) := by
      have hpos : 0 < (((d.L N * d.W N : ℕ)) : ℝ) * etaT (E N) (t0 N) := mul_pos hS0 hη0
      have := hs.trans hpow
      unfold gueScale at this
      rwa [inv_le_one_iff₀, or_iff_right (not_le.2 hpos)] at this
    rw [inv_le_iff_one_le_mul₀ hN0]
    nlinarith
  -- `ζ ≥ 0`
  have hζ0 : ∀ N (p : Fin (gueGridK n0 N + 1) × LoopData (d.L N) n) (ω : Grid.Ωg d),
      0 ≤ Real.sqrt (Grid.time t1 t0 (gueGridK n0) N p.1 - t1 N) *
          (⨆ j : Fin p.1, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
              (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)))
        + (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹ ^ n := by
    intro N p ω
    have h1 : 0 ≤ ⨆ j : Fin p.1, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
              (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)) :=
      Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
    have hle : Grid.time t1 t0 (gueGridK n0) N p.1 ≤ t0 N := by
      have hk : (p.1 : ℝ) ≤ (gueGridK n0 N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 p.1.2
      have hKp : (0 : ℝ) < (gueGridK n0 N : ℝ) := by exact_mod_cast hKpos N
      unfold Grid.time Grid.step
      have : (p.1 : ℝ) * ((t0 N - t1 N) / (gueGridK n0 N : ℝ)) ≤ t0 N - t1 N := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hKp]
        nlinarith [ht10 N]
      linarith
    have hη : 0 < etaT (E N) (Grid.time t1 t0 (gueGridK n0) N p.1) :=
      etaT_pos_of_lt_one (hEb N) (lt_of_le_of_lt hle (ht0 N))
    have h2 : 0 ≤ (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹ ^ n := by
      unfold gueScale; positivity
    have h3 := Real.sqrt_nonneg (Grid.time t1 t0 (gueGridK n0) N p.1 - t1 N)
    positivity
  -- reduction to `τ ≤ 1`
  suffices hmain : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → HighProb (Pgue d) (fun N => {ω | ∀ p :
      Fin (gueGridK n0 N + 1) × LoopData (d.L N) n,
      ‖gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N p.1 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N p.1)) p.2.idx
          - gloop (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N 0 ω)
            (zt (E N) (Grid.time t1 t0 (gueGridK n0) N 0)) p.2.idx
          - (Grid.step t1 t0 (gueGridK n0) N : ℂ) * ∑ j ∈ Finset.range p.1,
              loopDriftGUE d (E N) (Grid.time t1 t0 (gueGridK n0) N j) N p.2.idx
                (gueH d t1 t0 (gueGridK n0) N j ω)‖
        ≤ (N : ℝ) ^ τ * (Real.sqrt (Grid.time t1 t0 (gueGridK n0) N p.1 - t1 N) *
          (⨆ j : Fin p.1, Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
            (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
            loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
              (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)))
        + (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N p.1))⁻¹ ^ n)}) by
    intro τ hτ D hD
    filter_upwards [hmain (min τ 1) (lt_min hτ one_pos) (min_le_right _ _) D hD,
      eventually_ge_atTop 1] with N hN hN1
    refine le_trans (measure_mono ?_) hN
    intro ω hω hgood
    obtain ⟨p, hp⟩ := hω
    have h1 := hgood p
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hpow : (N : ℝ) ^ (min τ 1) ≤ (N : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le hN1' (min_le_left _ _)
    have := mul_le_mul_of_nonneg_right hpow (hζ0 N p ω)
    simp only at hp
    linarith
  intro τ hτ hτ1
  have hT := gue_highProb_incr_le (d := d) n0
  have hAE := gpd_highProb_AE d hκ n0 n hn1 hE ht1 ht10 ht0
  have hZ := gpd_highProb_Z d (E := E) ht10 n0 n hτ
  have hY := gpd_highProb_Y d hκ n0 n hn hE ht1 ht10 ht0 heta
  refine HighProb.mono (((hT.inter hAE).inter hZ).inter hY) ?_
  filter_upwards [heta, d.dim, gpd_num_step n0, gpd_num_Q (n := n) hn, gpd_num_E1 hn hτ1,
    gpd_num_E2 hn hτ1, gpd_num_E3 hn, gpd_num_E4 (n := n), gpd_num_E5 hn, gpd_num_tau n hτ,
    eventually_ge_atTop 1] with N hηN hdim hstep hQ hE1 hE2 hE3 hE4 hE5 htau hN1
  rintro ω ⟨⟨⟨hωT, hωAE⟩, hωZ⟩, hωY⟩ ⟨k, x⟩
  dsimp only
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have he := hEb N
  have hwf := LoopData.idx_wf x
  have hIlen : x.idx.length = n := LoopData.idx_length x
  have hIalen : x.idx.a.length = n := hIlen
  obtain ⟨hΔ0, hKΔ, hη, _, _, _⟩ := gpd_grid_facts (K := gueGridK n0) (N := N) he (ht1 N)
    (ht10 N) (ht0 N) (hKpos N) hηN
  have hKcast := gpd_gueGridK_cast n0 N
  obtain ⟨hΔa, hNΔ⟩ := hstep _ hΔ0 (by rw [← hKcast]; exact hKΔ)
  have hkK : (k : ℕ) ≤ gueGridK n0 N := Nat.lt_succ_iff.1 k.2
  have htr : ∀ j < gueGridK n0 N, ω (j + 1) ∈ gpdGood d N :=
    fun j hj i l => hωT (j + 1) (by omega) (by omega) i l
  have hr := fun j (hj : j < gueGridK n0 N) => hωAE j hj x
  have hZω : ∀ ℓ ≤ N, ‖∑ j ∈ Finset.range (k : ℕ), gpdZst d t1 t0 (gueGridK n0) N (E N) x.idx
      (2 ^ ℓ * gpdLam0 n0 N) (j + 1) ω‖
      ≤ (2 * (N : ℝ) ^ (τ / 4)) * Real.sqrt ((k : ℕ) * (2 ^ ℓ * gpdLam0 n0 N)) := by
    intro ℓ hℓ
    exact Set.mem_iInter.1 hωZ ⟨⟨ℓ, Nat.lt_succ_of_le hℓ⟩, k, x⟩
  have hYω := Set.mem_iInter.1 hωY ⟨k, x⟩
  have hQ' : 32 * (x.idx.length : ℝ) ^ 2 * Grid.step t1 t0 (gueGridK n0) N
      * ((N : ℝ) ^ (2 * x.idx.length + 2) + 2 * x.idx.length * (N : ℝ) ^ (2 * x.idx.length + 4)
        * Grid.step t1 t0 (gueGridK n0) N) < 2 ^ N * gpdLam0 n0 N := by
    rw [hIlen]; exact hQ _ hΔ0 hΔa
  have hc : 0 ≤ 2 * (N : ℝ) ^ (τ / 4) := by positivity
  have hpath := gpd_pathwise (I := x.idx) he hwf (ht1 N) (ht10 N) (ht0 N) (hKpos N)
    (gpd_lam0_pos n0 N hN1) hN1R hηN hNΔ hQ' hc htr hr hkK hZω hYω
  rw [hIlen, hIalen] at hpath
  refine hpath.trans ?_
  -- the scalar bookkeeping
  set Δ := Grid.step t1 t0 (gueGridK n0) N with hΔdef
  set sq := Real.sqrt (Grid.time t1 t0 (gueGridK n0) N (k : ℕ) - t1 N) with hsqdef
  set M := ⨆ j : Fin (k : ℕ), Real.sqrt ((((d.L N * d.W N : ℕ) : ℝ))⁻¹ *
      (etaT (E N) (Grid.time t1 t0 (gueGridK n0) N j))⁻¹ ^ 2 *
      loopMax (d.L N) (d.W N) (gueH d t1 t0 (gueGridK n0) N j ω)
        (zt (E N) (Grid.time t1 t0 (gueGridK n0) N j)) (2 * n)) with hMdef
  have hM0 : 0 ≤ M := Real.iSup_nonneg fun _ => Real.sqrt_nonneg _
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  set S : ℝ := (Fintype.card (d.Idx N) : ℝ) with hSdef
  have hSo : ((ouMatrixSize d N : ℕ) : ℝ) = S := by rw [hSdef, gpd_card_idx_real]
  have hvS : gpdv d t1 t0 (gueGridK n0) N = Δ / S := by
    rw [hSdef, gpd_card_idx_real]; rfl
  have hS1 : 1 ≤ S := by rw [hSdef]; exact_mod_cast Fintype.card_pos
  have hSN : S ≤ N := by
    rw [← hSo]
    have : ouMatrixSize d N ≤ N := by unfold ouMatrixSize; rw [Nat.mul_comm]; exact hdim.1
    exact_mod_cast this
  have hK0 : (0 : ℝ) ≤ (gueGridK n0 N : ℝ) := Nat.cast_nonneg _
  -- the five error terms
  have hT1 : 2 * (N : ℝ) ^ (τ / 4) * Real.sqrt ((k : ℕ) * gpdLam0 n0 N) ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
    refine le_trans ?_ hE1
    have hkR : ((k : ℕ) : ℝ) ≤ ((N : ℝ) + 1) ^ (32 * n0 + 64) := by
      rw [← hKcast]; exact_mod_cast hkK
    have hl := gpd_lam0_pos n0 N hN1
    have : Real.sqrt ((k : ℕ) * gpdLam0 n0 N)
        ≤ Real.sqrt (((N : ℝ) + 1) ^ (32 * n0 + 64) * ((N : ℝ) ^ (40 * n0 + 80))⁻¹) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hkR hl.le)
    exact mul_le_mul_of_nonneg_left this hc
  have hT2 : 8 * (n : ℝ) * (2 * (N : ℝ) ^ (τ / 4)) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
      ≤ ((N : ℝ) ^ n)⁻¹ / 5 := by
    have := hE2 Δ hΔ0 hΔa
    calc 8 * (n : ℝ) * (2 * (N : ℝ) ^ (τ / 4)) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ)
        = 16 * n * (N : ℝ) ^ (τ / 4) * Real.sqrt (2 * n * (N : ℝ) ^ (2 * n + 4) * Δ) := by ring
      _ ≤ _ := this
  have hT3 : gpdEpsY n0 N ≤ ((N : ℝ) ^ n)⁻¹ / 5 := hE3
  have hT4 := hE4 S Δ (gueGridK n0 N : ℝ) hS1 hSN hΔ0 hK0 hKΔ
  rw [← hvS] at hT4
  have hT5 := hE5 S Δ (gueGridK n0 N : ℝ) hS1 hSN hΔ0 hK0 hKΔ hΔa
  rw [← hSo] at hT5
  -- the prefactor and the control
  have hT6 : 8 * (n : ℝ) * (2 * (N : ℝ) ^ (τ / 4)) * sq * M ≤ (N : ℝ) ^ τ * (sq * M) := by
    have h := mul_le_mul_of_nonneg_right htau (mul_nonneg hsq0 hM0)
    calc 8 * (n : ℝ) * (2 * (N : ℝ) ^ (τ / 4)) * sq * M
        = 16 * n * (N : ℝ) ^ (τ / 4) * (sq * M) := by ring
      _ ≤ _ := h
  have hT7 : ((N : ℝ) ^ n)⁻¹
      ≤ (N : ℝ) ^ τ * (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N (k : ℕ)))⁻¹ ^ n := by
    have hηk := hη (k : ℕ) hkK
    have hSc : 0 < gueScale d E N (Grid.time t1 t0 (gueGridK n0) N (k : ℕ)) := by
      unfold gueScale
      rw [etaT_eq_zt_im]
      have : (0 : ℝ) < (((d.L N * d.W N : ℕ)) : ℝ) := by
        exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (d.W_pos N)
      exact mul_pos this (lt_of_lt_of_le (by positivity) hηk.1)
    have hScN : gueScale d E N (Grid.time t1 t0 (gueGridK n0) N (k : ℕ)) ≤ N := by
      unfold gueScale
      rw [etaT_eq_zt_im]
      have h1 : (((d.L N * d.W N : ℕ)) : ℝ) ≤ N := by
        have : (((d.L N * d.W N : ℕ)) : ℝ) = S := by rw [← hSo]; rfl
        rw [this]; exact hSN
      have h0 : (0 : ℝ) ≤ (((d.L N * d.W N : ℕ)) : ℝ) := Nat.cast_nonneg _
      calc (((d.L N * d.W N : ℕ)) : ℝ) * (zt (E N) (Grid.time t1 t0 (gueGridK n0) N (k : ℕ))).im
          ≤ (N : ℝ) * 1 := mul_le_mul h1 hηk.2 (lt_of_lt_of_le (by positivity) hηk.1).le hN0.le
        _ = N := mul_one _
    have hinv : (N : ℝ)⁻¹ ≤ (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N (k : ℕ)))⁻¹ :=
      inv_anti₀ hSc hScN
    have hpow : ((N : ℝ) ^ n)⁻¹
        ≤ (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N (k : ℕ)))⁻¹ ^ n := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (by positivity) hinv n
    have hNτ : (1 : ℝ) ≤ (N : ℝ) ^ τ := Real.one_le_rpow hN1R hτ.le
    have h0 : 0 ≤ (gueScale d E N (Grid.time t1 t0 (gueGridK n0) N (k : ℕ)))⁻¹ ^ n :=
      pow_nonneg (inv_nonneg.2 hSc.le) n
    exact hpow.trans (le_mul_of_one_le_left h0 hNτ)
  rw [mul_add]
  linarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7]

end Main

end RBM.Gauss.GUEGrid
