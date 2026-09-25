/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxFlucAvg

/-!
# Actual first-cell WLL/REL entry inputs at random `Lmax`

The accepted first-cell Step-1 local-law witness supplies the fixed-time,
time-uniform entry WLL.  On its own high-probability flow good event, the same
sample also satisfies `W⁻¹ ≤ 4 Lmax`.  Since `firstCellPsi² = 1/(4W)`, the
entry WLL squares to an all-tolerance REL bound against that sample's `Lmax`.

The old `N^(1/8)` event estimate in `RandomLmaxFlucAvg` is used below only for
the requested actual-model nonempty positive-time witness; it is not used to
prove the REL statement.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- The exact all-tolerance fixed-time entry WLL furnished by the actual Step-1
local-law witness.  The target control is the paper-scale `firstCellPsi`. -/
theorem firstCell_randomLmax_entry_WLL {τ' : ℝ}
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
          (if ij.1 = ij.2 then mE 0 else 0)‖)
      (fun N _ _ _ => firstCellPsi N) := by
  change UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
    (fun N u (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) ω =>
      ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
        (if ij.1 = ij.2 then mE 0 else 0)‖)
    (fun N _ _ _ => firstCellPsi N) at hll
  exact hll

/-- The local law makes the actual first-cell good event high probability,
uniformly over the entire noncollapsed time interval. -/
theorem firstCell_randomLmax_goodSet_highProb {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi) :
    HighProb (P Dims.exampleGrow)
      (goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
        firstCellDelta) := by
  let d := Dims.exampleGrow
  have hs0 : ∀ N, 0 ≤ firstCellS τ' N := by
    intro N
    change 0 ≤ gridT ((band d).W N : ℝ) τ' (1 / 2 : ℝ) 0
    rw [gridT_zero (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have ht1 : ∀ N, firstCellT τ' N < 1 := by
    intro N
    exact (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hst : ∀ N, firstCellS τ' N ≤ firstCellT τ' N := by
    intro N
    exact gridT_mono (by exact_mod_cast (band d).one_le_W N) hτ'.le
      (1 / 2 : ℝ) (Nat.zero_le 1)
  obtain ⟨hΨpos, _, _, _, _, hΨlowLL, _, hmargin, _, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  obtain ⟨hKbig, _, _, _⟩ := first_cell_polynomial_regime d τ'
  exact highProb_goodSetFlow_of_localLaw d
    (τ := (1 : ℝ) / 16) (E := 0) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellDelta) (Ψ := firstCellPsi)
    (K := 3) (B := 2) (by norm_num) (by norm_num)
    hs0 ht1 hst (by norm_num) (by norm_num) hKbig
    (fun N => (hΨpos N).le) hΨlowLL hll hmargin

/-- All entry squares are REL with respect to the same sample's actual `Lmax`.

The proof keeps the local-law failure event and the first-cell weak-law event
on the same probability space.  On their intersection, (4.1) gives
`W⁻¹ ≤ 4 Lmax` at every deterministic time and `firstCellPsi² = 1/(4W)`;
the uniform local law therefore yields the claimed square bound.  This is the
uniform-in-time same-event route recorded in T1411 §8.  For the formula-level
split in Lemma 4.1, off-diagonal entries have the scope of (4.2), while the
centered diagonal is governed by (4.3). -/
theorem firstCell_randomLmax_entry_REL {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
          (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2)
      (fun N u _ ω =>
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
  let d := Dims.exampleGrow
  have hΨ0 : ∀ N, 0 ≤ firstCellPsi N := fun N => (firstCellPsi_pos N).le
  have hWLL : UnifDomIcc (P d) (firstCellS τ') (firstCellT τ')
      (fun N u (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
          (if ij.1 = ij.2 then mE 0 else 0)‖)
      (fun N _ _ _ => firstCellPsi N) :=
    firstCell_randomLmax_entry_WLL hll
  have hsq : UnifDomIcc (P d) (firstCellS τ') (firstCellT τ')
      (fun N u (ij : Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) ij.1 ij.2 -
          (if ij.1 = ij.2 then mE 0 else 0)‖ ^ 2)
      (fun N _ _ _ => firstCellPsi N ^ 2) := by
    have hmul := UnifDomIcc.mul'
      (fun N u ij ω => norm_nonneg _)
      (fun N u ij ω => hΨ0 N)
      hWLL hWLL
    simpa only [pow_two] using hmul
  obtain ⟨_, _, _, _, _, _, hΨW, _, hδ1, _, _, _, _, _, _⟩ :=
    first_cell_joint_grid_scales hτ'
  have hΨW' : ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
      4 * ((d.W N : ℕ) : ℝ) * firstCellPsi N ^ 2 ≤ (N : ℝ) ^ τ := by
    intro τ hτ
    simpa [d, firstCellPsi, pow_two] using hΨW τ hτ
  exact hsq.trans (unifDomIcc_const_Lmax (V := fun N => d.Idx N × d.Idx N)
    d (by norm_num) hδ1 (firstCell_randomLmax_goodSet_highProb hτ' hll) hΨW')

/-- Centered diagonal specialization of the all-entry REL theorem.  This is
the index scope of the diagonal estimate (4.3). -/
theorem firstCell_randomLmax_diag_REL {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u i ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) i i - mE 0‖ ^ 2)
      (fun N u _ ω =>
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
  have h := firstCell_randomLmax_entry_REL hτ' hll
  have hp := UnifDomIcc.precomp
      (P := P Dims.exampleGrow)
      (V := fun N => Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N)
      (V' := fun N => Dims.exampleGrow.Idx N)
      (s := firstCellS τ') (t := firstCellT τ')
      (fun N i => (i, i)) h
  simpa using hp

/-- Off-diagonal specialization of the all-entry REL theorem.  This is the
index scope of the off-diagonal estimate (4.2). -/
theorem firstCell_randomLmax_offdiag_REL {τ' : ℝ} (hτ' : 0 < τ')
    (hll : LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
      (firstCellT τ') firstCellPsi) :
    UnifDomIcc (P Dims.exampleGrow) (firstCellS τ') (firstCellT τ')
      (fun N u (v : OffPair Dims.exampleGrow.L Dims.exampleGrow.W N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) v.1.1 v.1.2‖ ^ 2)
      (fun N u _ ω =>
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
  have h := firstCell_randomLmax_entry_REL hτ' hll
  have hp := UnifDomIcc.precomp
      (P := P Dims.exampleGrow)
      (V := fun N => Dims.exampleGrow.Idx N × Dims.exampleGrow.Idx N)
      (V' := fun N => OffPair Dims.exampleGrow.L Dims.exampleGrow.W N)
      (s := firstCellS τ') (t := firstCellT τ')
      (fun N (v : OffPair Dims.exampleGrow.L Dims.exampleGrow.W N) => v.1) h
  apply UnifDomIcc.of_le_left
      (ξ := fun N u (v : OffPair Dims.exampleGrow.L Dims.exampleGrow.W N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) v.1.1 v.1.2 -
          (if v.1.1 = v.1.2 then mE 0 else 0)‖ ^ 2)
      (ξ' := fun N u (v : OffPair Dims.exampleGrow.L Dims.exampleGrow.W N) ω =>
        ‖green (Hflow Dims.exampleGrow N u ω) (zt 0 u) v.1.1 v.1.2‖ ^ 2)
      ?_ hp
  intro N u v ω
  rw [ite_eq_right v.2, sub_zero]

/-- The moving first-cell endpoint obeys the required polynomial spectral floor
with `K = 1`; the bound starts at `N ≥ 2`. -/
theorem firstCell_eta_floor_K1 {τ' : ℝ} :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(1 : ℝ)) ≤ etaT 0 (firstCellT τ' N) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have ht : firstCellT τ' N ≤ 1 / 2 :=
    gridT_le (1 / 2 : ℝ) 1
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hη : etaT 0 (firstCellT τ' N) = 1 - firstCellT τ' N := by
    simp [etaT, mE_im, hsqrt]
  have hηhalf : (1 / 2 : ℝ) ≤ etaT 0 (firstCellT τ' N) := by
    rw [hη]
    linarith
  have hNinv : (N : ℝ) ^ (-(1 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg hNpos.le, Real.rpow_one]
    have hinv : (N : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hN2
    norm_num at hinv ⊢
    exact hinv
  exact hNinv.trans hηhalf

/-- The actual Gaussian first cell has an inhabited weak-law event and a
positive interior time with positive diagonal second moment on that same
event.  The event is taken directly from the Step-1 local-law witness. -/
theorem firstCell_randomLmax_actual_nondegenerate_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ')
        (firstCellT τ') firstCellPsi ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ')
          (firstCellT τ') firstCellDelta N,
          ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
            0 < u ∧ u < firstCellT τ' N ∧
              ∀ i : Dims.exampleGrow.Idx N,
                0 < ∫ ω', ‖Hflow Dims.exampleGrow N u ω' i i‖ ^ 2
                  ∂(P Dims.exampleGrow) := by
  obtain ⟨τ', hτ', hll, hnonempty⟩ := firstCell_step1_localLaw_witness
  refine ⟨τ', hτ', hll, ?_⟩
  filter_upwards [hnonempty] with N hN
  rcases hN with ⟨hinterval, hset⟩
  obtain ⟨ω, hω⟩ := hset
  obtain ⟨u, hu, hu0, hut⟩ := firstCell_positive_interior_time hinterval
  refine ⟨ω, hω, u, hu, hu0, hut, ?_⟩
  intro i
  exact firstCell_positive_diag_flow_second_moment i hu0

#print axioms firstCell_randomLmax_entry_WLL
#print axioms firstCell_randomLmax_goodSet_highProb
#print axioms firstCell_randomLmax_entry_REL
#print axioms firstCell_randomLmax_diag_REL
#print axioms firstCell_randomLmax_offdiag_REL
#print axioms firstCell_eta_floor_K1
#print axioms firstCell_randomLmax_actual_nondegenerate_witness

end RBM.Gauss
