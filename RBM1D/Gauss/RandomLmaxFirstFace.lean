/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxMinorProxy
import RBM1D.Gauss.Lemma41Glue

/-!
# First deletion face of an embedded minor loop

This module starts the fixed-time first-cell first-face argument by recording the exact
finite-sum face identity and the empty-minor orientation bridge.  It does not yet prove the
same-event endpoint, loop, or squared-loop bounds required for the first-face estimate.
-/

namespace RBM.Gauss

open scoped BigOperators

/-- The first deletion face of the squared Hilbert--Schmidt block loop is the sum of the
coordinatewise squared-entry faces.  The block indicator is kept inside the sum, so this
identity includes coordinates on either block boundary and coordinates deleted already. -/
theorem embeddedMinorLoop_sub_insert_eq_sum (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) (κ : d.Idx N) (a b : ZMod (d.L N)) :
    embeddedMinorLoop d N u z S ω a b -
        embeddedMinorLoop d N u z (insert κ S) ω a b =
      ((d.W N : ℝ)⁻¹) ^ 2 *
        ∑ p : d.Idx N × d.Idx N,
          if proxyBlock d N p.1 = a ∧ proxyBlock d N p.2 = b then
            (‖gEnt d N u z ω p.1 p.2 S‖ ^ 2 -
              ‖gEnt d N u z ω p.1 p.2 (insert κ S)‖ ^ 2) else 0 := by
  classical
  unfold embeddedMinorLoop
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : proxyBlock d N p.1 = a ∧ proxyBlock d N p.2 = b
  · simp [h]
  · simp [h]

/-- At every coordinate, including one whose row or column is the pivot, the first face is the
zero-embedded form of (4.9).  The rank-one formula is valid before any block restriction. -/
theorem gEnt_sub_insert_rankOne (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ)
    (ω : Ω d) (Ψ : ℝ) (M : ℕ) (S : Finset (d.Idx N)) (κ a b : d.Idx N)
    (hg : MinorGoodLe d N u z m ω Ψ M)
    (hcard : (insert κ S).card ≤ M) :
    gEnt d N u z ω a b S - gEnt d N u z ω a b (insert κ S) =
      gEnt d N u z ω a κ S * gEnt d N u z ω κ b S *
        (gEnt d N u z ω κ κ S)⁻¹ := by
  have h := deltaFam_gFam_apply hg a b κ ∅ S (by simpa using hcard)
  simpa only [deltaFam_apply, gFam_apply, gInvFam_apply, Finset.union_empty] using h

/-- At the empty minor, the proxy's ordered block pair is the reversed paper `Lre` pair.
This is the same orientation as (4.11), whose `Lre` entry has row block `b` and column block
`a`. -/
theorem embeddedMinorLoop_empty_eq_Lre_rev (d : Dims) (N : ℕ) (u : ℝ)
    (ω : Ω d) (a b : ZMod (d.L N)) :
    embeddedMinorLoop d N u (zt 0 u) ∅ ω a b =
      Lre (Hflow d N u ω) (zt 0 u) b a := by
  classical
  rw [embeddedMinorLoop, Lre_eq (Hflow_isHermitian d N u ω) b a]
  simp only [proxyBlock, gEnt_empty]
  simp_rw [Fintype.sum_prod_type]
  simp [eq_comm, ite_and]

end RBM.Gauss
