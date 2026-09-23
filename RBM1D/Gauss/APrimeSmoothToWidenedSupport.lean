/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeSmoothWeightActual

/-!
# T599: buffered support from the actual smooth weight to the widened weight

This deterministic bridge compares the two literal prefix cutoffs on the same sample,
at the same net index.  Positivity of the actual smooth weight at exponent `delta`
eventually implies positivity of the canonical widened weight at exponent `delta + xi`.
The only asymptotic loss is the factor `N^(2 * xi)` used to absorb the fixed constant
`4 * exp(1)^2`.

No event, moment estimate, regularity package, or quadratic-variation conclusion is used.
In particular, this module does not assert the false reverse support implication at the
same exponent.
-/

namespace RBM
namespace APrimeSmoothToWidenedSupport

open Filter Real Step2Bootstrap CutHypTheta Cutoff

private theorem cutChi_pos_of_lt_two {x : Real} (hx2 : x < 2) :
    0 < cutChi x := by
  by_cases hx1 : x <= 1
  · rw [cutChi_eq_one hx1]
    norm_num
  · have h1 : 1 < x := lt_of_not_ge hx1
    have ht0 : 0 < x - 1 := by linarith
    have hm1 : max (x - 1) 0 = x - 1 := max_eq_left ht0.le
    have hm2 : max (x - 2) 0 = 0 := max_eq_right (by linarith)
    rw [cutChi, hm1, hm2]
    have hid :
        1 - (6 * (x - 1) ^ 5 - 15 * (x - 1) ^ 4 + 10 * (x - 1) ^ 3) =
          (1 - (x - 1)) ^ 3 * (1 + 3 * (x - 1) + 6 * (x - 1) ^ 2) := by
      ring
    rw [hid]
    have hleft : 0 < (1 - (x - 1)) ^ 3 := pow_pos (by linarith) _
    have hright : 0 < 1 + 3 * (x - 1) + 6 * (x - 1) ^ 2 := by
      nlinarith [sq_nonneg (x - 1)]
    positivity

private theorem prefixSample_eq_softMax (d : Gauss.Dims)
    (E D : Real) (s mesh : Nat -> Real) (N k m : Nat) (omega : Gauss.Ω d) :
    APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega =
      softMax m (Finset.range k) (fun j =>
        APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N j)
          (APrimeSmoothWeightActual.epsilon d D N) m omega) := by
  change softMax m (Finset.range k) (fun j =>
    APrimeSmoothPrefix.smoothJSMatrix d E D s N (cutNetPt s mesh N j)
      (APrimeSmoothWeightActual.epsilon d D N) m
      ((Real.sqrt (cutNetPt s mesh N j) : Complex) • Gauss.Xmat d N omega)) = _
  apply congrArg (fun f : Nat -> Real => softMax m (Finset.range k) f)
  funext j
  have hflow := APrimeSmoothPrefix.smoothJSMatrix_flow d E D s N
    (cutNetPt s mesh N j) (APrimeSmoothWeightActual.epsilon d D N) m omega
  rw [Gauss.Hflow_eq_realSmul] at hflow
  exact hflow

/-- For every fixed positive buffer `xi`, positive support of the literal actual smooth
weight at `delta` is eventually contained in positive support of the canonical widened
weight at `delta + xi`.  The eventual threshold is uniform in every active prefix `k`
and every sample `omega`; all observables use the same `N`, `k`, sample, and net. -/
theorem eventually_actualWeight_pos_implies_widenedW_pos
    (d : Gauss.Dims)
    {E D delta xi : Real} {s t mesh : Nat -> Real}
    (hE : |E| < 2)
    (hst : forall N, s N <= t N)
    (ht1 : forall N, t N < 1)
    (hmesh : forall N, 0 < mesh N)
    (hxi : 0 < xi)
    (p : Nat) (hp : 1 <= p) :
    ∀ᶠ N : Nat in Filter.atTop, forall k : Nat,
      k <= cutNetTop s t mesh N ->
      forall omega : Gauss.Ω d,
        0 < APrimeSmoothWeightActual.weight d E D delta s t mesh
          2 p N k (APrimeSmoothWeightActual.canonicalM d s t mesh N) omega ->
        0 < APrimeWeight.widenedW
          (APrimeWeight.canonicalR s t mesh) 1
          (fun N u omega =>
            Step2Moment.jSnorm (Gauss.sample d) E D s N u omega)
          s t mesh (delta + xi) p N k omega := by
  have hpowTop : Tendsto (fun N : Nat => (N : Real) ^ (2 * xi)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 * xi)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hpowTop.eventually_gt_atTop (4 * (Real.exp 1) ^ 2),
    eventually_ge_atTop 2] with N habsorb hN2
  intro k hk omega hweight
  let m : Nat := APrimeSmoothWeightActual.canonicalM d s t mesh N
  let S : Real := APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega
  let J : Nat -> Real := fun j =>
    Step2Moment.jSnorm (Gauss.sample d) E D s N (cutNetPt s mesh N j) omega
  let H : Real := softMax (APrimeWeight.canonicalR s t mesh N)
    (Finset.range k) J
  have hN : 0 < N := by omega
  have hN1 : 1 <= N := by omega
  have hm : 1 <= m := by
    exact APrimeSmoothWeightActual.canonicalM_pos d s t mesh N
  have hactiveActual : k <= cutNetTop s t mesh N ∧ 2 <= N := ⟨hk, hN2⟩
  have hactiveWide : k <= cutNetTop s t mesh N ∧ 1 <= N := ⟨hk, hN1⟩
  have hpowne : 2 * p ≠ 0 := by omega
  have hcutpow :
      0 < (APrimeSmoothWeightActual.cutoff d E D delta s mesh N k m omega) ^
        (2 * p) := by
    simpa [APrimeSmoothWeightActual.weight, hactiveActual, m] using hweight
  have hcutne :
      APrimeSmoothWeightActual.cutoff d E D delta s mesh N k m omega ≠ 0 := by
    intro hz
    rw [hz, zero_pow hpowne] at hcutpow
    exact (lt_irrefl 0) hcutpow
  have hthetaActual : 0 < APrimeSmoothWeightActual.threshold delta N :=
    APrimeSmoothWeightActual.threshold_pos hN
  have hratioActual :
      S / APrimeSmoothWeightActual.threshold delta N < 2 := by
    by_contra hnot
    have hz : APrimeSmoothWeightActual.cutoff d E D delta s mesh N k m omega = 0 := by
      unfold APrimeSmoothWeightActual.cutoff
      exact cutChi_eq_zero (le_of_not_gt hnot)
    exact hcutne hz
  have hSlt : S < 2 * APrimeSmoothWeightActual.threshold delta N := by
    exact (div_lt_iff₀ hthetaActual).mp hratioActual
  have hS0 : 0 <= S := by
    change 0 <= APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega
    rw [prefixSample_eq_softMax]
    exact softMax_nonneg _ _ _
  have hs1 : s N < 1 := (hst N).trans_lt (ht1 N)
  have hJle : forall j, j ∈ Finset.range k -> |J j| <= S := by
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have huIcc : cutNetPt s mesh N j ∈ Set.Icc (s N) (t N) :=
      MomentDuhamelCut.netFinset_subset_Icc (hst N) (hmesh N) _
        (cutNetPt_mem_netFinset (hjk.le.trans hk))
    have hinner := APrimeSmoothPrefix.jSnorm_le_smoothJS d
      (E := E) (D := D) (u := cutNetPt s mesh N j)
      (ε := APrimeSmoothWeightActual.epsilon d D N) (s := s) (N := N)
      hE hs1 (huIcc.2.trans_lt (ht1 N))
      (APrimeSmoothWeightActual.epsilon_pos d D hN).le hm omega
    have houter :
        APrimeSmoothPrefix.smoothJS d E D s N (cutNetPt s mesh N j)
            (APrimeSmoothWeightActual.epsilon d D N) m omega <= S := by
      change _ <= APrimeSmoothWeightActual.prefixSample d E D s mesh N k m omega
      rw [prefixSample_eq_softMax]
      exact (le_abs_self _).trans (le_softMax
        (ρ := fun i => APrimeSmoothPrefix.smoothJS d E D s N
          (cutNetPt s mesh N i) (APrimeSmoothWeightActual.epsilon d D N) m omega)
        hm hj)
    rw [abs_of_nonneg]
    · exact hinner.trans houter
    · unfold J
      unfold Step2Moment.jSnorm
      exact div_nonneg
        ((show (0 : Real) <= 1 by norm_num).trans
          (Step2Moment.one_le_jS (Gauss.sample d) N
            (cutNetPt s mesh N j) omega))
        (by positivity)
  have hHle : H <= Real.exp 1 * S := by
    have hsoft := softMax_le
      (r := APrimeWeight.canonicalR s t mesh N)
      (S := Finset.range k)
      (by simp [APrimeWeight.canonicalR]) hS0 hJle
    have hcal := APrimeWeight.card_calib_top (cutNetTop s t mesh N) k hk
    calc
      H <= (k : Real) ^
          ((1 : Real) / (2 * (APrimeWeight.canonicalR s t mesh N : Real))) * S := by
        simpa [H] using hsoft
      _ <= Real.exp 1 * S := mul_le_mul_of_nonneg_right
        (by simpa [APrimeWeight.canonicalR] using hcal) hS0
  have hSlt' : S < 16 * (Real.exp 1) ^ 2 * (N : Real) ^ (2 * delta) := by
    convert hSlt using 1
    unfold APrimeSmoothWeightActual.threshold
    ring
  have hHlt : H < 16 * (Real.exp 1) ^ 3 * (N : Real) ^ (2 * delta) := by
    calc
      H <= Real.exp 1 * S := hHle
      _ < Real.exp 1 * (16 * (Real.exp 1) ^ 2 * (N : Real) ^ (2 * delta)) :=
        mul_lt_mul_of_pos_left hSlt' (Real.exp_pos 1)
      _ = 16 * (Real.exp 1) ^ 3 * (N : Real) ^ (2 * delta) := by ring
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hrpowAdd :
      (N : Real) ^ (2 * (delta + xi)) =
        (N : Real) ^ (2 * delta) * (N : Real) ^ (2 * xi) := by
    rw [show 2 * (delta + xi) = 2 * delta + 2 * xi by ring,
      Real.rpow_add hNreal]
  have hHwide : H < 4 * Real.exp 1 * (N : Real) ^ (2 * (delta + xi)) := by
    calc
      H < 16 * (Real.exp 1) ^ 3 * (N : Real) ^ (2 * delta) := hHlt
      _ = (4 * Real.exp 1 * (N : Real) ^ (2 * delta)) *
          (4 * (Real.exp 1) ^ 2) := by ring
      _ < (4 * Real.exp 1 * (N : Real) ^ (2 * delta)) *
          (N : Real) ^ (2 * xi) :=
        mul_lt_mul_of_pos_left habsorb (by positivity)
      _ = 4 * Real.exp 1 * (N : Real) ^ (2 * (delta + xi)) := by
        rw [hrpowAdd]
        ring
  have hden : 0 < 2 * Real.exp 1 * (N : Real) ^ (2 * (delta + xi)) := by
    positivity
  have hratioWide :
      H / (2 * Real.exp 1 * (N : Real) ^ (2 * (delta + xi))) < 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hcutWide :
      0 < cutChi (H / (2 * Real.exp 1 * (N : Real) ^ (2 * (delta + xi)))) :=
    cutChi_pos_of_lt_two hratioWide
  rw [APrimeWeight.widenedW, ite_eq_left hactiveWide]
  change 0 < (cutChi (H /
    (2 * Real.exp 1 * APrimePrior.priorLevel (delta + xi) (fun _ => 1) N))) ^
      (2 * p)
  simpa [APrimePrior.priorLevel] using pow_pos hcutWide (2 * p)

#print axioms eventually_actualWeight_pos_implies_widenedW_pos

end APrimeSmoothToWidenedSupport
end RBM
