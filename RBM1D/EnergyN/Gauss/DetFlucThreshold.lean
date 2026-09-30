/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetFlucThreshold
import RBM1D.EnergyN.Gauss.GoodSetFlow
import RBM1D.EnergyN.Gauss.DetFlucAvg

/-!
# The fluctuation threshold at a fixed time, at an `N`-dependent energy

Six statements at an `N`-dependent energy `E : ℕ → ℝ`: the uniform local law with the control
`detFlucControl Ψ` (`RBM.Gauss.localLaw_detFlucControlN`); three consequences of `N^{-K} ≤ η_u`
(`RBM.Gauss.etaInv_le_rpow_of_lowerN`, `RBM.Gauss.etaPolyHi_of_lowerN`,
`RBM.Gauss.etaNet_bound_of_lowerN`); the good set at `δ = detFlucDelta Ψ θ` with high
probability (`RBM.Gauss.highProb_detFlucDelta_of_localLawN`); and the moment gain at that `δ`
(`RBM.Gauss.fixedMoment_gain_of_localLawN`). No energy-dependent constant is fixed in this file.

`localLaw_detFlucControlN` uses only the generic `UnifDomIcc.mono_control` (no `E` binder of its
own) at the predicate `LocalLawUnifIccN` (`RBM1D/EnergyN/Gauss/GoodSetFlow.lean`);
`highProb_detFlucDelta_of_localLawN` uses `highProb_goodSetFlow_of_localLawN` (same file);
`fixedMoment_gain_of_localLawN` uses `fixedMoment_gain_of_goodSetFlowN`
(`RBM1D/EnergyN/Gauss/DetFlucAvg.lean`). None of
`detFlucControl`/`detFlucDelta`/
`detFlucDelta_margin`/`detFlucDelta_moment_small`/`detFlucDelta_pos`/`detFlucDelta_le_quarter`/
`detFlucDelta_polyLo`/`eventually_W_inv_le_detFlucDelta_sq` carries an `E`-binder.
-/

namespace RBM.Gauss

open Filter MeasureTheory Topology

/-- **The uniform local law at `u` with the larger control `detFlucControl Ψ`.** No
energy-dependent constant is fixed here (`UnifDomIcc.mono_control` is generic, no `E`-binder of
its own). -/
theorem localLaw_detFlucControlN {d : Dims} {E : ℕ → ℝ} {u Ψ : ℕ → ℝ}
    (hll : LocalLawUnifIccN d E u u Ψ) :
    LocalLawUnifIccN d E u u (detFlucControl Ψ) :=
  UnifDomIcc.mono_control hll (fun N _ _ _ => detFlucControl_ge_psi Ψ N)

/-- **`η_u⁻¹ ≤ N^K` eventually**, from `N^{-K} ≤ η_u`. No energy-dependent constant is fixed
here. -/
theorem etaInv_le_rpow_of_lowerN {E : ℕ → ℝ} {K : ℝ} {u : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N)) :
    ∀ᶠ N : ℕ in atTop, (etaT (E N) (u N))⁻¹ ≤ (N : ℝ) ^ K := by
  filter_upwards [hη, eventually_ge_atTop 1] with N hηN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hηpos : 0 < etaT (E N) (u N) := etaT_pos_of_lt_one (hE N) (hu1 N)
  have hpow : 0 < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hn _
  have h := inv_anti₀ hpow hηN
  rw [Real.rpow_neg hn.le, inv_inv] at h
  exact h

/-- **`η_u⁻¹ + 1` is polynomially bounded** (`PolyHi`), from `N^{-K} ≤ η_u`. No energy-dependent
constant is fixed here. -/
theorem etaPolyHi_of_lowerN {E : ℕ → ℝ} {K : ℝ} {u : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N)) :
    PolyHi (fun N => (etaT (E N) (u N))⁻¹ + 1) := by
  refine ⟨2, by norm_num, K, ?_⟩
  filter_upwards [etaInv_le_rpow_of_lowerN hE hu1 hK hη,
    eventually_ge_atTop 1] with N hInv hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hOne : (1 : ℝ) ≤ (N : ℝ) ^ K := Real.one_le_rpow hn hK
  linarith

/-- **`η_u⁻² (N + 1) ≤ N^{2K+2}` eventually**, from `N^{-K} ≤ η_u`. No energy-dependent constant
is fixed here. -/
theorem etaNet_bound_of_lowerN {E : ℕ → ℝ} {K : ℝ} {u : ℕ → ℝ}
    (hE : ∀ N, |E N| < 2) (hu1 : ∀ N, u N < 1) (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N)) :
    ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (u N))⁻¹ * (etaT (E N) (u N))⁻¹ * ((N : ℝ) + 1)
        ≤ (N : ℝ) ^ (2 * K + 2) := by
  filter_upwards [etaInv_le_rpow_of_lowerN hE hu1 hK hη,
    eventually_ge_atTop 2] with N hInv hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN2 : (N : ℝ) + 1 ≤ (N : ℝ) ^ (2 : ℕ) := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hInv0 : 0 ≤ (etaT (E N) (u N))⁻¹ := inv_nonneg.mpr
    (etaT_pos_of_lt_one (hE N) (hu1 N)).le
  have hPow0 : 0 ≤ (N : ℝ) ^ K := by positivity
  have hsq : (etaT (E N) (u N))⁻¹ * (etaT (E N) (u N))⁻¹ ≤
      (N : ℝ) ^ K * (N : ℝ) ^ K := by nlinarith
  calc
    (etaT (E N) (u N))⁻¹ * (etaT (E N) (u N))⁻¹ * ((N : ℝ) + 1)
        ≤ ((N : ℝ) ^ K * (N : ℝ) ^ K) * ((N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
    _ ≤ ((N : ℝ) ^ K * (N : ℝ) ^ K) * (N : ℝ) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hN2 (by positivity)
    _ = (N : ℝ) ^ (2 * K + 2) := by
          rw [← Real.rpow_add hn, ← Real.rpow_natCast, ← Real.rpow_add hn]
          congr 1
          ring

/-- **The good set `goodSetFlow` at the time `u` with `δ = detFlucDelta Ψ θ` holds with high
probability**, from the uniform local law with `Ψ ≤ N^{-a}`. No energy-dependent constant is
fixed here (it uses `highProb_goodSetFlow_of_localLawN`). -/
theorem highProb_detFlucDelta_of_localLawN (d : Dims) {E : ℕ → ℝ} {u Ψ : ℕ → ℝ}
    {a K θ : ℝ} (hE : ∀ N, |E N| < 2) (hu0 : ∀ N, 0 ≤ u N)
    (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIccN d E u u Ψ) :
    HighProb (P d) (fun N => goodSetFlow d (E N) u u (detFlucDelta Ψ θ) N) := by
  exact highProb_goodSetFlow_of_localLawN d (half_pos hθ0) hE hu0 hu1
    (fun _ => le_rfl) (by linarith : 0 ≤ 2 * K + 2) (by norm_num : 0 ≤ (4 : ℝ))
    (etaNet_bound_of_lowerN hE hu1 hK hη)
    (fun N => (detFlucControl_pos Ψ N).le)
    (detFlucControl_rpow_neg_four_le Ψ)
    (localLaw_detFlucControlN hll)
    (detFlucDelta_margin ha hθ0 hθa hθ1 hΨhi)

/-- **The moment gain `FlucGainUpTo'` at the time `u` with `δ = detFlucDelta Ψ θ`, and
`W⁻¹ ≤ (4 detFlucDelta Ψ θ)^2`**, eventually, from the uniform local law. No energy-dependent
constant is fixed here (it uses `fixedMoment_gain_of_goodSetFlowN`). -/
theorem fixedMoment_gain_of_localLawN (d : Dims) {E : ℕ → ℝ} {u Ψ : ℕ → ℝ}
    {a K θ : ℝ} (hE : ∀ N, |E N| < 2) (hu0 : ∀ N, 0 ≤ u N)
    (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIccN d E u u Ψ) (p : ℕ) :
    (∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (u N) (u N),
      FlucGainUpTo' d N v (zt (E N) v) (mE (E N))
        (2 * (2 * minorDiffC (2 * p) * (2 * detFlucDelta Ψ θ N)
          + 2 * detFlucDelta Ψ θ N))
        (4 * detFlucDelta Ψ θ N) (2 * p) (2 * p)) ∧
    (∀ᶠ N : ℕ in atTop,
      ((d.W N : ℝ))⁻¹ ≤ (4 * detFlucDelta Ψ θ N) ^ 2) := by
  have hΩ := highProb_detFlucDelta_of_localLawN d hE hu0 hu1 ha hK
    hθ0 hθa hθ1 hη hΨhi hll
  obtain ⟨hMδ, hδC⟩ :=
    detFlucDelta_moment_small ha hθ0.le hθa hθ1 hΨhi p
  constructor
  · exact fixedMoment_gain_of_goodSetFlowN d hE hu1
      (detFlucDelta_pos Ψ θ) (detFlucDelta_le_quarter Ψ θ)
      (detFlucDelta_polyLo hθ0.le)
      (etaPolyHi_of_lowerN hE hu1 hK hη) hΩ p hMδ hδC
  · exact eventually_W_inv_le_detFlucDelta_sq d ha hθ0.le hΨlo hΨhi

section Compat

end Compat

end RBM.Gauss
