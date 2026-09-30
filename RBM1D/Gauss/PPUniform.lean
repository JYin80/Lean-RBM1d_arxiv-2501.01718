/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.PPInduction
import RBM1D.Gauss.Step3Charges
import RBM1D.Gauss.Lemma514Holder

/-!
# The time-uniform `(+,+)` bound: the control and a division lemma

Formalization support for Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, (5.92)/(5.112) at `n = 2`,
`σ = (+,+)` (Lemma 5.11 case), with the continuity argument of §5.6.

The time-uniform bound is `A_u² |(L−K)_{u,(+,+),(a,b)}| ≺ 1 + R² + R^{5/2}` uniformly in
`u ∈ [s,t]` and `(a,b)`, `R = ℓ_t/ℓ_s`.

## Main results

* `RBM.Gauss.thetaPP`, `RBM.Gauss.one_le_thetaPP` — the `(+,+)` control
  `Θpp N := 1 + R_N² + R_N^{5/2}`, and `1 ≤ Θpp`.
* `RBM.Gauss.stochDom_div_factor` — a positive deterministic factor can be divided out of a
  `StochDom`.
* `RBM.Gauss.idx_sigPP_two` — the loop index of `(σ_pp, ![a,b])` is `⟨[+,+],[a,b]⟩`.
-/

noncomputable section

namespace RBM.Gauss

open MeasureTheory Filter

/-! ### A positive deterministic factor can be divided out of a `StochDom` -/

/-- If `k·ξ ≺ c` with `k > 0` deterministic, then `ξ ≺ c·k⁻¹` (the `StochDom` companion of
`RBM.Gauss.unifDomIcc_mul_scale`). -/
theorem stochDom_div_factor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*}
    {ξ : ∀ N, U N → Ω → ℝ} {k c : ∀ N, U N → ℝ} (hk : ∀ N u, 0 < k N u)
    (h : StochDom P (fun N u ω => k N u * ξ N u ω) (fun N u _ => c N u)) :
    StochDom P ξ (fun N u _ => c N u * (k N u)⁻¹) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono fun ω hω => ?_).trans hN
  obtain ⟨u, hu⟩ := hω
  refine ⟨u, ?_⟩
  have hk0 := hk N u
  have hu' : (N : ℝ) ^ τ * (c N u * (k N u)⁻¹) < ξ N u ω := hu
  change (N : ℝ) ^ τ * c N u < k N u * ξ N u ω
  have heq : (N : ℝ) ^ τ * c N u = k N u * ((N : ℝ) ^ τ * (c N u * (k N u)⁻¹)) := by
    field_simp
  rw [heq]
  exact mul_lt_mul_of_pos_left hu' hk0

variable (d : Dims)

/-! ### (T1) The time-uniform `(+,+)` bound -/

/-- The `(+,+)` control `1 + R² + R^{5/2}`, `R = ℓ_t/ℓ_s` (`Grid.RPP`). -/
def thetaPP (s t : ℕ → ℝ) (N : ℕ) : ℝ :=
  1 + Grid.RPP d s t N ^ 2 + Grid.RPP d s t N ^ (5 / 2 : ℝ)

theorem one_le_thetaPP (s t : ℕ → ℝ) (N : ℕ) : 1 ≤ thetaPP d s t N := by
  unfold thetaPP
  have h0 := Grid.RPP_nonneg d s t N
  have h1 : 0 ≤ Grid.RPP d s t N ^ (5 / 2 : ℝ) := Real.rpow_nonneg h0 _
  nlinarith

/-- The loop index of `(σ_pp, ![a,b])` is `⟨[+,+],[a,b]⟩`. -/
theorem idx_sigPP_two {L : ℕ} (a b : ZMod L) :
    (LoopData.idx (Grid.sigPP, ![a, b]) : LoopIdx (ZMod L)) = ⟨[true, true], [a, b]⟩ := by
  simp [LoopData.idx, Grid.sigPP, List.ofFn_succ]

/-! ### Checks: the type of each gained `X` -/

end RBM.Gauss

end

-- the new plain-pair successors
