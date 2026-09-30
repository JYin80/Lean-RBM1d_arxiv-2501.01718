/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GoodSetFlow
import RBM1D.EnergyN.Flow.Hypotheses

/-!
# The uniform local law and the good set along the flow, at an `N`-dependent energy

At an `N`-dependent energy `E : ℕ → ℝ`: the predicate `RBM.Gauss.LocalLawUnifIccN` (the uniform
local law on `[s, t]` with the control `Ψ`), its time-net form
`RBM.Gauss.stochDom_timeIcc_localLawN`, the good set `goodSetFlow` with high probability
(`RBM.Gauss.highProb_goodSetFlow_of_localLawN`), and the uniform local law from (2.75)
(`RBM.Gauss.localLawUnifIcc_of_localLawFlowN`).

None of the three theorems fixes an energy-dependent constant: every `(mE E).im`/`etaT E`-use is
pointwise, computed after `N` is bound (inside `filter_upwards ... with N` or
`intro D _; filter_upwards with N`), so nothing is fixed before the `∀ᶠ N`. The energy-free
helper `abs_norm_green_flow_entry_sub_le` (this file) and the generic (`E`-free) net engine
`stochDom_timeIcc_of_unifDom`/`highProb_norm_Xmat_le` (`Gauss/Step1Hyp.lean`) are used at `E N`.
-/

namespace RBM.Gauss

open MeasureTheory Filter Matrix

open scoped Matrix.Norms.L2Operator

/-- **The uniform local law on `[s, t]` with the control `Ψ`**: `|G_ij - δ_ij m| ≤ Ψ`, uniformly
in `u ∈ [s, t]` and `i, j` (`UnifDomIcc`). No energy-dependent constant is fixed here. -/
abbrev LocalLawUnifIccN (d : Dims) (E : ℕ → ℝ) (s t Ψ : ℕ → ℝ) : Prop :=
  UnifDomIcc (P d) s t
    (fun N u (ij : d.Idx N × d.Idx N) ω =>
      ‖green (Hflow d N u ω) (zt (E N) u) ij.1 ij.2 - (if ij.1 = ij.2 then mE (E N) else 0)‖)
    (fun N _ _ _ => Ψ N)

variable {d : Dims} {E : ℕ → ℝ} {s t δ Ψ : ℕ → ℝ} {K B : ℝ}

/-- **The uniform local law as a stochastic domination over `TimeIcc s t N`**, given the net bound
`hKbig` and the lower bound `N^{-B} ≤ Ψ`. -/
theorem stochDom_timeIcc_localLawN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hKbig : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ K)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N)
    (hll : LocalLawUnifIccN d E s t Ψ) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × (d.Idx N × d.Idx N))
      (fun N p ω => ‖green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)) p.2.1 p.2.2
        - (if p.2.1 = p.2.2 then mE (E N) else 0)‖)
      (fun N _ _ => Ψ N) := by
  refine stochDom_timeIcc_of_unifDom (card_Idx_prod_le d) hst one_pos ?_ hK hB
    (by norm_num : (0:ℝ) < (1:ℝ)/2) (fun N _ _ _ => hΨ0 N)
    (δ := fun N => 1 / (N : ℝ) ^ ((K + B + 1) / ((1 : ℝ) / 2)))
    (Eventually.of_forall fun _ => le_rfl) (highProb_norm_Xmat_le d) ?_ ?_ ?_ hll
  · intro N
    have h1 := hs0 N
    have h2 := (ht1 N).le
    linarith
  · filter_upwards [hKbig] with N hKN ω hω ij u hu v hv
    have hX : ‖Xmat d N ω‖ ≤ (N : ℝ) := hω
    have hmod := abs_norm_green_flow_entry_sub_le d N (hE N) (hs0 N) (ht1 N) ω ij.1 ij.2 hu hv
    have hsq : Real.sqrt |u - v| = |u - v| ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have hsq0 : (0 : ℝ) ≤ |u - v| ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg _) _
    have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
    have hη0 : (0 : ℝ) < (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ := by positivity
    have hstep : (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * (‖Xmat d N ω‖ + 1)
        ≤ (N : ℝ) ^ K := by
      refine le_trans ?_ hKN
      have : ‖Xmat d N ω‖ + 1 ≤ (N : ℝ) + 1 := by linarith
      nlinarith
    rw [hsq] at hmod
    calc |‖green (Hflow d N u ω) (zt (E N) u) ij.1 ij.2 - (if ij.1 = ij.2 then mE (E N) else 0)‖
            - ‖green (Hflow d N v ω) (zt (E N) v) ij.1 ij.2
              - (if ij.1 = ij.2 then mE (E N) else 0)‖|
        ≤ ((etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * (‖Xmat d N ω‖ + 1))
            * |u - v| ^ ((1 : ℝ) / 2) := hmod
      _ ≤ (N : ℝ) ^ K * |u - v| ^ ((1 : ℝ) / 2) := by gcongr
  · filter_upwards [hΨlow] with N hN _ _ _ _ _
    exact hN
  · intro ε hε
    filter_upwards [eventually_le_rpow 1 hε] with N hN _ _ _ _ _ _ _ _
    nlinarith [hΨ0 N]

/-- **The good set `goodSetFlow` holds with high probability** when `N^τ Ψ ≤ δ` eventually, from
the uniform local law. -/
theorem highProb_goodSetFlow_of_localLawN (d : Dims) {τ : ℝ} (hτ : 0 < τ) (hE : ∀ N, |E N| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) (hst : ∀ N, s N ≤ t N) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hKbig : ∀ᶠ N : ℕ in atTop,
      (etaT (E N) (t N))⁻¹ * (etaT (E N) (t N))⁻¹ * ((N : ℝ) + 1) ≤ (N : ℝ) ^ K)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N)
    (hll : LocalLawUnifIccN d E s t Ψ)
    (hmargin : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ τ * Ψ N ≤ δ N) :
    HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N) := by
  refine ((stochDom_timeIcc_localLawN d hE hs0 ht1 hst hK hB hKbig hΨ0 hΨlow hll).highProb
    hτ).mono ?_
  filter_upwards [hmargin] with N hN ω hω u hu x y
  exact (hω (⟨u, hu⟩, (x, y))).trans hN

/-- **The uniform local law `LocalLawUnifIccN` from (2.75)**, when `(W ℓ_u η_u)^{-1/2} ≤ Ψ`
eventually on `[s, t]`. -/
theorem localLawUnifIcc_of_localLawFlowN (hLL : RBM.LocalLawFlowN (sample d) E s t)
    (hmaj : ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      ((band d).scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 2) ≤ Ψ N) :
    LocalLawUnifIccN d E s t Ψ := by
  intro τ hτ D hD
  filter_upwards [hLL τ hτ D hD, hmaj] with N hN hM u hu ij
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  refine ⟨(⟨u, hu⟩, ij), ?_⟩
  have hτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have h1 : (N : ℝ) ^ τ * ((band d).scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ τ * Ψ N :=
    mul_le_mul_of_nonneg_left (hM u hu) hτ0
  have h2 : (N : ℝ) ^ τ * Ψ N
      < ‖green (Hflow d N u ω) (zt (E N) u) ij.1 ij.2 - (if ij.1 = ij.2 then mE (E N) else 0)‖ :=
    hω
  show (N : ℝ) ^ τ * ((band d).scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 2)
    < (sample d).llErr (E N) N u ω ij
  rw [(sample d).llErr_eq N u ω ij]
  show (N : ℝ) ^ τ * ((band d).scale (E N) N u)⁻¹ ^ ((1 : ℝ) / 2)
    < ‖green (Hflow d N u ω) (zt (E N) u) ij.1 ij.2 - (if ij.1 = ij.2 then mE (E N) else 0)‖
  linarith

end RBM.Gauss
