/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDENetClose
import RBM1D.EnergyN.Gauss.LDEFlow

/-!
# The large-deviation bounds along the flow with a floor, at an `N`-dependent energy

Four statements at an `N`-dependent energy `E : ℕ → ℝ`: the row, column and quadratic
large-deviation bounds as stochastic dominations over `TimeIcc s t N` with the floor `N^{-B}`
(`RBM.Gauss.stochDom_ldeRow_flow_floorN`, `RBM.Gauss.stochDom_ldeCol_flow_floorN`,
`RBM.Gauss.stochDom_ldeQuad_flow_floorN`), and the quadratic bound uniformly on `[s, t]`
(`RBM.Gauss.unifDomIcc_ldeQuadN`).

None of the four fixes an energy-dependent constant. The row and column statements feed
`unifDomIcc_ldeRowN`/`unifDomIcc_ldeColN` (`RBM1D/EnergyN/Gauss/LDEFlow.lean`) to the `E`-free
combinator `RBM.Gauss.stochDom_timeIcc_of_unifDom_relative`. `unifDomIcc_ldeQuadN` binds `N`
first (`intro τ hτ D hD; filter_upwards … with N …`) and then uses only
energy-free/per-fixed-`E` helpers, such as `RBM.Gauss.hwConst`, each called at `E N` after `N` is
bound. `stochDom_ldeQuad_flow_floorN` assembles `unifDomIcc_ldeQuadN` the same way as the
row/column pair, via `RBM.Gauss.abs_ldeQuad_flow_sub_le` (energy-free, called at `E N`).
-/

namespace RBM.Gauss

open MeasureTheory Filter

open scoped Matrix.Norms.L2Operator

section AssembleN

variable {d : Dims} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **The row large-deviation bound with the floor `N^{-B}`**, as a stochastic domination over
`TimeIcc s t N` and off-diagonal pairs, when `N^{-K} ≤ η_t` eventually. -/
theorem stochDom_ldeRow_flow_floorN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (t N)) {B : ℝ} (hB : 0 ≤ B) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × OffPair d.L d.W N)
      (fun N p ω =>
        ldeRowLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)))
          p.2.1.1 p.2.1.2)
      (fun N p ω =>
        ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)))
          p.2.1.1 p.2.1.2 + (N : ℝ) ^ (-B)) := by
  refine stochDom_timeIcc_of_unifDom_relative (card_OffPair_le d) hst one_pos
    (fun N => by have := hs0 N; have := (ht1 N).le; linarith)
    (A := 2 * (10 * K + 12 + B)) (by linarith)
    (ξ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeRowLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2)
    (ζ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2
        + (N : ℝ) ^ (-B)) ?_
    (δ := fun N => ((N : ℝ) ^ (-(10 * K + 12 + B))) ^ 2) ?_
    (highProb_norm_Xmat_le d) ?_
    ((unifDomIcc_ldeRowN d hE hs0 ht1).mono_control fun N u q ω => by
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      linarith)
  · intro N u q ω
    have h1 : (0 : ℝ) ≤ ldeRowRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg _ _) (by positivity)
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    refine le_of_eq ?_
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(10 * K + 12 + B))) 2, ← Real.rpow_mul hN0.le,
      one_div, ← Real.rpow_neg hN0.le]
    congr 1
    push_cast
    ring
  · filter_upwards [hη, card_Idx_le d, eventually_mod_le_floor hK hB,
      eventually_ge_atTop 1] with N hηN hcardN hmodN hN1 ω hω q u hu v hv huv
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
    have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (K + 1) := Real.one_le_rpow hN1' (by linarith)
    have hN11 : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hRη : ∀ w : ℝ, w ≤ t N → (etaT (E N) w)⁻¹ ≤ (N : ℝ) ^ (K + 1) := by
      intro w hw
      have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
      have hle : etaT (E N) (t N) ≤ etaT (E N) w := etaT_le_of_le (hE N) hw
      have hNKpos : (0 : ℝ) < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hN0 _
      have h1 : (etaT (E N) w)⁻¹ ≤ (etaT (E N) (t N))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hηt hle
      have h2 : (etaT (E N) (t N))⁻¹ ≤ ((N : ℝ) ^ (-K))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hNKpos hηN
      have h3 : ((N : ℝ) ^ (-K))⁻¹ = (N : ℝ) ^ K := by rw [Real.rpow_neg hN0.le, inv_inv]
      have h4 : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [h3] at h2
      linarith
    have hRn : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      rw [Real.rpow_one] at hcardN; linarith
    have hRx : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (K + 1) := le_trans hω hN11
    have key := abs_ldeRow_flow_sub_le d N (hE N) hu1 hv1 hR1 (hRη u hu.2) (hRη v hv.2) hRn ω
      hRx q.1.1 ⟨q.1.2, Ne.symm q.2⟩
    have hfl := hmodN u v huv
    obtain ⟨hlo1, hhi1⟩ := abs_le.1 (key.1.trans hfl)
    obtain ⟨hlo2, hhi2⟩ := abs_le.1 (key.2.trans hfl)
    have hζ0 : (0 : ℝ) ≤ ldeRowRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg _ _) (by positivity)
    exact ⟨by linarith, by linarith⟩

/-- **The column large-deviation bound with the floor `N^{-B}`**, as a stochastic domination over
`TimeIcc s t N` and off-diagonal pairs, when `N^{-K} ≤ η_t` eventually. -/
theorem stochDom_ldeCol_flow_floorN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (t N)) {B : ℝ} (hB : 0 ≤ B) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × OffPair d.L d.W N)
      (fun N p ω =>
        ldeColLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)))
          p.2.1.1 p.2.1.2)
      (fun N p ω =>
        ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)))
          p.2.1.1 p.2.1.2 + (N : ℝ) ^ (-B)) := by
  refine stochDom_timeIcc_of_unifDom_relative (card_OffPair_le d) hst one_pos
    (fun N => by have := hs0 N; have := (ht1 N).le; linarith)
    (A := 2 * (10 * K + 12 + B)) (by linarith)
    (ξ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeColLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2)
    (ζ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2
        + (N : ℝ) ^ (-B)) ?_
    (δ := fun N => ((N : ℝ) ^ (-(10 * K + 12 + B))) ^ 2) ?_
    (highProb_norm_Xmat_le d) ?_
    ((unifDomIcc_ldeColN d hE hs0 ht1).mono_control fun N u q ω => by
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      linarith)
  · intro N u q ω
    have h1 : (0 : ℝ) ≤ ldeColRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (Sblk_nonneg _ _)
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    refine le_of_eq ?_
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(10 * K + 12 + B))) 2, ← Real.rpow_mul hN0.le,
      one_div, ← Real.rpow_neg hN0.le]
    congr 1
    push_cast
    ring
  · filter_upwards [hη, card_Idx_le d, eventually_mod_le_floor hK hB,
      eventually_ge_atTop 1] with N hηN hcardN hmodN hN1 ω hω q u hu v hv huv
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
    have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (K + 1) := Real.one_le_rpow hN1' (by linarith)
    have hN11 : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hRη : ∀ w : ℝ, w ≤ t N → (etaT (E N) w)⁻¹ ≤ (N : ℝ) ^ (K + 1) := by
      intro w hw
      have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
      have hle : etaT (E N) (t N) ≤ etaT (E N) w := etaT_le_of_le (hE N) hw
      have hNKpos : (0 : ℝ) < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hN0 _
      have h1 : (etaT (E N) w)⁻¹ ≤ (etaT (E N) (t N))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hηt hle
      have h2 : (etaT (E N) (t N))⁻¹ ≤ ((N : ℝ) ^ (-K))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hNKpos hηN
      have h3 : ((N : ℝ) ^ (-K))⁻¹ = (N : ℝ) ^ K := by rw [Real.rpow_neg hN0.le, inv_inv]
      have h4 : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [h3] at h2
      linarith
    have hRn : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      rw [Real.rpow_one] at hcardN; linarith
    have hRx : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (K + 1) := le_trans hω hN11
    have key := abs_ldeCol_flow_sub_le d N (hE N) hu1 hv1 hR1 (hRη u hu.2) (hRη v hv.2) hRn ω
      hRx q.1.2 ⟨q.1.1, q.2⟩
    have hfl := hmodN u v huv
    obtain ⟨hlo1, hhi1⟩ := abs_le.1 (key.1.trans hfl)
    obtain ⟨hlo2, hhi2⟩ := abs_le.1 (key.2.trans hfl)
    have hζ0 : (0 : ℝ) ≤ ldeColRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt (E N) u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (Sblk_nonneg _ _)
    exact ⟨by linarith, by linarith⟩

end AssembleN

section QuadFixedN

variable {d : Dims} {s t : ℕ → ℝ} {E : ℕ → ℝ}

/-- **The quadratic large-deviation bound `ldeQuadLHS ≤ ldeQuadRHS`**, uniformly on `[s, t]`. No
energy-dependent constant is fixed here: `hwConst` carries no energy-dependent constant, and the
only `E`-uses (`zt_im_ne_zero_of_lt_one`, `modelChaos_normSq_chaos`, `modelChaos_Vq`, `vqM_eq`)
are per-fixed-`N` calls, made after `N` is bound by `filter_upwards`. -/
theorem unifDomIcc_ldeQuadN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) :
    UnifDomIcc (P d) s t
      (fun N u (i : BIdx d.L d.W N) ω =>
        ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u))
          (Sblk (d.L N) (d.W N)) u i)
      (fun N u (i : BIdx d.L d.W N) ω =>
        ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i) := by
  intro τ hτ D hD
  obtain ⟨q, hq⟩ := exists_nat_ge ((D + 1) / τ)
  have hDq : D + 1 ≤ τ * (q : ℝ) := by rw [div_le_iff₀ hτ] at hq; linarith
  have hexpand : τ * ((q : ℝ) + 1) = τ * (q : ℝ) + τ := by ring
  have hexp : 0 < τ * ((q : ℝ) + 1) - D := by rw [hexpand]; linarith
  filter_upwards [eventually_le_rpow (hwConst q) hexp, Filter.eventually_ge_atTop 1]
    with N hCN hN1 u hu i
  have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNτ : (0 : ℝ) < (N : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 τ
  have hz : (zt (E N) u).im ≠ 0 := zt_im_ne_zero_of_lt_one (hE N) hu1
  have hrhs : ∀ ω : Ω d,
      0 ≤ ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i :=
    fun ω => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (Sblk_nonneg _ _) (by positivity)) (Sblk_nonneg _ _)
  rcases eq_or_lt_of_le hu0 with hzero | hupos
  · -- `u = 0`: the chaos vanishes, so the failure event is empty
    subst hzero
    have hempty : {ω : Ω d | (N : ℝ) ^ τ *
        ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N 0 ω) (zt (E N) 0)) i
        < ldeQuadLHS (Hflow d N 0 ω) (green (Hflow d N 0 ω) (zt (E N) 0))
          (Sblk (d.L N) (d.W N)) 0 i} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have hz0 : ldeQuadLHS (Hflow d N 0 ω) (green (Hflow d N 0 ω) (zt (E N) 0))
          (Sblk (d.L N) (d.W N)) 0 i = 0 := by
        rw [← modelChaos_normSq_chaos hz i le_rfl ω, chaos_modelChaos_zero hz i ω]
        simp
      rw [hz0]
      have h1 := hrhs ω
      have hp : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg hN0.le τ
      positivity
    rw [hempty, measure_empty]
    exact zero_le
  · -- `0 < u`
    set lam : ℝ := (N : ℝ) ^ τ / u ^ 2 with hlamdef
    have hlam : 0 < lam := by rw [hlamdef]; positivity
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hupos, hu1]
    have hlamge : (N : ℝ) ^ τ ≤ lam := by
      rw [hlamdef, le_div_iff₀ (by positivity)]
      nlinarith [hNτ, hu2]
    have hset : {ω : Ω d | (N : ℝ) ^ τ *
        ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i
        < ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u))
          (Sblk (d.L N) (d.W N)) u i}
        = {ω | lam * vqM d N u (zt (E N) u) i ω
            < ‖(modelChaos d N u hz i).chaos ω‖ ^ 2} := by
      ext ω
      have hL := modelChaos_normSq_chaos hz i hu0 ω
      have hV : vqM d N u (zt (E N) u) i ω
          = u ^ 2 * ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i := by
        rw [← vqM_eq hz hu0 i ω]; exact modelChaos_Vq hz i hu0 ω
      have hune : u ≠ 0 := ne_of_gt hupos
      simp only [Set.mem_ofPred_eq, ← hL, hV, hlamdef]
      rw [show (N : ℝ) ^ τ / u ^ 2 * (u ^ 2 *
          ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i)
          = (N : ℝ) ^ τ
            * ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i from by
        field_simp]
    rw [hset]
    refine (meas_lt_normSq_chaos_le hz hu0 i hlam q).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (N : ℝ) ^ (τ * ((q : ℝ) + 1)) = ((N : ℝ) ^ τ) ^ (q + 1) := by
      rw [← Real.rpow_natCast ((N : ℝ) ^ τ) (q + 1), ← Real.rpow_mul hN0.le]
      push_cast
      ring_nf
    have hden : ((N : ℝ) ^ τ) ^ (q + 1) ≤ lam ^ (q + 1) :=
      pow_le_pow_left₀ hNτ.le hlamge (q + 1)
    have hd1 : (0 : ℝ) < ((N : ℝ) ^ τ) ^ (q + 1) := by positivity
    calc hwConst q / lam ^ (q + 1)
        ≤ hwConst q / ((N : ℝ) ^ τ) ^ (q + 1) :=
          div_le_div_of_nonneg_left (hwConst_pos q).le hd1 hden
      _ = hwConst q / (N : ℝ) ^ (τ * ((q : ℝ) + 1)) := by rw [hpow]
      _ ≤ (N : ℝ) ^ (τ * ((q : ℝ) + 1) - D) / (N : ℝ) ^ (τ * ((q : ℝ) + 1)) := by
          gcongr
      _ = (N : ℝ) ^ (-D) := by
          rw [← Real.rpow_sub hN0]
          congr 1
          ring

end QuadFixedN

section QuadFloorN

variable {d : Dims} {s t : ℕ → ℝ} {E : ℕ → ℝ}

/-- **The quadratic large-deviation bound with the floor `N^{-B}`**, as a stochastic domination
over `TimeIcc s t N`, when `N^{-K} ≤ η_t` eventually. -/
theorem stochDom_ldeQuad_flow_floorN (d : Dims) (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (t N)) {B : ℝ} (hB : 0 ≤ B) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × BIdx d.L d.W N)
      (fun N p ω =>
        ldeQuadLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)))
          (Sblk (d.L N) (d.W N)) (p.1 : ℝ) p.2)
      (fun N p ω =>
        ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt (E N) (p.1 : ℝ)))
          p.2 + (N : ℝ) ^ (-B)) := by
  refine stochDom_timeIcc_of_unifDom_relative (card_Idx_le d) hst one_pos
    (fun N => by have := hs0 N; have := (ht1 N).le; linarith)
    (A := 2 * (14 * K + 16 + B)) (by linarith)
    (ξ := fun N u (i : BIdx d.L d.W N) ω =>
      ldeQuadLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt (E N) u)) (Sblk (d.L N) (d.W N)) u i)
    (ζ := fun N u (i : BIdx d.L d.W N) ω =>
      ldeQuadRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt (E N) u)) i
        + (N : ℝ) ^ (-B)) ?_
    (δ := fun N => ((N : ℝ) ^ (-(14 * K + 16 + B))) ^ 2) ?_
    (highProb_norm_Xmat_le d) ?_
    ((unifDomIcc_ldeQuadN d hE hs0 ht1).mono_control fun N u i ω => by
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      linarith)
  · intro N u i ω
    have h1 : (0 : ℝ) ≤ ldeQuadRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt (E N) u)) i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (Sblk_nonneg _ _) (by positivity)) (Sblk_nonneg _ _)
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    refine le_of_eq ?_
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(14 * K + 16 + B))) 2, ← Real.rpow_mul hN0.le,
      one_div, ← Real.rpow_neg hN0.le]
    congr 1
    push_cast
    ring
  · filter_upwards [hη, card_Idx_le d, eventually_mod_le_floor_quad hK hB,
      eventually_ge_atTop 1] with N hηN hcardN hmodN hN1 ω hω i u hu v hv huv
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu0 : 0 ≤ u := le_trans (hs0 N) hu.1
    have hv0 : 0 ≤ v := le_trans (hs0 N) hv.1
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
    have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (K + 1) := Real.one_le_rpow hN1' (by linarith)
    have hN11 : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hRη : ∀ w : ℝ, w ≤ t N → (etaT (E N) w)⁻¹ ≤ (N : ℝ) ^ (K + 1) := by
      intro w hw
      have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE N) (ht1 N)
      have hle : etaT (E N) (t N) ≤ etaT (E N) w := etaT_le_of_le (hE N) hw
      have hNKpos : (0 : ℝ) < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hN0 _
      have h1 : (etaT (E N) w)⁻¹ ≤ (etaT (E N) (t N))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hηt hle
      have h2 : (etaT (E N) (t N))⁻¹ ≤ ((N : ℝ) ^ (-K))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hNKpos hηN
      have h3 : ((N : ℝ) ^ (-K))⁻¹ = (N : ℝ) ^ K := by rw [Real.rpow_neg hN0.le, inv_inv]
      have h4 : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [h3] at h2
      linarith
    have hRn : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      rw [Real.rpow_one] at hcardN; linarith
    have hRx : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (K + 1) := le_trans hω hN11
    have key := abs_ldeQuad_flow_sub_le d N (hE N) hu0 hv0 hu1 hv1 hR1 (hRη u hu.2)
      (hRη v hv.2) hRn ω hRx i
    have hfl := hmodN u v huv
    obtain ⟨hlo1, hhi1⟩ := abs_le.1 (key.1.trans hfl)
    obtain ⟨hlo2, hhi2⟩ := abs_le.1 (key.2.trans hfl)
    have hζ0 : (0 : ℝ) ≤ ldeQuadRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt (E N) u)) i :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (Sblk_nonneg _ _) (by positivity)) (Sblk_nonneg _ _)
    exact ⟨by linarith, by linarith⟩

end QuadFloorN

end RBM.Gauss

section Compat

open RBM RBM.Gauss MeasureTheory Filter

end Compat
