/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetFlucAvgComplete
import RBM1D.EnergyN.Gauss.DetFlucThreshold

/-!
# The fixed-time fluctuation-average statement, proved, at an `N`-dependent energy

Three statements at an `N`-dependent energy `E : ℕ → ℝ`: the fluctuation averages of uniform
weights are dominated by the iterated budget
(`RBM.Gauss.unifDomIcc_flucAvg_iter_budget_eventuallyN`), the budget bound at a fixed time
(`RBM.Gauss.fixedMoment_flucAvg_budget_familyN`), and the proof of `fixedTimeFAStatementN`
(`RBM.Gauss.fixedTimeFAStatement_provedN`). No energy-dependent constant is fixed in them.

The only `E`-uses of `unifDomIcc_flucAvg_iter_budget_eventuallyN` (`flucBound_env`,
`integral_norm_flucAvg_pow_le_iter_budget`, `Gauss/FlucAvg.lean`/`Gauss/FlucIter.lean`) take
`{E u : ℝ}` explicitly and are applied only after `N` is bound by the surrounding
`filter_upwards`, i.e. they are energy-free deterministic facts used at `E N`.
`fixedMoment_flucAvg_budget_familyN` uses `fixedMoment_gain_of_localLawN`
(`RBM1D/EnergyN/Gauss/DetFlucThreshold.lean`) and `unifDomIcc_flucAvg_iter_budget_eventuallyN`.
`fixedTimeFAStatement_provedN` proves the predicate `fixedTimeFAStatementN`
(`RBM1D/EnergyN/Gauss/DetFlucAvg.lean`), using `fixedMoment_flucAvg_budget_familyN` and the
generic (`E`-free) combinator `fixedMoment_budgetFamily_absorb`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

/-- **The fluctuation averages `flucAvg` of uniform weights are at most `ep · Bm`** uniformly on
`[s, t]`, from the moment gains `hg` for every `p`. No energy-dependent constant is fixed here:
every `E`-use (`flucBound_env`, `integral_norm_flucAvg_pow_le_iter_budget`) is energy-free,
applied after `N` is bound. -/
theorem unifDomIcc_flucAvg_iter_budget_eventuallyN {E : ℕ → ℝ} {s t : ℕ → ℝ}
    {V : ℕ → Type*} (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    {Tw : ∀ N, V N → d.Idx N → ℝ} {cw : ℕ → ℝ}
    {Aw : ∀ N, V N → Finset (d.Idx N)}
    {Bp : ℕ → ℕ → ℝ} {Bm Kp ep : ℕ → ℝ}
    (hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ u ∈ Set.Icc (s N) (t N),
      FlucGainUpTo' d N u (zt (E N) u) (mE (E N)) (Bp p N) (ep N) (2 * p) (2 * p))
    (hKp : ∀ p, 0 ≤ Kp p) (hBm : ∀ N, 0 ≤ Bm N)
    (hBK : ∀ p N, Bp p N ≤ Kp p * Bm N)
    (hpos : ∀ N, 0 < ep N * Bm N) (hρ1 : ∀ N, ep N ≤ 1)
    (hcρ : ∀ᶠ N : ℕ in atTop, cw N ≤ ep N ^ 2)
    (hw : ∀ N (a : V N), UniformWeight (Tw N a) (cw N) (Aw N a))
    (hcardA : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ a : V N, 2 * p ≤ (Aw N a).card) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖flucAvg d N u (zt (E N) u) (mE (E N)) (Tw N a) ω‖)
      (fun N _ _ _ => ep N * Bm N) := by
  refine unifDomIcc_of_moment (fun N => hpos N) (fun p N u hu a => ?_) ?_
  · exact integrable_norm_flucAvg_pow
      (flucBound_env (hE N) (lt_of_le_of_lt hu.2 (ht1 N)) d N u).flucDiag_le p
  · intro ε hε p
    have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) :=
      pow_nonneg (mul_nonneg (by positivity) (hKp p)) _
    have hc1 : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p) := by positivity
    have hcoef : (0 : ℝ) ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
        * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) := mul_nonneg hc1 hK0
    refine ⟨((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
      * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) + 1, by linarith, ?_⟩
    filter_upwards [hcardA p, hg p, hcρ, eventually_ge_atTop 1]
      with N h2 hgN hcρN hN1 u hu a
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hrw : (fun ω => |‖flucAvg d N u (zt (E N) u) (mE (E N)) (Tw N a) ω‖| ^ (2 * p))
        = fun ω => ‖flucAvg d N u (zt (E N) u) (mE (E N)) (Tw N a) ω‖ ^ (2 * p) := by
      funext ω; rw [abs_norm]
    rw [hrw]
    have hmain := integral_norm_flucAvg_pow_le_iter_budget (hE N) hu1 (hgN u hu) le_rfl le_rfl
      (hρ1 N) hcρN (hw N a) (h2 a)
    have hep0 : (0 : ℝ) ≤ ep N := (hgN u hu).rho_nonneg
    have hBp0 : (0 : ℝ) ≤ Bp p N := (hgN u hu).B_nonneg
    have hstep1 : ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
        ≤ ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      calc (2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N
          ≤ (2 : ℝ) ^ (2 * p - 1) * ep N * (Kp p * Bm N) :=
            mul_le_mul_of_nonneg_left (hBK p N) (by positivity)
        _ = ((2 : ℝ) ^ (2 * p - 1) * Kp p) * (ep N * Bm N) := by ring
    have hmain2 : ∫ ω, ‖flucAvg d N u (zt (E N) u) (mE (E N)) (Tw N a) ω‖ ^ (2 * p) ∂(P d)
        ≤ (((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
            * ((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p)) * (ep N * Bm N) ^ (2 * p) := by
      refine le_trans hmain ?_
      calc ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * ((2 : ℝ) ^ (2 * p - 1) * ep N * Bp p N) ^ (2 * p)
          ≤ ((2 * p : ℝ) + 1) * (2 * p : ℝ) ^ (2 * p)
              * (((2 : ℝ) ^ (2 * p - 1) * Kp p) ^ (2 * p) * (ep N * Bm N) ^ (2 * p)) :=
            mul_le_mul_of_nonneg_left hstep1 hc1
        _ = _ := by ring
    have hNe : (1 : ℝ) ≤ (N : ℝ) ^ (ε * p) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by positivity)
    have hpow : (0 : ℝ) ≤ (ep N * Bm N) ^ (2 * p) :=
      pow_nonneg (mul_nonneg hep0 (hBm N)) _
    refine le_trans hmain2 ?_
    nlinarith [mul_nonneg hcoef hpow, hpow, hNe, hcoef]

/-- **The fluctuation averages of uniform weights are at most `4 detFlucDelta Ψ θ ^ 2`** at the
time `u`, from the uniform local law. It uses `fixedMoment_gain_of_localLawN` and
`unifDomIcc_flucAvg_iter_budget_eventuallyN`. -/
theorem fixedMoment_flucAvg_budget_familyN (d : Dims) {E : ℕ → ℝ} {u Ψ : ℕ → ℝ}
    {a K θ : ℝ} (hE : ∀ N, |E N| < 2) (hu0 : ∀ N, 0 ≤ u N)
    (hu1 : ∀ N, u N < 1) (ha : 0 < a) (hK : 0 ≤ K)
    (hθ0 : 0 < θ) (hθa : θ ≤ a / 4) (hθ1 : θ ≤ 1 / 4)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT (E N) (u N))
    (hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N)
    (hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a))
    (hll : LocalLawUnifIccN d E u u Ψ)
    {V : ℕ → Type*} {Tw : ∀ N, V N → d.Idx N → ℝ}
    {cw : ℕ → ℝ} {Aw : ∀ N, V N → Finset (d.Idx N)}
    (hw : ∀ N (b : V N), UniformWeight (Tw N b) (cw N) (Aw N b))
    (hcW : ∀ N, cw N ≤ ((d.W N : ℝ))⁻¹)
    (hcard : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ b : V N, 2 * p ≤ (Aw N b).card) :
    UnifDomIcc (P d) u u
      (fun N v (b : V N) ω => ‖flucAvg d N v (zt (E N) v) (mE (E N)) (Tw N b) ω‖)
      (fun N _ _ _ => 4 * detFlucDelta Ψ θ N ^ 2) := by
  let δ := detFlucDelta Ψ θ
  have hg : ∀ p : ℕ, ∀ᶠ N : ℕ in atTop, ∀ v ∈ Set.Icc (u N) (u N),
      FlucGainUpTo' d N v (zt (E N) v) (mE (E N))
        ((8 * minorDiffC (2 * p) + 4) * δ N) (4 * δ N) (2 * p) (2 * p) := by
    intro p
    have h := (fixedMoment_gain_of_localLawN d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll p).1
    filter_upwards [h] with N hN v hv
    convert hN v hv using 1 <;> ring
  have hcρ : ∀ᶠ N : ℕ in atTop, cw N ≤ (4 * δ N) ^ 2 := by
    have h := (fixedMoment_gain_of_localLawN d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll 0).2
    filter_upwards [h] with N hN
    exact (hcW N).trans hN
  have hδpos : ∀ N, 0 < δ N := detFlucDelta_pos Ψ θ
  have hδ4 : ∀ N, δ N ≤ 1 / 4 := detFlucDelta_le_quarter Ψ θ
  have hKp : ∀ p, (0 : ℝ) ≤ 8 * minorDiffC (2 * p) + 4 := by
    intro p
    have hC := minorDiffC_nonneg (2 * p)
    linarith
  have h := unifDomIcc_flucAvg_iter_budget_eventuallyN d hE hu1 hg hKp
    (fun N => (hδpos N).le) (fun p N => le_refl _)
    (fun N => mul_pos (by linarith [hδpos N]) (hδpos N))
    (fun N => by linarith [hδ4 N]) hcρ hw hcard
  convert h using 1
  funext N v b ω
  ring

/-- **The fixed-time fluctuation-average statement `fixedTimeFAStatementN` holds**
(`RBM1D/EnergyN/Gauss/DetFlucAvg.lean`). -/
theorem fixedTimeFAStatement_provedN (d : Dims) (E : ℕ → ℝ) (u Ψ : ℕ → ℝ) (a K : ℝ) :
    fixedTimeFAStatementN d E u Ψ a K := by
  intro ha hK hE hu hη hΨ hll
  have hu0 : ∀ N, 0 ≤ u N := fun N => (hu N).1
  have hu1 : ∀ N, u N < 1 := fun N => (hu N).2
  have hΨlo : ∀ᶠ N : ℕ in atTop, ((d.W N : ℝ)) ^ (-(1 : ℝ) / 2) ≤ Ψ N :=
    hΨ.mono (fun N hN => hN.1)
  have hΨhi : ∀ᶠ N : ℕ in atTop, Ψ N ≤ (N : ℝ) ^ (-a) :=
    hΨ.mono (fun N hN => hN.2)
  constructor
  · apply fixedMoment_budgetFamily_absorb d ha hΨlo
    intro θ hθ0 hθa hθ1
    refine fixedMoment_flucAvg_budget_familyN d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll (fun N i => uniformWeight_Sblk i) ?_ ?_
    · intro N
      have hw : (0 : ℝ) < d.W N := Nat.cast_pos.2 (d.W_pos N)
      have h3w : (d.W N : ℝ) ≤ (3 * d.W N : ℝ) := by
        push_cast
        linarith
      exact inv_anti₀ hw h3w
    · intro p
      filter_upwards [eventually_le_W d (2 * p)] with N hN i
      rw [card_Sblk_support]
      omega
  · apply fixedMoment_budgetFamily_absorb d ha hΨlo
    intro θ hθ0 hθa hθ1
    refine fixedMoment_flucAvg_budget_familyN d hE hu0 hu1 ha hK hθ0 hθa hθ1
      hη hΨlo hΨhi hll (fun N b => uniformWeight_blockAvg b) ?_ ?_
    · intro N
      exact le_refl _
    · intro p
      filter_upwards [eventually_le_W d (2 * p)] with N hN b
      rw [card_blockAvg_support]
      exact hN

section Compat

end Compat

end RBM.Gauss
