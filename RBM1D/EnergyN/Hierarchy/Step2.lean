/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2
import RBM1D.EnergyN.Hierarchy.Step1
import RBM1D.EnergyN.Hierarchy.SumZeroDyn
import RBM1D.EnergyN.Unif.Hierarchy.Step3

/-!
# Step 2 of the proof of Theorem 2.21 at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.3.

Three statements of Step 2 at an `N`-dependent energy `E : ℕ → ℝ`: the bound
`|K_{u,(+,-),a}| ≺ (W ℓ_u η_u)^{-1}` from a kernel bound (`RBM.Step2.kval_stochDomN`), the local
law (2.75) from (2.74), (2.76) and Lemma 4.1 (`RBM.Step2.localLaw_of_scale_factsN`), and
Lemma 5.6, (5.30) (`RBM.Step2.eq530N`).

## The external `κ`

`RBM.Step2.localLaw_of_scale_factsN` uses a kernel constant `C` with
`‖K‖ ≤ C (W ℓ η)^{-1}`. It takes an explicit `κ` (`hκ0`, `hκ1`, `hEκ`), obtains the single
uniform `C` once, before `∀ N`, from `RBM.Step3.exists_norm_Kval_le_unif`
(`RBM1D/EnergyN/Unif/Hierarchy/Step3.lean`), and instantiates it at every `E N` (by
`hEκ N : |E N| ≤ 2 - κ`).

`RBM.Step2.kval_stochDomN` and `RBM.Step2.eq530N` fix no energy-dependent constant:
`kval_stochDomN` receives its constant `C` as a hypothesis, and `eq530N` only uses
`RBM.SumZeroDyn.flow_crudeN` and `RBM.Cond272N` (`Flow/EnergyUniform.lean`), neither of which
fixes an `E`-dependent constant before `∀ᶠ N`.
-/

namespace RBM

namespace Step2

open MeasureTheory Filter Real

section LocalLaw

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **`|K_{u,(+,-),a}| ≺ (W ℓ_u η_u)^{-1}`** from the deterministic kernel bound `hC`. No
energy-dependent constant is fixed here (the constant `C` is a hypothesis). -/
theorem kval_stochDomN {C : ℝ}
    (hC : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 2),
      ‖B.Kval (E N) N u v.idx‖ ≤ C * (B.scale (E N) N u)⁻¹ ^ (2 - 1))
    (hA : ∀ N (u : TimeIcc s t N), 0 < B.scale (E N) N u) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) (_ : Ω) =>
        ‖B.Kval (E N) N p.1 (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹) := by
  refine Step1.stochDom_of_le_const_mul (fun _ _ _ => norm_nonneg _)
    (fun N p _ => (inv_pos.2 (hA N p.1)).le) C fun N p ω => ?_
  have h := hC N p.1 (sigPM, ![p.2.1, p.2.2])
  rw [idx_sigPM] at h
  simpa using h

/-- **The local law (2.75)**, `‖G_u - m‖_max ≺ (W ℓ_u η_u)^{-1/2}` on `[s, t]`, from (2.74),
(2.76) and Lemma 4.1 along the flow. The kernel constant is the single uniform `C` of
`Step3.exists_norm_Kval_le_unif`, obtained once before `∀ N` and instantiated at every
`E N`. -/
theorem localLaw_of_scale_factsN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hfacts : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      (etaT (E N) (s N) / etaT (E N) u) ^ 4 ≤ B.scale (E N) N u ∧
        (N : ℝ) ^ c ≤ B.scale (E N) N u)
    (h276 : ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2 *
        B.decayProf N p.1 D p.2.1 p.2.2))
    (h274 : StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr (E N) N p.1 ω p.2)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 4)))
    (h41 : Step1.Lemma41FlowN X E s t) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => X.llErr (E N) N p.1 ω p.2)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ ((1 : ℝ) / 2)) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hu0 : ∀ N (u : TimeIcc s t N), (0 : ℝ) ≤ (u : ℝ) := fun N u => (hs0 N).trans u.2.1
  have hu1 : ∀ N (u : TimeIcc s t N), (u : ℝ) < 1 := fun N u => u.2.2.trans_lt (ht1 N)
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale (E N) N u := fun N u =>
    B.scale_pos' (hE N) N (hu0 N u) (hu1 N u)
  have hAi : ∀ N (u : TimeIcc s t N), 0 ≤ (B.scale (E N) N u)⁻¹ := fun N u =>
    (inv_pos.2 (hA N u)).le
  -- (5.73): `|L_{u,(+,-)}| ≺ (W ℓ_u η_u)^{-1}`, kernel constant `C` uniform
  obtain ⟨C, -, hCall⟩ := Step3.exists_norm_Kval_le_unif (B := B) hκ0 hκ1 hs0 ht1 (n := 2)
    (by norm_num)
  have hC : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 2),
      ‖B.Kval (E N) N u v.idx‖ ≤ C * (B.scale (E N) N u)⁻¹ ^ (2 - 1) :=
    fun N u v => hCall (E N) (hEκ N) N u v
  have hLK : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale (E N) N p.1)⁻¹) := by
    refine Step3.stochDom_mono (fun N p _ => hAi N p.1) 2 ?_ (h276 1 one_pos)
    filter_upwards [hfacts] with N hN p ω
    obtain ⟨hR4, -⟩ := hN p.1
    have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
    have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
    have hdec : B.decayProf N p.1 1 p.2.1 p.2.2 ≤ 2 := by
      unfold Band.decayProf
      have h1 : Real.exp (-(((zdist (B.L N) (p.2.1 - p.2.2) : ℝ) / B.ell N p.1) ^ ((1 : ℝ) / 2)))
          ≤ 1 := Real.exp_le_one_iff.2 (by
            have hℓ : 0 < B.ell N p.1 := Step3.ellHat_pos_of_lt_one (B.one_le_L N) (hu1 N p.1)
            have := Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg (zdist (B.L N)
              (p.2.1 - p.2.2))) hℓ.le) ((1 : ℝ) / 2)
            linarith)
      have h2 : (B.W N : ℝ) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
      linarith
    have hApos := hA N p.1
    have hdec0 : 0 ≤ B.decayProf N p.1 1 p.2.1 p.2.2 := by unfold Band.decayProf; positivity
    have hR0 : 0 ≤ (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 := by
      have := div_pos (etaT_pos' (hE N) ((hst N).trans_lt (ht1 N))) (etaT_pos' (hE N) (hu1 N p.1))
      positivity
    calc (etaT (E N) (s N) / etaT (E N) p.1) ^ 4 * (B.scale (E N) N p.1)⁻¹ ^ 2 *
          B.decayProf N p.1 1 p.2.1 p.2.2
        ≤ B.scale (E N) N p.1 * (B.scale (E N) N p.1)⁻¹ ^ 2 * 2 := by gcongr
      _ = 2 * (B.scale (E N) N p.1)⁻¹ := by field_simp
  have hK := kval_stochDomN (B := B) (Ω := Ω) (E := E) (s := s) (t := t) hC hA
  have hL : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        ‖X.Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2)‖)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹) := by
    refine Step3.stochDom_mono (fun N p _ => hAi N p.1) 2
      (Eventually.of_forall fun N p ω => ?_) (StochDom.of_le_left (fun N p ω => ?_) (hLK.add hK))
    · simp only [Pi.add_apply]; linarith
    · simp only [Pi.add_apply, Sample.lkErr]
      have := norm_sub_norm_le (X.Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
        (B.Kval (E N) N p.1 (pmLoop p.2.1 p.2.2))
      linarith
  -- Lemma 4.1
  have hLind : StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        (Step1.goodEv X (E N) N p.1).indicator
          (fun ω => ‖X.Lval (E N) N p.1 ω (pmLoop p.2.1 p.2.2)‖) ω)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹) := by
    refine StochDom.of_le_left (fun N p ω => ?_) hL
    by_cases hω : ω ∈ Step1.goodEv X (E N) N p.1
    · rw [Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω]; exact norm_nonneg _
  have h41' := h41 (fun N u => (B.scale (E N) N u)⁻¹) hAi hLind
  have hsq : StochDom B.P
      (fun N (u : TimeIcc s t N) ω => (Step1.goodEv X (E N) N u).indicator
        (fun ω => Step1.llMax X (E N) N u ω ^ 2) ω)
      (fun N u _ => (B.scale (E N) N u)⁻¹) := by
    refine Step3.stochDom_mono (fun N u _ => hAi N u) 2 (Eventually.of_forall fun N u ω => ?_) h41'
    have := Step1.inv_W_le_inv_scale (B := B) (hE N) N (hu0 N u) (hu1 N u)
    linarith
  -- the good event of Lemma 4.1 holds for all `u` w.h.p., by (2.74)
  have hΩ : HighProb B.P (fun N => {ω | ∀ u : TimeIcc s t N, ω ∈ Step1.goodEv X (E N) N u}) := by
    refine (h274.highProb (by positivity : (0 : ℝ) < c / 24)).mono ?_
    filter_upwards [hfacts, eventually_ge_atTop 1] with N hN hN1 ω hω u
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    obtain ⟨-, hNc⟩ := hN u
    have hApos := hA N u
    have hA1 : 1 ≤ B.scale (E N) N u := (Real.one_le_rpow hN1' hc0.le).trans hNc
    refine Step1.llMax_le X fun ij => (hω (u, ij)).trans ?_
    -- `N^{c/24} A^{-1/4} ≤ A^{-1/6}`
    have h1 : (N : ℝ) ^ (c / 24) ≤ B.scale (E N) N u ^ ((1 : ℝ) / 12) := by
      have e : (N : ℝ) ^ (c / 24) = ((N : ℝ) ^ c) ^ ((1 : ℝ) / 24) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
      rw [e]
      calc ((N : ℝ) ^ c) ^ ((1 : ℝ) / 24) ≤ B.scale (E N) N u ^ ((1 : ℝ) / 24) :=
            Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) hNc (by norm_num)
        _ ≤ B.scale (E N) N u ^ ((1 : ℝ) / 12) :=
            Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
    rw [Real.inv_rpow hApos.le, Real.inv_rpow hApos.le]
    have e2 : B.scale (E N) N u ^ ((1 : ℝ) / 4) =
        B.scale (E N) N u ^ ((1 : ℝ) / 12) * B.scale (E N) N u ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_add hApos]; norm_num
    rw [e2, mul_inv, ← mul_assoc]
    have hp : 0 < B.scale (E N) N u ^ ((1 : ℝ) / 12) := Real.rpow_pos_of_pos hApos _
    have hq : 0 < (B.scale (E N) N u ^ ((1 : ℝ) / 6))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos hApos _)
    have : (N : ℝ) ^ (c / 24) * (B.scale (E N) N u ^ ((1 : ℝ) / 12))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hp]; exact h1
    calc (N : ℝ) ^ (c / 24) * (B.scale (E N) N u ^ ((1 : ℝ) / 12))⁻¹ *
          (B.scale (E N) N u ^ ((1 : ℝ) / 6))⁻¹ ≤ 1 * (B.scale (E N) N u ^ ((1 : ℝ) / 6))⁻¹ := by
          gcongr
      _ = _ := one_mul _
  have hmax := Step1.stochDom_of_indicator
    (Ωs := fun N (u : TimeIcc s t N) => Step1.goodEv X (E N) N u)
    (ξ := fun N (u : TimeIcc s t N) ω => Step1.llMax X (E N) N u ω ^ 2)
    (ζ := fun N u _ => (B.scale (E N) N u)⁻¹) hΩ hsq
  have hhalf := stochDom_rpow_half_of_sq
    (ξ := fun N (u : TimeIcc s t N) ω => Step1.llMax X (E N) N u ω)
    (fun N (u : TimeIcc s t N) _ => hAi N u) hmax
  have hfin := hhalf.precomp_param (V := fun N => TimeIcc s t N × (B.Idx N × B.Idx N))
    fun N p => p.1
  refine StochDom.of_le_left
    (ξ' := fun N (p : TimeIcc s t N × (B.Idx N × B.Idx N)) ω => Step1.llMax X (E N) N p.1 ω)
    (fun N p ω => Step1.llErr_le_llMax X N p.1 ω p.2) ?_
  exact hfin

end LocalLaw

section Eq530

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **Lemma 5.6, (5.30)**: eventually, for all `u ∈ [s, t]` and `|x - y| ≥ δ ℓ*_u`, the entries of
`Θ_u` and of `(1 - s S) Θ_u` are at most `W^{-D}`. No energy-dependent constant is fixed here
(it uses `SumZeroDyn.flow_crudeN` and `Cond272N` only; the rest of the proof does not mention
`E`). -/
theorem eq530N (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) {δ D : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : TimeIcc s t N) (x y : ZMod (B.L N)),
      δ * ellStar (B.W N) (B.ell N u) ≤ zdist (B.L N) (x - y) →
        ‖Theta (B.L N) ((u : ℝ) : ℂ) x y‖ ≤ (B.W N : ℝ) ^ (-D) ∧
        ‖((1 - ((s N : ℝ) : ℂ) • SB (B.L N)) * Theta (B.L N) ((u : ℝ) : ℂ)) x y‖ ≤
          (B.W N : ℝ) ^ (-D) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hC : 0 < 2 * cTwo52 := by have := cTwo52_pos; positivity
  have hW := tendsto_W B
  -- `ℓ*_u ≥ (log W)^{3/2}`, so `δ ℓ*_u / 2 ≥ 1` eventually
  have hlog : Tendsto (fun N => log (B.W N : ℝ) ^ (3 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_log_atTop.comp hW)
  filter_upwards [SumZeroDyn.flow_crudeN hE hs0 hst ht1 hc, eventually_le_W_sq B,
    hW.eventually (eventually_mul_exp_neg_log_rpow_le (by have := cZero_pos; positivity :
      0 < cZero * (δ / 2)) hC (D + 3)),
    hW.eventually_ge_atTop 2, hlog.eventually_ge_atTop (2 / δ)] with N hcr hW2 hexp hW2' hl
  obtain ⟨-, -, hN1, hsc⟩ := hcr
  intro u x y hxy
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by linarith
  have hL3 := B.three_le_L N
  have hu0 : 0 ≤ (u : ℝ) := ((hs0 N).trans u.2.1)
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have hℓ1 : 1 ≤ B.ell N u := one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have hN : (N : ℝ) ≤ (B.W N : ℝ) ^ 2 := hW2
  have hinv : (1 - (u : ℝ))⁻¹ ≤ N := (hsc u).2.2
  -- the bound on `Θ_u` at distance `≥ (δ/2) ℓ*_u`
  have hfar : ∀ z : ZMod (B.L N), (δ / 2) * ellStar (B.W N) (B.ell N u) ≤ zdist (B.L N) (z - y) →
      ‖Theta (B.L N) ((u : ℝ) : ℂ) z y‖ ≤ (B.W N : ℝ) ^ (-(D + 1)) := by
    intro z hz
    have h1 := norm_Theta_le_of_ellStar (B.L N) hL3 hu0 hu1 hz
    refine h1.trans ?_
    have hpre : cTwo52 / ((1 - (u : ℝ)) * B.ell N u) ≤ cTwo52 * (B.W N : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ (1 - (u : ℝ)) * (B.W N : ℝ) ^ 2 * B.ell N u := by
        have h2 : 1 ≤ (1 - (u : ℝ)) * N := by
          rw [inv_le_iff_one_le_mul₀' h1u] at hinv; linarith
        have h3 : (1 - (u : ℝ)) * N ≤ (1 - (u : ℝ)) * (B.W N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hN h1u.le
        nlinarith
      have := cTwo52_pos
      nlinarith
    have hexp' : 2 * cTwo52 * exp (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ))) ≤
        (B.W N : ℝ) ^ (-(D + 3)) := by
      simpa [mul_assoc] using hexp
    have hWsplit : (B.W N : ℝ) ^ (-(D + 3)) * (B.W N : ℝ) ^ 2 = (B.W N : ℝ) ^ (-(D + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hW0]; push_cast; ring_nf
    have he0 := exp_pos (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ)))
    calc cTwo52 / ((1 - (u : ℝ)) * B.ell N u) * exp (-(cZero * (δ / 2) *
          log (B.W N) ^ (3 / 2 : ℝ)))
        ≤ cTwo52 * (B.W N : ℝ) ^ 2 * exp (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ))) := by
          gcongr
      _ = (B.W N : ℝ) ^ 2 * (cTwo52 * exp (-(cZero * (δ / 2) * log (B.W N) ^ (3 / 2 : ℝ)))) := by
          ring
      _ ≤ (B.W N : ℝ) ^ 2 * (B.W N : ℝ) ^ (-(D + 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := mul_pos cTwo52_pos he0
          linarith
      _ = _ := by rw [mul_comm]; exact hWsplit
  have hWD : (B.W N : ℝ) ^ (-(D + 1)) ≤ (B.W N : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
  have hstar : 1 ≤ (δ / 2) * ellStar (B.W N) (B.ell N u) := by
    unfold ellStar
    have : 2 / δ ≤ log (B.W N) ^ (3 / 2 : ℝ) * B.ell N u := by
      have hlogpos : 0 ≤ log (B.W N) ^ (3 / 2 : ℝ) := by
        have := (div_pos two_pos hδ).le; linarith
      nlinarith
    rw [div_le_iff₀ hδ] at this
    nlinarith
  refine ⟨(hfar x (by linarith)).trans hWD, ?_⟩
  have hs1 : s N ≤ 1 := ((hst N).trans_lt (ht1 N)).le
  have h2 := norm_oneSub_mul_Theta_le (B.L N) hL3 (hs0 N) hs1 (t := u) (x := x) (y := y)
    (M := (B.W N : ℝ) ^ (-(D + 1))) fun z hz => hfar z (by linarith)
  refine h2.trans ?_
  have : 2 * (B.W N : ℝ) ^ (-(D + 1)) = 2 * (B.W N : ℝ)⁻¹ * (B.W N : ℝ) ^ (-D) := by
    rw [neg_add, Real.rpow_add hW0, Real.rpow_neg_one]; ring
  rw [this]
  have : 2 * (B.W N : ℝ)⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hW0]; linarith
  have hε : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
  nlinarith

end Eq530

end Step2

end RBM
