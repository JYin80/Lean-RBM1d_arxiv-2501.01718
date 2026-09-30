/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Step6Hyp
import RBM1D.EnergyN.Hierarchy.Step6
import RBM1D.EnergyN.Unif.Flow.Iteration
import RBM1D.EnergyN.Flow.Hypotheses

/-!
# The Gaussian-model inputs `h527`, `hq11` of Step 6, at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.8.

The inputs `h527` ((5.127)) and `hq11` of `RBM.sharpExpect_step6_driftEG'N` for the Gaussian
model, at an `N`-dependent energy `E : ℕ → ℝ`: `RBM.Gauss.eq527N_gauss` (by diagonal
specialisation of `RBM.Gauss.eq527_gauss`), and `RBM.Gauss.stochDom_lkErr_mulN`,
`RBM.Gauss.unifDetDom_integral_lkErr_mulN`, `RBM.Gauss.quad11_unifDetDom'N`,
`RBM.Gauss.quad11_unifDetDom_gauss'N`.

## The external `κ`

`RBM.Gauss.quad11_unifDetDom'N` needs a kernel constant `C1` (`n = 1`) in the slot `CK` of
`unifDetDom_integral_lkErr_mulN`. It takes `C1` from `RBM.Band.norm_Kval_le_unif`
(`∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - k → …`, `EnergyN/Unif/Flow/Iteration.lean`), obtained once before
`N` and instantiated at `E N` via `hEκ N`. `RBM.Gauss.stochDom_lkErr_mulN` and
`RBM.Gauss.unifDetDom_integral_lkErr_mulN` take their kernel bound `CK` as an explicit
hypothesis, so they fix no energy-dependent constant; `RBM.Gauss.quad11_unifDetDom_gauss'N` takes
the bound through `RBM.Gauss.quad11_unifDetDom'N`.
-/

namespace RBM.Gauss

open MeasureTheory Filter

/-! ### `RBM.Gauss.eq527N_gauss`: diagonal specialisation -/

section Eq527GaussN

/-- **`h527` of `RBM.sharpExpect_step6_driftEG'N` for the Gaussian model, at an `N`-dependent
energy.** Diagonal specialisation of `RBM.Gauss.eq527_gauss`: for each
`N`, apply the fixed-energy theorem at `E := E N` (giving (5.127) for every internal index), then
extract the `N`-th equation. -/
theorem eq527N_gauss (d : Dims) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) :
    Step6.Eq527N (sample d) E s t :=
  fun N u a => eq527_gauss d (hE N) hs0 ht1 N u a

end Eq527GaussN

/-! ### The first-moment reverse bridge, at an `N`-dependent energy -/

section FirstMomentN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **The product of two `|L - K|`'s is `≺` the product of the two controls**, at an
`N`-dependent energy. No
energy-dependent constant is fixed here: `m`, `n` are fixed loop lengths, no kernel constant is
derived here. -/
theorem stochDom_lkErr_mulN (X : Sample B) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {m n : ℕ}
    (hdm : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ m))
    (hdn : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ n)) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × (LoopData (B.L N) m × LoopData (B.L N) n)) ω =>
        X.lkErr (E N) N p.1 ω p.2.1.idx * X.lkErr (E N) N p.1 ω p.2.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ (m + n)) := by
  refine StochDom.of_subset_union hdm hdn fun τ hτ =>
    ⟨τ / 2, half_pos hτ, Filter.Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨p, hp⟩
  by_contra hno
  simp only [Set.mem_union, badSet, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have h1 := hno.1 (p.1, p.2.1)
  have h2 := hno.2 (p.1, p.2.2)
  have hsc0 : 0 < B.scale (E N) N (p.1 : ℝ) :=
    B.scale_pos' (hE N) N ((hs0 N).trans p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
  have hinv0 : (0 : ℝ) ≤ (B.scale (E N) N (p.1 : ℝ))⁻¹ := (inv_nonneg.2 hsc0.le)
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hY2 : 0 ≤ X.lkErr (E N) N (p.1 : ℝ) ω p.2.2.idx := norm_nonneg _
  have hζ1 : (0 : ℝ) ≤ (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ m := pow_nonneg hinv0 m
  have hkey : X.lkErr (E N) N (p.1 : ℝ) ω p.2.1.idx * X.lkErr (E N) N (p.1 : ℝ) ω p.2.2.idx
      ≤ (N : ℝ) ^ τ * (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ (m + n) := by
    calc X.lkErr (E N) N (p.1 : ℝ) ω p.2.1.idx * X.lkErr (E N) N (p.1 : ℝ) ω p.2.2.idx
        ≤ ((N : ℝ) ^ (τ / 2) * (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ m)
            * X.lkErr (E N) N (p.1 : ℝ) ω p.2.2.idx := mul_le_mul_of_nonneg_right h1 hY2
      _ ≤ ((N : ℝ) ^ (τ / 2) * (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ m)
            * ((N : ℝ) ^ (τ / 2) * (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ n) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hpos hζ1)
      _ = ((N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2))
            * ((B.scale (E N) N (p.1 : ℝ))⁻¹ ^ m * (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ n) := by ring
      _ = (N : ℝ) ^ τ * (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ (m + n) := by
          rw [UnifDetDom.rpow_half_mul_rpow_half N hτ, ← pow_add]
  linarith

/-- **The first-moment reverse bridge, applied to a product of two `|L - K|`'s**, at an
`N`-dependent energy. No energy-dependent constant is fixed here: `CK` is a hypothesis (`hKm`,
`hKn`), not derived internally. -/
theorem unifDetDom_integral_lkErr_mulN (X : Sample B) {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT (E N) u)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hKm : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) m),
      ‖B.Kval (E N) N u v.idx‖ ≤ CK * (B.scale (E N) N u)⁻¹ ^ (m - 1))
    (hKn : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) n),
      ‖B.Kval (E N) N u v.idx‖ ≤ CK * (B.scale (E N) N u)⁻¹ ^ (n - 1))
    (hint : ∀ N (p : TimeIcc s t N × (LoopData (B.L N) m × LoopData (B.L N) n)),
      Integrable (fun ω => X.lkErr (E N) N p.1 ω p.2.1.idx * X.lkErr (E N) N p.1 ω p.2.2.idx)
        B.P)
    (hdm : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ m))
    (hdn : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ n)) :
    UnifDetDom
      (fun N (p : TimeIcc s t N × (LoopData (B.L N) m × LoopData (B.L N) n)) =>
        ∫ ω, X.lkErr (E N) N p.1 ω p.2.1.idx * X.lkErr (E N) N p.1 ω p.2.2.idx ∂B.P)
      (fun N p => (B.scale (E N) N p.1)⁻¹ ^ (m + n)) := by
  have := B.isProbabilityMeasure
  refine unifDetDom_integral_of_stochDom_of_nonneg (B := ((m + n : ℕ) : ℝ))
    (Kenv := c * ((m : ℝ) + (n : ℝ)) + 1)
    (fun N p ω => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hint ?_ (by positivity) ?_
    (by positivity) ?_ (stochDom_lkErr_mulN X hE hs0 ht1 hdm hdn)
  · intro N p
    have hsc0 : 0 < B.scale (E N) N (p.1 : ℝ) :=
      B.scale_pos' (hE N) N ((hs0 N).trans p.1.2.1) (p.1.2.2.trans_lt (ht1 N))
    positivity
  · filter_upwards [B.dim, eventually_ge_atTop 1] with N hdim hN1 p
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hu0 : (0 : ℝ) ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have hsc0 : 0 < B.scale (E N) N (p.1 : ℝ) := B.scale_pos' (hE N) N hu0 hu1
    have hell : B.ell N (p.1 : ℝ) ≤ (B.L N : ℝ) := by
      simp only [Band.ell, ellHat]; exact min_le_right _ _
    have hell0 : (0 : ℝ) ≤ B.ell N (p.1 : ℝ) :=
      le_trans zero_le_one (one_le_ellHat_of_nonneg (B.one_le_L N) hu0 hu1)
    have heta1 : etaT (E N) (p.1 : ℝ) ≤ 1 := etaT_le_one (hE N) hu0
    have heta0 : (0 : ℝ) < etaT (E N) (p.1 : ℝ) := etaT_pos_of_lt_one (hE N) hu1
    have hW0 : (0 : ℝ) ≤ (B.W N : ℝ) := Nat.cast_nonneg _
    have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
    have hscN : B.scale (E N) N (p.1 : ℝ) ≤ (N : ℝ) := by
      have h1 : B.scale (E N) N (p.1 : ℝ)
          = (B.W N : ℝ) * B.ell N (p.1 : ℝ) * etaT (E N) (p.1 : ℝ) := rfl
      rw [h1]
      have hstep : (B.W N : ℝ) * B.ell N (p.1 : ℝ) * etaT (E N) (p.1 : ℝ)
          ≤ ((B.W N : ℝ) * (B.L N : ℝ)) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hell hW0) heta1 heta0.le (by positivity)
      linarith
    have hinv : (N : ℝ)⁻¹ ≤ (B.scale (E N) N (p.1 : ℝ))⁻¹ := inv_anti₀ hsc0 hscN
    have hpow : ((N : ℝ)⁻¹) ^ (m + n) ≤ (B.scale (E N) N (p.1 : ℝ))⁻¹ ^ (m + n) :=
      pow_le_pow_left₀ (inv_nonneg.2 hNpos.le) hinv _
    refine le_trans (le_of_eq ?_) hpow
    rw [Real.rpow_neg hNpos.le, Real.rpow_natCast, inv_pow]
  · filter_upwards [hη, eventually_ge_atTop 1, eventually_le_rpow ((1 + CK) ^ 2) one_pos] with
      N hηN hN1 hCN p ω
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hu0 : (0 : ℝ) ≤ (p.1 : ℝ) := (hs0 N).trans p.1.2.1
    have hu1 : (p.1 : ℝ) < 1 := p.1.2.2.trans_lt (ht1 N)
    have h1 := lkErr_loopData_le_rpow X (hE N) hN1 hu0 hu1 hc0 (hηN p.1) ω hm p.2.1 hCK0
      (hKm N p.1 p.2.1)
    have h2 := lkErr_loopData_le_rpow X (hE N) hN1 hu0 hu1 hc0 (hηN p.1) ω hn p.2.2 hCK0
      (hKn N p.1 p.2.2)
    have hr1 : (0 : ℝ) ≤ (1 + CK) * (N : ℝ) ^ (c * m) := by positivity
    have hstep : X.lkErr (E N) N (p.1 : ℝ) ω p.2.1.idx * X.lkErr (E N) N (p.1 : ℝ) ω p.2.2.idx
        ≤ ((1 + CK) * (N : ℝ) ^ (c * m)) * ((1 + CK) * (N : ℝ) ^ (c * n)) :=
      mul_le_mul h1 h2 (norm_nonneg _) hr1
    refine hstep.trans ?_
    have hCN' : (1 + CK) ^ 2 ≤ (N : ℝ) := by rwa [Real.rpow_one] at hCN
    have hprod0 : (0 : ℝ) ≤ (N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ)) := by positivity
    have hRHS : (N : ℝ) ^ (c * ((m : ℝ) + (n : ℝ)) + 1)
        = ((N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ))) * (N : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    calc ((1 + CK) * (N : ℝ) ^ (c * (m : ℝ))) * ((1 + CK) * (N : ℝ) ^ (c * (n : ℝ)))
        = (1 + CK) ^ 2 * ((N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ))) := by ring
      _ ≤ (N : ℝ) * ((N : ℝ) ^ (c * (m : ℝ)) * (N : ℝ) ^ (c * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hCN' hprod0
      _ = (N : ℝ) ^ (c * ((m : ℝ) + (n : ℝ)) + 1) := by
          rw [hRHS, Real.rpow_one]; ring

/-- **`hq11` of `RBM.sharpExpect_step6_driftEG'N`**, at an `N`-dependent energy:
`E[(L-K)_1 (L-K)_1] ≺ (W ℓ_u η_u)^{-2}`, uniformly in `u ∈ [s,t]` and in the two blocks. The
kernel constant `C1` (`n = 1`) comes from `RBM.Band.norm_Kval_le_unif`, obtained once before `N`
and instantiated at `E N` (module docstring). -/
theorem quad11_unifDetDom'N (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT (E N) u)
    (hint : ∀ N (p : TimeIcc s t N × (LoopData (B.L N) 1 × LoopData (B.L N) 1)),
      Integrable (fun ω => X.lkErr (E N) N p.1 ω p.2.1.idx * X.lkErr (E N) N p.1 ω p.2.2.idx)
        B.P)
    (hlmk : SharpLmKFlowN X E s t) :
    UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖Step6.quad11 X (E N) N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  obtain ⟨C1, hC10, hC1⟩ := B.norm_Kval_le_unif hκ0 hκ1 (n := 1) le_rfl
  have hK1 : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) 1),
      ‖B.Kval (E N) N u v.idx‖ ≤ C1 * (B.scale (E N) N u)⁻¹ ^ (1 - 1) := fun N u v =>
    hC1 (E N) (hEκ N) N u ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N)) v.idx v.idx_wf (by simp)
  have hmain := unifDetDom_integral_lkErr_mulN X hE hs0 ht1 (m := 1) (n := 1) le_rfl le_rfl
    hc0 hη hC10 hK1 hK1 hint (hlmk 1 le_rfl) (hlmk 1 le_rfl)
  have hre := hmain.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      (p.1, (oneLoopData p.2.1, oneLoopData p.2.2)))
  refine UnifDetDom.mono_left (Filter.Eventually.of_forall fun N p => ?_) hre
  simpa using norm_quad11_le_integral X (E N) N p.1 p.2.1 p.2.2

/-- **The same bound for the Gaussian model, with no integrability hypothesis**, at an
`N`-dependent energy, using `RBM.Gauss.quad11_unifDetDom'N`. -/
theorem quad11_unifDetDom_gauss'N (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hη : ∀ᶠ N : ℕ in Filter.atTop, ∀ u : TimeIcc s t N, (N : ℝ) ^ (-c) ≤ etaT (E N) u)
    (hlmk : SharpLmKFlowN (sample d) E s t) :
    UnifDetDom
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) =>
        ‖Step6.quad11 (sample d) (E N) N p.1 p.2.1 p.2.2‖)
      (fun N p => ((band d).scale (E N) N p.1)⁻¹ ^ 2) := by
  have hE : ∀ N, |E N| < 2 := fun N => by linarith [abs_nonneg (E N), hEκ N]
  refine quad11_unifDetDom'N (sample d) hκ0 hκ1 hEκ hs0 ht1 hc0 hη ?_ hlmk
  intro N p
  exact integrable_sample_lkErr_mul_real d N (hE N) (p.1.2.2.trans_lt (ht1 N)) _ _
    p.2.1.idx_wf (by simp [LoopData.idx]) p.2.2.idx_wf (by simp [LoopData.idx])

end FirstMomentN

end RBM.Gauss
