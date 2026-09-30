/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridFarLift
import RBM1D.EnergyN.Gauss.Lemma514Holder
import RBM1D.EnergyN.Gauss.Step2Plain

/-!
# The far-field pointwise bound and the far part of (2.76), at an `N`-dependent energy

The predicate `RBM.Gauss.Grid.FarGridPointwiseN` (the far-field analogue of `GridPointwise'N`,
with the tail bound `tailT` at far pairs) and two consequences at an `N`-dependent energy
`E : ℕ → ℝ`: the far-field bound at each time (`RBM.Gauss.Grid.FarLift.hpt_of_farGridPointwiseN`)
and uniformly on `[s, t]` (`RBM.Gauss.Grid.hfar_of_farGridPointwiseN`).

`FarLift.pg_bad_far_eq_flow` (this file, deterministic, `E`-free apart from a scalar argument),
`FarLift.exists_netTime_le_close` and `stochDom_of_forall_seq_left` (fully `E`-free) are
energy-free and used at `E N`.

## The external `κ`

`hpt_of_farGridPointwiseN` needs no `κ`: it is a direct assembly of the `∀ᶠ N` clause of
`FarGridPointwiseN` with the (`E`-free) `pg_bad_far_eq_flow`.

`hfar_of_farGridPointwiseN` calls `hKb_flowN` (`RBM1D/EnergyN/Gauss/Lemma514Holder.lean`), whose
constant depends on the gap, as `h276_of_pointwise_plainN`
(`RBM1D/EnergyN/Gauss/Step2Gauss.lean`) does. It therefore takes
`{κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)` rather than `∀ N, |E N| < 2`.
The paper's statements are uniform in `|E| ≤ 2 - κ`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped Matrix.Norms.L2Operator

variable (d : Dims)

/-- **The far-field pointwise grid bound**: as `GridPointwise'N`, for the event that `lkErrMat` of
the grid process exceeds `N^δ tailT` at some far pair `|p₁ - p₂| > 6 ℓ*_u`. -/
def FarGridPointwiseN (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N,
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ D₁ : ℝ, 0 < D₁ →
      ∃ K : ℕ → ℕ, (∀ N, K N ≠ 0) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ((K N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ C) ∧
        ∀ᶠ N : ℕ in atTop, Pg d {ω | ∃ p : ZMod (d.L N) × ZMod (d.L N),
          6 * ellStar (d.W N : ℝ) ((band d).ell N (u N : ℝ)) < (zdist (d.L N) (p.1 - p.2) : ℝ) ∧
          (N : ℝ) ^ δ * tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ)) (etaT (E N) (u N : ℝ)) D
              (zdist (d.L N) (p.1 - p.2))
            < lkErrMat d (E N) N (u N : ℝ) (H d s (fun N => (u N : ℝ)) K N (K N) ω)
                (pmLoop p.1 p.2)}
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-D₁))

/-- **The far part of (2.76) at each time `u N ∈ [s, t]`**: for pairs with `|v₁ - v₂| > 6 ℓ*_u`,
`|L - K| ≺ tailT`, from `FarGridPointwiseN`. -/
theorem FarLift.hpt_of_farGridPointwiseN {E : ℕ → ℝ} {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hG : FarGridPointwiseN d E s t) :
    ∀ D : ℝ, 0 < D → ∀ u : ∀ N, TimeIcc s t N, StochDom (RBM.Gauss.P d)
      (fun N (v : ZMod (d.L N) × ZMod (d.L N)) ω =>
        if (zdist (d.L N) (v.1 - v.2) : ℝ) ≤ 6 * ellStar (d.W N : ℝ) ((band d).ell N (u N : ℝ))
          then 0 else (sample d).lkErr (E N) N (u N : ℝ) ω (pmLoop v.1 v.2))
      (fun N v _ => tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ)) (etaT (E N) (u N : ℝ)) D
        (zdist (d.L N) (v.1 - v.2))) := by
  intro D hD u
  obtain ⟨δ₀, hδ₀, hG'⟩ := hG D hD u
  intro τ hτ D₁ hD₁
  obtain ⟨K, hK0, -, hbad⟩ := hG' (min τ δ₀) (lt_min hτ hδ₀) (min_le_right _ _) D₁ hD₁
  filter_upwards [hbad, eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  rw [FarLift.pg_bad_far_eq_flow d (E := E N) (δ := min τ δ₀) (uR := fun N => (u N : ℝ))
    (hs0 N) (u N).2.1 (hK0 N) (far := fun v => 6 * ellStar (d.W N : ℝ) ((band d).ell N (u N : ℝ))
       < (zdist (d.L N) (v.1 - v.2) : ℝ))
    (fun v => tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ)) (etaT (E N) (u N : ℝ)) D
      (zdist (d.L N) (v.1 - v.2)))] at hN
  refine le_trans (measure_mono ?_) hN
  intro ω hω
  obtain ⟨v, hv⟩ := hω
  by_cases hfar : (zdist (d.L N) (v.1 - v.2) : ℝ)
      ≤ 6 * ellStar (d.W N : ℝ) ((band d).ell N (u N : ℝ))
  · exfalso
    simp only [if_pos hfar] at hv
    have htail0 : (0 : ℝ) ≤ tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ)) (etaT (E N) (u N : ℝ))
        D (zdist (d.L N) (v.1 - v.2)) := tailT_nonneg (by positivity) _
    have hpow0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) _
    nlinarith [hv, htail0, hpow0]
  · simp only [if_neg hfar] at hv
    refine ⟨v, not_le.mp hfar, ?_⟩
    have hδτN : (N : ℝ) ^ (min τ δ₀) ≤ (N : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hN1'
      (min_le_left _ _)
    have htail0 : (0 : ℝ) ≤ tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ)) (etaT (E N) (u N : ℝ))
        D (zdist (d.L N) (v.1 - v.2)) := tailT_nonneg (by positivity) _
    calc (N : ℝ) ^ (min τ δ₀) * tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ))
            (etaT (E N) (u N : ℝ)) D (zdist (d.L N) (v.1 - v.2))
        ≤ (N : ℝ) ^ τ * tailT (d.W N : ℝ) ((band d).ell N (u N : ℝ))
            (etaT (E N) (u N : ℝ)) D (zdist (d.L N) (v.1 - v.2)) :=
          mul_le_mul_of_nonneg_right hδτN htail0
      _ < (sample d).lkErr (E N) N (u N : ℝ) ω (pmLoop v.1 v.2) := hv

/-- **The far part of (2.76) uniformly in `u ∈ [s, t]`**, from `FarGridPointwiseN` and
`N^c ≤ W ℓ_t η_t` eventually. The proof calls `hKb_flowN`, whose constant depends on the gap, so
the theorem takes `{κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)`. -/
theorem hfar_of_farGridPointwiseN (d : Dims) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ}
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {c : ℝ} (hc0 : 0 < c)
    (hAc : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ c ≤ (band d).scale (E N) N (t N))
    (hG : FarGridPointwiseN d E s t) :
    ∀ D : ℝ, 0 < D → StochDom (band d).P
      (fun N (p : TimeIcc s t N × (ZMod ((band d).L N) × ZMod ((band d).L N))) ω =>
        if (zdist ((band d).L N) (p.2.1 - p.2.2) : ℝ) ≤
            6 * ellStar ((band d).W N : ℝ) ((band d).ell N p.1)
          then 0 else (sample d).lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => tailT ((band d).W N : ℝ) ((band d).ell N p.1) (etaT (E N) p.1) D
        (zdist ((band d).L N) (p.2.1 - p.2.2))) := by
  intro D hD0
  have hE' : ∀ N, |E N| < 2 := fun N => by linarith [hEκ N]
  have hlen : ∀ N, t N - s N ≤ 1 := fun N => by linarith [hs0 N, ht1 N]
  have hΞ : HighProb (band d).P (fun N => {ω | ‖Xmat d N ω‖ ≤ (N : ℝ)}) := highProb_norm_Xmat_le d
  have hseq := FarLift.hpt_of_farGridPointwiseN d hs0 hG D hD0
  have hlow : ∀ᶠ N : ℕ in atTop, ∀ (p : TimeIcc s t N × (ZMod (d.L N) × ZMod (d.L N))) (ω : Ω d),
      (N : ℝ) ^ (-(D + 2)) ≤ tailT ((band d).W N : ℝ) ((band d).ell N (p.1 : ℝ))
        (etaT (E N) (p.1 : ℝ)) D (zdist (d.L N) (p.2.1 - p.2.2)) := by
    filter_upwards [(band d).dim, eventually_ge_atTop 1] with N hdimN hN1 p ω
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hWpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have hL1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
    have hWleN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).W N ≤ N := le_trans (Nat.le_mul_of_pos_right _ hL1) hdimN.1
      exact_mod_cast hle
    have hWD_le : (N : ℝ) ^ (-D) ≤ ((band d).W N : ℝ) ^ (-D) := by
      have hpow_le : ((band d).W N : ℝ) ^ D ≤ (N : ℝ) ^ D :=
        Real.rpow_le_rpow hWpos.le hWleN hD0.le
      have hpow_pos : (0 : ℝ) < ((band d).W N : ℝ) ^ D := Real.rpow_pos_of_pos hWpos D
      have := inv_anti₀ hpow_pos hpow_le
      rwa [← Real.rpow_neg hWpos.le, ← Real.rpow_neg (Nat.cast_nonneg N)] at this
    have hTail : ((band d).W N : ℝ) ^ (-D) ≤ tailT ((band d).W N : ℝ) ((band d).ell N (p.1 : ℝ))
        (etaT (E N) (p.1 : ℝ)) D (zdist (d.L N) (p.2.1 - p.2.2)) := rpow_neg_le_tailT _
    have hND2 : (N : ℝ) ^ (-(D + 2)) ≤ (N : ℝ) ^ (-D) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    linarith [hWD_le, hTail, hND2]
  have hreg1 := etaT_inv_le_of_plainN (band d) hE' ht1 hc0 hAc
  have hreg1' : ∀ᶠ N : ℕ in atTop, (etaT (E N) (t N))⁻¹ ≤ (N : ℝ) ^ (1 : ℝ) := by
    filter_upwards [hreg1] with N hN; rwa [Real.rpow_one]
  have hKb2raw := hKb_flowN (band d) hκ0 hκ1 hEκ ht1 zero_le_one (2 : ℕ) hreg1'
  have he3 : (1 : ℝ) * ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  have hKb2 : ∀ᶠ N : ℕ in atTop, ∀ w ∈ Set.Icc (0 : ℝ) (t N), ∀ J : LoopIdx (ZMod ((band d).L N)),
      J.WF → 2 ≤ J.length → J.length ≤ 2 → ‖(band d).Kval (E N) N w J‖ ≤ (N : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hKb2raw] with N hN w hw J hJ h2 h2'
    have := hN w hw J hJ h2 h2'
    rwa [he3] at this
  have hgap1 : ∀ᶠ N : ℕ in atTop,
      8 * (N : ℝ) ^ ((8 : ℝ) - (4 * D + 44) / 2) ≤ 1 * (N : ℝ) ^ (-(D + 2 + 2)) :=
    eventually_mul_rpow_le_mul_rpow 8 1 one_pos (by linarith)
  have hgap2 : ∀ᶠ N : ℕ in atTop,
      5 * (N : ℝ) ^ ((4 : ℝ) - (4 * D + 44)) ≤ 1 * (N : ℝ) ^ (-(D + 2)) :=
    eventually_mul_rpow_le_mul_rpow 5 1 one_pos (by linarith)
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ {ω : Ω d | ‖Xmat d N ω‖ ≤ (N : ℝ)},
      ∀ u u' : TimeIcc s t N, (u' : ℝ) ≤ u → (u : ℝ) - u' ≤ (N : ℝ) ^ (-(4 * D + 44)) →
      ∀ v : ZMod (d.L N) × ZMod (d.L N),
        (if (zdist (d.L N) (v.1 - v.2) : ℝ) ≤
              6 * ellStar ((band d).W N : ℝ) ((band d).ell N (u : ℝ))
            then (0 : ℝ) else (sample d).lkErr (E N) N (u : ℝ) ω (pmLoop v.1 v.2)) ≤
          (if (zdist (d.L N) (v.1 - v.2) : ℝ) ≤
              6 * ellStar ((band d).W N : ℝ) ((band d).ell N (u' : ℝ))
            then (0 : ℝ) else (sample d).lkErr (E N) N (u' : ℝ) ω (pmLoop v.1 v.2))
            + (N : ℝ) ^ (-(D + 2 + 2)) ∧
        tailT ((band d).W N : ℝ) ((band d).ell N (u' : ℝ)) (etaT (E N) (u' : ℝ)) D
            (zdist (d.L N) (v.1 - v.2))
          ≤ 2 * tailT ((band d).W N : ℝ) ((band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D
              (zdist (d.L N) (v.1 - v.2)) := by
    filter_upwards [hreg1, hKb2, (band d).dim, hlow, hgap1, hgap2, eventually_ge_atTop 1] with
      N hreg1N hKb2N hdimN hlowN hgap1N hgap2N hN1 ω hωΞ u u' huu' hclosedist v
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < N := by linarith
    have hWNpos : (0 : ℝ) < ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    have hLpos1 : 1 ≤ (band d).L N := by have := (band d).three_le_L N; omega
    have hWleN : ((band d).W N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).W N ≤ N := le_trans (Nat.le_mul_of_pos_right _ hLpos1) hdimN.1
      exact_mod_cast hle
    have hLleN : ((band d).L N : ℝ) ≤ (N : ℝ) := by
      have hle : (band d).L N ≤ N := le_trans (Nat.le_mul_of_pos_left _ ((band d).W_pos N)) hdimN.1
      exact_mod_cast hle
    have hLleN' : (d.L N : ℝ) ≤ (N : ℝ) := hLleN
    have hu_lo : s N ≤ (u : ℝ) := u.2.1
    have hu_hi : (u : ℝ) ≤ t N := u.2.2
    have hu'_lo : s N ≤ (u' : ℝ) := u'.2.1
    have hu'_hi : (u' : ℝ) ≤ t N := u'.2.2
    have hu_lo0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (hs0 N) hu_lo
    have hu'_lo0 : (0 : ℝ) ≤ (u' : ℝ) := le_trans (hs0 N) hu'_lo
    have hu_lt1 : (u : ℝ) < 1 := lt_of_le_of_lt hu_hi (ht1 N)
    have hu'_lt1 : (u' : ℝ) < 1 := lt_of_le_of_lt hu'_hi (ht1 N)
    have hu_Icc0T : (u : ℝ) ∈ Set.Icc (0 : ℝ) (t N) := ⟨hu_lo0, hu_hi⟩
    have hu'_Icc0T : (u' : ℝ) ∈ Set.Icc (0 : ℝ) (t N) := ⟨hu'_lo0, hu'_hi⟩
    have hX : ‖Xmat d N ω‖ + 1 ≤ 2 * (N : ℝ) := by linarith [hωΞ]
    have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
    refine ⟨?_, ?_⟩
    · by_cases hfar_u : (zdist (d.L N) (v.1 - v.2) : ℝ) ≤
          6 * ellStar ((band d).W N : ℝ) ((band d).ell N (u : ℝ))
      · rw [if_pos hfar_u]
        have h0 : (0 : ℝ) ≤ (if (zdist (d.L N) (v.1 - v.2) : ℝ) ≤
            6 * ellStar ((band d).W N : ℝ) ((band d).ell N (u' : ℝ)) then (0 : ℝ)
            else (sample d).lkErr (E N) N (u' : ℝ) ω (pmLoop v.1 v.2)) := by
          split_ifs
          · exact le_refl 0
          · exact norm_nonneg _
        have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2 + 2)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        linarith [h0, h1]
      · rw [if_neg hfar_u]
        have hfar_u' : ¬ ((zdist (d.L N) (v.1 - v.2) : ℝ) ≤
            6 * ellStar ((band d).W N : ℝ) ((band d).ell N (u' : ℝ))) :=
          RBM.Step2FarMart.far_mono_time (B := band d) hW1 huu' hu_lt1 hfar_u
        rw [if_neg hfar_u']
        have habs : |(u : ℝ) - u'| = (u : ℝ) - u' := abs_of_nonneg (by linarith [huu'])
        have habs' : |(u : ℝ) - u'| ≤ (N : ℝ) ^ (-(4 * D + 44)) := by rw [habs]; exact hclosedist
        have hsqrt_le : Real.sqrt |(u : ℝ) - u'| ≤ (N : ℝ) ^ (-(4 * D + 44) / 2) :=
          sqrt_abs_sub_le_rpow habs'
        have hmod := lkErr_modulus_plain d (hE' N) N (ht1 N) hu_Icc0T hu'_Icc0T hX hKb2N hreg1N
          hWleN hLleN hN1' v.1 v.2
        have heq8 : (N : ℝ) ^ (8 : ℕ) = (N : ℝ) ^ (8 : ℝ) := by
          rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have hstep : 8 * (N : ℝ) ^ (8 : ℕ) * (N : ℝ) ^ (-(4 * D + 44) / 2) ≤
            (N : ℝ) ^ (-(D + 2 + 2)) := by
          rw [heq8, mul_assoc, ← Real.rpow_add hN0]
          have hexpeq : (8 : ℝ) + -(4 * D + 44) / 2 = (8 : ℝ) - (4 * D + 44) / 2 := by ring
          rw [hexpeq]
          have h1mul : (1 : ℝ) * (N : ℝ) ^ (-(D + 2 + 2)) = (N : ℝ) ^ (-(D + 2 + 2)) := one_mul _
          linarith [hgap1N, h1mul]
        have hfinal : 8 * (N : ℝ) ^ (8 : ℕ) * Real.sqrt |(u : ℝ) - u'| ≤
            (N : ℝ) ^ (-(D + 2 + 2)) :=
          le_trans (mul_le_mul_of_nonneg_left hsqrt_le (by positivity)) hstep
        linarith [hmod, hfinal]
    · have hzdist_le_L : (zdist (d.L N) (v.1 - v.2) : ℝ) ≤ (d.L N : ℝ) := by
        have h2 := two_mul_zdist_le (d.L N) (v.1 - v.2)
        have hcast : (2 : ℕ) * zdist (d.L N) (v.1 - v.2) ≤ d.L N := h2
        have hcastR : (2 : ℝ) * (zdist (d.L N) (v.1 - v.2) : ℝ) ≤ (d.L N : ℝ) := by
          exact_mod_cast hcast
        have hzdist0 : (0 : ℝ) ≤ (zdist (d.L N) (v.1 - v.2) : ℝ) := Nat.cast_nonneg _
        linarith [hcastR, hzdist0]
      have hzdist0 : (0 : ℝ) ≤ (zdist (d.L N) (v.1 - v.2) : ℝ) := Nat.cast_nonneg _
      have hmodT := abs_tailT_sub_le d N (hE' N) hu_lo0 hu'_lo0 hu_hi hu'_hi (ht1 N) hzdist0
        hzdist_le_L (D := D)
      have habs : |(u : ℝ) - u'| = (u : ℝ) - u' := abs_of_nonneg (by linarith [huu'])
      have hδ0 : 0 < 1 - t N := by linarith [ht1 N]
      have hδ1 : 1 - t N ≤ 1 := by linarith [hs0 N, hst N]
      have hδsqrt : 1 - t N ≤ Real.sqrt (1 - t N) := by
        apply (Real.le_sqrt hδ0.le hδ0.le).2
        nlinarith [hδ1]
      have hinvsqrt : (Real.sqrt (1 - t N))⁻¹ ≤ (1 - t N)⁻¹ := inv_anti₀ hδ0 hδsqrt
      have hTinv : (1 - t N)⁻¹ ≤ (N : ℝ) := by
        have hηt : 0 < etaT (E N) (t N) := etaT_pos_of_lt_one' (hE' N) (ht1 N)
        have hle : etaT (E N) (t N) ≤ 1 - t N := etaT_le (hE' N).le (ht1 N).le
        exact (inv_anti₀ hηt hle).trans hreg1N
      have hCp_le : (2 * Real.sqrt (1 - t N))⁻¹ ≤ (N : ℝ) := by
        rw [mul_inv]
        have h2inv : (2 : ℝ)⁻¹ * (Real.sqrt (1 - t N))⁻¹ ≤ 1 * (Real.sqrt (1 - t N))⁻¹ :=
          mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.2 (Real.sqrt_nonneg _))
        rw [one_mul] at h2inv
        exact h2inv.trans (hinvsqrt.trans hTinv)
      have hCp0 : (0 : ℝ) ≤ (2 * Real.sqrt (1 - t N))⁻¹ := by positivity
      have hq0 : (0 : ℝ) ≤ (etaT (E N) (t N))⁻¹ := (inv_pos.2 (etaT_pos_of_lt_one' (hE' N)
        (ht1 N))).le
      have hL0 : (0 : ℝ) ≤ (d.L N : ℝ) := Nat.cast_nonneg _
      have hN2 : (N : ℝ) ^ (2 : ℕ) ≤ (N : ℝ) ^ (4 : ℕ) := pow_le_pow_right₀ hN1' (by norm_num)
      have hN3 : (N : ℝ) ^ (3 : ℕ) ≤ (N : ℝ) ^ (4 : ℕ) := pow_le_pow_right₀ hN1' (by norm_num)
      have term1 : 2 * (2 * Real.sqrt (1 - t N))⁻¹ * ((etaT (E N) (t N))⁻¹) ^ 2 ≤
          2 * (N : ℝ) ^ (4 : ℕ) := by
        have hq2 : ((etaT (E N) (t N))⁻¹) ^ 2 ≤ (N : ℝ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hq0 hreg1N 2
        have h1 : (2 * Real.sqrt (1 - t N))⁻¹ * ((etaT (E N) (t N))⁻¹) ^ 2
            ≤ (N : ℝ) * (N : ℝ) ^ (2 : ℕ) := mul_le_mul hCp_le hq2 (by positivity) (by linarith)
        calc 2 * (2 * Real.sqrt (1 - t N))⁻¹ * ((etaT (E N) (t N))⁻¹) ^ 2
            = 2 * ((2 * Real.sqrt (1 - t N))⁻¹ * ((etaT (E N) (t N))⁻¹) ^ 2) := by ring
          _ ≤ 2 * ((N : ℝ) * (N : ℝ) ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 2 * (N : ℝ) ^ (3 : ℕ) := by ring
          _ ≤ 2 * (N : ℝ) ^ (4 : ℕ) := by linarith [hN3]
      have term2 : 2 * ((etaT (E N) (t N))⁻¹) ^ 3 ≤ 2 * (N : ℝ) ^ (4 : ℕ) := by
        have hq3 : ((etaT (E N) (t N))⁻¹) ^ 3 ≤ (N : ℝ) ^ (3 : ℕ) :=
          pow_le_pow_left₀ hq0 hreg1N 3
        have h1 := mul_le_mul_of_nonneg_left hq3 (by norm_num : (0 : ℝ) ≤ 2)
        linarith [h1, hN3]
      have term3 : ((etaT (E N) (t N))⁻¹) ^ 2 * ((d.L N : ℝ) / 2) * (2 * Real.sqrt (1 - t N))⁻¹
          ≤ (N : ℝ) ^ (4 : ℕ) := by
        have hq2 : ((etaT (E N) (t N))⁻¹) ^ 2 ≤ (N : ℝ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hq0 hreg1N 2
        have hLd2 : (d.L N : ℝ) / 2 ≤ (N : ℝ) / 2 := by linarith [hLleN']
        have h1 : ((etaT (E N) (t N))⁻¹) ^ 2 * ((d.L N : ℝ) / 2)
            ≤ (N : ℝ) ^ (2 : ℕ) * ((N : ℝ) / 2) :=
          mul_le_mul hq2 hLd2 (by positivity) (by positivity)
        have h2 : ((etaT (E N) (t N))⁻¹) ^ 2 * ((d.L N : ℝ) / 2) * (2 * Real.sqrt (1 - t N))⁻¹
            ≤ (N : ℝ) ^ (2 : ℕ) * ((N : ℝ) / 2) * (N : ℝ) :=
          mul_le_mul h1 hCp_le hCp0 (by positivity)
        calc ((etaT (E N) (t N))⁻¹) ^ 2 * ((d.L N : ℝ) / 2) * (2 * Real.sqrt (1 - t N))⁻¹
            ≤ (N : ℝ) ^ (2 : ℕ) * ((N : ℝ) / 2) * (N : ℝ) := h2
          _ = (N : ℝ) ^ (4 : ℕ) / 2 := by ring
          _ ≤ (N : ℝ) ^ (4 : ℕ) := by
                nlinarith [pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ)) 4]
      have htailLip_le : tailLip d N (E N) (t N) ≤ 5 * (N : ℝ) ^ (4 : ℕ) := by
        unfold tailLip
        linarith [term1, term2, term3]
      have heq4 : (N : ℝ) ^ (4 : ℕ) = (N : ℝ) ^ (4 : ℝ) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hN_A_tailLip : (N : ℝ) ^ (-(4 * D + 44)) * tailLip d N (E N) (t N)
          ≤ (N : ℝ) ^ (-(D + 2)) := by
        have hstep0 : (N : ℝ) ^ (-(4 * D + 44)) * tailLip d N (E N) (t N)
            ≤ (N : ℝ) ^ (-(4 * D + 44)) * (5 * (N : ℝ) ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left htailLip_le (by positivity)
        have hstep1 : (N : ℝ) ^ (-(4 * D + 44)) * (5 * (N : ℝ) ^ (4 : ℕ))
            = 5 * (N : ℝ) ^ (4 : ℝ) * (N : ℝ) ^ (-(4 * D + 44)) := by rw [heq4]; ring
        have hstep2 : 5 * (N : ℝ) ^ (4 : ℝ) * (N : ℝ) ^ (-(4 * D + 44))
            = 5 * (N : ℝ) ^ ((4 : ℝ) - (4 * D + 44)) := by
          rw [mul_assoc, ← Real.rpow_add hN0]
          congr 2
        have h1mul : (1 : ℝ) * (N : ℝ) ^ (-(D + 2)) = (N : ℝ) ^ (-(D + 2)) := one_mul _
        calc (N : ℝ) ^ (-(4 * D + 44)) * tailLip d N (E N) (t N)
            ≤ (N : ℝ) ^ (-(4 * D + 44)) * (5 * (N : ℝ) ^ (4 : ℕ)) := hstep0
          _ = 5 * (N : ℝ) ^ (4 : ℝ) * (N : ℝ) ^ (-(4 * D + 44)) := hstep1
          _ = 5 * (N : ℝ) ^ ((4 : ℝ) - (4 * D + 44)) := hstep2
          _ ≤ (N : ℝ) ^ (-(D + 2)) := by linarith [hgap2N, h1mul]
      have hbound : tailT ((band d).W N : ℝ) ((band d).ell N (u' : ℝ)) (etaT (E N) (u' : ℝ)) D
          (zdist (d.L N) (v.1 - v.2)) -
          tailT ((band d).W N : ℝ) ((band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D
          (zdist (d.L N) (v.1 - v.2)) ≤ (N : ℝ) ^ (-(D + 2)) := by
        have h1 : tailT ((band d).W N : ℝ) ((band d).ell N (u' : ℝ)) (etaT (E N) (u' : ℝ)) D
              (zdist (d.L N) (v.1 - v.2)) -
            tailT ((band d).W N : ℝ) ((band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D
              (zdist (d.L N) (v.1 - v.2)) ≤
            |tailT ((band d).W N : ℝ) ((band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D
              (zdist (d.L N) (v.1 - v.2)) -
            tailT ((band d).W N : ℝ) ((band d).ell N (u' : ℝ)) (etaT (E N) (u' : ℝ)) D
              (zdist (d.L N) (v.1 - v.2))| := by
          rw [abs_sub_comm]; exact le_abs_self _
        have h2 : |tailT ((band d).W N : ℝ) ((band d).ell N (u : ℝ)) (etaT (E N) (u : ℝ)) D
              (zdist (d.L N) (v.1 - v.2)) -
            tailT ((band d).W N : ℝ) ((band d).ell N (u' : ℝ)) (etaT (E N) (u' : ℝ)) D
              (zdist (d.L N) (v.1 - v.2))| ≤ |(u : ℝ) - u'| * tailLip d N (E N) (t N) := hmodT
        have h3 : |(u : ℝ) - u'| * tailLip d N (E N) (t N)
            ≤ (N : ℝ) ^ (-(4 * D + 44)) * tailLip d N (E N) (t N) := by
          rw [habs]
          exact mul_le_mul_of_nonneg_right hclosedist (tailLip_nonneg d N (hE' N) (ht1 N))
        linarith [h1, h2, h3, hN_A_tailLip]
      linarith [hbound, hlowN (u, v) ω]
  exact stochDom_of_forall_seq_left (s := s) (t := t) hst (T := 1) one_pos hlen
    (A := 4 * D + 44) (by linarith) hseq hΞ hlow hclose

end RBM.Gauss.Grid
