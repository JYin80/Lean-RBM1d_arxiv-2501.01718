/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.DetIBPWeighted
import RBM1D.EnergyN.Gauss.CondStableFlow

/-!
# The weighted conditional expectation of the diagonal, at an `N`-dependent energy

Two statements at an `N`-dependent energy `E : ℕ → ℝ`: `condExpDiag` at the index `i` differs from
`u m² Σ_k S_ik (G_kk - m)` by at most `Ψ²`, uniformly on `[s, t]`, given a bound on the remainder
`ibpRem` (`RBM.Gauss.unifDomIcc_condExpDiag_weighted_of_remN`) or given the uniform local law and
the good set (`RBM.Gauss.unifDomIcc_condExpDiag_weightedN`). Neither fixes an energy-dependent
constant.

The only `E`-use of `unifDomIcc_condExpDiag_weighted_of_remN`,
`RBM.Gauss.norm_condExpDiag_sub_le_two_phi`, takes `{N : ℕ} {E u : ℝ}` and is applied after `N`
is bound, i.e. it is energy-free, used at `E N`. `unifDomIcc_condExpDiag_weightedN` feeds
`RBM.Gauss.unifDomIcc_ibpRemN` (`RBM1D/EnergyN/Gauss/CondStableFlow.lean`) into it, with `hΩ`/`hll`
in the shapes `HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N)` and
`RBM.Gauss.LocalLawUnifIccN`.
-/

namespace RBM.Gauss

open Filter MeasureTheory

variable {d : Dims} {s t Ψ : ℕ → ℝ}

/-- **`|condExpDiag_i - u m² Σ_k S_ik (G_kk - m)| ≤ Ψ²`** uniformly on `[s, t]`, from the bound
`hrem` on `ibpRem` (`1` on the diagonal, `Ψ²` off it) and `W⁻¹ ≤ Ψ²`. -/
theorem unifDomIcc_condExpDiag_weighted_of_remN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hrem : UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω => ‖ibpRem d N (E N) u q ω‖)
      (fun N _ (q : d.Idx N × d.Idx N) _ =>
        if q.1 = q.2 then (1 : ℝ) else Ψ N * Ψ N)) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condExpDiag d N u (zt (E N) u) (mE (E N)) i ω
          - (u : ℂ) * mE (E N) ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt (E N) u) k k - mE (E N))‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  classical
  intro τ hτ D hD
  have hτ2 : (0 : ℝ) < τ / 2 := by linarith
  filter_upwards [hrem (τ / 2) hτ2 (D + 2) (by linarith),
    card_Idx_le d, eventually_ge_atTop 1, eventually_le_rpow 2 hτ2] with
    N hremN hcardN hN1 h2N u hu i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hu0 : 0 ≤ u := (hs0 N).trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt (ht1 N)
  set a : ℝ := (N : ℝ) ^ (τ / 2) with hadef
  have ha0 : 0 ≤ a := (Real.rpow_pos_of_pos hNpos _).le
  have ha2 : a * a = (N : ℝ) ^ τ := by
    rw [hadef, ← Real.rpow_add hNpos]
    congr 1
    ring
  set T : d.Idx N → Set (Ω d) := fun k =>
    {ω | a * (if i = k then (1 : ℝ) else Ψ N * Ψ N) <
      ‖ibpRem d N (E N) u (i, k) ω‖} with hTdef
  have hTk : ∀ k : d.Idx N, (P d) (T k) ≤
      ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) := by
    intro k
    exact hremN u hu (i, k)
  have hunion : (P d) (⋃ k, T k) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
    have hpow : (0 : ℝ) ≤ (N : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg hNpos.le _
    have hcard' : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) := by
      rw [Real.rpow_one] at hcardN
      exact hcardN
    calc
      (P d) (⋃ k, T k) ≤ ∑ k : d.Idx N, (P d) (T k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : d.Idx N, ENNReal.ofReal ((N : ℝ) ^ (-(D + 2))) :=
          Finset.sum_le_sum fun k _ => hTk k
      _ = ENNReal.ofReal ((Fintype.card (d.Idx N) : ℝ) *
          (N : ℝ) ^ (-(D + 2))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (Fintype.card (d.Idx N) : ℝ) * (N : ℝ) ^ (-(D + 2)) ≤
              (N : ℝ) * (N : ℝ) ^ (-(D + 2)) :=
            mul_le_mul_of_nonneg_right hcard' hpow
          have h2 : (N : ℝ) * (N : ℝ) ^ (-(D + 2)) =
              (N : ℝ) ^ (-(D + 1)) := by
            have hsplit := Real.rpow_add hNpos 1 (-(D + 2))
            rw [Real.rpow_one] at hsplit
            rw [← hsplit]
            congr 1
            ring
          have h3 : (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) :=
            Real.rpow_le_rpow_of_exponent_le hNge1 (by linarith)
          linarith
  have hsub : {ω | (N : ℝ) ^ τ * (Ψ N * Ψ N) <
      ‖condExpDiag d N u (zt (E N) u) (mE (E N)) i ω
        - (u : ℂ) * mE (E N) ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt (E N) u) k k - mE (E N))‖} ⊆ ⋃ k, T k := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hcon
    simp only [Set.mem_iUnion, not_exists] at hcon
    have hTle : ∀ k : d.Idx N, ‖ibpRem d N (E N) u (i, k) ω‖ ≤
        a * (if i = k then (1 : ℝ) else Ψ N * Ψ N) := by
      intro k
      have := hcon k
      rw [hTdef] at this
      simpa only [Set.mem_ofPred_eq, not_lt] using this
    have hΦ0 : 0 ≤ Ψ N * Ψ N := mul_nonneg (hΨ0 N) (hΨ0 N)
    have hbound := norm_condExpDiag_sub_le_two_phi (hE N) hu0 hu1 i ω ha0 hΦ0
      (hWΨ N) (fun k hk => by simpa [Ne.symm hk] using hTle k)
      (by simpa using hTle i)
    have h2a : 2 * a ≤ a * a := by
      have ha : 2 ≤ a := h2N
      nlinarith
    have hfin : ‖condExpDiag d N u (zt (E N) u) (mE (E N)) i ω
        - (u : ℂ) * mE (E N) ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
          * (green (Hflow d N u ω) (zt (E N) u) k k - mE (E N))‖ ≤
        (N : ℝ) ^ τ * (Ψ N * Ψ N) := by
      calc
        _ ≤ 2 * a * (Ψ N * Ψ N) := hbound
        _ ≤ (a * a) * (Ψ N * Ψ N) :=
          mul_le_mul_of_nonneg_right h2a hΦ0
        _ = _ := by rw [ha2]
    exact (not_le.2 hω) hfin
  exact (measure_mono hsub).trans hunion

variable {δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **The same bound from the uniform local law**, the good set `hΩ` and the envelope `hEnv`,
through `unifDomIcc_ibpRemN`. -/
theorem unifDomIcc_condExpDiag_weightedN {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop,
      ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hWΨ : ∀ N, ((d.W N : ℝ))⁻¹ ≤ Ψ N * Ψ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condExpDiag d N u (zt (E N) u) (mE (E N)) i ω
          - (u : ℂ) * mE (E N) ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
            * (green (Hflow d N u ω) (zt (E N) u) k k - mE (E N))‖)
      (fun N _ _ _ => Ψ N * Ψ N) :=
  unifDomIcc_condExpDiag_weighted_of_remN hE hs0 ht1 hΨ0 hWΨ
    (unifDomIcc_ibpRemN d hE ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΩ hll)

end RBM.Gauss
