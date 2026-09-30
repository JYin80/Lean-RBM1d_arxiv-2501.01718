/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514NonAlt
import RBM1D.Gauss.Lemma514Two
import RBM1D.Gauss.Step2Plain

/-!
# Lemma 5.14 at loop length `n = 2`, non-alternating charges (`σ 0 = σ 1`)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2/§5.5/§7 — Lemma 5.14 (Definition 5.12 and Lemma 7.3 allow `n ≥ 2`;
`RBM1D/Gauss/Lemma514NonAlt.lean` covers `n ≥ 3`, and this file supplies `n = 2`), Case 1 of
(7.16) at the smallest non-degenerate loop length.

## Why `n = 2` needs no new argument

`RBM.Gauss.Grid.norm_DgridN_le` (`Lemma514NonAlt.lean`) carries a hypothesis `hn3 : 3 ≤ n` that
its proof does not use; the only numeric fact about `n` it needs is `2 ≤ n` (the hypothesis of
`norm_primBil_le514`).  The `K`-loop term `∑ lK ∈ Finset.Icc 3 n, …` is an **empty sum** at
`n = 2`: in (5.14) `2 ≤ l_K ≤ n`, so the `l_K > 2` K-loop is empty at `n = 2`; the non-linear
term is still two length-2 loops, `E^{(L̃)}` uses length-1/length-3 loops, and the quadratic
variation uses a length-6 loop — none of which need `n ≥ 3`.  On `Fin 2`, `NonAlt` is
definitionally `∃ k : Fin 2, σ k = σ (k+1)`, and `k = 0` gives exactly `σ 0 = σ 1`, so the
non-alternating class at `n = 2` is the non-vacuous class of charges `(+,+)`, `(-,-)`.

## Main results

* `RBM.Gauss.Grid.norm_DgridN_le'` — `norm_DgridN_le`, `hn3 : 3 ≤ n` replaced by the
  (already sufficient) `hn2 : 2 ≤ n`; identical proof.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

variable (d : Dims)

section DgridTwo

/-- **h-drift (size), `2 ≤ n` version**: identical to `norm_DgridN_le`
(`Lemma514NonAlt.lean`) but with the hypothesis weakened from `3 ≤ n` to `2 ≤ n` — the
proof never uses `3 ≤ n` (see the module docstring); the `K`-loop `∑ lK ∈ Finset.Icc 3 n, …` is an
empty sum whenever `n < 3`, in particular at `n = 2`. -/
theorem norm_DgridN_le' {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ)
    (K : ℕ → ℕ) (N : ℕ) (σ : Fin n → Bool) (j : ℕ) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ}
    (hτ' : 0 < τ') (hD' : 0 ≤ D') (hΦ0 : 0 ≤ Φ) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N j < 1) (hA1 : 1 ≤ (band d).scale E N (time s t K N j))
    (hreg : KDecayRegime d N n τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) n ε₁ Λ Φ τ' D' ℓs)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(band d).Kval E N (time s t K N j) J‖
        ≤ CK * ((band d).scale E N (time s t K N j))⁻¹ ^ (J.length - 1))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m, 2 ≤ m → m ≤ n → xiLKM d E N (time s t K N j) (H d s t K N j ω) m ≤ B)
    (b : LoopArg (d.L N) n) :
    ‖DgridN d E s t K N σ j ω b‖ ≤ dDr514 d E N n (time s t K N j) ε₁ τ' D' Φ CK B := by
  set u := time s t K N j with hu
  set M := H d s t K N j ω with hM
  have hmem' := hmem
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩ := hmem
  obtain ⟨hdec, hlk⟩ := goodSet514_decay d E N u n ε₁ Λ Φ τ' D' ℓs hmem'
  have hNe : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set I : LoopIdx (ZMod (d.L N)) := ⟨List.ofFn σ, List.ofFn b⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hIlen : I.length = n := by simp [hI, LoopIdx.length]
  -- the three pieces
  have heG := norm_eGterm_le d hE N hu0 hu1 hτ' hA1 M hdec (Ξ1 := (N : ℝ) ^ ε₁)
    (Φ := (N : ℝ) ^ ε₁ * Φ) hNe (mul_nonneg hNe hΦ0) h5 h4 I hIwf hIlen
  have hprod : ∀ m, 2 ≤ m → m ≤ n →
      xiLKM d E N u M m * xiLKM d E N u M (n - m + 2) * ((band d).scale E N u)⁻¹
        ≤ (N : ℝ) ^ ε₁ * Φ := by
    intro m hm1 hm2
    have := h3 m hm1 hm2
    rwa [div_eq_mul_inv] at this
  have hpB := norm_primBil_le514 d hE N hu0 hu1 hτ' hA1 (n := n) (by omega) M hlk
    (Φ := (N : ℝ) ^ ε₁ * Φ) (mul_nonneg hNe hΦ0) hB0 hprod hB I hIwf hIlen
  have hcoup : ∀ lK ∈ Finset.Icc 3 n,
      ‖Decay.couplingLen (d.L N) (d.W N) lK ((band d).Kval E N u)
          (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J) I‖
        ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹
              * ((N : ℝ) ^ ε₁ * Φ) * ((band d).scale E N u)⁻¹ ^ n
          + 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D')
              * ((N : ℝ) ^ ε₁ * Φ) := by
    intro lK hlK
    rw [Finset.mem_Icc] at hlK
    have h := norm_KsimLK_le d hE N hu0 hu1 hτ' hD' hA1 hlK.1 hlK.2 hreg hCK0 hK M I hIwf hIlen
    have hX := h2 (n - lK + 2) (by omega) (by omega)
    have hX0 : 0 ≤ xiLKM d E N u M (n - lK + 2) :=
      xiLKM_nonneg d E N u (le_trans zero_le_one hA1) M _
    have hc1 : 0 ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ := by
      have := etaT_pos hE hu1
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
      positivity
    have hc2 : 0 ≤ ((band d).scale E N u)⁻¹ ^ n := by
      have : 0 ≤ (band d).scale E N u := le_trans zero_le_one hA1
      positivity
    have hc3 : 0 ≤ 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
      positivity
    refine h.trans ?_
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hc1) hc2
    have e2 := mul_le_mul_of_nonneg_left hX hc3
    linarith
  have hsum := (norm_sum_le (Finset.Icc 3 n) (fun lK => Decay.couplingLen (d.L N) (d.W N) lK
      (fun I => (band d).Kval E N u I)
      (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) I)).trans
    (Finset.sum_le_sum hcoup)
  have hsplit : DgridN d E s t K N σ j ω b
      = eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
        + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (d.L N) (d.W N) lK
            (fun I => (band d).Kval E N u I)
            (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) I)
        + primBil (d.L N) (d.W N)
            (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J)
            (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J) I := rfl
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  unfold dDr514
  have heG' : ‖eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I‖
      ≤ 4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * (N : ℝ) ^ ε₁
            * ((N : ℝ) ^ ε₁ * Φ) * ((band d).scale E N u)⁻¹ ^ n
        + (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁ := heG
  exact add_le_add (add_le_add heG' hsum) hpB

end DgridTwo

section AssemblyTwo

end AssemblyTwo

section EndpointTwo

end EndpointTwo

section EndpointTwoSubtype

end EndpointTwoSubtype

section WitnessTwo

end WitnessTwo

end RBM.Gauss.Grid

end

