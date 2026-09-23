/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.StochDomMono
import RBM1D.Flow.FlowFamiliesCore

/-!
# The clean `Ξᴸ` conversion core

This file isolates the loopwise-to-`Ξᴸ` conversion and the a priori estimate (2.73) below the
Step 3 hierarchy.
-/

namespace RBM

open MeasureTheory Filter

namespace Step2PP

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-! ### From a loopwise bound to `Ξ^{(L)}` -/

/-- **From a loopwise bound to `Ξ^{(L)}`.**  If `|L_{u,σ,a}| ≺ f_u` uniformly in `u ∈ [s,t]`
and in the loop `(σ,a)` of length `m`, then `Ξ^{(L)}_{u,m} ≺ f_u (W ℓ_u η_u)^{m-1}`.  This is
the `Ξ^{(L)}` companion of `RBM.StepGlue.stochDom_flowXiLK`. -/
theorem stochDom_flowXiL (X : Sample B) {m : ℕ} {f : ∀ N, TimeIcc s t N → ℝ}
    (hA : ∀ N (u : TimeIcc s t N), 0 ≤ B.scale E N u)
    (h : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) m) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => f N p.1)) :
    StochDom B.P (Step3.flowXiL X E s t m)
      (fun N u _ => f N u * B.scale E N u ^ (m - 1)) := by
  refine StochDom.of_subset_union h h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun N => ?_⟩
  rintro ω ⟨u, hu⟩
  by_cases h' : ∃ p : TimeIcc s t N × LoopData (B.L N) m,
      (N : ℝ) ^ τ * f N p.1 < ‖X.Lval E N p.1 ω p.2.idx‖
  · exact Or.inl h'
  · exfalso
    have hall : ∀ v : LoopData (B.L N) m, ‖X.Lval E N u ω v.idx‖ ≤ (N : ℝ) ^ τ * f N u :=
      fun v => not_lt.1 fun hc => h' ⟨(u, v), hc⟩
    have hmax : loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) m ≤ (N : ℝ) ^ τ * f N u :=
      ciSup_le hall
    have hApow : (0 : ℝ) ≤ B.scale E N u ^ (m - 1) := pow_nonneg (hA N u) _
    have : Step3.flowXiL X E s t m N u ω ≤ (N : ℝ) ^ τ * (f N u * B.scale E N u ^ (m - 1)) := by
      show loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) m * B.scale E N u ^ (m - 1) ≤ _
      calc loopMax (B.L N) (B.W N) (X.H N u ω) (zt E u) m * B.scale E N u ^ (m - 1)
          ≤ ((N : ℝ) ^ τ * f N u) * B.scale E N u ^ (m - 1) :=
            mul_le_mul_of_nonneg_right hmax hApow
        _ = (N : ℝ) ^ τ * (f N u * B.scale E N u ^ (m - 1)) := by ring
    exact absurd hu (not_lt.2 this)

/-! ### The a priori inputs of (5.83) at `n = 2` -/

/-- **(2.73) in the form `Ξ^{(L)}_{u,m} ≺ (ℓ_t/ℓ_s)^{m-1}`**, for every `m ≥ 1`, uniformly in
`u ∈ [s,t]`.  This is `RBM.Steps.apriori` read through `RBM.Step2PP.stochDom_flowXiL`; note that
(2.73) is a bound on `max_{σ,a}`, so **all** charges are covered. -/
theorem flow_xiL_apriori_le' (X : Sample B) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hapriori : AprioriFlow X E s t) {m : ℕ}
    (hm : 1 ≤ m) :
    StochDom B.P (Step3.flowXiL X E s t m)
      (fun N (_ : TimeIcc s t N) (_ : Ω) => Step3.flowR B s t N ^ (m - 1)) := by
  have hL : ∀ N, 1 ≤ B.L N := fun N => by have := B.three_le_L N; omega
  have hA : ∀ N (u : TimeIcc s t N), 0 < B.scale E N u := fun N u =>
    B.scale_pos' hE N ((hs0 N).trans u.2.1) (u.2.2.trans_lt (ht1 N))
  have hR0 : ∀ N, (0 : ℝ) ≤ Step3.flowR B s t N := fun N =>
    div_nonneg (Step3.ellHat_pos_of_lt_one (hL N) (ht1 N)).le
      (Step3.ellHat_pos_of_lt_one (hL N) ((hst N).trans_lt (ht1 N))).le
  have hXi := stochDom_flowXiL X (f := fun N (u : TimeIcc s t N) =>
    (B.ell N u / B.ell N (s N)) ^ (m - 1) * (B.scale E N u)⁻¹ ^ (m - 1))
    (fun N u => (hA N u).le) (hapriori m hm)
  refine Step3.stochDom_mono (fun N _ _ => pow_nonneg (hR0 N) _) 1
    (Eventually.of_forall fun N u _ => ?_) hXi
  have hA0 : 0 < B.scale E N u := hA N u
  have hℓs : 0 < B.ell N (s N) :=
    Step3.ellHat_pos_of_lt_one (hL N) ((hst N).trans_lt (ht1 N))
  have hℓu : B.ell N u ≤ B.ell N (t N) := Step3.ellHat_mono u.2.2 (ht1 N)
  have hr0 : (0 : ℝ) ≤ B.ell N u / B.ell N (s N) := by
    have := (Step3.ellHat_pos_of_lt_one (L := B.L N) (hL N) (u.2.2.trans_lt (ht1 N))).le
    positivity
  have hkey : (B.ell N u / B.ell N (s N)) ^ (m - 1) * (B.scale E N u)⁻¹ ^ (m - 1) *
      B.scale E N u ^ (m - 1) = (B.ell N u / B.ell N (s N)) ^ (m - 1) := by
    rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hA0.ne'), mul_one]
  rw [hkey, one_mul]
  exact pow_le_pow_left₀ hr0 (div_le_div_of_nonneg_right hℓu hℓs.le) _

end Step2PP

end RBM
