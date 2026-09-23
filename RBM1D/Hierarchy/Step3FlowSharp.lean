/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step3

/-!
# The concrete sharp-loop conclusions of Step 3

This module isolates the two actual flow producers for (2.77) from the elementary interfaces
and deterministic induction retained in `RBM1D.Hierarchy.Step3`.
-/

namespace RBM

open MeasureTheory Filter

namespace Step3

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

section FlowFamilies

variable {E : ℝ} {s t : ℕ → ℝ}

variable (X : Sample B)

/-- **(2.77) for the flow, in the shape of `RBM.Steps.sharpLoop`**, at a length `n` for which
(5.107) is available: `max_{σ,a} |L_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n+1}` uniformly in `u ∈ [s,t]`.
Inputs: `|E| ≤ 2 - κ`, `0 < s ≤ t < 1`, (2.72), Lemma 5.14 (5.92), `S(m,0)` for `m ≥ 1` (from
(2.73), (3.46)) and `S(m,l)` for `m ≤ 2` (from (2.75), (2.76)). -/
theorem flow_sharpLoop_of {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (h514 : ∀ n, 3 ≤ n → Lemma514 B.P (flowXiLK X E s t) (flowXiL X E s t) (flowA B E s t) n)
    (h0 : ∀ m, 1 ≤ m → S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 →
      S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m l)
    {n : ℕ} (hn : 1 ≤ n)
    (h107 : StochDom B.P (flowXiL X E s t n)
      fun N u ω => 1 + (flowA B E s t N u)⁻¹ * flowXiLK X E s t n N u ω) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  have hE : |E| < 2 := by linarith
  have hA := flowA_pos (B := B) hE hs0 ht1
  have H := hyp_flow X hκ0 hκ1 hEκ hs0 hst ht1 hc h514
  have hY := (xiL_le_one_of H h0 h12 hn h107).precomp_param
    (fun N (p : TimeIcc s t N × LoopData (B.L N) n) => p.1)
  have hinv : ∀ N (p : TimeIcc s t N × LoopData (B.L N) n) (_ : Ω),
      0 ≤ (B.scale E N p.1)⁻¹ ^ (n - 1) := fun N p _ => pow_nonneg (inv_pos.2 (hA N p.1)).le _
  have hprod := StochDom.mul hinv (fun _ _ _ => zero_le_one) hY (StochDom.refl hinv)
  refine StochDom.of_le_left (fun N p ω => ?_)
    (stochDom_mono hinv 1 (Eventually.of_forall fun N p ω => by simp) hprod)
  have h1 := X.norm_Lval_le_loopMax (E := E) (t := p.1) (ω := ω) p.2
  have hA' := hA N p.1
  simp only [Pi.mul_apply, flowXiL, Sample.xiL, loopXi]
  refine h1.trans (le_of_eq ?_)
  unfold flowA at hA'
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hA'.ne', one_pow, mul_one]

/-- **(2.77) for the flow** (`n = 1` and `n ≥ 3`), in the shape of `RBM.Steps.sharpLoop`.
(`n = 2` needs (5.107) at `n = 2`, i.e. `|K_{u,σ,a}| ≤ C (W ℓ_u η_u)^{-1}` for `2`-loops,
which is not used anywhere in the induction and not proved here.) -/
theorem flow_sharpLoop {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : |E| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272 B E s t)
    (h514 : ∀ n, 3 ≤ n → Lemma514 B.P (flowXiLK X E s t) (flowXiL X E s t) (flowA B E s t) n)
    (h0 : ∀ m, 1 ≤ m → S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 →
      S B.P (flowXiLK X E s t) (flowAs B E s) (flowR B s t) (flowA B E s t) m l)
    {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => ‖X.Lval E N p.1 ω p.2.idx‖)
      (fun N p _ => (B.scale E N p.1)⁻¹ ^ (n - 1)) := by
  exact flow_sharpLoop_of X hκ0 hκ1 hEκ hs0 hst ht1 hc h514 h0 h12 hn
    (flow_xiL_le X hκ0 hκ1 hEκ hs0 ht1 hn)

end FlowFamilies

end Step3

end RBM
