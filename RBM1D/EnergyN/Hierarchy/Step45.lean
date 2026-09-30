/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step45
import RBM1D.EnergyN.Hierarchy.Step3

/-!
# Steps 4 and 5 of the proof of Theorem 2.21 at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.7.

## Main declarations

* `RBM.Step45.FlowEq548N` — the bound (5.48) for the flow, as a predicate.
* `RBM.Step45.flow_lkErr_le_ofN` — (2.78) from `Ξ^{(L-K)}_{u,n} ≺ 1`.
* `RBM.Step45.flow_sharpLmKN` — (2.78) for the flow (Step 4), through `RBM.Step3.hyp_flowN`
  (whose kernel constant is the uniform `RBM.Step3.exists_norm_Kval_le_unif`), the generic
  `RBM.Step45.xiLK_le_one_of_hyp`, and `flow_lkErr_le_ofN`.
* `RBM.Step45.flow_sharpDecayN` — (2.79) for the flow (Step 5), from (2.78) for `n = 2` and
  (5.48).
-/

namespace RBM

open MeasureTheory Filter

namespace Step45

open Step3

section FlowStep4N

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(2.78) from `Ξ^{(L-K)}_{u,n} ≺ 1`**, at an `N`-dependent energy: `max_{σ,a}
|L_{u,σ,a} - K_{u,σ,a}| ≺ (W ℓ_u η_u)^{-n}`, uniformly in `u ∈ [s,t]`. -/
theorem flow_lkErr_le_ofN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    {n : ℕ} (hX : StochDom B.P (fun N u ω => flowXiLK X (E N) s t n N u ω) fun _ _ _ => 1) :
    StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ n) := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < flowA B (E N) s t N u :=
    fun N u => flowA_pos (hE N) hs0 ht1 N u
  have hY := hX.precomp_param (fun N (p : TimeIcc s t N × LoopData (B.L N) n) => p.1)
  have hinv : ∀ N (p : TimeIcc s t N × LoopData (B.L N) n) (_ : Ω),
      0 ≤ (B.scale (E N) N p.1)⁻¹ ^ n := fun N p _ => pow_nonneg (inv_pos.2 (hA N p.1)).le _
  have hprod := StochDom.mul hinv (fun _ _ _ => zero_le_one) hY (StochDom.refl hinv)
  refine StochDom.of_le_left (fun N p ω => ?_)
    (Step3.stochDom_mono hinv 1 (Eventually.of_forall fun N p ω => by simp) hprod)
  have h1 := X.lkErr_le_lkMax (E := E N) (t := p.1) (ω := ω) p.2
  have hA' := hA N p.1
  simp only [Pi.mul_apply, flowXiLK, Sample.xiLK]
  refine h1.trans (le_of_eq ?_)
  unfold flowA at hA'
  rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hA'.ne', one_pow, mul_one]

/-- **(2.78) for the flow** (Step 4), at an `N`-dependent energy, for every `n ≥ 1`. The families
are eta-expanded at `E N`; the step condition is `Cond272N`. -/
theorem flow_sharpLmKN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (h514 : ∀ n, 2 ≤ n → Lemma514 B.P (fun n N u ω => flowXiLK X (E N) s t n N u ω)
      (fun n N u ω => flowXiL X (E N) s t n N u ω) (fun N u => flowA B (E N) s t N u) n)
    (h0 : ∀ m, 1 ≤ m → S B.P (fun n N u ω => flowXiLK X (E N) s t n N u ω)
      (fun N => flowAs B (E N) s N) (flowR B s t) (fun N u => flowA B (E N) s t N u) m 0)
    (h12 : ∀ m l, 1 ≤ m → m ≤ 2 →
      S B.P (fun n N u ω => flowXiLK X (E N) s t n N u ω) (fun N => flowAs B (E N) s N)
        (flowR B s t) (fun N u => flowA B (E N) s t N u) m l)
    (h1 : StochDom B.P (fun N u ω => flowXiLK X (E N) s t 1 N u ω) fun _ _ _ => 1)
    (h2 : StochDom B.P (fun N u ω => flowXiLK X (E N) s t 2 N u ω)
      fun N u _ => flowA B (E N) s t N u ^ ((1 : ℝ) / 4)) :
    ∀ n : ℕ, 1 ≤ n → StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) n) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ n) := by
  have hE : ∀ N, |E N| < 2 := fun N => by have := hEκ N; linarith
  have H := hyp_flowN X hκ0 hκ1 hEκ hs0 hst ht1 hc fun n hn => h514 n (by omega)
  intro n hn
  exact flow_lkErr_le_ofN X hE hs0 ht1
    (Step45.xiLK_le_one_of_hyp H h0 h12 (h514 2 le_rfl) h1 h2 n hn)

end FlowStep4N

section FlowStep5N

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(5.48)** for the flow, at an `N`-dependent energy, for every `D > 0`, uniformly in
`u ∈ [s,t]` and `a₁, a₂`. -/
def FlowEq548N {B : Band Ω} (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  Eq548 B.P
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
      X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
    (fun N => (B.W N : ℝ)) (fun N p => B.ell N p.1) (fun N p => etaT (E N) p.1)
    (fun N p => (zdist (B.L N) (p.2.1 - p.2.2) : ℝ))
    (fun N p => (etaT (E N) (s N) / etaT (E N) p.1) ^ 2)

variable {B : Band Ω} {X : Sample B}

variable (X) {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(2.79) for the flow** (Step 5), at an `N`-dependent energy: for `σ = (+,-)` and every
`D > 0`, `|L_{u,σ,a} - K_{u,σ,a}| ≺ (W ℓ_u η_u)^{-2} (exp(-(|a₁-a₂|/ℓ_u)^{1/2}) + W^{-D})`,
uniformly in `u ∈ [s,t]` and `a₁, a₂`. -/
theorem flow_sharpDecayN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h4 : StochDom B.P
      (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) ω => X.lkErr (E N) N p.1 ω p.2.idx)
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ 2))
    (h548 : FlowEq548N X E s t) :
    ∀ D : ℝ, 0 < D → StochDom B.P
      (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) ω =>
        X.lkErr (E N) N p.1 ω (pmLoop p.2.1 p.2.2))
      (fun N p _ => (B.scale (E N) N p.1)⁻¹ ^ 2 * B.decayProf N p.1 D p.2.1 p.2.2) := by
  have hu0 : ∀ N (u : TimeIcc s t N), (0 : ℝ) ≤ (u : ℝ) := fun N u => (hs0 N).trans u.2.1
  have hu1 : ∀ N (u : TimeIcc s t N), (u : ℝ) < 1 := fun N u => u.2.2.trans_lt (ht1 N)
  have h4' := h4.precomp_param
    (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) => (p.1, pmData p.2.1 p.2.2))
  refine decay_of_split (tendsto_atTop.2 fun b => B.eventually_le_W b) (eventually_W_le B)
    (fun N => by exact_mod_cast B.W_pos N)
    (fun N p => Step3.ellHat_pos_of_lt_one (by have := B.three_le_L N; omega) (hu1 N p.1))
    (fun N p => B.scale_pos' (hE N) N (hu0 N p.1) (hu1 N p.1)) ?_ h4' h548
  refine Eventually.of_forall fun N p => ?_
  have h := etaT_mul_ellHat_le (B.three_le_L N) (hE N).le (hu0 N p.1) (hu1 N p.1)
  have hW : (0 : ℝ) ≤ B.W N := Nat.cast_nonneg _
  have heq : (B.W N : ℝ) * B.ell N p.1 * etaT (E N) p.1
      = B.W N * (etaT (E N) p.1 * B.ell N p.1) := by ring
  rw [heq]
  exact mul_le_of_le_one_right hW h

end FlowStep5N

end Step45

end RBM
