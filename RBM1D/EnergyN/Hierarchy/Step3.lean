/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step3
import RBM1D.Flow.EnergyUniform
import RBM1D.EnergyN.Unif.Hierarchy.Step3

/-!
# Step 3 of the proof of Theorem 2.21 at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.6.

The inputs of Step 3 at an `N`-dependent energy `E : ℕ → ℝ`.

## The external `κ`

`RBM.Step3.flow_xiL_leN` takes its kernel constant `C` from
`RBM.Step3.exists_norm_Kval_le_unif` (`∃ C, 0 ≤ C ∧ ∀ E, |E| ≤ 2 - κ → …`), obtained once
before `N` and instantiated at `E N` via `hEκ N`.

## Main declarations

* `RBM.Step3.scales_flowN` — (2.72) gives the scale conditions of Step 3.
* `RBM.Step3.flow_xiL_le_ofN` — the first bound of (5.107), with `C` as a hypothesis.
* `RBM.Step3.flow_xiL_leN` — the same, with `C` fixed as above.
* `RBM.Step3.hyp_flowN` — the inputs of Step 3 for the flow.
-/

namespace RBM

open MeasureTheory Filter

namespace Step3

section FlowFamiliesN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}
variable {E : ℕ → ℝ} {s t : ℕ → ℝ}

/-- **(2.72) gives the scale conditions of Step 3** for `u ∈ [s,t]`, at an `N`-dependent
energy. -/
theorem scales_flowN (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N)
    (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) :
    Scales (fun N => flowAs B (E N) s N) (flowR B s t) (fun N u => flowA B (E N) s t N u) := by
  have hs1 : ∀ N, s N < 1 := fun N => (hst N).trans_lt (ht1 N)
  have hL : ∀ N, 1 ≤ B.L N := fun N => by have := B.three_le_L N; omega
  have hW : ∀ N, (0 : ℝ) < B.W N := fun N => by exact_mod_cast B.W_pos N
  have key : ∀ᶠ N : ℕ in atTop, ∀ u : TimeIcc s t N,
      1 ≤ flowAs B (E N) s N ∧ flowA B (E N) s t N u ≤ flowAs B (E N) s N ∧
        1 ≤ flowR B s t N ∧
        flowR B s t N ^ 2 * flowAs B (E N) s N ^ ((3 : ℝ) / 4) ≤ flowA B (E N) s t N u := by
    filter_upwards [hc] with N hN u
    exact scale_facts_of_cond272 (hW N) (hL N) (hE N) u.2.1 u.2.2 (ht1 N) hN
  refine ⟨fun N => B.scale_pos' (hE N) N (hs0 N) (hs1 N), fun N => ?_,
    fun N u => flowA_pos (hE N) hs0 ht1 N u, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (ellHat_pos_of_lt_one (hL N) (ht1 N)).le
      (ellHat_pos_of_lt_one (hL N) (hs1 N)).le
  · filter_upwards [key] with N hN
    exact (hN ⟨s N, le_rfl, hst N⟩).1
  · filter_upwards [key] with N hN
    exact (hN ⟨s N, le_rfl, hst N⟩).2.2.1
  · filter_upwards [key] with N hN u
    exact (hN u).2.1
  · filter_upwards [key] with N hN u
    exact (hN u).2.2.2

variable (X : Sample B)

/-- **(5.107) for the flow**, at an `N`-dependent energy, from a caller-supplied bound
`|K_{u,σ,a}| ≤ C (W ℓ_u η_u)^{-n+1}` (this is (2.59)): `Ξ^{(L)}_{u,n} ≺ 1 + (W ℓ_u η_u)^{-1}
Ξ^{(L-K)}_{u,n}`, uniformly in `u ∈ [s,t]`. No energy-dependent constant is fixed here: `C` is a
hypothesis. -/
theorem flow_xiL_le_ofN {C : ℝ} (hE : ∀ N, |E N| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n)
    (hC : ∀ N (u : TimeIcc s t N) (v : LoopData (B.L N) n),
      ‖B.Kval (E N) N u v.idx‖ ≤ C * (B.scale (E N) N u)⁻¹ ^ (n - 1)) :
    StochDom B.P (fun N u ω => flowXiL X (E N) s t n N u ω)
      fun N u ω => 1 + (flowA B (E N) s t N u)⁻¹ * flowXiLK X (E N) s t n N u ω := by
  have hA : ∀ N (u : TimeIcc s t N), 0 < flowA B (E N) s t N u :=
    fun N u => flowA_pos (hE N) hs0 ht1 N u
  have hζ : ∀ N u ω, 0 ≤ 1 + (flowA B (E N) s t N u)⁻¹ * flowXiLK X (E N) s t n N u ω :=
    fun N u ω => by
      have := (inv_pos.2 (hA N u)).le
      have := X.xiLK_nonneg (E := E N) (N := N) (t := u) (ω := ω) (m := n) (hA N u).le
      unfold flowXiLK; positivity
  refine StochDom.of_le_left (ξ' := fun N u ω =>
    max C 1 * (1 + (flowA B (E N) s t N u)⁻¹ * flowXiLK X (E N) s t n N u ω))
    (fun N u ω => ?_)
    (StochDom.const_mul_left (le_trans zero_le_one (le_max_right _ _)) hζ (StochDom.refl hζ))
  have h1 := X.xiL_le_add (ω := ω) (hA N u) hn (hC N u)
  have h2 : 0 ≤ (flowA B (E N) s t N u)⁻¹ * flowXiLK X (E N) s t n N u ω := by
    have := (inv_pos.2 (hA N u)).le
    have := X.xiLK_nonneg (E := E N) (N := N) (t := u) (ω := ω) (m := n) (hA N u).le
    unfold flowXiLK; positivity
  have h3 : C ≤ max C 1 := le_max_left _ _
  have h4 : 1 ≤ max C 1 := le_max_right _ _
  unfold flowXiL
  unfold flowXiLK flowA at h2
  unfold flowXiLK flowA
  nlinarith

/-- **(5.107) for the flow** (`n ≥ 3`), at an `N`-dependent energy, from (2.59). The kernel
constant is the uniform one of `RBM.Step3.exists_norm_Kval_le_unif`. -/
theorem flow_xiL_leN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1) {n : ℕ} (hn : 1 ≤ n) :
    StochDom B.P (fun N u ω => flowXiL X (E N) s t n N u ω)
      fun N u ω => 1 + (flowA B (E N) s t N u)⁻¹ * flowXiLK X (E N) s t n N u ω := by
  obtain ⟨C, -, hC⟩ := exists_norm_Kval_le_unif (B := B) (s := s) (t := t) hκ0 hκ1 hs0 ht1 hn
  exact flow_xiL_le_ofN X (fun N => by have := hEκ N; linarith) hs0 ht1 hn
    (fun N u v => hC (E N) (hEκ N) N u v)

/-- **The inputs of Step 3 for the flow**, at an `N`-dependent energy. The families are
eta-expanded at `E N`; the step condition is `Cond272N`. -/
theorem hyp_flowN {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ)
    (hs0 : ∀ N, 0 ≤ s N) (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t)
    (h514 : ∀ n, 3 ≤ n → Lemma514 B.P (fun n N u ω => flowXiLK X (E N) s t n N u ω)
      (fun n N u ω => flowXiL X (E N) s t n N u ω) (fun N u => flowA B (E N) s t N u) n) :
    Hyp B.P (fun n N u ω => flowXiLK X (E N) s t n N u ω)
      (fun n N u ω => flowXiL X (E N) s t n N u ω) (fun N => flowAs B (E N) s N) (flowR B s t)
      (fun N u => flowA B (E N) s t N u) := by
  have hE : ∀ N, |E N| < 2 := fun N => by have := hEκ N; linarith
  have hA : ∀ N (u : TimeIcc s t N), 0 < flowA B (E N) s t N u :=
    fun N u => flowA_pos (hE N) hs0 ht1 N u
  exact
    { scales := scales_flowN hE hs0 hst ht1 hc
      X_nonneg := fun n N u ω => X.xiLK_nonneg (hA N u).le
      Y_nonneg := fun n N u ω => X.xiL_nonneg (hA N u).le
      xiL_le := fun n hn => flow_xiL_leN X hκ0 hκ1 hEκ hs0 ht1 (by omega)
      xiL_split := fun n l₁ l₂ h₁ h₂ hl N u ω =>
        loopXi_le (X.hermitian N u ω) (hA N u).le h₁ h₂ hl
      lemma514 := h514 }

end FlowFamiliesN

end Step3

end RBM
