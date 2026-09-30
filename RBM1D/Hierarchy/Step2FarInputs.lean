/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step2MomentStep
import RBM1D.Hierarchy.DriftDef

/-!
# The far field of (5.48): the `J` bridge at the `(+,-)` `2`-loop, and `Ξ ≺ 1`

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.3, (5.29), (5.30), (5.35), (5.48) and §7, (7.2).

(5.35) takes its `J` through bounds on the `G`-loop `RBM.gloop` — that is, on `L` itself.  The
sharp bound `J* ≺ (η_s/η_u)²` (the remark after (5.47)) is a statement about `RBM.Step2.jS`,
i.e. about `J*` of `L - K`.  The gap is exactly a far-field bound on `K`:

`|K_{u,(+,-),(x,y)}| ≤ T_{u,D}(‖x - y‖)`  for  `‖x - y‖ ≥ ℓ*_u/2`.

At loop length `2` this needs **no** tree representation: `σ = (+,-)` gives `m(+)m(-) = 1`
(`RBM.Step2FarInputs.mSigma_true_mul_false`), so Example 2.15 reads
`K_{u,(+,-),(x,y)} = W^{-1}(Θ_u)_{xy}` (`RBM.Step2FarInputs.Kval_pm_eq`), and Lemma 5.6/(5.30)
(`RBM.Step2.norm_Theta_le_of_ellStar`) gives `|(Θ_u)_{xy}| ≤ W^{-D} ≤ T_{u,D}` at distance
`≥ δ ℓ*_u`.  `RBM.Band.norm_Kval_le` at `n = 2` only gives `A^{-1}`, which is far too big, and
`RBM.Decay.norm_Kgen_le_exp` requires `3 ≤ n`; the `n = 2` decay of `K` is the decay of `Θ`,
which is (2.52)/(5.30).

With that, `‖L_{u,(+,-),(x,y)}‖ ≤ (J*-1)T + T = J* T` (`norm_gloop_pm_le_jS_mul_tT`); the `-1`
comes from `J* = max_a |A_a|/T + 1` (5.29), so the bridge is **exact**, with no constant lost.

## Main results

* `RBM.Step2FarInputs.mSigma_true_mul_false`, `RBM.Step2FarInputs.Kval_pm_eq`,
  `RBM.Step2FarInputs.norm_Kval_pm_le_norm_Theta` — `K` at the `(+,-)` `2`-loop is `W^{-1}Θ_u`.
* `RBM.Step2FarInputs.norm_lk_le_jS_sub_one_mul`, `RBM.Step2FarInputs.norm_gloop_pm_le_jS_mul_tT`
  — the `J` bridge.
* `RBM.Step2FarInputs.eventually_xiK_le` — `Ξ ≺ 1`: the kernel constant of (7.2) is `N^{o(1)}`.
* `RBM.Step2FarInputs.cFar_le_cFar_one`, `RBM.Step2FarInputs.cNear_le_cNear_one` — the far- and
  near-field constants of (5.35) are largest at `ℓ_u = 1`, so their supremum over `u` is
  `u`-free.
-/

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 1. The concrete one-step data -/

section Pinned

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

variable (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

end Pinned

/-! ### 2. One step of (5.21) in the far field, with the length of `[s,v]` kept -/

section FarStep

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s : ℕ → ℝ}

end FarStep

/-! ### 3. The one-step inputs, with no free tensor -/

section Inputs

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Inputs

/-! ### 4. `Ξ ≺ 1`

`Ξ = RBM.Step2.xiK` is `N^{o(1)}` unconditionally on the band. -/

section Poly

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`Ξ ≺ 1`.**  The kernel constant of (7.2),
`Ξ = C(1 + 2L e^{-(log W)^{3/2}/8}) + (Im m)^{-2} + e^{(log W)^{3/4}}`, is `N^{o(1)}`: the
middle term is a constant, the first is `≤ 2C` once `L ≤ W²` and `W ≥ e^{400}`, and the last
is `≤ W^{τ/2} ≤ N^{τ/2}`.  Nothing about the flow enters — only `W L ≤ N` and (2.2). -/
theorem eventually_xiK_le (B : Band Ω) (m : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in Filter.atTop, Step2.xiK (B.L N) (B.W N) m ≤ (N : ℝ) ^ τ := by
  have hτ2 : 0 < τ / 2 := by linarith
  filter_upwards [B.dim, Step2.eventually_le_W_sq B,
    (Step2.tendsto_W B).eventually_ge_atTop (exp 400),
    (Step2.tendsto_W B).eventually (eventually_exp_mul_log_rpow_le 1 hτ2),
    eventually_le_rpow (2 * cTail + (m ^ 2)⁻¹) hτ2, eventually_le_rpow 2 hτ2,
    Filter.eventually_ge_atTop 1] with
    N hdim hW2 hWe hWexp hC hC2 hN1
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hW1 : (1 : ℝ) ≤ B.W N := by exact_mod_cast B.W_pos N
  have hW0 : (0 : ℝ) < B.W N := by linarith
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdim.1
  have hL1 : (1 : ℝ) ≤ B.L N := by exact_mod_cast (by omega : 1 ≤ B.L N)
  have hLN : (B.L N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hWN : (B.W N : ℝ) ≤ (N : ℝ) := by nlinarith
  have hLW : (B.L N : ℝ) ≤ (B.W N : ℝ) ^ 2 := hLN.trans hW2
  have hexpL : 2 * (B.L N : ℝ) * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8)) ≤ 1 := by
    have := Step2.two_mul_sq_mul_exp_le hWe
    have h0 := exp_pos (-(log (B.W N : ℝ) ^ (3 / 2 : ℝ) / 8))
    nlinarith
  have hct := cTail_nonneg
  have h1 : cTail * (1 + 2 * (B.L N : ℝ) * exp (-(log (B.W N) ^ (3 / 2 : ℝ) / 8)))
      ≤ 2 * cTail := by nlinarith
  have h2 : exp (log (B.W N : ℝ) ^ (3 / 4 : ℝ)) ≤ (N : ℝ) ^ (τ / 2) := by
    have h := hWexp
    rw [one_mul] at h
    exact h.trans (Real.rpow_le_rpow hW0.le hWN hτ2.le)
  have hsplit : (N : ℝ) ^ (τ / 2) * (N : ℝ) ^ (τ / 2) = (N : ℝ) ^ τ := by
    rw [← Real.rpow_add hN0]; ring_nf
  have h3 : (1 : ℝ) ≤ (N : ℝ) ^ (τ / 2) := Real.one_le_rpow hN hτ2.le
  have h4 : 2 * (N : ℝ) ^ (τ / 2) ≤ (N : ℝ) ^ τ := by nlinarith [hsplit, hC2, h3]
  unfold Step2.xiK
  linarith

end Poly

/-! ### 4b. (5.48) end to end -/

section EndToEnd

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end EndToEnd

/-! ### 5. The two drift inputs, produced from (5.35) and (5.34) -/

section Produce

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Produce

/-! ### 6. Satisfiability -/

section Sat

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Sat

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 7. (5.35), shape 2, split into `M_gn` (near) and `M_gf` (far) -/

section Shape

end Shape

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 7b. (5.35) itself, folded into one right-hand side -/

section Link

variable {L W : ℕ} [NeZero L] [NeZero W]
  {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ} {z : ℂ}

end Link

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 8. The exponent account of `M_gf (1-s)` -/

section Account

end Account

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 9. The account on the flow, and the `u`-free far-field constant -/

section Flow

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- **`c_far(W,ℓ) ≤ c_far(W,1)` for `ℓ ≥ 1`.**  The only `ℓ`-dependence of
`RBM.Lemma57.cFar` is the summand `8/ℓ`, so the supremum over `u` is at `ℓ_u = 1`. -/
theorem cFar_le_cFar_one {Wr ℓu : ℝ} (hW : 1 ≤ Wr) (hℓu : 1 ≤ ℓu) :
    Lemma57.cFar Wr ℓu ≤ Lemma57.cFar Wr 1 := by
  have hlog : (0:ℝ) ≤ log Wr := Real.log_nonneg hW
  have hloss : (0:ℝ) < Lemma57.loss32 Wr := Lemma57.loss32_pos Wr
  have hℓ0 : (0:ℝ) < ℓu := by linarith
  have h8 : (8:ℝ) / ℓu ≤ 8 / 1 := by
    rw [div_one, div_le_iff₀ hℓ0]; nlinarith
  have h34 : (0:ℝ) ≤ 4 * log Wr ^ (3 / 2 : ℝ) := by positivity
  unfold Lemma57.cFar
  nlinarith

/-- **`c_near(W,ℓ) ≤ c_near(W,1)` for `ℓ ≥ 1`.**  As for `RBM.Lemma57.cFar`, the only
`ℓ`-dependence is the summand `2/ℓ`. -/
theorem cNear_le_cNear_one {Wr ℓu : ℝ} (hW : 1 ≤ Wr) (hℓu : 1 ≤ ℓu) :
    Lemma57.cNear Wr ℓu ≤ Lemma57.cNear Wr 1 := by
  have hlog : (0:ℝ) ≤ log Wr := Real.log_nonneg hW
  have hexp : (0:ℝ) < exp (log Wr ^ (3 / 4 : ℝ)) := exp_pos _
  have hℓ0 : (0:ℝ) < ℓu := by linarith
  have h2 : (2:ℝ) / ℓu ≤ 2 / 1 := by
    rw [div_one, div_le_iff₀ hℓ0]; nlinarith
  have h3 : (0:ℝ) ≤ 2 * log Wr ^ (3 : ℝ) := by positivity
  unfold Lemma57.cNear
  nlinarith

end Flow

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 10. The two drift constants, produced from (5.35) -/

section Produce535

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Produce535

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 11. The one-step inputs with the `E^{(G̃)}` half of the drift produced -/

section Assemble

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Assemble

/-! ### 12. The produced constants are non-degenerate -/

section NonDegenerate

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

end NonDegenerate

/-! ### 13. (5.48) end to end, with the `E^{(G̃)}` half of the drift produced -/

section EndToEnd535

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end EndToEnd535

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 14. The constants are not vacuously zero -/

section NonVacuous

end NonVacuous

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 15. The far-field bridge: `K` at the `(+,-)` `2`-loop -/

section KBridge

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} {E : ℝ} {s t : ℕ → ℝ}

/-- `m(+) m(-) = m^{(E)} \overline{m^{(E)}} = |m^{(E)}|² = 1` for `|E| ≤ 2`
(`RBM.norm_mE`).  This is the `ξ = 1` of `RBM.xiOf_mSigma_true_false`, read off the product
rather than the edge parameters. -/
theorem mSigma_true_mul_false {E : ℝ} (hE : |E| ≤ 2) :
    mSigma E true * mSigma E false = 1 := by
  have h : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj', norm_mE hE]; simp
  simpa [mSigma] using h

/-- **`K` at the `(+,-)` `2`-loop is `W^{-1}Θ_u`.**  Example 2.15 (2.57) reads
`K_{t,σ,(x,y)} = W^{-1} m(σ₁)m(σ₂) (Θ_{t m(σ₁)m(σ₂)})_{xy}`; at `σ = (+,-)` the factor is `1`,
so the whole `n = 2` decay of `K` **is** the decay of `Θ`. -/
theorem Kval_pm_eq {E : ℝ} (hE : |E| ≤ 2) (B : Band Ω) (N : ℕ) (u : ℝ)
    (x y : ZMod (B.L N)) :
    B.Kval E N u ⟨[true, false], [x, y]⟩
      = ((B.W N : ℂ))⁻¹ * Theta (B.L N) ((u : ℝ) : ℂ) x y := by
  show Kgen (B.L N) (B.W N) (mSigma E) u ⟨[true, false], [x, y]⟩ = _
  rw [Kgen_two, kTwo, mSigma_true_mul_false hE]
  ring_nf

/-- `‖K_{u,(+,-),(x,y)}‖ ≤ ‖(Θ_u)_{xy}‖`, since `W ≥ 1`. -/
theorem norm_Kval_pm_le_norm_Theta {E : ℝ} (hE : |E| ≤ 2) (B : Band Ω) (N : ℕ) (u : ℝ)
    (x y : ZMod (B.L N)) :
    ‖B.Kval E N u ⟨[true, false], [x, y]⟩‖ ≤ ‖Theta (B.L N) ((u : ℝ) : ℂ) x y‖ := by
  have hW1 : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
  rw [Kval_pm_eq hE, norm_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  exact inv_le_one_of_one_le₀ hW1

end KBridge

/-! ### 16. The `G`-loop bounds of (5.35) with `J := J*_{u,D}` -/

section JBridge

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-- **(5.29) read off its definition**: `J*_{u,D} = max_a |(L-K)_a| / T_{u,D} + 1`, so the
*sharp* pointwise bound is with `J* - 1`, not `J*`.  This one unit is what pays for `K` in
`RBM.Step2FarInputs.norm_gloop_pm_le_jS_mul_tT`, so the bridge costs nothing. -/
theorem norm_lk_le_jS_sub_one_mul (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (a : LoopArg (B.L N) 2) :
    ‖Step2.lk X E N u ω a‖
      ≤ (Step2.jS X E D N u ω - 1) * Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) := by
  have hW0 : (0 : ℝ) < (B.W N : ℝ) := by
    have : (1 : ℝ) ≤ (B.W N : ℝ) := by exact_mod_cast B.W_pos N
    linarith
  show ‖Step2.lk X E N u ω a‖ ≤ (Step2.jS X E D N u ω - 1)
    * tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (a 0 - a 1))
  have hT : (0 : ℝ) < tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D
      (zdist (B.L N) (a 0 - a 1)) := tailT_pos hW0 _
  have hsup := Finset.le_sup' (f := fun b : LoopArg (B.L N) 2 =>
      ‖Step2.lk X E N u ω b‖
        / tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (b 0 - b 1)))
    (Finset.mem_univ a)
  have heq : Step2.jS X E D N u ω - 1
      = Finset.univ.sup' Finset.univ_nonempty (fun b : LoopArg (B.L N) 2 =>
          ‖Step2.lk X E N u ω b‖
            / tailT (B.W N : ℝ) (B.ell N u) (etaT E u) D (zdist (B.L N) (b 0 - b 1))) := by
    show Step2.jStar (B.L N) (fun b => ‖Step2.lk X E N u ω b‖) (B.W N) (B.ell N u)
        (etaT E u) D - 1 = _
    rw [Step2.jStar]; ring
  rw [heq, ← div_le_iff₀ hT]
  exact hsup

/-- **The `J` bridge, sharp form.**  In the far field, where `|K| ≤ T_{u,D}`,
`|L_{u,(+,-),(x,y)}| ≤ J*_{u,D} T_{u,D}(‖x-y‖)` — with `J*` itself, not a multiple of it:
`(J*-1)T` for `L-K` plus `T` for `K`. -/
theorem norm_gloop_pm_le_jS_mul_tT (X : Sample B) (E D : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (x y : ZMod (B.L N))
    (hK : ‖B.Kval E N u ⟨[true, false], [x, y]⟩‖
      ≤ Step2.tT B E N D u (zdist (B.L N) (x - y))) :
    ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[true, false], [x, y]⟩‖
      ≤ Step2.jS X E D N u ω * Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
  have hlk : ‖Step2.lk X E N u ω ![x, y]‖
      ≤ (Step2.jS X E D N u ω - 1) * Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
    have h := norm_lk_le_jS_sub_one_mul X E D N u ω ![x, y]
    simpa using h
  have hsplit : gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) ⟨[true, false], [x, y]⟩
      = Step2.lk X E N u ω ![x, y] + B.Kval E N u ⟨[true, false], [x, y]⟩ := by
    show _ = (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u) - B.Kval E N u)
        ⟨[true, false], [x, y]⟩ + _
    simp
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have := add_le_add hlk hK
  linarith [this]

end JBridge

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 17. (5.35) with `J` instantiated by `J*_{u,D}` — the acceptance of the bridge -/

section Instantiate

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Instantiate

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 18. (5.34): the quadratic gluing term, and `M_qf (1-s) ≺ 1` -/

section Quad

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

/-! #### The exponent account, as two pure inequalities -/

end Quad

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 19. (5.34) with `J := J*_{u,D'}`: the two quadratic inputs -/

section QuadProduce

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end QuadProduce

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 20. `M_f (1-s) ≺ 1` with **both** halves proved, and (5.48) end to end -/

section Assemble535534

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Assemble535534

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 21. Satisfiability, vacuity and degeneracy checks for §15–§20

`RBM.Step2Moment.one_le_jS` gives `J*_{u,D} ≥ 1` unconditionally, so a bound
`J*_{u,D} ≤ N^δ (η_s/η_u)²` is never met by a degenerate zero and is a *critical* request. -/

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 22. The data of (5.35) with `J := RBM.Step2.jS` and both quadratic constants produced -/

section EGDataJS

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end EGDataJS

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 23. The account's hypothesis set is satisfiable, and its (2.72) input is load-bearing -/

end Step2FarInputs
end RBM

namespace RBM
namespace Step2FarInputs

open Real Filter MeasureTheory

/-! ### 24. (5.48) with the `D'`-threshold that (5.34)'s `W L W^{-D'}` floor needs -/

section Threshold

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω} (X : Sample B) {E : ℝ} {s t : ℕ → ℝ}

end Threshold

end Step2FarInputs
end RBM
