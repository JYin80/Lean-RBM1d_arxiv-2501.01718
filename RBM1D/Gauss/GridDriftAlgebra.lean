/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EGDef
import RBM1D.Propagator.Deriv
import RBM1D.Gauss.GridDriftLip
import RBM1D.Gauss.GridPath
import RBM1D.Gauss.GridLoopStep

/-!
# T1506 — the discrete drift algebra, (5.19)/(5.20) on the grid

Formalization support for `docs/supervisor/2026-09-25-2045.md` §2 (d): the bridge between
`RBM.Gauss.MomentDuhamel`-style one-loop conditional-expectation facts and the discrete stopped
Duhamel formula of §5.3, at the `σ = (+,-)` `2`-loop.

## Main results

* `RBM.Gauss.Grid.loopDrift_sub_K_deriv` (T1) : the pointwise drift-minus-`K` identity, (5.19)
  applied to the `l_K = 2` coupling.
* `RBM.Gauss.Grid.K_step` (T2) : the exact (not merely bounded) second-order remainder of the
  primitive `K`'s own time-derivative step, via the resolvent identity for `Theta`.
* `RBM.Gauss.Grid.Uker_step` (T3) : the exact quadratic remainder of the evolution kernel's
  one-step linearization, at `n = 2` (the scope of this ticket).
* `RBM.Gauss.Grid.discrete_hierarchy_step` (T4) : the combination with T1503 (T4)
  `RBM.Gauss.Grid.condExp_loop_drift`, with the explicit deterministic error `stepErr`
  (`O(Δ^{3/2} + Δ²)`), and `discrete_hierarchy_step_unif`, the same with a bound
  `C₁(δ) Δ² + C₂(δ) Δ^{3/2}` uniform in the grid index on `u_{k+1} ≤ 1 - δ`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Matrix Finset
open scoped Matrix.Norms.Operator

/-! ### Notation: `L_u(M)` and `K_u` on the `LoopArg` side, at `σ = (+,-)` -/

section Notation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`L_u(M)`**: the vector of `2`-loops `a ↦ gloop ... M (zt E u) ⟨[true,false],[a₁,a₂]⟩`. -/
def Lval (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (M : Matrix (B.Idx N) (B.Idx N) ℂ)
    (a : LoopArg (B.L N) 2) : ℂ :=
  gloop (B.L N) (B.W N) M (zt E u) ⟨[true, false], List.ofFn a⟩

/-- **`K_u`** on the same labels. -/
def Kv (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (B.L N) 2) : ℂ :=
  B.Kval E N u ⟨[true, false], List.ofFn a⟩

end Notation

/-! ### (T1) : the pointwise drift-minus-`K` identity -/

section T1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(T1)**: pointwise, for Hermitian `M` and the `σ = (+,-)` `2`-loop, `loopDrift − primRhs(K_u)`
splits into the `Θ`-part (5.19), the `E^{(G̃)}`-part, and the quadratic gluing part (5.13). -/
theorem loopDrift_sub_K_deriv (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) (hz : (zt E u).im ≠ 0)
    (hxi2 : ‖(u : ℂ) * (mSigma E false * mSigma E true)‖ < 1) (a : LoopArg (B.L N) 2) :
    loopDrift (d := B.toDims) (N := N) E u ⟨[true, false], List.ofFn a⟩ M
        - primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨[true, false], List.ofFn a⟩
      = ThetaOp (B.L N) (xiOf (mSigma E) ![true, false]) (u : ℂ)
            (fun v => Lval B E N u M v - Kv B E N u v) a
          + eGterm (B.L N) (B.W N) (mSigma E) M (zt E u) ⟨[true, false], List.ofFn a⟩
          + primBil (B.L N) (B.W N)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
              ⟨[true, false], List.ofFn a⟩ := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hwf : (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))).WF := rfl
  have hlen : (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))).length = 2 := rfl
  have hK : ∀ σ₁ σ₂ (a₁ a₂ : ZMod (B.L N)),
      B.Kval E N u ⟨[σ₁, σ₂], [a₁, a₂]⟩
        = kTwo (B.L N) (B.W N) (mSigma E) u σ₁ σ₂ a₁ a₂ := by
    intro σ₁ σ₂ a₁ a₂; rw [Band.Kval, Kgen_two]
  have hxiL : xiLoop (mSigma E) (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      (2 - 1) = mSigma E false * mSigma E true := by
    simp [xiLoop, LoopIdx.length]
  have hxi : ‖(u : ℂ) * xiLoop (mSigma E)
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) (2 - 1)‖ < 1 := by
    rw [hxiL]; exact hxi2
  have hcoup := couplingLen_two_eq_thetaGenLoop (L := B.L N) (B.W N) (mSigma E) u
    (B.Kval E N u) (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) hL3 hK
    (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) hwf (by rw [hlen]) hxi
  have hsplit := EGDef.couplingLen_two_of_len_two (B.L N) (B.W N) (B.Kval E N u)
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
    (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) hlen
  have hps := primRhs_sub (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u)) (B.Kval E N u)
    (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
  have hbridge := thetaGenLoop_ofFn (mSigma E) u
    (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u) [true, false] a
  rw [thetaGenOp_eq_ThetaOp] at hbridge
  have hxiEq : (fun i : Fin 2 => mSigma E (([true, false] : List Bool).getD (i : ℕ) true)
        * mSigma E (([true, false] : List Bool).getD (((i : ℕ) + 1) % 2) true))
      = xiOf (mSigma E) ![true, false] := by
    funext i; fin_cases i <;> rfl
  rw [hxiEq] at hbridge
  have hFunEq : (fun v => Lval B E N u M v - Kv B E N u v)
      = (fun v : LoopArg (B.L N) 2 =>
          (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (⟨[true, false], List.ofFn v⟩ : LoopIdx (ZMod (B.L N)))) := rfl
  rw [← hFunEq] at hbridge
  show eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      + primRhs (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u))
          (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      - primRhs (B.L N) (B.W N) (B.Kval E N u)
          (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      = ThetaOp (B.L N) (xiOf (mSigma E) ![true, false]) (u : ℂ)
            (fun v => Lval B E N u M v - Kv B E N u v) a
        + eGterm (B.L N) (B.W N) (mSigma E) M (zt E u)
            (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
  have hgoal : primRhs (B.L N) (B.W N) (gloop (B.L N) (B.W N) M (zt E u))
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      - primRhs (B.L N) (B.W N) (B.Kval E N u)
          (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      = ThetaOp (B.L N) (xiOf (mSigma E) ![true, false]) (u : ℂ)
            (fun v => Lval B E N u M v - Kv B E N u v) a
        + primBil (B.L N) (B.W N)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (gloop (B.L N) (B.W N) M (zt E u) - B.Kval E N u)
            (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) := by
    rw [← hbridge, ← hcoup, hsplit]
    linear_combination hps
  linear_combination hgoal

end T1

/-! ### (T2) : the exact remainder of `K`'s own time-step -/

section T2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The matrix-level identity behind (T2): a product of three `Theta`s, written as an iterated
sum, matches the two nested sums that `primRhs_two` produces. -/
private theorem theta_SB_theta_entry {L : ℕ} [NeZero L] (ξ ζ : ℂ) (x y : ZMod L) :
    (Theta L ξ * SB L * Theta L ζ) x y
      = ∑ p : ZMod L, ∑ q : ZMod L, Theta L ξ x p * SB L p q * Theta L ζ q y := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **(T2)**: `K_{u'} - K_u - (u'-u) · primRhs(K_u)` is *exactly* (no approximation)
`(u'-u)² · μ³/W · (Theta(u'μ)·SB·Theta(uμ)·SB·Theta(uμ))`, `μ := m(σ₁)m(σ₂)`, via the resolvent
identity `Theta_sub_Theta` applied twice. `errK` is the explicit bound on that matrix entry. -/
theorem K_step (B : Band Ω) (E : ℝ) (N : ℕ) (s1 s2 : Bool) (a₁ a₂ : ZMod (B.L N))
    {u u' : ℝ} (hu0 : 0 ≤ u) (huu' : u ≤ u')
    (hxi : ‖(u' : ℂ) * (mSigma E s1 * mSigma E s2)‖ < 1) :
    ‖B.Kval E N u' ⟨[s1, s2], [a₁, a₂]⟩ - B.Kval E N u ⟨[s1, s2], [a₁, a₂]⟩
        - ((u' - u : ℝ) : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨[s1, s2], [a₁, a₂]⟩‖
      ≤ ‖mSigma E s1 * mSigma E s2‖ ^ 3 / (B.W N : ℝ)
          * (1 - u' * ‖mSigma E s1 * mSigma E s2‖)⁻¹
          * (1 - u * ‖mSigma E s1 * mSigma E s2‖)⁻¹ ^ 2
          * (u' - u) ^ 2 := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  set μ : ℂ := mSigma E s1 * mSigma E s2 with hμdef
  have hu'0 : 0 ≤ u' := hu0.trans huu'
  have hcastnorm : ∀ v : ℝ, 0 ≤ v → ‖(v : ℂ) * μ‖ = v * ‖μ‖ := by
    intro v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  have hu'norm : ‖(u' : ℂ) * μ‖ = u' * ‖μ‖ := hcastnorm u' hu'0
  have hunorm : ‖(u : ℂ) * μ‖ = u * ‖μ‖ := hcastnorm u hu0
  have hu'lt : u' * ‖μ‖ < 1 := hu'norm ▸ hxi
  have hult : u * ‖μ‖ < 1 := by
    have hmono : u * ‖μ‖ ≤ u' * ‖μ‖ := mul_le_mul_of_nonneg_right huu' (norm_nonneg _)
    linarith
  have hult' : ‖(u : ℂ) * μ‖ < 1 := hunorm ▸ hult
  have hu'lt' : ‖(u' : ℂ) * μ‖ < 1 := hxi
  have hKform : ∀ v : ℝ, B.Kval E N v ⟨[s1, s2], [a₁, a₂]⟩
      = (B.W N : ℂ)⁻¹ * μ * Theta (B.L N) ((v : ℂ) * μ) a₁ a₂ := by
    intro v; rw [Band.Kval, Kgen_two, kTwo]
  have hKformXY : ∀ v : ℝ, ∀ x y : ZMod (B.L N), B.Kval E N v ⟨[s1, s2], [x, y]⟩
      = (B.W N : ℂ)⁻¹ * μ * Theta (B.L N) ((v : ℂ) * μ) x y := by
    intro v x y; rw [Band.Kval, Kgen_two, kTwo]
  have hPR : primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨[s1, s2], [a₁, a₂]⟩
      = μ ^ 2 * (B.W N : ℂ)⁻¹
          * (Theta (B.L N) ((u : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂ := by
    have hentry := theta_SB_theta_entry (L := B.L N) ((u : ℂ) * μ) ((u : ℂ) * μ) a₁ a₂
    rw [primRhs_two, hentry]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hKformXY u a₁ p, hKformXY u q a₂]
    have hW0 : (B.W N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (B.W N))
    field_simp
  have hTsub1 : Theta (B.L N) ((u' : ℂ) * μ) - Theta (B.L N) ((u : ℂ) * μ)
      = (((u' : ℂ) * μ) - ((u : ℂ) * μ)) •
          (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) :=
    Theta_sub_Theta (B.L N) hL3 hult' hu'lt'
  have hΔμ : ((u' : ℂ) * μ) - ((u : ℂ) * μ) = ((u' - u : ℝ) : ℂ) * μ := by push_cast; ring
  have hKdiff : B.Kval E N u' ⟨[s1, s2], [a₁, a₂]⟩ - B.Kval E N u ⟨[s1, s2], [a₁, a₂]⟩
      = (B.W N : ℂ)⁻¹ * μ * (((u' - u : ℝ) : ℂ) * μ)
          * (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂ := by
    rw [hKform u', hKform u, ← mul_sub]
    have := congrFun (congrFun hTsub1 a₁) a₂
    rw [Matrix.sub_apply, Matrix.smul_apply, hΔμ, smul_eq_mul] at this
    rw [show Theta (B.L N) ((u' : ℂ) * μ) a₁ a₂ - Theta (B.L N) ((u : ℂ) * μ) a₁ a₂
        = ((u' - u : ℝ) : ℂ) * μ
          * (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂
      from this]
    ring
  have hTdiffSB : (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ))
      - (Theta (B.L N) ((u : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ))
      = (((u' - u : ℝ) : ℂ) * μ) •
          (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
            * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) := by
    rw [← sub_mul, ← sub_mul, hTsub1, hΔμ, Matrix.smul_mul, Matrix.smul_mul]
  have hPQentry := congrFun (congrFun hTdiffSB a₁) a₂
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPQentry
  have hexact : B.Kval E N u' ⟨[s1, s2], [a₁, a₂]⟩ - B.Kval E N u ⟨[s1, s2], [a₁, a₂]⟩
      - ((u' - u : ℝ) : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N u) ⟨[s1, s2], [a₁, a₂]⟩
      = ((u' - u : ℝ) : ℂ) ^ 2 * μ ^ 3 * (B.W N : ℂ)⁻¹
          * (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
              * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂ := by
    rw [hKdiff, hPR]
    linear_combination ((B.W N : ℂ)⁻¹ * μ ^ 2 * ((u' - u : ℝ) : ℂ)) * hPQentry
  have hW0 : (B.W N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (B.W N))
  have hW0' : (0 : ℝ) < B.W N := by positivity
  have hRbound : ‖(Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
        * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂‖
      ≤ (1 - u' * ‖μ‖)⁻¹ * (1 - u * ‖μ‖)⁻¹ ^ 2 := by
    have hentry_le_op : ∀ M : Matrix (ZMod (B.L N)) (ZMod (B.L N)) ℂ, ‖M a₁ a₂‖ ≤ ‖M‖ :=
      fun M => (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => norm_nonneg (M a₁ i))
          (Finset.mem_univ a₂)).trans (sum_norm_row_le (B.L N) M a₁)
    have hT1 : ‖Theta (B.L N) ((u' : ℂ) * μ)‖ ≤ (1 - u' * ‖μ‖)⁻¹ := by
      have h := norm_Theta_le (B.L N) hL3 hu'lt'
      rwa [hu'norm] at h
    have hT2 : ‖Theta (B.L N) ((u : ℂ) * μ)‖ ≤ (1 - u * ‖μ‖)⁻¹ := by
      have h := norm_Theta_le (B.L N) hL3 hult'
      rwa [hunorm] at h
    have hSB1 : ‖SB (B.L N)‖ = 1 := norm_SB (B.L N) hL3
    have hSB1' : ‖SB (B.L N)‖ ≤ 1 := hSB1.le
    have hnn1 : (0 : ℝ) ≤ (1 - u' * ‖μ‖)⁻¹ := by positivity
    have hnn2 : (0 : ℝ) ≤ (1 - u * ‖μ‖)⁻¹ := by positivity
    calc ‖(Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
              * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂‖
        ≤ ‖Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
              * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)‖ :=
          hentry_le_op _
      _ ≤ ‖Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
              * SB (B.L N)‖ * ‖Theta (B.L N) ((u : ℂ) * μ)‖ := norm_mul_le _ _
      _ ≤ (‖Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)‖
              * ‖SB (B.L N)‖) * ‖Theta (B.L N) ((u : ℂ) * μ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ((‖Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N)‖ * ‖Theta (B.L N) ((u : ℂ) * μ)‖)
              * ‖SB (B.L N)‖) * ‖Theta (B.L N) ((u : ℂ) * μ)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _)
      _ ≤ (((‖Theta (B.L N) ((u' : ℂ) * μ)‖ * ‖SB (B.L N)‖) * ‖Theta (B.L N) ((u : ℂ) * μ)‖)
              * ‖SB (B.L N)‖) * ‖Theta (B.L N) ((u : ℂ) * μ)‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)) (norm_nonneg _))
            (norm_nonneg _)
      _ ≤ (((1 - u' * ‖μ‖)⁻¹ * 1) * (1 - u * ‖μ‖)⁻¹) * 1 * (1 - u * ‖μ‖)⁻¹ := by
          gcongr <;> first | exact hT1 | exact hT2 | exact hSB1'
      _ = (1 - u' * ‖μ‖)⁻¹ * (1 - u * ‖μ‖)⁻¹ ^ 2 := by ring
  rw [hexact]
  have hnorm_eq : ‖((u' - u : ℝ) : ℂ) ^ 2 * μ ^ 3 * (B.W N : ℂ)⁻¹
        * (Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
            * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂‖
      = (u' - u) ^ 2 * ‖μ‖ ^ 3 * (B.W N : ℝ)⁻¹
          * ‖(Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
              * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    have h1 : ‖((u' - u : ℝ) : ℂ)‖ = u' - u := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ u' - u)]
    have h2 : ‖((B.W N : ℂ))⁻¹‖ = (B.W N : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    rw [h1, h2]
  rw [hnorm_eq]
  have hfin : (u' - u) ^ 2 * ‖μ‖ ^ 3 * (B.W N : ℝ)⁻¹
        * ‖(Theta (B.L N) ((u' : ℂ) * μ) * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)
            * SB (B.L N) * Theta (B.L N) ((u : ℂ) * μ)) a₁ a₂‖
      ≤ (u' - u) ^ 2 * ‖μ‖ ^ 3 * (B.W N : ℝ)⁻¹
          * ((1 - u' * ‖μ‖)⁻¹ * (1 - u * ‖μ‖)⁻¹ ^ 2) := by
    gcongr
  refine hfin.trans (le_of_eq ?_)
  ring

end T2

/-! ### (T3) : the one-step linearization of the evolution kernel, at `n = 2` -/

section T3

/-- Splitting a sum over `LoopArg L 2 = Fin 2 → ZMod L` into a double sum, generalized to any
`AddCommMonoid` codomain (the `ℝ`-valued instance of this fact is
`RBM.sum_fin_two_fun`, `Hierarchy/KernelDecay.lean:1746`). -/
private theorem sum_LoopArg_two {L : ℕ} [NeZero L] {β : Type*} [AddCommMonoid β]
    (F : ZMod L → ZMod L → β) :
    ∑ b : LoopArg L 2, F (b 0) (b 1) = ∑ x : ZMod L, ∑ y : ZMod L, F x y := by
  rw [← (piFinTwoEquiv fun _ : Fin 2 => ZMod L).symm.sum_comp, Fintype.sum_prod_type]
  simp

/-- The row-sum bound for the edge kernel `ξ • (SB · Theta(tξ))` (the same as
`SumZeroDyn.genSM`, up to `Theta_commute_SB`, but re-derived here to avoid the extra import). -/
private theorem row_bound_edge {L : ℕ} [NeZero L] (hL : 3 ≤ L) {ξ t : ℂ} (ht : ‖t * ξ‖ < 1)
    (x : ZMod L) :
    ∑ c : ZMod L, ‖ξ * (SB L * Theta L (t * ξ)) x c‖ ≤ ‖ξ‖ * (1 - ‖t * ξ‖)⁻¹ := by
  simp_rw [fun c => norm_mul ξ ((SB L * Theta L (t * ξ)) x c)]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le L _ x).trans ?_) (norm_nonneg _)
  calc ‖SB L * Theta L (t * ξ)‖ ≤ ‖SB L‖ * ‖Theta L (t * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta L (t * ξ)‖ := by rw [norm_SB L hL, one_mul]
    _ ≤ (1 - ‖t * ξ‖)⁻¹ := norm_Theta_le L hL ht

/-- **(T3)**: the one-step linearization of the evolution kernel, restricted to `n = 2` (the
ticket's own scope: `L_u(M)` and `K_u` are `2`-loops, so `Uker`/`ThetaOp` are only ever needed at
`n = 2` here). The base point of the linear term is `u_j` (the ticket's stated form), which costs
one extra exact application of `Theta_sub_Theta` beyond the exact quadratic remainder that
`edgeKer_eq` alone produces at the endpoint `u_j + Δ`. -/
theorem Uker_step {L : ℕ} [NeZero L] (hL : 3 ≤ L) (ξ : Fin 2 → ℂ) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {u Δ : ℝ} (hu0 : 0 ≤ u) (hΔ0 : 0 ≤ Δ) (hut1 : u + Δ < 1)
    {A : LoopArg L 2 → ℂ} {M : ℝ} (hM0 : 0 ≤ M) (hA : ∀ b, ‖A b‖ ≤ M) (a : LoopArg L 2) :
    ‖Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) A a - A a - (Δ : ℂ) * ThetaOp L ξ (u : ℂ) A a‖
      ≤ 3 * (1 - (u + Δ))⁻¹ ^ 2 * Δ ^ 2 * M := by
  have hu1 : u < 1 := by linarith
  have hξt : ∀ i, ‖((u + Δ : ℝ) : ℂ) * ξ i‖ < 1 := by
    intro i
    calc ‖((u + Δ : ℝ) : ℂ) * ξ i‖ = (u + Δ) * ‖ξ i‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ (u + Δ) * 1 := mul_le_mul_of_nonneg_left (hξ i) (by linarith)
      _ = u + Δ := mul_one _
      _ < 1 := hut1
  have hξu : ∀ i, ‖(u : ℂ) * ξ i‖ < 1 := by
    intro i
    calc ‖(u : ℂ) * ξ i‖ = u * ‖ξ i‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      _ ≤ u * 1 := mul_le_mul_of_nonneg_left (hξ i) hu0
      _ = u := mul_one _
      _ < 1 := hu1
  set P : Fin 2 → ZMod L → ZMod L → ℂ :=
    fun i x y => ξ i * (SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ i)) x y with hPdef
  have hedge : ∀ (i : Fin 2) (x y : ZMod L),
      edgeKer L (ξ i) (u : ℂ) ((u + Δ : ℝ) : ℂ) x y
        = (1 : Matrix (ZMod L) (ZMod L) ℂ) x y + (Δ : ℂ) * P i x y := by
    intro i x y
    have h := congrFun (congrFun
      (edgeKer_eq L hL (ξ := ξ i) (s := (u : ℂ)) (t := ((u + Δ : ℝ) : ℂ)) (hξt i)) x) y
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h, hPdef]
    have hcast : (u : ℂ) - ((u + Δ : ℝ) : ℂ) = -((Δ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    ring
  have hUkerEq : Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) A a
      = ∑ x : ZMod L, ∑ y : ZMod L,
          edgeKer L (ξ 0) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 0) x
            * edgeKer L (ξ 1) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 1) y * A (![x, y]) := by
    rw [Uker_apply]
    rw [← sum_LoopArg_two (fun x y => edgeKer L (ξ 0) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 0) x
      * edgeKer L (ξ 1) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 1) y * A (![x, y]))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fin.prod_univ_two]
    have hAeq : A b = A ![b 0, b 1] := by
      congr 1; funext i; fin_cases i <;> rfl
    rw [hAeq]
  have hstep : ∀ x y : ZMod L,
      edgeKer L (ξ 0) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 0) x
          * edgeKer L (ξ 1) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 1) y
        = (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y
          + (Δ : ℂ) * ((1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * P 1 (a 1) y
              + P 0 (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y)
          + (Δ : ℂ) ^ 2 * (P 0 (a 0) x * P 1 (a 1) y) := by
    intro x y; rw [hedge 0 (a 0) x, hedge 1 (a 1) y]; ring
  have haeq : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  have hcollapse1 : ∑ x : ZMod L, ∑ y : ZMod L,
      (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y
        * A (![x, y]) = A a := by
    have hinner : ∀ x : ZMod L, ∑ y : ZMod L,
        (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y
          * A (![x, y])
        = (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * A (![x, a 1]) := by
      intro x
      have hy : ∀ y : ZMod L,
          (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y
              * A (![x, y])
            = (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x
              * (if a 1 = y then A (![x, y]) else 0) := by
        intro y
        simp only [Matrix.one_apply]
        split_ifs with h <;> ring
      simp_rw [hy]
      rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ (a 1) (fun y => A (![x, y]))]
      simp
    simp_rw [hinner]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (a 0) (fun x => A ![x, a 1])]
    simp [← haeq]
  have hcollapse2 : ∑ x : ZMod L, ∑ y : ZMod L,
      (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * P 1 (a 1) y * A (![x, y])
        = ∑ y : ZMod L, P 1 (a 1) y * A (![a 0, y]) := by
    have hfactor : ∀ x : ZMod L, ∑ y : ZMod L,
        (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * P 1 (a 1) y * A (![x, y])
        = (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * ∑ y : ZMod L, P 1 (a 1) y * A (![x, y]) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    simp_rw [hfactor]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (a 0) (fun x => ∑ y : ZMod L, P 1 (a 1) y * A (![x, y]))]
    simp
  have hcollapse3 : ∑ x : ZMod L, ∑ y : ZMod L,
      P 0 (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y * A (![x, y])
        = ∑ x : ZMod L, P 0 (a 0) x * A (![x, a 1]) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    have hfactor : ∑ y : ZMod L, P 0 (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y
          * A (![x, y])
        = P 0 (a 0) x * ∑ y : ZMod L,
            (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y * A (![x, y]) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hfactor]
    simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ (a 1) (fun y => A (![x, y]))]
    simp
  have hUkerExpand : Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) A a
      = A a + (Δ : ℂ) * ((∑ y : ZMod L, P 1 (a 1) y * A (![a 0, y]))
          + (∑ x : ZMod L, P 0 (a 0) x * A (![x, a 1])))
        + (Δ : ℂ) ^ 2 * (∑ x : ZMod L, ∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])) := by
    rw [hUkerEq]
    have hexpand : ∀ x y : ZMod L,
        edgeKer L (ξ 0) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 0) x
            * edgeKer L (ξ 1) (u : ℂ) ((u + Δ : ℝ) : ℂ) (a 1) y * A (![x, y])
          = (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y
              * A (![x, y])
            + (Δ : ℂ) * ((1 : Matrix (ZMod L) (ZMod L) ℂ) (a 0) x * P 1 (a 1) y * A (![x, y]))
            + (Δ : ℂ) * (P 0 (a 0) x * (1 : Matrix (ZMod L) (ZMod L) ℂ) (a 1) y * A (![x, y]))
            + (Δ : ℂ) ^ 2 * (P 0 (a 0) x * P 1 (a 1) y * A (![x, y])) := by
      intro x y; rw [hstep x y]; ring
    simp_rw [hexpand]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcollapse1, hcollapse2, hcollapse3]
    ring
  have hThetaEq : ThetaOp L ξ ((u + Δ : ℝ) : ℂ) A a
      = (∑ y : ZMod L, P 1 (a 1) y * A (![a 0, y]))
        + (∑ x : ZMod L, P 0 (a 0) x * A (![x, a 1])) := by
    have hcomm : ∀ (i : Fin 2) (x y : ZMod L), P i x y
        = ξ i * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L) x y := by
      intro i x y
      have hm : SB L * Theta L (((u + Δ : ℝ) : ℂ) * ξ i)
          = Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L :=
        (Theta_commute_SB L hL (hξt i)).eq.symm
      rw [hPdef]
      simp only
      rw [hm]
    show (∑ i : Fin 2, ∑ c : ZMod L,
        ξ i * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L) (a i) c * A (Function.update a i c))
        = _
    rw [Fin.sum_univ_two]
    have hupd0 : ∀ c : ZMod L, Function.update a 0 c = ![c, a 1] := by
      intro c; funext i; fin_cases i <;> rfl
    have hupd1 : ∀ c : ZMod L, Function.update a 1 c = ![a 0, c] := by
      intro c; funext i; fin_cases i <;> rfl
    simp_rw [← hcomm, hupd0, hupd1]
    rw [add_comm]
  have hThetaEqU : ThetaOp L ξ (u : ℂ) A a
      = (∑ y : ZMod L, ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y * A (![a 0, y]))
        + (∑ x : ZMod L, ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x * A (![x, a 1])) := by
    have hcomm : ∀ (i : Fin 2) (x y : ZMod L),
        ξ i * (SB L * Theta L ((u : ℂ) * ξ i)) x y
          = ξ i * (Theta L ((u : ℂ) * ξ i) * SB L) x y := by
      intro i x y
      have hm : SB L * Theta L ((u : ℂ) * ξ i) = Theta L ((u : ℂ) * ξ i) * SB L :=
        (Theta_commute_SB L hL (hξu i)).eq.symm
      rw [hm]
    show (∑ i : Fin 2, ∑ c : ZMod L,
        ξ i * (Theta L ((u : ℂ) * ξ i) * SB L) (a i) c * A (Function.update a i c))
        = _
    rw [Fin.sum_univ_two]
    have hupd0 : ∀ c : ZMod L, Function.update a 0 c = ![c, a 1] := by
      intro c; funext i; fin_cases i <;> rfl
    have hupd1 : ∀ c : ZMod L, Function.update a 1 c = ![a 0, c] := by
      intro c; funext i; fin_cases i <;> rfl
    simp_rw [← hcomm, hupd0, hupd1]
    rw [add_comm]
  have hβpos : (0 : ℝ) < 1 - (u + Δ) := by linarith
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
  have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
  have hTuΔ_le : ∀ i : Fin 2, ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ i)‖ ≤ β := by
    intro i
    have h := norm_Theta_le L hL (hξt i)
    refine h.trans (inv_anti₀ hβpos ?_)
    calc (1 : ℝ) - (u + Δ) ≤ 1 - (u + Δ) * ‖ξ i‖ := by nlinarith [hξ i, hΔ0, hu0]
      _ = 1 - ‖((u + Δ : ℝ) : ℂ) * ξ i‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + Δ)]
  have hTu_le : ∀ i : Fin 2, ‖Theta L ((u : ℂ) * ξ i)‖ ≤ β := by
    intro i
    have h := norm_Theta_le L hL (hξu i)
    refine h.trans (inv_anti₀ hβpos ?_)
    calc (1 : ℝ) - (u + Δ) ≤ 1 - u * ‖ξ i‖ := by nlinarith [hξ i, hΔ0, hu0]
      _ = 1 - ‖(u : ℂ) * ξ i‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  have hSB_le1 : ‖SB L‖ ≤ 1 := (norm_SB L hL).le
  have hrow_P : ∀ i : Fin 2, ∀ x : ZMod L, ∑ c : ZMod L, ‖P i x c‖ ≤ β := by
    intro i x
    rw [hPdef]
    refine (row_bound_edge hL (hξt i) x).trans ?_
    calc ‖ξ i‖ * (1 - ‖((u + Δ : ℝ) : ℂ) * ξ i‖)⁻¹ ≤ 1 * β := by
          refine mul_le_mul (hξ i) ?_
            (inv_nonneg.mpr (by linarith [hξt i])) zero_le_one
          refine inv_anti₀ hβpos ?_
          calc (1 : ℝ) - (u + Δ) ≤ 1 - (u + Δ) * ‖ξ i‖ := by nlinarith [hξ i, hΔ0, hu0]
            _ = 1 - ‖((u + Δ : ℝ) : ℂ) * ξ i‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith : (0 : ℝ) ≤ u + Δ)]
      _ = β := one_mul β
  have hrow_diff : ∀ i : Fin 2, ∀ x : ZMod L,
      ∑ c : ZMod L, ‖P i x c - ξ i * (SB L * Theta L ((u : ℂ) * ξ i)) x c‖ ≤ Δ * β ^ 2 := by
    intro i x
    have hentry : ∀ c : ZMod L, P i x c - ξ i * (SB L * Theta L ((u : ℂ) * ξ i)) x c
        = ξ i * (SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) - Theta L ((u : ℂ) * ξ i))) x c := by
      intro c
      rw [hPdef]
      simp only [Matrix.mul_sub, Matrix.sub_apply]
      ring
    have hTsub := Theta_sub_Theta L hL (ξ := (u : ℂ) * ξ i) (ζ := ((u + Δ : ℝ) : ℂ) * ξ i)
      (hξu i) (hξt i)
    have hcast : ((u + Δ : ℝ) : ℂ) * ξ i - (u : ℂ) * ξ i = ((Δ : ℝ) : ℂ) * ξ i := by
      push_cast; ring
    rw [hcast] at hTsub
    have hentry2 : ∀ c : ZMod L, P i x c - ξ i * (SB L * Theta L ((u : ℂ) * ξ i)) x c
        = (((Δ : ℝ) : ℂ) * ξ i ^ 2) *
            (SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i))) x c := by
      intro c
      rw [hentry c, hTsub, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
      ring
    have hnormeq : ∀ c : ZMod L,
        ‖P i x c - ξ i * (SB L * Theta L ((u : ℂ) * ξ i)) x c‖
          = Δ * ‖ξ i‖ ^ 2 * ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L
              * Theta L ((u : ℂ) * ξ i))) x c‖ := by
      intro c
      rw [hentry2 c, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hΔ0, norm_pow]
    simp_rw [hnormeq]
    rw [← Finset.mul_sum]
    have hop : ‖SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i))‖
        ≤ β ^ 2 := by
      calc ‖SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i))‖
          ≤ ‖SB L‖ * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i)‖ :=
            norm_mul_le _ _
        _ ≤ 1 * ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i)‖ :=
            mul_le_mul_of_nonneg_right hSB_le1 (norm_nonneg _)
        _ = ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i)‖ := one_mul _
        _ ≤ ‖Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L‖ * ‖Theta L ((u : ℂ) * ξ i)‖ :=
            norm_mul_le _ _
        _ ≤ (‖Theta L (((u + Δ : ℝ) : ℂ) * ξ i)‖ * ‖SB L‖) * ‖Theta L ((u : ℂ) * ξ i)‖ :=
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (β * 1) * β := by
            gcongr
            · exact hTuΔ_le i
            · exact hTu_le i
        _ = β ^ 2 := by ring
    have hrowsum : ∑ c : ZMod L,
        ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i))) x c‖
          ≤ β ^ 2 :=
      (sum_norm_row_le L _ x).trans hop
    have hξi2 : ‖ξ i‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖ξ i‖ := norm_nonneg _
      nlinarith [hξ i]
    calc Δ * ‖ξ i‖ ^ 2 * ∑ c : ZMod L,
          ‖(SB L * (Theta L (((u + Δ : ℝ) : ℂ) * ξ i) * SB L * Theta L ((u : ℂ) * ξ i))) x c‖
        ≤ Δ * ‖ξ i‖ ^ 2 * β ^ 2 := by gcongr
      _ ≤ Δ * 1 * β ^ 2 := by gcongr
      _ = Δ * β ^ 2 := by ring
  have hRem_bound : ‖∑ x : ZMod L, ∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])‖
      ≤ β ^ 2 * M := by
    have hstep : ∀ x : ZMod L, ‖∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])‖
        ≤ ‖P 0 (a 0) x‖ * (β * M) := by
      intro x
      calc ‖∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])‖
          ≤ ∑ y : ZMod L, ‖P 0 (a 0) x * P 1 (a 1) y * A (![x, y])‖ := norm_sum_le _ _
        _ = ∑ y : ZMod L, ‖P 0 (a 0) x‖ * (‖P 1 (a 1) y‖ * ‖A (![x, y])‖) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [norm_mul, norm_mul, mul_assoc]
        _ = ‖P 0 (a 0) x‖ * ∑ y : ZMod L, ‖P 1 (a 1) y‖ * ‖A (![x, y])‖ := by
            rw [Finset.mul_sum]
        _ ≤ ‖P 0 (a 0) x‖ * ∑ y : ZMod L, ‖P 1 (a 1) y‖ * M := by
            gcongr with y
            exact hA _
        _ = ‖P 0 (a 0) x‖ * ((∑ y : ZMod L, ‖P 1 (a 1) y‖) * M) := by rw [Finset.sum_mul]
        _ ≤ ‖P 0 (a 0) x‖ * (β * M) := by
            gcongr
            exact hrow_P 1 (a 1)
    calc ‖∑ x : ZMod L, ∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])‖
        ≤ ∑ x : ZMod L, ‖∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])‖ := norm_sum_le _ _
      _ ≤ ∑ x : ZMod L, ‖P 0 (a 0) x‖ * (β * M) := Finset.sum_le_sum fun x _ => hstep x
      _ = (∑ x : ZMod L, ‖P 0 (a 0) x‖) * (β * M) := by rw [Finset.sum_mul]
      _ ≤ β * (β * M) := by
          gcongr
          exact hrow_P 0 (a 0)
      _ = β ^ 2 * M := by ring
  have hS2diff : ‖(∑ y : ZMod L, P 1 (a 1) y * A (![a 0, y]))
        - (∑ y : ZMod L, ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y * A (![a 0, y]))‖
      ≤ Δ * β ^ 2 * M := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    calc ‖∑ y : ZMod L,
          (P 1 (a 1) y - ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y) * A (![a 0, y])‖
        ≤ ∑ y : ZMod L,
            ‖(P 1 (a 1) y - ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y) * A (![a 0, y])‖ :=
          norm_sum_le _ _
      _ = ∑ y : ZMod L,
            ‖P 1 (a 1) y - ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y‖ * ‖A (![a 0, y])‖ :=
          Finset.sum_congr rfl fun y _ => by rw [norm_mul]
      _ ≤ ∑ y : ZMod L,
            ‖P 1 (a 1) y - ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y‖ * M := by
          gcongr with y
          exact hA _
      _ = (∑ y : ZMod L,
            ‖P 1 (a 1) y - ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y‖) * M := by
          rw [Finset.sum_mul]
      _ ≤ (Δ * β ^ 2) * M := by
          gcongr
          exact hrow_diff 1 (a 1)
      _ = Δ * β ^ 2 * M := by ring
  have hS3diff : ‖(∑ x : ZMod L, P 0 (a 0) x * A (![x, a 1]))
        - (∑ x : ZMod L, ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x * A (![x, a 1]))‖
      ≤ Δ * β ^ 2 * M := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    calc ‖∑ x : ZMod L,
          (P 0 (a 0) x - ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x) * A (![x, a 1])‖
        ≤ ∑ x : ZMod L,
            ‖(P 0 (a 0) x - ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x) * A (![x, a 1])‖ :=
          norm_sum_le _ _
      _ = ∑ x : ZMod L,
            ‖P 0 (a 0) x - ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x‖ * ‖A (![x, a 1])‖ :=
          Finset.sum_congr rfl fun x _ => by rw [norm_mul]
      _ ≤ ∑ x : ZMod L,
            ‖P 0 (a 0) x - ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x‖ * M := by
          gcongr with x
          exact hA _
      _ = (∑ x : ZMod L,
            ‖P 0 (a 0) x - ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x‖) * M := by
          rw [Finset.sum_mul]
      _ ≤ (Δ * β ^ 2) * M := by
          gcongr
          exact hrow_diff 0 (a 0)
      _ = Δ * β ^ 2 * M := by ring
  have hmain : Uker L ξ (u : ℂ) ((u + Δ : ℝ) : ℂ) A a - A a - (Δ : ℂ) * ThetaOp L ξ (u : ℂ) A a
      = (Δ : ℂ) * (((∑ y : ZMod L, P 1 (a 1) y * A (![a 0, y]))
              - (∑ y : ZMod L, ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y * A (![a 0, y])))
            + ((∑ x : ZMod L, P 0 (a 0) x * A (![x, a 1]))
              - (∑ x : ZMod L, ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x * A (![x, a 1]))))
        + (Δ : ℂ) ^ 2
          * (∑ x : ZMod L, ∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y])) := by
    rw [hUkerExpand, hThetaEqU]
    ring
  rw [hmain]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(Δ : ℂ) * (((∑ y : ZMod L, P 1 (a 1) y * A (![a 0, y]))
              - (∑ y : ZMod L, ξ 1 * (SB L * Theta L ((u : ℂ) * ξ 1)) (a 1) y * A (![a 0, y])))
            + ((∑ x : ZMod L, P 0 (a 0) x * A (![x, a 1]))
              - (∑ x : ZMod L, ξ 0 * (SB L * Theta L ((u : ℂ) * ξ 0)) (a 0) x
                  * A (![x, a 1]))))‖
      ≤ Δ * (Δ * β ^ 2 * M + Δ * β ^ 2 * M) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ0]
    gcongr
    exact (norm_add_le _ _).trans (add_le_add hS2diff hS3diff)
  have h2 : ‖(Δ : ℂ) ^ 2
        * (∑ x : ZMod L, ∑ y : ZMod L, P 0 (a 0) x * P 1 (a 1) y * A (![x, y]))‖
      ≤ Δ ^ 2 * (β ^ 2 * M) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ0]
    gcongr
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [hβdef]; ring

end T3


/-! ### (T4) : deterministic auxiliary bounds (`ℓ^∞` operator norm scope) -/

section T4Aux

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- `List.ofFn` on `Fin 2`. -/
theorem ofFn_two' {α : Type*} (a : Fin 2 → α) : List.ofFn a = [a 0, a 1] := by
  simp [List.ofFn_succ]

/-- **Deterministic sup bound for `K_u`** on the `σ = (+,-)` labels, in the bulk `|E| < 2`. -/
theorem norm_Kv_le (B : Band Ω') {E : ℝ} (hE : |E| < 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (b : LoopArg (B.L N) 2) :
    ‖Kv B E N u b‖ ≤ (B.W N : ℝ)⁻¹ * (1 - u)⁻¹ := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hμ : ‖mSigma E true * mSigma E false‖ = 1 := by
    rw [norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, one_mul]
  have hnorm : ‖(u : ℂ) * (mSigma E true * mSigma E false)‖ = u := by
    rw [norm_mul, hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, mul_one]
  have hlt : ‖(u : ℂ) * (mSigma E true * mSigma E false)‖ < 1 := by rw [hnorm]; exact hu1
  have hentry : ∀ M : Matrix (ZMod (B.L N)) (ZMod (B.L N)) ℂ, ‖M (b 0) (b 1)‖ ≤ ‖M‖ :=
    fun M => (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => norm_nonneg (M (b 0) i))
        (Finset.mem_univ (b 1))).trans (sum_norm_row_le (B.L N) M (b 0))
  have hTh : ‖Theta (B.L N) ((u : ℂ) * (mSigma E true * mSigma E false)) (b 0) (b 1)‖
      ≤ (1 - u)⁻¹ := by
    refine (hentry _).trans ?_
    have h := norm_Theta_le (B.L N) hL3 hlt
    rwa [hnorm] at h
  unfold Kv
  rw [ofFn_two', Band.Kval, Kgen_two, kTwo, norm_mul, norm_mul, norm_inv, Complex.norm_natCast,
    hμ, mul_one]
  gcongr

/-- **Deterministic sup bound for `L_u(M)`**, Hermitian `M`, from (5.2)
(`norm_gloop_le_of_le_abs_im`, the bound behind `RBM.Gauss.norm_loopObs_le`). -/
theorem norm_Lval_le (B : Band Ω') (E : ℝ) (N : ℕ) (u : ℝ)
    {M : Matrix (B.Idx N) (B.Idx N) ℂ} (hM : M.IsHermitian) {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |(zt E u).im|) (b : LoopArg (B.L N) 2) :
    ‖Lval B E N u M b‖ ≤ η⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ := by
  have h := norm_gloop_le_of_le_abs_im (L := B.L N) (W := B.W N) hM hη hz
    (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod (B.L N))) (by simp) (by simp)
  simpa [Lval] using h

/-- The edge parameters of `σ = (+,-)` have modulus `1` in the bulk. -/
theorem norm_xiOf_pm_le {E : ℝ} (hE : |E| < 2) (i : Fin 2) :
    ‖xiOf (mSigma E) ![true, false] i‖ ≤ 1 := by
  unfold xiOf
  rw [norm_mul, norm_mSigma hE.le, norm_mSigma hE.le, one_mul]

/-- `zMotionLip` is non-increasing in `η`. -/
theorem zMotionLip_anti (L W n : ℕ) (m : Bool → ℂ) {η₁ η₂ : ℝ} (h1 : 0 < η₁) (h12 : η₁ ≤ η₂) :
    zMotionLip L W n η₂ m ≤ zMotionLip L W n η₁ m := by
  have h2 : 0 < η₂ := h1.trans_le h12
  have hi : η₂⁻¹ ≤ η₁⁻¹ := inv_anti₀ h1 h12
  unfold zMotionLip
  gcongr

/-- `zMotionZLip` is non-increasing in `η`. -/
theorem zMotionZLip_anti (L W n : ℕ) (m : Bool → ℂ) {η₁ η₂ : ℝ} (h1 : 0 < η₁) (h12 : η₁ ≤ η₂) :
    zMotionZLip L W n η₂ m ≤ zMotionZLip L W n η₁ m := by
  have h2 : 0 < η₂ := h1.trans_le h12
  have hi : η₂⁻¹ ≤ η₁⁻¹ := inv_anti₀ h1 h12
  unfold zMotionZLip
  gcongr

/-- `genPtLip` is non-increasing in `η`. -/
theorem genPtLip_anti (L W n : ℕ) (m : Bool → ℂ) {η₁ η₂ : ℝ} (h1 : 0 < η₁) (h12 : η₁ ≤ η₂) :
    genPtLip L W n η₂ m ≤ genPtLip L W n η₁ m := by
  have h2 : 0 < η₂ := h1.trans_le h12
  have hi : η₂⁻¹ ≤ η₁⁻¹ := inv_anti₀ h1 h12
  unfold genPtLip driftLip
  gcongr
  · unfold zMotionLip
    gcongr

end T4Aux

end RBM.Gauss.Grid

/-! ### (T4) : the combination (`L²` operator norm scope, matching T1503's `∫ ‖X‖`) -/

namespace RBM.Gauss.Grid

open RBM Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator

section T4

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **The explicit deterministic error `errStep'` of (T4)**: T1503 (T4)'s right-hand side at a
`2`-loop, plus the (T2) remainder `W⁻¹(1-u_{k+1})⁻¹(1-u_k)⁻² Δ²`, plus the (T3) remainder
`3(1-u_{k+1})⁻² Δ² M_k` with the deterministic sup bound
`M_k = |Im z_{u_k}|⁻² W⁻¹ + W⁻¹ (1-u_k)⁻¹` on `A_k`. It is `O(Δ^{3/2} + Δ²)`. -/
noncomputable def stepErr (B : Band Ω') (E : ℝ) (N : ℕ) (uk uk1 Δ : ℝ) : ℝ :=
  zMotionZLip (B.L N) (B.W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖ * Δ ^ 2 / 2
    + (zMotionLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E)
        + (2 / 3) * genPtLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E))
      * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat B.toDims N x‖ ∂ (P B.toDims))
    + (B.W N : ℝ)⁻¹ * (1 - uk1)⁻¹ * (1 - uk)⁻¹ ^ 2 * Δ ^ 2
    + 3 * (1 - uk1)⁻¹ ^ 2 * Δ ^ 2
        * (|(zt E uk).im|⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ + (B.W N : ℝ)⁻¹ * (1 - uk)⁻¹)

set_option maxHeartbeats 1000000 in
-- large goal terms (conditional expectations over the grid path, `Uker`, `eGterm`, `primBil`)
/-- **(T4)**: the discrete hierarchy step, the grid version of (5.19)/(5.20). For
`A_j := L_{u_j}(H_j) − K_{u_j}` on the `σ = (+,-)` `2`-loop labels,
`E[A_{k+1} | F_k] − U_{u_k,u_{k+1}} A_k = Δ·(EG-part + quad-part)(H_k) + R_k` with
`‖R_k‖_∞ ≤ stepErr` (deterministic, explicit, `O(Δ^{3/2} + Δ²)`). The `Θ`-part of the drift is
absorbed exactly into `Uker` via (T1) and (T3). -/
theorem discrete_hierarchy_step (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hst : s N < t N) (hk : k < K N) (hu0 : 0 ≤ time s t K N k)
    (hu1 : time s t K N (k + 1) < 1) :
    ∀ᵐ ω ∂ (Pg B.toDims), ∀ a : LoopArg (B.L N) 2,
      ‖(Pg B.toDims)[fun ω' => Lval B E N (time s t K N (k + 1))
              (H B.toDims s t K N (k + 1) ω') a
            - Kv B E N (time s t K N (k + 1)) a | filt B.toDims k] ω
          - Uker (B.L N) (xiOf (mSigma E) ![true, false]) (time s t K N k : ℂ)
              (time s t K N (k + 1) : ℂ)
              (fun v => Lval B E N (time s t K N k) (H B.toDims s t K N k ω) v
                - Kv B E N (time s t K N k) v) a
          - (step s t K N : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) (H B.toDims s t K N k ω)
                    (zt E (time s t K N k)) ⟨[true, false], List.ofFn a⟩
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    ⟨[true, false], List.ofFn a⟩)‖
        ≤ stepErr B E N (time s t K N k) (time s t K N (k + 1)) (step s t K N) := by
  set d : Dims := B.toDims with hd
  set uk : ℝ := time s t K N k with hukdef
  set uk1 : ℝ := time s t K N (k + 1) with huk1def
  set Δ : ℝ := step s t K N with hΔdef
  have hKpos : 0 < K N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hΔpos : 0 < Δ := by
    rw [hΔdef]; unfold step; exact div_pos (by linarith) (by exact_mod_cast hKpos)
  have huk1eq : uk1 = uk + Δ := by
    rw [huk1def, hukdef, hΔdef]; unfold time; push_cast; ring
  have hukuk1 : uk ≤ uk1 := by rw [huk1eq]; linarith
  have huk_lt : uk < 1 := by linarith
  have hzk : (zt E uk).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb huk_lt
  have hzk1 : (zt E uk1).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  have hηk : 0 < |(zt E uk).im| := abs_pos.mpr hzk
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  -- the per-label statement
  have hlabel : ∀ a : LoopArg (B.L N) 2, ∀ᵐ ω ∂ (Pg d),
      ‖(Pg d)[fun ω' => Lval B E N uk1 (H d s t K N (k + 1) ω') a
              - Kv B E N uk1 a | filt d k] ω
          - Uker (B.L N) (xiOf (mSigma E) ![true, false]) (uk : ℂ) (uk1 : ℂ)
              (fun v => Lval B E N uk (H d s t K N k ω) v - Kv B E N uk v) a
          - (Δ : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) (H d s t K N k ω) (zt E uk)
                    ⟨[true, false], List.ofFn a⟩
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) (H d s t K N k ω) (zt E uk) - B.Kval E N uk)
                    (gloop (B.L N) (B.W N) (H d s t K N k ω) (zt E uk) - B.Kval E N uk)
                    ⟨[true, false], List.ofFn a⟩)‖
        ≤ stepErr B E N uk uk1 Δ := by
    intro a
    set I : LoopIdx (ZMod (d.L N)) := ⟨[true, false], List.ofFn a⟩ with hIdef
    have hwf : I.WF := rfl
    have hn : 1 ≤ I.a.length :=
      (by norm_num : 1 ≤ 2).trans_eq (List.length_ofFn (f := (a : Fin 2 → ZMod (B.L N)))).symm
    have hσlen : I.σ.length = 2 := rfl
    -- integrability of `Φ_{u_{k+1}} ∘ H_{k+1}` (the route of `condExp_loop_step`'s `hIntTarget`)
    have hTF : TestFun d N (loopObs d N (zt E uk1) I) :=
      testFun_loopObs_of_im_le hzk1 (abs_pos.mpr hzk1) le_rfl hwf hn
    obtain ⟨C₀, hC₀⟩ := hTF.bdd₀
    have hHk1meas : Measurable (fun ω : Ωg d => H d s t K N (k + 1) ω) :=
      (H_measurable_filt d s t K N (k + 1)).mono ((filt d).le (k + 1)) le_rfl
    have hInt : Integrable
        (fun ω : Ωg d => loopObs d N (zt E uk1) I (H d s t K N (k + 1) ω)) (Pg d) :=
      (memLp_top_of_bound
        (hTF.contDiff.continuous.measurable.comp hHk1meas).aestronglyMeasurable C₀
        (Eventually.of_forall fun ω => hC₀ _)).integrable le_top
    -- `E[A_{k+1}(a) | F_k] = E[Φ_{u_{k+1}} ∘ H_{k+1} | F_k] − K_{u_{k+1}}(a)`
    have hfun : (fun ω' => Lval B E N uk1 (H d s t K N (k + 1) ω') a - Kv B E N uk1 a)
        = (fun ω' : Ωg d => loopObs d N (zt E uk1) I (H d s t K N (k + 1) ω'))
          - (fun _ => Kv B E N uk1 a) := by
      funext ω'
      rw [Pi.sub_apply, loopObs_of_isHermitian (H_isHermitian d s t K N (k + 1) ω')]
      rfl
    have hCE : (Pg d)[fun ω' => Lval B E N uk1 (H d s t K N (k + 1) ω') a
          - Kv B E N uk1 a | filt d k]
        =ᵐ[Pg d] fun ω => (Pg d)[fun ω' : Ωg d => loopObs d N (zt E uk1) I
            (H d s t K N (k + 1) ω') | filt d k] ω - Kv B E N uk1 a := by
      rw [hfun]
      filter_upwards [condExp_sub hInt (integrable_const (Kv B E N uk1 a)) (filt d k)]
        with ω hω
      rw [hω, Pi.sub_apply, condExp_const ((filt d).le k)]
    have hT := condExp_loop_drift s t K N k E hEb hwf hn hst hk hu0 hu1 hzk hzk1
    filter_upwards [hT, hCE] with ω h1 h2
    rw [h2]
    set M : Matrix (d.Idx N) (d.Idx N) ℂ := H d s t K N k ω with hMdef
    have hM : M.IsHermitian := H_isHermitian d s t K N k ω
    set c : ℂ := (Pg d)[fun ω' : Ωg d => loopObs d N (zt E uk1) I
      (H d s t K N (k + 1) ω') | filt d k] ω with hcdef
    -- (e₁) T1503
    have he1 : ‖c - Lval B E N uk M a - (Δ : ℂ) * loopDrift (d := d) (N := N) E uk I M‖
        ≤ zMotionZLip (B.L N) (B.W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖ * Δ ^ 2 / 2
          + (zMotionLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E)
              + (2 / 3) * genPtLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E))
            * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)) := by
      rw [loopObs_of_isHermitian hM, hσlen, smul_eq_mul] at h1
      exact h1
    -- (T1) at `u_k`, `M = H_k ω`
    have hμ : ‖mSigma E false * mSigma E true‖ = 1 := by
      rw [norm_mul, norm_mSigma hEb.le, norm_mSigma hEb.le, one_mul]
    have hμ' : ‖mSigma E true * mSigma E false‖ = 1 := by
      rw [norm_mul, norm_mSigma hEb.le, norm_mSigma hEb.le, one_mul]
    have hxi2 : ‖(uk : ℂ) * (mSigma E false * mSigma E true)‖ < 1 := by
      rw [norm_mul, hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, mul_one]
      exact huk_lt
    have hT1 := loopDrift_sub_K_deriv B E N uk hM hzk hxi2 a
    -- (T2) at `u_k → u_{k+1}`
    have hxi' : ‖(uk1 : ℂ) * (mSigma E true * mSigma E false)‖ < 1 := by
      rw [norm_mul, hμ', Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hu0.trans hukuk1), mul_one]
      exact hu1
    have hT2raw := K_step B E N true false (a 0) (a 1) hu0 hukuk1 hxi'
    have hcast : ((uk1 - uk : ℝ) : ℂ) = (Δ : ℂ) := by rw [huk1eq]; push_cast; ring
    have hsub : uk1 - uk = Δ := by rw [huk1eq]; ring
    rw [hcast, hsub, hμ', ← ofFn_two' a] at hT2raw
    have he2 : ‖Kv B E N uk1 a - Kv B E N uk a
          - (Δ : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N uk) ⟨[true, false], List.ofFn a⟩‖
        ≤ (B.W N : ℝ)⁻¹ * (1 - uk1)⁻¹ * (1 - uk)⁻¹ ^ 2 * Δ ^ 2 := by
      refine hT2raw.trans (le_of_eq ?_)
      simp only [one_pow, mul_one]
      ring
    -- (T3) with the deterministic sup bound `M_k`
    set Mk : ℝ := |(zt E uk).im|⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ + (B.W N : ℝ)⁻¹ * (1 - uk)⁻¹ with hMk
    have hMk0 : 0 ≤ Mk := by
      have : (0 : ℝ) ≤ (1 - uk)⁻¹ := inv_nonneg.mpr (by linarith)
      positivity
    have hA : ∀ b, ‖Lval B E N uk M b - Kv B E N uk b‖ ≤ Mk := fun b =>
      (norm_sub_le _ _).trans (add_le_add (norm_Lval_le B E N uk hM hηk le_rfl b)
        (norm_Kv_le B hEb N hu0 huk_lt b))
    have hut1 : uk + Δ < 1 := by rw [← huk1eq]; exact hu1
    have hT3 := Uker_step hL3 (xiOf (mSigma E) ![true, false]) (norm_xiOf_pm_le hEb) hu0
      hΔpos.le hut1 hMk0 hA a
    rw [← huk1eq] at hT3
    -- the exact cancellation
    have hident : c - Kv B E N uk1 a
          - Uker (B.L N) (xiOf (mSigma E) ![true, false]) (uk : ℂ) (uk1 : ℂ)
              (fun v => Lval B E N uk M v - Kv B E N uk v) a
          - (Δ : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) M (zt E uk) ⟨[true, false], List.ofFn a⟩
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) M (zt E uk) - B.Kval E N uk)
                    (gloop (B.L N) (B.W N) M (zt E uk) - B.Kval E N uk)
                    ⟨[true, false], List.ofFn a⟩)
        = (c - Lval B E N uk M a - (Δ : ℂ) * loopDrift (d := d) (N := N) E uk I M)
          - (Kv B E N uk1 a - Kv B E N uk a
              - (Δ : ℂ) * primRhs (B.L N) (B.W N) (B.Kval E N uk) ⟨[true, false], List.ofFn a⟩)
          - (Uker (B.L N) (xiOf (mSigma E) ![true, false]) (uk : ℂ) (uk1 : ℂ)
                (fun v => Lval B E N uk M v - Kv B E N uk v) a
              - (Lval B E N uk M a - Kv B E N uk a)
              - (Δ : ℂ) * ThetaOp (B.L N) (xiOf (mSigma E) ![true, false]) (uk : ℂ)
                (fun v => Lval B E N uk M v - Kv B E N uk v) a) := by
      linear_combination (Δ : ℂ) * hT1
    have hfinal : stepErr B E N uk uk1 Δ
        = (zMotionZLip (B.L N) (B.W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖
              * Δ ^ 2 / 2
            + (zMotionLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E)
                + (2 / 3) * genPtLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E))
              * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat d N x‖ ∂ (P d)))
          + (B.W N : ℝ)⁻¹ * (1 - uk1)⁻¹ * (1 - uk)⁻¹ ^ 2 * Δ ^ 2
          + 3 * (1 - uk1)⁻¹ ^ 2 * Δ ^ 2 * Mk := by
      rw [hMk]; rfl
    have key : ∀ x y z : ℂ, ‖x - y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := fun x y z => by
      linarith [norm_sub_le (x - y) z, norm_sub_le x y]
    rw [hident, hfinal]
    refine (key _ _ _).trans ?_
    linarith [he1, he2, hT3]
  exact ae_all_iff.mpr hlabel

/-- The `Δ²`-coefficient of the uniform bound on `stepErr`, on `u_{k+1} ≤ 1 - δ`
(`η_δ := δ · Im m^{(E)}`). Independent of the grid index. -/
noncomputable def stepErrC1 (B : Band Ω') (E : ℝ) (N : ℕ) (δ : ℝ) : ℝ :=
  zMotionZLip (B.L N) (B.W N) 2 (δ * (mE E).im) (mSigma E) * ‖mE E‖ / 2
    + (B.W N : ℝ)⁻¹ * δ⁻¹ * δ⁻¹ ^ 2
    + 3 * δ⁻¹ ^ 2 * ((δ * (mE E).im)⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ + (B.W N : ℝ)⁻¹ * δ⁻¹)

/-- The `Δ^{3/2}`-coefficient of the uniform bound on `stepErr`, on `u_{k+1} ≤ 1 - δ`.
Independent of the grid index. -/
noncomputable def stepErrC2 (B : Band Ω') (E : ℝ) (N : ℕ) (δ : ℝ) : ℝ :=
  (zMotionLip (B.L N) (B.W N) 2 (δ * (mE E).im) (mSigma E)
      + (2 / 3) * genPtLip (B.L N) (B.W N) 2 (δ * (mE E).im) (mSigma E))
    * (∫ x, ‖Xmat B.toDims N x‖ ∂ (P B.toDims))

/-- **Uniformity of `stepErr` in the grid index**: on `u_k ≤ u_{k+1} ≤ 1 - δ`,
`stepErr ≤ C₁(δ) Δ² + C₂(δ) Δ^{3/2}` with `C₁, C₂` depending only on `(L, W, E, δ, ∫‖X‖)`. -/
theorem stepErr_le_unif (B : Band Ω') {E : ℝ} (hEb : |E| < 2) (N : ℕ) {uk uk1 Δ δ : ℝ}
    (hδ : 0 < δ) (hukuk1 : uk ≤ uk1) (huδ : uk1 ≤ 1 - δ) (hΔ : 0 ≤ Δ) :
    stepErr B E N uk uk1 Δ ≤ stepErrC1 B E N δ * Δ ^ 2 + stepErrC2 B E N δ * Δ ^ (3 / 2 : ℝ) := by
  have hm : 0 < (mE E).im := mE_im_pos hEb
  have hηδ : 0 < δ * (mE E).im := mul_pos hδ hm
  have h1uk1 : δ ≤ 1 - uk1 := by linarith
  have h1uk : δ ≤ 1 - uk := by linarith
  have hη1 : δ * (mE E).im ≤ (1 - uk1) * (mE E).im := mul_le_mul_of_nonneg_right h1uk1 hm.le
  have hzim : |(zt E uk).im| = (1 - uk) * (mE E).im := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) hm.le)]
  have hη2 : δ * (mE E).im ≤ |(zt E uk).im| := by
    rw [hzim]; exact mul_le_mul_of_nonneg_right h1uk hm.le
  have hzpos : 0 < |(zt E uk).im| := hηδ.trans_le hη2
  have hinv1 : (1 - uk1)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ h1uk1
  have hinv0 : (1 - uk)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ h1uk
  have hinvη : |(zt E uk).im|⁻¹ ≤ (δ * (mE E).im)⁻¹ := inv_anti₀ hηδ hη2
  have hp1 : 0 ≤ (1 - uk1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hp0 : 0 ≤ (1 - uk)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 ≤ ∫ x, ‖Xmat B.toDims N x‖ ∂ (P B.toDims) :=
    integral_nonneg fun _ => norm_nonneg _
  have hZZ := zMotionZLip_anti (B.L N) (B.W N) 2 (mSigma E) hηδ hη1
  have hZL := zMotionLip_anti (B.L N) (B.W N) 2 (mSigma E) hηδ hη2
  have hGL := genPtLip_anti (B.L N) (B.W N) 2 (mSigma E) hηδ hη2
  have hZL0 : 0 ≤ zMotionLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E) := by
    unfold zMotionLip; positivity
  have hGL0 : 0 ≤ genPtLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E) := by
    unfold genPtLip driftLip zMotionLip; positivity
  have hZZ0 : 0 ≤ zMotionZLip (B.L N) (B.W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) := by
    have : 0 ≤ ((1 - uk1) * (mE E).im)⁻¹ := inv_nonneg.mpr (by nlinarith)
    unfold zMotionZLip; positivity
  have hW : (0 : ℝ) ≤ (B.W N : ℝ)⁻¹ := by positivity
  have hΔ32 : 0 ≤ Δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hΔ _
  have t1 : zMotionZLip (B.L N) (B.W N) 2 ((1 - uk1) * (mE E).im) (mSigma E) * ‖mE E‖ * Δ ^ 2 / 2
      ≤ zMotionZLip (B.L N) (B.W N) 2 (δ * (mE E).im) (mSigma E) * ‖mE E‖ * Δ ^ 2 / 2 := by
    gcongr
  have t2 : (zMotionLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E)
        + (2 / 3) * genPtLip (B.L N) (B.W N) 2 |(zt E uk).im| (mSigma E))
        * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat B.toDims N x‖ ∂ (P B.toDims))
      ≤ (zMotionLip (B.L N) (B.W N) 2 (δ * (mE E).im) (mSigma E)
        + (2 / 3) * genPtLip (B.L N) (B.W N) 2 (δ * (mE E).im) (mSigma E))
        * Δ ^ (3 / 2 : ℝ) * (∫ x, ‖Xmat B.toDims N x‖ ∂ (P B.toDims)) := by
    gcongr
  have t3 : (B.W N : ℝ)⁻¹ * (1 - uk1)⁻¹ * (1 - uk)⁻¹ ^ 2 * Δ ^ 2
      ≤ (B.W N : ℝ)⁻¹ * δ⁻¹ * δ⁻¹ ^ 2 * Δ ^ 2 := by
    gcongr
  have t4 : 3 * (1 - uk1)⁻¹ ^ 2 * Δ ^ 2
        * (|(zt E uk).im|⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ + (B.W N : ℝ)⁻¹ * (1 - uk)⁻¹)
      ≤ 3 * δ⁻¹ ^ 2 * Δ ^ 2
        * ((δ * (mE E).im)⁻¹ ^ 2 * (B.W N : ℝ)⁻¹ + (B.W N : ℝ)⁻¹ * δ⁻¹) := by
    have : 0 ≤ |(zt E uk).im|⁻¹ := inv_nonneg.mpr hzpos.le
    gcongr
  unfold stepErr stepErrC1 stepErrC2
  nlinarith [t1, t2, t3, t4]

/-- **(T4), uniform form**: the conclusion of `discrete_hierarchy_step` with the error bounded by
`C₁(δ) Δ² + C₂(δ) Δ^{3/2}`, uniformly in the grid index `k`, whenever `u_{k+1} ≤ 1 - δ`. In
particular `R_k = O(Δ^{3/2}) = o(Δ)` uniformly in `k` on `[0, 1 - δ]`. -/
theorem discrete_hierarchy_step_unif (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hst : s N < t N) (hk : k < K N) (hu0 : 0 ≤ time s t K N k) {δ : ℝ}
    (hδ : 0 < δ) (huδ : time s t K N (k + 1) ≤ 1 - δ) :
    ∀ᵐ ω ∂ (Pg B.toDims), ∀ a : LoopArg (B.L N) 2,
      ‖(Pg B.toDims)[fun ω' => Lval B E N (time s t K N (k + 1))
              (H B.toDims s t K N (k + 1) ω') a
            - Kv B E N (time s t K N (k + 1)) a | filt B.toDims k] ω
          - Uker (B.L N) (xiOf (mSigma E) ![true, false]) (time s t K N k : ℂ)
              (time s t K N (k + 1) : ℂ)
              (fun v => Lval B E N (time s t K N k) (H B.toDims s t K N k ω) v
                - Kv B E N (time s t K N k) v) a
          - (step s t K N : ℂ)
              * (eGterm (B.L N) (B.W N) (mSigma E) (H B.toDims s t K N k ω)
                    (zt E (time s t K N k)) ⟨[true, false], List.ofFn a⟩
                + primBil (B.L N) (B.W N)
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    (gloop (B.L N) (B.W N) (H B.toDims s t K N k ω) (zt E (time s t K N k))
                      - B.Kval E N (time s t K N k))
                    ⟨[true, false], List.ofFn a⟩)‖
        ≤ stepErrC1 B E N δ * (step s t K N) ^ 2
          + stepErrC2 B E N δ * (step s t K N) ^ (3 / 2 : ℝ) := by
  have hu1 : time s t K N (k + 1) < 1 := by linarith
  have hKpos : 0 < K N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hΔpos : 0 < step s t K N := by
    unfold step; exact div_pos (by linarith) (by exact_mod_cast hKpos)
  have hsucc : time s t K N (k + 1) = time s t K N k + step s t K N := by
    unfold time; push_cast; ring
  have hle : time s t K N k ≤ time s t K N (k + 1) := by rw [hsucc]; linarith
  filter_upwards [discrete_hierarchy_step B s t K N k E hEb hst hk hu0 hu1] with ω h a
  exact (h a).trans (stepErr_le_unif B hEb N hδ hle huδ hΔpos.le)

/-- **Satisfiability witness** for the hypotheses of `discrete_hierarchy_step` and
`discrete_hierarchy_step_unif` (none involves the band `B`): `E = 0`, a grid of step `Δ = 1/8`
on `[1/4, 1/2]` (`K = 2`), step `k = 0` (`u_0 = 1/4`, `u_1 = 3/8`), `δ = 5/8`. This is T1503 §8's
witness plus `δ`; nothing degenerates (`Δ > 0`, `u_1 < 1`, `δ > 0`). -/
example :
    ∃ (s t : ℕ → ℝ) (K : ℕ → ℕ) (N k : ℕ) (E δ : ℝ), |E| < 2 ∧ s N < t N ∧ k < K N ∧
      0 ≤ time s t K N k ∧ time s t K N (k + 1) < 1 ∧ 0 < δ ∧
      time s t K N (k + 1) ≤ 1 - δ ∧ 0 < step s t K N := by
  refine ⟨fun _ => 1 / 4, fun _ => 1 / 2, fun _ => 2, 0, 0, 0, 5 / 8, by norm_num, by norm_num,
    by norm_num, ?_, ?_, by norm_num, ?_, ?_⟩
  · unfold time step; norm_num
  · unfold time step; norm_num
  · unfold time step; norm_num
  · unfold step; norm_num

end T4

end RBM.Gauss.Grid
