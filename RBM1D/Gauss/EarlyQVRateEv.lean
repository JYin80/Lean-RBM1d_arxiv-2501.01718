/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EarlyQVRate
import RBM1D.Hierarchy.Step2Near47
import RBM1D.Gauss.Step6Hyp
import RBM1D.Flow.Thm221Bare
import RBM1D.Flow.EnergyUniform
import RBM1D.Hierarchy.Step2FarMart
import RBM1D.Flow.Eq548Producer
import RBM1D.Gauss.EntryBoundTime

/-!
# The structural inputs of `(S3)`: the `4`-loop maximum and the glued `6`-loops

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §2.7 (2.73), §5.2–§5.3, (5.22), (5.36).

`RBM1D/Gauss/EarlyQVRate.lean` bounds the quadratic variation `quadVar (M ↦ (L-K)_{u,σ,b}(M))`
pointwise by `E ⊗ E`.  This file supplies the deterministic inputs through which the right-hand
side of (5.36) is controlled by the a-priori estimate (2.73).

## What is here

* `RBM.EarlyQVRateEv.sMax`, `RBM.EarlyQVRateEv.re_gloop_four_le_sMax` — the maximum of the real
  parts of the `4`-loops, as a **finite maximum**, not as a hypothesis.
* `RBM.EarlyQVRateEv.sMax_le` — `sMax` is bounded by any uniform bound on the `4`-loops, in
  particular by (2.73) at `n = 4`; this is the paper's `μ ≺ r_u^{3/2} A_u^{-3/2}` with
  `μ = 2√sMax`.
* `RBM.EarlyQVRateEv.glueLD0`, `glueLD1`, `glueLD0_idx`, `glueLD1_idx`, `eeL6_two_le` — the two
  glued `6`-loops of Figure 14 (`RBM.EEDef.glueIdx_two_zero` / `_two_one`) are
  `RBM.LoopData _ 6`, i.e. members of the family that (2.73) controls, and
  `∑_{b'} ‖S_{bb'}‖ = 1` (`RBM.sum_norm_SB_apply_row`), so a uniform bound `C` on the `6`-loops
  gives `eeL6 ≤ 2C`.
* `RBM.EarlyQVRateEv.sDet`, `RBM.EarlyQVRateEv.sDet_nonneg` — the deterministic level
  `(ℓ_u/ℓ_s)^3 (W ℓ_u η_u)^{-3}` of `sMax` that (2.73) gives at `n = 4`.

Nothing here is an `axiom` and nothing is `sorry`.
-/

namespace RBM

namespace EarlyQVRateEv

open Matrix Finset RBM.Gauss MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-! ### 1. The maximum of the `4`-loops, as a finite maximum -/

/-- The maximum of the real part of the `4`-loops of (5.66). -/
noncomputable def sMax (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Bool × ZMod (B.L N) × ZMod (B.L N) × ZMod (B.L N))).sup'
    ⟨(true, 0, 0, 0), Finset.mem_univ _⟩
    (fun q => (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[q.1, !q.1, q.1, !q.1], [q.2.1, q.2.2.1, q.2.1, q.2.2.2]⟩).re)

theorem re_gloop_four_le_sMax (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (s : Bool) (x y y' : ZMod (B.L N)) :
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ sMax X E N u ω :=
  Finset.le_sup' (f := fun q : Bool × ZMod (B.L N) × ZMod (B.L N) × ZMod (B.L N) =>
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[q.1, !q.1, q.1, !q.1], [q.2.1, q.2.2.1, q.2.1, q.2.2.2]⟩).re)
    (Finset.mem_univ (s, x, y, y'))

/-- **`sMax` from (2.73) at `n = 4`.**  `sMax` is a maximum of real parts of `4`-loops, so any
uniform bound on the `4`-loops at the time `u` — in particular the a-priori bound (2.73) at
`n = 4`, `N^τ (ℓ_u/ℓ_s)^3 (Wℓ_uη_u)^{-3}` — bounds it.  This is the `μ ≺ r_u^{3/2} A_u^{-3/2}`
of the paper: `μ = 2√sMax`. -/
theorem sMax_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω) {C : ℝ}
    (hC : ∀ p : LoopData (B.L N) 4, ‖X.Lval E N u ω p.idx‖ ≤ C) :
    sMax X E N u ω ≤ C := by
  refine Finset.sup'_le _ _ (fun q _ => ?_)
  have h := hC (![q.1, !q.1, q.1, !q.1], ![q.2.1, q.2.2.1, q.2.1, q.2.2.2])
  have hidx : (LoopData.idx
      (![q.1, !q.1, q.1, !q.1], ![q.2.1, q.2.2.1, q.2.1, q.2.2.2]) : LoopIdx (ZMod (B.L N)))
      = ⟨[q.1, !q.1, q.1, !q.1], [q.2.1, q.2.2.1, q.2.1, q.2.2.2]⟩ := by
    simp [LoopData.idx, List.ofFn_succ]
  rw [hidx] at h
  exact le_trans (Complex.re_le_norm _) h

/-! ### 2. The glued `6`-loops of (5.22) are `6`-loops of (2.73) -/

/-- The `k = 0` glued loop of Figure 14, as an element of `RBM.LoopData L 6`. -/
def glueLD0 {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    LoopData L 6 :=
  (![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)],
   ![EEBridge.leftArg c 0, EEBridge.leftArg c 1, b,
     EEBridge.rightArg c 1, EEBridge.rightArg c 0, b'])

/-- The `k = 1` glued loop of Figure 14, as an element of `RBM.LoopData L 6`. -/
def glueLD1 {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    LoopData L 6 :=
  (![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)],
   ![EEBridge.leftArg c 1, EEBridge.leftArg c 0, b,
     EEBridge.rightArg c 0, EEBridge.rightArg c 1, b'])

theorem glueLD0_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    (glueLD0 σ c b b').idx
      = EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c)) 0 b b' := by
  rw [EEDef.glueIdx_two_zero]
  simp [glueLD0, LoopData.idx, List.ofFn_succ]

theorem glueLD1_idx {L : ℕ} (σ : Fin 2 → Bool) (c : LoopArg L (2 + 2)) (b b' : ZMod L) :
    (glueLD1 σ c b b').idx
      = EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c)) 1 b b' := by
  rw [EEDef.glueIdx_two_one]
  simp [glueLD1, LoopData.idx, List.ofFn_succ]

/-- **The glued `6`-loops, bounded by (2.73) at `n = 6`.**  Every glued `6`-loop of (5.22) is a
`6`-loop of the family that the a-priori bound (2.73) controls, and `∑_{b'} ‖S_{bb'}‖ = 1`
(`RBM.sum_norm_SB_apply_row`), so a uniform bound `C` on the `6`-loops gives `eeL6 ≤ 2 C`. -/
theorem eeL6_two_le (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (σ : Fin 2 → Bool) (c : LoopArg (B.L N) (2 + 2)) (b : ZMod (B.L N)) {C : ℝ}
    (hC : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖ ≤ C) :
    EEDef.eeL6 X E N u ω σ c b ≤ 2 * C := by
  classical
  have hrow := sum_norm_SB_apply_row (B.L N) (B.three_le_L N) b
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC (glueLD0 σ c b b))
  have key : ∀ k : ℕ, (∀ b' : ZMod (B.L N),
      ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
        (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c))
          k b b')‖ ≤ C) → EEDef.eeL6k X E N u ω σ c k b ≤ C := by
    intro k hk
    have hstep : ∀ b' ∈ (Finset.univ : Finset (ZMod (B.L N))),
        ‖SB (B.L N) b b'‖ * ‖gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
            (EEBridge.glueIdx (toIdx σ (EEBridge.leftArg c)) (toIdx σ (EEBridge.rightArg c))
              k b b')‖ ≤ ‖SB (B.L N) b b'‖ * C :=
      fun b' _ => mul_le_mul_of_nonneg_left (hk b') (norm_nonneg _)
    calc EEDef.eeL6k X E N u ω σ c k b ≤ ∑ b' : ZMod (B.L N), ‖SB (B.L N) b b'‖ * C :=
          Finset.sum_le_sum hstep
      _ = C := by rw [← Finset.sum_mul, hrow, one_mul]
  have h0 : EEDef.eeL6k X E N u ω σ c 0 b ≤ C :=
    key 0 fun b' => by rw [← glueLD0_idx σ c b b']; exact hC _
  have h1 : EEDef.eeL6k X E N u ω σ c 1 b ≤ C :=
    key 1 fun b' => by rw [← glueLD1_idx σ c b b']; exact hC _
  rw [EEDef.eeL6_two_eq]
  linarith

/-! ### 3. The right-hand side of `(S3)`, and the pointwise bound on the Step-1 event -/

/-! ### 4. `(S3)` at one time, from the a-priori bound (2.73) at `n = 6` -/

/-! ### 5. The union bound over the grid and over `b` -/

/-! ### 6. The wrapper in the `∀ ε D″, ∃ N₀, ∀ N ≥ N₀` shape -/

/-! ### 8. `μ = 2√Smax` written into `ζ` -/

/-- **The deterministic level of `sMax`**: `(ℓ_u/ℓ_s)^3 (W ℓ_u η_u)^{-3}`, i.e. the square of
the paper's `μ ≺ r_u^{3/2} A_u^{-3/2}`, which is what (2.73) delivers at `n = 4` (the control
of the a-priori bound at `n = 4` is exactly this). -/
noncomputable def sDet (B : Band Ω) (E : ℝ) (N : ℕ) (u ℓs : ℝ) : ℝ :=
  (B.ell N u / ℓs) ^ 3 * (B.scale E N u)⁻¹ ^ 3

theorem sDet_nonneg (B : Band Ω) (E : ℝ) (N : ℕ) {u ℓs : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hℓs : 0 < ℓs) : 0 ≤ sDet B E N u ℓs := by
  have hℓu : (1 : ℝ) ≤ B.ell N u := one_le_ellHat (B.L N) (B.three_le_L N) hu0 hu1
  have hA : 0 ≤ B.scale E N u := B.scale_nonneg E N hu1.le
  exact mul_nonneg (pow_nonneg (div_nonneg (by linarith) hℓs.le) 3)
    (pow_nonneg (inv_nonneg.2 hA) 3)

/-! ### 7. Satisfiability, on a non-degenerate grid -/

section Witness

end Witness

/-! ### Deviations

**The factor `μ`.**  The paper states (5.36) with the far-field factor
`μ ≺ r_u^{3/2} A_u^{-3/2}`, obtained from (2.73) at `n = 4`.  Here `μ = 2√sMax` with `sMax` the
*defined* maximum of the real parts of the `4`-loops (`RBM.EarlyQVRateEv.sMax`), and the step to
the paper's `μ` is the separate lemma `RBM.EarlyQVRateEv.sMax_le`; the deterministic level is
`RBM.EarlyQVRateEv.sDet = (ℓ_u/ℓ_s)^3 (W ℓ_u η_u)^{-3}`.  Keeping `sMax` symbolic avoids an
event restriction, and lets the consumer choose the level at which `μ` is evaluated. -/

end EarlyQVRateEv

end RBM
