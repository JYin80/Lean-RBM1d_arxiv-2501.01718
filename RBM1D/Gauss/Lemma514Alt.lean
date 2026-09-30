/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridAssemblyKerClass
import RBM1D.Gauss.GridQAlgebra
import RBM1D.Gauss.EETensorBound
import RBM1D.Gauss.Lemma510Fixed
import RBM1D.Gauss.OpNorm
import Mathlib.Probability.ConditionalExpectation

/-!
# Lemma 5.14, all-`n` endpoint, alternating charges (Case 2 + Q): the ingredients

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, Lemma 5.14, (5.87)-(5.105), for the Gaussian model, at every even `n ≥ 4` and
the two cyclically alternating charges.  It uses the fixed assembly interface
(`GridAssemblyKerClass.lean`, restricted kernel class, moment-based `Y` tail).

## Main results

* `sigmaAltGen`, `sigmaAltGen_nonconst` (and the complementary `sigmaAltGen'` versions) — the
  general even-`n` alternating charge, which alternates around the whole cycle (no repeat, so
  Case 1 is unavailable), and is non-constant, for `Qop_endpoint'`.
* `integrable_normPow_incr` — integrability of the moments of the fresh grid increment; the
  independence-based collapse of its conditional moments to deterministic constants
  (`indep_incr` + Mathlib's `condExp_indep_eq`) controls the `Y` tail for the identity-kernel
  martingale difference.
* `sumZeroAt_Qop` — `Q_t` always lands in the sum-zero class (feeds `KerClass`'s `SumZeroAt`
  half unconditionally).

The remaining ingredients of the endpoint are in `RBM1D/Gauss/Lemma514AltEnd.lean`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Matrix Finset MeasureTheory ProbabilityTheory Filter RBM.SumZeroDyn
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ### The general even-`n` alternating charge -/

section AltCharge

/-- **The general alternating charge**: `σ i = true` iff `i` is even, read cyclically on
`Fin n`. For even `n` this alternates around the whole cycle. -/
def sigmaAltGen (n : ℕ) : Fin n → Bool := fun i => decide (i.val % 2 = 0)

/-- The complementary alternating charge, `!sigmaAltGen n`. -/
def sigmaAltGen' (n : ℕ) : Fin n → Bool := fun i => !decide (i.val % 2 = 0)

/-- **`sigmaAltGen` is non-constant** (`n ≥ 2`): index `0` and index `1` differ. Feeds the
hypothesis `hσ : ∃ i j, σ i ≠ σ j` of `Qop_endpoint'`. -/
theorem sigmaAltGen_nonconst {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ i j : Fin n, sigmaAltGen n i ≠ sigmaAltGen n j := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  simp [sigmaAltGen]

theorem sigmaAltGen'_nonconst {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) :
    ∃ i j : Fin n, sigmaAltGen' n i ≠ sigmaAltGen' n j := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  simp [sigmaAltGen']

end AltCharge

/-! ### The `Y`-moment producer

`stepDecompC` gives `Y^C = ξ^C - Z^C` (mean zero, `filt d j`-measurable `AbC`) and the
a.e. pathwise bound `‖Y^C_b(ω)‖ ≤ g(ω) + E[g|F_j](ω)`, `g(ω) := (Σ_a‖U(b,a)‖)(C₂/2)Δ‖X(ω(j+1))‖²`
(`stepYC_norm_le_ae`). With `U := gridDeltaC` (the identity matrix, so `A_b ↦ stepZC/stepYC_b` is
literally the martingale difference of the observable `b`, no extra combination), the row sum is
always `1`, so the bound is uniform in `b`. Since `ω ↦ ω(j+1)` is independent of `filt d j`
(`indep_incr`) and identically distributed to a single draw (`map_incr`), `E[g^m|F_j]` is a.e. a
*constant*, computable from the moments of `‖Xmat‖` (`integrable_norm_Xmat_pow`, all orders). -/

section YMomentProducer

variable (d : Dims)

/-- **Integrability of any even power of the fresh increment's norm** (the fourth-moment
analogue of `integrable_normSq_incr`/`integrable_normPow4_incr`, at every order `p`, by the
same `map_incr` change-of-variables argument, fed by `integrable_norm_Xmat_pow`). -/
theorem integrable_normPow_incr (N j p : ℕ) :
    Integrable (fun ω : Ωg d => ‖Xmat d N (ω (j + 1))‖ ^ (2 * p)) (Pg d) := by
  have hg : Integrable (fun x : Ω d => ‖Xmat d N x‖ ^ (2 * p)) (P d) :=
    integrable_norm_Xmat_pow d N p
  have hf : AEMeasurable (fun ω : Ωg d => ω (j + 1)) (Pg d) :=
    (measurable_pi_apply (j + 1)).aemeasurable
  have hmap : (Pg d).map (fun ω : Ωg d => ω (j + 1)) = P d := map_incr d j
  have hgASM : AEStronglyMeasurable (fun x : Ω d => ‖Xmat d N x‖ ^ (2 * p))
      ((Pg d).map fun ω => ω (j + 1)) := by
    rw [hmap]; exact hg.aestronglyMeasurable
  exact (integrable_map_measure hgASM hf).1 (by rw [hmap]; exact hg)

end YMomentProducer

/-! ### `Q`-transformed tensors are always sum-zero at `0`

The Case-2 kernel bound (`hker_of_Q716_sumZero`) needs `SumZeroAt L 0 X` on the initial datum
`A0 = Q_{u_0} ∘ (L-K)_{u_0,σ}` and on the drift `Dr_j = Q_{u_j} D_j + [Q_{u_j},Θ] (L-K)_j
- ϑ̇_{u_j} P (L-K)_j`. Both are automatic, unconditionally: `Q_t` always kills the `P`-sum
(`RBM.SumZero_Qop`), and the other two summands of `Dr_j` are differences/products of `Q`-images,
so no decay/good-event input is needed for
this half of `hA0cls`/`hDcls` — only the `FastDecay` half genuinely uses `decaySet`. -/

section SumZeroClosure

variable (L : ℕ) [NeZero L]

/-- **`Q_t ∘ A` is sum-zero at `0`** (Definition (7.15)'s coordinate `a_1`), for **any** `A`,
whenever `‖t‖ < 1`: `Q`'s whole purpose is to kill the `P`-sum (`SumZero_Qop`). Feeds
`hA0cls`/`hDcls`'s `SumZeroAt` half directly — no `decaySet` input is needed for it. -/
theorem sumZeroAt_Qop (hL : 3 ≤ L) {n : ℕ} {t : ℂ} (ht : ‖t‖ < 1) (A : LoopArg L (n + 1) → ℂ) :
    SumZeroAt L 0 (Qop L t A) :=
  SumZeroDyn.sumZeroAt_zero_of_sumZero L (SumZero_Qop L hL ht A)

end SumZeroClosure

end RBM.Gauss.Grid

end

