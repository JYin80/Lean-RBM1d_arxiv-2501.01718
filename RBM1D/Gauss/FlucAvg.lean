/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.FlucCount
import RBM1D.Gauss.Envelope
import Mathlib.Analysis.Matrix.MeasurableSpace
import RBM1D.Defs.MatrixMeasurable

/-!
# Assembling the fluctuation averaging: the pieces of (4.12) and (4.5)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §4, (4.12):

  `∑_k t_k (1 - E_k)(G_{kk} - m) ≺ Ψ²`,   `0 ≤ |t_k| ≤ W⁻¹`, `∑_k |t_k| ≤ 1`   **(4.12)**

and from there `|⟨(G - m)E_a⟩| ≺ Ψ²`, which is **(4.5)**.

## What is proved here

1. **Measurability.**  `RBM.Gauss.measurable_green_apply`: `ω ↦ G_{ij}(ω)` is measurable, because
   `A⁻¹ = Ring.inverse (det A) • adjugate A` with `det`, `adjugate` polynomial and
   `Ring.inverse = (·)⁻¹` measurable on `ℂ`.  `RBM.Gauss.measurable_condRow`: `ω ↦ E_k[X](ω)`
   is measurable for measurable `X`, because `E_k` is an integral over the second factor of
   `Ω × Ω` along the jointly measurable `RBM.Gauss.rowSplit`
   (`MeasureTheory.StronglyMeasurable.integral_prod_right'`).  Together with
   `RBM.Gauss.rowIntegrable_greenDiagCentered` these discharge the measurability and
   row-integrability side conditions of the moment expansion of `RBM1D/Gauss/FlucCount.lean`.
2. **The pointwise parameters.**  `RBM.Gauss.FlucBound` packages uniform bounds `B` on the
   factors and `ε` on the replacement error; `RBM.Gauss.flucBound_env` produces them
   unconditionally from the deterministic envelope `‖G_t‖_op ≤ η_t⁻¹` of
   `RBM1D/Gauss/Envelope.lean`: `B = 2(η_t⁻¹ + 1)`, `ε = 4 η_t⁻¹`.
3. **The moment side.**  `RBM.Gauss.measurable_flucAvg`, `RBM.Gauss.norm_flucAvg_le` and
   `RBM.Gauss.integrable_norm_flucAvg_pow`; the two coefficient families of (4.12) are counted
   by `RBM.Gauss.card_blockAvg_support` and `RBM.Gauss.card_Sblk_support`, with the polynomial
   cardinality bound of Definition 2.1 (i) supplied from the model's own `dim` and `bandwidth`
   fields (`RBM.Gauss.card_Idx_le`, `RBM.Gauss.card_ZMod_L_le`).
4. **(4.5).**  `RBM.Gauss.norm_trace_green_sub_mul_Eblk_le_flucAvg` instantiates the `x` of
   `RBM.norm_trace_green_sub_mul_Eblk_le` at `RBM.Gauss.condExpDiag`, after which its `hFA` and
   `hFA'` **are** the two (4.12) bounds: `hFA` is discharged into `RBM.Gauss.flucAvg`.

## Pointwise parameters versus `≺`

The moment bounds of `RBM1D/Gauss/FlucVanish.lean` and `RBM1D/Gauss/FlucCount.lean` are stated
for **pointwise-uniform** `B` and `ε`, while the minor replacement (4.9) gives `≺ Ψ²`, a bound
on a high-probability event.  So:

* Pointwise parameters **do** exist, unconditionally: `RBM.Gauss.flucBound_env`.  Their size is
  `η_t⁻¹`, so they are far weaker than what (4.12) needs, but they show the interface is not
  vacuous.
* Truncation **cannot** upgrade `ε` from `η_t⁻¹` to `Ψ²` at this interface, and no amount of
  indicator bookkeeping would help.  The reason is structural, not technical: the vanishing
  lemma of `RBM1D/Gauss/FlucVanish.lean` uses `E_{k}[(1 - E_k)X] = 0`, an exact identity for the
  *untruncated* variable. Multiplying a factor by `1_Ω` destroys it, since
  `E_k[1_Ω (1 - E_k) X] ≠ 0`; and `1_Ω` is not `FinDepOffRow`, so it cannot be pulled out of `E_k`
  either.
* **Even with `ε ≍ Ψ²` and `B ≍ Ψ` the first-order bound would not give (4.12).**  Its lone-slot
  stratum contributes `(2p - 1) ε B^{2p-1} ≍ Ψ^{2p+1}`, whereas (4.12) needs `Ψ^{4p}`; already at
  `p = 1` this is `Ψ³` against `Ψ⁴`.  The missing input is the *higher-order* minor expansion:
  the replacement `Z_{k_i} ↦ Z^{(k_{i₀})}_{k_i}` has to be iterated to order `2p`, so that the
  residual error is `Ψ^{4p}` rather than `Ψ²`.  `RBM1D/Gauss/FlucVanish.lean` performs it to
  first order only; the iteration is `RBM1D/Gauss/FlucIter.lean`.

## Deviation from the paper

None in substance.  The uniform parameters `B`, `ε` are bundled as `RBM.Gauss.FlucBound` rather
than inlined as `Ψ`, `Ψ²`.

## Main results

* `RBM.Gauss.measurable_green_apply`, `RBM.Gauss.measurable_condRow` — the two
  measurability facts.
* `RBM.Gauss.FlucBound`, `RBM.Gauss.flucBound_env` — the pointwise parameters and the
  unconditional envelope instance.
* `RBM.Gauss.card_blockAvg_support`, `RBM.Gauss.card_Sblk_support` — the two coefficient
  families.
* `RBM.Gauss.norm_trace_green_sub_mul_Eblk_le_flucAvg` — **(4.5)**, deterministic form, with
  `hFA` discharged into (4.12).
-/

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory Filter Finset

variable {d : Dims} {N : ℕ}

/-! ### Measurability

Two measurability facts, needed for the measurability and row-integrability side conditions of
the moment expansion of `RBM1D/Gauss/FlucCount.lean`. -/

/-- `ω ↦ H_u(ω) - z` is measurable as a matrix-valued map. -/
theorem measurable_Hflow_sub (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) :
    Measurable fun ω : Ω d =>
      Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ) := by
  refine Matrix.measurable_iff.2 fun a b => ?_
  have h : (fun ω : Ω d => (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) a b)
      = fun ω => Hflow d N u ω a b - z * (1 : Matrix (d.Idx N) (d.Idx N) ℂ) a b := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (measurable_Hflow d N u a b).sub measurable_const

/-- **`ω ↦ G_{ij}(ω)` is measurable.** -/
theorem measurable_green_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (i j : d.Idx N) :
    Measurable fun ω => green (Hflow d N u ω) z i j :=
  measurable_matrix_inv_apply (measurable_Hflow_sub d N u z) i j

/-- The same for the minor resolvent `G^{(κ)}`. -/
theorem measurable_greenMinorMat_apply (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (κ : d.Idx N)
    (a b : {a : d.Idx N // a ≠ κ}) :
    Measurable fun ω => greenMinorMat d N u z κ ω a b := by
  refine measurable_matrix_inv_apply (M := fun ω : Ω d =>
    (Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ κ} → d.Idx N)
      (Subtype.val : {a : d.Idx N // a ≠ κ} → d.Idx N)
      - z • (1 : Matrix {a : d.Idx N // a ≠ κ} {a : d.Idx N // a ≠ κ} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  have h : (fun ω : Ω d =>
      ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ κ} → d.Idx N)
        (Subtype.val : {a : d.Idx N // a ≠ κ} → d.Idx N)
        - z • (1 : Matrix {a : d.Idx N // a ≠ κ} {a : d.Idx N // a ≠ κ} ℂ)) p q)
      = fun ω => Hflow d N u ω p.1 q.1
          - z * (1 : Matrix {a : d.Idx N // a ≠ κ} {a : d.Idx N // a ≠ κ} ℂ) p q := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (measurable_Hflow d N u p.1 q.1).sub measurable_const

/-- **`ω ↦ E_k[X](ω)` is measurable** for measurable `X`.  `E_k` is an
integral over the second factor of `Ω × Ω`, and `rowSplit` is jointly measurable
(`RBM.Gauss.measurable_rowSplit`), so `MeasureTheory.StronglyMeasurable.integral_prod_right'`
applies. -/
theorem measurable_condRow (d : Dims) (N : ℕ) (k : d.Idx N) {X : Ω d → ℂ} (hX : Measurable X) :
    Measurable (condRow d N k X) := by
  have hjoint : StronglyMeasurable fun p : Ω d × Ω d => X (rowSplit d N k p.1 p.2) :=
    (hX.comp (measurable_rowSplit d N k)).stronglyMeasurable
  exact hjoint.integral_prod_right'.measurable

theorem measurable_greenDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) :
    Measurable (greenDiagCentered d N u z m k) :=
  (measurable_green_apply d N u z k k).sub measurable_const

theorem measurable_greenMinorDiagCentered (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (κ : d.Idx N)
    (k : {a : d.Idx N // a ≠ κ}) :
    Measurable (greenMinorDiagCentered d N u z m κ k) :=
  (measurable_greenMinorMat_apply d N u z κ k k).sub measurable_const

/-- The factors `Z_k` of the moment expansion of `RBM1D/Gauss/FlucCount.lean` are measurable. -/
theorem measurable_flucDiag (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) :
    Measurable (flucDiag d N u z m k) :=
  (measurable_greenDiagCentered d N u z m k).sub
    (measurable_condRow d N k (measurable_greenDiagCentered d N u z m k))

/-! ### The deterministic envelope, entrywise

`Im z_t = η_t > 0` for `|E| < 2`, `t < 1`, so `‖G_t‖_op ≤ η_t⁻¹` for *every* `ω`
(`RBM.Gauss.norm_green_zt_le`), and the same for every minor `G^{(κ)}_t`, a resolvent of the
Hermitian matrix `H^{(κ)}`.  These are the only pointwise bounds available; see the discussion
of the truncation seam in the module docstring. -/

section Envelope

open scoped Matrix.Norms.L2Operator

variable {u E t : ℝ}

/-- `|G_{ij}| ≤ η_t⁻¹` for every `ω`. -/
theorem norm_green_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ) (i j : d.Idx N)
    (ω : Ω d) : ‖green (Hflow d N u ω) (zt E t) i j‖ ≤ (etaT E t)⁻¹ :=
  le_trans (norm_apply_le_l2_opNorm _ i j)
    (norm_green_zt_le (Hflow_isHermitian d N u ω) hE ht)

/-- `G^{(κ)}` is the resolvent of the minor `H^{(κ)}`, which is Hermitian. -/
theorem greenMinorMat_eq_green_submatrix (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (κ : d.Idx N)
    (ω : Ω d) :
    greenMinorMat d N u z κ ω
      = green ((Hflow d N u ω).submatrix (Subtype.val : {a : d.Idx N // a ≠ κ} → d.Idx N)
          (Subtype.val : {a : d.Idx N // a ≠ κ} → d.Idx N)) z := rfl

/-- `|G^{(κ)}_{ab}| ≤ η_t⁻¹` for every `ω`: the minor of a Hermitian matrix is Hermitian, so the
same envelope applies. -/
theorem norm_greenMinorMat_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ) {κ : d.Idx N}
    (a b : {a : d.Idx N // a ≠ κ}) (ω : Ω d) :
    ‖greenMinorMat d N u (zt E t) κ ω a b‖ ≤ (etaT E t)⁻¹ := by
  have : Nonempty {a : d.Idx N // a ≠ κ} := ⟨a⟩
  rw [greenMinorMat_eq_green_submatrix]
  exact le_trans (norm_apply_le_l2_opNorm _ a b)
    (norm_green_zt_le ((Hflow_isHermitian d N u ω).submatrix _) hE ht)

/-- `|G_{kk} - m| ≤ η_t⁻¹ + 1` for every `ω` (`‖m^{(E)}‖ = 1`). -/
theorem norm_greenDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N)
    (ω : Ω d) :
    ‖greenDiagCentered d N u (zt E t) (mE E) k ω‖ ≤ (etaT E t)⁻¹ + 1 := by
  refine le_trans (norm_sub_le _ _) (add_le_add (norm_green_apply_le_etaT hE ht u k k ω) ?_)
  exact le_of_eq (norm_mE hE.le)

theorem norm_greenMinorDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) {κ : d.Idx N}
    (k : {a : d.Idx N // a ≠ κ}) (ω : Ω d) :
    ‖greenMinorDiagCentered d N u (zt E t) (mE E) κ k ω‖ ≤ (etaT E t)⁻¹ + 1 := by
  refine le_trans (norm_sub_le _ _)
    (add_le_add (norm_greenMinorMat_apply_le_etaT hE ht u k k ω) ?_)
  exact le_of_eq (norm_mE hE.le)

/-- `RowIntegrable` for `G_{kk} - m`, the row-integrability side condition of the moment
expansion. -/
theorem rowIntegrable_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : d.Idx N) :
    RowIntegrable d N k (greenDiagCentered d N u (zt E t) (mE E) k) :=
  rowIntegrable_of_measurable_of_bound (measurable_greenDiagCentered d N u (zt E t) (mE E) k)
    (norm_greenDiagCentered_le_env hE ht u k)

theorem rowIntegrable_greenMinorDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {κ : d.Idx N} (k : {a : d.Idx N // a ≠ κ}) (j : d.Idx N) :
    RowIntegrable d N j (greenMinorDiagCentered d N u (zt E t) (mE E) κ k) :=
  rowIntegrable_of_measurable_of_bound
    (measurable_greenMinorDiagCentered d N u (zt E t) (mE E) κ k)
    (norm_greenMinorDiagCentered_le_env hE ht u k)

end Envelope

/-! ### The pointwise parameters `B` and `ε`

The moment bound of `RBM1D/Gauss/FlucCount.lean` is stated for *pointwise-uniform* parameters `B` (a
bound on every factor `Z_k` and every replaced factor `Z^{(κ)}_k`) and `ε` (a bound on the
replacement error).  The minor replacement (4.9) instead gives `≺ Ψ²`, a bound on a
high-probability event.  `RBM.Gauss.FlucBound` packages the pointwise parameters; the *only*
unconditional instance is the deterministic envelope one, `RBM.Gauss.flucBound_env`, and the module
docstring explains why no indicator/truncation argument can do better at this interface. -/

/-- The three uniform bounds of `RBM1D/Gauss/FlucCount.lean`, packaged. -/
structure FlucBound (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (B ε : ℝ) : Prop where
  /-- `B` is nonnegative. -/
  B_nonneg : 0 ≤ B
  /-- `ε` is nonnegative. -/
  eps_nonneg : 0 ≤ ε
  /-- Every factor `Z_k` is bounded by `B`, for every `ω`. -/
  flucDiag_le : ∀ (k : d.Idx N) (ω : Ω d), ‖flucDiag d N u z m k ω‖ ≤ B
  /-- Every replaced factor `Z^{(κ)}_k` is bounded by `B`, for every `ω`. -/
  flucDiagMinor_le : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}) (ω : Ω d),
    ‖flucDiagMinor d N u z m κ k ω‖ ≤ B
  /-- The replacement `Z_k ↦ Z^{(κ)}_k` costs at most `ε`, for every `ω`. -/
  repl_le : ∀ (κ : d.Idx N) (k : {a : d.Idx N // a ≠ κ}) (ω : Ω d),
    ‖flucDiag d N u z m k.1 ω - flucDiagMinor d N u z m κ k ω‖ ≤ ε

section EnvParams

open scoped Matrix.Norms.L2Operator

variable {E t : ℝ}

/-- **The seam, closed the only way it can be closed unconditionally.**  Pointwise parameters
`B` and `ε` really do exist: the deterministic envelope `‖G_t‖ ≤ η_t⁻¹` of `Envelope.lean` holds
for *every* `ω`, with no exceptional set, and it survives the `(1 - E_k)` (factor `2`,
`RBM.Gauss.norm_sub_condRow_le`) and the minor replacement (`G` and `G^{(κ)}` are resolvents of
two Hermitian matrices, so their difference is at most `2 η_t⁻¹`).

The resulting parameters are `B = 2(η_t⁻¹ + 1)` and `ε = 4 η_t⁻¹`: finite and explicit, but of
size `η_t⁻¹`, not of size `Ψ`.  See the module docstring for why the `≺`-sized parameters are
*not* obtainable by truncation at this interface. -/
theorem flucBound_env (hE : |E| < 2) (ht : t < 1) (d : Dims) (N : ℕ) (u : ℝ) :
    FlucBound d N u (zt E t) (mE E) (2 * ((etaT E t)⁻¹ + 1)) (4 * (etaT E t)⁻¹) := by
  have hη : 0 < etaT E t := etaT_pos_of_lt_one hE ht
  refine ⟨by positivity, by positivity, fun k ω => ?_, fun κ k ω => ?_, fun κ k ω => ?_⟩
  · exact norm_flucDiag_le (norm_greenDiagCentered_le_env hE ht u k) ω
  · exact norm_flucDiagMinor_le (norm_greenMinorDiagCentered_le_env hE ht u k) ω
  · have he : ∀ ω' : Ω d, ‖green (Hflow d N u ω') (zt E t) k.1 k.1
        - greenMinorMat d N u (zt E t) κ ω' k k‖ ≤ 2 * (etaT E t)⁻¹ := by
      intro ω'
      refine le_trans (norm_sub_le _ _) ?_
      have h1 := norm_green_apply_le_etaT hE ht u k.1 k.1 ω'
      have h2 := norm_greenMinorMat_apply_le_etaT hE ht u k k ω'
      linarith
    have := norm_flucDiag_sub_flucDiagMinor_le (u := u) (z := zt E t) (m := mE E)
      (κ := κ) (k := k) (rowIntegrable_greenDiagCentered hE ht u k.1)
      (rowIntegrable_greenMinorDiagCentered hE ht u k k.1) he ω
    linarith

end EnvParams

/-! ### The moment bound in the assembled form -/

section Moment

variable {u : ℝ} {z m : ℂ} {p : ℕ} {T : d.Idx N → ℝ}

theorem measurable_flucAvg (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (T : d.Idx N → ℝ) :
    Measurable (flucAvg d N u z m T) :=
  Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_flucDiag d N u z m k)

/-- `‖∑_k t_k Z_k‖ ≤ (∑_k |t_k|) B`. -/
theorem norm_flucAvg_le {B : ℝ} (hB : ∀ (k : d.Idx N) (ω : Ω d), ‖flucDiag d N u z m k ω‖ ≤ B)
    (ω : Ω d) : ‖flucAvg d N u z m T ω‖ ≤ (∑ k, |T k|) * B := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (Classical.arbitrary _) ω)
  calc ‖flucAvg d N u z m T ω‖ ≤ ∑ k, ‖(T k : ℂ) * flucDiag d N u z m k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, |T k| * B := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hB k ω) (abs_nonneg _)
    _ = (∑ k, |T k|) * B := by rw [Finset.sum_mul]

theorem integrable_norm_flucAvg_pow {B : ℝ}
    (hB : ∀ (k : d.Idx N) (ω : Ω d), ‖flucDiag d N u z m k ω‖ ≤ B) (p : ℕ) :
    Integrable (fun ω => |‖flucAvg d N u z m T ω‖| ^ (2 * p)) (P d) := by
  have hrw : (fun ω => |‖flucAvg d N u z m T ω‖| ^ (2 * p))
      = fun ω => ‖flucAvg d N u z m T ω‖ ^ (2 * p) := by
    funext ω; rw [abs_norm]
  rw [hrw]
  refine Integrable.mono' (integrable_const (((∑ k, |T k|) * B) ^ (2 * p)))
    (((measurable_flucAvg d N u z m T).norm.pow_const (2 * p)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h0 : (0 : ℝ) ≤ ∑ k, |T k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (Classical.arbitrary _) ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_flucAvg_le hB ω) _

end Moment

/-! ### From moments to `≺`: (4.12) -/

section Dom

variable {E t : ℝ}

end Dom

/-! ### The two coefficient families of (4.12)

`t_k = W⁻¹ 1(k ∈ I_a)` (`RBM.blkCoef`) and `t_k = S_{ik}` (`RBM.Sblk`).  Both are uniform
weights (`RBM1D/Gauss/FlucCount.lean`); here the index sets are counted and the polynomial
cardinality bound of Definition 2.1 (i) is supplied from the model's own `dim` and `bandwidth`
fields. -/

section Families

/-- `W(N) → ∞`, from (2.2). -/
theorem tendsto_W (d : Dims) : Tendsto (fun N => (d.W N : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop d.bandwidth
    ((tendsto_rpow_atTop (by linarith [d.c_pos])).comp tendsto_natCast_atTop_atTop)

/-- Every `p` is eventually below `W(N)`. -/
theorem eventually_le_W (d : Dims) (p : ℕ) : ∀ᶠ N : ℕ in atTop, p ≤ d.W N := by
  filter_upwards [(tendsto_W d).eventually_ge_atTop (p : ℝ)] with N hN
  exact_mod_cast hN

/-- `#(ZMod L(N)) ≤ N` eventually. -/
theorem card_ZMod_L_le (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (ZMod (d.L N)) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
  filter_upwards [d.dim] with N hN
  rw [Real.rpow_one, ZMod.card]
  have hW : 1 ≤ d.W N := d.W_pos N
  have : d.L N ≤ d.W N * d.L N := Nat.le_mul_of_pos_left _ (d.W_pos N)
  exact_mod_cast this.trans hN.1

/-- `#(Idx d N) ≤ N` eventually. -/
theorem card_Idx_le (d : Dims) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := by
  filter_upwards [d.dim] with N hN
  rw [Real.rpow_one]
  have hcard : Fintype.card (d.Idx N) = d.L N * d.W N := by
    rw [Fintype.card_prod, ZMod.card, Fintype.card_fin]
  rw [hcard]
  have : d.L N * d.W N = d.W N * d.L N := Nat.mul_comm _ _
  exact_mod_cast this ▸ hN.1

/-- The block average `t_k = W⁻¹ 1(k ∈ I_a)` of (4.12) is a uniform weight on a set of `W`
elements. -/
theorem card_blockAvg_support (d : Dims) (N : ℕ) (a : ZMod (d.L N)) :
    ((univ : Finset (d.Idx N)).filter fun k => k.1 = a).card = d.W N := by
  simpa using card_filter_fst_mem (d := d) (N := N) {a}

/-- The variance-profile row `t_k = S_{ik}` of (4.12) is a uniform weight on a set of `3W`
elements. -/
theorem card_Sblk_support (d : Dims) (N : ℕ) (i : d.Idx N) :
    ((univ : Finset (d.Idx N)).filter
      fun j => i.1 - j.1 ∈ sbSupport (d.L N)).card = 3 * d.W N := by
  classical
  have hset : ((univ : Finset (d.Idx N)).filter fun j => i.1 - j.1 ∈ sbSupport (d.L N))
      = (univ : Finset (d.Idx N)).filter
          fun j => j.1 ∈ (univ : Finset (ZMod (d.L N))).filter
            fun b => i.1 - b ∈ sbSupport (d.L N) := by
    ext j; simp
  rw [hset, card_filter_fst_mem, card_filter_sub_mem_sbSupport]

variable {E t : ℝ}

end Families

/-! ### (4.5) -/

section Avg

/-- `E_k(G_{kk} - m)`, the quantity called `x` in `RBM1D/Green/EntryBound.lean`. -/
noncomputable def condExpDiag (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ) (k : d.Idx N) : Ω d → ℂ :=
  condRow d N k (greenDiagCentered d N u z m k)

variable {E κ t : ℝ}

/-- **(4.5), deterministic form, with `hFA` discharged.**  The hypothesis `hFA` of
`RBM.norm_sum_coef_green_sub_le` — `‖∑_k S_{ik}((G_{kk} - m) - x_k)‖ ≤ B` with `x_k` the
conditional expectation — *is* a bound on `RBM.Gauss.flucAvg`, i.e. it is exactly what (4.12)
supplies; likewise `hFA'` for the second coefficient family.  Here `x` is instantiated at
`RBM.Gauss.condExpDiag`, after which `hFA`, `hFA'` *are* the two (4.12) bounds.  Only `hIBP` is left
as an unproved input. -/
theorem norm_trace_green_sub_mul_Eblk_le_flucAvg (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hE : |E| ≤ 2 - κ) (ht0 : 0 ≤ t) (ht1 : t < 1) (u : ℝ) (ω : Ω d) {A B B' : ℝ}
    (hIBP : ∀ i : d.Idx N, ‖condExpDiag d N u (zt E t) (mE E) i ω
      - (t : ℂ) * mE E ^ 2 * ∑ k, (Sblk (d.L N) (d.W N) i k : ℂ)
        * (green (Hflow d N u ω) (zt E t) k k - mE E)‖ ≤ A)
    (hFArow : ∀ i : d.Idx N,
      ‖flucAvg d N u (zt E t) (mE E) (fun j => Sblk (d.L N) (d.W N) i j) ω‖ ≤ B)
    (a : ZMod (d.L N))
    (hFAblk : ‖flucAvg d N u (zt E t) (mE E) (blkCoef (d.L N) (d.W N) a) ω‖ ≤ B') :
    ‖Matrix.trace ((green (Hflow d N u ω) (zt E t)
        - mE E • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)) * Eblk (d.L N) (d.W N) a)‖
      ≤ B' + Kstab κ * (A + B) :=
  norm_trace_green_sub_mul_Eblk_le (d.three_le_L N) hκ0 hκ1 hE ht0 ht1
    (green (Hflow d N u ω) (zt E t)) (fun k => condExpDiag d N u (zt E t) (mE E) k ω)
    hIBP hFArow a hFAblk

end Avg

end RBM.Gauss

