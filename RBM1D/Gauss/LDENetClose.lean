/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.LDEFlow
import RBM1D.Gauss.Step1Hyp

/-!
# (4.2) along the flow: the deterministic modulus, and why `LDENetClose` needs a floor

`RBM.Gauss.LDENetClose` (`RBM1D/Gauss/LDEFlow.lean`, T143) is the one input left of
`RBM.Gauss.ldeFlowDom_of_close`, hence of `RBM.LKDecayQuant.LDEFlowDom`, hence of
`RBM.SumZeroDyn.LKDecay`.  It asks, at net spacing `δ_N` and on a high-probability event,

* `ξ(u) ≤ ξ(v) + ζ(u)`, and
* `ζ(v) ≤ 2 ζ(u)`,

for the two sides `ξ = ldeRowLHS`, `ζ = ldeRowRHS` of (4.2) (and their column companions).

## What is proved here

**The deterministic modulus is a theorem, unconditionally.**  Along the Gaussian flow
`H_u = √u X` at the moving spectral parameter `z_u`, both sides of (4.2) are Hölder-`1/2` in
the time with a *polynomial* constant:

`RBM.Gauss.abs_ldeRow_flow_sub_le`, `RBM.Gauss.abs_ldeCol_flow_sub_le` —
`|ξ(u) - ξ(v)| ≤ 6 R^{10} (|√u-√v| + |u-v|)` and the same for `ζ`, where `R` bounds
`η_u⁻¹`, `|Idx|` and `‖X‖`.

The chain is entirely entrywise.  `ζ` and `ξ` are built from the *minor* resolvent
`G^{(i)}(u) = (H_u^{(i)} - z_u)⁻¹`, a resolvent of a principal submatrix, and the repository
has no bound on the `ℓ²→ℓ²` operator norm of a submatrix; so the resolvent identity is used in
the entrywise form `RBM.Gauss.norm_green_sub_apply_le_of_entries`, at the cost of two extra
factors of `|Idx|`, which are harmless.

**Hence (4.2), uniformly in `u`, with an additive floor, and with no probabilistic input left:**

`RBM.Gauss.stochDom_ldeRow_flow_floor`, `RBM.Gauss.stochDom_ldeCol_flow_floor`,
`RBM.Gauss.ldeFlowDom_floor` — for every `B ≥ 0`,

`ldeRowLHS(u) ≺ ldeRowRHS(u) + N^{-B}` uniformly in `u ∈ [s_N, t_N]` and in the off-diagonal
pair.

The net spacing is taken as `δ_N = (N^{-(10K+12+B)})²`, which makes the modulus fall below the
floor (`RBM.Gauss.eventually_mod_le_floor`); the high-probability event is `{‖X‖ ≤ N}`
(`RBM.Gauss.highProb_norm_Xmat_le`, T109, unconditional); the fixed-time input is the
unconditional `RBM.Gauss.unifDomIcc_ldeRow`/`_ldeCol` of T143, relaxed to the floored control
by `RBM.Gauss.UnifDomIcc.mono_control`.  The only extra hypothesis is the regime bound
`N^{-K} ≤ η_{t_N}`, which is deterministic.

## Why `LDENetClose` itself is *not* discharged

`RBM.Gauss.ldeNetClose_of_lower_bound` isolates exactly what is missing: given the modulus
above, `LDENetClose` is equivalent to a **polynomial lower bound on the control**,
`N^{-B} ≤ ζ(u)`, uniform in `u` and in the pair `(i, j)`.

That lower bound is false.  `ζ(u) = ∑_{k ∈ band(i)} S_{ik} |G^{(i)}_{kj}(u)|²` is
*exponentially* small in the band distance between `i` and `j` — that is the content of the
decay estimate (2.76)/(4.3) — so no `N^{-B}` bounds it below uniformly in the pair.  Nor can
the floor be absorbed by `RBM.StochDom.of_highProb_add_rpow_neg` (T135): that absorption lemma
needs the same polynomial lower bound on the control.

The remaining route, sketched in T143's note, is the *relative* modulus
`‖∂_u ĉ(u)‖ ≤ N^K ‖ĉ(u)‖` for the band-restricted minor Green column `ĉ`.  The resolvent
derivative gives this in the **full** norm, and converting it to the band-restricted one needs
the minor off-diagonal decay; but even with that decay in hand the conversion needs a matching
*lower* bound on `‖ĉ(u)‖`, uniformly in `u` — an anti-concentration statement for
`u ↦ G^{(i)}_{·j}(u)` that neither the repository nor the paper provides (the paper's continuity
step here is implicit; see `docs/paper-deltas.md`).  It is **not** a missing Gaussian-process
tool: the union bound over a polynomial net already beats the Gaussian tail `e^{-N^{2τ}}`, so
Dudley / generic chaining is not needed.

What the consumer would need in order to use the floored form is `RBM.LKDecayQuant.LDEFlowDom`
restated with `+ N^{-B}` in the control (a `RBM1D/Hierarchy/` change, not made here).
-/

namespace RBM.Gauss

open MeasureTheory Filter Finset Matrix

open scoped Matrix.Norms.L2Operator

/-! ### An entrywise form of the resolvent identity -/

section MatrixEntry

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- `|(A Δ B)_{ab}| ≤ M² ∑_{c,e} |Δ_{ce}|` when every entry of `A` and of `B` is at most `M`.
The entrywise counterpart of `‖A Δ B‖ ≤ ‖A‖ ‖Δ‖ ‖B‖`; it is used instead of the operator-norm
form because the flow's Hölder constant is needed for a *principal submatrix*, and the
`ℓ² → ℓ²` operator norm of a submatrix is not available in this repository. -/
theorem norm_mul_mul_apply_le_of_entries (A Δ B : Matrix n n ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ a b, ‖A a b‖ ≤ M) (hB : ∀ a b, ‖B a b‖ ≤ M) (a b : n) :
    ‖(A * Δ * B) a b‖ ≤ M ^ 2 * ∑ e, ∑ c, ‖Δ c e‖ := by
  have hrow : ∀ e : n, ‖(A * Δ) a e‖ ≤ ∑ c, M * ‖Δ c e‖ := by
    intro e
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA a c) (norm_nonneg _)
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ e : n, ‖(A * Δ) a e * B e b‖ ≤ (∑ c, M * ‖Δ c e‖) * M := by
    intro e
    rw [norm_mul]
    exact mul_le_mul (hrow e) (hB e b) (norm_nonneg _)
      (Finset.sum_nonneg fun c _ => mul_nonneg hM (norm_nonneg _))
  refine (Finset.sum_le_sum fun e _ => hstep e).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => le_of_eq ?_
  rw [← Finset.mul_sum]
  ring

/-- **The entrywise resolvent identity.**  If every entry of `G = (H-z)⁻¹` and of
`G' = (H'-z')⁻¹` is at most `M`, and every entry of `H - H'` is at most `Δb`, then

`|G_{ab} - G'_{ab}| ≤ M² · |n|² · (Δb + |z - z'|)`.

The extra `|n|²` compared with the operator-norm form `‖G - G'‖ ≤ ‖G‖(‖H-H'‖+|z-z'|)‖G'‖` is
the price of working entrywise; it is harmless, because everything downstream only needs
polynomial constants. -/
theorem norm_green_sub_apply_le_of_entries {H H' : Matrix n n ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {M : ℝ} (hM : 0 ≤ M)
    (hG : ∀ a b, ‖green H z a b‖ ≤ M) (hG' : ∀ a b, ‖green H' z' a b‖ ≤ M)
    {Δb : ℝ} (hΔ : ∀ c e, ‖H c e - H' c e‖ ≤ Δb) (a b : n) :
    ‖green H z a b - green H' z' a b‖
      ≤ M ^ 2 * ((Fintype.card n : ℝ) ^ 2 * (Δb + ‖z - z'‖)) := by
  have hdu : IsUnit (H - z • (1 : Matrix n n ℂ)).det := isUnit_det_sub_smul_one hH hz
  have hdv : IsUnit (H' - z' • (1 : Matrix n n ℂ)).det := isUnit_det_sub_smul_one hH' hz'
  set Δ : Matrix n n ℂ :=
    (H' - z' • (1 : Matrix n n ℂ)) - (H - z • (1 : Matrix n n ℂ)) with hΔdef
  have hentry : ∀ c e : n, ‖Δ c e‖ ≤ Δb + ‖z - z'‖ := by
    intro c e
    have hce : Δ c e = (H' c e - H c e) + (z - z') * (if c = e then (1 : ℂ) else 0) := by
      simp only [hΔdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      ring
    rw [hce]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖H' c e - H c e‖ ≤ Δb := by
      rw [norm_sub_rev]; exact hΔ c e
    have h2 : ‖(z - z') * (if c = e then (1 : ℂ) else 0)‖ ≤ ‖z - z'‖ := by
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      split_ifs <;> simp
    linarith
  have hsum : ∑ e : n, ∑ c : n, ‖Δ c e‖ ≤ (Fintype.card n : ℝ) ^ 2 * (Δb + ‖z - z'‖) := by
    calc ∑ e : n, ∑ c : n, ‖Δ c e‖
        ≤ ∑ _e : n, ∑ _c : n, (Δb + ‖z - z'‖) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun c _ => hentry c e
      _ = (Fintype.card n : ℝ) ^ 2 * (Δb + ‖z - z'‖) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hmul : green H z - green H' z' = green H z * Δ * green H' z' := green_sub_eq hdu hdv
  rw [← Matrix.sub_apply, hmul]
  refine (norm_mul_mul_apply_le_of_entries (green H z) Δ (green H' z') hM hG hG' a b).trans ?_
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end MatrixEntry

/-! ### The modulus of the minor resolvent along the flow -/

section MinorFlow

variable {d : Dims} {N : ℕ} {E : ℝ}

/-- **The minor resolvent of the flow moves by a polynomial constant times `|u-v|^{1/2}`.**

`G^{(i)}(u) = (H_u^{(i)} - z_u)⁻¹` is the resolvent of a principal submatrix of `H_u`, and both
the matrix and the spectral parameter move: `‖H_u - H_v‖_max = |√u-√v| ‖X‖_max` and
`|z_u - z_v| = |u-v|`.  Entrywise,

`|G^{(i)}_{ab}(u) - G^{(i)}_{ab}(v)| ≤ M² |Idx|² (‖X‖+1) (|√u-√v| + |u-v|)`,

where `M` bounds `η_u⁻¹` and `η_v⁻¹`. -/
theorem norm_greenMinorMat_flow_sub_apply_le (d : Dims) (N : ℕ) (hE : |E| < 2)
    {u v M : ℝ} (hu1 : u < 1) (hv1 : v < 1) (hMu : (etaT E u)⁻¹ ≤ M) (hMv : (etaT E v)⁻¹ ≤ M)
    (ω : Ω d) (i : d.Idx N) (a b : {k : d.Idx N // k ≠ i}) :
    ‖greenMinorMat d N u (zt E u) i ω a b - greenMinorMat d N v (zt E v) i ω a b‖
      ≤ M ^ 2 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1))
          * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hηv : 0 < etaT E v := etaT_pos_of_lt_one' hE hv1
  have hM0 : (0 : ℝ) ≤ M := le_trans (inv_nonneg.2 hηu.le) hMu
  have hzu : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hηu.ne'
  have hzv : (zt E v).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hηv.ne'
  have habs1 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| := abs_nonneg _
  have habs2 : (0 : ℝ) ≤ |u - v| := abs_nonneg _
  have hXn : (0 : ℝ) ≤ ‖Xmat d N ω‖ := norm_nonneg _
  rw [greenMinorMat_eq_green_submatrix, greenMinorMat_eq_green_submatrix]
  have key := norm_green_sub_apply_le_of_entries
      ((Hflow_isHermitian d N u ω).submatrix
        (Subtype.val : {k : d.Idx N // k ≠ i} → d.Idx N))
      ((Hflow_isHermitian d N v ω).submatrix
        (Subtype.val : {k : d.Idx N // k ≠ i} → d.Idx N))
      hzu hzv hM0
      (fun a b => le_trans (norm_greenMinorMat_apply_le_etaT hE hu1 u a b ω) hMu)
      (fun a b => le_trans (norm_greenMinorMat_apply_le_etaT hE hv1 v a b ω) hMv)
      (Δb := |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖) ?_ a b
  · rw [norm_zt_sub hE.le] at key
    refine key.trans ?_
    set cs : ℝ := (Fintype.card {k : d.Idx N // k ≠ i} : ℝ) with hcs
    set nn : ℝ := (Fintype.card (d.Idx N) : ℝ) with hnn
    have hcard : cs ≤ nn := by
      rw [hcs, hnn]; exact_mod_cast Fintype.card_subtype_le _
    have hcs0 : (0 : ℝ) ≤ cs := by rw [hcs]; exact Nat.cast_nonneg _
    have h1 : cs ^ 2 ≤ nn ^ 2 := by nlinarith
    have h2 : |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v|
        ≤ (‖Xmat d N ω‖ + 1) * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by nlinarith
    have h3 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v| := by positivity
    calc M ^ 2 * (cs ^ 2 * (|Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ + |u - v|))
        ≤ M ^ 2 * (nn ^ 2 * ((‖Xmat d N ω‖ + 1)
            * (|Real.sqrt u - Real.sqrt v| + |u - v|))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (mul_le_mul_of_nonneg_right h1 h3)
            (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = M ^ 2 * (nn ^ 2 * (‖Xmat d N ω‖ + 1))
            * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by ring
  · intro c e
    have h1 : ((Hflow d N u ω).submatrix (Subtype.val : {k : d.Idx N // k ≠ i} → d.Idx N)
          (Subtype.val : {k : d.Idx N // k ≠ i} → d.Idx N)) c e
        - ((Hflow d N v ω).submatrix (Subtype.val : {k : d.Idx N // k ≠ i} → d.Idx N)
          (Subtype.val : {k : d.Idx N // k ≠ i} → d.Idx N)) c e
        = (Hflow d N u ω - Hflow d N v ω) c.1 e.1 := by
      simp only [Matrix.submatrix_apply, Matrix.sub_apply]
    rw [h1, norm_Hflow_sub_apply]
    exact mul_le_mul_of_nonneg_left (norm_entry_le_l2_opNorm _ _ _) habs1

/-! ### The two coefficient families of (4.2) -/

/-- `minorCol` is the `(k, j)` entry of the minor resolvent. -/
theorem minorCol_eq_greenMinorMat (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (i : d.Idx N)
    (j : {a : d.Idx N // a ≠ i}) (ω : Ω d) {k : d.Idx N} (hk : k ≠ i) :
    minorCol d N u z i j ω k = greenMinorMat d N u z i ω ⟨k, hk⟩ j := by
  unfold minorCol greenMinorMat
  rw [dite_eq_left_of_eq_true (by simpa using hk)]

/-- `minorRowConj` is the conjugate of the `(k, l)` entry of the minor resolvent. -/
theorem minorRowConj_eq_greenMinorMat (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ) (j : d.Idx N)
    (k : {a : d.Idx N // a ≠ j}) (ω : Ω d) {l : d.Idx N} (hl : l ≠ j) :
    minorRowConj d N u z j k ω l
      = (starRingEnd ℂ) (greenMinorMat d N u z j ω k ⟨l, hl⟩) := by
  unfold minorRowConj greenMinorMat
  rw [dite_eq_left_of_eq_true (by simpa using hl)]

/-- The entries of `minorCol` are bounded by `M` whenever `η_u⁻¹ ≤ M`. -/
theorem norm_minorCol_le (d : Dims) (N : ℕ) (hE : |E| < 2) {u M : ℝ} (hu1 : u < 1)
    (hMu : (etaT E u)⁻¹ ≤ M) (ω : Ω d) (i : d.Idx N) (j : {a : d.Idx N // a ≠ i})
    (k : d.Idx N) : ‖minorCol d N u (zt E u) i j ω k‖ ≤ M := by
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hM0 : (0 : ℝ) ≤ M := le_trans (inv_nonneg.2 hηu.le) hMu
  by_cases hk : k = i
  · rw [show minorCol d N u (zt E u) i j ω k = 0 from by simp [minorCol, hk], norm_zero]
    exact hM0
  · rw [minorCol_eq_greenMinorMat d N u (zt E u) i j ω hk]
    exact le_trans (norm_greenMinorMat_apply_le_etaT hE hu1 u _ _ ω) hMu

/-- The entries of `minorRowConj` are bounded by `M` whenever `η_u⁻¹ ≤ M`. -/
theorem norm_minorRowConj_le (d : Dims) (N : ℕ) (hE : |E| < 2) {u M : ℝ} (hu1 : u < 1)
    (hMu : (etaT E u)⁻¹ ≤ M) (ω : Ω d) (j : d.Idx N) (k : {a : d.Idx N // a ≠ j})
    (l : d.Idx N) : ‖minorRowConj d N u (zt E u) j k ω l‖ ≤ M := by
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hM0 : (0 : ℝ) ≤ M := le_trans (inv_nonneg.2 hηu.le) hMu
  by_cases hl : l = j
  · rw [show minorRowConj d N u (zt E u) j k ω l = 0 from by simp [minorRowConj, hl], norm_zero]
    exact hM0
  · rw [minorRowConj_eq_greenMinorMat d N u (zt E u) j k ω hl, Complex.norm_conj]
    exact le_trans (norm_greenMinorMat_apply_le_etaT hE hu1 u _ _ ω) hMu

/-- The modulus of continuity in `u` of `minorCol`. -/
theorem norm_minorCol_flow_sub_le (d : Dims) (N : ℕ) (hE : |E| < 2) {u v M : ℝ}
    (hu1 : u < 1) (hv1 : v < 1) (hMu : (etaT E u)⁻¹ ≤ M) (hMv : (etaT E v)⁻¹ ≤ M)
    (ω : Ω d) (i : d.Idx N) (j : {a : d.Idx N // a ≠ i}) (k : d.Idx N) :
    ‖minorCol d N u (zt E u) i j ω k - minorCol d N v (zt E v) i j ω k‖
      ≤ M ^ 2 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1))
          * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hM0 : (0 : ℝ) ≤ M := le_trans (inv_nonneg.2 hηu.le) hMu
  by_cases hk : k = i
  · have h0 : minorCol d N u (zt E u) i j ω k = 0 := by simp [minorCol, hk]
    have h0' : minorCol d N v (zt E v) i j ω k = 0 := by simp [minorCol, hk]
    rw [h0, h0', sub_zero, norm_zero]
    positivity
  · rw [minorCol_eq_greenMinorMat d N u (zt E u) i j ω hk,
      minorCol_eq_greenMinorMat d N v (zt E v) i j ω hk]
    exact norm_greenMinorMat_flow_sub_apply_le d N hE hu1 hv1 hMu hMv ω i _ _

/-- The modulus of continuity in `u` of `minorRowConj`. -/
theorem norm_minorRowConj_flow_sub_le (d : Dims) (N : ℕ) (hE : |E| < 2) {u v M : ℝ}
    (hu1 : u < 1) (hv1 : v < 1) (hMu : (etaT E u)⁻¹ ≤ M) (hMv : (etaT E v)⁻¹ ≤ M)
    (ω : Ω d) (j : d.Idx N) (k : {a : d.Idx N // a ≠ j}) (l : d.Idx N) :
    ‖minorRowConj d N u (zt E u) j k ω l - minorRowConj d N v (zt E v) j k ω l‖
      ≤ M ^ 2 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1))
          * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hM0 : (0 : ℝ) ≤ M := le_trans (inv_nonneg.2 hηu.le) hMu
  by_cases hl : l = j
  · have h0 : minorRowConj d N u (zt E u) j k ω l = 0 := by simp [minorRowConj, hl]
    have h0' : minorRowConj d N v (zt E v) j k ω l = 0 := by simp [minorRowConj, hl]
    rw [h0, h0', sub_zero, norm_zero]
    positivity
  · rw [minorRowConj_eq_greenMinorMat d N u (zt E u) j k ω hl,
      minorRowConj_eq_greenMinorMat d N v (zt E v) j k ω hl, ← map_sub, Complex.norm_conj]
    exact norm_greenMinorMat_flow_sub_apply_le d N hE hu1 hv1 hMu hMv ω j _ _

end MinorFlow

/-! ### The two sides of (4.2) as functions of the coefficient vector -/

section Sides

variable {d : Dims} {N : ℕ} {E : ℝ}

/-- The `S`-weighted band norm of a coefficient vector: the right-hand side of (4.2). -/
noncomputable def sWeight (d : Dims) (N : ℕ) (i : d.Idx N) (c : d.Idx N → ℂ) : ℝ :=
  ∑ k : {k : d.Idx N // k ≠ i}, Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2

/-- The row sum with *frozen* coefficients; the left-hand side of (4.2) is its squared norm. -/
noncomputable def rowLin (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (c : d.Idx N → ℂ)
    (ω : Ω d) : ℂ :=
  ∑ k : {k : d.Idx N // k ≠ i}, Hflow d N u ω i k.1 * c k.1

theorem rowSum_eq_rowLin (d : Dims) (N : ℕ) (u : ℝ) (i : d.Idx N) (C : Ω d → d.Idx N → ℂ)
    (ω : Ω d) : rowSum d N u i C ω = rowLin d N u i (C ω) ω := rfl

/-- A sum over the `|Idx| - 1` off-diagonal indices, bounded termwise. -/
theorem sum_subtype_ne_le (d : Dims) (N : ℕ) (i : d.Idx N) (f : {k : d.Idx N // k ≠ i} → ℝ)
    {b : ℝ} (hb : 0 ≤ b) (hf : ∀ k, f k ≤ b) :
    ∑ k : {k : d.Idx N // k ≠ i}, f k ≤ (Fintype.card (d.Idx N) : ℝ) * b := by
  calc ∑ k : {k : d.Idx N // k ≠ i}, f k
      ≤ ∑ _k : {k : d.Idx N // k ≠ i}, b := Finset.sum_le_sum fun k _ => hf k
    _ = (Fintype.card {k : d.Idx N // k ≠ i} : ℝ) * b := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card (d.Idx N) : ℝ) * b := by
        refine mul_le_mul_of_nonneg_right ?_ hb
        exact_mod_cast Fintype.card_subtype_le _

/-- `S^{(B)}_{ij}/W ≤ 1`. -/
theorem Sblk_le_one (d : Dims) (N : ℕ) (i j : d.Idx N) :
    Sblk (d.L N) (d.W N) i j ≤ 1 := by
  have hW : (1 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  have h1 := sbKre_le (L := d.L N) (i.1 - j.1)
  have h2 := sbKre_nonneg (L := d.L N) (i.1 - j.1)
  unfold Sblk
  rw [div_le_one (by linarith)]
  linarith

theorem abs_norm_sq_sub_le (z w : ℂ) : |‖z‖ ^ 2 - ‖w‖ ^ 2| ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have h : ‖z‖ ^ 2 - ‖w‖ ^ 2 = (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) := by ring
  rw [h, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ + ‖w‖), mul_comm]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le z w) (by positivity)

theorem norm_Hflow_apply_le_opNorm (d : Dims) (N : ℕ) {u : ℝ} (hu1 : u ≤ 1) (ω : Ω d)
    (i k : d.Idx N) : ‖Hflow d N u ω i k‖ ≤ ‖Xmat d N ω‖ := by
  have h : Hflow d N u ω i k = (Real.sqrt u : ℂ) * Xmat d N ω i k := rfl
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u)]
  calc Real.sqrt u * ‖Xmat d N ω i k‖
      ≤ 1 * ‖Xmat d N ω i k‖ :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_one.2 hu1) (norm_nonneg _)
    _ = ‖Xmat d N ω i k‖ := one_mul _
    _ ≤ ‖Xmat d N ω‖ := norm_entry_le_l2_opNorm _ _ _

/-- **The control of (4.2) is Lipschitz in the coefficient vector.** -/
theorem abs_sWeight_sub_le (d : Dims) (N : ℕ) (i : d.Idx N) (c c' : d.Idx N → ℂ) {M Δ : ℝ}
    (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hc : ∀ k, ‖c k‖ ≤ M) (hc' : ∀ k, ‖c' k‖ ≤ M)
    (hd : ∀ k, ‖c k - c' k‖ ≤ Δ) :
    |sWeight d N i c - sWeight d N i c'| ≤ (Fintype.card (d.Idx N) : ℝ) * (2 * M * Δ) := by
  have hterm : ∀ k : {k : d.Idx N // k ≠ i},
      |Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2
        - Sblk (d.L N) (d.W N) i k.1 * ‖c' k.1‖ ^ 2| ≤ 2 * M * Δ := by
    intro k
    rw [← mul_sub, abs_mul, abs_of_nonneg (Sblk_nonneg _ _)]
    have h1 : |‖c k.1‖ ^ 2 - ‖c' k.1‖ ^ 2| ≤ 2 * M * Δ := by
      refine (abs_norm_sq_sub_le (c k.1) (c' k.1)).trans ?_
      exact mul_le_mul (by linarith [hc k.1, hc' k.1]) (hd k.1) (norm_nonneg _) (by linarith)
    calc Sblk (d.L N) (d.W N) i k.1 * |‖c k.1‖ ^ 2 - ‖c' k.1‖ ^ 2|
        ≤ 1 * (2 * M * Δ) :=
          mul_le_mul (Sblk_le_one d N i k.1) h1 (abs_nonneg _) zero_le_one
      _ = 2 * M * Δ := one_mul _
  have heq : sWeight d N i c - sWeight d N i c'
      = ∑ k : {k : d.Idx N // k ≠ i}, (Sblk (d.L N) (d.W N) i k.1 * ‖c k.1‖ ^ 2
          - Sblk (d.L N) (d.W N) i k.1 * ‖c' k.1‖ ^ 2) := by
    unfold sWeight; rw [← Finset.sum_sub_distrib]
  rw [heq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact sum_subtype_ne_le d N i _ (by positivity) hterm

/-- **The linear form of (4.2) is bounded by a polynomial constant.** -/
theorem norm_rowLin_le (d : Dims) (N : ℕ) {u : ℝ} (hu1 : u ≤ 1) (i : d.Idx N)
    (c : d.Idx N → ℂ) (ω : Ω d) {M : ℝ} (hM : 0 ≤ M) (hc : ∀ k, ‖c k‖ ≤ M) :
    ‖rowLin d N u i c ω‖ ≤ (Fintype.card (d.Idx N) : ℝ) * (‖Xmat d N ω‖ * M) := by
  refine (norm_sum_le _ _).trans (sum_subtype_ne_le d N i _ (by positivity) ?_)
  intro k
  rw [norm_mul]
  exact mul_le_mul (norm_Hflow_apply_le_opNorm d N hu1 ω i k.1) (hc k.1)
    (norm_nonneg _) (norm_nonneg _)

/-- **The linear form of (4.2) is jointly Lipschitz in the time and the coefficient vector.** -/
theorem norm_rowLin_sub_le (d : Dims) (N : ℕ) {u v : ℝ} (hv1 : v ≤ 1) (i : d.Idx N)
    (c c' : d.Idx N → ℂ) (ω : Ω d) {M Δ : ℝ} (hM : 0 ≤ M) (hΔ : 0 ≤ Δ)
    (hc : ∀ k, ‖c k‖ ≤ M) (hd : ∀ k, ‖c k - c' k‖ ≤ Δ) :
    ‖rowLin d N u i c ω - rowLin d N v i c' ω‖
      ≤ (Fintype.card (d.Idx N) : ℝ)
          * (‖Xmat d N ω‖ * (|Real.sqrt u - Real.sqrt v| * M + Δ)) := by
  have heq : rowLin d N u i c ω - rowLin d N v i c' ω
      = ∑ k : {k : d.Idx N // k ≠ i},
          (Hflow d N u ω i k.1 * c k.1 - Hflow d N v ω i k.1 * c' k.1) := by
    unfold rowLin; rw [← Finset.sum_sub_distrib]
  rw [heq]
  refine (norm_sum_le _ _).trans (sum_subtype_ne_le d N i _ (by positivity) ?_)
  intro k
  have hsplit : Hflow d N u ω i k.1 * c k.1 - Hflow d N v ω i k.1 * c' k.1
      = (Hflow d N u ω i k.1 - Hflow d N v ω i k.1) * c k.1
        + Hflow d N v ω i k.1 * (c k.1 - c' k.1) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have e1 : ‖Hflow d N u ω i k.1 - Hflow d N v ω i k.1‖
      ≤ |Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖ := by
    rw [← Matrix.sub_apply, norm_Hflow_sub_apply]
    exact mul_le_mul_of_nonneg_left (norm_entry_le_l2_opNorm _ _ _) (abs_nonneg _)
  have e2 : ‖Hflow d N v ω i k.1‖ ≤ ‖Xmat d N ω‖ :=
    norm_Hflow_apply_le_opNorm d N hv1 ω i k.1
  have p1 : ‖Hflow d N u ω i k.1 - Hflow d N v ω i k.1‖ * ‖c k.1‖
      ≤ (|Real.sqrt u - Real.sqrt v| * ‖Xmat d N ω‖) * M :=
    mul_le_mul e1 (hc k.1) (norm_nonneg _) (by positivity)
  have p2 : ‖Hflow d N v ω i k.1‖ * ‖c k.1 - c' k.1‖ ≤ ‖Xmat d N ω‖ * Δ :=
    mul_le_mul e2 (hd k.1) (norm_nonneg _) (norm_nonneg _)
  nlinarith [p1, p2]

/-! ### Identification with `ldeRowRHS` and `ldeColRHS` -/

variable {u : ℝ} {z : ℂ}

theorem sWeight_minorCol_eq (u : ℝ) {i : d.Idx N} (j : {a : d.Idx N // a ≠ i}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGii : green (Hflow d N u ω) z i i ≠ 0) :
    sWeight d N i (minorCol d N u z i j ω)
      = ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) i j.1 := by
  unfold sWeight ldeRowRHS
  rw [Finset.sum_subtype (p := fun k => k ≠ i) (Finset.univ.erase i)
    (fun k => by simp [Finset.mem_erase]) _]
  exact Finset.sum_congr rfl fun k _ =>
    by rw [minorCol_eq_greenMinor u j hdet hGii k.2]

theorem sWeight_minorRowConj_eq (u : ℝ) {j : d.Idx N} (k : {a : d.Idx N // a ≠ j}) {ω : Ω d}
    (hdet : IsUnit (Hflow d N u ω - z • (1 : Matrix (d.Idx N) (d.Idx N) ℂ)).det)
    (hGjj : green (Hflow d N u ω) z j j ≠ 0) :
    sWeight d N j (minorRowConj d N u z j k ω)
      = ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) z) k.1 j := by
  unfold sWeight ldeColRHS
  rw [Finset.sum_subtype (p := fun l => l ≠ j) (Finset.univ.erase j)
    (fun l => by simp [Finset.mem_erase]) _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [minorRowConj_eq_greenMinor u k hdet hGjj l.2, Complex.norm_conj,
    Sblk_comm (d.L N) (d.W N) j l.1]
  ring

end Sides

/-! ### The deterministic modulus of continuity of the two sides of (4.2) -/

section Modulus

variable {d : Dims} {N : ℕ} {E : ℝ}

/-- **Both sides of the row estimate (4.2) are Hölder-`1/2` in the time, with a constant that is
polynomial in `η_u⁻¹`, `|Idx|` and `‖X‖.`**

`R` is a common bound for `η_u⁻¹`, `η_v⁻¹`, `|Idx|` and `‖X‖`; the exponent `10` is not
optimised, only polynomial. -/
theorem abs_ldeRow_flow_sub_le (d : Dims) (N : ℕ) (hE : |E| < 2) {u v R : ℝ}
    (hu1 : u < 1) (hv1 : v < 1) (hR1 : 1 ≤ R)
    (hRu : (etaT E u)⁻¹ ≤ R) (hRv : (etaT E v)⁻¹ ≤ R)
    (hRn : (Fintype.card (d.Idx N) : ℝ) ≤ R) (ω : Ω d) (hRx : ‖Xmat d N ω‖ ≤ R)
    (i : d.Idx N) (j : {a : d.Idx N // a ≠ i}) :
    |ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt E u)) i j.1
        - ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N v ω) (zt E v)) i j.1|
        ≤ 6 * R ^ 10 * (|Real.sqrt u - Real.sqrt v| + |u - v|)
      ∧ |ldeRowLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt E u)) i j.1
        - ldeRowLHS (Hflow d N v ω) (green (Hflow d N v ω) (zt E v)) i j.1|
        ≤ 6 * R ^ 10 * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hR3 : (1 : ℝ) ≤ R ^ 3 := by nlinarith [sq_nonneg R, sq_nonneg (R - 1)]
  have hR7 : (0 : ℝ) ≤ R ^ 7 := by positivity
  have hpow : R ^ 7 ≤ R ^ 10 := by
    nlinarith [mul_le_mul_of_nonneg_left hR3 hR7]
  set ε : ℝ := |Real.sqrt u - Real.sqrt v| + |u - v| with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by rw [hεdef]; positivity
  have hzu : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact (etaT_pos_of_lt_one' hE hu1).ne'
  have hzv : (zt E v).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact (etaT_pos_of_lt_one' hE hv1).ne'
  set c : d.Idx N → ℂ := minorCol d N u (zt E u) i j ω with hc_def
  set c' : d.Idx N → ℂ := minorCol d N v (zt E v) i j ω with hc'_def
  have hcb : ∀ k, ‖c k‖ ≤ R := fun k => norm_minorCol_le d N hE hu1 hRu ω i j k
  have hcb' : ∀ k, ‖c' k‖ ≤ R := fun k => norm_minorCol_le d N hE hv1 hRv ω i j k
  have hdd : ∀ k, ‖c k - c' k‖ ≤ 2 * R ^ 5 * ε := by
    intro k
    refine (norm_minorCol_flow_sub_le d N hE hu1 hv1 hRu hRv ω i j k).trans ?_
    have h1 : (Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1) ≤ R ^ 2 * (2 * R) := by
      have h0 : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
      have hn2 : (Fintype.card (d.Idx N) : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith
      have hx1 : ‖Xmat d N ω‖ + 1 ≤ 2 * R := by linarith
      exact mul_le_mul hn2 hx1 (by positivity) (by positivity)
    calc R ^ 2 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1)) * ε
        ≤ R ^ 2 * (R ^ 2 * (2 * R)) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hε0
      _ = 2 * R ^ 5 * ε := by ring
  have hΔ0 : (0 : ℝ) ≤ 2 * R ^ 5 * ε := by positivity
  -- the control
  have hRHS : |sWeight d N i c - sWeight d N i c'| ≤ 6 * R ^ 10 * ε := by
    refine (abs_sWeight_sub_le d N i c c' hR0 hΔ0 hcb hcb' hdd).trans ?_
    calc (Fintype.card (d.Idx N) : ℝ) * (2 * R * (2 * R ^ 5 * ε))
        ≤ R * (2 * R * (2 * R ^ 5 * ε)) := by
          refine mul_le_mul_of_nonneg_right hRn (by positivity)
      _ = 4 * R ^ 7 * ε := by ring
      _ ≤ 6 * R ^ 10 * ε := by nlinarith [hpow, hε0, pow_nonneg hR0 10]
  -- the linear form
  have hbu : ‖rowLin d N u i c ω‖ ≤ R * (R * R) := by
    refine (norm_rowLin_le d N hu1.le i c ω hR0 hcb).trans ?_
    exact mul_le_mul hRn (mul_le_mul_of_nonneg_right hRx hR0) (by positivity) hR0
  have hbv : ‖rowLin d N v i c' ω‖ ≤ R * (R * R) := by
    refine (norm_rowLin_le d N hv1.le i c' ω hR0 hcb').trans ?_
    exact mul_le_mul hRn (mul_le_mul_of_nonneg_right hRx hR0) (by positivity) hR0
  have hsub : ‖rowLin d N u i c ω - rowLin d N v i c' ω‖ ≤ R * (R * (3 * R ^ 5 * ε)) := by
    refine (norm_rowLin_sub_le d N hv1.le i c c' ω hR0 hΔ0 hcb hdd).trans ?_
    have h2 : |Real.sqrt u - Real.sqrt v| ≤ ε := by
      rw [hεdef]; have := abs_nonneg (u - v); linarith
    have h3 : R ≤ R ^ 5 := by nlinarith [pow_nonneg hR0 4, sq_nonneg R, sq_nonneg (R - 1)]
    have h5 : |Real.sqrt u - Real.sqrt v| * R ≤ ε * R ^ 5 := mul_le_mul h2 h3 hR0 hε0
    have h1 : |Real.sqrt u - Real.sqrt v| * R + 2 * R ^ 5 * ε ≤ 3 * R ^ 5 * ε := by linarith
    have h4 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * R + 2 * R ^ 5 * ε := by positivity
    exact mul_le_mul hRn (mul_le_mul hRx h1 h4 hR0) (by positivity) hR0
  have hLHS : |‖rowLin d N u i c ω‖ ^ 2 - ‖rowLin d N v i c' ω‖ ^ 2| ≤ 6 * R ^ 10 * ε := by
    have hsum : ‖rowLin d N u i c ω‖ + ‖rowLin d N v i c' ω‖ ≤ 2 * (R * (R * R)) := by
      linarith
    have hfin : (2 * (R * (R * R))) * (R * (R * (3 * R ^ 5 * ε))) = 6 * R ^ 10 * ε := by ring
    refine (abs_norm_sq_sub_le _ _).trans ?_
    rw [← hfin]
    exact mul_le_mul hsum hsub (norm_nonneg _) (by positivity)
  refine ⟨?_, ?_⟩
  · rw [← sWeight_minorCol_eq (z := zt E u) u j (isUnit_det_Hflow_sub d N u ω hzu)
      (green_Hflow_diag_ne_zero d N u ω hzu i),
      ← sWeight_minorCol_eq (z := zt E v) v j (isUnit_det_Hflow_sub d N v ω hzv)
      (green_Hflow_diag_ne_zero d N v ω hzv i)]
    exact hRHS
  · rw [ldeRowLHS_eq (z := zt E u) u j (isUnit_det_Hflow_sub d N u ω hzu)
      (green_Hflow_diag_ne_zero d N u ω hzu i),
      ldeRowLHS_eq (z := zt E v) v j (isUnit_det_Hflow_sub d N v ω hzv)
      (green_Hflow_diag_ne_zero d N v ω hzv i)]
    exact hLHS


/-- **The column half of `RBM.Gauss.abs_ldeRow_flow_sub_le`**, by Hermitian symmetry: the
coefficients are the conjugated `k`-th row of `G^{(j)}` instead of the `j`-th column of
`G^{(i)}`, and everything else is the same. -/
theorem abs_ldeCol_flow_sub_le (d : Dims) (N : ℕ) (hE : |E| < 2) {u v R : ℝ}
    (hu1 : u < 1) (hv1 : v < 1) (hR1 : 1 ≤ R)
    (hRu : (etaT E u)⁻¹ ≤ R) (hRv : (etaT E v)⁻¹ ≤ R)
    (hRn : (Fintype.card (d.Idx N) : ℝ) ≤ R) (ω : Ω d) (hRx : ‖Xmat d N ω‖ ≤ R)
    (j : d.Idx N) (k : {a : d.Idx N // a ≠ j}) :
    |ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt E u)) k.1 j
        - ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N v ω) (zt E v)) k.1 j|
        ≤ 6 * R ^ 10 * (|Real.sqrt u - Real.sqrt v| + |u - v|)
      ∧ |ldeColLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt E u)) k.1 j
        - ldeColLHS (Hflow d N v ω) (green (Hflow d N v ω) (zt E v)) k.1 j|
        ≤ 6 * R ^ 10 * (|Real.sqrt u - Real.sqrt v| + |u - v|) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hR3 : (1 : ℝ) ≤ R ^ 3 := by nlinarith [sq_nonneg R, sq_nonneg (R - 1)]
  have hR7 : (0 : ℝ) ≤ R ^ 7 := by positivity
  have hpow : R ^ 7 ≤ R ^ 10 := by
    nlinarith [mul_le_mul_of_nonneg_left hR3 hR7]
  set ε : ℝ := |Real.sqrt u - Real.sqrt v| + |u - v| with hεdef
  have hε0 : (0 : ℝ) ≤ ε := by rw [hεdef]; positivity
  have hzu : (zt E u).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact (etaT_pos_of_lt_one' hE hu1).ne'
  have hzv : (zt E v).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact (etaT_pos_of_lt_one' hE hv1).ne'
  set c : d.Idx N → ℂ := minorRowConj d N u (zt E u) j k ω with hc_def
  set c' : d.Idx N → ℂ := minorRowConj d N v (zt E v) j k ω with hc'_def
  have hcb : ∀ l, ‖c l‖ ≤ R := fun l => norm_minorRowConj_le d N hE hu1 hRu ω j k l
  have hcb' : ∀ l, ‖c' l‖ ≤ R := fun l => norm_minorRowConj_le d N hE hv1 hRv ω j k l
  have hdd : ∀ l, ‖c l - c' l‖ ≤ 2 * R ^ 5 * ε := by
    intro l
    refine (norm_minorRowConj_flow_sub_le d N hE hu1 hv1 hRu hRv ω j k l).trans ?_
    have h1 : (Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1) ≤ R ^ 2 * (2 * R) := by
      have h0 : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
      have hn2 : (Fintype.card (d.Idx N) : ℝ) ^ 2 ≤ R ^ 2 := by nlinarith
      have hx1 : ‖Xmat d N ω‖ + 1 ≤ 2 * R := by linarith
      exact mul_le_mul hn2 hx1 (by positivity) (by positivity)
    calc R ^ 2 * ((Fintype.card (d.Idx N) : ℝ) ^ 2 * (‖Xmat d N ω‖ + 1)) * ε
        ≤ R ^ 2 * (R ^ 2 * (2 * R)) * ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hε0
      _ = 2 * R ^ 5 * ε := by ring
  have hΔ0 : (0 : ℝ) ≤ 2 * R ^ 5 * ε := by positivity
  have hRHS : |sWeight d N j c - sWeight d N j c'| ≤ 6 * R ^ 10 * ε := by
    refine (abs_sWeight_sub_le d N j c c' hR0 hΔ0 hcb hcb' hdd).trans ?_
    calc (Fintype.card (d.Idx N) : ℝ) * (2 * R * (2 * R ^ 5 * ε))
        ≤ R * (2 * R * (2 * R ^ 5 * ε)) := by
          refine mul_le_mul_of_nonneg_right hRn (by positivity)
      _ = 4 * R ^ 7 * ε := by ring
      _ ≤ 6 * R ^ 10 * ε := by nlinarith [hpow, hε0, pow_nonneg hR0 10]
  have hbu : ‖rowLin d N u j c ω‖ ≤ R * (R * R) := by
    refine (norm_rowLin_le d N hu1.le j c ω hR0 hcb).trans ?_
    exact mul_le_mul hRn (mul_le_mul_of_nonneg_right hRx hR0) (by positivity) hR0
  have hbv : ‖rowLin d N v j c' ω‖ ≤ R * (R * R) := by
    refine (norm_rowLin_le d N hv1.le j c' ω hR0 hcb').trans ?_
    exact mul_le_mul hRn (mul_le_mul_of_nonneg_right hRx hR0) (by positivity) hR0
  have hsub : ‖rowLin d N u j c ω - rowLin d N v j c' ω‖ ≤ R * (R * (3 * R ^ 5 * ε)) := by
    refine (norm_rowLin_sub_le d N hv1.le j c c' ω hR0 hΔ0 hcb hdd).trans ?_
    have h2 : |Real.sqrt u - Real.sqrt v| ≤ ε := by
      rw [hεdef]; have := abs_nonneg (u - v); linarith
    have h3 : R ≤ R ^ 5 := by nlinarith [pow_nonneg hR0 4, sq_nonneg R, sq_nonneg (R - 1)]
    have h5 : |Real.sqrt u - Real.sqrt v| * R ≤ ε * R ^ 5 := mul_le_mul h2 h3 hR0 hε0
    have h1 : |Real.sqrt u - Real.sqrt v| * R + 2 * R ^ 5 * ε ≤ 3 * R ^ 5 * ε := by linarith
    have h4 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| * R + 2 * R ^ 5 * ε := by positivity
    exact mul_le_mul hRn (mul_le_mul hRx h1 h4 hR0) (by positivity) hR0
  have hLHS : |‖rowLin d N u j c ω‖ ^ 2 - ‖rowLin d N v j c' ω‖ ^ 2| ≤ 6 * R ^ 10 * ε := by
    have hsum : ‖rowLin d N u j c ω‖ + ‖rowLin d N v j c' ω‖ ≤ 2 * (R * (R * R)) := by
      linarith
    have hfin : (2 * (R * (R * R))) * (R * (R * (3 * R ^ 5 * ε))) = 6 * R ^ 10 * ε := by ring
    refine (abs_norm_sq_sub_le _ _).trans ?_
    rw [← hfin]
    exact mul_le_mul hsum hsub (norm_nonneg _) (by positivity)
  refine ⟨?_, ?_⟩
  · rw [← sWeight_minorRowConj_eq (z := zt E u) u k (isUnit_det_Hflow_sub d N u ω hzu)
      (green_Hflow_diag_ne_zero d N u ω hzu j),
      ← sWeight_minorRowConj_eq (z := zt E v) v k (isUnit_det_Hflow_sub d N v ω hzv)
      (green_Hflow_diag_ne_zero d N v ω hzv j)]
    exact hRHS
  · rw [ldeColLHS_eq (z := zt E u) u k (isUnit_det_Hflow_sub d N u ω hzu)
      (green_Hflow_diag_ne_zero d N u ω hzu j),
      ldeColLHS_eq (z := zt E v) v k (isUnit_det_Hflow_sub d N v ω hzv)
      (green_Hflow_diag_ne_zero d N v ω hzv j)]
    exact hLHS

end Modulus


/-! ### From the modulus to the net comparison, with a floor -/

section Floor

/-- Relaxing the control preserves `RBM.Gauss.UnifDomIcc`. -/
theorem UnifDomIcc.mono_control {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {V : ℕ → Type*} {s t : ℕ → ℝ} {ξ ζ ζ' : ∀ N, ℝ → V N → Ω → ℝ}
    (h : UnifDomIcc P s t ξ ζ) (hle : ∀ N u a ω, ζ N u a ω ≤ ζ' N u a ω) :
    UnifDomIcc P s t ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN u hu a
  refine le_trans (measure_mono ?_) (hN u hu a)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hNpos : (0 : ℝ) ≤ (N : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg N) τ
  have hmono := hle N u a ω
  nlinarith

/-- **The net spacing is chosen so that the deterministic modulus sits below the floor.**

With the net spacing `δ_N = (N^{-(10K+12+B)})²` — i.e. `A = 2(10K+12+B)` in the engine — the
constant `6 R^{10}` of `RBM.Gauss.abs_ldeRow_flow_sub_le` at `R = N^{K+1}` times the Hölder
factor `|√u-√v| + |u-v| ≤ 2|u-v|^{1/2}` is at most the floor `N^{-B}`. -/
theorem eventually_mod_le_floor {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop, ∀ u v : ℝ,
      |u - v| ≤ ((N : ℝ) ^ (-(10 * K + 12 + B))) ^ 2 →
        6 * ((N : ℝ) ^ (K + 1)) ^ 10 * (|Real.sqrt u - Real.sqrt v| + |u - v|)
          ≤ (N : ℝ) ^ (-B) := by
  filter_upwards [eventually_ge_atTop 1, eventually_le_rpow 12 (by norm_num : (0:ℝ) < 2)]
    with N hN1 h12 u v huv
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  set a : ℝ := 10 * K + 12 + B with ha
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; linarith
  have h1a : (1 : ℝ) ≤ (N : ℝ) ^ a := Real.one_le_rpow hN1' ha0
  have hpa : (0 : ℝ) < (N : ℝ) ^ a := by linarith
  have hna : (N : ℝ) ^ (-a) = ((N : ℝ) ^ a)⁻¹ := Real.rpow_neg hN0.le a
  have hna0 : (0 : ℝ) ≤ (N : ℝ) ^ (-a) := Real.rpow_nonneg hN0.le _
  have hna1 : (N : ℝ) ^ (-a) ≤ 1 := by
    rw [hna, ← one_div, div_le_one hpa]; linarith
  -- the Hölder factor
  have hx0 : (0 : ℝ) ≤ |u - v| := abs_nonneg _
  have hx1 : |u - v| ≤ 1 := by nlinarith
  have hsq : Real.sqrt |u - v| ≤ (N : ℝ) ^ (-a) := by
    have h := Real.sqrt_le_sqrt huv
    rwa [Real.sqrt_sq hna0] at h
  have hxs : |u - v| ≤ Real.sqrt |u - v| := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt |u - v| := Real.sqrt_nonneg _
    have hss : Real.sqrt |u - v| * Real.sqrt |u - v| = |u - v| :=
      Real.mul_self_sqrt hx0
    nlinarith
  have hdiff : |Real.sqrt u - Real.sqrt v| ≤ Real.sqrt |u - v| := abs_sqrt_sub_sqrt_le u v
  have hε : |Real.sqrt u - Real.sqrt v| + |u - v| ≤ 2 * (N : ℝ) ^ (-a) := by linarith
  have hε0 : (0 : ℝ) ≤ |Real.sqrt u - Real.sqrt v| + |u - v| := by positivity
  -- the polynomial constant
  have hR10 : ((N : ℝ) ^ (K + 1)) ^ (10 : ℕ) = (N : ℝ) ^ (10 * K + 10) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (K + 1)) 10, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hR0 : (0 : ℝ) ≤ ((N : ℝ) ^ (K + 1)) ^ (10 : ℕ) := by positivity
  have hp2 : (0 : ℝ) < (N : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have hinv : 12 * ((N : ℝ) ^ (2 : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hp2]; exact h12
  have hBnn : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg hN0.le _
  calc 6 * ((N : ℝ) ^ (K + 1)) ^ 10 * (|Real.sqrt u - Real.sqrt v| + |u - v|)
      ≤ 6 * ((N : ℝ) ^ (K + 1)) ^ 10 * (2 * (N : ℝ) ^ (-a)) := by
        refine mul_le_mul_of_nonneg_left hε (by positivity)
    _ = 12 * ((N : ℝ) ^ (10 * K + 10) * (N : ℝ) ^ (-a)) := by rw [hR10]; ring
    _ = 12 * ((N : ℝ) ^ (-(2 : ℝ)) * (N : ℝ) ^ (-B)) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
        congr 2
        rw [ha]; ring
    _ = 12 * (((N : ℝ) ^ (2 : ℝ))⁻¹ * (N : ℝ) ^ (-B)) := by
        rw [Real.rpow_neg hN0.le]
    _ ≤ 1 * (N : ℝ) ^ (-B) := by nlinarith
    _ = (N : ℝ) ^ (-B) := one_mul _

end Floor


/-! ### (4.2) along the flow, with an additive floor -/

section Assemble

variable {d : Dims} {E : ℝ} {s t : ℕ → ℝ}

/-- **The row large deviation estimate (4.2), uniformly in the time, with an additive floor.**

Unconditional apart from the standing regime hypotheses: `hη` is the polynomial lower bound
`N^{-K} ≤ η_{t_N}` on the spectral window, which is deterministic and part of the regime, and
`|E| < 2`, `0 ≤ s_N ≤ t_N < 1` are the usual constraints on the flow interval.  No
`RBM.Gauss.LDENetClose`, no good event beyond `‖X‖ ≤ N`, and no off-diagonal decay.

The floor `N^{-B}` is for **every** `B ≥ 0`, so the statement is `ξ ≺ ζ + N^{-B}` for all `B`.
It cannot be removed: see the module docstring. -/
theorem stochDom_ldeRow_flow_floor (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {B : ℝ} (hB : 0 ≤ B) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × OffPair d.L d.W N)
      (fun N p ω =>
        ldeRowLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2)
      (fun N p ω =>
        ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2 + (N : ℝ) ^ (-B)) := by
  refine stochDom_timeIcc_of_unifDom_relative (card_OffPair_le d) hst one_pos
    (fun N => by have := hs0 N; have := (ht1 N).le; linarith)
    (A := 2 * (10 * K + 12 + B)) (by linarith)
    (ξ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeRowLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2)
    (ζ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2
        + (N : ℝ) ^ (-B)) ?_
    (δ := fun N => ((N : ℝ) ^ (-(10 * K + 12 + B))) ^ 2) ?_
    (highProb_norm_Xmat_le d) ?_
    ((unifDomIcc_ldeRow d hE hs0 ht1).mono_control fun N u q ω => by
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      linarith)
  · intro N u q ω
    have h1 : (0 : ℝ) ≤ ldeRowRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg _ _) (by positivity)
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    refine le_of_eq ?_
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(10 * K + 12 + B))) 2, ← Real.rpow_mul hN0.le,
      one_div, ← Real.rpow_neg hN0.le]
    congr 1
    push_cast
    ring
  · filter_upwards [hη, card_Idx_le d, eventually_mod_le_floor hK hB,
      eventually_ge_atTop 1] with N hηN hcardN hmodN hN1 ω hω q u hu v hv huv
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
    have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (K + 1) := Real.one_le_rpow hN1' (by linarith)
    have hN11 : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hRη : ∀ w : ℝ, w ≤ t N → (etaT E w)⁻¹ ≤ (N : ℝ) ^ (K + 1) := by
      intro w hw
      have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
      have hle : etaT E (t N) ≤ etaT E w := etaT_le_of_le hE hw
      have hNKpos : (0 : ℝ) < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hN0 _
      have h1 : (etaT E w)⁻¹ ≤ (etaT E (t N))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hηt hle
      have h2 : (etaT E (t N))⁻¹ ≤ ((N : ℝ) ^ (-K))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hNKpos hηN
      have h3 : ((N : ℝ) ^ (-K))⁻¹ = (N : ℝ) ^ K := by rw [Real.rpow_neg hN0.le, inv_inv]
      have h4 : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [h3] at h2
      linarith
    have hRn : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      rw [Real.rpow_one] at hcardN; linarith
    have hRx : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (K + 1) := le_trans hω hN11
    have key := abs_ldeRow_flow_sub_le d N hE hu1 hv1 hR1 (hRη u hu.2) (hRη v hv.2) hRn ω hRx
      q.1.1 ⟨q.1.2, Ne.symm q.2⟩
    have hfl := hmodN u v huv
    obtain ⟨hlo1, hhi1⟩ := abs_le.1 (key.1.trans hfl)
    obtain ⟨hlo2, hhi2⟩ := abs_le.1 (key.2.trans hfl)
    have hζ0 : (0 : ℝ) ≤ ldeRowRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Sblk_nonneg _ _) (by positivity)
    exact ⟨by linarith, by linarith⟩


/-- **The column large deviation estimate (4.2), uniformly in the time, with an additive
floor.**  The companion of `RBM.Gauss.stochDom_ldeRow_flow_floor`. -/
theorem stochDom_ldeCol_flow_floor (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {B : ℝ} (hB : 0 ≤ B) :
    StochDom (P d) (U := fun N => RBM.TimeIcc s t N × OffPair d.L d.W N)
      (fun N p ω =>
        ldeColLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2)
      (fun N p ω =>
        ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2 + (N : ℝ) ^ (-B)) := by
  refine stochDom_timeIcc_of_unifDom_relative (card_OffPair_le d) hst one_pos
    (fun N => by have := hs0 N; have := (ht1 N).le; linarith)
    (A := 2 * (10 * K + 12 + B)) (by linarith)
    (ξ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeColLHS (Hflow d N u ω) (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2)
    (ζ := fun N u (q : OffPair d.L d.W N) ω =>
      ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2
        + (N : ℝ) ^ (-B)) ?_
    (δ := fun N => ((N : ℝ) ^ (-(10 * K + 12 + B))) ^ 2) ?_
    (highProb_norm_Xmat_le d) ?_
    ((unifDomIcc_ldeCol d hE hs0 ht1).mono_control fun N u q ω => by
      have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
      linarith)
  · intro N u q ω
    have h1 : (0 : ℝ) ≤ ldeColRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (Sblk_nonneg _ _)
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    refine le_of_eq ?_
    rw [← Real.rpow_natCast ((N : ℝ) ^ (-(10 * K + 12 + B))) 2, ← Real.rpow_mul hN0.le,
      one_div, ← Real.rpow_neg hN0.le]
    congr 1
    push_cast
    ring
  · filter_upwards [hη, card_Idx_le d, eventually_mod_le_floor hK hB,
      eventually_ge_atTop 1] with N hηN hcardN hmodN hN1 ω hω q u hu v hv huv
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
    have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (K + 1) := Real.one_le_rpow hN1' (by linarith)
    have hN11 : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (N : ℝ) ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have hRη : ∀ w : ℝ, w ≤ t N → (etaT E w)⁻¹ ≤ (N : ℝ) ^ (K + 1) := by
      intro w hw
      have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
      have hle : etaT E (t N) ≤ etaT E w := etaT_le_of_le hE hw
      have hNKpos : (0 : ℝ) < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hN0 _
      have h1 : (etaT E w)⁻¹ ≤ (etaT E (t N))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hηt hle
      have h2 : (etaT E (t N))⁻¹ ≤ ((N : ℝ) ^ (-K))⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div]
        exact one_div_le_one_div_of_le hNKpos hηN
      have h3 : ((N : ℝ) ^ (-K))⁻¹ = (N : ℝ) ^ K := by rw [Real.rpow_neg hN0.le, inv_inv]
      have h4 : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      rw [h3] at h2
      linarith
    have hRn : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
      rw [Real.rpow_one] at hcardN; linarith
    have hRx : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (K + 1) := le_trans hω hN11
    have key := abs_ldeCol_flow_sub_le d N hE hu1 hv1 hR1 (hRη u hu.2) (hRη v hv.2) hRn ω hRx
      q.1.2 ⟨q.1.1, q.2⟩
    have hfl := hmodN u v huv
    obtain ⟨hlo1, hhi1⟩ := abs_le.1 (key.1.trans hfl)
    obtain ⟨hlo2, hhi2⟩ := abs_le.1 (key.2.trans hfl)
    have hζ0 : (0 : ℝ) ≤ ldeColRHS (Sblk (d.L N) (d.W N))
        (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2 :=
      Finset.sum_nonneg fun l _ => mul_nonneg (by positivity) (Sblk_nonneg _ _)
    exact ⟨by linarith, by linarith⟩

/-- **`RBM.LKDecayQuant.LDEFlowDom` for `RBM.Gauss.sample d`, with an additive floor in the
control** — the shape `RBM.Gauss.ldeFlowDom_of_close` produces from
`RBM.Gauss.LDENetClose`, except that the control carries `+ N^{-B}` and **no hypothesis
beyond the regime is left**. -/
theorem ldeFlowDom_floor (d : Dims) (hE : |E| < 2) (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {B : ℝ} (hB : 0 ≤ B) :
    (StochDom (P d) (U := fun N => RBM.TimeIcc s t N × OffPair d.L d.W N)
      (fun N p ω =>
        ldeRowLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2)
      (fun N p ω =>
        ldeRowRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2 + (N : ℝ) ^ (-B)))
    ∧ StochDom (P d) (U := fun N => RBM.TimeIcc s t N × OffPair d.L d.W N)
      (fun N p ω =>
        ldeColLHS (Hflow d N (p.1 : ℝ) ω) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2)
      (fun N p ω =>
        ldeColRHS (Sblk (d.L N) (d.W N)) (green (Hflow d N (p.1 : ℝ) ω) (zt E (p.1 : ℝ)))
          p.2.1.1 p.2.1.2 + (N : ℝ) ^ (-B)) :=
  ⟨stochDom_ldeRow_flow_floor d hE hs0 hst ht1 hK hη hB,
    stochDom_ldeCol_flow_floor d hE hs0 hst ht1 hK hη hB⟩


/-! ### What `RBM.Gauss.LDENetClose` needs on top of the modulus -/

/-- **`RBM.Gauss.LDENetClose` follows from a polynomial lower bound on the control.**

The deterministic modulus of this file gives, at net spacing `δ_N`,
`|ξ(u) - ξ(v)| ≤ N^{-B}` and `|ζ(u) - ζ(v)| ≤ N^{-B}` on `{‖X‖ ≤ N}`.  Both clauses of
`RBM.Gauss.LDENetClose` then follow *provided* the control itself is at least `N^{-B}`:

* `ξ(u) ≤ ξ(v) + N^{-B} ≤ ξ(v) + ζ(u)`;
* `ζ(v) ≤ ζ(u) + N^{-B} ≤ 2 ζ(u)`.

So `LDENetClose` is *exactly* the additive modulus (a theorem here) plus `N^{-B} ≤ ζ`, the
polynomial lower bound on the control that T143's engine was rebuilt to avoid.  `hlow` is
**not** available for (4.2): `ζ(u) = ∑_{k ∈ band(i)} S_{ik}|G^{(i)}_{kj}(u)|²` is exponentially
small in the band distance between `i` and `j`, so no polynomial lower bound holds uniformly in
the pair.  This is why `RBM.Gauss.stochDom_ldeRow_flow_floor` carries the floor instead. -/
theorem ldeNetClose_of_lower_bound (d : Dims) (hE : |E| < 2) (ht1 : ∀ N, t N < 1)
    {K : ℝ} (hK : 0 ≤ K)
    (hη : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-K) ≤ etaT E (t N)) {B : ℝ} (hB : 0 ≤ B)
    {Ξ : ℕ → Set (Ω d)}
    (hΞX : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ‖Xmat d N ω‖ ≤ (N : ℝ))
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ ω ∈ Ξ N, ∀ q : OffPair d.L d.W N,
      ∀ u ∈ Set.Icc (s N) (t N),
        (N : ℝ) ^ (-B) ≤ ldeRowRHS (Sblk (d.L N) (d.W N))
            (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2
          ∧ (N : ℝ) ^ (-B) ≤ ldeColRHS (Sblk (d.L N) (d.W N))
            (green (Hflow d N u ω) (zt E u)) q.1.1 q.1.2) :
    LDENetClose d E s t Ξ (fun N => ((N : ℝ) ^ (-(10 * K + 12 + B))) ^ 2) := by
  filter_upwards [hη, card_Idx_le d, eventually_mod_le_floor hK hB, hΞX, hlow,
    eventually_ge_atTop 1] with N hηN hcardN hmodN hΞN hlowN hN1 ω hω q u hu v hv huv
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  have hv1 : v < 1 := lt_of_le_of_lt hv.2 (ht1 N)
  have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (K + 1) := Real.one_le_rpow hN1' (by linarith)
  have hN11 : (N : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
    calc (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (K + 1) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
  have hRη : ∀ w : ℝ, w ≤ t N → (etaT E w)⁻¹ ≤ (N : ℝ) ^ (K + 1) := by
    intro w hw
    have hηt : 0 < etaT E (t N) := etaT_pos_of_lt_one' hE (ht1 N)
    have hle : etaT E (t N) ≤ etaT E w := etaT_le_of_le hE hw
    have hNKpos : (0 : ℝ) < (N : ℝ) ^ (-K) := Real.rpow_pos_of_pos hN0 _
    have h1 : (etaT E w)⁻¹ ≤ (etaT E (t N))⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hηt hle
    have h2 : (etaT E (t N))⁻¹ ≤ ((N : ℝ) ^ (-K))⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hNKpos hηN
    have h3 : ((N : ℝ) ^ (-K))⁻¹ = (N : ℝ) ^ K := by rw [Real.rpow_neg hN0.le, inv_inv]
    have h4 : (N : ℝ) ^ K ≤ (N : ℝ) ^ (K + 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    rw [h3] at h2
    linarith
  have hRn : (Fintype.card (d.Idx N) : ℝ) ≤ (N : ℝ) ^ (K + 1) := by
    rw [Real.rpow_one] at hcardN; linarith
  have hRx : ‖Xmat d N ω‖ ≤ (N : ℝ) ^ (K + 1) := le_trans (hΞN ω hω) hN11
  have keyR := abs_ldeRow_flow_sub_le d N hE hu1 hv1 hR1 (hRη u hu.2) (hRη v hv.2) hRn ω hRx
    q.1.1 ⟨q.1.2, Ne.symm q.2⟩
  have keyC := abs_ldeCol_flow_sub_le d N hE hu1 hv1 hR1 (hRη u hu.2) (hRη v hv.2) hRn ω hRx
    q.1.2 ⟨q.1.1, q.2⟩
  have hfl := hmodN u v huv
  obtain ⟨hloR1, hhiR1⟩ := abs_le.1 (keyR.1.trans hfl)
  obtain ⟨hloR2, hhiR2⟩ := abs_le.1 (keyR.2.trans hfl)
  obtain ⟨hloC1, hhiC1⟩ := abs_le.1 (keyC.1.trans hfl)
  obtain ⟨hloC2, hhiC2⟩ := abs_le.1 (keyC.2.trans hfl)
  obtain ⟨hlowRow, hlowCol⟩ := hlowN ω hω q u hu
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

end Assemble

end RBM.Gauss
