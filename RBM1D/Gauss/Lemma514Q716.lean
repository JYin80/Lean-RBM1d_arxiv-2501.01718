/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514Moment
import RBM1D.Hierarchy.SumZeroDyn
import RBM1D.Flow.Scales

/-!
# Lemma 5.14 on the moment route: `Q_u` + (7.16) instead of the bare row sums (T201)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.5 (pp. 67–69) and Lemma 7.3 (7.16).

T195 established that the moment route's kernel step — `RBM.Gauss.momNorm_Uker_apply_le`,
which bounds `‖(U_{u,v,σ} ∘ A)_a‖_q` by the `l¹` row mass of `U` — is **Lemma 7.1**, and that
its constant is *unbounded* on the paper's own grid.  This file supplies the replacement that
(5.92) actually calls for: every term is projected by `Q_u` first, and then estimated by
Case 2 of **(7.16)**, whose `r^m` cancels against the `A^{-m}` normalisation, leaving **no
prefactor depending on `η_s/η_t`** — which is exactly what (5.92) asserts.

## Main results

* §1 — the (7.1) tier and why it is unusable.
  `RBM.Gauss.one_add_norm_edge_eq`: for `‖ξ‖ = 1` the `hkerC` integrand is *identically*
  `η_u/η_w`, i.e. Lemma 7.1.  `RBM.Gauss.gridS_window_ratio`, `RBM.Gauss.gridS_window_len`:
  on the grid `1 - s_k = W^{-kτ'}` of p. 24 the window satisfies `(t-s)/(1-t) = W^{τ'} - 1`
  *exactly*.  `RBM.Gauss.no_const_hkerC_on_gridS`, `RBM.Gauss.no_const_hker2C_on_gridS`: hence
  the `hkerC` / `hker2C` slots of `RBM.Gauss.hrhs_of_moment_inputs` have **no** `N`-independent
  constant there, and any consumer of them is vacuous on the assembly window.  (These are
  T195's probes, which T193 found had never entered the repository.)
* §2 — `RBM.Gauss.momNorm_le_affine`: Minkowski for `momNorm` against `c Y + d`.  T146's
  `momNorm_le_of_le_weighted_sum` is Jensen and needs a *common* bound on all summands; the
  (7.16) estimate has a random main term and a deterministic error term, so it needs the real
  thing.  Obtained from T146's lemma by rescaling to unit moment norm.
* §3 — `RBM.Gauss.momNorm_Uker_sumZero_scale_le`: **(7.16) Case 2 in moment form**, the
  replacement for `RBM.Gauss.momNorm_Uker_apply_le`.  §3b gives the arbitrary-`ξ` version
  (`RBM.Gauss.norm_Uker_sumZero_scale_le'`, `RBM.Gauss.momNorm_Uker_sumZero_scale_le'`), needed
  because the `E ⊗ E` charge `RBM.SumZeroDyn.xi2` is a `Fin.append` and not a `xiOf`.
* §4 — `RBM.Gauss.momNorm_le_affine_on_event`: the good-event split, because (7.13) holds only
  with high probability.
* §5 — `RBM.Gauss.witTensor` and `RBM.Gauss.gridS_Q716_witness`: the satisfiability witness, on
  the **paper's own grid** and with **no short-window hypothesis**.  The witness is not zero,
  `Q_u` fixes it (`RBM.Gauss.Qop_witTensor`), the (7.13) error is `δ = 0`, and the resulting
  constant does not depend on `N`.
* §6 — the five terms of `RBM.MomentDuhamel.Hyp.momentDuhamelQ` on the (7.16) tier
  (`RBM.Gauss.momNorm_Uker_Qop_le`, `…_commS_le`, `…_PsumVarthetaDot_le`, `…_QQ_le`): in each
  the sum-zero premise of (7.16) is discharged by a theorem, not assumed.

## What this file does **not** do

* It does not produce the (7.13) fast decay of the five tensors along the flow.  That is the
  one premise of (7.16) which is a statement about the model; §4 is the interface it will be
  consumed through.
* It does not close the `P ∘ (L-K)` half of (5.95)–(5.101), so it does **not** give a primed
  `RBM.Gauss.hrhs_of_moment_inputs` with the same conclusion: `RBM.SumZeroDyn.lkT` is not
  sum-zero, only `Q_u ∘ lkT` is, and returning from `Q_v ∘ (L-K)_v` to `(L-K)_v` is exactly
  the piece `RBM.MomentDuhamel.Hyp.momentDuhamelQ` is stated against and that has no consumer.

Nothing here is an `axiom` and nothing here is `sorry`.
-/

namespace RBM.Gauss

open Filter MeasureTheory Real

/-! ### §1  The (7.1) tier, and why it cannot be used: T195's negative results, re-landed

T193 found that T195 was a read-only audit whose probes never entered the repository.  They
are re-proved here, because the whole point of this file is the *contrast* between them and
the (7.16) tier of §3. -/

/-- **The `hkerC` integrand, computed exactly.**  For an edge parameter of modulus one — which
is what `ξ_i = m(σ_i) m(σ_{i+1})` is in the bulk, `RBM.norm_xiOf_mSigma` — the left-hand side
of the `hkerC` slot of `RBM.Gauss.hrhs_of_moment_inputs` is **identically** `η_u / η_w`.

That is *verbatim* Lemma 7.1, and (5.92) is the statement that Lemma 5.14 holds with **no**
prefactor depending on `η_s/η_t`. -/
theorem one_add_norm_edge_eq {u w : ℝ} (hu0 : 0 ≤ u) (huw : u ≤ w) (hw1 : w < 1) {ξ : ℂ}
    (hξ : ‖ξ‖ = 1) :
    1 + ‖((u : ℂ) - (w : ℂ)) * ξ‖ * (1 - ‖(w : ℂ) * ξ‖)⁻¹ = (1 - u) / (1 - w) := by
  have hw0 : (0 : ℝ) ≤ w := hu0.trans huw
  have h1w : (0 : ℝ) < 1 - w := by linarith
  have hnum : ‖((u : ℂ) - (w : ℂ)) * ξ‖ = w - u := by
    rw [norm_mul, hξ, mul_one, show ((u : ℝ) : ℂ) - ((w : ℝ) : ℂ) = ((u - w : ℝ) : ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by linarith)]
  have hden : (1 - ‖((w : ℝ) : ℂ) * ξ‖)⁻¹ = (1 - w)⁻¹ := by
    rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  rw [hnum, hden, eq_div_iff h1w.ne']
  field_simp
  ring

/-- **The paper's grid, one window.**  With `1 - s_k = W^{-kτ'}` (p. 24, `RBM.gridS`) the
ratio `η_{s_k} / η_{s_{k+1}}` is exactly `W^{τ'}`. -/
theorem gridS_window_ratio {W τ' : ℝ} (hW : 0 < W) (k : ℕ) :
    (1 - gridS W τ' k) / (1 - gridS W τ' (k + 1)) = W ^ τ' := by
  have h0 : (0 : ℝ) < 1 - gridS W τ' k := sub_pos.mpr (gridS_lt_one hW k)
  rw [one_sub_gridS_succ hW, mul_comm, ← div_div, div_self h0.ne', one_div,
    Real.rpow_neg hW.le, inv_inv]

/-- **The window length of the paper's grid, relative to the distance to the edge.**
`(t - s)/(1 - t) = W^{τ'} - 1` — an *equality*, so no constant `κ` with `t - s ≤ κ(1-t)` can
be chosen independently of `W`. -/
theorem gridS_window_len {W τ' : ℝ} (hW : 0 < W) (k : ℕ) :
    (gridS W τ' (k + 1) - gridS W τ' k) / (1 - gridS W τ' (k + 1)) = W ^ τ' - 1 := by
  have h1 : (0 : ℝ) < 1 - gridS W τ' (k + 1) := sub_pos.mpr (gridS_lt_one hW (k + 1))
  have h := gridS_window_ratio hW (τ' := τ') k
  rw [div_eq_iff h1.ne'] at h
  rw [div_eq_iff h1.ne']
  linarith

/-- **T195's `no_const_Ck`.**  On the paper's own grid the `hkerC` constant does not exist:
`η_{s_k}/η_{s_{k+1}} = W_N^{τ'} → ∞`.

This is not "we could not prove it": the hypothesis is *false*. -/
theorem no_const_gridS_ratio {τ' : ℝ} (hτ' : 0 < τ') {W : ℕ → ℝ} (hW : ∀ N, 0 < W N)
    (hWtop : Tendsto W atTop atTop) {Ck : ℝ} (k : ℕ)
    (h : ∀ N, (1 - gridS (W N) τ' k) / (1 - gridS (W N) τ' (k + 1)) ≤ Ck) : False := by
  have htop : Tendsto (fun N => (W N) ^ τ') atTop atTop :=
    (tendsto_rpow_atTop hτ').comp hWtop
  obtain ⟨N, hN⟩ := (htop.eventually_gt_atTop Ck).exists
  exact absurd ((gridS_window_ratio (hW N) k) ▸ h N) (not_le.mpr hN)

/-- **The `hkerC` / `hker2C` slots are unsatisfiable on the paper's grid.**

Take `s_N = s_k`, `t_N = s_{k+1}` on the grid of p. 24 with `W = W_N → ∞`.  The left-hand side
of the `hkerC` hypothesis of `RBM.Gauss.hrhs_of_moment_inputs`, at `u = s_N` and `w = t_N`,
is *verbatim* the expression below; by `RBM.Gauss.one_add_norm_edge_eq` it equals `W_N^{τ'}`,
so no `N`-independent `Ck` bounds it.

Every theorem that consumes `hkerC` (or `hker2C`) with an `N`-independent constant is therefore
**vacuous** on the assembly window.  This is why §3 exists. -/
theorem no_const_edge_row_on_gridS {ξ : ℂ} (hξ : ‖ξ‖ = 1) {τ' : ℝ} (hτ' : 0 < τ')
    {W : ℕ → ℝ} (hW : ∀ N, 1 ≤ W N) (hWtop : Tendsto W atTop atTop) {Ck : ℝ} (k : ℕ)
    (h : ∀ N, 1 + ‖(((gridS (W N) τ' k : ℝ) : ℂ) - ((gridS (W N) τ' (k + 1) : ℝ) : ℂ)) * ξ‖
          * (1 - ‖((gridS (W N) τ' (k + 1) : ℝ) : ℂ) * ξ‖)⁻¹ ≤ Ck) :
    False := by
  refine no_const_gridS_ratio hτ' (fun N => lt_of_lt_of_le zero_lt_one (hW N)) hWtop
    (Ck := Ck) k (fun N => ?_)
  have hW0 : (0 : ℝ) < W N := lt_of_lt_of_le zero_lt_one (hW N)
  have hs0 : 0 ≤ gridS (W N) τ' k := gridS_nonneg (hW N) hτ'.le k
  have hst : gridS (W N) τ' k ≤ gridS (W N) τ' (k + 1) :=
    gridS_mono (hW N) hτ'.le (Nat.le_succ k)
  have ht1 : gridS (W N) τ' (k + 1) < 1 := gridS_lt_one hW0 (k + 1)
  rw [← one_add_norm_edge_eq hs0 hst ht1 hξ]
  exact h N

/-- `‖ξ_i‖ = 1` for the doubled charge of (5.85)/(5.103) as well. -/
theorem norm_xi2_eq_one {E : ℝ} (hE : |E| ≤ 2) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (i : Fin ((n + 2) + (n + 2))) : ‖SumZeroDyn.xi2 E σ i‖ = 1 := by
  unfold SumZeroDyn.xi2
  induction i using Fin.addCases with
  | left i => rw [Fin.append_left]; exact norm_xiOf_mSigma hE σ i
  | right i => rw [Fin.append_right]; exact norm_xiOf_mSigma hE σ i

/-- **`hkerC` has no constant on the grid.**  The literal `hkerC` slot of
`RBM.Gauss.hrhs_of_moment_inputs`, at `u = s_N`, `v_N = t_N`, on the grid of p. 24. -/
theorem no_const_hkerC_on_gridS {E : ℝ} (hE : |E| ≤ 2) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (i : Fin (n + 2)) {τ' : ℝ} (hτ' : 0 < τ') {W : ℕ → ℝ} (hW : ∀ N, 1 ≤ W N)
    (hWtop : Tendsto W atTop atTop) {Ck : ℝ} (k : ℕ)
    (h : ∀ N, 1 + ‖(((gridS (W N) τ' k : ℝ) : ℂ) - ((gridS (W N) τ' (k + 1) : ℝ) : ℂ))
            * xiOf (mSigma E) σ i‖
          * (1 - ‖((gridS (W N) τ' (k + 1) : ℝ) : ℂ) * xiOf (mSigma E) σ i‖)⁻¹ ≤ Ck) :
    False :=
  no_const_edge_row_on_gridS (norm_xiOf_mSigma hE σ i) hτ' hW hWtop k h

/-- **`hker2C` has no constant on the grid** either: the doubled charge also has `‖ξ‖ = 1`. -/
theorem no_const_hker2C_on_gridS {E : ℝ} (hE : |E| ≤ 2) {n : ℕ} (σ : Fin (n + 2) → Bool)
    (i : Fin ((n + 2) + (n + 2))) {τ' : ℝ} (hτ' : 0 < τ') {W : ℕ → ℝ} (hW : ∀ N, 1 ≤ W N)
    (hWtop : Tendsto W atTop atTop) {Ck : ℝ} (k : ℕ)
    (h : ∀ N, 1 + ‖(((gridS (W N) τ' k : ℝ) : ℂ) - ((gridS (W N) τ' (k + 1) : ℝ) : ℂ))
            * SumZeroDyn.xi2 E σ i‖
          * (1 - ‖((gridS (W N) τ' (k + 1) : ℝ) : ℂ) * SumZeroDyn.xi2 E σ i‖)⁻¹ ≤ Ck) :
    False :=
  no_const_edge_row_on_gridS (norm_xi2_eq_one hE σ i) hτ' hW hWtop k h

/-! ### §2  Minkowski for `momNorm` against an affine majorant

`RBM.Gauss.momNorm_le_of_le_weighted_sum` (T146) gives the triangle inequality only when every
summand has the **same** moment bound `M`; Jensen alone cannot do better.  The (7.16) estimate
`‖U ∘ G‖ ≤ c ψ(ω) + d` has a random first summand and a *deterministic* second one, so what is
needed is genuine Minkowski.  It is obtained from T146's lemma by rescaling the random summand
to unit moment norm, which equalises the two bounds. -/

section Minkowski

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- `‖d‖_q = d` for a non-negative constant, on a probability space. -/
theorem momNorm_const [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0) {d : ℝ} (hd : 0 ≤ d) :
    momNorm P q (fun _ => d) = d := by
  have h : ∫ _ω, |d| ^ q ∂P = d ^ q := by
    simp [integral_const, abs_of_nonneg hd]
  rw [momNorm, h, one_div]
  exact Real.pow_rpow_inv_natCast hd hq

/-- `‖a Y‖_q = a ‖Y‖_q` for `a ≥ 0`. -/
theorem momNorm_const_mul {q : ℕ} (hq : q ≠ 0) {a : ℝ} (ha : 0 ≤ a) (Y : Ω → ℝ) :
    momNorm P q (fun ω => a * Y ω) = a * momNorm P q Y := by
  have hpt : ∀ ω, |a * Y ω| ^ q = a ^ q * |Y ω| ^ q := by
    intro ω; rw [abs_mul, abs_of_nonneg ha, mul_pow]
  have hnn : (0 : ℝ) ≤ ∫ ω, |Y ω| ^ q ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  rw [momNorm, momNorm]
  simp only [hpt]
  rw [integral_const_mul, Real.mul_rpow (by positivity) hnn, one_div,
    Real.pow_rpow_inv_natCast ha hq]

/-- **Minkowski against an affine majorant.**  If `|Z| ≤ c Y + d` pointwise with `Y ≥ 0` and
`c, d ≥ 0` deterministic, then `‖Z‖_q ≤ c ‖Y‖_q + d`.

This is the step the moment form of (7.16) needs and that `momNorm_le_of_le_weighted_sum`
cannot supply: there the error term `d` and the main term have different moment norms. -/
theorem momNorm_le_affine [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0)
    {Y Z : Ω → ℝ} (hY0 : ∀ ω, 0 ≤ Y ω) (hint : Integrable (fun ω => Y ω ^ q) P)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hZ : ∀ ω, |Z ω| ≤ c * Y ω + d) :
    momNorm P q Z ≤ c * momNorm P q Y + d := by
  classical
  have habs : (fun ω => |Y ω| ^ q) = fun ω => Y ω ^ q := by
    funext ω; rw [abs_of_nonneg (hY0 ω)]
  have hintA : Integrable (fun ω => |Y ω| ^ q) P := by rwa [habs]
  have hm0 : 0 ≤ momNorm P q Y := momNorm_nonneg P q Y
  rcases hm0.eq_or_lt with hm | hmpos
  · -- `‖Y‖_q = 0`: then `Y = 0` a.e. and `|Z| ≤ d` a.e.
    have hzero : ∫ ω, |Y ω| ^ q ∂P = 0 := by
      have h := hm.symm
      rw [momNorm] at h
      have hnn : (0 : ℝ) ≤ ∫ ω, |Y ω| ^ q ∂P :=
        integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
      rcases hnn.eq_or_lt with h0 | h0
      · exact h0.symm
      · exact absurd h (ne_of_gt (Real.rpow_pos_of_pos h0 _))
    have hae : (fun ω => |Y ω| ^ q) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => pow_nonneg (abs_nonneg _) _) hintA).1 hzero
    have haeY : ∀ᵐ ω ∂P, Y ω = 0 := by
      filter_upwards [hae] with ω hω
      have : |Y ω| ^ q = 0 := hω
      have := pow_eq_zero_iff hq |>.1 this
      simpa [abs_eq_zero] using this
    have hZd : ∀ᵐ ω ∂P, |Z ω| ^ q ≤ |d| ^ q := by
      filter_upwards [haeY] with ω hω
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ q
      have := hZ ω
      rw [hω, mul_zero, zero_add] at this
      rwa [abs_of_nonneg hd]
    have hle : ∫ ω, |Z ω| ^ q ∂P ≤ ∫ _ω, |d| ^ q ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => pow_nonneg (abs_nonneg _) _)
        (integrable_const _) hZd
    have := Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _) hle
      (by positivity : (0:ℝ) ≤ (1:ℝ) / q)
    rw [← momNorm, ← momNorm] at this
    rw [momNorm_const hq hd] at this
    rw [← hm]
    simpa using this
  · -- `‖Y‖_q > 0`: rescale to unit moment norm, then apply the equal-bound Minkowski
    set m := momNorm P q Y with hmdef
    have hmne : m ≠ 0 := hmpos.ne'
    set cf : Fin 2 → ℝ := fun i => if i = 0 then c * m else d with hcfdef
    set Yf : Fin 2 → Ω → ℝ := fun i ω => if i = 0 then m⁻¹ * Y ω else 1 with hYfdef
    have hcf1 : cf 0 = c * m := by simp [hcfdef]
    have hcf2 : cf 1 = d := by simp [hcfdef]
    have hYf1 : Yf 0 = fun ω => m⁻¹ * Y ω := by funext ω; simp [hYfdef]
    have hYf2 : Yf 1 = fun _ : Ω => (1 : ℝ) := by funext ω; simp [hYfdef]
    have hsplit : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    have hcf0 : ∀ i, 0 ≤ cf i := by
      intro i
      rcases hsplit i with h | h <;> subst h
      · rw [hcf1]; exact mul_nonneg hc hmpos.le
      · rw [hcf2]; exact hd
    have hYf0 : ∀ i ω, 0 ≤ Yf i ω := by
      intro i ω
      rcases hsplit i with h | h <;> subst h
      · rw [hYf1]; exact mul_nonneg (inv_nonneg.2 hmpos.le) (hY0 ω)
      · rw [hYf2]; norm_num
    have hYfint : ∀ i, Integrable (fun ω => Yf i ω ^ q) P := by
      intro i
      rcases hsplit i with h | h <;> subst h
      · rw [hYf1]; simpa [mul_pow] using hint.const_mul (m⁻¹ ^ q)
      · rw [hYf2]; simp
    have hYfM : ∀ i, momNorm P q (Yf i) ≤ 1 := by
      intro i
      rcases hsplit i with h | h <;> subst h
      · rw [hYf1, momNorm_const_mul hq (inv_nonneg.2 hmpos.le), ← hmdef, inv_mul_cancel₀ hmne]
      · rw [hYf2, momNorm_const hq (zero_le_one : (0 : ℝ) ≤ 1)]
    have hZsum : ∀ ω, |Z ω| ≤ ∑ i, cf i * Yf i ω := by
      intro ω
      rw [Fin.sum_univ_two, hcf1, hcf2, hYf1, hYf2]
      have hrw : c * m * (m⁻¹ * Y ω) = c * Y ω := by field_simp
      rw [hrw, mul_one]
      exact hZ ω
    have key := momNorm_le_of_le_weighted_sum (P := P) hq hcf0 hYf0 hYfint
      (M := 1) zero_le_one hYfM hZsum
    rw [Fin.sum_univ_two, hcf1, hcf2, mul_one] at key
    exact key

end Minkowski

/-! ### §3  (7.16) in moment form: the replacement for `momNorm_Uker_apply_le`

`RBM.Gauss.momNorm_Uker_apply_le` (T146) is Lemma **7.1** in moment form: its constant is the
`l¹` row mass of `U`, which by §1 is `(η_u/η_v)^{n+2}` and is unbounded on the assembly grid.

`RBM.SumZeroDyn.norm_Uker_sumZero_scale_le` is Case 2 of **(7.16)** in the normalisation the
hierarchy uses: for a **sum-zero**, fast-decaying tensor of size `A_u^{-m} ψ + ζ` it returns
`C_m K^{2m} A_v^{-m} ψ + …`, i.e. the `r^m` of (7.16) has already been cancelled against the
`A^{-m}` normalisation and **no `(η_s/η_v)` prefactor is left on the main term** — which is
what (5.92) asserts.

What was missing is its moment form.  Here it is; the only analytic input beyond the pathwise
estimate is §2's Minkowski, because the pathwise bound is affine in `ψ(ω)`. -/

section Moment716

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- **Case 2 of (7.16) in moment form.**

For a tensor `G(ω)` which is, for every `ω`, sum-zero and `(ℓ_u K, δ)`-fast-decaying with
`|G(ω)_b| ≤ A_u^{-(n+2)} ψ(ω) + ζ`,

`‖(U_{u,v,σ} ∘ G(ω))_a‖_q ≤ C_{n} K^{2(n+2)} A_v^{-(n+2)} ‖ψ‖_q + (error)`.

Compare `RBM.Gauss.momNorm_Uker_apply_le`, whose constant is `Ck^{n+2}` with
`Ck = η_u/η_v` (§1): **the main term here has no such factor**, only the `K^{2(n+2)} = W^{Cτ}`
that `≺` absorbs.  The error term does carry `((1-s)/(1-v))^{n+2}`, but it multiplies `ζ` and
`δ`, which are the `W^{-D}` of (7.13) — the paper's `W^{-D + C_n}`.

The supremum over the tensor label `b` is *inside* `ψ`, not outside the moment: unlike
Lemma 7.1, (7.16) is not an `l¹` bound on the kernel and cannot be, since its constant is
strictly smaller than the `l¹` row mass.  That costs nothing at the `≺` level, because
`RBM.StochDom` is uniform in the index by construction — `RBM.badSet` quantifies over the
index *inside* the probability — so a `≺` bound on the entries is already one on the
supremum, with no union bound.

**On the `∀ ω`:** the sum-zero and fast-decay premises are stated for every `ω` here because
they are premises about `G`, not claims about the model; they are satisfiable (see
`RBM.Gauss.gridS_Q716_witness`, which exhibits a non-zero `G` meeting all of them with
`ζ = δ = 0`).  The model's own fast decay holds only on a high-probability event, and that
case is routed through `RBM.Gauss.momNorm_le_affine_on_event` of §4. -/
theorem momNorm_Uker_sumZero_scale_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖G ω b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (G ω))
    (hGz : ∀ ω, SumZero L (G ω)) (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) (u : ℂ) (v : ℂ) (G ω) a‖)
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ) := by
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith [hsu.trans huv]
  have hℓv : 0 < ellHat L (v : ℂ) := SumZeroDyn.ellHat_real_pos' L hL hv0 hv1
  have hc := SumZeroDyn.cKerSumZero_nonneg (n + 2)
  have hc' := SumZeroDyn.cKerSumZeroErr_nonneg (n + 2)
  set ρ : ℝ := (1 - s) / (1 - v) with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρdef]; positivity
  have hmain0 : (0 : ℝ) ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2))
      * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) := by positivity
  have herr0 : (0 : ℝ) ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ρ ^ (n + 2) * ζ
      + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ρ ^ (n + 2) * δ := by positivity
  refine momNorm_le_affine hq hψ0 hint hmain0 herr0 (fun ω => ?_)
  rw [abs_of_nonneg (norm_nonneg _)]
  have hpt := SumZeroDyn.norm_Uker_sumZero_scale_le L hL hE σ hs0 hsu huv hv0 hv1 hκA hK
    (hψ0 ω) hζ hδ (hGM ω) (hGd ω) (hGz ω) a
  refine hpt.trans (le_of_eq ?_)
  rw [hρdef]

end Moment716

/-! ### §3b  The same for an arbitrary edge parameter

`RBM.SumZeroDyn.norm_Uker_sumZero_scale_le` is stated for the charge `ξ = (m(σᵢ)m(σ_{i+1}))ᵢ`
of Definition 5.2.  The `E ⊗ E` term of (5.24) carries `RBM.SumZeroDyn.xi2`, which is a
`Fin.append` of two such families and is *not* of that form (the cyclic pairing differs at the
seam).  Since Case 2 of (7.16) (`RBM.norm_Uker_fastDecay_le_sumZero`) needs only
`0 < ‖ξᵢ‖ ≤ 1`, the primed statement below covers both. -/

section General716

/-- **(5.93)/(7.16) Case 2, for an arbitrary edge parameter** — the primed form of
`RBM.SumZeroDyn.norm_Uker_sumZero_scale_le`.  The main term carries no `(η_u/η_v)` factor:
the `r^m` of (7.16) has been absorbed by the change of normalisation `A_u^{-m} → A_v^{-m}`. -/
theorem norm_Uker_sumZero_scale_le' (L : ℕ) [NeZero L] (hL : 3 ≤ L) {m : ℕ} (hm : 2 ≤ m)
    {ξ : Fin m → ℂ} (hξ0 : ∀ i, ξ i ≠ 0) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ψ ζ δ : ℝ} (hK : 1 ≤ K) (hψ : 0 ≤ ψ) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : LoopArg L m → ℂ}
    (hGM : ∀ b, ‖G b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ + ζ)
    (hG : FastDecay L (ellHat L (u : ℂ) * K) δ G) {j : Fin m} (hz : SumZeroAt L j G)
    (a : LoopArg L m) :
    ‖Uker L ξ (u : ℂ) (v : ℂ) G a‖
      ≤ cKerSumZero m * K ^ (2 * m) * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * ψ
        + (cKerSumZero m * K ^ (2 * m) * ((1 - s) / (1 - v)) ^ m * ζ
          + cKerSumZeroErr m * (L : ℝ) ^ m * ((1 - s) / (1 - v)) ^ m * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  have hℓu := SumZeroDyn.ellHat_real_pos' L hL hu0 hu1
  have hℓv := SumZeroDyn.ellHat_real_pos' L hL (hu0.trans huv) hv1
  have h1u : (0 : ℝ) < 1 - u := by linarith
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have hM0 : 0 ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ + ζ := by positivity
  have key := norm_Uker_fastDecay_le_sumZero L hm hL hu0 huv hv0 hv1 hξ0 hξ hK hM0 hδ hGM hG hz a
  refine key.trans ?_
  set r := (1 - u) * ellHat L (u : ℂ) / ((1 - v) * ellHat L (v : ℂ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hrρ : r ≤ (1 - s) / (1 - v) := SumZeroDyn.ratio_le L hL hs0 hsu huv hv1
  have hcancel : r ^ m * (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m
      = (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m := by
    rw [← mul_pow]; congr 1; rw [hr]; field_simp
  have hc := SumZeroDyn.cKerSumZero_nonneg m
  have hc' := SumZeroDyn.cKerSumZeroErr_nonneg m
  have hK0 : (0 : ℝ) ≤ K ^ (2 * m) := by positivity
  have e1 : cKerSumZero m * K ^ (2 * m) * r ^ m
      * ((κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ + ζ)
      = cKerSumZero m * K ^ (2 * m) * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * ψ
        + cKerSumZero m * K ^ (2 * m) * r ^ m * ζ := by
    rw [← hcancel]; ring
  rw [e1, add_assoc]
  refine add_le_add le_rfl (add_le_add ?_ ?_)
  · gcongr
  · gcongr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- **(7.16) Case 2 in moment form, for an arbitrary edge parameter.**  This is the statement
that replaces `RBM.Gauss.momNorm_Uker_apply_le` in all three terms of `hrhs`, including the
`E ⊗ E` term with its `RBM.SumZeroDyn.xi2` charge. -/
theorem momNorm_Uker_sumZero_scale_le' [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    {ξ : Fin m → ℂ} (hξ0 : ∀ i, ξ i ≠ 0) (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {G : Ω → LoopArg L m → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖G ω b‖ ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ m * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (G ω))
    {j : Fin m} (hGz : ∀ ω, SumZeroAt L j (G ω)) (a : LoopArg L m) :
    momNorm P q (fun ω => ‖Uker L ξ (u : ℂ) (v : ℂ) (G ω) a‖)
      ≤ cKerSumZero m * K ^ (2 * m)
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m * momNorm P q ψ
        + (cKerSumZero m * K ^ (2 * m) * ((1 - s) / (1 - v)) ^ m * ζ
          + cKerSumZeroErr m * (L : ℝ) ^ m * ((1 - s) / (1 - v)) ^ m * δ) := by
  have h1v : (0 : ℝ) < 1 - v := by linarith
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith [hsu.trans huv]
  have hℓv : 0 < ellHat L (v : ℂ) := SumZeroDyn.ellHat_real_pos' L hL hv0 hv1
  have hc := SumZeroDyn.cKerSumZero_nonneg m
  have hc' := SumZeroDyn.cKerSumZeroErr_nonneg m
  set ρ : ℝ := (1 - s) / (1 - v) with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := by rw [hρdef]; positivity
  have hmain0 : (0 : ℝ) ≤ cKerSumZero m * K ^ (2 * m)
      * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ m := by positivity
  have herr0 : (0 : ℝ) ≤ cKerSumZero m * K ^ (2 * m) * ρ ^ m * ζ
      + cKerSumZeroErr m * (L : ℝ) ^ m * ρ ^ m * δ := by positivity
  refine momNorm_le_affine hq hψ0 hint hmain0 herr0 (fun ω => ?_)
  rw [abs_of_nonneg (norm_nonneg _)]
  have hpt := norm_Uker_sumZero_scale_le' L hL hm hξ0 hξ hs0 hsu huv hv0 hv1 hκA hK
    (hψ0 ω) hζ hδ (hGM ω) (hGd ω) (hGz ω) a
  refine hpt.trans (le_of_eq ?_)
  rw [hρdef]

end General716

/-! ### §4  The good-event split

T195 recorded the seam: `SumZero` survives `Q_u` as an algebraic identity (free, for every
`ω`), but **(7.13) — the fast decay — holds only on a high-probability event**.  So the moment
form of (7.16) has to be assembled the way `RBM.Gauss.hHol_flow` assembles its `Ξ`: the (7.16)
bound on `Ξ`, a crude deterministic envelope off it, and the measure of the complement paid
for by Markov.  `RBM.Gauss.momNorm_le_affine_on_event` is that step, once and for all.

Note the shape of the loss: `Env * P(Ξᶜ)^{1/q}` with `q = 2p` **fixed**, so the complement has
to be super-polynomially small — which is exactly what `RBM.HighProb` gives. -/

section Event

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- **Minkowski against an affine majorant, on a good event.**

`|Z| ≤ c Y + d` only on `Ξ`, `|Z| ≤ Env` everywhere, `P(Ξᶜ) ≤ pr`; then
`‖Z‖_q ≤ (c ‖Y‖_q + d) + Env · pr^{1/q}`. -/
theorem momNorm_le_affine_on_event [IsProbabilityMeasure P] {q : ℕ} (hq : q ≠ 0)
    {Y Z : Ω → ℝ} (hY0 : ∀ ω, 0 ≤ Y ω) (hYint : Integrable (fun ω => Y ω ^ q) P)
    (hZint : Integrable (fun ω => |Z ω| ^ q) P)
    {Ξ : Set Ω} (hΞ : MeasurableSet Ξ) {c d Env pr : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hEnv : 0 ≤ Env) (hpr : 0 ≤ pr)
    (hZΞ : ∀ ω ∈ Ξ, |Z ω| ≤ c * Y ω + d) (hZall : ∀ ω, |Z ω| ≤ Env)
    (hP : (P Ξᶜ).toReal ≤ pr) :
    momNorm P q Z ≤ (c * momNorm P q Y + d) + Env * pr ^ ((1 : ℝ) / q) := by
  classical
  have hq0 : (0 : ℝ) ≤ (1 : ℝ) / q := by positivity
  have hq1 : (1 : ℝ) / q ≤ 1 := by
    rw [div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hq)]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hq
  set Z' : Ω → ℝ := Set.indicator Ξ Z with hZ'def
  -- the truncated variable obeys the affine bound everywhere
  have hZ'le : ∀ ω, |Z' ω| ≤ c * Y ω + d := by
    intro ω
    by_cases hω : ω ∈ Ξ
    · rw [hZ'def, Set.indicator_of_mem hω]; exact hZΞ ω hω
    · rw [hZ'def, Set.indicator_of_notMem hω, abs_zero]
      have := hY0 ω; positivity
  have hmain : momNorm P q Z' ≤ c * momNorm P q Y + d :=
    momNorm_le_affine hq hY0 hYint hc hd hZ'le
  -- `∫ |Z'|^q = ∫_Ξ |Z|^q`
  have hind : (fun ω => |Z' ω| ^ q) = Set.indicator Ξ (fun ω => |Z ω| ^ q) := by
    funext ω
    by_cases hω : ω ∈ Ξ
    · rw [Set.indicator_of_mem hω, hZ'def, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, hZ'def, Set.indicator_of_notMem hω, abs_zero,
        zero_pow hq]
  have hZ'int : ∫ ω, |Z' ω| ^ q ∂P = ∫ ω in Ξ, |Z ω| ^ q ∂P := by
    rw [hind, integral_indicator hΞ]
  -- the complement
  have hcompl : ∫ ω in Ξᶜ, |Z ω| ^ q ∂P ≤ Env ^ q * pr := by
    have hmono : ∫ ω in Ξᶜ, |Z ω| ^ q ∂P ≤ ∫ _ω in Ξᶜ, Env ^ q ∂P :=
      setIntegral_mono_on hZint.integrableOn integrableOn_const
        hΞ.compl (fun ω _ => pow_le_pow_left₀ (abs_nonneg _) (hZall ω) q)
    refine hmono.trans ?_
    rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
    exact mul_le_mul_of_nonneg_left hP (by positivity)
  -- assemble
  have hsplit : ∫ ω, |Z ω| ^ q ∂P
      = (∫ ω in Ξ, |Z ω| ^ q ∂P) + ∫ ω in Ξᶜ, |Z ω| ^ q ∂P :=
    (integral_add_compl hΞ hZint).symm
  have hZ'0 : (0 : ℝ) ≤ ∫ ω, |Z' ω| ^ q ∂P :=
    integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _
  have hpow : (momNorm P q Z') ^ q = ∫ ω, |Z' ω| ^ q ∂P := by
    rw [momNorm, one_div]
    exact Real.rpow_inv_natCast_pow hZ'0 hq
  have hbound : ∫ ω, |Z ω| ^ q ∂P ≤ (momNorm P q Z') ^ q + Env ^ q * pr := by
    rw [hsplit, hpow, ← hZ'int]
    exact add_le_add le_rfl hcompl
  have hZ'n : (0 : ℝ) ≤ momNorm P q Z' := momNorm_nonneg P q Z'
  have hstep := Real.rpow_le_rpow (integral_nonneg fun _ => pow_nonneg (abs_nonneg _) _)
    hbound hq0
  rw [← momNorm] at hstep
  refine hstep.trans ?_
  have hsub : ((momNorm P q Z') ^ q + Env ^ q * pr) ^ ((1 : ℝ) / q)
      ≤ ((momNorm P q Z') ^ q) ^ ((1 : ℝ) / q) + (Env ^ q * pr) ^ ((1 : ℝ) / q) :=
    Real.rpow_add_le_add_rpow (by positivity) (by positivity) hq0 hq1
  refine hsub.trans ?_
  have h1 : ((momNorm P q Z') ^ q) ^ ((1 : ℝ) / q) = momNorm P q Z' := by
    rw [one_div]; exact Real.pow_rpow_inv_natCast (momNorm_nonneg P q Z') hq
  have h2 : (Env ^ q * pr) ^ ((1 : ℝ) / q) = Env * pr ^ ((1 : ℝ) / q) := by
    rw [Real.mul_rpow (by positivity) hpr, one_div,
      Real.pow_rpow_inv_natCast hEnv hq]
  rw [h1, h2]
  exact add_le_add hmain le_rfl

end Event

/-! ### §5  Satisfiability: the (7.16) premises are met on the paper's grid, by a non-zero
tensor that `Q_u` fixes

The danger this section rules out is the mirror image of §1's.  §1 shows the (7.1) slot is
*unsatisfiable* on the grid; a replacement that were satisfiable only because `Q_u` had
projected everything to `0` would be just as worthless.  So the witness below is explicit and
**non-zero**, it is sum-zero (hence `Q_u ∘ G = G`, `RBM.Qop_of_sumZero`), it is fast-decaying
with error `δ = 0`, and its data `(κA, K, ζ, δ)` do not depend on `N`. -/

section Witness

variable (L : ℕ) [NeZero L]

/-- A sum-zero row weight supported on `{0, 1}`. -/
def witEdge (c : ZMod L) : ℂ := (if c = 0 then 1 else 0) - (if c = 1 then 1 else 0)

/-- The witness tensor: `κ · 1(b₀ = 0) · ∏_{i≥1} witEdge(bᵢ)`.  It is sum-zero because
`∑_c witEdge c = 0`, supported in a ball of radius `1`, and equal to `κ` at the origin. -/
def witTensor (m : ℕ) (κ : ℂ) : LoopArg L (m + 2) → ℂ :=
  fun b => κ * ((if b 0 = 0 then 1 else 0) * ∏ i : Fin (m + 1), witEdge L (b i.succ))

theorem sum_witEdge (hL : 3 ≤ L) : ∑ c : ZMod L, witEdge L c = 0 := by
  have : Fact (1 < L) := ⟨by omega⟩
  simp [witEdge, Finset.sum_sub_distrib]

omit [NeZero L] in
theorem norm_witEdge_le (c : ZMod L) : ‖witEdge L c‖ ≤ 1 := by
  unfold witEdge
  split_ifs <;> norm_num

omit [NeZero L] in
theorem witEdge_eq_zero {c : ZMod L} (h0 : c ≠ 0) (h1 : c ≠ 1) :
    witEdge L c = 0 := by
  unfold witEdge; simp [h0, h1]

omit [NeZero L] in
theorem norm_witTensor_le {m : ℕ} {κ : ℂ} (b : LoopArg L (m + 2)) :
    ‖witTensor L m κ b‖ ≤ ‖κ‖ := by
  unfold witTensor
  rw [norm_mul, norm_mul, norm_prod]
  have h1 : ‖(if b 0 = 0 then (1 : ℂ) else 0)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have h2 : ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖ ≤ 1 := by
    calc ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖ ≤ ∏ _i : Fin (m + 1), (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_witEdge_le L _)
      _ = 1 := by simp
  have hp0 : (0 : ℝ) ≤ ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖ :=
    Finset.prod_nonneg fun i _ => norm_nonneg _
  have h3 : ‖(if b 0 = 0 then (1 : ℂ) else 0)‖ * ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖
      ≤ 1 := by
    calc ‖(if b 0 = 0 then (1 : ℂ) else 0)‖ * ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖
        ≤ 1 * ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖ := by gcongr
      _ = ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖ := one_mul _
      _ ≤ 1 := h2
  calc ‖κ‖ * (‖(if b 0 = 0 then (1 : ℂ) else 0)‖ * ∏ i : Fin (m + 1), ‖witEdge L (b i.succ)‖)
      ≤ ‖κ‖ * 1 := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = ‖κ‖ := mul_one _

omit [NeZero L] in
/-- The witness is `κ` at the origin, hence **not the zero tensor**. -/
theorem witTensor_zero_arg (hL : 3 ≤ L) {m : ℕ} (κ : ℂ) :
    witTensor L m κ (fun _ => 0) = κ := by
  have : Fact (1 < L) := ⟨by omega⟩
  unfold witTensor witEdge
  simp

omit [NeZero L] in
theorem witTensor_ne_zero (hL : 3 ≤ L) {m : ℕ} {κ : ℂ} (hκ : κ ≠ 0) :
    witTensor L m κ ≠ 0 := by
  intro h
  apply hκ
  rw [← witTensor_zero_arg L hL (m := m) κ, h]
  rfl

/-- **The witness is sum-zero.**  Hence `Q_u` fixes it (`RBM.Qop_of_sumZero`) and the (7.16)
premise is met without `Q_u` destroying anything. -/
theorem sumZero_witTensor (hL : 3 ≤ L) {m : ℕ} (κ : ℂ) : SumZero L (witTensor L m κ) := by
  intro x
  have hstep : ∀ r : LoopArg L (m + 1),
      witTensor L m κ (Fin.cons x r)
        = κ * ((if x = 0 then (1 : ℂ) else 0) * ∏ i : Fin (m + 1), witEdge L (r i)) := by
    intro r
    unfold witTensor
    simp
  rw [Psum, Finset.sum_congr rfl fun r _ => hstep r, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_prod_pi L (fun (_ : Fin (m + 1)) (c : ZMod L) => witEdge L c)]
  simp [sum_witEdge L hL]

/-- `Q_u` acts as the identity on the witness: the projection does **not** kill it. -/
theorem Qop_witTensor (hL : 3 ≤ L) {m : ℕ} (κ : ℂ) (t : ℂ) :
    Qop L t (witTensor L m κ) = witTensor L m κ :=
  Qop_of_sumZero L (sumZero_witTensor L hL κ)

/-- **The witness is fast-decaying with error exactly `0`**: it is supported on tensors all of
whose entries lie in `{0, 1}`, so any pair of indices at distance `> 1` forces the value `0`. -/
theorem fastDecay_witTensor (hL : 3 ≤ L) {m : ℕ} (κ : ℂ) {ℓ : ℝ} (hℓ : 1 < ℓ) :
    FastDecay L ℓ 0 (witTensor L m κ) := by
  have : Fact (1 < L) := ⟨by omega⟩
  rintro a ⟨i, j, hij⟩
  have hGa : witTensor L m κ a = 0 := by
    by_contra hne
    -- every entry of `a` lies in `{0, 1}`
    have hfac : (if a 0 = 0 then (1 : ℂ) else 0) * ∏ i : Fin (m + 1), witEdge L (a i.succ) ≠ 0 := by
      intro h
      exact hne (by unfold witTensor; rw [h, mul_zero])
    obtain ⟨hind, hprod⟩ := mul_ne_zero_iff.1 hfac
    have ha0 : a 0 = 0 := by
      by_contra h
      exact hind (by simp [h])
    have hall : ∀ k : Fin (m + 2), a k = 0 ∨ a k = 1 := by
      intro k
      refine Fin.cases (motive := fun k => a k = 0 ∨ a k = 1) (Or.inl ha0) (fun i => ?_) k
      have hne' : witEdge L (a i.succ) ≠ 0 := by
        have := Finset.prod_ne_zero_iff.1 hprod i (Finset.mem_univ i)
        exact this
      by_contra h
      push Not at h
      exact hne' (witEdge_eq_zero L h.1 h.2)
    -- hence all pairwise distances are at most `1`
    have hz : zdist L (a i - a j) ≤ 1 := by
      rcases hall i with hi | hi <;> rcases hall j with hj | hj <;> rw [hi, hj]
      · simp
      · simpa using zdist_neg_one_le L hL
      · simpa using zdist_one_le L hL
      · simp
    have : (zdist L (a i - a j) : ℝ) ≤ 1 := by exact_mod_cast hz
    linarith
  rw [hGa, norm_zero]

end Witness

section GridWitness

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- **The satisfiability witness on the paper's own grid** — the acceptance criterion of T201.

Take one window `s_N = s_k`, `v_N = s_{k+1}` of the grid `1 - s_j = W^{-jτ'}` of p. 24, i.e.
the window the six-step construction actually uses and on which
`RBM.Gauss.no_const_hkerC_on_gridS` shows the `hkerC` slot of
`RBM.Gauss.hrhs_of_moment_inputs` has **no** `N`-independent constant.  Then every premise of
`RBM.Gauss.momNorm_Uker_sumZero_scale_le` is met there, with

* `ζ = 0` and the (7.13) error `δ = 0` — the witness is *exactly* supported in a ball of
  radius `1`;
* `ψ ≡ 1`, the tensor being the time-`s_N` normalisation `A_{s_N}^{-(m+2)}` times a tensor of
  sup-norm one;
* `K = 3`, independent of `N` (any `K` with `ℓ_u K > 1` does, and `ℓ_u ≥ 1/2` always);

and the conclusion is the **time-`v_N`** normalisation `A_{v_N}^{-(m+2)}` times
`cKerSumZero (m+2) · 3^{2(m+2)}`, which does **not** depend on `N`.  Compare
`RBM.Gauss.momNorm_Uker_apply_le`, whose constant on the same window is `(W^{τ'})^{m+2}`.

The first two conjuncts are the anti-vacuity check demanded of a `Q_u` route: the tensor is
**not zero**, and `Q_u` fixes it, so the estimate is not a statement about `0`.

**No short-window hypothesis is used**: `hτ'` is only `0 ≤ τ'`, and `W` is arbitrary. -/
theorem gridS_Q716_witness [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {m : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (m + 2) → Bool)
    {W τ' : ℝ} (hW : 1 ≤ W) (hτ' : 0 ≤ τ') (k : ℕ) {κA : ℝ} (hκA : 0 < κA)
    (a : LoopArg L (m + 2)) :
    (witTensor L m
        (((κA * ((1 - gridS W τ' k) * ellHat L ((gridS W τ' k : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
      ≠ 0)
    ∧ Qop L ((gridS W τ' k : ℝ) : ℂ) (witTensor L m
        (((κA * ((1 - gridS W τ' k) * ellHat L ((gridS W τ' k : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ))
      = witTensor L m
        (((κA * ((1 - gridS W τ' k) * ellHat L ((gridS W τ' k : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ)
    ∧ momNorm P q (fun _ω => ‖Uker L (xiOf (mSigma E) σ) ((gridS W τ' k : ℝ) : ℂ)
          ((gridS W τ' (k + 1) : ℝ) : ℂ)
          (witTensor L m
            (((κA * ((1 - gridS W τ' k) * ellHat L ((gridS W τ' k : ℝ) : ℂ)))⁻¹ ^ (m + 2) : ℝ) : ℂ))
          a‖)
        ≤ cKerSumZero (m + 2) * 3 ^ (2 * (m + 2))
            * (κA * ((1 - gridS W τ' (k + 1))
                * ellHat L ((gridS W τ' (k + 1) : ℝ) : ℂ)))⁻¹ ^ (m + 2) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
  set s : ℝ := gridS W τ' k with hsdef
  set v : ℝ := gridS W τ' (k + 1) with hvdef
  have hs0 : 0 ≤ s := gridS_nonneg hW hτ' k
  have hsv : s ≤ v := gridS_mono hW hτ' (Nat.le_succ k)
  have hv1 : v < 1 := gridS_lt_one hW0 (k + 1)
  have hv0 : 0 ≤ v := hs0.trans hsv
  have hs1 : s < 1 := hsv.trans_lt hv1
  have hℓs : (1 : ℝ) / 2 ≤ ellHat L (s : ℂ) := half_le_ellHat_real L hL hs0 hs1
  have hℓs0 : (0 : ℝ) < ellHat L (s : ℂ) := by linarith
  have h1s : (0 : ℝ) < 1 - s := by linarith
  set c0 : ℝ := (κA * ((1 - s) * ellHat L (s : ℂ)))⁻¹ ^ (m + 2) with hc0def
  have hc00 : 0 < c0 := by rw [hc0def]; positivity
  refine ⟨witTensor_ne_zero L hL (by exact_mod_cast hc00.ne'),
    Qop_witTensor L hL _ _, ?_⟩
  -- the (7.16) premises
  have hdec : FastDecay L (ellHat L (s : ℂ) * 3) 0 (witTensor L m ((c0 : ℝ) : ℂ)) :=
    fastDecay_witTensor L hL _ (by linarith)
  have henv : ∀ (ω : Ω) (b : LoopArg L (m + 2)),
      ‖witTensor L m ((c0 : ℝ) : ℂ) b‖
        ≤ (κA * ((1 - s) * ellHat L (s : ℂ)))⁻¹ ^ (m + 2) * (1 : ℝ) + 0 := by
    intro ω b
    have h := norm_witTensor_le L (m := m) (κ := ((c0 : ℝ) : ℂ)) b
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc00.le] at h
    rw [← hc0def]; linarith
  have hint : Integrable (fun _ω : Ω => (1 : ℝ) ^ q) P := by simp
  have key := momNorm_Uker_sumZero_scale_le (P := P) L hL hq (n := m) hE σ
    hs0 (le_refl s) hsv hv0 hv1 hκA (K := 3) (ζ := 0) (δ := 0) (by norm_num) le_rfl le_rfl
    (G := fun _ω : Ω => witTensor L m ((c0 : ℝ) : ℂ)) (ψ := fun _ω : Ω => (1 : ℝ))
    (fun _ => zero_le_one) hint henv (fun _ => hdec)
    (fun _ => sumZero_witTensor L hL _) a
  rw [momNorm_const hq (zero_le_one : (0 : ℝ) ≤ 1)] at key
  simpa using key

end GridWitness

/-! ### §6  The five terms of (5.91)+(5.103) after `Q_u`, on the (7.16) tier

`RBM.MomentDuhamel.Hyp.momentDuhamelQ` — the `Q_t` route of (5.91) + (5.103), which T195 found
**has no consumer** — is the form in which §5.5 states Lemma 5.14: every tensor under a `U`
there has already been projected.  That is what makes (7.16) available, because the sum-zero
premise is then a *theorem* and not a hypothesis:

| term of `momentDuhamelQ` | tensor | sum-zero by |
|---|---|---|
| initial datum (5.91) | `Q_{s_N} ∘ (L-K)_{s_N}` | `RBM.SumZero_Qop` |
| drift (5.91) | `Q_u ∘ F_u` | `RBM.SumZero_Qop` |
| commutator (5.99) | `[Q_u, Θ_{u,σ}] ∘ (L-K)_u` | `RBM.SumZeroDyn.SumZero_commS` |
| `ϑ̇` term (5.100) | `(P ∘ (L-K)_u)_{b₀} · ϑ̇_{u,b}` | `RBM.SumZeroDyn.Psum_varthetaDot` |
| `E ⊗ E` (5.103) | `(Q_u ⊗ Q_u) ∘ (E ⊗ E)_u` | `RBM.SumZeroDyn.sumZeroAt_QQ` |

The five theorems below are the five applications of §3.  In each of them the only remaining
premises are (7.13) — the fast decay, which holds on a high-probability event and is therefore
routed through §4 — and the size envelope.  **None of them carries an `(η_u/η_v)` prefactor.**

This is the termwise content of "(5.92) holds with no prefactor depending on `η_s/η_t`". -/

section FiveTerms

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

open RBM.MomentDuhamel

/-- **Terms 1 and 2 of `momentDuhamelQ`** (the initial datum of (5.91) and its drift): the
tensor is `Q_u ∘ A`, so the sum-zero premise of (7.16) is discharged by `RBM.SumZero_Qop`. -/
theorem momNorm_Uker_Qop_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖Qop L ((u : ℝ) : ℂ) (A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (Qop L ((u : ℝ) : ℂ) (A ω)))
    (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (Qop L ((u : ℝ) : ℂ) (A ω)) a‖)
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ) :=
  momNorm_Uker_sumZero_scale_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA hK hζ hδ hψ0 hint hGM hGd
    (fun ω => SumZero_Qop L hL
      (SumZeroDyn.norm_ofReal_lt_one (hs0.trans hsu) (huv.trans_lt hv1)) (A ω)) a

/-- **Term 3 of `momentDuhamelQ`**, the commutator `[Q_u, Θ_{u,σ}]` of (5.99): sum-zero by
`RBM.SumZeroDyn.SumZero_commS` (that is (5.90)). -/
theorem momNorm_Uker_commS_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖SumZeroDyn.commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ
      (SumZeroDyn.commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)))
    (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.commS L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) (A ω)) a‖)
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  refine momNorm_Uker_sumZero_scale_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA hK hζ hδ hψ0 hint
    hGM hGd (fun ω => ?_) a
  exact SumZeroDyn.SumZero_commS L hL
    (fun i => norm_ofReal_mul_lt_one hu0 hu1 (norm_xiOf_mSigma hE σ i).le)
    (SumZeroDyn.norm_ofReal_lt_one hu0 hu1) (A ω)

/-- **Term 4 of `momentDuhamelQ`**, the `ϑ̇` term of (5.100): sum-zero because
`P ∘ ϑ̇_u = 0` (`RBM.SumZeroDyn.Psum_varthetaDot`, the `u`-derivative of `P ∘ ϑ_u = 1`). -/
theorem momNorm_Uker_PsumVarthetaDot_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L]
    (hL : 3 ≤ L) {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| ≤ 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {A : Ω → LoopArg L (n + 2) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ (ω : Ω) (b : LoopArg L (n + 2)),
      ‖Psum L (A ω) (b 0) * SumZeroDyn.varthetaDot L (n := n + 1) u b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ (n + 2) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ
      (fun b : LoopArg L (n + 2) =>
        Psum L (A ω) (b 0) * SumZeroDyn.varthetaDot L (n := n + 1) u b))
    (a : LoopArg L (n + 2)) :
    momNorm P q (fun ω => ‖Uker L (xiOf (mSigma E) σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (fun b : LoopArg L (n + 2) =>
          Psum L (A ω) (b 0) * SumZeroDyn.varthetaDot L (n := n + 1) u b) a‖)
      ≤ cKerSumZero (n + 2) * K ^ (2 * (n + 2))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ (n + 2) * momNorm P q ψ
        + (cKerSumZero (n + 2) * K ^ (2 * (n + 2)) * ((1 - s) / (1 - v)) ^ (n + 2) * ζ
          + cKerSumZeroErr (n + 2) * (L : ℝ) ^ (n + 2) * ((1 - s) / (1 - v)) ^ (n + 2) * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  refine momNorm_Uker_sumZero_scale_le L hL hq hE σ hs0 hsu huv hv0 hv1 hκA hK hζ hδ hψ0 hint
    hGM hGd (fun ω x => ?_) a
  rw [SumZeroDyn.Psum_mul_left, SumZeroDyn.Psum_varthetaDot L hL hu0 hu1, mul_zero]

/-- **Term 5 of `momentDuhamelQ`**, the `E ⊗ E` term of (5.103): sum-zero at the coordinate `0`
by `RBM.SumZeroDyn.sumZeroAt_QQ`, that is (5.104).  The charge is `RBM.SumZeroDyn.xi2`, which
is why §3b's arbitrary-`ξ` form is needed. -/
theorem momNorm_Uker_QQ_le [IsProbabilityMeasure P] (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    {q : ℕ} (hq : q ≠ 0) {n : ℕ} {E : ℝ} (hE : |E| < 2) (σ : Fin (n + 2) → Bool)
    {s u v : ℝ} (hs0 : 0 ≤ s) (hsu : s ≤ u) (huv : u ≤ v) (hv0 : 0 ≤ v) (hv1 : v < 1)
    {κA : ℝ} (hκA : 0 < κA) {K ζ δ : ℝ} (hK : 1 ≤ K) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    {A : Ω → LoopArg L ((n + 2) + (n + 2)) → ℂ} {ψ : Ω → ℝ} (hψ0 : ∀ ω, 0 ≤ ψ ω)
    (hint : Integrable (fun ω => ψ ω ^ q) P)
    (hGM : ∀ ω b, ‖SumZeroDyn.QQ L ((u : ℝ) : ℂ) (A ω) b‖
      ≤ (κA * ((1 - u) * ellHat L (u : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * ψ ω + ζ)
    (hGd : ∀ ω, FastDecay L (ellHat L (u : ℂ) * K) δ (SumZeroDyn.QQ L ((u : ℝ) : ℂ) (A ω)))
    (a : LoopArg L ((n + 2) + (n + 2))) :
    momNorm P q (fun ω => ‖Uker L (SumZeroDyn.xi2 E σ) ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        (SumZeroDyn.QQ L ((u : ℝ) : ℂ) (A ω)) a‖)
      ≤ cKerSumZero ((n + 2) + (n + 2)) * K ^ (2 * ((n + 2) + (n + 2)))
            * (κA * ((1 - v) * ellHat L (v : ℂ)))⁻¹ ^ ((n + 2) + (n + 2)) * momNorm P q ψ
        + (cKerSumZero ((n + 2) + (n + 2)) * K ^ (2 * ((n + 2) + (n + 2)))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2)) * ζ
          + cKerSumZeroErr ((n + 2) + (n + 2)) * (L : ℝ) ^ ((n + 2) + (n + 2))
              * ((1 - s) / (1 - v)) ^ ((n + 2) + (n + 2)) * δ) := by
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu1 : u < 1 := huv.trans_lt hv1
  refine momNorm_Uker_sumZero_scale_le' L hL hq (by omega) (SumZeroDyn.xi2_ne_zero hE σ)
    (SumZeroDyn.norm_xi2_le hE σ) hs0 hsu huv hv0 hv1 hκA hK hζ hδ hψ0 hint hGM hGd
    (j := 0) (fun ω => ?_) a
  exact SumZeroDyn.sumZeroAt_QQ L hL (SumZeroDyn.norm_ofReal_lt_one hu0 hu1) (A ω)

end FiveTerms

end RBM.Gauss


