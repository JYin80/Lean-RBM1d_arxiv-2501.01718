/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridDuhamel
import RBM1D.Gauss.GridStepDecomp
import RBM1D.Gauss.GridDriftAlgebra
import RBM1D.Gauss.GridQVConv
import RBM1D.Gauss.MomentDuhamel
import RBM1D.Hierarchy.ChargeReduce

/-!
# T1516 — the grid Duhamel expansion of `A_k`, with the `Z`/`Y`/drift/`R` split

Formalization of `docs/supervisor/2026-09-26-0048.md` §1 step 1, §1b, §1d: `A_k` (the `2`-loop
`(L-K)` at the grid time `u_k`) written as five terms, each already controlled by a merged or
in-flight lemma. This ticket is the algebra and the conditional-expectation bookkeeping: it
proves no new estimate.

## Main results

* `RBM.Gauss.Grid.lkFun_eq_Lval_sub_Kv` (T0) — `MomentDuhamel.lkFun` at `Step2.sigPM` is
  literally `Lval − Kv`.
* `RBM.Gauss.Grid.ukerMat`, `RBM.Gauss.Grid.Uker_eq_sum_ukerMat`, `RBM.Gauss.Grid.ukerMat_nonneg`
  (T1) — the real kernel matrix behind the unit-charge `Uker`.
* `RBM.Gauss.Grid.condExp_A_succ` (T2) — the discrete hierarchy step, restated with the named
  remainder `R_j`.
* `RBM.Gauss.Grid.grid_expansion` (T3) — the four-term expansion of `A_k` at a fixed `k ≤ K N`.
* `RBM.Gauss.Grid.grid_expansion_all` (T4) — the same, a.e. simultaneously for all `k ≤ K N`.

See `docs/reports/T1516-prove.md` for the math preflight, in particular the discharge of `hReal`
for the `(u,a)`-indexed test function `Φgrid` (the `(+,-)` `2`-loop reality argument via
`gloop_two_plus_minus_nonneg`, and the reality of `Kv` via `ChargeReduce.conj_Theta_apply`).
-/

noncomputable section

namespace RBM.Gauss.Grid

open RBM Matrix Finset MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.L2Operator

/-! ### (T0) : `MomentDuhamel.lkFun` at `Step2.sigPM` is `Lval − Kv` -/

section T0

variable {Ω' : Type*} [MeasurableSpace Ω']

theorem lkFun_eq_Lval_sub_Kv (B : Band Ω') (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) (a : LoopArg (B.L N) 2) :
    MomentDuhamel.lkFun B E N u M Step2.sigPM a = Lval B E N u M a - Kv B E N u a := by
  have hidx : LoopData.idx (Step2.sigPM, a)
      = (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) := by
    have hσ : List.ofFn (Step2.sigPM) = [true, false] := by
      show List.ofFn (![true, false] : Fin 2 → Bool) = [true, false]
      simp [List.ofFn_succ]
    unfold LoopData.idx
    rw [hσ]
  unfold MomentDuhamel.lkFun Lval Kv
  rw [hidx]

end T0

/-! ### (T1) : the real kernel matrix behind the unit-charge `Uker` -/

section T1

variable (L : ℕ) [NeZero L]

/-- **`ukerMat`**: the real matrix entry of the unit-charge kernel `Uker L (fun _ => 1) u v`,
read off by applying `Uker` to the indicator of `a` and taking the real part (T1509
`Uker_one_nonneg` shows this loses nothing for `0 ≤ u ≤ v < 1`). -/
noncomputable def ukerMat (u v : ℝ) (b a : LoopArg L 2) : ℝ :=
  (Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) (Pi.single a (1 : ℂ)) b).re

/-- The kernel entry `Uker L (fun _ => 1) u v` applied to the indicator of `a`, evaluated at
`b`, is exactly the product-of-`edgeKer` entry connecting `b` to `a`. -/
private theorem Uker_one_single (u v : ℝ) (b a : LoopArg L 2) :
    Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) (Pi.single a (1 : ℂ)) b
      = ∏ i : Fin 2, edgeKer L (1 : ℂ) (u : ℂ) (v : ℂ) (b i) (a i) := by
  classical
  rw [Uker_apply]
  have hterm : ∀ c : LoopArg L 2,
      (∏ i : Fin 2, edgeKer L (1 : ℂ) (u : ℂ) (v : ℂ) (b i) (c i))
          * (Pi.single a (1 : ℂ) : LoopArg L 2 → ℂ) c
        = if c = a then ∏ i : Fin 2, edgeKer L (1 : ℂ) (u : ℂ) (v : ℂ) (b i) (a i) else 0 := by
    intro c
    by_cases h : c = a
    · subst h; simp [Pi.single_apply]
    · simp [Pi.single_apply, h, Ne.symm h]
  simp_rw [hterm]
  simp

/-- **(T1a)**: `Uker L (fun _ => 1) u v A b = Σ_a (ukerMat L u v b a : ℂ) * A a`, for
`0 ≤ u ≤ v < 1`. -/
theorem Uker_eq_sum_ukerMat (hL : 3 ≤ L) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (A : LoopArg L 2 → ℂ) (b : LoopArg L 2) :
    Uker L (fun _ => (1 : ℂ)) (u : ℂ) (v : ℂ) A b
      = ∑ a : LoopArg L 2, (ukerMat L u v b a : ℂ) * A a := by
  rw [Uker_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  obtain ⟨r, hr0, hreq⟩ := Uker_one_nonneg hL hu0 huv hv1 b a
  have hentry : ukerMat L u v b a = r := by
    unfold ukerMat
    rw [Uker_one_single, hreq, Complex.ofReal_re]
  rw [hentry, ← hreq]

/-- **(T1b)**: `ukerMat` is nonnegative, for `0 ≤ u ≤ v < 1`. -/
theorem ukerMat_nonneg (hL : 3 ≤ L) {u v : ℝ} (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (b a : LoopArg L 2) :
    0 ≤ ukerMat L u v b a := by
  obtain ⟨r, hr0, hreq⟩ := Uker_one_nonneg hL hu0 huv hv1 b a
  have hentry : ukerMat L u v b a = r := by
    unfold ukerMat
    rw [Uker_one_single, hreq, Complex.ofReal_re]
  rw [hentry]; exact hr0

end T1

/-! ### `hReal`, `hC₂` for the `(u,a)`-indexed test function `Φgrid` — actually discharged -/

section Phi

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **`Φgrid`**: the `(u,a)`-indexed test function `Φ_{u,a}` of the ticket, built from the
globally `C²` `loopObs` (agreeing with `Lval − Kv` on the Hermitian submanifold, the only place
it is ever evaluated along the grid flow). -/
noncomputable def Φgrid (B : Band Ω') (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (B.L N) 2)
    (M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ) : ℂ :=
  loopObs B.toDims N (zt E u) (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) M
    - Kv B E N u a

/-- `Φgrid` agrees with `Lval − Kv` on Hermitian matrices, in particular along the grid flow. -/
theorem Φgrid_of_isHermitian (B : Band Ω') (E : ℝ) (N : ℕ) (u : ℝ) (a : LoopArg (B.L N) 2)
    {M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ} (hM : M.IsHermitian) :
    Φgrid B E N u a M = Lval B E N u M a - Kv B E N u a := by
  have hXY : loopObs B.toDims N (zt E u)
      (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) M = Lval B E N u M a := by
    unfold Lval
    exact loopObs_of_isHermitian (d := B.toDims) (N := N) hM
  unfold Φgrid
  rw [hXY]

/-- Two derivatives of a function are unaffected by subtracting an `M`-independent constant. -/
private theorem fderiv2_sub_const {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : Differentiable ℝ Φ) (c : ℂ) :
    fderiv ℝ (fderiv ℝ (fun M => Φ M - c)) = fderiv ℝ (fderiv ℝ Φ) := by
  have h1 : fderiv ℝ (fun M => Φ M - c) = fderiv ℝ Φ := by
    funext M
    exact ((hΦ M).hasFDerivAt.sub_const c).fderiv
  rw [h1]

/-- Subtracting an `M`-independent constant preserves the `TestFun` class. -/
theorem testFun_sub_const {d : Dims} {N : ℕ} {Φ : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (h : TestFun d N Φ) (c : ℂ) : TestFun d N (fun M => Φ M - c) := by
  have h1 : fderiv ℝ (fun M => Φ M - c) = fderiv ℝ Φ := by
    funext M
    exact ((h.differentiable M).hasFDerivAt.sub_const c).fderiv
  refine ⟨h.contDiff.sub contDiff_const, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bdd₀
    exact ⟨C + ‖c‖, fun M => (norm_sub_le _ _).trans (by linarith [hC M])⟩
  · rw [h1]; exact h.bdd₁
  · rw [h1]; exact h.bdd₂

/-- The loop index of the fixed shape `[true,false]` at any label pair is well-formed. -/
private theorem wf_pm (L : ℕ) (a : LoopArg L 2) :
    (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod L)).WF := rfl

private theorem len_pm (L : ℕ) (a : LoopArg L 2) :
    1 ≤ (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod L)).a.length := by
  have : (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod L)).a.length = 2 :=
    List.length_ofFn
  omega

/-- **`hReal`, actually discharged**: `Φgrid` is real on the Hermitian submanifold, for
`|E| ≤ 2` and `0 ≤ u < 1`. -/
theorem Φgrid_im_eq_zero (B : Band Ω') {E : ℝ} (hE : |E| ≤ 2) (N : ℕ) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (a : LoopArg (B.L N) 2) {M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ}
    (hM : M.IsHermitian) : (Φgrid B E N u a M).im = 0 := by
  rw [Φgrid_of_isHermitian B E N u a hM]
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  -- the `(+,-)` `2`-loop is a nonnegative real
  have hgloop : (Lval B E N u M a).im = 0 := by
    obtain ⟨r, _, hreq⟩ := gloop_two_plus_minus_nonneg (L := B.L N) (W := B.W N) (z := zt E u)
      hM (a 0) (a 1)
    have hLval : Lval B E N u M a
        = gloop (B.L N) (B.W N) M (zt E u) (⟨[true, false], [a 0, a 1]⟩ : LoopIdx (ZMod (B.L N))) := by
      unfold Lval; congr 1
    simp [hLval, hreq]
  -- `Kv` is real: `μ := m(+)m(-)` is real, hence so is `Theta` at `u·μ`
  have hKv : (Kv B E N u a).im = 0 := by
    set μ : ℂ := mSigma E true * mSigma E false with hμ
    have hμreal : μ = (Complex.normSq (mE E) : ℂ) := by
      rw [hμ, show mSigma E true = mE E from rfl, show mSigma E false = (starRingEnd ℂ) (mE E)
        from rfl, Complex.mul_conj]
    have hξ : ‖(u : ℂ) * μ‖ < 1 := by
      rw [hμ]; exact norm_mul_mSigma_lt_one hE hu0 hu1 true false
    have hconjμ : (starRingEnd ℂ) ((u : ℂ) * μ) = (u : ℂ) * μ := by
      have hcast : (u : ℂ) * μ = ((u * Complex.normSq (mE E) : ℝ) : ℂ) := by
        rw [hμreal]; push_cast; ring
      rw [hcast, Complex.conj_ofReal]
    have hKform : Kv B E N u a
        = (B.W N : ℂ)⁻¹ * μ * Theta (B.L N) ((u : ℂ) * μ) (a 0) (a 1) := by
      have hidx : Kv B E N u a = B.Kval E N u ⟨[true, false], [a 0, a 1]⟩ := by
        unfold Kv; congr 1
      rw [hidx, Band.Kval, Kgen_two, kTwo]
    have hthetaconj := ChargeReduce.conj_Theta_apply (B.L N) hL3 hξ (a 0) (a 1)
    rw [hconjμ] at hthetaconj
    have hthetaim : (Theta (B.L N) ((u : ℂ) * μ) (a 0) (a 1)).im = 0 := by
      have him := congrArg Complex.im hthetaconj
      rw [Complex.conj_im] at him
      linarith
    have hμim : μ.im = 0 := by simp [hμreal]
    simp [hKform, Complex.mul_im, Complex.inv_im, Complex.normSq_natCast, hμim, hthetaim]
  simp [Complex.sub_im, hgloop, hKv]

/-- `Φgrid` is a `TestFun`, for `|E| < 2` and any `u < 1`. -/
theorem Φgrid_testFun (B : Band Ω') {E : ℝ} (hEb : |E| < 2) (N : ℕ) {u : ℝ} (hu1 : u < 1)
    (a : LoopArg (B.L N) 2) : TestFun B.toDims N (Φgrid B E N u a) := by
  have hzu : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  have hTF : TestFun B.toDims N
      (loopObs B.toDims N (zt E u) (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))) :=
    testFun_loopObs_of_im_le hzu (abs_pos.mpr hzu) le_rfl (wf_pm (B.L N) a) (len_pm (B.L N) a)
  exact testFun_sub_const hTF (Kv B E N u a)

/-- **`hC₂`, an explicit uniform constant.** The second derivative of `Φgrid` is bounded by the
same constant `C₂` for every label `a`, since the loop shape `[true,false]` (hence `I.a.length =
2`) is the same for every `a`. -/
theorem Φgrid_bdd2 (B : Band Ω') {E : ℝ} (hEb : |E| < 2) (N : ℕ) {u η : ℝ} (hu1 : u < 1)
    (hη : 0 < η) (hzη : η ≤ |(zt E u).im|) (a : LoopArg (B.L N) 2)
    (M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ) :
    ‖fderiv ℝ (fderiv ℝ (Φgrid B E N u a)) M‖
      ≤ (Fintype.card (B.toDims.Idx N) : ℝ) * ((2 : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ 2) := by
  have hzu : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1
  obtain ⟨h1, h2, h3⟩ := le_two_mul_one_add_inv_cube hη
  have hbdd := bddC2C_loopObs (d := B.toDims) (N := N) (B := 2 * (1 + η⁻¹) ^ 3) hzu hη hzη h1 h2 h3
    (wf_pm (B.L N) a)
  have hfd : fderiv ℝ (Φgrid B E N u a) = fderiv ℝ
      (loopObs B.toDims N (zt E u) (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))) := by
    funext M'
    show fderiv ℝ (fun M => loopObs B.toDims N (zt E u)
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) M - Kv B E N u a) M' = _
    exact ((hbdd.differentiable M').hasFDerivAt.sub_const (Kv B E N u a)).fderiv
  have hbound := hbdd.bdd₂ M
  rw [← hfd] at hbound
  change ‖fderiv ℝ (fderiv ℝ (Φgrid B E N u a)) M‖
      ≤ (Fintype.card (B.toDims.Idx N) : ℝ)
        * (((List.ofFn a).length : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ (List.ofFn a).length)
    at hbound
  rw [List.length_ofFn] at hbound
  refine hbound.trans (le_of_eq ?_)
  norm_num

end Phi

/-! ### (T2) : the discrete hierarchy step, with the remainder `R_j` named -/

section T2

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **`A_j`**: the `2`-loop `(L-K)` at the grid time `u_j`, along the grid flow. -/
noncomputable def Agrid (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (ω : Ωg B.toDims) : LoopArg (B.L N) 2 → ℂ :=
  fun a => Lval B E N (time s t K N j) (H B.toDims s t K N j ω) a - Kv B E N (time s t K N j) a

/-- **`D_j`**: the deterministic `Δ`-drift `(eGterm + primBil(A_j,A_j))(H_j ω)` of T1506 (T4). -/
noncomputable def Dgrid (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (ω : Ωg B.toDims) : LoopArg (B.L N) 2 → ℂ :=
  fun a => eGterm (B.L N) (B.W N) (mSigma E) (H B.toDims s t K N j ω) (zt E (time s t K N j))
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))
      + primBil (B.L N) (B.W N)
          (gloop (B.L N) (B.W N) (H B.toDims s t K N j ω) (zt E (time s t K N j))
            - B.Kval E N (time s t K N j))
          (gloop (B.L N) (B.W N) (H B.toDims s t K N j ω) (zt E (time s t K N j))
            - B.Kval E N (time s t K N j))
          (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))

/-- **`R_j`**: the T1506 (T4) remainder, named by subtraction. -/
noncomputable def Rgrid (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (ω : Ωg B.toDims) (a : LoopArg (B.L N) 2) : ℂ :=
  (Pg B.toDims)[fun ω' => Agrid B E s t K N (j + 1) ω' a | filt B.toDims j] ω
    - Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
        (Agrid B E s t K N j ω) a
    - (step s t K N : ℂ) * Dgrid B E s t K N j ω a

/-- **(T2) `condExp_A_succ`**: the discrete hierarchy step, T1506's `discrete_hierarchy_step`
restated with `ξ ≡ 1` (via `Step2.sigPM_xi`) and the remainder named `R_j`. -/
theorem condExp_A_succ (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hst : s N < t N) (hj : j < K N) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N (j + 1) < 1) :
    ∀ᵐ ω ∂(Pg B.toDims), ∀ a : LoopArg (B.L N) 2,
      (Pg B.toDims)[fun ω' => Agrid B E s t K N (j + 1) ω' a | filt B.toDims j] ω
          = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
              (Agrid B E s t K N j ω) a
            + (step s t K N : ℂ) * Dgrid B E s t K N j ω a + Rgrid B E s t K N j ω a
        ∧ ‖Rgrid B E s t K N j ω a‖
            ≤ stepErr B E N (time s t K N j) (time s t K N (j + 1)) (step s t K N) := by
  have hdet := discrete_hierarchy_step B s t K N j E hEb hst hj hu0 hu1
  have hxi : xiOf (mSigma E) (![true, false] : Fin 2 → Bool) = fun _ => (1 : ℂ) :=
    Step2.sigPM_xi hEb.le
  rw [hxi] at hdet
  filter_upwards [hdet] with ω hω
  intro a
  exact ⟨by unfold Rgrid; ring, hω a⟩

end T2

/-! ### The grid Duhamel telescope, deterministic (clamped so that T1485's hypotheses hold
for every `k : ℕ`, then read back at the grid times on `k ≤ K N`) -/

section Telescope

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **The clamped grid Duhamel telescope.** T1485 `duhamel_telescope`'s hypotheses need the
semigroup law for *every* `k : ℕ`, but the raw grid times `time s t K N k` leave `[0,1)` once
`k > K N`. Clamping the index at `K N` keeps the times in `[s N, t N] ⊆ [0,1)` for every `k : ℕ`,
and agrees with the raw grid times on `k ≤ K N`, which is all `duhamel_telescope`'s conclusion at
`k ≤ K N` ever reads. -/
private theorem grid_duhamel_telescope (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0)
    (A' : ℕ → LoopArg (B.L N) 2 → ℂ) (k : ℕ) (hk : k ≤ K N) :
    A' k - Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ) (A' 0)
      = ∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
          (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
          (A' (j + 1) - Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (A' j)) := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  have hstep0 : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have huC_mem : ∀ i : ℕ, s N ≤ time s t K N (min i (K N)) ∧ time s t K N (min i (K N)) ≤ t N := by
    intro i
    constructor
    · have h0 : 0 ≤ ((min i (K N) : ℕ) : ℝ) * step s t K N := by positivity
      unfold time; linarith
    · have hle : ((min i (K N) : ℕ) : ℝ) ≤ (K N : ℝ) := by
        exact_mod_cast min_le_right i (K N)
      have hmul := mul_le_mul_of_nonneg_right hle hstep0
      have heq : time s t K N (K N) = t N := time_last s t K N hK0
      unfold time at heq ⊢
      linarith [hmul]
  have huC_lt1 : ∀ (i : ℕ) (l : Fin 2),
      ‖(time s t K N (min i (K N)) : ℂ) * (fun _ : Fin 2 => (1 : ℂ)) l‖ < 1 := by
    intro i l
    obtain ⟨hlo, hhi⟩ := huC_mem i
    simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (hs0.trans hlo)]
    linarith [hhi]
  have hsg := Uker_grid_semigroup (L := B.L N) (ξ := fun _ : Fin 2 => (1 : ℂ)) hL3
    (fun i => time s t K N (min i (K N))) huC_lt1
  obtain ⟨hself, hcomp⟩ := hsg
  have htele := duhamel_telescope
    (fun i j => UkerHom (B.L N) (fun _ : Fin 2 => (1 : ℂ))
      (time s t K N (min i (K N)) : ℂ) (time s t K N (min j (K N)) : ℂ)) hself hcomp A' k
  simp only [UkerHom_apply] at htele
  have hclamp : ∀ i : ℕ, i ≤ K N → time s t K N (min i (K N)) = time s t K N i := by
    intro i hi; rw [min_eq_left hi]
  have h0K : (0 : ℕ) ≤ K N := Nat.zero_le _
  rw [hclamp 0 h0K, hclamp k hk] at htele
  rw [htele]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  have hj1 : j + 1 ≤ K N := by omega
  have hj0 : j ≤ K N := by omega
  rw [hclamp (j + 1) hj1, hclamp j hj0]

end Telescope

/-! ### The per-step summand, matching T1505's `stepZ`/`stepY` and T1506's `R_j` -/

section Summand

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **`hIntReal`, discharged.** `stepZ` (real-valued) is integrable: from `g_eq_pointwise`,
`g = h0 + Zc + R` pointwise (`T1505`), so `Zc = g - h0 - R` is integrable (`integrable_h0`,
`integrable_Rlabel_sum`, already merged); `stepZ = Zc.re`, and `Integrable.re` transfers
integrability from `Zc` to `stepZ`. -/
private theorem stepZ_integrable (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) (E : ℝ)
    {u : ℝ} (hΦ : ∀ a, TestFun B.toDims N (Φgrid B E N u a))
    (hReal : ∀ a M, M.IsHermitian → (Φgrid B E N u a M).im = 0)
    {C₂ : ℝ} (hC₂ : ∀ a M, ‖fderiv ℝ (fderiv ℝ (Φgrid B E N u a)) M‖ ≤ C₂)
    (hΔ : 0 ≤ step s t K N) (U : LoopArg (B.L N) 2 → LoopArg (B.L N) 2 → ℝ)
    (b : LoopArg (B.L N) 2) :
    Integrable (stepZ B.toDims s t K N j (Φgrid B E N u) U b) (Pg B.toDims) := by
  have hg_int := integrable_h0 B.toDims s t K N (j + 1) hΦ U b
  have hh0_int := integrable_h0 B.toDims s t K N j hΦ U b
  have hR_int := integrable_Rlabel_sum B.toDims s t K N j hΦ hC₂ hΔ U b
  have hZeq : (fun ω => (stepZ B.toDims s t K N j (Φgrid B E N u) U b ω : ℂ))
      = (fun ω => ∑ a : LoopArg (B.L N) 2,
            (U b a : ℂ) * Φgrid B E N u a (H B.toDims s t K N (j + 1) ω))
        - (fun ω => ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φgrid B E N u a (H B.toDims s t K N j ω))
        - (fun ω => ∑ a : LoopArg (B.L N) 2,
              (U b a : ℂ) * Rlabel B.toDims s t K N j (Φgrid B E N u a) ω) := by
    funext ω
    have hg : (∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φgrid B E N u a (H B.toDims s t K N (j + 1) ω))
        = (∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φgrid B E N u a (H B.toDims s t K N j ω))
          + (stepZ B.toDims s t K N j (Φgrid B E N u) U b ω : ℂ)
          + (∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Rlabel B.toDims s t K N j (Φgrid B E N u a) ω) :=
      g_eq_pointwise B.toDims s t K N j hΦ hReal U b ω
    simp only [Pi.sub_apply]
    rw [hg]; ring
  have hZc_int : Integrable (fun ω => (stepZ B.toDims s t K N j (Φgrid B E N u) U b ω : ℂ))
      (Pg B.toDims) := by
    rw [hZeq]; exact (hg_int.sub hh0_int).sub hR_int
  have hre : (fun ω => RCLike.re ((stepZ B.toDims s t K N j (Φgrid B E N u) U b ω : ℝ) : ℂ))
      = stepZ B.toDims s t K N j (Φgrid B E N u) U b := funext fun ω => RCLike.ofReal_re _
  rw [← hre]
  exact hZc_int.re

/-- **The per-step summand identity.** For `j+1 ≤ k ≤ K N`, a.e. `ω`, the `j`-th summand of the
telescoping expansion splits exactly into `stepZ + stepY` (T1505) plus the drift and remainder
images under `U_{j+1,k}` (T1506's `D_j`, `R_j`), with `Φ := Φgrid` at `u_{j+1}` and
`U := ukerMat (u_{j+1}, u_k)`. -/
private theorem grid_step_summand_ae (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hst : s N < t N) (hj : j < K N) (hu0j : 0 ≤ time s t K N j)
    (hu0j1 : 0 ≤ time s t K N (j + 1)) (hu1j1 : time s t K N (j + 1) < 1) (k : ℕ)
    (huj1k : time s t K N (j + 1) ≤ time s t K N k) (hu1k : time s t K N k < 1)
    (b : LoopArg (B.L N) 2) :
    ∀ᵐ ω ∂(Pg B.toDims),
      Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
          (Agrid B E s t K N (j + 1) ω - Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (Agrid B E s t K N j ω)) b
        = (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ)
          + stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω
          + (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b
          + Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b := by
  have hL3 : 3 ≤ B.L N := B.three_le_L N
  set Φ : LoopArg (B.L N) 2 → Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ → ℂ
      := Φgrid B E N (time s t K N (j + 1)) with hΦdef
  set U : LoopArg (B.L N) 2 → LoopArg (B.L N) 2 → ℝ
      := ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k) with hUdef
  have hzu1 : (zt E (time s t K N (j + 1))).im ≠ 0 := zt_im_ne_zero_of_lt_one hEb hu1j1
  have hη : 0 < |(zt E (time s t K N (j + 1))).im| := abs_pos.mpr hzu1
  have hΦtf : ∀ a, TestFun B.toDims N (Φ a) := fun a => Φgrid_testFun B hEb N hu1j1 a
  have hReal : ∀ a M, M.IsHermitian → (Φ a M).im = 0 :=
    fun a M hM => Φgrid_im_eq_zero B hEb.le N hu0j1 hu1j1 a hM
  have hC₂ : ∀ a M, ‖fderiv ℝ (fderiv ℝ (Φ a)) M‖
      ≤ (Fintype.card (B.toDims.Idx N) : ℝ)
          * ((2 : ℝ) ^ 2 * (2 * (1 + |(zt E (time s t K N (j + 1))).im|⁻¹) ^ 3) ^ 2) :=
    fun a M => Φgrid_bdd2 B hEb N hu1j1 hη le_rfl a M
  have hΔ0 : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hIntReal : Integrable (stepZ B.toDims s t K N j Φ U b) (Pg B.toDims) :=
    stepZ_integrable B s t K N j E hΦtf hReal hC₂ hΔ0 U b
  have hSD := stepDecomp B.toDims s t K N j hΦtf hReal hC₂ hΔ0 U b hIntReal
  have hXiEq : ∀ ω : Ωg B.toDims, stepXi B.toDims s t K N j Φ U b ω
      = (stepZ B.toDims s t K N j Φ U b ω : ℂ) + stepY B.toDims s t K N j Φ U b ω := hSD.1
  have hΦeqAgrid : ∀ a (ω : Ωg B.toDims),
      Φ a (H B.toDims s t K N (j + 1) ω) = Agrid B E s t K N (j + 1) ω a :=
    fun a ω => Φgrid_of_isHermitian B E N (time s t K N (j + 1)) a
      (H_isHermitian B.toDims s t K N (j + 1) ω)
  have hint_a : ∀ a ∈ (Finset.univ : Finset (LoopArg (B.L N) 2)),
      Integrable (fun ω => (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω)) (Pg B.toDims) :=
    fun a _ => (integrable_Phi_H B.toDims s t K N (j + 1) (hΦtf a)).const_mul (U b a : ℂ)
  have hcondsum := condExp_finsetSum hint_a (filt B.toDims j)
  have hCEsum : ∀ᵐ ω ∂(Pg B.toDims),
      (Pg B.toDims)[fun ω' => ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω')
          | filt B.toDims j] ω
        = ∑ a : LoopArg (B.L N) 2, (U b a : ℂ)
            * (Pg B.toDims)[fun ω' => Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω := by
    have hsum_fn : (∑ a : LoopArg (B.L N) 2,
          fun ω' => (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω'))
        = (fun ω' => ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω')) := by
      funext ω'; simp only [Finset.sum_apply]
    rw [← hsum_fn]
    have hsmul_ae : ∀ᵐ ω ∂(Pg B.toDims), ∀ a : LoopArg (B.L N) 2,
        (Pg B.toDims)[fun ω' => (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω
          = (U b a : ℂ)
              * (Pg B.toDims)[fun ω' => Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω :=
      ae_all_iff.mpr fun a => condExp_smul (U b a : ℂ)
        (fun ω' => Φ a (H B.toDims s t K N (j + 1) ω')) (filt B.toDims j)
    filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
    rw [hω1]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hω2 a
  have hT2 := condExp_A_succ B s t K N j E hEb hst hj hu0j hu1j1
  filter_upwards [hCEsum, hT2] with ω hωCE hω3
  have hUsum : ∀ X : LoopArg (B.L N) 2 → ℂ,
      Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) X b
        = ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * X a :=
    fun X => Uker_eq_sum_ukerMat (B.L N) hL3 hu0j1 huj1k hu1k X b
  have hstepXi_eq : stepXi B.toDims s t K N j Φ U b ω
      = (∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω))
        - ∑ a : LoopArg (B.L N) 2, (U b a : ℂ)
            * (Pg B.toDims)[fun ω' => Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω := by
    show (∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω))
        - (Pg B.toDims)[fun ω' => ∑ a : LoopArg (B.L N) 2,
            (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω
        = _
    rw [hωCE]
  rw [hUsum]
  simp only [Pi.sub_apply]
  calc ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * (Agrid B E s t K N (j + 1) ω a
        - Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
            (Agrid B E s t K N j ω) a)
      = ∑ a : LoopArg (B.L N) 2, ((U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω)
          - (U b a : ℂ)
              * (Pg B.toDims)[fun ω' => Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω
          + (U b a : ℂ) * (step s t K N : ℂ) * Dgrid B E s t K N j ω a
          + (U b a : ℂ) * Rgrid B E s t K N j ω a) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hΦeqAgrid a ω]
        have hfeq : (fun ω' => Φ a (H B.toDims s t K N (j + 1) ω'))
            = (fun ω' => Agrid B E s t K N (j + 1) ω' a) := funext fun ω' => hΦeqAgrid a ω'
        have hCEeq : (Pg B.toDims)[fun ω' => Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω
            = (Pg B.toDims)[fun ω' => Agrid B E s t K N (j + 1) ω' a | filt B.toDims j] ω := by
          rw [hfeq]
        have h3 := (hω3 a).1
        rw [hCEeq, h3]; ring
    _ = (∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Φ a (H B.toDims s t K N (j + 1) ω))
          - ∑ a : LoopArg (B.L N) 2,
              (U b a : ℂ)
                * (Pg B.toDims)[fun ω' => Φ a (H B.toDims s t K N (j + 1) ω') | filt B.toDims j] ω
          + ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * (step s t K N : ℂ) * Dgrid B E s t K N j ω a
          + ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * Rgrid B E s t K N j ω a := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = stepXi B.toDims s t K N j Φ U b ω
          + (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b
          + Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b := by
        have hUsumD : (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b
            = ∑ a : LoopArg (B.L N) 2, (U b a : ℂ) * (step s t K N : ℂ) * Dgrid B E s t K N j ω a := by
          rw [hUsum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
        rw [← hstepXi_eq, ← hUsumD, ← hUsum (Rgrid B E s t K N j ω)]
    _ = (stepZ B.toDims s t K N j Φ U b ω : ℂ) + stepY B.toDims s t K N j Φ U b ω
          + (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b
          + Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b := by
        rw [hXiEq ω]

end Summand

/-! ### (T3)/(T4) : the four-term expansion of `A_k`, at a fixed `k ≤ K N` and then for all -/

section Expansion

variable {Ω' : Type*} [MeasurableSpace Ω']

private theorem time_mono (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (hst : s N ≤ t N) {i j : ℕ}
    (hij : i ≤ j) : time s t K N i ≤ time s t K N j := by
  have hstep0 : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold time
  nlinarith [hstep0]

/-- **(T3) `grid_expansion`**: for a fixed `k ≤ K N`, a.e. `ω`, for every label `b`, `A_k ω b`
splits into the initial term, the `Z`/`Y` sums (T1505), the drift sum and the remainder sum
(T1506), each pushed through `U_{j+1,k}`. -/
theorem grid_expansion (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) (hK1 : 1 ≤ K N) (k : ℕ) (hk : k ≤ K N) :
    ∀ᵐ ω ∂(Pg B.toDims), ∀ b : LoopArg (B.L N) 2,
      Agrid B E s t K N k ω b
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
              (Agrid B E s t K N 0 ω) b
          + (∑ j ∈ Finset.range k, (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
                  (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ))
          + (∑ j ∈ Finset.range k, stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
                (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω)
          + (∑ j ∈ Finset.range k, (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b)
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b) := by
  have hK0 : K N ≠ 0 := by omega
  have htele : ∀ ω : Ωg B.toDims,
      Agrid B E s t K N k ω
          - Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
              (Agrid B E s t K N 0 ω)
        = ∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
            (Agrid B E s t K N (j + 1) ω - Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (Agrid B E s t K N j ω)) :=
    fun ω => grid_duhamel_telescope B s t K N hs0 hst.le ht1 hK0
      (fun j => Agrid B E s t K N j ω) k hk
  have htimelast : time s t K N (K N) = t N := time_last s t K N hK0
  have hsummand : ∀ j : ℕ, j < k → ∀ᵐ ω ∂(Pg B.toDims), ∀ b : LoopArg (B.L N) 2,
      Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
          (Agrid B E s t K N (j + 1) ω - Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (Agrid B E s t K N j ω)) b
        = (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ)
          + stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω
          + (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b
          + Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b := by
    intro j hjk
    have hjK : j < K N := lt_of_lt_of_le hjk hk
    have hu0j : 0 ≤ time s t K N j := by
      have := time_mono s t K N hst.le (Nat.zero_le j)
      rw [time_zero] at this; linarith
    have hu0j1 : 0 ≤ time s t K N (j + 1) := by
      have := time_mono s t K N hst.le (Nat.zero_le (j + 1))
      rw [time_zero] at this; linarith
    have hu1j1 : time s t K N (j + 1) < 1 := by
      have h1 : time s t K N (j + 1) ≤ time s t K N (K N) :=
        time_mono s t K N hst.le (by omega)
      rw [htimelast] at h1; linarith
    have huj1k : time s t K N (j + 1) ≤ time s t K N k :=
      time_mono s t K N hst.le (by omega)
    have hu1k : time s t K N k < 1 := by
      have h1 : time s t K N k ≤ time s t K N (K N) := time_mono s t K N hst.le hk
      rw [htimelast] at h1; linarith
    exact ae_all_iff.mpr fun b =>
      grid_step_summand_ae B s t K N j E hEb hst hjK hu0j hu0j1 hu1j1 k huj1k hu1k b
  have hsummand_all : ∀ᵐ ω ∂(Pg B.toDims), ∀ j : ℕ, j < k → ∀ b : LoopArg (B.L N) 2,
      Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
          (Agrid B E s t K N (j + 1) ω - Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (Agrid B E s t K N j ω)) b
        = (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ)
          + stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω
          + (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b
          + Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b := by
    refine ae_all_iff.mpr fun j => ?_
    by_cases hjk : j < k
    · filter_upwards [hsummand j hjk] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hjk
  filter_upwards [hsummand_all] with ω hω
  intro b
  have hkeyb := congrFun (htele ω) b
  simp only [Pi.sub_apply] at hkeyb
  rw [Finset.sum_apply] at hkeyb
  have hsum_eq : ∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
        (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
        (Agrid B E s t K N (j + 1) ω - Uker (B.L N) (fun _ => (1 : ℂ))
            (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (Agrid B E s t K N j ω)) b
      = (∑ j ∈ Finset.range k, (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ))
        + (∑ j ∈ Finset.range k, stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
              (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω)
        + (∑ j ∈ Finset.range k, (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b)
        + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b) := by
    refine Eq.trans (Finset.sum_congr rfl fun j hj => hω j (Finset.mem_range.mp hj) b) ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hsum_eq] at hkeyb
  linear_combination hkeyb

/-- **(T4) `grid_expansion_all`**: the same statement, a.e. simultaneously for every `k ≤ K N`. -/
theorem grid_expansion_all (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) (hK1 : 1 ≤ K N) :
    ∀ᵐ ω ∂(Pg B.toDims), ∀ k : ℕ, k ≤ K N → ∀ b : LoopArg (B.L N) 2,
      Agrid B E s t K N k ω b
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
              (Agrid B E s t K N 0 ω) b
          + (∑ j ∈ Finset.range k, (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
                  (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ))
          + (∑ j ∈ Finset.range k, stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
                (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω)
          + (∑ j ∈ Finset.range k, (step s t K N : ℂ) * Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω) b)
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω) b) := by
  refine ae_all_iff.mpr fun k => ?_
  by_cases hk : k ≤ K N
  · filter_upwards [grid_expansion B s t K N E hEb hs0 hst ht1 hK1 k hk] with ω hω _
    exact hω
  · exact Filter.Eventually.of_forall fun _ h => absurd h hk

end Expansion

/-! ### Repair (audit RETURN): `U`-linearity of `stepZ`/`stepY`, and the `k`-independent
label vectors in the input shape of T1504 (T1′/T1″/T2), T1504 (T3) and T1510 -/

section Bridge

/-- **`gridDelta`**: the identity kernel on labels, `δ b a := if b = a then 1 else 0`. -/
def gridDelta (L : ℕ) (b a : LoopArg L 2) : ℝ := if b = a then 1 else 0

variable (d : Dims) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)

/-- `lin` of `Ab` is the `U`-weighted sum of the per-label `lin`s (real-linearity in `U`). -/
private theorem lin_Ab_eq_sum' (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)
    (ω : Ωg d) (X : Matrix (d.Idx N) (d.Idx N) ℂ) :
    lin N (Ab d s t K N j Φ U b ω) X
      = ∑ a : LoopArg (d.L N) 2, U b a * lin N (gradMat (Φ a) (H d s t K N j ω)) X := by
  unfold lin Ab
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ a : LoopArg (d.L N) 2,
      Matrix.trace ((U b a : ℂ) • gradMat (Φ a) (H d s t K N j ω) * X)
        = (U b a : ℂ) * Matrix.trace (gradMat (Φ a) (H d s t K N j ω) * X) := by
    intro a
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- `stepZ` at the identity kernel is the single-label linear term. -/
private theorem stepZ_gridDelta (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (a : LoopArg (d.L N) 2) (ω : Ωg d) :
    stepZ d s t K N j Φ (gridDelta (d.L N)) a ω
      = Real.sqrt (step s t K N)
          * lin N (gradMat (Φ a) (H d s t K N j ω)) (Xmat d N (ω (j + 1))) := by
  unfold stepZ
  rw [lin_Ab_eq_sum']
  congr 1
  rw [Finset.sum_eq_single a]
  · simp [gridDelta]
  · intro c _ hc
    simp [gridDelta, Ne.symm hc]
  · simp

/-- **`stepZ` is linear in the real kernel `U`** (pointwise, every `ω`):
`stepZ U b ω = Σ_a U(b,a) · stepZ δ a ω`. -/
theorem stepZ_eq_sum_gridDelta (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) (ω : Ωg d) :
    stepZ d s t K N j Φ U b ω
      = ∑ a : LoopArg (d.L N) 2, U b a * stepZ d s t K N j Φ (gridDelta (d.L N)) a ω := by
  rw [show stepZ d s t K N j Φ U b ω = Real.sqrt (step s t K N)
      * lin N (Ab d s t K N j Φ U b ω) (Xmat d N (ω (j + 1))) from rfl, lin_Ab_eq_sum',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [stepZ_gridDelta]
  ring

/-- **(R1) `stepZ_ukerMat_eq_Uker`**: for every `ω` and `0 ≤ v ≤ w < 1`, the kernel folded into
the label weight equals the kernel `Uker(v,w)` applied to the `k`-independent label vector
`a ↦ stepZ δ a ω`. -/
theorem stepZ_ukerMat_eq_Uker (Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ)
    {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) (b : LoopArg (d.L N) 2) (ω : Ωg d) :
    (stepZ d s t K N j Φ (ukerMat (d.L N) v w) b ω : ℂ)
      = Uker (d.L N) (fun _ => (1 : ℂ)) (v : ℂ) (w : ℂ)
          (fun a => (stepZ d s t K N j Φ (gridDelta (d.L N)) a ω : ℂ)) b := by
  rw [Uker_eq_sum_ukerMat (d.L N) (d.three_le_L N) hv0 hvw hw1, stepZ_eq_sum_gridDelta]
  push_cast
  rfl

/-- **`stepXi` is linear in the real kernel `U`**, a.e., simultaneously for all labels `b`. -/
theorem stepXi_eq_sum_gridDelta_ae {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) :
    ∀ᵐ ω ∂(Pg d), ∀ b : LoopArg (d.L N) 2,
      stepXi d s t K N j Φ U b ω
        = ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * stepXi d s t K N j Φ (gridDelta (d.L N)) a ω := by
  have hfun : ∀ a : LoopArg (d.L N) 2,
      (fun ω' => ∑ c : LoopArg (d.L N) 2,
          ((gridDelta (d.L N) a c : ℝ) : ℂ) * Φ c (H d s t K N (j + 1) ω'))
        = fun ω' => Φ a (H d s t K N (j + 1) ω') := by
    intro a; funext ω'
    rw [Finset.sum_eq_single a]
    · simp [gridDelta]
    · intro c _ hc
      simp [gridDelta, Ne.symm hc]
    · simp
  have hδ : ∀ a (ω : Ωg d), stepXi d s t K N j Φ (gridDelta (d.L N)) a ω
      = Φ a (H d s t K N (j + 1) ω)
        - (Pg d)[fun ω' => Φ a (H d s t K N (j + 1) ω') | filt d j] ω := by
    intro a ω
    have h1 := congrFun (hfun a) ω
    unfold stepXi
    rw [h1, hfun a]
  refine ae_all_iff.mpr fun b => ?_
  have hint_a : ∀ a ∈ (Finset.univ : Finset (LoopArg (d.L N) 2)),
      Integrable (fun ω => (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω)) (Pg d) :=
    fun a _ => (integrable_Phi_H d s t K N (j + 1) (hΦ a)).const_mul (U b a : ℂ)
  have hcondsum := condExp_finsetSum hint_a (filt d j)
  have hsmul_ae : ∀ᵐ ω ∂(Pg d), ∀ a : LoopArg (d.L N) 2,
      (Pg d)[fun ω' => (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω') | filt d j] ω
        = (U b a : ℂ) * (Pg d)[fun ω' => Φ a (H d s t K N (j + 1) ω') | filt d j] ω :=
    ae_all_iff.mpr fun a => condExp_smul (U b a : ℂ)
      (fun ω' => Φ a (H d s t K N (j + 1) ω')) (filt d j)
  have hsum_fn : (∑ a : LoopArg (d.L N) 2,
        fun ω' => (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω'))
      = (fun ω' => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω')) := by
    funext ω'; simp only [Finset.sum_apply]
  rw [hsum_fn] at hcondsum
  filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
  simp_rw [hδ]
  unfold stepXi
  rw [hω1]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => hω2 a]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepY` is linear in the real kernel `U`**, a.e., simultaneously for all labels `b`. -/
theorem stepY_eq_sum_gridDelta_ae {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) :
    ∀ᵐ ω ∂(Pg d), ∀ b : LoopArg (d.L N) 2,
      stepY d s t K N j Φ U b ω
        = ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * stepY d s t K N j Φ (gridDelta (d.L N)) a ω := by
  filter_upwards [stepXi_eq_sum_gridDelta_ae d s t K N j hΦ U] with ω hω b
  unfold stepY
  rw [hω b, stepZ_eq_sum_gridDelta d s t K N j Φ U b ω]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **(R2) `stepY_ukerMat_eq_Uker_ae`**: for `0 ≤ v ≤ w < 1`, a.e. `ω`, for every label `b`,
the kernel folded into the label weight equals the kernel `Uker(v,w)` applied to the
`k`-independent label vector `a ↦ stepY δ a ω`. -/
theorem stepY_ukerMat_eq_Uker_ae {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ}
    (hΦ : ∀ a, TestFun d N (Φ a)) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) :
    ∀ᵐ ω ∂(Pg d), ∀ b : LoopArg (d.L N) 2,
      stepY d s t K N j Φ (ukerMat (d.L N) v w) b ω
        = Uker (d.L N) (fun _ => (1 : ℂ)) (v : ℂ) (w : ℂ)
            (fun a => stepY d s t K N j Φ (gridDelta (d.L N)) a ω) b := by
  filter_upwards [stepY_eq_sum_gridDelta_ae d s t K N j hΦ (ukerMat (d.L N) v w)] with ω hω b
  rw [hω b, Uker_eq_sum_ukerMat (d.L N) (d.three_le_L N) hv0 hvw hw1]

end Bridge

section ExpansionPrime

variable {Ω' : Type*} [MeasurableSpace Ω']

/-- **`Zvec`**: the `k`-independent label vector of the martingale (`Z`) part of the grid step
ending at index `i` (step `i-1 → i`, test function `Φgrid` at `u_i`, identity kernel):
`Zvec (j+1) ω a = stepZ j (Φgrid u_{j+1}) δ a ω`. -/
noncomputable def Zvec (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ)
    (ω : Ωg B.toDims) (a : LoopArg (B.L N) 2) : ℂ :=
  (stepZ B.toDims s t K N (i - 1) (Φgrid B E N (time s t K N i)) (gridDelta (B.L N)) a ω : ℂ)

/-- **`Yvec`**: the `k`-independent label vector of the remainder (`Y`) part of the grid step
ending at index `i`: `Yvec (j+1) ω a = stepY j (Φgrid u_{j+1}) δ a ω`. -/
noncomputable def Yvec (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ)
    (ω : Ωg B.toDims) (a : LoopArg (B.L N) 2) : ℂ :=
  stepY B.toDims s t K N (i - 1) (Φgrid B E N (time s t K N i)) (gridDelta (B.L N)) a ω

theorem Zvec_succ (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (ω : Ωg B.toDims) (a : LoopArg (B.L N) 2) :
    Zvec B E s t K N (j + 1) ω a
      = (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1))) (gridDelta (B.L N)) a ω
          : ℂ) := rfl

theorem Yvec_succ (B : Band Ω') (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    (ω : Ωg B.toDims) (a : LoopArg (B.L N) 2) :
    Yvec B E s t K N (j + 1) ω a
      = stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1))) (gridDelta (B.L N)) a ω :=
  rfl

/-- The per-step `Z`/`Y` bridge at the grid, for `j < k ≤ K N`: a.e., for every label `b`. -/
private theorem grid_ZY_bridge_ae (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) (hK1 : 1 ≤ K N)
    (k : ℕ) (hk : k ≤ K N) (j : ℕ) (hjk : j < k) :
    ∀ᵐ ω ∂(Pg B.toDims), ∀ b : LoopArg (B.L N) 2,
      (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
          (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ)
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
            (Zvec B E s t K N (j + 1) ω) b
      ∧ stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
          (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
            (Yvec B E s t K N (j + 1) ω) b := by
  have hK0 : K N ≠ 0 := by omega
  have htimelast : time s t K N (K N) = t N := time_last s t K N hK0
  have hu0j1 : 0 ≤ time s t K N (j + 1) := by
    have := time_mono s t K N hst.le (Nat.zero_le (j + 1))
    rw [time_zero] at this; linarith
  have huj1k : time s t K N (j + 1) ≤ time s t K N k := time_mono s t K N hst.le (by omega)
  have hu1k : time s t K N k < 1 := by
    have h1 : time s t K N k ≤ time s t K N (K N) := time_mono s t K N hst.le hk
    rw [htimelast] at h1; linarith
  have hu1j1 : time s t K N (j + 1) < 1 := lt_of_le_of_lt huj1k hu1k
  have hΦtf : ∀ a, TestFun B.toDims N (Φgrid B E N (time s t K N (j + 1)) a) :=
    fun a => Φgrid_testFun B hEb N hu1j1 a
  filter_upwards [stepY_ukerMat_eq_Uker_ae B.toDims s t K N j hΦtf hu0j1 huj1k hu1k] with ω hω b
  exact ⟨stepZ_ukerMat_eq_Uker B.toDims s t K N j _ hu0j1 huj1k hu1k b ω, hω b⟩

/-- **(T3′) `grid_expansion'`**: the primed successor of (T3). For a fixed `k ≤ K N`, a.e. `ω`,
for every label `b`, with all four sums in the applied-vector input shape of their consumers:
the `Z` and `Y` sums are `(Σ_{j<k} U_{j+1,k} (Zvec (j+1) ω)) b` and
`(Σ_{j<k} U_{j+1,k} (Yvec (j+1) ω)) b` with label vectors `Zvec`, `Yvec` independent of `k`
(T1504 (T1′/T1″), (T2)); the drift sum is `(Σ_{j<k} Δ • U_{j+1,k} (D_j ω)) b` (T1510
`weighted_duhamel_sum_stopped`); the remainder sum is `(Σ_{j<k} U_{j+1,k} (R_j ω)) b`
(T1504 (T3) `stopped_duhamel_det_bound`). -/
theorem grid_expansion' (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) (hK1 : 1 ≤ K N) (k : ℕ) (hk : k ≤ K N) :
    ∀ᵐ ω ∂(Pg B.toDims), ∀ b : LoopArg (B.L N) 2,
      Agrid B E s t K N k ω b
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
              (Agrid B E s t K N 0 ω) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B E s t K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B E s t K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω)) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω)) b := by
  have hbr : ∀ᵐ ω ∂(Pg B.toDims), ∀ j : ℕ, j < k → ∀ b : LoopArg (B.L N) 2,
      (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
          (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ)
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
            (Zvec B E s t K N (j + 1) ω) b
      ∧ stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
          (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
            (Yvec B E s t K N (j + 1) ω) b := by
    refine ae_all_iff.mpr fun j => ?_
    by_cases hjk : j < k
    · filter_upwards [grid_ZY_bridge_ae B s t K N E hEb hs0 hst ht1 hK1 k hk j hjk] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hjk
  filter_upwards [grid_expansion B s t K N E hEb hs0 hst ht1 hK1 k hk, hbr] with ω hω hωbr
  intro b
  rw [hω b]
  simp only [Finset.sum_apply, Pi.smul_apply, Complex.real_smul]
  have hZ : (∑ j ∈ Finset.range k, (stepZ B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
        (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω : ℂ))
      = ∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ)
          (time s t K N k : ℂ) (Zvec B E s t K N (j + 1) ω) b :=
    Finset.sum_congr rfl fun j hj => (hωbr j (Finset.mem_range.mp hj) b).1
  have hY : (∑ j ∈ Finset.range k, stepY B.toDims s t K N j (Φgrid B E N (time s t K N (j + 1)))
        (ukerMat (B.L N) (time s t K N (j + 1)) (time s t K N k)) b ω)
      = ∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N (j + 1) : ℂ)
          (time s t K N k : ℂ) (Yvec B E s t K N (j + 1) ω) b :=
    Finset.sum_congr rfl fun j hj => (hωbr j (Finset.mem_range.mp hj) b).2
  rw [hZ, hY]

/-- **(T4′) `grid_expansion_all'`**: the primed successor of (T4); the statement of (T3′) a.e.
simultaneously for every `k ≤ K N` and every label `b` (one null set). -/
theorem grid_expansion_all' (B : Band Ω') (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (E : ℝ)
    (hEb : |E| < 2) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) (hK1 : 1 ≤ K N) :
    ∀ᵐ ω ∂(Pg B.toDims), ∀ k : ℕ, k ≤ K N → ∀ b : LoopArg (B.L N) 2,
      Agrid B E s t K N k ω b
        = Uker (B.L N) (fun _ => (1 : ℂ)) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
              (Agrid B E s t K N 0 ω) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Zvec B E s t K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Yvec B E s t K N (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, step s t K N • Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Dgrid B E s t K N j ω)) b
          + (∑ j ∈ Finset.range k, Uker (B.L N) (fun _ => (1 : ℂ))
                (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Rgrid B E s t K N j ω)) b := by
  refine ae_all_iff.mpr fun k => ?_
  by_cases hk : k ≤ K N
  · filter_upwards [grid_expansion' B s t K N E hEb hs0 hst ht1 hK1 k hk] with ω hω _
    exact hω
  · exact Filter.Eventually.of_forall fun _ h => absurd h hk

end ExpansionPrime

end RBM.Gauss.Grid
