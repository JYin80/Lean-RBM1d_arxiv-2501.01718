/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.Lemma514NonAlt
import RBM1D.Gauss.KerClassSumZero
import RBM1D.Gauss.PPInduction
import RBM1D.Gauss.Lemma514Two

/-!
# The all-`n` endpoint of Lemma 5.14 for the alternating charges (Case 2 + `Q`)

Formalization of Horng-Tzer Yau and Jun Yin, *Delocalization of One-Dimensional Random Band
Matrices*, §5.2, Lemma 5.14 (5.92), Case 2 ((5.87)–(5.105)): for the two alternating charges
`σ ∈ {sigmaAltGen n, sigmaAltGen' n}` at every even loop length `n = m + 2 ≥ 2`, the tensor
`A_u = Q_u ∘ (L − K)_u` (Definition 5.12) is run on the grid with the one-step identity
`grid_step_Q`, the sum-zero kernel bound (7.16) Case 2 (`hker_of_Q716_sumZero`), the class
bridges, Ward's bound (5.96), the commutator bound (5.99), the joint `Q ⊗ Q` quadratic variation
(5.103)–(5.105) (`qv_contraction_le_sumZero`, called directly), the conditional `Y` moments,
and `grid_assembly_at_tau'`; the endpoint is converted back by (5.101).

## Main results

The ingredients of the endpoint, in the order of the proof:

* §1–§2 the `Q`-label family `gridΦQ`, the process `AtrueQ = Q_{u_j}(L−K)_{u_j}`, the drift
  `DgridQ` (Case 2 drift of (5.88)–(5.90)), the one-step identity (`grid_step_Q`) and the capped
  Duhamel expansion `hexpQ`.
* §3 Ward's bound (5.96) and the endpoint (5.101) with the decay input from `lkDecaySet`
  (`norm_P_lk_le_ward'`, `Qop_endpoint'`): the tail of a generic decay input is not small in the
  cut-off regime.
* §4–§5 drift size and kernel classes (`norm_DgridQ_le`, `kerClass_DgridQ` from
  `kerClass_caseTwo_drift`, `kerClass_A0Q` from `kerClass_Qop_zero`).
* §6 the martingale part: `hqvQ` calls `qv_contraction_le_sumZero` (the joint `Q ⊗ Q`
  `2n`-tensor) directly.
* §7 the second-order increment via `Ymoments_of_ae_eq`.
* §8 the remainder `qStepErr = O(Δ^{3/2})·poly(N)`.
* §9 the sharp (7.16) Case 2 weights `kapQ`/`epsQ` for `grid_assembly_at_tau'`, `sz = true`.
* §10 the (5.93) budget `budgetQ` (`tb_driftQ`, `tb_qvQ`, `tb_RQ`): the kernel acts through
  `κ_{j+1,k} A_{u_j}^{-n} ≤ cKerSumZero·Kd^{2n}·A_{u_k}^{-n}` — no `η_s/η_t` prefactor.
* §11 tails (`tail1_le` … `tail7_le`, `ev_tailW`, `ev_tailExp`) and main-term absorption
  (`ev_ha1Q` … `ev_ha4Q`, `ev_ht5`, `ev_ht6`).
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.SumZeroDyn
open scoped NNReal ENNReal
open scoped Matrix.Norms.L2Operator

/-! ## §1 : the `Q`-transformed label family -/

section QFamily

variable (d : Dims)

/-- `(band d').toDims = d'`. -/
theorem band_toDims_eqQ (d' : Dims) : (band d').toDims = d' := by
  cases d'; rfl

/-- **The `Q`-transformed label family** `ΦQ_i b M = (Q_{u_i} ∘ Φ_i(M))_b`, `Φ_i = gridΦG`. -/
def gridΦQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool) (i : ℕ)
    (a : LoopArg (d.L N) (m + 2)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) : ℂ :=
  Qop (d.L N) (time s t K N i : ℂ) (fun c => gridΦG d E s t K N σ i c M) a

theorem gridΦQ_eq_sum (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ}
    (σ : Fin (m + 2) → Bool) (i : ℕ) (a : LoopArg (d.L N) (m + 2)) :
    gridΦQ d E s t K N σ i a
      = fun M => ∑ c : LoopArg (d.L N) (m + 2),
          Qmat (d.L N) (time s t K N i : ℂ) a c * gridΦG d E s t K N σ i c M := by
  funext M
  exact Qop_eq_sum_Qmat (d.L N) (time s t K N i : ℂ) _ a

theorem gridΦQ_testFun {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0) {m : ℕ} (σ : Fin (m + 2) → Bool) :
    ∀ i, 1 ≤ i → i ≤ K N → ∀ a, TestFun d N (gridΦQ d E s t K N σ i a) := by
  intro i hi1 hi a
  rw [gridΦQ_eq_sum]
  exact testFun_linComb _ fun c => gridΦG_testFun d hE hst ht1 hK0 (by omega) σ i hi1 hi c

/-- The row sums of the matrix of `Q_t`: `Σ_b ‖Qmat t a b‖ ≤ 1 + L^k`. -/
theorem sum_norm_Qmat_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a : LoopArg L (k + 1)) :
    ∑ b : LoopArg L (k + 1), ‖Qmat L (t : ℂ) a b‖ ≤ 1 + (L : ℝ) ^ k := by
  classical
  have hϑ : ‖vartheta L (t : ℂ) a‖ ≤ 1 := norm_vartheta_le_one hL ht0 ht1 a
  have hpt : ∀ b : LoopArg L (k + 1), ‖Qmat L (t : ℂ) a b‖
      ≤ (if b = a then (1 : ℝ) else 0) + (if b 0 = a 0 then (1 : ℝ) else 0) := by
    intro b
    unfold Qmat
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · split_ifs
      · exact hϑ
      · simp
  refine (Finset.sum_le_sum fun b _ => hpt b).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a (fun _ => (1 : ℝ))]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  have h := SumZeroDyn.sum_loopArg_succ L
    (fun b : LoopArg L (k + 1) => ((if b 0 = a 0 then (1 : ℝ) else 0 : ℝ) : ℂ))
  have h2 : (∑ b : LoopArg L (k + 1), (if b 0 = a 0 then (1 : ℝ) else 0))
      = ∑ x : ZMod L, ∑ _r : LoopArg L k, (if x = a 0 then (1 : ℝ) else 0) := by
    have := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.ofReal_re, Fin.cons_zero] at this
    exact this
  rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (a 0)]
  simp [LoopArg, ZMod.card]

theorem gridΦQ_bdd2 {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0) {m : ℕ}
    (σ : Fin (m + 2) → Bool) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ K N)
    (a : LoopArg (d.L N) (m + 2)) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    ‖fderiv ℝ (fderiv ℝ (gridΦQ d E s t K N σ i a)) M‖
      ≤ (1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N (m + 2) (etaT E (t N)) := by
  have hmem := mem_Icc_time s t K N i hs0 hst hi
  have hu1 : time s t K N i < 1 := hmem.2.trans_lt ht1
  have hη : 0 < etaT E (t N) := etaT_pos hE ht1
  have hzη : etaT E (t N) ≤ |(zt E (time s t K N i)).im| := by
    rw [abs_zt_im hE hu1]; exact etaT_anti hE hmem.2
  rw [gridΦQ_eq_sum]
  have h := norm_fderiv2_linComb_le (Qmat (d.L N) (time s t K N i : ℂ) a)
    (fun c => gridΦG_testFun d hE hst ht1 hK0 (by omega) σ i hi1 hi c)
    (C := C2g d N (m + 2) (etaT E (t N)))
    (fun c M' => ΦgridG_bdd2 (band d) hE N hu1 hη hzη σ c M') M
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by unfold C2g; positivity))
  exact sum_norm_Qmat_le (d.three_le_L N) (hs0.trans hmem.1) hu1 a

end QFamily

/-! ## §2 : the `Q`-process, its one-step identity and its expansion -/

section QProcess

variable (d : Dims)

/-- **`AtrueQ`**: `A_j = Q_{u_j} ∘ (L − K)_{u_j}(H_j)`. -/
def AtrueQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) (m + 2) → ℂ :=
  Qop (d.L N) (time s t K N j : ℂ) (AtrueN d E s t K N σ j ω)

/-- **`DgridQ`**: the Case 2 drift `Q_u D + [Q_u, Θ_{u,σ}](L−K) − ϑ̇_u · P(L−K)` of (5.88)–(5.90). -/
def DgridQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) (m + 2) → ℂ :=
  fun a => Qop (d.L N) (time s t K N j : ℂ) (DgridN d E s t K N σ j ω) a
    + commS (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (AtrueN d E s t K N σ j ω) a
    - varthetaDot (d.L N) (time s t K N j) a * Psum (d.L N) (AtrueN d E s t K N σ j ω) (a 0)

/-- **`RgridQ`**: the exact remainder, named by subtraction. -/
def RgridQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (j : ℕ) (ω : Ωg d) (a : LoopArg (d.L N) (m + 2)) : ℂ :=
  (Pg d)[fun ω' => AtrueQ d E s t K N σ (j + 1) ω' a | filt d j] ω
    - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
        (AtrueQ d E s t K N σ j ω) a
    - (step s t K N : ℂ) * DgridQ d E s t K N σ j ω a

/-- The explicit remainder bound of `grid_step_Q` at the grid step `j`. -/
def qErrQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N m : ℕ) (Bk : ℝ) (j : ℕ) : ℝ :=
  qStepErr (d.L N) m (time s t K N j) (step s t K N)
    (lkEnv (band d) E N m (time s t K N j) Bk) (driftEnv (band d) E N m (time s t K N j) Bk)
    (stepErrN (band d) E N (m + 2) (time s t K N j) (time s t K N (j + 1)) (step s t K N) Bk)

theorem driftF_eq_DgridN (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ}
    (σ : Fin (m + 2) → Bool) (j : ℕ) (ω : Ωg d) :
    DriftDef.driftF (band d) E N (time s t K N j) (H d s t K N j ω) σ
      = DgridN d E s t K N σ j ω := rfl

/-- **The one-step `Q`-identity on the Dims grid**: a.e., `|R^Q_j| ≤ qErrQ`. -/
theorem RgridQ_le_ae (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hst : s N < t N) (hj : j < K N) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N (j + 1) < 1) {m : ℕ} (σ : Fin (m + 2) → Bool) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (d.L N) (m + 2), ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (m + 2 - 1)‖ < 1) :
    ∀ᵐ ω ∂ (Pg d), ∀ a : LoopArg (d.L N) (m + 2),
      ‖RgridQ d E s t K N σ j ω a‖ ≤ qErrQ d E s t K N m Bk j := by
  have h : ∀ᵐ ω ∂ (Pg d), ∀ a : LoopArg (d.L N) (m + 2),
      ‖(Pg d)[fun ω' => Qop (d.L N) (time s t K N (j + 1) : ℂ)
              (lkTM (band d) E N (time s t K N (j + 1)) (H d s t K N (j + 1) ω') σ) a
            | filt d j] ω
          - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
              (Qop (d.L N) (time s t K N j : ℂ)
                (lkTM (band d) E N (time s t K N j) (H d s t K N j ω) σ)) a
          - (step s t K N : ℂ)
              * (Qop (d.L N) (time s t K N j : ℂ)
                    (DriftDef.driftF (band d) E N (time s t K N j) (H d s t K N j ω) σ) a
                + commS (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ)
                    (lkTM (band d) E N (time s t K N j) (H d s t K N j ω) σ) a
                - varthetaDot (d.L N) (time s t K N j) a
                    * Psum (d.L N) (lkTM (band d) E N (time s t K N j) (H d s t K N j ω) σ)
                        (a 0))‖
        ≤ qStepErr (d.L N) m (time s t K N j) (step s t K N)
            (lkEnv (band d) E N m (time s t K N j) Bk) (driftEnv (band d) E N m (time s t K N j) Bk)
            (stepErrN (band d) E N (m + 2) (time s t K N j) (time s t K N (j + 1)) (step s t K N) Bk) :=
    band_toDims_eqQ d ▸ grid_step_Q (band d) s t K N j E hEb hst hj hu0 hu1 σ hBk0 hBk hξ
  filter_upwards [h] with ω hω a
  exact hω a

/-- `ΦQ_i` evaluated at `H_i` is the `i`-th value of `AtrueQ`. -/
theorem gridΦQ_H (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (i : ℕ) (a : LoopArg (d.L N) (m + 2)) (ω : Ωg d) :
    gridΦQ d E s t K N σ i a (H d s t K N i ω) = AtrueQ d E s t K N σ i ω a := by
  unfold gridΦQ AtrueQ
  have : (fun c => gridΦG d E s t K N σ i c (H d s t K N i ω)) = AtrueN d E s t K N σ i ω :=
    funext fun c => gridΦG_eq_AtrueN d E s t K N i σ c ω
  rw [this]

/-- **The exact per-step identity of the `Q`-process** (pointwise, since `RgridQ` is named by
subtraction): `A_{j+1} − U_{j,j+1}A_j = Δ·DQ_j + ZQ_{j+1} + YQ_{j+1} + RQ_j`. -/
theorem step_summand_identityQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) {m : ℕ}
    (σ : Fin (m + 2) → Bool) (hj : j < K N) (ω : Ωg d) (a : LoopArg (d.L N) (m + 2)) :
    AtrueQ d E s t K N σ (j + 1) ω a
        - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
            (AtrueQ d E s t K N σ j ω) a
      = (step s t K N : ℂ) * DgridQ d E s t K N σ j ω a
        + gridZC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω a
        + gridYC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω a
        + RgridQ d E s t K N σ j ω a := by
  have hj1 : (1 : ℕ) ≤ j + 1 ∧ j + 1 ≤ K N := ⟨by omega, by omega⟩
  have hZeq : gridZC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω a
      = stepZC d s t K N j (m + 2) (gridΦQ d E s t K N σ (j + 1)) (gridDeltaC (d.L N) (m + 2)) a ω := by
    unfold gridZC
    simp only [hj1, and_self, ↓reduceIte, Nat.add_sub_cancel]
  have hYeq : gridYC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω a
      = stepYC d s t K N j (m + 2) (gridΦQ d E s t K N σ (j + 1)) (gridDeltaC (d.L N) (m + 2)) a ω := by
    unfold gridYC
    simp only [hj1, and_self, ↓reduceIte, Nat.add_sub_cancel]
  have hXY : stepZC d s t K N j (m + 2) (gridΦQ d E s t K N σ (j + 1)) (gridDeltaC (d.L N) (m + 2)) a ω
        + stepYC d s t K N j (m + 2) (gridΦQ d E s t K N σ (j + 1)) (gridDeltaC (d.L N) (m + 2)) a ω
      = stepXiC d s t K N j (m + 2) (gridΦQ d E s t K N σ (j + 1))
          (gridDeltaC (d.L N) (m + 2)) a ω := by
    unfold stepYC; ring
  have hcollapse := stepXiC_gridDeltaC_eq d s t K N j (m + 2) (gridΦQ d E s t K N σ (j + 1)) a ω
  have hfun : (fun ω' => gridΦQ d E s t K N σ (j + 1) a (H d s t K N (j + 1) ω'))
      = (fun ω' => AtrueQ d E s t K N σ (j + 1) ω' a) :=
    funext fun ω' => gridΦQ_H d E s t K N σ (j + 1) a ω'
  rw [gridΦQ_H, hfun] at hcollapse
  have hR : RgridQ d E s t K N σ j ω a
      = (Pg d)[fun ω' => AtrueQ d E s t K N σ (j + 1) ω' a | filt d j] ω
        - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
            (AtrueQ d E s t K N σ j ω) a
        - (step s t K N : ℂ) * DgridQ d E s t K N σ j ω a := rfl
  rw [hZeq, hYeq, hR]
  linear_combination -hcollapse - hXY

/-- **The generic capped Duhamel expansion** of any grid process whose one-step increment is
a.e. a given label vector `Inc j` (`grid_duhamel_telescope_n` + `Uker_comp`). -/
theorem expansion_generic {n : ℕ} {ξ : Fin n → ℂ} (hξ : ∀ i, ‖ξ i‖ ≤ 1)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1)
    (hK0 : K N ≠ 0) (A' Inc : ℕ → Ωg d → LoopArg (d.L N) n → ℂ)
    (hstep : ∀ j < K N, ∀ᵐ ω ∂(Pg d),
      A' (j + 1) ω - Uker (d.L N) ξ (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (A' j ω)
        = Inc j ω)
    (τ : Ωg d → ℕ) (hτ : ∀ ω, τ ω ≤ K N) (k : ℕ) (hk : k ≤ K N) :
    ∀ᵐ ω ∂(Pg d),
      Uker (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ) (A' (min k (τ ω)) ω)
        = Uker (d.L N) ξ (time s t K N 0 : ℂ) (time s t K N k : ℂ) (A' 0 ω)
          + ∑ j ∈ Finset.range (min k (τ ω)),
              Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ) (Inc j ω) := by
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hubound : ∀ i, i ≤ K N → ∀ l, ‖(time s t K N i : ℂ) * ξ l‖ < 1 := by
    intro i hi l
    have hmem := mem_Icc_time s t K N i hs0 hst hi
    have hnn : 0 ≤ time s t K N i := hs0.trans hmem.1
    have hb : ‖(time s t K N i : ℂ) * ξ l‖ ≤ time s t K N i := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      nlinarith [hξ l, norm_nonneg (ξ l), hnn]
    exact lt_of_le_of_lt (hb.trans hmem.2) ht1
  have hstepAll : ∀ᵐ ω ∂ (Pg d), ∀ j : Fin (K N),
      A' ((j : ℕ) + 1) ω - Uker (d.L N) ξ (time s t K N (j : ℕ) : ℂ)
          (time s t K N ((j : ℕ) + 1) : ℂ) (A' (j : ℕ) ω) = Inc (j : ℕ) ω :=
    ae_all_iff.mpr fun j => hstep (j : ℕ) j.isLt
  filter_upwards [hstepAll] with ω hω
  have hmKN : min k (τ ω) ≤ K N := (min_le_right _ _).trans (hτ ω)
  have htele := grid_duhamel_telescope_n d hξ s t K N hs0 hst ht1 hK0
    (fun j => A' j ω) (min k (τ ω)) hmKN
  have hsub : ∀ j ∈ Finset.range (min k (τ ω)),
      Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ)
          (A' (j + 1) ω - Uker (d.L N) ξ (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ) (A' j ω))
        = Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ)
            (Inc j ω) := by
    intro j hj
    have hjm : j < min k (τ ω) := Finset.mem_range.mp hj
    have hjKN : j < K N := lt_of_lt_of_le hjm hmKN
    rw [hω ⟨j, hjKN⟩]
  rw [Finset.sum_congr rfl hsub] at htele
  have htele' : A' (min k (τ ω)) ω
      = (∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) ξ (time s t K N (j + 1) : ℂ)
            (time s t K N (min k (τ ω)) : ℂ) (Inc j ω))
        + Uker (d.L N) ξ (time s t K N 0 : ℂ) (time s t K N (min k (τ ω)) : ℂ) (A' 0 ω) :=
    sub_eq_iff_eq_add.mp htele
  have hmU := hubound (min k (τ ω)) hmKN
  have hkU := hubound k hk
  have hpush := congrArg
    (Uker (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)) htele'
  rw [Uker_add] at hpush
  rw [Uker_comp (d.L N) hL3 hmU hkU (A' 0 ω)] at hpush
  have hsumpush : Uker (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)
      (∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) ξ (time s t K N (j + 1) : ℂ)
          (time s t K N (min k (τ ω)) : ℂ) (Inc j ω))
      = ∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) ξ (time s t K N (j + 1) : ℂ)
          (time s t K N k : ℂ) (Inc j ω) := by
    have hmap := map_sum
      (UkerHom (d.L N) ξ (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ))
      (fun j => Uker (d.L N) ξ (time s t K N (j + 1) : ℂ) (time s t K N (min k (τ ω)) : ℂ)
        (Inc j ω)) (Finset.range (min k (τ ω)))
    simp only [UkerHom_apply] at hmap
    rw [hmap]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j < min k (τ ω) := Finset.mem_range.mp hj
    exact Uker_comp (d.L N) hL3 hmU hkU _
  rw [hsumpush] at hpush
  rw [hpush]
  ring

/-- **The kernel-frozen-after-exit `Q`-process** `A_k := U_{u_{k∧τ}, u_k}(AtrueQ(k∧τ))`. -/
def AfrozQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (τ : Ωg d → ℕ) (k : ℕ) (ω : Ωg d) : LoopArg (d.L N) (m + 2) → ℂ :=
  Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (min k (τ ω)) : ℂ) (time s t K N k : ℂ)
    (AtrueQ d E s t K N σ (min k (τ ω)) ω)

theorem AfrozQ_eq_of_eq {E : ℝ} (hE : |E| < 2) {s t : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) {m : ℕ} (σ : Fin (m + 2) → Bool)
    {τ : Ωg d → ℕ} {ω : Ωg d} (hτ : τ ω = K N) :
    AfrozQ d E s t K N σ τ (K N) ω = AtrueQ d E s t K N σ (K N) ω := by
  unfold AfrozQ
  rw [hτ, min_self]
  have hmem := mem_Icc_time s t K N (K N) hs0 hst le_rfl
  exact Uker_self (d.L N) (d.three_le_L N)
    (fun i => norm_time_mul_xiOf_lt hE σ (hs0.trans hmem.1) (hmem.2.trans_lt ht1) i) _

open Classical in
/-- **The `Q`-remainder, truncated off the null set where the bound fails.** -/
def RgridQT (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (Bk : ℝ) (j : ℕ) (ω : Ωg d) : LoopArg (d.L N) (m + 2) → ℂ :=
  if ∀ a, ‖RgridQ d E s t K N σ j ω a‖ ≤ qErrQ d E s t K N m Bk j
  then RgridQ d E s t K N σ j ω else 0

theorem norm_RgridQT_le (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) {m : ℕ}
    (σ : Fin (m + 2) → Bool) (Bk : ℝ) (j : ℕ) (h0 : 0 ≤ qErrQ d E s t K N m Bk j)
    (ω : Ωg d) (a : LoopArg (d.L N) (m + 2)) :
    ‖RgridQT d E s t K N σ Bk j ω a‖ ≤ qErrQ d E s t K N m Bk j := by
  unfold RgridQT
  split_ifs with h
  · exact h a
  · simpa using h0

theorem RgridQT_ae (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) (E : ℝ) (hEb : |E| < 2)
    (hst : s N < t N) (hj : j < K N) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N (j + 1) < 1) {m : ℕ} (σ : Fin (m + 2) → Bool) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    (hξ : ∀ a : LoopArg (d.L N) (m + 2), ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
        (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (m + 2 - 1)‖ < 1) :
    0 ≤ qErrQ d E s t K N m Bk j
      ∧ ∀ᵐ ω ∂(Pg d), RgridQT d E s t K N σ Bk j ω = RgridQ d E s t K N σ j ω := by
  have h := RgridQ_le_ae d s t K N j E hEb hst hj hu0 hu1 σ hBk0 hBk hξ
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, hω⟩ := h.exists
    obtain ⟨a⟩ := (inferInstance : Nonempty (LoopArg (d.L N) (m + 2)))
    exact (norm_nonneg _).trans (hω a)
  · filter_upwards [h] with ω hω
    unfold RgridQT
    rw [ite_cond_eq_true _ _ (eq_true hω)]

set_option maxHeartbeats 1600000 in
/-- **`GridAssemblyHypPW.hexp` for the frozen `Q`-process, with the truncated remainder.** -/
theorem hexpQ {m : ℕ} (E : ℝ) (hEb : |E| < 2) (σ : Fin (m + 2) → Bool)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1)
    (hK0 : K N ≠ 0) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ j < K N, ∀ w ∈ Set.Icc (0 : ℝ) (time s t K N (j + 1)), ∀ J : LoopIdx (ZMod (d.L N)),
      J.WF → 2 ≤ J.length → J.length ≤ m + 2 → ‖(band d).Kval E N w J‖ ≤ Bk)
    (τ : Ωg d → ℕ) (hτ : ∀ ω, τ ω ≤ K N) :
    ∀ k ≤ K N, ∀ᵐ ω ∂(Pg d),
      AfrozQ d E s t K N σ τ k ω
        = Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N 0 : ℂ) (time s t K N k : ℂ)
            (AtrueQ d E s t K N σ 0 ω)
          + ∑ j ∈ Finset.range (min k (τ ω)), Uker (d.L N) (xiOf (mSigma E) σ)
              (time s t K N (j + 1) : ℂ) (time s t K N k : ℂ)
              ((step s t K N : ℂ) • DgridQ d E s t K N σ j ω
                + gridZC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω
                + gridYC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω
                + RgridQT d E s t K N σ Bk j ω) := by
  intro k hk
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst.le hi
  have hξb : ∀ j ≤ K N, ∀ a : LoopArg (d.L N) (m + 2), ‖(time s t K N j : ℂ) * xiLoop (mSigma E)
      (⟨List.ofFn σ, List.ofFn a⟩ : LoopIdx (ZMod (d.L N))) (m + 2 - 1)‖ < 1 :=
    fun j hj a => norm_time_mul_xiLoop_lt hEb _ _ (hs0.trans (hmem j hj).1)
      ((hmem j hj).2.trans_lt ht1)
  have hstep : ∀ j < K N, ∀ᵐ ω ∂(Pg d),
      AtrueQ d E s t K N σ (j + 1) ω
          - Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N j : ℂ) (time s t K N (j + 1) : ℂ)
              (AtrueQ d E s t K N σ j ω)
        = (step s t K N : ℂ) • DgridQ d E s t K N σ j ω
          + gridZC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω
          + gridYC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω
          + RgridQT d E s t K N σ Bk j ω := by
    intro j hj
    have hR := (RgridQT_ae d s t K N j E hEb hst hj (hs0.trans (hmem j hj.le).1)
      ((hmem (j + 1) (by omega)).2.trans_lt ht1) σ hBk0 (hBk j hj) (hξb j hj.le)).2
    filter_upwards [hR] with ω hω
    funext a
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hω]
    exact step_summand_identityQ d E s t K N j σ hj ω a
  exact expansion_generic d (fun l => (norm_xiOf_mSigma hEb.le σ l).le) s t K N hs0 hst.le ht1
    hK0 (AtrueQ d E s t K N σ) _ hstep τ hτ k hk

end QProcess

/-! ## §3 : Ward's bound (5.96) and the endpoint (5.101) from `lkDecaySet`

Ward's bound and the endpoint with a generic decay input carry a tail that is not small in the
cut-off regime `ℓ_u = L`; `goodSet514` contains `lkDecaySet` (the `L − K` half of (5.75)), which
gives the fast decay of `(L − K)_{u,σ}` with error `W^{-D}` directly. -/

section WardLK

open Real

/-- **(5.96) from `lkDecaySet`.** -/
theorem norm_P_lk_le_ward' (d : Dims) {E : ℝ} (hE : |E| < 2) {N m₀ : ℕ} {u τ D : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hτ : 0 ≤ τ) {n : ℕ} (hn : n + 1 ≤ m₀)
    {σ : Fin (n + 2) → Bool} (hσ : ∃ i j, σ i ≠ σ j)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hdec : M ∈ lkDecaySet d E N m₀ u τ D) (x : ZMod (d.L N)) :
    ‖Psum (d.L N) (lkTM (band d) E N u M σ) x‖
      ≤ (4 * exp 1) ^ n * ((d.W N : ℝ) ^ τ) ^ n * ((d.W N : ℝ) * etaT E u)⁻¹ ^ (n + 2)
          * ((band d).ell N u)⁻¹ * xiLKB (band d) E N u M (n + 1)
        + ((d.W N : ℝ) * etaT E u)⁻¹ * (d.L N : ℝ) ^ n * (d.W N : ℝ) ^ (-D) := by
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  obtain ⟨σ', σ'', hw⟩ := psum_ward_of (wardMid_DlM (W := d.W N) hM hL3 hE hu0 hu1)
    (wardLast_DlM (W := d.W N) hM hL3 hE hu0 hu1) σ hσ
  set R : ℝ := (band d).ell N u * (d.W N : ℝ) ^ τ with hRdef
  set δ : ℝ := (d.W N : ℝ) ^ (-D) with hδdef
  have hLK : Decay.LoopDecay (d.L N) m₀ R δ
      (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) := hdec
  have hLK' := hLK.mono (d.L N) hn le_rfl le_rfl
  have hfd : ∀ ρ : Fin (n + 1) → Bool, FastDecay (d.L N) R δ (lkTM (band d) E N u M ρ) :=
    fun ρ => hLK'.fastDecay (d.L N) (List.ofFn ρ) (by simp)
  have hell1 : (1 : ℝ) ≤ (band d).ell N u := one_le_ellHat (d.L N) hL3 hu0 hu1
  have hWτ : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ := one_le_W_rpow d N hτ
  have hR1 : 1 ≤ R := by rw [hRdef]; nlinarith
  have hR : 0 < R := by linarith
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg (by exact_mod_cast (d.W_pos N).le) _
  have hd0 := lkMaxB_nonneg (band d) E N u M (n + 1)
  have hP := norm_Psum_le_of_ward (d.L N) (hw x) hR hd0 hδ0
    (norm_lkTM_le (band d) E N u M σ') (norm_lkTM_le (band d) E N u M σ'') (hfd σ') (hfd σ'')
  rw [norm_wardKappa (d.W N) hE hu1] at hP
  have hη := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  set w : ℝ := (d.W N : ℝ) * etaT E u with hw_def
  have hw0 : 0 < w := by rw [hw_def]; positivity
  set ℓ : ℝ := (band d).ell N u with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  set X : ℝ := (d.W N : ℝ) ^ τ with hXdef
  have hmax := lkMaxB_eq_xiLKB (band d) hE N hu0 hu1 M (n + 1)
  have hscale : (band d).scale E N u = w * ℓ := by
    rw [Band.scale, hw_def, hℓdef]; simp only [band_W]; ring
  rw [hscale] at hmax
  set Ξ : ℝ := xiLKB (band d) E N u M (n + 1) with hΞdef
  have hpowle : (2 * exp 1 * (R + 1)) ^ n ≤ (4 * exp 1) ^ n * ℓ ^ n * X ^ n := by
    rw [← mul_pow, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ n
    have : R = ℓ * X := rfl
    have he := exp_pos 1
    nlinarith
  have hκ : ((2 * (d.W N : ℕ) * etaT E u : ℝ))⁻¹ * 2 = w⁻¹ := by
    rw [hw_def]; field_simp
  calc ‖Psum (d.L N) (lkTM (band d) E N u M σ) x‖
      ≤ ((2 * (d.W N : ℕ) * etaT E u : ℝ))⁻¹
          * (2 * ((2 * exp 1 * (R + 1)) ^ n * lkMaxB (band d) E N u M (n + 1)
            + (d.L N : ℝ) ^ n * δ)) := hP
    _ = w⁻¹ * ((2 * exp 1 * (R + 1)) ^ n * lkMaxB (band d) E N u M (n + 1))
          + w⁻¹ * (d.L N : ℝ) ^ n * δ := by rw [← hκ]; ring
    _ ≤ w⁻¹ * ((4 * exp 1) ^ n * ℓ ^ n * X ^ n * lkMaxB (band d) E N u M (n + 1))
          + w⁻¹ * (d.L N : ℝ) ^ n * δ := by gcongr
    _ = (4 * exp 1) ^ n * X ^ n * w⁻¹ ^ (n + 2) * ℓ⁻¹ * Ξ + w⁻¹ * (d.L N : ℝ) ^ n * δ := by
        rw [hmax]
        congr 1
        simp only [inv_pow, mul_pow]
        field_simp
        ring

/-- **(5.101) from `lkDecaySet`**: `|(L−K)_t − Q_t(L−K)_t| ≤ c^{n+1}(4e)^n W^{nτ} A_t^{-(n+2)}
Ξ^{(L−K)}_{t,n+1} + (c/ℓ_t)^{n+1}(Wη_t)^{-1} L^n W^{-D}`. -/
theorem Qop_endpoint' (d : Dims) {E : ℝ} (hE : |E| < 2) {N m₀ : ℕ} {t τ D : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (hτ : 0 ≤ τ) {n : ℕ} (hn : n + 1 ≤ m₀)
    {σ : Fin (n + 2) → Bool} (hσ : ∃ i j, σ i ≠ σ j)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hdec : M ∈ lkDecaySet d E N m₀ t τ D) (a : LoopArg (d.L N) (n + 2)) :
    ‖lkTM (band d) E N t M σ a - Qop (d.L N) (t : ℂ) (lkTM (band d) E N t M σ) a‖
      ≤ cTwo52 ^ (n + 1) * (4 * exp 1) ^ n * ((d.W N : ℝ) ^ τ) ^ n
          * ((band d).scale E N t)⁻¹ ^ (n + 2) * xiLKB (band d) E N t M (n + 1)
        + (cTwo52 / (band d).ell N t) ^ (n + 1)
          * (((d.W N : ℝ) * etaT E t)⁻¹ * (d.L N : ℝ) ^ n * (d.W N : ℝ) ^ (-D)) := by
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hdiff : lkTM (band d) E N t M σ a - Qop (d.L N) (t : ℂ) (lkTM (band d) E N t M σ) a
      = Psum (d.L N) (lkTM (band d) E N t M σ) (a 0) * vartheta (d.L N) (t : ℂ) a := by
    simp only [Qop]; ring
  rw [hdiff, norm_mul]
  have hP := norm_P_lk_le_ward' d hE ht0 ht1 hτ hn hσ hM hdec (a 0)
  have hV := norm_vartheta_real_le (d.L N) hL3 ht0 ht1 a
  have hell1 : (1 : ℝ) ≤ (band d).ell N t := one_le_ellHat (d.L N) hL3 ht0 ht1
  have hc := cTwo52_pos
  refine (mul_le_mul hP hV (norm_nonneg _) ((norm_nonneg _).trans hP)).trans (le_of_eq ?_)
  have hη := etaT_pos hE ht1
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hscale : (band d).scale E N t = ((d.W N : ℝ) * etaT E t) * (band d).ell N t := by
    rw [Band.scale]; simp only [band_W]; ring
  rw [hscale]
  have hellEq : (band d).ell N t = ellHat (d.L N) (t : ℂ) := rfl
  have hℓ0 : 0 < ellHat (d.L N) (t : ℂ) := by rw [← hellEq]; linarith
  rw [hellEq]
  simp only [inv_pow, mul_pow, div_pow]
  field_simp
  ring

end WardLK

/-! ## §4 : the Case 2 drift — size (5.78)–(5.80), (5.96), (5.99) and class -/

section DriftQ

variable (d : Dims)

/-- `norm_DgridN_le` re-proved from its own inputs with `2 ≤ n` (at `n = 2` the
`l_K ≥ 3` coupling sum is empty). -/
theorem norm_DgridN_le2 {n : ℕ} [NeZero n] (hn2 : 2 ≤ n) {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ)
    (K : ℕ → ℕ) (N : ℕ) (σ : Fin n → Bool) (j : ℕ) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ}
    (hτ' : 0 < τ') (hD' : 0 ≤ D') (hΦ0 : 0 ≤ Φ) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N j < 1) (hA1 : 1 ≤ (band d).scale E N (time s t K N j))
    (hreg : KDecayRegime d N n τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) n ε₁ Λ Φ τ' D' ℓs)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ n →
      ‖(band d).Kval E N (time s t K N j) J‖
        ≤ CK * ((band d).scale E N (time s t K N j))⁻¹ ^ (J.length - 1))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m, 2 ≤ m → m ≤ n → xiLKM d E N (time s t K N j) (H d s t K N j ω) m ≤ B)
    (b : LoopArg (d.L N) n) :
    ‖DgridN d E s t K N σ j ω b‖ ≤ dDr514 d E N n (time s t K N j) ε₁ τ' D' Φ CK B := by
  set u := time s t K N j with hu
  set M := H d s t K N j ω with hM
  have hmem' := hmem
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩ := hmem
  obtain ⟨hdec, hlk⟩ := goodSet514_decay d E N u n ε₁ Λ Φ τ' D' ℓs hmem'
  have hNe : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set I : LoopIdx (ZMod (d.L N)) := ⟨List.ofFn σ, List.ofFn b⟩ with hI
  have hIwf : I.WF := by simp [hI, LoopIdx.WF]
  have hIlen : I.length = n := by simp [hI, LoopIdx.length]
  have heG := norm_eGterm_le d hE N hu0 hu1 hτ' hA1 M hdec (Ξ1 := (N : ℝ) ^ ε₁)
    (Φ := (N : ℝ) ^ ε₁ * Φ) hNe (mul_nonneg hNe hΦ0) h5 h4 I hIwf hIlen
  have hprod : ∀ m, 2 ≤ m → m ≤ n →
      xiLKM d E N u M m * xiLKM d E N u M (n - m + 2) * ((band d).scale E N u)⁻¹
        ≤ (N : ℝ) ^ ε₁ * Φ := by
    intro m hm1 hm2
    have := h3 m hm1 hm2
    rwa [div_eq_mul_inv] at this
  have hpB := norm_primBil_le514 d hE N hu0 hu1 hτ' hA1 (n := n) hn2 M hlk
    (Φ := (N : ℝ) ^ ε₁ * Φ) (mul_nonneg hNe hΦ0) hB0 hprod hB I hIwf hIlen
  have hcoup : ∀ lK ∈ Finset.Icc 3 n,
      ‖Decay.couplingLen (d.L N) (d.W N) lK ((band d).Kval E N u)
          (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J) I‖
        ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹
              * ((N : ℝ) ^ ε₁ * Φ) * ((band d).scale E N u)⁻¹ ^ n
          + 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D')
              * ((N : ℝ) ^ ε₁ * Φ) := by
    intro lK hlK
    rw [Finset.mem_Icc] at hlK
    have h := norm_KsimLK_le d hE N hu0 hu1 hτ' hD' hA1 hlK.1 hlK.2 hreg hCK0 hK M I hIwf hIlen
    have hX := h2 (n - lK + 2) (by omega) (by omega)
    have hc1 : 0 ≤ 8 * Real.exp 1 * (n : ℝ) ^ 2 * CK * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ := by
      have := etaT_pos hE hu1
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
      positivity
    have hc2 : 0 ≤ ((band d).scale E N u)⁻¹ ^ n := by
      have : 0 ≤ (band d).scale E N u := le_trans zero_le_one hA1
      positivity
    have hc3 : 0 ≤ 2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
      positivity
    refine h.trans ?_
    have e1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hc1) hc2
    have e2 := mul_le_mul_of_nonneg_left hX hc3
    linarith
  have hsum := (norm_sum_le (Finset.Icc 3 n) (fun lK => Decay.couplingLen (d.L N) (d.W N) lK
      (fun I => (band d).Kval E N u I)
      (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) I)).trans
    (Finset.sum_le_sum hcoup)
  have hsplit : DgridN d E s t K N σ j ω b
      = eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I
        + (∑ lK ∈ Finset.Icc 3 n, Decay.couplingLen (d.L N) (d.W N) lK
            (fun I => (band d).Kval E N u I)
            (fun I => gloop (d.L N) (d.W N) M (zt E u) I - (band d).Kval E N u I) I)
        + primBil (d.L N) (d.W N)
            (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J)
            (fun J => gloop (d.L N) (d.W N) M (zt E u) J - (band d).Kval E N u J) I := rfl
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  unfold dDr514
  have heG' : ‖eGterm (d.L N) (d.W N) (mSigma E) M (zt E u) I‖
      ≤ 4 * Real.exp 1 * (n : ℝ) * (d.W N : ℝ) ^ τ' * (etaT E u)⁻¹ * (N : ℝ) ^ ε₁
            * ((N : ℝ) ^ ε₁ * Φ) * ((band d).scale E N u)⁻¹ ^ n
        + (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁ := heG
  exact add_le_add (add_le_add heG' hsum) hpB

/-- The drift tensor is `(ℓ_{u_j}·4W^{τ'}, driftErr514)`-fast-decaying on `goodSet514(u_j)`
(`fastDecay_driftF_window`, the input of `kerClass_drift`, read at `u_j`). -/
theorem fastDecay_DgridN {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (j : ℕ) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ} (hτ' : 0 < τ')
    (hD' : 0 ≤ D') (hu0 : 0 ≤ time s t K N j) (hu1 : time s t K N j < 1)
    (hreg : KDecayRegime d N (m + 2) τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    {MK MD : ℝ} (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hKb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖ ≤ MK)
    (hDb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) J
        - (band d).Kval E N (time s t K N j) J‖ ≤ MD) :
    FastDecay (d.L N) (ellHat (d.L N) ((time s t K N j : ℝ) : ℂ) * (4 * (d.W N : ℝ) ^ τ'))
      (driftErr514 d N m MK MD D') (DgridN d E s t K N σ j ω) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, hdec⟩, hlk⟩, _⟩, _⟩ := hmem
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hKd := K_decay_rpow d hE (m + 2) hτ' hD' hu0 hu1 hreg
  have hDd : Decay.LoopDecay (d.L N) (m + 2) ((band d).ell N (time s t K N j) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω)
        (zt E (time s t K N j)) I - (band d).Kval E N (time s t K N j) I) :=
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl
  have hLd : Decay.LoopDecay (d.L N) (m + 3) ((band d).ell N (time s t K N j) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω)
        (zt E (time s t K N j)) I) :=
    Decay.LoopDecay.mono (d.L N) hdec (by omega) le_rfl le_rfl
  exact FastDecayFlow.fastDecay_driftF_window (band d) E N (time s t K N j)
    (d.three_le_L N) hu0 hu1 (H d s t K N j ω) σ (K := (d.W N : ℝ) ^ τ')
    (δ := (d.W N : ℝ) ^ (-D')) (δF := driftErr514 d N m MK MD D') hW1
    (Real.rpow_nonneg (by positivity) _) hMK hMD hKd hDd hLd hKb hDb le_rfl

/-- The crude (`Φ`-free) drift envelope `driftEnv`. -/
theorem norm_DgridN_crude {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (j : ℕ) (ω : Ωg d) (hu0 : 0 ≤ time s t K N j)
    (hu1 : time s t K N j < 1) {Bk : ℝ} (hBk0 : 0 ≤ Bk)
    (hBk : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖ ≤ Bk)
    (b : LoopArg (d.L N) (m + 2)) :
    ‖DgridN d E s t K N σ j ω b‖ ≤ driftEnv (band d) E N m (time s t K N j) Bk := by
  rw [← driftF_eq_DgridN]
  have hM := H_isHermitian d s t K N j ω
  have hηu : 0 < etaT E (time s t K N j) := etaT_pos_of_lt_one hE hu1
  exact norm_driftF_le_crude (band d) E N hE (time s t K N j) (H d s t K N j ω) σ b
    (MG := (etaT E (time s t K N j))⁻¹ ^ (m + 3)) (by positivity) hBk0
    (fun J hJ h1 hle => norm_gloop_le_win hM hE hu0 le_rfl hu1 (m + 3) J hJ h1 hle) hBk

/-- Ward's bound on `P ∘ (L−K)` at the grid time, the explicit right-hand side. -/
def PwQ (d : Dims) (E : ℝ) (N m : ℕ) (u ε₁ τ' D' Φ : ℝ) : ℝ :=
  (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * ((d.W N : ℝ) * etaT E u)⁻¹ ^ (m + 2)
      * ((band d).ell N u)⁻¹ * ((N : ℝ) ^ ε₁ * Φ)
    + ((d.W N : ℝ) * etaT E u)⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D')

/-- The pathwise bound of the Case 2 drift `Q D + [Q, Θ](L−K) − ϑ̇·P(L−K)` on `goodSet514(u_j)`. -/
def dDrQ (d : Dims) (E : ℝ) (N m : ℕ) (u ε₁ τ' D' Φ CK B MK MD : ℝ) : ℝ :=
  (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
      * dDr514 d E N (m + 2) u ε₁ τ' D' Φ CK B
    + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D'
    + 4 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
      * PwQ d E N m u ε₁ τ' D' Φ

theorem PwQ_nonneg {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u ε₁ τ' D' Φ : ℝ} (hu1 : u < 1)
    (hΦ : 0 ≤ Φ) : 0 ≤ PwQ d E N m u ε₁ τ' D' Φ := by
  unfold PwQ
  have := etaT_pos hE hu1
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (band d).ell N u := by
    show 0 ≤ ellHat (d.L N) (u : ℂ); unfold ellHat; exact le_min (by positivity) (Nat.cast_nonneg _)
  positivity

set_option maxHeartbeats 1600000 in
/-- **h-drift (size), Case 2**: on `{j < τ}`, `‖DQ_j‖ ≤ dDrQ` — (5.78)–(5.80) for `Q D` through
Lemma 5.13 (`norm_Qop_le_of_fastDecay`), (5.99) for the commutator, `max_varthetaDot_le`, and
Ward's (5.96) for `P(L−K)` (`Ξ^{(L−K)}_{n−1} ≤ N^{ε₁}Φ` on `goodSet514`). -/
theorem norm_DgridQ_le {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (hσ : ∃ i j, σ i ≠ σ j) (j : ℕ) (ω : Ωg d)
    {ε₁ Λ Φ τ' D' ℓs : ℝ} (hτ' : 0 < τ') (hD' : 0 ≤ D') (hΦ0 : 0 ≤ Φ)
    (hu0 : 0 ≤ time s t K N j) (hu1 : time s t K N j < 1)
    (hA1 : 1 ≤ (band d).scale E N (time s t K N j))
    (hreg : KDecayRegime d N (m + 2) τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    {CK : ℝ} (hCK0 : 0 ≤ CK)
    (hK : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖
        ≤ CK * ((band d).scale E N (time s t K N j))⁻¹ ^ (J.length - 1))
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ m', 2 ≤ m' → m' ≤ m + 2 → xiLKM d E N (time s t K N j) (H d s t K N j ω) m' ≤ B)
    {MK MD : ℝ} (hMK : 0 ≤ MK) (hMD : 0 ≤ MD)
    (hKb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖ ≤ MK)
    (hDb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) J
        - (band d).Kval E N (time s t K N j) J‖ ≤ MD)
    (b : LoopArg (d.L N) (m + 2)) :
    ‖DgridQ d E s t K N σ j ω b‖
      ≤ dDrQ d E N m (time s t K N j) ε₁ τ' D' Φ CK B MK MD := by
  set u := time s t K N j with hu
  have hL3 : 3 ≤ d.L N := d.three_le_L N
  have hmem' := hmem
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, h2⟩, _⟩, _⟩, _⟩, _⟩, hlk⟩, _⟩, _⟩ := hmem'
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hK4 : (1 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by linarith
  -- `Q D`
  have hDsize : ∀ b', ‖DgridN d E s t K N σ j ω b'‖ ≤ dDr514 d E N (m + 2) u ε₁ τ' D' Φ CK B :=
    fun b' => norm_DgridN_le2 d (by omega) hE s t K N σ j ω hτ' hD' hΦ0 hu0 hu1 hA1 hreg hmem hCK0
      hK hB0 hB b'
  have hdD0 : 0 ≤ dDr514 d E N (m + 2) u ε₁ τ' D' Φ CK B := (norm_nonneg _).trans (hDsize b)
  have hδD0 : 0 ≤ driftErr514 d N m MK MD D' := driftErr514_nonneg d N m hMK hMD
  have hFD := fastDecay_DgridN d hE s t K N σ j ω hτ' hD' hu0 hu1 hreg hmem hMK hMD hKb hDb
  have hQD := norm_Qop_le_of_fastDecay (d.L N) hL3 hu0 hu1 hK4 hdD0 hδD0 hDsize hFD b
  -- Ward
  have hP : ∀ x, ‖Psum (d.L N) (AtrueN d E s t K N σ j ω) x‖ ≤ PwQ d E N m u ε₁ τ' D' Φ := by
    intro x
    have hw := norm_P_lk_le_ward' d hE hu0 hu1 hτ'.le (n := m) (m₀ := 2 * (m + 2) + 2)
      (by omega) hσ (H_isHermitian d s t K N j ω) hlk x
    have hX : xiLKB (band d) E N u (H d s t K N j ω) (m + 1) ≤ (N : ℝ) ^ ε₁ * Φ :=
      h2 (m + 1) (by omega) (by omega)
    have hc0 : 0 ≤ (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m
        * ((d.W N : ℝ) * etaT E u)⁻¹ ^ (m + 2) * ((band d).ell N u)⁻¹ := by
      have := etaT_pos hE hu1
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ (band d).ell N u := by
        show 0 ≤ ellHat (d.L N) (u : ℂ); unfold ellHat
        exact le_min (by positivity) (Nat.cast_nonneg _)
      positivity
    refine hw.trans ?_
    unfold PwQ
    have := mul_le_mul_of_nonneg_left hX hc0
    exact add_le_add this le_rfl
  have hP0 := PwQ_nonneg d hE N m (ε₁ := ε₁) (τ' := τ') (D' := D') hu1 hΦ0
  have hcomm := norm_comm_QTheta_le (d.L N) hL3 hE.le hu0 hu1 σ hP0 hP b
  have hvd := max_varthetaDot_le (d.L N) hL3 (n := m + 1) hu0 hu1 b
  have h1u : 0 ≤ (1 - u)⁻¹ := inv_nonneg.mpr (by linarith)
  have hcl : 0 ≤ (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1) := by
    have := cTwo52_pos
    have : 0 < ellHat (d.L N) (u : ℂ) := ellHat_real_pos' (d.L N) hL3 hu0 hu1
    positivity
  have hPx := hP (b 0)
  have hvdP : ‖varthetaDot (d.L N) u b * Psum (d.L N) (AtrueN d E s t K N σ j ω) (b 0)‖
      ≤ 2 * ((m + 1 : ℕ) : ℝ) * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1) * (1 - u)⁻¹
        * PwQ d E N m u ε₁ τ' D' Φ := by
    rw [norm_mul]
    exact mul_le_mul hvd hPx (norm_nonneg _) (by positivity)
  have hsplit : DgridQ d E s t K N σ j ω b
      = Qop (d.L N) (u : ℂ) (DgridN d E s t K N σ j ω) b
        + commS (d.L N) (xiOf (mSigma E) σ) (u : ℂ) (AtrueN d E s t K N σ j ω) b
        - varthetaDot (d.L N) u b * Psum (d.L N) (AtrueN d E s t K N σ j ω) (b 0) := rfl
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
  unfold dDrQ
  have e3 : 2 * (((m + 1 : ℕ) : ℝ) + 1) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
        * PwQ d E N m u ε₁ τ' D' Φ
      + 2 * ((m + 1 : ℕ) : ℝ) * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1) * (1 - u)⁻¹
        * PwQ d E N m u ε₁ τ' D' Φ
      ≤ 4 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
        * PwQ d E N m u ε₁ τ' D' Φ := by
    have h0 : 0 ≤ (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
        * PwQ d E N m u ε₁ τ' D' Φ := by positivity
    push_cast
    nlinarith
  have hQD' : ‖Qop (d.L N) (u : ℂ) (DgridN d E s t K N σ j ω) b‖
      ≤ (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
          * dDr514 d E N (m + 2) u ε₁ τ' D' Φ CK B
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D' := hQD
  linarith

/-- **h-Dcls, Case 2** (`kerClass_caseTwo_drift`): the drift is in the sum-zero class at
`u_{j+1}` with radius `16 W^{τ'}` and the explicit error. -/
theorem kerClass_DgridQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (j : ℕ) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ} (hτ' : 0 < τ')
    (hD' : 0 ≤ D') (hu0 : 0 ≤ time s t K N j) (hjj : time s t K N j ≤ time s t K N (j + 1))
    (hu1 : time s t K N (j + 1) < 1) (hreg : KDecayRegime d N (m + 2) τ' D')
    (hmem : H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    {MK MD Bk : ℝ} (hMK : 0 ≤ MK) (hMD : 0 ≤ MD) (hBk0 : 0 ≤ Bk)
    (hKb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖ ≤ MK)
    (hBk : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → 2 ≤ J.length → J.length ≤ m + 2 →
      ‖(band d).Kval E N (time s t K N j) J‖ ≤ Bk)
    (hDb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖gloop (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N j)) J
        - (band d).Kval E N (time s t K N j) J‖ ≤ MD) :
    KerClass (d.L N) (time s t K N) (4 * (4 * (d.W N : ℝ) ^ τ')) true
      (deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
          (driftEnv (band d) E N m (time s t K N j) Bk) (driftErr514 d N m MK MD D')
        + deltaCommS (d.L N) (m + 1) (time s t K N j) (4 * (d.W N : ℝ) ^ τ') MD
          ((d.W N : ℝ) ^ (-D'))
        + deltaVD (d.L N) (m + 1) (time s t K N j) (4 * (d.W N : ℝ) ^ τ') MD
          ((d.W N : ℝ) ^ (-D')))
      (j + 1) (DgridQ d E s t K N σ j ω) := by
  have huj1 : time s t K N j < 1 := hjj.trans_lt hu1
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hK4 : (1 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by linarith
  have hmem' := hmem
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hlk⟩, _⟩, _⟩ := hmem'
  have hFD := fastDecay_DgridN d hE s t K N σ j ω hτ' hD' hu0 huj1 hreg hmem hMK hMD hKb hDb
  have hDM := norm_DgridN_crude d hE s t K N σ j ω hu0 huj1 hBk0 hBk
  have hEnv0 : 0 ≤ driftEnv (band d) E N m (time s t K N j) Bk := by
    obtain ⟨b0⟩ := (inferInstance : Nonempty (LoopArg (d.L N) (m + 2)))
    exact (norm_nonneg _).trans (hDM b0)
  have hAM : ∀ b, ‖AtrueN d E s t K N σ j ω b‖ ≤ MD := fun b =>
    hDb ⟨List.ofFn σ, List.ofFn b⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
  have hAd : Decay.LoopDecay (d.L N) (m + 2)
      ((band d).ell N (time s t K N j) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N j ω)
        (zt E (time s t K N j)) I - (band d).Kval E N (time s t K N j) I) :=
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl
  have hAfd0 := Decay.LoopDecay.fastDecay (d.L N) hAd (List.ofFn σ) (by simp)
  have hℓ0 : 0 ≤ ellHat (d.L N) ((time s t K N j : ℝ) : ℂ) := by
    unfold ellHat; exact le_min (by positivity) (Nat.cast_nonneg _)
  have hAfd : FastDecay (d.L N) (ellHat (d.L N) ((time s t K N j : ℝ) : ℂ) * (4 * (d.W N : ℝ) ^ τ'))
      ((d.W N : ℝ) ^ (-D')) (AtrueN d E s t K N σ j ω) :=
    SumZeroDyn.FastDecay.mono (d.L N) hAfd0 (mul_le_mul_of_nonneg_left (by linarith) hℓ0) le_rfl
  exact kerClass_caseTwo_drift (d.L N) (d.three_le_L N) hu0 hu1 hjj
    (fun k => (norm_xiOf_mSigma hE.le σ k).le) hK4 hEnv0 hMD (driftErr514_nonneg d N m hMK hMD)
    (Real.rpow_nonneg (by positivity) _) hDM hAM hFD hAfd

end DriftQ

/-! ## §5 : the initial datum `A_0 = Q_{u_0}(L−K)_{u_0}` -/

section InitQ

variable (d : Dims)

/-- **h-A0cls, Case 2** (`kerClass_Qop_zero`, widened to the drift's radius `16W^{τ'}`). -/
theorem kerClass_A0Q {m : ℕ} {E : ℝ} (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ} (hτ' : 0 < τ')
    (hu0 : 0 ≤ time s t K N 0) (hu1 : time s t K N 0 < 1)
    (hmem : H d s t K N 0 ω ∈ goodSet514 d E N (time s t K N 0) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    {MD : ℝ} (hMD : 0 ≤ MD)
    (hDb : ∀ J : LoopIdx (ZMod (d.L N)), J.WF → J.length ≤ m + 2 →
      ‖gloop (d.L N) (d.W N) (H d s t K N 0 ω) (zt E (time s t K N 0)) J
        - (band d).Kval E N (time s t K N 0) J‖ ≤ MD) :
    KerClass (d.L N) (time s t K N) (4 * (4 * (d.W N : ℝ) ^ τ')) true
      (deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') MD ((d.W N : ℝ) ^ (-D'))) 0
      (AtrueQ d E s t K N σ 0 ω) := by
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hK4 : (1 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by linarith
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hlk⟩, _⟩, _⟩ := hmem
  have hAd : Decay.LoopDecay (d.L N) (m + 2)
      ((band d).ell N (time s t K N 0) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N 0 ω)
        (zt E (time s t K N 0)) I - (band d).Kval E N (time s t K N 0) I) :=
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl
  have hAfd0 := Decay.LoopDecay.fastDecay (d.L N) hAd (List.ofFn σ) (by simp)
  have hℓ0 : 0 ≤ ellHat (d.L N) ((time s t K N 0 : ℝ) : ℂ) := by
    unfold ellHat; exact le_min (by positivity) (Nat.cast_nonneg _)
  have hAfd : FastDecay (d.L N)
      (ellHat (d.L N) ((time s t K N 0 : ℝ) : ℂ) * (4 * (d.W N : ℝ) ^ τ'))
      ((d.W N : ℝ) ^ (-D')) (AtrueN d E s t K N σ 0 ω) :=
    SumZeroDyn.FastDecay.mono (d.L N) hAfd0 (mul_le_mul_of_nonneg_left (by linarith) hℓ0) le_rfl
  have hAM : ∀ b, ‖AtrueN d E s t K N σ 0 ω b‖ ≤ MD := fun b =>
    hDb ⟨List.ofFn σ, List.ofFn b⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
  have h := kerClass_Qop_zero (d.L N) (d.three_le_L N) (u := time s t K N) hu0 hu1 hK4 hMD
    (Real.rpow_nonneg (by positivity) _) hAM hAfd
  exact kerClass_mono (d.L N) h (mul_le_mul_of_nonneg_left (by linarith) hℓ0) le_rfl

/-- **The size of `A_0`**: `‖Q_{u_0}(L−K)_{u_0}‖ ≤ (1+(24ecW^{τ'})^{m+1}) X0 + (2c)^{m+1}L^{m+1}W^{-D'}`
(Lemma 5.13 (5.87), `norm_Qop_le_of_fastDecay`). -/
theorem norm_AtrueQ0_le {m : ℕ} {E : ℝ} (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (ω : Ωg d) {ε₁ Λ Φ τ' D' ℓs : ℝ} (hτ' : 0 < τ')
    (hu0 : 0 ≤ time s t K N 0) (hu1 : time s t K N 0 < 1)
    (hmem : H d s t K N 0 ω ∈ goodSet514 d E N (time s t K N 0) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    {X0 : ℝ} (hX00 : 0 ≤ X0) (hX0 : ∀ b, ‖AtrueN d E s t K N σ 0 ω b‖ ≤ X0)
    (a : LoopArg (d.L N) (m + 2)) :
    ‖AtrueQ d E s t K N σ 0 ω a‖
      ≤ (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * X0
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'.le
  have hK4 : (1 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by linarith
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, hlk⟩, _⟩, _⟩ := hmem
  have hAd : Decay.LoopDecay (d.L N) (m + 2)
      ((band d).ell N (time s t K N 0) * (d.W N : ℝ) ^ τ')
      ((d.W N : ℝ) ^ (-D')) (fun I => gloop (d.L N) (d.W N) (H d s t K N 0 ω)
        (zt E (time s t K N 0)) I - (band d).Kval E N (time s t K N 0) I) :=
    Decay.LoopDecay.mono (d.L N) hlk (by omega) le_rfl le_rfl
  have hAfd0 := Decay.LoopDecay.fastDecay (d.L N) hAd (List.ofFn σ) (by simp)
  have hℓ0 : 0 ≤ ellHat (d.L N) ((time s t K N 0 : ℝ) : ℂ) := by
    unfold ellHat; exact le_min (by positivity) (Nat.cast_nonneg _)
  have hAfd : FastDecay (d.L N)
      (ellHat (d.L N) ((time s t K N 0 : ℝ) : ℂ) * (4 * (d.W N : ℝ) ^ τ'))
      ((d.W N : ℝ) ^ (-D')) (AtrueN d E s t K N σ 0 ω) :=
    SumZeroDyn.FastDecay.mono (d.L N) hAfd0 (mul_le_mul_of_nonneg_left (by linarith) hℓ0) le_rfl
  exact norm_Qop_le_of_fastDecay (d.L N) (d.three_le_L N) hu0 hu1 hK4 hX00
    (Real.rpow_nonneg (by positivity) _) hX0 hAfd a

end InitQ

/-! ## §6 : the martingale part — the joint `Q ⊗ Q` quadratic variation (5.103)–(5.105) -/

section QVQ

variable (d : Dims)

/-- The sub-Gaussian constant of the `j`-th propagated `Q`-increment towards `u_k`:
`Δ · qvBdSumZero(u_{j+1}, u_k)` (the right-hand side of `qv_contraction_le_sumZero`). -/
def cQVQ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N m : ℕ) (τ' D'' Φq : ℝ) (k : ℕ)
    (_a : LoopArg (d.L N) (m + 2)) (j : ℕ) : ℝ≥0 :=
  (step s t K N * qvBdSumZero d N E (m + 1) (time s t K N (j + 1)) (time s t K N k) τ' D''
    Φq).toNNReal

theorem qvBdSumZero_pos {E : ℝ} (hE : |E| < 2) {N k : ℕ} {v w τ D Φ : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) (hΦ : 0 ≤ Φ) :
    0 < qvBdSumZero d N E k v w τ D Φ := by
  have hv1 : v < 1 := hvw.trans_lt hw1
  have hW : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hL : (0 : ℝ) < d.L N := by have := d.three_le_L N; exact_mod_cast (by omega : 0 < d.L N)
  have hWD : (0 : ℝ) < (d.W N : ℝ) ^ (-D) := Real.rpow_pos_of_pos hW _
  have hWτ : (0 : ℝ) < (d.W N : ℝ) ^ τ := Real.rpow_pos_of_pos hW _
  have hη : 0 < etaT E v := etaT_pos hE hv1
  have hEE : 0 < eeHermErr d N (k + 1) D := by
    unfold eeHermErr
    have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    positivity
  have hℓv : 0 < ellHat (d.L N) ((v : ℝ) : ℂ) :=
    Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hv1
  have hℓw : 0 < ellHat (d.L N) ((w : ℝ) : ℂ) :=
    Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hw1
  have hA : 0 < (band d).scale E N v := (band d).scale_pos' hE N hv0 hv1
  have hAt : 0 ≤ ((band d).scale E N w)⁻¹ ^ (2 * (k + 1)) := by
    have := (band d).scale_pos' hE N (hv0.trans hvw) hw1
    positivity
  have h1v : 0 < 1 - v := by linarith
  have h1w : 0 < 1 - w := by linarith
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have he : 0 ≤ eeHermBd d N (k + 1) Φ ((band d).scale E N v)
      (ellHat (d.L N) (v : ℂ) * (d.W N : ℝ) ^ τ) D :=
    eeHermBd_nonneg d N (k + 1) hΦ hA (by positivity)
  have hq : 0 < FastDecayFlow.qqErr (d.L N) k (ellHat (d.L N) (v : ℂ)) ((d.W N : ℝ) ^ τ)
      (eeHermBd d N (k + 1) Φ ((band d).scale E N v)
        (ellHat (d.L N) (v : ℂ) * (d.W N : ℝ) ^ τ) D) (eeHermErr d N (k + 1) D) := by
    unfold FastDecayFlow.qqErr FastDecayFlow.qBlockErr FastDecayFlow.qBlockSize
    positivity
  have hfirst : 0 ≤ cKerSumZero ((k + 1) + (k + 1)) * (4 * (d.W N : ℝ) ^ τ) ^ (2 * ((k + 1) + (k + 1)))
      * (qqCoefE (d.L N) k ((d.W N : ℝ) ^ τ)
          * (6 * Real.exp 1 * ((k + 1 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ * Φ * (etaT E v)⁻¹
              * ((band d).scale E N w)⁻¹ ^ (2 * (k + 1))
            + ((1 - v) * ellHat (d.L N) (v : ℂ) / ((1 - w) * ellHat (d.L N) (w : ℂ)))
                ^ ((k + 1) + (k + 1)) * eeHermErr d N (k + 1) D)
        + ((1 - v) * ellHat (d.L N) (v : ℂ) / ((1 - w) * ellHat (d.L N) (w : ℂ)))
            ^ ((k + 1) + (k + 1))
          * (qqCoefD (d.L N) k ((d.W N : ℝ) ^ τ) * eeHermErr d N (k + 1) D)) := by
    have := cKerSumZero_nonneg ((k + 1) + (k + 1))
    have := qqCoefE_nonneg (d.L N) k hWτ.le
    have := qqCoefD_nonneg (d.L N) k hWτ.le
    positivity
  have hsecond : 0 < cKerSumZeroErr ((k + 1) + (k + 1)) * (d.L N : ℝ) ^ ((k + 1) + (k + 1))
      * ((1 - v) / (1 - w)) ^ ((k + 1) + (k + 1))
      * FastDecayFlow.qqErr (d.L N) k (ellHat (d.L N) (v : ℂ)) ((d.W N : ℝ) ^ τ)
          (eeHermBd d N (k + 1) Φ ((band d).scale E N v)
            (ellHat (d.L N) (v : ℂ) * (d.W N : ℝ) ^ τ) D)
          (eeHermErr d N (k + 1) D) := by
    have : 0 < cKerSumZeroErr ((k + 1) + (k + 1)) := by
      unfold cKerSumZeroErr; positivity
    positivity
  unfold qvBdSumZero
  linarith

set_option maxHeartbeats 1600000 in
/-- **h-qv, Case 2, the full joint `Q ⊗ Q` tensor** (`hqv_of_vC` +
`qv_contraction_le_sumZero`, called directly), with the time shift `u_j → u_{j+1}` discharged by
`xiLM_shift_le`/`decaySet_shift`. -/
theorem hqvQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (σ : Fin (m + 2) → Bool) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0)
    (τ : Ωg d → ℕ) (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    {ε₁ Λ Φ τ' D' D'' ℓs Φq : ℝ} (hτ' : 0 ≤ τ')
    (hmemτ : ∀ ω j, j < τ ω →
      H d s t K N j ω ∈ goodSet514 d E N (time s t K N j) (m + 2) ε₁ Λ Φ τ' D' ℓs)
    (hA1 : ∀ j ≤ K N, 1 ≤ (band d).scale E N (time s t K N j))
    (hshiftΞ : ∀ j < K N, (N : ℝ) ^ ε₁ * Λ
      + ((2 * (m + 2) + 2 : ℕ) : ℝ) * ((etaT E (time s t K N (j + 1)))⁻¹ ^ (2 * (m + 2) + 2 + 1)
          * (time s t K N (j + 1) - time s t K N j))
        * ((band d).scale E N (time s t K N j)) ^ (2 * (m + 2) + 2 - 1) ≤ Φq)
    (hshiftD : ∀ j < K N, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ 2 * (m + 2) + 2 →
      (d.W N : ℝ) ^ (-D') + (ℓ : ℝ) * ((etaT E (time s t K N (j + 1)))⁻¹ ^ (ℓ + 1)
          * (time s t K N (j + 1) - time s t K N j)) ≤ (d.W N : ℝ) ^ (-D'')) :
    ∀ k ≤ K N, ∀ (a : LoopArg (d.L N) (m + 2)) (j : ℕ), j < k →
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (j + 1) : ℂ)
            (time s t K N k : ℂ) (gridZC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω') a)
          ω).re)
        (cQVQ d E s t K N m τ' D'' Φq k a j) (Pg d) ∧
      HasCondSubgaussianMGF (filt d j) ((filt d).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator
          (fun ω' => Uker (d.L N) (xiOf (mSigma E) σ) (time s t K N (j + 1) : ℂ)
            (time s t K N k : ℂ) (gridZC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω') a)
          ω).im)
        (cQVQ d E s t K N m τ' D'' Φq k a j) (Pg d) := by
  have hΔ : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst hi
  refine hqv_of_vC s t K N (m + 2) (xiOf (mSigma E) σ) τ hτmeas (gridΦQ d E s t K N σ)
    (gridΦQ_testFun d hE hst ht1 hK0 σ) hΔ (cQVQ d E s t K N m τ' D'' Φq) ?_
  intro k hk a j hj ω hjτ
  have hjK : j < K N := lt_of_lt_of_le hj hk
  have hj1 := hmem (j + 1) (by omega)
  have hj0 := hmem j hjK.le
  have hkk := hmem k hk
  have hjj : time s t K N j ≤ time s t K N (j + 1) := by
    unfold time; push_cast; nlinarith [hΔ]
  have hj1k : time s t K N (j + 1) ≤ time s t K N k := by
    unfold time
    have : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    nlinarith [hΔ]
  have hgood := hmemτ ω j hjτ
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hΞ0, _⟩, _⟩, _⟩, _⟩, hdec0⟩, _⟩, _⟩, _⟩ := hgood
  have hHerm := H_isHermitian d s t K N j ω
  have hsh := xiLM_shift_le d hE hHerm (hs0.trans hj0.1) hjj (hj1.2.trans_lt ht1)
    (m := 2 * (m + 2) + 2) (by omega)
  have hΞ : loopXi (d.L N) (d.W N) (H d s t K N j ω) (zt E (time s t K N (j + 1)))
      ((band d).scale E N (time s t K N (j + 1))) (2 * (m + 1 + 1) + 2) ≤ Φq := by
    show xiLM d E N (time s t K N (j + 1)) (H d s t K N j ω) (2 * (m + 2) + 2) ≤ Φq
    have h0 : xiLM d E N (time s t K N j) (H d s t K N j ω) (2 * (m + 2) + 2) ≤ (N : ℝ) ^ ε₁ * Λ :=
      hΞ0
    have := hshiftΞ j hjK
    linarith
  have hdec : H d s t K N j ω ∈ decaySet d E N (2 * (m + 1 + 1) + 2) (time s t K N (j + 1)) τ' D'' :=
    decaySet_shift d hE hHerm (hs0.trans hj0.1) hjj (hj1.2.trans_lt ht1) hdec0 (hshiftD j hjK)
  have h := mul_le_mul_of_nonneg_left
    (qv_contraction_le_sumZero hE (k := m + 1) σ (hs0.trans hj1.1) hj1k (hkk.2.trans_lt ht1) hτ'
      (fun c => (band d).Kval E N (time s t K N (j + 1)) (toIdx σ c)) hHerm
      (hA1 (j + 1) (by omega)) hΞ hdec a) hΔ
  refine h.trans ?_
  exact Real.le_coe_toNNReal _

theorem cQVQ_sum_pos {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N < t N) (ht1 : t N < 1) {τ' D'' Φq : ℝ} (hΦq : 0 ≤ Φq) :
    ∀ k, 1 ≤ k → k ≤ K N → ∀ a : LoopArg (d.L N) (m + 2),
      0 < ∑ j ∈ Finset.range k, (cQVQ d E s t K N m τ' D'' Φq k a j : ℝ) := by
  intro k hk1 hk a
  have hK : 0 < K N := lt_of_lt_of_le hk1 hk
  have hΔ : 0 < step s t K N := div_pos (by linarith) (by exact_mod_cast hK)
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst.le hi
  have hterm : ∀ j ∈ Finset.range k, 0 ≤ (cQVQ d E s t K N m τ' D'' Φq k a j : ℝ) :=
    fun j _ => NNReal.coe_nonneg _
  have h0 : (0 : ℕ) ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hterm h0)
  unfold cQVQ
  have h1 := hmem 1 (by omega)
  have hk' := hmem k hk
  have h1k : time s t K N (0 + 1) ≤ time s t K N k := by
    unfold time
    have : ((0 + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith [hΔ.le]
  have hpos := mul_pos hΔ (qvBdSumZero_pos d hE (N := N) (k := m + 1) (τ := τ') (D := D'')
    (hs0.trans h1.1) h1k (hk'.2.trans_lt ht1) hΦq)
  rw [Real.coe_toNNReal _ hpos.le]
  exact hpos

end QVQ

/-! ## §7 : the second-order increment — the conditional moments -/

section YQ

variable (d : Dims)

/-- `c = ρ (C₂/2) Δ` of `Ymoments_of_ae_eq` for the `Q`-family: coarse kernel row sum
`ρ = (1+(1-T)^{-1})^n`, `C₂ = (1 + L^{n-1}) C2g`. -/
def cYQ (d : Dims) (N m : ℕ) (T η Δ : ℝ) : ℝ :=
  (1 + (1 - T)⁻¹) ^ (m + 2) * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N (m + 2) η) / 2 * Δ)

def vYQ (d : Dims) (N m : ℕ) (T η Δ : ℝ) : ℝ :=
  cYQ d N m T η Δ ^ 2 * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2)

def wYQ (d : Dims) (N m : ℕ) (T η Δ : ℝ) : ℝ :=
  cYQ d N m T η Δ ^ 4 * (8 * (xMom d N 8 + xMom d N 2 ^ 4))

/-- The `Y` scale `P` of `grid_assembly_at_tau'`. -/
def PYQ (d : Dims) (N m : ℕ) (T η : ℝ) : ℝ :=
  ((1 + (1 - T)⁻¹) ^ (m + 2) * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N (m + 2) η) / 2)) ^ 2
    * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) + 1)

theorem vYQ_wYQ_le (N m : ℕ) (T η Δ : ℝ) :
    vYQ d N m T η Δ ≤ Δ ^ 2 * PYQ d N m T η ∧ wYQ d N m T η Δ ≤ Δ ^ 4 * PYQ d N m T η ^ 2 := by
  set c0 := (1 + (1 - T)⁻¹) ^ (m + 2) * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N (m + 2) η) / 2)
    with hc0
  have hc : cYQ d N m T η Δ = c0 * Δ := by unfold cYQ; rw [hc0]; ring
  have h2 := xMom_nonneg d N 2
  have h4 := xMom_nonneg d N 4
  have h8 := xMom_nonneg d N 8
  set X := 2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) + 1 with hX
  have hX1 : 1 ≤ X := by
    rw [hX]
    have : 0 ≤ 2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) := by
      positivity
    linarith
  have hP : PYQ d N m T η = c0 ^ 2 * X := by unfold PYQ; rw [← hc0, ← hX]
  constructor
  · unfold vYQ
    rw [hc, hP]
    have : 2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 ≤ X := by rw [hX]; nlinarith
    have e : (c0 * Δ) ^ 2 * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2)
        = Δ ^ 2 * (c0 ^ 2 * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (sq_nonneg _)) (sq_nonneg _)
  · unfold wYQ
    rw [hc, hP]
    have h8X : 8 * (xMom d N 8 + xMom d N 2 ^ 4) ≤ X ^ 2 := by
      have : 8 * (xMom d N 8 + xMom d N 2 ^ 4) ≤ X := by rw [hX]; nlinarith
      nlinarith
    have e : (c0 * Δ) ^ 4 * (8 * (xMom d N 8 + xMom d N 2 ^ 4))
        = Δ ^ 4 * (c0 ^ 4 * (8 * (xMom d N 8 + xMom d N 2 ^ 4))) := by ring
    rw [e]
    have e2 : (c0 ^ 2 * X) ^ 2 = c0 ^ 4 * X ^ 2 := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h8X (by positivity)) (by positivity)

set_option maxHeartbeats 1600000 in
/-- **h-Y′ for the `Q`-process**, from `Ymoments_of_ae_eq` applied to the
family `ΦQ` with the kernel folded into the label weight (`stepYC_ukerMatC_eq_Uker_ae`). -/
theorem Y_fieldsQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (N : ℕ) (hs0 : 0 ≤ s N) (hst : s N ≤ t N) (ht1 : t N < 1) (hK0 : K N ≠ 0)
    (σ : Fin (m + 2) → Bool) (τ : Ωg d → ℕ) (hτmeas : ∀ j, MeasurableSet[filt d j] {ω | j < τ ω})
    (k : ℕ) (hk : k ≤ K N) (b : LoopArg (d.L N) (m + 2)) (j : ℕ) (hj : j < k) :
    let Y := gridYC d s t K N (m + 2) (gridΦQ d E s t K N σ)
    let u := time s t K N
    let ξ := xiOf (mSigma E) σ
    let V := vYQ d N m (t N) (etaT E (t N)) (step s t K N)
    let W := wYQ d N m (t N) (etaT E (t N)) (step s t K N)
    (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re | filt d j] =ᵐ[Pg d] 0
    ∧ (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im | filt d j] =ᵐ[Pg d] 0
    ∧ Integrable (fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re ^ 4) (Pg d)
    ∧ Integrable (fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im ^ 4) (Pg d)
    ∧ (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re ^ 2 | filt d j]
        ≤ᵐ[Pg d] (fun _ => V)
    ∧ (Pg d)[fun ω => (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im ^ 2 | filt d j]
        ≤ᵐ[Pg d] (fun _ => V)
    ∧ (∫ ω, (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).re ^ 4 ∂(Pg d)) ≤ W
    ∧ (∫ ω, (stoppedEdge (d.L N) ξ u (u k) τ Y b j ω).im ^ 4 ∂(Pg d)) ≤ W := by
  intro Y u ξ V W
  have hΔ : 0 ≤ step s t K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hjK : j < K N := lt_of_lt_of_le hj hk
  have hmem : ∀ i, i ≤ K N → time s t K N i ∈ Set.Icc (s N) (t N) :=
    fun i hi => mem_Icc_time s t K N i hs0 hst hi
  have hj1 := hmem (j + 1) (by omega)
  have hkk := hmem k hk
  set Φ := gridΦQ d E s t K N σ (j + 1) with hΦdef
  have hΦ : ∀ a, TestFun d N (Φ a) :=
    gridΦQ_testFun d hE hst ht1 hK0 σ (j + 1) (by omega) (by omega)
  have hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖
      ≤ (1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N (m + 2) (etaT E (t N)) :=
    fun a A => gridΦQ_bdd2 d hE hs0 hst ht1 hK0 σ (j + 1) (by omega) (by omega) a A
  set U := ukerMatC (L := d.L N) ξ (time s t K N (j + 1)) (time s t K N k) with hUdef
  have hR : ∑ a, ‖U b a‖ ≤ (1 + (1 - t N)⁻¹) ^ (m + 2) := by
    refine (sum_norm_ukerMatC_le (d.three_le_L N) (fun i => (norm_xiOf_mSigma hE.le σ i).le)
      (hs0.trans hj1.1) (hj1.2.trans_lt ht1) (hs0.trans hkk.1) (hkk.2.trans_lt ht1) b).trans ?_
    have h1 : 0 < 1 - time s t K N k := by linarith [hkk.2]
    have h2 : (1 - time s t K N k)⁻¹ ≤ (1 - t N)⁻¹ := inv_anti₀ (by linarith) (by linarith [hkk.2])
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hS : MeasurableSet[filt d j] {ω | j < τ ω} := hτmeas j
  have hYeq : ∀ ω, Y (j + 1) ω
      = fun a => stepYC d s t K N j (m + 2) Φ (gridDeltaC (d.L N) (m + 2)) a ω := by
    intro ω; funext a
    show gridYC d s t K N (m + 2) (gridΦQ d E s t K N σ) (j + 1) ω a = _
    unfold gridYC
    have hc : 1 ≤ j + 1 ∧ j + 1 ≤ K N := ⟨by omega, by omega⟩
    simp only [hc, and_self, ↓reduceIte, Nat.add_sub_cancel]
    rfl
  have hae := stepYC_ukerMatC_eq_Uker_ae d s t K N j (m + 2) hΦ ξ (time s t K N (j + 1))
    (time s t K N k)
  have hSE : stoppedEdge (d.L N) ξ u (u k) τ Y b j
      =ᵐ[Pg d] {ω | j < τ ω}.indicator (fun ω => stepYC d s t K N j (m + 2) Φ U b ω) := by
    filter_upwards [hae] with ω hω
    rw [stoppedEdge_apply]
    by_cases h : j < τ ω
    · have hm : ω ∈ {ω' | j < τ ω'} := h
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, hω b, hYeq ω]
    · have hm : ω ∉ {ω' | j < τ ω'} := h
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
  have hRe := Ymoments_of_ae_eq s t K N j (m + 2) hΦ hC₂ hΔ U b hR hS hSE Complex.reCLM
    (fun z => by simpa using Complex.abs_re_le_norm z)
  have hIm := Ymoments_of_ae_eq s t K N j (m + 2) hΦ hC₂ hΔ U b hR hS hSE Complex.imCLM
    (fun z => by simpa using Complex.abs_im_le_norm z)
  simp only [Complex.reCLM_apply] at hRe
  simp only [Complex.imCLM_apply] at hIm
  obtain ⟨hmRe, hiRe, hcRe, h4Re⟩ := hRe
  obtain ⟨hmIm, hiIm, hcIm, h4Im⟩ := hIm
  exact ⟨hmRe, hmIm, hiRe, hiIm, hcRe, hcIm, h4Re, h4Im⟩

end YQ

/-! ## §8 : the `Q`-remainder is `O(Δ^{3/2})` with a polynomial constant -/

section QStepErr

/-- `VdB/Δ + τB/Δ` coefficient. -/
def gQ (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) + 5 * ((n : ℝ) + 2) ^ 2

/-- The constant of `qStepErr_le`. -/
def CqQ (n : ℕ) : ℝ :=
  ((n : ℝ) + 3) * gQ n + 2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2) + 5 * ((n : ℝ) + 2) ^ 2

theorem gQ_nonneg (n : ℕ) : 0 ≤ gQ n := by unfold gQ; have := cTwo52_pos; positivity
theorem CqQ_nonneg (n : ℕ) : 0 ≤ CqQ n := by unfold CqQ; have := gQ_nonneg n; positivity

set_option maxHeartbeats 1600000 in
/-- **`qStepErr` is `(1+L^{n+1}) S + O(Δ²)·poly`**: with `Y ≥ 1` bounding `L` and
`(1-(u+Δ))^{-1}`, and `ΔY ≤ 1`. -/
theorem qStepErr_le {L : ℕ} [NeZero L] (hL : 3 ≤ L) (n : ℕ) {u Δ Mk Dm S Y : ℝ} (hu0 : 0 ≤ u)
    (hΔ0 : 0 ≤ Δ) (hut1 : u + Δ < 1) (hMk0 : 0 ≤ Mk) (hDm0 : 0 ≤ Dm) (hS0 : 0 ≤ S)
    (hY1 : 1 ≤ Y) (hLY : (L : ℝ) ≤ Y) (hβ : (1 - (u + Δ))⁻¹ ≤ Y) (hΔY : Δ * Y ≤ 1) :
    qStepErr L n u Δ Mk Dm S
      ≤ (1 + Y ^ (n + 1)) * S + Δ ^ (3 / 2 : ℝ) * (CqQ n * Y ^ (2 * n + 9) * (Mk + Dm)) := by
  have hu1 : u < 1 := by linarith
  have h1uΔ : 0 < 1 - (u + Δ) := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hΔ1 : Δ ≤ 1 := by nlinarith
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
  have hβ0 : 0 ≤ β := inv_nonneg.2 h1uΔ.le
  have h1u : (1 - u)⁻¹ ≤ Y := (inv_anti₀ h1uΔ (by linarith)).trans hβ
  have h1u0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have hΔβ : Δ * β ≤ 1 := (mul_le_mul_of_nonneg_left hβ hΔ0).trans hΔY
  have hΔβ0 : 0 ≤ Δ * β := mul_nonneg hΔ0 hβ0
  have hc := cTwo52_pos
  have hℓ := half_le_ellHat_real L hL hu0 hu1
  have hℓ0 : 0 < ellHat L (u : ℂ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the pieces
  set Lp : ℝ := (L : ℝ) ^ (n + 1) with hLp
  have hLp0 : 0 ≤ Lp := by positivity
  have hLpY : Lp ≤ Y ^ (n + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hLY _
  set Ust : ℝ := ((n + 2 : ℕ) : ℝ) * Δ ^ 2 * β ^ 2
    + ((1 + Δ * β) ^ (n + 2) - 1 - ((n + 2 : ℕ) : ℝ) * Δ * β) with hUstdef
  have hUst : Ust ≤ (((n : ℝ) + 2) + 4 ^ (n + 2)) * Δ ^ 2 * Y ^ 2 := by
    have h1 : ((n + 2 : ℕ) : ℝ) * Δ ^ 2 * β ^ 2 ≤ ((n : ℝ) + 2) * Δ ^ 2 * Y ^ 2 := by
      push_cast
      have := pow_le_pow_left₀ hβ0 hβ 2
      have : 0 ≤ ((n : ℝ) + 2) * Δ ^ 2 := by positivity
      nlinarith
    have h2 := one_add_pow_sub_le (n + 2) hΔβ0 hΔβ
    have e : ((n + 2 : ℕ) : ℝ) * Δ * β = ((n + 2 : ℕ) : ℝ) * (Δ * β) := by ring
    have h3 : 4 ^ (n + 2) * (Δ * β) ^ 2 ≤ 4 ^ (n + 2) * (Δ ^ 2 * Y ^ 2) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ0 hβ 2)
        (sq_nonneg _)) (by positivity)
    rw [hUstdef, e]
    nlinarith
  have hUst0 : 0 ≤ Ust := by
    rw [hUstdef]
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ Δ * β by linarith) (n + 2)
    have e : ((n + 2 : ℕ) : ℝ) * Δ * β = ((n + 2 : ℕ) : ℝ) * (Δ * β) := by ring
    rw [e]
    have : 0 ≤ ((n + 2 : ℕ) : ℝ) * Δ ^ 2 * β ^ 2 := by positivity
    linarith
  set τB : ℝ := 5 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * β ^ (n + 1 + 6) * Δ ^ 2 with hτBdef
  have hτB : τB ≤ 5 * ((n : ℝ) + 2) ^ 2 * Y ^ (n + 7) * Δ ^ 2 := by
    rw [hτBdef]
    have e : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
    rw [e, show n + 1 + 6 = n + 7 by ring]
    have := pow_le_pow_left₀ hβ0 hβ (n + 7)
    have h0 : 0 ≤ 5 * ((n : ℝ) + 2) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) (sq_nonneg _)
  have hτB0 : 0 ≤ τB := by rw [hτBdef]; positivity
  set VdB : ℝ := 2 * ((n + 1 : ℕ) : ℝ) * (cTwo52 / ellHat L (u : ℂ)) ^ (n + 1) * (1 - u)⁻¹
    with hVdBdef
  have hcl : cTwo52 / ellHat L (u : ℂ) ≤ 2 * cTwo52 := by
    rw [div_le_iff₀ hℓ0]; nlinarith
  have hVdB : VdB ≤ 2 * ((n : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) * Y := by
    rw [hVdBdef]
    have h1 := pow_le_pow_left₀ (by positivity) hcl (n + 1)
    push_cast
    gcongr
  have hVdB0 : 0 ≤ VdB := by rw [hVdBdef]; positivity
  set Vdiff : ℝ := Δ * VdB + τB with hVdiffdef
  have hYn7 : Y ≤ Y ^ (n + 7) := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ (n + 7) := pow_le_pow_right₀ hY1 (by omega)
  have hVdiff : Vdiff ≤ Δ * (gQ n * Y ^ (n + 7)) := by
    rw [hVdiffdef]
    have h1 : Δ * VdB ≤ Δ * (2 * ((n : ℝ) + 1) * (2 * cTwo52) ^ (n + 1) * Y ^ (n + 7)) := by
      refine mul_le_mul_of_nonneg_left (hVdB.trans ?_) hΔ0
      exact mul_le_mul_of_nonneg_left hYn7 (by positivity)
    have h2 : τB ≤ Δ * (5 * ((n : ℝ) + 2) ^ 2 * Y ^ (n + 7)) := by
      refine hτB.trans ?_
      have : Δ ^ 2 ≤ Δ := by nlinarith
      have h0 : 0 ≤ 5 * ((n : ℝ) + 2) ^ 2 * Y ^ (n + 7) := by positivity
      nlinarith
    unfold gQ
    nlinarith
  have hVdiff0 : 0 ≤ Vdiff := by rw [hVdiffdef]; positivity
  have hΔ2 : Δ ^ 2 ≤ Δ ^ (3 / 2 : ℝ) := by
    rcases hΔ0.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge h hΔ1 (by norm_num)
  have hg0 := gQ_nonneg n
  -- assemble
  have hY2n9 : ∀ a, a ≤ 2 * n + 9 → Y ^ a ≤ Y ^ (2 * n + 9) := fun a ha => pow_le_pow_right₀ hY1 ha
  have T1 : (1 + Lp) * S ≤ (1 + Y ^ (n + 1)) * S := by
    have : 1 + Lp ≤ 1 + Y ^ (n + 1) := by linarith
    exact mul_le_mul_of_nonneg_right this hS0
  have T2 : Δ * (Lp * Dm) * Vdiff ≤ Δ ^ 2 * (gQ n * Y ^ (2 * n + 9) * Dm) := by
    have h1 : Δ * (Lp * Dm) * Vdiff ≤ Δ * (Y ^ (n + 1) * Dm) * (Δ * (gQ n * Y ^ (n + 7))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLpY hDm0) hΔ0) hVdiff
        hVdiff0 (by positivity)
    have h2 : Y ^ (n + 1) * Y ^ (n + 7) ≤ Y ^ (2 * n + 9) := by
      rw [← pow_add]; exact hY2n9 _ (by omega)
    calc Δ * (Lp * Dm) * Vdiff ≤ Δ * (Y ^ (n + 1) * Dm) * (Δ * (gQ n * Y ^ (n + 7))) := h1
      _ = Δ ^ 2 * (gQ n * (Y ^ (n + 1) * Y ^ (n + 7)) * Dm) := by ring
      _ ≤ Δ ^ 2 * (gQ n * Y ^ (2 * n + 9) * Dm) := by gcongr
  have T3 : 2 * (Lp * (Ust * Mk)) ≤ Δ ^ 2 * ((2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2))
      * Y ^ (2 * n + 9) * Mk) := by
    have h1 : 2 * (Lp * (Ust * Mk)) ≤ 2 * (Y ^ (n + 1) * (((((n : ℝ) + 2) + 4 ^ (n + 2))
        * Δ ^ 2 * Y ^ 2) * Mk)) := by
      gcongr
    have h2 : Y ^ (n + 1) * Y ^ 2 ≤ Y ^ (2 * n + 9) := by
      rw [← pow_add]; exact hY2n9 _ (by omega)
    calc 2 * (Lp * (Ust * Mk)) ≤ 2 * (Y ^ (n + 1) * (((((n : ℝ) + 2) + 4 ^ (n + 2))
          * Δ ^ 2 * Y ^ 2) * Mk)) := h1
      _ = Δ ^ 2 * ((2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2)) * (Y ^ (n + 1) * Y ^ 2) * Mk) := by ring
      _ ≤ _ := by gcongr
  have T4 : Lp * Mk * τB ≤ Δ ^ 2 * (5 * ((n : ℝ) + 2) ^ 2 * Y ^ (2 * n + 9) * Mk) := by
    have h1 : Lp * Mk * τB ≤ Y ^ (n + 1) * Mk * (5 * ((n : ℝ) + 2) ^ 2 * Y ^ (n + 7) * Δ ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hLpY hMk0) hτB hτB0 (by positivity)
    have h2 : Y ^ (n + 1) * Y ^ (n + 7) ≤ Y ^ (2 * n + 9) := by
      rw [← pow_add]; exact hY2n9 _ (by omega)
    calc Lp * Mk * τB ≤ Y ^ (n + 1) * Mk * (5 * ((n : ℝ) + 2) ^ 2 * Y ^ (n + 7) * Δ ^ 2) := h1
      _ = Δ ^ 2 * (5 * ((n : ℝ) + 2) ^ 2 * (Y ^ (n + 1) * Y ^ (n + 7)) * Mk) := by ring
      _ ≤ _ := by gcongr
  have T5 : Δ * (Lp * (((n + 2 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk)) * Vdiff
      ≤ Δ ^ 2 * (((n : ℝ) + 2) * gQ n * Y ^ (2 * n + 9) * Mk) := by
    have h1 : Δ * (Lp * (((n + 2 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk)) * Vdiff
        ≤ Δ * (Y ^ (n + 1) * (((n : ℝ) + 2) * Y * Mk)) * (Δ * (gQ n * Y ^ (n + 7))) := by
      push_cast
      gcongr
    have h2 : Y ^ (n + 1) * Y * Y ^ (n + 7) ≤ Y ^ (2 * n + 9) := by
      rw [← pow_succ, ← pow_add]; exact hY2n9 _ (by omega)
    calc Δ * (Lp * (((n + 2 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk)) * Vdiff
        ≤ Δ * (Y ^ (n + 1) * (((n : ℝ) + 2) * Y * Mk)) * (Δ * (gQ n * Y ^ (n + 7))) := h1
      _ = Δ ^ 2 * (((n : ℝ) + 2) * gQ n * (Y ^ (n + 1) * Y * Y ^ (n + 7)) * Mk) := by ring
      _ ≤ _ := by gcongr
  have hsum : Δ ^ 2 * (gQ n * Y ^ (2 * n + 9) * Dm)
      + Δ ^ 2 * ((2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2)) * Y ^ (2 * n + 9) * Mk)
      + Δ ^ 2 * (5 * ((n : ℝ) + 2) ^ 2 * Y ^ (2 * n + 9) * Mk)
      + Δ ^ 2 * (((n : ℝ) + 2) * gQ n * Y ^ (2 * n + 9) * Mk)
      ≤ Δ ^ (3 / 2 : ℝ) * (CqQ n * Y ^ (2 * n + 9) * (Mk + Dm)) := by
    have e : Δ ^ 2 * (gQ n * Y ^ (2 * n + 9) * Dm)
        + Δ ^ 2 * ((2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2)) * Y ^ (2 * n + 9) * Mk)
        + Δ ^ 2 * (5 * ((n : ℝ) + 2) ^ 2 * Y ^ (2 * n + 9) * Mk)
        + Δ ^ 2 * (((n : ℝ) + 2) * gQ n * Y ^ (2 * n + 9) * Mk)
        = Δ ^ 2 * Y ^ (2 * n + 9) * (gQ n * Dm
          + (2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2) + 5 * ((n : ℝ) + 2) ^ 2
            + ((n : ℝ) + 2) * gQ n) * Mk) := by ring
    rw [e]
    have hle : gQ n * Dm + (2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2) + 5 * ((n : ℝ) + 2) ^ 2
        + ((n : ℝ) + 2) * gQ n) * Mk ≤ CqQ n * (Mk + Dm) := by
      have e2 : CqQ n * (Mk + Dm) - (gQ n * Dm + (2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2)
          + 5 * ((n : ℝ) + 2) ^ 2 + ((n : ℝ) + 2) * gQ n) * Mk)
          = gQ n * Mk + (((n : ℝ) + 2) * gQ n + 2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2)
            + 5 * ((n : ℝ) + 2) ^ 2) * Dm := by unfold CqQ; ring
      have : 0 ≤ gQ n * Mk + (((n : ℝ) + 2) * gQ n + 2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2)
            + 5 * ((n : ℝ) + 2) ^ 2) * Dm := by positivity
      linarith
    have hY0' : 0 ≤ Y ^ (2 * n + 9) := by positivity
    have hX0 : 0 ≤ gQ n * Dm + (2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2) + 5 * ((n : ℝ) + 2) ^ 2
        + ((n : ℝ) + 2) * gQ n) * Mk := by positivity
    calc Δ ^ 2 * Y ^ (2 * n + 9) * (gQ n * Dm
          + (2 * ((n : ℝ) + 2) + 2 * 4 ^ (n + 2) + 5 * ((n : ℝ) + 2) ^ 2
            + ((n : ℝ) + 2) * gQ n) * Mk)
        ≤ Δ ^ (3 / 2 : ℝ) * Y ^ (2 * n + 9) * (CqQ n * (Mk + Dm)) := by
          gcongr
      _ = _ := by ring
  show (1 + Lp) * S + Δ * (Lp * Dm) * Vdiff + 2 * (Lp * (Ust * Mk)) + Lp * Mk * τB
      + Δ * (Lp * (((n + 2 : ℕ) : ℝ) * (1 - u)⁻¹ * Mk)) * Vdiff ≤ _
  linarith

end QStepErr

section QStepErrGrid

variable (d : Dims)

theorem lkEnv_le {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u Bk Y : ℝ} (hu1 : u < 1)
    (hηY : (etaT E u)⁻¹ ≤ Y) (hY1 : 1 ≤ Y) (hBk : Bk ≤ Y) :
    lkEnv (band d) E N m u Bk ≤ 2 * Y ^ (m + 2) := by
  unfold lkEnv
  rw [abs_zt_im hE hu1]
  have hη0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
  have hW1 : (1 : ℝ) ≤ ((band d).W N : ℝ) := by exact_mod_cast (band d).W_pos N
  have hWi : (((band d).W N : ℝ))⁻¹ ^ (m + 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hW1)
  have h1 : (etaT E u)⁻¹ ^ (m + 2) ≤ Y ^ (m + 2) := pow_le_pow_left₀ hη0 hηY _
  have h2 : Y ≤ Y ^ (m + 2) := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ (m + 2) := pow_le_pow_right₀ hY1 (by omega)
  have h3 : (etaT E u)⁻¹ ^ (m + 2) * (((band d).W N : ℝ))⁻¹ ^ (m + 1) ≤ Y ^ (m + 2) := by
    calc (etaT E u)⁻¹ ^ (m + 2) * (((band d).W N : ℝ))⁻¹ ^ (m + 1)
        ≤ Y ^ (m + 2) * 1 := mul_le_mul h1 hWi (by positivity) (by positivity)
      _ = Y ^ (m + 2) := mul_one _
  linarith

theorem driftEnv_le {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u Bk Y : ℝ} (hu1 : u < 1) (hBk0 : 0 ≤ Bk)
    (hηY : (etaT E u)⁻¹ ≤ Y) (hY1 : 1 ≤ Y) (hBk : Bk ≤ Y) (hW : (d.W N : ℝ) ≤ Y)
    (hL : (d.L N : ℝ) ≤ Y) :
    driftEnv (band d) E N m u Bk ≤ 10 * ((m : ℝ) + 2) ^ 3 * Y ^ (2 * m + 8) := by
  have hη0 : 0 ≤ (etaT E u)⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
  set MG : ℝ := (etaT E u)⁻¹ ^ (m + 3) with hMG
  have hMG0 : 0 ≤ MG := by positivity
  have hY0 : 0 ≤ Y := by linarith
  have hMGY : MG ≤ Y ^ (m + 3) := pow_le_pow_left₀ hη0 hηY _
  have hY3 : 1 ≤ Y ^ (m + 3) := one_le_pow₀ hY1
  have hYY : Y ≤ Y ^ (m + 3) := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ (m + 3) := pow_le_pow_right₀ hY1 (by omega)
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ d.L N := Nat.cast_nonneg _
  have hm2 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  show (d.W N : ℝ) * ((m : ℝ) + 2) * ((d.L N : ℝ) * ((MG + 1) * MG))
      + ((m : ℝ) + 2) * (2 * ((d.W N : ℝ) * ((m : ℝ) + 2) ^ 2
          * ((d.L N : ℝ) * (Bk * (MG + Bk)))))
      + (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * ((d.L N : ℝ) * ((MG + Bk) * (MG + Bk))) ≤ _
  have hY8 : Y ^ (2 * m + 8) = Y * (Y * (Y ^ (m + 3) * Y ^ (m + 3))) := by
    rw [← pow_add, ← pow_succ', ← pow_succ']; ring_nf
  have e1 : (d.W N : ℝ) * ((m : ℝ) + 2) * ((d.L N : ℝ) * ((MG + 1) * MG))
      ≤ ((m : ℝ) + 2) * (2 * Y ^ (2 * m + 8)) := by
    rw [hY8]
    have : (MG + 1) * MG ≤ (2 * Y ^ (m + 3)) * Y ^ (m + 3) :=
      mul_le_mul (by linarith) hMGY hMG0 (by positivity)
    calc (d.W N : ℝ) * ((m : ℝ) + 2) * ((d.L N : ℝ) * ((MG + 1) * MG))
        ≤ Y * ((m : ℝ) + 2) * (Y * ((2 * Y ^ (m + 3)) * Y ^ (m + 3))) := by gcongr
      _ = _ := by ring
  have e2 : ((m : ℝ) + 2) * (2 * ((d.W N : ℝ) * ((m : ℝ) + 2) ^ 2
          * ((d.L N : ℝ) * (Bk * (MG + Bk)))))
      ≤ ((m : ℝ) + 2) ^ 3 * (4 * Y ^ (2 * m + 8)) := by
    rw [hY8]
    have : Bk * (MG + Bk) ≤ Y ^ (m + 3) * (2 * Y ^ (m + 3)) :=
      mul_le_mul (hBk.trans hYY) (by linarith) (by positivity) (by positivity)
    calc ((m : ℝ) + 2) * (2 * ((d.W N : ℝ) * ((m : ℝ) + 2) ^ 2
          * ((d.L N : ℝ) * (Bk * (MG + Bk)))))
        ≤ ((m : ℝ) + 2) * (2 * (Y * ((m : ℝ) + 2) ^ 2
          * (Y * (Y ^ (m + 3) * (2 * Y ^ (m + 3)))))) := by gcongr
      _ = _ := by ring
  have e3 : (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * ((d.L N : ℝ) * ((MG + Bk) * (MG + Bk)))
      ≤ ((m : ℝ) + 2) ^ 2 * (4 * Y ^ (2 * m + 8)) := by
    rw [hY8]
    have hb : MG + Bk ≤ 2 * Y ^ (m + 3) := by linarith
    have : (MG + Bk) * (MG + Bk) ≤ (2 * Y ^ (m + 3)) * (2 * Y ^ (m + 3)) :=
      mul_le_mul hb hb (by positivity) (by positivity)
    calc (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * ((d.L N : ℝ) * ((MG + Bk) * (MG + Bk)))
        ≤ Y * ((m : ℝ) + 2) ^ 2 * (Y * ((2 * Y ^ (m + 3)) * (2 * Y ^ (m + 3)))) := by gcongr
      _ = _ := by ring
  have hY8' : 0 ≤ Y ^ (2 * m + 8) := by positivity
  have hc1 : ((m : ℝ) + 2) ≤ ((m : ℝ) + 2) ^ 3 := by
    calc ((m : ℝ) + 2) = ((m : ℝ) + 2) ^ 1 := (pow_one _).symm
      _ ≤ ((m : ℝ) + 2) ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
  have hc2 : ((m : ℝ) + 2) ^ 2 ≤ ((m : ℝ) + 2) ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
  nlinarith

/-- The constant of `qErrQ_le`. -/
def CRQ (m : ℕ) : ℝ := 200 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2)
  + CqQ m * (2 + 10 * ((m : ℝ) + 2) ^ 3)

theorem CRQ_nonneg (m : ℕ) : 0 ≤ CRQ m := by
  unfold CRQ; have := CqQ_nonneg m; positivity

set_option maxHeartbeats 1600000 in
/-- **The `Q`-remainder at one grid step is `O(Δ^{3/2})`**: `qErrQ ≤ Δ^{3/2} CRQ Y^{4m+21}` with
`Y ≥ 1` bounding `W, L, #Idx, 1+η^{-1}_{u_{j+1}}, Bk` and `ΔY ≤ 1`. -/
theorem qErrQ_le {E : ℝ} (hE : |E| < 2) (s t : ℕ → ℝ) (K : ℕ → ℕ) (N m : ℕ) {Bk Y : ℝ}
    (j : ℕ) (hu0 : 0 ≤ time s t K N j) (hjj : time s t K N j ≤ time s t K N (j + 1))
    (hu1 : time s t K N (j + 1) < 1) (hΔ0 : 0 ≤ step s t K N)
    (hstep : time s t K N (j + 1) = time s t K N j + step s t K N) (hBk0 : 0 ≤ Bk)
    (hY1 : 1 ≤ Y) (hW : (d.W N : ℝ) ≤ Y) (hL : (d.L N : ℝ) ≤ Y)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ Y)
    (hηY : 1 + (etaT E (time s t K N (j + 1)))⁻¹ ≤ Y) (hβ : (1 - time s t K N (j + 1))⁻¹ ≤ Y)
    (hBk : Bk ≤ Y) (hΔY : step s t K N * Y ≤ 1) :
    qErrQ d E s t K N m Bk j ≤ step s t K N ^ (3 / 2 : ℝ) * (CRQ m * Y ^ (4 * m + 21)) := by
  set u := time s t K N j with hu
  set Δ := step s t K N with hΔ
  have huj1 : u < 1 := hjj.trans_lt hu1
  have hη1 := etaT_pos hE hu1
  have hηj := etaT_pos hE huj1
  have hηle : (etaT E u)⁻¹ ≤ (etaT E (time s t K N (j + 1)))⁻¹ :=
    inv_anti₀ hη1 (etaT_anti hE hjj)
  have hηu : (etaT E u)⁻¹ ≤ Y := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hut1 : u + Δ < 1 := by rw [← hstep]; exact hu1
  have hβ' : (1 - (u + Δ))⁻¹ ≤ Y := by rw [← hstep]; exact hβ
  have hMk := lkEnv_le d hE N m huj1 hηu hY1 hBk
  have hDm := driftEnv_le d hE N m huj1 hBk0 hηu hY1 hBk hW hL
  have hMk0 : 0 ≤ lkEnv (band d) E N m u Bk := by
    unfold lkEnv; positivity
  have hDm0 : 0 ≤ driftEnv (band d) E N m u Bk := by
    unfold driftEnv; positivity
  have hS := stepErrN_le d hE N (m + 2) hu0 hjj hu1 hΔ0 hBk0 hY1 hW hL hcard hηY hBk hΔY
  have hS0 := stepErrN_nonneg d hE N (m + 2) hjj hu1 hΔ0 hBk0
  have hq := qStepErr_le (d.three_le_L N) m hu0 hΔ0 hut1 hMk0 hDm0 hS0 hY1 hL hβ' hΔY
  have hΔ32 : 0 ≤ Δ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hΔ0 _
  unfold qErrQ
  refine hq.trans ?_
  have hYm1 : 1 + Y ^ (m + 1) ≤ 2 * Y ^ (m + 1) := by
    have := one_le_pow₀ (n := m + 1) hY1; linarith
  have hpow1 : Y ^ (m + 1) * Y ^ (2 * (m + 2) + 16) ≤ Y ^ (4 * m + 21) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hY1 (by omega)
  have hpow2 : Y ^ (m + 2) ≤ Y ^ (2 * m + 8) := pow_le_pow_right₀ hY1 (by omega)
  have hpow3 : Y ^ (2 * m + 9) * Y ^ (2 * m + 8) ≤ Y ^ (4 * m + 21) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hY1 (by omega)
  have hC0 : 0 ≤ 100 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2) := by positivity
  have t1 : (1 + Y ^ (m + 1)) * stepErrN (band d) E N (m + 2) u (time s t K N (j + 1)) Δ Bk
      ≤ Δ ^ (3 / 2 : ℝ) * (200 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2) * Y ^ (4 * m + 21)) := by
    calc (1 + Y ^ (m + 1)) * stepErrN (band d) E N (m + 2) u (time s t K N (j + 1)) Δ Bk
        ≤ (2 * Y ^ (m + 1)) * (Δ ^ (3 / 2 : ℝ) * (100 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2)
            * Y ^ (2 * (m + 2) + 16))) := mul_le_mul hYm1 hS hS0 (by positivity)
      _ = Δ ^ (3 / 2 : ℝ) * (200 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2)
            * (Y ^ (m + 1) * Y ^ (2 * (m + 2) + 16))) := by ring
      _ ≤ _ := by gcongr
  have t2 : Δ ^ (3 / 2 : ℝ) * (CqQ m * Y ^ (2 * m + 9)
        * (lkEnv (band d) E N m u Bk + driftEnv (band d) E N m u Bk))
      ≤ Δ ^ (3 / 2 : ℝ) * (CqQ m * (2 + 10 * ((m : ℝ) + 2) ^ 3) * Y ^ (4 * m + 21)) := by
    have hsum : lkEnv (band d) E N m u Bk + driftEnv (band d) E N m u Bk
        ≤ (2 + 10 * ((m : ℝ) + 2) ^ 3) * Y ^ (2 * m + 8) := by
      have : 2 * Y ^ (m + 2) ≤ 2 * Y ^ (2 * m + 8) := by linarith
      nlinarith
    have hCq := CqQ_nonneg m
    refine mul_le_mul_of_nonneg_left ?_ hΔ32
    calc CqQ m * Y ^ (2 * m + 9) * (lkEnv (band d) E N m u Bk + driftEnv (band d) E N m u Bk)
        ≤ CqQ m * Y ^ (2 * m + 9) * ((2 + 10 * ((m : ℝ) + 2) ^ 3) * Y ^ (2 * m + 8)) := by
          gcongr
      _ = CqQ m * (2 + 10 * ((m : ℝ) + 2) ^ 3) * (Y ^ (2 * m + 9) * Y ^ (2 * m + 8)) := by ring
      _ ≤ _ := by gcongr
  unfold CRQ
  have e : Δ ^ (3 / 2 : ℝ) * ((200 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2)
        + CqQ m * (2 + 10 * ((m : ℝ) + 2) ^ 3)) * Y ^ (4 * m + 21))
      = Δ ^ (3 / 2 : ℝ) * (200 * (((m + 2 : ℕ) : ℝ) + 1) ^ 6 * 4 ^ (m + 2) * Y ^ (4 * m + 21))
        + Δ ^ (3 / 2 : ℝ) * (CqQ m * (2 + 10 * ((m : ℝ) + 2) ^ 3) * Y ^ (4 * m + 21)) := by ring
  rw [e]
  linarith

set_option maxHeartbeats 1600000 in
/-- **The remainder term of the `Q`-assembly**:
`Σ_{j<K} (1+(1-u_K)^{-1})^n qErrQ_j ≤ (1+N)^n·CRQ (2N)^{4m+21}·Δ^{1/2}`. -/
theorem tb_RQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hW : (d.W N : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hN1 : (1 : ℝ) ≤ N) {CK : ℝ} (hCK : 0 ≤ CK)
    (hCKN : CK + 1 ≤ 2 * (N : ℝ)) (hΔN : step s v K N * (2 * (N : ℝ)) ≤ 1) :
    ∑ j ∈ Finset.range (K N), (1 + (1 - time s v K N (K N))⁻¹) ^ (m + 2)
        * qErrQ d E s v K N m (CK + 1) j
      ≤ (1 + (N : ℝ)) ^ (m + 2) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21))
          * step s v K N ^ ((1 : ℝ) / 2) := by
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have huK : u (K N) = v N := time_last s v K N hK0
  have hKΔ : (K N : ℝ) * Δ = v N - s N := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step; field_simp
  set CR := CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21) with hCR
  have hCR0 : 0 ≤ CR := by have := CRQ_nonneg m; positivity
  have hcoarse : (1 + (1 - u (K N))⁻¹) ^ (m + 2) ≤ (1 + (N : ℝ)) ^ (m + 2) := by
    rw [huK]
    have h := (inv_eta_le_of hE hv1 hη le_rfl).2
    have h0 : 0 ≤ (1 - v N)⁻¹ := inv_nonneg.mpr (by linarith)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hstep' : ∀ j ∈ Finset.range (K N), (1 + (1 - u (K N))⁻¹) ^ (m + 2)
      * qErrQ d E s v K N m (CK + 1) j ≤ (1 + (N : ℝ)) ^ (m + 2) * CR * Δ ^ ((3 : ℝ) / 2) := by
    intro j hj
    have hjK : j < K N := Finset.mem_range.mp hj
    have hjj : u j ≤ u (j + 1) := by rw [hu]; unfold time; push_cast; nlinarith
    have hη1 := inv_eta_le_of hE hv1 hη (hmem (j + 1) (by omega)).2
    have hst : u (j + 1) = u j + Δ := by rw [hu, hΔ]; unfold time; push_cast; ring
    have hq := qErrQ_le d hE s v K N m j (hu0 j hjK.le) hjj (hu1 (j + 1) (by omega)) hΔ0 hst
      (by linarith : (0 : ℝ) ≤ CK + 1) (by linarith : (1 : ℝ) ≤ 2 * N) (by linarith)
      (by linarith) (by linarith) (by linarith [hη1.1]) (by linarith [hη1.2]) hCKN hΔN
    have hc0 : 0 ≤ (1 + (1 - u (K N))⁻¹) ^ (m + 2) := by
      have : 0 ≤ (1 - u (K N))⁻¹ := inv_nonneg.mpr (by linarith [hu1 (K N) le_rfl])
      positivity
    have hb0 : 0 ≤ Δ ^ (3 / 2 : ℝ) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21)) := by
      have := CRQ_nonneg m
      have := Real.rpow_nonneg hΔ0 (3 / 2 : ℝ)
      positivity
    calc (1 + (1 - u (K N))⁻¹) ^ (m + 2) * qErrQ d E s v K N m (CK + 1) j
        ≤ (1 + (1 - u (K N))⁻¹) ^ (m + 2)
            * (Δ ^ (3 / 2 : ℝ) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21))) :=
          mul_le_mul_of_nonneg_left hq hc0
      _ ≤ (1 + (N : ℝ)) ^ (m + 2) * (Δ ^ (3 / 2 : ℝ) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21))) :=
          mul_le_mul_of_nonneg_right hcoarse hb0
      _ = (1 + (N : ℝ)) ^ (m + 2) * CR * Δ ^ ((3 : ℝ) / 2) := by rw [hCR]; ring
  refine (Finset.sum_le_sum hstep').trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h32 : Δ ^ ((3 : ℝ) / 2) = Δ * Δ ^ ((1 : ℝ) / 2) := by
    rcases hΔ0.eq_or_lt with h | h
    · rw [← h]; simp
    · rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one]
  rw [h32]
  have hKΔ1 : (K N : ℝ) * Δ ≤ 1 := by rw [hKΔ]; linarith
  have hX0 : 0 ≤ (1 + (N : ℝ)) ^ (m + 2) * CR * Δ ^ ((1 : ℝ) / 2) := by
    have := Real.rpow_nonneg hΔ0 ((1 : ℝ) / 2)
    positivity
  have e : (K N : ℝ) * ((1 + (N : ℝ)) ^ (m + 2) * CR * (Δ * Δ ^ ((1 : ℝ) / 2)))
      = ((K N : ℝ) * Δ) * ((1 + (N : ℝ)) ^ (m + 2) * CR * Δ ^ ((1 : ℝ) / 2)) := by ring
  rw [e]
  calc ((K N : ℝ) * Δ) * ((1 + (N : ℝ)) ^ (m + 2) * CR * Δ ^ ((1 : ℝ) / 2))
      ≤ 1 * ((1 + (N : ℝ)) ^ (m + 2) * CR * Δ ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hKΔ1 hX0
    _ = _ := by rw [hCR, one_mul]

end QStepErrGrid

/-! ## §9 : the assembly at a fixed `N` (`grid_assembly_at_tau'`, every field discharged) -/

section AssemblyQ

variable (d : Dims)

/-- The sharp (7.16) Case 2 kernel weight of `hker_of_Q716_sumZero`. -/
def kapQ (L n : ℕ) (Kd : ℝ) (u : ℕ → ℝ) (i k : ℕ) : ℝ :=
  cKerSumZero n * Kd ^ (2 * n)
    * ((1 - u i) * ellHat L ((u i : ℝ) : ℂ) / ((1 - u k) * ellHat L ((u k : ℝ) : ℂ))) ^ n

/-- The additive decay-error weight of (7.16) Case 2. -/
def epsQ (L n : ℕ) (u : ℕ → ℝ) (i k : ℕ) : ℝ :=
  cKerSumZeroErr n * (L : ℝ) ^ n * ((1 - u i) / (1 - u k)) ^ n

/-- The class error of the Case 2 drift (`kerClass_caseTwo_drift`). -/
def δDQ (d : Dims) (E : ℝ) (N m : ℕ) (u τ' D' MK MD Bk : ℝ) : ℝ :=
  deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') (driftEnv (band d) E N m u Bk)
      (driftErr514 d N m MK MD D')
    + deltaCommS (d.L N) (m + 1) u (4 * (d.W N : ℝ) ^ τ') MD ((d.W N : ℝ) ^ (-D'))
    + deltaVD (d.L N) (m + 1) u (4 * (d.W N : ℝ) ^ τ') MD ((d.W N : ℝ) ^ (-D'))

theorem kapQ_nonneg {L n : ℕ} [NeZero L] (hL : 3 ≤ L) {Kd : ℝ} (hKd : 0 ≤ Kd) (u : ℕ → ℝ)
    {i k : ℕ} (_hi0 : 0 ≤ u i) (hi1 : u i < 1) (_hk0 : 0 ≤ u k) (hk1 : u k < 1) :
    0 ≤ kapQ L n Kd u i k := by
  unfold kapQ
  have hc := cKerSumZero_nonneg n
  have hl1 : 0 < ellHat L ((u i : ℝ) : ℂ) := Step3.ellHat_pos_of_lt_one (by omega) hi1
  have hl2 : 0 < ellHat L ((u k : ℝ) : ℂ) := Step3.ellHat_pos_of_lt_one (by omega) hk1
  have h1 : 0 < 1 - u i := by linarith
  have h2 : 0 < 1 - u k := by linarith
  positivity

theorem epsQ_nonneg (L n : ℕ) (u : ℕ → ℝ) {i k : ℕ} (hi1 : u i < 1) (hk1 : u k < 1) :
    0 ≤ epsQ L n u i k := by
  unfold epsQ cKerSumZeroErr
  have h1 : 0 < 1 - u i := by linarith
  have h2 : 0 < 1 - u k := by linarith
  have := cTwo52_pos
  positivity

theorem δDQ_nonneg {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u τ' D' MK MD Bk : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hτ' : 0 ≤ τ') (hMK : 0 ≤ MK) (hMD : 0 ≤ MD) (hBk : 0 ≤ Bk) :
    0 ≤ δDQ d E N m u τ' D' MK MD Bk := by
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' :=
    Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'
  have hK4 : (1 : ℝ) ≤ 4 * (d.W N : ℝ) ^ τ' := by linarith
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hEnv : 0 ≤ driftEnv (band d) E N m u Bk := by
    have := etaT_pos hE hu1
    unfold driftEnv; positivity
  unfold δDQ
  have := deltaQop_nonneg (d.L N) (n := m + 1) hK4 hEnv (driftErr514_nonneg d N m (D' := D') hMK hMD)
  have := deltaCommS_nonneg (d.L N) (d.three_le_L N) (n := m + 1) hu0 hu1 hK4 hMD hWD
  have := deltaVD_nonneg (d.L N) (d.three_le_L N) (n := m + 1) hu0 hu1 hK4 hMD hWD
  linarith

theorem dDrQ_nonneg {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u ε₁ τ' D' Φ CK B MK MD : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hA : 0 < (band d).scale E N u) (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK)
    (hB : 0 ≤ B) (hMK : 0 ≤ MK) (hMD : 0 ≤ MD) :
    0 ≤ dDrQ d E N m u ε₁ τ' D' Φ CK B MK MD := by
  unfold dDrQ
  have := dDr514_nonneg d hE N (m + 2) (ε₁ := ε₁) (τ' := τ') (D' := D') hu1 hA hΦ hCK hB
  have := driftErr514_nonneg d N m (D' := D') hMK hMD
  have := PwQ_nonneg d hE N m (ε₁ := ε₁) (τ' := τ') (D' := D') hu1 hΦ
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  have := cTwo52_pos
  have : 0 < ellHat (d.L N) (u : ℂ) := ellHat_real_pos' (d.L N) (d.three_le_L N) hu0 hu1
  have : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  positivity

end AssemblyQ

/-! ## §10 : the (5.93) budget at a fixed `N` — no `η_s/η_t` prefactor on any main term -/

section BudgetQ

variable (d : Dims)

/-- **(5.93), the sharp Case 2 kernel on a datum of scale `A_{u_i}^{-n}`**:
`κ_{i,k} A_{u_i}^{-n} = cKerSumZero·Kd^{2n}·A_{u_k}^{-n}` exactly. -/
theorem kapQ_mul_scale_pow_eq {E : ℝ} (hE : |E| < 2) (N n : ℕ) (Kd : ℝ) (u : ℕ → ℝ)
    (i k : ℕ) (hi0 : 0 ≤ u i) (hi1 : u i < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1) :
    kapQ (d.L N) n Kd u i k * ((band d).scale E N (u i))⁻¹ ^ n
      = cKerSumZero n * Kd ^ (2 * n) * ((band d).scale E N (u k))⁻¹ ^ n := by
  unfold kapQ
  rw [mul_assoc, scale_ratio_pow (d := d) hE hi0 hi1 hk0 hk1 n]

/-- **(5.93) on the drift**: `κ_{j+1,k} A_{u_j}^{-n} ≤ cKerSumZero·Kd^{2n}·A_{u_k}^{-n}`. -/
theorem kapQ_succ_mul_scale_pow_le {E : ℝ} (hE : |E| < 2) (N n : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd)
    (u : ℕ → ℝ) (j k : ℕ) (hj0 : 0 ≤ u j) (hjj : u j ≤ u (j + 1)) (hj1k : u (j + 1) ≤ u k)
    (hk1 : u k < 1) :
    kapQ (d.L N) n Kd u (j + 1) k * ((band d).scale E N (u j))⁻¹ ^ n
      ≤ cKerSumZero n * Kd ^ (2 * n) * ((band d).scale E N (u k))⁻¹ ^ n := by
  have hj1 : u (j + 1) < 1 := hj1k.trans_lt hk1
  have hk0 : 0 ≤ u k := hj0.trans (hjj.trans hj1k)
  have hA1 : 0 < (band d).scale E N (u (j + 1)) :=
    (band d).scale_pos' hE N (hj0.trans hjj) hj1
  have hle : (band d).scale E N (u (j + 1)) ≤ (band d).scale E N (u j) :=
    scale_anti514 d hE N hjj hj1
  have hinv : ((band d).scale E N (u j))⁻¹ ^ n ≤ ((band d).scale E N (u (j + 1)))⁻¹ ^ n :=
    pow_le_pow_left₀ (inv_nonneg.mpr (hA1.le.trans hle)) (inv_anti₀ hA1 hle) n
  have hκ0 : 0 ≤ kapQ (d.L N) n Kd u (j + 1) k :=
    kapQ_nonneg (d.three_le_L N) hKd u (hj0.trans hjj) hj1 hk0 hk1
  calc kapQ (d.L N) n Kd u (j + 1) k * ((band d).scale E N (u j))⁻¹ ^ n
      ≤ kapQ (d.L N) n Kd u (j + 1) k * ((band d).scale E N (u (j + 1)))⁻¹ ^ n :=
        mul_le_mul_of_nonneg_left hinv hκ0
    _ = _ := kapQ_mul_scale_pow_eq d hE N n Kd u (j + 1) k (hj0.trans hjj) hj1 hk0 hk1

/-- `κ_{i,k} ≤ cKerSumZero·Kd^{2n}·A_{u_i}^n` when `A_{u_k} ≥ 1` (for the tails only). -/
theorem kapQ_le_max {E : ℝ} (hE : |E| < 2) (N n : ℕ) {Kd : ℝ} (hKd : 0 ≤ Kd) (u : ℕ → ℝ)
    (i k : ℕ) (hi0 : 0 ≤ u i) (hi1 : u i < 1) (hk0 : 0 ≤ u k) (hk1 : u k < 1)
    (hAk : 1 ≤ (band d).scale E N (u k)) :
    kapQ (d.L N) n Kd u i k ≤ cKerSumZero n * Kd ^ (2 * n) * (band d).scale E N (u i) ^ n := by
  have hr := ratio514_pow_le d hE N n u i k hi0 hi1 hk0 hk1 hAk
  unfold kapQ
  have hc := cKerSumZero_nonneg n
  exact mul_le_mul_of_nonneg_left hr (by positivity)

theorem epsQ_le {L n : ℕ} (u : ℕ → ℝ) {i k : ℕ} {X : ℝ} (hi0 : 0 ≤ u i) (hi1 : u i < 1)
    (hk1 : u k < 1) (hX : (1 - u k)⁻¹ ≤ X) :
    epsQ L n u i k ≤ cKerSumZeroErr n * (L : ℝ) ^ n * X ^ n := by
  have h := eps514_le (n := n) u hi0 hi1 hk1 hX
  unfold eps514 at h
  unfold epsQ
  have : 0 ≤ cKerSumZeroErr n * (L : ℝ) ^ n := by
    unfold cKerSumZeroErr; have := cTwo52_pos; positivity
  exact mul_le_mul_of_nonneg_left h this

/-- The main coefficient of the Case 2 drift bound. -/
def McQ (d : Dims) (N m : ℕ) (ε₁ τ' CK : ℝ) : ℝ :=
  (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * Mc514 d N (m + 2) ε₁ τ' CK
    + 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m
      * (N : ℝ) ^ ε₁

/-- The tail of the Case 2 drift bound. -/
def TailDQ (d : Dims) (E : ℝ) (N m : ℕ) (u ε₁ τ' D' Φ B MK MD : ℝ) : ℝ :=
  (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * Ec514 d N (m + 2) ε₁ D' Φ B
    + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D'
    + 4 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
      * (((d.W N : ℝ) * etaT E u)⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))

theorem McQ_nonneg (N m : ℕ) {ε₁ τ' CK : ℝ} (hCK : 0 ≤ CK) : 0 ≤ McQ d N m ε₁ τ' CK := by
  unfold McQ Mc514
  have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
  have := cTwo52_pos
  positivity

/-- **The Case 2 drift bound split into its sharp main part and its tail**:
`dDrQ ≤ McQ·Φ·η_u^{-1}·A_u^{-n} + TailDQ` (`(1-u)^{-1} ≤ η_u^{-1}` since `Im m ≤ 1`). -/
theorem dDrQ_le_split {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u ε₁ τ' D' Φ CK B MK MD : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hΦ : 0 ≤ Φ) :
    dDrQ d E N m u ε₁ τ' D' Φ CK B MK MD
      ≤ McQ d N m ε₁ τ' CK * Φ * (etaT E u)⁻¹ * ((band d).scale E N u)⁻¹ ^ (m + 2)
        + TailDQ d E N m u ε₁ τ' D' Φ B MK MD := by
  have hL3 := d.three_le_L N
  have hη := etaT_pos hE hu1
  have hW0 : (0 : ℝ) < d.W N := by exact_mod_cast d.W_pos N
  have hℓ0 : 0 < ellHat (d.L N) (u : ℂ) := ellHat_real_pos' (d.L N) hL3 hu0 hu1
  have h1u : 0 < 1 - u := by linarith
  have hc := cTwo52_pos
  have hmim := mE_im_pos hE
  have hmim1 := mE_im_le_one hE
  -- (1-u)^{-1} ≤ η_u^{-1}
  have h1uη : (1 - u)⁻¹ ≤ (etaT E u)⁻¹ := by
    have heq : (1 - u)⁻¹ = (mE E).im * (etaT E u)⁻¹ := by
      unfold etaT; field_simp
    rw [heq]
    have h0 : 0 ≤ (etaT E u)⁻¹ := by positivity
    nlinarith
  -- the Ward main term
  have hscale : (band d).scale E N u = ((d.W N : ℝ) * etaT E u) * ellHat (d.L N) (u : ℂ) := by
    show (d.W N : ℝ) * ellHat (d.L N) (u : ℂ) * etaT E u = _; ring
  set w := (d.W N : ℝ) ^ τ' with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg hW0.le _
  have hNe : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hward : 4 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
        * ((4 * Real.exp 1) ^ m * w ^ m * ((d.W N : ℝ) * etaT E u)⁻¹ ^ (m + 2)
          * ((band d).ell N u)⁻¹ * ((N : ℝ) ^ ε₁ * Φ))
      ≤ 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * w ^ m * (N : ℝ) ^ ε₁
          * Φ * (etaT E u)⁻¹ * ((band d).scale E N u)⁻¹ ^ (m + 2) := by
    have hellEq : (band d).ell N u = ellHat (d.L N) (u : ℂ) := rfl
    rw [hellEq, hscale]
    have e : 4 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1)
        * ((4 * Real.exp 1) ^ m * w ^ m * ((d.W N : ℝ) * etaT E u)⁻¹ ^ (m + 2)
          * (ellHat (d.L N) (u : ℂ))⁻¹ * ((N : ℝ) ^ ε₁ * Φ))
        = (4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * w ^ m * (N : ℝ) ^ ε₁
          * Φ * (((d.W N : ℝ) * etaT E u) * ellHat (d.L N) (u : ℂ))⁻¹ ^ (m + 2)) * (1 - u)⁻¹ := by
      simp only [mul_inv, inv_pow, div_eq_mul_inv, mul_pow]
      ring
    rw [e]
    have h0 : 0 ≤ 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * w ^ m
        * (N : ℝ) ^ ε₁ * Φ * (((d.W N : ℝ) * etaT E u) * ellHat (d.L N) (u : ℂ))⁻¹ ^ (m + 2) := by
      positivity
    calc _ ≤ (4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * w ^ m * (N : ℝ) ^ ε₁
          * Φ * (((d.W N : ℝ) * etaT E u) * ellHat (d.L N) (u : ℂ))⁻¹ ^ (m + 2))
            * (etaT E u)⁻¹ := mul_le_mul_of_nonneg_left h1uη h0
      _ = _ := by ring
  have hsplit := dDr514_eq d E N (m + 2) u ε₁ τ' D' Φ CK B
  have hE0 : dDr514 d E N (m + 2) u ε₁ τ' D' Φ CK B
      = Mc514 d N (m + 2) ε₁ τ' CK * Φ * (etaT E u)⁻¹ * ((band d).scale E N u)⁻¹ ^ (m + 2)
        + Ec514 d N (m + 2) ε₁ D' Φ B := by
    rw [hsplit]; unfold Mc514 Ec514; ring
  unfold dDrQ McQ TailDQ PwQ
  rw [hE0]
  rw [← hw]
  have hq : 0 ≤ 4 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (cTwo52 / ellHat (d.L N) (u : ℂ)) ^ (m + 1) := by
    positivity
  nlinarith [hward]

end BudgetQ

section ClassErr

open Real

/-- **The commutator class error, `u`-free**. -/
theorem deltaCommS_le (L : ℕ) [NeZero L] (n : ℕ) {t Kd M δ X : ℝ} (hℓ1 : 1 ≤ ellHat L (t : ℂ))
    (hℓL : ellHat L (t : ℂ) ≤ L) (ht1 : t < 1) (hX : (1 - t)⁻¹ ≤ X) (hKd : 0 ≤ Kd)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    deltaCommS L n t Kd M δ
      ≤ ((n : ℝ) + 1) * X * ((2 * exp 1 * ((L : ℝ) * Kd + 1)) ^ n * M + (L : ℝ) ^ n * δ)
          * cTwo52 ^ n * (2 + (L : ℝ) * cTwo52) * exp (-(cZero * Kd / 2)) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  set ℓ := ellHat L (t : ℂ) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hX0 : 0 ≤ X := (inv_nonneg.2 h1t.le).trans hX
  set P := psumBnd L n t Kd M δ with hPdef
  set Pb := (2 * exp 1 * ((L : ℝ) * Kd + 1)) ^ n * M + (L : ℝ) ^ n * δ with hPb
  have hP0 : 0 ≤ P := by rw [hPdef]; unfold psumBnd; positivity
  have hPP : P ≤ Pb := by
    rw [hPdef, hPb]; unfold psumBnd
    have : ℓ * Kd + 1 ≤ (L : ℝ) * Kd + 1 := by nlinarith
    have h2 : (2 * exp 1 * (ℓ * Kd + 1)) ^ n ≤ (2 * exp 1 * ((L : ℝ) * Kd + 1)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [exp_pos 1]) n
    nlinarith
  have hcl : (cTwo52 / ℓ) ^ n ≤ cTwo52 ^ n := FastDecayFlow.cTwo52_div_pow_le n hℓ1
  have hcl0 : 0 ≤ (cTwo52 / ℓ) ^ n := by positivity
  set e1 := exp (-(cZero * Kd / 2)) with he1
  have he10 : 0 ≤ e1 := (exp_pos _).le
  have ha : exp (-(cZero * ((ℓ * Kd) / 2) / ℓ)) = e1 := by
    rw [he1]; congr 1; field_simp
  have hb : exp (-(cZero * (ℓ * Kd) / ℓ)) ≤ e1 := by
    rw [he1]; apply exp_le_exp.2
    have : cZero * (ℓ * Kd) / ℓ = cZero * Kd := by field_simp
    rw [this]; nlinarith
  have hcc : exp (-(cZero * ((2 * (ℓ * Kd) + 1) / 2) / ℓ)) ≤ e1 := by
    rw [he1]; apply exp_le_exp.2
    have : cZero * ((2 * (ℓ * Kd) + 1) / 2) / ℓ = cZero * Kd + cZero / (2 * ℓ) := by field_simp
    rw [this]
    have : 0 ≤ cZero / (2 * ℓ) := by positivity
    nlinarith
  have hq : cTwo52 / ((1 - t) * ℓ) ≤ cTwo52 * X := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ (1 - t) * X := by
      have := mul_le_mul_of_nonneg_left hX h1t.le
      rwa [mul_inv_cancel₀ h1t.ne'] at this
    have h2 : 1 ≤ (1 - t) * X * ℓ := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hc.le
    nlinarith
  unfold deltaCommS commSErr
  rw [← hℓ, ← hPdef, ha]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have t1 : (1 - t)⁻¹ * (P * ((cTwo52 / ℓ) ^ n * e1)) ≤ X * (Pb * (cTwo52 ^ n * e1)) := by
    gcongr
  have t2 : (L : ℝ) * (cTwo52 / ((1 - t) * ℓ) * exp (-(cZero * (ℓ * Kd) / ℓ)) * (P * (cTwo52 / ℓ) ^ n))
      ≤ (L : ℝ) * (cTwo52 * X * e1 * (Pb * cTwo52 ^ n)) := by
    gcongr
  have t3 : (1 - t)⁻¹ * P * ((cTwo52 / ℓ) ^ n * exp (-(cZero * ((2 * (ℓ * Kd) + 1) / 2) / ℓ)))
      ≤ X * Pb * (cTwo52 ^ n * e1) := by
    gcongr
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  calc ((n : ℝ) + 1) * ((1 - t)⁻¹ * (P * ((cTwo52 / ℓ) ^ n * e1))
        + (L : ℝ) * (cTwo52 / ((1 - t) * ℓ) * exp (-(cZero * (ℓ * Kd) / ℓ))
          * (P * (cTwo52 / ℓ) ^ n)))
      + (1 + (n : ℝ)) * (1 - t)⁻¹ * P
        * ((cTwo52 / ℓ) ^ n * exp (-(cZero * ((2 * (ℓ * Kd) + 1) / 2) / ℓ)))
      ≤ ((n : ℝ) + 1) * (X * (Pb * (cTwo52 ^ n * e1))
          + (L : ℝ) * (cTwo52 * X * e1 * (Pb * cTwo52 ^ n)))
        + (1 + (n : ℝ)) * (X * Pb * (cTwo52 ^ n * e1)) := by
        have := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hn1
        have h3 := mul_le_mul_of_nonneg_left t3 (by positivity : (0 : ℝ) ≤ 1 + (n : ℝ))
        nlinarith
    _ = _ := by ring

/-- **The `ϑ̇·P` class error, `u`-free**. -/
theorem deltaVD_le (L : ℕ) [NeZero L] (n : ℕ) {t Kd M δ X : ℝ} (hℓ1 : 1 ≤ ellHat L (t : ℂ))
    (hℓL : ellHat L (t : ℂ) ≤ L) (ht1 : t < 1) (hX : (1 - t)⁻¹ ≤ X) (hKd : 0 ≤ Kd)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) :
    deltaVD L n t Kd M δ
      ≤ ((2 * exp 1 * ((L : ℝ) * Kd + 1)) ^ n * M + (L : ℝ) ^ n * δ)
          * (3 * n * cTwo52 ^ n * X * exp (cZero / 2)) * exp (-(cZero * Kd)) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  set ℓ := ellHat L (t : ℂ) with hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have h1t : 0 < 1 - t := by linarith
  set P := psumBnd L n t Kd M δ with hPdef
  set Pb := (2 * exp 1 * ((L : ℝ) * Kd + 1)) ^ n * M + (L : ℝ) ^ n * δ with hPb
  have hP0 : 0 ≤ P := by rw [hPdef]; unfold psumBnd; positivity
  have hPP : P ≤ Pb := by
    rw [hPdef, hPb]; unfold psumBnd
    have : ℓ * Kd + 1 ≤ (L : ℝ) * Kd + 1 := by nlinarith
    have h2 : (2 * exp 1 * (ℓ * Kd + 1)) ^ n ≤ (2 * exp 1 * ((L : ℝ) * Kd + 1)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by nlinarith [exp_pos 1]) n
    nlinarith
  have hcl : (cTwo52 / ℓ) ^ n ≤ cTwo52 ^ n := FastDecayFlow.cTwo52_div_pow_le n hℓ1
  have hex : exp (-(cZero * (ℓ * Kd - 1 / 2) / ℓ)) ≤ exp (cZero / 2) * exp (-(cZero * Kd)) := by
    rw [← exp_add]; apply exp_le_exp.2
    have : cZero * (ℓ * Kd - 1 / 2) / ℓ = cZero * Kd - cZero / (2 * ℓ) := by field_simp
    rw [this]
    have : cZero / (2 * ℓ) ≤ cZero / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hX0 : 0 ≤ X := (inv_nonneg.2 h1t.le).trans hX
  unfold deltaVD
  rw [← hℓ, ← hPdef]
  have h1 : 3 * (n : ℝ) * (cTwo52 / ℓ) ^ n * (1 - t)⁻¹ * exp (-(cZero * (ℓ * Kd - 1 / 2) / ℓ))
      ≤ 3 * n * cTwo52 ^ n * X * (exp (cZero / 2) * exp (-(cZero * Kd))) := by
    gcongr
  calc P * (3 * (n : ℝ) * (cTwo52 / ℓ) ^ n * (1 - t)⁻¹ * exp (-(cZero * (ℓ * Kd - 1 / 2) / ℓ)))
      ≤ Pb * (3 * n * cTwo52 ^ n * X * (exp (cZero / 2) * exp (-(cZero * Kd)))) :=
        mul_le_mul hPP h1 (by positivity) (by positivity)
    _ = _ := by ring

end ClassErr

section TailQ

variable (d : Dims)

open Real

/-- The `u`-free bound of the Case 2 class error `δDQ`. -/
def δDbd (d : Dims) (N m : ℕ) (τ' D' MK MD DE Y : ℝ) : ℝ :=
  driftErr514 d N m MK MD D'
    + exp (-(cZero * (4 * (d.W N : ℝ) ^ τ') / 2))
      * ((6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1) * DE
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D'
        + (((m : ℝ) + 2) * Y * cTwo52 ^ (m + 1) * (2 + (d.L N : ℝ) * cTwo52)
            + 3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * Y * exp (cZero / 2))
          * ((2 * exp 1 * ((d.L N : ℝ) * (4 * (d.W N : ℝ) ^ τ') + 1)) ^ (m + 1) * MD
            + (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')))

theorem δDQ_le {E : ℝ} (hE : |E| < 2) (N m : ℕ) {u τ' D' MK MD Bk DE Y : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (hτ' : 0 ≤ τ') (hMK : 0 ≤ MK) (hMD : 0 ≤ MD) (hBk0 : 0 ≤ Bk)
    (hX : (1 - u)⁻¹ ≤ Y) (hDE : driftEnv (band d) E N m u Bk ≤ DE) :
    δDQ d E N m u τ' D' MK MD Bk ≤ δDbd d N m τ' D' MK MD DE Y := by
  have hL3 := d.three_le_L N
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'
  set Kd := 4 * (d.W N : ℝ) ^ τ' with hKd
  have hKd0 : 0 ≤ Kd := by rw [hKd]; linarith
  have hℓ1 : 1 ≤ ellHat (d.L N) (u : ℂ) := one_le_ellHat (d.L N) hL3 hu0 hu1
  have hℓL : ellHat (d.L N) (u : ℂ) ≤ d.L N := ellHat_real_le_L hu1
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hdE0 := driftErr514_nonneg d N m (D' := D') hMK hMD
  have hEnv0 : 0 ≤ driftEnv (band d) E N m u Bk := by
    have := etaT_pos hE hu1
    unfold driftEnv; positivity
  have h1 := deltaCommS_le (d.L N) (m + 1) hℓ1 hℓL hu1 hX hKd0 hMD hWD
  have h2 := deltaVD_le (d.L N) (m + 1) hℓ1 hℓL hu1 hX hKd0 hMD hWD
  have hexle : exp (-(cZero * Kd)) ≤ exp (-(cZero * Kd / 2)) := by
    apply exp_le_exp.2; nlinarith
  set E1 := exp (-(cZero * Kd / 2)) with hE1
  have hE10 : 0 ≤ E1 := (exp_pos _).le
  set Pb := (2 * exp 1 * ((d.L N : ℝ) * Kd + 1)) ^ (m + 1) * MD
    + (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') with hPb
  have hPb0 : 0 ≤ Pb := by rw [hPb]; positivity
  have hY0 : 0 ≤ Y := (inv_nonneg.2 (by linarith)).trans hX
  have h2' : deltaVD (d.L N) (m + 1) u Kd MD ((d.W N : ℝ) ^ (-D'))
      ≤ Pb * (3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * Y * exp (cZero / 2)) * E1 := by
    refine h2.trans ?_
    push_cast
    have : 0 ≤ Pb * (3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * Y * exp (cZero / 2)) := by positivity
    exact mul_le_mul_of_nonneg_left hexle this
  have h1' : deltaCommS (d.L N) (m + 1) u Kd MD ((d.W N : ℝ) ^ (-D'))
      ≤ ((m : ℝ) + 2) * Y * Pb * cTwo52 ^ (m + 1) * (2 + (d.L N : ℝ) * cTwo52) * E1 := by
    refine h1.trans (le_of_eq ?_)
    push_cast; ring
  have h0 : deltaQop (d.L N) (m + 1) Kd (driftEnv (band d) E N m u Bk) (driftErr514 d N m MK MD D')
      ≤ driftErr514 d N m MK MD D'
        + ((6 * exp 1 * cTwo52 * Kd) ^ (m + 1) * DE
          + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D') * E1 := by
    unfold deltaQop
    rw [← hE1]
    have : (6 * exp 1 * cTwo52 * Kd) ^ (m + 1) * driftEnv (band d) E N m u Bk
        ≤ (6 * exp 1 * cTwo52 * Kd) ^ (m + 1) * DE :=
      mul_le_mul_of_nonneg_left hDE (by positivity)
    have e : (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D'
        = (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D' := rfl
    nlinarith
  unfold δDQ δDbd
  rw [← hKd, ← hE1, ← hPb]
  nlinarith

end TailQ

section TailQ2

variable (d : Dims)

open Real

theorem driftErr514_mono (N m : ℕ) {MK MD MD' D' : ℝ} (hMK : 0 ≤ MK) (hMD : MD ≤ MD') :
    driftErr514 d N m MK MD D' ≤ driftErr514 d N m MK MD' D' := by
  unfold driftErr514
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have : (0 : ℝ) ≤ (d.W N : ℝ) * ((m : ℝ) + 2) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
    positivity
  have : (0 : ℝ) ≤ (m : ℝ) * (2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ)
      * (d.W N : ℝ) ^ (-D')) := by positivity
  have : (0 : ℝ) ≤ 2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
    positivity
  nlinarith

theorem δDbd_mono (N m : ℕ) {τ' D' MK MD MD' DE Y : ℝ} (hMK : 0 ≤ MK) (hMD0 : 0 ≤ MD)
    (hMD : MD ≤ MD') (hY : 0 ≤ Y) (hτ' : 0 ≤ τ') :
    δDbd d N m τ' D' MK MD DE Y ≤ δDbd d N m τ' D' MK MD' DE Y := by
  have h1 := driftErr514_mono d N m (D' := D') hMK hMD
  have hc := cTwo52_pos
  have hW0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  unfold δDbd
  have hE0 : 0 ≤ exp (-(cZero * (4 * (d.W N : ℝ) ^ τ') / 2)) := (exp_pos _).le
  have hA : 0 ≤ ((m : ℝ) + 2) * Y * cTwo52 ^ (m + 1) * (2 + (d.L N : ℝ) * cTwo52)
      + 3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * Y * exp (cZero / 2) := by positivity
  have hB : (2 * exp 1 * ((d.L N : ℝ) * (4 * (d.W N : ℝ) ^ τ') + 1)) ^ (m + 1) * MD
      ≤ (2 * exp 1 * ((d.L N : ℝ) * (4 * (d.W N : ℝ) ^ τ') + 1)) ^ (m + 1) * MD' :=
    mul_le_mul_of_nonneg_left hMD (by positivity)
  have hC : (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD D'
      ≤ (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m MK MD' D' :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hD := mul_le_mul_of_nonneg_left (add_le_add_right hB ((d.L N : ℝ) ^ (m + 1)
    * (d.W N : ℝ) ^ (-D'))) hA
  nlinarith

/-- The `u`-free tail of the Case 2 drift bound. -/
def TailDbd (d : Dims) (N m : ℕ) (ε₁ τ' D' Φ CK : ℝ) : ℝ :=
  (1 + (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
      * Ec514 d N (m + 2) ε₁ D' Φ (((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) * (N : ℝ) ^ (m + 2))
    + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1)
      * driftErr514 d N m (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1) D'
    + 4 * ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1)
      * ((N : ℝ) * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))

set_option maxHeartbeats 4000000 in
/-- **(5.93) for the Case 2 drift, with the sharp kernel**: the drift term of the `Q`-assembly
bound at the target `u_K = v` is at most `cKerSumZero Kd^{2n}·McQ·Φ·A_v^{-n}·Σ_j Δ/η_{u_j}` (no
`η_s/η_t` prefactor) plus `u`-free tails. -/
theorem tb_driftQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hA : ∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale E N u)
    (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hN1 : (1 : ℝ) ≤ N) (hW : (d.W N : ℝ) ≤ N)
    (hL : (d.L N : ℝ) ≤ N) {ε₁ τ' D' Φ CK : ℝ} (hτ' : 0 ≤ τ') (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK)
    (hCKN : CK + 1 ≤ N) :
    step s v K N * ∑ j ∈ Finset.range (K N),
        (kapQ (d.L N) (m + 2) (4 * (4 * (d.W N : ℝ) ^ τ')) (time s v K N) (j + 1) (K N)
            * dDrQ d E N m (time s v K N j) ε₁ τ' D' Φ CK
                (MD514 d E N (m + 2) (CK + 1) (time s v K N j)
                  * (band d).scale E N (time s v K N j) ^ (m + 2))
                (CK + 1) (MD514 d E N (m + 2) (CK + 1) (time s v K N j))
          + epsQ (d.L N) (m + 2) (time s v K N) (j + 1) (K N)
            * δDQ d E N m (time s v K N j) τ' D' (CK + 1)
                (MD514 d E N (m + 2) (CK + 1) (time s v K N j)) (CK + 1))
      ≤ cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * McQ d N m ε₁ τ' CK
            * Φ * ((band d).scale E N (v N))⁻¹ ^ (m + 2)
            * ∑ j ∈ Finset.range (K N), step s v K N / etaT E (time s v K N j)
        + (cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
            * TailDbd d N m ε₁ τ' D' Φ CK
          + cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
            * δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
                (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N) := by
  set n := m + 2 with hn
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  set Kd := 4 * (4 * (d.W N : ℝ) ^ τ') with hKd
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have huK : u (K N) = v N := time_last s v K N hK0
  have hKΔ : (K N : ℝ) * Δ = v N - s N := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step; field_simp
  have hsumΔ : ∑ _j ∈ Finset.range (K N), Δ ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKΔ]; linarith
  have hW0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  have hKd0 : 0 ≤ Kd := by rw [hKd]; positivity
  set cS := cKerSumZero n with hcS
  have hcS0 : 0 ≤ cS := cKerSumZero_nonneg n
  set cE := cKerSumZeroErr n with hcE
  have hcE0 : 0 ≤ cE := by rw [hcE]; unfold cKerSumZeroErr; have := cTwo52_pos; positivity
  set Mbig : ℝ := (N : ℝ) + (N : ℝ) ^ n + CK + 1 with hMbig
  have hMbig0 : 0 ≤ Mbig := by rw [hMbig]; positivity
  set Mc := McQ d N m ε₁ τ' CK with hMc
  have hMc0 : 0 ≤ Mc := McQ_nonneg d N m hCK
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hAv : 1 ≤ (band d).scale E N (v N) := hA (v N) (hs0.trans hsv.le) le_rfl
  have hc := cTwo52_pos
  have hTbd0 : 0 ≤ TailDbd d N m ε₁ τ' D' Φ CK := by
    unfold TailDbd Ec514
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
    have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    have := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) hMbig0
    positivity
  have hDbd0 : 0 ≤ δDbd d N m τ' D' (CK + 1) Mbig (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8))
      N := by
    unfold δDbd
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
    have := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) hMbig0
    have := cZero_pos
    positivity
  -- per-step bounds
  have hstep : ∀ j ∈ Finset.range (K N),
      Δ * (kapQ (d.L N) n Kd u (j + 1) (K N)
            * dDrQ d E N m (u j) ε₁ τ' D' Φ CK
                (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
                (CK + 1) (MD514 d E N n (CK + 1) (u j))
          + epsQ (d.L N) n u (j + 1) (K N)
            * δDQ d E N m (u j) τ' D' (CK + 1) (MD514 d E N n (CK + 1) (u j)) (CK + 1))
        ≤ cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (Δ / etaT E (u j))
          + Δ * (cS * Kd ^ (2 * n) * (N : ℝ) ^ n * TailDbd d N m ε₁ τ' D' Φ CK
            + cE * (d.L N : ℝ) ^ n * (N : ℝ) ^ n
              * δDbd d N m τ' D' (CK + 1) Mbig (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8))
                N) := by
    intro j hj
    have hjK : j < K N := Finset.mem_range.mp hj
    have hj0 := hu0 j hjK.le
    have hj1 := hu1 j hjK.le
    have hjj : u j ≤ u (j + 1) := by
      rw [hu]; unfold time; push_cast; nlinarith
    have hj1K : u (j + 1) ≤ u (K N) := by
      rw [hu]; unfold time
      have : ((j + 1 : ℕ) : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hjK
      nlinarith
    have hAj : 1 ≤ (band d).scale E N (u j) := hA (u j) hj0 (hmem j hjK.le).2
    have hAj0 : 0 < (band d).scale E N (u j) := lt_of_lt_of_le one_pos hAj
    have hηj := inv_eta_le_of hE hv1 hη (hmem j hjK.le).2
    have hηj0 : 0 < etaT E (u j) := etaT_pos hE hj1
    have hMD : MD514 d E N n (CK + 1) (u j) ≤ Mbig := by
      unfold MD514
      have : (etaT E (u j))⁻¹ ^ n ≤ (N : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hηj.1 n
      rw [hMbig]; linarith
    have hMD0 : 0 ≤ MD514 d E N n (CK + 1) (u j) := by unfold MD514; positivity
    have hAjN : (band d).scale E N (u j) ≤ N := (scale_le_LW d hE N hj0 hj1).trans hLW
    have hB : MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n ≤ Mbig * (N : ℝ) ^ n :=
      mul_le_mul hMD (pow_le_pow_left₀ hAj0.le hAjN n) (by positivity) hMbig0
    -- the split
    have hsplit := dDrQ_le_split d hE N m (ε₁ := ε₁) (τ' := τ') (D' := D') (CK := CK)
      (B := MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) (MK := CK + 1)
      (MD := MD514 d E N n (CK + 1) (u j)) hj0 hj1 hΦ
    -- the tail
    have hT : TailDQ d E N m (u j) ε₁ τ' D' Φ
        (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) (CK + 1)
        (MD514 d E N n (CK + 1) (u j)) ≤ TailDbd d N m ε₁ τ' D' Φ CK := by
      unfold TailDQ TailDbd
      have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
      have hEc : Ec514 d N n ε₁ D' Φ (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
          ≤ Ec514 d N n ε₁ D' Φ (Mbig * (N : ℝ) ^ n) := by
        unfold Ec514
        have : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') := by
          positivity
        nlinarith
      have hdE := driftErr514_mono d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) hMD
      have hℓ1 : 1 ≤ ellHat (d.L N) (u j : ℂ) := one_le_ellHat (d.L N) (d.three_le_L N) hj0 hj1
      have hcl : (cTwo52 / ellHat (d.L N) (u j : ℂ)) ^ (m + 1) ≤ cTwo52 ^ (m + 1) :=
        FastDecayFlow.cTwo52_div_pow_le (m + 1) hℓ1
      have hW1 : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
      have hWη : ((d.W N : ℝ) * etaT E (u j))⁻¹ ≤ N := by
        rw [mul_inv]
        have : (d.W N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
        have h0 : 0 ≤ (etaT E (u j))⁻¹ := by positivity
        nlinarith [hηj.1]
      have h1u : (1 - u j)⁻¹ ≤ N := hηj.2
      have h1u0 : 0 ≤ (1 - u j)⁻¹ := inv_nonneg.2 (by linarith)
      have hX1 : (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
          * Ec514 d N (m + 2) ε₁ D' Φ (MD514 d E N n (CK + 1) (u j)
            * (band d).scale E N (u j) ^ n)
          ≤ (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
            * Ec514 d N (m + 2) ε₁ D' Φ (Mbig * (N : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hEc (by positivity)
      have hX2 := mul_le_mul_of_nonneg_left hdE
        (by positivity : (0 : ℝ) ≤ (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1))
      have hX3 : 4 * ((m : ℝ) + 2) * (1 - u j)⁻¹ * (cTwo52 / ellHat (d.L N) (u j : ℂ)) ^ (m + 1)
            * (((d.W N : ℝ) * etaT E (u j))⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
          ≤ 4 * ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1)
            * ((N : ℝ) * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D')) := by
        have hpos : 0 ≤ (cTwo52 / ellHat (d.L N) (u j : ℂ)) ^ (m + 1) := by positivity
        gcongr
      rw [hMbig] at hX1 hX2
      linarith
    have hκ0 : 0 ≤ kapQ (d.L N) n Kd u (j + 1) (K N) :=
      kapQ_nonneg (d.three_le_L N) hKd0 u (hj0.trans hjj) (hu1 (j + 1) (by omega))
        (hu0 (K N) le_rfl) (hu1 (K N) le_rfl)
    have hsharp := kapQ_succ_mul_scale_pow_le d hE N n hKd0 u j (K N) hj0 hjj hj1K
      (by rw [huK]; exact hv1)
    rw [huK] at hsharp
    have hκmax : kapQ (d.L N) n Kd u (j + 1) (K N) ≤ cS * Kd ^ (2 * n) * (N : ℝ) ^ n := by
      have h := kapQ_le_max d hE N n hKd0 u (j + 1) (K N) (hj0.trans hjj)
        (hu1 (j + 1) (by omega)) (hu0 (K N) le_rfl) (hu1 (K N) le_rfl) (by rw [huK]; exact hAv)
      have hA1N : (band d).scale E N (u (j + 1)) ≤ N :=
        (scale_le_LW d hE N (hj0.trans hjj) (hu1 (j + 1) (by omega))).trans hLW
      have hA10 : 0 < (band d).scale E N (u (j + 1)) :=
        (band d).scale_pos' hE N (hj0.trans hjj) (hu1 (j + 1) (by omega))
      refine h.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA10.le hA1N n) (by positivity))
    have hmain : kapQ (d.L N) n Kd u (j + 1) (K N)
          * dDrQ d E N m (u j) ε₁ τ' D' Φ CK
              (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
              (CK + 1) (MD514 d E N n (CK + 1) (u j))
        ≤ cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (etaT E (u j))⁻¹
          + cS * Kd ^ (2 * n) * (N : ℝ) ^ n * TailDbd d N m ε₁ τ' D' Φ CK := by
      have t0 := mul_le_mul_of_nonneg_left hsplit hκ0
      have e1 : kapQ (d.L N) n Kd u (j + 1) (K N)
          * (McQ d N m ε₁ τ' CK * Φ * (etaT E (u j))⁻¹ * ((band d).scale E N (u j))⁻¹ ^ (m + 2)
            + TailDQ d E N m (u j) ε₁ τ' D' Φ
              (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) (CK + 1)
              (MD514 d E N n (CK + 1) (u j)))
          = Mc * Φ * (etaT E (u j))⁻¹
              * (kapQ (d.L N) n Kd u (j + 1) (K N) * ((band d).scale E N (u j))⁻¹ ^ n)
            + kapQ (d.L N) n Kd u (j + 1) (K N) * TailDQ d E N m (u j) ε₁ τ' D' Φ
              (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) (CK + 1)
              (MD514 d E N n (CK + 1) (u j)) := by
        rw [hMc]; ring
      rw [e1] at t0
      have hq : 0 ≤ Mc * Φ * (etaT E (u j))⁻¹ := by positivity
      have t1 := mul_le_mul_of_nonneg_left hsharp hq
      have t2 : kapQ (d.L N) n Kd u (j + 1) (K N) * TailDQ d E N m (u j) ε₁ τ' D' Φ
              (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n) (CK + 1)
              (MD514 d E N n (CK + 1) (u j))
          ≤ cS * Kd ^ (2 * n) * (N : ℝ) ^ n * TailDbd d N m ε₁ τ' D' Φ CK :=
        (mul_le_mul_of_nonneg_left hT hκ0).trans (mul_le_mul_of_nonneg_right hκmax hTbd0)
      have e2 : Mc * Φ * (etaT E (u j))⁻¹ * (cKerSumZero n * Kd ^ (2 * n)
            * ((band d).scale E N (v N))⁻¹ ^ n)
          = cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (etaT E (u j))⁻¹ := by
        rw [hcS]; ring
      linarith
    have heps : epsQ (d.L N) n u (j + 1) (K N)
          * δDQ d E N m (u j) τ' D' (CK + 1) (MD514 d E N n (CK + 1) (u j)) (CK + 1)
        ≤ cE * (d.L N : ℝ) ^ n * (N : ℝ) ^ n
          * δDbd d N m τ' D' (CK + 1) Mbig (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N := by
      have he := epsQ_le (L := d.L N) (n := n) u (hj0.trans hjj) (hu1 (j + 1) (by omega))
        (hu1 (K N) le_rfl) (by simpa only [huK] using (inv_eta_le_of hE hv1 hη le_rfl).2)
      have he0 := epsQ_nonneg (d.L N) n u (hu1 (j + 1) (by omega)) (hu1 (K N) le_rfl)
      have hDE : driftEnv (band d) E N m (u j) (CK + 1)
          ≤ 10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8) :=
        driftEnv_le d hE N m hj1 (by linarith) hηj.1 hN1 hCKN hW hL
      have hd1 := δDQ_le d hE N m (D' := D') hj0 hj1 hτ' (by linarith : (0 : ℝ) ≤ CK + 1) hMD0
        (by linarith : (0 : ℝ) ≤ CK + 1) hηj.2 hDE
      have hd2 := δDbd_mono d N m (τ' := τ') (D' := D') (DE := 10 * ((m : ℝ) + 2) ^ 3
        * (N : ℝ) ^ (2 * m + 8)) (by linarith : (0 : ℝ) ≤ CK + 1) hMD0 hMD hN0 hτ'
      exact (mul_le_mul_of_nonneg_left (hd1.trans hd2) he0).trans
        (mul_le_mul_of_nonneg_right he hDbd0)
    have hΔdiv : Δ * (cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n
        * (etaT E (u j))⁻¹)
        = cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (Δ / etaT E (u j)) := by
      rw [div_eq_mul_inv]; ring
    have key := mul_le_mul_of_nonneg_left (add_le_add hmain heps) hΔ0
    have e : Δ * ((cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n
          * (etaT E (u j))⁻¹ + cS * Kd ^ (2 * n) * (N : ℝ) ^ n * TailDbd d N m ε₁ τ' D' Φ CK)
          + cE * (d.L N : ℝ) ^ n * (N : ℝ) ^ n
            * δDbd d N m τ' D' (CK + 1) Mbig (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N)
        = cS * Kd ^ (2 * n) * Mc * Φ * ((band d).scale E N (v N))⁻¹ ^ n * (Δ / etaT E (u j))
          + Δ * (cS * Kd ^ (2 * n) * (N : ℝ) ^ n * TailDbd d N m ε₁ τ' D' Φ CK
            + cE * (d.L N : ℝ) ^ n * (N : ℝ) ^ n
              * δDbd d N m τ' D' (CK + 1) Mbig (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8))
                N) := by
      rw [div_eq_mul_inv]; ring
    rw [e] at key
    exact key
  have htot := Finset.sum_le_sum hstep
  rw [Finset.mul_sum]
  refine htot.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hE0 : 0 ≤ cS * Kd ^ (2 * n) * (N : ℝ) ^ n * TailDbd d N m ε₁ τ' D' Φ CK
      + cE * (d.L N : ℝ) ^ n * (N : ℝ) ^ n
        * δDbd d N m τ' D' (CK + 1) Mbig (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N := by
    positivity
  have := mul_le_mul_of_nonneg_right hsumΔ hE0
  linarith

end TailQ2

section QVTail

variable (d : Dims)

open Real

theorem qqErrBd_mono (L k : ℕ) {K e e' δ : ℝ} (hK : 0 ≤ K) (he0 : 0 ≤ e) (he : e ≤ e')
    (hδ : 0 ≤ δ) : FastDecayFlow.qqErrBd L k K e δ ≤ FastDecayFlow.qqErrBd L k K e' δ := by
  have := cTwo52_pos
  unfold FastDecayFlow.qqErrBd FastDecayFlow.qBlockErrBd FastDecayFlow.qBlockSizeBd
  gcongr

/-- The `u`-free bound of `eeHermBd` on the window (`A_u ≥ 1`, `ℓ_u ≤ L`). -/
def eeBd (d : Dims) (N n : ℕ) (Φ w D : ℝ) : ℝ :=
  n * (2 * exp 1 * n * Φ * ((d.W N : ℝ) * ((d.L N : ℝ) * w + 1))
    + n * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D))

theorem eeHermBd_le (N n : ℕ) {Φ A ℓ w D : ℝ} (hΦ : 0 ≤ Φ) (hA : 1 ≤ A) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ d.L N) (hw : 0 ≤ w) :
    eeHermBd d N n Φ A (ℓ * w) D ≤ eeBd d N n Φ w D := by
  unfold eeHermBd eeBd
  have hA0 : 0 < A := by linarith
  have hW0 : (0 : ℝ) ≤ d.W N := Nat.cast_nonneg _
  have h1 : (d.W N : ℝ) * (ℓ * w + 1) / A ≤ (d.W N : ℝ) * ((d.L N : ℝ) * w + 1) := by
    rw [div_le_iff₀ hA0]
    have : ℓ * w + 1 ≤ (d.L N : ℝ) * w + 1 := by nlinarith
    have h2 : (d.W N : ℝ) * (ℓ * w + 1) ≤ (d.W N : ℝ) * ((d.L N : ℝ) * w + 1) :=
      mul_le_mul_of_nonneg_left this hW0
    have h3 : 0 ≤ (d.W N : ℝ) * ((d.L N : ℝ) * w + 1) := by positivity
    nlinarith
  have h2 : A⁻¹ ^ (2 * n) ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hA)
  have h3 : 0 ≤ (d.W N : ℝ) * (ℓ * w + 1) / A := by positivity
  have h4 : (d.W N : ℝ) * (ℓ * w + 1) / A * A⁻¹ ^ (2 * n) ≤ (d.W N : ℝ) * ((d.L N : ℝ) * w + 1) :=
    by nlinarith [pow_nonneg (inv_nonneg.2 hA0.le) (2 * n)]
  have h5 : 0 ≤ 2 * exp 1 * (n : ℝ) * Φ := by positivity
  have h6 := mul_le_mul_of_nonneg_left h4 h5
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **(5.93) for the martingale part, sharp (5.105), Case 2**: the joint `Q ⊗ Q` QV sum at the
target `u_K = v` is at most `C·Φq·A_v^{-2n}·(Σ_j Δ/η_{u_j} + Δ/η_v)` plus a `u`-free tail. -/
theorem tb_qvQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hA : ∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale E N u)
    (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) {τ' D'' Φq : ℝ} (hτ' : 0 ≤ τ') (hΦq : 0 ≤ Φq)
    (a : LoopArg (d.L N) (m + 2)) :
    ∑ j ∈ Finset.range (K N), (cQVQ d E s v K N m τ' D'' Φq (K N) a j : ℝ)
      ≤ cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (2 * ((m + 1 + 1)
            + (m + 1 + 1))) * qqCoefE (d.L N) (m + 1) ((d.W N : ℝ) ^ τ')
          * (6 * Real.exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * Φq)
          * ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 1 + 1))
          * (∑ j ∈ Finset.range (K N), step s v K N / etaT E (time s v K N j)
              + step s v K N / etaT E (v N))
        + (cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (2 * ((m + 1 + 1)
              + (m + 1 + 1)))
            * (qqCoefE (d.L N) (m + 1) ((d.W N : ℝ) ^ τ') * ((N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
                * eeHermErr d N (m + 1 + 1) D'')
              + (N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
                * (qqCoefD (d.L N) (m + 1) ((d.W N : ℝ) ^ τ') * eeHermErr d N (m + 1 + 1) D''))
          + cKerSumZeroErr ((m + 1 + 1) + (m + 1 + 1)) * (d.L N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
            * (N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
            * FastDecayFlow.qqErrBd (d.L N) (m + 1) ((d.W N : ℝ) ^ τ')
                (eeBd d N (m + 1 + 1) Φq ((d.W N : ℝ) ^ τ') D'') (eeHermErr d N (m + 1 + 1) D'')) := by
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  set n2 := (m + 1 + 1) + (m + 1 + 1) with hn2
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hmem : ∀ i, i ≤ K N → u i ∈ Set.Icc (s N) (v N) :=
    fun i hi => mem_Icc_time s v K N i hs0 hsv.le hi
  have hu0 : ∀ i ≤ K N, 0 ≤ u i := fun i hi => hs0.trans (hmem i hi).1
  have hu1 : ∀ i ≤ K N, u i < 1 := fun i hi => (hmem i hi).2.trans_lt hv1
  have huK : u (K N) = v N := time_last s v K N hK0
  have hKΔ : (K N : ℝ) * Δ = v N - s N := by
    have hKpos : (0 : ℝ) < K N := by exact_mod_cast (by omega : 0 < K N)
    rw [hΔ]; unfold step; field_simp
  set w := (d.W N : ℝ) ^ τ' with hw
  have hw0 : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  set cS2 := cKerSumZero n2 with hcS2
  have hcS20 : 0 ≤ cS2 := cKerSumZero_nonneg _
  set cE2 := cKerSumZeroErr n2 with hcE2
  have hcE20 : 0 ≤ cE2 := by rw [hcE2]; unfold cKerSumZeroErr; have := cTwo52_pos; positivity
  set qE := qqCoefE (d.L N) (m + 1) w with hqE
  have hqE0 : 0 ≤ qE := qqCoefE_nonneg _ _ hw0
  set qD := qqCoefD (d.L N) (m + 1) w with hqD
  have hqD0 : 0 ≤ qD := qqCoefD_nonneg _ _ hw0
  set ee := eeHermErr d N (m + 1 + 1) D'' with hee
  have hee0 : 0 ≤ ee := eeHermErr_nonneg d N _ D''
  set eb := eeBd d N (m + 1 + 1) Φq w D'' with heb
  have heb0 : 0 ≤ eb := by
    rw [heb]; unfold eeBd
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D'') := Real.rpow_nonneg (by positivity) _
    positivity
  set Cm := cS2 * (4 * w) ^ (2 * n2) * qE * (6 * Real.exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * w * Φq)
    with hCm
  have hCm0 : 0 ≤ Cm := by positivity
  set Tl := cS2 * (4 * w) ^ (2 * n2) * (qE * ((N : ℝ) ^ n2 * ee) + (N : ℝ) ^ n2 * (qD * ee))
    + cE2 * (d.L N : ℝ) ^ n2 * (N : ℝ) ^ n2 * FastDecayFlow.qqErrBd (d.L N) (m + 1) w eb ee
    with hTl
  have hqq0 : 0 ≤ FastDecayFlow.qqErrBd (d.L N) (m + 1) w eb ee :=
    FastDecayFlow.qqErrBd_nonneg _ _ hw0 heb0 hee0
  have hTl0 : 0 ≤ Tl := by rw [hTl]; positivity
  have hAv : 1 ≤ (band d).scale E N (v N) := hA (v N) (hs0.trans hsv.le) le_rfl
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hstep : ∀ j ∈ Finset.range (K N), (cQVQ d E s v K N m τ' D'' Φq (K N) a j : ℝ)
      ≤ Cm * ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 1 + 1)) * (Δ / etaT E (u (j + 1)))
        + Δ * Tl := by
    intro j hj
    have hjK : j < K N := Finset.mem_range.mp hj
    have hj10 := hu0 (j + 1) (by omega)
    have hj11 := hu1 (j + 1) (by omega)
    have hj1K : u (j + 1) ≤ u (K N) := by
      rw [hu]; unfold time
      have : ((j + 1 : ℕ) : ℝ) ≤ (K N : ℝ) := by exact_mod_cast hjK
      have : 0 ≤ step s v K N := hΔ0
      nlinarith
    have hpos := qvBdSumZero_pos d hE (N := N) (k := m + 1) (τ := τ') (D := D'') hj10 hj1K
      (hu1 (K N) le_rfl) hΦq
    unfold cQVQ
    rw [Real.coe_toNNReal _ (mul_nonneg hΔ0 hpos.le)]
    unfold qvBdSumZero
    rw [huK]
    have hR := ratio514_pow_le d hE N n2 u (j + 1) (K N) hj10 hj11 (hu0 (K N) le_rfl)
      (hu1 (K N) le_rfl) (by rw [huK]; exact hAv)
    rw [huK] at hR
    have hA1N : (band d).scale E N (u (j + 1)) ≤ N :=
      (scale_le_LW d hE N hj10 hj11).trans hLW
    have hA11 : 1 ≤ (band d).scale E N (u (j + 1)) := hA (u (j + 1)) hj10 (hmem (j + 1) (by omega)).2
    have hA10 : 0 < (band d).scale E N (u (j + 1)) := lt_of_lt_of_le one_pos hA11
    have hR' := hR.trans (pow_le_pow_left₀ hA10.le hA1N _)
    have hr := eps514_le (n := n2) u hj10 hj11 (hu1 (K N) le_rfl)
      (by simpa only [huK] using (inv_eta_le_of hE hv1 hη le_rfl).2)
    unfold eps514 at hr
    rw [huK] at hr
    have hℓ1 : 1 ≤ ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) :=
      one_le_ellHat (d.L N) (d.three_le_L N) hj10 hj11
    have hℓL : ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) ≤ d.L N := ellHat_real_le_L hj11
    have he := eeHermBd_le d N (m + 1 + 1) (Φ := Φq) (D := D'') hΦq hA11 (by linarith) hℓL hw0
    have he0 : 0 ≤ eeHermBd d N (m + 1 + 1) Φq ((band d).scale E N (u (j + 1)))
        (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) * w) D'' :=
      eeHermBd_nonneg d N _ hΦq hA10 (by positivity)
    have hqq := (FastDecayFlow.qqErr_le (d.L N) (m + 1) hℓ1 hℓL hw0 he0 hee0).trans
      (qqErrBd_mono (d.L N) (m + 1) hw0 he0 he hee0)
    have hR0 : 0 ≤ ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
        / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 := by
      have h1 : 0 < 1 - u (j + 1) := by linarith
      have h2 : 0 < 1 - v N := by linarith
      have h3 : 0 < ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) := by linarith
      have h4 : 0 < ellHat (d.L N) ((v N : ℝ) : ℂ) :=
        Step3.ellHat_pos_of_lt_one (by have := d.three_le_L N; omega) hv1
      positivity
    have hr0 : 0 ≤ ((1 - u (j + 1)) / (1 - v N)) ^ n2 := by
      have h1 : 0 < 1 - u (j + 1) := by linarith
      have h2 : 0 < 1 - v N := by linarith
      positivity
    have hqqe0 : 0 ≤ FastDecayFlow.qqErr (d.L N) (m + 1) (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)) w
        (eeHermBd d N (m + 1 + 1) Φq ((band d).scale E N (u (j + 1)))
          (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) * w) D'') ee := by
      unfold FastDecayFlow.qqErr FastDecayFlow.qBlockErr FastDecayFlow.qBlockSize
      have := cTwo52_pos; have := cZero_pos
      positivity
    have t1 : cS2 * (4 * w) ^ (2 * n2) * (qE * (((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
          / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 * ee)
        + ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
          / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 * (qD * ee))
        ≤ cS2 * (4 * w) ^ (2 * n2) * (qE * ((N : ℝ) ^ n2 * ee) + (N : ℝ) ^ n2 * (qD * ee)) := by
      gcongr
    have t2 : cE2 * (d.L N : ℝ) ^ n2 * ((1 - u (j + 1)) / (1 - v N)) ^ n2
        * FastDecayFlow.qqErr (d.L N) (m + 1) (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)) w
          (eeHermBd d N (m + 1 + 1) Φq ((band d).scale E N (u (j + 1)))
            (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) * w) D'') ee
        ≤ cE2 * (d.L N : ℝ) ^ n2 * (N : ℝ) ^ n2 * FastDecayFlow.qqErrBd (d.L N) (m + 1) w eb ee := by
      gcongr
    have e : Δ * (cS2 * (4 * w) ^ (2 * n2) * (qE * (6 * Real.exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * w
            * Φq * (etaT E (u (j + 1)))⁻¹ * ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 1 + 1))
          + ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
            / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 * ee)
          + ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
            / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 * (qD * ee))
        + cE2 * (d.L N : ℝ) ^ n2 * ((1 - u (j + 1)) / (1 - v N)) ^ n2
          * FastDecayFlow.qqErr (d.L N) (m + 1) (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)) w
            (eeHermBd d N (m + 1 + 1) Φq ((band d).scale E N (u (j + 1)))
              (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) * w) D'') ee)
        = Cm * ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 1 + 1)) * (Δ / etaT E (u (j + 1)))
          + Δ * (cS2 * (4 * w) ^ (2 * n2) * (qE * (((1 - u (j + 1))
              * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
              / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 * ee)
            + ((1 - u (j + 1)) * ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)
              / ((1 - v N) * ellHat (d.L N) ((v N : ℝ) : ℂ))) ^ n2 * (qD * ee))
            + cE2 * (d.L N : ℝ) ^ n2 * ((1 - u (j + 1)) / (1 - v N)) ^ n2
              * FastDecayFlow.qqErr (d.L N) (m + 1) (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ)) w
                (eeHermBd d N (m + 1 + 1) Φq ((band d).scale E N (u (j + 1)))
                  (ellHat (d.L N) ((u (j + 1) : ℝ) : ℂ) * w) D'') ee) := by
      rw [hCm, div_eq_mul_inv]; ring
    rw [e]
    have t3 := mul_le_mul_of_nonneg_left (add_le_add t1 t2) hΔ0
    rw [hTl]
    linarith
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have hsucc := sum_succ_le (K := K N) (fun j => Δ / etaT E (u j))
    (div_nonneg hΔ0 (etaT_pos hE (hu1 0 (Nat.zero_le _))).le)
  simp only [huK] at hsucc
  have hsumΔ : ∑ _j ∈ Finset.range (K N), Δ ≤ 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hKΔ]; linarith
  have hA0 : 0 ≤ Cm * ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 1 + 1)) := by
    have := (band d).scale_pos' hE N (hs0.trans hsv.le) hv1
    positivity
  have t1 := mul_le_mul_of_nonneg_left hsucc hA0
  have t2 := mul_le_mul_of_nonneg_right hsumΔ hTl0
  rw [hCm] at t1 hA0
  rw [hTl] at t2
  linarith

end QVTail


section EvTail

variable (d : Dims)

open Real

/-- **A `W^{-D}` tail is eventually below `N^{-q}/R`** once `D ≥ 2(P+q+1)` (`W ≥ N^{1/2}`). -/
theorem ev_tailW (C : ℝ) (P q : ℕ) {D : ℝ} (hD : 2 * ((P : ℝ) + q + 1) ≤ D) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ P * (d.W N : ℝ) ^ (-D) ≤ ((N : ℝ) ^ q)⁻¹ / R := by
  have hD0 : 0 ≤ D := by
    have : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  filter_upwards [ev_dims514 d, ev_rpow_le (a := (P : ℝ) - D / 2) (b := -(q : ℝ))
    (by linarith) (R * max C 0)] with N hd hA
  obtain ⟨hN1, -, -, -, -, -, hsq⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hWD := rpow_neg_le_of_sqrt_le hN0 hsq hD0
  have hWD0 : 0 ≤ (d.W N : ℝ) ^ (-D) := Real.rpow_nonneg (by positivity) _
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have h1 : C * (N : ℝ) ^ P * (d.W N : ℝ) ^ (-D) ≤ max C 0 * (N : ℝ) ^ P * (N : ℝ) ^ (-(D / 2)) := by
    have : C * (N : ℝ) ^ P ≤ max C 0 * (N : ℝ) ^ P :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    calc C * (N : ℝ) ^ P * (d.W N : ℝ) ^ (-D) ≤ max C 0 * (N : ℝ) ^ P * (d.W N : ℝ) ^ (-D) :=
          mul_le_mul_of_nonneg_right this hWD0
      _ ≤ _ := mul_le_mul_of_nonneg_left hWD (by positivity)
  have e : max C 0 * (N : ℝ) ^ P * (N : ℝ) ^ (-(D / 2)) = max C 0 * (N : ℝ) ^ ((P : ℝ) - D / 2) := by
    rw [natpow_eq_rpow, mul_assoc, ← Real.rpow_add hN0]; ring_nf
  have e2 : ((N : ℝ) ^ q)⁻¹ = (N : ℝ) ^ (-(q : ℝ)) := by
    rw [natpow_eq_rpow, Real.rpow_neg hN0.le]
  rw [e] at h1
  rw [e2, le_div_iff₀ hR]
  have : max C 0 * (N : ℝ) ^ ((P : ℝ) - D / 2) * R = R * max C 0 * (N : ℝ) ^ ((P : ℝ) - D / 2) := by
    ring
  nlinarith

/-- **An `exp(-c W^{τ'})` tail is eventually below `N^{-q}/R`**. -/
theorem ev_tailExp (C : ℝ) (P q : ℕ) {c τ' : ℝ} (hc : 0 < c) (hτ' : 0 < τ') {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ P * exp (-(c * (d.W N : ℝ) ^ τ')) ≤ ((N : ℝ) ^ q)⁻¹ / R := by
  filter_upwards [ev_dims514 d, SumZeroDyn.eventually_exp_small (R * max C 0) ((P + q : ℕ) : ℝ) c
    (τ₁ := τ' / 2) hc (by positivity)] with N hd hE
  obtain ⟨hN1, -, -, -, -, -, hsq⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hM : 0 ≤ max C 0 := le_max_right _ _
  have hWτ : (N : ℝ) ^ (τ' / 2) ≤ (d.W N : ℝ) ^ τ' := by
    have h1 : ((N : ℝ) ^ ((1 : ℝ) / 2)) ^ τ' ≤ (d.W N : ℝ) ^ τ' :=
      Real.rpow_le_rpow (by positivity) hsq hτ'.le
    rw [← Real.rpow_mul hN0.le] at h1
    convert h1 using 2; ring
  have hex : exp (-(c * (d.W N : ℝ) ^ τ')) ≤ exp (-(c * (N : ℝ) ^ (τ' / 2))) := by
    apply exp_le_exp.2; nlinarith
  have hex0 : 0 ≤ exp (-(c * (N : ℝ) ^ (τ' / 2))) := (exp_pos _).le
  have h1 : C * (N : ℝ) ^ P * exp (-(c * (d.W N : ℝ) ^ τ'))
      ≤ max C 0 * (N : ℝ) ^ P * exp (-(c * (N : ℝ) ^ (τ' / 2))) := by
    have : C * (N : ℝ) ^ P ≤ max C 0 * (N : ℝ) ^ P :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    calc C * (N : ℝ) ^ P * exp (-(c * (d.W N : ℝ) ^ τ'))
        ≤ max C 0 * (N : ℝ) ^ P * exp (-(c * (d.W N : ℝ) ^ τ')) :=
          mul_le_mul_of_nonneg_right this (exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hex (by positivity)
  have e : (N : ℝ) ^ ((P + q : ℕ) : ℝ) = (N : ℝ) ^ P * (N : ℝ) ^ q := by
    rw [Real.rpow_natCast, pow_add]
  rw [e] at hE
  refine h1.trans ?_
  rw [le_div_iff₀ hR]
  have hq : 0 < (N : ℝ) ^ q := by positivity
  rw [← mul_le_mul_iff_of_pos_right hq]
  have e2 : ((N : ℝ) ^ q)⁻¹ * (N : ℝ) ^ q = 1 := inv_mul_cancel₀ hq.ne'
  rw [e2]
  nlinarith

end EvTail

section TailPoint

variable (d : Dims)

open Real

/-- The polynomial degree used for every tail. -/
def PT (m : ℕ) : ℕ := 20 * m + 60

theorem tail1_le (N m : ℕ) {τ' D' : ℝ} (hN1 : (1 : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hwN : (d.W N : ℝ) ^ τ' ≤ N) (hw0 : 0 ≤ (d.W N : ℝ) ^ τ') :
    cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
      * ((2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
      ≤ (cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * (2 * cTwo52) ^ (m + 1))
        * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D') := by
  have hc := cTwo52_pos
  have hcS := cKerSumZero_nonneg (m + 2)
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  calc cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
        * ((2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
      ≤ cKerSumZero (m + 2) * (4 * (4 * (N : ℝ))) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
        * ((2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')) := by gcongr
    _ = (cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * (2 * cTwo52) ^ (m + 1))
        * (N : ℝ) ^ (4 * m + 7) * (d.W N : ℝ) ^ (-D') := by ring
    _ ≤ _ := by gcongr; unfold PT; omega

theorem tail7_le (N m : ℕ) {D' : ℝ} (hN1 : (1 : ℝ) ≤ N) :
    cTwo52 ^ (m + 1) * ((N : ℝ) * (N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
      ≤ cTwo52 ^ (m + 1) * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D') := by
  have hc := cTwo52_pos
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  calc cTwo52 ^ (m + 1) * ((N : ℝ) * (N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
      = cTwo52 ^ (m + 1) * (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by ring
    _ ≤ _ := by gcongr; unfold PT; omega

theorem tail2_le (N m : ℕ) {τ' D' CK : ℝ} (hN1 : (1 : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hwN : (d.W N : ℝ) ^ τ' ≤ N) (hw1 : 1 ≤ (d.W N : ℝ) ^ τ') (hCK : 0 ≤ CK)
    (hCKN : CK + 1 ≤ N) :
    cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
      * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
          ((d.W N : ℝ) ^ (-D'))
      ≤ (cKerSumZeroErr (m + 2) * (1 + (2 * cTwo52) ^ (m + 1))) * (N : ℝ) ^ PT m
          * (d.W N : ℝ) ^ (-D')
        + (3 * cKerSumZeroErr (m + 2) * (24 * exp 1 * cTwo52) ^ (m + 1)) * (N : ℝ) ^ PT m
          * exp (-(cZero * (d.W N : ℝ) ^ τ')) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have hcE : 0 ≤ cKerSumZeroErr (m + 2) := by unfold cKerSumZeroErr; positivity
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set w := (d.W N : ℝ) ^ τ' with hw
  have hex : exp (-(cZero * (4 * w) / 2)) ≤ exp (-(cZero * w)) := by
    apply exp_le_exp.2; nlinarith
  have hex1 : exp (-(cZero * w)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hex0 : 0 ≤ exp (-(cZero * (4 * w) / 2)) := (exp_pos _).le
  have hMb : (N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1 ≤ 3 * (N : ℝ) ^ (m + 2) := by
    have : (N : ℝ) ≤ (N : ℝ) ^ (m + 2) := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
    linarith
  unfold deltaQop
  have h1 : (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) ≤ (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have e : 6 * exp 1 * cTwo52 * (4 * w) = 24 * exp 1 * cTwo52 * w := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hwN (by positivity)
  have hA : (d.W N : ℝ) ^ (-D') + ((6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1)
        * ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
        * exp (-(cZero * (4 * w) / 2))
      ≤ (1 + (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1)) * (d.W N : ℝ) ^ (-D')
        + (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (3 * (N : ℝ) ^ (m + 2))
          * exp (-(cZero * w)) := by
    have t1 : (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
        * exp (-(cZero * (4 * w) / 2))
        ≤ (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (3 * (N : ℝ) ^ (m + 2))
          * exp (-(cZero * w)) := by
      have : 0 ≤ (N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1 := by positivity
      gcongr
    have t2 : (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')
        * exp (-(cZero * (4 * w) / 2))
        ≤ (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by
      have : exp (-(cZero * (4 * w) / 2)) ≤ 1 := hex.trans hex1
      calc (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')
            * exp (-(cZero * (4 * w) / 2))
          ≤ (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') * 1 := by gcongr
        _ = _ := mul_one _
    nlinarith
  have hA0 : 0 ≤ (d.W N : ℝ) ^ (-D') + ((6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1)
        * ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
        * exp (-(cZero * (4 * w) / 2)) := by positivity
  calc cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
        * ((d.W N : ℝ) ^ (-D') + ((6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1)
          * ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
          + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
          * exp (-(cZero * (4 * w) / 2)))
      ≤ cKerSumZeroErr (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
        * ((1 + (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1)) * (d.W N : ℝ) ^ (-D')
          + (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (3 * (N : ℝ) ^ (m + 2))
            * exp (-(cZero * w))) := by gcongr
    _ ≤ cKerSumZeroErr (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
        * ((1 + (2 * cTwo52) ^ (m + 1)) * (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')
          + (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) * (3 * (N : ℝ) ^ (m + 2))
            * exp (-(cZero * w))) := by
        have : (1 + (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1))
            ≤ (1 + (2 * cTwo52) ^ (m + 1)) * (N : ℝ) ^ (m + 1) := by
          have := one_le_pow₀ (n := m + 1) hN1; nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 2 * cTwo52) (m+1)]
        gcongr
    _ = (cKerSumZeroErr (m + 2) * (1 + (2 * cTwo52) ^ (m + 1))) * (N : ℝ) ^ (3 * m + 5)
          * (d.W N : ℝ) ^ (-D')
        + (3 * cKerSumZeroErr (m + 2) * (24 * exp 1 * cTwo52) ^ (m + 1)) * (N : ℝ) ^ (4 * m + 7)
          * exp (-(cZero * w)) := by ring
    _ ≤ _ := by
        gcongr
        · unfold PT; omega
        · unfold PT; omega

end TailPoint

section TailPoint3

variable (d : Dims)

open Real

theorem Ec514_le_crude (N n : ℕ) {ε₁ D' Φ B : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hε₁ : (N : ℝ) ^ ε₁ ≤ N) (hΦ : 0 ≤ Φ) (hB0 : 0 ≤ B)
    (hB : B ≤ 3 * (N : ℝ) ^ (2 * n)) :
    Ec514 d N n ε₁ D' Φ B
      ≤ (1 + Φ) * (((n : ℝ) + 2 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2) * (N : ℝ) ^ (2 * n + 2)
          * (d.W N : ℝ) ^ (-D')) := by
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNe0 : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0 _
  have hcard : ((Finset.Icc 3 n).card : ℝ) ≤ n := by
    have : (Finset.Icc 3 n).card ≤ n := by simp only [Nat.card_Icc]; omega
    exact_mod_cast this
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by linarith [mul_comm (d.W N : ℝ) (d.L N : ℝ)]
  have hWL0 : (0 : ℝ) ≤ (d.W N : ℝ) * (d.L N : ℝ) := by positivity
  have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * n + 2) := pow_le_pow_right₀ hN1 (by omega)
  have hN21 : (N : ℝ) * (N : ℝ) ^ (2 * n) ≤ (N : ℝ) ^ (2 * n + 2) := by
    rw [← pow_succ']; exact pow_le_pow_right₀ hN1 (by omega)
  unfold Ec514
  have t1 : (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁
      ≤ (n : ℝ) * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D') := by
    have : (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul hWL hε₁ hNe0 hN0
    calc (n : ℝ) * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * (N : ℝ) ^ ε₁
        = (n : ℝ) * ((d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁) * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ (n : ℝ) * (N : ℝ) ^ 2 * (d.W N : ℝ) ^ (-D') := by gcongr
      _ ≤ _ := by gcongr
  have t2 : ((Finset.Icc 3 n).card : ℝ) * (2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ)
        * (d.W N : ℝ) ^ (-D') * ((N : ℝ) ^ ε₁ * Φ))
      ≤ Φ * (2 * (n : ℝ) ^ 3 * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D')) := by
    have : (d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul hWL hε₁ hNe0 hN0
    calc ((Finset.Icc 3 n).card : ℝ) * (2 * (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ)
          * (d.W N : ℝ) ^ (-D') * ((N : ℝ) ^ ε₁ * Φ))
        = Φ * (2 * ((Finset.Icc 3 n).card : ℝ) * (n : ℝ) ^ 2
          * ((d.W N : ℝ) * (d.L N : ℝ) * (N : ℝ) ^ ε₁) * (d.W N : ℝ) ^ (-D')) := by ring
      _ ≤ Φ * (2 * (n : ℝ) * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D')) := by
          gcongr; exact this.trans hN2
      _ = _ := by ring
  have t3 : (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * B
      ≤ 3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D') := by
    calc (n : ℝ) ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * B
        = (n : ℝ) ^ 2 * ((d.W N : ℝ) * (d.L N : ℝ) * B) * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ (n : ℝ) ^ 2 * ((N : ℝ) * (3 * (N : ℝ) ^ (2 * n))) * (d.W N : ℝ) ^ (-D') := by
          gcongr
      _ = 3 * (n : ℝ) ^ 2 * ((N : ℝ) * (N : ℝ) ^ (2 * n)) * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ _ := by gcongr
  set Z := (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D') with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have e1 : (n : ℝ) * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D') = (n : ℝ) * Z := by ring
  have e2 : Φ * (2 * (n : ℝ) ^ 3 * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D'))
      = Φ * (2 * (n : ℝ) ^ 3 * Z) := by ring
  have e3 : 3 * (n : ℝ) ^ 2 * (N : ℝ) ^ (2 * n + 2) * (d.W N : ℝ) ^ (-D') = 3 * (n : ℝ) ^ 2 * Z := by
    ring
  have eG : (1 + Φ) * (((n : ℝ) + 2 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2) * (N : ℝ) ^ (2 * n + 2)
      * (d.W N : ℝ) ^ (-D'))
      = ((n : ℝ) + 2 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2) * Z
        + Φ * (((n : ℝ) + 2 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2) * Z) := by ring
  rw [e1] at t1; rw [e2] at t2; rw [e3] at t3; rw [eG]
  have h1 : 0 ≤ 2 * (n : ℝ) ^ 3 * Z := by positivity
  have h2 : Φ * (2 * (n : ℝ) ^ 3 * Z) ≤ Φ * (((n : ℝ) + 2 * (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2) * Z) := by
    apply mul_le_mul_of_nonneg_left _ hΦ
    have : 0 ≤ ((n : ℝ) + 3 * (n : ℝ) ^ 2) * Z := by positivity
    nlinarith
  nlinarith

theorem driftErr514_le_crude (N m : ℕ) {MK MD D' : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hMK0 : 0 ≤ MK) (hMD0 : 0 ≤ MD)
    (hMK : MK ≤ (N : ℝ) ^ (m + 2)) (hMD : MD ≤ 3 * (N : ℝ) ^ (m + 2)) :
    driftErr514 d N m MK MD D' ≤ 20 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (m + 3) * (d.W N : ℝ) ^ (-D') := by
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by linarith [mul_comm (d.W N : ℝ) (d.L N : ℝ)]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set Q := (N : ℝ) ^ (m + 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hNQ : (N : ℝ) * Q = (N : ℝ) ^ (m + 3) := by rw [hQ, ← pow_succ']
  unfold driftErr514
  have t1 : (d.W N : ℝ) * ((m : ℝ) + 2) * ((d.L N : ℝ) * (MD * (d.W N : ℝ) ^ (-D')))
      ≤ ((m : ℝ) + 2) * (N : ℝ) * (3 * Q) * (d.W N : ℝ) ^ (-D') := by
    calc (d.W N : ℝ) * ((m : ℝ) + 2) * ((d.L N : ℝ) * (MD * (d.W N : ℝ) ^ (-D')))
        = ((m : ℝ) + 2) * ((d.W N : ℝ) * (d.L N : ℝ)) * MD * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ _ := by gcongr
  have t2 : (m : ℝ) * (2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D')
        * (MK + MD)) ≤ (m : ℝ) * (2 * ((m : ℝ) + 2) ^ 2 * (N : ℝ) * (4 * Q) * (d.W N : ℝ) ^ (-D')) := by
    have : MK + MD ≤ 4 * Q := by linarith
    calc (m : ℝ) * (2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D')
          * (MK + MD))
        = (m : ℝ) * (2 * ((m : ℝ) + 2) ^ 2 * ((d.W N : ℝ) * (d.L N : ℝ)) * (MK + MD)
          * (d.W N : ℝ) ^ (-D')) := by ring
      _ ≤ _ := by gcongr
  have t3 : 2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * MD
      ≤ 2 * ((m : ℝ) + 2) ^ 2 * (N : ℝ) * (3 * Q) * (d.W N : ℝ) ^ (-D') := by
    calc 2 * (d.W N : ℝ) * ((m : ℝ) + 2) ^ 2 * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D') * MD
        = 2 * ((m : ℝ) + 2) ^ 2 * ((d.W N : ℝ) * (d.L N : ℝ)) * MD * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ _ := by gcongr
  have hsum : ((m : ℝ) + 2) * (N : ℝ) * (3 * Q) * (d.W N : ℝ) ^ (-D')
      + (m : ℝ) * (2 * ((m : ℝ) + 2) ^ 2 * (N : ℝ) * (4 * Q) * (d.W N : ℝ) ^ (-D'))
      + 2 * ((m : ℝ) + 2) ^ 2 * (N : ℝ) * (3 * Q) * (d.W N : ℝ) ^ (-D')
      ≤ 20 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (m + 3) * (d.W N : ℝ) ^ (-D') := by
    rw [← hNQ]
    have hZ : 0 ≤ (N : ℝ) * Q * (d.W N : ℝ) ^ (-D') := by positivity
    have e : ((m : ℝ) + 2) * (N : ℝ) * (3 * Q) * (d.W N : ℝ) ^ (-D')
        + (m : ℝ) * (2 * ((m : ℝ) + 2) ^ 2 * (N : ℝ) * (4 * Q) * (d.W N : ℝ) ^ (-D'))
        + 2 * ((m : ℝ) + 2) ^ 2 * (N : ℝ) * (3 * Q) * (d.W N : ℝ) ^ (-D')
        = (3 * ((m : ℝ) + 2) + 8 * (m : ℝ) * ((m : ℝ) + 2) ^ 2 + 6 * ((m : ℝ) + 2) ^ 2)
          * ((N : ℝ) * Q * (d.W N : ℝ) ^ (-D')) := by ring
    rw [e]
    have hc : 3 * ((m : ℝ) + 2) + 8 * (m : ℝ) * ((m : ℝ) + 2) ^ 2 + 6 * ((m : ℝ) + 2) ^ 2
        ≤ 20 * ((m : ℝ) + 2) ^ 3 := by nlinarith
    calc (3 * ((m : ℝ) + 2) + 8 * (m : ℝ) * ((m : ℝ) + 2) ^ 2 + 6 * ((m : ℝ) + 2) ^ 2)
          * ((N : ℝ) * Q * (d.W N : ℝ) ^ (-D'))
        ≤ 20 * ((m : ℝ) + 2) ^ 3 * ((N : ℝ) * Q * (d.W N : ℝ) ^ (-D')) :=
          mul_le_mul_of_nonneg_right hc hZ
      _ = _ := by ring
  linarith

end TailPoint3

section TailPoint3b

variable (d : Dims)

open Real

def CTd (m : ℕ) : ℝ :=
  (1 + (24 * exp 1 * cTwo52) ^ (m + 1))
      * (((m + 2 : ℕ) : ℝ) + 2 * ((m + 2 : ℕ) : ℝ) ^ 3 + 3 * ((m + 2 : ℕ) : ℝ) ^ 2)
    + 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 + 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1)

theorem CTd_nonneg (m : ℕ) : 0 ≤ CTd m := by unfold CTd; have := cTwo52_pos; positivity

set_option maxHeartbeats 1600000 in
theorem TailDbd_le_crude (N m : ℕ) {ε₁ τ' D' Φ CK : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hL : (d.L N : ℝ) ≤ N) (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hwN : (d.W N : ℝ) ^ τ' ≤ N)
    (hw0 : 0 ≤ (d.W N : ℝ) ^ τ') (hε₁ : (N : ℝ) ^ ε₁ ≤ N) (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK)
    (hCKN : CK + 1 ≤ N) :
    TailDbd d N m ε₁ τ' D' Φ CK ≤ (1 + Φ) * (CTd m * (N : ℝ) ^ (3 * m + 7) * (d.W N : ℝ) ^ (-D')) := by
  have hc := cTwo52_pos
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNn : (N : ℝ) ≤ (N : ℝ) ^ (m + 2) := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  set Mb := (N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1 with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hMb3 : Mb ≤ 3 * (N : ℝ) ^ (m + 2) := by linarith
  have hB : Mb * (N : ℝ) ^ (m + 2) ≤ 3 * (N : ℝ) ^ (2 * (m + 2)) := by
    have := mul_le_mul_of_nonneg_right hMb3 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ (m + 2))
    calc Mb * (N : ℝ) ^ (m + 2) ≤ 3 * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2) := this
      _ = _ := by ring
  have hEc := Ec514_le_crude d N (m + 2) (ε₁ := ε₁) (D' := D') hN1 hLW hε₁ hΦ (by positivity) hB
  have hdE := driftErr514_le_crude d N m (MK := CK + 1) (MD := Mb) (D' := D') hN1 hLW (by linarith)
    hMb0 (by linarith) hMb3
  have hG : 1 + (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)
      ≤ (1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * (N : ℝ) ^ (m + 1) := by
    have h1 : (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)
        ≤ (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      have e : 6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ') = 24 * exp 1 * cTwo52 * (d.W N : ℝ) ^ τ' := by
        ring
      rw [e]; exact mul_le_mul_of_nonneg_left hwN (by positivity)
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (m + 1) := one_le_pow₀ hN1
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 24 * exp 1 * cTwo52) (m + 1)]
  set Z := (N : ℝ) ^ (3 * m + 7) * (d.W N : ℝ) ^ (-D') with hZ
  have hZ0 : 0 ≤ Z := by positivity
  set c1 := ((m + 2 : ℕ) : ℝ) + 2 * ((m + 2 : ℕ) : ℝ) ^ 3 + 3 * ((m + 2 : ℕ) : ℝ) ^ 2 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  unfold TailDbd
  rw [← hMb]
  -- term 1
  have T1 : (1 + (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
      * Ec514 d N (m + 2) ε₁ D' Φ (Mb * (N : ℝ) ^ (m + 2))
      ≤ (1 + Φ) * ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * c1 * Z) := by
    have hEc0 : 0 ≤ Ec514 d N (m + 2) ε₁ D' Φ (Mb * (N : ℝ) ^ (m + 2)) := by
      unfold Ec514
      have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0 _
      positivity
    calc (1 + (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1))
          * Ec514 d N (m + 2) ε₁ D' Φ (Mb * (N : ℝ) ^ (m + 2))
        ≤ ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * (N : ℝ) ^ (m + 1))
          * ((1 + Φ) * (c1 * (N : ℝ) ^ (2 * (m + 2) + 2) * (d.W N : ℝ) ^ (-D'))) :=
          mul_le_mul hG hEc hEc0 (by positivity)
      _ = (1 + Φ) * ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * c1
          * ((N : ℝ) ^ (m + 1) * (N : ℝ) ^ (2 * (m + 2) + 2)) * (d.W N : ℝ) ^ (-D')) := by ring
      _ = (1 + Φ) * ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * c1 * Z) := by
          rw [hZ, ← pow_add]; ring_nf
  -- term 2
  have T2 : (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
      ≤ (1 + Φ) * (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * Z) := by
    have hdE0 := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) hMb0
    calc (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
        ≤ (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1)
          * (20 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (m + 3) * (d.W N : ℝ) ^ (-D')) := by gcongr
      _ = 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3
          * ((N : ℝ) ^ (m + 1) * (N : ℝ) ^ (m + 3)) * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * Z := by
          have hp : (N : ℝ) ^ (m + 1) * (N : ℝ) ^ (m + 3) ≤ (N : ℝ) ^ (3 * m + 7) := by
            rw [← pow_add]; exact pow_le_pow_right₀ hN1 (by omega)
          rw [hZ]
          have h0 : 0 ≤ 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 := by positivity
          calc 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3
                * ((N : ℝ) ^ (m + 1) * (N : ℝ) ^ (m + 3)) * (d.W N : ℝ) ^ (-D')
              ≤ 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3
                * (N : ℝ) ^ (3 * m + 7) * (d.W N : ℝ) ^ (-D') := by gcongr
            _ = _ := by ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith)
  -- term 3
  have T3 : 4 * ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1)
      * ((N : ℝ) * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
      ≤ (1 + Φ) * (4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * Z) := by
    calc 4 * ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1)
          * ((N : ℝ) * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
        ≤ 4 * ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1)
          * ((N : ℝ) * (N : ℝ) ^ m * (d.W N : ℝ) ^ (-D')) := by gcongr
      _ = 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * ((N : ℝ) ^ (m + 2)) * (d.W N : ℝ) ^ (-D') := by
          ring
      _ ≤ 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * Z := by
          have hp : (N : ℝ) ^ (m + 2) ≤ (N : ℝ) ^ (3 * m + 7) := pow_le_pow_right₀ hN1 (by omega)
          rw [hZ]
          calc 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (N : ℝ) ^ (m + 2) * (d.W N : ℝ) ^ (-D')
              ≤ 4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (N : ℝ) ^ (3 * m + 7) * (d.W N : ℝ) ^ (-D') := by
                gcongr
            _ = _ := by ring
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by linarith)
  have e : (1 + Φ) * (CTd m * Z) = (1 + Φ) * ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * c1 * Z)
      + (1 + Φ) * (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * Z)
      + (1 + Φ) * (4 * ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * Z) := by
    unfold CTd; rw [hc1]; ring
  rw [show (1 + Φ) * (CTd m * (N : ℝ) ^ (3 * m + 7) * (d.W N : ℝ) ^ (-D')) = (1 + Φ) * (CTd m * Z)
    by rw [hZ]; ring, e]
  linarith

end TailPoint3b

section TailPoint3c

variable (d : Dims)

open Real

def coefC (m : ℕ) : ℝ :=
  ((m : ℝ) + 2) * cTwo52 ^ (m + 1) * (2 + cTwo52) + 3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * exp (cZero / 2)

def CδW (m : ℕ) : ℝ := 20 * ((m : ℝ) + 2) ^ 3 + 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 + coefC m

def CδE (m : ℕ) : ℝ :=
  10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 + 3 * coefC m * (10 * exp 1) ^ (m + 1)

theorem coefC_nonneg (m : ℕ) : 0 ≤ coefC m := by unfold coefC; have := cTwo52_pos; positivity
theorem CδW_nonneg (m : ℕ) : 0 ≤ CδW m := by
  unfold CδW; have := coefC_nonneg m; have := cTwo52_pos; positivity
theorem CδE_nonneg (m : ℕ) : 0 ≤ CδE m := by
  unfold CδE; have := coefC_nonneg m; have := cTwo52_pos; positivity

set_option maxHeartbeats 1600000 in
theorem δDbd_le_crude (N m : ℕ) {τ' D' CK : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hL : (d.L N : ℝ) ≤ N) (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hwN : (d.W N : ℝ) ^ τ' ≤ N)
    (hw1 : 1 ≤ (d.W N : ℝ) ^ τ') (hCK : 0 ≤ CK) (hCKN : CK + 1 ≤ N) :
    δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
        (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N
      ≤ CδW m * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D')
        + CδE m * (N : ℝ) ^ (3 * m + 9) * exp (-(cZero * (d.W N : ℝ) ^ τ')) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hNn : (N : ℝ) ≤ (N : ℝ) ^ (m + 2) := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by omega)
  set Mb := (N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1 with hMb
  have hMb0 : 0 ≤ Mb := by positivity
  have hMb3 : Mb ≤ 3 * (N : ℝ) ^ (m + 2) := by linarith
  have hdE := driftErr514_le_crude d N m (MK := CK + 1) (MD := Mb) (D' := D') hN1 hLW (by linarith)
    hMb0 (by linarith) hMb3
  have hdE0 := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1) hMb0
  set w := (d.W N : ℝ) ^ τ' with hw
  set Ex := exp (-(cZero * w)) with hEx
  have hEx0 : 0 ≤ Ex := (exp_pos _).le
  have hEx1 : Ex ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hE4 : exp (-(cZero * (4 * w) / 2)) ≤ Ex := by
    rw [hEx]; apply exp_le_exp.2; nlinarith
  have hE40 : 0 ≤ exp (-(cZero * (4 * w) / 2)) := (exp_pos _).le
  set DE := 10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8) with hDE
  have hDE0 : 0 ≤ DE := by positivity
  -- the pieces inside the bracket
  have hG1 : (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) ≤ (24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have e : 6 * exp 1 * cTwo52 * (4 * w) = 24 * exp 1 * cTwo52 * w := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hwN (by positivity)
  have hcoef : ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1) * (2 + (d.L N : ℝ) * cTwo52)
        + 3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * (N : ℝ) * exp (cZero / 2)
      ≤ coefC m * (N : ℝ) ^ 2 := by
    unfold coefC
    have h1 : (N : ℝ) * (2 + (d.L N : ℝ) * cTwo52) ≤ (N : ℝ) ^ 2 * (2 + cTwo52) := by
      have : (d.L N : ℝ) * cTwo52 ≤ (N : ℝ) * cTwo52 := mul_le_mul_of_nonneg_right hL hc.le
      nlinarith
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hA : 0 ≤ ((m : ℝ) + 2) * cTwo52 ^ (m + 1) := by positivity
    have hB : 0 ≤ 3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * exp (cZero / 2) := by positivity
    have := mul_le_mul_of_nonneg_left h1 hA
    have := mul_le_mul_of_nonneg_left h2 hB
    nlinarith
  have hPb : (2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1)) ^ (m + 1) * Mb
        + (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')
      ≤ 3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4) + (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by
    have hb : 2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1) ≤ 10 * exp 1 * (N : ℝ) ^ 2 := by
      have : (d.L N : ℝ) * (4 * w) + 1 ≤ 5 * (N : ℝ) ^ 2 := by nlinarith
      nlinarith [exp_pos 1]
    have h1 : (2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1)) ^ (m + 1) ≤ (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (2 * m + 2) := by
      calc (2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1)) ^ (m + 1) ≤ (10 * exp 1 * (N : ℝ) ^ 2) ^ (m + 1) :=
            pow_le_pow_left₀ (by positivity) hb _
        _ = (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (2 * m + 2) := by rw [mul_pow, ← pow_mul]; ring_nf
    have h2 : (2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1)) ^ (m + 1) * Mb
        ≤ 3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4) := by
      calc (2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1)) ^ (m + 1) * Mb
          ≤ ((10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (2 * m + 2)) * (3 * (N : ℝ) ^ (m + 2)) :=
            mul_le_mul h1 hMb3 hMb0 (by positivity)
        _ = 3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4) := by
            rw [show 3 * m + 4 = (2 * m + 2) + (m + 2) by ring, pow_add]; ring
    have h3 : (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') ≤ (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by
      gcongr
    linarith
  unfold δDbd
  rw [← hw]
  -- assemble
  set coef := ((m : ℝ) + 2) * (N : ℝ) * cTwo52 ^ (m + 1) * (2 + (d.L N : ℝ) * cTwo52)
        + 3 * ((m : ℝ) + 1) * cTwo52 ^ (m + 1) * (N : ℝ) * exp (cZero / 2) with hcoefdef
  have hcoef0 : 0 ≤ coef := by rw [hcoefdef]; positivity
  set Pb := (2 * exp 1 * ((d.L N : ℝ) * (4 * w) + 1)) ^ (m + 1) * Mb
        + (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') with hPbdef
  have hPb0 : 0 ≤ Pb := by rw [hPbdef]; positivity
  have B1 : (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * DE
      ≤ 10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9) := by
    calc (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * DE
        ≤ ((24 * exp 1 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1)) * DE :=
          mul_le_mul_of_nonneg_right hG1 hDE0
      _ = 10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9) := by
          rw [hDE, show 3 * m + 9 = (m + 1) + (2 * m + 8) by ring, pow_add]; ring
  have B2 : (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
      ≤ 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D') := by
    calc (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
        ≤ (2 * cTwo52) ^ (m + 1) * (N : ℝ) ^ (m + 1)
          * (20 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (m + 3) * (d.W N : ℝ) ^ (-D')) := by gcongr
      _ = _ := by rw [show 2 * m + 4 = (m + 1) + (m + 3) by ring, pow_add]; ring
  have B3 : coef * Pb ≤ coefC m * (N : ℝ) ^ 2
      * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4) + (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')) :=
    mul_le_mul hcoef hPb hPb0 (by have := coefC_nonneg m; positivity)
  have hbr0 : 0 ≤ (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * DE
      + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
      + coef * Pb := by positivity
  -- E * bracket
  have hEbr : exp (-(cZero * (4 * w) / 2)) * ((6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * DE
      + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
      + coef * Pb)
      ≤ Ex * (10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9)
          + coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4)))
        + (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D')
          + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))) := by
    have hX1 : 0 ≤ 10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9)
        + coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4)) := by
      have := coefC_nonneg m; positivity
    have hX2 : 0 ≤ 20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D')
        + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')) := by
      have := coefC_nonneg m; positivity
    have hsum : (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * DE
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
        + coef * Pb
        ≤ (10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9)
          + coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4)))
        + (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D')
          + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))) := by
      have e : coefC m * (N : ℝ) ^ 2
          * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4) + (N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
          = coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4))
            + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')) := by ring
      linarith
    calc exp (-(cZero * (4 * w) / 2)) * ((6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1) * DE
          + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * driftErr514 d N m (CK + 1) Mb D'
          + coef * Pb)
        ≤ exp (-(cZero * (4 * w) / 2)) * ((10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3
            * (N : ℝ) ^ (3 * m + 9) + coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1)
              * (N : ℝ) ^ (3 * m + 4)))
          + (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4)
            * (d.W N : ℝ) ^ (-D') + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1)
              * (d.W N : ℝ) ^ (-D')))) := mul_le_mul_of_nonneg_left hsum hE40
      _ ≤ Ex * (10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9)
            + coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4)))
          + 1 * (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4)
            * (d.W N : ℝ) ^ (-D') + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1)
              * (d.W N : ℝ) ^ (-D'))) := by
          rw [mul_add]
          exact add_le_add (mul_le_mul_of_nonneg_right hE4 hX1)
            (mul_le_mul_of_nonneg_right (hE4.trans hEx1) hX2)
      _ = _ := by rw [one_mul]
  -- final polynomial comparison
  have hp1 : (N : ℝ) ^ (m + 3) ≤ (N : ℝ) ^ (2 * m + 4) := pow_le_pow_right₀ hN1 (by omega)
  have hp2 : (N : ℝ) ^ 2 * (N : ℝ) ^ (m + 1) ≤ (N : ℝ) ^ (2 * m + 4) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hN1 (by omega)
  have hp3 : (N : ℝ) ^ 2 * (N : ℝ) ^ (3 * m + 4) ≤ (N : ℝ) ^ (3 * m + 9) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hN1 (by omega)
  have hW1 : driftErr514 d N m (CK + 1) Mb D'
      ≤ 20 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D') :=
    hdE.trans (by gcongr)
  have hC := coefC_nonneg m
  have hW2 : coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
      ≤ coefC m * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D') := by
    calc coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
        = coefC m * ((N : ℝ) ^ 2 * (N : ℝ) ^ (m + 1)) * (d.W N : ℝ) ^ (-D') := by ring
      _ ≤ _ := by gcongr
  have hE2 : coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4))
      ≤ 3 * coefC m * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 9) := by
    calc coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4))
        = 3 * coefC m * (10 * exp 1) ^ (m + 1) * ((N : ℝ) ^ 2 * (N : ℝ) ^ (3 * m + 4)) := by ring
      _ ≤ _ := by gcongr
  have hEE : Ex * (10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9)
          + coefC m * (N : ℝ) ^ 2 * (3 * (10 * exp 1) ^ (m + 1) * (N : ℝ) ^ (3 * m + 4)))
      ≤ CδE m * (N : ℝ) ^ (3 * m + 9) * Ex := by
    unfold CδE
    have := mul_le_mul_of_nonneg_left (add_le_add_left hE2
      (10 * (24 * exp 1 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (3 * m + 9))) hEx0
    nlinarith
  have hWW : driftErr514 d N m (CK + 1) Mb D'
      + (20 * (2 * cTwo52) ^ (m + 1) * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D')
        + coefC m * (N : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')))
      ≤ CδW m * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D') := by
    unfold CδW
    nlinarith
  linarith

end TailPoint3c

section TailPoint4

variable (d : Dims)

open Real

/-- **`qqErrBd` is linear in `(δ, e·exp(-c₀K))` with a polynomial coefficient.** -/
theorem qqErrBd_le (L k : ℕ) {K e δ : ℝ} (hK : 0 ≤ K) (he : 0 ≤ e) (hδ : 0 ≤ δ) :
    FastDecayFlow.qqErrBd L k K e δ
      ≤ 11 * (2 * exp 1 * (2 * ((L : ℝ) * K) + 1) * (1 + cTwo52) * (1 + (L : ℝ))) ^ (4 * k)
        * (δ + e * exp (-(cZero * K))) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  set B := 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) * (1 + cTwo52) * (1 + (L : ℝ)) with hB
  have he1 : (1 : ℝ) ≤ 2 * exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hLK : 0 ≤ (L : ℝ) * K := by positivity
  have hB1 : 1 ≤ B := by
    rw [hB]
    have h1 : 1 ≤ 2 * ((L : ℝ) * K) + 1 := by linarith
    have h2 : 1 ≤ 1 + cTwo52 := by linarith
    have h3 : 1 ≤ 1 + (L : ℝ) := by linarith
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le he1 h1) h2) h3
    simpa [mul_assoc] using this
  have hB0 : 0 ≤ B := by linarith
  -- basic comparisons
  have hbase_a : 2 * exp 1 * ((L : ℝ) * K + 1) ≤ B := by
    rw [hB]
    have h1 : 2 * exp 1 * ((L : ℝ) * K + 1) ≤ 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) := by
      nlinarith [exp_pos 1]
    have h2 : 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) ≤ 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) * (1 + cTwo52)
        * (1 + (L : ℝ)) := by
      have : 0 ≤ 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) := by positivity
      have h3 : 1 ≤ (1 + cTwo52) * (1 + (L : ℝ)) := by nlinarith
      nlinarith
    linarith
  have hbase_b : 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) ≤ B := by
    rw [hB]
    have : 0 ≤ 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) := by positivity
    have h3 : 1 ≤ (1 + cTwo52) * (1 + (L : ℝ)) := by nlinarith
    nlinarith
  have hbase_L : (L : ℝ) ≤ B := by
    rw [hB]
    have h1 : 1 ≤ 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) * (1 + cTwo52) := by
      have h1' : 1 ≤ 2 * ((L : ℝ) * K) + 1 := by linarith
      have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he1 h1')
        (by linarith : (1 : ℝ) ≤ 1 + cTwo52)
      simpa [mul_assoc] using this
    nlinarith
  have hbase_c : cTwo52 ≤ B := by
    rw [hB]
    have h1 : 1 ≤ 2 * exp 1 * (2 * ((L : ℝ) * K) + 1) := by
      have h1' : 1 ≤ 2 * ((L : ℝ) * K) + 1 := by linarith
      simpa using one_le_mul_of_one_le_of_one_le he1 h1'
    have : cTwo52 ≤ (1 + cTwo52) * (1 + (L : ℝ)) := by nlinarith
    nlinarith
  set a := (2 * exp 1 * ((L : ℝ) * K + 1)) ^ k with ha
  set b := (2 * exp 1 * (2 * ((L : ℝ) * K) + 1)) ^ k with hb
  set ℓ := (L : ℝ) ^ k with hℓ
  set γ := cTwo52 ^ k with hγ
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hγ0 : 0 ≤ γ := by positivity
  have haB : a ≤ B ^ k := pow_le_pow_left₀ (by positivity) hbase_a k
  have hbB : b ≤ B ^ k := pow_le_pow_left₀ (by positivity) hbase_b k
  have hℓB : ℓ ≤ B ^ k := pow_le_pow_left₀ hL0 hbase_L k
  have hγB : γ ≤ B ^ k := pow_le_pow_left₀ hc.le hbase_c k
  have hBk1 : 1 ≤ B ^ k := one_le_pow₀ hB1
  set B2 := B ^ (2 * k) with hB2
  have hB2e : B ^ k * B ^ k = B2 := by rw [hB2, ← pow_add]; ring_nf
  have hB21 : 1 ≤ B2 := one_le_pow₀ hB1
  have hB4e : B2 * B2 = B ^ (4 * k) := by rw [hB2, ← pow_add]; ring_nf
  set x := exp (-(cZero * K)) with hx
  have hx0 : 0 ≤ x := (exp_pos _).le
  have hx1 : x ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hx2 : exp (-(cZero * (2 * K))) ≤ x := by
    rw [hx]; apply exp_le_exp.2; nlinarith
  have hx20 : 0 ≤ exp (-(cZero * (2 * K))) := (exp_pos _).le
  -- the products
  have hag : a * γ ≤ B2 := by rw [← hB2e]; exact mul_le_mul haB hγB hγ0 (by positivity)
  have hℓg : ℓ * γ ≤ B2 := by rw [← hB2e]; exact mul_le_mul hℓB hγB hγ0 (by positivity)
  have hbg : b * γ ≤ B2 := by rw [← hB2e]; exact mul_le_mul hbB hγB hγ0 (by positivity)
  set Y1 := e + (a * e + ℓ * δ) * γ with hY1
  set Y2 := δ + (a * e + ℓ * δ) * γ * x + ℓ * δ * γ with hY2
  have hY10 : 0 ≤ Y1 := by rw [hY1]; positivity
  have hY20 : 0 ≤ Y2 := by rw [hY2]; positivity
  have hY1b : Y1 ≤ 2 * B2 * (e + δ) := by
    rw [hY1]
    have h1 : (a * e + ℓ * δ) * γ = (a * γ) * e + (ℓ * γ) * δ := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_right hag he
    have h3 := mul_le_mul_of_nonneg_right hℓg hδ
    have h4 : e ≤ B2 * e := le_mul_of_one_le_left he hB21
    have h5 : 0 ≤ B2 * δ := by positivity
    have e2 : 2 * B2 * (e + δ) = 2 * (B2 * e) + 2 * (B2 * δ) := by ring
    rw [e2]
    linarith
  have hY2b : Y2 ≤ 3 * B2 * δ + B2 * e * x := by
    rw [hY2]
    have h1 : (a * e + ℓ * δ) * γ * x = (a * γ) * e * x + (ℓ * γ) * δ * x := by ring
    rw [h1]
    have t1 : (a * γ) * e * x ≤ B2 * e * x := by
      have := mul_le_mul_of_nonneg_right hag he
      exact mul_le_mul_of_nonneg_right this hx0
    have t2 : (ℓ * γ) * δ * x ≤ B2 * δ := by
      have := mul_le_mul_of_nonneg_right hℓg hδ
      have h3 : (ℓ * γ) * δ * x ≤ (ℓ * γ) * δ * 1 :=
        mul_le_mul_of_nonneg_left hx1 (by positivity)
      linarith
    have t3 : ℓ * δ * γ ≤ B2 * δ := by
      have := mul_le_mul_of_nonneg_right hℓg hδ
      linarith [show ℓ * δ * γ = (ℓ * γ) * δ by ring]
    have t4 : δ ≤ B2 * δ := le_mul_of_one_le_left hδ hB21
    have e2 : 3 * B2 * δ = 3 * (B2 * δ) := by ring
    rw [e2]
    linarith
  have hqq : FastDecayFlow.qqErrBd L k K e δ
      = Y2 + (b * Y1 + ℓ * Y2) * γ * exp (-(cZero * (2 * K))) + ℓ * Y2 * γ := by
    unfold FastDecayFlow.qqErrBd FastDecayFlow.qBlockErrBd FastDecayFlow.qBlockSizeBd
    rw [hY1, hY2, ha, hb, hℓ, hγ, hx]
  rw [hqq]
  have t1 : (b * Y1 + ℓ * Y2) * γ * exp (-(cZero * (2 * K))) ≤ B2 * Y1 * x + B2 * Y2 := by
    have h1 : (b * Y1 + ℓ * Y2) * γ = (b * γ) * Y1 + (ℓ * γ) * Y2 := by ring
    rw [h1]
    have s1 : (b * γ) * Y1 ≤ B2 * Y1 := mul_le_mul_of_nonneg_right hbg hY10
    have s2 : (ℓ * γ) * Y2 ≤ B2 * Y2 := mul_le_mul_of_nonneg_right hℓg hY20
    have hE : ((b * γ) * Y1 + (ℓ * γ) * Y2) * exp (-(cZero * (2 * K)))
        ≤ (B2 * Y1 + B2 * Y2) * x := mul_le_mul (by linarith) hx2 hx20 (by positivity)
    have h6 : B2 * Y2 * x ≤ B2 * Y2 := by
      have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ B2 * Y2); linarith
    have e7 : (B2 * Y1 + B2 * Y2) * x = B2 * Y1 * x + B2 * Y2 * x := by ring
    linarith
  have t2 : ℓ * Y2 * γ ≤ B2 * Y2 := by
    have := mul_le_mul_of_nonneg_right hℓg hY20
    linarith [show ℓ * Y2 * γ = (ℓ * γ) * Y2 by ring]
  have t3 : Y2 + (B2 * Y1 * x + B2 * Y2) + B2 * Y2 ≤ 3 * B2 * Y2 + B2 * Y1 * x := by
    have : Y2 ≤ B2 * Y2 := le_mul_of_one_le_left hY20 hB21
    have e2 : 3 * B2 * Y2 = 3 * (B2 * Y2) := by ring
    rw [e2]; linarith
  have t4 : 3 * B2 * Y2 + B2 * Y1 * x ≤ 11 * (B2 * B2) * (δ + e * x) := by
    have u1 : 3 * B2 * Y2 ≤ 9 * (B2 * B2) * δ + 3 * (B2 * B2) * (e * x) := by
      have := mul_le_mul_of_nonneg_left hY2b (by positivity : (0 : ℝ) ≤ 3 * B2)
      calc 3 * B2 * Y2 ≤ 3 * B2 * (3 * B2 * δ + B2 * e * x) := this
        _ = _ := by ring
    have u2 : B2 * Y1 * x ≤ B2 * (2 * B2 * (e + δ)) * x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY1b (by positivity)) hx0
    have u3 : B2 * (2 * B2 * (e + δ)) * x = 2 * (B2 * B2) * (e * x) + 2 * (B2 * B2) * (δ * x) := by
      ring
    have u4 : δ * x ≤ δ := by
      have := mul_le_mul_of_nonneg_left hx1 hδ; linarith
    have hBB : 0 ≤ B2 * B2 := by positivity
    have u5 : 2 * (B2 * B2) * (δ * x) ≤ 2 * (B2 * B2) * δ := mul_le_mul_of_nonneg_left u4 (by positivity)
    have hq : 0 ≤ (B2 * B2) * (e * x) := by positivity
    have e3 : 11 * (B2 * B2) * (δ + e * x) = 11 * (B2 * B2) * δ + 11 * ((B2 * B2) * (e * x)) := by ring
    have e4 : 9 * (B2 * B2) * δ + 3 * (B2 * B2) * (e * x) = 9 * (B2 * B2) * δ + 3 * ((B2 * B2) * (e * x)) := by ring
    have e5 : 2 * (B2 * B2) * (e * x) = 2 * ((B2 * B2) * (e * x)) := by ring
    rw [e3]; rw [e4] at u1; rw [u3, e5] at u2
    linarith
  rw [← hB4e]
  linarith

end TailPoint4

section TailPoint4b

variable (d : Dims)

open Real

def CqE (k : ℕ) : ℝ :=
  (1 + (6 * exp 1 * cTwo52) ^ k) * (1 + (8 * exp 1 * cTwo52) ^ k)
    + (2 * cTwo52) ^ k * (6 * exp 1 * cTwo52) ^ k

def CqD (k : ℕ) : ℝ := (2 * cTwo52) ^ k * (2 + (8 * exp 1 * cTwo52) ^ k + 2 * (2 * cTwo52) ^ k)

theorem CqE_nonneg (k : ℕ) : 0 ≤ CqE k := by unfold CqE; have := cTwo52_pos; positivity
theorem CqD_nonneg (k : ℕ) : 0 ≤ CqD k := by unfold CqD; have := cTwo52_pos; positivity

theorem qqCoefE_le_crude {L k : ℕ} {w N : ℝ} (hN1 : 1 ≤ N) (hL : (L : ℝ) ≤ N) (hw0 : 0 ≤ w)
    (hwN : w ≤ N) : qqCoefE L k w ≤ CqE k * N ^ (2 * k) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have hNk : 1 ≤ N ^ k := one_le_pow₀ hN1
  have hN0 : 0 ≤ N := by linarith
  have h2k : N ^ (2 * k) = N ^ k * N ^ k := by rw [two_mul, pow_add]
  unfold qqCoefE qqCoefPoly qqCoefTail CqE
  have a1 : 1 + (6 * exp 1 * cTwo52 * w) ^ k ≤ (1 + (6 * exp 1 * cTwo52) ^ k) * N ^ k := by
    have : (6 * exp 1 * cTwo52 * w) ^ k ≤ (6 * exp 1 * cTwo52) ^ k * N ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 6 * exp 1 * cTwo52) k]
  have a2 : 1 + (8 * exp 1 * cTwo52 * w) ^ k ≤ (1 + (8 * exp 1 * cTwo52) ^ k) * N ^ k := by
    have : (8 * exp 1 * cTwo52 * w) ^ k ≤ (8 * exp 1 * cTwo52) ^ k * N ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
    nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 8 * exp 1 * cTwo52) k]
  have a3 : (2 * cTwo52 * L) ^ k * (6 * exp 1 * cTwo52 * w) ^ k * exp (-(cZero * w))
      ≤ ((2 * cTwo52) ^ k * N ^ k) * ((6 * exp 1 * cTwo52) ^ k * N ^ k) := by
    have hx : exp (-(cZero * w)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    have b1 : (2 * cTwo52 * L) ^ k ≤ (2 * cTwo52) ^ k * N ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
    have b2 : (6 * exp 1 * cTwo52 * w) ^ k ≤ (6 * exp 1 * cTwo52) ^ k * N ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
    calc (2 * cTwo52 * L) ^ k * (6 * exp 1 * cTwo52 * w) ^ k * exp (-(cZero * w))
        ≤ (2 * cTwo52 * L) ^ k * (6 * exp 1 * cTwo52 * w) ^ k * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul b1 b2 (by positivity) (by positivity)
  have a12 := mul_le_mul a1 a2 (by positivity) (by positivity)
  rw [h2k]
  have e : ((1 + (6 * exp 1 * cTwo52) ^ k) * (1 + (8 * exp 1 * cTwo52) ^ k)
      + (2 * cTwo52) ^ k * (6 * exp 1 * cTwo52) ^ k) * (N ^ k * N ^ k)
      = (1 + (6 * exp 1 * cTwo52) ^ k) * N ^ k * ((1 + (8 * exp 1 * cTwo52) ^ k) * N ^ k)
        + ((2 * cTwo52) ^ k * N ^ k) * ((6 * exp 1 * cTwo52) ^ k * N ^ k) := by ring
  rw [e]
  linarith

theorem qqCoefD_le_crude {L k : ℕ} {w N : ℝ} (hN1 : 1 ≤ N) (hL : (L : ℝ) ≤ N) (hw0 : 0 ≤ w)
    (hwN : w ≤ N) : qqCoefD L k w ≤ CqD k * N ^ (2 * k) := by
  have hc := cTwo52_pos
  have hNk : 1 ≤ N ^ k := one_le_pow₀ hN1
  have hN0 : 0 ≤ N := by linarith
  have h2k : N ^ (2 * k) = N ^ k * N ^ k := by rw [two_mul, pow_add]
  unfold qqCoefD CqD
  have b1 : (2 * cTwo52 * L) ^ k ≤ (2 * cTwo52) ^ k * N ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
  have b2 : 2 + (8 * exp 1 * cTwo52 * w) ^ k + 2 * (2 * cTwo52 * L) ^ k
      ≤ (2 + (8 * exp 1 * cTwo52) ^ k + 2 * (2 * cTwo52) ^ k) * N ^ k := by
    have c1 : (8 * exp 1 * cTwo52 * w) ^ k ≤ (8 * exp 1 * cTwo52) ^ k * N ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
    nlinarith
  rw [h2k]
  calc (2 * cTwo52 * L) ^ k * (2 + (8 * exp 1 * cTwo52 * w) ^ k + 2 * (2 * cTwo52 * L) ^ k)
      ≤ ((2 * cTwo52) ^ k * N ^ k) * ((2 + (8 * exp 1 * cTwo52) ^ k + 2 * (2 * cTwo52) ^ k) * N ^ k) :=
        mul_le_mul b1 b2 (by positivity) (by positivity)
    _ = _ := by ring

end TailPoint4b

section TailPoint4c

variable (d : Dims)

open Real

def C4W (m : ℕ) : ℝ :=
  cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * 4 ^ (2 * ((m + 1 + 1) + (m + 1 + 1)))
      * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * (CqE (m + 1) + CqD (m + 1))
    + 22 * cKerSumZeroErr ((m + 1 + 1) + (m + 1 + 1)) * (12 * exp 1 * (1 + cTwo52)) ^ (4 * (m + 1))
      * ((m + 1 + 1 : ℕ) : ℝ) ^ 2

def C4E (m : ℕ) : ℝ :=
  88 * exp 1 * cKerSumZeroErr ((m + 1 + 1) + (m + 1 + 1)) * (12 * exp 1 * (1 + cTwo52)) ^ (4 * (m + 1))
    * ((m + 1 + 1 : ℕ) : ℝ) ^ 2

end TailPoint4c

section QVdefs

variable (d : Dims)

/-- The QV tail of `tb_qvQ`. -/
def QVtail (d : Dims) (N m : ℕ) (τ' D'' Φq : ℝ) : ℝ :=
  cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (2 * ((m + 1 + 1)
      + (m + 1 + 1)))
    * (qqCoefE (d.L N) (m + 1) ((d.W N : ℝ) ^ τ') * ((N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
        * eeHermErr d N (m + 1 + 1) D'')
      + (N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
        * (qqCoefD (d.L N) (m + 1) ((d.W N : ℝ) ^ τ') * eeHermErr d N (m + 1 + 1) D''))
  + cKerSumZeroErr ((m + 1 + 1) + (m + 1 + 1)) * (d.L N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
    * (N : ℝ) ^ ((m + 1 + 1) + (m + 1 + 1))
    * FastDecayFlow.qqErrBd (d.L N) (m + 1) ((d.W N : ℝ) ^ τ')
        (eeBd d N (m + 1 + 1) Φq ((d.W N : ℝ) ^ τ') D'') (eeHermErr d N (m + 1 + 1) D'')

/-- The QV main coefficient (per unit `Λ`), including the `log N` of `Σ Δ/η`. -/
def QVmain (d : Dims) (E : ℝ) (N m : ℕ) (ε₁ τ' : ℝ) : ℝ :=
  cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (2 * ((m + 1 + 1)
      + (m + 1 + 1))) * qqCoefE (d.L N) (m + 1) ((d.W N : ℝ) ^ τ')
    * (6 * Real.exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁))
    * ((mE E).im⁻¹ * Real.log N + 1)

end QVdefs

section TailPoint4d

variable (d : Dims)

open Real

set_option maxHeartbeats 4000000 in
theorem tail4_le (N m : ℕ) {ε₁ τ' D'' Λ : ℝ} (hN1 : (1 : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hW : (d.W N : ℝ) ≤ N) (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hwN : (d.W N : ℝ) ^ τ' ≤ N)
    (hw1 : 1 ≤ (d.W N : ℝ) ^ τ') (hε₁ : (N : ℝ) ^ ε₁ ≤ N) (hΛ : 1 ≤ Λ) :
    QVtail d N m τ' D'' (2 * (N : ℝ) ^ ε₁ * Λ)
      ≤ Λ * (C4W m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D'')
        + C4E m * (N : ℝ) ^ PT m * exp (-(cZero * (d.W N : ℝ) ^ τ'))) := by
  have hc := cTwo52_pos
  have hcz := cZero_pos
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D'') := Real.rpow_nonneg (by positivity) _
  have hΛ0 : 0 ≤ Λ := by linarith
  set w := (d.W N : ℝ) ^ τ' with hw
  have hw0 : 0 ≤ w := by linarith
  set k := m + 1 with hk
  set n2 := (m + 1 + 1) + (m + 1 + 1) with hn2
  set nn : ℝ := ((m + 1 + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 ≤ nn := by positivity
  set cS2 := cKerSumZero n2 with hcS2
  have hcS20 : 0 ≤ cS2 := cKerSumZero_nonneg _
  set cE2 := cKerSumZeroErr n2 with hcE2
  have hcE20 : 0 ≤ cE2 := by rw [hcE2]; unfold cKerSumZeroErr; positivity
  set ee := eeHermErr d N (m + 1 + 1) D'' with hee
  have hee0 : 0 ≤ ee := eeHermErr_nonneg d N _ D''
  have heeb : ee ≤ nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') := by
    rw [hee]; unfold eeHermErr
    have : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by linarith [mul_comm (d.W N : ℝ) (d.L N : ℝ)]
    calc nn ^ 2 * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D'')
        = nn ^ 2 * ((d.W N : ℝ) * (d.L N : ℝ)) * (d.W N : ℝ) ^ (-D'') := by ring
      _ ≤ _ := by gcongr
  set eb := eeBd d N (m + 1 + 1) (2 * (N : ℝ) ^ ε₁ * Λ) w D'' with heb
  have heb0 : 0 ≤ eb := by
    rw [heb]; unfold eeBd
    have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0 _
    positivity
  have hebb : eb ≤ Λ * (8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4) + nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') := by
    rw [heb]; unfold eeBd
    rw [← hnn]
    have hNe0 : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0 _
    have h1 : (d.W N : ℝ) * ((d.L N : ℝ) * w + 1) ≤ 2 * (N : ℝ) ^ 3 := by
      have : (d.L N : ℝ) * w + 1 ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
      calc (d.W N : ℝ) * ((d.L N : ℝ) * w + 1) ≤ (N : ℝ) * (2 * (N : ℝ) ^ 2) := by gcongr
        _ = 2 * (N : ℝ) ^ 3 := by ring
    have h2 : 2 * (N : ℝ) ^ ε₁ * Λ ≤ 2 * (N : ℝ) * Λ := by gcongr
    have h3 : 2 * exp 1 * nn * (2 * (N : ℝ) ^ ε₁ * Λ) * ((d.W N : ℝ) * ((d.L N : ℝ) * w + 1))
        ≤ 2 * exp 1 * nn * (2 * (N : ℝ) * Λ) * (2 * (N : ℝ) ^ 3) := by gcongr
    have h4 : nn * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D'')
        ≤ nn * (N : ℝ) * (d.W N : ℝ) ^ (-D'') := by
      have : (d.W N : ℝ) * (d.L N : ℝ) ≤ N := by linarith [mul_comm (d.W N : ℝ) (d.L N : ℝ)]
      calc nn * (d.W N : ℝ) * (d.L N : ℝ) * (d.W N : ℝ) ^ (-D'')
          = nn * ((d.W N : ℝ) * (d.L N : ℝ)) * (d.W N : ℝ) ^ (-D'') := by ring
        _ ≤ _ := by gcongr
    have e : nn * (2 * exp 1 * nn * (2 * (N : ℝ) * Λ) * (2 * (N : ℝ) ^ 3)
        + nn * (N : ℝ) * (d.W N : ℝ) ^ (-D''))
        = Λ * (8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4) + nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') := by ring
    rw [← e]
    gcongr
  have hqE := qqCoefE_le_crude (L := d.L N) (k := k) hN1 hL hw0 hwN
  have hqD := qqCoefD_le_crude (L := d.L N) (k := k) hN1 hL hw0 hwN
  have hqE0 : 0 ≤ qqCoefE (d.L N) k w := qqCoefE_nonneg _ _ hw0
  have hqD0 : 0 ≤ qqCoefD (d.L N) k w := qqCoefD_nonneg _ _ hw0
  have hqq := qqErrBd_le (d.L N) k (K := w) hw0 heb0 hee0
  set B := 2 * exp 1 * (2 * ((d.L N : ℝ) * w) + 1) * (1 + cTwo52) * (1 + (d.L N : ℝ)) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBb : B ≤ 12 * exp 1 * (1 + cTwo52) * (N : ℝ) ^ 3 := by
    rw [hB]
    have h1 : 2 * ((d.L N : ℝ) * w) + 1 ≤ 3 * (N : ℝ) ^ 2 := by nlinarith
    have h2 : 1 + (d.L N : ℝ) ≤ 2 * (N : ℝ) := by linarith
    calc 2 * exp 1 * (2 * ((d.L N : ℝ) * w) + 1) * (1 + cTwo52) * (1 + (d.L N : ℝ))
        ≤ 2 * exp 1 * (3 * (N : ℝ) ^ 2) * (1 + cTwo52) * (2 * (N : ℝ)) := by gcongr
      _ = _ := by ring
  have hB4 : B ^ (4 * k) ≤ (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * (N : ℝ) ^ (12 * k) := by
    calc B ^ (4 * k) ≤ (12 * exp 1 * (1 + cTwo52) * (N : ℝ) ^ 3) ^ (4 * k) :=
          pow_le_pow_left₀ hB0 hBb _
      _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
  set x := exp (-(cZero * w)) with hx
  have hx0 : 0 ≤ x := (exp_pos _).le
  have hx1 : x ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  -- part 2
  have P2 : cE2 * (d.L N : ℝ) ^ n2 * (N : ℝ) ^ n2 * FastDecayFlow.qqErrBd (d.L N) k w eb ee
      ≤ Λ * (22 * cE2 * (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * nn ^ 2 * (N : ℝ) ^ PT m
          * (d.W N : ℝ) ^ (-D'')
        + 88 * exp 1 * cE2 * (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * nn ^ 2 * (N : ℝ) ^ PT m * x) := by
    have hsum : ee + eb * x ≤ Λ * (2 * nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')
        + 8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4 * x) := by
      have t1 : eb * x ≤ Λ * (8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4) * x
          + nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') := by
        have := mul_le_mul_of_nonneg_right hebb hx0
        have h2 : nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') * x ≤ nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') := by
          have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D''))
          linarith
        nlinarith
      have t2 : 2 * nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')
          ≤ Λ * (2 * nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')) :=
        le_mul_of_one_le_left (by positivity) hΛ
      have e : Λ * (2 * nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'') + 8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4 * x)
          = Λ * (2 * nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')) + Λ * (8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4) * x := by
        ring
      rw [e]
      nlinarith
    have hLn : (d.L N : ℝ) ^ n2 ≤ (N : ℝ) ^ n2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL _
    have hC0 : 0 ≤ cE2 * (d.L N : ℝ) ^ n2 * (N : ℝ) ^ n2 := by positivity
    calc cE2 * (d.L N : ℝ) ^ n2 * (N : ℝ) ^ n2 * FastDecayFlow.qqErrBd (d.L N) k w eb ee
        ≤ cE2 * (d.L N : ℝ) ^ n2 * (N : ℝ) ^ n2 * (11 * B ^ (4 * k) * (ee + eb * x)) :=
          mul_le_mul_of_nonneg_left hqq hC0
      _ ≤ cE2 * (N : ℝ) ^ n2 * (N : ℝ) ^ n2 * (11 * ((12 * exp 1 * (1 + cTwo52)) ^ (4 * k)
            * (N : ℝ) ^ (12 * k)) * (Λ * (2 * nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')
              + 8 * exp 1 * nn ^ 2 * (N : ℝ) ^ 4 * x))) := by
          have : 0 ≤ ee + eb * x := by positivity
          gcongr
      _ = Λ * (22 * cE2 * (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * nn ^ 2
            * ((N : ℝ) ^ n2 * (N : ℝ) ^ n2 * (N : ℝ) ^ (12 * k) * (N : ℝ)) * (d.W N : ℝ) ^ (-D'')
          + 88 * exp 1 * cE2 * (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * nn ^ 2
            * ((N : ℝ) ^ n2 * (N : ℝ) ^ n2 * (N : ℝ) ^ (12 * k) * (N : ℝ) ^ 4) * x) := by ring
      _ ≤ _ := by
          have hp1 : (N : ℝ) ^ n2 * (N : ℝ) ^ n2 * (N : ℝ) ^ (12 * k) * (N : ℝ) ≤ (N : ℝ) ^ PT m := by
            rw [← pow_add, ← pow_add, ← pow_succ]
            exact pow_le_pow_right₀ hN1 (by rw [hn2, hk]; unfold PT; omega)
          have hp2 : (N : ℝ) ^ n2 * (N : ℝ) ^ n2 * (N : ℝ) ^ (12 * k) * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ PT m := by
            rw [← pow_add, ← pow_add, ← pow_add]
            exact pow_le_pow_right₀ hN1 (by rw [hn2, hk]; unfold PT; omega)
          gcongr
  -- part 1
  have P1 : cS2 * (4 * w) ^ (2 * n2) * (qqCoefE (d.L N) k w * ((N : ℝ) ^ n2 * ee)
        + (N : ℝ) ^ n2 * (qqCoefD (d.L N) k w * ee))
      ≤ Λ * (cS2 * 4 ^ (2 * n2) * nn ^ 2 * (CqE k + CqD k) * (N : ℝ) ^ PT m
        * (d.W N : ℝ) ^ (-D'')) := by
    have h4w : (4 * w) ^ (2 * n2) ≤ 4 ^ (2 * n2) * (N : ℝ) ^ (2 * n2) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have hCq0 := CqE_nonneg k
    have hCd0 := CqD_nonneg k
    have hin : qqCoefE (d.L N) k w * ((N : ℝ) ^ n2 * ee) + (N : ℝ) ^ n2 * (qqCoefD (d.L N) k w * ee)
        ≤ (CqE k + CqD k) * (N : ℝ) ^ (2 * k) * (N : ℝ) ^ n2 * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')) := by
      have a1 : qqCoefE (d.L N) k w * ((N : ℝ) ^ n2 * ee)
          ≤ CqE k * (N : ℝ) ^ (2 * k) * ((N : ℝ) ^ n2 * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D''))) := by
        gcongr
      have a2 : (N : ℝ) ^ n2 * (qqCoefD (d.L N) k w * ee)
          ≤ (N : ℝ) ^ n2 * (CqD k * (N : ℝ) ^ (2 * k) * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D''))) := by
        gcongr
      have e : (CqE k + CqD k) * (N : ℝ) ^ (2 * k) * (N : ℝ) ^ n2 * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D''))
          = CqE k * (N : ℝ) ^ (2 * k) * ((N : ℝ) ^ n2 * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D'')))
            + (N : ℝ) ^ n2 * (CqD k * (N : ℝ) ^ (2 * k) * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D''))) := by
        ring
      rw [e]; linarith
    have hin0 : 0 ≤ qqCoefE (d.L N) k w * ((N : ℝ) ^ n2 * ee) + (N : ℝ) ^ n2 * (qqCoefD (d.L N) k w * ee) := by
      positivity
    have hCq := CqE_nonneg k
    have hCd := CqD_nonneg k
    calc cS2 * (4 * w) ^ (2 * n2) * (qqCoefE (d.L N) k w * ((N : ℝ) ^ n2 * ee)
          + (N : ℝ) ^ n2 * (qqCoefD (d.L N) k w * ee))
        ≤ cS2 * (4 ^ (2 * n2) * (N : ℝ) ^ (2 * n2)) * ((CqE k + CqD k) * (N : ℝ) ^ (2 * k)
          * (N : ℝ) ^ n2 * (nn ^ 2 * (N : ℝ) * (d.W N : ℝ) ^ (-D''))) := by gcongr
      _ = cS2 * 4 ^ (2 * n2) * nn ^ 2 * (CqE k + CqD k)
          * ((N : ℝ) ^ (2 * n2) * (N : ℝ) ^ (2 * k) * (N : ℝ) ^ n2 * (N : ℝ)) * (d.W N : ℝ) ^ (-D'') := by
          ring
      _ ≤ cS2 * 4 ^ (2 * n2) * nn ^ 2 * (CqE k + CqD k) * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D'') := by
          have hp : (N : ℝ) ^ (2 * n2) * (N : ℝ) ^ (2 * k) * (N : ℝ) ^ n2 * (N : ℝ) ≤ (N : ℝ) ^ PT m := by
            rw [← pow_add, ← pow_add, ← pow_succ]
            exact pow_le_pow_right₀ hN1 (by rw [hn2, hk]; unfold PT; omega)
          gcongr
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hΛ
  unfold QVtail
  rw [← hw, ← hn2, ← hcS2, ← hcE2, ← hee, ← heb]
  have e : Λ * (C4W m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D'') + C4E m * (N : ℝ) ^ PT m * x)
      = Λ * (cS2 * 4 ^ (2 * n2) * nn ^ 2 * (CqE k + CqD k) * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D''))
        + Λ * (22 * cE2 * (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * nn ^ 2 * (N : ℝ) ^ PT m
          * (d.W N : ℝ) ^ (-D'')
        + 88 * exp 1 * cE2 * (12 * exp 1 * (1 + cTwo52)) ^ (4 * k) * nn ^ 2 * (N : ℝ) ^ PT m * x) := by
    unfold C4W C4E; rw [← hcS2, ← hcE2, ← hn2, ← hnn, ← hk]; ring
  rw [e]
  linarith

end TailPoint4d

section TailPoint3d

variable (d : Dims)

open Real

def C3W (m : ℕ) : ℝ :=
  cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * CTd m + cKerSumZeroErr (m + 2) * CδW m

def C3E (m : ℕ) : ℝ := cKerSumZeroErr (m + 2) * CδE m

set_option maxHeartbeats 1600000 in
theorem tail3_le (N m : ℕ) {ε₁ τ' D' Φ CK : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hL : (d.L N : ℝ) ≤ N) (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N) (hwN : (d.W N : ℝ) ^ τ' ≤ N)
    (hw1 : 1 ≤ (d.W N : ℝ) ^ τ') (hε₁ : (N : ℝ) ^ ε₁ ≤ N) (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK)
    (hCKN : CK + 1 ≤ N) :
    cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
        * TailDbd d N m ε₁ τ' D' Φ CK
      + cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
        * δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
            (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N
      ≤ (1 + Φ) * (C3W m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D')
        + C3E m * (N : ℝ) ^ PT m * exp (-(cZero * (d.W N : ℝ) ^ τ'))) := by
  have hc := cTwo52_pos
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
  have hw0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := by linarith
  have hcS := cKerSumZero_nonneg (m + 2)
  have hcE : 0 ≤ cKerSumZeroErr (m + 2) := by unfold cKerSumZeroErr; positivity
  have hT := TailDbd_le_crude d N m (ε₁ := ε₁) (D' := D') (Φ := Φ) hN1 hL hLW hwN hw0 hε₁ hΦ hCK hCKN
  have hδ := δDbd_le_crude d N m (D' := D') hN1 hL hLW hwN hw1 hCK hCKN
  have hCT := CTd_nonneg m
  have hCW := CδW_nonneg m
  have hCE := CδE_nonneg m
  set x := exp (-(cZero * (d.W N : ℝ) ^ τ')) with hx
  have hx0 : 0 ≤ x := (exp_pos _).le
  have hK : (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) ≤ 16 ^ (2 * (m + 2)) * (N : ℝ) ^ (2 * (m + 2)) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have P1 : cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
        * TailDbd d N m ε₁ τ' D' Φ CK
      ≤ (1 + Φ) * (cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * CTd m * (N : ℝ) ^ PT m
          * (d.W N : ℝ) ^ (-D')) := by
    have hT0 : 0 ≤ TailDbd d N m ε₁ τ' D' Φ CK := by
      unfold TailDbd Ec514
      have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0 _
      have := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
      positivity
    calc cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
          * TailDbd d N m ε₁ τ' D' Φ CK
        ≤ cKerSumZero (m + 2) * (16 ^ (2 * (m + 2)) * (N : ℝ) ^ (2 * (m + 2))) * (N : ℝ) ^ (m + 2)
          * ((1 + Φ) * (CTd m * (N : ℝ) ^ (3 * m + 7) * (d.W N : ℝ) ^ (-D'))) := by gcongr
      _ = (1 + Φ) * (cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * CTd m
          * ((N : ℝ) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (3 * m + 7))
          * (d.W N : ℝ) ^ (-D')) := by ring
      _ ≤ _ := by
          have hp : (N : ℝ) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (3 * m + 7) ≤ (N : ℝ) ^ PT m := by
            rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hN1 (by unfold PT; omega)
          gcongr
  have P2 : cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
        * δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
            (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N
      ≤ cKerSumZeroErr (m + 2) * CδW m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D')
        + C3E m * (N : ℝ) ^ PT m * x := by
    have hLn : (d.L N : ℝ) ^ (m + 2) ≤ (N : ℝ) ^ (m + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hL _
    have hδ0 : 0 ≤ δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
        (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N := by
      unfold δDbd
      have := driftErr514_nonneg d N m (D' := D') (by linarith : (0 : ℝ) ≤ CK + 1)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
      have := cZero_pos
      positivity
    calc cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
          * δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
            (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N
        ≤ cKerSumZeroErr (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
          * (CδW m * (N : ℝ) ^ (2 * m + 4) * (d.W N : ℝ) ^ (-D')
            + CδE m * (N : ℝ) ^ (3 * m + 9) * x) := by gcongr
      _ = cKerSumZeroErr (m + 2) * CδW m * ((N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (2 * m + 4))
            * (d.W N : ℝ) ^ (-D')
          + cKerSumZeroErr (m + 2) * CδE m * ((N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (3 * m + 9))
            * x := by ring
      _ ≤ _ := by
          have hp1 : (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (2 * m + 4) ≤ (N : ℝ) ^ PT m := by
            rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hN1 (by unfold PT; omega)
          have hp2 : (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2) * (N : ℝ) ^ (3 * m + 9) ≤ (N : ℝ) ^ PT m := by
            rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hN1 (by unfold PT; omega)
          unfold C3E
          gcongr
  have hC3E0 : 0 ≤ C3E m := by unfold C3E; positivity
  have e : (1 + Φ) * (C3W m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D') + C3E m * (N : ℝ) ^ PT m * x)
      = (1 + Φ) * (cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * CTd m * (N : ℝ) ^ PT m
          * (d.W N : ℝ) ^ (-D'))
        + (1 + Φ) * (cKerSumZeroErr (m + 2) * CδW m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D')
          + C3E m * (N : ℝ) ^ PT m * x) := by unfold C3W; ring
  rw [e]
  have hP2' : cKerSumZeroErr (m + 2) * CδW m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D')
        + C3E m * (N : ℝ) ^ PT m * x
      ≤ (1 + Φ) * (cKerSumZeroErr (m + 2) * CδW m * (N : ℝ) ^ PT m * (d.W N : ℝ) ^ (-D')
          + C3E m * (N : ℝ) ^ PT m * x) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  linarith

end TailPoint3d

section AbsorbQ

variable (d : Dims)

open Real

/-- **The `Y` scale of the `Q`-route is polynomial**: `PYQ ≤ 3428·1024^n n^4 N^{10m+24}`. -/
theorem PYQ_le (N m : ℕ) {T η : ℝ} (hN1 : (1 : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N) (hT : T < 1)
    (hT' : (1 - T)⁻¹ ≤ N) (hη : 0 < η) (hη' : η⁻¹ ≤ N) :
    PYQ d N m T η ≤ 3428 * 32 ^ (2 * (m + 2)) * ((m + 2 : ℕ) : ℝ) ^ 4 * (N : ℝ) ^ (10 * m + 24) := by
  set n := m + 2 with hn
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hT0 : 0 ≤ (1 - T)⁻¹ := inv_nonneg.mpr (by linarith)
  have hη0 : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  have hc0 : (0 : ℝ) ≤ Fintype.card (d.Idx N) := Nat.cast_nonneg _
  have hy : (1 + (1 - T)⁻¹) ^ n * (C2g d N n η / 2) ≤ 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (4 * n + 1) := by
    unfold C2g
    have h1 : (1 + (1 - T)⁻¹) ^ n ≤ (2 * (N : ℝ)) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    have h2 : (2 * (1 + η⁻¹) ^ 3) ^ n ≤ (16 * (N : ℝ) ^ 3) ^ n := by
      refine pow_le_pow_left₀ (by positivity) ?_ n
      have : (1 + η⁻¹) ^ 3 ≤ (2 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
      nlinarith
    have h3 : (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) / 2
        ≤ (N : ℝ) * ((n : ℝ) ^ 2 * (16 * (N : ℝ) ^ 3) ^ n) := by
      have : (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n)
          ≤ (N : ℝ) * ((n : ℝ) ^ 2 * (16 * (N : ℝ) ^ 3) ^ n) :=
        mul_le_mul hcard (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity) hN0
      have h0 : 0 ≤ (Fintype.card (d.Idx N) : ℝ) * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) := by
        positivity
      linarith
    calc (1 + (1 - T)⁻¹) ^ n * ((Fintype.card (d.Idx N) : ℝ)
          * ((n : ℝ) ^ 2 * (2 * (1 + η⁻¹) ^ 3) ^ n) / 2)
        ≤ (2 * (N : ℝ)) ^ n * ((N : ℝ) * ((n : ℝ) ^ 2 * (16 * (N : ℝ) ^ 3) ^ n)) :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
      _ = 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (4 * n + 1) := by
          rw [mul_pow, mul_pow, ← pow_mul, show (32 : ℝ) = 2 * 16 by norm_num, mul_pow]
          ring
  have hLm : 1 + (d.L N : ℝ) ^ (m + 1) ≤ 2 * (N : ℝ) ^ (m + 1) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hL (m + 1)
    have := one_le_pow₀ (n := m + 1) hN1
    linarith
  have hyQ : (1 + (1 - T)⁻¹) ^ n * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N n η) / 2)
      ≤ 2 * 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (5 * m + 10) := by
    have hC0 : 0 ≤ C2g d N n η := by unfold C2g; positivity
    have e : (1 + (1 - T)⁻¹) ^ n * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N n η) / 2)
        = (1 + (d.L N : ℝ) ^ (m + 1)) * ((1 + (1 - T)⁻¹) ^ n * (C2g d N n η / 2)) := by ring
    rw [e]
    calc (1 + (d.L N : ℝ) ^ (m + 1)) * ((1 + (1 - T)⁻¹) ^ n * (C2g d N n η / 2))
        ≤ (2 * (N : ℝ) ^ (m + 1)) * (32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (4 * n + 1)) :=
          mul_le_mul hLm hy (by positivity) (by positivity)
      _ = 2 * 32 ^ n * (n : ℝ) ^ 2 * ((N : ℝ) ^ (m + 1) * (N : ℝ) ^ (4 * n + 1)) := by ring
      _ = 2 * 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (5 * m + 10) := by
          rw [← pow_add]; congr 2; rw [hn]; ring
  have hyQ0 : 0 ≤ (1 + (1 - T)⁻¹) ^ n * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N n η) / 2) := by
    unfold C2g; positivity
  -- moments
  have hm2 : xMom d N 2 ≤ N := (integral_normSq_Xmat_le514 d N).trans hcard
  have hm4 : xMom d N 4 ≤ 3 * N := by
    have h := integral_norm_Xmat_pow_le514 d N 1
    rw [show traceConst (2 ^ 1) = 3 by norm_num [traceConst], show 2 * 2 ^ 1 = 4 by norm_num] at h
    show ∫ x, ‖Xmat d N x‖ ^ 4 ∂(P d) ≤ 3 * N
    linarith
  have hm8 : xMom d N 8 ≤ 105 * N := by
    have h := integral_norm_Xmat_pow_le514 d N 2
    rw [show traceConst (2 ^ 2) = 105 by norm_num [traceConst], show 2 * 2 ^ 2 = 8 by norm_num] at h
    show ∫ x, ‖Xmat d N x‖ ^ 8 ∂(P d) ≤ 105 * N
    linarith
  have hm20 := xMom_nonneg d N 2
  have hN4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := by
    calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hN1 (by norm_num)
  have hN24 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
  have hN41 : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN1
  have hX : 2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) + 1
      ≤ 857 * (N : ℝ) ^ 4 := by
    have a1 : xMom d N 2 ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hm20 hm2 2
    have a2 : xMom d N 2 ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hm20 hm2 4
    nlinarith
  have hX0 : 0 ≤ 2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) + 1 := by
    have := xMom_nonneg d N 4; have := xMom_nonneg d N 8; positivity
  unfold PYQ
  calc ((1 + (1 - T)⁻¹) ^ n * (((1 + (d.L N : ℝ) ^ (m + 1)) * C2g d N n η) / 2)) ^ 2
        * (2 * xMom d N 4 + 2 * xMom d N 2 ^ 2 + 8 * (xMom d N 8 + xMom d N 2 ^ 4) + 1)
      ≤ (2 * 32 ^ n * (n : ℝ) ^ 2 * (N : ℝ) ^ (5 * m + 10)) ^ 2 * (857 * (N : ℝ) ^ 4) :=
        mul_le_mul (pow_le_pow_left₀ hyQ0 hyQ 2) hX hX0 (by positivity)
    _ = 3428 * 32 ^ (2 * n) * (n : ℝ) ^ 4 * (N : ℝ) ^ (10 * m + 24) := by
        ring

end AbsorbQ

section AbsorbMainQ

variable (d : Dims)

open Real

/-- `(W^{τ'})^j ≤ N^{jτ'}` and `1 ≤ W^{τ'}`, packaged. -/
theorem wpow_le {N : ℕ} {τ' : ℝ} (hτ' : 0 ≤ τ') (hWN : (d.W N : ℝ) ≤ N) (j : ℕ) :
    ((d.W N : ℝ) ^ τ') ^ j ≤ (N : ℝ) ^ ((j : ℝ) * τ') :=
  rpow_pow_le_of_le (Nat.cast_nonneg _) hWN hτ' j

theorem G_le_w {N m : ℕ} {τ' : ℝ} (hτ' : 0 ≤ τ') :
    1 + (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)
      ≤ (1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * ((d.W N : ℝ) ^ τ') ^ (m + 1) := by
  have hc := cTwo52_pos
  have hw1 : 1 ≤ (d.W N : ℝ) ^ τ' := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'
  have h1 : (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)
      = (24 * exp 1 * cTwo52) ^ (m + 1) * ((d.W N : ℝ) ^ τ') ^ (m + 1) := by
    rw [← mul_pow]; ring_nf
  have h2 : (1 : ℝ) ≤ ((d.W N : ℝ) ^ τ') ^ (m + 1) := one_le_pow₀ hw1
  rw [h1]; nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 24 * exp 1 * cTwo52) (m + 1)]

set_option maxHeartbeats 1600000 in
/-- (ha1Q) The initial-datum main term. -/
theorem ev_ha1Q (m : ℕ) {ε ε₁ τ' : ℝ} (hτ' : 0 ≤ τ')
    (hε : ((3 * m + 5 : ℕ) : ℝ) * τ' + ε₁ < ε) :
    ∀ᶠ N : ℕ in atTop, cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2))
      * (1 + (6 * exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * (N : ℝ) ^ ε₁
      ≤ (N : ℝ) ^ ε / 16 := by
  set C := cKerSumZero (m + 2) * 16 ^ (2 * (m + 2)) * (1 + (24 * exp 1 * cTwo52) ^ (m + 1)) with hC
  have hc := cTwo52_pos
  have hC0 : 0 ≤ C := by rw [hC]; have := cKerSumZero_nonneg (m + 2); positivity
  filter_upwards [ev_dims514 d, ev_rpow_le hε (16 * C)] with N hd hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  set w := (d.W N : ℝ) ^ τ' with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'
  have hG := G_le_w d (N := N) (m := m) hτ'
  rw [← hw] at hG
  have hK : (4 * (4 * w)) ^ (2 * (m + 2)) = 16 ^ (2 * (m + 2)) * w ^ (2 * (m + 2)) := by
    rw [← mul_pow]; ring_nf
  have hwp := wpow_le d (N := N) hτ' hWN (3 * m + 5)
  rw [← hw] at hwp
  have hNe : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  have hcS := cKerSumZero_nonneg (m + 2)
  calc cKerSumZero (m + 2) * (4 * (4 * w)) ^ (2 * (m + 2))
        * (1 + (6 * exp 1 * cTwo52 * (4 * w)) ^ (m + 1)) * (N : ℝ) ^ ε₁
      ≤ cKerSumZero (m + 2) * (16 ^ (2 * (m + 2)) * w ^ (2 * (m + 2)))
        * ((1 + (24 * exp 1 * cTwo52) ^ (m + 1)) * w ^ (m + 1)) * (N : ℝ) ^ ε₁ := by
        rw [hK]; gcongr
    _ = C * w ^ (3 * m + 5) * (N : ℝ) ^ ε₁ := by
        rw [hC, show 3 * m + 5 = 2 * (m + 2) + (m + 1) by ring, pow_add]; ring
    _ ≤ C * (N : ℝ) ^ (((3 * m + 5 : ℕ) : ℝ) * τ') * (N : ℝ) ^ ε₁ := by gcongr
    _ = (16 * C * (N : ℝ) ^ (((3 * m + 5 : ℕ) : ℝ) * τ' + ε₁)) / 16 := by
        rw [Real.rpow_add hN0]; ring
    _ ≤ (N : ℝ) ^ ε / 16 := by linarith

/-- (ha4Q) The endpoint-correction main term. -/
theorem ev_ha4Q (m : ℕ) {ε ε₁ τ' : ℝ} (hτ' : 0 ≤ τ') (hε : ((m : ℕ) : ℝ) * τ' + ε₁ < ε) :
    ∀ᶠ N : ℕ in atTop, cTwo52 ^ (m + 1) * (4 * exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * (N : ℝ) ^ ε₁
      ≤ (N : ℝ) ^ ε / 16 := by
  set C := cTwo52 ^ (m + 1) * (4 * exp 1) ^ m with hC
  have hC0 : 0 ≤ C := by rw [hC]; have := cTwo52_pos; positivity
  filter_upwards [ev_dims514 d, ev_rpow_le hε (16 * C)] with N hd hA
  obtain ⟨hN1, -, hWN, -, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hwp := wpow_le d (N := N) hτ' hWN m
  have hNe : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  calc cTwo52 ^ (m + 1) * (4 * exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * (N : ℝ) ^ ε₁
      = C * ((d.W N : ℝ) ^ τ') ^ m * (N : ℝ) ^ ε₁ := by rw [hC]
    _ ≤ C * (N : ℝ) ^ (((m : ℕ) : ℝ) * τ') * (N : ℝ) ^ ε₁ := by gcongr
    _ = (16 * C * (N : ℝ) ^ (((m : ℕ) : ℝ) * τ' + ε₁)) / 16 := by rw [Real.rpow_add hN0]; ring
    _ ≤ (N : ℝ) ^ ε / 16 := by linarith

/-- `qqCoefTail ≤ 1` eventually (`exp(-c₀ W^{τ'})` beats the polynomial `(2cL)^k (6ecW^{τ'})^k`). -/
theorem ev_qqCoefTail (k : ℕ) {τ' : ℝ} (hτ' : 0 < τ') (hτ'1 : τ' ≤ 1) :
    ∀ᶠ N : ℕ in atTop, qqCoefTail (d.L N) k ((d.W N : ℝ) ^ τ') ≤ 1 := by
  have hc := cTwo52_pos
  filter_upwards [ev_dims514 d, ev_tailExp d ((2 * cTwo52) ^ k * (6 * exp 1 * cTwo52) ^ k) (2 * k) 0
    cZero_pos hτ' one_pos] with N hd hT
  obtain ⟨hN1, -, hWN, hL, -, -, -⟩ := hd
  have hN0 : (0 : ℝ) < N := by linarith
  have hwN : (d.W N : ℝ) ^ τ' ≤ N := by
    calc (d.W N : ℝ) ^ τ' ≤ (N : ℝ) ^ τ' := Real.rpow_le_rpow (by positivity) hWN hτ'.le
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hτ'1
      _ = N := Real.rpow_one _
  have hw0 : 0 ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
  simp only [pow_zero, inv_one, div_one] at hT
  unfold qqCoefTail
  refine le_trans ?_ hT
  have b1 : (2 * cTwo52 * (d.L N : ℝ)) ^ k ≤ (2 * cTwo52) ^ k * (N : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
  have b2 : (6 * exp 1 * cTwo52 * (d.W N : ℝ) ^ τ') ^ k ≤ (6 * exp 1 * cTwo52) ^ k * (N : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by gcongr) k
  calc (2 * cTwo52 * (d.L N : ℝ)) ^ k * (6 * exp 1 * cTwo52 * (d.W N : ℝ) ^ τ') ^ k
        * exp (-(cZero * (d.W N : ℝ) ^ τ'))
      ≤ ((2 * cTwo52) ^ k * (N : ℝ) ^ k) * ((6 * exp 1 * cTwo52) ^ k * (N : ℝ) ^ k)
        * exp (-(cZero * (d.W N : ℝ) ^ τ')) := by
        gcongr
    _ = (2 * cTwo52) ^ k * (6 * exp 1 * cTwo52) ^ k * (N : ℝ) ^ (2 * k)
        * exp (-(cZero * (d.W N : ℝ) ^ τ')) := by ring

end AbsorbMainQ

section AbsorbTailQ

open Real

theorem ev_ht5 (m : ℕ) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(((2 * (m + 2) + 3 : ℕ) : ℝ)))
      ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096 := by
  filter_upwards [eventually_ge_atTop 4096] with N hN
  have hN1 : (4096 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  rw [show 2 * (m + 2) + 3 = (2 * (m + 2) + 2) + 1 by ring, pow_succ, mul_inv]
  have h1 : (N : ℝ)⁻¹ ≤ 1 / 4096 := by
    rw [inv_le_comm₀ hN0 (by norm_num)]; norm_num; linarith
  have h2 : 0 ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ := by positivity
  calc ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ * (N : ℝ)⁻¹ ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ * (1 / 4096) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = _ := by ring

theorem ev_ht6 (m : ℕ) {C_K : ℝ}
    (hCK : (((m + 2 : ℕ) : ℝ) + ((4 * m + 21 : ℕ) : ℝ)) - C_K / 2 < -(((2 * (m + 2) + 2 : ℕ) : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ (N : ℝ) ^ (-C_K) →
      (1 + (N : ℝ)) ^ (m + 2) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21)) * Δ ^ ((1 : ℝ) / 2)
        ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096 := by
  set C := 4096 * (CRQ m * 2 ^ (m + 2) * 2 ^ (4 * m + 21)) with hC
  have hC0 : 0 ≤ C := by rw [hC]; have := CRQ_nonneg m; positivity
  filter_upwards [ev_rpow_le hCK C, eventually_ge_atTop 1] with N hA hN1'
  intro Δ hΔ0 hΔ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hN0 : (0 : ℝ) < N := by linarith
  have hsq : Δ ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-C_K / 2) := by
    calc Δ ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) ^ (-C_K)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hΔ0 hΔ (by norm_num)
      _ = (N : ℝ) ^ (-C_K / 2) := by rw [← Real.rpow_mul hN0.le]; ring_nf
  have h1N : (1 + (N : ℝ)) ^ (m + 2) ≤ 2 ^ (m + 2) * (N : ℝ) ^ (m + 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hCR := CRQ_nonneg m
  have hq : 0 < (N : ℝ) ^ (2 * (m + 2) + 2) := by positivity
  calc (1 + (N : ℝ)) ^ (m + 2) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21)) * Δ ^ ((1 : ℝ) / 2)
      ≤ (2 ^ (m + 2) * (N : ℝ) ^ (m + 2)) * (CRQ m * (2 ^ (4 * m + 21) * (N : ℝ) ^ (4 * m + 21)))
        * (N : ℝ) ^ (-C_K / 2) := by
        rw [mul_pow 2 (N : ℝ)]
        gcongr
    _ = (C / 4096) * ((N : ℝ) ^ (((m + 2 : ℕ) : ℝ)) * (N : ℝ) ^ (((4 * m + 21 : ℕ) : ℝ))
          * (N : ℝ) ^ (-C_K / 2)) := by
        rw [hC, Real.rpow_natCast, Real.rpow_natCast]; ring
    _ = (C * (N : ℝ) ^ ((((m + 2 : ℕ) : ℝ) + ((4 * m + 21 : ℕ) : ℝ)) - C_K / 2)) / 4096 := by
        rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_add hN0]; ring_nf
    _ ≤ (N : ℝ) ^ (-(((2 * (m + 2) + 2 : ℕ) : ℝ))) / 4096 := by gcongr
    _ = _ := by rw [Real.rpow_neg hN0.le, Real.rpow_natCast]

end AbsorbTailQ

section BudgetFinal

variable (d : Dims)

open Real

set_option maxHeartbeats 8000000 in
/-- **The (5.93) budget of the `Q`-route at a fixed `N`**: on the good event (`τ = K`), the
assembly bound plus the endpoint correction (5.101) is `≤ N^ε (Λ^{1/2} + Φ) A_v^{-n}`, given the
regime facts and the absorption inequalities (each eventually true in `N`, §11). The sharp
kernel enters only through `kapQ_mul_scale_pow_eq`/`tb_driftQ`/`tb_qvQ`: **no `η_s/η_t`
prefactor** on any main term. -/
theorem budgetQ {m : ℕ} {E : ℝ} (hE : |E| < 2) (s v : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ)
    {ε ε₁ τ' D' D_Y Λ Φ CK X0 S0 XiK : ℝ} (a : LoopArg (d.L N) (m + 2))
    (hs0 : 0 ≤ s N) (hsv : s N < v N) (hv1 : v N < 1) (hK1 : 1 ≤ K N)
    (hN1 : (1 : ℝ) ≤ N) (hW : (d.W N : ℝ) ≤ N) (hL : (d.L N : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hLW : (d.L N : ℝ) * (d.W N : ℝ) ≤ N)
    (hη : (etaT E (v N))⁻¹ ≤ N) (hA : ∀ u, 0 ≤ u → u ≤ v N → 1 ≤ (band d).scale E N u)
    (hΛ : 1 ≤ Λ) (hΦ : 0 ≤ Φ) (hCK : 0 ≤ CK) (hCKN : CK + 1 ≤ N)
    (hΔN : step s v K N * (2 * (N : ℝ)) ≤ 1) (hτ' : 0 ≤ τ') (hε₁ : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1)
    (hε : 0 ≤ ε)
    (hlog : ∑ j ∈ Finset.range (K N), step s v K N / etaT E (time s v K N j)
      ≤ (mE E).im⁻¹ * Real.log N)
    (hX00 : 0 ≤ X0) (hX0 : X0 ≤ (N : ℝ) ^ ε₁ * ((band d).scale E N (s N))⁻¹ ^ (m + 2))
    (hS0 : S0 ≤ (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * X0
        + (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
    (hXi : XiK ≤ (N : ℝ) ^ ε₁ * Φ)
    (ha1 : cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2))
      * (1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1)) * (N : ℝ) ^ ε₁
      ≤ (N : ℝ) ^ ε / 16)
    (ha2 : cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2))
      * McQ d N m ε₁ τ' CK * ((mE E).im⁻¹ * Real.log N) ≤ (N : ℝ) ^ ε / 16)
    (ha3 : (N : ℝ) ^ ε₁ * Real.sqrt (QVmain d E N m ε₁ τ') ≤ (N : ℝ) ^ ε / 16)
    (ha4 : cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * (N : ℝ) ^ ε₁
      ≤ (N : ℝ) ^ ε / 16)
    (ht1 : cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
      * ((2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D'))
      ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096)
    (ht2 : cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
      * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
          ((d.W N : ℝ) ^ (-D'))
      ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096)
    (ht3 : cKerSumZero (m + 2) * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * (m + 2)) * (N : ℝ) ^ (m + 2)
        * TailDbd d N m ε₁ τ' D' Φ CK
      + cKerSumZeroErr (m + 2) * (d.L N : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2)
        * δDbd d N m τ' D' (CK + 1) ((N : ℝ) + (N : ℝ) ^ (m + 2) + CK + 1)
            (10 * ((m : ℝ) + 2) ^ 3 * (N : ℝ) ^ (2 * m + 8)) N
      ≤ (1 + Φ) * (((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096))
    (ht4 : QVtail d N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ)
      ≤ Λ * (((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096))
    (ht5 : (N : ℝ) ^ (-D_Y) ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096)
    (ht6 : (1 + (N : ℝ)) ^ (m + 2) * (CRQ m * (2 * (N : ℝ)) ^ (4 * m + 21))
        * step s v K N ^ ((1 : ℝ) / 2) ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096)
    (ht7 : cTwo52 ^ (m + 1) * ((N : ℝ) * (N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
      ≤ ((N : ℝ) ^ (2 * (m + 2) + 2))⁻¹ / 4096) :
    kapQ (d.L N) (m + 2) (4 * (4 * (d.W N : ℝ) ^ τ')) (time s v K N) 0 (K N) * S0
      + epsQ (d.L N) (m + 2) (time s v K N) 0 (K N)
        * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
            (MD514 d E N (m + 2) (CK + 1) (time s v K N 0)) ((d.W N : ℝ) ^ (-D'))
      + step s v K N * ∑ j ∈ Finset.range (K N),
          (kapQ (d.L N) (m + 2) (4 * (4 * (d.W N : ℝ) ^ τ')) (time s v K N) (j + 1) (K N)
              * dDrQ d E N m (time s v K N j) ε₁ τ' D' Φ CK
                  (MD514 d E N (m + 2) (CK + 1) (time s v K N j)
                    * (band d).scale E N (time s v K N j) ^ (m + 2))
                  (CK + 1) (MD514 d E N (m + 2) (CK + 1) (time s v K N j))
            + epsQ (d.L N) (m + 2) (time s v K N) (j + 1) (K N)
              * δDQ d E N m (time s v K N j) τ' D' (CK + 1)
                  (MD514 d E N (m + 2) (CK + 1) (time s v K N j)) (CK + 1))
      + (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range (K N),
          (cQVQ d E s v K N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ))
      + (N : ℝ) ^ (-D_Y)
      + ∑ j ∈ Finset.range (K N), (1 + (1 - time s v K N (K N))⁻¹) ^ (m + 2)
          * qErrQ d E s v K N m (CK + 1) j
      + (cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m
            * ((band d).scale E N (v N))⁻¹ ^ (m + 2) * XiK
          + (cTwo52 / (band d).ell N (v N)) ^ (m + 1)
            * (((d.W N : ℝ) * etaT E (v N))⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D')))
      ≤ (N : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) * ((band d).scale E N (v N) ^ (m + 2))⁻¹ := by
  revert a
  set n := m + 2 with hn
  intro a
  set u := time s v K N with hu
  set Δ := step s v K N with hΔ
  have hK0 : K N ≠ 0 := by omega
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hu00 : u 0 = s N := time_zero s v K N
  have huK : u (K N) = v N := time_last s v K N hK0
  have hN0 : (0 : ℝ) < N := by linarith
  have hAv : 1 ≤ (band d).scale E N (v N) := hA (v N) (hs0.trans hsv.le) le_rfl
  have hAv0 : 0 < (band d).scale E N (v N) := lt_of_lt_of_le one_pos hAv
  have hAvN : (band d).scale E N (v N) ≤ N := (scale_le_LW d hE N (hs0.trans hsv.le) hv1).trans hLW
  set X := ((band d).scale E N (v N))⁻¹ ^ n with hX
  have hX0' : 0 ≤ X := by positivity
  have hXN : (N : ℝ)⁻¹ ^ n ≤ X := pow_le_pow_left₀ (by positivity) (inv_anti₀ hAv0 hAvN) n
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε
  have hNe0 : (0 : ℝ) ≤ (N : ℝ) ^ ε := by linarith
  have hsqΛ : 1 ≤ Λ ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  set Tn := ((N : ℝ) ^ (2 * n + 2))⁻¹ / 4096 with hTn
  have hTn0 : 0 ≤ Tn := by positivity
  have hTnX : Tn ≤ X / 4096 := by
    rw [hTn]
    have h1 : ((N : ℝ) ^ (2 * n + 2))⁻¹ ≤ (N : ℝ)⁻¹ ^ n := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hN1 (by omega))
    have := h1.trans hXN
    linarith
  have hgoalX : (N : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) * ((band d).scale E N (v N) ^ n)⁻¹
      = (N : ℝ) ^ ε * (Λ ^ ((1 : ℝ) / 2) + Φ) * X := by rw [hX, inv_pow]
  rw [hgoalX]
  have hW1 : (1 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.one_le_rpow (by exact_mod_cast d.W_pos N) hτ'
  have hKd0 : (0 : ℝ) ≤ 4 * (4 * (d.W N : ℝ) ^ τ') := by linarith
  set G := 1 + (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1) with hG
  have hG0 : 0 ≤ G := by rw [hG]; have := cTwo52_pos; positivity
  have hcS0 := cKerSumZero_nonneg n
  have hcE0 : 0 ≤ cKerSumZeroErr n := by unfold cKerSumZeroErr; have := cTwo52_pos; positivity
  have hc := cTwo52_pos
  -- initial datum
  have hκ00 : 0 ≤ kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N) :=
    kapQ_nonneg (d.three_le_L N) hKd0 u (by rw [hu00]; exact hs0) (by rw [hu00]; linarith)
      (by rw [huK]; linarith) (by rw [huK]; exact hv1)
  have hκeq := kapQ_mul_scale_pow_eq d hE N n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
    (by rw [hu00]; exact hs0) (by rw [hu00]; linarith) (by rw [huK]; linarith)
    (by rw [huK]; exact hv1)
  rw [huK, hu00] at hκeq
  have hκmax := kapQ_le_max d hE N n hKd0 u 0 (K N) (by rw [hu00]; exact hs0)
    (by rw [hu00]; linarith) (by rw [huK]; linarith) (by rw [huK]; exact hv1)
    (by rw [huK]; exact hAv)
  rw [hu00] at hκmax
  have hAs : (band d).scale E N (s N) ≤ N := (scale_le_LW d hE N hs0 (hsv.trans hv1)).trans hLW
  have hAs0 : 0 < (band d).scale E N (s N) := (band d).scale_pos' hE N hs0 (hsv.trans hv1)
  have hκmax' : kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
      ≤ cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n) * (N : ℝ) ^ n :=
    hκmax.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hAs0.le hAs n) (by positivity))
  have T1 : kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N) * S0
      ≤ (N : ℝ) ^ ε / 16 * X + Tn := by
    have hNε1 : 0 ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
    have h1 : kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N) * S0
        ≤ kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
            * (G * ((N : ℝ) ^ ε₁ * ((band d).scale E N (s N))⁻¹ ^ n))
          + kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
            * ((2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')) := by
      have := mul_le_mul_of_nonneg_left (hS0.trans (add_le_add
        (mul_le_mul_of_nonneg_left hX0 hG0) le_rfl)) hκ00
      linarith
    have h2 : kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
          * (G * ((N : ℝ) ^ ε₁ * ((band d).scale E N (s N))⁻¹ ^ n))
        = G * (N : ℝ) ^ ε₁ * (kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
            * ((band d).scale E N (s N))⁻¹ ^ n) := by ring
    rw [h2, hκeq] at h1
    have h3 : G * (N : ℝ) ^ ε₁ * (cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n)
        * ((band d).scale E N (v N))⁻¹ ^ n) ≤ (N : ℝ) ^ ε / 16 * X := by
      have e : G * (N : ℝ) ^ ε₁ * (cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n)
          * ((band d).scale E N (v N))⁻¹ ^ n)
          = (cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n) * G * (N : ℝ) ^ ε₁) * X := by
        rw [hX]; ring
      rw [e]; exact mul_le_mul_of_nonneg_right ha1 hX0'
    have h4 : kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u 0 (K N)
          * ((2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D')) ≤ Tn := by
      refine le_trans ?_ ht1
      have : 0 ≤ (2 * cTwo52) ^ (m + 1) * (d.L N : ℝ) ^ (m + 1) * (d.W N : ℝ) ^ (-D') := by
        have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
        positivity
      exact mul_le_mul_of_nonneg_right hκmax' this
    linarith
  -- initial decay error
  have T2 : epsQ (d.L N) n u 0 (K N)
        * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
            (MD514 d E N n (CK + 1) (u 0)) ((d.W N : ℝ) ^ (-D')) ≤ Tn := by
    refine le_trans ?_ ht2
    have he := epsQ_le (L := d.L N) (n := n) u (by rw [hu00]; exact hs0) (by rw [hu00]; linarith)
      (by rw [huK]; exact hv1) (by simpa only [huK] using (inv_eta_le_of hE hv1 hη le_rfl).2)
    have he0 := epsQ_nonneg (d.L N) n u (i := 0) (by rw [hu00]; linarith) (by rw [huK]; exact hv1)
    have hMD : MD514 d E N n (CK + 1) (u 0) ≤ (N : ℝ) + (N : ℝ) ^ n + CK + 1 := by
      unfold MD514
      have hη0 := (inv_eta_le_of hE hv1 hη (show u 0 ≤ v N by rw [hu00]; exact hsv.le)).1
      have : (etaT E (u 0))⁻¹ ^ n ≤ (N : ℝ) ^ n :=
        pow_le_pow_left₀ (inv_nonneg.2 (etaT_pos hE (by rw [hu00]; linarith)).le) hη0 n
      linarith
    have hMD0 : 0 ≤ MD514 d E N n (CK + 1) (u 0) := by
      unfold MD514; have := etaT_pos hE (show u 0 < 1 by rw [hu00]; linarith); positivity
    have hdq : deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') (MD514 d E N n (CK + 1) (u 0))
        ((d.W N : ℝ) ^ (-D'))
        ≤ deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') ((N : ℝ) + (N : ℝ) ^ n + CK + 1)
          ((d.W N : ℝ) ^ (-D')) := by
      unfold deltaQop
      have : 0 ≤ (6 * Real.exp 1 * cTwo52 * (4 * (d.W N : ℝ) ^ τ')) ^ (m + 1) := by positivity
      have h0 : 0 ≤ Real.exp (-(cZero * (4 * (d.W N : ℝ) ^ τ') / 2)) := (Real.exp_pos _).le
      gcongr
    have hdq0 : 0 ≤ deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ') ((N : ℝ) + (N : ℝ) ^ n + CK + 1)
        ((d.W N : ℝ) ^ (-D')) :=
      deltaQop_nonneg (d.L N) (by linarith) (by positivity) (Real.rpow_nonneg (by positivity) _)
    calc epsQ (d.L N) n u 0 (K N) * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
          (MD514 d E N n (CK + 1) (u 0)) ((d.W N : ℝ) ^ (-D'))
        ≤ epsQ (d.L N) n u 0 (K N) * deltaQop (d.L N) (m + 1) (4 * (d.W N : ℝ) ^ τ')
          ((N : ℝ) + (N : ℝ) ^ n + CK + 1) ((d.W N : ℝ) ^ (-D')) :=
          mul_le_mul_of_nonneg_left hdq he0
      _ ≤ _ := mul_le_mul_of_nonneg_right he hdq0
  -- drift
  have t3 := tb_driftQ d (m := m) hE s v K N hs0 hsv hv1 hK1 hη hA hLW hN1 hW hL (ε₁ := ε₁)
    (τ' := τ') (D' := D') hτ' hΦ hCK hCKN
  have hMc0 := McQ_nonneg d N m (ε₁ := ε₁) (τ' := τ') hCK
  have T3 : Δ * ∑ j ∈ Finset.range (K N),
          (kapQ (d.L N) n (4 * (4 * (d.W N : ℝ) ^ τ')) u (j + 1) (K N)
              * dDrQ d E N m (u j) ε₁ τ' D' Φ CK
                  (MD514 d E N n (CK + 1) (u j) * (band d).scale E N (u j) ^ n)
                  (CK + 1) (MD514 d E N n (CK + 1) (u j))
            + epsQ (d.L N) n u (j + 1) (K N)
              * δDQ d E N m (u j) τ' D' (CK + 1) (MD514 d E N n (CK + 1) (u j)) (CK + 1))
      ≤ (N : ℝ) ^ ε / 16 * Φ * X + (1 + Φ) * Tn := by
    refine t3.trans ?_
    have h1 : cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n) * McQ d N m ε₁ τ' CK * Φ * X
          * ∑ j ∈ Finset.range (K N), Δ / etaT E (u j)
        ≤ (N : ℝ) ^ ε / 16 * Φ * X := by
      have h0 : 0 ≤ cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n) * McQ d N m ε₁ τ' CK := by
        positivity
      have := mul_le_mul_of_nonneg_left hlog h0
      have e : cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n) * McQ d N m ε₁ τ' CK * Φ * X
            * ∑ j ∈ Finset.range (K N), Δ / etaT E (u j)
          = (cKerSumZero n * (4 * (4 * (d.W N : ℝ) ^ τ')) ^ (2 * n) * McQ d N m ε₁ τ' CK
            * ∑ j ∈ Finset.range (K N), Δ / etaT E (u j)) * (Φ * X) := by ring
      rw [e]
      have h2 := this.trans ha2
      calc _ ≤ (N : ℝ) ^ ε / 16 * (Φ * X) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring
    linarith
  -- QV
  have t4 := tb_qvQ d (m := m) hE s v K N hs0 hsv hv1 hK1 hη hA hLW (τ' := τ') (D'' := D' - 1)
    (Φq := 2 * (N : ℝ) ^ ε₁ * Λ) hτ' (by positivity) a
  have hSv : ∑ j ∈ Finset.range (K N), Δ / etaT E (u j) + Δ / etaT E (v N)
      ≤ (mE E).im⁻¹ * Real.log N + 1 := by
    have hv := etaT_pos hE hv1
    have : Δ / etaT E (v N) ≤ 1 := by
      rw [div_eq_mul_inv]
      have h1 : Δ * (etaT E (v N))⁻¹ ≤ Δ * N := mul_le_mul_of_nonneg_left hη hΔ0
      nlinarith
    linarith
  have hQm0 : 0 ≤ QVmain d E N m ε₁ τ' := by
    unfold QVmain
    have := cKerSumZero_nonneg ((m + 1 + 1) + (m + 1 + 1))
    have := qqCoefE_nonneg (d.L N) (m + 1) (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) τ')
    have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
    have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    have hl : 0 ≤ (mE E).im⁻¹ * Real.log N + 1 := by
      have := Real.log_nonneg hN1
      have := (mE_im_pos hE).le
      positivity
    positivity
  have hQt0 : 0 ≤ QVtail d N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) := by
    unfold QVtail
    have := cKerSumZero_nonneg ((m + 1 + 1) + (m + 1 + 1))
    have hw0 : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
    have := qqCoefE_nonneg (d.L N) (m + 1) hw0
    have := qqCoefD_nonneg (d.L N) (m + 1) hw0
    have hee := eeHermErr_nonneg d N (m + 1 + 1) (D' - 1)
    have heb : 0 ≤ eeBd d N (m + 1 + 1) (2 * (N : ℝ) ^ ε₁ * Λ) ((d.W N : ℝ) ^ τ') (D' - 1) := by
      unfold eeBd
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-(D' - 1)) := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ Λ := by linarith
      positivity
    have := FastDecayFlow.qqErrBd_nonneg (d.L N) (m + 1) hw0 heb hee
    have : 0 < cKerSumZeroErr ((m + 1 + 1) + (m + 1 + 1)) := by
      unfold cKerSumZeroErr; positivity
    positivity
  have hsum : ∑ j ∈ Finset.range (K N),
        (cQVQ d E s v K N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ)
      ≤ QVmain d E N m ε₁ τ' * Λ * X ^ 2 + QVtail d N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) := by
    refine t4.trans ?_
    have hX2 : ((band d).scale E N (v N))⁻¹ ^ (2 * (m + 1 + 1)) = X ^ 2 := by
      rw [hX, ← pow_mul, mul_comm]
    rw [hX2]
    unfold QVmain QVtail
    have hcoef0 : 0 ≤ cKerSumZero ((m + 1 + 1) + (m + 1 + 1)) * (4 * (d.W N : ℝ) ^ τ') ^ (2 * ((m + 1 + 1)
          + (m + 1 + 1))) * qqCoefE (d.L N) (m + 1) ((d.W N : ℝ) ^ τ')
        * (6 * Real.exp 1 * ((m + 1 + 1 : ℕ) : ℝ) ^ 2 * (d.W N : ℝ) ^ τ' * (2 * (N : ℝ) ^ ε₁ * Λ))
        * X ^ 2 := by
      have := cKerSumZero_nonneg ((m + 1 + 1) + (m + 1 + 1))
      have := qqCoefE_nonneg (d.L N) (m + 1) (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (d.W N)) τ')
      have : (0 : ℝ) ≤ (d.W N : ℝ) ^ τ' := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ Λ := by linarith
      positivity
    have := mul_le_mul_of_nonneg_left hSv hcoef0
    nlinarith
  have T4 : (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range (K N),
        (cQVQ d E s v K N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ))
      ≤ (N : ℝ) ^ ε / 16 * Λ ^ ((1 : ℝ) / 2) * X + Λ ^ ((1 : ℝ) / 2) * (X / 64) := by
    have hNe1 : (0 : ℝ) ≤ (N : ℝ) ^ ε₁ := Real.rpow_nonneg (by positivity) _
    have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
    have hs1 := Real.sqrt_le_sqrt (hsum.trans (add_le_add le_rfl ht4))
    have hs2 : Real.sqrt (QVmain d E N m ε₁ τ' * Λ * X ^ 2 + Λ * Tn)
        ≤ Real.sqrt (QVmain d E N m ε₁ τ') * Real.sqrt Λ * X + Real.sqrt Λ * Real.sqrt Tn := by
      have hZΛ : 0 ≤ QVmain d E N m ε₁ τ' * Λ * X ^ 2 := by positivity
      refine (sqrt_add_le514 hZΛ (by positivity)).trans ?_
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ QVmain d E N m ε₁ τ' * Λ), Real.sqrt_mul hQm0,
        Real.sqrt_sq hX0', Real.sqrt_mul hΛ0]
    have hsΛ : Real.sqrt Λ = Λ ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Λ
    have hsTn : Real.sqrt Tn = ((N : ℝ) ^ (n + 1))⁻¹ / 64 := by
      rw [hTn, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
      rw [show 2 * n + 2 = (n + 1) + (n + 1) by ring, pow_add]
      field_simp
      ring
    have hNε1 : (N : ℝ) ^ ε₁ ≤ N := by
      calc (N : ℝ) ^ ε₁ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hε₁1
        _ = N := Real.rpow_one _
    have hk2 : (N : ℝ) ^ ε₁ * (((N : ℝ) ^ (n + 1))⁻¹ / 64) ≤ X / 64 := by
      have e : ((N : ℝ) ^ (n + 1))⁻¹ = (N : ℝ)⁻¹ ^ n * (N : ℝ)⁻¹ := by
        rw [inv_pow, pow_succ, mul_inv]
      rw [e]
      have h1 : (N : ℝ) ^ ε₁ * (N : ℝ)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hN0]; exact hNε1
      have h2 : 0 ≤ (N : ℝ)⁻¹ ^ n := by positivity
      calc (N : ℝ) ^ ε₁ * ((N : ℝ)⁻¹ ^ n * (N : ℝ)⁻¹ / 64)
          = ((N : ℝ) ^ ε₁ * (N : ℝ)⁻¹) * (N : ℝ)⁻¹ ^ n / 64 := by ring
        _ ≤ 1 * (N : ℝ)⁻¹ ^ n / 64 := by gcongr
        _ ≤ X / 64 := by linarith
    have k1 : (N : ℝ) ^ ε₁ * (Real.sqrt (QVmain d E N m ε₁ τ') * Real.sqrt Λ * X)
        ≤ (N : ℝ) ^ ε / 16 * Λ ^ ((1 : ℝ) / 2) * X := by
      have e : (N : ℝ) ^ ε₁ * (Real.sqrt (QVmain d E N m ε₁ τ') * Real.sqrt Λ * X)
          = ((N : ℝ) ^ ε₁ * Real.sqrt (QVmain d E N m ε₁ τ')) * (Λ ^ ((1 : ℝ) / 2) * X) := by
        rw [hsΛ]; ring
      rw [e]
      have := mul_le_mul_of_nonneg_right ha3 (by positivity : (0 : ℝ) ≤ Λ ^ ((1 : ℝ) / 2) * X)
      calc _ ≤ (N : ℝ) ^ ε / 16 * (Λ ^ ((1 : ℝ) / 2) * X) := this
        _ = _ := by ring
    have k2 : (N : ℝ) ^ ε₁ * (Real.sqrt Λ * Real.sqrt Tn) ≤ Λ ^ ((1 : ℝ) / 2) * (X / 64) := by
      rw [hsΛ, hsTn]
      have := mul_le_mul_of_nonneg_left hk2 (by positivity : (0 : ℝ) ≤ Λ ^ ((1 : ℝ) / 2))
      calc (N : ℝ) ^ ε₁ * (Λ ^ ((1 : ℝ) / 2) * (((N : ℝ) ^ (n + 1))⁻¹ / 64))
          = Λ ^ ((1 : ℝ) / 2) * ((N : ℝ) ^ ε₁ * (((N : ℝ) ^ (n + 1))⁻¹ / 64)) := by ring
        _ ≤ _ := this
    calc (N : ℝ) ^ ε₁ * Real.sqrt (∑ j ∈ Finset.range (K N),
          (cQVQ d E s v K N m τ' (D' - 1) (2 * (N : ℝ) ^ ε₁ * Λ) (K N) a j : ℝ))
        ≤ (N : ℝ) ^ ε₁ * (Real.sqrt (QVmain d E N m ε₁ τ') * Real.sqrt Λ * X
            + Real.sqrt Λ * Real.sqrt Tn) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe1
      _ = (N : ℝ) ^ ε₁ * (Real.sqrt (QVmain d E N m ε₁ τ') * Real.sqrt Λ * X)
          + (N : ℝ) ^ ε₁ * (Real.sqrt Λ * Real.sqrt Tn) := by ring
      _ ≤ _ := add_le_add k1 k2
  -- remainder
  have t6 := tb_RQ d (m := m) hE s v K N hs0 hsv hv1 hK1 hη hW hL hcard hN1 hCK
    (by linarith) hΔN
  -- endpoint correction
  have T7 : cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m
          * ((band d).scale E N (v N))⁻¹ ^ (m + 2) * XiK
        + (cTwo52 / (band d).ell N (v N)) ^ (m + 1)
          * (((d.W N : ℝ) * etaT E (v N))⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
      ≤ (N : ℝ) ^ ε / 16 * Φ * X + Tn := by
    have h1 : cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m
          * ((band d).scale E N (v N))⁻¹ ^ (m + 2) * XiK
        ≤ (N : ℝ) ^ ε / 16 * Φ * X := by
      have h0 : 0 ≤ cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * X := by
        positivity
      have := mul_le_mul_of_nonneg_left hXi h0
      have e : cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m
          * ((band d).scale E N (v N))⁻¹ ^ (m + 2) * XiK
          = cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * X * XiK := by
        rw [hX]
      rw [e]
      refine this.trans ?_
      have e2 : cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * X
          * ((N : ℝ) ^ ε₁ * Φ)
          = (cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * (N : ℝ) ^ ε₁)
            * (Φ * X) := by ring
      rw [e2]
      calc _ ≤ (N : ℝ) ^ ε / 16 * (Φ * X) := mul_le_mul_of_nonneg_right ha4 (by positivity)
        _ = _ := by ring
    have h2 : (cTwo52 / (band d).ell N (v N)) ^ (m + 1)
          * (((d.W N : ℝ) * etaT E (v N))⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D')) ≤ Tn := by
      refine le_trans ?_ ht7
      have hℓ1 : 1 ≤ (band d).ell N (v N) :=
        one_le_ellHat (d.L N) (d.three_le_L N) (hs0.trans hsv.le) hv1
      have hcl : (cTwo52 / (band d).ell N (v N)) ^ (m + 1) ≤ cTwo52 ^ (m + 1) :=
        FastDecayFlow.cTwo52_div_pow_le (m + 1) hℓ1
      have hW1' : (1 : ℝ) ≤ d.W N := by exact_mod_cast d.W_pos N
      have hηv := etaT_pos hE hv1
      have hWη : ((d.W N : ℝ) * etaT E (v N))⁻¹ ≤ N := by
        rw [mul_inv]
        have : (d.W N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1'
        have h0 : 0 ≤ (etaT E (v N))⁻¹ := by positivity
        nlinarith
      have hLm : (d.L N : ℝ) ^ m ≤ (N : ℝ) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hL m
      have hWD : (0 : ℝ) ≤ (d.W N : ℝ) ^ (-D') := Real.rpow_nonneg (by positivity) _
      have hp : 0 ≤ (cTwo52 / (band d).ell N (v N)) ^ (m + 1) := by
        have : 0 < (band d).ell N (v N) := by linarith
        positivity
      gcongr
    linarith
  -- total
  set Λh := Λ ^ ((1 : ℝ) / 2) with hΛh
  have hΦX : 0 ≤ Φ * X := by positivity
  have hX1 : X ≤ Λh * X := le_mul_of_one_le_left hX0' hsqΛ
  have hT6 : ∑ j ∈ Finset.range (K N), (1 + (1 - u (K N))⁻¹) ^ n
      * qErrQ d E s v K N m (CK + 1) j ≤ Tn := t6.trans ht6
  have T7' : cTwo52 ^ (m + 1) * (4 * Real.exp 1) ^ m * ((d.W N : ℝ) ^ τ') ^ m * X * XiK
        + (cTwo52 / (band d).ell N (v N)) ^ (m + 1)
          * (((d.W N : ℝ) * etaT E (v N))⁻¹ * (d.L N : ℝ) ^ m * (d.W N : ℝ) ^ (-D'))
      ≤ (N : ℝ) ^ ε / 16 * Φ * X + Tn := T7
  have hA1 : X ≤ (N : ℝ) ^ ε * X := le_mul_of_one_le_left hX0' hNe
  have hB1 : Φ * X ≤ (N : ℝ) ^ ε * (Φ * X) := le_mul_of_one_le_left hΦX hNe
  have hC1 : Λh * X ≤ (N : ℝ) ^ ε * (Λh * X) := le_mul_of_one_le_left (by positivity) hNe
  have hAC : (N : ℝ) ^ ε * X ≤ (N : ℝ) ^ ε * (Λh * X) := mul_le_mul_of_nonneg_left hX1 hNe0
  have hΦTn : Φ * Tn ≤ Φ * X / 4096 := by
    have := mul_le_mul_of_nonneg_left hTnX hΦ; linarith
  have e1 : (N : ℝ) ^ ε / 16 * X = (N : ℝ) ^ ε * X / 16 := by ring
  have e3 : (N : ℝ) ^ ε / 16 * Φ * X = (N : ℝ) ^ ε * (Φ * X) / 16 := by ring
  have e4 : (N : ℝ) ^ ε / 16 * Λh * X = (N : ℝ) ^ ε * (Λh * X) / 16 := by ring
  have e5 : Λh * (X / 64) = Λh * X / 64 := by ring
  have e6 : (1 + Φ) * Tn = Tn + Φ * Tn := by ring
  have eG : (N : ℝ) ^ ε * (Λh + Φ) * X = (N : ℝ) ^ ε * (Λh * X) + (N : ℝ) ^ ε * (Φ * X) := by ring
  rw [e1] at T1
  rw [e3, e6] at T3
  rw [e4, e5] at T4
  rw [e3] at T7'
  rw [eG]
  linarith [T1, T2, T3, T4, T7', ht5, hT6, hX1, hA1, hB1, hC1, hAC, hΦTn, hTnX]

end BudgetFinal

section EndpointQ

variable (d : Dims)

/-- The two alternating charges, as a predicate. -/
def IsAltQ (m : ℕ) (σ : Fin (m + 2) → Bool) : Prop := σ = sigmaAltGen (m + 2) ∨ σ = sigmaAltGen' (m + 2)

instance (m : ℕ) : DecidablePred (IsAltQ m) := fun σ => by unfold IsAltQ; infer_instance

theorem IsAltQ.nonconst {m : ℕ} {σ : Fin (m + 2) → Bool} (h : IsAltQ m σ) : ∃ i j, σ i ≠ σ j := by
  have : NeZero (m + 2) := ⟨by omega⟩
  rcases h with h | h <;> rw [h]
  · exact sigmaAltGen_nonconst (by omega)
  · exact sigmaAltGen'_nonconst (by omega)

end EndpointQ

section CorollariesQ

variable (d : Dims)

end CorollariesQ

section WitnessQ

variable (d : Dims)

end WitnessQ

end RBM.Gauss.Grid

end

