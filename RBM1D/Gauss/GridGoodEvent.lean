/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.GridGoodSet
import RBM1D.Gauss.GridExpansion
import RBM1D.Gauss.GridQVForm
import RBM1D.Gauss.GridQVStep
import RBM1D.Gauss.GridQVSum
import RBM1D.Gauss.GridDuhamelTail
import RBM1D.Gauss.GridNetLift

/-!
# The grid stopping time and the good event

Fixed data: `d : Dims`, an energy `E`, times `s ≤ u ≤ t < 1` (`u` is the grid endpoint sequence),
a grid size `K`, `u_j := time s u K N j`, `Δ := step s u K N`, the threshold
`thr(v) := Step2.thr E s δ N v = N^δ (η_s/η_v)^4`, and the good set
`G(v) := goodSet d E N v ℓ_s τ₁ ε ζCtr τ3 τ57 D` of `GridGoodSet.lean` with
`ℓ_s := (band d).ell N (s N)`.

## Main results

* `gridTau`, `lt_gridTau_measurableSet`, `lt_gridTau_imp`, `gridTau_le`: the grid stopping time
  `τ = min (firstHit (jSMat(u_j,H_j) − thr(u_j)) 0 K) (firstHit (1_{G(u_j)ᶜ}(H_j)) (1/2) K)`.
* `Qprime`, `cZ`, `cZ_nonneg`, `floor_le_cZ`: the explicit Azuma constants `cZ` for `Z := Zvec`
  and `τ := gridTau` (positive floor `Δ N^{-C_c}` included), built from `Qprime` (the rate of
  `GridQVStep.lean` at `J = N^{2ε} thr(u_j)`, via `Qd`).  Glue lemmas: `ukerMat_eq_prod_re`,
  `quadVar_Φgrid_eq`, `jGMat_nonneg`, `time_succ_eq`, `time_mono_of_le`.
* `xZ`, `xZ_pos`, `xZ_sq`, `azumaMm`: the Azuma threshold
  `xZ k a = N^{δ/16} √(4 Σ_{j<k} cZ k a j + N^{-C_x})` (floor inside the root) and the constant
  `Mm = azumaMm` of the bound `xZ k a ≤ Mm (R_k²+1) T_{u_k}(a)`.  With the threshold `x 0 a = 0`
  the Azuma event would read `‖0‖ < 0`; the floor inside the root avoids this.
* `CK`, `gridK`: the grid `gridK D D₁ = ⌈N^{C_K}⌉` with `C_K = CK D D₁ = D₁ + 2D + 80`.
* `initSet`, `goodEventGrid`: the initial-value set and the good event on the grid.
-/

noncomputable section

namespace RBM.Gauss.Grid

open MeasureTheory ProbabilityTheory Filter Matrix RBM
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable (d : Dims)

/-! ## (T1) : the grid stopping time -/

section T1

/-- **`gridTau`**: the first grid index at which either `J*` reaches the time-dependent
threshold, `jSMat(u_j, H_j) ≥ thr(u_j)`, or the grid state leaves the good set, `H_j ∉ G(u_j)`
(`K N` if neither happens). -/
def gridTau (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) : ℕ :=
  min (firstHit (fun j (ω : Ωg d) => jSMat d E D N (time s u K N j) (H d s u K N j ω)
      - Step2.thr E s δ N (time s u K N j)) 0 (K N) ω)
    (firstHit (fun j (ω : Ωg d) =>
      (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
        (fun _ => (1 : ℝ)) (H d s u K N j ω)) (1 / 2) (K N) ω)

variable {d}

private theorem measurable_tauJ (E D δ : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      jSMat d E D N (time s u K N j) M - Step2.thr E s δ N (time s u K N j)) :=
  (measurable_jSMat d E D N _).sub measurable_const

private theorem measurable_tauG {E : ℝ} (hE : |E| < 2) (τ₁ ε ζCtr τ3 τ57 D : ℝ) (s u : ℕ → ℝ)
    (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    Measurable (fun M : Matrix (d.Idx N) (d.Idx N) ℂ =>
      (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
        (fun _ => (1 : ℝ)) M) :=
  measurable_const.indicator (measurableSet_goodSet d E N _ _ τ₁ ε ζCtr τ3 τ57 D hE).compl

/-- `{j < gridTau}` is `filt d j`-measurable. -/
theorem lt_gridTau_measurableSet {E : ℝ} (hE : |E| < 2) (D δ τ₁ ε ζCtr τ3 τ57 : ℝ)
    (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (j : ℕ) :
    MeasurableSet[filt d j] {ω | j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω} :=
  lt_min_firstHit_grid_measurableSet d s u K N
    (F := fun j M => jSMat d E D N (time s u K N j) M - Step2.thr E s δ N (time s u K N j))
    (F' := fun j M => (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57
      D)ᶜ.indicator (fun _ => (1 : ℝ)) M)
    (measurable_tauJ E D δ s u K N) (measurable_tauG hE τ₁ ε ζCtr τ3 τ57 D s u K N) 0 (1 / 2)
    (K N) j

/-- **(T1)** Strictly before `gridTau`, `J*` is below the threshold and the grid state is in the
good set. -/
theorem lt_gridTau_imp {E D δ τ₁ ε ζCtr τ3 τ57 : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ}
    {ω : Ωg d} (h : j < gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω) :
    jSMat d E D N (time s u K N j) (H d s u K N j ω) < Step2.thr E s δ N (time s u K N j) ∧
      H d s u K N j ω ∈
        goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D := by
  obtain ⟨h1, h2⟩ := lt_min_firstHit_imp _ _ _ _ _ h
  refine ⟨by linarith, ?_⟩
  by_contra hmem
  have h2' : (goodSet d E N (time s u K N j) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D)ᶜ.indicator
      (fun _ => (1 : ℝ)) (H d s u K N j ω) < 1 / 2 := h2
  rw [Set.indicator_of_mem (Set.mem_compl hmem)] at h2'
  norm_num at h2'

/-- `gridTau ≤ K N`. -/
theorem gridTau_le (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N : ℕ) (ω : Ωg d) :
    gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω ≤ K N :=
  (min_le_left _ _).trans (firstHit_le _ _ _ ω)

end T1

/-! ## Counterexample: the Azuma threshold without a floor -/

section T3

variable {d}

end T3


/-! ## (T5) : the initial value on the grid -/

section T5

variable {d}

private theorem ofFn_pm_eq_pmLoop {L : ℕ} (b : LoopArg L 2) :
    (⟨[true, false], List.ofFn b⟩ : LoopIdx (ZMod L)) = pmLoop (b 0) (b 1) := by
  simp [pmLoop, List.ofFn_succ]

private theorem Lval_band_eq (E : ℝ) (N : ℕ) (v : ℝ) (M : Matrix (d.Idx N) (d.Idx N) ℂ)
    (b : LoopArg (d.L N) 2) :
    Lval (band d) E N v M b = gloop (d.L N) (d.W N) M (zt E v) (pmLoop (b 0) (b 1)) := by
  change gloop (d.L N) (d.W N) M (zt E v) ⟨[true, false], List.ofFn b⟩ = _
  rw [ofFn_pm_eq_pmLoop]

private theorem Kv_band_eq (E : ℝ) (N : ℕ) (v : ℝ) (b : LoopArg (d.L N) 2) :
    Kv (band d) E N v b = (band d).Kval E N v (pmLoop (b 0) (b 1)) := by
  unfold Kv pmLoop
  congr 2

/-- The matrix set of the initial bound at time `v`, with multiplier `x`. -/
def initSet (E : ℝ) (N : ℕ) (v D x : ℝ) : Set (Matrix (d.Idx N) (d.Idx N) ℂ) :=
  {M | ∀ b : LoopArg (d.L N) 2, ‖Lval (band d) E N v M b - Kv (band d) E N v b‖ ≤
    x * Step2.tT (band d) E N D v (zdist (d.L N) (b 0 - b 1))}

theorem measurableSet_initSet (E : ℝ) (N : ℕ) (v D x : ℝ) :
    MeasurableSet (initSet (d := d) E N v D x) := by
  have heq : initSet (d := d) E N v D x = ⋂ b : LoopArg (d.L N) 2,
      {M | ‖Lval (band d) E N v M b - Kv (band d) E N v b‖ ≤
        x * Step2.tT (band d) E N D v (zdist (d.L N) (b 0 - b 1))} := by
    exact Set.ofPred_forall _
  rw [heq]
  refine MeasurableSet.iInter fun b => measurableSet_le ?_ measurable_const
  exact ((measurable_gloop_matrix d N (zt E v) _).sub measurable_const).norm

/-- On `initSet … x`, `jSMat ≤ x + 1`. -/
theorem jSMat_le_of_mem_initSet {E : ℝ} {N : ℕ} {v D x : ℝ}
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M ∈ initSet (d := d) E N v D x) :
    jSMat d E D N v M ≤ x + 1 := by
  have hW : (0 : ℝ) < (d.W N : ℝ) := by exact_mod_cast d.W_pos N
  unfold jSMat Step2.jStar
  refine add_le_add (Finset.sup'_le _ _ fun a _ => ?_) le_rfl
  have hT := tailT_pos (ℓu := (band d).ell N v) (ηu := etaT E v) (D := D) hW
    (zdist (d.L N) (a 0 - a 1) : ℝ)
  rw [div_le_iff₀ hT]
  have ha := hM a
  rw [Lval_band_eq, Kv_band_eq] at ha
  dsimp only
  rw [Step2.idx_sigPM]
  exact ha

end T5


/-! ## (T2) : the Azuma constants for `Zvec` and `gridTau` -/

section T2

variable {d}

/-- `u_{j+1} = u_j + Δ`. -/
theorem time_succ_eq (s u : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ) :
    time s u K N (j + 1) = time s u K N j + step s u K N := by
  unfold time; push_cast; ring

/-- The real kernel entry of `ukerMat` is the product of `edgeKer` entries (the private
`Uker_one_single`, re-proved). -/
theorem ukerMat_eq_prod_re (L : ℕ) [NeZero L] (v w : ℝ) (b a : LoopArg L 2) :
    ukerMat L v w b a = (∏ i : Fin 2, edgeKer L 1 (v : ℂ) (w : ℂ) (b i) (a i)).re := by
  classical
  unfold ukerMat
  congr 1
  rw [Uker_apply]
  have hterm : ∀ c : LoopArg L 2,
      (∏ i : Fin 2, edgeKer L ((fun _ => (1 : ℂ)) i) (v : ℂ) (w : ℂ) (b i) (c i))
          * (Pi.single a (1 : ℂ) : LoopArg L 2 → ℂ) c
        = if c = a then ∏ i : Fin 2, edgeKer L 1 (v : ℂ) (w : ℂ) (b i) (a i) else 0 := by
    intro c
    by_cases h : c = a
    · subst h; simp
    · simp [h]
  simp_rw [hterm]
  simp

private theorem quadVar_Φgrid_eq_aux {Ω' : Type*} [MeasurableSpace Ω'] (B : Band Ω') {E : ℝ}
    (hE : |E| < 2) (N : ℕ) {w : ℝ} (hw1 : w < 1) (a : LoopArg (B.L N) 2)
    {M : Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ} (hM : M.IsHermitian) :
    Gauss.quadVar B.toDims N (Φgrid B E N w a) M
      = Gauss.quadVar B.toDims N
          (fun M' => MomentDuhamel.lkFun B E N w M' Step2.sigPM a) M := by
  have hz : (zt E w).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hw1
  have h := EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs (B := B) hz Step2.sigPM hM a
  refine Eq.trans ?_ h.symm
  have hidx : (toIdx (L := B.toDims.L N) Step2.sigPM a : LoopIdx (ZMod (B.toDims.L N)))
      = (⟨[true, false], List.ofFn (n := 2) (α := ZMod (B.toDims.L N)) a⟩ :
          LoopIdx (ZMod (B.toDims.L N))) := by
    change LoopData.idx (Step2.sigPM, a) = _
    rw [Step2.idx_sigPM]
    exact (ofFn_pm_eq_pmLoop a).symm
  rw [hidx]
  unfold Gauss.quadVar coordD1
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfd : fderiv ℝ (Φgrid B E N w a) M
      = fderiv ℝ (loopObs B.toDims N (zt E w)
          (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N)))) M := by
    unfold Φgrid
    exact fderiv_sub_const (𝕜 := ℝ)
      (f := (loopObs B.toDims N (zt E w)
        (⟨[true, false], List.ofFn a⟩ : LoopIdx (ZMod (B.L N))) :
          Matrix (B.toDims.Idx N) (B.toDims.Idx N) ℂ → ℂ)) (x := M) (Kv B E N w a)
  rw [hfd]
  rfl

/-- The quadratic variation of `Φgrid` is that of `lkFun`, at Hermitian `M`: `Φgrid = loopObs − Kv`
has the derivative of `loopObs`, which agrees with that of `lkFun` on the used coordinates
(`EarlyQVRate.quadVar_lkFun_eq_quadVar_loopObs`). -/
theorem quadVar_Φgrid_eq {E : ℝ} (hE : |E| < 2) (N : ℕ) {w : ℝ} (hw1 : w < 1)
    (a : LoopArg (d.L N) 2) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    Gauss.quadVar d N (Φgrid (band d) E N w a) M
      = Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun (band d) E N w M' Step2.sigPM a) M :=
  quadVar_Φgrid_eq_aux (band d) hE N hw1 a hM

/-- `0 ≤ jGMat` once `ℓ_u > 0` and `W ≥ 3` (the `(0,0)` term of the supremum is `0`). -/
theorem jGMat_nonneg (E : ℝ) (N : ℕ) (u : ℝ) {ℓu ηu D : ℝ} (hℓu : 0 < ℓu)
    (hW3 : 3 ≤ d.W N) (M : Matrix (d.Idx N) (d.Idx N) ℂ) :
    0 ≤ jGMat d E N u ℓu ηu D M := by
  have hW : (3 : ℝ) ≤ (d.W N : ℝ) := by exact_mod_cast hW3
  have hlog : 0 < Real.log (d.W N : ℝ) := Real.log_pos (by linarith)
  have hstar : 0 < ellStar (d.W N : ℝ) ℓu := by
    unfold ellStar; exact mul_pos (Real.rpow_pos_of_pos hlog _) hℓu
  have hif : ¬ (ellStar (d.W N : ℝ) ℓu / 2 ≤ (zdist (d.L N) ((0 : ZMod (d.L N)) - 0) : ℝ)) := by
    simp only [sub_self]
    have : (zdist (d.L N) (0 : ZMod (d.L N)) : ℝ) = 0 := by simp [zdist]
    rw [this]; linarith
  unfold jGMat
  refine add_nonneg zero_le_one ?_
  refine Finset.le_sup'_of_le _ (Finset.mem_univ ((0 : ZMod (d.L N)), (0 : ZMod (d.L N)))) ?_
  dsimp only
  rw [ite_eq_right_iff.mpr (fun h => absurd h hif)]

/-- `time` is monotone in the grid index when `s N ≤ u N`. -/
theorem time_mono_of_le {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ} (hsu : s N ≤ u N) {i i' : ℕ}
    (hii : i ≤ i') : time s u K N i ≤ time s u K N i' := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h : (i : ℝ) ≤ (i' : ℝ) := by exact_mod_cast hii
  unfold time
  nlinarith

variable (d) in
/-- **The rate `Q′_j`** of `quadVar_step_le`, at `J = qvJ E s δ ε N u_j = N^{2ε} thr(u_j)`
and `ℓ_s = (band d).ell N (s N)`, written through `Qd` (verbatim the same expression):
`Q′_j = 2 N^{τ₁} Qd(u_j) + 2 Csh(u_{j+1})² Δ² W^{2D}`. -/
def Qprime (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ ε D τ₁ : ℝ) (N j : ℕ) : ℝ :=
  2 * (N : ℝ) ^ τ₁ * Qd (band d) E s δ ε D N (time s u K N j)
    + 2 * qvTimeShiftConst d N E (time s u K N (j + 1)) ^ 2 * step s u K N ^ 2
        * ((band d).W N : ℝ) ^ (2 * D)

variable (d) in
/-- **The Azuma constants for `Zvec` and `gridTau`**:
`c k a j = Δ (√Q′_j ((1 − u_{j+1})/(1 − u_k))² xiK T_{u_k}(a))² + Δ N^{-C_c}`
(with the positive floor `Δ N^{-C_c}`). -/
def cZ (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ ε D τ₁ Cc : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) (j : ℕ) : ℝ :=
  step s u K N * (Real.sqrt (Qprime d E s u K δ ε D τ₁ N j)
      * ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2
      * Step2.xiK (d.L N) (d.W N) (mE E).im
      * Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))) ^ 2
    + step s u K N * (N : ℝ) ^ (-Cc)

theorem cZ_nonneg {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) (j : ℕ) :
    0 ≤ cZ d E s u K δ ε D τ₁ Cc N k a j := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold cZ
  have : 0 ≤ (N : ℝ) ^ (-Cc) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  positivity

/-- The positive floor: `Δ N^{-C_c} ≤ c k a j`, so `Σ_{j<k} c k a j ≥ k Δ N^{-C_c} > 0` for
`k ≥ 1` and `Δ > 0`. -/
theorem floor_le_cZ {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) (j : ℕ) :
    step s u K N * (N : ℝ) ^ (-Cc) ≤ cZ d E s u K δ ε D τ₁ Cc N k a j := by
  have hΔ0 : 0 ≤ step s u K N := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold cZ
  have : 0 ≤ step s u K N * (Real.sqrt (Qprime d E s u K δ ε D τ₁ N j)
      * ((1 - time s u K N (j + 1)) / (1 - time s u K N k)) ^ 2
      * Step2.xiK (d.L N) (d.W N) (mE E).im
      * Step2.tT (band d) E N D (time s u K N k) (zdist (d.L N) (a 0 - a 1))) ^ 2 := by
    positivity
  linarith

end T2

/-! ## The Azuma event, the Chebyshev bound at the random target, and the good event -/

section Amend

variable {d}

theorem measurable_coord_filt {k l : ℕ} (hl : l ≤ k) :
    Measurable[filt d k] (fun ω : Ωg d => ω l) := by
  have : (fun ω : Ωg d => ω l)
      = (fun g : Set.Iic k → Ω d => g ⟨l, hl⟩) ∘ (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k) :=
    rfl
  rw [this]
  exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Ω d) k))

theorem measurable_lin (N : ℕ) :
    Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ × Matrix (d.Idx N) (d.Idx N) ℂ =>
      lin N p.1 p.2) := by
  unfold lin
  have h : ∀ i k : d.Idx N, Measurable (fun p : Matrix (d.Idx N) (d.Idx N) ℂ ×
      Matrix (d.Idx N) (d.Idx N) ℂ => p.1 i k * p.2 k i) := fun i k =>
    (Measurable.eval_matrix (i := i) (j := k) measurable_fst).mul
      (Measurable.eval_matrix (i := k) (j := i) measurable_snd)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Complex.measurable_re.comp ?_
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => h i k

theorem measurable_stepZ_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Measurable[filt d (j + 1)] (fun ω => stepZ d s t K N j Φ U b ω) := by
  have hA : Measurable[filt d (j + 1)] (fun ω => Ab d s t K N j Φ U b ω) :=
    (measurable_Ab d s t K N j hΦ U b).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have hX : Measurable[filt d (j + 1)] (fun ω : Ωg d => Xmat d N (ω (j + 1))) :=
    (measurable_Xmat d N).comp (measurable_coord_filt le_rfl)
  have hP : Measurable[filt d (j + 1)] (fun ω : Ωg d =>
      (Ab d s t K N j Φ U b ω, Xmat d N (ω (j + 1)))) := hA.prodMk hX
  have hL := (measurable_lin (d := d) N).comp hP
  change Measurable[filt d (j + 1)] (fun ω : Ωg d => Real.sqrt (step s t K N) *
      lin N (Ab d s t K N j Φ U b ω) (Xmat d N (ω (j + 1))))
  exact hL.const_mul _

theorem measurable_stepY_filt (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
    {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
    (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2) :
    Measurable[filt d (j + 1)] (fun ω => stepY d s t K N j Φ U b ω) := by
  have hH : Measurable[filt d (j + 1)] (fun ω => H d s t K N (j + 1) ω) :=
    H_measurable_filt d s t K N (j + 1)
  have h1 : Measurable[filt d (j + 1)] (fun ω =>
      ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω)) :=
    Finset.measurable_sum _ fun a _ =>
      ((hΦ a).contDiff.continuous.measurable.comp hH).const_mul _
  have h2 : Measurable[filt d (j + 1)] ((Pg d)[fun ω' => ∑ a : LoopArg (d.L N) 2,
      (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω') | filt d j]) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt d).mono (Nat.le_succ j)) le_rfl
  have h3 := measurable_stepZ_filt s t K N j hΦ U b
  unfold stepY stepXi
  exact (h1.sub h2).sub (Complex.measurable_ofReal.comp h3)


/-- The increments `Zvec i` with the index cut to `1 ≤ i ≤ K N` (and `0` elsewhere); on the
indices that enter the sums this is `Zvec` itself, and it is adapted for **every** index. -/
def ZvecCut (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ) (ω : Ωg d)
    (a : LoopArg (d.L N) 2) : ℂ :=
  (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) * Zvec (band d) E s u K N i ω a

theorem ZvecCut_succ {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ} (hj : j < K N) :
    ZvecCut (d := d) E s u K N (j + 1) = Zvec (band d) E s u K N (j + 1) := by
  funext ω a
  unfold ZvecCut
  have h1 : (if 1 ≤ j + 1 ∧ j + 1 ≤ K N then (1 : ℂ) else 0) = 1 := by
    simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
  rw [h1, one_mul]

theorem time_lt_one_of_le {s t u : ℕ → ℝ} (hsu : ∀ N, s N ≤ u N)
    (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℕ → ℕ} (hK0 : ∀ N, K N ≠ 0) {N i : ℕ}
    (hi : i ≤ K N) : time s u K N i < 1 := by
  have h := time_mono_of_le (K := K) (hsu N) hi
  rw [time_last s u K N (hK0 N)] at h
  exact (h.trans (hut N)).trans_lt (ht1 N)

theorem stronglyMeasurable_ZvecCut {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ}
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℕ → ℕ}
    (hK0 : ∀ N, K N ≠ 0) (N i : ℕ) :
    StronglyMeasurable[filt d i] (ZvecCut (d := d) E s u K N i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ K N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [ZvecCut_succ (by omega)]
    have hu1 : time s u K N (j + 1) < 1 :=
      time_lt_one_of_le hsu hut ht1 hK0 hi.2
    have hΦ : ∀ a, TestFun d N (Φgrid (band d) E N (time s u K N (j + 1)) a) :=
      fun a => Φgrid_testFun (band d) hE N hu1 a
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact Complex.measurable_ofReal.comp (measurable_stepZ_filt s u K N j hΦ _ a)
  · have : ZvecCut (d := d) E s u K N i = fun _ => 0 := by
      funext ω a; unfold ZvecCut; have h0 : (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]; exact hi
      rw [h0, zero_mul]; rfl
    rw [this]; exact stronglyMeasurable_const

variable (d) in
/-- **The Azuma threshold**, with the positive floor inside the square
root: `xZ k a := N^{δ/16} · √(4 Σ_{j<k} c k a j + N^{-C_x})`. -/
def xZ (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (δ ε D τ₁ Cc Cx : ℝ) (N k : ℕ)
    (a : LoopArg (d.L N) 2) : ℝ :=
  (N : ℝ) ^ (δ / 16) *
    Real.sqrt (4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx))

theorem xZ_pos {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc Cx : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) :
    0 < xZ d E s u K δ ε D τ₁ Cc Cx N k a := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : 0 ≤ ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j :=
    Finset.sum_nonneg fun j _ => cZ_nonneg hsu k a j
  unfold xZ
  have : 0 < 4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx) := by
    have := Real.rpow_pos_of_pos hN0 (-Cx); linarith
  exact mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_pos.2 this)

theorem xZ_sq {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {δ ε D τ₁ Cc Cx : ℝ} {N : ℕ}
    (hsu : s N ≤ u N) (k : ℕ) (a : LoopArg (d.L N) 2) :
    xZ d E s u K δ ε D τ₁ Cc Cx N k a ^ 2 = (N : ℝ) ^ (δ / 8) *
      (4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx)) := by
  have hS : 0 ≤ ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j :=
    Finset.sum_nonneg fun j _ => cZ_nonneg hsu k a j
  have hX : 0 ≤ 4 * ∑ j ∈ Finset.range k, cZ d E s u K δ ε D τ₁ Cc N k a j + (N : ℝ) ^ (-Cx) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg N) (-Cx); linarith
  unfold xZ
  rw [mul_pow, Real.sq_sqrt hX]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  push_cast; ring

/-- `C N^b e^{-N^a} ≤ N^{-D}` eventually. -/
theorem eventually_mul_exp_neg_rpow_le (C b : ℝ) {a : ℝ} (ha : 0 < a) (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [SumZeroDyn.eventually_exp_small C (b + D) 1 one_pos ha,
    eventually_ge_atTop 1] with N h hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a)
      = (C * (N : ℝ) ^ (b + D) * Real.exp (-(1 * (N : ℝ) ^ a))) * (N : ℝ) ^ (-D) := by
    rw [one_mul, Real.rpow_add hN0]
    have : (N : ℝ) ^ D * (N : ℝ) ^ (-D) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    calc C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a)
        = C * (N : ℝ) ^ b * Real.exp (-(N : ℝ) ^ a) * ((N : ℝ) ^ D * (N : ℝ) ^ (-D)) := by
          rw [this, mul_one]
      _ = _ := by ring
  rw [e]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hN0.le _) h


theorem card_loopArg_two (L : ℕ) [NeZero L] : Fintype.card (LoopArg L 2) = L ^ 2 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- `Zvec (j+1) ≡ 0` when the grid step is `0`. -/
theorem Zvec_succ_eq_zero_of_step {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N : ℕ}
    (h0 : step s u K N = 0) (j : ℕ) (ω : Ωg d) (a : LoopArg (d.L N) 2) :
    Zvec (band d) E s u K N (j + 1) ω a = 0 := by
  change (stepZ d s u K N j (Φgrid (band d) E N (time s u K N (j + 1))) (gridDelta (d.L N)) a ω
    : ℂ) = 0
  simp [stepZ, h0]

theorem Uker_apply_eq_zero_of {L : ℕ} [NeZero L] {n : ℕ} (ξ : Fin n → ℂ) (s' t' : ℂ)
    {A : LoopArg L n → ℂ} (hA : ∀ b, A b = 0) (a : LoopArg L n) : Uker L ξ s' t' A a = 0 := by
  rw [Uker_apply]; simp [hA]

/-- `#(Idx N) = L N · W N ≤ N`. -/
theorem card_idx_le {N : ℕ} (hdim : d.W N * d.L N ≤ N) :
    (Fintype.card (d.Idx N) : ℝ) ≤ N := by
  have h1 : Fintype.card (d.Idx N) = d.L N * d.W N := by simp [ZMod.card]
  have h2 : d.L N * d.W N ≤ N := by rw [Nat.mul_comm]; exact hdim
  rw [h1]; exact_mod_cast h2

/-- `Csh(u') ≤ 1536 N⁸` once `#(Idx N) ≤ N` and `η_{u'}^{-1} ≤ N`. -/
theorem qvTimeShiftConst_le {E u' : ℝ} {N : ℕ} (hN1 : (1 : ℝ) ≤ N)
    (hcard : (Fintype.card (d.Idx N) : ℝ) ≤ N) (hη : (etaT E u')⁻¹ ≤ N)
    (hη0 : 0 ≤ (etaT E u')⁻¹) :
    qvTimeShiftConst d N E u' ≤ 1536 * (N : ℝ) ^ 8 := by
  unfold qvTimeShiftConst
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h1 : 1 + (etaT E u')⁻¹ ≤ 2 * N := by linarith
  have hc0 : (0 : ℝ) ≤ Fintype.card (d.Idx N) := Nat.cast_nonneg _
  calc 16 * Real.sqrt 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (1 + (etaT E u')⁻¹) ^ 6
      ≤ 16 * (3 / 2) * (N : ℝ) ^ 2 * (2 * N) ^ 6 := by gcongr
    _ = 1536 * (N : ℝ) ^ 8 := by ring

variable (d) in
/-- **The Azuma multiplier `Mm` of the grid Azuma event**, explicit:
`Mm = N^{δ/16} √(4 Ξ² (2 qvSumConst N^{τ₁+δ/64} + 2) + 5)` with `Ξ = xiK(L, W, Im m)`. -/
def azumaMm (E δ τ₁ : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (δ / 16) * Real.sqrt (4 * Step2.xiK (d.L N) (d.W N) (mE E).im ^ 2 *
    (2 * qvSumConst E * (N : ℝ) ^ (τ₁ + δ / 64) + 2) + 5)

theorem azumaMm_nonneg (E δ τ₁ : ℝ) (N : ℕ) : 0 ≤ azumaMm d E δ τ₁ N := by
  unfold azumaMm
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.sqrt_nonneg _)

/-- Summing a termwise affine bound. -/
theorem sum_le_affine_sum {k : ℕ} {f g : ℕ → ℝ} (A B C D : ℝ)
    (h : ∀ j ∈ Finset.range k, f j ≤ A * (B * g j + C) + D) :
    ∑ j ∈ Finset.range k, f j ≤ A * (B * ∑ j ∈ Finset.range k, g j + (k : ℝ) * C) +
      (k : ℝ) * D := by
  calc ∑ j ∈ Finset.range k, f j ≤ ∑ j ∈ Finset.range k, (A * (B * g j + C) + D) :=
        Finset.sum_le_sum h
    _ = A * (B * ∑ j ∈ Finset.range k, g j + (k : ℝ) * C) + (k : ℝ) * D := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]

/-- The final real arithmetic of the bound `xZ k a ≤ Mm (R_k²+1) T_{u_k}(a)`, `Mm = azumaMm`. -/
theorem sqrt_floor_arith {ξ T R q S NC NX : ℝ} (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hS : S ≤ ξ ^ 2 * T ^ 2 * ((q + 2) * (R ^ 4 + 1)) + NC) (hNC : NC ≤ T ^ 2)
    (hNX : NX ≤ T ^ 2) :
    Real.sqrt (4 * S + NX) ≤ T * (R ^ 2 + 1) * Real.sqrt (4 * ξ ^ 2 * (q + 2) + 5) := by
  have hQ0 : 0 ≤ 4 * ξ ^ 2 * (q + 2) + 5 := by positivity
  have hY0 : 0 ≤ T * (R ^ 2 + 1) * Real.sqrt (4 * ξ ^ 2 * (q + 2) + 5) := by positivity
  rw [Real.sqrt_le_left hY0, mul_pow, Real.sq_sqrt hQ0]
  have hR4 : 0 ≤ R ^ 4 := by positivity
  have hsq : R ^ 4 + 1 ≤ (R ^ 2 + 1) ^ 2 := by nlinarith [sq_nonneg R]
  have hT2 : 0 ≤ T ^ 2 := by positivity
  have hX : 4 * S + NX ≤ T ^ 2 * (R ^ 4 + 1) * (4 * ξ ^ 2 * (q + 2) + 5) := by
    have e : T ^ 2 * (R ^ 4 + 1) * (4 * ξ ^ 2 * (q + 2) + 5)
        = 4 * (ξ ^ 2 * T ^ 2 * ((q + 2) * (R ^ 4 + 1))) + 5 * T ^ 2 * (R ^ 4 + 1) := by ring
    rw [e]
    have : 5 * T ^ 2 ≤ 5 * T ^ 2 * (R ^ 4 + 1) := by nlinarith
    linarith
  calc 4 * S + NX ≤ T ^ 2 * (R ^ 4 + 1) * (4 * ξ ^ 2 * (q + 2) + 5) := hX
    _ ≤ T ^ 2 * (R ^ 2 + 1) ^ 2 * (4 * ξ ^ 2 * (q + 2) + 5) := by gcongr
    _ = (T * (R ^ 2 + 1)) ^ 2 * (4 * ξ ^ 2 * (q + 2) + 5) := by ring

/-- `W^{2D} Csh² Δ² · 2 ≤ 1` for `Δ ≤ N^{-(D+10)}`, `W ≤ N`, `Csh ≤ 1536 N⁸`, `N ≥ 64`. -/
theorem two_Csh_sq_step_sq_le {N : ℕ} (hN64 : (64 : ℝ) ≤ N) {Cs Δ W D : ℝ} (hD : 0 ≤ D)
    (hCs0 : 0 ≤ Cs) (hCs : Cs ≤ 1536 * (N : ℝ) ^ 8) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ (N : ℝ) ^ (-(D + 10))) (hW1 : 1 ≤ W) (hWN : W ≤ N) :
    2 * Cs ^ 2 * Δ ^ 2 * W ^ (2 * D) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hW : W ^ (2 * D) ≤ (N : ℝ) ^ (2 * D) :=
    Real.rpow_le_rpow (by linarith) hWN (by linarith)
  have hΔ2 : Δ ^ 2 ≤ (N : ℝ) ^ (-(2 * D + 20)) := by
    calc Δ ^ 2 ≤ ((N : ℝ) ^ (-(D + 10))) ^ 2 := pow_le_pow_left₀ hΔ0 hΔ 2
      _ = (N : ℝ) ^ (-(2 * D + 20)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hCs2 : Cs ^ 2 ≤ 1536 ^ 2 * (N : ℝ) ^ (16 : ℝ) := by
    calc Cs ^ 2 ≤ (1536 * (N : ℝ) ^ 8) ^ 2 := pow_le_pow_left₀ hCs0 hCs 2
      _ = 1536 ^ 2 * (N : ℝ) ^ (16 : ℝ) := by
        rw [mul_pow, ← pow_mul, show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hprod : (N : ℝ) ^ (16 : ℝ) * (N : ℝ) ^ (-(2 * D + 20)) * (N : ℝ) ^ (2 * D)
      = (N : ℝ) ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  have h4 : (N : ℝ) ^ (-4 : ℝ) ≤ 1 / (2 * 1536 ^ 2) := by
    rw [Real.rpow_neg hN0.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (64 : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hN64 4
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hW0 : 0 ≤ W ^ (2 * D) := Real.rpow_nonneg (by linarith) _
  have hN16 : 0 ≤ (N : ℝ) ^ (16 : ℝ) := Real.rpow_nonneg hN0.le _
  have hNm : 0 ≤ (N : ℝ) ^ (-(2 * D + 20)) := Real.rpow_nonneg hN0.le _
  calc 2 * Cs ^ 2 * Δ ^ 2 * W ^ (2 * D)
      ≤ 2 * (1536 ^ 2 * (N : ℝ) ^ (16 : ℝ)) * (N : ℝ) ^ (-(2 * D + 20)) * (N : ℝ) ^ (2 * D) := by
        gcongr
    _ = 2 * 1536 ^ 2 * ((N : ℝ) ^ (16 : ℝ) * (N : ℝ) ^ (-(2 * D + 20)) * (N : ℝ) ^ (2 * D)) := by
        ring
    _ ≤ 2 * 1536 ^ 2 * (1 / (2 * 1536 ^ 2)) := by rw [hprod]; gcongr
    _ = 1 := by norm_num

section StepYInputs

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (N j : ℕ)
  {Φ : LoopArg (d.L N) 2 → Matrix (d.Idx N) (d.Idx N) ℂ → ℂ} (hΦ : ∀ a, TestFun d N (Φ a))
  (hReal : ∀ a A, A.IsHermitian → (Φ a A).im = 0) {C₂ : ℝ}
  (hC₂ : ∀ a A, ‖fderiv ℝ (fderiv ℝ (Φ a)) A‖ ≤ C₂) (hΔ : 0 ≤ step s t K N)
  (U : LoopArg (d.L N) 2 → LoopArg (d.L N) 2 → ℝ) (b : LoopArg (d.L N) 2)

include hΦ hReal hC₂ hΔ in
/-- `stepZ` is integrable (the private `stepZ_integrable` of `GridExpansion.lean`, for a general
`Φ`). -/
theorem integrable_stepZ' : Integrable (stepZ d s t K N j Φ U b) (Pg d) := by
  have hg_int := integrable_h0 d s t K N (j + 1) hΦ U b
  have hh0_int := integrable_h0 d s t K N j hΦ U b
  have hR_int := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
  have hZeq : (fun ω => (stepZ d s t K N j Φ U b ω : ℂ))
      = (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N (j + 1) ω))
        - (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Φ a (H d s t K N j ω))
        - (fun ω => ∑ a : LoopArg (d.L N) 2, (U b a : ℂ) * Rlabel d s t K N j (Φ a) ω) := by
    funext ω
    have hg := g_eq_pointwise d s t K N j hΦ hReal U b ω
    simp only [Pi.sub_apply]
    rw [hg]; ring
  have hZc_int : Integrable (fun ω => (stepZ d s t K N j Φ U b ω : ℂ)) (Pg d) := by
    rw [hZeq]; exact (hg_int.sub hh0_int).sub hR_int
  have hre : (fun ω => RCLike.re ((stepZ d s t K N j Φ U b ω : ℝ) : ℂ))
      = stepZ d s t K N j Φ U b := funext fun ω => RCLike.ofReal_re _
  rw [← hre]
  exact hZc_int.re

include hΦ hReal hC₂ hΔ in
/-- `stepY` is integrable. -/
theorem integrable_stepY' : Integrable (stepY d s t K N j Φ U b) (Pg d) := by
  have hY := stepY_eq_ae d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)
  have hRint := integrable_Rlabel_sum d s t K N j hΦ hC₂ hΔ U b
  exact (hRint.sub integrable_condExp).congr hY.symm

include hΦ hReal hC₂ hΔ in
/-- `stepY ∈ L²`: `‖stepY‖ ≤ g + E[g|F_j]` with `g = C‖X_{j+1}‖² ∈ L²`. -/
theorem memLp_stepY' : MemLp (stepY d s t K N j Φ U b) 2 (Pg d) := by
  have hbd := stepY_norm_le_ae d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)
  set g : Ωg d → ℝ := fun ω => (∑ a : LoopArg (d.L N) 2, |U b a|) * ((C₂ / 2) * step s t K N)
      * ‖Xmat d N (ω (j + 1))‖ ^ 2 with hgdef
  have hgmeas : Measurable g := by
    have hX : Measurable (fun ω : Ωg d => Xmat d N (ω (j + 1))) :=
      (measurable_Xmat d N).comp (measurable_pi_apply (j + 1))
    exact measurable_const.mul ((measurable_norm.comp hX).pow_const 2)
  have hg2 : MemLp g 2 (Pg d) := by
    rw [memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable]
    have : (fun ω => g ω ^ 2) = fun ω => ((∑ a : LoopArg (d.L N) 2, |U b a|) *
        ((C₂ / 2) * step s t K N)) ^ 2 * ‖Xmat d N (ω (j + 1))‖ ^ 4 := by
      funext ω; rw [hgdef]; ring
    rw [this]
    exact (integrable_normPow4_incr d N j).const_mul _
  have hsum : MemLp (fun ω => g ω + (Pg d)[g | filt d j] ω) 2 (Pg d) :=
    hg2.add (hg2.condExp (by norm_num))
  refine hsum.of_le (integrable_stepY' s t K N j hΦ hReal hC₂ hΔ U b).aestronglyMeasurable ?_
  filter_upwards [hbd] with ω hω
  exact hω.trans (le_abs_self _)

include hΦ hReal hC₂ hΔ in
/-- The stopped `stepY` has conditional mean zero (real part). -/
theorem condExp_indicator_stepY_re {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S) :
    (Pg d)[fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).re | filt d j] =ᵐ[Pg d] 0 := by
  have hint := integrable_stepY' s t K N j hΦ hReal hC₂ hΔ U b
  have hmean := (stepDecomp d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)).2.2.2
  have hfun : (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).re)
      = S.indicator (fun ω => (stepY d s t K N j Φ U b ω).re) := by
    funext ω; by_cases h : ω ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hfun]
  have hre : Integrable (fun ω => (stepY d s t K N j Φ U b ω).re) (Pg d) := hint.re
  have h1 := condExp_indicator (m := filt d j) hre hS
  have h2 : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).re | filt d j] =ᵐ[Pg d] 0 := by
    have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint
      Complex.reCLM).symm
    have hc' : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).re | filt d j]
        =ᵐ[Pg d] fun ω => ((Pg d)[stepY d s t K N j Φ U b | filt d j] ω).re := by
      simpa [Function.comp_def] using hc
    filter_upwards [hc', hmean] with ω h1 h2
    rw [h1, h2]; simp
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  by_cases h : ω ∈ S
  · rw [Set.indicator_of_mem h, hω2]
  · rw [Set.indicator_of_notMem h]; rfl

include hΦ hReal hC₂ hΔ in
/-- The stopped `stepY` has conditional mean zero (imaginary part). -/
theorem condExp_indicator_stepY_im {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S) :
    (Pg d)[fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).im | filt d j] =ᵐ[Pg d] 0 := by
  have hint := integrable_stepY' s t K N j hΦ hReal hC₂ hΔ U b
  have hmean := (stepDecomp d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)).2.2.2
  have hfun : (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).im)
      = S.indicator (fun ω => (stepY d s t K N j Φ U b ω).im) := by
    funext ω; by_cases h : ω ∈ S
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hfun]
  have him : Integrable (fun ω => (stepY d s t K N j Φ U b ω).im) (Pg d) := hint.im
  have h1 := condExp_indicator (m := filt d j) him hS
  have h2 : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).im | filt d j] =ᵐ[Pg d] 0 := by
    have hc := (ContinuousLinearMap.comp_condExp_comm (m := filt d j) hint
      Complex.imCLM).symm
    have hc' : (Pg d)[fun ω => (stepY d s t K N j Φ U b ω).im | filt d j]
        =ᵐ[Pg d] fun ω => ((Pg d)[stepY d s t K N j Φ U b | filt d j] ω).im := by
      simpa [Function.comp_def] using hc
    filter_upwards [hc', hmean] with ω h1 h2
    rw [h1, h2]; simp
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  by_cases h : ω ∈ S
  · rw [Set.indicator_of_mem h, hω2]
  · rw [Set.indicator_of_notMem h]; rfl

include hΦ hReal hC₂ hΔ in
/-- The `L²` input of `stopped_duhamel_cheb_tail` for the stopped `stepY`:
`∫ (1_S stepY)_re² + ∫ (1_S stepY)_im² ≤ 4 (C_r C₂/2)² Δ² ∫‖X_{j+1}‖⁴` for any row bound
`Σ_a |U(b,a)| ≤ C_r` (`stepDecomp_Y_sq`). -/
theorem integral_sq_indicator_stepY_le {S : Set (Ωg d)} (hS : MeasurableSet[filt d j] S)
    {Cr : ℝ} (hCr : ∑ a : LoopArg (d.L N) 2, |U b a| ≤ Cr) (hC₂0 : 0 ≤ C₂) :
    ∫ ω, (S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2 ∂(Pg d)
      + ∫ ω, (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2 ∂(Pg d)
      ≤ 4 * (Cr * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by
  have hm := memLp_stepY' s t K N j hΦ hReal hC₂ hΔ U b
  have hmI : MemLp (S.indicator (stepY d s t K N j Φ U b)) 2 (Pg d) :=
    hm.indicator ((filt d).le j S hS)
  have hre : Integrable (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2) (Pg d) :=
    hmI.re.integrable_sq
  have him : Integrable (fun ω => (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2) (Pg d) :=
    hmI.im.integrable_sq
  have hn2 : Integrable (fun ω => ‖stepY d s t K N j Φ U b ω‖ ^ 2) (Pg d) :=
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm
  rw [← integral_add hre him]
  have hY2 := stepDecomp_Y_sq d s t K N j hΦ hReal hC₂ hΔ U b
    (integrable_stepZ' s t K N j hΦ hReal hC₂ hΔ U b)
  have hX4 : 0 ≤ ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) :=
    integral_nonneg fun _ => by positivity
  have hU0 : 0 ≤ ∑ a : LoopArg (d.L N) 2, |U b a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ∫ ω, ((S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2
        + (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2) ∂(Pg d)
      ≤ ∫ ω, ‖stepY d s t K N j Φ U b ω‖ ^ 2 ∂(Pg d) := by
        refine integral_mono (hre.add him) hn2 fun ω => ?_
        have e : (S.indicator (stepY d s t K N j Φ U b) ω).re ^ 2
            + (S.indicator (stepY d s t K N j Φ U b) ω).im ^ 2
            = ‖S.indicator (stepY d s t K N j Φ U b) ω‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        simp only
        rw [e]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_indicator_le_norm_self _ _) 2
    _ ≤ 4 * ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := hY2
    _ ≤ 4 * (Cr * (C₂ / 2)) ^ 2 * (step s t K N) ^ 2
          * ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) := by
        have h1 : (∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2) ≤ Cr * (C₂ / 2) :=
          mul_le_mul_of_nonneg_right hCr (by linarith)
        have h2 : ((∑ a : LoopArg (d.L N) 2, |U b a|) * (C₂ / 2)) ^ 2 ≤ (Cr * (C₂ / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        gcongr

end StepYInputs

/-- `∫ ‖X_{j+1}‖⁴ dPg = ∫ ‖X‖⁴ dP ≤ 3 · #(Idx N)` (the Gaussian fourth moment via the trace
moments, `traceConst 2 = 3`). -/
theorem integral_norm_Xmat_incr_four_le (N j : ℕ) :
    ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) ≤ 3 * (Fintype.card (d.Idx N) : ℝ) := by
  have hmap : ∫ ω, ‖Xmat d N (ω (j + 1))‖ ^ 4 ∂(Pg d) = ∫ x, ‖Xmat d N x‖ ^ 4 ∂(P d) := by
    rw [← map_incr d j]
    rw [integral_map (measurable_pi_apply (j + 1)).aemeasurable]
    · rw [map_incr d j]
      exact ((measurable_norm_Xmat d N).pow_const 4).aestronglyMeasurable
  rw [hmap]
  have h1 := integral_norm_Xmat_pow_le (d := d) N 1
  norm_num at h1
  have hfrob : ∀ ω : Ω d, frobSq (Xmat d N ω ^ 2) = ∑ i, colSq (Xmat d N ω) 2 i := by
    intro ω; unfold frobSq colSq; exact Finset.sum_comm
  simp only [hfrob] at h1
  rw [integral_finsetSum _ fun i _ => integrable_colSq d N 2 i] at h1
  have h2 : ∑ i : d.Idx N, ∫ ω, colSq (Xmat d N ω) 2 i ∂(P d)
      ≤ ∑ _i : d.Idx N, traceConst 2 := Finset.sum_le_sum fun i _ => integral_colSq_le d N 2 i
  have h3 : traceConst 2 = 3 := by norm_num [traceConst]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h3] at h2
  linarith

/-- Row sum of the unit-charge kernel: `Σ_a |U_{v,w}(b,a)| ≤ ((1−v)/(1−w))²` for
`0 ≤ v ≤ w < 1` (`norm_Uker_apply_le` at the constant tensor `1`). -/
theorem sum_abs_ukerMat_le (L : ℕ) [NeZero L] (hL : 3 ≤ L) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w)
    (hw1 : w < 1) (b : LoopArg L 2) :
    ∑ a : LoopArg L 2, |ukerMat L v w b a| ≤ ((1 - v) / (1 - w)) ^ 2 := by
  have habs : ∀ a, |ukerMat L v w b a| = ukerMat L v w b a := fun a =>
    abs_of_nonneg (ukerMat_nonneg L hL hv0 hvw hw1 b a)
  simp only [habs]
  have hsum : ∑ a : LoopArg L 2, ukerMat L v w b a
      = (Uker L (fun _ => (1 : ℂ)) (v : ℂ) (w : ℂ) (fun _ => (1 : ℂ)) b).re := by
    rw [Uker_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ukerMat_eq_prod_re, mul_one]
  rw [hsum]
  have hw0 : 0 ≤ w := hv0.trans hvw
  have h1w : 0 < 1 - w := by linarith
  have hnw : ‖(w : ℂ) * 1‖ = w := by rw [mul_one, Complex.norm_real, Real.norm_of_nonneg hw0]
  have hnvw : ‖((v : ℂ) - (w : ℂ)) * 1‖ = w - v := by
    rw [mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hB := norm_Uker_apply_le L hL (ξ := fun _ => (1 : ℂ)) (s := (v : ℂ)) (t := (w : ℂ))
    (fun _ => by rw [hnw]; exact hw1) (C := (1 - v) / (1 - w)) (M := 1) zero_le_one
    (fun _ => by
      rw [hnw, hnvw, le_div_iff₀ h1w, add_mul, one_mul, mul_assoc, inv_mul_cancel₀ h1w.ne',
        mul_one]
      linarith)
    (A := fun _ => (1 : ℂ)) (fun _ => by simp) b
  rw [mul_one] at hB
  exact (Complex.re_le_norm _).trans hB

/-- The increments `Yvec i` with the index cut to `1 ≤ i ≤ K N`. -/
def YvecCut (E : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (N i : ℕ) (ω : Ωg d)
    (a : LoopArg (d.L N) 2) : ℂ :=
  (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) * Yvec (band d) E s u K N i ω a

theorem YvecCut_succ {E : ℝ} {s u : ℕ → ℝ} {K : ℕ → ℕ} {N j : ℕ} (hj : j < K N) :
    YvecCut (d := d) E s u K N (j + 1) = Yvec (band d) E s u K N (j + 1) := by
  funext ω a
  unfold YvecCut
  have h1 : (if 1 ≤ j + 1 ∧ j + 1 ≤ K N then (1 : ℂ) else 0) = 1 := by
    simp only [ite_eq_left_iff, zero_ne_one, imp_false, not_not]; omega
  rw [h1, one_mul]

theorem stronglyMeasurable_YvecCut {E : ℝ} (hE : |E| < 2) {s t u : ℕ → ℝ}
    (hsu : ∀ N, s N ≤ u N) (hut : ∀ N, u N ≤ t N) (ht1 : ∀ N, t N < 1) {K : ℕ → ℕ}
    (hK0 : ∀ N, K N ≠ 0) (N i : ℕ) :
    StronglyMeasurable[filt d i] (YvecCut (d := d) E s u K N i) := by
  by_cases hi : 1 ≤ i ∧ i ≤ K N
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [YvecCut_succ (by omega)]
    have hu1 : time s u K N (j + 1) < 1 := time_lt_one_of_le hsu hut ht1 hK0 hi.2
    have hΦ : ∀ a, TestFun d N (Φgrid (band d) E N (time s u K N (j + 1)) a) :=
      fun a => Φgrid_testFun (band d) hE N hu1 a
    refine Measurable.stronglyMeasurable ?_
    refine @Measurable.of_eval _ _ _ (filt d (j + 1)) _ _ fun a => ?_
    exact measurable_stepY_filt s u K N j hΦ _ a
  · have : YvecCut (d := d) E s u K N i = fun _ => 0 := by
      funext ω a; unfold YvecCut
      have h0 : (if 1 ≤ i ∧ i ≤ K N then (1 : ℂ) else 0) = 0 := by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]; exact hi
      rw [h0, zero_mul]; rfl
    rw [this]; exact stronglyMeasurable_const

/-- **The grid-size exponent of the Chebyshev bound at the stopping index**: `C_K(D, D₁) =
D₁ + 2D + 80` (depends only on `D, D₁`). -/
def CK (D D₁ : ℝ) : ℝ := D₁ + 2 * D + 80

/-- **The grid size of the Chebyshev bound at the stopping index**: `K N = ⌈N^{C_K}⌉` (`max 1`
only matters at `N = 0`). -/
def gridK (D D₁ : ℝ) (N : ℕ) : ℕ := max 1 ⌈(N : ℝ) ^ CK D D₁⌉₊

theorem gridK_ne_zero (D D₁ : ℝ) (N : ℕ) : gridK D D₁ N ≠ 0 := by
  unfold gridK; omega

theorem rpow_CK_le_gridK (D D₁ : ℝ) (N : ℕ) : (N : ℝ) ^ CK D D₁ ≤ gridK D D₁ N := by
  unfold gridK
  calc (N : ℝ) ^ CK D D₁ ≤ (⌈(N : ℝ) ^ CK D D₁⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ ((max 1 ⌈(N : ℝ) ^ CK D D₁⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _

/-- `Δ ≤ N^{-C_K}` on the grid `gridK`, once `0 ≤ u N − s N ≤ 1`. -/
theorem step_gridK_le {s u : ℕ → ℝ} {D D₁ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hus : u N - s N ≤ 1) : step s u (gridK D D₁) N ≤ (N : ℝ) ^ (-CK D D₁) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < (N : ℝ) ^ CK D D₁ := Real.rpow_pos_of_pos hN0 _
  have hK := rpow_CK_le_gridK D D₁ N
  have hK0 : (0 : ℝ) < gridK D D₁ N := lt_of_lt_of_le hpos hK
  unfold step
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc u N - s N ≤ 1 := hus
    _ = ((N : ℝ) ^ CK D D₁)⁻¹ * (N : ℝ) ^ CK D D₁ := (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ ((N : ℝ) ^ CK D D₁)⁻¹ * gridK D D₁ N :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- `gridK` has polynomially many points: `K N + 1 ≤ N^{C_K + 2}` eventually. -/
theorem gridK_card_le {D D₁ : ℝ} (hCK : 0 ≤ CK D D₁) :
    ∀ᶠ N : ℕ in atTop, ((gridK D D₁ N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (CK D D₁ + 2) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hA1 : (1 : ℝ) ≤ (N : ℝ) ^ CK D D₁ := Real.one_le_rpow (by linarith) hCK
  have hK : (gridK D D₁ N : ℝ) ≤ (N : ℝ) ^ CK D D₁ + 1 := by
    unfold gridK
    rcases le_total 1 ⌈(N : ℝ) ^ CK D D₁⌉₊ with h | h
    · rw [max_eq_right h]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    · rw [max_eq_left h]; push_cast; linarith
  push_cast
  rw [Real.rpow_add hN0, Real.rpow_two]
  have hN4 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hN4 (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ CK D D₁)
  linarith

/-- The per-step `L²` constant of the Chebyshev bound at the stopping index:
`4 (C_r C₂/2)² Δ² M₄ ≤ 2²² N¹⁹ Δ²`. -/
theorem cheb_e_le {N : ℕ} (hN1 : (1 : ℝ) ≤ N) {Cr card ηi M4 Δ : ℝ} (hCr0 : 0 ≤ Cr)
    (hCr : Cr ≤ (N : ℝ) ^ 2) (hc0 : 0 ≤ card) (hc : card ≤ N) (hηi0 : 0 ≤ ηi) (hηi : ηi ≤ N)
    (hM0 : 0 ≤ M4) (hM : M4 ≤ 3 * card) :
    4 * (Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2)) ^ 2 * Δ ^ 2 * M4
      ≤ 2 ^ 22 * (N : ℝ) ^ 19 * Δ ^ 2 := by
  have h1 : 1 + ηi ≤ 2 * N := by linarith
  have hC2 : card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2 ≤ 512 * (N : ℝ) ^ 7 := by
    have e : card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2 = 8 * card * (1 + ηi) ^ 6 := by
      ring
    rw [e]
    calc 8 * card * (1 + ηi) ^ 6 ≤ 8 * N * (2 * N) ^ 6 := by gcongr
      _ = 512 * (N : ℝ) ^ 7 := by ring
  have hC20 : 0 ≤ card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2 := by positivity
  have hP : Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2) ≤ 512 * (N : ℝ) ^ 9 := by
    calc _ ≤ (N : ℝ) ^ 2 * (512 * (N : ℝ) ^ 7) := mul_le_mul hCr hC2 hC20 (by positivity)
      _ = 512 * (N : ℝ) ^ 9 := by ring
  have hP2 : (Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2)) ^ 2
      ≤ (512 * (N : ℝ) ^ 9) ^ 2 := pow_le_pow_left₀ (by positivity) hP 2
  have hM' : M4 ≤ 3 * N := by linarith
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  calc 4 * (Cr * (card * ((2 : ℝ) ^ 2 * (2 * (1 + ηi) ^ 3) ^ 2) / 2)) ^ 2 * Δ ^ 2 * M4
      ≤ 4 * (512 * (N : ℝ) ^ 9) ^ 2 * Δ ^ 2 * (3 * N) := by gcongr
    _ = 3 * 2 ^ 20 * (N : ℝ) ^ 19 * Δ ^ 2 := by ring
    _ ≤ 2 ^ 22 * (N : ℝ) ^ 19 * Δ ^ 2 := by
        have : (0 : ℝ) ≤ (N : ℝ) ^ 19 * Δ ^ 2 := by positivity
        nlinarith

variable (d) in
/-- **The good event** at size `N`, for a grid `K` and floor exponents `C_c, C_x`:
the grid Azuma event for all `k ≤ K N` ∩ the failure of the Chebyshev event at `τ` ∩ the good
set at every grid index `j ≤ K N` ∩ the (T5) initial bounds. -/
def goodEventGrid (E D δ τ₁ ε ζCtr τ3 τ57 : ℝ) (s u : ℕ → ℝ) (K : ℕ → ℕ) (Cc Cx : ℝ) (N : ℕ) :
    Set (Ωg d) :=
  {ω | ∀ k ≤ K N, ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (min k (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω)),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ) (time s u K N k : ℂ)
            (Zvec (band d) E s u K N (j + 1) ω)) a‖
        < xZ d E s u K δ ε D τ₁ Cc Cx N k a}
  ∩ {ω | ∀ a : LoopArg (d.L N) 2,
      ‖(∑ j ∈ Finset.range (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω),
          Uker (d.L N) (fun _ => (1 : ℂ)) (time s u K N (j + 1) : ℂ)
            (time s u K N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω) : ℂ)
            (Yvec (band d) E s u K N (j + 1) ω)) a‖
        < Step2.tT (band d) E N D (time s u K N (gridTau d E D δ τ₁ ε ζCtr τ3 τ57 s u K N ω))
            (zdist (d.L N) (a 0 - a 1))}
  ∩ {ω | ∀ k : Fin (K N + 1),
      H d s u K N k ω ∈ goodSet d E N (time s u K N k) ((band d).ell N (s N)) τ₁ ε ζCtr τ3 τ57 D}
  ∩ {ω | (∀ b : LoopArg (d.L N) 2, ‖Agrid (band d) E s u K N 0 ω b‖ ≤
        (N : ℝ) ^ (δ / 16) * Step2.tT (band d) E N D (time s u K N 0)
          (zdist (d.L N) (b 0 - b 1)))
      ∧ jSMat d E D N (time s u K N 0) (H d s u K N 0 ω)
        < Step2.thr E s δ N (time s u K N 0)}

end Amend

end RBM.Gauss.Grid

end

