/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.EarlyQVRateEv
import RBM1D.Gauss.LoopLeibniz
import RBM1D.Gauss.APrimeNearRem
import RBM1D.Gauss.GridDriftSum
import RBM1D.Gauss.LoopLipschitz
import RBM1D.Gauss.FlowHolder
import RBM1D.Loop.Split
import RBM1D.Gauss.DimsExample
import RBM1D.Gauss.CutoffBounds

/-!
# T1514 — R3a: the single-label quadratic variation on the good set, with the one-step time
shift (supervisor `2026-09-26-0048` §1e M2, §2 R3(a))

Formalization of the deterministic gap the supervisor's note M2 identifies: the martingale
difference of grid step `j` has gradient `coordD1(Φ_{u_{j+1}})` evaluated **at `H_j`**
(`RBM.Gauss.Grid.condExp_loop_step`, `RBM.Gauss.Grid.H_succ`), while T1497 controls
`quadVar(Φ_u)` at a matrix of the *same* time `u`.  (T1) below closes this time/matrix
mismatch deterministically, by an explicit resolvent telescoping (the same identity the ticket
suggests: `G(z') - G(z) = (z'-z) G(z') G(z)`, `‖G‖ ≤ η⁻¹`) rather than the paper's Duhamel-style
FTC argument, since here it is the *derivative* `coordD1`, not the value, that needs a time
modulus.  (T2) records the (elementary) monotonicity of `diagShape'`/`nearEpsilon` in the
blockwise cap `J`.  (T3) assembles (T1), (T2), and the already-merged `tailT_mono_time`
(T1510) into the one-step quadratic-variation bound `RBM.Gauss.Grid.quadVar_step_le`.

## Main results

* `RBM.Gauss.Grid.qvTimeShiftConst` : the explicit constant `Csh` of (T1).
* `RBM.Gauss.Grid.sqrt_quadVar_time_shift` (T1).
* `RBM.Gauss.Grid.diagShape'_mono_J`, `RBM.Gauss.Grid.nearEpsilon_mono_J`,
  `RBM.Gauss.Grid.diagShape'_le_dropIndicator` (T2), together with the private helpers
  `diagFarRate_mono_J`, `diagShape'_mono_eps` used by (T3).
* `RBM.Gauss.Grid.quadVar_step_le` (T3).

Nothing here is an `axiom`, and nothing here is `sorry`.
-/

noncomputable section

namespace RBM.Gauss.Grid

open Matrix Finset
open scoped Matrix.Norms.L2Operator

/-! ### §0 : small deterministic helpers, reused from the (private) patterns already merged
elsewhere in the repository (`Gauss/APrimeQVGlobalPolyCore.lean`), copied here since those
copies are `private` to their own file. -/

private theorem band_toDims_eq (d' : Dims) : (Gauss.band d').toDims = d' := by
  cases d'; rfl

private theorem norm_single_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (c : ℂ) : ‖Matrix.single i j c‖ ≤ ‖c‖ := by
  rw [Matrix.cstar_norm_def]
  refine (Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.single i j c)).opNorm_le_bound
    (norm_nonneg c) ?_
  intro x
  have h := PiLp.norm_apply_le x j
  have heq : Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.single i j c) x =
      (c * x j) • (PiLp.single 2 i (1 : ℂ)) := by
    conv_lhs => rw [show x = WithLp.toLp 2 x.ofLp from rfl]
    rw [Matrix.toEuclideanCLM_toLp, Matrix.single_mulVec_eq]
    simp
  rw [heq, norm_smul, PiLp.norm_single, norm_one, mul_one, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg c)

private theorem norm_Bmat_le_two (d : Dims) (N : ℕ)
    (i j : d.Idx N) (b : Bool) : ‖Gauss.Bmat d N i j b‖ ≤ 2 := by
  classical
  by_cases hij : i = j
  · subst j
    have heq : Gauss.Bmat d N i i b =
        Matrix.single i i (if b then (1 : ℂ) else Complex.I) := by
      ext k l
      simp only [Gauss.Bmat_apply, Matrix.single_apply]
      by_cases hkl : k = i ∧ l = i
      · rcases hkl with ⟨rfl, rfl⟩
        simp
      · have hkl' : ¬(i = k ∧ i = l) := by simpa [eq_comm] using hkl
        simp [hkl, hkl']
    rw [heq]
    have h := norm_single_le i i (if b then (1 : ℂ) else Complex.I)
    have hc : ‖(if b then (1 : ℂ) else Complex.I)‖ ≤ 2 := by
      cases b <;> norm_num
    exact h.trans hc
  · have heq : Gauss.Bmat d N i j b =
        Matrix.single i j (if b then (1 : ℂ) else Complex.I) +
          Matrix.single j i (if b then (1 : ℂ) else -Complex.I) := by
      ext k l
      simp only [Gauss.Bmat_apply, Matrix.add_apply, Matrix.single_apply]
      by_cases h₁ : k = i ∧ l = j
      · simp [h₁, hij, eq_comm]
      · by_cases h₂ : k = j ∧ l = i
        · simp [h₂, hij, eq_comm]
        · have h₁' : ¬(i = k ∧ j = l) := by simpa [eq_comm] using h₁
          have h₂' : ¬(j = k ∧ i = l) := by simpa [eq_comm] using h₂
          simp [h₁, h₂, h₁', h₂']
    rw [heq]
    have h₁ := norm_single_le i j (if b then (1 : ℂ) else Complex.I)
    have h₂ := norm_single_le j i (if b then (1 : ℂ) else -Complex.I)
    have hsum := norm_add_le
      (Matrix.single i j (if b then (1 : ℂ) else Complex.I))
      (Matrix.single j i (if b then (1 : ℂ) else -Complex.I))
    have hc₁ : ‖(if b then (1 : ℂ) else Complex.I)‖ = 1 := by cases b <;> norm_num
    have hc₂ : ‖(if b then (1 : ℂ) else -Complex.I)‖ = 1 := by cases b <;> norm_num
    rw [hc₁] at h₁
    rw [hc₂] at h₂
    linarith

private theorem gvar_le_one (d : Dims) (N : ℕ) (i j : d.Idx N) (b : Bool) :
    (Gauss.gvar d ⟨N, i, j, b⟩ : ℝ) ≤ 1 := by
  have hS : Sblk (d.L N) (d.W N) i j ≤ 1 := by
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (d.Idx N))) (fun k _ => Sblk_nonneg i k) (Finset.mem_univ j)
    rw [sum_Sblk_row (d.three_le_L N) i] at hsingle
    exact hsingle
  by_cases hij : i = j
  · subst j; simpa using hS
  · rw [Gauss.gvar_offDiag d N i j b hij]; nlinarith [Sblk_nonneg i j]

/-- The crude, dimension-explicit bound on the total coordinate weight
`∑_{q∈usedCoord} gvar(q) ≤ 2·(card idx)²`. -/
private theorem sum_gvar_usedCoord_le (d : Dims) (N : ℕ) :
    ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ)
      ≤ 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 := by
  classical
  have hcard : (Gauss.usedCoord d N).card ≤ 2 * (Fintype.card (d.Idx N)) ^ 2 := by
    calc (Gauss.usedCoord d N).card
        ≤ (Finset.univ : Finset (d.Idx N × d.Idx N × Bool)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 * (Fintype.card (d.Idx N)) ^ 2 := by
          simp [Fintype.card_prod, Fintype.card_bool]; ring
  have hcardR : ((Gauss.usedCoord d N).card : ℝ) ≤ 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 := by
    exact_mod_cast hcard
  calc ∑ q ∈ Gauss.usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ)
      ≤ ∑ _q ∈ Gauss.usedCoord d N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun q _ => ?_
        obtain ⟨i, j, b⟩ := q
        exact gvar_le_one d N i j b
    _ = ((Gauss.usedCoord d N).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 := hcardR

/-! ### §1 : `prodList` telescoping at fixed `M`, moving `z` only -/

section ProdListTelescope

variable {L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (ZMod L × Fin W) (ZMod L × Fin W) ℂ}
  {z : ℂ} {K : ℝ}

private theorem norm_Eblk_le_one (b : ZMod L) : ‖Eblk L W b‖ ≤ 1 := by
  have h := norm_Eblk_le (L := L) (W := W) b
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W)
  refine h.trans ?_
  rw [inv_le_one_iff₀]; right; exact hW1

private theorem norm_prodList_le_pow (hK : 0 ≤ K) (hG : ∀ s, ‖Gsig M z s‖ ≤ K) :
    ∀ l : List (Bool × ZMod L), ‖prodList L W M z l‖ ≤ K ^ l.length := by
  intro l
  induction l with
  | nil => simp [prodList]
  | cons p l ih =>
    have hcons : prodList L W M z (p :: l) = Gsig M z p.1 * Eblk L W p.2 * prodList L W M z l :=
      rfl
    rw [hcons, List.length_cons, pow_succ']
    have hE : ‖Eblk L W p.2‖ ≤ 1 := norm_Eblk_le_one p.2
    refine (norm_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
    calc ‖Gsig M z p.1‖ * ‖Eblk L W p.2‖ * ‖prodList L W M z l‖
        ≤ K * 1 * K ^ l.length :=
          mul_le_mul (mul_le_mul (hG p.1) hE (norm_nonneg _) hK) ih (norm_nonneg _)
            (by positivity)
      _ = K * K ^ l.length := by ring

private theorem norm_prodList_sub_le {z' : ℂ} {Δ : ℝ} (hK : 1 ≤ K) (hΔ : 0 ≤ Δ)
    (hG : ∀ s, ‖Gsig M z s‖ ≤ K) (hG' : ∀ s, ‖Gsig M z' s‖ ≤ K)
    (hsub : ∀ s, ‖Gsig M z s - Gsig M z' s‖ ≤ Δ) :
    ∀ l : List (Bool × ZMod L),
      ‖prodList L W M z l - prodList L W M z' l‖ ≤ (l.length : ℝ) * K ^ l.length * Δ := by
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  intro l
  induction l with
  | nil => simp [prodList]
  | cons p l ih =>
    have hE : ‖Eblk L W p.2‖ ≤ 1 := norm_Eblk_le_one p.2
    have hQ₁ := norm_prodList_le_pow (M := M) (z := z) hK0 hG l
    have hsplit : prodList L W M z (p :: l) - prodList L W M z' (p :: l)
        = (Gsig M z p.1 - Gsig M z' p.1) * Eblk L W p.2 * prodList L W M z l
          + Gsig M z' p.1 * Eblk L W p.2 *
              (prodList L W M z l - prodList L W M z' l) := by
      change Gsig M z p.1 * Eblk L W p.2 * prodList L W M z l
          - Gsig M z' p.1 * Eblk L W p.2 * prodList L W M z' l = _
      noncomm_ring
    rw [hsplit, List.length_cons]
    refine (norm_add_le _ _).trans ?_
    have hA : ‖(Gsig M z p.1 - Gsig M z' p.1) * Eblk L W p.2 * prodList L W M z l‖
        ≤ Δ * K ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      calc ‖Gsig M z p.1 - Gsig M z' p.1‖ * ‖Eblk L W p.2‖ * ‖prodList L W M z l‖
          ≤ Δ * 1 * K ^ l.length :=
            mul_le_mul (mul_le_mul (hsub p.1) hE (norm_nonneg _) hΔ) hQ₁ (norm_nonneg _)
              (by positivity)
        _ = Δ * K ^ l.length := by ring
    have hB : ‖Gsig M z' p.1 * Eblk L W p.2 *
          (prodList L W M z l - prodList L W M z' l)‖
        ≤ K * ((l.length : ℝ) * K ^ l.length * Δ) := by
      refine (norm_mul_le _ _).trans ?_
      refine (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans ?_
      have h1 : ‖Gsig M z' p.1‖ * ‖Eblk L W p.2‖ ≤ K * 1 :=
        mul_le_mul (hG' p.1) hE (norm_nonneg _) hK0
      calc ‖Gsig M z' p.1‖ * ‖Eblk L W p.2‖
            * ‖prodList L W M z l - prodList L W M z' l‖
          ≤ K * 1 * ((l.length : ℝ) * K ^ l.length * Δ) :=
            mul_le_mul h1 ih (norm_nonneg _) (by positivity)
        _ = K * ((l.length : ℝ) * K ^ l.length * Δ) := by ring
    have hpow : (0 : ℝ) ≤ K ^ l.length := pow_nonneg hK0 _
    have hkey : Δ * K ^ l.length + K * ((l.length : ℝ) * K ^ l.length * Δ)
        ≤ ((l.length : ℝ) + 1) * K ^ (l.length + 1) * Δ := by
      rw [pow_succ']
      have h1 : K ^ l.length ≤ K * K ^ l.length := by nlinarith
      nlinarith [Nat.cast_nonneg (α := ℝ) l.length]
    push_cast
    linarith

end ProdListTelescope

/-! ### §2 : the uniform resolvent envelope/increment at two times `u ≤ u'`, and the resulting
`loopCut` time-Lipschitz bound at a fixed Hermitian `M` -/

section LoopCutTime

variable {d : Dims} {N : ℕ}

/-- The uniform (`s`-independent) resolvent envelope and increment at the two times `u ≤ u'`. -/
private theorem gsig_bounds {E u u' : ℝ} (hE : |E| < 2) (huu' : u ≤ u') (hu'1 : u' < 1)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian) :
    1 ≤ (1 + (etaT E u')⁻¹) ∧
      (∀ s, ‖Gsig M (zt E u) s‖ ≤ 1 + (etaT E u')⁻¹) ∧
      (∀ s, ‖Gsig M (zt E u') s‖ ≤ 1 + (etaT E u')⁻¹) ∧
      (∀ s, ‖Gsig M (zt E u) s - Gsig M (zt E u') s‖
        ≤ (1 + (etaT E u')⁻¹) ^ 2 * (u' - u)) := by
  have := Dims.nonempty_Idx d N
  have hu1 : u < 1 := huu'.trans_lt hu'1
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  have hz' : (zt E u').im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu'1
  have hηu : 0 < etaT E u := etaT_pos_of_lt_one' hE hu1
  have hηu' : 0 < etaT E u' := etaT_pos_of_lt_one' hE hu'1
  have hηmono : etaT E u' ≤ etaT E u := etaT_le_of_le hE huu'
  have hinv : (etaT E u)⁻¹ ≤ (etaT E u')⁻¹ := inv_anti₀ hηu' hηmono
  refine ⟨le_add_of_nonneg_right (by positivity), ?_, ?_, ?_⟩
  · intro s
    have h := norm_Gsig_le hM hz s
    rw [← etaT_eq_zt_im, abs_of_pos hηu] at h
    linarith
  · intro s
    have h := norm_Gsig_le hM hz' s
    rw [← etaT_eq_zt_im, abs_of_pos hηu'] at h
    linarith
  · intro s
    have h1 := norm_Gsig_sub_le_norm_green_sub hM hM (z₁ := zt E u) (z₂ := zt E u') s
    have h2 := norm_green_sub_le hM hM hz hz'
    have hzz : ‖zt E u - zt E u'‖ = u' - u := by
      rw [norm_zt_sub hE.le, abs_of_nonpos (by linarith : u - u' ≤ 0)]; ring
    rw [sub_self, norm_zero, zero_add, hzz] at h2
    have hgu : ‖green M (zt E u)‖ ≤ 1 + (etaT E u')⁻¹ := by
      have h := RBM.norm_green_le hM hz
      rw [← etaT_eq_zt_im, abs_of_pos hηu] at h
      linarith
    have hgu' : ‖green M (zt E u')‖ ≤ 1 + (etaT E u')⁻¹ := by
      have h := RBM.norm_green_le hM hz'
      rw [← etaT_eq_zt_im, abs_of_pos hηu'] at h
      linarith
    have hune : 0 ≤ u' - u := by linarith
    calc ‖Gsig M (zt E u) s - Gsig M (zt E u') s‖
        ≤ ‖green M (zt E u) - green M (zt E u')‖ := h1
      _ ≤ ‖green M (zt E u)‖ * (u' - u) * ‖green M (zt E u')‖ := h2
      _ ≤ (1 + (etaT E u')⁻¹) * (u' - u) * (1 + (etaT E u')⁻¹) := by
          gcongr
      _ = (1 + (etaT E u')⁻¹) ^ 2 * (u' - u) := by ring

/-- **The `loopCut` time-Lipschitz bound**, at a fixed Hermitian `M`, for a `2`-loop index
`I` (`I.a.length = 2`) and either edge `k < 2`.  This is the deterministic core of (T1): the
resolvent identity `G(z) - G(z') = (z-z') G(z) G(z')` telescoped through the (at most
length-`1`) sub-products `prodList` on either side of the cut. -/
private theorem norm_loopCut_time_sub_le {E u u' : ℝ} (hE : |E| < 2) (huu' : u ≤ u')
    (hu'1 : u' < 1) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {I : LoopIdx (ZMod (d.L N))} (hlen : I.a.length = 2) (hwf : I.WF) {k : ℕ} (hk : k < 2) :
    ‖loopCut (d.L N) (d.W N) M (zt E u) I k - loopCut (d.L N) (d.W N) M (zt E u') I k‖
      ≤ 4 * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u) := by
  set K : ℝ := 1 + (etaT E u')⁻¹ with hKdef
  set Δ : ℝ := K ^ 2 * (u' - u) with hΔdef
  obtain ⟨hK1, hGu, hGu', hGsub⟩ := gsig_bounds (d := d) (N := N) hE huu' hu'1 hM
  have hΔ0 : 0 ≤ Δ := by
    have : 0 ≤ u' - u := by linarith
    rw [hΔdef]; positivity
  set lp : List (Bool × ZMod (d.L N)) := I.σ.zip I.a with hlp
  have hlplen : lp.length = 2 := by rw [hlp, List.length_zip, hwf, hlen, min_self]
  set s0 : Bool := (lp.getD k (true, 0)).1 with hs0
  set b0 : ZMod (d.L N) := (lp.getD k (true, 0)).2 with hb0
  set P1 : Matrix (d.Idx N) (d.Idx N) ℂ := prodList (d.L N) (d.W N) M (zt E u) (lp.drop (k + 1))
    with hP1
  set P1' : Matrix (d.Idx N) (d.Idx N) ℂ :=
    prodList (d.L N) (d.W N) M (zt E u') (lp.drop (k + 1)) with hP1'
  set P2 : Matrix (d.Idx N) (d.Idx N) ℂ := prodList (d.L N) (d.W N) M (zt E u) (lp.take k)
    with hP2
  set P2' : Matrix (d.Idx N) (d.Idx N) ℂ := prodList (d.L N) (d.W N) M (zt E u') (lp.take k)
    with hP2'
  have hn1 : (lp.drop (k + 1)).length ≤ 1 := by
    rw [List.length_drop, hlplen]; omega
  have hn2 : (lp.take k).length ≤ 1 := by
    rw [List.length_take, hlplen]; omega
  have hgenpow : ∀ n : ℕ, n ≤ 1 → K ^ n ≤ K := by
    intro n hn; interval_cases n
    · rw [pow_zero]; exact hK1
    · simp
  have hgen : ∀ n : ℕ, n ≤ 1 → (n : ℝ) * K ^ n ≤ K := by
    intro n hn; interval_cases n
    · simp; linarith
    · simp
  have hP1K1 : ‖P1‖ ≤ K :=
    (norm_prodList_le_pow (by positivity) hGu (lp.drop (k + 1))).trans (hgenpow _ hn1)
  have hP1'K1 : ‖P1'‖ ≤ K :=
    (norm_prodList_le_pow (by positivity) hGu' (lp.drop (k + 1))).trans (hgenpow _ hn1)
  have hP2K1 : ‖P2‖ ≤ K :=
    (norm_prodList_le_pow (by positivity) hGu (lp.take k)).trans (hgenpow _ hn2)
  have hP2'K1 : ‖P2'‖ ≤ K :=
    (norm_prodList_le_pow (by positivity) hGu' (lp.take k)).trans (hgenpow _ hn2)
  have hP1subK : ‖P1 - P1'‖ ≤ K * Δ :=
    (norm_prodList_sub_le hK1 hΔ0 hGu hGu' hGsub (lp.drop (k + 1))).trans
      (mul_le_mul_of_nonneg_right (hgen _ hn1) hΔ0)
  have hP2subK : ‖P2 - P2'‖ ≤ K * Δ :=
    (norm_prodList_sub_le hK1 hΔ0 hGu hGu' hGsub (lp.take k)).trans
      (mul_le_mul_of_nonneg_right (hgen _ hn2) hΔ0)
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hXK : ‖Gsig M (zt E u) s0‖ ≤ K := hGu s0
  have hX'K : ‖Gsig M (zt E u') s0‖ ≤ K := hGu' s0
  have hXsub : ‖Gsig M (zt E u) s0 - Gsig M (zt E u') s0‖ ≤ Δ := hGsub s0
  have hAK : ‖Eblk (d.L N) (d.W N) b0‖ ≤ 1 := norm_Eblk_le_one b0
  have hLCu : loopCut (d.L N) (d.W N) M (zt E u) I k
      = Gsig M (zt E u) s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 * Gsig M (zt E u) s0 := rfl
  have hLCu' : loopCut (d.L N) (d.W N) M (zt E u') I k
      = Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * P2' * Gsig M (zt E u') s0 := rfl
  rw [hLCu, hLCu']
  have hsplit :
      Gsig M (zt E u) s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 * Gsig M (zt E u) s0
        - Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * P2' * Gsig M (zt E u') s0
      = (Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
            Gsig M (zt E u) s0
        + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
            (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)
        + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 *
            Gsig M (zt E u') s0
        + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * (P2 - P2') *
            Gsig M (zt E u') s0 := by
    noncomm_ring
  rw [hsplit]
  have hT1 : ‖(Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
        Gsig M (zt E u) s0‖ ≤ Δ * K ^ 3 := by
    calc ‖(Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
          Gsig M (zt E u) s0‖
        ≤ ‖Gsig M (zt E u) s0 - Gsig M (zt E u') s0‖ * ‖Eblk (d.L N) (d.W N) b0‖ *
            ‖P1‖ * ‖P2‖ * ‖Gsig M (zt E u) s0‖ := by
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ Δ * 1 * K * K * K :=
          mul_le_mul
            (mul_le_mul (mul_le_mul (mul_le_mul hXsub hAK (norm_nonneg _) hΔ0) hP1K1
              (norm_nonneg _) (by positivity)) hP2K1 (norm_nonneg _) (by positivity))
            hXK (norm_nonneg _) (by positivity)
      _ = Δ * K ^ 3 := by ring
  have hT2 : ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
        (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)‖ ≤ Δ * K ^ 3 := by
    calc ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
          (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)‖
        ≤ ‖Gsig M (zt E u') s0‖ * ‖Eblk (d.L N) (d.W N) b0‖ * ‖P1‖ * ‖P2‖ *
            ‖Gsig M (zt E u) s0 - Gsig M (zt E u') s0‖ := by
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ K * 1 * K * K * Δ :=
          mul_le_mul
            (mul_le_mul (mul_le_mul (mul_le_mul hX'K hAK (norm_nonneg _) hK0) hP1K1
              (norm_nonneg _) (by positivity)) hP2K1 (norm_nonneg _) (by positivity))
            hXsub (norm_nonneg _) (by positivity)
      _ = Δ * K ^ 3 := by ring
  have hT3 : ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 *
        Gsig M (zt E u') s0‖ ≤ Δ * K ^ 4 := by
    calc ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 *
          Gsig M (zt E u') s0‖
        ≤ ‖Gsig M (zt E u') s0‖ * ‖Eblk (d.L N) (d.W N) b0‖ * ‖P1 - P1'‖ * ‖P2‖ *
            ‖Gsig M (zt E u') s0‖ := by
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ K * 1 * (K * Δ) * K * K :=
          mul_le_mul
            (mul_le_mul (mul_le_mul (mul_le_mul hX'K hAK (norm_nonneg _) hK0) hP1subK
              (norm_nonneg _) (by positivity)) hP2K1 (norm_nonneg _) (by positivity))
            hX'K (norm_nonneg _) (by positivity)
      _ = Δ * K ^ 4 := by ring
  have hT4 : ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * (P2 - P2') *
        Gsig M (zt E u') s0‖ ≤ Δ * K ^ 4 := by
    calc ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * (P2 - P2') *
          Gsig M (zt E u') s0‖
        ≤ ‖Gsig M (zt E u') s0‖ * ‖Eblk (d.L N) (d.W N) b0‖ * ‖P1'‖ * ‖P2 - P2'‖ *
            ‖Gsig M (zt E u') s0‖ := by
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ K * 1 * K * (K * Δ) * K :=
          mul_le_mul
            (mul_le_mul (mul_le_mul (mul_le_mul hX'K hAK (norm_nonneg _) hK0) hP1'K1
              (norm_nonneg _) (by positivity)) hP2subK (norm_nonneg _) (by positivity))
            hX'K (norm_nonneg _) (by positivity)
      _ = Δ * K ^ 4 := by ring
  have hsum := norm_add_le
    ((Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
        Gsig M (zt E u) s0
      + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
          (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)
      + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 * Gsig M (zt E u') s0)
    (Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * (P2 - P2') * Gsig M (zt E u') s0)
  have hsum2 := norm_add_le
    ((Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
      Gsig M (zt E u) s0)
    (Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
      (Gsig M (zt E u) s0 - Gsig M (zt E u') s0))
  have hsum3 := norm_add_le
    ((Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
        Gsig M (zt E u) s0
      + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
          (Gsig M (zt E u) s0 - Gsig M (zt E u') s0))
    (Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 * Gsig M (zt E u') s0)
  have hKpow : Δ * K ^ 3 + Δ * K ^ 3 + Δ * K ^ 4 + Δ * K ^ 4 ≤ 4 * K ^ 6 * (u' - u) := by
    have hK3 : K ^ 3 ≤ K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
    have hΔeq : Δ = K ^ 2 * (u' - u) := hΔdef
    nlinarith [hΔeq, hK3, hΔ0, sq_nonneg K]
  calc ‖(Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
          Gsig M (zt E u) s0
        + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
            (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)
        + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 *
            Gsig M (zt E u') s0
        + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * (P2 - P2') *
            Gsig M (zt E u') s0‖
      ≤ ‖(Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
            Gsig M (zt E u) s0
          + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
              (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)
          + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 *
              Gsig M (zt E u') s0‖
        + ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1' * (P2 - P2') *
            Gsig M (zt E u') s0‖ := hsum
    _ ≤ (‖(Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
            Gsig M (zt E u) s0
          + Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
              (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)‖
          + ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * (P1 - P1') * P2 *
              Gsig M (zt E u') s0‖) + Δ * K ^ 4 := add_le_add hsum3 hT4
    _ ≤ ((‖(Gsig M (zt E u) s0 - Gsig M (zt E u') s0) * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
              Gsig M (zt E u) s0‖
          + ‖Gsig M (zt E u') s0 * Eblk (d.L N) (d.W N) b0 * P1 * P2 *
              (Gsig M (zt E u) s0 - Gsig M (zt E u') s0)‖) + Δ * K ^ 4) + Δ * K ^ 4 :=
        add_le_add (add_le_add hsum2 hT3) le_rfl
    _ ≤ ((Δ * K ^ 3 + Δ * K ^ 3) + Δ * K ^ 4) + Δ * K ^ 4 :=
        add_le_add (add_le_add (add_le_add hT1 hT2) le_rfl) le_rfl
    _ ≤ 4 * K ^ 6 * (u' - u) := hKpow

/-- **The uniform (`q`-independent) time-shift bound for `coordD1(loopObs)`.** -/
private theorem norm_coordD1_loopObs_time_sub_le {E u u' : ℝ} (hE : |E| < 2) (huu' : u ≤ u')
    (hu'1 : u' < 1) {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    {I : LoopIdx (ZMod (d.L N))} (hlen : I.a.length = 2) (hwf : I.WF)
    {q : d.Idx N × d.Idx N × Bool} (hq : q ∈ usedCoord d N) :
    ‖coordD1 d N (loopObs d N (zt E u') I) M q - coordD1 d N (loopObs d N (zt E u) I) M q‖
      ≤ 16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u) := by
  have hu1 : u < 1 := huu'.trans_lt hu'1
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  have hz' : (zt E u').im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu'1
  obtain ⟨i, j, b⟩ := q
  have hb : i ≠ j ∨ b = true := by
    rcases mem_usedCoord.1 hq with h | h
    · exact Or.inl fun he => absurd (he ▸ h) (lt_irrefl _)
    · exact Or.inr h.2
  have heq_u := coordD1_loopObs_eq hz hM hwf i j b hb
  have heq_u' := coordD1_loopObs_eq hz' hM hwf i j b hb
  rw [heq_u, heq_u']
  have hcard0 : (0 : ℝ) ≤ (Fintype.card (d.Idx N) : ℝ) := Nat.cast_nonneg _
  have hdiff :
      -(∑ k ∈ Finset.range I.a.length,
          Matrix.trace (Bmat d N i j b * loopCut (d.L N) (d.W N) M (zt E u') I k))
        - -(∑ k ∈ Finset.range I.a.length,
          Matrix.trace (Bmat d N i j b * loopCut (d.L N) (d.W N) M (zt E u) I k))
      = ∑ k ∈ Finset.range I.a.length,
          Matrix.trace (Bmat d N i j b *
            (loopCut (d.L N) (d.W N) M (zt E u) I k
              - loopCut (d.L N) (d.W N) M (zt E u') I k)) := by
    rw [neg_sub_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_sub, Matrix.trace_sub]
  rw [hdiff, hlen]
  have hbound : ∀ k ∈ Finset.range 2,
      ‖Matrix.trace (Bmat d N i j b *
        (loopCut (d.L N) (d.W N) M (zt E u) I k - loopCut (d.L N) (d.W N) M (zt E u') I k))‖
        ≤ (Fintype.card (d.Idx N) : ℝ) * (2 * (4 * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u))) := by
    intro k hk
    have hk2 : k < 2 := Finset.mem_range.mp hk
    have h1 := norm_trace_le_card_mul
      (Bmat d N i j b * (loopCut (d.L N) (d.W N) M (zt E u) I k
        - loopCut (d.L N) (d.W N) M (zt E u') I k))
    have h2 : ‖Bmat d N i j b *
        (loopCut (d.L N) (d.W N) M (zt E u) I k - loopCut (d.L N) (d.W N) M (zt E u') I k)‖
        ≤ 2 * (4 * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul (norm_Bmat_le_two d N i j b)
        (norm_loopCut_time_sub_le hE huu' hu'1 hM hlen hwf hk2) (norm_nonneg _) (by norm_num)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hcard0)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.range 2, ‖Matrix.trace (Bmat d N i j b *
        (loopCut (d.L N) (d.W N) M (zt E u) I k - loopCut (d.L N) (d.W N) M (zt E u') I k))‖
      ≤ ∑ _k ∈ Finset.range 2,
          (Fintype.card (d.Idx N) : ℝ) * (2 * (4 * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u))) :=
        Finset.sum_le_sum hbound
    _ = 2 * ((Fintype.card (d.Idx N) : ℝ) *
          (2 * (4 * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)))) := by
        rw [Finset.sum_const, Finset.card_range]; ring
    _ = 16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u) := by ring

end LoopCutTime

/-! ### §3 : (T1) the explicit time-shift bound for `√quadVar` -/

section T1

variable {d : Dims} {N : ℕ}

/-- **The explicit constant `Csh` of (T1)`, at most polynomial in `Fintype.card (d.Idx N)`
and `(etaT E u')⁻¹`. -/
noncomputable def qvTimeShiftConst (d : Dims) (N : ℕ) (E u' : ℝ) : ℝ :=
  16 * Real.sqrt 2 * (Fintype.card (d.Idx N) : ℝ) ^ 2 * (1 + (etaT E u')⁻¹) ^ 6

theorem qvTimeShiftConst_nonneg (d : Dims) (N : ℕ) (E u' : ℝ) :
    0 ≤ qvTimeShiftConst d N E u' := by unfold qvTimeShiftConst; positivity

/-- **(T1)**: `RBM.Gauss.Grid.sqrt_quadVar_time_shift`.  For `|E| < 2`, `0 ≤ u ≤ u' < 1`,
Hermitian `M`, and every `2`-loop `a`,
`√(quadVar Φ_{u',a} M) ≤ √(quadVar Φ_{u,a} M) + Csh · (u' - u)`. -/
theorem sqrt_quadVar_time_shift (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2) {u u' : ℝ}
    (_hu0 : 0 ≤ u) (huu' : u ≤ u') (hu'1 : u' < 1) {M : Matrix (d.Idx N) (d.Idx N) ℂ}
    (hM : M.IsHermitian) (a : LoopArg (d.L N) 2) :
    Real.sqrt (Gauss.quadVar d N
        (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N u' M' Step2.sigPM a) M)
      ≤ Real.sqrt (Gauss.quadVar d N
            (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N u M' Step2.sigPM a) M)
          + qvTimeShiftConst d N E u' * (u' - u) := by
  have hu1 : u < 1 := huu'.trans_lt hu'1
  have hz : (zt E u).im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu1
  have hz' : (zt E u').im ≠ 0 := zt_im_ne_zero_of_lt_one hE hu'1
  set I : LoopIdx (ZMod (d.L N)) := toIdx Step2.sigPM a with hIdef
  have hwf : I.WF := toIdx_wf Step2.sigPM a
  have hlen : I.a.length = 2 := toIdx_length Step2.sigPM a
  have hcoordu : ∀ q ∈ usedCoord d N,
      coordD1 d N (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N u M' Step2.sigPM a) M q
        = coordD1 d N (loopObs d N (zt E u) I) M q :=
    fun q hq => EarlyQVRate.coordD1_lkFun_eq (B := Gauss.band d) hz Step2.sigPM hM a
      (q := q) hq
  have hcoordu' : ∀ q ∈ usedCoord d N,
      coordD1 d N (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N u' M' Step2.sigPM a) M q
        = coordD1 d N (loopObs d N (zt E u') I) M q :=
    fun q hq => EarlyQVRate.coordD1_lkFun_eq (B := Gauss.band d) hz' Step2.sigPM hM a
      (q := q) hq
  set F : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    fun M' => MomentDuhamel.lkFun (Gauss.band d) E N u M' Step2.sigPM a with hF
  set G : Matrix (d.Idx N) (d.Idx N) ℂ → ℂ :=
    fun M' => MomentDuhamel.lkFun (Gauss.band d) E N u' M' Step2.sigPM a with hG
  set x : d.Idx N × d.Idx N × Bool → ℝ := fun q => ‖coordD1 d N F M q‖ with hx
  set y : d.Idx N × d.Idx N × Bool → ℝ :=
    fun q => ‖coordD1 d N G M q‖ - ‖coordD1 d N F M q‖ with hy
  have hquadG : Gauss.quadVar d N G M
      = ∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * (x q + y q) ^ 2 := by
    rw [Gauss.quadVar]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 2
    rw [hx, hy]; ring
  have hquadF : Gauss.quadVar d N F M
      = ∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * x q ^ 2 := rfl
  have hmink := sqrt_wsum_add_le (usedCoord d N) (fun q => (Gauss.gvar d (Gauss.crd d N q) : ℝ))
    (fun q _ => (Gauss.gvar d (Gauss.crd d N q)).2) x y
  rw [← hquadF, ← hquadG] at hmink
  have hyabs : ∀ q ∈ usedCoord d N,
      |y q| ≤ 16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u) := by
    intro q hq
    have h1 : y q = ‖coordD1 d N (loopObs d N (zt E u') I) M q‖
        - ‖coordD1 d N (loopObs d N (zt E u) I) M q‖ := by
      simp only [hy, hcoordu q hq, hcoordu' q hq]
    have h2 := norm_coordD1_loopObs_time_sub_le hE huu' hu'1 hM hlen hwf hq
    rw [h1]
    calc |‖coordD1 d N (loopObs d N (zt E u') I) M q‖
          - ‖coordD1 d N (loopObs d N (zt E u) I) M q‖|
        ≤ ‖coordD1 d N (loopObs d N (zt E u') I) M q
            - coordD1 d N (loopObs d N (zt E u) I) M q‖ := abs_norm_sub_norm_le _ _
      _ ≤ 16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u) := h2
  have hCbig : 0 ≤ 16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u) := by
    have : 0 ≤ u' - u := by linarith
    positivity
  have hsum2S : ∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * y q ^ 2
      ≤ (16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) ^ 2 *
        (2 * (Fintype.card (d.Idx N) : ℝ) ^ 2) := by
    calc ∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * y q ^ 2
        ≤ ∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) *
            (16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) ^ 2 := by
          refine Finset.sum_le_sum fun q hq => ?_
          refine mul_le_mul_of_nonneg_left ?_ (Gauss.gvar d (Gauss.crd d N q)).2
          have := hyabs q hq
          calc y q ^ 2 = |y q| ^ 2 := (sq_abs _).symm
            _ ≤ (16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = (∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ)) *
            (16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) ^ 2 := by
          rw [Finset.sum_mul]
      _ ≤ (2 * (Fintype.card (d.Idx N) : ℝ) ^ 2) *
            (16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) ^ 2 :=
          mul_le_mul_of_nonneg_right (sum_gvar_usedCoord_le d N) (by positivity)
      _ = _ := by ring
  have hsqrt2card : Real.sqrt (2 * (Fintype.card (d.Idx N) : ℝ) ^ 2)
      = Real.sqrt 2 * (Fintype.card (d.Idx N) : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq (by positivity)]
  have hy2 : Real.sqrt (∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * y q ^ 2)
      ≤ qvTimeShiftConst d N E u' * (u' - u) := by
    have hstep : Real.sqrt (∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * y q ^ 2)
        ≤ (16 * (Fintype.card (d.Idx N) : ℝ) * (1 + (etaT E u')⁻¹) ^ 6 * (u' - u)) *
          (Real.sqrt 2 * (Fintype.card (d.Idx N) : ℝ)) := by
      have hpre := Real.sqrt_le_sqrt hsum2S
      rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq hCbig, hsqrt2card] at hpre
    refine hstep.trans_eq ?_
    rw [qvTimeShiftConst]; ring
  calc Real.sqrt (Gauss.quadVar d N G M)
      ≤ Real.sqrt (Gauss.quadVar d N F M) +
          Real.sqrt (∑ q ∈ usedCoord d N, (Gauss.gvar d (Gauss.crd d N q) : ℝ) * y q ^ 2) := hmink
    _ ≤ Real.sqrt (Gauss.quadVar d N F M) + qvTimeShiftConst d N E u' * (u' - u) :=
        add_le_add (le_refl _) hy2

end T1

/-! ### §4 : (T2) monotonicity of `diagShape'`/`nearEpsilon` in `J`, and the drop-indicator
bound -/

section T2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `diagFarRate` is monotone increasing in `J`, for `J ≥ 0`. -/
private theorem diagFarRate_mono_J (B : Band Ω) (N : ℕ) {ℓu ηu D J J' Smax : ℝ}
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hW1 : 1 ≤ (B.W N : ℝ)) (hJ : 0 ≤ J) (hJJ' : J ≤ J')
    (_hSmax : 0 ≤ Smax) :
    APrimeQVEndpoint.diagFarRate B N ℓu ηu D J Smax
      ≤ APrimeQVEndpoint.diagFarRate B N ℓu ηu D J' Smax := by
  have hcfar := Lemma57.cFar2_nonneg hW1 hℓu
  have hsq : (2 * J) ^ 2 ≤ (2 * J') ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hcube : (2 * J) ^ 3 ≤ (2 * J') ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hc1 : (0 : ℝ) ≤ 2 * ηu⁻¹ *
      (Lemma57.cFar2 (B.W N : ℝ) ℓu * ((B.W N : ℝ) * ℓu * ηu * (2 * Real.sqrt Smax))) := by
    positivity
  have hc23 : (0 : ℝ) ≤ 2 * ηu⁻¹ * 72 * ((B.W N : ℝ) * ℓu * ηu)⁻¹
      + 4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) := by
    positivity
  have hexpand : ∀ x : ℝ, APrimeQVEndpoint.diagFarRate B N ℓu ηu D x Smax
      = (2 * ηu⁻¹ * (Lemma57.cFar2 (B.W N : ℝ) ℓu *
            ((B.W N : ℝ) * ℓu * ηu * (2 * Real.sqrt Smax)))) * (2 * x) ^ 2
        + (2 * ηu⁻¹ * 72 * ((B.W N : ℝ) * ℓu * ηu)⁻¹
            + 4 * (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D)) * (2 * x) ^ 3 := by
    intro x; unfold APrimeQVEndpoint.diagFarRate; ring
  rw [hexpand, hexpand]
  nlinarith [mul_le_mul_of_nonneg_left hsq hc1, mul_le_mul_of_nonneg_left hcube hc23]

/-- **(T2)**: `RBM.Gauss.Grid.diagShape'_mono_J`.  `diagShape'` is monotone increasing in its
`J` argument, for `J ≥ 0`. -/
theorem diagShape'_mono_J (B : Band Ω) (N : ℕ) {ℓu ℓs ηu D J J' Smax ε : ℝ}
    (hℓu : 0 < ℓu) (hηu : 0 < ηu) (hW1 : 1 ≤ (B.W N : ℝ)) (hJ : 0 ≤ J) (hJJ' : J ≤ J')
    (hSmax : 0 ≤ Smax) (b : LoopArg (B.L N) (0 + 2)) :
    APrimeQVEndpoint.diagShape' B N ℓu ℓs ηu D J Smax ε b
      ≤ APrimeQVEndpoint.diagShape' B N ℓu ℓs ηu D J' Smax ε b := by
  unfold APrimeQVEndpoint.diagShape'
  have hT2 : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2 := sq_nonneg _
  have hfar := diagFarRate_mono_J B N (D := D) hℓu hηu hW1 hJ hJJ' hSmax
  nlinarith [mul_le_mul_of_nonneg_right hfar hT2]

/-- `diagShape'` is monotone increasing in its `ε` argument, for `ε ≥ 0`. -/
private theorem diagShape'_mono_eps (B : Band Ω) (N : ℕ) {ℓu ℓs ηu D J Smax ε ε' : ℝ}
    (_hε : 0 ≤ ε) (hεε' : ε ≤ ε') (b : LoopArg (B.L N) (0 + 2)) :
    APrimeQVEndpoint.diagShape' B N ℓu ℓs ηu D J Smax ε b
      ≤ APrimeQVEndpoint.diagShape' B N ℓu ℓs ηu D J Smax ε' b := by
  unfold APrimeQVEndpoint.diagShape'
  have hT2 : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2 := sq_nonneg _
  have hχ01 : (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
      then (1 : ℝ) else 0) ≤ 1 ∧ 0 ≤
      (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
        then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  nlinarith [mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) * ε ≤ 2 * ε') hχ01.2) hT2, hT2, hχ01.1,
    hχ01.2]

/-- **(T2)**: `nearEpsilon` is monotone increasing in its `J` argument, for `J ≥ 0`. -/
theorem nearEpsilon_mono_J {W L ℓu ηu D J J' : ℝ} (hW0 : 0 ≤ W) (hL0 : 0 ≤ L)
    (hJ : 0 ≤ J) (hJJ' : J ≤ J') :
    EEDef.nearEpsilon W L ℓu ηu D J ≤ EEDef.nearEpsilon W L ℓu ηu D J' := by
  have hsq : J ^ 2 ≤ J' ^ 2 := pow_le_pow_left₀ hJ hJJ' 2
  have hc : (0 : ℝ) ≤ W * L * (2 * ηu⁻¹ ^ 2 *
        tailT W ℓu ηu D (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) ^ 2) *
      (W * ℓu * ηu) ^ 4 * Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) := by
    have hWL : (0 : ℝ) ≤ W * L := mul_nonneg hW0 hL0
    have hA : (0 : ℝ) ≤ 2 * ηu⁻¹ ^ 2 *
        tailT W ℓu ηu D (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) ^ 2 := by positivity
    have hB : (0 : ℝ) ≤ (W * ℓu * ηu) ^ 4 := by positivity
    have hC : (0 : ℝ) ≤ Real.exp (4 * Real.log W ^ (3 / 4 : ℝ)) := (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hWL hA) hB) hC
  have hexpand : ∀ x : ℝ, EEDef.nearEpsilon W L ℓu ηu D x
      = (W * L * (2 * ηu⁻¹ ^ 2 *
            tailT W ℓu ηu D (Lemma57.ellStarStar W ℓu - 4 * ellStar W ℓu) ^ 2) *
          (W * ℓu * ηu) ^ 4 * Real.exp (4 * Real.log W ^ (3 / 4 : ℝ))) * x ^ 2 := by
    intro x; unfold EEDef.nearEpsilon; ring
  rw [hexpand, hexpand]
  exact mul_le_mul_of_nonneg_left hsq hc

/-- **(T2)**: the "drop the indicator" bound:
`diagShape' ≤ (diagNearRate + 2ε + diagFarRate) · T²`. -/
theorem diagShape'_le_dropIndicator (B : Band Ω) (N : ℕ) {ℓu ℓs ηu D J Smax ε : ℝ}
    (hW1 : 1 ≤ (B.W N : ℝ)) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs) (hηu : 0 < ηu) (hε : 0 ≤ ε)
    (b : LoopArg (B.L N) (0 + 2)) :
    APrimeQVEndpoint.diagShape' B N ℓu ℓs ηu D J Smax ε b
      ≤ (APrimeQVEndpoint.diagNearRate B N ℓu ℓs ηu + 2 * ε
          + APrimeQVEndpoint.diagFarRate B N ℓu ηu D J Smax) *
        tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2 := by
  unfold APrimeQVEndpoint.diagShape'
  have hnear0 : 0 ≤ APrimeQVEndpoint.diagNearRate B N ℓu ℓs ηu := by
    unfold APrimeQVEndpoint.diagNearRate
    have := Lemma57.cNear2_nonneg hW1 hℓu
    positivity
  have hχ01 : (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu
      then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hT2 : (0 : ℝ) ≤ tailT (B.W N : ℝ) ℓu ηu D (zdist (B.L N) (b 0 - b 1)) ^ 2 := sq_nonneg _
  have hstep : (APrimeQVEndpoint.diagNearRate B N ℓu ℓs ηu + 2 * ε) *
        (if (zdist (B.L N) (b 0 - b 1) : ℝ) ≤ 4 * ellStar (B.W N : ℝ) ℓu then (1 : ℝ) else 0)
      ≤ APrimeQVEndpoint.diagNearRate B N ℓu ℓs ηu + 2 * ε :=
    mul_le_of_le_one_right (by linarith) hχ01
  nlinarith [mul_le_mul_of_nonneg_right hstep hT2]

end T2

/-! ### §5 : (T3) the one-step quadratic-variation bound -/

section T3

/-- **(T3)**: `RBM.Gauss.Grid.quadVar_step_le`.  `Q'` is written out in full (no new
definition), matching the ticket's displayed formula exactly. -/
theorem quadVar_step_le (d : Dims) (N : ℕ) {E : ℝ} (hE : |E| < 2)
    {uj Δ : ℝ} (huj0 : 0 ≤ uj) (hΔ : 0 ≤ Δ) (hu'1 : uj + Δ < 1)
    {D J' J τ ℓs : ℝ} (_hD0 : 0 ≤ D) (hℓs : 0 < ℓs) (hJ'0 : 0 ≤ J') (hJ'J : J' ≤ J)
    {M : Matrix (d.Idx N) (d.Idx N) ℂ} (hM : M.IsHermitian)
    (hqv : ∀ a : LoopArg (d.L N) 2,
      Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N uj M' Step2.sigPM a) M
        ≤ (N : ℝ) ^ τ * APrimeQVEndpoint.diagShape' (Gauss.band d) N
            ((Gauss.band d).ell N uj) ℓs (etaT E uj) D J'
            (EarlyQVRateEv.sDet (Gauss.band d) E N uj ℓs)
            (EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
              ((Gauss.band d).ell N uj) (etaT E uj) D J') a) :
    ∀ a : LoopArg (d.L N) 2,
      Gauss.quadVar d N
          (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N (uj + Δ) M' Step2.sigPM a) M
        ≤ (2 * (N : ℝ) ^ τ *
              (APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
                  (etaT E uj)
                + 2 * EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
                    ((Gauss.band d).ell N uj) (etaT E uj) D J
                + APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj)
                    (etaT E uj) D J (EarlyQVRateEv.sDet (Gauss.band d) E N uj ℓs))
            + 2 * qvTimeShiftConst d N E (uj + Δ) ^ 2 * Δ ^ 2 *
                ((Gauss.band d).W N : ℝ) ^ (2 * D)) *
          tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
            (zdist (d.L N) (a 0 - a 1)) ^ 2 := by
  intro a
  have huj1 : uj < 1 := by linarith
  have huu' : uj ≤ uj + Δ := by linarith
  have hJ0 : 0 ≤ J := hJ'0.trans hJ'J
  have hL1 : 1 ≤ d.L N := by have := d.three_le_L N; omega
  have hℓu : 0 < (Gauss.band d).ell N uj :=
    lt_of_lt_of_le zero_lt_one (one_le_ellHat_of_nonneg hL1 huj0 huj1)
  have hηu : 0 < etaT E uj := etaT_pos_of_lt_one' hE huj1
  have hW1 : 1 ≤ ((Gauss.band d).W N : ℝ) := by
    have := d.W_pos N; exact_mod_cast this
  set Smax : ℝ := EarlyQVRateEv.sDet (Gauss.band d) E N uj ℓs with hSmaxdef
  set nJ' : ℝ := EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
      ((Gauss.band d).ell N uj) (etaT E uj) D J' with hnJ'def
  set nJ : ℝ := EEDef.nearEpsilon ((Gauss.band d).W N : ℝ) ((Gauss.band d).L N : ℝ)
      ((Gauss.band d).ell N uj) (etaT E uj) D J with hnJdef
  have hnJ'0 : 0 ≤ nJ' := by rw [hnJ'def]; unfold EEDef.nearEpsilon; positivity
  have hnJ0 : 0 ≤ nJ := by rw [hnJdef]; unfold EEDef.nearEpsilon; positivity
  have hεmono : nJ' ≤ nJ := by
    rw [hnJ'def, hnJdef]
    exact nearEpsilon_mono_J (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ'0 hJ'J
  -- (T1): the time-shift bound.
  have hT1 := sqrt_quadVar_time_shift d N hE huj0 huu' hu'1 hM a
  rw [show uj + Δ - uj = Δ from by ring] at hT1
  set Csh : ℝ := qvTimeShiftConst d N E (uj + Δ) with hCshdef
  set QVu : ℝ := Gauss.quadVar d N
      (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N uj M' Step2.sigPM a) M with hQVudef
  set QVu' : ℝ := Gauss.quadVar d N
      (fun M' => MomentDuhamel.lkFun (Gauss.band d) E N (uj + Δ) M' Step2.sigPM a) M
      with hQVu'def
  have hQVu0 : 0 ≤ QVu := Gauss.quadVar_nonneg _ _
  have hQVu'0 : 0 ≤ QVu' := Gauss.quadVar_nonneg _ _
  have hCsh0 : 0 ≤ Csh := qvTimeShiftConst_nonneg d N E (uj + Δ)
  have hsq : QVu' ≤ 2 * QVu + 2 * (Csh * Δ) ^ 2 := by
    have hsq1 : Real.sqrt QVu' ^ 2 ≤ (Real.sqrt QVu + Csh * Δ) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hT1 2
    have e1 : Real.sqrt QVu' ^ 2 = QVu' := Real.sq_sqrt hQVu'0
    have e2 : Real.sqrt QVu ^ 2 = QVu := Real.sq_sqrt hQVu0
    nlinarith [hsq1, e1, e2, sq_nonneg (Real.sqrt QVu - Csh * Δ)]
  -- (hqv): the pointwise bound at `u_j`, capped at `J'`.
  have hqva := hqv a
  rw [← hQVudef] at hqva
  -- (T2): the monotonicity chain `J' ↦ J`, both directly and through `nearEpsilon`.
  have hdsE : APrimeQVEndpoint.diagShape' (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
        (etaT E uj) D J' Smax nJ' a
      ≤ APrimeQVEndpoint.diagShape' (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
          (etaT E uj) D J' Smax nJ a :=
    diagShape'_mono_eps (Gauss.band d) N hnJ'0 hεmono a
  have hdsJ : APrimeQVEndpoint.diagShape' (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
        (etaT E uj) D J' Smax nJ a
      ≤ APrimeQVEndpoint.diagShape' (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
          (etaT E uj) D J Smax nJ a := by
    refine diagShape'_mono_J (Gauss.band d) N hℓu hηu hW1 hJ'0 hJ'J ?_ a
    rw [hSmaxdef]; exact EarlyQVRateEv.sDet_nonneg (Gauss.band d) E N huj0 huj1 hℓs
  have hdsSum : APrimeQVEndpoint.diagShape' (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
        (etaT E uj) D J Smax nJ a
      ≤ (APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs (etaT E uj)
          + 2 * nJ
          + APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj) (etaT E uj)
              D J Smax) *
        tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N uj) (etaT E uj) D
          (zdist (d.L N) (a 0 - a 1)) ^ 2 :=
    diagShape'_le_dropIndicator (Gauss.band d) N hW1 hℓu hℓs hηu hnJ0 a
  -- (T1510): `T_{u_j} ≤ T_{u_{j+1}}`.
  have htailmono : tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N uj) (etaT E uj) D
        (zdist (d.L N) (a 0 - a 1) : ℝ)
      ≤ tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
          (zdist (d.L N) (a 0 - a 1) : ℝ) :=
    tailT_mono_time (d.L N) (d.three_le_L N) (m := (mE E).im) (mE_im_pos hE) huj0 huu' hu'1
      (by positivity) (by positivity)
  have hW0 : (0 : ℝ) < ((Gauss.band d).W N : ℝ) := by linarith
  have htailmono2 : tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N uj) (etaT E uj) D
        (zdist (d.L N) (a 0 - a 1) : ℝ) ^ 2
      ≤ tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
          (zdist (d.L N) (a 0 - a 1) : ℝ) ^ 2 :=
    pow_le_pow_left₀ (tailT_nonneg hW0.le _) htailmono 2
  have hdNR0 : 0 ≤ APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
      (etaT E uj) := by
    unfold APrimeQVEndpoint.diagNearRate
    have := Lemma57.cNear2_nonneg hW1 hℓu
    positivity
  have hdFR0 : 0 ≤ APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj)
      (etaT E uj) D J Smax := by
    unfold APrimeQVEndpoint.diagFarRate
    have hcfar := Lemma57.cFar2_nonneg hW1 hℓu
    positivity
  have hcoef0 : 0 ≤ APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
        (etaT E uj) + 2 * nJ +
      APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj) (etaT E uj) D J
        Smax := by
    linarith [hdNR0, hnJ0, hdFR0]
  have hNτ0 : (0 : ℝ) ≤ (N : ℝ) ^ τ := by positivity
  have hchainA : QVu ≤ (N : ℝ) ^ τ *
      ((APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs (etaT E uj)
          + 2 * nJ
          + APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj) (etaT E uj)
              D J Smax) *
        tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N uj) (etaT E uj) D
          (zdist (d.L N) (a 0 - a 1)) ^ 2) := by
    calc QVu
        ≤ (N : ℝ) ^ τ * APrimeQVEndpoint.diagShape' (Gauss.band d) N
              ((Gauss.band d).ell N uj) ℓs (etaT E uj) D J' Smax nJ' a := hqva
      _ ≤ (N : ℝ) ^ τ * APrimeQVEndpoint.diagShape' (Gauss.band d) N
              ((Gauss.band d).ell N uj) ℓs (etaT E uj) D J' Smax nJ a :=
          mul_le_mul_of_nonneg_left hdsE hNτ0
      _ ≤ (N : ℝ) ^ τ * APrimeQVEndpoint.diagShape' (Gauss.band d) N
              ((Gauss.band d).ell N uj) ℓs (etaT E uj) D J Smax nJ a :=
          mul_le_mul_of_nonneg_left hdsJ hNτ0
      _ ≤ _ := mul_le_mul_of_nonneg_left hdsSum hNτ0
  have hchainB : QVu ≤ (N : ℝ) ^ τ *
      (APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs (etaT E uj)
          + 2 * nJ
          + APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj) (etaT E uj)
              D J Smax) *
      tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
        (zdist (d.L N) (a 0 - a 1)) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_left htailmono2 hcoef0
    calc QVu ≤ (N : ℝ) ^ τ *
        ((APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs (etaT E uj)
            + 2 * nJ
            + APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj) (etaT E uj)
                D J Smax) *
          tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N uj) (etaT E uj) D
            (zdist (d.L N) (a 0 - a 1)) ^ 2) := hchainA
      _ ≤ (N : ℝ) ^ τ *
          ((APrimeQVEndpoint.diagNearRate (Gauss.band d) N ((Gauss.band d).ell N uj) ℓs
              (etaT E uj)
              + 2 * nJ
              + APrimeQVEndpoint.diagFarRate (Gauss.band d) N ((Gauss.band d).ell N uj)
                  (etaT E uj) D J Smax) *
            tailT ((Gauss.band d).W N : ℝ) ((Gauss.band d).ell N (uj + Δ)) (etaT E (uj + Δ)) D
              (zdist (d.L N) (a 0 - a 1)) ^ 2) := mul_le_mul_of_nonneg_left hstep hNτ0
      _ = _ := by ring
  have hone := Cutoff.one_le_rpow_mul_tailT_sq
    (W := ((Gauss.band d).W N : ℝ)) (ℓu := (Gauss.band d).ell N (uj + Δ))
    (ηu := etaT E (uj + Δ)) (D := D) (ℓ := (zdist (d.L N) (a 0 - a 1) : ℝ)) hW1
  have hCshΔsq0 : (0 : ℝ) ≤ 2 * Csh ^ 2 * Δ ^ 2 := by positivity
  nlinarith [hsq, hchainB, mul_le_mul_of_nonneg_left hone hCshΔsq0]

end T3

end RBM.Gauss.Grid

#print axioms RBM.Gauss.Grid.sqrt_quadVar_time_shift
#print axioms RBM.Gauss.Grid.diagShape'_mono_J
#print axioms RBM.Gauss.Grid.nearEpsilon_mono_J
#print axioms RBM.Gauss.Grid.diagShape'_le_dropIndicator
#print axioms RBM.Gauss.Grid.quadVar_step_le
