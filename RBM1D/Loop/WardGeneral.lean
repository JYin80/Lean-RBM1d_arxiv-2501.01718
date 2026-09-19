/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Loop.WardStep
import RBM1D.Loop.Ward
import RBM1D.Loop.Cyclic

/-!
# Ward's identity for `K` at every length (Lemma 3.6, (3.13))

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, Lemma 3.6, (3.13): for any solution
`K` of Definition 2.12 with `m = m^{(E)}` on `[0, T₀]`, `T₀ < 1`, with bounded `2`-loops, and
every loop `(+, μ, -; a', x)`,
`∑_x K_{t,(+,μ,-),(a',x)} = (K_{t,(+,μ),a'} - K_{t,(-,μ),a'}) / (2 W i η_t)`.

The proof is the paper's: the defect `wD` satisfies the linear equation (3.18)
(`RBM.ward_rhs_identity` plus `∂_t κ_t = κ_t/(1-t)`, `W c_t = (1-t)⁻¹`) and vanishes at `t = 0`;
Grönwall and induction on the length.
-/

namespace RBM

open Finset LoopIdx

variable (L : ℕ) [NeZero L]

section Kappa

variable {E : ℝ}

/-- `κ_t = (2 W i η_t)⁻¹`. -/
noncomputable def wardKappa (W : ℕ) (E t : ℝ) : ℂ := (2 * W * Complex.I * etaT E t)⁻¹

theorem wardKappa_mul (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    wardKappa W E t * (mSigma E true - mSigma E false) = wardC W t := by
  rw [wardKappa, mSigma_true, mSigma_false, ← div_eq_inv_mul,
    show mE E - (starRingEnd ℂ) (mE E) = 1 * (mE E - (starRingEnd ℂ) (mE E)) by ring,
    sub_div_two_W_I_etaT W hE ht1, wardC, one_div]

theorem hasDerivAt_wardKappa (W : ℕ) [NeZero W] (hE : |E| < 2) {t : ℝ} (ht1 : t < 1) :
    HasDerivAt (wardKappa W E) (wardKappa W E t / (1 - t)) t := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hIm : ((mE E).im : ℂ) ≠ 0 := by exact_mod_cast (mE_im_pos hE).ne'
  have ht : (1 : ℂ) - t ≠ 0 := by
    rw [sub_ne_zero, ne_comm]
    exact_mod_cast ht1.ne
  have hg : HasDerivAt (fun s : ℝ => 2 * (W : ℂ) * Complex.I * (etaT E s : ℂ))
      (-(2 * (W : ℂ) * Complex.I * (mE E).im)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (etaT E s : ℂ)) (-((mE E).im : ℂ)) t := by
      have := (((hasDerivAt_id t).const_sub 1).mul_const (mE E).im).ofReal_comp
      simpa [etaT] using this
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1.const_mul (2 * (W : ℂ) * Complex.I)
  have hne : 2 * (W : ℂ) * Complex.I * (etaT E t : ℂ) ≠ 0 := by
    simp only [etaT]
    push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hW) Complex.I_ne_zero)
      (mul_ne_zero ht hIm)
  refine (hg.inv hne).congr_deriv ?_
  simp only [wardKappa, etaT]
  push_cast
  field_simp

end Kappa

section Init

/-- Summing the "all labels equal" indicator over the last label. -/
theorem sum_allEq_append (a' : List (ZMod L)) (ha : a' ≠ []) :
    ∑ x : ZMod L, (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then (1 : ℂ) else 0)
      = if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0 := by
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil ha
  have hh : h ∈ h :: t := List.mem_cons_self
  by_cases hall : ∀ y ∈ h :: t, ∀ z ∈ h :: t, y = z
  · rw [ite_eq_left hall]
    have key : ∀ x : ZMod L,
        (∀ y ∈ h :: t ++ [x], ∀ z ∈ h :: t ++ [x], y = z) ↔ x = h := by
      intro x
      constructor
      · intro hx
        exact hx x (List.mem_append_right _ (List.mem_singleton_self x)) h
          (List.mem_append_left _ hh)
      · intro hxh
        have hin : ∀ w ∈ h :: t ++ [x], w ∈ h :: t := by
          intro w hw
          rcases List.mem_append.mp hw with hw | hw
          · exact hw
          · rw [List.mem_singleton.mp hw, hxh]
            exact hh
        exact fun y hy z hz => hall y (hin y hy) z (hin z hz)
    simp only [key, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  · rw [ite_eq_right hall]
    refine Finset.sum_eq_zero fun x _ => ite_eq_right fun hx => hall fun y hy z hz =>
      hx y (List.mem_append_left _ hy) z (List.mem_append_left _ hz)

/-- **The initial value.**  At `t = 0`, (3.13) holds for the initial value of Definition 2.12. -/
theorem wD_primInit (W : ℕ) [NeZero W] {E : ℝ} (hE : |E| < 2) (μ : List Bool)
    (a' : List (ZMod L)) (hμ : μ.length + 1 = a'.length) :
    wD L (primInit L W (mSigma E)) (wardKappa W E 0) μ a' = 0 := by
  have ha : a' ≠ [] := by
    intro h
    rw [h] at hμ
    simp at hμ
  obtain ⟨N, hN⟩ : ∃ N, a'.length = N + 1 := ⟨a'.length - 1, by omega⟩
  have hfull : ∀ x : ZMod L, primInit L W (mSigma E) (fullLoop μ a' x)
      = (W : ℂ)⁻¹ ^ (N + 1) * (mSigma E true * (μ.map (mSigma E)).prod * mSigma E false) *
        (if ∀ y ∈ a' ++ [x], ∀ z ∈ a' ++ [x], y = z then 1 else 0) := by
    intro x
    simp only [primInit, fullLoop, LoopIdx.length, List.length_append, List.length_singleton,
      hN, Nat.add_sub_cancel, List.map_cons, List.map_append, List.map_nil, List.prod_cons,
      List.prod_append, List.prod_nil, mul_one, mul_assoc]
    rfl
  have hpm : ∀ s, primInit L W (mSigma E) (pmLoop s μ a')
      = (W : ℂ)⁻¹ ^ N * (mSigma E s * (μ.map (mSigma E)).prod) *
        (if ∀ y ∈ a', ∀ z ∈ a', y = z then 1 else 0) := by
    intro s
    simp only [primInit, pmLoop, LoopIdx.length, hN, Nat.add_sub_cancel, List.map_cons,
      List.prod_cons]
    rfl
  have hk := wardKappa_mul W hE (t := 0) (by norm_num)
  have hmm : mSigma E true * mSigma E false = 1 := mE_mul_conj hE.le
  simp only [wD, wStar, hfull, hpm, ← Finset.mul_sum, sum_allEq_append L a' ha]
  rw [wardC] at hk
  push_cast at hk
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  set P := (μ.map (mSigma E)).prod
  set I := (if ∀ y ∈ a', ∀ z ∈ a', y = z then (1 : ℂ) else 0)
  calc (W : ℂ)⁻¹ ^ (N + 1) * (mSigma E true * P * mSigma E false) * I
        - wardKappa W E 0 * ((W : ℂ)⁻¹ ^ N * (mSigma E true * P) * I
          - (W : ℂ)⁻¹ ^ N * (mSigma E false * P) * I)
      = (W : ℂ)⁻¹ ^ N * P * I * ((W : ℂ)⁻¹ * (mSigma E true * mSigma E false)
          - wardKappa W E 0 * (mSigma E true - mSigma E false)) := by ring
    _ = 0 := by rw [hmm, hk, sub_zero, mul_one, mul_one, sub_self, mul_zero]

end Init

section Level

variable {E : ℝ}

theorem cutMu_adjacent (μ : List Bool) (k : ℕ) : cutMu k (k + 1) μ = μ := by
  simp only [cutMu, show k + 1 - 2 = k - 1 by omega, List.take_append_drop]

omit [NeZero L] in
theorem length_cutA_adjacent (a' : List (ZMod L)) (a : ZMod L) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ a'.length) : (cutA k (k + 1) a a').length = a'.length := by
  simp only [cutA, List.length_append, List.length_take, List.length_cons, List.length_drop,
    Nat.add_sub_cancel]
  omega

/-- The index set of the level-`N` Ward defects: middle charges and labels. -/
abbrev WardVec (N : ℕ) := List.Vector Bool (N - 1) × List.Vector (ZMod L) N

/-- **One level of the induction** (loops of length `N + 1 ≥ 3`). -/
theorem ward_level (hL : 3 ≤ L) (W : ℕ) [NeZero W] (hE : |E| < 2)
    (K : ℝ → LoopIdx (ZMod L) → ℂ) (T₀ R : ℝ) (N : ℕ) (hN : 2 ≤ N) (hT₀ : T₀ < 1)
    (hR0 : 0 ≤ R)
    (hK : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => K s J) (primRhs L W (K t) J) t)
    (hcyc : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (ZMod L), J.WF → 2 ≤ J.length →
      K t J.rot = K t J)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ J : LoopIdx (ZMod L), J.WF → J.length = 2 → ‖K t J‖ ≤ R)
    (h2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : ZMod L, wStar L (K t) [] [a] = wardC W t)
    (hlow : ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (ZMod L)),
      μ.length + 1 = a'.length → a'.length < N → wD L (K t) (wardKappa W E t) μ a' = 0)
    (h0 : ∀ (μ : List Bool) (a' : List (ZMod L)), μ.length + 1 = a'.length → a'.length = N →
      wD L (K 0) (wardKappa W E 0) μ a' = 0) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (ZMod L)), μ.length + 1 = a'.length →
      a'.length = N → wD L (K t) (wardKappa W E t) μ a' = 0 := by
  let κ := wardKappa W E
  let D : ℝ → WardVec L N → ℂ := fun t p => wD L (K t) (κ t) p.1.1 p.2.1
  have hp : ∀ p : WardVec L N, p.1.1.length + 1 = p.2.1.length := fun p => by
    rw [p.1.2, p.2.2]
    omega
  have hpN : ∀ p : WardVec L N, p.2.1.length = N := fun p => p.2.2
  let T : ℝ → WardVec L N → ℂ := fun t p =>
    (∑ k ∈ Icc 1 (N - 1), ∑ a : ZMod L, ∑ b : ZMod L,
        wD L (K t) (κ t) (cutMu k (k + 1) p.1.1) (cutA k (k + 1) a p.2.1) * SB L a b *
          K t ((pmLoop true p.1.1 p.2.1).cutGlueR k (k + 1) b))
      + ∑ a : ZMod L, ∑ b : ZMod L,
        wD L (K t) (κ t) (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a]) * SB L a b *
          K t ((pmLoop false p.1.1 p.2.1).cutGlueL 1 N b)
  let D' : ℝ → WardVec L N → ℂ := fun t p => (W : ℂ) * T t p + (1 - (t : ℂ))⁻¹ * D t p
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  -- the shapes are well formed
  have hfullWF : ∀ (μ : List Bool) (a' : List (ZMod L)) (x : ZMod L),
      μ.length + 1 = a'.length → (fullLoop μ a' x).WF ∧ (fullLoop μ a' x).length = a'.length + 1 :=
    fun μ a' x h => ⟨by simp [WF, fullLoop]; omega, by simp [LoopIdx.length, fullLoop]⟩
  have hpmWF : ∀ (s : Bool) (μ : List Bool) (a' : List (ZMod L)),
      μ.length + 1 = a'.length → (pmLoop s μ a').WF ∧ (pmLoop s μ a').length = a'.length :=
    fun s μ a' h => ⟨by simp [WF, pmLoop]; omega, by simp [LoopIdx.length, pmLoop]⟩
  -- the derivative
  have hD : ∀ t ∈ Set.Icc 0 T₀, HasDerivAt D (D' t) t := by
    intro t ht
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    refine hasDerivAt_pi.2 fun p => ?_
    obtain ⟨hWFp, hlp⟩ := hpmWF true p.1.1 p.2.1 (hp p)
    obtain ⟨hWFm, hlm⟩ := hpmWF false p.1.1 p.2.1 (hp p)
    have hsum : HasDerivAt (fun s => ∑ x : ZMod L, K s (fullLoop p.1.1 p.2.1 x))
        (∑ x : ZMod L, primRhs L W (K t) (fullLoop p.1.1 p.2.1 x)) t :=
      HasDerivAt.fun_sum fun x _ => hK t ht _ (hfullWF _ _ x (hp p)).1
        (by rw [(hfullWF _ _ x (hp p)).2, hpN]; omega)
    have hplus := hK t ht _ hWFp (by rw [hlp, hpN]; omega)
    have hminus := hK t ht _ hWFm (by rw [hlm, hpN]; omega)
    have hprod := (hasDerivAt_wardKappa W hE ht1).mul (hplus.sub hminus)
    refine (hsum.sub hprod).congr_deriv ?_
    -- the value of the derivative
    have hid := ward_rhs_identity L (K t) (κ t) p.1.1 p.2.1 hL W (wardC W t) (hp p)
      (by rw [hpN]; exact hN) (hcyc t ht) (h2 t ht)
      (fun μ'' a'' h1 h2' => hlow t ht μ'' a'' h1 (by rw [hpN] at h2'; exact h2'))
    have hWc : (W : ℂ) * wardC W t = (1 - (t : ℂ))⁻¹ := by
      rw [wardC, mul_inv, ← mul_assoc, mul_inv_cancel₀ hW, one_mul]
    have ht' : (1 : ℂ) - t ≠ 0 := by
      rw [sub_ne_zero, ne_comm]
      exact_mod_cast ht1.ne
    simp only [D', T, D, wD, κ, hpN, Pi.sub_apply] at hid ⊢
    linear_combination hid + wStar L (K t) p.1.1 p.2.1 * hWc
  -- components of `D t`
  have hcomp : ∀ t (μ : List Bool) (a' : List (ZMod L)), μ.length = N - 1 → a'.length = N →
      ‖wD L (K t) (κ t) μ a'‖ ≤ ‖D t‖ :=
    fun t μ a' h1 h2 => norm_le_pi_norm (D t) (⟨μ, h1⟩, ⟨a', h2⟩)
  -- the bound
  set C : ℝ := W * ((∑ _k ∈ Icc 1 (N - 1), ∑ _a : ZMod L, ∑ _b : ZMod L, R)
    + ∑ _a : ZMod L, ∑ _b : ZMod L, R) + (1 - T₀)⁻¹ with hC
  have hT₀' : 0 < 1 - T₀ := by linarith
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ t ∈ Set.Ico 0 T₀, ‖D' t‖ ≤ C * ‖D t‖ := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T₀ := Set.Ico_subset_Icc_self ht
    have h1t : 0 < 1 - t := by linarith [ht.2]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg _))).2 fun p => ?_
    have hμN : p.1.1.length = N - 1 := p.1.2
    obtain ⟨hWFp, hlp⟩ := hpmWF true p.1.1 p.2.1 (hp p)
    obtain ⟨hWFm, hlm⟩ := hpmWF false p.1.1 p.2.1 (hp p)
    have hT1 : ∀ k ∈ Icc 1 (N - 1), ∀ a b : ZMod L,
        ‖wD L (K t) (κ t) (cutMu k (k + 1) p.1.1) (cutA k (k + 1) a p.2.1) * SB L a b *
          K t ((pmLoop true p.1.1 p.2.1).cutGlueR k (k + 1) b)‖ ≤ R * ‖D t‖ := by
      intro k hk a b
      rw [mem_Icc] at hk
      have hlpN : k + 1 ≤ (pmLoop true p.1.1 p.2.1).length := by rw [hlp, hpN]; omega
      have hWR := LoopIdx.WF.cutGlueR b hWFp hk.1 (Nat.lt_succ_self k) hlpN
      have hlen := LoopIdx.length_cutGlueR (pmLoop true p.1.1 p.2.1) b hk.1
        (Nat.lt_succ_self k) hlpN
      have hK2 := hR t ht' _ hWR (by rw [hlen]; omega)
      have hD1 := hcomp t (cutMu k (k + 1) p.1.1) (cutA k (k + 1) a p.2.1)
        (by rw [cutMu_adjacent]; exact hμN)
        (by rw [length_cutA_adjacent L p.2.1 a hk.1 (by rw [hpN]; omega), hpN])
      rw [norm_mul, norm_mul]
      calc _ ≤ ‖D t‖ * 1 * R := by
            gcongr
            exact norm_SB_apply_le L hL a b
        _ = R * ‖D t‖ := by ring
    have hT2 : ∀ a b : ZMod L,
        ‖wD L (K t) (κ t) (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a]) * SB L a b *
          K t ((pmLoop false p.1.1 p.2.1).cutGlueL 1 N b)‖ ≤ R * ‖D t‖ := by
      intro a b
      have hlmN : N ≤ (pmLoop false p.1.1 p.2.1).length := by rw [hlm, hpN]
      have hWL := LoopIdx.WF.cutGlueL b hWFm le_rfl (by omega) hlmN
      have hlen := LoopIdx.length_cutGlueL (pmLoop false p.1.1 p.2.1) b le_rfl (by omega) hlmN
      have hK2 := hR t ht' _ hWL (by rw [hlen, hlm, hpN]; omega)
      have hD1 := hcomp t (p.1.1.take (N - 1)) (p.2.1.take (N - 1) ++ [a])
        (by rw [List.length_take, hμN]; omega)
        (by rw [List.length_append, List.length_take, hpN, List.length_singleton]; omega)
      rw [norm_mul, norm_mul]
      calc _ ≤ ‖D t‖ * 1 * R := by
            gcongr
            exact norm_SB_apply_le L hL a b
        _ = R * ‖D t‖ := by ring
    have hinv : ‖(1 - (t : ℂ))⁻¹‖ ≤ (1 - T₀)⁻¹ := by
      rw [norm_inv, show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg h1t.le]
      exact inv_anti₀ hT₀' (by linarith [ht.2])
    calc ‖D' t p‖ ≤ ‖(W : ℂ) * T t p‖ + ‖(1 - (t : ℂ))⁻¹ * D t p‖ := norm_add_le _ _
      _ ≤ W * ((∑ _k ∈ Icc 1 (N - 1), ∑ _a : ZMod L, ∑ _b : ZMod L, R * ‖D t‖)
            + ∑ _a : ZMod L, ∑ _b : ZMod L, R * ‖D t‖) + (1 - T₀)⁻¹ * ‖D t‖ := by
          gcongr
          · rw [norm_mul, Complex.norm_natCast]
            gcongr
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
              exact hT1 k hk a b
            · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
              exact hT2 a b
          · rw [norm_mul]
            exact mul_le_mul hinv (norm_le_pi_norm (D t) p) (norm_nonneg _) (by positivity)
      _ = C * ‖D t‖ := by
          simp only [hC, add_mul, Finset.sum_mul, mul_assoc]
  have hD0 : D 0 = 0 := funext fun p => h0 _ _ (hp p) (hpN p)
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := D) (f' := D') (K := C) (a := 0) (b := T₀)
    (fun s hs => (hD s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hD s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt) hD0 hbound
  intro t ht μ a' hμ ha'
  have hμ' : μ.length = N - 1 := by omega
  exact congrFun (hzero t ht) (⟨μ, hμ'⟩, ⟨a', ha'⟩)

/-- **Lemma 3.6, (3.13), at every length.**  For a solution `K` of Definition 2.12 with
`m = m^{(E)}`, `|E| < 2`, on `[0, T₀]` with `T₀ < 1` and bounded `2`-loops: for every loop
`(+, μ, -; a', x)`,
`∑_x K_{t,(+,μ,-),(a',x)} = κ_t (K_{t,(+,μ),a'} - K_{t,(-,μ),a'})`, `κ_t = (2 W i η_t)⁻¹`. -/
theorem ward_of_isPrimitive (hL : 3 ≤ L) (W : ℕ) [NeZero W] (hE : |E| < 2) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W (mSigma E) T K) {T₀ R : ℝ}
    (hT₀ : T₀ < 1) (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R) :
    ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (ZMod L)), μ.length + 1 = a'.length →
      wD L (K t) (wardKappa W E t) μ a' = 0 := by
  -- level `2`
  have hlev2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : ZMod L, wD L (K t) (wardKappa W E t) [] [a] = 0 := by
    intro t ht a
    have h := ward_two_of_isPrimitive L hL W hE hK hT₀ hT hR0 hR t ht a
    have e : ∑ x : ZMod L, K t (fullLoop [] [a] x)
        = ∑ a₂ : ZMod L, K t ⟨[true, false], [a, a₂]⟩ := rfl
    simp only [wD, wStar]
    rw [e, h]
    simp only [pmLoop, wardKappa, div_eq_inv_mul, sub_self]
  have h2 : ∀ t ∈ Set.Icc 0 T₀, ∀ a : ZMod L, wStar L (K t) [] [a] = wardC W t := by
    intro t ht a
    have h := hlev2 t ht a
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hT₀
    simp only [wD, sub_eq_zero] at h
    rw [h]
    simp only [pmLoop]
    rw [hK.2.2 t (hT ht) true a, hK.2.2 t (hT ht) false a, wardKappa_mul W hE ht1]
  have hcyc := isPrimitive_rot L hL W (mSigma E) hK hT hR0 hR
  -- the initial value
  have h0 : ∀ (μ : List Bool) (a' : List (ZMod L)), μ.length + 1 = a'.length → 2 ≤ a'.length →
      wD L (K 0) (wardKappa W E 0) μ a' = 0 := by
    intro μ a' hμ h2'
    rw [← wD_primInit L W hE μ a' hμ]
    simp only [wD, wStar]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => hK.2.1 _ ?_ ?_
      · simp [WF, fullLoop]; omega
      · simp [LoopIdx.length, fullLoop]; omega
    · rw [hK.2.1 _ (by simp [WF, pmLoop]; omega) (by simp [LoopIdx.length, pmLoop]; omega),
        hK.2.1 _ (by simp [WF, pmLoop]; omega) (by simp [LoopIdx.length, pmLoop]; omega)]
  -- induction on the length
  have main : ∀ N : ℕ, ∀ t ∈ Set.Icc 0 T₀, ∀ (μ : List Bool) (a' : List (ZMod L)),
      μ.length + 1 = a'.length → a'.length = N → wD L (K t) (wardKappa W E t) μ a' = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro t ht μ a' hμ hN
      rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · -- level `2`
        have hμ0 : μ = [] := List.eq_nil_of_length_eq_zero (by omega)
        obtain ⟨a, ha⟩ : ∃ a, a' = [a] := List.length_eq_one_iff.mp (by omega)
        rw [hμ0, ha]
        exact hlev2 t ht a
      · refine ward_level L hL W hE K T₀ R N hN2 hT₀ hR0 (fun s hs => hK.1 s (hT hs)) hcyc hR
          h2 ?_ ?_ t ht μ a' hμ hN
        · intro s hs μ'' a'' h1 hlt
          exact ih _ hlt s hs μ'' a'' h1 rfl
        · intro μ'' a'' h1 hN'
          exact h0 μ'' a'' h1 (by omega)
  intro t ht μ a' hμ
  exact main _ t ht μ a' hμ rfl

/-- **Lemma 3.6, (3.13)**, in the paper's form. -/
theorem sum_fullLoop_eq (hL : 3 ≤ L) (W : ℕ) [NeZero W] (hE : |E| < 2) {T : Set ℝ}
    {K : ℝ → LoopIdx (ZMod L) → ℂ} (hK : IsPrimitive L W (mSigma E) T K) {T₀ R : ℝ}
    (hT₀ : T₀ < 1) (hT : Set.Icc 0 T₀ ⊆ T) (hR0 : 0 ≤ R)
    (hR : ∀ t ∈ Set.Icc 0 T₀, ∀ I : LoopIdx (ZMod L), I.WF → I.length = 2 → ‖K t I‖ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T₀) (μ : List Bool) (a' : List (ZMod L))
    (hμ : μ.length + 1 = a'.length) :
    ∑ x : ZMod L, K t ⟨true :: μ ++ [false], a' ++ [x]⟩
      = (K t ⟨true :: μ, a'⟩ - K t ⟨false :: μ, a'⟩) / (2 * W * Complex.I * etaT E t) := by
  have h := ward_of_isPrimitive L hL W hE hK hT₀ hT hR0 hR t ht μ a' hμ
  simp only [wD, wStar, sub_eq_zero] at h
  rw [div_eq_inv_mul]
  exact h

end Level

end RBM
