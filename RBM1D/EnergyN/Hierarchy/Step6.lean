/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.Step6
import RBM1D.Flow.Scales
import RBM1D.Flow.EnergyUniform

/-!
# Step 6 of the proof of Theorem 2.21 at an `N`-dependent energy

Formalization of Horng-Tzer Yau and Jun Yin,
*Delocalization of One-Dimensional Random Band Matrices*, §5.8.

The hierarchy, decay and drift predicates of Step 6 and three theorems, at an `N`-dependent
energy `E : ℕ → ℝ`: `RBM.Step6.HierarchyN`, `RBM.Step6.FastDecayHypN`, `RBM.Step6.DriftBoundN`
(eventual) and `RBM.Step6.Eq527N` (deterministic); `RBM.Step6.sharpExpect_of_hierarchyN`,
`RBM.Step6.lemma515N` and `RBM.Step6.driftBound_of_5133N`.

## The external `κ`

The constant `cKer 2 * (1 + 4 / ((mE (E N)).im * τ')) + 3` of
`RBM.Step6.sharpExpect_of_hierarchyN` depends on `N`. The theorem takes an explicit `κ` with
`∀ N, |E N| ≤ 2 - κ` (the paper's statements are uniform in `|E| ≤ 2 - κ`) and bounds
`(mE (E N)).im ≥ √(2κ)/2 =: m_κ` (`RBM.mE_im_ge`, `Flow/Scales.lean`, the κ-bound pattern of
`invMEIm_le_unif`, `EnergyN/Unif/Loop/SumZero.lean`). This gives the uniform
`K0 := cKer 2 * (1 + 4 / (m_κ * τ')) + 3`, which bounds the constant above for every `N` since
`4/x` is antitone in `x > 0`.

`RBM.Step6.lemma515N` and `RBM.Step6.driftBound_of_5133N` fix no energy-dependent constant:
`cShortRow κ` is `κ`-only, and the constant of `RBM.Step6.driftBound_of_5133N` comes from the
identity `RBM.Step6.W_mul_ell_mul_scale_inv_pow_four`, `E`-free in its bound.
-/

namespace RBM

open MeasureTheory Filter

namespace Step6

/-! ### The four `N`-predicates -/

section PredicatesN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.129)–(5.131)**, at an `N`-dependent energy. -/
def HierarchyN (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) (DLK DG : DriftTensor B) : Prop :=
  ∀ N (u : TimeIcc s t N) (σ : Fin 2 → Bool) (a : LoopArg (B.L N) 2),
    lkT X (E N) N u σ a =
      Uker (B.L N) (xiOf (mSigma (E N)) σ) (s N : ℂ) ((u : ℝ) : ℂ) (lkT X (E N) N (s N) σ) a
        + (∫ v in s N..(u : ℝ),
            Uker (B.L N) (xiOf (mSigma (E N)) σ) (v : ℂ) ((u : ℝ) : ℂ) (DLK N v σ) a)
        + ∫ v in s N..(u : ℝ),
            Uker (B.L N) (xiOf (mSigma (E N)) σ) (v : ℂ) ((u : ℝ) : ℂ) (DG N v σ) a

/-- Fast decay of the tensors of (5.129)–(5.131), at an `N`-dependent energy. -/
def FastDecayHypN (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) (DLK DG : DriftTensor B) : Prop :=
  ∀ τ > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ σ : Fin 2 → Bool,
    FastDecay (B.L N) (B.ell N (s N) * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D))
        (lkT X (E N) N (s N) σ) ∧
      ∀ v ∈ Set.Icc (s N) (t N),
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D)) (DLK N v σ) ∧
        FastDecay (B.L N) (B.ell N v * (B.W N : ℝ) ^ τ) ((B.W N : ℝ) ^ (-D)) (DG N v σ)

/-- The bound `max_{σ,a} |D_{v,σ,a}| ≺ η_v^{-1} (W ℓ_v η_v)^{-3}`, at an `N`-dependent energy. -/
def DriftBoundN (B : Band Ω) (E : ℕ → ℝ) (s t : ℕ → ℝ) (D : DriftTensor B) : Prop :=
  UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => ‖D N p.1 p.2.1 p.2.2‖)
    (fun N p => (etaT (E N) p.1)⁻¹ * (B.scale (E N) N p.1)⁻¹ ^ 3)

/-- **(5.127)**, at an `N`-dependent energy. -/
def Eq527N (X : Sample B) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ N (u : TimeIcc s t N) (a : ZMod (B.L N)),
    lk1 X (E N) N u a = ((u : ℝ) : ℂ) * mE (E N) ^ 2 * ∑ b, SB (B.L N) b a * lk1 X (E N) N u b
      + ((u : ℝ) : ℂ) * mE (E N) * ∑ b, SB (B.L N) b a * quad11 X (E N) N u b a

variable {X : Sample B} {E : ℝ} {s t : ℕ → ℝ} {DLK DG : DriftTensor B}

end PredicatesN

/-! ### (2.80) from the hierarchy -/

section SharpExpectN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **(5.129)–(5.136) ⟹ (2.80)**, at an `N`-dependent energy, at `E N`. `κ` is explicit
(`hEκ : ∀ N, |E N| ≤ 2 - κ`), and the constant `K0` is bounded uniformly through `RBM.mE_im_ge`
(module docstring). -/
theorem sharpExpect_of_hierarchyN (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N)
    (hst : ∀ N, s N ≤ t N) (ht1 : ∀ N, t N < 1) (hc : Cond272N B E s t) {DLK DG : DriftTensor B}
    (hH : HierarchyN X E s t DLK DG) (hFD : FastDecayHypN X E s t DLK DG)
    (h5132 : UnifDetDom (fun N (u : LoopData (B.L N) 2) => X.expErr (E N) N (s N) u.idx)
      (fun N _ => (B.scale (E N) N (s N))⁻¹ ^ 3))
    (h5133 : DriftBoundN B E s t DLK) (h5135 : DriftBoundN B E s t DG) :
    UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => X.expErr (E N) N p.1 p.2.idx)
      (fun N _ => (B.scale (E N) N (t N))⁻¹ ^ 3) := by
  set C := cKer 2 with hCdef
  have hC0 : 0 ≤ C := cKer_nonneg 2
  have hC : Est714At C 2 := est714At_cKer (by norm_num)
  have hκ2 : κ ≤ 2 := by linarith
  intro τ hτ
  set τ' := τ / 8 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hmκ0 : 0 < Real.sqrt (2 * κ) / 2 := by positivity
  set K0 := C * (1 + 4 / (Real.sqrt (2 * κ) / 2 * τ')) + 3 with hK0
  filter_upwards [h5132 τ' hτ'0, h5133 τ' hτ'0, h5135 τ' hτ'0, hFD τ' hτ'0 7 (by norm_num), hc,
    B.dim, eventually_le_rpow K0 (half_pos hτ), eventually_ge_atTop 1]
    with N h1 h2 h3 h4 h5 h6 h7 h8
  rintro ⟨u, σ, a⟩
  set n : ℝ := (N : ℝ) with hn
  set W : ℝ := (B.W N : ℝ) with hWdef
  have hL3 := B.three_le_L N
  have hW1 : 1 ≤ W := B.one_le_W N
  have hW0 : 0 < W := by linarith
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; exact_mod_cast h8
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hWn : W ≤ n := by
    have hWL : B.W N ≤ B.W N * B.L N := Nat.le_mul_of_pos_right _ (by omega)
    rw [hn, hWdef]; exact_mod_cast hWL.trans h6.1
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  have h1u : 0 < 1 - (u : ℝ) := by linarith
  have h1s : 1 - (u : ℝ) ≤ 1 - s N := by linarith [u.2.1]
  have hE : |E N| < 2 := by linarith [hEκ N]
  have hμ := mE_im_pos hE
  have hμ1 : (mE (E N)).im ≤ 1 := mE_im_le_one hE
  have hμge : Real.sqrt (2 * κ) / 2 ≤ (mE (E N)).im := mE_im_ge hκ0 hκ2 (hEκ N)
  -- the scales: `1 ≤ A_t ≤ A_u ≤ W √(1-u)`
  have hAt0 : 0 < B.scale (E N) N (t N) := flowScale_pos hW0 (by omega) hE (ht1 N)
  have hAu0 : 0 < B.scale (E N) N u := flowScale_pos hW0 (by omega) hE hu1
  have hAt1 : 1 ≤ B.scale (E N) N (t N) := by
    have hr : ((1 - t N) / (1 - s N)) ^ 30 ≤ 1 := by
      have h1t : 0 < 1 - t N := by linarith [ht1 N]
      refine pow_le_one₀ (div_nonneg h1t.le (by linarith [hst N])) ?_
      rw [div_le_one (by linarith [hst N])]; linarith [hst N]
    exact (inv_le_one₀ hAt0).1 (h5.trans hr)
  have hAtu : B.scale (E N) N (t N) ≤ B.scale (E N) N u :=
    flowScale_antitoneOn hW0.le (B.L N) (E N) (Set.mem_Iic.2 hu1.le)
      (Set.mem_Iic.2 (ht1 N).le) u.2.2
  have hAu1 : 1 ≤ B.scale (E N) N u := hAt1.trans hAtu
  have hAuW : B.scale (E N) N u ≤ W * Real.sqrt (1 - u) := by
    rw [Band.scale_eq_flowScale, flowScale_eq_mul]
    have h := ellHat_mul_one_sub_le_sqrt (B.L N) hu1
    have hℓ := Step3.ellHat_pos_of_lt_one (L := B.L N) (by omega) hu1
    calc W * ellHat (B.L N) ((u : ℝ) : ℂ) * ((1 - u) * (mE (E N)).im)
        = W * (ellHat (B.L N) ((u : ℝ) : ℂ) * (1 - u)) * (mE (E N)).im := by ring
      _ ≤ W * Real.sqrt (1 - u) * 1 := by gcongr
      _ = W * Real.sqrt (1 - u) := mul_one _
  have hsq1 : Real.sqrt (1 - (u : ℝ)) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hAuW' : B.scale (E N) N u ≤ W := hAuW.trans (by nlinarith)
  have hinvu : (1 - (u : ℝ))⁻¹ ≤ W ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ h1u]
    have := hAu1.trans hAuW
    have h2 : (1 : ℝ) ≤ (W * Real.sqrt (1 - u)) ^ 2 := by nlinarith
    rwa [mul_pow, Real.sq_sqrt h1u.le] at h2
  -- the ratio `Q = (1-s)/(1-u) = η_s/η_u`
  set Q := (1 - s N) / (1 - (u : ℝ)) with hQ
  have hQ1 : 1 ≤ Q := by rw [hQ, one_le_div h1u]; exact h1s
  have hQW : Q ≤ W ^ 2 := by
    rw [hQ, div_eq_mul_inv]
    calc (1 - s N) * (1 - (u : ℝ))⁻¹ ≤ 1 * W ^ 2 :=
          mul_le_mul (by linarith [hs0 N]) hinvu (inv_nonneg.2 h1u.le) zero_le_one
      _ = W ^ 2 := one_mul _
  have hlog : Real.log Q ≤ 2 * (n ^ τ' / τ') := by
    have hlogn := Real.log_le_rpow_div hn0 hτ'0
    calc Real.log Q ≤ Real.log (n ^ 2) :=
          Real.log_le_log (by linarith) (hQW.trans (pow_le_pow_left₀ hW0.le hWn 2))
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * (n ^ τ' / τ') := by linarith
  -- the tail `Q² W^{-7} ≤ (W ℓ_u η_u)^{-3}`
  have hδ : W ^ (-(7 : ℝ)) = (W ^ 7)⁻¹ := by
    rw [Real.rpow_neg hW0.le, ← Real.rpow_natCast]; norm_num
  have hQδ : Q ^ 2 * W ^ (-(7 : ℝ)) ≤ (B.scale (E N) N u)⁻¹ ^ 3 := by
    rw [hδ, inv_pow]
    calc Q ^ 2 * (W ^ 7)⁻¹ ≤ (W ^ 2) ^ 2 * (W ^ 7)⁻¹ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hQW 2) (by positivity)
      _ = (W ^ 3)⁻¹ := by field_simp
      _ ≤ (B.scale (E N) N u ^ 3)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hAu0.le hAuW' 3)
  -- `K = W^{τ'} ≤ x = N^{τ'}`, `x⁴ = N^{τ/2}`
  have hKx : W ^ τ' ≤ n ^ τ' := Real.rpow_le_rpow hW0.le hWn hτ'0.le
  have hK1 : 1 ≤ W ^ τ' := Real.one_le_rpow hW1 hτ'0.le
  have hx1 : 1 ≤ n ^ τ' := Real.one_le_rpow hn1 hτ'0.le
  have hx4 : (n ^ τ') ^ 4 = n ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; congr 1; rw [hτ']; push_cast; ring
  -- the hierarchy and the deterministic bound
  have hξ : ∀ i, ‖xiOf (mSigma (E N)) σ i‖ ≤ 1 := norm_xiOf_mSigma_le hE.le σ
  have hcore := core_bound (L := B.L N) (W := W) (E := E N) hL3 hW0 hE hC0 hC (hs0 N) u.2.1 hu1
    hξ (K := W ^ τ') (c := n ^ τ') (δ := W ^ (-(7 : ℝ))) hK1 (by positivity) (by positivity)
    (T₀ := lkT X (E N) N (s N) σ) (D₁ := fun v => DLK N v σ) (D₂ := fun v => DG N v σ)
    (fun b => h1 (σ, b)) (h4 σ).1
    (fun v hv b => (h2 (⟨v, hv.1, hv.2.trans u.2.2⟩, (σ, b))).trans
      (le_of_eq (mul_assoc _ _ _).symm))
    (fun v hv => ((h4 σ).2 v ⟨hv.1, hv.2.trans u.2.2⟩).1)
    (fun v hv b => (h3 (⟨v, hv.1, hv.2.trans u.2.2⟩, (σ, b))).trans
      (le_of_eq (mul_assoc _ _ _).symm))
    (fun v hv => ((h4 σ).2 v ⟨hv.1, hv.2.trans u.2.2⟩).2) a
  have harith := final_arith hC0 hμ hτ'0 hx1 (by positivity) (by positivity) hKx hQ1 hlog hQδ
  -- `C * (1 + 4/(μ_N τ')) + 3 ≤ K0`, uniformly through `m_κ ≤ μ_N`
  have hK0μ : C * (1 + 4 / ((mE (E N)).im * τ')) + 3 ≤ K0 := by
    have hstep : Real.sqrt (2 * κ) / 2 * τ' ≤ (mE (E N)).im * τ' :=
      mul_le_mul_of_nonneg_right hμge hτ'0.le
    have h4le : 4 / ((mE (E N)).im * τ') ≤ 4 / (Real.sqrt (2 * κ) / 2 * τ') :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hstep
    have := mul_le_mul_of_nonneg_left h4le hC0
    rw [hK0]; linarith
  show X.expErr (E N) N u (LoopData.idx (σ, a)) ≤ n ^ τ * (B.scale (E N) N (t N))⁻¹ ^ 3
  rw [← norm_lkT, hH N u σ a]
  refine hcore.trans (harith.trans ?_)
  have hxa4 : (0 : ℝ) ≤ (n ^ τ') ^ 4 * (B.scale (E N) N u)⁻¹ ^ 3 := by positivity
  have hstep2 : (C * (1 + 4 / ((mE (E N)).im * τ')) + 3) * (n ^ τ') ^ 4
      * (B.scale (E N) N u)⁻¹ ^ 3 ≤ K0 * (n ^ τ') ^ 4 * (B.scale (E N) N u)⁻¹ ^ 3 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK0μ (by positivity)) (by positivity)
  refine hstep2.trans ?_
  rw [hx4]
  have ha : (B.scale (E N) N u)⁻¹ ^ 3 ≤ (B.scale (E N) N (t N))⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ hAt0 hAtu) 3
  calc K0 * n ^ (τ / 2) * (B.scale (E N) N u)⁻¹ ^ 3
      ≤ n ^ (τ / 2) * n ^ (τ / 2) * (B.scale (E N) N (t N))⁻¹ ^ 3 := by
        gcongr
    _ = n ^ τ * (B.scale (E N) N (t N))⁻¹ ^ 3 := by
        rw [hn, UnifDetDom.rpow_half_mul_rpow_half N hτ]

end SharpExpectN

/-! ### Lemma 5.15 and the drift bound (5.133) -/

section OtherN

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **Lemma 5.15, (5.126)**, at an `N`-dependent energy. `cShortRow κ` is
`κ`-only, so this fixes no energy-dependent constant. -/
theorem lemma515N (X : Sample B) {E : ℕ → ℝ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hEκ : ∀ N, |E N| ≤ 2 - κ) {s t : ℕ → ℝ} (hs0 : ∀ N, 0 ≤ s N) (ht1 : ∀ N, t N < 1)
    (h527 : Eq527N X E s t)
    (hquad : UnifDetDom (fun N (p : TimeIcc s t N × (ZMod (B.L N) × ZMod (B.L N))) =>
      ‖quad11 X (E N) N p.1 p.2.1 p.2.2‖) (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2)) :
    UnifDetDom (fun N (p : TimeIcc s t N × ZMod (B.L N)) => ‖lk1 X (E N) N p.1 p.2‖)
      (fun N p => (B.scale (E N) N p.1)⁻¹ ^ 2) := by
  intro τ hτ
  filter_upwards [hquad (τ / 2) (half_pos hτ), eventually_le_rpow (cShortRow κ) (half_pos hτ)]
    with N hN hc
  rintro ⟨u, a⟩
  have hE2 : |E N| ≤ 2 := (hEκ N).trans (by linarith)
  have hu0 : 0 ≤ (u : ℝ) := (hs0 N).trans u.2.1
  have hu1 : (u : ℝ) < 1 := u.2.2.trans_lt (ht1 N)
  set M := (N : ℝ) ^ (τ / 2) * (B.scale (E N) N u)⁻¹ ^ 2 with hM
  have hy : ∀ a', ‖((u : ℝ) : ℂ) * mE (E N) * ∑ b, SB (B.L N) b a' * quad11 X (E N) N u b a'‖
      ≤ M := fun a' => norm_quadTerm_le (B.L N) (B.three_le_L N) hE2 hu0 hu1.le
      (fun b a'' => hN (u, (b, a''))) a'
  have hx := norm_selfConsistent_le (B.L N) (B.three_le_L N) hκ0 hκ1 (hEκ N) hu0 hu1
    (x := lk1 X (E N) N u)
    (y := fun a' => ((u : ℝ) : ℂ) * mE (E N) * ∑ b, SB (B.L N) b a' * quad11 X (E N) N u b a')
    (h527 N u) hy a
  have hM0 : 0 ≤ M := by positivity
  calc ‖lk1 X (E N) N u a‖ ≤ cShortRow κ * M := hx
    _ ≤ (N : ℝ) ^ (τ / 2) * M := mul_le_mul_of_nonneg_right hc hM0
    _ = (N : ℝ) ^ τ * (B.scale (E N) N u)⁻¹ ^ 2 := by
        rw [hM, ← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half N hτ]

/-- **(5.133)**, at an `N`-dependent energy. No energy-dependent constant is fixed here:
`RBM.Step6.W_mul_ell_mul_scale_inv_pow_four` is an identity at each `E N`. -/
theorem driftBound_of_5133N {E : ℕ → ℝ} (hE : ∀ N, |E N| < 2) {s t : ℕ → ℝ}
    (ht1 : ∀ N, t N < 1) {D : DriftTensor B}
    (h : UnifDetDom (fun N (p : TimeIcc s t N × LoopData (B.L N) 2) => ‖D N p.1 p.2.1 p.2.2‖)
      (fun N p => (B.W N : ℝ) * B.ell N p.1 * (B.scale (E N) N p.1)⁻¹ ^ 4)) :
    DriftBoundN B E s t D :=
  h.congr_eventually (Eventually.of_forall fun _ => rfl) (Eventually.of_forall fun N =>
    funext fun p => W_mul_ell_mul_scale_inv_pow_four (hE N) N (p.1.2.2.trans_lt (ht1 N)))

end OtherN

end Step6

end RBM
