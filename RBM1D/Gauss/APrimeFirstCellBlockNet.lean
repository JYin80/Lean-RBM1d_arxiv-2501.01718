/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.OpNorm
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# A finite quarter-net for complex block vectors (T416)

This file is deterministic.  It constructs a `1/4`-net of the unit sphere of
`EuclideanSpace ℂ (Fin W)` with at most `9 ^ (2 * W)` points, and records the
corresponding finite-net reduction for the matrix `ℓ2 → ℓ2` operator norm.
-/

namespace RBM.Gauss

open Metric Set Module MeasureTheory Matrix
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator ComplexConjugate
open scoped Function

noncomputable section

/-! ## The complex unit sphere and quarter-nets -/

/-- The complex Euclidean block space used by `xBlock`. -/
abbrev BlockVec (W : ℕ) := EuclideanSpace ℂ (Fin W)

/-- A finite internal `1/4`-net of the complex unit sphere. -/
def IsQuarterSphereNet {W : ℕ} (V : Finset (BlockVec W)) : Prop :=
  (∀ v ∈ V, ‖v‖ = 1) ∧
    ∀ x : BlockVec W, ‖x‖ = 1 → ∃ v ∈ V, dist x v ≤ (1 : ℝ) / 4

/-- The volume-packing estimate behind the constant `9`: disjoint radius-`1/8`
balls centered in the unit ball all lie in the radius-`9/8` ball. -/
private theorem card_le_nine_pow_finrank_of_quarterSeparated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1 : ℝ) / 4 ≤ ‖c - d‖) :
    s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := (1 : ℝ) / 8
  let ρ : ℝ := (9 : ℝ) / 8
  have ρpos : 0 < ρ := by norm_num
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    calc
      δ + δ = (1 : ℝ) / 4 := by norm_num [δ]
      _ ≤ ‖c - d‖ := hsep c hc d hd hcd
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hs x hx)
      _ = ρ := by norm_num [δ, ρ]
  have hmeasure :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset hdisj fun c _ => measurableSet_ball]
        have hδ : 0 < δ := by norm_num [δ]
        simp only [μ.addHaar_ball_of_pos _ hδ]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have hcancel :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hmeasure
  have hreal : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) hcancel
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using h
  exact mod_cast hreal

/-- A `1/4`-separated subset of the complex unit sphere has at most `9^(2W)` points. -/
theorem quarterSeparated_card_le {W : ℕ} (V : Finset (BlockVec W))
    (hV : ∀ v ∈ V, ‖v‖ = 1)
    (hsep : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → (1 : ℝ) / 4 ≤ ‖v - w‖) :
    V.card ≤ 9 ^ (2 * W) := by
  have hcard := card_le_nine_pow_finrank_of_quarterSeparated V
    (fun v hv => (hV v hv).le) hsep
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin] at hcard
  exact hcard

/-- The deterministic complex-sphere net used by the block union bound.  The construction is a
maximal `1/4`-separated subset of the unit sphere; compactness makes it finite and the preceding
volume argument gives the exact cardinality bound. -/
theorem exists_quarterSphereNet (W : ℕ) :
    ∃ V : Finset (BlockVec W), IsQuarterSphereNet V ∧ V.card ≤ 9 ^ (2 * W) := by
  let S : Set (BlockVec W) := sphere 0 1
  let ε : ℝ≥0 := 1 / 4
  let η : ℝ≥0 := 1 / 8
  have hη : η ≠ 0 := by
    apply ne_of_gt
    norm_num [η]
  have hεη : ε = 2 * η := by
    norm_num [ε, η]
  have hεcoe : (ε : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ) / 4) := by
    norm_num [ε, ENNReal.coe_nnreal_eq]
  obtain ⟨C, _hCS, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact (s := S) (ε := η) hη
      (isCompact_sphere (0 : BlockVec W) 1)
  have hpack_le : packingNumber ε S ≤ C.encard := by
    calc
      packingNumber ε S = packingNumber (2 * η) S := by rw [hεη]
      _ ≤ externalCoveringNumber η S :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber η S
      _ ≤ C.encard := hCcover.externalCoveringNumber_le_encard
  have hpack : packingNumber ε S ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCfin) hpack_le
  let T : Set (BlockVec W) := maximalSeparatedSet ε S
  have hTenc : T.encard = packingNumber ε S := by
    simpa [T] using Metric.encard_maximalSeparatedSet hpack
  have hTfin : T.Finite := Set.encard_ne_top_iff.mp (hTenc ▸ hpack)
  let V : Finset (BlockVec W) := hTfin.toFinset
  have hVmem : ∀ {v : BlockVec W}, v ∈ V ↔ v ∈ T := by
    intro v
    exact hTfin.mem_toFinset
  have hVnorm : ∀ v ∈ V, ‖v‖ = 1 := by
    intro v hv
    have hvT : v ∈ T := hVmem.mp hv
    have hvS : v ∈ S := Metric.maximalSeparatedSet_subset hvT
    simpa [S] using hvS
  have hVsep : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → (1 : ℝ) / 4 ≤ ‖v - w‖ := by
    intro v hv w hw hvw
    have hsep := Metric.isSeparated_maximalSeparatedSet
      (ε := ε) (A := S) (hVmem.mp hv) (hVmem.mp hw) hvw
    have hpos : 0 < ‖v - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw)
    rw [hεcoe, edist_dist, dist_eq_norm] at hsep
    have hofReal : ENNReal.ofReal ((1 : ℝ) / 4) < ENNReal.ofReal ‖v - w‖ := hsep
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff hpos).mp hofReal)
  have hVcover : ∀ x : BlockVec W, ‖x‖ = 1 →
      ∃ v ∈ V, dist x v ≤ (1 : ℝ) / 4 := by
    intro x hx
    have hxS : x ∈ S := by simpa [S] using hx
    obtain ⟨v, hvT, hxv⟩ := Metric.isCover_maximalSeparatedSet hpack hxS
    refine ⟨v, hVmem.mpr hvT, ?_⟩
    change edist x v ≤ (ε : ℝ≥0∞) at hxv
    rw [hεcoe, edist_dist] at hxv
    have hofReal : ENNReal.ofReal (dist x v) ≤ ENNReal.ofReal ((1 : ℝ) / 4) := hxv
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (1 : ℝ) / 4)).mp hofReal
  refine ⟨V, ⟨hVnorm, hVcover⟩, ?_⟩
  exact quarterSeparated_card_le V hVnorm hVsep

/-- The endpoint `W = 1` is included in the construction (and gives a nonempty net). -/
theorem exists_quarterSphereNet_one :
    ∃ V : Finset (BlockVec 1), IsQuarterSphereNet V ∧ V.Nonempty ∧ V.card ≤ 9 ^ 2 := by
  obtain ⟨V, hV, hcard⟩ := exists_quarterSphereNet 1
  have he : ‖(EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 1) 0 1)‖ = 1 := by simp
  obtain ⟨v, hv, _⟩ := hV.2 _ he
  exact ⟨V, hV, ⟨v, hv⟩, by simpa using hcard⟩

/-! ## Reduction of the matrix operator norm to the net -/

/-- The maximum of `|v^* M w|` over a finite set.  It is defined as zero for the empty set;
the quarter-net theorem below supplies nonempty sets whenever `W ≥ 1`. -/
noncomputable def blockBilinearMax {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (V : Finset (BlockVec W)) : ℝ :=
  (((V ×ˢ V).sup fun p =>
    ‖inner ℂ p.1 (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M p.2)‖₊ : ℝ≥0) : ℝ)

theorem blockBilinearMax_nonneg {W : ℕ} (M : Matrix (Fin W) (Fin W) ℂ)
    (V : Finset (BlockVec W)) : 0 ≤ blockBilinearMax M V := by
  exact NNReal.zero_le_coe

/-- Every individual bilinear form appearing in the finite maximum is bounded by it. -/
theorem norm_inner_mulVec_le_blockBilinearMax {W : ℕ}
    (M : Matrix (Fin W) (Fin W) ℂ) (V : Finset (BlockVec W))
    {v w : BlockVec W} (hv : v ∈ V) (hw : w ∈ V) :
    ‖inner ℂ v (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M w)‖
      ≤ blockBilinearMax M V := by
  have hp : (v, w) ∈ V ×ˢ V := Finset.mem_product.mpr ⟨hv, hw⟩
  have hnn : ‖inner ℂ v (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M w)‖₊ ≤
      (V ×ˢ V).sup (fun p =>
        ‖inner ℂ p.1 (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M p.2)‖₊) :=
    Finset.le_sup
      (s := V ×ˢ V)
      (f := fun p =>
        ‖inner ℂ p.1 (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M p.2)‖₊)
      (b := (v, w)) hp
  exact_mod_cast hnn

/-- A quarter-net controls the exact matrix `ℓ2 → ℓ2` operator norm by twice the largest
bilinear form on the net.  The norm on the left is the same scoped L2 operator norm used for
`T407`'s `xBlock`. -/
theorem l2_opNorm_le_two_blockBilinearMax {W : ℕ}
    (M : Matrix (Fin W) (Fin W) ℂ) (V : Finset (BlockVec W))
    (hV : IsQuarterSphereNet V) :
    ‖M‖ ≤ 2 * blockBilinearMax M V := by
  let T : BlockVec W →L[ℂ] BlockVec W :=
    Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M
  let B : ℝ := blockBilinearMax M V
  have hB : 0 ≤ B := blockBilinearMax_nonneg M V
  have hunit : ∀ y : BlockVec W, ‖y‖ = 1 → ‖T y‖ ≤ B + ‖T‖ / 2 := by
    intro y hy
    obtain ⟨w, hwV, hyw⟩ := hV.2 y hy
    have hyw' : ‖y - w‖ ≤ (1 : ℝ) / 4 := by
      simpa [dist_eq_norm] using hyw
    by_cases hTy : T y = 0
    · rw [hTy, norm_zero]
      positivity
    let x : BlockVec W := NormedSpace.normalize (T y)
    have hx : ‖x‖ = 1 := NormedSpace.norm_normalize hTy
    obtain ⟨v, hvV, hxv⟩ := hV.2 x hx
    have hxv' : ‖x - v‖ ≤ (1 : ℝ) / 4 := by
      simpa [dist_eq_norm] using hxv
    have hvnorm : ‖v‖ = 1 := hV.1 v hvV
    have hTy_inner : ‖inner ℂ x (T y)‖ = ‖T y‖ := by
      change ‖inner ℂ (NormedSpace.normalize (T y)) (T y)‖ = ‖T y‖
      calc
        ‖inner ℂ (NormedSpace.normalize (T y)) (T y)‖ =
            ‖inner ℂ (NormedSpace.normalize (T y))
              (‖T y‖ • NormedSpace.normalize (T y))‖ := by
                rw [NormedSpace.norm_smul_normalize]
        _ = ‖T y‖ := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_right,
            inner_self_eq_norm_sq_to_K, NormedSpace.norm_normalize hTy]
          simp
    have hdecomp :
        inner ℂ x (T y) = inner ℂ v (T w) + inner ℂ (x - v) (T y) +
          inner ℂ v (T (y - w)) := by
      rw [T.map_sub, inner_sub_left, inner_sub_right]
      ring
    have hmain : ‖inner ℂ v (T w)‖ ≤ B := by
      change ‖inner ℂ v (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ) M w)‖
        ≤ blockBilinearMax M V
      exact norm_inner_mulVec_le_blockBilinearMax M V hvV hwV
    have hTy_op : ‖T y‖ ≤ ‖T‖ := by
      simpa [hy] using T.le_opNorm y
    have herr₁ : ‖inner ℂ (x - v) (T y)‖ ≤ ‖T‖ / 4 := by
      calc
        ‖inner ℂ (x - v) (T y)‖ ≤ ‖x - v‖ * ‖T y‖ := norm_inner_le_norm _ _
        _ ≤ ((1 : ℝ) / 4) * ‖T‖ := by
          exact mul_le_mul hxv' hTy_op (norm_nonneg _) (by norm_num)
        _ = ‖T‖ / 4 := by ring
    have hdiff_op : ‖T (y - w)‖ ≤ ‖T‖ * ‖y - w‖ := T.le_opNorm (y - w)
    have herr₂ : ‖inner ℂ v (T (y - w))‖ ≤ ‖T‖ / 4 := by
      calc
        ‖inner ℂ v (T (y - w))‖ ≤ ‖v‖ * ‖T (y - w)‖ := norm_inner_le_norm _ _
        _ ≤ 1 * (‖T‖ * ‖y - w‖) := by
          exact mul_le_mul (hvnorm.le) hdiff_op (norm_nonneg _) (by norm_num)
        _ ≤ 1 * (‖T‖ * ((1 : ℝ) / 4)) := by
          gcongr
        _ = ‖T‖ / 4 := by ring
    rw [← hTy_inner, hdecomp]
    calc
      ‖inner ℂ v (T w) + inner ℂ (x - v) (T y) + inner ℂ v (T (y - w))‖
          ≤ ‖inner ℂ v (T w)‖ + ‖inner ℂ (x - v) (T y)‖ +
              ‖inner ℂ v (T (y - w))‖ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact norm_add_le _ _
      _ ≤ B + ‖T‖ / 4 + ‖T‖ / 4 := add_le_add (add_le_add hmain herr₁) herr₂
      _ = B + ‖T‖ / 2 := by ring
  have hop : ‖T‖ ≤ B + ‖T‖ / 2 :=
    ContinuousLinearMap.opNorm_le_of_unit_norm
      (add_nonneg hB (div_nonneg (norm_nonneg T) (by norm_num))) hunit
  have hfinal : ‖T‖ ≤ 2 * B := by linarith
  rw [Matrix.cstar_norm_def]
  simpa [T, B] using hfinal

/-- The zero matrix sanity check: both sides of the net reduction vanish. -/
theorem blockBilinearMax_zero {W : ℕ} (V : Finset (BlockVec W)) :
    blockBilinearMax (0 : Matrix (Fin W) (Fin W) ℂ) V = 0 := by
  apply le_antisymm
  · change (((V ×ˢ V).sup fun p =>
        ‖inner ℂ p.1 (Matrix.toEuclideanCLM (n := Fin W) (𝕜 := ℂ)
          (0 : Matrix (Fin W) (Fin W) ℂ) p.2)‖₊ : ℝ≥0) : ℝ) ≤ 0
    norm_cast
    apply Finset.sup_le
    intro p hp
    simp
  · exact blockBilinearMax_nonneg _ _

/-- Packaged existence of a net giving the exact matrix bound, for every nonzero block size. -/
theorem exists_quarterSphereNet_l2_opNorm (W : ℕ) (hW : 1 ≤ W)
    (M : Matrix (Fin W) (Fin W) ℂ) :
    ∃ V : Finset (BlockVec W), IsQuarterSphereNet V ∧ V.Nonempty ∧
      V.card ≤ 9 ^ (2 * W) ∧ ‖M‖ ≤ 2 * blockBilinearMax M V := by
  obtain ⟨V, hV, hcard⟩ := exists_quarterSphereNet W
  let e : BlockVec W := EuclideanSpace.single (𝕜 := ℂ) (ι := Fin W) ⟨0, hW⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨v, hv, _⟩ := hV.2 e he
  exact ⟨V, hV, ⟨v, hv⟩, hcard, l2_opNorm_le_two_blockBilinearMax M V hV⟩

/-! ## Axiom audit -/

#print axioms quarterSeparated_card_le
#print axioms exists_quarterSphereNet
#print axioms l2_opNorm_le_two_blockBilinearMax
#print axioms exists_quarterSphereNet_l2_opNorm
#print axioms exists_quarterSphereNet_one
#print axioms blockBilinearMax_zero

end

end RBM.Gauss
