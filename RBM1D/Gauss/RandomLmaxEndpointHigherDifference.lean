/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.RandomLmaxEndpointDifference

/-!
# All-order actual first-cell endpoint-vector differences

On the accepted variable-loss first-cell event, every fixed finite list of fresh deletions has
row and column endpoint-vector difference square sums controlled by the same random `Lmax`.
-/

namespace RBM.Gauss

open Filter MeasureTheory
open scoped BigOperators

variable {α : Type*} [DecidableEq α] {E : Type*}

/-- One finite difference of a family with values in a normed vector space. -/
def deltaVecFam [Sub E] (κ : α) (Y : Finset α → E) : Finset α → E :=
  fun S => Y S - Y (insert κ S)

/-- Shift a vector family by one deletion label. -/
def shiftVecFam (κ : α) (Y : Finset α → E) : Finset α → E :=
  fun S => Y (insert κ S)

/-- Iterated finite differences for vector-valued families, with the same order convention as
`iterDeltaFam`. -/
def iterDeltaVec [NormedAddCommGroup E] : List α → (Finset α → E) → Finset α → E
  | [], Y, S => Y S
  | κ :: l, Y, S => iterDeltaVec l (deltaVecFam κ Y) S

@[simp] theorem iterDeltaVec_nil [NormedAddCommGroup E] (Y : Finset α → E) (S : Finset α) :
    iterDeltaVec [] Y S = Y S := rfl

@[simp] theorem iterDeltaVec_cons [NormedAddCommGroup E] (κ : α) (l : List α)
    (Y : Finset α → E) (S : Finset α) :
    iterDeltaVec (κ :: l) Y S = iterDeltaVec l (deltaVecFam κ Y) S := rfl

theorem deltaVecFam_add [NormedAddCommGroup E] (κ : α) (Y Z : Finset α → E) :
    deltaVecFam κ (fun S => Y S + Z S) =
      fun S => deltaVecFam κ Y S + deltaVecFam κ Z S := by
  funext S
  simp only [deltaVecFam]
  abel

theorem iterDeltaVec_add [NormedAddCommGroup E] (l : List α) (Y Z : Finset α → E) :
    iterDeltaVec l (fun S => Y S + Z S) =
      fun S => iterDeltaVec l Y S + iterDeltaVec l Z S := by
  funext S
  induction l generalizing Y Z S with
  | nil => rfl
  | cons κ l ih =>
      change iterDeltaVec l (deltaVecFam κ (fun S => Y S + Z S)) S =
        iterDeltaVec l (deltaVecFam κ Y) S + iterDeltaVec l (deltaVecFam κ Z) S
      rw [deltaVecFam_add, ih]

section VectorGraded

variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The vector-valued counterpart of `DiffBd`. -/
def VecDiffBd (Ψ : ℝ) (I : Finset α) (M n : ℕ) (c : ℝ) (p : ℕ)
    (Y : Finset α → E) : Prop :=
  ∀ (l : List α) (S : Finset α), l.Nodup → (∀ κ ∈ l, κ ∉ I) → l.length ≤ n →
    S.card + l.length ≤ M → ‖iterDeltaVec l Y S‖ ≤ c * Ψ ^ (p + l.length)

theorem iterDeltaVec_congr : ∀ (l : List α) {M : ℕ} (Y Z : Finset α → E),
    (∀ S : Finset α, S.card ≤ M → Y S = Z S) →
    ∀ S : Finset α, S.card + l.length ≤ M → iterDeltaVec l Y S = iterDeltaVec l Z S := by
  intro l
  induction l with
  | nil =>
      intro M Y Z h S hcard
      exact h S (by simpa using hcard)
  | cons κ l ih =>
      intro M Y Z h S hcard
      obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := by
        refine ⟨M - 1, ?_⟩
        simp only [List.length_cons] at hcard
        omega
      simp only [iterDeltaVec_cons]
      apply ih (M := M') (deltaVecFam κ Y) (deltaVecFam κ Z)
      · intro T hT
        have hEq1 := h T (by omega)
        have hEq2 := h (insert κ T) (by have := Finset.card_insert_le κ T; omega)
        simp only [deltaVecFam, hEq1, hEq2]
      · simp only [List.length_cons] at hcard
        omega

theorem VecDiffBd.congr {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ}
    {Y Z : Finset α → E} (h : VecDiffBd Ψ I M n c p Y)
    (hYZ : ∀ S : Finset α, S.card ≤ M → Y S = Z S) :
    VecDiffBd Ψ I M n c p Z := by
  intro l S hnd hav hlen hcard
  rw [← iterDeltaVec_congr l Y Z hYZ S hcard]
  exact h l S hnd hav hlen hcard

theorem VecDiffBd.mono_n {Ψ : ℝ} {I : Finset α} {M n n' : ℕ} {c : ℝ} {p : ℕ}
    {Y : Finset α → E} (h : VecDiffBd Ψ I M n c p Y) (hn : n' ≤ n) :
    VecDiffBd Ψ I M n' c p Y :=
  fun l S hnd hav hlen hcard => h l S hnd hav (le_trans hlen hn) hcard

theorem VecDiffBd.mono_I {Ψ : ℝ} {I I' : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ}
    {Y : Finset α → E} (h : VecDiffBd Ψ I M n c p Y) (hII : I ⊆ I') :
    VecDiffBd Ψ I' M n c p Y :=
  fun l S hnd hav hlen hcard => h l S hnd
    (fun κ hκ hm => hav κ hκ (hII hm)) hlen hcard

theorem VecDiffBd.mono_M {Ψ : ℝ} {I : Finset α} {M M' n : ℕ} {c : ℝ} {p : ℕ}
    {Y : Finset α → E} (h : VecDiffBd Ψ I M n c p Y) (hM : M' ≤ M) :
    VecDiffBd Ψ I M' n c p Y :=
  fun l S hnd hav hlen hcard => h l S hnd hav hlen (le_trans hcard hM)

theorem VecDiffBd.delta {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ}
    {Y : Finset α → E} {κ : α} (hκ : κ ∉ I)
    (h : VecDiffBd Ψ I (M + 1) (n + 1) c p Y) :
    VecDiffBd Ψ (insert κ I) M n c (p + 1) (deltaVecFam κ Y) := by
  intro l S hnd hav hlen hcard
  have hκl : κ ∉ l := fun hm => (hav κ hm) (Finset.mem_insert_self κ I)
  have hnd' : (κ :: l).Nodup := List.nodup_cons.2 ⟨hκl, hnd⟩
  have hav' : ∀ κ' ∈ (κ :: l), κ' ∉ I := by
    intro κ' hκ'
    rcases List.mem_cons.1 hκ' with h1 | h1
    · exact h1 ▸ hκ
    · exact fun hm => hav κ' h1 (Finset.mem_insert_of_mem hm)
  have h' := h (κ :: l) S hnd' hav' (by simp [List.length_cons]; omega)
    (by simp only [List.length_cons]; omega)
  have hexp : p + (l.length + 1) = p + 1 + l.length := by omega
  simpa only [iterDeltaVec_cons, List.length_cons, hexp] using h'

theorem deltaVecFam_shiftVecFam (κ κ' : α) (Y : Finset α → E) :
    deltaVecFam κ (shiftVecFam κ' Y) = shiftVecFam κ' (deltaVecFam κ Y) := by
  funext S
  simp only [deltaVecFam, shiftVecFam, Finset.insert_comm]

theorem iterDeltaVec_shiftVecFam (l : List α) (κ : α)
    (Y : Finset α → E) :
    iterDeltaVec l (shiftVecFam κ Y) = shiftVecFam κ (iterDeltaVec l Y) := by
  induction l generalizing Y with
  | nil => rfl
  | cons j l ih =>
      change iterDeltaVec l (deltaVecFam j (shiftVecFam κ Y)) =
        shiftVecFam κ (iterDeltaVec l (deltaVecFam j Y))
      rw [deltaVecFam_shiftVecFam, ih]

theorem VecDiffBd.shift {Ψ : ℝ} {I : Finset α} {M n : ℕ} {c : ℝ} {p : ℕ}
    {Y : Finset α → E} (h : VecDiffBd Ψ I (M + 1) n c p Y) (κ : α) :
    VecDiffBd Ψ I M n c p (shiftVecFam κ Y) := by
  intro l S hnd hav hlen hcard
  simpa only [iterDeltaVec_shiftVecFam, shiftVecFam] using
    h l (insert κ S) hnd hav hlen (by have := Finset.card_insert_le κ S; omega)

theorem deltaVecFam_smul (κ : α) (Y : Finset α → ℂ) (Z : Finset α → E) :
    deltaVecFam κ (fun S => Y S • Z S) =
      fun S => deltaFam κ Y S • Z S + shiftFam κ Y S • deltaVecFam κ Z S := by
  funext S
  simp only [deltaVecFam, deltaFam_apply, shiftFam_apply]
  rw [sub_smul, smul_sub]
  abel

theorem VecDiffBd.smul {Ψ : ℝ} (hΨ : 0 ≤ Ψ) :
    ∀ (n : ℕ) {I : Finset α} {M : ℕ} {c₁ c₂ : ℝ} {p q : ℕ}
      {Y : Finset α → ℂ} {Z : Finset α → E},
      0 ≤ c₁ → 0 ≤ c₂ → DiffBd Ψ I M n c₁ p Y → VecDiffBd Ψ I M n c₂ q Z →
      VecDiffBd Ψ I M n (2 ^ n * (c₁ * c₂)) (p + q) (fun S => Y S • Z S) := by
  intro n
  induction n with
  | zero =>
      intro I M c₁ c₂ p q Y Z hc₁ hc₂ hY hZ l S hnd hav hlen hcard
      have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst hl
      have hS : S.card ≤ M := by simpa using hcard
      have h1 := hY.le_self S hS
      have h2 := hZ [] S (by simp) (by simp) (by simp) hS
      have hmul : ‖Y S • Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := by
        rw [norm_smul]
        exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      have hexp : (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) =
          (c₁ * c₂) * Ψ ^ (p + q) := by rw [pow_add]; ring
      rw [iterDeltaVec_nil]
      calc
        ‖Y S • Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := hmul
        _ = 2 ^ 0 * (c₁ * c₂) * Ψ ^ (p + q + [].length) := by
          rw [hexp]
          simp
  | succ n ih =>
      intro I M c₁ c₂ p q Y Z hc₁ hc₂ hY hZ l S hnd hav hlen hcard
      match l with
      | [] =>
          have hS : S.card ≤ M := by simpa using hcard
          have h1 := hY.le_self S hS
          have h2 := hZ [] S (by simp) (by simp) (by simp) hS
          have hmul : ‖Y S • Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := by
            rw [norm_smul]
            exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          have hpow : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
          have hexp : (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) =
              (c₁ * c₂) * Ψ ^ (p + q) := by rw [pow_add]; ring
          rw [iterDeltaVec_nil]
          have hnonneg : 0 ≤ (c₁ * c₂) * Ψ ^ (p + q) := by positivity
          calc
            ‖Y S • Z S‖ ≤ (c₁ * Ψ ^ p) * (c₂ * Ψ ^ q) := hmul
            _ = (c₁ * c₂) * Ψ ^ (p + q) := hexp
            _ ≤ 2 ^ (n + 1) * (c₁ * c₂) * Ψ ^ (p + q + [].length) := by
              calc
                _ = 1 * ((c₁ * c₂) * Ψ ^ (p + q)) := by ring
                _ ≤ 2 ^ (n + 1) * ((c₁ * c₂) * Ψ ^ (p + q)) :=
                  mul_le_mul_of_nonneg_right hpow hnonneg
                _ = _ := by simp only [List.length_nil, Nat.add_zero]; ring
      | κ :: l' =>
          have hcard' : S.card + l'.length + 1 ≤ M := by
            simp only [List.length_cons] at hcard
            omega
          obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
          have hκI : κ ∉ I := hav κ List.mem_cons_self
          have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
          have hκl' : κ ∉ l' := (List.nodup_cons.1 hnd).1
          have hav' : ∀ κ' ∈ l', κ' ∉ insert κ I := by
            intro κ' hκ' hmem
            rcases Finset.mem_insert.1 hmem with h1 | h1
            · exact hκl' (h1 ▸ hκ')
            · exact hav κ' (List.mem_cons_of_mem _ hκ') h1
          have hlen' : l'.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          have hcardl' : S.card + l'.length ≤ M' := by omega
          have hδY : DiffBd Ψ (insert κ I) M' n c₁ (p + 1) (deltaFam κ Y) :=
            hY.delta hκI
          have hδZ : VecDiffBd Ψ (insert κ I) M' n c₂ (q + 1) (deltaVecFam κ Z) :=
            hZ.delta hκI
          have hYs : DiffBd Ψ (insert κ I) M' n c₁ p (shiftFam κ Y) :=
            ((hY.mono_n (Nat.le_succ n)).mono_I (Finset.subset_insert κ I)).shift κ
          have hZ' : VecDiffBd Ψ (insert κ I) M' n c₂ q Z :=
            ((hZ.mono_n (Nat.le_succ n)).mono_I (Finset.subset_insert κ I)).mono_M
              (Nat.le_succ M')
          have hA := ih hc₁ hc₂ hδY hZ' l' S hnd' hav' hlen' hcardl'
          have hB := ih hc₁ hc₂ hYs hδZ l' S hnd' hav' hlen' hcardl'
          have hsplit : iterDeltaVec (κ :: l') (fun S => Y S • Z S) S =
              iterDeltaVec l' (fun S => deltaFam κ Y S • Z S) S +
                iterDeltaVec l' (fun S => shiftFam κ Y S • deltaVecFam κ Z S) S := by
            rw [iterDeltaVec_cons, deltaVecFam_smul, iterDeltaVec_add]
          rw [hsplit]
          have htri := norm_add_le
            (iterDeltaVec l' (fun S => deltaFam κ Y S • Z S) S)
            (iterDeltaVec l' (fun S => shiftFam κ Y S • deltaVecFam κ Z S) S)
          have he1 : p + 1 + q + l'.length = p + q + (κ :: l').length := by
            simp [List.length_cons]
            omega
          have he2 : p + (q + 1) + l'.length = p + q + (κ :: l').length := by
            simp [List.length_cons]
            omega
          rw [he1] at hA
          rw [he2] at hB
          have hfin : 2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length) +
                2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length) ≤
              2 ^ (n + 1) * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length) := by
            rw [pow_succ]
            ring_nf
            nlinarith [pow_nonneg hΨ (p + q + (κ :: l').length)]
          have hnonneg : 0 ≤ 2 ^ n * (c₁ * c₂) * Ψ ^ (p + q + (κ :: l').length) := by
            positivity
          linarith

end VectorGraded

/-- The unnormalized Euclidean endpoint vector over the original `Fin W` block. -/
private abbrev FirstCellEndpointVec (N : ℕ) :=
  EuclideanSpace ℂ (Fin (Dims.exampleGrow.W N))

private noncomputable def firstCellEndpointRowFam (N : ℕ) (u : ℝ) (ω : Ω Dims.exampleGrow)
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (T : Finset (Dims.exampleGrow.Idx N)) :
    Finset (Dims.exampleGrow.Idx N) → FirstCellEndpointVec N :=
  fun S => WithLp.toLp 2 (fun r =>
    gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (S ∪ T))

private noncomputable def firstCellEndpointColFam (N : ℕ) (u : ℝ) (ω : Ω Dims.exampleGrow)
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (T : Finset (Dims.exampleGrow.Idx N)) :
    Finset (Dims.exampleGrow.Idx N) → FirstCellEndpointVec N :=
  fun S => WithLp.toLp 2 (fun r =>
    gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (S ∪ T))

private theorem firstCellEndpointVec_norm_sq_row (N : ℕ) (u : ℝ) (ω : Ω Dims.exampleGrow)
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (S T : Finset (Dims.exampleGrow.Idx N)) :
    ‖firstCellEndpointRowFam N u ω a k T S‖ ^ 2 =
      ∑ r : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (S ∪ T)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [firstCellEndpointRowFam]

private theorem firstCellEndpointVec_norm_sq_col (N : ℕ) (u : ℝ) (ω : Ω Dims.exampleGrow)
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (S T : Finset (Dims.exampleGrow.Idx N)) :
    ‖firstCellEndpointColFam N u ω a k T S‖ ^ 2 =
      ∑ r : Fin (Dims.exampleGrow.W N),
        ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (S ∪ T)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [firstCellEndpointColFam]

/-- Constants for the all-order vector induction. -/
private noncomputable def endpointScalarDiffC (n : ℕ) : ℝ :=
  2 ^ n * (atomC n * atomC n)

private noncomputable def endpointVectorDiffC : ℕ → ℝ
  | 0 => 1
  | n + 1 => 2 ^ n * (endpointScalarDiffC n * endpointVectorDiffC n)

private theorem endpointScalarDiffC_nonneg (n : ℕ) : 0 ≤ endpointScalarDiffC n := by
  unfold endpointScalarDiffC
  exact mul_nonneg (by positivity)
    (mul_nonneg (atomC_nonneg n) (atomC_nonneg n))

private theorem endpointScalarDiffC_ge_one (n : ℕ) : 1 ≤ endpointScalarDiffC n := by
  unfold endpointScalarDiffC
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hatom : 1 ≤ atomC n := one_le_atomC n
  nlinarith [sq_nonneg (atomC n - 1)]

private theorem endpointVectorDiffC_nonneg : ∀ n, 0 ≤ endpointVectorDiffC n
  | 0 => by simp [endpointVectorDiffC]
  | n + 1 => by
      simp only [endpointVectorDiffC]
      exact mul_nonneg (by positivity)
        (mul_nonneg (endpointScalarDiffC_nonneg n) (endpointVectorDiffC_nonneg n))

private theorem endpointVectorDiffC_ge_one : ∀ n, 1 ≤ endpointVectorDiffC n
  | 0 => by simp [endpointVectorDiffC]
  | n + 1 => by
      simp only [endpointVectorDiffC]
      have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hscalar := endpointScalarDiffC_ge_one n
      have hvec := endpointVectorDiffC_ge_one n
      nlinarith [mul_nonneg (sub_nonneg.mpr hscalar) (sub_nonneg.mpr hvec)]

private theorem endpointVectorDiffC_mono_step (n : ℕ) :
    endpointVectorDiffC n ≤ endpointVectorDiffC (n + 1) := by
  rw [endpointVectorDiffC]
  have hpow : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hscalar := endpointScalarDiffC_ge_one n
  have hvec := endpointVectorDiffC_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right hscalar hvec,
    mul_le_mul_of_nonneg_right hpow (mul_nonneg (endpointScalarDiffC_nonneg n) hvec)]

private theorem endpointVectorDiffC_mono {m n : ℕ} (h : m ≤ n) :
    endpointVectorDiffC m ≤ endpointVectorDiffC n := by
  induction h with
  | refl => exact le_rfl
  | @step n h ih =>
      exact le_trans ih (endpointVectorDiffC_mono_step n)

private theorem endpointVecDiffBd_of_base
    {N : ℕ} {M : ℕ} {Ψ K : ℝ}
    {F : Dims.exampleGrow.Idx N → Finset (Dims.exampleGrow.Idx N) →
      Finset (Dims.exampleGrow.Idx N) → FirstCellEndpointVec N}
    {coeff : Dims.exampleGrow.Idx N → Dims.exampleGrow.Idx N →
      Finset (Dims.exampleGrow.Idx N) → Finset (Dims.exampleGrow.Idx N) → ℂ}
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1) (hK : 0 ≤ K)
    (hbase : ∀ (k : Dims.exampleGrow.Idx N) (T S : Finset (Dims.exampleGrow.Idx N)),
      (S ∪ T).card ≤ M → ‖F k T S‖ ≤ K)
    (hcoef : ∀ (n : ℕ) (j k : Dims.exampleGrow.Idx N)
        (T : Finset (Dims.exampleGrow.Idx N)) (B : ℕ), j ≠ k → B + T.card ≤ M →
        DiffBd Ψ ({j, k} : Finset (Dims.exampleGrow.Idx N)) B n
          (endpointScalarDiffC n) 1 (fun U => coeff j k T U))
    (hrank : ∀ (j k : Dims.exampleGrow.Idx N) (T U : Finset (Dims.exampleGrow.Idx N)),
        j ≠ k → (insert j (U ∪ T)).card ≤ M →
        deltaVecFam j (F k T) U = coeff j k T U • F j T U) :
    ∀ (n : ℕ) (k : Dims.exampleGrow.Idx N) (T : Finset (Dims.exampleGrow.Idx N))
      (B : ℕ), B + T.card ≤ M →
      VecDiffBd Ψ ({k} : Finset (Dims.exampleGrow.Idx N)) B n
        (endpointVectorDiffC n * K) 0 (F k T) := by
  intro n
  induction n with
  | zero =>
      intro k T B hBT l S hnd hav hlen hcard
      have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst hl
      have hUnion : (S ∪ T).card ≤ M := by
        have hST : S.card + T.card ≤ M := by omega
        exact le_trans (Finset.card_union_le S T) hST
      have hval := hbase k T S hUnion
      simp only [iterDeltaVec_nil, endpointVectorDiffC, List.length_nil, zero_add, pow_zero,
        mul_one, one_mul]
      exact hval
  | succ n ih =>
      intro k T B hBT l S hnd hav hlen hcard
      cases l with
      | nil =>
          have hUnion : (S ∪ T).card ≤ M := by
            have hST : S.card + T.card ≤ M := by omega
            exact le_trans (Finset.card_union_le S T) hST
          have hval := hbase k T S hUnion
          have hKbound : K ≤ endpointVectorDiffC (n + 1) * K := by
            simpa using mul_le_mul_of_nonneg_right
              (endpointVectorDiffC_ge_one (n + 1)) hK
          simp only [iterDeltaVec_nil, List.length_nil, zero_add, pow_zero, mul_one]
          exact le_trans hval hKbound
      | cons j l' =>
          have hjk : j ≠ k := by
            intro hEq
            exact hav j List.mem_cons_self (by simp [hEq])
          have hnd' : l'.Nodup := (List.nodup_cons.1 hnd).2
          have hjtail : ∀ x ∈ l', x ∉ ({j, k} : Finset (Dims.exampleGrow.Idx N)) := by
            intro x hx hxmem
            rcases Finset.mem_insert.1 hxmem with hxj | hxk
            · exact (List.nodup_cons.1 hnd).1 (hxj ▸ hx)
            · exact hav x (List.mem_cons_of_mem _ hx) (by simpa [hxk])
          have hlen' : l'.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨B', hB⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by
            simp only [List.length_cons] at hcard
            omega⟩
          have hB'T : B' + T.card ≤ M := by omega
          have hBshift : B' + 1 + T.card ≤ M := by simpa [hB] using hBT
          have hcard' : S.card + l'.length ≤ B' := by
            simp only [List.length_cons] at hcard
            omega
          have hscalar := hcoef n j k T B' hjk hB'T
          have hvec := ih j T B' hB'T
          have hvec' := hvec.mono_I (by simp : ({j} : Finset (Dims.exampleGrow.Idx N)) ⊆ {j, k})
          have hvecC : 0 ≤ endpointVectorDiffC n * K :=
            mul_nonneg (endpointVectorDiffC_nonneg n) hK
          have hprod := VecDiffBd.smul hΨ0 n (endpointScalarDiffC_nonneg n)
            hvecC hscalar hvec'
          have hcongr : VecDiffBd Ψ ({j, k} : Finset (Dims.exampleGrow.Idx N)) B' n
              (2 ^ n * (endpointScalarDiffC n * (endpointVectorDiffC n * K))) 1
              (deltaVecFam j (F k T)) := hprod.congr (by
                intro U hU
                exact (hrank j k T U hjk (by
                  have hIns : (insert j (U ∪ T)).card ≤ (U ∪ T).card + 1 :=
                    Finset.card_insert_le j (U ∪ T)
                  have hUnion : (U ∪ T).card ≤ U.card + T.card := Finset.card_union_le U T
                  omega)).symm)
          have hbound := hcongr l' S hnd' hjtail hlen' hcard'
          rw [iterDeltaVec_cons]
          have hconst : 2 ^ n * (endpointScalarDiffC n * (endpointVectorDiffC n * K)) =
              endpointVectorDiffC (n + 1) * K := by
            simp only [endpointVectorDiffC]
            ring
          rw [hconst] at hbound
          have hexp : 1 + l'.length = l'.length + 1 := by omega
          simpa [hexp, List.length_cons] using hbound

/-- The variable-loss threshold is eventually small enough for every fixed deletion budget. -/
private theorem firstCellEndpointHigherDelta_small {b : ℝ} (M : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      firstCellMinorEndpointDelta b N ≤ 1 / 4 ∧
        8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 := by
  have hbeta := firstCellMinorEndpointBeta_le_one_sixteenth b
  have hpsi := firstCellPsi_le_rpow_neg_quarter
  have hMpow : ∀ᶠ N : ℕ in atTop,
      8 * (M : ℝ) ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow _ (by norm_num)
  have hfourpow : ∀ᶠ N : ℕ in atTop,
      4 ≤ (N : ℝ) ^ ((3 : ℝ) / 16) :=
    eventually_le_rpow 4 (by norm_num)
  filter_upwards [hpsi, hMpow, hfourpow, eventually_ge_atTop 1]
    with N hpsiN hMpowN hfourpowN hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hδle : firstCellMinorEndpointDelta b N ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
    have hmul := mul_le_mul_of_nonneg_left hpsiN
      (Real.rpow_nonneg (Nat.cast_nonneg N) (firstCellMinorEndpointBeta b))
    have hpow : (N : ℝ) ^ firstCellMinorEndpointBeta b *
        (N : ℝ) ^ (-(1 : ℝ) / 4) =
          (N : ℝ) ^ (firstCellMinorEndpointBeta b - 1 / 4) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    calc
      firstCellMinorEndpointDelta b N =
          (N : ℝ) ^ firstCellMinorEndpointBeta b * firstCellPsi N := rfl
      _ ≤ (N : ℝ) ^ firstCellMinorEndpointBeta b *
          (N : ℝ) ^ (-(1 : ℝ) / 4) := hmul
      _ = (N : ℝ) ^ (firstCellMinorEndpointBeta b - 1 / 4) := hpow
      _ ≤ (N : ℝ) ^ (-(3 : ℝ) / 16) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        linarith
  have hnegpow : (N : ℝ) ^ (-(3 : ℝ) / 16) =
      ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ := by
    rw [show -(3 : ℝ) / 16 = -((3 : ℝ) / 16) by ring,
      Real.rpow_neg (Nat.cast_nonneg N)]
  have hquarter : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ 1 / 4 := by
    rw [hnegpow]
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hfourpowN
    norm_num at hinv ⊢
    exact hinv
  have hsmall : firstCellMinorEndpointDelta b N ≤ 1 / 4 := hδle.trans hquarter
  have hbudget : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1 := by
    by_cases hM : M = 0
    · simp [hM]
    · have hMpos : (0 : ℝ) < 8 * (M : ℝ) := by
        exact mul_pos (by norm_num) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM))
      have hinv : ((N : ℝ) ^ ((3 : ℝ) / 16))⁻¹ ≤ (8 * (M : ℝ))⁻¹ :=
        inv_anti₀ hMpos hMpowN
      have hdeltaInv : (N : ℝ) ^ (-(3 : ℝ) / 16) ≤ (8 * (M : ℝ))⁻¹ := by
        rw [hnegpow]
        exact hinv
      calc
        8 * (M : ℝ) * firstCellMinorEndpointDelta b N
            ≤ 8 * (M : ℝ) * (N : ℝ) ^ (-(3 : ℝ) / 16) :=
              mul_le_mul_of_nonneg_left hδle (by positivity)
        _ ≤ 8 * (M : ℝ) * (8 * (M : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left hdeltaInv (by positivity)
        _ = 1 := by field_simp
  exact ⟨hsmall, hbudget⟩

private theorem firstCellEndpointHigher_delta_sq_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N)) :
    firstCellMinorEndpointDelta b N ^ 2 ≤
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N := hω.1
  have hWlow := inv_W_le_Lmax_flow (d := Dims.exampleGrow) (s := firstCellS τ')
    (t := firstCellT τ') (δ := firstCellMinorEndpointDelta b) (E := 0)
    (by norm_num) (hδquarter.trans (by norm_num)) hflow hu
  have hψSq := firstCellPsi_sq_eq_invW_div_four N
  have hdeltaSq : firstCellMinorEndpointDelta b N ^ 2 =
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        ((Dims.exampleGrow.W N : ℝ)⁻¹) / 4 := by
    rw [firstCellMinorEndpointDelta, mul_pow]
    have hp : ((N : ℝ) ^ firstCellMinorEndpointBeta b) ^ 2 =
        (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      congr 1 <;> ring
    rw [hp, hψSq]
    ring
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hL0 : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
    Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  rw [hdeltaSq]
  have hpow0 : 0 ≤ (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
        ((Dims.exampleGrow.W N : ℝ)⁻¹) / 4
      ≤ (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
          (4 * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) / 4 := by
            gcongr
    _ = (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by ring

private theorem firstCellEndpointHigher_minorGood
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N)) :
    MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω
      (2 * firstCellMinorEndpointDelta b N) M := by
  have hflow : ω ∈ goodSetFlow Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N := hω.1
  have ht1 : firstCellT τ' N < 1 := (gridT_le (1 / 2 : ℝ) 1).trans_lt (by norm_num)
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 ht1
  have hz : (zt 0 u).im ≠ 0 := zt_im_ne_zero_of_lt_one (by norm_num) hu1
  have hδ0 : 0 ≤ firstCellMinorEndpointDelta b N := by
    unfold firstCellMinorEndpointDelta
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (firstCellPsi_pos N).le
  have hG : GoodEvent (green (Hflow Dims.exampleGrow N u ω) (zt 0 u)) (mE 0)
      (firstCellMinorEndpointDelta b N) := hflow u hu
  exact minorGoodLe_of_goodEvent_flow (by norm_num) hz hδ0 hδquarter hMδ hG

private theorem firstCellEndpointHigher_row_base
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    {a : ZMod (Dims.exampleGrow.L N)}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b) (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (k : Dims.exampleGrow.Idx N) (T S : Finset (Dims.exampleGrow.Idx N))
    (hST : (S ∪ T).card ≤ M) :
    ‖firstCellEndpointRowFam N u ω a k T S‖ ≤
      Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
  by_cases hk : k ∈ S ∪ T
  · have hz : firstCellEndpointRowFam N u ω a k T S = 0 := by
      ext r
      exact gEnt_eq_zero_right hk
    simpa [hz] using Real.sqrt_nonneg
      ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
  · have hrows := firstCell_randomLmax_minor_endpoint_row_column_le hω hb
      hδquarter hMδ hN hu (S ∪ T) hST k hk a
    have hWpos : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
      exact_mod_cast Dims.exampleGrow.W_pos N
    have hsum :
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (S ∪ T)‖ ^ 2) ≤
          (Dims.exampleGrow.W N : ℝ) *
            (20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
      calc
        _ = (Dims.exampleGrow.W N : ℝ) *
            (((Dims.exampleGrow.W N : ℝ)⁻¹) *
              ∑ r : Fin (Dims.exampleGrow.W N),
                ‖gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (S ∪ T)‖ ^ 2) := by
              field_simp [hWpos.ne']
        _ ≤ (Dims.exampleGrow.W N : ℝ) *
            (20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) :=
              mul_le_mul_of_nonneg_left hrows.1 hWpos.le
    have hnormSq := firstCellEndpointVec_norm_sq_row N u ω a k S T
    have hL0 : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
      Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
    have hX0 : 0 ≤ (Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by positivity
    have hnorm : ‖firstCellEndpointRowFam N u ω a k T S‖ ^ 2 ≤
        (Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
      rw [hnormSq]
      nlinarith [hsum]
    nlinarith [Real.sq_sqrt hX0,
      norm_nonneg (firstCellEndpointRowFam N u ω a k T S),
      Real.sqrt_nonneg ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))]

private theorem firstCellEndpointHigher_col_base
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    {a : ZMod (Dims.exampleGrow.L N)}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b) (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (k : Dims.exampleGrow.Idx N) (T S : Finset (Dims.exampleGrow.Idx N))
    (hST : (S ∪ T).card ≤ M) :
    ‖firstCellEndpointColFam N u ω a k T S‖ ≤
      Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
  by_cases hk : k ∈ S ∪ T
  · have hz : firstCellEndpointColFam N u ω a k T S = 0 := by
      ext r
      exact gEnt_eq_zero_left hk
    simpa [hz] using Real.sqrt_nonneg
      ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
  · have hrows := firstCell_randomLmax_minor_endpoint_row_column_le hω hb
      hδquarter hMδ hN hu (S ∪ T) hST k hk a
    have hWpos : (0 : ℝ) < (Dims.exampleGrow.W N : ℝ) := by
      exact_mod_cast Dims.exampleGrow.W_pos N
    have hsum :
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (S ∪ T)‖ ^ 2) ≤
          (Dims.exampleGrow.W N : ℝ) *
            (20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
      calc
        _ = (Dims.exampleGrow.W N : ℝ) *
            (((Dims.exampleGrow.W N : ℝ)⁻¹) *
              ∑ r : Fin (Dims.exampleGrow.W N),
                ‖gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (S ∪ T)‖ ^ 2) := by
              field_simp [hWpos.ne']
        _ ≤ (Dims.exampleGrow.W N : ℝ) *
            (20 * (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) :=
              mul_le_mul_of_nonneg_left hrows.2 hWpos.le
    have hnormSq := firstCellEndpointVec_norm_sq_col N u ω a k S T
    have hL0 : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
      Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
    have hX0 : 0 ≤ (Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by positivity
    have hnorm : ‖firstCellEndpointColFam N u ω a k T S‖ ^ 2 ≤
        (Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) := by
      rw [hnormSq]
      nlinarith [hsum]
    nlinarith [Real.sq_sqrt hX0,
      norm_nonneg (firstCellEndpointColFam N u ω a k T S),
      Real.sqrt_nonneg ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
        Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))]

private noncomputable def firstCellEndpointRowCoeff (N : ℕ) (u : ℝ) (ω : Ω Dims.exampleGrow)
    (j k : Dims.exampleGrow.Idx N) (T : Finset (Dims.exampleGrow.Idx N)) :
    Finset (Dims.exampleGrow.Idx N) → ℂ := fun U =>
  gFam Dims.exampleGrow N u (zt 0 u) ω j k T U *
    gInvFam Dims.exampleGrow N u (zt 0 u) ω j T U

private noncomputable def firstCellEndpointColCoeff (N : ℕ) (u : ℝ) (ω : Ω Dims.exampleGrow)
    (j k : Dims.exampleGrow.Idx N) (T : Finset (Dims.exampleGrow.Idx N)) :
    Finset (Dims.exampleGrow.Idx N) → ℂ := fun U =>
  gFam Dims.exampleGrow N u (zt 0 u) ω k j T U *
    gInvFam Dims.exampleGrow N u (zt 0 u) ω j T U

private theorem firstCellEndpointRowCoeff_diffBd
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ} {Ψ : ℝ}
    (hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω Ψ M)
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1)
    (n : ℕ) (j k : Dims.exampleGrow.Idx N) (T : Finset (Dims.exampleGrow.Idx N))
    (B : ℕ) (hjk : j ≠ k) (hBT : B + T.card ≤ M) :
    DiffBd Ψ ({j, k} : Finset (Dims.exampleGrow.Idx N)) B n
      (endpointScalarDiffC n) 1 (firstCellEndpointRowCoeff N u ω j k T) := by
  obtain ⟨hoff, hinv⟩ := diffBd_atom hg hΨ0 hΨ1 n ({j, k} : Finset (Dims.exampleGrow.Idx N))
    T B hBT
  have hOff := hoff j k (by simp) (by simp) hjk
  have hInv := hinv j (by simp)
  change DiffBd Ψ ({j, k} : Finset (Dims.exampleGrow.Idx N)) B n
    (endpointScalarDiffC n) 1
    (fun U => gFam Dims.exampleGrow N u (zt 0 u) ω j k T U *
      gInvFam Dims.exampleGrow N u (zt 0 u) ω j T U)
  simpa [endpointScalarDiffC] using
    DiffBd.mul hΨ0 n (atomC_nonneg n) (atomC_nonneg n) hOff hInv

private theorem firstCellEndpointColCoeff_diffBd
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ} {Ψ : ℝ}
    (hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω Ψ M)
    (hΨ0 : 0 ≤ Ψ) (hΨ1 : Ψ ≤ 1)
    (n : ℕ) (j k : Dims.exampleGrow.Idx N) (T : Finset (Dims.exampleGrow.Idx N))
    (B : ℕ) (hjk : j ≠ k) (hBT : B + T.card ≤ M) :
    DiffBd Ψ ({j, k} : Finset (Dims.exampleGrow.Idx N)) B n
      (endpointScalarDiffC n) 1 (firstCellEndpointColCoeff N u ω j k T) := by
  obtain ⟨hoff, hinv⟩ := diffBd_atom hg hΨ0 hΨ1 n ({j, k} : Finset (Dims.exampleGrow.Idx N))
    T B hBT
  have hOff := hoff k j (by simp) (by simp) (Ne.symm hjk)
  have hInv := hinv j (by simp)
  change DiffBd Ψ ({j, k} : Finset (Dims.exampleGrow.Idx N)) B n
    (endpointScalarDiffC n) 1
    (fun U => gFam Dims.exampleGrow N u (zt 0 u) ω k j T U *
      gInvFam Dims.exampleGrow N u (zt 0 u) ω j T U)
  simpa [endpointScalarDiffC] using
    DiffBd.mul hΨ0 n (atomC_nonneg n) (atomC_nonneg n) hOff hInv

private theorem firstCellEndpointRow_rankOne
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω Ψ M)
    (a : ZMod (Dims.exampleGrow.L N))
    (j k : Dims.exampleGrow.Idx N) (T U : Finset (Dims.exampleGrow.Idx N))
    (hjk : j ≠ k) (hcard : (insert j (U ∪ T)).card ≤ M) :
    deltaVecFam j (firstCellEndpointRowFam N u ω a k T) U =
      firstCellEndpointRowCoeff N u ω j k T U • firstCellEndpointRowFam N u ω a j T U := by
  ext r
  have h := deltaFam_gFam_apply hg (a, r) k j T U hcard
  simp only [deltaFam_apply] at h
  change gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (U ∪ T) -
      gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k (insert j U ∪ T) =
    firstCellEndpointRowCoeff N u ω j k T U *
      gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) j (U ∪ T)
  simpa [firstCellEndpointRowCoeff, gFam, gInvFam, Finset.insert_union,
    Finset.union_insert, mul_assoc, mul_comm, mul_left_comm] using h

private theorem firstCellEndpointCol_rankOne
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ} {Ψ : ℝ}
    (hg : MinorGoodLe Dims.exampleGrow N u (zt 0 u) (mE 0) ω Ψ M)
    (a : ZMod (Dims.exampleGrow.L N))
    (j k : Dims.exampleGrow.Idx N) (T U : Finset (Dims.exampleGrow.Idx N))
    (hjk : j ≠ k) (hcard : (insert j (U ∪ T)).card ≤ M) :
    deltaVecFam j (firstCellEndpointColFam N u ω a k T) U =
      firstCellEndpointColCoeff N u ω j k T U • firstCellEndpointColFam N u ω a j T U := by
  ext r
  have h := deltaFam_gFam_apply hg k (a, r) j T U hcard
  simp only [deltaFam_apply] at h
  change gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (U ∪ T) -
      gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) (insert j U ∪ T) =
    firstCellEndpointColCoeff N u ω j k T U *
      gEnt Dims.exampleGrow N u (zt 0 u) ω j (a, r) (U ∪ T)
  simpa [firstCellEndpointColCoeff, gFam, gInvFam, Finset.insert_union,
    Finset.union_insert, mul_assoc, mul_comm, mul_left_comm] using h

private theorem iterDeltaVec_toLp_apply
    {N : ℕ} (l : List (Dims.exampleGrow.Idx N))
    (G : Finset (Dims.exampleGrow.Idx N) → Fin (Dims.exampleGrow.W N) → ℂ)
    (S : Finset (Dims.exampleGrow.Idx N)) (r : Fin (Dims.exampleGrow.W N)) :
    (iterDeltaVec l (fun U => WithLp.toLp 2 (G U)) S).ofLp r =
      iterDeltaFam l (fun U => G U r) S := by
  induction l generalizing G S with
  | nil => rfl
  | cons j l ih =>
      change (iterDeltaVec l (fun U =>
          WithLp.toLp 2 (G U) - WithLp.toLp 2 (G (insert j U))) S).ofLp r =
        iterDeltaFam l (fun U => G U r - G (insert j U) r) S
      have hfun : (fun U => WithLp.toLp 2 (G U) - WithLp.toLp 2 (G (insert j U))) =
          fun U => WithLp.toLp 2 (fun r => G U r - G (insert j U) r) := by
        funext U
        ext r
        rfl
      rw [hfun, ih]

private theorem firstCellEndpointRow_iter_norm_sq
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (l : List (Dims.exampleGrow.Idx N)) (S : Finset (Dims.exampleGrow.Idx N)) :
    ‖iterDeltaVec l (firstCellEndpointRowFam N u ω a k ∅) S‖ ^ 2 =
      ∑ r : Fin (Dims.exampleGrow.W N),
        ‖iterDeltaFam l (fun U =>
          gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro r hr
  rw [iterDeltaVec_toLp_apply]
  simp [firstCellEndpointRowFam, Finset.union_empty]

private theorem firstCellEndpointCol_iter_norm_sq
    {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (l : List (Dims.exampleGrow.Idx N)) (S : Finset (Dims.exampleGrow.Idx N)) :
    ‖iterDeltaVec l (firstCellEndpointColFam N u ω a k ∅) S‖ ^ 2 =
      ∑ r : Fin (Dims.exampleGrow.W N),
        ‖iterDeltaFam l (fun U =>
          gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro r hr
  rw [iterDeltaVec_toLp_apply]
  simp [firstCellEndpointColFam, Finset.union_empty]

private noncomputable def firstCellEndpointHigherC (M : ℕ) : ℝ :=
  max 320 (max (20 * endpointVectorDiffC M ^ 2 * 4 ^ M)
    (1 + (M : ℝ) / 4))

private theorem firstCellEndpointHigher_loss_compare
    {b C K Γ : ℝ} {N r M : ℕ}
    (hb : 0 < b) (hN : 1 ≤ N) (hK : 0 ≤ K) (hΓ : 0 ≤ Γ)
    (hKC : K ≤ C) (hCexp : 1 + (M : ℝ) / 4 ≤ C) (hrM : r ≤ M) :
    K * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (r : ℝ)) *
        Γ ^ (1 + r) ≤ C * (N : ℝ) ^ (C * b) * Γ ^ (1 + r) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hr : (r : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrM
  have hβ := firstCellMinorEndpointBeta_le_b_div_eight b
  have hexp : b + 2 * firstCellMinorEndpointBeta b * (r : ℝ) ≤ C * b := by
    have h2β : 2 * firstCellMinorEndpointBeta b ≤ b / 4 := by linarith
    calc
      b + 2 * firstCellMinorEndpointBeta b * (r : ℝ)
          ≤ b + (b / 4) * (r : ℝ) := by
            gcongr
      _ ≤ b + (b / 4) * (M : ℝ) := by
            gcongr
      _ = (1 + (M : ℝ) / 4) * b := by ring
      _ ≤ C * b := mul_le_mul_of_nonneg_right hCexp hb.le
  have hpow : (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (r : ℝ)) ≤
      (N : ℝ) ^ (C * b) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have hpow0 : 0 ≤ (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (r : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hpowΓ : 0 ≤ Γ ^ (1 + r) := pow_nonneg hΓ _
  calc
    K * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (r : ℝ)) * Γ ^ (1 + r)
        ≤ C * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (r : ℝ)) * Γ ^ (1 + r) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hKC hpow0) hpowΓ
    _ ≤ C * (N : ℝ) ^ (C * b) * Γ ^ (1 + r) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow (by linarith)) hpowΓ

private theorem firstCellEndpointHigher_row_vector_sum_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (l : List (Dims.exampleGrow.Idx N)) (S : Finset (Dims.exampleGrow.Idx N))
    (hv : ‖iterDeltaVec l (firstCellEndpointRowFam N u ω a k ∅) S‖ ≤
      endpointVectorDiffC l.length *
        Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) *
        (2 * firstCellMinorEndpointDelta b N) ^ l.length) :
    ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2) ≤
      (20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length) *
        (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length) := by
  let Γ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)
  let W : ℝ := Dims.exampleGrow.W N
  let K : ℝ := Real.sqrt (W * 20 * (N : ℝ) ^ b * Γ)
  letI : NeZero (Dims.growW N) :=
    ⟨Nat.ne_of_gt (by simpa [Dims.exampleGrow_W] using Dims.exampleGrow.W_pos N)⟩
  letI : NeZero (Dims.growL N) :=
    ⟨Nat.ne_of_gt (by
      have hL := Dims.exampleGrow.three_le_L N
      have hL' : 3 ≤ Dims.growL N := by simpa [Dims.exampleGrow_L] using hL
      omega)⟩
  have hWpos : 0 < W := by
    dsimp [W]
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hWcastNe : (Dims.exampleGrow.W N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Dims.exampleGrow.W_pos N))
  have hWgrowNe : (Dims.growW N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by
      have hW := Dims.exampleGrow.W_pos N
      simpa [Dims.exampleGrow_W] using hW))
  have hΓ : 0 ≤ Γ := by
    dsimp [Γ]
    exact Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hX0 : 0 ≤ W * 20 * (N : ℝ) ^ b * Γ := by
    dsimp [W]
    positivity
  have hKsq : K ^ 2 = W * 20 * (N : ℝ) ^ b * Γ := by
    dsimp [K]
    exact Real.sq_sqrt hX0
  have hδsq := firstCellEndpointHigher_delta_sq_le hω hδquarter hN hu
  have hψsq : (2 * firstCellMinorEndpointDelta b N) ^ 2 ≤
      4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ := by
    have hδ := hδsq
    dsimp [Γ] at hδ
    calc
      (2 * firstCellMinorEndpointDelta b N) ^ 2 =
          4 * firstCellMinorEndpointDelta b N ^ 2 := by ring
      _ ≤ 4 * ((N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) :=
        mul_le_mul_of_nonneg_left hδ (by norm_num)
      _ = 4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ := by ring
  have hpower : (2 * firstCellMinorEndpointDelta b N) ^ (2 * l.length) ≤
      (4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) ^ l.length := by
    have hpow := pow_le_pow_left₀ (sq_nonneg (2 * firstCellMinorEndpointDelta b N))
      hψsq l.length
    simpa [pow_mul] using hpow
  have hNpow : ((N : ℝ) ^ (2 * firstCellMinorEndpointBeta b)) ^ l.length =
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hpowprod :
    (4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) ^ l.length =
        4 ^ l.length * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) *
          Γ ^ l.length := by
    rw [mul_pow, mul_pow, hNpow]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have htwoPower :
      ((2 * firstCellMinorEndpointDelta b N) ^ l.length) ^ 2 =
        (2 * firstCellMinorEndpointDelta b N) ^ (2 * l.length) := by
    rw [← pow_mul]
    congr 1
    omega
  have hnormSq :
      ‖iterDeltaVec l (firstCellEndpointRowFam N u ω a k ∅) S‖ ^ 2 ≤
        (endpointVectorDiffC l.length * K *
          (2 * firstCellMinorEndpointDelta b N) ^ l.length) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hsumSq := firstCellEndpointRow_iter_norm_sq (N := N) (u := u) (ω := ω) a k l S
  have hnormEq :
      ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2) =
        ((Dims.exampleGrow.W N : ℝ)⁻¹) *
          ‖iterDeltaVec l (firstCellEndpointRowFam N u ω a k ∅) S‖ ^ 2 := by
    rw [hsumSq]
  calc
    _ = ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        ‖iterDeltaVec l (firstCellEndpointRowFam N u ω a k ∅) S‖ ^ 2 := hnormEq
    _ ≤ ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (endpointVectorDiffC l.length * K *
          (2 * firstCellMinorEndpointDelta b N) ^ l.length) ^ 2 :=
          mul_le_mul_of_nonneg_left hnormSq (inv_nonneg.mpr hWpos.le)
    _ = 20 * endpointVectorDiffC l.length ^ 2 * (N : ℝ) ^ b * Γ *
        (2 * firstCellMinorEndpointDelta b N) ^ (2 * l.length) := by
          rw [mul_pow, mul_pow, htwoPower, hKsq]
          dsimp [W, Γ]
          field_simp [hWgrowNe]
    _ ≤ 20 * endpointVectorDiffC l.length ^ 2 * (N : ℝ) ^ b * Γ *
        ((4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) ^ l.length) := by
          exact mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = (20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length) *
        (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) *
        Γ ^ (1 + l.length) := by
          rw [hpowprod, Real.rpow_add hNpos]
          simp [pow_succ]
          ring

private theorem firstCellEndpointHigher_col_vector_sum_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (a : ZMod (Dims.exampleGrow.L N)) (k : Dims.exampleGrow.Idx N)
    (l : List (Dims.exampleGrow.Idx N)) (S : Finset (Dims.exampleGrow.Idx N))
    (hv : ‖iterDeltaVec l (firstCellEndpointColFam N u ω a k ∅) S‖ ≤
      endpointVectorDiffC l.length *
        Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
          Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) *
        (2 * firstCellMinorEndpointDelta b N) ^ l.length) :
    ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2) ≤
      (20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length) *
        (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length) := by
  let Γ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)
  let W : ℝ := Dims.exampleGrow.W N
  let K : ℝ := Real.sqrt (W * 20 * (N : ℝ) ^ b * Γ)
  letI : NeZero (Dims.growW N) :=
    ⟨Nat.ne_of_gt (by simpa [Dims.exampleGrow_W] using Dims.exampleGrow.W_pos N)⟩
  letI : NeZero (Dims.growL N) :=
    ⟨Nat.ne_of_gt (by
      have hL := Dims.exampleGrow.three_le_L N
      have hL' : 3 ≤ Dims.growL N := by simpa [Dims.exampleGrow_L] using hL
      omega)⟩
  have hWpos : 0 < W := by
    dsimp [W]
    exact_mod_cast Dims.exampleGrow.W_pos N
  have hWcastNe : (Dims.exampleGrow.W N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Dims.exampleGrow.W_pos N))
  have hWgrowNe : (Dims.growW N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by
      have hW := Dims.exampleGrow.W_pos N
      simpa [Dims.exampleGrow_W] using hW))
  have hΓ : 0 ≤ Γ := by
    dsimp [Γ]
    exact Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  have hX0 : 0 ≤ W * 20 * (N : ℝ) ^ b * Γ := by
    dsimp [W]
    positivity
  have hKsq : K ^ 2 = W * 20 * (N : ℝ) ^ b * Γ := by
    dsimp [K]
    exact Real.sq_sqrt hX0
  have hδsq := firstCellEndpointHigher_delta_sq_le hω hδquarter hN hu
  have hψsq : (2 * firstCellMinorEndpointDelta b N) ^ 2 ≤
      4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ := by
    have hδ := hδsq
    dsimp [Γ] at hδ
    calc
      (2 * firstCellMinorEndpointDelta b N) ^ 2 =
          4 * firstCellMinorEndpointDelta b N ^ 2 := by ring
      _ ≤ 4 * ((N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) :=
        mul_le_mul_of_nonneg_left hδ (by norm_num)
      _ = 4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ := by ring
  have hpower : (2 * firstCellMinorEndpointDelta b N) ^ (2 * l.length) ≤
      (4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) ^ l.length := by
    have hpow := pow_le_pow_left₀ (sq_nonneg (2 * firstCellMinorEndpointDelta b N))
      hψsq l.length
    simpa [pow_mul] using hpow
  have hNpow : ((N : ℝ) ^ (2 * firstCellMinorEndpointBeta b)) ^ l.length =
      (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hpowprod :
      (4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) ^ l.length =
        4 ^ l.length * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) *
          Γ ^ l.length := by
    rw [mul_pow, mul_pow, hNpow]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have htwoPower :
      ((2 * firstCellMinorEndpointDelta b N) ^ l.length) ^ 2 =
        (2 * firstCellMinorEndpointDelta b N) ^ (2 * l.length) := by
    rw [← pow_mul]
    congr 1
    omega
  have hnormSq :
      ‖iterDeltaVec l (firstCellEndpointColFam N u ω a k ∅) S‖ ^ 2 ≤
        (endpointVectorDiffC l.length * K *
          (2 * firstCellMinorEndpointDelta b N) ^ l.length) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hsumSq := firstCellEndpointCol_iter_norm_sq (N := N) (u := u) (ω := ω) a k l S
  have hnormEq :
      ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2) =
        ((Dims.exampleGrow.W N : ℝ)⁻¹) *
          ‖iterDeltaVec l (firstCellEndpointColFam N u ω a k ∅) S‖ ^ 2 := by
    rw [hsumSq]
  calc
    _ = ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        ‖iterDeltaVec l (firstCellEndpointColFam N u ω a k ∅) S‖ ^ 2 := hnormEq
    _ ≤ ((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (endpointVectorDiffC l.length * K *
          (2 * firstCellMinorEndpointDelta b N) ^ l.length) ^ 2 :=
          mul_le_mul_of_nonneg_left hnormSq (inv_nonneg.mpr hWpos.le)
    _ = 20 * endpointVectorDiffC l.length ^ 2 * (N : ℝ) ^ b * Γ *
        (2 * firstCellMinorEndpointDelta b N) ^ (2 * l.length) := by
          rw [mul_pow, mul_pow, htwoPower, hKsq]
          dsimp [W, Γ]
          field_simp [hWgrowNe]
    _ ≤ 20 * endpointVectorDiffC l.length ^ 2 * (N : ℝ) ^ b * Γ *
        ((4 * (N : ℝ) ^ (2 * firstCellMinorEndpointBeta b) * Γ) ^ l.length) := by
          exact mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = (20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length) *
        (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b * (l.length : ℝ)) *
        Γ ^ (1 + l.length) := by
          rw [hpowprod, Real.rpow_add hNpos]
          simp [pow_succ]
          ring

/-- Both normalized original-block endpoint-vector square sums of all shifted finite differences,
on one unchanged first-cell variable-loss event and its same-sample `Lmax`. -/
theorem firstCell_randomLmax_minor_endpoint_higher_difference_row_column_le
    {τ' b : ℝ} {N : ℕ} {u : ℝ} {ω : Ω Dims.exampleGrow} {M : ℕ}
    (hω : ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
      (firstCellMinorEndpointDelta b) N)
    (hb : 0 < b)
    (hδquarter : firstCellMinorEndpointDelta b N ≤ 1 / 4)
    (hMδ : 8 * (M : ℝ) * firstCellMinorEndpointDelta b N ≤ 1)
    (hN : 1 ≤ N) (hu : u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N))
    (S : Finset (Dims.exampleGrow.Idx N)) (k : Dims.exampleGrow.Idx N)
    (l : List (Dims.exampleGrow.Idx N))
    (hnd : l.Nodup) (hfresh : ∀ j ∈ l, j ∉ S) (hk : k ∉ S)
    (hlk : ∀ j ∈ l, j ≠ k) (a : ZMod (Dims.exampleGrow.L N))
    (hbudget : S.card + l.length ≤ M) :
    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2) ≤
      firstCellEndpointHigherC M * (N : ℝ) ^ (firstCellEndpointHigherC M * b) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length)) ∧
    (((Dims.exampleGrow.W N : ℝ)⁻¹) *
        (∑ r : Fin (Dims.exampleGrow.W N),
          ‖iterDeltaFam l (fun U =>
            gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2) ≤
      firstCellEndpointHigherC M * (N : ℝ) ^ (firstCellEndpointHigherC M * b) *
        (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ (1 + l.length)) := by
  let C := firstCellEndpointHigherC M
  have hC320 : 320 ≤ C := by
    dsimp [C, firstCellEndpointHigherC]
    exact le_max_left _ _
  have hCCoeff : 20 * endpointVectorDiffC M ^ 2 * 4 ^ M ≤ C := by
    dsimp [C, firstCellEndpointHigherC]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCexp : 1 + (M : ℝ) / 4 ≤ C := by
    dsimp [C, firstCellEndpointHigherC]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hC1 : 1 ≤ C := by linarith
  have hΓ : 0 ≤ Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u) :=
    Lmax_nonneg (Hflow_isHermitian Dims.exampleGrow N u ω)
  cases l with
  | nil =>
      have hbase := firstCell_randomLmax_minor_endpoint_row_column_le hω hb
        hδquarter hMδ hN hu S (by omega) k hk a
      have hrowCmp := firstCellEndpointHigher_loss_compare
        (b := b) (C := C) (K := 20) (Γ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
        (N := N) (r := 0) (M := M) hb hN (by norm_num) hΓ (by linarith) hCexp
        (Nat.zero_le M)
      have hcolCmp := hrowCmp
      constructor
      · exact le_trans hbase.1 (by simpa [C] using hrowCmp)
      · exact le_trans hbase.2 (by simpa [C] using hcolCmp)
  | cons j tail =>
      let l := j :: tail
      by_cases htail : tail = []
      · subst tail
        have hjS : j ∉ S := hfresh j List.mem_cons_self
        have hjk : j ≠ k := hlk j List.mem_cons_self
        have hbudget1 : S.card + 1 ≤ M := by simpa using hbudget
        have hfirst := firstCell_randomLmax_minor_endpoint_difference_row_column_le
          hω hb hδquarter hMδ hN hu S hbudget1 j k hjS hk hjk a
        have hcmp := firstCellEndpointHigher_loss_compare
          (b := b) (C := C) (K := 320)
          (Γ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
          (N := N) (r := 1) (M := M) hb hN (by norm_num) hΓ (by linarith) hCexp
          (by omega)
        have hcmp' :
            320 * (N : ℝ) ^ (b + 2 * firstCellMinorEndpointBeta b) *
                (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 ≤
              firstCellEndpointHigherC M * (N : ℝ) ^
                (firstCellEndpointHigherC M * b) *
                (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^ 2 := by
          simpa [C, Nat.cast_one, one_add_one_eq_two, mul_one] using hcmp
        constructor
        · exact le_trans hfirst.1 hcmp'
        · exact le_trans hfirst.2 hcmp'
      · have hbudgetL : S.card + l.length ≤ M := by simpa [l] using hbudget
        have hbudgetM : l.length ≤ M := by omega
        have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
        have hpsi0 : 0 ≤ 2 * firstCellMinorEndpointDelta b N := by
          unfold firstCellMinorEndpointDelta
          exact mul_nonneg (by norm_num)
            (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
              (firstCellPsi_pos N).le)
        have hpsi1 : 2 * firstCellMinorEndpointDelta b N ≤ 1 := by
          nlinarith [hδquarter]
        have hK : 0 ≤ Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 *
            (N : ℝ) ^ b * Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) :=
          Real.sqrt_nonneg _
        have hg := firstCellEndpointHigher_minorGood hω hδquarter hMδ hu
        have hrowBase : ∀ (k' : Dims.exampleGrow.Idx N)
            (T U : Finset (Dims.exampleGrow.Idx N)), (U ∪ T).card ≤ M →
            ‖firstCellEndpointRowFam N u ω a k' T U‖ ≤
              Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
                Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
          intro k' T U hU
          exact firstCellEndpointHigher_row_base hω hb hδquarter hMδ hN hu k' T U hU
        have hcolBase : ∀ (k' : Dims.exampleGrow.Idx N)
            (T U : Finset (Dims.exampleGrow.Idx N)), (U ∪ T).card ≤ M →
            ‖firstCellEndpointColFam N u ω a k' T U‖ ≤
              Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
                Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) := by
          intro k' T U hU
          exact firstCellEndpointHigher_col_base hω hb hδquarter hMδ hN hu k' T U hU
        have hrowVecAll := endpointVecDiffBd_of_base
          (N := N) (M := M) (Ψ := 2 * firstCellMinorEndpointDelta b N)
          (K := Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
            Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)))
          (F := firstCellEndpointRowFam N u ω a)
          (coeff := firstCellEndpointRowCoeff N u ω)
          hpsi0 hpsi1 hK hrowBase
          (fun n j k' T B hjk hBT =>
            firstCellEndpointRowCoeff_diffBd hg hpsi0 hpsi1 n j k' T B hjk hBT)
          (fun j k' T U hjk hcard =>
            firstCellEndpointRow_rankOne hg a j k' T U hjk hcard)
        have hcolVecAll := endpointVecDiffBd_of_base
          (N := N) (M := M) (Ψ := 2 * firstCellMinorEndpointDelta b N)
          (K := Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
            Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)))
          (F := firstCellEndpointColFam N u ω a)
          (coeff := firstCellEndpointColCoeff N u ω)
          hpsi0 hpsi1 hK hcolBase
          (fun n j k' T B hjk hBT =>
            firstCellEndpointColCoeff_diffBd hg hpsi0 hpsi1 n j k' T B hjk hBT)
          (fun j k' T U hjk hcard =>
            firstCellEndpointCol_rankOne hg a j k' T U hjk hcard)
        have hrowVec := hrowVecAll l.length k ∅ M (by simp)
        have hcolVec := hcolVecAll l.length k ∅ M (by simp)
        have hrowVecBound : ‖iterDeltaVec l (firstCellEndpointRowFam N u ω a k ∅) S‖ ≤
            endpointVectorDiffC l.length *
              Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
                Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) *
              (2 * firstCellMinorEndpointDelta b N) ^ l.length := by
          simpa [Nat.zero_add] using hrowVec l S hnd
            (by intro x hx; simpa using hlk x hx) (Nat.le_refl _)
            hbudgetL
        have hcolVecBound : ‖iterDeltaVec l (firstCellEndpointColFam N u ω a k ∅) S‖ ≤
            endpointVectorDiffC l.length *
              Real.sqrt ((Dims.exampleGrow.W N : ℝ) * 20 * (N : ℝ) ^ b *
                Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) *
              (2 * firstCellMinorEndpointDelta b N) ^ l.length := by
          simpa [Nat.zero_add] using hcolVec l S hnd
            (by intro x hx; simpa using hlk x hx) (Nat.le_refl _)
            hbudgetL
        have hrowSum := firstCellEndpointHigher_row_vector_sum_le
          hω hδquarter hN hu a k l S hrowVecBound
        have hcolSum := firstCellEndpointHigher_col_vector_sum_le
          hω hδquarter hN hu a k l S hcolVecBound
        have hrM : l.length ≤ M := by omega
        have hAr : endpointVectorDiffC l.length ≤ endpointVectorDiffC M :=
          endpointVectorDiffC_mono hrM
        have hAr0 := endpointVectorDiffC_nonneg l.length
        have hAM0 := endpointVectorDiffC_nonneg M
        have hfour : (4 : ℝ) ^ l.length ≤ 4 ^ M :=
          pow_le_pow_right₀ (by norm_num) hrM
        have hAsq : endpointVectorDiffC l.length ^ 2 ≤ endpointVectorDiffC M ^ 2 :=
          pow_le_pow_left₀ hAr0 hAr 2
        have hcoeff : 20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length ≤
            20 * endpointVectorDiffC M ^ 2 * 4 ^ M := by
          calc
            _ ≤ 20 * endpointVectorDiffC M ^ 2 * 4 ^ l.length := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hAsq (by norm_num)) (pow_nonneg (by norm_num) _)
            _ ≤ 20 * endpointVectorDiffC M ^ 2 * 4 ^ M :=
              mul_le_mul_of_nonneg_left hfour (by positivity)
        have hcoefC : 20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length ≤ C :=
          le_trans hcoeff hCCoeff
        have hcmp := firstCellEndpointHigher_loss_compare
          (b := b) (C := C)
          (K := 20 * endpointVectorDiffC l.length ^ 2 * 4 ^ l.length)
          (Γ := Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u))
          (N := N) (r := l.length) (M := M) hb hN (by positivity) hΓ hcoefC hCexp hrM
        constructor
        · exact le_trans hrowSum (by simpa [l, C] using hcmp)
        · exact le_trans hcolSum (by simpa [l, C] using hcmp)

/-- A positive-time actual Gaussian witness for the all-order endpoint-vector theorem.  One
resident sample supplies every eligible list, base, terminal, and original-block label after
the fixed loss and budget have been chosen. -/
theorem firstCell_randomLmax_actual_endpoint_higher_difference_witness :
    ∃ τ' : ℝ, 0 < τ' ∧
      LocalLawUnifIcc Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ') firstCellPsi ∧
      ∀ b : ℝ, 0 < b → ∀ M : ℕ,
        ∀ᶠ N : ℕ in atTop,
          ∃ ω ∈ flowNetEvent Dims.exampleGrow 0 (firstCellS τ') (firstCellT τ')
              (firstCellMinorEndpointDelta b) N,
            ∃ u ∈ Set.Icc (firstCellS τ' N) (firstCellT τ' N),
              0 < u ∧ u < firstCellT τ' N ∧
                (∀ i : Dims.exampleGrow.Idx N,
                  0 < ∫ ω', ‖Hflow Dims.exampleGrow N u ω' i i‖ ^ 2
                    ∂(P Dims.exampleGrow)) ∧
                ∀ S : Finset (Dims.exampleGrow.Idx N),
                  ∀ k : Dims.exampleGrow.Idx N, k ∉ S →
                    ∀ l : List (Dims.exampleGrow.Idx N), l.Nodup →
                      (∀ j ∈ l, j ∉ S) → (∀ j ∈ l, j ≠ k) →
                        S.card + l.length ≤ M →
                          ∀ a : ZMod (Dims.exampleGrow.L N),
                            (((Dims.exampleGrow.W N : ℝ)⁻¹) *
                                (∑ r : Fin (Dims.exampleGrow.W N),
                                  ‖iterDeltaFam l (fun U =>
                                    gEnt Dims.exampleGrow N u (zt 0 u) ω (a, r) k U) S‖ ^ 2) ≤
                              firstCellEndpointHigherC M * (N : ℝ) ^
                                (firstCellEndpointHigherC M * b) *
                                (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^
                                  (1 + l.length)) ∧
                            (((Dims.exampleGrow.W N : ℝ)⁻¹) *
                                (∑ r : Fin (Dims.exampleGrow.W N),
                                  ‖iterDeltaFam l (fun U =>
                                    gEnt Dims.exampleGrow N u (zt 0 u) ω k (a, r) U) S‖ ^ 2) ≤
                              firstCellEndpointHigherC M * (N : ℝ) ^
                                (firstCellEndpointHigherC M * b) *
                                (Lmax (Hflow Dims.exampleGrow N u ω) (zt 0 u)) ^
                                  (1 + l.length)) := by
  obtain ⟨τ', hτ', hll, _⟩ := firstCell_randomLmax_actual_nondegenerate_witness
  refine ⟨τ', hτ', hll, ?_⟩
  intro b hb M
  have hHP := firstCell_randomLmax_minor_endpoint_flowNetEvent_highProb hτ' hb hll
  have hnonempty := hHP.nonempty measure_univ
  have hwindow := first_cell_window_nondegenerate Dims.exampleGrow hτ'
  have hsmall := firstCellEndpointHigherDelta_small (b := b) M
  filter_upwards [hnonempty, hwindow, hsmall, eventually_ge_atTop 1]
    with N hnon hwindowN hsmallN hN
  rcases hnon with ⟨ω, hω⟩
  obtain ⟨u, hu, hu0, hut⟩ := firstCell_positive_interior_time hwindowN
  refine ⟨ω, hω, u, hu, hu0, hut, ?_, ?_⟩
  · intro i
    exact firstCell_positive_diag_flow_second_moment i hu0
  · intro S k hk l hnd hfresh hlk hbudget a
    exact firstCell_randomLmax_minor_endpoint_higher_difference_row_column_le
      hω hb hsmallN.1 hsmallN.2 hN hu S k l hnd hfresh hk hlk a hbudget

#print axioms firstCell_randomLmax_minor_endpoint_higher_difference_row_column_le
#print axioms firstCell_randomLmax_actual_endpoint_higher_difference_witness

end RBM.Gauss
