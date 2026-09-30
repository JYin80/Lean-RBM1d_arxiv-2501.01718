/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Fin.Tuple.Embedding
import RBM1D.Flow.Universality

/-!
# Injective-sum decomposition (Theorem 2.6, Step 2)

The `Mixed(k,m)` recursion:
a sum over injective maps `Fin k ↪ n` of a smooth compactly supported `O` is a finite signed
combination of sums over *all* maps `Fin (kk i) → n` (`kk i ≤ k`) of test functions `Oj i`,
obtained by peeling one coordinate at a time (`Fin.Embedding.snoc`/`.init`) and using
inclusion–exclusion `Mixed(k+1,m) = Mixed(k,m+1) - ∑_{i<k} Mixed(k,m)`. No Möbius function is
used.
-/

namespace RBM

open Function Set

/-! ### Generic topology helper -/

private lemma hasCompactSupport_comp_of_retraction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {O : Y → ℝ} (hO : HasCompactSupport O)
    {Φ : X → Y} {Ψ : Y → X} (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) : HasCompactSupport (O ∘ Φ) := by
  have hsupp : Function.support (O ∘ Φ) = Φ ⁻¹' Function.support O := by
    ext x; simp [Function.mem_support, Function.comp]
  have h2 : IsCompact (Φ ⁻¹' tsupport O) := by
    have hsub : Φ ⁻¹' tsupport O ⊆ Ψ '' (tsupport O) := fun x hx => ⟨Φ x, hx, hΨΦ x⟩
    exact (hO.image hΨ).of_isClosed_subset ((isClosed_tsupport O).preimage hΦ) hsub
  have h1 : closure (Φ ⁻¹' Function.support O) ⊆ Φ ⁻¹' (tsupport O) := by
    apply closure_minimal (preimage_mono subset_closure)
    exact (isClosed_tsupport O).preimage hΦ
  show IsCompact (closure (Function.support (O ∘ Φ)))
  rw [hsupp]
  exact h2.of_isClosed_subset isClosed_closure h1

/-! ### Extending an embedding `Fin k ↪ n` by one point -/

private noncomputable def embSnocEquiv {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) :
    (Fin (k + 1) ↪ n) ≃ Σ f : Fin k ↪ n, {a : n // a ∉ Set.range f} where
  toFun f := ⟨Fin.Embedding.init f, ⟨f (Fin.last k), by
    rintro ⟨j, hj⟩
    have hj' : f j.castSucc = f (Fin.last k) := hj
    have := f.injective hj'
    exact absurd this (Fin.castSucc_lt_last j).ne⟩⟩
  invFun p := Fin.Embedding.snoc p.1 p.2.2
  left_inv f := by
    apply DFunLike.ext
    intro i
    induction i using Fin.lastCases with
    | last => simp [Fin.Embedding.coe_snoc]
    | cast j =>
      show (Fin.Embedding.snoc (Fin.Embedding.init f) _) j.castSucc = f j.castSucc
      rw [Fin.Embedding.snoc_castSucc]
      rfl
  right_inv := by
    rintro ⟨f, a, ha⟩
    ext1
    · show Fin.Embedding.init (Fin.Embedding.snoc f ha) = f
      apply DFunLike.ext
      intro j
      show (Fin.Embedding.snoc f ha) j.castSucc = f j
      rw [Fin.Embedding.snoc_castSucc]
    · show (Fin.Embedding.snoc f ha) (Fin.last k) = a
      rw [Fin.Embedding.snoc_last]

private lemma sum_embedding_snoc_split {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (F : (Fin (k + 1) ↪ n) → ℝ) :
    ∑ f : Fin (k + 1) ↪ n, F f =
      ∑ f' : Fin k ↪ n, ∑ a : {a : n // a ∉ Set.range f'},
        F ((embSnocEquiv k).symm ⟨f', a⟩) := by
  rw [← Equiv.sum_comp (embSnocEquiv k).symm F, Fintype.sum_sigma]

private lemma sum_compl_range_split {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (f' : Fin k ↪ n) (G : n → ℝ) :
    ∑ a : {a : n // a ∉ Set.range f'}, G a.1 =
      ∑ a : n, G a - ∑ i : Fin k, G (f' i) := by
  have h1 : ∑ a ∈ (Finset.univ.image f' : Finset n)ᶜ, G a
      = ∑ a : {a : n // a ∉ Set.range f'}, G a.1 :=
    Finset.sum_subtype _ (by simp) G
  rw [← h1]
  have h2 : ∑ a ∈ (Finset.univ.image f' : Finset n)ᶜ, G a
      = ∑ a : n, G a - ∑ a ∈ (Finset.univ.image f' : Finset n), G a := by
    rw [eq_sub_iff_add_eq, Finset.sum_compl_add_sum]
  rw [h2]
  congr 1
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact f'.injective hxy

private lemma sum_cons_reindex {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ)
    (G : n → (Fin m → n) → ℝ) :
    ∑ x : n, ∑ h : Fin m → n, G x h = ∑ z : Fin (m + 1) → n, G (z 0) (z ∘ Fin.succ) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => n))
    (fun p => G p.1 p.2) (fun z => G (z 0) (z ∘ Fin.succ)) (fun p => ?_)
  simp [Fin.consEquiv]

private lemma sum_unique_emb_zero {n : Type*} [Fintype n] [DecidableEq n]
    (F : (Fin 0 ↪ n) → ℝ) : ∑ f : Fin 0 ↪ n, F f = F Function.Embedding.ofIsEmpty := by
  have : Unique (Fin 0 ↪ n) := by
    refine ⟨⟨Function.Embedding.ofIsEmpty⟩, fun f => ?_⟩
    apply DFunLike.ext
    exact isEmptyElim
  rw [Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

private lemma comp_snoc {n : Type*} {k : ℕ} (lam : n → ℝ) (u : Fin k → n) (x : n) :
    lam ∘ (Fin.snoc u x : Fin (k + 1) → n) = Fin.snoc (lam ∘ u) (lam x) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-! ### The two-argument test-function class and its decomposition statement -/

private def IsTestFun2 {k m : ℕ} (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry O) ∧ HasCompactSupport (Function.uncurry O)

private def BddByR {k m : ℕ} (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ) : Prop :=
  ∀ x y, O x y ≠ 0 → (∀ j, |x j| ≤ R) ∧ (∀ j, |y j| ≤ R)

private def Decomp2 (k m : ℕ) (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (kk : ι → ℕ) (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ),
    (∀ i, kk i ≤ k + m) ∧ (∀ i, IsTestFun (Oj i)) ∧
    (∀ i x, Oj i x ≠ 0 → ∀ j, |x j| ≤ R) ∧
    ∀ (n : Type) [Fintype n] [DecidableEq n] (lam : n → ℝ),
      ∑ f : Fin k ↪ n, ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h) =
        ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n, Oj i (lam ∘ g)

/-! ### Base case `k = 0` -/

private lemma decomp2_zero (m : ℕ) (O : (Fin 0 → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ)
    (hO : IsTestFun2 O) (hR : BddByR O R) : Decomp2 0 m O R := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => m, fun _ => O Fin.elim0, ?_, ?_, ?_, ?_⟩
  · intro _; simp
  · intro _
    have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin m → ℝ => ((Fin.elim0 : Fin 0 → ℝ), z)) :=
      contDiff_const.prodMk contDiff_id
    have hΨ : Continuous (fun z : Fin m → ℝ => ((Fin.elim0 : Fin 0 → ℝ), z)) :=
      continuous_const.prodMk continuous_id
    refine ⟨hO.1.comp hΦ, ?_⟩
    have := hasCompactSupport_comp_of_retraction (O := Function.uncurry O) hO.2
      (Φ := fun z : Fin m → ℝ => ((Fin.elim0 : Fin 0 → ℝ), z)) (Ψ := Prod.snd)
      hΨ continuous_snd (fun z => rfl)
    exact this
  · intro _ x hx j
    exact (hR Fin.elim0 x hx).2 j
  · intro n _ _ lam
    rw [sum_unique_emb_zero]
    have hlam0 : lam ∘ (Function.Embedding.ofIsEmpty : Fin 0 ↪ n) = (Fin.elim0 : Fin 0 → ℝ) := by
      funext i; exact i.elim0
    rw [hlam0]
    simp

/-! ### The inductive step -/

private def mkO1 {k m : ℕ} (O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ) :
    (Fin k → ℝ) → (Fin (m + 1) → ℝ) → ℝ :=
  fun y z => O (Fin.snoc y (z 0)) (z ∘ Fin.succ)

private def mkO2 {k m : ℕ} (O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ) (i : Fin k) :
    (Fin k → ℝ) → (Fin m → ℝ) → ℝ :=
  fun y z => O (Fin.snoc y (y i)) z

private lemma isTestFun2_mkO1 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ}
    (hO : IsTestFun2 O) : IsTestFun2 (mkO1 O) := by
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ), p.2 ∘ Fin.succ)) := by
    refine (?_ : ContDiff ℝ (⊤:ℕ∞) (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        (Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ))).prodMk ?_
    · apply contDiff_pi'
      intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact (contDiff_apply ℝ ℝ (0 : Fin (m + 1))).comp contDiff_snd
      | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
    · apply contDiff_pi'
      intro i
      exact (contDiff_apply ℝ ℝ (i.succ)).comp contDiff_snd
  have hΦc : Continuous
      (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ), p.2 ∘ Fin.succ)) := hΦcd.continuous
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) =>
        (Fin.init p.1, (Fin.cons (p.1 (Fin.last k)) p.2 : Fin (m + 1) → ℝ))) := by
    refine (?_ : ContDiff ℝ (⊤:ℕ∞) (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) => Fin.init p.1)).prodMk ?_
    · apply contDiff_pi'
      intro j
      exact (contDiff_apply ℝ ℝ (j.castSucc)).comp contDiff_fst
    · apply contDiff_pi'
      intro i
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact (contDiff_apply ℝ ℝ (Fin.last k)).comp contDiff_fst
      | succ j => simp only [Fin.cons_succ]; exact (contDiff_apply ℝ ℝ j).comp contDiff_snd
  have hΨc : Continuous
      (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) =>
        (Fin.init p.1, (Fin.cons (p.1 (Fin.last k)) p.2 : Fin (m + 1) → ℝ))) := hΨcd.continuous
  have hret : ∀ p : (Fin k → ℝ) × (Fin (m + 1) → ℝ),
      (Fin.init (Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ),
          (Fin.cons ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ) (Fin.last k)) (p.2 ∘ Fin.succ)
            : Fin (m + 1) → ℝ)) = p := by
    rintro ⟨y, z⟩
    have e1 : Fin.init (Fin.snoc y (z 0) : Fin (k + 1) → ℝ) = y := by simp
    have e2 : (Fin.snoc y (z 0) : Fin (k + 1) → ℝ) (Fin.last k) = z 0 := by simp
    simp only [e1, e2]
    congr 1
    exact Fin.cons_self_tail z
  have hEq : Function.uncurry (mkO1 O) = Function.uncurry O ∘
      (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ), p.2 ∘ Fin.succ)) := by
    funext p; rfl
  rw [IsTestFun2, hEq]
  exact ⟨hO.1.comp hΦcd, hasCompactSupport_comp_of_retraction (O := Function.uncurry O) hO.2 hΦc hΨc hret⟩

private lemma isTestFun2_mkO2 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ} (i : Fin k)
    (hO : IsTestFun2 O) : IsTestFun2 (mkO2 O i) := by
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) => ((Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2)) := by
    refine (?_ : ContDiff ℝ (⊤:ℕ∞) (fun p : (Fin k → ℝ) × (Fin m → ℝ) =>
        (Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ))).prodMk contDiff_snd
    apply contDiff_pi'
    intro j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
  have hΦc : Continuous
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) => ((Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2)) :=
    hΦcd.continuous
  have hΨc : Continuous (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) => (Fin.init p.1, p.2)) := by
    fun_prop
  have hret : ∀ p : (Fin k → ℝ) × (Fin m → ℝ),
      (Fin.init (Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2) = p := by
    rintro ⟨y, z⟩
    have e1 : Fin.init (Fin.snoc y (y i) : Fin (k + 1) → ℝ) = y := by simp
    rw [e1]
  have hEq : Function.uncurry (mkO2 O i) = Function.uncurry O ∘
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) => ((Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2)) := by
    funext p; rfl
  rw [IsTestFun2, hEq]
  exact ⟨hO.1.comp hΦcd, hasCompactSupport_comp_of_retraction (O := Function.uncurry O) hO.2 hΦc hΨc hret⟩

private lemma bddByR_mkO1 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ} {R : ℝ}
    (hR : BddByR O R) : BddByR (mkO1 O) R := by
  intro y z hz
  have hz' := hR (Fin.snoc y (z 0)) (z ∘ Fin.succ) hz
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := hz'.1 j.castSucc
    rwa [Fin.snoc_castSucc] at this
  · induction j using Fin.cases with
    | zero => have := hz'.1 (Fin.last k); rwa [Fin.snoc_last] at this
    | succ j => exact hz'.2 j

private lemma bddByR_mkO2 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ} {R : ℝ} (i : Fin k)
    (hR : BddByR O R) : BddByR (mkO2 O i) R := by
  intro y z hz
  have hz' := hR (Fin.snoc y (y i)) z hz
  refine ⟨fun j => ?_, fun j => hz'.2 j⟩
  have := hz'.1 j.castSucc
  rwa [Fin.snoc_castSucc] at this

/-! ### The key combinatorial identity for the inductive step -/

private lemma key_identity {n : Type*} [Fintype n] [DecidableEq n] {k m : ℕ}
    (O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ) (lam : n → ℝ) :
    ∑ f : Fin (k + 1) ↪ n, ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h) =
      (∑ f' : Fin k ↪ n, ∑ z : Fin (m + 1) → n, mkO1 O (lam ∘ f') (lam ∘ z)) -
        ∑ i : Fin k, ∑ f' : Fin k ↪ n, ∑ h : Fin m → n, mkO2 O i (lam ∘ f') (lam ∘ h) := by
  have step1 : ∑ f : Fin (k + 1) ↪ n, ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h) =
      ∑ f' : Fin k ↪ n, ∑ a : {a : n // a ∉ Set.range f'},
        ∑ h : Fin m → n, O (lam ∘ ((embSnocEquiv k).symm ⟨f', a⟩)) (lam ∘ h) :=
    sum_embedding_snoc_split k (fun f => ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h))
  rw [step1]
  have step2 : ∀ (f' : Fin k ↪ n) (a : {a : n // a ∉ Set.range f'}),
      ∑ h : Fin m → n, O (lam ∘ ((embSnocEquiv k).symm ⟨f', a⟩)) (lam ∘ h) =
        ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a.1)) (lam ∘ h) := by
    intro f' a
    have hco : lam ∘ ((embSnocEquiv k).symm ⟨f', a⟩ : Fin (k + 1) ↪ n) =
        Fin.snoc (lam ∘ (f' : Fin k → n)) (lam a.1) := by
      show lam ∘ (Fin.Embedding.snoc f' a.2 : Fin (k + 1) ↪ n) = _
      rw [show (⇑(Fin.Embedding.snoc f' a.2) : Fin (k + 1) → n) = Fin.snoc (⇑f') a.1 from
        Fin.Embedding.coe_snoc f' a.2]
      exact comp_snoc lam f' a.1
    rw [hco]
  simp_rw [step2]
  have step3 : ∀ f' : Fin k ↪ n,
      ∑ a : {a : n // a ∉ Set.range f'}, ∑ h : Fin m → n,
          O (Fin.snoc (lam ∘ f') (lam a.1)) (lam ∘ h) =
        (∑ a : n, ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h)) -
          ∑ i : Fin k, ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam (f' i))) (lam ∘ h) := by
    intro f'
    exact sum_compl_range_split k f'
      (fun a => ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h))
  simp_rw [step3]
  have step4 : ∀ f' : Fin k ↪ n,
      ∑ a : n, ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h) =
        ∑ z : Fin (m + 1) → n, mkO1 O (lam ∘ f') (lam ∘ z) := by
    intro f'
    rw [sum_cons_reindex m (fun a h => O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h))]
    rfl
  simp_rw [step4]
  have step5 : ∀ (f' : Fin k ↪ n) (i : Fin k),
      ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam (f' i))) (lam ∘ h) =
        ∑ h : Fin m → n, mkO2 O i (lam ∘ f') (lam ∘ h) := by
    intro f' i; rfl
  simp_rw [step5]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-! ### Main induction -/

private lemma decomp2_of_testFun2 : ∀ (k m : ℕ) (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ),
    IsTestFun2 O → BddByR O R → Decomp2 k m O R := by
  intro k
  induction k with
  | zero => exact decomp2_zero
  | succ k ih =>
    intro m O R hO hR
    obtain ⟨ι1, fι1, c1, kk1, Oj1, hkk1, hTest1, hBound1, heq1⟩ :=
      ih (m + 1) (mkO1 O) R (isTestFun2_mkO1 hO) (bddByR_mkO1 hR)
    have D2 : ∀ i : Fin k, Decomp2 k m (mkO2 O i) R := fun i =>
      ih m (mkO2 O i) R (isTestFun2_mkO2 i hO) (bddByR_mkO2 i hR)
    choose ι2 fι2 c2 kk2 Oj2 hkk2 hTest2 hBound2 heq2 using D2
    let _ := fι1
    let _ := fι2
    refine ⟨ι1 ⊕ (Σ i : Fin k, ι2 i), inferInstance,
      Sum.elim c1 (fun p => -(c2 p.1 p.2)),
      fun i => match i with
        | Sum.inl j => kk1 j
        | Sum.inr p => kk2 p.1 p.2,
      fun i => match i with
        | Sum.inl j => Oj1 j
        | Sum.inr p => Oj2 p.1 p.2,
      ?_, ?_, ?_, ?_⟩
    · rintro (j | ⟨i,j⟩)
      · dsimp only; have := hkk1 j; omega
      · dsimp only; have := hkk2 i j; omega
    · rintro (j | ⟨i,j⟩)
      · exact hTest1 j
      · exact hTest2 i j
    · rintro (j | ⟨i,j⟩) x hx
      · exact hBound1 j x hx
      · exact hBound2 i j x hx
    · intro n _ _ lam
      rw [key_identity O lam, heq1 n lam]
      have hsum2 : ∀ i : Fin k,
          ∑ f' : Fin k ↪ n, ∑ h : Fin m → n, mkO2 O i (lam ∘ f') (lam ∘ h)
            = ∑ j : ι2 i, (c2 i j : ℝ) * ∑ g : Fin (kk2 i j) → n, Oj2 i j (lam ∘ g) :=
        fun i => heq2 i n lam
      simp_rw [hsum2]
      rw [Fintype.sum_sum_type, Fintype.sum_sigma]
      simp only [Sum.elim_inl, Sum.elim_inr]
      push_cast
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring

/-! ### Top-level theorem -/

theorem injSum_decomp (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : IsTestFun O) {R : ℝ}
    (hR : ∀ x, O x ≠ 0 → ∀ j, |x j| ≤ R) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (kk : ι → ℕ)
      (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ),
      (∀ i, kk i ≤ k) ∧ (∀ i, IsTestFun (Oj i)) ∧
      (∀ i x, Oj i x ≠ 0 → ∀ j, |x j| ≤ R) ∧
      ∀ (n : Type) [Fintype n] [DecidableEq n] (lam : n → ℝ),
        ∑ f : Fin k ↪ n, O (lam ∘ f) = ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n, Oj i (lam ∘ g) := by
  have hO2 : IsTestFun2 (fun x (_ : Fin 0 → ℝ) => O x) := by
    refine ⟨hO.1.comp contDiff_fst, ?_⟩
    exact hasCompactSupport_comp_of_retraction (O := O) hO.2 continuous_fst
      (Ψ := fun x => (x, (Fin.elim0 : Fin 0 → ℝ)))
      (by fun_prop) (fun p => by ext <;> simp [Subsingleton.elim p.2 (Fin.elim0 : Fin 0 → ℝ)])
  have hR2 : BddByR (fun x (_ : Fin 0 → ℝ) => O x) R := by
    intro x y hx
    exact ⟨hR x hx, fun j => j.elim0⟩
  obtain ⟨ι, fι, c, kk, Oj, hkk, hTest, hBound, heq⟩ := decomp2_of_testFun2 k 0 _ R hO2 hR2
  refine ⟨ι, fι, c, kk, Oj, hkk, hTest, hBound, ?_⟩
  intro n _ _ lam
  have := heq n lam
  simp only [Fintype.sum_unique] at this
  exact this

end RBM
