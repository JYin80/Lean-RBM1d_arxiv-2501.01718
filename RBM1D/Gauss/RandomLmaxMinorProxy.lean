/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.MinorDiffGain
import RBM1D.Gauss.FirstCellStep1LocalLaw

/-!
# Actual Gaussian smooth proxies for embedded principal minors

This module records the fixed-budget proxy attached to the actual embedded resolvents
`greenSetMat`. It reuses the existing row-freeness, (4.9), and scalar finite-minor calculus.
The all-tolerance actual entry source and the shared-minor fluctuation-average argument are
separate stages; this module does not assert either of them.
-/

namespace RBM.Gauss

open Filter MeasureTheory
open scoped BigOperators

/-- The block of an index is its original cyclic block coordinate. -/
def proxyBlock (d : Dims) (N : ℕ) (i : d.Idx N) : ZMod (d.L N) := i.1

/-- The squared Hilbert--Schmidt loop of the actual principal minor, with zero embedding and
the original bandwidth normalization. -/
noncomputable def embeddedMinorLoop (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) (a b : ZMod (d.L N)) : ℝ :=
  ((d.W N : ℝ)⁻¹) ^ 2 *
    ∑ p : d.Idx N × d.Idx N,
      if proxyBlock d N p.1 = a ∧ proxyBlock d N p.2 = b then
        ‖gEnt d N u z ω p.1 p.2 S‖ ^ 2 else 0

/-- The deterministic exponent used for all moment and failure budgets. -/
noncomputable def randomLmaxProxyExponent (N : ℕ) : ℕ :=
  2 * Nat.ceil (2 * Real.log ((N : ℝ) + 2)) + 8

/-- The positive mass whose `q_N`-root is the smooth maximum. -/
noncomputable def embeddedMinorProxyMass (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) : ℝ :=
  ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N +
    ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
      (embeddedMinorLoop d N u z S ω a b) ^ randomLmaxProxyExponent N

/-- The positive smooth maximum of all original-block loops of the embedded minor. -/
noncomputable def embeddedMinorProxy (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) : ℝ :=
  Real.rpow
    (embeddedMinorProxyMass d N u z S ω)
    ((randomLmaxProxyExponent N : ℝ)⁻¹)

/-- Every embedded-minor loop is nonnegative. -/
theorem embeddedMinorLoop_nonneg (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) (a b : ZMod (d.L N)) :
    0 ≤ embeddedMinorLoop d N u z S ω a b := by
  unfold embeddedMinorLoop
  positivity

private theorem finDepOffRows_const {d : Dims} {N : ℕ} (S : Finset (d.Idx N))
    {V : Type*} (v : V) : FinDepOffRows d N S fun _ : Ω d => v := by
  exact ⟨∅, by simp, fun _ _ _ => rfl⟩

private theorem finDepOffRows_mono {d : Dims} {N : ℕ} {S T : Finset (d.Idx N)}
    {V : Type*} {f : Ω d → V} (hST : S ⊆ T)
    (hf : FinDepOffRows d N T f) : FinDepOffRows d N S f := by
  obtain ⟨I, hI, hfun⟩ := hf
  exact ⟨I, fun c hc k hk => hI c hc k (hST hk), hfun⟩

private theorem finDepOffRows_add {d : Dims} {N : ℕ} {S : Finset (d.Idx N)}
    {V : Type*} [Add V] {f g : Ω d → V}
    (hf : FinDepOffRows d N S f) (hg : FinDepOffRows d N S g) :
    FinDepOffRows d N S fun ω => f ω + g ω := by
  obtain ⟨I, hI, hIf⟩ := hf
  obtain ⟨J, hJ, hJg⟩ := hg
  refine ⟨I ∪ J, ?_, ?_⟩
  · intro c hc k hk
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hI c hc k hk
    · exact hJ c hc k hk
  · intro ω ω' hω
    change f ω + g ω = f ω' + g ω'
    rw [hIf ω ω' (fun c hc => hω c (Finset.mem_union_left _ hc)),
      hJg ω ω' (fun c hc => hω c (Finset.mem_union_right _ hc))]

private theorem finDepOffRows_pair {d : Dims} {N : ℕ} {S : Finset (d.Idx N)}
    {V W : Type*} {f : Ω d → V} {g : Ω d → W}
    (hf : FinDepOffRows d N S f) (hg : FinDepOffRows d N S g) :
    FinDepOffRows d N S fun ω => (f ω, g ω) := by
  obtain ⟨I, hI, hIf⟩ := hf
  obtain ⟨J, hJ, hJg⟩ := hg
  refine ⟨I ∪ J, ?_, ?_⟩
  · intro c hc k hk
    rcases Finset.mem_union.mp hc with hc | hc
    · exact hI c hc k hk
    · exact hJ c hc k hk
  · intro ω ω' hω
    simp only [Prod.mk.injEq]
    exact ⟨hIf ω ω' (fun c hc => hω c (Finset.mem_union_left _ hc)),
      hJg ω ω' (fun c hc => hω c (Finset.mem_union_right _ hc))⟩

/-- Resample exactly the coordinates belonging to at least one row in `S`. -/
noncomputable def splitRows (d : Dims) (N : ℕ) (S : Finset (d.Idx N))
    (ω ω' : Ω d) : Ω d := fun c =>
  if ∃ k ∈ S, IsRowCoord d N k c then ω' c else ω c

private theorem finDepOffRows_splitRows_eq {d : Dims} {N : ℕ} {S : Finset (d.Idx N)}
    {V : Type*} {f : Ω d → V} (hf : FinDepOffRows d N S f)
    (ω ω' : Ω d) : f (splitRows d N S ω ω') = f ω := by
  obtain ⟨I, hI, hfun⟩ := hf
  apply (hfun (splitRows d N S ω ω') ω ?_)
  intro c hc
  rw [splitRows]
  have hnot : ¬∃ k ∈ S, IsRowCoord d N k c := by
    rintro ⟨k, hk, hcoord⟩
    exact (hI c hc k hk) hcoord
  simp [hnot]

private theorem finDepOffRows_sum {d : Dims} {N : ℕ} {S : Finset (d.Idx N)}
    {α V : Type*} [AddCommMonoid V] (t : Finset α)
    (f : α → Ω d → V) (hf : ∀ a ∈ t, FinDepOffRows d N S (f a)) :
    FinDepOffRows d N S fun ω => ∑ a ∈ t, f a ω := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      exact finDepOffRows_const S 0
  | @insert a t ha ih =>
      have hsum : (fun ω : Ω d => ∑ x ∈ insert a t, f x ω) =
          fun ω => f a ω + ∑ x ∈ t, f x ω := by
        funext ω
        rw [Finset.sum_insert ha]
      rw [hsum]
      exact finDepOffRows_add (hf a (Finset.mem_insert_self a t))
        (ih (fun x hx => hf x (Finset.mem_insert_of_mem hx)))

private theorem finDepOffRows_gEnt (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (a b : d.Idx N) :
    FinDepOffRows d N S fun ω => gEnt d N u z ω a b S := by
  by_cases ha : a ∉ S
  · by_cases hb : b ∉ S
    · have heq : (fun ω => gEnt d N u z ω a b S) =
          (fun ω => greenSetMat d N u z S ω ⟨a, ha⟩ ⟨b, hb⟩) := by
        funext ω
        exact gEnt_apply ha hb
      rw [heq]
      exact finDepOffRows_greenSetMat_apply d N u z S ⟨a, ha⟩ ⟨b, hb⟩
    · have heq : (fun ω => gEnt d N u z ω a b S) = fun _ => 0 := by
        funext ω
        exact gEnt_eq_zero_right (not_not.mp hb)
      rw [heq]
      exact finDepOffRows_const S 0
  · have heq : (fun ω => gEnt d N u z ω a b S) = fun _ => 0 := by
      funext ω
      exact gEnt_eq_zero_left (not_not.mp ha)
    rw [heq]
    exact finDepOffRows_const S 0

/-- The block-loop proxy is strictly free of every deleted row. -/
theorem finDepOffRows_embeddedMinorLoop (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (a b : ZMod (d.L N)) :
    FinDepOffRows d N S fun ω => embeddedMinorLoop d N u z S ω a b := by
  classical
  have hsum := finDepOffRows_sum (d := d) (N := N) (S := S)
    (Finset.univ : Finset (d.Idx N × d.Idx N))
    (fun p ω => if proxyBlock d N p.1 = a ∧ proxyBlock d N p.2 = b then
      ‖gEnt d N u z ω p.1 p.2 S‖ ^ 2 else 0)
    (by
      intro p hp
      exact (finDepOffRows_gEnt d N u z S p.1 p.2).comp fun x =>
        if proxyBlock d N p.1 = a ∧ proxyBlock d N p.2 = b then ‖x‖ ^ 2 else 0)
  have hscaled := hsum.comp fun x => ((d.W N : ℝ)⁻¹) ^ 2 * x
  simpa [embeddedMinorLoop] using hscaled

/-- The entire smooth minor proxy is free of all deleted rows. -/
theorem finDepOffRows_embeddedMinorProxy (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) :
    FinDepOffRows d N S fun ω => embeddedMinorProxy d N u z S ω := by
  classical
  let q := randomLmaxProxyExponent N
  have hsum := finDepOffRows_sum (d := d) (N := N) (S := S)
    (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N)))
    (fun p ω => (embeddedMinorLoop d N u z S ω p.1 p.2) ^ q)
    (by
      intro p hp
      exact (finDepOffRows_embeddedMinorLoop d N u z S p.1 p.2).comp fun x => x ^ q)
  have hmass : FinDepOffRows d N S fun ω => embeddedMinorProxyMass d N u z S ω := by
    have hfloor := finDepOffRows_const S (((d.W N : ℝ)⁻¹) ^ q)
    have hsum' : FinDepOffRows d N S fun ω =>
        ∑ p ∈ (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N))),
          (embeddedMinorLoop d N u z S ω p.1 p.2) ^ q := hsum
    have h := finDepOffRows_add hfloor hsum'
    simpa [embeddedMinorProxyMass, q, Fintype.sum_prod_type] using h
  simpa [embeddedMinorProxy] using hmass.comp fun x =>
    Real.rpow x ((randomLmaxProxyExponent N : ℝ)⁻¹)

/-- Same-event equality of the fully deleted denominator after resampling all rows in its
deletion set. -/
theorem embeddedMinorProxy_splitRows_eq (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω ω' : Ω d) :
    embeddedMinorProxy d N u z S (splitRows d N S ω ω') =
      embeddedMinorProxy d N u z S ω :=
  finDepOffRows_splitRows_eq (finDepOffRows_embeddedMinorProxy d N u z S) ω ω'

/-- Row-normalized centered diagonal for an embedded minor. For a fresh pivot `i`, its
denominator is the proxy of the minor with row `i` also removed. -/
noncomputable def rowNormalizedMinorDiag (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ)
    (S : Finset (d.Idx N)) (i : d.Idx N) (ω : Ω d) : ℂ :=
  if i ∉ S then
    greenSetDiagCentered d N u z m i S ω /
      (embeddedMinorProxy d N u z (insert i S) ω : ℂ)
  else 0

/-- The normalized diagonal family remains free of every row already deleted in `S`. -/
theorem finDepOffRows_rowNormalizedMinorDiag (d : Dims) (N : ℕ) (u : ℝ) (z m : ℂ)
    (S : Finset (d.Idx N)) (i : d.Idx N) :
    FinDepOffRows d N S fun ω => rowNormalizedMinorDiag d N u z m S i ω := by
  by_cases hi : i ∉ S
  · have hnum := finDepOffRows_greenSetDiagCentered d N u z m i S
    have hden := finDepOffRows_embeddedMinorProxy d N u z (insert i S)
    have hden' := finDepOffRows_mono (Finset.subset_insert i S) hden
    have hpair := finDepOffRows_pair hnum hden'
    have hratio := hpair.comp fun p : ℂ × ℝ => p.1 / (p.2 : ℂ)
    have heq : (fun ω => rowNormalizedMinorDiag d N u z m S i ω) =
        (fun ω => greenSetDiagCentered d N u z m i S ω /
          (embeddedMinorProxy d N u z (insert i S) ω : ℂ)) := by
      funext ω
      simp [rowNormalizedMinorDiag, hi]
    rw [heq]
    exact hratio
  · have heq : (fun ω => rowNormalizedMinorDiag d N u z m S i ω) = fun _ => 0 := by
      funext ω
      simp [rowNormalizedMinorDiag, hi]
    rw [heq]
    exact finDepOffRows_const S 0

/-- The mass defining the smooth proxy is positive on every sample. -/
theorem embeddedMinorProxyMass_pos (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    0 < embeddedMinorProxyMass d N u z S ω := by
  unfold embeddedMinorProxyMass
  have hW : 0 < (d.W N : ℝ) := Nat.cast_pos.mpr (d.W_pos N)
  have hfloor : 0 < ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N :=
    pow_pos (inv_pos.mpr hW) _
  have hloop : ∀ a b : ZMod (d.L N), 0 ≤ embeddedMinorLoop d N u z S ω a b :=
    fun a b => embeddedMinorLoop_nonneg d N u z S ω a b
  have hsum : 0 ≤ ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
      (embeddedMinorLoop d N u z S ω a b) ^ randomLmaxProxyExponent N := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    exact pow_nonneg (hloop a b) _
  linarith

/-- The smooth proxy is strictly positive, including on exceptional samples. -/
theorem embeddedMinorProxy_pos (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    0 < embeddedMinorProxy d N u z S ω := by
  rw [embeddedMinorProxy]
  exact Real.rpow_pos_of_pos (embeddedMinorProxyMass_pos d N u z S ω) _

/-- The deterministic exponent is positive for every size. -/
theorem randomLmaxProxyExponent_pos (N : ℕ) : 0 < randomLmaxProxyExponent N := by
  change 0 < 2 * Nat.ceil (2 * Real.log ((N : ℝ) + 2)) + 8
  omega

/-- The proxy dominates its deterministic floor, so its reciprocal has the global envelope
`W`. -/
theorem embeddedMinorProxy_inv_le_W (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    (embeddedMinorProxy d N u z S ω)⁻¹ ≤ (d.W N : ℝ) := by
  have hW : 0 < (d.W N : ℝ) := Nat.cast_pos.mpr (d.W_pos N)
  have hqN := randomLmaxProxyExponent_pos N
  have hq : 0 < (randomLmaxProxyExponent N : ℝ) := Nat.cast_pos.mpr hqN
  have hmass := embeddedMinorProxyMass_pos d N u z S ω
  have hlam := embeddedMinorProxy_pos d N u z S ω
  have hroot : (embeddedMinorProxy d N u z S ω) ^ randomLmaxProxyExponent N
      = embeddedMinorProxyMass d N u z S ω := by
    rw [← Real.rpow_natCast]
    change Real.rpow (Real.rpow (embeddedMinorProxyMass d N u z S ω)
      ((randomLmaxProxyExponent N : ℝ)⁻¹)) (randomLmaxProxyExponent N : ℝ)
      = embeddedMinorProxyMass d N u z S ω
    have hmul := (Real.rpow_mul (le_of_lt hmass)
      ((randomLmaxProxyExponent N : ℝ)⁻¹)
      (randomLmaxProxyExponent N : ℝ)).symm
    calc
      Real.rpow (Real.rpow (embeddedMinorProxyMass d N u z S ω)
          ((randomLmaxProxyExponent N : ℝ)⁻¹)) (randomLmaxProxyExponent N : ℝ)
          = Real.rpow (embeddedMinorProxyMass d N u z S ω)
              ((randomLmaxProxyExponent N : ℝ)⁻¹ *
                (randomLmaxProxyExponent N : ℝ)) := hmul
      _ = embeddedMinorProxyMass d N u z S ω := by
            rw [inv_mul_cancel₀ hq.ne']
            exact Real.rpow_one _
  have hfloor : ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N
      ≤ embeddedMinorProxyMass d N u z S ω := by
    unfold embeddedMinorProxyMass
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => pow_nonneg (embeddedMinorLoop_nonneg d N u z S ω a b) _)
  have hroot' : ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N
      ≤ (embeddedMinorProxy d N u z S ω) ^ randomLmaxProxyExponent N := by
    rw [hroot]
    exact hfloor
  have hbase : (d.W N : ℝ)⁻¹ ≤ embeddedMinorProxy d N u z S ω := by
    apply (Real.rpow_le_rpow_iff (inv_nonneg.mpr hW.le)
      (le_of_lt hlam) hq).mp
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact hroot'
  calc
    (embeddedMinorProxy d N u z S ω)⁻¹ ≤ ((d.W N : ℝ)⁻¹)⁻¹ := by
      exact (inv_le_inv₀ hlam (inv_pos.mpr hW)).2 hbase
    _ = (d.W N : ℝ) := inv_inv _

/-- The smooth proxy dominates the deterministic floor. -/
theorem embeddedMinorProxy_ge_floor (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    (d.W N : ℝ)⁻¹ ≤ embeddedMinorProxy d N u z S ω := by
  have hW : 0 < (d.W N : ℝ) := Nat.cast_pos.mpr (d.W_pos N)
  have hqN := randomLmaxProxyExponent_pos N
  have hq : 0 < (randomLmaxProxyExponent N : ℝ) := Nat.cast_pos.mpr hqN
  have hmass := embeddedMinorProxyMass_pos d N u z S ω
  have hlam := embeddedMinorProxy_pos d N u z S ω
  have hroot : (embeddedMinorProxy d N u z S ω) ^ randomLmaxProxyExponent N
      = embeddedMinorProxyMass d N u z S ω := by
    rw [← Real.rpow_natCast]
    change Real.rpow (Real.rpow (embeddedMinorProxyMass d N u z S ω)
      ((randomLmaxProxyExponent N : ℝ)⁻¹)) (randomLmaxProxyExponent N : ℝ)
      = embeddedMinorProxyMass d N u z S ω
    have hmul := (Real.rpow_mul (le_of_lt hmass)
      ((randomLmaxProxyExponent N : ℝ)⁻¹)
      (randomLmaxProxyExponent N : ℝ)).symm
    calc
      Real.rpow (Real.rpow (embeddedMinorProxyMass d N u z S ω)
          ((randomLmaxProxyExponent N : ℝ)⁻¹)) (randomLmaxProxyExponent N : ℝ)
          = Real.rpow (embeddedMinorProxyMass d N u z S ω)
              ((randomLmaxProxyExponent N : ℝ)⁻¹ *
                (randomLmaxProxyExponent N : ℝ)) := hmul
      _ = embeddedMinorProxyMass d N u z S ω := by
            rw [inv_mul_cancel₀ hq.ne']
            exact Real.rpow_one _
  have hfloor : ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N
      ≤ embeddedMinorProxyMass d N u z S ω := by
    unfold embeddedMinorProxyMass
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => pow_nonneg (embeddedMinorLoop_nonneg d N u z S ω a b) _)
  have hpow : ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N
      ≤ (embeddedMinorProxy d N u z S ω) ^ randomLmaxProxyExponent N := by
    rw [hroot]
    exact hfloor
  apply (Real.rpow_le_rpow_iff (inv_nonneg.mpr hW.le) (le_of_lt hlam) hq).mp
  rw [Real.rpow_natCast, Real.rpow_natCast]
  exact hpow

/-- Every block loop is pointwise dominated by the smooth proxy. -/
theorem embeddedMinorProxy_ge_loop (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) (a b : ZMod (d.L N)) :
    embeddedMinorLoop d N u z S ω a b ≤ embeddedMinorProxy d N u z S ω := by
  have hW : 0 < (d.W N : ℝ) := Nat.cast_pos.mpr (d.W_pos N)
  have hqN := randomLmaxProxyExponent_pos N
  have hq : 0 < (randomLmaxProxyExponent N : ℝ) := Nat.cast_pos.mpr hqN
  have hmass := embeddedMinorProxyMass_pos d N u z S ω
  have hlam := embeddedMinorProxy_pos d N u z S ω
  have hroot : (embeddedMinorProxy d N u z S ω) ^ randomLmaxProxyExponent N
      = embeddedMinorProxyMass d N u z S ω := by
    rw [← Real.rpow_natCast]
    change Real.rpow (Real.rpow (embeddedMinorProxyMass d N u z S ω)
      ((randomLmaxProxyExponent N : ℝ)⁻¹)) (randomLmaxProxyExponent N : ℝ)
      = embeddedMinorProxyMass d N u z S ω
    have hmul := (Real.rpow_mul (le_of_lt hmass)
      ((randomLmaxProxyExponent N : ℝ)⁻¹)
      (randomLmaxProxyExponent N : ℝ)).symm
    calc
      Real.rpow (Real.rpow (embeddedMinorProxyMass d N u z S ω)
          ((randomLmaxProxyExponent N : ℝ)⁻¹)) (randomLmaxProxyExponent N : ℝ)
          = Real.rpow (embeddedMinorProxyMass d N u z S ω)
              ((randomLmaxProxyExponent N : ℝ)⁻¹ *
                (randomLmaxProxyExponent N : ℝ)) := hmul
      _ = embeddedMinorProxyMass d N u z S ω := by
            rw [inv_mul_cancel₀ hq.ne']
            exact Real.rpow_one _
  have hterm : (embeddedMinorLoop d N u z S ω a b) ^
      randomLmaxProxyExponent N ≤
      ∑ x : ZMod (d.L N), ∑ y : ZMod (d.L N),
        (embeddedMinorLoop d N u z S ω x y) ^ randomLmaxProxyExponent N := by
    calc
      (embeddedMinorLoop d N u z S ω a b) ^ randomLmaxProxyExponent N
          ≤ ∑ y : ZMod (d.L N),
              (embeddedMinorLoop d N u z S ω a y) ^ randomLmaxProxyExponent N :=
            Finset.single_le_sum (fun y _ => pow_nonneg
              (embeddedMinorLoop_nonneg d N u z S ω a y) _) (Finset.mem_univ b)
      _ ≤ ∑ x : ZMod (d.L N), ∑ y : ZMod (d.L N),
              (embeddedMinorLoop d N u z S ω x y) ^ randomLmaxProxyExponent N :=
            Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ => pow_nonneg
              (embeddedMinorLoop_nonneg d N u z S ω x y) _) (Finset.mem_univ a)
  have hmassLower : (embeddedMinorLoop d N u z S ω a b) ^
      randomLmaxProxyExponent N ≤ embeddedMinorProxyMass d N u z S ω := by
    unfold embeddedMinorProxyMass
    calc
      (embeddedMinorLoop d N u z S ω a b) ^ randomLmaxProxyExponent N
          ≤ ∑ x : ZMod (d.L N), ∑ y : ZMod (d.L N),
              (embeddedMinorLoop d N u z S ω x y) ^ randomLmaxProxyExponent N := hterm
      _ ≤ ((d.W N : ℝ)⁻¹) ^ randomLmaxProxyExponent N +
            ∑ x : ZMod (d.L N), ∑ y : ZMod (d.L N),
              (embeddedMinorLoop d N u z S ω x y) ^ randomLmaxProxyExponent N := by
            linarith [pow_nonneg (inv_nonneg.mpr hW.le) (randomLmaxProxyExponent N)]
  have hpow : (embeddedMinorLoop d N u z S ω a b) ^
      randomLmaxProxyExponent N ≤
      (embeddedMinorProxy d N u z S ω) ^ randomLmaxProxyExponent N := by
    rw [hroot]
    exact hmassLower
  apply (Real.rpow_le_rpow_iff (embeddedMinorLoop_nonneg d N u z S ω a b)
    (le_of_lt hlam) hq).mp
  rw [Real.rpow_natCast, Real.rpow_natCast]
  exact hpow

/-- Number of coordinates in the smooth maximum, including its floor coordinate. -/
noncomputable def embeddedMinorProxyCount (d : Dims) (N : ℕ) : ℝ :=
  (Fintype.card (ZMod (d.L N)) : ℝ) ^ 2 + 1

/-- If a common deterministic envelope bounds the floor and every block loop, the proxy is
bounded by the q-root of the number of coordinates times that envelope. -/
theorem embeddedMinorProxy_le_countRoot_mul (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) {B : ℝ} (hB : 0 < B)
    (hfloor : (d.W N : ℝ)⁻¹ ≤ B)
    (hloops : ∀ a b : ZMod (d.L N), embeddedMinorLoop d N u z S ω a b ≤ B) :
    embeddedMinorProxy d N u z S ω ≤
      (embeddedMinorProxyCount d N) ^ ((randomLmaxProxyExponent N : ℝ)⁻¹) * B := by
  let q := randomLmaxProxyExponent N
  let qR := (q : ℝ)
  have hqN : 0 < q := randomLmaxProxyExponent_pos N
  have hqR : 0 < qR := Nat.cast_pos.mpr hqN
  have hqInv : 0 ≤ qR⁻¹ := (inv_nonneg.mpr hqR.le)
  have hfloorPow : ((d.W N : ℝ)⁻¹) ^ q ≤ B ^ q :=
    pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg _)) hfloor q
  have hsumPow :
      (∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
        (embeddedMinorLoop d N u z S ω a b) ^ q)
        ≤ (Fintype.card (ZMod (d.L N)) : ℝ) ^ 2 * B ^ q := by
    calc
      (∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
          (embeddedMinorLoop d N u z S ω a b) ^ q)
          ≤ ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N), B ^ q := by
              apply Finset.sum_le_sum
              intro a _
              apply Finset.sum_le_sum
              intro b _
              exact pow_le_pow_left₀ (embeddedMinorLoop_nonneg d N u z S ω a b)
                (hloops a b) q
      _ = (Fintype.card (ZMod (d.L N)) : ℝ) ^ 2 * B ^ q := by
            simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            ring
  have hmass : embeddedMinorProxyMass d N u z S ω ≤
      embeddedMinorProxyCount d N * B ^ q := by
    unfold embeddedMinorProxyMass embeddedMinorProxyCount
    calc
      ((d.W N : ℝ)⁻¹) ^ q +
          ∑ a : ZMod (d.L N), ∑ b : ZMod (d.L N),
            (embeddedMinorLoop d N u z S ω a b) ^ q
          ≤ B ^ q + (Fintype.card (ZMod (d.L N)) : ℝ) ^ 2 * B ^ q :=
            add_le_add hfloorPow hsumPow
      _ = ((Fintype.card (ZMod (d.L N)) : ℝ) ^ 2 + 1) * B ^ q := by ring
  have hmassPos := embeddedMinorProxyMass_pos d N u z S ω
  have hmassNonneg := le_of_lt hmassPos
  have hcountNonneg : 0 ≤ embeddedMinorProxyCount d N := by
    unfold embeddedMinorProxyCount
    positivity
  have hpowRoot : Real.rpow (B ^ q) qR⁻¹ = B := by
    rw [← Real.rpow_natCast]
    change Real.rpow (Real.rpow B qR) qR⁻¹ = B
    have hmul := (Real.rpow_mul hB.le qR qR⁻¹).symm
    calc
      Real.rpow (Real.rpow B qR) qR⁻¹ = Real.rpow B (qR * qR⁻¹) := hmul
      _ = B := by
        rw [mul_inv_cancel₀ hqR.ne']
        exact Real.rpow_one _
  calc
    embeddedMinorProxy d N u z S ω
        = Real.rpow (embeddedMinorProxyMass d N u z S ω) qR⁻¹ := rfl
    _ ≤ Real.rpow (embeddedMinorProxyCount d N * B ^ q) qR⁻¹ :=
          Real.rpow_le_rpow hmassNonneg hmass hqInv
    _ = Real.rpow (embeddedMinorProxyCount d N) qR⁻¹ * B := by
          calc
            Real.rpow (embeddedMinorProxyCount d N * B ^ q) qR⁻¹
                = Real.rpow (embeddedMinorProxyCount d N) qR⁻¹ *
                    Real.rpow (B ^ q) qR⁻¹ :=
                  Real.mul_rpow hcountNonneg (pow_nonneg hB.le q)
            _ = Real.rpow (embeddedMinorProxyCount d N) qR⁻¹ * B := by rw [hpowRoot]
    _ ≤ (embeddedMinorProxyCount d N) ^ qR⁻¹ * B := by
          exact mul_le_mul_of_nonneg_right le_rfl hB.le

/-- The chosen logarithmic exponent controls the number of block coordinates uniformly for
all sufficiently large model sizes. -/
theorem embeddedMinorProxyCount_rpow_le_exp_eventually (d : Dims) :
    ∀ᶠ N : ℕ in atTop,
      (embeddedMinorProxyCount d N) ^ ((randomLmaxProxyExponent N : ℝ)⁻¹)
        ≤ Real.exp 1 := by
  filter_upwards [d.dim] with N hdim
  have hW1 : 1 ≤ (d.W N : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (d.W_pos N))
  have hLle : (d.L N : ℝ) ≤ (N : ℝ) := by
    have hprod : (d.W N : ℝ) * (d.L N : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hdim.1
    have hL0 : 0 ≤ (d.L N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcard : (Fintype.card (ZMod (d.L N)) : ℝ) = (d.L N : ℝ) := by
    exact_mod_cast (ZMod.card (d.L N))
  have hx : 0 < (N : ℝ) + 2 := by positivity
  have hcountPos : 0 < embeddedMinorProxyCount d N := by
    unfold embeddedMinorProxyCount
    positivity
  have hcountBound : embeddedMinorProxyCount d N ≤ ((N : ℝ) + 2) ^ 2 := by
    unfold embeddedMinorProxyCount
    rw [hcard]
    nlinarith [hLle]
  have hlogCount : Real.log (embeddedMinorProxyCount d N)
      ≤ 2 * Real.log ((N : ℝ) + 2) := by
    calc
      Real.log (embeddedMinorProxyCount d N)
          ≤ Real.log (((N : ℝ) + 2) ^ 2) := Real.log_le_log hcountPos hcountBound
      _ = 2 * Real.log ((N : ℝ) + 2) := by rw [Real.log_pow]; norm_num
  have hlogX0 : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ (N : ℝ) + 2)
  have hceil : 2 * Real.log ((N : ℝ) + 2)
      ≤ (Nat.ceil (2 * Real.log ((N : ℝ) + 2)) : ℝ) := by
    exact_mod_cast Nat.le_ceil (2 * Real.log ((N : ℝ) + 2))
  have hqLower : 2 * Real.log ((N : ℝ) + 2)
      ≤ (randomLmaxProxyExponent N : ℝ) := by
    change 2 * Real.log ((N : ℝ) + 2)
      ≤ (2 * Nat.ceil (2 * Real.log ((N : ℝ) + 2)) + 8 : ℕ) at *
    push_cast
    nlinarith
  have hq : 0 < (randomLmaxProxyExponent N : ℝ) :=
    Nat.cast_pos.mpr (randomLmaxProxyExponent_pos N)
  have hlogQuot : Real.log (embeddedMinorProxyCount d N) *
      (randomLmaxProxyExponent N : ℝ)⁻¹ ≤ 1 := by
    apply (div_le_one₀ hq).2
    nlinarith [hlogCount, hqLower]
  calc
    (embeddedMinorProxyCount d N) ^ ((randomLmaxProxyExponent N : ℝ)⁻¹)
        = Real.exp (Real.log (embeddedMinorProxyCount d N) *
            (randomLmaxProxyExponent N : ℝ)⁻¹) :=
          Real.rpow_def_of_pos hcountPos _
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hlogQuot

/-- The largest embedded-minor loop, over the original block coordinates. -/
noncomputable def embeddedMinorLoopMax (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) : ℝ :=
  (Finset.univ : Finset (ZMod (d.L N) × ZMod (d.L N))).sup'
    Finset.univ_nonempty fun p => embeddedMinorLoop d N u z S ω p.1 p.2

theorem embeddedMinorLoop_le_max (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) (a b : ZMod (d.L N)) :
    embeddedMinorLoop d N u z S ω a b ≤ embeddedMinorLoopMax d N u z S ω := by
  exact Finset.le_sup' (fun p : ZMod (d.L N) × ZMod (d.L N) =>
    embeddedMinorLoop d N u z S ω p.1 p.2) (Finset.mem_univ (a, b))

theorem embeddedMinorLoopMax_nonneg (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    0 ≤ embeddedMinorLoopMax d N u z S ω := by
  unfold embeddedMinorLoopMax
  exact le_trans (embeddedMinorLoop_nonneg d N u z S ω 0 0)
    (Finset.le_sup' (fun p : ZMod (d.L N) × ZMod (d.L N) =>
      embeddedMinorLoop d N u z S ω p.1 p.2) (Finset.mem_univ (0, 0)))

theorem embeddedMinorProxy_ge_loopMax (d : Dims) (N : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (d.Idx N)) (ω : Ω d) :
    embeddedMinorLoopMax d N u z S ω ≤ embeddedMinorProxy d N u z S ω := by
  unfold embeddedMinorLoopMax
  refine Finset.sup'_le _ _ fun p _ => ?_
  exact embeddedMinorProxy_ge_loop d N u z S ω p.1 p.2

/-- Same-sample P0 comparison: the smooth proxy is between the maximum of the floor and the
embedded-minor loops and `e` times that maximum, eventually uniformly in the minor and sample. -/
theorem embeddedMinorProxy_P0_eventually (d : Dims) :
    ∀ᶠ N : ℕ in atTop, ∀ (u : ℝ) (z : ℂ) (S : Finset (d.Idx N)) (ω : Ω d),
      max ((d.W N : ℝ)⁻¹) (embeddedMinorLoopMax d N u z S ω)
          ≤ embeddedMinorProxy d N u z S ω ∧
      embeddedMinorProxy d N u z S ω ≤ Real.exp 1 *
          max ((d.W N : ℝ)⁻¹) (embeddedMinorLoopMax d N u z S ω) := by
  filter_upwards [embeddedMinorProxyCount_rpow_le_exp_eventually d] with N hcount
  intro u z S ω
  let B := max ((d.W N : ℝ)⁻¹) (embeddedMinorLoopMax d N u z S ω)
  have hW : 0 < (d.W N : ℝ) := Nat.cast_pos.mpr (d.W_pos N)
  have hB : 0 < B := lt_of_lt_of_le (inv_pos.mpr hW) (le_max_left _ _)
  have hfloor : (d.W N : ℝ)⁻¹ ≤ B := le_max_left _ _
  have hloops : ∀ a b : ZMod (d.L N), embeddedMinorLoop d N u z S ω a b ≤ B := by
    intro a b
    exact (embeddedMinorLoop_le_max d N u z S ω a b).trans (le_max_right _ _)
  have hup := embeddedMinorProxy_le_countRoot_mul d N u z S ω hB hfloor hloops
  have hcount' : (embeddedMinorProxyCount d N) ^
      ((randomLmaxProxyExponent N : ℝ)⁻¹) ≤ Real.exp 1 := hcount
  have hupper : embeddedMinorProxy d N u z S ω ≤ Real.exp 1 * B := by
    exact hup.trans (mul_le_mul_of_nonneg_right hcount' hB.le)
  have hlowFloor := embeddedMinorProxy_ge_floor d N u z S ω
  have hlowLoop := embeddedMinorProxy_ge_loopMax d N u z S ω
  constructor
  · exact max_le hlowFloor hlowLoop
  · exact hupper

#print axioms embeddedMinorProxy_pos
#print axioms embeddedMinorProxy_inv_le_W
#print axioms embeddedMinorProxy_splitRows_eq
#print axioms finDepOffRows_rowNormalizedMinorDiag
#print axioms embeddedMinorProxy_P0_eventually

end RBM.Gauss
