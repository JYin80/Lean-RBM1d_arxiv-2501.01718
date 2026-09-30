/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.CondStableFlow
import RBM1D.EnergyN.Gauss.GoodSetFlow

/-!
# Conditional stability bounds along the flow at an `N`-dependent energy

Uniform domination (`UnifDomIcc`) on `[s, t]`, at an `N`-dependent energy `E : ℕ → ℝ`, of the
Green-function entries, their products and row-conditional expectations, the centered diagonal
entries, and the integration-by-parts remainder `ibpRem`, from the uniform local law
`RBM.Gauss.LocalLawUnifIccN` and the good set `goodSetFlow` with high probability
(`RBM1D/EnergyN/Gauss/GoodSetFlow.lean`).

None of these statements fixes an energy-dependent constant: the deterministic controls `Ψ`,
`Ψ²` and `1` carry no fixed `(mE E).im`/`(2-|E|)`-type constant; the only energy-dependent
numbers (`(η_{t_N})⁻¹`, `etaT`-inverses) enter through hypotheses `hEnv`/`hη` that are
themselves `∀ᶠ N`, or through energy-free helpers such as
`RBM.Gauss.norm_green_diag_sub_mE_le_flow` and `RBM.Gauss.norm_green_apply_le_etaT`, which are
per-`N`/per-fixed-`E` and are applied at `E N`. The generic (`E`-free) combinators
(`UnifDomIcc.of_le_left`, `unifDomIcc_of_highProb`, `unifDomIcc_condRow_of_envelope`,
`unifDomIcc_condRow_sub_self`, `unifDomIcc_const`, …) are used unchanged.
-/

namespace RBM.Gauss

open MeasureTheory Filter

open scoped ENNReal

section LocalLawN

variable {d : Dims} {E : ℕ → ℝ} {s t Ψ : ℕ → ℝ}

/-- **`|G_ii - m| ≤ Ψ`** uniformly on `[s, t]`, from the uniform local law. -/
theorem unifDomIcc_green_diag_subN (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω => ‖green (Hflow d N u ω) (zt (E N) u) i i - mE (E N)‖)
      (fun N _ _ _ => Ψ N) := by
  refine UnifDomIcc.of_le_left (ξ := fun N u (i : d.Idx N) ω =>
    ‖green (Hflow d N u ω) (zt (E N) u) i i - (if i = i then mE (E N) else 0)‖)
    (fun N u i ω => by simp) (hll.precomp fun N (i : d.Idx N) => (i, i))

/-- **`|G_ij| ≤ Ψ` for `i ≠ j`** uniformly on `[s, t]`, from the uniform local law. -/
theorem unifDomIcc_green_offdiagN (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω =>
        ‖green (Hflow d N u ω) (zt (E N) u) v.1.1 v.1.2‖)
      (fun N _ _ _ => Ψ N) := by
  refine UnifDomIcc.of_le_left (ξ := fun N u (v : OffPair d.L d.W N) ω =>
    ‖green (Hflow d N u ω) (zt (E N) u) v.1.1 v.1.2
      - (if v.1.1 = v.1.2 then mE (E N) else 0)‖)
    (fun N u v ω => by rw [ite_eq_right v.2, sub_zero])
    (hll.precomp fun N (v : OffPair d.L d.W N) => v.1)

/-- **`|(G_ii - m)(G_jj - m)| ≤ Ψ²`** uniformly on `[s, t]`, from the uniform local law. -/
theorem unifDomIcc_prod_green_diag_subN (hΨ0 : ∀ N, 0 ≤ Ψ N)
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω =>
        ‖(green (Hflow d N u ω) (zt (E N) u) q.1 q.1 - mE (E N))
          * (green (Hflow d N u ω) (zt (E N) u) q.2 q.2 - mE (E N))‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have h1 := (unifDomIcc_green_diag_subN hll).precomp
    fun N (q : d.Idx N × d.Idx N) => q.1
  have h2 := (unifDomIcc_green_diag_subN hll).precomp
    fun N (q : d.Idx N × d.Idx N) => q.2
  refine UnifDomIcc.of_le_left ?_
    (UnifDomIcc.mul' (fun N u q ω => norm_nonneg _) (fun N u q ω => hΨ0 N) h1 h2)
  intro N u q ω
  exact le_of_eq (norm_mul _ _)

end LocalLawN

section RemN

variable {d : Dims} {E : ℕ → ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **The row-`i` conditional expectation `condRow` of `(G_ii - m)(G_jj - m)` is at most
`Ψ²`** uniformly on `[s, t]`, under the envelope `hEnv` and the lower bound `hΨlow`. -/
theorem unifDomIcc_condRow_prod_green_diagN (d : Dims) (hE : ∀ N, |E N| < 2)
    (ht1 : ∀ N, t N < 1) (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω =>
        ‖condRow d N q.1 (fun η => (green (Hflow d N u η) (zt (E N) u) q.1 q.1 - mE (E N))
          * (green (Hflow d N u η) (zt (E N) u) q.2 q.2 - mE (E N))) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hΨΨ0 : ∀ (N : ℕ) (u : ℝ) (q : d.Idx N × d.Idx N) (ω : Ω d), 0 ≤ Ψ N * Ψ N :=
    fun N _ _ _ => mul_nonneg (hΨ0 N) (hΨ0 N)
  refine unifDomIcc_condRow_of_envelope
    (X := fun N u (q : d.Idx N × d.Idx N) ω =>
      (green (Hflow d N u ω) (zt (E N) u) q.1 q.1 - mE (E N))
        * (green (Hflow d N u ω) (zt (E N) u) q.2 q.2 - mE (E N)))
    (k := fun N _ (q : d.Idx N × d.Idx N) => q.1)
    (Env := fun N => ((etaT (E N) (t N))⁻¹ + 1) ^ 2)
    (fun N u q => ((measurable_green_apply d N u (zt (E N) u) q.1 q.1).sub
      measurable_const).mul ((measurable_green_apply d N u (zt (E N) u) q.2 q.2).sub
        measurable_const))
    (fun N u q => measurable_const) hΨΨ0 hΨΨ0 hKenv hB ?_ hEnv
    (fun N u q ω => integrable_const _)
    (unifDomIcc_const (fun N => mul_nonneg (hΨ0 N) (hΨ0 N)) hΨlow) ?_
    (unifDomIcc_prod_green_diag_subN hΨ0 hll)
  · intro N u hu q ω
    rw [norm_mul, sq]
    have h1 := norm_green_diag_sub_mE_le_flow (s := s) (hE N) (ht1 N) hu q.1 ω
    have h2 := norm_green_diag_sub_mE_le_flow (s := s) (hE N) (ht1 N) hu q.2 ω
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  · simp only [condRowReal_const]
    exact UnifDomIcc.refl hΨΨ0

end RemN

section ReplN

variable {d : Dims} {E : ℕ → ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`|greenDiagCentered_j - greenMinorDiagCentered^{(i)}_j| ≤ Ψ²` for `i ≠ j`**, uniformly on
`[s, t]`, with the good set `hΩ`. -/
theorem unifDomIcc_greenDiagCentered_sub_minorN (d : Dims) (hE : ∀ N, |E N| < 2)
    (ht1 : ∀ N, t N < 1) (hΨ0 : ∀ N, 0 ≤ Ψ N) (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω =>
        ‖greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2 ω
          - greenMinorDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.1
            ⟨v.1.2, Ne.symm v.2⟩ ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hswap := (unifDomIcc_green_offdiagN hll).precomp
    fun N (v : OffPair d.L d.W N) => (⟨(v.1.2, v.1.1), Ne.symm v.2⟩ : OffPair d.L d.W N)
  have hprod := UnifDomIcc.mul' (fun N u (v : OffPair d.L d.W N) ω => norm_nonneg _)
    (fun N u (v : OffPair d.L d.W N) ω => hΨ0 N) hswap (unifDomIcc_green_offdiagN hll)
  refine UnifDomIcc.of_le_left_on hΩ ?_
    (UnifDomIcc.const_mul_left (by norm_num : (0 : ℝ) ≤ 2)
      (fun N u (v : OffPair d.L d.W N) ω => mul_nonneg (hΨ0 N) (hΨ0 N)) hprod)
  filter_upwards [hδ1] with N hδN ω hω u hu v
  exact norm_greenDiagCentered_sub_minor_le d N (hE N) (lt_of_le_of_lt hu.2 (ht1 N)) hδN
    (hω u hu) v

end ReplN

section IbpRemN

variable {d : Dims} {E : ℕ → ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`|condRow_i (greenDiagCentered_j) - greenDiagCentered_j| ≤ Ψ²` for `i ≠ j`**, uniformly on
`[s, t]`. -/
theorem unifDomIcc_condRow_greenDiagCentered_sub_selfN (d : Dims) (hE : ∀ N, |E N| < 2)
    (ht1 : ∀ N, t N < 1) (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω =>
        ‖condRow d N v.1.1 (greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2) ω
          - greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2 ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hΨΨ0 : ∀ (N : ℕ) (u : ℝ) (v : OffPair d.L d.W N) (ω : Ω d), 0 ≤ Ψ N * Ψ N :=
    fun N _ _ _ => mul_nonneg (hΨ0 N) (hΨ0 N)
  refine unifDomIcc_condRow_sub_self
    (X := fun N u (v : OffPair d.L d.W N) =>
      greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2)
    (X' := fun N u (v : OffPair d.L d.W N) =>
      greenMinorDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.1 ⟨v.1.2, Ne.symm v.2⟩)
    (k := fun N _ (v : OffPair d.L d.W N) => v.1.1)
    (Env := fun N => ((etaT (E N) (t N))⁻¹ + 1) ^ 2)
    (fun N u v => measurable_greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2)
    (fun N u v => measurable_greenMinorDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.1 _)
    (fun N u v => measurable_const) hΨΨ0 hΨΨ0 hKenv hB ?_ hEnv
    (fun N u v ω => integrable_const _)
    (unifDomIcc_const (fun N => mul_nonneg (hΨ0 N) (hΨ0 N)) hΨlow) ?_
    (UnifDomIcc.refl hΨΨ0)
    (fun N u v => (finDepOffRow_greenMinorMat_apply d N u (zt (E N) u) v.1.1
      ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩).comp fun z => z - mE (E N))
    ?_ (unifDomIcc_greenDiagCentered_sub_minorN d hE ht1 hΨ0 hδ1 hΩ hll)
  · intro N u hu v ω
    have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
    have hηu : 0 < etaT (E N) u := etaT_pos_of_lt_one (hE N) hu1
    have h1 := norm_green_apply_le_etaT (hE N) hu1 u v.1.2 v.1.2 ω
    have h2 := norm_greenMinorMat_apply_le_etaT (d := d) (N := N) (hE N) hu1 u
      (κ := v.1.1) ⟨v.1.2, Ne.symm v.2⟩ ⟨v.1.2, Ne.symm v.2⟩ ω
    have hmono := inv_etaT_le_inv_etaT (hE N) hu.2 (ht1 N)
    have hη0 : (0 : ℝ) ≤ (etaT (E N) (t N))⁻¹ := by
      have := etaT_pos_of_lt_one (hE N) (ht1 N); positivity
    have hstep : ‖greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2 ω
        - greenMinorDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.1
          ⟨v.1.2, Ne.symm v.2⟩ ω‖
        ≤ 2 * (etaT (E N) (t N))⁻¹ := by
      have he : greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2 ω
          - greenMinorDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.1
            ⟨v.1.2, Ne.symm v.2⟩ ω
          = green (Hflow d N u ω) (zt (E N) u) v.1.2 v.1.2
            - greenMinorMat d N u (zt (E N) u) v.1.1 ω ⟨v.1.2, Ne.symm v.2⟩
              ⟨v.1.2, Ne.symm v.2⟩ := by
        simp only [greenDiagCentered, greenMinorDiagCentered]; ring
      rw [he]
      refine le_trans (norm_sub_le _ _) ?_
      linarith
    refine hstep.trans ?_
    nlinarith
  · simp only [condRowReal_const]
    exact UnifDomIcc.refl hΨΨ0
  · intro N u hu v
    exact rowIntegrable_of_measurable_of_bound
      (measurable_greenDiagCentered d N u (zt (E N) u) (mE (E N)) v.1.2)
      (norm_greenDiagCentered_le_env (hE N) (lt_of_le_of_lt hu.2 (ht1 N)) u v.1.2)

/-- **The integration-by-parts remainder `ibpRem` at `(i, j)`, `i ≠ j`, is at most `Ψ²`**,
uniformly on `[s, t]`. -/
theorem unifDomIcc_ibpRem_offdiagN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (v : OffPair d.L d.W N) ω => ‖ibpRem d N (E N) u (v.1.1, v.1.2) ω‖)
      (fun N _ _ _ => Ψ N * Ψ N) := by
  have hΨΨ0 : ∀ (N : ℕ) (u : ℝ) (v : OffPair d.L d.W N) (ω : Ω d), 0 ≤ Ψ N * Ψ N :=
    fun N _ _ _ => mul_nonneg (hΨ0 N) (hΨ0 N)
  have hp := (unifDomIcc_condRow_prod_green_diagN d hE ht1 hΨ0 hKenv hB hEnv hΨlow hll).precomp
    fun N (v : OffPair d.L d.W N) => (v.1.1, v.1.2)
  have hm := unifDomIcc_condRow_greenDiagCentered_sub_selfN d hE ht1 hΨ0 hKenv hB hEnv hΨlow
    hδ1 hΩ hll
  refine UnifDomIcc.of_le_left_icc ?_ (UnifDomIcc.add' hΨΨ0 hp hm)
  intro N u hu v ω
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  rw [ibpRem_eq_add (gaussIBP d) (hE N) hu1 v.1.1 v.1.2 ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE (hE N).le, one_mul]
  exact le_rfl

end IbpRemN

section DiagN

variable {d : Dims} {E : ℕ → ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`|greenDiagCentered| ≤ 1`** uniformly on `[s, t]`, with the good set `hΩ`. -/
theorem unifDomIcc_greenDiagCentered_oneN (d : Dims) {V : ℕ → Type*}
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (kk : ∀ N, V N → d.Idx N) :
    UnifDomIcc (P d) s t
      (fun N u (a : V N) ω => ‖greenDiagCentered d N u (zt (E N) u) (mE (E N)) (kk N a) ω‖)
      (fun _ _ _ _ => (1 : ℝ)) := by
  refine unifDomIcc_of_highProb hΩ fun τ hτ => ?_
  filter_upwards [hδ1, eventually_le_rpow 1 hτ] with N hδN h1N ω hω u hu a
  have h := (hω u hu).norm_diag_sub_le (kk N a)
  simp only [greenDiagCentered]
  rw [mul_one]
  linarith

/-- **`|condExpDiag_i| ≤ 1`** uniformly on `[s, t]`, with the good set `hΩ` and the envelope
`hEnv`. -/
theorem unifDomIcc_condExpDiag_oneN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N)) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω => ‖condExpDiag d N u (zt (E N) u) (mE (E N)) i ω‖)
      (fun _ _ _ _ => (1 : ℝ)) := by
  have hone : ∀ (N : ℕ) (u : ℝ) (i : d.Idx N) (ω : Ω d), (0 : ℝ) ≤ 1 := fun _ _ _ _ => zero_le_one
  have hlow : UnifDomIcc (P d) s t
      (fun N _ (_ : d.Idx N) (_ : Ω d) => (N : ℝ) ^ (-B)) (fun _ _ _ _ => (1 : ℝ)) := by
    refine unifDomIcc_const (fun _ => zero_le_one) ?_
    filter_upwards [eventually_ge_atTop 1] with N hN1
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  refine unifDomIcc_condRow_of_envelope
    (X := fun N u (i : d.Idx N) => greenDiagCentered d N u (zt (E N) u) (mE (E N)) i)
    (k := fun N _ (i : d.Idx N) => i)
    (Env := fun N => ((etaT (E N) (t N))⁻¹ + 1) ^ 2)
    (fun N u i => measurable_greenDiagCentered d N u (zt (E N) u) (mE (E N)) i)
    (fun N u i => measurable_const) hone hone hKenv hB ?_ hEnv
    (fun N u i ω => integrable_const _) hlow ?_
    (unifDomIcc_greenDiagCentered_oneN d hδ1 hΩ fun N (i : d.Idx N) => i)
  · intro N u hu i ω
    have h1 := norm_green_diag_sub_mE_le_flow (s := s) (hE N) (ht1 N) hu i ω
    have hη0 : (0 : ℝ) ≤ (etaT (E N) (t N))⁻¹ :=
      (inv_pos.2 (etaT_pos_of_lt_one (hE N) (ht1 N))).le
    simp only [greenDiagCentered]
    nlinarith
  · simp only [condRowReal_const]
    exact UnifDomIcc.refl hone

end DiagN

section RemAllN

variable {d : Dims} {E : ℕ → ℝ} {s t Ψ δ : ℕ → ℝ} {Kenv B : ℝ}

/-- **`|ibpRem (i, i)| ≤ 1`** uniformly on `[s, t]`. -/
theorem unifDomIcc_ibpRem_diagN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω => ‖ibpRem d N (E N) u (i, i) ω‖)
      (fun _ _ _ _ => (1 : ℝ)) := by
  have hone : ∀ (N : ℕ) (u : ℝ) (i : d.Idx N) (ω : Ω d), (0 : ℝ) ≤ 1 := fun _ _ _ _ => zero_le_one
  have hP1 : UnifDomIcc (P d) s t
      (fun N u (i : d.Idx N) ω =>
        ‖condRow d N i (fun η => (green (Hflow d N u η) (zt (E N) u) i i - mE (E N))
          * (green (Hflow d N u η) (zt (E N) u) i i - mE (E N))) ω‖) (fun _ _ _ _ => (1 : ℝ)) :=
    ((unifDomIcc_condRow_prod_green_diagN d hE ht1 hΨ0 hKenv hB hEnv hΨlow hll).precomp
      fun N (i : d.Idx N) => (i, i)).trans
      (unifDomIcc_const (fun _ => zero_le_one) hΨ1)
  have hP2 := unifDomIcc_condExpDiag_oneN (s := s) d hE ht1 hKenv hB hEnv hδ1 hΩ
  have hP3 := unifDomIcc_greenDiagCentered_oneN (s := s) d hδ1 hΩ fun N (i : d.Idx N) => i
  refine UnifDomIcc.of_le_left_icc ?_
    (UnifDomIcc.add' hone hP1 (UnifDomIcc.add' hone hP2 hP3))
  intro N u hu i ω
  have hu1 : u < 1 := lt_of_le_of_lt hu.2 (ht1 N)
  rw [ibpRem_eq_add (gaussIBP d) (hE N) hu1 i i ω]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, norm_mE (hE N).le, one_mul]
  refine add_le_add le_rfl ?_
  have hrw : condRow d N i (greenDiagCentered d N u (zt (E N) u) (mE (E N)) i) ω
      - (green (Hflow d N u ω) (zt (E N) u) i i - mE (E N))
      = condExpDiag d N u (zt (E N) u) (mE (E N)) i ω
        - greenDiagCentered d N u (zt (E N) u) (mE (E N)) i ω := rfl
  rw [hrw]
  exact norm_sub_le _ _

/-- **`|ibpRem (i, j)|` is at most `1` on the diagonal and `Ψ²` off it**, uniformly on
`[s, t]`. -/
theorem unifDomIcc_ibpRemN (d : Dims) (hE : ∀ N, |E N| < 2) (ht1 : ∀ N, t N < 1)
    (hΨ0 : ∀ N, 0 ≤ Ψ N) (hKenv : 0 ≤ Kenv) (hB : 0 ≤ B)
    (hEnv : ∀ᶠ N : ℕ in atTop, ((etaT (E N) (t N))⁻¹ + 1) ^ 2 ≤ (N : ℝ) ^ Kenv)
    (hΨlow : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-B) ≤ Ψ N * Ψ N)
    (hΨ1 : ∀ᶠ N : ℕ in atTop, Ψ N * Ψ N ≤ 1)
    (hδ1 : ∀ᶠ N : ℕ in atTop, δ N ≤ 1 / 2)
    (hΩ : HighProb (P d) (fun N => goodSetFlow d (E N) s t δ N))
    (hll : LocalLawUnifIccN d E s t Ψ) :
    UnifDomIcc (P d) s t
      (fun N u (q : d.Idx N × d.Idx N) ω => ‖ibpRem d N (E N) u q ω‖)
      (fun N _ (q : d.Idx N × d.Idx N) _ => if q.1 = q.2 then (1 : ℝ) else Ψ N * Ψ N) := by
  have hoff := unifDomIcc_ibpRem_offdiagN d hE ht1 hΨ0 hKenv hB hEnv hΨlow hδ1 hΩ hll
  have hdiag := unifDomIcc_ibpRem_diagN d hE ht1 hΨ0 hKenv hB hEnv hΨlow hΨ1 hδ1 hΩ hll
  intro τ hτ D hD
  filter_upwards [hoff τ hτ D hD, hdiag τ hτ D hD] with N h1 h2 u hu q
  obtain ⟨i, j⟩ := q
  by_cases hq : i = j
  · subst hq
    simpa using h2 u hu i
  · have := h1 u hu ⟨(i, j), hq⟩
    simpa [hq] using this

end RemAllN

end RBM.Gauss

section Compat

open RBM RBM.Gauss MeasureTheory Filter

open scoped ENNReal

end Compat
