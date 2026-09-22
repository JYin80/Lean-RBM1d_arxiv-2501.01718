/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.APrimeNearRem
import RBM1D.Gauss.APrimeJG
import RBM1D.Gauss.APrimeQVBridge

/-!
# T334: uncut quadratic variation from actual block Green witnesses

The length-four and length-six estimates are explicit pointwise Step-1 event
inputs. The near six-loop residual is repaired before endpoint propagation.
-/

namespace RBM.APrimeFullQV

open RBM.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- Pointwise length-six and length-four Step-1 source event. `ellSource` can
encode the explicit loss in the length-six estimate. -/
structure SourceEvent (X : Sample B) (E : ℝ) (N : ℕ) (u : ℝ) (ω : Ω)
    (ellSource Smax : ℝ) : Prop where
  six : ∀ c b, EEDef.eeL6 X E N u ω Step2.sigPM (Fin.append c c) b ≤
    (B.ell N u / ellSource) ^ 5 *
      ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹) ^ 2 *
      ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹
  four : ∀ (s : Bool) (x y y' : ZMod (B.L N)),
    (gloop (B.L N) (B.W N) (X.H N u ω) (zt E u)
      ⟨[s, !s, s, !s], [x, y, x, y']⟩).re ≤ Smax

/-- The actual Step-1 length-four and length-six loop bounds imply the
pointwise QV source event. The factor two in the six-loop bridge is explicit. -/
theorem sourceEvent_of_step1 (X : Sample B) (E : ℝ) (N : ℕ)
    (u : ℝ) (ω : Ω) {ellSource C4 C6 : ℝ}
    (h4 : ∀ p : LoopData (B.L N) 4, ‖X.Lval E N u ω p.idx‖ ≤ C4)
    (h6 : ∀ p : LoopData (B.L N) 6, ‖X.Lval E N u ω p.idx‖ ≤ C6)
    (h6level : 2 * C6 ≤ (B.ell N u / ellSource) ^ 5 *
      ((((B.W N : ℝ) * B.ell N u * etaT E u) ^ 2)⁻¹) ^ 2 *
      ((B.W N : ℝ) * B.ell N u * etaT E u)⁻¹) :
    SourceEvent X E N u ω ellSource C4 := by
  constructor
  · intro c b
    exact (EarlyQVRateEv.eeL6_two_le X E N u ω Step2.sigPM
      (Fin.append c c) b h6).trans h6level
  · intro s x y y'
    exact (EarlyQVRateEv.re_gloop_four_le_sMax X E N u ω s x y y').trans
      (EarlyQVRateEv.sMax_le X E N u ω h4)

/-- Actual raw diagonal QV. The right side contains the near term and both
far powers in `diagFarRate`; the remainder carries the output spatial tail. -/
theorem early_raw_full (X : Sample B) {E D u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) (ω : Ω)
    (a : LoopArg (B.L N) 2) {ellSource Smax : ℝ}
    (hsource : SourceEvent X E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (B.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (B.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    (hN : 1 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u)
    (hAN : (B.W N : ℝ) * B.ell N u * etaT E u ≤ N)
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hJcap : APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D ≤ N) :
    Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a) (X.H N u ω) ≤
      APrimeQVEndpoint.diagShape' B N (B.ell N u) ellSource (etaT E u) D
        (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D) Smax
        (EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D
          (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D)) a ∧
    EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D
      (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D) ≤ (B.W N : ℝ)⁻¹ := by
  let J := APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D
  let ε := EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D J
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hℓu : 1 ≤ B.ell N u := by
    simpa only [Band.ell] using one_le_ellHat_of_nonneg hL hu0 hu1
  have hη : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hJ : 1 ≤ J := APrimeJG.one_le_jG X E N u ω hW0
  have hε : 0 ≤ ε := by unfold ε EEDef.nearEpsilon; positivity
  have hgm : ∀ (s : Bool) (x y : ZMod (B.L N))
      (p q : ZMod (B.L N) × Fin (B.W N)), p.1 = x → q.1 = y →
      ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ APrimeJG.gmBlk X E N u ω x y := by
    intro s x y p q hp hq
    rcases p with ⟨px, pi⟩
    rcases q with ⟨qx, qi⟩
    simp only at hp hq
    subst px
    subst qx
    exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω s x y pi qi
  have h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      APrimeJG.gsqBlk X E N u ω x y ≤
        J * Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
    intro x y hxy
    simpa only [J, Step2.tT] using
      APrimeJG.gsqBlk_le_jG_mul_tailT X E N u ω hW0 x y hxy
  have hnear := EEDef.eeL6_near_remainder X E N u ω Step2.sigPM
    (by linarith : 0 < B.ell N u) hη hJ hlog4
    (APrimeJG.gmBlk_nonneg X E N u ω) hgm
    (APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω)
    (APrimeJG.gmBlk_row_le_gsqBlk X E N u ω)
    (by simpa only [Step2.tT] using h42)
    (APrimeJG.gsqBlk_le_inv_etaT_sq X hE N hu1 ω)
  have hεsmall : ε ≤ (B.W N : ℝ)⁻¹ := by
    apply EEDef.nearEpsilon_le_inv hW
      (by exact_mod_cast (show 0 < B.L N by have := B.three_le_L N; omega) :
        (0 : ℝ) < B.L N)
      (by linarith : 0 < B.ell N u) hη hN (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ J) (by linarith : 2 * (1 : ℝ) + 14 ≤ D)
      heta hA hAN hWL hNW (by simpa [J] using hJcap) hlog4 hlog
  have hraw := EarlyQVRate.quadVar_lkFun_le_ee_sym' X hE hu0 hu1 ω
    Step2.sigPM a hℓu hell hη hJ hε
    (APrimeJG.gmBlk_nonneg X E N u ω) hgm
    (APrimeJG.gsqBlk_nonneg X E N u ω)
    (APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω)
    (APrimeJG.gmBlk_row_le_gsqBlk X E N u ω)
    hsource.four (hsource.six a) (hnear a) h42
  exact ⟨by simpa only [J, ε] using hraw, by simpa only [J, ε] using hεsmall⟩

/-- Exact early-QV normalization after cancellation of its own spatial tail.
The far coefficient still includes both `J²` and `J³` and the leakage term. -/
theorem early_normalized_full (X : Sample B) {E D u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) (ω : Ω)
    (a : LoopArg (B.L N) 2) {ellSource Smax : ℝ}
    (hsource : SourceEvent X E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (B.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (B.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    (hN : 1 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u)
    (hAN : (B.W N : ℝ) * B.ell N u * etaT E u ≤ N)
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hJcap : APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D ≤ N)
    {x Θ : ℝ} (hx : 0 < x) (hΘ : 0 < Θ) :
    Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a) (X.H N u ω) /
        (Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) ^ 2 * x ^ 8 * Θ ^ 2) ≤
      (APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT E u) +
        2 * (B.W N : ℝ)⁻¹ +
        APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D
          (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D) Smax) /
        (x ^ 8 * Θ ^ 2) := by
  let J := APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D
  let ε := EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D J
  let T := Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1))
  let An := APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT E u)
  let Af := APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D J Smax
  let χ : ℝ := if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
      4 * ellStar (B.W N : ℝ) (B.ell N u) then 1 else 0
  have hraw := early_raw_full X hE hu0 hu1 N ω a hsource hell hD hW
    hlog4 hlog hN heta hA hAN hWL hNW hJcap
  have hε : ε ≤ (B.W N : ℝ)⁻¹ := hraw.2
  have hη : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hℓ : 0 < B.ell N u := by
    have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
    have h := one_le_ellHat_of_nonneg hL hu0 hu1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) (u : ℂ) by linarith)
  have hAn : 0 ≤ An := by
    dsimp [An, APrimeQVEndpoint.diagNearRate]
    have hc := Lemma57.cNear2_nonneg
      (show 1 ≤ (B.W N : ℝ) from
        (Real.one_le_exp (by norm_num)).trans hW) hℓ
    positivity
  have hε0 : 0 ≤ ε := by dsimp [ε, EEDef.nearEpsilon]; positivity
  have hχ : χ ≤ 1 := by dsimp [χ]; split_ifs <;> norm_num
  have hnear : (An + 2 * ε) * χ ≤ An + 2 * (B.W N : ℝ)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left hχ (by linarith : 0 ≤ An + 2 * ε)
    nlinarith [h1, hε]
  have hT : 0 < T := by
    dsimp [T, Step2.tT]
    exact tailT_pos (by exact_mod_cast B.W_pos N) _
  have hshape : APrimeQVEndpoint.diagShape' B N (B.ell N u) ellSource
      (etaT E u) D J Smax ε a = ((An + 2 * ε) * χ + Af) * T ^ 2 := by
    dsimp [APrimeQVEndpoint.diagShape', An, Af, χ, T, Step2.tT]
    ring
  have hmain : Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a) (X.H N u ω) ≤
      (An + 2 * (B.W N : ℝ)⁻¹ + Af) * T ^ 2 := by
    calc
      _ ≤ APrimeQVEndpoint.diagShape' B N (B.ell N u) ellSource
          (etaT E u) D J Smax ε a := hraw.1
      _ = ((An + 2 * ε) * χ + Af) * T ^ 2 := hshape
      _ ≤ (An + 2 * (B.W N : ℝ)⁻¹ + Af) * T ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg T)
  have hden : 0 < T ^ 2 * x ^ 8 * Θ ^ 2 := by positivity
  have hdiv := (div_le_div_of_nonneg_right hmain hden.le)
  have hsimp : ((An + 2 * (B.W N : ℝ)⁻¹ + Af) * T ^ 2) /
      (T ^ 2 * x ^ 8 * Θ ^ 2) =
      (An + 2 * (B.W N : ℝ)⁻¹ + Af) / (x ^ 8 * Θ ^ 2) := by
    field_simp [ne_of_gt hT, ne_of_gt hx, ne_of_gt hΘ]
  simpa only [T, An, Af, J, hsimp] using hdiv

namespace ExponentRows

/-! The variables `t⁴=x_j`, `b²=A`, `p=N^δ`, and `q=N^τ` make
the three early rows integral-power identities. -/

/-- Near row: `x_j^(-9/2)` after the `x_j^8 Θ²` division. -/
theorem near {η t p r : ℝ} (hη : 0 < η) (ht : 0 < t) (hp : 0 < p)
    (hr0 : 0 ≤ r) (hr : r ≤ t ^ 2) :
    η⁻¹ * t ^ 4 * r ^ 5 / (t ^ 32 * p ^ 4) ≤
      η⁻¹ * (p⁻¹) ^ 4 * (t⁻¹) ^ 18 := by
  have hnum : η⁻¹ * t ^ 4 * r ^ 5 ≤ η⁻¹ * t ^ 4 * (t ^ 2) ^ 5 := by
    gcongr
  have hden : 0 ≤ t ^ 32 * p ^ 4 := by positivity
  calc
    _ ≤ η⁻¹ * t ^ 4 * (t ^ 2) ^ 5 / (t ^ 32 * p ^ 4) :=
      div_le_div_of_nonneg_right hnum hden
    _ = η⁻¹ * (p⁻¹) ^ 4 * (t⁻¹) ^ 18 := by
      field_simp

/-- Quadratic far row: `N^(2τ) A^(-1/2) x_j^(7/4)`. -/
theorem far_quadratic {η t b p q KJ KS J S : ℝ}
    (hη : 0 < η) (ht : 0 < t) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) (hKJ : 0 ≤ KJ) (hKS : 0 ≤ KS)
    (hJ0 : 0 ≤ J) (hS0 : 0 ≤ S)
    (hJ : J ≤ KJ * p ^ 2 * q * t ^ 16)
    (hS : S ≤ KS * t ^ 3 * (b⁻¹) ^ 3) :
    η⁻¹ * t ^ 4 * (J ^ 2 * b ^ 2 * S) / (t ^ 32 * p ^ 4) ≤
      η⁻¹ * KJ ^ 2 * KS * q ^ 2 * b⁻¹ * t ^ 7 := by
  have hcore : J ^ 2 * b ^ 2 * S ≤
      (KJ * p ^ 2 * q * t ^ 16) ^ 2 * b ^ 2 *
        (KS * t ^ 3 * (b⁻¹) ^ 3) := by
    gcongr
  have hnum : η⁻¹ * t ^ 4 * (J ^ 2 * b ^ 2 * S) ≤
      η⁻¹ * t ^ 4 *
        ((KJ * p ^ 2 * q * t ^ 16) ^ 2 * b ^ 2 *
          (KS * t ^ 3 * (b⁻¹) ^ 3)) := by
    gcongr
  have hden : 0 ≤ t ^ 32 * p ^ 4 := by positivity
  calc
    _ ≤ η⁻¹ * t ^ 4 *
          ((KJ * p ^ 2 * q * t ^ 16) ^ 2 * b ^ 2 *
            (KS * t ^ 3 * (b⁻¹) ^ 3)) /
          (t ^ 32 * p ^ 4) := div_le_div_of_nonneg_right hnum hden
    _ = η⁻¹ * KJ ^ 2 * KS * q ^ 2 * b⁻¹ * t ^ 7 := by
      field_simp

/-- Cubic far row: `N^(2δ+3τ) A^(-1) x_j^5`. -/
theorem far_cubic {η t b p q KJ J : ℝ}
    (hη : 0 < η) (ht : 0 < t) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) (hKJ : 0 ≤ KJ)
    (hJ0 : 0 ≤ J) (hJ : J ≤ KJ * p ^ 2 * q * t ^ 16) :
    η⁻¹ * t ^ 4 * (J ^ 3 * (b⁻¹) ^ 2) / (t ^ 32 * p ^ 4) ≤
      η⁻¹ * KJ ^ 3 * p ^ 2 * q ^ 3 * (b⁻¹) ^ 2 * t ^ 20 := by
  have hnum : η⁻¹ * t ^ 4 * (J ^ 3 * (b⁻¹) ^ 2) ≤
      η⁻¹ * t ^ 4 *
        ((KJ * p ^ 2 * q * t ^ 16) ^ 3 * (b⁻¹) ^ 2) := by
    gcongr
  have hden : 0 ≤ t ^ 32 * p ^ 4 := by positivity
  calc
    _ ≤ η⁻¹ * t ^ 4 *
          ((KJ * p ^ 2 * q * t ^ 16) ^ 3 * (b⁻¹) ^ 2) /
          (t ^ 32 * p ^ 4) := div_le_div_of_nonneg_right hnum hden
    _ = η⁻¹ * KJ ^ 3 * p ^ 2 * q ^ 3 * (b⁻¹) ^ 2 * t ^ 20 := by
      field_simp

/-- All three T331 §4 early exponent rows, with the exact Step-1 length-four
square-root level and the calibrated block-support bound as premises. -/
theorem full {η t b p q KJ KS r J S : ℝ}
    (hη : 0 < η) (ht : 0 < t) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) (hKJ : 0 ≤ KJ) (hKS : 0 ≤ KS)
    (hr0 : 0 ≤ r) (hJ0 : 0 ≤ J) (hS0 : 0 ≤ S)
    (hr : r ≤ t ^ 2)
    (hJ : J ≤ KJ * p ^ 2 * q * t ^ 16)
    (hS : S ≤ KS * t ^ 3 * (b⁻¹) ^ 3) :
    η⁻¹ * t ^ 4 * (r ^ 5 + J ^ 2 * b ^ 2 * S +
      J ^ 3 * (b⁻¹) ^ 2) / (t ^ 32 * p ^ 4) ≤
    η⁻¹ * ((p⁻¹) ^ 4 * (t⁻¹) ^ 18 +
      KJ ^ 2 * KS * q ^ 2 * b⁻¹ * t ^ 7 +
      KJ ^ 3 * p ^ 2 * q ^ 3 * (b⁻¹) ^ 2 * t ^ 20) := by
  have hn := near hη ht hp hr0 hr
  have hqv := far_quadratic hη ht hb hp hq hKJ hKS hJ0 hS0 hJ hS
  have hc := far_cubic hη ht hb hp hq hKJ hJ0 hJ
  have hsum := add_le_add (add_le_add hn hqv) hc
  convert hsum using 1 <;> ring

/-- The integral-power rows above are precisely the three fractional powers
in T331 §4 when `x=t⁴` and `A=b²`. -/
theorem power_translation {t b : ℝ} (ht : 0 < t) (hb : 0 < b) :
    (t ^ 4) ^ (-(9 / 2 : ℝ)) = (t⁻¹) ^ 18 ∧
    (t ^ 4) ^ ((7 / 4 : ℝ)) = t ^ 7 ∧
    (t ^ 4) ^ (5 : ℝ) = t ^ 20 ∧
    (b ^ 2) ^ (-(1 / 2 : ℝ)) = b⁻¹ ∧
    (b ^ 2) ^ (-1 : ℝ) = (b⁻¹) ^ 2 := by
  constructor
  · calc
      (t ^ 4) ^ (-(9 / 2 : ℝ)) = t ^ ((4 : ℝ) * (-(9 / 2 : ℝ))) := by
        rw [show t ^ 4 = t ^ (4 : ℝ) by norm_cast]
        exact (Real.rpow_mul ht.le 4 (-(9 / 2 : ℝ))).symm
      _ = (t⁻¹) ^ 18 := by
        have h := Real.rpow_mul ht.le (-1 : ℝ) (18 : ℝ)
        norm_num at h ⊢
  constructor
  · calc
      (t ^ 4) ^ ((7 / 4 : ℝ)) = t ^ ((4 : ℝ) * (7 / 4 : ℝ)) := by
        rw [show t ^ 4 = t ^ (4 : ℝ) by norm_cast]
        exact (Real.rpow_mul ht.le 4 (7 / 4 : ℝ)).symm
      _ = t ^ 7 := by norm_num
  constructor
  · norm_num
    ring
  constructor
  · calc
      (b ^ 2) ^ (-(1 / 2 : ℝ)) = b ^ ((2 : ℝ) * (-(1 / 2 : ℝ))) := by
        rw [show b ^ 2 = b ^ (2 : ℝ) by norm_cast]
        exact (Real.rpow_mul hb.le 2 (-(1 / 2 : ℝ))).symm
      _ = b⁻¹ := by norm_num [Real.rpow_neg_one]
  · calc
      (b ^ 2) ^ (-1 : ℝ) = b ^ ((2 : ℝ) * (-1 : ℝ)) := by
        rw [show b ^ 2 = b ^ (2 : ℝ) by norm_cast]
        exact (Real.rpow_mul hb.le 2 (-1 : ℝ)).symm
      _ = (b⁻¹) ^ 2 := by
        norm_num [Real.rpow_neg_one]

/-- Concrete logarithmic-loss and floor conditions turn the exact T280g
coefficient into the three monomials used in `full`. -/
theorem coefficient_bound {W L ℓu ℓs ηu D J S C : ℝ}
    (hW : 1 ≤ W) (hℓu : 0 < ℓu) (hℓs : 0 < ℓs)
    (hη : 0 < ηu) (hJ : 1 ≤ J) (hC : 1 ≤ C)
    (hNearLoss : Lemma57.cNear2 W ℓu ≤ C)
    (hFarLoss : Lemma57.cFar2 W ℓu ≤ C)
    (hLeak : W * L * W ^ (-D) ≤ ηu⁻¹ * (W * ℓu * ηu)⁻¹)
    (hFloor : W⁻¹ ≤ ηu⁻¹ * (ℓu / ℓs) ^ 5) :
    2 * ηu⁻¹ * Lemma57.cNear2 W ℓu * (ℓu / ℓs) ^ 5 +
      2 * W⁻¹ +
      (2 * ηu⁻¹ *
        (Lemma57.cFar2 W ℓu *
          ((2 * J) ^ 2 * ((W * ℓu * ηu) * (2 * √S))) +
          72 * (2 * J) ^ 3 * (W * ℓu * ηu)⁻¹) +
        4 * W * L * W ^ (-D) * (2 * J) ^ 3) ≤
      2048 * C * ηu⁻¹ *
        ((ℓu / ℓs) ^ 5 + J ^ 2 * (W * ℓu * ηu) * √S +
          J ^ 3 * (W * ℓu * ηu)⁻¹) := by
  let A := W * ℓu * ηu
  let r := ℓu / ℓs
  let R := ηu⁻¹ * r ^ 5
  let Q := ηu⁻¹ * J ^ 2 * A * √S
  let V := ηu⁻¹ * J ^ 3 * A⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hcn : Lemma57.cNear2 W ℓu * R ≤ C * R :=
    mul_le_mul_of_nonneg_right hNearLoss hR
  have hcf : Lemma57.cFar2 W ℓu * Q ≤ C * Q :=
    mul_le_mul_of_nonneg_right hFarLoss hQ
  have hleak : (W * L * W ^ (-D)) * (J ^ 3) ≤ V := by
    have hh := mul_le_mul_of_nonneg_right hLeak
      (pow_nonneg (show 0 ≤ J by linarith) 3)
    dsimp [V, A] at hh ⊢
    nlinarith [hh]
  have hCR : R ≤ C * R := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hR]
  have hCQ : Q ≤ C * Q := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hQ]
  have hCV : V ≤ C * V := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hV]
  dsimp [R, Q, V, A, r] at *
  nlinarith [hcn, hcf, hleak, hCR, hCQ, hCV]

/-- The cubic spatial leakage is paid by the ordinary dimension and scale
inequalities once `D≥4`; T334 uses the stronger fixed `D≥60`. -/
theorem leak_paid_by_dims {W L N A η D : ℝ}
    (hW : 1 ≤ W) (hN : 1 ≤ N) (hA0 : 0 < A) (hη0 : 0 < η)
    (hWL : W * L ≤ N) (hAN : A ≤ N) (hNW : N ≤ W ^ 2)
    (hη1 : η ≤ 1) (hD : 4 ≤ D) :
    W * L * W ^ (-D) ≤ η⁻¹ * A⁻¹ := by
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hWD0 : 0 < W ^ D := Real.rpow_pos_of_pos hW0 D
  have hηA : 0 < η * A := mul_pos hη0 hA0
  have hNW2 : N ^ 2 ≤ W ^ 4 := by
    have hh : N ^ 2 ≤ (W ^ 2) ^ 2 := by gcongr
    nlinarith
  have hW4 : W ^ 4 ≤ W ^ D := by
    have hh := Real.rpow_le_rpow_of_exponent_le hW hD
    rw [show W ^ 4 = W ^ (4 : ℝ) by norm_cast]
    exact hh
  have hprod : (W * L) * (η * A) ≤ W ^ D := by
    calc
      (W * L) * (η * A) ≤ N * (1 * N) := by gcongr
      _ = N ^ 2 := by ring
      _ ≤ W ^ 4 := hNW2
      _ ≤ W ^ D := hW4
  calc
    W * L * W ^ (-D) = (W * L) / (W ^ D) := by
      rw [Real.rpow_neg hW0.le]
      ring
    _ ≤ 1 / (η * A) := by
      apply (div_le_div_iff₀ hWD0 hηA).2
      nlinarith [hprod]
    _ = η⁻¹ * A⁻¹ := by field_simp

/-- The floor correction is paid by `W≥1`, `η≤1`, and `r≥1`. -/
theorem floor_paid {W η r : ℝ} (hW : 1 ≤ W) (hη : 0 < η)
    (hη1 : η ≤ 1) (hr : 1 ≤ r) :
    W⁻¹ ≤ η⁻¹ * r ^ 5 := by
  have hWi : W⁻¹ ≤ 1 := (inv_le_one₀ (by linarith : 0 < W)).2 hW
  have hηi : 1 ≤ η⁻¹ := (one_le_inv₀ hη).2 hη1
  have hrp : 1 ≤ r ^ 5 := one_le_pow₀ hr
  nlinarith [mul_nonneg (sub_nonneg.mpr hηi) (sub_nonneg.mpr hrp)]

end ExponentRows

/-- The three bounded early exponents for the actual raw QV, under the
explicit Step-1/support scale inequalities and numerical log-loss bounds.
Here `x_j=t⁴`, `A=b²`, `N^δ=p`, and `N^τ=q`; `power_translation` identifies the
three displayed powers with T331 §4. -/
theorem early_T331_profile (X : Sample B) {E D u : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) (ω : Ω)
    (a : LoopArg (B.L N) 2) {ellSource Smax : ℝ}
    (hsource : SourceEvent X E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (B.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (B.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    (hN : 1 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT E u)
    (hA : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u)
    (hAN : (B.W N : ℝ) * B.ell N u * etaT E u ≤ N)
    (hWL : (B.W N : ℝ) * (B.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (B.W N : ℝ) ^ 2)
    (hJcap : APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D ≤ N)
    {ηs t b p q C KJ KS : ℝ}
    (hηs : 0 < ηs) (ht : 0 < t) (hb : 0 < b)
    (hp : 0 < p) (hq : 0 < q) (hC : 1 ≤ C)
    (hKJ : 0 ≤ KJ) (hKS : 0 ≤ KS)
    (hηscale : (etaT E u)⁻¹ = ηs⁻¹ * t ^ 4)
    (hAeq : (B.W N : ℝ) * B.ell N u * etaT E u = b ^ 2)
    (hsourceScale : ellSource ≤ B.ell N u)
    (hr : B.ell N u / ellSource ≤ t ^ 2)
    (hS : √Smax ≤ KS * t ^ 3 * (b⁻¹) ^ 3)
    (hJwide : APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D ≤
      KJ * p ^ 2 * q * t ^ 16)
    (hNearLoss : Lemma57.cNear2 (B.W N : ℝ) (B.ell N u) ≤ C)
    (hFarLoss : Lemma57.cFar2 (B.W N : ℝ) (B.ell N u) ≤ C) :
    Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a) (X.H N u ω) /
        (Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) ^ 2 * t ^ 32 * p ^ 4) ≤
      2048 * C * ηs⁻¹ *
        ((p⁻¹) ^ 4 * (t⁻¹) ^ 18 +
          KJ ^ 2 * KS * q ^ 2 * b⁻¹ * t ^ 7 +
          KJ ^ 3 * p ^ 2 * q ^ 3 * (b⁻¹) ^ 2 * t ^ 20) := by
  let J := APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D
  let r := B.ell N u / ellSource
  let A := (B.W N : ℝ) * B.ell N u * etaT E u
  let S := √Smax
  let K := APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT E u) +
    2 * (B.W N : ℝ)⁻¹ +
    APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D J Smax
  have hηu : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hη1 : etaT E u ≤ 1 := etaT_le_one hE hu0
  have hℓu : 0 < B.ell N u := by
    have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
    have hh := one_le_ellHat_of_nonneg hL hu0 hu1
    simpa only [Band.ell] using (show 0 < ellHat (B.L N) (u : ℂ) by linarith)
  have hJ0 : 0 ≤ J := (APrimeJG.one_le_jG X E N u ω
    (by exact_mod_cast B.W_pos N)).trans' (by norm_num)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ hell).2
    nlinarith [hsourceScale]
  have hW1 : 1 ≤ (B.W N : ℝ) :=
    (Real.one_le_exp (by norm_num)).trans hW
  have hLeak : (B.W N : ℝ) * (B.L N : ℝ) * (B.W N : ℝ) ^ (-D) ≤
      (etaT E u)⁻¹ * A⁻¹ := by
    exact ExponentRows.leak_paid_by_dims hW1 hN
      (by dsimp [A]; linarith) hηu hWL hAN hNW hη1 (by linarith)
  have hFloor : (B.W N : ℝ)⁻¹ ≤ (etaT E u)⁻¹ * r ^ 5 :=
    ExponentRows.floor_paid hW1 hηu hη1 hr1
  have hraw := early_normalized_full X hE hu0 hu1 N ω a hsource hell hD
    hW hlog4 hlog hN heta hA hAN hWL hNW hJcap
    (show 0 < t ^ 4 by positivity) (show 0 < p ^ 2 by positivity)
  have hraw' : Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a) (X.H N u ω) /
        (Step2.tT B E N D u (zdist (B.L N) (a 0 - a 1)) ^ 2 * t ^ 32 * p ^ 4) ≤
      K / (t ^ 32 * p ^ 4) := by
    simpa only [K, J, ← pow_mul, Nat.reduceMul] using hraw
  have hcoeff : K ≤ 2048 * C * (etaT E u)⁻¹ *
      (r ^ 5 + J ^ 2 * A * S + J ^ 3 * A⁻¹) := by
    simpa only [K, J, r, A, S, APrimeQVEndpoint.diagNearRate,
      APrimeQVEndpoint.diagFarRate] using
      (ExponentRows.coefficient_bound
        (W := (B.W N : ℝ)) (L := (B.L N : ℝ))
        (ℓu := B.ell N u) (ℓs := ellSource) (ηu := etaT E u)
        (D := D) (J := J) (S := Smax) (C := C)
        (show 1 ≤ (B.W N : ℝ) from
          (Real.one_le_exp (by norm_num)).trans hW)
        hℓu hell hηu (APrimeJG.one_le_jG X E N u ω
          (by exact_mod_cast B.W_pos N)) hC
        hNearLoss hFarLoss (by simpa only [A] using hLeak)
        (by simpa only [r] using hFloor))
  have hden : 0 ≤ t ^ 32 * p ^ 4 := by positivity
  have hcoeff' := div_le_div_of_nonneg_right hcoeff hden
  have hrows := ExponentRows.full hηs ht hb hp hq hKJ hKS hr0 hJ0
    (Real.sqrt_nonneg Smax) hr hJwide hS
  have hrepr : (etaT E u)⁻¹ *
      (r ^ 5 + J ^ 2 * A * S + J ^ 3 * A⁻¹) /
        (t ^ 32 * p ^ 4) =
      ηs⁻¹ * t ^ 4 *
        (r ^ 5 + J ^ 2 * b ^ 2 * S + J ^ 3 * (b⁻¹) ^ 2) /
          (t ^ 32 * p ^ 4) := by
    rw [hηscale]
    dsimp [A]
    rw [hAeq]
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hrows (by positivity : 0 ≤ 2048 * C)
  calc
    _ ≤ K / (t ^ 32 * p ^ 4) := hraw'
    _ ≤ (2048 * C * (etaT E u)⁻¹ *
          (r ^ 5 + J ^ 2 * A * S + J ^ 3 * A⁻¹)) /
          (t ^ 32 * p ^ 4) := hcoeff'
    _ = 2048 * C * (ηs⁻¹ * t ^ 4 *
          (r ^ 5 + J ^ 2 * b ^ 2 * S + J ^ 3 * (b⁻¹) ^ 2) /
          (t ^ 32 * p ^ 4)) := by
      calc
        _ = 2048 * C * ((etaT E u)⁻¹ *
            (r ^ 5 + J ^ 2 * A * S + J ^ 3 * A⁻¹) /
              (t ^ 32 * p ^ 4)) := by ring
        _ = _ := by rw [hrepr]
    _ ≤ _ := by simpa only [mul_assoc] using hscaled

/-- The square-root endpoint profile. Its `diagFarRate` contains both the
quadratic and cubic block powers, including the spatially weighted leakage. -/
noncomputable def rootProfile (B : Band Ω) (E : ℝ) (N : ℕ)
    (u v D ellSource J Smax ε : ℝ) (a : LoopArg (B.L N) 2) : ℝ :=
  √(APrimeQVEndpoint.diagNearRate B N (B.ell N u) ellSource (etaT E u) + 2 * ε) *
      ((((1 - u) / (1 - v)) ^ 2 *
          Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
          Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) *
        (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
            6 * ellStar (B.W N : ℝ) (B.ell N v) then 1 else 0)
      + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
          (B.W N : ℝ) ^ (-D) *
          Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) +
    √(APrimeQVEndpoint.diagFarRate B N (B.ell N u) (etaT E u) D J Smax) *
      (((1 - u) / (1 - v)) ^ 2 *
        Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
        Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)))

/-- Enlarging the repaired raw near coefficient enlarges the endpoint profile.
The kernel and leakage multipliers are nonnegative. -/
theorem rootProfile_mono_epsilon (B : Band Ω) (E : ℝ) (N : ℕ)
    (u v D ellSource J Smax : ℝ) (a : LoopArg (B.L N) 2)
    {ε ε' : ℝ} (hW : 0 ≤ (B.W N : ℝ)) (hε : ε ≤ ε') :
    rootProfile B E N u v D ellSource J Smax ε a ≤
      rootProfile B E N u v D ellSource J Smax ε' a := by
  have hT : 0 ≤ Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    simpa only [Step2.tT] using
      tailT_nonneg hW (zdist (B.L N) (a 0 - a 1))
  have hxi : 0 ≤ Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im :=
    Step2.xiK_nonneg _ _ _
  have hchi : 0 ≤ (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
      6 * ellStar (B.W N : ℝ) (B.ell N v) then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hWD : 0 ≤ (B.W N : ℝ) ^ (-D) := Real.rpow_nonneg hW _
  have hK : 0 ≤
      (((1 - u) / (1 - v)) ^ 2 *
          Step2.xiK (B.L N) (B.W N : ℝ) (mE E).im *
          Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1))) *
        (if (zdist (B.L N) (a 0 - a 1) : ℝ) ≤
            6 * ellStar (B.W N : ℝ) (B.ell N v) then 1 else 0)
      + 256 * Real.exp 3 * ((1 - u) / (1 - v)) ^ 2 *
          (B.W N : ℝ) ^ (-D) *
          Step2.tT B E N D v (zdist (B.L N) (a 0 - a 1)) := by
    positivity
  unfold rootProfile
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ hK
  apply Real.sqrt_le_sqrt
  linarith

/-- Full evolved QV of the actual Gaussian loop observable. All random
inputs remain pointwise source-event hypotheses. -/
theorem sqrt_evolved_full (X : Sample B) {E D u v : ℝ} (hE : |E| < 2)
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (N : ℕ) (ω : Ω) (a : LoopArg (B.L N) 2)
    {ellSource Smax : ℝ} (hsource : SourceEvent X E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (B.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (B.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (B.W N : ℝ))
    (hAu : 1 ≤ (B.W N : ℝ) * B.ell N u * etaT E u) :
    √(Gauss.quadVar B.toDims N
      (fun M' => Uker (B.L N) (xiOf (mSigma E) Step2.sigPM)
        (u : ℂ) (v : ℂ)
        (fun b => Gauss.loopObs B.toDims N (zt E u)
          (Gauss.toIdx Step2.sigPM b) M') a) (X.H N u ω)) ≤
      rootProfile B E N u v D ellSource
        (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D) Smax
        (EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D
          (APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D)) a := by
  let J := APrimeJG.jG X E N u ω (B.ell N u) (etaT E u) D
  let ε := EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D J
  have hu1 : u < 1 := huv.trans_lt hv1
  have hη : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hJ : 1 ≤ J := APrimeJG.one_le_jG X E N u ω hW0
  have hgm : ∀ (s : Bool) (x y : ZMod (B.L N))
      (p q : ZMod (B.L N) × Fin (B.W N)), p.1 = x → q.1 = y →
      ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ APrimeJG.gmBlk X E N u ω x y := by
    intro s x y p q hp hq
    rcases p with ⟨px, pi⟩
    rcases q with ⟨qx, qi⟩
    simp only at hp hq
    subst px
    subst qx
    exact APrimeJG.norm_Gsig_le_gmBlk X E N u ω s x y pi qi
  have h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      APrimeJG.gsqBlk X E N u ω x y ≤
        J * Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
    intro x y hxy
    simpa only [J, Step2.tT] using
      APrimeJG.gsqBlk_le_jG_mul_tailT X E N u ω hW0 x y hxy
  have hnear := EEDef.eeL6_near_remainder X E N u ω Step2.sigPM
    (by have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
        have hh := one_le_ellHat_of_nonneg hL hu0 hu1
        simpa only [Band.ell] using (show 0 < ellHat (B.L N) (u : ℂ) by linarith))
    hη hJ hlog4 (APrimeJG.gmBlk_nonneg X E N u ω) hgm
    (APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω)
    (APrimeJG.gmBlk_row_le_gsqBlk X E N u ω)
    (by simpa only [Step2.tT, Band.ell] using h42)
    (APrimeJG.gsqBlk_le_inv_etaT_sq X hE N hu1 ω)
  have hroot := APrimeQVEndpoint.sqrt_evolvedQV_le_endpoint' X hE
    hu0 huv hv1 hW ω a hell hJ (by linarith : 1 ≤ D) hAu hlog
    (by dsimp [EEDef.nearEpsilon]; positivity)
    (APrimeJG.gmBlk_nonneg X E N u ω) hgm
    (APrimeJG.gsqBlk_nonneg X E N u ω)
    (APrimeJG.gmBlk_mul_swap_le_gsqBlk X E N u ω)
    (APrimeJG.gmBlk_row_le_gsqBlk X E N u ω)
    hsource.four hsource.six hnear h42
  simpa only [rootProfile, J, ε, Band.ell] using hroot

/-- The fixed-endpoint normalization of the actual uncut `qvAt`. The square
root is divided by `driftScale = T_{v,D}(a)(η_s/η_v)^4` exactly once. -/
theorem sqrt_qvAt_full (d : Gauss.Dims) {E D s u v : ℝ} (hE : |E| < 2)
    (hsu : s ≤ u) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (N : ℕ) (ω : Gauss.Ω d) (a : LoopArg (d.L N) 2)
    {ellSource Smax : ℝ}
    (hsource : SourceEvent (Gauss.sample d) E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (d.W N : ℝ))
    (hAu : 1 ≤ (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u) :
    √(APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v u ω) ≤
      (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
        rootProfile (Gauss.band d) E N u v D ellSource
          (APrimeJG.jG (Gauss.sample d) E N u ω
            ((Gauss.band d).ell N u) (etaT E u) D) Smax
          (EEDef.nearEpsilon (d.W N : ℝ) (d.L N : ℝ)
            ((Gauss.band d).ell N u) (etaT E u) D
            (APrimeJG.jG (Gauss.sample d) E N u ω
              ((Gauss.band d).ell N u) (etaT E u) D)) a := by
  have hc : 0 ≤ (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d hE
      (hsu.trans huv) hv1 N a)).le
  rw [APrimeQVBridge.sqrt_qvAt_eq_evolved_loopObs d hE
    (hsu.trans huv) hv1 N a ω]
  apply mul_le_mul_of_nonneg_left ?_ hc
  have h := sqrt_evolved_full (B := Gauss.band d) (Gauss.sample d)
    hE hu0 huv hv1 N ω a hsource hell hD hW hlog4 hlog hAu
  cases d
  convert h using 1 <;> rfl

/-- Square form of the same full current-QV profile. -/
theorem qvAt_full (d : Gauss.Dims) {E D s u v : ℝ} (hE : |E| < 2)
    (hsu : s ≤ u) (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v < 1)
    (N : ℕ) (ω : Gauss.Ω d) (a : LoopArg (d.L N) 2)
    {ellSource Smax : ℝ}
    (hsource : SourceEvent (Gauss.sample d) E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (d.W N : ℝ))
    (hAu : 1 ≤ (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u) :
    APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v u ω ≤
      ((APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
        rootProfile (Gauss.band d) E N u v D ellSource
          (APrimeJG.jG (Gauss.sample d) E N u ω
            ((Gauss.band d).ell N u) (etaT E u) D) Smax
          (EEDef.nearEpsilon (d.W N : ℝ) (d.L N : ℝ)
            ((Gauss.band d).ell N u) (etaT E u) D
            (APrimeJG.jG (Gauss.sample d) E N u ω
              ((Gauss.band d).ell N u) (etaT E u) D)) a) ^ 2 := by
  apply APrimeQVEndpoint.quadVar_le_sq_of_sqrt_le
    (Gauss.quadVar_nonneg _ _)
  exact sqrt_qvAt_full d hE hsu hu0 huv hv1 N ω a hsource
    hell hD hW hlog4 hlog hAu

/-- At the current point the raw near residual is already at most `W⁻¹`,
before the fixed endpoint denominator is applied to the full QV. -/
theorem qvAt_full_with_near_repair (d : Gauss.Dims) {E D s u v : ℝ}
    (hE : |E| < 2) (hsu : s ≤ u) (hu0 : 0 ≤ u)
    (huv : u ≤ v) (hv1 : v < 1)
    (N : ℕ) (ω : Gauss.Ω d) (a : LoopArg (d.L N) 2)
    {ellSource Smax : ℝ}
    (hsource : SourceEvent (Gauss.sample d) E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (d.W N : ℝ))
    (hN : 1 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT E u)
    (hAu : 1 ≤ (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u)
    (hAN : (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u ≤ N)
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2)
    (hJcap : APrimeJG.jG (Gauss.sample d) E N u ω
      ((Gauss.band d).ell N u) (etaT E u) D ≤ N) :
    APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v u ω ≤
      ((APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
        rootProfile (Gauss.band d) E N u v D ellSource
          (APrimeJG.jG (Gauss.sample d) E N u ω
            ((Gauss.band d).ell N u) (etaT E u) D) Smax
          (EEDef.nearEpsilon (d.W N : ℝ) (d.L N : ℝ)
            ((Gauss.band d).ell N u) (etaT E u) D
            (APrimeJG.jG (Gauss.sample d) E N u ω
              ((Gauss.band d).ell N u) (etaT E u) D)) a) ^ 2 ∧
    EEDef.nearEpsilon (d.W N : ℝ) (d.L N : ℝ)
      ((Gauss.band d).ell N u) (etaT E u) D
      (APrimeJG.jG (Gauss.sample d) E N u ω
        ((Gauss.band d).ell N u) (etaT E u) D) ≤ (d.W N : ℝ)⁻¹ := by
  refine ⟨qvAt_full d hE hsu hu0 huv hv1 N ω a hsource
    hell hD hW hlog4 hlog hAu, ?_⟩
  exact (early_raw_full (B := Gauss.band d) (Gauss.sample d) hE
    hu0 (huv.trans_lt hv1) N ω a hsource hell hD hW hlog4 hlog
    hN heta hAu hAN hWL hNW hJcap).2

/-- The repaired coefficient is replaced by `W⁻¹` in the full endpoint
profile *before* applying the fixed endpoint normalization. -/
theorem qvAt_full_absorbed (d : Gauss.Dims) {E D s u v : ℝ}
    (hE : |E| < 2) (hsu : s ≤ u) (hu0 : 0 ≤ u)
    (huv : u ≤ v) (hv1 : v < 1)
    (N : ℕ) (ω : Gauss.Ω d) (a : LoopArg (d.L N) 2)
    {ellSource Smax : ℝ}
    (hsource : SourceEvent (Gauss.sample d) E N u ω ellSource Smax)
    (hell : 0 < ellSource) (hD : 60 ≤ D)
    (hW : Real.exp 1 ≤ (d.W N : ℝ))
    (hlog4 : 4 ≤ Real.log (d.W N : ℝ))
    (hlog : (4 * D) ^ 2 ≤ Real.log (d.W N : ℝ))
    (hN : 1 ≤ (N : ℝ))
    (heta : (N : ℝ)⁻¹ ≤ etaT E u)
    (hAu : 1 ≤ (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u)
    (hAN : (d.W N : ℝ) * (Gauss.band d).ell N u * etaT E u ≤ N)
    (hWL : (d.W N : ℝ) * (d.L N : ℝ) ≤ N)
    (hNW : (N : ℝ) ≤ (d.W N : ℝ) ^ 2)
    (hJcap : APrimeJG.jG (Gauss.sample d) E N u ω
      ((Gauss.band d).ell N u) (etaT E u) D ≤ N) :
    APrimeDriftTimeFamily.qvAt d E D N Step2.sigPM a s v u ω ≤
      ((APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ *
        rootProfile (Gauss.band d) E N u v D ellSource
          (APrimeJG.jG (Gauss.sample d) E N u ω
            ((Gauss.band d).ell N u) (etaT E u) D) Smax
          ((d.W N : ℝ)⁻¹) a) ^ 2 := by
  have hsmall := (qvAt_full_with_near_repair d hE hsu hu0 huv hv1
    N ω a hsource hell hD hW hlog4 hlog hN heta hAu hAN hWL hNW hJcap).2
  have hmono := rootProfile_mono_epsilon (Gauss.band d) E N u v D ellSource
    (APrimeJG.jG (Gauss.sample d) E N u ω
      ((Gauss.band d).ell N u) (etaT E u) D) Smax a
    (by exact_mod_cast (d.W_pos N).le) hsmall
  have hc : 0 ≤ (APrimeDriftTimeFamily.driftScale d E D N a s v)⁻¹ :=
    (inv_pos.mpr (APrimeDriftTimeFamily.driftScale_pos d hE
      (hsu.trans huv) hv1 N a)).le
  have hroot := sqrt_qvAt_full d hE hsu hu0 huv hv1 N ω a hsource
    hell hD hW hlog4 hlog hAu
  have hfinal := hroot.trans (mul_le_mul_of_nonneg_left hmono hc)
  exact APrimeQVEndpoint.quadVar_le_sq_of_sqrt_le
    (Gauss.quadVar_nonneg _ _) hfinal

/-- A positive-duration Gaussian first cell with nonzero endpoint scale and
the actual block witness `J ≥ 1`. -/
theorem first_cell_gaussian (d : Gauss.Dims) (N : ℕ) (ω : Gauss.Ω d) :
    ∃ a : LoopArg (d.L N) 2,
      (0 : ℝ) < 1 / 2 ∧
      0 < APrimeDriftTimeFamily.driftScale d 0 60 N a 0 (1 / 2) ∧
      1 ≤ APrimeJG.jG (Gauss.sample d) 0 N 0 ω
        ((Gauss.band d).ell N 0) (etaT 0 0) 60 := by
  let a : LoopArg (d.L N) 2 := fun _ => 0
  refine ⟨a, by norm_num, ?_, ?_⟩
  · exact APrimeDriftTimeFamily.driftScale_pos d (D := 60)
      (by norm_num) (by norm_num) (by norm_num) N a
  · exact APrimeJG.one_le_jG (Gauss.sample d) 0 N 0 ω
      (by exact_mod_cast d.W_pos N)

#print axioms early_raw_full
#print axioms early_normalized_full
#print axioms ExponentRows.full
#print axioms ExponentRows.power_translation
#print axioms ExponentRows.coefficient_bound
#print axioms ExponentRows.leak_paid_by_dims
#print axioms ExponentRows.floor_paid
#print axioms early_T331_profile
#print axioms sourceEvent_of_step1
#print axioms sqrt_evolved_full
#print axioms sqrt_qvAt_full
#print axioms qvAt_full
#print axioms qvAt_full_with_near_repair
#print axioms rootProfile_mono_epsilon
#print axioms qvAt_full_absorbed
#print axioms first_cell_gaussian

end RBM.APrimeFullQV
