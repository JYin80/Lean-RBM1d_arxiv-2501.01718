/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Gauss.NearFieldRemainder
import RBM1D.Gauss.BlockGreen
import RBM1D.Gauss.FlowContInt

/-!
# Uncut quadratic variation from actual block Green witnesses

The length-four and length-six estimates are explicit pointwise Step-1 event
inputs. The near six-loop residual is handled before endpoint propagation.
-/

namespace RBM.FullQuadVar

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
    (hJcap : BlockGreen.jG X E N u ω (B.ell N u) (etaT E u) D ≤ N) :
    Gauss.quadVar B.toDims N
      (fun M' => MomentDuhamel.lkFun B E N u M' Step2.sigPM a) (X.H N u ω) ≤
      QVEndpoint.diagShape' B N (B.ell N u) ellSource (etaT E u) D
        (BlockGreen.jG X E N u ω (B.ell N u) (etaT E u) D) Smax
        (EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D
          (BlockGreen.jG X E N u ω (B.ell N u) (etaT E u) D)) a ∧
    EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D
      (BlockGreen.jG X E N u ω (B.ell N u) (etaT E u) D) ≤ (B.W N : ℝ)⁻¹ := by
  let J := BlockGreen.jG X E N u ω (B.ell N u) (etaT E u) D
  let ε := EEDef.nearEpsilon (B.W N : ℝ) (B.L N : ℝ) (B.ell N u) (etaT E u) D J
  have hL : 1 ≤ B.L N := by have := B.three_le_L N; omega
  have hℓu : 1 ≤ B.ell N u := by
    simpa only [Band.ell] using one_le_ellHat_of_nonneg hL hu0 hu1
  have hη : 0 < etaT E u := Step2.etaT_pos' hE hu1
  have hW0 : (0 : ℝ) < B.W N := by exact_mod_cast B.W_pos N
  have hJ : 1 ≤ J := BlockGreen.one_le_jG X E N u ω hW0
  have hε : 0 ≤ ε := by unfold ε EEDef.nearEpsilon; positivity
  have hgm : ∀ (s : Bool) (x y : ZMod (B.L N))
      (p q : ZMod (B.L N) × Fin (B.W N)), p.1 = x → q.1 = y →
      ‖Gsig (X.H N u ω) (zt E u) s p q‖ ≤ BlockGreen.gmBlk X E N u ω x y := by
    intro s x y p q hp hq
    rcases p with ⟨px, pi⟩
    rcases q with ⟨qx, qi⟩
    simp only at hp hq
    subst px
    subst qx
    exact BlockGreen.norm_Gsig_le_gmBlk X E N u ω s x y pi qi
  have h42 : ∀ x y : ZMod (B.L N),
      ellStar (B.W N : ℝ) (B.ell N u) / 2 ≤ (zdist (B.L N) (x - y) : ℝ) →
      BlockGreen.gsqBlk X E N u ω x y ≤
        J * Step2.tT B E N D u (zdist (B.L N) (x - y)) := by
    intro x y hxy
    simpa only [J, Step2.tT] using
      BlockGreen.gsqBlk_le_jG_mul_tailT X E N u ω hW0 x y hxy
  have hnear := EEDef.eeL6_near_remainder X E N u ω Step2.sigPM
    (by linarith : 0 < B.ell N u) hη hJ hlog4
    (BlockGreen.gmBlk_nonneg X E N u ω) hgm
    (BlockGreen.gmBlk_mul_swap_le_gsqBlk X E N u ω)
    (BlockGreen.gmBlk_row_le_gsqBlk X E N u ω)
    (by simpa only [Step2.tT] using h42)
    (BlockGreen.gsqBlk_le_inv_etaT_sq X hE N hu1 ω)
  have hεsmall : ε ≤ (B.W N : ℝ)⁻¹ := by
    apply EEDef.nearEpsilon_le_inv hW
      (by exact_mod_cast (show 0 < B.L N by have := B.three_le_L N; omega) :
        (0 : ℝ) < B.L N)
      (by linarith : 0 < B.ell N u) hη hN (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ J) (by linarith : 2 * (1 : ℝ) + 14 ≤ D)
      heta hA hAN hWL hNW (by simpa [J] using hJcap) hlog4 hlog
  have hraw := EarlyQVRate.quadVar_lkFun_le_ee_sym' X hE hu0 hu1 ω
    Step2.sigPM a hℓu hell hη hJ hε
    (BlockGreen.gmBlk_nonneg X E N u ω) hgm
    (BlockGreen.gsqBlk_nonneg X E N u ω)
    (BlockGreen.gmBlk_mul_swap_le_gsqBlk X E N u ω)
    (BlockGreen.gmBlk_row_le_gsqBlk X E N u ω)
    hsource.four (hsource.six a) (hnear a) h42
  exact ⟨by simpa only [J, ε] using hraw, by simpa only [J, ε] using hεsmall⟩

namespace ExponentRows

/-! The variables `t⁴=x_j`, `b²=A`, `p=N^δ`, and `q=N^τ` make
the three early rows integral-power identities. -/

end ExponentRows

end RBM.FullQuadVar
