/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Defs.Domination
import RBM1D.Defs.Model
import RBM1D.Propagator.Basic
import RBM1D.Propagator.Bounds
import RBM1D.Propagator.Deriv
import RBM1D.Propagator.Support
import RBM1D.Propagator.Root
import RBM1D.Propagator.Decay
import RBM1D.Propagator.Symbol
import RBM1D.Test.Numeric

/-!
# Axiom audit

Every Phase 1 result should depend only on `propext`, `Classical.choice`
and `Quot.sound`.  Anything else (in particular `sorryAx`) is a bug.
-/

#print axioms RBM.SB_isSymm
#print axioms RBM.sum_SB_row
#print axioms RBM.SB_mulVec_one
#print axioms RBM.norm_SB
#print axioms RBM.Theta_mul
#print axioms RBM.mul_Theta
#print axioms RBM.Theta_transpose
#print axioms RBM.Theta_commute_SB
#print axioms RBM.Theta_commute
#print axioms RBM.sum_Theta_row
#print axioms RBM.Theta_eq_tsum
#print axioms RBM.Theta_apply_add_right
#print axioms RBM.hasDerivAt_Theta_apply
#print axioms RBM.Theta_sub_Theta
#print axioms RBM.norm_Theta_le
#print axioms RBM.norm_Theta_apply_le
#print axioms RBM.SB_pow_apply_eq_zero
#print axioms RBM.norm_Theta_apply_le_pow
#print axioms RBM.norm_root_ne_one
#print axioms RBM.norm_rho_lt_one
#print axioms RBM.theta_eq_circulant
#print axioms RBM.theta_apply_closed_form
#print axioms RBM.norm_theta_apply_le_rho_pow
#print axioms RBM.UnifDetDom.trans
#print axioms RBM.UnifDetDom.mul
#print axioms RBM.UnifDetDom.const_mul_right
#print axioms RBM.DetDom.add_left
#print axioms RBM.DetDom.smul_left
#print axioms RBM.Shat_eq_cos
#print axioms RBM.SB_mulVec_char
#print axioms RBM.one_sub_mul_Shat_ne_zero
#print axioms RBM.Theta_eq_circulant_fourierKernel
#print axioms RBM.Theta_apply_fourier
#print axioms RBM.xi_mul_poly
#print axioms RBM.one_sub_xi_mul
#print axioms RBM.one_sub_rho_sq
#print axioms RBM.rho_real_bounds
#print axioms RBM.Numeric.Theta_five_half
#print axioms RBM.sum_Svar_row
#print axioms RBM.Svar_transpose
#print axioms RBM.sum_Eblk
#print axioms RBM.Eblk_mul_Eblk
#print axioms RBM.Spaper_eq
#print axioms RBM.Epaper_eq
#print axioms RBM.split_bijective
