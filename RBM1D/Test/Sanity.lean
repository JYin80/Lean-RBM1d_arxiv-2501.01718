/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Propagator.Basic
import RBM1D.Propagator.Bounds
import RBM1D.Propagator.Deriv
import RBM1D.Propagator.Support
import RBM1D.Propagator.Root

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
