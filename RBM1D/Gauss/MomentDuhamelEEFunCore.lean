/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM1D.Hierarchy.EEBridgeArgCore

/-! The exact deterministic `eeFun` definition from the moment-Duhamel facade. -/

namespace RBM
namespace MomentDuhamel

variable {Ω : Type*} [MeasurableSpace Ω] {B : Band Ω}

/-- **`(E ⊗ E)_{u,σ,c}` of Definition 5.4 as a function of the time and the matrix**, with no
`ω`, i.e. `RBM.EEBridge.eeArg` at the spectral parameter `z_u`.

This is *not* a datum of the interface below: `E ⊗ E` is a completely explicit tensor built
from the resolvent of `M` at `z_u` (T127), so the moment inequalities of `Hyp` quantify over
nothing here.  Making it a data field — as `RBM.SumZeroDyn.Hierarchy.EE` is — would let an
instance take it enormous and render `momentDuhamel` vacuous, which is exactly the fiat
failure mode `Hyp` exists to close; see `docs/STATUS.md` under T145. -/
noncomputable def eeFun (B : Band Ω) (E : ℝ) (N : ℕ) (u : ℝ)
    (M : Matrix (B.Idx N) (B.Idx N) ℂ) {m : ℕ} (σ : Fin m → Bool)
    (c : LoopArg (B.L N) (m + m)) : ℂ :=
  EEBridge.eeArg B.toDims N (zt E u) M σ c


end MomentDuhamel
end RBM
