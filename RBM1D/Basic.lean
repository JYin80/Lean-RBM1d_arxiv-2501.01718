/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

/-!
# RBM1D

A Lean 4 / Mathlib formalization of the deterministic core of

> Horng-Tzer Yau and Jun Yin,
> *Delocalization of One-Dimensional Random Band Matrices*.

See `docs/STATUS.md` for what is formalized, `docs/paper-deltas.md` for the
places where the Lean statement departs from the paper, and `blueprint/` for the
dependency graph.

The file layout follows the paper:

* `RBM1D.Defs.Block`       — the block covariance matrix `S^(B)` of Section 2.1
* `RBM1D.Defs.Dist`        — graph distance on the cycle `ZMod L`
* `RBM1D.Propagator.Basic` — Definition 2.13 and Lemma 2.14 (1), (2), (3), (5)
* `RBM1D.Propagator.Deriv` — equation (2.51)
* `RBM1D.Propagator.Bounds`— the bounds (3.35), (3.36)
* `RBM1D.Propagator.Support` — band structure and a first exponential decay bound
-/
