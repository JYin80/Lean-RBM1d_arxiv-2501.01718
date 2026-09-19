/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Lean

/-!
# Axiom audit: the `#assert_rbm_axioms` command

`#assert_rbm_axioms` walks every declaration in the namespace `RBM` visible in the current
environment, collects the axioms it depends on (the same computation as `#print axioms`), and
**fails** unless all of them are among `propext`, `Classical.choice`, `Quot.sound`.  In
particular any `sorry` (`sorryAx`) or project `axiom` anywhere in the `RBM` namespace breaks
the build.  It also fails if it finds fewer than `50` declarations, so that a renamed
namespace cannot make the audit pass vacuously.

When the stochastic layer introduces its `axiom` interfaces (`CLAUDE.md`, rule 6), they must
be added to an explicit allow-list here, so that every dependency on them stays visible.
-/

namespace RBM.Audit

open Lean Elab Command

/-- The axioms every `RBM` declaration may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Fails unless every declaration in `RBM` uses only `RBM.Audit.allowedAxioms`. -/
elab "#assert_rbm_axioms" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if (`RBM).isPrefixOf n then acc.push n else acc
  if names.size < 50 then
    throwError m!"axiom audit: only {names.size} declarations found in `RBM`"
  let mut bad : Array MessageData := #[]
  for n in names do
    let axs ← collectAxioms n
    let extra := axs.filter fun a => !allowedAxioms.contains a
    unless extra.isEmpty do
      bad := bad.push m!"{n} depends on {extra.toList}"
  if bad.isEmpty then
    logInfo m!"axiom audit: {names.size} declarations in `RBM`, all within {allowedAxioms}"
  else
    throwError m!"axiom audit failed:\n{MessageData.joinSep bad.toList "\n"}"

end RBM.Audit
