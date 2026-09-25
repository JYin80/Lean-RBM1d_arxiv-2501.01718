Ticket: T1485 (amend-1; supersedes T1485.md, withdrawn before any work started. The old "overshoot control" target is dropped: `docs/claude-team/pilot-P4P5-paper.md` §6(a) shows it is not needed)
Group / type: pilot-TruePath (G1b) / prove — pilot P5 (discrete Duhamel)
Role: prover
Release condition for the audit stage: prove report shows math preflight PASS; `lake build RBM1D.Gauss.GridDuhamel` succeeds.
Math source and targets: the discrete replacement of Lemma 5.3 / (5.20)–(5.21), `pilot-P4P5-paper.md` §3 and §9 repair (A).
  (T1) `duhamel_telescope` (generic): in an additive commutative group `V`, for `U : ℕ → ℕ → V →+ V` with `U k k = id` and `U j k ∘ U i j = U i k` for `i ≤ j ≤ k`, and any `A : ℕ → V`: `A k - U 0 k (A 0) = ∑ j ∈ range k, U (j+1) k (A (j+1) - U j (j+1) (A j))`.
  (T2) `duhamel_telescope_stopped`: the same identity with `k` replaced by `min k (τ ω)` for a function `τ : Ω' → ℕ`, per ω (a corollary of (T1)).
  (T3) `Uker_grid_semigroup`: specialisation to the repo's kernel `RBM.Uker` (`Hierarchy/Kernel.lean:190`) at grid times `u_k = time s t K N k` of T1481, using the existing `RBM.Uker_comp` and `RBM.Uker_self`: the family `fun j k => Uker ξ (u_j) (u_k)` satisfies the hypotheses of (T1).
  (T4) `Uker_factor`: `Uker ξ (u_{j+1}) (u_k) = (Uker ξ (u_k) t)⁻¹ ∘ Uker ξ (u_{j+1}) t`, stated as `Uker ξ u_k t ∘ Uker ξ u_{j+1} u_k = Uker ξ u_{j+1} t` together with invertibility of `Uker ξ u_k t` when `1 - t·ξ_i·S^{(B)}` and `1 - u_k·ξ_i·S^{(B)}` are invertible (the same conditions as in `Uker`'s existing lemmas). This is the factorisation of repair (A); a quantitative bound on the inverse is NOT a target here.
Step 0 (read-only checks): exact statements of `RBM.Uker_comp`, `RBM.Uker_self`, `RBM.Uker_duhamel` (grep in `RBM1D/Hierarchy/Kernel.lean`), including their side conditions; if `Uker_comp` needs hypotheses not available at grid times, report them as `blocked` with the question rather than adding assumptions.
Dependencies (must already be accepted): `RBM.Uker`, `RBM.Uker_comp`, `RBM.Uker_self` (committed); (T3)/(T4) use `time` from T1481 — if T1481 is not yet merged, state (T3)/(T4) for an arbitrary monotone sequence `u : ℕ → ℝ` instead, which is at least as strong.
Upstream / downstream: consumed by the A5 Step 2 assembly. prover: algebra.
Sole writable files: `RBM1D/Gauss/GridDuhamel.lean`        Must not touch: every other file.
Root import: none.
Branch: t/T1485
Required reading (only these): `CLAUDE.md` §3; `RBM1D/Hierarchy/Kernel.lean` (around lines 150–260 and the `Uker_*` lemmas); `docs/claude-team/pilot-P4P5-paper.md` §3, §9.
Acceptance criteria: (T1)–(T4) with these names in `RBM.Gauss.Grid`; no `sorry`/`admit`/`axiom`; auditor checks that (T1) is not stated with hypotheses that trivialise it (e.g. `U ≡ id` only), and that (T3)/(T4) use the repo's actual `Uker`.
