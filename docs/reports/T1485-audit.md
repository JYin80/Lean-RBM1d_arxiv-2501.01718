# T1485-audit — discrete Duhamel telescoping identity (pilot P5)

Ticket: `docs/tickets/T1485-amend-1.md`. Prover report: `docs/reports/T1485-prove.md`.
Audited commit: `7257bb8` on `t/T1485` (detached audit worktree `/Users/junyin/Lean_proof/RBM1D-wt/T1485-audit`;
`t/T1485` itself is checked out in the prover worktree).
Diff vs `main`: exactly one new file, `RBM1D/Gauss/GridDuhamel.lean` (+162). No existing file touched,
so no frozen signature changed; no root import added (ticket: "Root import: none").

## Overall verdict: PASS (T1, T2, T3, T4 all PASS)

## Common checks

* **Math preflight**: the report has a per-target math preflight (T1-T4 each PASS, overall PASS),
  placed before the "Lean work" section, with Step 0 read-only checks of `Uker_self`/`Uker_comp`/
  `Uker_duhamel` and their side conditions. Satisfies check 1.
* **Builds (audit worktree)**:
  `lake build RBM1D.Gauss.GridDuhamel` -> `Build completed successfully (2428 jobs)`, no errors/warnings.
  `lake build RBM1D` -> `Build completed successfully (9324 jobs)`, exit 0 (only pre-existing
  `ring`-fallback info lines from other modules).
* **Axioms** (`#print axioms`, run by the auditor): `duhamel_telescope`, `duhamel_telescope_stopped`,
  `UkerHom`, `UkerHom_apply`, `Uker_grid_semigroup`, `Uker_factor` all depend only on
  `[propext, Classical.choice, Quot.sound]`.
* **No `sorry`/`admit`/`axiom`** in the file (grep).
* **Dependencies**: only `RBM.Uker` (Kernel.lean:190, (5.17)), `RBM.Uker_add` (:241), `RBM.Uker_self`
  (:282), `RBM.Uker_comp` (:306) — all committed on `main`; plus Mathlib. No dependency on the unmerged
  T1481; no cycle (the file imports only `RBM1D.Hierarchy.Kernel`).
* **Actual `Uker`**: `UkerHom` is `AddMonoidHom.mk' (RBM.Uker L ξ s t) (RBM.Uker_add L ξ s t)`, and
  `UkerHom_apply` is `rfl`. `Uker` is the repo kernel `a ↦ ∑_b (∏_i edgeKer L (ξ i) s t (a i) (b i)) A b`
  with `edgeKer s t = (1 - sξ S^(B)) Θ(tξ)`, which is not the identity for `s ≠ t`. (T3)/(T4) are stated
  for this kernel, not for a surrogate.

## (T1) `duhamel_telescope` — PASS

* Statement vs ticket/paper (pilot §3 telescoping identity
  `A_k − U_{u_0,u_k}A_0 = Σ_{j<k} U_{u_{j+1},u_k}(A_{j+1} − U_{u_j,u_{j+1}}A_j)`): `V` `AddCommGroup`,
  `U : ℕ → ℕ → V →+ V`, `hself : ∀ k, U k k = id`, `hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k`,
  arbitrary `A : ℕ → V`, `k : ℕ`; conclusion
  `A k - U 0 k (A 0) = ∑ j ∈ range k, U (j+1) k (A (j+1) - U j (j+1) (A j))`. Exact match, index range
  `range k` = `j < k`, composition order `U j k ∘ U i j` correct (earlier kernel applied first).
* Hypotheses are exactly the two structural laws; the composition law is required only for ordered
  triples `i ≤ j ≤ k` (weaker than a full group law, so the theorem is at least as strong as the target).
* Non-vacuity: auditor compiled (scratch file, not in repo) a witness
  `U j k := AddMonoidHom.mulLeft (2^(k-j))` on `ℝ` satisfying both laws with `U 0 1 ≠ id`. The in-file
  `example : True` only checks the exponent arithmetic and is not itself a witness of the hypotheses —
  cosmetic, not a defect; the audit witness closes the point. Hypotheses are not `U ≡ id` only.
* Boundary `k = 0`: both sides `0` via `hself 0`; handled in the proof, no `k = 0` loophole in the
  statement (it is `∀ k`).

## (T2) `duhamel_telescope_stopped` — PASS

* Same hypotheses as (T1) plus `τ : Ω' → ℕ`, `ω : Ω'`, `k : ℕ`; conclusion is (T1) with every
  occurrence of `k` replaced by `min k (τ ω)` (upper summation limit and kernel end index). Proof is
  (T1) at `min k (τ ω)`. Matches the ticket ("per ω, a corollary of (T1)") and pilot §3 ("replace k by
  k∧τ; τ takes grid values"). No measurability/stopping-time claims are made or needed; `τ` is an
  arbitrary function, which is at least as general as a stopping time.

## (T3) `Uker_grid_semigroup` — PASS

* Statement: `hL : 3 ≤ L`, `u : ℕ → ℝ` arbitrary, `hu : ∀ k i, ‖(u k : ℂ) * ξ i‖ < 1`; conclusion is the
  conjunction of `hself` and `hcomp` of (T1) for `fun j k => UkerHom L ξ (u j) (u k)`.
* T1481 (`time`) is not merged, so the arbitrary-sequence fallback licensed by the ticket is used; it
  specialises to `u := time s t K N` by instantiation, so it is at least as strong. (The ticket names
  no monotonicity requirement; none is used.)
* Side conditions: `hu` is exactly the pointwise hypothesis of `Uker_self`/`Uker_comp`, needed at every
  index because (T1)'s hypotheses quantify over all indices. Note for the downstream consumer: when
  specialising to a finite grid `u_0..u_K`, `hu` must hold for all `k : ℕ`; if `time s t K N k` leaves
  `[s,t]` for `k > K`, use `u k := time s t K N (min k K)`. This is a usage remark, not a defect.
* Non-vacuity: auditor compiled `∀ (k : ℕ) (i : Fin 1), ‖((k/(k+1) : ℝ) : ℂ) * (1/2)‖ < 1`, i.e. a
  nonconstant bounded `u` with nonzero `ξ` satisfies `hu`; no degenerate `n = 0`, `ξ = 0`, or
  large-parameter requirement.

## (T4) `Uker_factor` — PASS

* Statement: `hL`, `u : ℕ → ℝ`, `t : ℝ`, `j k : ℕ`, `hu : ∀ i, ‖(u k) ξ i‖ < 1`, `ht : ∀ i, ‖t ξ i‖ < 1`;
  conclusion `Uker (u k) t (Uker (u (j+1)) (u k) A) = Uker (u (j+1)) t A` and both
  `Uker (u k) t ∘ Uker t (u k) = id`, `Uker t (u k) ∘ Uker (u k) t = id`. This is precisely the ticket's
  positive form of `U_{u_{j+1},u_k} = U_{u_k,t}^{-1} U_{u_{j+1},t}` (repair (A), pilot §9) with explicit
  two-sided inverse; no quantitative bound claimed, as the ticket requires.
* Side conditions: `hu`, `ht` are the norm-smallness conditions of the existing `Uker_self`/`Uker_comp`
  lemmas (the ticket asks for "the same conditions as in `Uker`'s existing lemmas"); no hypothesis on
  `u (j+1)`, consistent with `Uker_comp` having no start-time condition. No condition such as `u k ≤ t`
  is needed or imposed. Witness: same as (T3) with `t` in the same bounded range.

## Paper deltas

None required by this file: (T1)/(T2) are pure algebra and (T3)/(T4) are direct instances of accepted
(5.17)-kernel lemmas. The route-level replacement of Itô/(5.20)-(5.21) by the discrete grid identity is
the dispatcher's pilot decision (pilot §3/§9), not a statement change introduced here.

## Returned / blocked items

None.
