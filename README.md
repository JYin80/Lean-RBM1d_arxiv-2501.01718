# Lean formalization of Yau–Yin, "Delocalization of one-dimensional random band matrices"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Horng-Tzer Yau and Jun Yin, *Delocalization of one-dimensional random band matrices*,
> [arXiv:2501.01718](https://arxiv.org/abs/2501.01718).

The version of the paper that the Lean code follows is
[`paper/YauYin_RBM1D_Lean_version.pdf`](paper/YauYin_RBM1D_Lean_version.pdf) (source:
`paper/YauYin_RBM1D_Lean_version.tex`, `paper/Jun.bib`). Page, equation and theorem numbers in
`docs/PAPER-VS-LEAN.md` refer to this PDF.

## Main results

The five main theorems are stated in [`RBM1D/PaperMain.lean`](RBM1D/PaperMain.lean).

| Paper | Lean | What it says |
|---|---|---|
| Theorem 2.2 | `RBM.Paper.theorem2_2` | Delocalization, (2.10): with probability at least `1 − N^{−D}`, every eigenvector whose eigenvalue lies in `[−2+κ, 2−κ]` satisfies `\|ψ_k(x)\|² ≤ N^{−1+τ}` for all `x`. |
| Theorem 2.3 | `RBM.Paper.theorem2_3` | Local semicircle law: the entrywise bound (2.3), the block-averaged bound (2.4) and the bound for the normalized trace of `G(z) − m(z)`, each with probability at least `1 − N^{−D}`, for spectral parameters with `\|Re z\| ≤ 2−κ` and `N^{−1+τ} ≤ Im z ≤ 1`. |
| Theorem 2.4 | `RBM.Paper.theorem2_4` | Quantum diffusion, (2.6)–(2.9): high-probability bounds and expectation bounds for `Tr G E_a G^† E_b` and `Tr G E_a G E_b` around `W^{−1}(ξ/(1 − ξS^{(B)}))_{ab}`. |
| Theorem 2.5 | `RBM.Paper.theorem2_5` | Generalized quantum unique ergodicity, (2.12) and (2.13), for `0 < τ* < c/2` and energies with `\|E\| ≤ 2−κ`. |
| Theorem 2.6 | `RBM.Paper.theorem2_6` | Bulk universality, (2.18): at every energy with `\|E\| ≤ 2−κ`, the difference between the `k`-point correlation functions of the band matrix and of the GUE, rescaled around `E` and integrated against a smooth compactly supported test function, tends to 0. |

Theorems 2.2–2.5 have no hypotheses other than their parameters (sizes, exponents, spectral
parameters or energies, and the conditions on them). Theorem 2.6 has one more hypothesis,
`h51 : RBM.Gauss.LSY22' d`, described below. `docs/PAPER-VS-LEAN.md` §2 lists every difference
between a Lean statement and the printed one (for example, probability bounds are stated for the
complementary event, and spectral parameters and energies are sequences indexed by `N`).

## The model and the one external input

The matrix is the complex Gaussian block band matrix of the paper's §2.1: `L` blocks of size `W`,
entries independent up to Hermitian symmetry, complex Gaussian off the diagonal and real Gaussian on
the diagonal, with variance profile `S = S^{(B)} ⊗ S_W`, where `S^{(B)}_{ab} = 1/3` for blocks at
distance at most 1 on `Z_L`, and `W ≥ N^{1/2+c}` (2.2).

The proof uses exactly one result from the literature without proving it: the fixed-energy
universality of Dyson Brownian motion, [51, Theorem 2.2] (B. Landon, P. Sosoe, H.-T. Yau, *Fixed
energy universality of Dyson Brownian motion*, Adv. Math. 346 (2019)), in the form stated in
[arXiv:1609.09011v4](https://arxiv.org/abs/1609.09011v4), whose Remark after Theorem 2.2 covers the
complex Hermitian case. It enters only Theorem 2.6, as the explicit hypothesis `LSY22'`.
`docs/PAPER-VS-LEAN.md` §4 states it, explains how the Lean hypothesis matches it and lists what the
Lean proves around it.

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no declared `axiom`. The last command of `RBM1D.lean`,
`#assert_rbm_axioms` (defined in `RBM1D/Test/Axioms.lean`), checks this for every declaration in
the namespace `RBM`, and makes the build fail otherwise.

## Build and check

The toolchain is `leanprover/lean4:v4.34.0` (file `lean-toolchain`) with Mathlib `v4.34.0`.

```
lake exe cache get
lake build
lake build RBM1D.PaperMain
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` builds the whole library,
including the axiom check above. `lake build RBM1D.PaperMain` prints the hypothesis table of the
five theorems, their axioms, and the axioms of two lemmas on the spectral parameter `zStar` of the
compiled instances below. In the table each binder is classified as a size or exponent parameter
(`S`), a variable (`V`), a condition on the variable (`Q`), or another hypothesis (`H`); the command
fails unless the only `H` binder is `h51` in Theorem 2.6. The output ends with the following lines
(two long lists shortened to `...`); on a fresh build, build progress lines and linter output come
before them:

```
info: RBM1D/PaperMain.lean:368:0: Hypothesis table of Theorems 2.2–2.6 (classes S, V, Q, H):
RBM.Paper.theorem2_2: [(d, S), (κ, S), (hκ, S), (τ, S), (D, S), (hτ, S), (hD, S)]; (H): [] : []
RBM.Paper.theorem2_3: [(d, S),
 ...
 (hD, S)]; (H): [] : []
RBM.Paper.theorem2_4: [(d, S),
 ...
 (hD, S)]; (H): [] : []
RBM.Paper.theorem2_5: [(d, S), (κ, S), (τ, S), (hκ, S), (hτ0, S), (hτ, S), (E, V), (hE, Q)]; (H): [] : []
RBM.Paper.theorem2_6: [(d, S), (h51, H), (κ, S), (hκ, S)]; (H): [h51] : [Gauss.LSY22' #0]
info: RBM1D/PaperMain.lean:374:0: 'RBM.Paper.theorem2_2' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/PaperMain.lean:375:0: 'RBM.Paper.theorem2_3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/PaperMain.lean:376:0: 'RBM.Paper.theorem2_4' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/PaperMain.lean:377:0: 'RBM.Paper.theorem2_5' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/PaperMain.lean:378:0: 'RBM.Paper.theorem2_6' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/PaperMain.lean:379:0: 'RBM.Paper.NonVacuity.zStar_im_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM1D/PaperMain.lean:380:0: 'RBM.Paper.NonVacuity.zStar_im_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`RBM1D/PaperMain.lean` also contains compiled instances of all five theorems for a band matrix with
`W ≈ N^{3/4}` and `L ≈ N^{1/4} → ∞`. They show that the hypotheses of Theorems 2.2–2.5, and those
of Theorem 2.6 other than `h51`, can be satisfied. The instance of Theorem 2.6 takes `h51` as a
hypothesis; it does not show that `h51` holds.

## Map of the library

- `RBM1D/Analysis/`: the stretched-exponential tail functions (5.27)–(5.28) used in §5.3 and (7.12).
- `RBM1D/Defs/`: basic definitions: the variance profile `S = S^{(B)} ⊗ S_W` and the block projections `E_a` (2.5), distances and sums on `Z_L`, the semicircle Stieltjes transform `m` and the flow `z_t`, and stochastic domination `≺` (Definition 2.1).
- `RBM1D/Propagator/`: the propagator `Θ_ξ = (1 − ξS^{(B)})^{−1}`: its Fourier representation, closed form and decay (2.52), derivative (2.51), difference estimates (2.53)–(2.54), and the contour argument of Appendix B.
- `RBM1D/Loop/`: deterministic `G`-loops and `G`-chains (Definition 2.9, Appendix A): the primitive equation and its uniqueness, the tree representation (Lemma 3.4), Corollary 3.5, Ward's identity (Lemma 3.6), the sum-zero property (Lemma 3.10), the bound on `K^{(π)}` (Lemma 3.11), and the continuity estimate on loops (Lemma 5.1, §6).
- `RBM1D/Green/`: the entry estimates for the Green's function (Lemma 4.1) and the minor formulas (Lemma 4.2).
- `RBM1D/Hierarchy/`: the loop hierarchy of §5: the dynamics of `L − K`, the evolution kernel (Definition 5.2, Lemmas 7.1–7.3), the fast decay property (§5.4), the sum-zero operator (Definition 5.12, Lemma 5.14), the six steps (2.73)–(2.80) of the proof of Theorem 2.21, and the GUE phase of §7.2.
- `RBM1D/Gauss/`: the Gaussian band matrix on an explicit probability space, and the probabilistic estimates for it: Gaussian integration by parts, large deviation estimates, fluctuation averaging (4.12), the operator norm bound, the discrete time grid that replaces the matrix Brownian motion (2.34) together with its stopping times and martingale bounds, and Lemmas 5.9, 5.10, 5.14 and the steps of Theorem 2.21 for this model.
- `RBM1D/EnergyN/`: the same results with an energy that may depend on `N`, with constants chosen independently of the energy; this gives the forms of Theorems 2.2–2.5 that are uniform over `|E| ≤ 2−κ`.
- `RBM1D/Flow/`: the flow bookkeeping (the scale `ℓ_t` of (2.59) and the time grid `1 − s_k = W^{−kτ'}` of §2.7), Lemmas 2.18–2.20 from Theorem 2.21, Theorems 2.3 and 2.4 from these lemmas (§2.6), and the proof of Theorem 2.6: the Ornstein–Uhlenbeck flow, the Green's function comparison (2.23)–(2.25), the free convolution, eigenvalue interlacing and Weyl's inequality, Step 1 with the input [51], and Steps 2–3.
- `RBM1D/Test/`: the axiom check `#assert_rbm_axioms`.
- `RBM1D/Delocalization.lean`: the spectral bound (2.10), `|ψ_k(x)|² ≤ η · Im G_xx(λ_k + iη)`, and the passage from a Green's function bound to eigenvector delocalization.
- `RBM1D/PaperMain.lean`: Theorems 2.2–2.6 in final form, their compiled instances, the hypothesis table and the axiom prints.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail:
§1 what is proved (the model and the five theorems with their hypotheses); §2 every difference
between the Lean statements and the printed ones; §3 uniformity in `(W, L)`; §4 the external input
[51]; §5 where the Lean proof takes a different route from the paper (for example, a discrete time
grid in place of the matrix Brownian motion, and internal proofs in place of cited results other
than [51]).

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Paper: Horng-Tzer Yau and Jun Yin. Lean formalization: Jun Yin.
