#!/usr/bin/env bash
# 侦察本机 Mathlib 里那几个 API 的确切名字，写到 recon.txt。
cd "$(dirname "$0")" || exit 1
M=.lake/packages/mathlib/Mathlib
{
  echo "=== toolchain ==="; cat lean-toolchain 2>/dev/null; elan show 2>&1 | head -20
  echo; echo "=== mathlib rev ==="; git -C .lake/packages/mathlib rev-parse --short HEAD 2>&1
  echo; echo "=== Circulant.lean 全部声明 ==="
  grep -nE "^(@\[[^]]*\] )?(protected )?(noncomputable )?(theorem|lemma|def|abbrev|instance) " \
    "$M/LinearAlgebra/Matrix/Circulant.lean" 2>&1
  echo; echo "=== linftyOp 范数 ==="
  grep -rnE "(scoped )?(noncomputable )?(instance|theorem|lemma|def) [A-Za-z_.']*[Ll]inftyOp" "$M" 2>/dev/null | head -50
  echo; echo "=== Neumann / NormedRing.inverse ==="
  grep -rn "inverse_one_sub\|inverse_continuousAt\|tsum_geometric_of_norm_lt\|hasSum_geometric_of_norm_lt" "$M" 2>/dev/null | head -30
  echo; echo "=== Matrix 上的 Algebra/NormedAlgebra 实例 ==="
  grep -rn "instance.*Matrix.*Normed\|namespace Matrix" "$M/Analysis/Matrix.lean" 2>/dev/null | head -20
  ls "$M/Analysis/" 2>/dev/null | head -40
  echo; echo "=== ODE 唯一性 ==="
  grep -rn "theorem ODE_solution_unique" "$M" 2>/dev/null | head -10
} > recon.txt 2>&1
echo "wrote $(wc -l < recon.txt) lines to recon.txt"
