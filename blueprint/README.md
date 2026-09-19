# Blueprint

依赖图 / 蓝图，对照论文编号。绿色节点 = 已在 Lean 中证明（`\leanok`）。

渲染需要 `leanblueprint`（Python）和 LaTeX：

```bash
pip install leanblueprint
cd ~/Lean_proof/RBM1D
leanblueprint checkdecls   # 校验每个 \lean{} 都能解析到真实声明
leanblueprint web          # 生成 docs/，含依赖图
leanblueprint pdf
```

未安装该工具时，`content.tex` 仍是可读的纯 LaTeX 源文件。
