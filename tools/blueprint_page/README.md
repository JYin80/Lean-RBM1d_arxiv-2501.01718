# 蓝图总览网页生成器

原来由 Cowork（Claude）在云端运行并发布到 claude.ai 的 artifact。复制到仓库，供其他模型或本地使用。

依赖：`python3`、graphviz（`dot` 命令）。

```bash
cd tools/blueprint_page
python3 paper.py ../../blueprint/src/content.tex <定理数>   # 全文依赖图：paper.dot / paper.svg / papermap.html / chips.html
python3 build.py ../../blueprint/src/content.tex <定理数>   # 各章子图 g0–g3.svg 与最终页面 blueprint.html
```

定理数（完整口径）：

```bash
R='^\s*(@\[[^]]*\]\s*)?((private|protected|nonrec|noncomputable)\s+)*(theorem|lemma)\s'
git grep -hE "$R" HEAD -- 'RBM1D/*.lean' | wc -l
```

* 两个脚本都有**总数守恒守卫**：`content.tex` 里的定理环境数 ≠ 解析出的节点数就退出（防止标题含 `]` 等情况静默丢节点）。
* `paper.py` 顶部的 `STATUS_OVERRIDE`（把「Lean 证明依赖尚未卸掉的假设」的节点标蓝）与 `EXTRA`（论文里有、Lean 用矩路线替代的节点及其说明）是**手写的**，要随工单进度更新。
* 产出的 `blueprint.html` 引用同目录的 `paper.svg`、`g0.svg`–`g3.svg`，浏览器直接打开即可。
