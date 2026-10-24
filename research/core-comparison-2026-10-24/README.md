# 用共同 q 标尺校准 Kummer 系数幂

本轮继续前轮真实 Laurent germ → 约化限制类 → 剩余域 Kummer 类 → 主格的边界，处理先前要求两端类逐字相等过强的问题。数学源码是 `candidates/core-kummer/Boundary/AnchoredComparison.lean`；它导入已验收的 `Boundary.Frontier`，没有修改前轮源码、配置或 registry。

下面只解释该源码实际证明的命题。不主张这些是文献中从未出现的新定理，也不主张它们已构造原始 IUT 的来源箭头。

## 有限层：允许单位修正和共同系数幂

取整数值乘法赋值 `v : Valuation K ℤᵐ⁰`，记 `w(z)=WithZero.log(v(z))`。这是整数指数，符号约定不应与通常的加法 ord 混用。设非零单位 `x,y,q,r,c,d : Kˣ`，归一化次数 `m ≠ 0`，并且：

- `w(q)=w(r)=E ≠ 0`；q、r 可以是不同元素。
- `v(c)=v(d)=1`；没有要求它们的有限层 Kummer 类为平凡类。
- 在同一实际连续 H¹ 类型、第 `N=m*n*|E|` 层，有同一个自然数指数 u，使
  `κ_N(x^m)=κ_N(c)*κ_N(y^m)^u` 及 `κ_N(q)=κ_N(d)*κ_N(r)^u`。
- 独立于类比较的有限界 `|w(x)-w(y)| < n`。

`principal_eq_of_unit_corrected_anchored_classes` 证明实际主格相等：

```text
x • v.valuationSubring = y • v.valuationSubring
```

证明先由实际 Kummer 核定理取得幂比见证。两个比较分别给出
`N | m*w(x)-u*m*w(y)`、`N | E-u*E`。消去共同 u 得
`N | m*E*(w(x)-w(y))`，再取消非零 m、E 的精度因子，得到
`n | w(x)-w(y)`。最后由严格有限界分离指数。

`N=m*n*|E|` 是已经证明充分的精度，不声称最小。u 不必假设可逆，所以此判据也可用于合法的互素系数幂这一子情形。标尺比较本身是额外的来源义务，不能由想要的主格相等反造。

## 全塔、负对照、标签界及分解群接入

`principal_eq_of_anchored_tower` 在全部 `ell^k` 层消去共同标尺的作用，不要求有限差界。每层 u 可以变化，也不要求选择的 u 彼此相容；但同一层必须用同一个 u 比较归一化值和标尺。该全塔版本目前采用无 c、d 修正的比较；带单位修正的版本本轮只在上述有限层判据中交付。

`unanchored_unit_power_fails` 是精确负对照：对任意 k，4 与 `3^k` 互素，并且
`κ_{3^k}(q^4)=κ_{3^k}(q)^4`，但当 `w(q)≠0` 时 q⁴ 与 q 的实际主格不相等。因而“存在互素系数幂比较”本身不足以恢复主格。这里形式化的是所列互素性、类等式及主格不等；没有额外声称已经构造跨 theater 的系数自同构。

`coefficientPower` 是在实际连续 H¹ 上由 `ContH1.map id (powMonoidHom u)` 定义的系数幂映射；`coefficientPower_eq_pow` 将它与 H¹ 的 u 次幂联系起来。这区别于把函数乘以一个 `Oˣ` 元素。

`quadratic_label_bound` 对真实代数形状 `q^(j²)` 证明：当 `i,j≤J` 时，

```text
|w(q^(i²))-w(q^(j²))| ≤ |w(q)|*J².
```

这给固定 q 和有限标签范围的显式独立界；源码没有假称已完成对整个 `InitialThetaData` 的 Lean 实例化，也没有给随初始数据变化的统一数值界。

`CoreAnchoredDecomposition.residue_kummer_pow_of_reduced_comparison` 接入真实的限制、`reduceMu`、`decompositionMap` 和 `decomposition_kummer`。它从约化限制类的幂比较反射出剩余域 Kummer 类的幂比较，依赖分解群到剩余域 Galois 群的真实满射；不假设 `reduceMu` 可逆。用于两个比较时仍须保留同一 u。

## 来源核查与尚缺的箭头

Luna 完成两份固定 commit 的只读报告：

- `source-transform-audit.md`：真实 theta 值变换、单个 germ 的 specialization、乘法修正因子的准确类型。
- `anchor-source-audit.md`：q-pilot、cyclotomic synchronization 与共同标尺最接近的实际签名；结构字段与来源构造分开记录。

本轮没有在所审源码找到一个从原始 IUT 执行构造出来、同时控制 theta 与 q 标尺的共同作用方块。`GAP-shared-anchor-source.md` 保持 OPEN。原始 tempered Pi 仍不在所审上游实现范围。此前 G01–G06、R-01–08 没有因此关闭；Corollary 3.12、abc 均未证明。

下一轮应直接核对：原始允许复合能否提供两个比较共享的系数作用，以及 q、r 在被运输后的同一个算术赋值上是否相等。若 theta 端与 q 端有两个独立的作用指数，本轮消元定理不能使用。不要再以包装同样假设的新结构代替这一步。

## 验证与快速调用

`execution.json` 记录父进程实际观察的严格 Lean 编译与导出退出码，`lean-build.log` 给出15项声明的公理检查；仅允许 `propext`、`Classical.choice`、`Quot.sound`。`editor/` 记录实际 VS Code 验收；只有观察到15项信息、零错误、零警告且哈希一致时才准入新的 fact-tree 分片。准入结果以 `index.json` 状态为准，不能由本说明代替。

本轮实际结果：父进程两阶段均退出0；VS Code 观察到15条信息、0错误、0警告，并核到第292行最后一项声明。新分片为 `VERIFIED_LOCAL_SHARD`：15项选定声明、20个本地节点、21条本地依赖边、33条祖先事实引用边。生成后的 `--check` 与实际类型查询均通过。

从仓库根目录快速检查或查询：

```powershell
& 'C:\msys64\ucrt64\bin\python.exe' -B research/core-comparison-2026-10-24/index.py --check
& 'C:\msys64\ucrt64\bin\python.exe' -B research/core-comparison-2026-10-24/index.py --query principal_eq_of_unit_corrected
```

检查不重新运行 Lean。查询返回内核环境导出的准确类型及依赖。新分片以哈希引用上一轮分片；祖先依赖另列 `ancestor_fact_edges`，没有把旧节点重复计为本轮的新证明。
