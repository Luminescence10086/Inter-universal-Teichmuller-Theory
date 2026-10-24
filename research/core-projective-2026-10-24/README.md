# 不同 q 标尺下的交叉赋值与标签刚性

本轮数学入口：`candidates/core-kummer/Boundary/ProjectiveComparison.lean`，导入前轮已验收的 `Boundary.AnchoredComparison`。没有修改任何旧数学模块、配置、registry 或原有脏文件。

与前轮相比，核心改进是去掉交叉关系所需的“q、r 同赋值”假设，并允许全塔每层有单位修正。得到的是相对关系；恢复绝对主格仍需要独立校准。下面各数学陈述对应源码的实际声明，不主张其文献原创性，也不把局部工具称为已构造原始 IUT 箭头。

## 1. 不需要同赋值标尺的消元

固定实际整数值赋值 `v : Valuation K ℤᵐ⁰`，记 `w(z)=WithZero.log(v(z))`，这是乘法赋值的整数指数，不是实对数，也不能与通常加法 ord 的符号约定混用。

对实际单位 x、y、q、r，假设同一实际连续 H¹ 类型中有：

```text
κ_N(x^m) = κ_N(c) * κ_N(y^m)^u
κ_N(q)   = κ_N(d) * κ_N(r)^u
v(c)=v(d)=1
```

不假设 `w(q)=w(r)`。`cross_determinant_dvd_of_classes` 证明

```text
N | m * (w(r)*w(x) - w(q)*w(y)).
```

这个结论来自实际 Kummer 核定理和整数整除消元，保留 c、d 的 Kummer 类，未假设它们为平凡类。若独立界满足
`|m*(w(r)*w(x)-w(q)*w(y))| < N` 且 m≠0，有限层定理给出

```text
w(r)*w(x) = w(q)*w(y).
```

`cross_determinant_eq_zero_of_tower` 在所有 `ell^k` 层得到同一交叉等式，无须事先给有限差界。每层 u、c、d 可以改变，不要求所选见证跨层相容；但同一层的值比较和标尺比较必须使用同一个 u。这个来源要求仍未构造。

## 2. 比绝对主格更早可以判定的标签

对 `x=q^(i²)`、`y=r^(j²)`，当 `w(q)`、`w(r)` 均非零时，交叉等式已经推出 `i=j`，即使两根标尺的赋值不同。对应声明为 `quadratic_labels_eq_of_cross_determinant`。

本轮也给出实际有限精度消费者 `quadratic_labels_eq_of_finite_comparison`：若 `i,j≤J`，则独立的交叉差界是

```text
|m*(w(r)*w(q^(i²))-w(q)*w(r^(j²)))|
    ≤ m*|w(q)|*|w(r)|*J².
```

所以在 `N > m*|w(q)|*|w(r)|*J²` 层取得上述共同幂比较，即可证明 `i=j`。归一化幂 m 仍显式保留，不能把 LGP 根与其 ell 次幂混同。

这是对原始 `lgpValue=qroot^(j²)` 形状的可用局部检验工具，不是对 `InitialThetaData`、Hodge theater 或实际允许标签置换的完整实例化。根单位修正已经可以在比较式 c、d 中容纳；若要把函数本身写作根单位乘 Gaussian 值，仍须在实际输入处验证对应单位/赋值关系。

## 3. 不能越过的绝对尺度边界

`principal_eq_of_calibrated_cross_determinant` 证明：另有 `w(q)=w(r)≠0` 时，交叉等式恢复 x、y 的实际主格相等。

`unequal_anchors_lose_absolute_scale` 给出严格负对照：取 x=q⁴、y=q，左右标尺也分别为 q⁴、q。在每个 `3^k` 层，两条共同幂比较都用指数4，4与该层数互素，交叉等式成立；若 w(q)≠0，实际主格依然不相等。两条类等式在此选取下是同一个已验证的等式。此声明不声称构造原始 theater 的自同构。

因此，当前已验证的是“相对交叉关系能控制二次标签”，并非“相对关系已经恢复绝对 log-volume”。具体剩余缺口见 `GAP-projective-to-absolute.md`。

## 4. 提交审查及倒推图接入

按用户要求，Luna 独立审查 `research/backward-paths`，并用 `git ls-remote` 实时确认远端与本地同为 `d3c5599668aa57c5c00244117abd26787fcd559e`。见 `backward-delivery-review.md`。没有合并或切换分支。

审查指出：P6 以 (9-1) 为输入，只给条件性推论；`EtaAlg.realisation` 的字段仅要求输出 adelic 且位于 hull，不构造原文允许的算法执行。主代理另读 `Iut/Wall/EtaAlg.lean:105-125,142-153,169-200` 核对了这些签名。该来源审查不是本轮 Lean 数学节点。

本轮工具最多接到倒推图的局部同步/标签检查，尚未接通：真实 η 执行来源、绝对 volume 校准、同一允许输出的全局界。不能据局部交叉关系或 P6 的编译成功标记 G0 已解决。

## 5. 验证与快速查询

9项声明已由父进程严格编译及导出，实际退出码均为0，仅使用 `propext`、`Classical.choice`、`Quot.sound`。实际 VS Code 验收证据单独保存在 `editor/`；只有零错误/零警告且达到最后一项声明后，新分片才可准入。准入状态以 `index.json` 为准。

本轮实际验收已完成：9条信息、0错误、0警告，核到第169行最后声明。分片状态为 `VERIFIED_LOCAL_SHARD`；9项选定声明、10个本地节点、7条本地依赖边、19条祖先事实引用边，递归引用2份祖先分片。生成后的哈希检查与准确类型查询均通过。

本轮索引沿 `parent_shard` 递归绑定所有祖先事实，并保留新节点对旧节点的引用边，避免将旧证明重复计为本轮新增。

```powershell
& 'C:\msys64\ucrt64\bin\python.exe' -B research/core-projective-2026-10-24/index.py --check
& 'C:\msys64\ucrt64\bin\python.exe' -B research/core-projective-2026-10-24/index.py --query quadratic_labels_eq_of_finite
```

这些命令不重跑 Lean；查询读取内核环境导出的类型与依赖。Corollary 3.12、原始核心来源 gap 和 abc 均保持 OPEN。
