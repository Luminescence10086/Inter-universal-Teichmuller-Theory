# 从真实 theta germ 推出 q 平移的类比较

本轮入口是 `candidates/core-kummer/Boundary/ThetaGermTransport.lean`。这次比较式来自真实定义的幂级数恒等式，不以“两个源类已经相等”为假设。范围是上游 `TateParameter.theta` 的 unsigned theta 级数在同一局部模型中的一次 q 平移；不是原始 Θ-link，也不重建 tempered fundamental group。

## 真实来源和移植范围

上游固定为 TateCurvesTheta commit `d1fba94861c886b671f4137ab35e24b7474c9e00`。逐字移植 `QParameter/Basic.lean`、`Theta/Basic.lean`、`Theta/Periodicity.lean`，并从上游 `Kummer/ThetaGerm.lean` 第1–233行抽取 `ThetaGermCore.lean`。后三个 germ 定义 `thetaGerm`、`thetaGermUnit` 等仍保持上游名称与定义体。抽取只替换一个 import 并补闭合 namespace，不包含整个原模块；Apache 2.0 作者头和许可证保留。

`port-source.json` 记录来源和候选的实际字节哈希；`port-build-exits.json` 及四份独立日志记录父进程依赖顺序严格编译，四项均退出0。未修改已有 lakefile、Mathlib 或旧证明文件。完整导入选择说明见 `import-audit.md`。

令

```text
G_u = thetaGerm(u) = Σ_n thetaTerm(u,n)*(1+X)^n
```

这只是定义的系数记法：源码实际使用每个系数的收敛和，而非把上式未经证明当作幂级数拓扑中的和。定义、常数项与收敛事实来自上述真实上游抽取。

## 1. 幂级数本身的生成元恒等式

`summable_germ_coefficient` 证明每个系数的双边加权和收敛。`thetaTerm_q_shift` 从三角指数公式证明逐项换标。再结合整数 binomial 系数递推，`thetaGerm_q_mul` 得到实际幂级数等式：

```text
C(q*u) * ((1+X) * G_(q*u)) = G_u.
```

证明逐个系数进行，使用已证明的可和性来分配和；没有从单个点值相等推断整个 germ 相等。

当 θ(u)≠0，`thetaGermUnit_q_mul` 给出真实单位等式：

```text
G_(q*u)^unit = (C(q*u)^unit * (1+X)^unit)^(-1) * G_u^unit.
```

`map_thetaGermUnit_q_mul` 将它送过任意乘法同态。`kummer_thetaGermUnit_q_mul` 进一步把实际幂级数单位映入 Fˣ，再送到实际连续 H¹ 的 Kummer 类，完整保留两个因子的类。

## 2. 约化限制：精确消去坐标，保留算术常数

`reducedGermHom` 是实际的复合：

```text
K[[X]]ˣ → Fˣ → H¹(Gal(Ω/F), μ_n(Ω))
                 → H¹(D_A, μ_n(κ(A))).
```

最后一个箭头是限制到真实分解群并用 `reduceMu` 约化系数。输入包括 k→F→Ω 的标量塔、常数及 residue 代数相容、A 包含幂级数像、X 的 residue 为0、所需代数性及根存在条件。整个计算在同一个分解群和同一系数作用上完成。

`reduced_coordinate_eq_one` 用真实 `decomposition_kummer` 将 `(1+X)` 专门化到1，从而消去它的约化限制类。`reduced_constant` 在常数嵌入相容条件下，把 `C(q*u)` 的类识别为实际算术 Kummer 类的 pullback。最终：

```text
R(G_(q*u)) = pullback(κ_n(q*u))^(-1) * R(G_u).
```

这是 `reduced_thetaGermUnit_q_mul` 的实际内容。q*u 没有被假设为 n 次幂、根单位或赋值单位，也没有被无条件置成平凡类。这条正向公式使用真实 specialization 方块；不消费前轮要求的源类相等假设。

## 3. 对算术主格的精确影响

独立取常数域上的 `v : Valuation K ℤᵐ⁰`，记 w 为乘法赋值的整数指数，区别于实对数和 X-adic 赋值。`exponent_theta_q_mul` 证明：

```text
w(θ(q*u)) = w(θ(u)) - w(q) - w(u).
```

`principal_eq_iff_zero_automorphy_exponent` 证明，在 θ(u)≠0 时：

```text
θ(q*u) • O_v = θ(u) • O_v   ↔   w(q)+w(u)=0.
```

因此本轮提供一个可调用的真实变换及主格保持判据。这里没有判定原始 IUT 有错：theta 的 automorphy 因子正是应被跟踪的数据；原论证是否在允许操作中正确运输它，还需实际来源构造。

## 4. 尚未证明的接入部分

本轮只交付一次 q 平移。完整整数作用、平方根参数下的 étale theta germ、原始 Hodge theater/Θ-link、跨标签/tensor/全局度量与允许 η 输出均没有因此构造。特别不能把 `G_(q*u)` 和 `G_u` 在同一 Laurent 模型中的关系，叫作原始跨 Θ-link 的比较。

下一步的具体目标见 `GAP-etale-germ-source.md`：对原始 `etaleTheta(U)=U*theta(-U²)` 的来源，验证乘法局部坐标的平方代换，并保留全部 automorphy 因子。已有点值公式可作核对目标，不能代替 germ 身份证明。旧核心 gap、Corollary 3.12、abc 仍保持 OPEN。

## 5. 验证与快速调用

18项选定声明严格 Lean 编译已由父进程观察到退出0；`lean-build.log` 的公理检查仅含 `propext`、`Classical.choice`、`Quot.sound`。移植来源和编译产物也被哈希绑定。实际 VS Code 的验收证据放在 `editor/`；只有达到最后声明、0错误、0警告后才正式准入。状态以 `index.json` 为准。

实际验收现已完成：18条信息、0错误、0警告，核到第254行最后声明。新分片为 `VERIFIED_LOCAL_SHARD`：18项选定声明、25个本地节点、42条本地依赖边、8条祖先事实引用边，引用3份祖先分片。生成后的 `--check` 和准确类型查询均通过。

```powershell
& 'C:\msys64\ucrt64\bin\python.exe' -B research/core-germ-2026-10-24/index.py --check
& 'C:\msys64\ucrt64\bin\python.exe' -B research/core-germ-2026-10-24/index.py --query reduced_thetaGermUnit_q_mul
```

查询读取内核环境导出的准确类型及依赖，不重跑 Lean。新分片递归引用既有祖先事实，未修改中央 registry。
