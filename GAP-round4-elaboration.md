# 第四轮 elaboration 事件记录

日期：2026-10-19。类型：工程检查事件；状态：**已解决**。这不是已经关闭的 IUT 数学 gap，G01–G06 仍开放。

在 `integerIdealImage_eq_pow_ball` 的正向证明中，多次检查停在 `Ideal.mem_span_singleton`：理想元素从集合 image 的 witness 解构后，Lean 将 `ℤ_[p]` 的底层类型显露为 `{x : ℚ_[p] // ‖x‖ ≤ 1}`。自动推断环类型时试图为这个显式子类型寻找 `CommSemiring`，而不是使用已安装的 `ℤ_[p]` 环实例。

失败记录位于 `local-field/verification/round4-attempt1.json` 至 `round4-attempt4.json`。第二次尝试还包含一处定位不够精确的补丁错误，随即移除；它不构成数学反例。首次记录程序还在打印 Unicode 时遇到 GBK 编码错误；Lean 诊断已先保存到 JSON，之后统一使用 UTF-8 输出。

最终修复显式指定环参数：

```lean
(Ideal.mem_span_singleton (α := ℤ_[p])).mp hyIdeal
```

并通过已证范数判别构造理想成员资格，显式使用 `PadicInt.coe_mul`、`coe_pow`、`coe_natCast` 传输等式，不依赖对半可约类型的偶然 rewrite 行为。

关闭依据：`round4-attempt5.json` 中，当时包含十个定理的完整 `Filtration.lean` 检查退出码为 0、stdout/stderr 均为空。随后新增声明仍须通过本轮最终 CLI 与 VS Code 检查才能准入；本记录不代替该准入。
