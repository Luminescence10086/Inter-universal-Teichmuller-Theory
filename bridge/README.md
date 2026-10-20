# 基域 Q_p 工具与整合接口

本工程整合 73 条目录声明：层梯 21、联合可容许性 14、槽位作用 15、加权账本 14、组合接口 9。实际 IUT 对象尚未实现，Corollary 3.12 与 abc 尚未证明。

`Integration.lean` 的两个保账 iff 区分“每个坐标非零”与“允许零坐标”：前者要求权重不变和总估值预算为零，后者要求每槽加权预算为零。另补完整的逐槽交换判据、固定层边际 iff，以及明确假设非空的唯一层定理。详细前提与筛选依据见 [整合报告](../research/round8-integration.md)。

## 调用

```powershell
python -X utf8 tools/verify.py
python -X utf8 tools/query_integrated.py combined
python -X utf8 tools/query_integrated.py combined --deep
```

从仓库根目录调用统一入口：

```powershell
python -X utf8 tools/forest.py query combined
python -X utf8 tools/forest.py refresh --deep
python -X utf8 tools/bridge.py
python -X utf8 tools/semantic_lock.py
```

事实树的机器入口是 `fact-tree/facts.json`；全局入口为上级的 `fact-tree/catalogue.md`。`local-field → bridge` 使用实际同工具链 import。与主工程的合同仅比较接口，不转移证明。

## 验证

标准 `tools/verify.py` 委托 `verify_integrated.py`，保持原输出目录。schema-3 收据绑定源码/配置/验证工具集合、local-field 源码与外部 checkout 身份、实际导入编译产物与现存 sidecar、Lean/Lake 程序，以及每份源文件和 EditorCheck 的真实观察。完整检查期间输入变化则拒绝准入；原工程的 schema-2 收据不适用于本工程。

实际 VS Code 第八轮观察包括五份源文件匹配位置的 `No goals`，以及入口的 146 条 information、0 error、0 warning。证据见 `verification/vscode-observation-round8.txt` 与收据；最终准入状态由完整 verifier 产出的 facts.json 核定。CLI 成功本身不能替代编辑器验收。

显式、非类型类的 Prop 前提由 `tools/Binders.lean` 报告并与目录核对。允许的传递公理仅 `propext`、`Classical.choice`、`Quot.sound`。输入/运行快照发现普通漂移；收据不是防伪证明。

## 范围

- 层梯随指标严格反单调；`cost_exact` 仅证明集合像等式，没有体积或代价函数。
- 固定任意目标层都可矩形化；不等于证明映射保持该目标层本身。
- 逐槽交换判据不排除混槽映射。已给出可逆、非对角且与交换置换相容的实例，但未证明它保持其他区域或账本。
- 权重 `(1,1,2,1)` 是手选测试数据；范数乘积身份只涉及无权总账本，未定义测度或 Arakelov 量。
- 当前检索未定位可直接调用的 p-adic log 接口；这不构成无法实现该接口的证明。实际 log-image 身份仍是开放工作。

Lean 使用 `leanprover/lean4:v4.34.0-rc2`；固定 Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`。路径依赖由 manifest 和 local-field/external-lock.json 指定。主工程 Lean 4.34.0 的证明不跨版本导入。
