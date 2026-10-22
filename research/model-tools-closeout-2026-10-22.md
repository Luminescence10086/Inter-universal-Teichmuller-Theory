# 两条工具路径本轮交付

统一入口：`model-tools/run.py`。说明和输入格式位于 `model-tools/README.md`、`model-tools/schemas/`。源码与证书身份在 `model-tools/delivery.json`。

## 已完成的工具功能

- **包络代价计算器**：输入素数、有限商环截断指数、坐标阈值及有限置换族；计算包络阈值、逐坐标达到最小值的见证、精确基数指数，并生成最小性/计数的 Lean 证书。请求扩大预算时要求族中含恒等置换；缺少此条件时可仅计算包络，扩大预算为 null。
- **允许域保账检查器**：输入整数权重、置换、标量估值和有限估值轮廓族；自动构造双向整数张成证书，分别检查实际非零 Q_p 元组上的保账与域保持。失败时产生实际 p 的整数幂元组及 Lean 反例，账本数值亦包含在证明中。缺少域输入返回 INSUFFICIENT。
- **共享核验入口**：固定组件和 Lake 目标，重算结果与证书绑定，实际构建辅助模块并调用 Lean，检查零 warning/error、公理白名单及源文件前后身份。超时有界，失败不能升级为 VERIFIED。

运行示例（主工作区根目录，输出目录须全新）：

```powershell
python model-tools/run.py hull --input model-tools/examples/hull-swap.json --out reviews/my-hull
python model-tools/run.py ledger --input model-tools/examples/ledger-two-profiles.json --out reviews/my-ledger
```

工程依赖同一机器上的 `D:/iut-wt/m1`、`D:/iut-wt/m2` 候选工程及其固定本地依赖；当前不是任意机器可直接安装的发行包。

## 核验范围

Python 工程检查：runner 10 项、ledger 8 项、hull 5 项通过。这些测试不代替数学证明。

代表证书实际经过 Lean CLI 和公理检查：三循环包络、2/3/4 示例的包络部分、无恒等置换的包络；最新 ledger 协议下的三循环反例、正例、保账但不保持域、整数生成元不是实际轮廓差四类。具体输入、定理名及 SHA-256 见 delivery.json；原始输出在 `reviews/tool-round/`。

收尾额外修复：把返回的 base_equation、image_profiles 及反例的实际账本数值纳入 Lean 证明；移除未形式化的列变换矩阵公开输出；将 witness_values 加入生产定理白名单。协议测试直接使用生产配置，避免测试配置掩盖遗漏。

## 未完成与边界

`GAP-tool-round-editor.md` 仍 OPEN：未完成用户要求的实际 VS Code 零错误/零警告验收。本轮新增结果没有正式 fact-tree 准入；CLI 的 VERIFIED 只表示对应证书已经过命令行核验。

本轮构建的是有限模型及有限估值轮廓域的可调用工具。没有构造真实 IUT admissible region、Theta-link 或 log-volume；没有关闭既有 IUT gaps，也没有证明 Corollary 3.12 或 abc。未声称学术新颖性。

dsh 组合器复核见 `research/dsh-core-review-2026-10-22.md`。本轮未修改其源码。
