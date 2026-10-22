# dsh 组合器验收：暂不通过

复核 `audit/core.py`，SHA-256 `284446ba5ececd0c39a248bdff00d2b1fcc46ef31e00cb99bbbbedd743792d65`。原自测 12/12 通过；独立的小规模故障注入仍复现三类误放行。

1. **空报告误放行**：`stage_dependency` 对 `[]` 与 `{}` 都判 PASS。缺少依赖证据应 INCOMPLETE，而不能默认为零缺口。
2. **忽略实际退出码**：dependency 与 gates 的进程 exit=17、stdout 保留成功 JSON，仍判 PASS。需检查进程状态及结构化状态的一致性；dependency 合法的 exit=3 应按其不完整闭包协议单独处理。
3. **跳过必需阶段仍总 PASS**：只留下 acceptance PASS、跳过其他三阶段，也返回总 PASS 与 exit=0。部分执行应显式为 INCOMPLETE，或使用区别于四阶段总验收的状态。现有自测恰恰要求该误放行行为，需一并修改。

值得保留：统一入口、分阶段报告、跨阶段一致性检查思路，以及 `mathematical_admission=false` 的边界。修复上述问题前不宜将其总 PASS 用作验收门禁。

复现脚本 `reviews/tool-round/dsh/review_core.py`；原始报告与结果 `reviews/tool-round/dsh/`。这属于 Python 工程验收，不是数学命题。后续修复只需重放这些小输入与原自测，无需重跑整套 Lean。本轮两个数学工具不依赖此组合器。
