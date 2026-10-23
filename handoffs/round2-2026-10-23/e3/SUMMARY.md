# E3 交付摘要（TCB 依赖审查保守化 · 第二轮复核）

结论：**no-change**。分支 `round2/e3` HEAD `6707684c8b6d7d521bb4cc803bc9a83ab0f0fb47`（base `4841271858…`）已满足第一阶段 6 项必交用例；逐条核对未发现需要修改 `audit/tcb_manifest.py` 或 E3 测试的真实缺口，故无新提交。

| # | 必交用例 | 用例 id | 断言方向核对 |
|---|---|---|---|
| 1 | 子进程读 `decision.txt` | `E3.child_process_input` | 完整 fixture 先跑子进程 verifier，改 `decision.txt` 使退出码 0→1（证明是真判定输入）；`executed-program` 边界、`decision.txt` 只进 unclassified、不进 over_pinned、removed=[]、仍在 proposed_pin、CLI=4 ✓ |
| 2 | `import helper; helper.check(ROOT)` | `E3.qualified_sibling_input` | 同法证 `decision.txt` 为真输入；helper 被纳入闭包并报缺 pin；CLI≠0 且 JSON 不得声称干净完整 ✓ |
| 3 | 实际 bridge 绑定 | `E3.real_bridge_consumer_bindings` | pinned=36 冻结、WITHHELD、removed=[]、proposed_pin 仍 36 项，freshness/semantic_lock/bridge/DefinitionBodies.lean 全保留；semantic_lock、freshness 列入边界、lean-build 为已声明边界、over_pinned=[] ✓ |
| 4 | 简单直接 read 完整 fixture | `E3.simple_complete_read_control` | 闭包 complete、boundaries=[]、read_paths 精确、PROPOSED、withheld=false、CLI=0（未退化为一律 UNRESOLVED）✓ |
| 5 | "没找到 read" 只能是未分类 | 用例 1、5 | 不完整闭包下 `tools/spare.py`/`decision.txt` 记 unclassified、over_pinned=0、removed=[]；同类 fixture 去掉子进程边界后才允许删 pin（门禁非"一律拒绝"）✓ |
| 6 | 四类分别报告 | `E3.separate_input_dependency_runtime_toolchain` | categories 恰为 input/dependency/runtime/toolchain；Lean 源归 toolchain 且理由写明 import/build 图、非"只有 Python 在 hash"；runtime 含 lake；36 = consumed+unclassified+declared ✓ |

实测：`python -B -m unittest discover -s audit/tests -p "test_tcb*.py"` → 13 tests **OK，退出 0**，5.66 s（本轮 5.99 s 墙钟）。pin 侧零改动：`bridge/verification/checked-inputs.json` 36 项 schema 3，`git diff 4841271 HEAD -- bridge/verification/` 为空，proposal=WITHHELD、removed=0、无正式删 pin；bridge 闭包不完整（lean-build / unanalysed-entry / unreached-consumer），20 项 pin 仍为 unclassified。

环境注记：本沙箱下 `tempfile.mkdtemp`（POSIX 0o700）建出的目录不可再写入（`PermissionError WinError 5`），故首轮 11 项 fixture 全部环境性报错。用一个只把 `mkdtemp` 改成 0o777 的外壳 `harness_e3_tests.py` 重放同一选择集（不改、不跳过、不放宽任何断言），得到上述退出 0；宿主上直接用 `-m unittest discover` 即可复现。

未解决：① 20 项 bridge pin 仍无法分类，需第二阶段的"显式消费者清单 + 依赖边证据"才能收窄；② 用例 1/2 把"子进程/模块方法不可解析"这一当前实现分支写死（未来若真能完整解析，测试会误报失败，属过严而非漏检）；③ 本沙箱的 0o700 临时目录限制需外壳规避。
