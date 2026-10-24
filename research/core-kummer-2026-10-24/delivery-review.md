# 2026-10-24 提交复验

审查对象：`origin/delivery/round2-2026-10-23`，`53f6062edeb6563e0a5e357f558f51502eb94403`。
交付分支保存交接材料；实现分属六个分支。没有合并、切换主工作区分支或改正式 pin/receipt/registry。

`check_delivery.py` 只读取固定提交的 Git blobs，不执行交付者脚本。六组 HEAD、变更范围、工作区变更文件字节匹配；53 份声明日志的 SHA256 和字节数（提供时）匹配。P0 的范围按 previous_head_commit 比较；E3 的 no-change 指本轮未追加代码，不表示相对最早基线没有差异。机器结果见 `delivery-object-check.json`。

| 任务 | 实现 HEAD | 本轮独立复验 | 结论边界 |
|---|---|---|---|
| P0 | eff68757c84f3183bb0f8bed240a12dab2bc4039 | 专属入口 14/14，退出 0，28.0s | 修复前轮两条反例；人工步骤不能变成 PASS；未做六分支集成 |
| E1 | 24f42c645ba6ec61a693926d7956268e955a5b15 | 快速入口 7/7，退出 0，总耗时 79.2s，期限 120s | 解决此前输出通过但进程未按期退出的问题；本轮未重复完整变异矩阵 |
| E2 | 7d3b66d25a5de9aaa4083d99b964fad65fa16ff4 | HEAD 与前轮独立通过版本一致；本轮核字节与日志 | 沿用前轮 9 项回归；非本轮重跑 |
| E3 | 6707684c8b6d7d521bb4cc803bc9a83ab0f0fb47 | HEAD 与前轮独立通过版本一致；本轮核字节与日志 | 沿用前轮第一阶段 6 项；闭包不全仍 WITHHELD |
| M1 | 80967748f03e0545834d1cae3ffcfe4bcc7c4dac | 源文件重建及 Axioms.lean，warningAsError，均退出 0 | 一般整数张成判据修复完成；编辑器准入另记，不从 CLI 推断 |
| M2 | e0b5294a3ef86674b14ccf18eb30949854752374 | 源文件重建及 Axioms.lean，warningAsError，均退出 0 | 任意坐标子集乘积的最小性修复完成；编辑器准入另记 |

M1 通过有限整数线性组合定义 `MemDiffSpanOn`，由实际差分生成元条件推出一般条件，反向用 {0,2,3} 的例子区分。M2 的 `hull_least_coordinateProduct` 对 `Set.pi univ S` 量化，并由通用坐标包络最小性推出。二者依旧没有实例化原始 IUT 的允许输出/全局误差预算。

注意事项：

- 交付 README 的 M2 完整 SHA 有一处 `14ecf`/`14ccf` 笔误；bundle 与真实 HEAD 一致，应以本表为准。
- E1 可选 `--reuse-probes` 复用调用方 JSON 的 probe 结果；其静态 repo_witness 不覆盖执行器自身及所有探针实现/环境。因此只适用于受信任缓存，不能充当独立验收证据。本轮直接执行探针，没有使用该缓存。此处记录信任边界，不声称已复现新的必需回归失败。
- 作者环境中的 sandbox/mkdir 修补和作者通过日志不算本轮独立重跑。本轮 P0/E1 在正常本机 Python 直接运行，无交付 shim。
- Lean 公理报告只允许 `propext`, `Classical.choice`, `Quot.sound`；不等于实现了 IUT 的原始几何。

本轮日志：`p0-replay.log`, `e1-replay.log`, `m1-source-replay.log`, `m1-axioms-replay.log`, `m2-source-replay.log`, `m2-axioms-replay.log`。实际退出码已在执行工具返回中确认。编辑器观察有则写入 `editor/`，未观察的项目维持候选，不新增正式准入。
