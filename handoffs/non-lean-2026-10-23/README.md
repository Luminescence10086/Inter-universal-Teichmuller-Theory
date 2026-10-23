# 非 Lean 交付包（N01–N16）

本目录是 `handoffs/non-lean-task-catalog-2026-10-23.md` 的执行结果。每一项一个子目录 `Nxx/`，
内含 `SUMMARY.md`、任务卡要求的主体文件、`delivery.json`（真实 SHA256、`status` 五选一、固定 commit）。

## 一次跑完全部校验

```powershell
py -3 handoffs\non-lean-2026-10-23\N16\check_deliveries.py --selftest --json-out report.json
```
退出码 `0` 表示 16 项全部满足契约（键齐全、路径不逃逸、**哈希逐条按盘上重算一致**、状态取值合法、布尔旗标全 false、
没有出现被禁止的声明）。`--selftest` 还会用五个坏夹具证明检查器**会拒绝**坏输入。

## 各任务一句话

| 任务 | status | 一句话 |
|---|---|---|
| N01 | STATIC_COMPLETE | 官方 7-20 版与工程在用的 7-16 版**不是同一字节、也不是同一版本**（差 2 处文本：日期行、致谢段人名与断行）；缓存与 ncatlab 镜像字节相同 |
| N02 | STATIC_COMPLETE | 9 项争议矩阵；LANA 直引两处确认"没有 (9-1) 的证明""无共识"；Scholze–Stix/Joshi/Dupuy–Hilado 内容标 `SECONDARY_DIGEST`（本地无原文） |
| N03 | STATIC_COMPLETE | (9-1) 的量词与类型规格：`∃ S, etaAnab ι S = etaQ D`，**不是**全族不变；9 条义务，O1 的见证不存在 |
| N04 | PARTIAL | 系数环/order/分解/有限商签名摘录；仓库里**没有** `Finite (Tensor …)` 定义，有限商参考格 `UNRESOLVED`；并记录了 INPUT_DRIFT（点名的 `Arithmetic.lean` 不含所需内容） |
| N05 | STATIC_COMPLETE | 11 行保持台账（7 条原文 + 4 条源码）；`shared_finite_quotient` **全部** `UNRESOLVED`；引文经独立校验器逐条核对（`verify_N05.py` → `ALL_QUOTES_VERIFIED`） |
| N06 | STATIC_COMPLETE | 10 行归一化台账；最要紧三条：两套 pilot 之间缺常数 `c`、局部→全局缺权重 `w_v`、两套 log 之间**没有桥** |
| N07 | PARTIAL | 7 步执行链与四层区分；`out` 是**裸字段**，`realisation` 只给包含；缺的那条箭头就是"从 (ι,S) 到区域" |
| N08 | STATIC_COMPLETE | 5 条待证引理；**L2 的失败例**说明 `n≥2` 时共同容器一般**不是** `λ·O` 形 |
| N09 | EXPERIMENTAL | 有限搜索器；单因子模型结构性地给不出"共同容器"正例，`Z/9×Z/9` 有；"只测 F_p 标量"的回归例触发 |
| N10 | EXPERIMENTAL | 四个有限模型；M1 证明 `∃` 与 `∀` 可一个 SAT 一个 UNSAT；M2b 给出"各自可满足、联合不可满足"；M3 说明未知关系必须留 UNKNOWN |
| N11 | EXPERIMENTAL | 两张工具设计卡（hull 审计器、达到–证书二分器）+ 6 次检索的先前工作记录；卡 2 依赖卡 1 |
| N12 | STATIC_COMPLETE | 只记上次未覆盖的 7 项增量；发现 `MR9Plan.md` 的 pin 文本与 `lakefile.toml` **不一致** |
| N13 | STATIC_COMPLETE | 6 张风险卡 + 1 项"已核无问题"；最要紧：`reading ≠ 0` 被写成"非扭"、`exponent_determined` 的假设在发散探针处自动成立、`TransitionCompatibility.lean:634-637` 与 `593-596` 重复 |
| N14 | STATIC_COMPLETE | 21 项收据分级：6 项 `SUPPORTED`、6 项 `INSUFFICIENT`、2 项 `STALE_HASH`、7 项 `MISSING` |
| N15 | STATIC_COMPLETE | 37 行索引 + 37 节点/边图（每条边带证据路径）+ 12 条文档修改建议（只提不改） |
| N16 | STATIC_COMPLETE | 独立静态检查器 + 五个坏夹具的自检；全包 16/16 干净 |

## 三条总体结论（都在上面的目录里有证据，不是概括出来的）

1. **核心缺口没有被这批工作填上**：`out` 仍然没有构造（N07），有限商与真实系数环没有接上（N04/N08），
   两套 log 之间没有比较映射（N06-10）。这三个都是**结构性**缺口，不是"再算一算"能补的。
2. **编辑器证据比声明弱得多**：21 项里只有 6 项的证据真正指向本文件（N14）；W9/W10 的抓取甚至早于其源码修改。
3. **本工程此前两处错误已被指出并有反例**：把"全族不变"当成 (9-1) 的必要条件（N10 的 M1、N03 的 O5），
   以及把"读数非零"当成"非扭"（N13 的 C1）。

## 边界
本包**不**运行 Lean/Lake、**不**做编辑器取证、**不**改主线源码/配置/旧收据/GAP、**不**触碰 `fact-tree/registry.json`；
核心 GAP 全部保持 OPEN。静态交付完成不表示所研究的数学命题成立。
