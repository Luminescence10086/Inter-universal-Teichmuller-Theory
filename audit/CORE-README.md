# core.py — 四件套组合成的单一入口

## 一句话

`python -B audit/core.py --bundle <bundle.json> --task <ID> --repo <checkout>`
把已交付的四件审计工具串成**一个判定**，并补上任何单件都做不到的两项检查。

## 组合了什么

| 阶段 | 工具 | 作用 |
|---|---|---|
| `acceptance` | `audit/acceptance/run.py` | bundle schema、冻结范围、逐用例重放（P0） |
| `impact` | `audit/affected.py` | 该提交范围作废了哪些收据/节点/合同（E2） |
| `gates` | `audit/mutation_harness.py` | 门禁是否仍抓得住它自称抓得住的变异（E1） |
| `dependency` | `audit/tcb_manifest.py` | 保守的依赖/pin 审查（E3） |

优先使用**目标检出自己的**那份工具；缺失时退回本检出并在判定里注明，绝不假装审了别处。

## 组合带来的两项新检查

1. **跨阶段矛盾**：`acceptance` 判定 PASS，但同一 bundle 的 base..head 在 `impact` 里作废了
   收据（或留下未决成员）→ 整体 **FAIL**。收据正是验收所依赖的东西，"已验收"与"它自己
   把收据作废"不能同时为真。
2. **影响面自相矛盾**：`impact` 报告"发现新增 snapshot 成员"，却"0 收据作废、0 未决" →
   **FAIL**（内部不一致）。成员判定本身交给 E2 修好后的 production snapshot 函数，
   组合器不重写 glob，也不靠路径后缀猜。

## 判定代数

任一必需阶段 FAIL → **FAIL**；无 FAIL 但有 INCOMPLETE（含人工步骤）→ **INCOMPLETE**；
全部 PASS → **PASS**。不做多数表决，`INCOMPLETE` 永不四舍五入成 `PASS`。
`dependency` 里"闭包不完整、删 pin 提案被扣留"是**预期状态**，不阻断；但
"读了却没 pin"（`under_pinned > 0`）是真缺口 → FAIL。

## 输出

`core-verdict.json`（每阶段的 status/detail/data、失败阶段、跨阶段项、跳过阶段）＋一页摘要。
退出码：`0` 仅当 PASS。`mathematical_admission` 恒为 `false`：工程阶段不能授予数学准入。

## 三种用法

```text
# 1) 审一个交付包（作者/复核者的主用法）
python -B audit/core.py --bundle <bundle.json> --task E1 --repo <checkout>

# 2) 自审这个检出的审计栈整体是否自洽（整合分支/合并前用）
python -B audit/core.py --self-audit --repo .

# 3) 只跑组合逻辑自测
python -B audit/core.py --self-test
```

`--self-audit` 把 acceptance 换成"本检出的启动器 10 项冻结用例"，impact 的区间取
"契约基线 → HEAD"，其余两阶段不变。它回答的是"这个检出的审计栈还能互相印证吗"，
不是"某个 PR 能否合并"。

## 已实测

```text
python -B audit/core.py --self-test            → 12/12 composition cases ok
python -B audit/core.py --self-audit --repo .  → verdict PASS (exit 0)
  acceptance  PASS  launcher self-cases pass on this checkout
  impact      PASS  16 changed, 0 receipt(s) voided, 0 new snapshot member(s), membership decided
  gates       PASS  every claimed catch held and the negative control stayed quiet
  dependency  PASS  no read-but-unpinned input; removal proposals withheld where closure incomplete
```

同时实测了两类"组合器该拒绝"的情形：对过期 bundle（检出 HEAD 已前移）acceptance 判
FAIL；对仍用旧版 `affected.py`（无成员判定）的检出，impact 判 INCOMPLETE 而不是放行。

覆盖：全 PASS→PASS；任一 FAIL→FAIL；INCOMPLETE 不升级；验收 PASS 却作废收据→FAIL；
影响面内部矛盾→FAIL；成员未决→INCOMPLETE；读而未 pin→FAIL；提案被扣留→不阻断；
四件工具存在且 `--help` 可用。

## 边界

- 只做组合与一致性问题，不做代码审查，不改 pin/收据/fact-tree/Lean 源。
- 阶段各自的语义原样保留；本工具只拒绝用一个漂亮的词把它们盖住。
- 目标检出若仍是旧版 `affected.py`（无成员判定），`impact` 阶段会报 INCOMPLETE 而非放行。
