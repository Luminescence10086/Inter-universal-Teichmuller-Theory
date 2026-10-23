import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N10 = ROOT / 'handoffs/non-lean-2026-10-23/N10'
res = json.loads((N10 / 'results.json').read_text(encoding='utf-8-sig'))


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


models = {m['name']: m for m in res['models']}
summary = f"""# N10 — 相关选择的有限约束实验

状态：`EXPERIMENTAL`（有限模型里的穷举结果；不是任何原始命题的证明或反证）

## 运行
```powershell
py -3 handoffs\\non-lean-2026-10-23\\N10\\constraints.py     # 写 results.json，瞬时完成
```
四个模型都小到可以把真值表打全，评审可以手算复核。无外部求解器，因此不存在"求解器说 UNSAT"这类黑箱证据。

## 四个模型的实际结果
| 模型 | 结论 | 说明 |
|---|---|---|
| M1 单族 | `E1 = SAT`、`E2 = UNSAT` | **存在某个选择使读数等于 q** 成立，而 **所有选择都等于 q** 不成立 |
| M2 两族（有交集） | `joint = SAT` | 对照组：证人可以重合 |
| M2b 两族（证人互斥） | `joint = UNSAT` | **每个要求各自可满足，但不能用同一个 `S` 同时满足** |
| M3 未知关系 | 已知约束下 7 个赋值；额外假设独立性后只剩 6 个 | 额外假设**无证据地砍掉**了一个满足全部已知约束的赋值 |

## 三条要点
1. **M1 就是本工程此前错误的形状**：把 `E2`（全族不变）当成 `(9-1)`（`E1`，存在型）的必要条件。
   有限模型里两者可以一个 SAT 一个 UNSAT，所以写成必要条件是错的。
2. **M2b 是"联合见证"谬误的最小实例**：`∃S` 对每个要求分别成立，不等于存在一个 `S` 同时成立。
   这正是 N07 里 `ι`、`S`、`τ` 不能"分别存在就拼起来"的原因。
3. **M3 说明未知关系必须留成 UNKNOWN**：把未知关系默认成独立，会把可行解砍掉；
   N05 的 `shared_finite_quotient` 在每条原文里都是 `UNRESOLVED`，所以这里不能默认。

## 边界（必须一起读）
- 有限不可满足**不**构成原始 IUT 不可满足的证明；反过来，有限可满足也不证明原始情形可满足。
- 四个模型都是玩具：与 `Ind3 D`、`logVol`、`R^ss` 没有已建立的对应（`UNRESOLVED`）。
- 约束来源映射写在 `results.json` 的 `constraint_provenance`：`E2` 明确标注"**不在**原文中"，是本工程此前的错误加强。
"""
(N10 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md',
           'handoffs/non-lean-2026-10-23/N03/obligations.csv',
           'handoffs/non-lean-2026-10-23/N05/evidence.csv',
           'handoffs/non-lean-2026-10-23/N07/witness-contract.csv'] if (ROOT / p).exists()]
outputs = [{'path': rel(N10 / n), 'sha256': sha(N10 / n)} for n in
           ['SUMMARY.md', 'constraints.py', 'results.json', 'make_N10_delivery.py']]

delivery = {
    'task_id': 'N10',
    'status': 'EXPERIMENTAL',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N10/results.json', 'line_or_page': "models[2] (M2b)",
         'supports': 'the joint-unsatisfiability while both families are individually satisfiable'},
        {'path': 'handoffs/non-lean-2026-10-23/N10/results.json', 'line_or_page': "models[0] (M1)",
         'supports': 'E1 SAT and E2 UNSAT on the same family, i.e. the existential form does not imply invariance'},
    ],
    'commands_run': ['py -3 handoffs/non-lean-2026-10-23/N10/constraints.py  -> results.json'],
    'new_hypotheses': [],
    'unresolved': [
        '四个模型都是玩具，与 Ind3/logVol/R^ss 无已建立对应',
        '没有使用 SAT/SMT 求解器；正因如此也不存在可独立复核的求解器见证，全部为显式枚举',
        '有限不可满足不构成原始不可满足的证明',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N10 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N10 delivery written')
