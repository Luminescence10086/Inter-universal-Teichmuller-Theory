import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N09 = ROOT / 'handoffs/non-lean-2026-10-23/N09'
cand = json.loads((N09 / 'candidate.json').read_text(encoding='utf-8-sig'))


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


runs = cand['runs']
summary = f"""# N09 — 有限商、轨道与 hull 候选搜索器

状态：`EXPERIMENTAL`（候选与反例线索；**不是**证明证书，也不能喂给 Lean 当输入）

## 运行
```powershell
py -3 handoffs\\non-lean-2026-10-23\\N09\\search.py --demo     # 写 candidate.json，约 2 秒
```
单文件、只用标准库；所有枚举精确（整数/元组运算），无浮点、无随机。

## 四个实例的实际结果
| 模型 | 元素数 | 子模数 | 正例（严格更大的真容器） | 只测 F_p 标量的回归 |
|---|---|---|---|---|
{"".join(f"| {r['ring']} | {r['elements']} | {r['submodule_count']} | {'有' if r['positive_case'] else '无'} | {'触发' if r['field_scalar_regression'] else '不触发'} |{chr(10)}" for r in runs)}
## 三条要点（都是实验观察，不是定理）
1. **单因子 Z/(p^k) 给不出正例**，而且原因是结构性的：主理想环的子模是**线性序**的，两个子模的"共同容器"
   总是其中较大的那个。所以"共同容器"这类问题在一因子模型里没有内容——这一点本身是本次实验的负结果，
   工具把它写在每个 run 的 `note` 里，而不是把 `positive=false` 当成失败。
2. **多因子模型 Z/9 × Z/9 有真正例**：`A = Z/3 × {{0}}`、`B = {{0}} × Z/3`，共同容器是 `Z/3 × Z/3`（3×3=9 个元素），
   严格大于 A、B（各 3 个）且真包含于整个环（81 个）。这就是"共同容器"概念真正开始有内容的模型。
3. **只测素域标量会误判**（回归例，Z/9 上）：某些元素在完整单位群下的轨道严格大于在 F_3 标量下的轨道——
   因为乘 `3` 落到真子格。若只用域标量测试，会漏掉这些轨道元素，从而把"共同容器"判小。

## 上限行为
`--demo` 里显式包含一个超限实例：`Z/(3^9)`（19,683 个元素）超过 `cap_elements = 4000`，工具返回
`UNKNOWN` 并写进 `candidate.json` 的 `unknown_demo`——**不静默降级、不缩小规模假装跑完**。

## 边界
- 结果只对所声明的有限模型成立；与原始 IUT 的系数环、order、hull 没有已建立的对应（`UNRESOLVED`）。
- 不声称任何"共同容器"结论可迁移到 `⊗_j K_{{c j}}` 或 `λ·O`；那需要 N04/N07/N08 的来源对齐。
- 本工具的输出不是 Lean 证书，也不构成 fact-tree 准入。
"""
(N09 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

outputs = [{'path': rel(N09 / n), 'sha256': sha(N09 / n)} for n in
           ['SUMMARY.md', 'search.py', 'candidate.json', 'make_N09_delivery.py']]
delivery = {
    'task_id': 'N09',
    'status': 'EXPERIMENTAL',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': [{'path': 'handoffs/non-lean-task-catalog-2026-10-23.md',
                'sha256': sha(ROOT / 'handoffs/non-lean-task-catalog-2026-10-23.md')}],
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N09/candidate.json',
         'line_or_page': "runs[-1].positive_case (Z/9 x Z/9)",
         'supports': 'the one instance where a strictly larger proper common container exists'},
        {'path': 'handoffs/non-lean-2026-10-23/N09/candidate.json',
         'line_or_page': "runs[0].field_scalar_regression (Z/9)",
         'supports': 'the regression the catalog asks for: F_p scalars alone give a strictly smaller orbit'},
    ],
    'commands_run': [
        'py -3 handoffs/non-lean-2026-10-23/N09/search.py --demo  -> candidate.json',
    ],
    'new_hypotheses': [],
    'unresolved': [
        '与原始 IUT 的系数环/order/hull 没有建立任何对应；结论只对所声明的有限模型成立',
        '未尝试真实系数环（N04 只给出签名，没有给出可枚举的有限商实例）',
        '饱和计数只在示例层面给出，未系统扫描',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N09 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N09 delivery written')
