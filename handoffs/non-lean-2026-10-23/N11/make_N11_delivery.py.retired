import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N11 = ROOT / 'handoffs/non-lean-2026-10-23/N11'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


summary = """# N11 — 跨领域方法迁移与真正的新工具设计

状态：`STATIC_COMPLETE`（两张工具设计卡 + 有界先前工作检索；**都是方案，不是结果**）

## 只选两条路线（另外两条为什么不做）
- **选路线 3（非阿几何、格与有限模）→ 卡 1「容器–最小 hull 审计器」**：因为仓库里 `hull` 逐字就是 `scaledIntegral b`
  （即 `b·O`），"是不是最小 hull / 有限模拉回是不是只是容器"逐字是格的**饱和**问题——可算、可否证。
- **选路线 4（约束求解与优化对偶）→ 卡 2「达到–证书二分器」**：因为 `realisation` 只给**包含**（`EtaAlg.lean:123-125`），
  目标是**等式**（`EtaAlg.lean:151`）；"上界证书 vs 达到的见证"正是这条缺口的精确形状。
- **不选路线 1（群胚/下降）**：它最自然的产出是"联合兼容选择"的存在性，那是**比 (9-1) 更强**的族条件（N03-O5 的雷区），
  且 `Ind3` 目前只有集合结构 + 一个存在性的 `τ`（`EtaAlg.lean:112`），群胚结构造不出来。
- **不选路线 2（逆极限/紧致性）**：`Region D` 上没有拓扑、`Ind3` 不是滤过族；要先造拓扑才能谈紧致，超出本轮边界。

## 两张卡各自最硬的一句话
- **卡 1**：一旦指数集不是 box，逐坐标 box **严格大于**对数凸包；有限例里后者测度为 0、甚至不是 admissible 区。
  所以"hull = 逐坐标 `λ·O`"是**有内容的断言**，不是无害松弛（`toy_check.py` Part A 已跑：`BOX` / `NONBOX(φ,x)` 两类判定，
  其中 A2/A3 两个反例各自给出显式分离泛函）。
- **卡 2**：两个对象可以在**所有已声明字段**上一致，却一个达到目标值、一个不达到（Part B 的 M1/M2）。
  所以只靠 `(T1)–(T3)` 的答案是 `UNDETERMINED`；要判定必须多声明 `sup` 那一项。这就是 N07-H1 的精确形状。

## 依赖关系（必须一起读）
卡 2 的有效性**以卡 1 的归约（A2/A3）为条件**：`Ind3` 在对象空间不是多面体，Farkas 只在指数坐标归约之后可用。
这一条已写进 `tool-cards.md` §0，不允许单独引用卡 2。

## 先前工作（`prior-art.md`，6 次查询）
没有检索到"原始 hull 恰为逐坐标 `λ·O`"或"三值达到/证书分类器"的现成工作。**没检索到 ≠ 不存在**，
且检索只覆盖英文关键词与摘要级片段，不构成原创性证明。
"""
(N11 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': p, 'sha256': sha(ROOT / p)} for p in
          ['handoffs/non-lean-task-catalog-2026-10-23.md',
           'handoffs/non-lean-2026-10-23/N03/target.md',
           'handoffs/non-lean-2026-10-23/N07/pipeline.md',
           'handoffs/non-lean-2026-10-23/N08/bridge-plan.md',
           'reviews/core-round/external/iut/Iut/Wall/Ind3.lean',
           'reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean'] if (ROOT / p).exists()]
outputs = [{'path': rel(N11 / n), 'sha256': sha(N11 / n)} for n in
           ['SUMMARY.md', 'tool-cards.md', 'prior-art.md', 'toy_check.py', 'toy_check.log', 'make_N11_delivery.py']]

delivery = {
    'task_id': 'N11',
    'status': 'EXPERIMENTAL',
    'source_commit': 'f7ed1cc8ea33234ec66b1f49fb9e12212742cdcb',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N11/toy_check.log',
         'line_or_page': 'Part A rows A2/A3 (NONBOX with explicit separating functional)',
         'supports': 'that a box container can be strictly larger than the log-convex hull, with a witness'},
        {'path': 'handoffs/non-lean-2026-10-23/N11/tool-cards.md',
         'line_or_page': 'section 2.5 (Part B M1/M2)',
         'supports': 'that two objects agreeing on every declared field can differ on attainability, so the answer is UNDETERMINED'},
    ],
    'commands_run': [
        'py -3 handoffs/non-lean-2026-10-23/N11/toy_check.py  -> RESULT: ALL PASS (Part A and Part B)',
        'web_search x2 (6 queries total) for the bounded prior-art check -> prior-art.md',
    ],
    'new_hypotheses': [
        'A2/A3 (the exponent-set reading of vcIComp) are declared PROPOSED_INTERFACE, not proved',
        'A5 (non-archimedean analogue of the log-convex envelope theorem) has no cited source in this round',
    ],
    'unresolved': [
        '两张卡都是设计；没有任何一条被 Lean 形式化',
        '卡 2 的有效性依赖卡 1 的归约，单独引用会失效',
        '先前工作检索只覆盖 6 次英文查询与摘要级片段，不构成原创性证明',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N11 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N11 delivery written')
