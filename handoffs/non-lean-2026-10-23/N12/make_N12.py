import hashlib
import json
import pathlib

ROOT = pathlib.Path(r'D:\Inter-universal Teichmüller Theory')
N12 = ROOT / 'handoffs/non-lean-2026-10-23/N12'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


diff_files = sorted((N12 / '_diffs').glob('*.diff'))
snap = sorted((N12 / '_base').iterdir()) + sorted((N12 / '_head').iterdir())
engine = [N12 / '_work_diff.py', N12 / '_work_diff_index.py', N12 / '_work_anchors.py', N12 / '_work_tags.py']
inputs = (
    [{'path': rel(N12 / n), 'sha256': sha(N12 / n)} for n in
     ['diff_index.txt', '_hash_raw.json', '_ls_tree_base.txt', '_ls_tree_head.txt',
      '_base_lakefile.toml.txt', '_base_lake-manifest.json.txt', '_head_lakefile.toml.txt',
      '_head_lake-manifest.json.txt']]
    + [{'path': rel(p), 'sha256': sha(p)} for p in snap if p.is_file()]
    + [{'path': rel(p), 'sha256': sha(p)} for p in diff_files]
    + [{'path': rel(p), 'sha256': sha(p)} for p in engine]
)

summary = """# N12 — 外部仓库增量与关键接口跟踪

状态：`STATIC_COMPLETE`（版本差异索引；不是数学审查，也没有运行外部 Lean）

## 范围
固定两个本地克隆：`reviews/core-round/external/iut`（base `f7ed1cc8` → head `188ff572`）。本次**只跟踪上一次审查
未覆盖的变更**：上一次已列明的 6 个新增 Lean 文件、5 个修改的 Lean 文件、7 个相同核心锚点，本轮不重复。

## 本轮的增量（7 项，全部机械可比）
1. `Plans/MR10Plan.md` **新增**：AbsTopIII Cor 2.7（全纯椭圆尖点化，IUT 引用的那一步）的实施计划。
2. `Iut/AutHolomorphic/README.md`：新增一句指向上面那份 MR10 计划。
3. `Iut/Multiradial/ROADMAP.md`：`Reconstruction/` 行改写——曲线在数域上的尖点惯性群现由 `Cusp/BelyiSpec.lean`
   （MR8.8）承担，Belyi 尖点化引用 [AbsTopII] Cor 3.7/3.8；并新增 `[TopSurr] Thm 4.12` 一行，
   作为 [AbsTopI] Ex 4.8(i) 里 rel-isom-DGC 的来源（对应 MR7）。
4. `Plans/MR9Plan.md`：Thm 1.9(b) 的"到几何的桥"标记为完成，依据 `Cusp/SurfacePi1.lean`、`Cusp/SurfaceGeom.lean`
   的 `exists_fhat_equiv`；并改写 pin 说明。
5. `lakefile.toml`：`pi1` 由 `7647d28` 升到 `12719c9`；`orbicurve-cores` 由 `21ce4b7` 升到 `d08559e`。
6. `lake-manifest.json`：依赖集合里出现 `curves-jacobian`（`601db27c`），`weil-curves` 仍在。
7. `scripts/shell_lint_allowlist.txt`：2026-10-23 的 shell 审计把 439 条 `new` 全部重标为 `def`（+695 行）。

## 一处必须点出的不一致（`SOURCE_FACT` + 判定）
`Plans/MR9Plan.md:125-126` 写"iut pins `curves-jacobian` a258c15、`belyi` 5f3a88e、`pi1` 12719c9"，
但同一 commit 的 `lakefile.toml` 实际钉的是 `curves-jacobian 601db27c…`、`belyi 7206d783…`。
`pi1` 一致，另外两个**不一致**。这不是数学问题，是计划文本与锁文件不同步；检索者若照计划文本引用依赖版本会引错。
"""
(N12 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

rows = [
 'id,path,line_or_page,before_sha256_or_absent,after_sha256,change_kind,affected_object,evidence_cmd',
 ('D1,Plans/MR10Plan.md,"new file (whole)","absent",2e0bb2c540dcdf8ec16e97684a6eeceed66c9518,'
  'definition_of_plan,"plan for AbsTopIII Cor 2.7 (holomorphic elliptic cuspidalisation); referenced by AutHolomorphic README",'
  '"git -C reviews/core-round/external/iut diff --stat f7ed1cc8..188ff572"'),
 ('D2,Iut/AutHolomorphic/README.md,"41-46",1ee01274503dcb710985a764e3e49f5808c16403,08f657ff58eda94dbb145549904d9440218e6580,'
  'documentation_pointer,"adds one sentence pointing at Plans/MR10Plan.md","git diff f7ed1cc8..188ff572 -- Iut/AutHolomorphic/README.md"'),
 ('D3,Iut/Multiradial/ROADMAP.md,"136,238-241",8d13db74533056358074a60815663f35c11c5d66,68abacef9952aea5a08b464b3cbe2c8fad699f10,'
  'status_row_rewrite,"Reconstruction row now credits Cusp/BelyiSpec.lean (MR8.8); new [TopSurr] Thm 4.12 row named as the source of rel-isom-DGC for MR7",'
  '"git diff f7ed1cc8..188ff572 -- Iut/Multiradial/ROADMAP.md"'),
 ('D4,Plans/MR9Plan.md,"112,125-126",6b7022bc87fffa204beb1a8c5bca56e6327c0b61,e7c58031316def8b2bb1ca2069d8024c6c4504db,'
  'status_row_rewrite,"Thm 1.9(b) bridge marked done via Cusp/SurfacePi1.lean + SurfaceGeom.lean exists_fhat_equiv; pin sentence rewritten",'
  '"git diff f7ed1cc8..188ff572 -- Plans/MR9Plan.md"'),
 ('D5,lakefile.toml,"54-66 (requires pi1, orbicurve-cores)",fe38fe423115de09c8170ae3873ac93ecd4c1c7b,a140c99dea8f8307e5c89f7579a9c4f0a3172d06,'
  'dependency_pin,"pi1 7647d28 -> 12719c9; orbicurve-cores 21ce4b7 -> d08559e","git diff f7ed1cc8..188ff572 -- lakefile.toml"'),
 ('D6,lake-manifest.json,"1-47",2e32d3da7a171d54625b4fa4e5cf217e13e7ae0f,98efbffc5363c18243befee94fbcfcf403ed6622,'
  'dependency_set,"curves-jacobian 601db27c enters the resolved dependency set; weil-curves stays","git diff f7ed1cc8..188ff572 -- lake-manifest.json"'),
 ('D7,scripts/shell_lint_allowlist.txt,"2-5 and 967+",f29dec54fa7e171dad53ff856289f03844353fb8,e94ba172ff7180723a92d37ae7bb64509b1c87b7,'
  'audit_retag,"shell audit 2026-10-23 retags 439 new entries as def (+695 lines); asserts no shells among them",'
  '"git diff f7ed1cc8..188ff572 -- scripts/shell_lint_allowlist.txt"'),
 ('D8,"Plans/MR9Plan.md vs lakefile.toml","125-126 vs 54-66",-,same_as_base,'
  'inconsistency_not_a_change,"plan text says curves-jacobian a258c15 / belyi 5f3a88e; lakefile pins 601db27c / 7206d783 (pi1 agrees)",'
  '"Select-String -Path lakefile.toml -Pattern curves-jacobian -Context 0,3"'),
]
(N12 / 'delta.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

outputs = [{'path': rel(N12 / n), 'sha256': sha(N12 / n)} for n in
           ['SUMMARY.md', 'delta.csv', 'make_N12.py']]
delivery = {
    'task_id': 'N12',
    'status': 'STATIC_COMPLETE',
    'source_commit': '188ff572b61b748e5606d1419980f1e0b5abb0aa',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N12/_diffs/lakefile.toml.diff',
         'line_or_page': 'hunks at requires pi1 / orbicurve-cores',
         'supports': 'the two dependency pin bumps, byte for byte'},
        {'path': 'handoffs/non-lean-2026-10-23/N12/_diffs/Iut__Multiradial__ROADMAP.md.diff',
         'line_or_page': 'second hunk, the new [TopSurr] Thm 4.12 row',
         'supports': 'that the rel-isom-DGC source row was added, and its wording'},
    ],
    'commands_run': [
        'git -C reviews/core-round/external/iut rev-parse HEAD -> 188ff572... (base recorded as f7ed1cc8...)',
        'git -C ... ls-tree -r --name-only <rev>  (base and head) -> _ls_tree_*.txt',
        'git -C ... diff <base>..<head> --stat   -> diff_index.txt',
        'git -C ... show <rev>:<path> for the 7 non-Lean-changed paths -> _base/ _head/ + _diffs/',
        'Get-FileHash -Algorithm SHA256 on every snapshot and diff',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'pin 文本与锁文件不一致：MR9Plan 写 curves-jacobian a258c15 / belyi 5f3a88e，lakefile 钉 601db27c / 7206d783（UNRESOLVED，需主线确认以哪个为准）',
        'README/ROADMAP 自称"done""exists"属于仓库自述，本任务不据此判定任何命题已证',
        '未在远程重新 fetch：结论只对该克隆的 188ff572 成立；若上游有新 commit，须另固定',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N12 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N12 written', len(inputs), 'inputs')
