import hashlib
import json
import pathlib

ROOT = pathlib.Path(r'D:\Inter-universal Teichmüller Theory')
N01 = ROOT / 'handoffs/non-lean-2026-10-23/N01'


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def rel(p):
    return str(pathlib.Path(p).resolve().relative_to(ROOT)).replace('\\', '/')


ARTIFACTS = [
    ('official_pdf_github', N01 / 'official-LANA_report_202607.pdf',
     'https://github.com/katobungen/LANA_report_202607/raw/pdf/LANA_report_202607.pdf', '50'),
    ('official_text_pypdf', N01 / 'official-LANA_report_202607.txt', '(derived from the official pdf, pypdf)', '50'),
    ('cache_pdf_used_earlier', ROOT / 'research/round2-source-cache/LANA-interim-report-2026-07.pdf',
     'local cache from the earlier round', '50'),
    ('cache_text_used_earlier', ROOT / 'research/round2-source-cache/LANA-interim-report-2026-07.txt',
     '(derived from the cached pdf, pypdf, earlier round)', '50'),
    ('ncatlab_mirror_pdf', N01 / 'fetched-ncatlab.pdf', 'ncatlab mirror, fetched this round', '50'),
    ('zen_page_0717e', N01 / 'zen-0717e.html', 'https://zen.ac.jp/news/zmcpostevent0717e', '-'),
    ('zen_page_0331e', N01 / 'zen-0331e.html', 'https://zen.ac.jp/news/zmcpostevent0331e', '-'),
]

rows = ['artifact,path_or_url,retrieved_at,bytes,sha256,page_count,pypdf_text_bytes,note']
for name, path, url, pages in ARTIFACTS:
    p = pathlib.Path(path)
    if not p.exists():
        rows.append(f'{name},"{url}",MISSING,,,,,')
        continue
    b = p.read_bytes()
    txt_bytes = ''
    if name in ('official_text_pypdf', 'cache_text_used_earlier'):
        txt_bytes = len(b)
    rows.append(f'{name},"{url}",2026-10-23,{len(b)},{hashlib.sha256(b).hexdigest()},{pages},{txt_bytes},'
                f'{"byte-identical to cache" if name == "ncatlab_mirror_pdf" else ""}')
(N01 / 'versions.csv').write_text('\n'.join(rows) + '\n', encoding='utf-8')

diffs = f"""# N01 关键差异（每次差异给页码/行号）

同一工具（pypdf 默认参数）抽取的两个版本，逐页对齐后共 **2 处实质差异**，均已定位到文本行号。

| # | 位置 | 缓存（早期版本） | 官方 GitHub（本轮下载） | 影响 |
|---|------|------------------|--------------------------|------|
| 1 | txt 第 41 行（第 1 页，Date 行） | `Date: Last Updated: July 16, 2026.` | `Date: Last Updated: July 20, 2026.` | 版本日期不同：缓存是 7 月 16 日版，官方是 7 月 20 日版 |
| 2 | txt 第 327–337 行（致谢段，重排） | `Alex Kontrovich`；`the Educational Institute of The Nippon Foundation and DW ANGO` 段按旧断行 | `Alex Kontorovich`；同名段重新断行成 12 行 | 人名更正 + 排版变化；致谢内容本身未见增删 |

字节层面：官方 PDF 640,461 B / 缓存 PDF 640,457 B，**不是同一字节**。首个差异出现在 PDF 的第一个内容流对象处
（`6 0 obj` 的 `/Length 2513` 对 `/Length 2512`），其后全部偏移；两文件页数都是 **50 页**。
ncatlab 镜像与缓存 PDF **字节完全相同**（同为 640,457 B，`sha256` 一致），说明缓存很可能取自该镜像，而不是取自官方 GitHub。

结论（`SOURCE_FACT`）：**同一标题、同一 50 页、但不是同一字节、也不是同一版本**；缓存对应 2026-07-16 版，
官方对应 2026-07-20 版。此前"官方 PDF 与缓存字节同一性未核实"的问题现在有答案：**不同一**。
"""
(N01 / 'diffs.md').write_text(diffs, encoding='utf-8')

summary = f"""# N01 — 官方报告与缓存版本核对

状态：`STATIC_COMPLETE`（来源版本证据；不是数学审阅）

## 结论三句话
1. 本轮从官方 GitHub（`katobungen/LANA_report_202607`，`pdf` 分支）取到了 `LANA_report_202607.pdf`：
   640,461 B，`sha256 {sha(N01 / 'official-LANA_report_202607.pdf')}`，50 页，正文日期 **July 20, 2026**。
2. 工程里一直在用的缓存 `research/round2-source-cache/LANA-interim-report-2026-07.pdf`：
   640,457 B，`sha256 {sha(ROOT / 'research/round2-source-cache/LANA-interim-report-2026-07.pdf')}`，50 页，
   日期 **July 16, 2026**；它与 ncatlab 镜像**字节完全相同**。
3. 因此"同一标题"成立，"相同字节"不成立，差异可定位到 2 处（日期行、致谢段人名与断行）。见 `diffs.md`。

## 已核实 / 未核实
- 已核实（`SOURCE_FACT`）：字节哈希、页数、日期行、致谢段两处文本差异、镜像与缓存的字节同一性。
- 未核实（`UNRESOLVED`）：zen.ac.jp 页面本身只是链接页，本轮抓到了 HTML 但没有从中再取到第三个独立副本；
  7 月 20 日版与 7 月 16 日版之间是否存在**数学内容**改动，只核对了文本层 2 处差异，未逐节重读全文。

## 影响
- 工程内此前引用 LANA 报告页码/措辞（例如 `research/core-backward-2026-10-23/lana-report-assessment.md`）
  依据的是 **7 月 16 日版**；若某条引文的页码落在致谢或日期附近需重对，其余正文未见文本差异。
- 旧缓存保留未动。
"""
(N01 / 'SUMMARY.md').write_text(summary, encoding='utf-8')

inputs = [{'path': rel(N01 / n), 'sha256': sha(N01 / n)} for n in
          ['official-LANA_report_202607.pdf', 'official-LANA_report_202607.txt', 'fetched-ncatlab.pdf',
           'zen-0717e.html', 'zen-0331e.html', 'text-diff-same-method.txt', 'cache-repro-pypdf-default.txt']]
inputs.append({'path': 'research/round2-source-cache/LANA-interim-report-2026-07.pdf',
               'sha256': sha(ROOT / 'research/round2-source-cache/LANA-interim-report-2026-07.pdf')})
outputs = [{'path': rel(N01 / n), 'sha256': sha(N01 / n)} for n in
           ['SUMMARY.md', 'versions.csv', 'diffs.md', 'make_N01.py']]

delivery = {
    'task_id': 'N01',
    'status': 'STATIC_COMPLETE',
    'source_commit': '568e4be9f8b3e4f1d35b5c358e3f3b7836f469c2',
    'inputs': inputs,
    'outputs': outputs,
    'review_anchors': [
        {'path': 'handoffs/non-lean-2026-10-23/N01/diffs.md', 'line_or_page': 'table rows 1-2',
         'supports': 'the two textual differences between the cached (July 16) and official (July 20) versions'},
        {'path': 'handoffs/non-lean-2026-10-23/N01/versions.csv', 'line_or_page': 'rows official_pdf_github / cache_pdf_used_earlier',
         'supports': 'both sizes and sha256 values, so a reviewer can recompute them independently'},
    ],
    'commands_run': [
        'Invoke-WebRequest https://github.com/katobungen/LANA_report_202607/raw/pdf/LANA_report_202607.pdf',
        'py -3 (pypdf) page count + default text extraction for both pdfs',
        'diff of the two pypdf text extractions -> text-diff-same-method.txt',
        'Get-FileHash -Algorithm SHA256 on all artifacts',
    ],
    'new_hypotheses': [],
    'unresolved': [
        'zen.ac.jp 两个页面只作链接页使用，没有从它们再取到独立第三份 PDF（UNRESOLVED，未再重试）',
        '7-16 与 7-20 之间是否有数学内容改动：只比对文本层，得到 2 处差异，未逐节重读全文（UNRESOLVED）',
        '本任务不做数学有效性审查',
    ],
    'lean_run': False,
    'editor_run': False,
    'native_iut_realized': False,
    'fact_tree_admitted': False,
}
(N01 / 'delivery.json').write_text(json.dumps(delivery, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print('N01 written')
