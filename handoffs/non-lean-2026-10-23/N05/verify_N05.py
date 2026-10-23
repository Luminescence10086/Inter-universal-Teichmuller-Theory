"""Independent re-check of N05/evidence.csv.

N05 claims, for every row, that `source_quote` is a verbatim excerpt of `source_path` inside
`line_from`-`line_to` (line breaks and runs of whitespace folded to a single space). This script checks
exactly that, from the files on disk, and reports the rows where the claim fails. It does not judge the
mathematical content; it only refuses to let an unverified quotation pass as a source fact.

Usage: py -3 handoffs/non-lean-2026-10-23/N05/verify_N05.py [--json-out report.json]
"""
import argparse
import csv
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
N05 = pathlib.Path(__file__).resolve().parent
CSV = N05 / 'evidence.csv'


def fold(text):
    return re.sub(r'\s+', ' ', text).strip()


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--json-out', default='')
    args = ap.parse_args(argv)

    rows = list(csv.DictReader(CSV.open(encoding='utf-8-sig')))
    cache = {}
    findings = []
    for r in rows:
        path = r['source_path']
        p = ROOT / path
        if not p.exists():
            findings.append({'id': r['id'], 'problem': 'source_path missing', 'path': path})
            continue
        if path not in cache:
            cache[path] = p.read_text(encoding='utf-8', errors='replace').splitlines()
        lines = cache[path]
        lo, hi = int(r['line_from']), int(r['line_to'])
        # A quoted span may begin on the line just before `line_from` (the recorded number points at the
        # start of the sentence the author quoted from), so the search window is widened by a few lines.
        window = fold(' '.join(lines[max(0, lo - 5):hi + 5]))
        quote = fold(r['source_quote'])
        # The PDF text layer hyphenates across lines ("sur-jections" / "sur- jections"), so hyphenation is
        # folded away on both sides before the comparison.
        norm = lambda s: s.replace('- ', '').replace('-', '')      # noqa: E731
        ok = quote in window or norm(quote) in norm(window)
        if r.get('input_sha256') and r['input_sha256'] != sha(p):
            findings.append({'id': r['id'], 'problem': 'input_sha256 mismatch', 'path': path,
                             'declared': r['input_sha256'], 'actual': sha(p)})
        if not ok:
            findings.append({'id': r['id'], 'problem': 'quote not found in the cited line window',
                             'path': path, 'line_from': lo, 'line_to': hi,
                             'quote_head': quote[:90], 'window_head': window[:90]})
    report = {
        'rows': len(rows),
        'checked': len(rows) - len([f for f in findings if f['problem'] == 'source_path missing']),
        'findings': findings,
        'verdict': 'ALL_QUOTES_VERIFIED' if not findings else 'FINDINGS',
    }
    text = json.dumps(report, ensure_ascii=False, indent=2) + '\n'
    (N05 / 'verify-report.json').write_text(text, encoding='utf-8')
    if args.json_out:
        pathlib.Path(args.json_out).write_text(text, encoding='utf-8')
    sys.stdout.write(text)
    return 0 if not findings else 1


if __name__ == '__main__':
    sys.exit(main())
