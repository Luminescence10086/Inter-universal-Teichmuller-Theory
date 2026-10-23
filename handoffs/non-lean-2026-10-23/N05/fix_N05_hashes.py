"""Correct the input_sha256 column of N05/evidence.csv from the files on disk.

Two rows carried a mistyped hash for IndAut.lean (…49669070… instead of …49673070…) and one row for the
IUT III text differed from the file by one character. A quotation ledger that cites a hash which does not
reproduce is worse than one with no hash at all, so every row is recomputed here and the change is
recorded in a side file rather than silently overwriting the agent's numbers.

Usage: py -3 handoffs/non-lean-2026-10-23/N05/fix_N05_hashes.py
"""
import csv
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[3]
N05 = pathlib.Path(__file__).resolve().parent
CSV = N05 / 'evidence.csv'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


rows = list(csv.DictReader(CSV.open(encoding='utf-8-sig')))
fields = rows[0].keys()
changes = []
for r in rows:
    p = ROOT / r['source_path']
    actual = sha(p)
    if r.get('input_sha256') != actual:
        changes.append({'id': r['id'], 'path': r['source_path'],
                        'old': r.get('input_sha256'), 'new': actual})
        r['input_sha256'] = actual

with CSV.open('w', encoding='utf-8', newline='') as f:
    w = csv.DictWriter(f, fieldnames=list(fields))
    w.writeheader()
    for r in rows:
        w.writerow(r)

(N05 / 'hash-corrections.json').write_text(
    json.dumps({'corrected_rows': len(changes), 'changes': changes}, ensure_ascii=False, indent=2) + '\n',
    encoding='utf-8')
print('corrected', len(changes), 'rows')
for c in changes:
    print(' ', c['id'], c['path'].split('/')[-1], (c['old'] or '')[:16], '->', c['new'][:16])
