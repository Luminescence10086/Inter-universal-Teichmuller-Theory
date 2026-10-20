"""Read-only catalog query; --deep also rehashes imported compiled objects."""
import argparse
import json
import sys
from verify import ROOT, snapshot, assert_snapshot, digest

if hasattr(sys.stdout, 'reconfigure'):
    sys.stdout.reconfigure(encoding='utf-8')
parser = argparse.ArgumentParser()
parser.add_argument('query', nargs='?', default='')
parser.add_argument('--deep', action='store_true')
args = parser.parse_args()
tree = json.loads((ROOT / 'fact-tree/facts.json').read_text(encoding='utf-8'))
if tree.get('schema') != 2 or tree.get('status') != 'checked':
    raise SystemExit('fact-tree is not checked; run tools/verify.py')
assert_snapshot(tree['input_sha256'], snapshot())
ids = {n['id'] for n in tree['nodes']}
expected = {(dep, n['id']) for n in tree['nodes'] for dep in n['depends_on']}
actual = {(e['from'], e['to']) for e in tree['edges']}
if len(ids) != len(tree['nodes']) or expected != actual or any(a not in ids or b not in ids for a, b in actual):
    raise SystemExit('Malformed graph or missing dependency; rerun verification')
if args.deep:
    assert_snapshot(tree['runtime_sha256'], {p: digest(p) for p in tree['runtime_sha256']})
for node in tree['nodes']:
    if args.query.lower() in (node['id'] + ' ' + node['statement']).lower():
        print(node['id'])
        print('  ' + node['statement'].replace('\n', '\n  '))
        print('  dependencies: ' + (', '.join(node['depends_on']) or 'none'))
        print('  axioms: ' + (', '.join(node['axioms']) or 'none'))
