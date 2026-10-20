"""Read-only query of the fully admitted bridge, with full source/runtime checks."""
import argparse
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parent / 'tools'))
from freshness import validate_project


def main():
    if hasattr(sys.stdout, 'reconfigure'):
        sys.stdout.reconfigure(encoding='utf-8')
    parser = argparse.ArgumentParser()
    parser.add_argument('query', nargs='?', default='')
    parser.add_argument('--deep', action='store_true')
    args = parser.parse_args()
    rows, _ = validate_project(ROOT, args.deep)
    import json
    tree = json.loads((ROOT / 'fact-tree/facts.json').read_text(encoding='utf-8'))
    for node in tree['nodes']:
        if args.query.lower() in (node['id'] + ' ' + rows[node['id']]['statement']).lower():
            print(node['id'])
            print('  ' + rows[node['id']]['statement'])
            print('  hypotheses: ' + ', '.join(node.get('hypotheses', [])))
            print('  dependencies: ' + ', '.join(node['depends_on']))


if __name__ == '__main__':
    main()
