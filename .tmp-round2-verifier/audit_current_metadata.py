import json
from pathlib import Path
r=Path(__file__).resolve().parent.parent
rows=json.loads(json.loads(json.loads((r/'verification/export.json').read_text(encoding='utf-8'))['stdout'].splitlines()[0])['data'])
by={x['id']:x for x in rows}
facts=json.loads((r/'fact-tree/facts.json').read_text(encoding='utf-8'))
registered={x['id'] for x in facts['nodes']}
missing=[]
for n in facts['nodes']:
    seen=set(); todo=list(n['constants'])
    while todo:
        x=todo.pop()
        if x in seen: continue
        seen.add(x)
        if x in by: todo+=by[x]['constants']
    new=(seen & registered)-set(n['depends_on'])-{n['id']}
    if new:missing.append([n['id'],sorted(new)])
print(json.dumps({'fact_nodes':len(registered),'exported_thm_rows':len(rows),'additional_registered_theorem_paths_via_exported_thms':missing},ensure_ascii=False))

