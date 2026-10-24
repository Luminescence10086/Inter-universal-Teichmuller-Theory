import json, re
p = 'delegated/2026-10-24/T097/sources.json'
d = json.load(open(p, encoding='utf-8'))
bad = 0
for s in d['sources']:
    f = s['file']; want = s.get('lines_total')
    for c in s['citations']:
        m = re.fullmatch(r'L(\d+)(?:-L(\d+))?', c['locator'])
        if not m: continue
        b = int(m.group(2) or m.group(1))
        if want is not None and b > want:
            print('OUT OF RANGE', f, c['locator'], b, want); bad += 1
print('remaining range problems:', bad)
print('sources:', len(d['sources']), 'citations:', sum(len(s['citations']) for s in d['sources']))
