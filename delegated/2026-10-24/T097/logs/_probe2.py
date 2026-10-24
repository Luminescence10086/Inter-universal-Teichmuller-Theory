import re
for f in ['research/round2-source-cache/iut-I-official-retrieved-2026-10-16.txt','research/round2-source-cache/iut-II-official-retrieved-2026-10-23.txt']:
    lines = open(f, encoding='utf-8', errors='replace').read().split('\n')
    hits = [(i+1, l.strip()) for i, l in enumerate(lines) if re.search(r'multiradial representation|holomorphic hull of the union|possible images', l)]
    print('==', f, 'hits', len(hits))
    for n, l in hits[:8]:
        print('   %-6d %s' % (n, l[:110]))
