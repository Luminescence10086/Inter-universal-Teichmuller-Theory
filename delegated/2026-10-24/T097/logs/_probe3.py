import re
f='research/round2-source-cache/iut-II-official-retrieved-2026-10-23.txt'
lines = open(f, encoding='utf-8', errors='replace').read().split('\n')
print(len(lines))
for n,l in enumerate(lines[:12],1):
    print('  %-4d %s' % (n, l[:120]))
print('--- Definition 4.9 / prime-strip ---')
for i,l in enumerate(lines,1):
    if re.search(r'Definition 4\.9|F\S*prime-?strip', l):
        print('  %-6d %s' % (i, l.strip()[:112]))
