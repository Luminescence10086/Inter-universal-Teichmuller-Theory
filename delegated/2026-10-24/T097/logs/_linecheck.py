checks = [
 ('reviews/core-round/external/iut/Iut/Wall/Checks.lean', [93,94,95,110,116,121]),
 ('reviews/core-round/external/iut/Iut/Wall/Constraints.lean', [151,152,153,191,192,193,110,111,112]),
 ('reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean', [105,106,107,108,109,211,212,213,219,222]),
 ('reviews/core-round/external/iut/Iut/Wall/Ind3.lean', [213,222]),
 ('reviews/core-round/external/iut/Iut/Wall/README.md', [4,5,6,99,100,101,176,177,178,180,181,413,414,420,421,422,435]),
]
for f, ns in checks:
    lines = open(f, encoding='utf-8').read().split('\n')
    print('==', f, 'lines', len(lines))
    for n in ns:
        print('  %-5d | %s' % (n, lines[n-1][:118]))
