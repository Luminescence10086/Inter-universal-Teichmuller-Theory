spots = [
 ('reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean', [169,173,174,175]),
 ('reviews/core-round/external/iut/Iut/Wall/Rss.lean', [374,446,486]),
 ('reviews/core-round/external/iut/Iut/Wall/Ind3.lean', [215,216,220,224,253,254]),
 ('reviews/core-round/external/iut/Iut/Wall/Checks.lean', [54,56,57]),
 ('reviews/core-round/external/iut/Iut/Wall/Constraints.lean', [137,138,220,224]),
 ('reviews/core-round/external/iut/Iut/Wall/MultiContainer.lean', [295,296,297,298]),
 ('research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt', [9720,9724,10549,10577,10965,10981]),
 ('reviews/core-round/external/MoheetBrain--iut-bridge-audit/tmp/Scholze_Stix.txt', [571,572,573,626,631,632]),
 ('research/core-backward-2026-10-23/PATH.md', [54,55,56]),
 ('reviews/core-round/external/MoheetBrain--iut-bridge-audit/tmp/Comments_Scholze_Stix.txt', [260,261,266,267,268]),
]
for f, ns in spots:
    lines = open(f, encoding='utf-8', errors='replace').read().split('\n')
    print('==', f, len(lines))
    for n in ns:
        print('  %-6d | %s' % (n, lines[n-1][:112]))
