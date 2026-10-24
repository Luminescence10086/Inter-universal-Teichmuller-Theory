files = [
 'research/round2-source-cache/LANA-interim-report-2026-07.txt',
 'research/round2-source-cache/iut-I-official-retrieved-2026-10-16.txt',
 'research/round2-source-cache/iut-II-official-retrieved-2026-10-23.txt',
 'research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt',
 'research/round2-source-cache/iut-IV-official-retrieved-2026-10-16.txt',
 'reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean',
 'reviews/core-round/external/iut/Iut/Wall/Ind3.lean',
 'reviews/core-round/external/iut/Iut/Wall/Checks.lean',
 'reviews/core-round/external/iut/Iut/Wall/Constraints.lean',
 'reviews/core-round/external/iut/Iut/Wall/Rss.lean',
 'reviews/core-round/external/iut/Iut/Wall/README.md',
 'reviews/core-round/external/iut/Iut/Wall/MultiContainer.lean',
 'research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean',
 'research/core-backward-2026-10-23/PATH.md',
 'research/core-projective-2026-10-24/backward-delivery-review.md',
 'reviews/core-round/external/MoheetBrain--iut-bridge-audit/tmp/Scholze_Stix.txt',
 'reviews/core-round/external/MoheetBrain--iut-bridge-audit/tmp/Comments_Scholze_Stix.txt',
]
for f in files:
    b = open(f,'rb').read()
    n = b.count(b'\n') + (0 if b.endswith(b'\n') else 1)
    print('%-6d %-10d %s' % (n, len(b), f))
