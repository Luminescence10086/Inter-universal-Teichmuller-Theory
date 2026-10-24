import json, re
p = 'delegated/2026-10-24/T097/sources.json'
d = json.load(open(p, encoding='utf-8'))
counts = {
 'research/round2-source-cache/LANA-interim-report-2026-07.txt':2341,
 'research/round2-source-cache/iut-I-official-retrieved-2026-10-16.txt':10927,
 'research/round2-source-cache/iut-II-official-retrieved-2026-10-23.txt':7697,
 'research/round2-source-cache/iut-III-official-retrieved-2026-10-16.txt':11854,
 'research/round2-source-cache/iut-IV-official-retrieved-2026-10-16.txt':4635,
 'reviews/core-round/external/iut/Iut/Wall/EtaAlg.lean':229,
 'reviews/core-round/external/iut/Iut/Wall/Ind3.lean':293,
 'reviews/core-round/external/iut/Iut/Wall/Checks.lean':184,
 'reviews/core-round/external/iut/Iut/Wall/Constraints.lean':341,
 'reviews/core-round/external/iut/Iut/Wall/Rss.lean':517,
 'reviews/core-round/external/iut/Iut/Wall/README.md':435,
 'reviews/core-round/external/iut/Iut/Wall/MultiContainer.lean':513,
 'research/lana-link-acceptance-2026-10-23/ChoiceExistenceRegression.lean':43,
 'research/core-backward-2026-10-23/PATH.md':94,
 'research/core-projective-2026-10-24/backward-delivery-review.md':82,
 'reviews/core-round/external/MoheetBrain--iut-bridge-audit/tmp/Scholze_Stix.txt':652,
 'reviews/core-round/external/MoheetBrain--iut-bridge-audit/tmp/Comments_Scholze_Stix.txt':324,
}
bad = 0
for s in d['sources']:
    f = s['file']
    want = counts.get(f)
    if want is None:
        continue
    got = s.get('lines_total')
    if got != want:
        print('FIX lines_total %-70s %s -> %s' % (f, got, want))
        s['lines_total'] = want
        bad += 1
    for c in s['citations']:
        m = re.fullmatch(r'L(\d+)(?:-L(\d+))?', c['locator'])
        if not m:
            continue
        a = int(m.group(1)); b = int(m.group(2) or a)
        if b > want:
            print('OUT OF RANGE %s %s (%d > %d)' % (f, c['locator'], b, want))
            bad += 1
if bad:
    json.dump(d, open(p,'w',encoding='utf-8'), ensure_ascii=False, indent=2)
    open(p,'a',encoding='utf-8').write('\n')
print('fixes applied:', bad)
