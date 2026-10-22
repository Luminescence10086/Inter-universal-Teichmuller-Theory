"""Fill the N3-synthesis handoff with a real claim, hashed evidence and a real objection."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUN = ROOT / 'cdsa/runs/demo-01'
handoff_path = RUN / 'handoff' / 'N3-synthesis.json'


def digest(rel):
    return hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()


handoff = json.loads(handoff_path.read_text(encoding='utf-8'))
handoff.pop('__instructions__', None)
handoff.update({
    'claim': ('The correspondence ledger for this round was regenerated and independently '
              'verified: 8 entries anchored to exported theorem ids, 3 forbidden '
              'identifications recorded, and the single mathematical blocker identified as '
              'the p-adic logarithm; no IUT object was constructed and no gap closed.'),
    'evidence': [
        {'kind': 'file', 'ref': 'bridges/correspondence.json',
         'sha256': digest('bridges/correspondence.json'),
         'detail': 'the ledger this claim is about'},
        {'kind': 'file', 'ref': 'research/exploration/RESULTS.md',
         'sha256': digest('research/exploration/RESULTS.md'),
         'detail': 'the round report'},
        {'kind': 'command', 'ref': 'cdsa/runs/demo-01/logs/N2-verify.stdout.txt',
         'sha256': digest('cdsa/runs/demo-01/logs/N2-verify.stdout.txt'),
         'detail': 'independent verifier output (generation and verification separated)'},
    ],
    'confidence': 0.75,
    'dissent': [
        'The claim is about correspondence and blockers only. The ledger proves no IUT '
        'statement: E1 just means the missing object is recorded, and F-01 warns that our '
        'A(k)-level theorems must not be read as statements about Ism.',
        'Anchoring is structural: check_correspondence.py verifies ids, tiers, sections and '
        'companions, not whether the prose is faithful to each theorem.',
    ],
})
handoff_path.write_text(json.dumps(handoff, ensure_ascii=False, indent=2) + '\n',
                        encoding='utf-8')
print('handoff filled:', handoff_path.relative_to(ROOT))
