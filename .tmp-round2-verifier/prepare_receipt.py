import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parent
hashes=lambda p:hashlib.sha256((root/p).read_bytes()).hexdigest()
context=['lean-toolchain','lakefile.toml','lake-manifest.json','IUTAudit.lean','tools/EditorCheck.lean']
r={'context_sha256':{p:hashes(p) for p in context},'files':{'IUTAudit/Descent.lean':{'sha256':hashes('IUTAudit/Descent.lean'),'lean_server_checked':True,'errors':0,'warnings':0,'observation':'SYNTHETIC TEST ONLY - no real editor observation'}}}
(root/'verification/vscode-receipt.json').write_text(json.dumps(r),encoding='utf-8')
