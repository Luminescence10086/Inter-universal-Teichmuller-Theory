"""Extract IUT II's text from the retrieved PDF, matching the cache's page-marker convention.

The cached IUT I / III / IV .txt files delimit pages with `===== PDF PAGE n =====`, so the same
format is produced here; that keeps the locators comparable across the four papers.
"""
import sys
from pathlib import Path

from pypdf import PdfReader

src = Path(sys.argv[1])
dst = Path(sys.argv[2])

reader = PdfReader(str(src))
out = []
for i, page in enumerate(reader.pages, start=1):
    out.append(f'===== PDF PAGE {i} =====')
    try:
        out.append(page.extract_text() or '')
    except Exception as exc:  # noqa: BLE001 - record the page rather than losing the file
        out.append(f'[extraction failed: {type(exc).__name__}: {exc}]')
text = '\n'.join(out)
dst.write_text(text, encoding='utf-8')
print(f'pages: {len(reader.pages)}')
print(f'bytes written: {len(text.encode("utf-8"))}')
print(f'lines: {text.count(chr(10)) + 1}')
