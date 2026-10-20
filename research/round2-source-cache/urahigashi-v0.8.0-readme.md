# A local non-containment in Step (v) of IUT IV, Theorem 1.10

Version 1.0.0: the draft of 5 October 2026 (6 pages).
Archived at DOI [10.5281/zenodo.23166432](https://doi.org/10.5281/zenodo.23166432) (all versions).

Step (v) of the proof of Theorem 1.10 in Mochizuki's *Inter-universal Teichmüller theory IV* bounds,
for each tuple of places, the log-volume of the corresponding component of the holomorphic hull of the
union of possible images of a Θ-pilot object defined in Corollary 3.12 of the third paper. This note
gives an explicit initial Θ-datum, with two places of multiplicative reduction above the prime 30965771,
and an element of the projection of that union to one summand, obtained from a theta value by a
permutation of labels allowed by the indeterminacy (Ind1), that does not lie in the module through which
Step (v) bounds that component; the corresponding component of the hull therefore has larger log-volume
than the bound obtained in Step (v).

No assertion is made about Corollary 3.12 itself, the final global inequality of Theorem 1.10, or the
abc conjecture. This is a preprint; it has not been refereed.

The first report in this repository compared a different datum, at the prime 211, with the local
estimates of IUT IV; the source application of that comparison was withdrawn in its version 0.1.7. This
note is a separate paper, not a revision of the first report: its datum has two places above the prime,
both of multiplicative reduction, and it neither cites nor relies on the first report.

## Files

```
paper/stepv_local_noncontainment.pdf   the note (6 pages)
paper/stepv_local_noncontainment.tex   its LaTeX source, bibliography included
LICENSE                                Creative Commons Attribution 4.0 International (CC BY 4.0)
SHA256SUMS                             SHA-256 checksums of the files above
```

## Building the PDF

```
cd paper
pdflatex -interaction=nonstopmode -halt-on-error stepv_local_noncontainment.tex
pdflatex -interaction=nonstopmode -halt-on-error stepv_local_noncontainment.tex
```

The supplied PDF has six pages. Rebuilding may change PDF metadata and byte checksums even when the
pages are unchanged.

## Use of generative AI

Generative AI tools (large language models: Claude by Anthropic, and ChatGPT and Codex by OpenAI) were
used extensively in this work, under the author's direction: in finding the example and its proofs, in
the computations, in checking the statements against the cited sources, and in writing the text. The
author takes full responsibility for the contents of this note.

Copyright 2026 Toshihisa Urahigashi. The files in this folder are licensed under the Creative Commons
Attribution 4.0 International License (CC BY 4.0); see `LICENSE`. The rest of this repository remains
under the Apache License, Version 2.0.
