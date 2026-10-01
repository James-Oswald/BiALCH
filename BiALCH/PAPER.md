# Revised paper

- `source-revised.tex`: standalone revision of `source.tex`; the original is preserved.
- `refs-revised.bib`: cited entries from `refs.bib`, without duplicate keys.
- `FaithfulTranslation.lean`: the separately available formal development.

The revision retains the original title, section structure, introduction,
motivating example, background definitions, and discussion. The original
ALCH syntax and interpretation definitions, including the dotted weak Kleene
and double-dotted AC quantifiers, are copied verbatim. The translations use
τ, μ, π, and ν in displayed equations, with complete mathematical proofs.
There are no references to Lean or its declarations in the manuscript.

## Build

From this directory:

```sh
make paper
```

Requires PDFLaTeX, BibTeX, and latexmk. The PDF is
`tex-build/source-revised.pdf`. Build products and rendered QA pages are ignored
by the local `.gitignore`. `make clean-paper` removes the LaTeX build products.

The bundled, unmodified `aaai2027.sty` and `aaai2027.bst` come from the
[official AAAI-27 author kit](https://aaai.org/authorkit27/), retrieved October 1,
2026. The manuscript retains submission mode (anonymous PDF).

## Mathematical scope

Truth and meaningfulness premises are combined in one classical knowledge base
with coherence axioms. The two conclusions are checked against that same theory.
The paper gives existential semantics to the original blank-node notation and
proves both directions of the model correspondence. The complexity subsection
states the limits of the established result; unsupported complexity and S*
entailment theorems are not reinstated.

The two auxiliary constant notations denote the same fresh concept, preserving
the common value in the original AC constant clause. The separate Lean model
currently permits those two constant coordinates to vary independently.
