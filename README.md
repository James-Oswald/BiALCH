# BiALCH

Lean sources live in `src/`, and the paper sources live in `paper/`.
The Lake project configuration and paper build entry point stay at the root.

## Lean

Run `lake build` to compile `src/DirectTranslation.lean` through
`src/BiALCH.lean`. `src/Basic.lean` and `src/FaithfulTranslation.lean` are kept
for reference and excluded from the default build.

## Paper

The revised paper source is `paper/source-revised.tex`. Run `make paper` to build
it; LaTeX output is kept in the ignored `tex-build/` directory.
