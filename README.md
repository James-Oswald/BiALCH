# BiALCH

Lean sources live in `src/`, and the paper sources live in `paper/`.
The Lake project configuration and paper build entry point stay at the root.

## Lean

`src/` contains only `DirectTranslation.lean`, which is the sole Lean module
compiled by `lake build`. The older `Basic.lean` and
`FaithfulTranslation.lean`, along with the former project wrapper and
executable, are kept under `reference/` and are not part of the build.

## Paper

The revised paper source is `paper/source-revised.tex`. Run `make paper` to build
it; LaTeX output is kept in the ignored `tex-build/` directory.
