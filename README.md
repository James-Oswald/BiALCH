# BiALCH

Lean formalizations and the paper sources live at the repository root alongside
the Lake project configuration.

## Lean

Run `lake build` to compile the maintained `DirectTranslation.lean` and
`FaithfulTranslation.lean` developments through `BiALCH.lean`. `Basic.lean` is
an older, unfinished prototype and is excluded from the default build.

## Paper

The revised paper source is `source-revised.tex`. Run `make paper` to build it;
LaTeX output is kept in the ignored `tex-build/` directory.
