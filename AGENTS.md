# Agent guidance

Keep context small. Start with only the Lean source file(s) named by the task:
`Basic.lean`, `DirectTranslation.lean`, and `FaithfulTranslation.lean`. Read other
files only when the task requires them. For paper work, prefer `PAPER.md`; read
`Reviews.md` or TeX sources only when specifically needed.

## Never inspect generated build output

- Do not list, search, open, summarize, or otherwise read anything under
  `tex-build/`, `tex-qa/`, `.lake/`, or `build/` (including Lake packages and
  caches).
- Exclude those directories from every file listing and search. For example:
  `rg --glob '!tex-build/**' --glob '!tex-qa/**' --glob '!.lake/**' --glob '!build/**' ...`
- Do not read generated TeX files such as `.aux`, `.log`, `.fls`, `.fdb_latexmk`,
  `.synctex.gz`, or generated PDFs.

## Scope

- Avoid broad repository dumps and recursive reads. Use targeted searches and
  inspect only the relevant declarations and nearby code.
- Do not read TeX sources, bibliography/style files, or paper build configuration
  for Lean-code tasks.
- Make the smallest change that satisfies the task. Run `lake build` when the
  user asks for verification or a change affects Lean definitions or proofs.
