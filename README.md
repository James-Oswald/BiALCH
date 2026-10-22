# BiALCH

BiALCH formalizes a faithful translation from analytic containment (AC) for ALCH to classical ALCHRU in Lean.

The main result preserves and reflects entailment:

```lean
(Γ ⊨ᴬᶜ Δ) ↔ ((τ (π Γ) ∪ 𝒟 (π Γ) ∪ 𝒟 (π Δ)) ⊨ᶜ τ (π Δ))
```

where 
- `π` is the AC to WK translation,
- `τ` is the WK to classical translation,
- `𝒟` creates bridge axioms relating truth 
and meaningfulness.

## Source files

All active Lean modules live in `src/` and are checked by `lake build`.

| File | Contents |
| --- | --- |
| [Final.lean](src/Final.lean) | The logical languages, truth values, set-based quantifiers, classical/WK/AC semantics, translations, interpretation constructions, and proofs through `MainResult`. |
| [ClassicalTableauProver.lean](src/ClassicalTableauProver.lean) | Signed ALCHRU tableau branches, executable finite search, the small-model proof, and soundness and completeness for `entailmentC`. |
| [TranslationRender.lean](src/TranslationRender.lean) | Formatting and finite enumeration of the set translations used by the demo. |
| [TranslationDemo.lean](src/TranslationDemo.lean) | AC knowledge bases of increasing size, their WK and classical translations, and prover results for the direct classical and translated entailments. |
| [Utils.lean](src/Utils.lean) | A small set library, set-builder syntax, image and membership lemmas, top/bottom notation, and elementary logical helpers. |
| [DefDel.lean](src/DefDel.lean) | The `def∇` and `inductive∇` syntax extensions, which let recursive declarations refer to themselves using `∇`, plus a small list example. |

`Final.lean` develops the proof in two stages:

1. **AC to WK:** `acConceptCoordinates` proves both concept coordinates together by structural induction; `acConceptSupport` selects the positive coordinate, and `acSentenceSupport_iff` lifts this to satisfaction. The entailment directions combine in `A_iff_pi_WK`.
2. **WK to classical:** `translateConceptEncode` preserves truth and meaningfulness together; the decoding lemmas recover them wherever the bridge axioms hold. The sentence and knowledge-base results combine in `entailmentK_iff_classical`, which composes with the first stage to prove `MainResult`.

The classical language includes the universal role and role intersection. These express the meaningfulness witnesses needed by restricted quantifiers and role inclusions. Quantifiers operate on sets of value pairs, and knowledge bases are sets of sentences.

Throughout the source, `I` names an interpretation, `φ` and `ψ` name sentences, `Γ` and `Δ` name knowledge bases, and postfix `*` denotes a set type.

## Build and examples

The repository pins Lean `v4.33.0-rc2` in `lean-toolchain`; with Lean's Elan toolchain manager installed, run from the repository root:

```sh
lake build
```

To display the complete translations and classical entailment comparisons of the example knowledge bases:

```sh
lake build TranslationDemo
```

To render the Myne document from only `src/Final.lean`, build a Myne version
with `[declarationMap]` support and run:

```sh
myne -i src
cd myne-out/tex && latexmk -pdf -interaction=nonstopmode -halt-on-error Final.tex
```

The website is written to `myne-out/html/`, and the TeX source and PDF are
written to `myne-out/tex/`. Each top-level section is a separate website page.
Lean imports continue to support the proof build but are not Myne inputs.

The project is configured in `lakefile.toml`, with `src/` as its source directory and all six modules as library roots.

For a finite indexed signature, `ALCHAC.ClassicalTableau.SmallModel.decideEntailment nc nr ni Γ Δ`
returns a `Bool`. Its correctness theorem states that it returns `true` exactly when the
sets enumerated by `Γ` and `Δ` satisfy `entailmentC`. The search explores complete
atomic labels and role edges, so its running time can grow quickly with the number
of names and subformulas. The largest translation example uses an explicitly checked
three-node counterbranch for its direct classical reading.

## Symbol glossary

Each entry explains the notation's mathematical or programming meaning. Concept constructors describe syntax; their evaluation depends on whether the interpretation is classical, WK, or AC.

### Sets and truth values

| Notation | Meaning |
| --- | --- |
| `α*` | The type of sets whose elements have type `α`. |
| `Γ ∪ Δ` | Union two sets of sentences. |
| `Set α` | A collection of elements of type `α`, represented by a membership condition. |
| `x ∈ X` | The element `x` belongs to the set `X`. |
| `x ∉ X` | The element `x` does not belong to the set `X`. |
| `{f x \| x : α}` | The set of all values of `f x` as `x` ranges over the type `α`. |
| `V₃` | The three WK truth values: true, indeterminate, and false. |
| `𝔱` | The WK value true. |
| `𝔢` | The WK value indeterminate or semantically undefined. |
| `𝔣` | The WK value false. |
| `V₃²` | A pair of WK values recording AC support and refutation. |
| `v⁺` | The first, or support, coordinate of an AC value. |
| `v⁻` | The second, or refutation, coordinate of an AC value. |
| `+ₚ` | The tag selecting the positive coordinate or positive copy of an atom. |
| `-ₚ` | The tag selecting the negative coordinate or negative copy of an atom. |
| `v[s]` | Select the coordinate of `v` indicated by the side tag `s`. |

### Truth-value operations

| Notation | Meaning |
| --- | --- |
| `¬ₖ v` | WK negation exchanges true and false while preserving indeterminacy. |
| `v ∧ₖ w` | WK conjunction is indeterminate if either operand is indeterminate, and otherwise follows classical conjunction. |
| `v ∨ₖ w` | WK disjunction is indeterminate if either operand is indeterminate, and otherwise follows classical disjunction. |
| `∃ₖ X` | Restricted WK existential quantification is true when `X` contains a jointly true role–concept pair and indeterminate when every pair has an indeterminate coordinate. |
| `∀ₖ X` | Restricted WK universal quantification is true when every true role coordinate has a true concept coordinate and some pair is jointly meaningful. |
| `∼ₐ v` | AC negation exchanges the support and refutation coordinates. |
| `v ∧ₐ w` | AC conjunction conjoins support and disjoins refutation using WK operations. |
| `v ∨ₐ w` | AC disjunction disjoins support and conjoins refutation using WK operations. |
| `∃ₐ X` | AC existential quantification combines existential support with universal refutation over the positive role coordinates. |
| `∀ₐ X` | AC universal quantification combines universal support with existential refutation over the positive role coordinates. |

### Concepts, roles, and sentences

| Notation | Meaning |
| --- | --- |
| `𝒞 σ` | The type of ALCH concepts over signature `σ` (using atomic roles). |
| `𝒞ᵁ σ` | The type of ALCHRU concepts over `σ` (allowing the universal role and role intersection.) |
| `ℛᵁ σ` | The type of ALCHRU roles (built from atomic roles, the universal role, and intersections). |
| `Φ σ` | The type of ALCH sentences over `σ` (using atomic roles). |
| `Φᵁ σ` | The type of ALCHRU sentences over `σ` (allowing universal and intersection roles). |
| `⊤` | The top concept, classically satisfied by every domain element. |
| `⊥` | The bottom concept, classically satisfied by no domain element. |
| `[a]ₐ` | Treat the atomic concept name `a` as a concept expression. |
| `¬ₜ c` | Form the negation of concept `c`. |
| `c ⊓ₜ d` | Form the conjunction of concepts `c` and `d`. |
| `c ⊔ₜ d` | Form the disjunction of concepts `c` and `d`. |
| `∃[r] c` | Form the existential restriction of concept `c` along role `r`. |
| `∀[r] c` | Form the universal restriction of concept `c` along role `r`. |
| `[r]ᵣ` | Treat the atomic role name `r` as a role expression. |
| `r ⊓ᵣ s` | Form the intersection of two roles. |
| `𝒰` | The universal role, classically relating every pair of domain elements. |
| `a :ₐ c` | Assert that individual `a` satisfies concept `c`. |
| `(a, b) :ᵣ r` | Assert that role `r` relates individuals `a` and `b`. |
| `c ⊑ d` | Assert concept inclusion from `c` to `d`. |
| `c ≡ d` | Assert concept equivalence through inclusion in both directions. |
| `r ⊑ᵣ s` | Assert role inclusion from `r` to `s`. |
| `∃₁ c` | Assert that at least one domain element satisfies the classical concept `c`. Defined as the ALCHRU sentence `⊤ ⊑ ∃[𝒰] c` |
| `r ⨅⁺ s` | Assert that the two classical atomic roles hold on at least one common pair of domain elements. Defined as the ALCHRU sentence `∃₁(∃[([r]ᵣ ⊓ᵣ [s]ᵣ)] ⊤)` |

### Interpretations and consequence

| Notation | Meaning |
| --- | --- |
| `ℐᶜ σ` | The type of classical interpretations over signature `σ`. |
| `ℐᵂᴷ σ` | The type of WK interpretations over signature `σ`. |
| `ℐᴬᶜ σ` | The type of AC interpretations over signature `σ`. |
| `Δᴵ` | The nonempty domain of the interpretation currently in scope. |
| `aᴵ` | Interpret a name or expression using the interpretation currently in scope. |
| `a^I` | Interpret a name or expression using the explicitly supplied interpretation `I`. |
| `I ⊨ᶜ φ` | The classical interpretation `I` satisfies sentence `φ`. |
| `I ⊨ᵂᴷ φ` | The WK interpretation `I` assigns sentence `φ` the value true. |
| `I ⊨ᴬᶜ φ` | The AC interpretation `I` assigns sentence `φ` a true support coordinate. |
| `Γ ⊨ᶜ Δ` | Every classical interpretation satisfying all of `Γ` satisfies all of `Δ`. |
| `Γ ⊨ᵂᴷ Δ` | Every WK interpretation satisfying all of `Γ` satisfies all of `Δ`. |
| `Γ ⊨ᴬᶜ Δ` | Every AC interpretation satisfying all of `Γ` satisfies all of `Δ`. |

### Translations and interpretation constructions

| Notation | Meaning |
| --- | --- |
| `σᵂᴷ` | The signature with positive and negative copies of each concept name and the original role and individual names. |
| `σᵀ` | The signature with truth and meaningfulness copies of each concept and role name and the original individual names. |
| `π c` | Translate an AC concept into a WK concept recording its support coordinate. |
| `π φ` | Translate an AC sentence into the WK sentence that preserves its satisfaction. |
| `π Γ` | Translate every sentence in an AC knowledge base to WK. |
| `τ c` | Translate a WK concept into a classical concept expressing that its value is true. |
| `μ c` | Translate a WK concept into a classical concept expressing that its value is meaningful. |
| `τ φ` | Translate a WK sentence into classical sentences expressing its truth, including any required meaningfulness witnesses. |
| `τ Γ` | Collect the classical sentence translations of every sentence in a WK knowledge base. |
| `𝕋` | The tag for the truth copy of an atomic concept or role. |
| `𝕄` | The tag for the meaningfulness copy of an atomic concept or role. |
| `𝒟 a`, `𝒟 r` | The bridge axiom requiring an atomic concept's or role's truth copy to imply its meaningfulness copy. |
| `𝒟 c`, `𝒟 φ`, `𝒟 Γ` | Collect the bridge axioms for the atomic names occurring in a concept, sentence, or knowledge base. |
| `○I` | Project an AC interpretation to WK by splitting concept coordinates and retaining positive role coordinates. |
| `●I` | Lift a WK interpretation to AC by pairing concept copies and assigning indeterminate negative role coordinates. |
| `□I` | Encode a WK interpretation classically using separate truth and meaningfulness predicates. |
| `■I` | Decode a classical interpretation to WK by reading its truth and meaningfulness predicates. |
| `τ (π Γ)` | Translate an AC knowledge base all the way to classical sentences. |
| `𝒟 (π Γ)` | Collect the classical bridge axioms needed for the names in an AC knowledge base. |

### Recursive declaration syntax

| Notation | Meaning |
| --- | --- |
| `def∇` | Define a recursive function whose body may refer to the function itself using `∇`. |
| `inductive∇` | Define an inductive type whose constructors may refer to the type itself using `∇`. |
| `∇` | Refer to the current recursive function or inductive type with its declaration parameters already supplied. |

## Other directories

- `paper/` contains the original and revised manuscripts, bibliographies, and LaTeX support files.
- `reference/` preserves historical Lean developments outside the active build.
- `.github/` contains the GitHub Actions configuration for Lean continuous integration.
- `.vscode/` contains editor settings for working on the repository.
- `.lake/` contains local Lake dependencies and generated Lean build artifacts.
- `tex-build/` contains generated LaTeX build output.
- `.git/` contains the repository's version history and Git metadata.
