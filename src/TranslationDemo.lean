import Final

/-!
Run `lake build TranslationDemo` to see the translations below.
The printers in this file only abbreviate the generated syntax; all translations
come from `Final.lean`. A `+` or `-` labels an AC coordinate; `.t` and `.m`
label the WK truth and meaningfulness concepts or roles.
-/

namespace TranslationDemo

open ALCHAC

inductive ConceptName where
| A | B | C
deriving Repr

inductive RoleName where
| r | s
deriving Repr

inductive IndividualName where
| alice | bob
deriving Repr

def σ : Signature where
  Nc := ConceptName
  Nr := RoleName
  Ni := IndividualName

def atomName : ConceptName → String
| .A => "A"
| .B => "B"
| .C => "C"

def roleName : RoleName → String
| .r => "r"
| .s => "s"

def individualName : IndividualName → String
| .alice => "alice"
| .bob => "bob"

def sideName : Side → String
| .positive => "+"
| .negative => "-"

def bitName : Bit → String
| .truth => "t"
| .meaningful => "m"

def wkAtomName (a : ConceptName × Side) : String :=
  atomName a.1 ++ sideName a.2

def targetAtomName (a : (ConceptName × Side) × Bit) : String :=
  wkAtomName a.1 ++ "." ++ bitName a.2

def targetRoleName (r : RoleName × Bit) : String :=
  roleName r.1 ++ "." ++ bitName r.2

def showConcept {sig : Signature} {R : Type}
    (showAtom : sig.Nc → String) (showRole : R → String) : Concept sig R → String
| ⊤ => "⊤"
| ⊥ => "⊥"
| [a]ₐ => showAtom a
| ¬ₜ c => "¬(" ++ showConcept showAtom showRole c ++ ")"
| c ⊓ₜ d => "(" ++ showConcept showAtom showRole c ++ " ⊓ " ++
    showConcept showAtom showRole d ++ ")"
| c ⊔ₜ d => "(" ++ showConcept showAtom showRole c ++ " ⊔ " ++
    showConcept showAtom showRole d ++ ")"
| ∃[r] c => "∃" ++ showRole r ++ ".(" ++ showConcept showAtom showRole c ++ ")"
| ∀[r] c => "∀" ++ showRole r ++ ".(" ++ showConcept showAtom showRole c ++ ")"

def showUIRole {sig : Signature} (showAtom : sig.Nr → String) :
    ALCHUI_Role sig → String
| [r]ᵣ => showAtom r
| 𝒰 => "U"
| r ⊓ᵣ s => "(" ++ showUIRole showAtom r ++ " ∩ " ++ showUIRole showAtom s ++ ")"

def showSentence {sig : Signature} {R : Type}
    (showIndividual : sig.Ni → String) (showAtom : sig.Nc → String)
    (showRole : R → String) : Sentence sig R → String
| a :ₐ c => showIndividual a ++ " : " ++ showConcept showAtom showRole c
| (a, b) :ᵣ r => "(" ++ showIndividual a ++ ", " ++ showIndividual b ++
    ") : " ++ showRole r
| c ⊑ d => showConcept showAtom showRole c ++ " ⊑ " ++
    showConcept showAtom showRole d
| c ≡ d => showConcept showAtom showRole c ++ " ≡ " ++
    showConcept showAtom showRole d
| r ⊑ᵣ s => showRole r ++ " ⊑ᵣ " ++ showRole s

def showWKConcept : ALCH_Concept (wkSignature σ) → String :=
  showConcept wkAtomName roleName

def showTargetConcept : ALCHUI_Concept (targetSignature (wkSignature σ)) → String :=
  showConcept targetAtomName (showUIRole targetRoleName)

def showTargetSentence : ALCHUI_Sentence (targetSignature (wkSignature σ)) → String :=
  showSentence individualName targetAtomName (showUIRole targetRoleName)

def showPolarities (c : ALCH_Concept σ) : String × String :=
  (showWKConcept (polarize σ c .positive),
    showWKConcept (polarize σ c .negative))

def showWKTranslation (c : ALCH_Concept (wkSignature σ)) : String × String :=
  let translated := translateConcept (wkSignature σ) c
  (showTargetConcept translated.1, showTargetConcept translated.2)

def A : ALCH_Concept σ := [ConceptName.A]ₐ
def B : ALCH_Concept σ := [ConceptName.B]ₐ
def C : ALCH_Concept σ := [ConceptName.C]ₐ

def Apos : ALCH_Concept (wkSignature σ) := [(ConceptName.A, .positive)]ₐ
def Bpos : ALCH_Concept (wkSignature σ) := [(ConceptName.B, .positive)]ₐ

/- The first and second entries are the positive and negative coordinates. -/
#eval showPolarities (⊤ : ALCH_Concept σ)       -- (⊤, ⊥)
#eval showPolarities (⊥ : ALCH_Concept σ)       -- (⊥, ⊤)
#eval showPolarities (¬ₜ A)                     -- (A-, A+)
#eval showPolarities (¬ₜ (A ⊓ₜ B))             -- (A- ⊔ B-, A+ ⊓ B+)
#eval showPolarities (¬ₜ (∃[RoleName.r] (A ⊔ₜ B)))
-- The last positive coordinate uses ∀r and an intersection of negative atoms.

/- WK truth and meaningfulness are distinct. In particular, negation needs
   meaningfulness, disjunction needs both operands meaningful, and ∀ needs a
   meaningful witness even when its ordinary universal part is vacuous. -/
#eval showWKTranslation (¬ₜ Apos)
#eval showWKTranslation (Apos ⊔ₜ Bpos)
#eval showWKTranslation (∃[RoleName.r] Apos)
#eval showWKTranslation (∀[RoleName.r] Apos)

/- Inclusion produces a truth GCI and a U-based shared witness. Role inclusion
   produces a truth inclusion and an intersection witness on the same pair.
   Equivalence emits both inclusion directions; a role assertion emits one
   truth assertion. -/
#eval (translateSentence (wkSignature σ) (Apos ⊑ Bpos)).map showTargetSentence
#eval (translateSentence (wkSignature σ) (Apos ≡ Bpos)).map showTargetSentence
#eval (translateSentence (wkSignature σ) (RoleName.r ⊑ᵣ RoleName.s)).map
  showTargetSentence
#eval (translateSentence (wkSignature σ)
  ((IndividualName.alice, IndividualName.bob) :ᵣ RoleName.r)).map showTargetSentence

/- Assertions translate to one truth assertion; their bridges live in B. -/
def premises : List (ALCH_Sentence σ) :=
  [IndividualName.alice :ₐ (∃[RoleName.r] (A ⊔ₜ B)),
    RoleName.r ⊑ᵣ RoleName.s]

def conclusions : List (ALCH_Sentence σ) :=
  [IndividualName.alice :ₐ (∀[RoleName.s] (¬ₜ C))]

#eval (T σ premises).map showTargetSentence
#eval (ALCHAC.B σ premises).map showTargetSentence
#eval (T σ conclusions).map showTargetSentence
#eval (ALCHAC.B σ conclusions).map showTargetSentence
-- B includes the conclusion's names because target models must decode it too.
-- Repeated bridges remain repeated: B is a list traversal, not a deduplicator.
-- The source ¬C appears as C- in T: polarize has already swapped coordinates.

end TranslationDemo
