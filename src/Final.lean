import DefDel
import Utils

namespace ALCHAC

/-- Operator overload for superscript WK -/
class ToWK (α : Type u) (γ : outParam (Type w)) where
  wkIze : α → γ

postfix:max "ᵂᴷ" => ToWK.wkIze

/-- Operator overload for superscript AC -/
class ToAC (α : Type u) (γ : outParam (Type w)) where
  acIze : α → γ

postfix:max "ᴬᶜ" => ToAC.acIze

/-- Operator overload for superscript C -/
class ToC (α : Type u) (γ : outParam (Type w)) where
  cIze : α → γ

postfix:max "ᶜ" => ToC.cIze


-- MARK: Truth Values
/- # Truth Values -/

/-- The type of Weak kleene truth values 𝔱 , 𝔢 , and 𝔣 -/
inductive V₃ where
| t
| e
| f
deriving DecidableEq, Repr

notation "𝔱" => V₃.t
notation "𝔢" => V₃.e
notation "𝔣" => V₃.f

/-- Pairs of weak kleene truth values -/
abbrev V32 := V₃ × V₃
notation "V₃²" => V32

-- MARK: WK Operators
/- # Weak Kleene Operators -/

/-- Negation of weak kleene truth values -/
def negK : V₃ → V₃
| 𝔱 => 𝔣
| 𝔢 => 𝔢
| 𝔣 => 𝔱

/-- Conjunction of weak kleene truth values -/
def andK : V₃ → V₃ → V₃
| 𝔢, _
| _, 𝔢 => 𝔢
| 𝔱, 𝔱 => 𝔱
| _, _ => 𝔣

/-- Disjunction of weak kleene truth values -/
def orK : V₃ → V₃ → V₃
| 𝔢, _
| _, 𝔢 => 𝔢
| 𝔣, 𝔣 => 𝔣
| _, _ => 𝔱

prefix:70 "¬ₖ " => negK
infixl:70 " ∧ₖ " => andK
infixl:65 " ∨ₖ " => orK


/-- Fergusonian Restricted existential quantifier -/
noncomputable def paperExists (X : Set V₃²) : V₃ := by
  classical
  exact
  -- 𝔱 if any pair is (𝔱, 𝔱)
  if H1: ⟨𝔱, 𝔱⟩ ∈ X then
    𝔱
  -- 𝔢 if all pairs have an 𝔢 component
  else if H2: ∀ x ∈ X, x.1 = 𝔢 ∨ x.2 = 𝔢 then
    𝔢
  -- 𝔣 if no pair is (𝔱, 𝔱) and there is at least
  -- one pair without an 𝔢 component
  else if H3: ⟨𝔱, 𝔱⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔣
  -- Impossible case
  else by grind only -- Impossible case

/-- Fergusonian Restricted universal quantifier -/
noncomputable def paperForall (X : Set V₃²) : V₃ := by
  classical
  exact
  -- 𝔱 if no pair is (𝔱, 𝔣) or (𝔱, 𝔢) and there is at
  -- least one pair without an 𝔢 component
  if H1: ⟨𝔱, 𝔣⟩ ∉ X ∧ ⟨𝔱, 𝔢⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔱
  -- 𝔢 if all pairs have an 𝔢 component
  else if H2: ∀ x ∈ X, x.1 = 𝔢 ∨ x.2 = 𝔢 then
    𝔢
  -- 𝔣 if no pair is (𝔱, 𝔣) or (𝔱, 𝔢) and there is
  --at least one pair without an 𝔢 component
  else if H3: (⟨𝔱, 𝔣⟩ ∈ X ∨ ⟨𝔱, 𝔢⟩ ∈ X) ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔣
  else by grind only -- Impossible case

noncomputable def existsK {D : Type} (r c : D → V₃) : V₃ :=
  paperExists (Set.range (λ x => (r x, c x)))

noncomputable def forallK {D : Type} (r c : D → V₃) : V₃ :=
  paperForall (Set.range (λ x => (r x, c x)))

notation "∃ₖ[" r "]" c:75 => existsK r c
notation "∀ₖ[" r "]" c:75 => forallK r c

-- The following indexed-family characterizations are used only to state and
-- prove convenient truth/meaningfulness lemmas. The semantic operators above are
-- defined by the paper's set clauses.
private noncomputable def existsKIndexed {D : Type} (r c : D → V₃) : V₃ := by
  classical
  exact if ∃ x, r x = 𝔱 ∧ c x = 𝔱 then 𝔱
    else if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then 𝔣
    else 𝔢

private noncomputable def forallKIndexed {D : Type} (r c : D → V₃) : V₃ := by
  classical
  exact if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then
    if ∀ x, r x = 𝔱 → c x = 𝔱 then 𝔱 else 𝔣
    else 𝔢


-- MARK: AC Operators
/- # AC Operators -/

def negA (v : V₃²) : V₃² := (v.2, v.1)
def andA (v w : V₃²) : V₃² := (v.1 ∧ₖ w.1, v.2 ∨ₖ w.2)
def orA (v w : V₃²) : V₃² := (v.1 ∨ₖ w.1, v.2 ∧ₖ w.2)

prefix:70 "∼ₐ " => negA
infixl:70 " ∧ₐ " => andA
infixl:65 " ∨ₐ " => orA

noncomputable def existsA {D : Type} (r c : D → V₃²) : V₃² :=
  (∃ₖ[(λ x => (r x).1)] (λ x => (c x).1),
   ∀ₖ[(λ x => (r x).1)] (λ x => (c x).2))

noncomputable def forallA {D : Type} (r c : D → V₃²) : V₃² :=
  (∀ₖ[(λ x => (r x).1)] (λ x => (c x).1),
   ∃ₖ[(λ x => (r x).1)] (λ x => (c x).2))

notation "∃ₐ[" r "]" c:75 => existsA r c
notation "∀ₐ[" r "]" c:75 => forallA r c

-- MARK: Language
/- # ALCH(RU) Language -/

structure Signature where
  Nc : Type
  [reprNc : Repr Nc]
  Nr : Type
  [reprNr : Repr Nr]
  Ni : Type
  [reprNi : Repr Ni]

attribute [instance] Signature.reprNc
attribute [instance] Signature.reprNr
attribute [instance] Signature.reprNi

/--
The type of ALCHRU Roles (ALCHRU role language).
-/
inductive∇ ALCHRU_Role (σ : Signature) where
| atom : σ.Nr → ∇
| universal : ∇
| inter : ∇ → ∇ → ∇
notation "ℛᵁ" => ALCHRU_Role

/--
The type of generalized Concepts (The concept language).
The role type is parameterized such that we can
get ALCH by using the atomic roles from the signature,
and ALCHRU by using the roles from the ALCHRU role language.
-/
inductive∇ Concept (σ : Signature) (R : Type) where
| top
| bot
| atom : σ.Nc → ∇
| neg : ∇ → ∇
| conj : ∇ → ∇ → ∇
| disj : ∇ → ∇ → ∇
| ex : R → ∇ → ∇
| all : R → ∇ → ∇
deriving Repr

/-- The type of ALCH Concepts (ALCH Concept Language). -/
abbrev ALCH_Concept (σ : Signature) := Concept σ σ.Nr
notation "𝒞" => ALCH_Concept

/-- The type of ALCHRU Concepts (ALCHRU Concept Language). -/
abbrev ALCHRU_Concept (σ : Signature) := Concept σ (ℛᵁ σ)
notation "𝒞ᵁ" => ALCHRU_Concept

/--
The type of generalized Sentences (The sentence language).
The role type is parameterized such that we can
get ALCH by using the atomic roles from the signature,
and ALCHRU by using the roles from the ALCHRU role language.
-/
inductive∇ Sentence (σ : Signature) (R : Type) where
| isa : σ.Ni → Concept σ R → ∇
| role : σ.Ni → σ.Ni → R → ∇
| sub : Concept σ R → Concept σ R → ∇
| equiv : Concept σ R → Concept σ R → ∇
| rsub : R → R → ∇
deriving Repr

/-- The type of ALCH Sentences -/
abbrev ALCH_Sentence (σ : Signature) := Sentence σ σ.Nr
notation "Φ" => ALCH_Sentence

/-- The type of ALCHRU Sentences -/
abbrev ALCHRU_Sentence (σ : Signature) := Sentence σ (ℛᵁ σ)
notation "Φᵁ" => ALCHRU_Sentence

variable {σ : Signature}

-- Concept Notations
instance : Top (Concept σ R) := ⟨.top⟩
instance : Bot (Concept σ R) := ⟨.bot⟩
instance : Coe σ.Nc (Concept σ R) := ⟨Concept.atom⟩
notation "[" a "]ₐ" => Concept.atom a
infixl:70 " ⊓ₜ " => Concept.conj
infixl:65 " ⊔ₜ " => Concept.disj
notation "¬ₜ " c:75 => Concept.neg c
notation "∃[" r "]" c:75 => Concept.ex r c
notation "∀[" r "]" c:75 => Concept.all r c

/-- Role Notations -/
notation "[" r "]ᵣ" => ALCHRU_Role.atom r
infixl:70 " ⊓ᵣ " => ALCHRU_Role.inter
notation "𝒰" => ALCHRU_Role.universal

/-- Sentence Notations -/
notation a " :ₐ " c:50 => Sentence.isa a c
notation "(" a ", " b ")" " :ᵣ " r:50 => Sentence.role a b r
infix:50 " ⊑ " => Sentence.sub
infix:50 " ≡ " => Sentence.equiv
infix:50 " ⊑ᵣ " => Sentence.rsub

-- MARK: Interpretations
/- # Interpretations -/

/--
The type of interpretations on a signature.
Parameterized over the type of truth values V,
which allows us to use this structure to define
classical, WK, and AC interpretations.
-/
structure Interpretation (σ : Signature) (V : Type) where
  D : Type
  inhabited : Nonempty D
  individualValuation : σ.Ni → D
  atomicConceptValuation : σ.Nc → D → V
  roleValuation : σ.Nr → D → D → V

attribute [class] Interpretation

/--
The type of classical Interpretations.
Uses the two-valued type (`Prop`) for valuations.
-/
abbrev CInterpretation (σ : Signature) :=
  Interpretation σ Prop
notation "ℐᶜ" => CInterpretation

/--
The type of Weak Kleene Interpretations
Uses the three-valued Kleene domain (`V₃`) for valuations.
-/
abbrev WKInterpretation (σ : Signature) :=
  Interpretation σ V₃
notation "ℐᵂᴷ" => WKInterpretation

/-- The type of Analytic Containment Interpretations.
Uses pairs of three-valued Kleene (`V₃²`) for valuations.
-/
abbrev ACInterpretation (σ : Signature) :=
  Interpretation σ V₃²
notation "ℐᴬᶜ" => ACInterpretation

-- MARK: Interpretation Notation
/-! # Interpretation Notation -/
/-!
The rest of this section is alot of class slop that allows
us to use the current interpretation as a class instance,
so that we can use superscript I notation to denote
interpreting individuals, roles, concepts, and sentences
in a nice way.
-/

/-- Interpret a syntax object using the current interpretation. -/
class Interpret (σ : Signature) (V : Type) (α : Type u) where
  Result : Interpretation σ V → Type
  interpret (I : Interpretation σ V) : α → Result I

instance : Interpret σ V σ.Ni where
  Result I := I.D
  interpret I := I.individualValuation

instance : Interpret σ V σ.Nr where
  Result I := I.D → I.D → V
  interpret I := I.roleValuation

instance : Interpret σ V σ.Nc where
  Result I := I.D → V
  interpret I := I.atomicConceptValuation


/--
Interpret syntax using whichever interpretation is
available as a class instance.
-/
class InterpretCurrent (σ : Signature) (α : Type u) where
  Result : Type
  interpret : α → Result

instance [I : ℐᶜ σ] [h : Interpret σ Prop α] :
InterpretCurrent σ α where
  Result := h.Result I
  interpret := h.interpret I

instance [I : ℐᵂᴷ σ] [h : Interpret σ V₃ α] :
InterpretCurrent σ α where
  Result := h.Result I
  interpret := h.interpret I

instance [I : ℐᴬᶜ σ] [h : Interpret σ V₃² α] :
InterpretCurrent σ α where
  Result := h.Result I
  interpret := h.interpret I

set_option quotPrecheck false in
postfix:max "ᴵ" => InterpretCurrent.interpret (σ := σ)

set_option quotPrecheck false in
notation "Δᴵ" => InterpretCurrent.Result (σ := σ) (α := σ.Ni)

-- MARK: C Semantics
/- # Classical Semantics -/

/-- Classical Role evaluation for ALCHRU -/
def∇ evalRoleC [ℐᶜ σ] : ℛᵁ σ → Δᴵ → Δᴵ → Prop
| [r]ᵣ, x, y => rᴵ x y
| 𝒰, _, _ => True
| r ⊓ᵣ s, x, y => ∇ r x y ∧ ∇ s x y

/-- ·ᴵ for ALCHRU roles in classical semantics -/
instance : Interpret σ Prop (ℛᵁ σ) :=
  ⟨λ I => I.D → I.D → Prop, λ_=>evalRoleC⟩

-- Classical Concept evaluation on ALCHRU concepts
def∇ evalConceptC [ℐᶜ σ] : 𝒞ᵁ σ → Δᴵ → Prop
| ⊤, _ => True
| ⊥, _ => False
| [C]ₐ, x => Cᴵ x
| ¬ₜC, x => ¬(∇ C x)
| C ⊓ₜ D, x => (∇ C x) ∧ (∇ D x)
| C ⊔ₜ D, x => ∇ C x ∨ (∇ D x)
| ∃[R] C, x => ∃ y, Rᴵ x y ∧ ∇ C y
| ∀[R] C, x => ∀ y, Rᴵ x y → ∇ C y

/-- ·ᴵ for ALCHRU concepts in classical semantics -/
instance : Interpret σ Prop (𝒞ᵁ σ) :=
  ⟨(·.D → Prop), λ_=> evalConceptC⟩

/-- Classical sentence semantics for ALCHRU. -/
def evalSentenceC [ℐᶜ σ] : Φᵁ σ → Prop
| a :ₐ C => Cᴵ aᴵ
| (a, b) :ᵣ R => Rᴵ aᴵ bᴵ
| C ⊑ D => ∀ x, Cᴵ x → Dᴵ x
| C ≡ D => ∀ x, Cᴵ x ↔ Dᴵ x
| R ⊑ᵣ S => ∀ x y, Rᴵ x y → Sᴵ x y

notation  I "⊨ᶜ " S => @evalSentenceC _ I S

/-- Classical entailment for ALCHRU. -/
def entailmentC (Γ Δ : List (Φᵁ σ)) : Prop :=
  ∀ I, (∀ ψ ∈ Γ, I ⊨ᶜ ψ) → (∀ φ ∈ Δ, I ⊨ᶜ φ)

notation  Γ " ⊨ᶜ " Δ => entailmentC Γ Δ

-- MARK: WK Semantics
/- # Weak Kleene Semantics -/

/-- Weak Kleene concept semantics for ALCHRU. -/
noncomputable def∇ evalConceptK [ℐᵂᴷ σ] : 𝒞 σ → Δᴵ → V₃
| ⊤, _ => 𝔱
| ⊥, _ => 𝔣
| [a]ₐ, x => aᴵ x
| ¬ₜ C, x => ¬ₖ(∇ C x)
| C ⊓ₜ D, x => (∇ C x) ∧ₖ (∇ D x)
| C ⊔ₜ D, x => (∇ C x) ∨ₖ (∇ D x)
| ∃[R] C, x => ∃ₖ[Rᴵ x] (∇ C)
| ∀[R] C, x => ∀ₖ[Rᴵ x] (∇ C)

/-- ·ᴵ for ALCHRU concepts in weak Kleene semantics -/
noncomputable instance : Interpret σ V₃ (𝒞 σ) :=
  ⟨(·.D → V₃), λ_=> evalConceptK⟩

/-- Weak Kleene sentence semantics for ALCHRU. -/
noncomputable def evalSentenceK [ℐᵂᴷ σ] : Φ σ → V₃
| a :ₐ C => Cᴵ aᴵ
| (a, b) :ᵣ r => rᴵ aᴵ bᴵ
| C ⊑ D => ∀ₖ[Cᴵ] Dᴵ
| C ≡ D => (∀ₖ[Cᴵ] Dᴵ) ∧ₖ (∀ₖ[Dᴵ] Cᴵ)
| R ⊑ᵣ S => ∀ₖ[(λ p : Δᴵ × Δᴵ => Rᴵ p.1 p.2)] (λ p => Sᴵ p.1 p.2)

/-- ·ᴵ for ALCHRU sentences in weak Kleene semantics -/
noncomputable instance : Interpret σ V₃ (Φ σ) :=
  ⟨λ_=>V₃, λ_=> evalSentenceK⟩

/-- Satisfaction relation for weak Kleene semantics -/
def satisfiesK [ℐᵂᴷ σ] (φ : Φ σ) : Prop :=
  φᴵ = 𝔱

notation  I "⊨ᴷ " S => @satisfiesK _ I S

/-- Entailment for weak Kleene semantics -/
def entailmentK (Γ Δ : List (Φ σ)) : Prop :=
  ∀ (I : ℐᵂᴷ σ), (∀ ψ ∈ Γ, I ⊨ᴷ ψ) → (∀ φ ∈ Δ, I ⊨ᴷ φ)

notation  Γ " ⊨ᴷ " Δ => entailmentK Γ Δ

-- MARK: AC Semantics
/- # Analytic Containment Semantics -/

noncomputable def∇ evalConceptA [ℐᴬᶜ σ] : 𝒞 σ → Δᴵ → V₃²
| ⊤, _ => (𝔱, 𝔣)
| ⊥, _ => (𝔣, 𝔱)
| [a]ₐ, x => aᴵ x
| ¬ₜ c, x => ∼ₐ(∇ c x)
| c ⊓ₜ d, x => (∇ c x) ∧ₐ (∇ d x)
| c ⊔ₜ d, x => (∇ c x) ∨ₐ (∇ d x)
| ∃[r] c, x => ∃ₐ[rᴵ x] (∇ c)
| ∀[r] c, x => ∀ₐ[rᴵ x] (∇ c)

noncomputable instance : Interpret σ V₃² (𝒞 σ) :=
  ⟨(·.D → V₃²), λ_=>evalConceptA⟩

noncomputable def evalSentenceA [ℐᴬᶜ σ] : Φ σ → V₃²
| a :ₐ c => cᴵ aᴵ
| (a, b) :ᵣ r => rᴵ aᴵ bᴵ
| c ⊑ d => ∀ₐ[cᴵ] dᴵ
| c ≡ d => (∀ₐ[cᴵ] dᴵ) ∧ₐ (∀ₐ[dᴵ] cᴵ)
| r ⊑ᵣ s => ∀ₐ[(λ p : Δᴵ × Δᴵ => rᴵ p.1 p.2)] (λ p => sᴵ p.1 p.2)

noncomputable instance : Interpret σ V₃² (Φ σ) :=
  ⟨λ_=>V₃²,λ_=>evalSentenceA⟩

def satisfiesA [ℐᴬᶜ σ] (φ : Φ σ) : Prop :=
  (φᴵ : V₃²).1 = 𝔱

notation  I "⊨ᴬ " S => @satisfiesA _ I S

def entailmentA (Γ Δ : List (Φ σ)) : Prop :=
  ∀ (I : ℐᴬᶜ σ), (∀ ψ ∈ Γ, I ⊨ᴬ ψ) → (∀ φ ∈ Δ, I ⊨ᴬ φ)

notation  Γ " ⊨ᴬ " Δ => entailmentA Γ Δ

-- MARK: AC to WK
/-! # AC to WK Translation -/
/-!
The main idea of the AC to WK translation is to
*polarize* all concepts in an ALCH sentence according to
their syntactic position, transforming it into a weak
kleene sentence. Polarization pushes negations down
as far as possible, ensuring that the resulting concept
is in a form suitable for weak Kleene evaluation.

-/

/--
WK side indicator for polarizing concepts (+ₚ or -ₚ).
-/
inductive Side where
| positive
| negative
deriving DecidableEq, Repr

notation "+ₚ" => Side.positive
notation "-ₚ" => Side.negative

/--
Given a signature σ, the weak Kleene signature
σᵂᴷ is defined by pairing each original concept with
a side indicator (+ₚ or -ₚ)
-/
abbrev wkSignature (σ : Signature) : Signature where
  Nc := σ.Nc × Side
  Nr := σ.Nr
  Ni := σ.Ni

/-- σᵂᴷ shorthand for the weak Kleene signature of σ -/
instance toWKSignature : ToWK Signature Signature where
  wkIze := wkSignature

/--
Polarize recursively transforms an ALCH concept into its
weak Kleene counterpart based on the given side indicator
(+ₚ or -ₚ).
-/
def∇ polarizeConcept {σ : Signature} : 𝒞 σ → Side → 𝒞 σᵂᴷ
| ⊤, +ₚ => ⊤
| ⊤, -ₚ => ⊥
| ⊥, +ₚ => ⊥
| ⊥, -ₚ => ⊤
| [a]ₐ, side => [(a, side)]ₐ
| ¬ₜc, +ₚ => ∇ c -ₚ
| ¬ₜc, -ₚ => ∇ c +ₚ
| c ⊓ₜ d, +ₚ => (∇ c +ₚ) ⊓ₜ (∇ d +ₚ)
| c ⊓ₜ d, -ₚ => (∇ c -ₚ) ⊔ₜ (∇ d -ₚ)
| c ⊔ₜ d, +ₚ => (∇ c +ₚ) ⊔ₜ (∇ d +ₚ)
| c ⊔ₜ d, -ₚ => (∇ c -ₚ) ⊓ₜ (∇ d -ₚ)
| ∃[r] c, +ₚ => ∃[r] ∇ c +ₚ
| ∃[r] c, -ₚ => ∀[r] ∇ c -ₚ
| ∀[r] c, +ₚ => ∀[r] ∇ c +ₚ
| ∀[r] c, -ₚ => ∃[r] ∇ c -ₚ

notation C "ᵖ⁺" => polarizeConcept C +ₚ
notation C "ᵖ⁻" => polarizeConcept C -ₚ
postfix:max "ᵖ" => polarizeConcept

/--
Polarizes an ALCH sentence over the original signature
σ to its weak Kleene counterpart over the signature σᵂᴷ
by polarizing all concepts positively.
-/
def polarizeSentence (σ : Signature) : Φ σ → Φ σᵂᴷ
| a :ₐ c => a :ₐ cᵖ⁺
| (a, b) :ᵣ r => (a, b) :ᵣ r
| c ⊑ d => cᵖ⁺ ⊑ dᵖ⁺
| c ≡ d => cᵖ⁺ ≡ dᵖ⁺
| r ⊑ᵣ s => r ⊑ᵣ s

abbrev polarizeSentenceSet (σ : Signature) :
List (Φ σ) → List (Φ σᵂᴷ) :=
  List.map (polarizeSentence σ)

instance : ToWK (List (Φ σ)) (List (Φ σᵂᴷ)) where
  wkIze := polarizeSentenceSet _

def coordinate (v : V₃²) : Side → V₃
| +ₚ => v.1
| -ₚ => v.2

-- So we can use v[+ₚ] and v[-ₚ] to access the
-- respective components of a V₃² vector.
instance : GetElem (V₃²) Side V₃ (λ _ _ => True) where
  getElem := λ v s _ => coordinate v s

def acToWK (I : ℐᴬᶜ σ) : ℐᵂᴷ σᵂᴷ where
  D :=                      I.D
  inhabited :=              I.inhabited
  individualValuation :=    I.individualValuation
  atomicConceptValuation := λ (a, s) x => ((I.atomicConceptValuation a) x)[s]
  roleValuation :=          λ r x y => ((I.roleValuation r) x y)[+ₚ]

instance : ToWK (ℐᴬᶜ σ) (ℐᵂᴷ σᵂᴷ) := ⟨acToWK⟩

def wkToAC (K : ℐᵂᴷ σᵂᴷ) : ℐᴬᶜ σ where
  D :=                      K.D
  inhabited :=              K.inhabited
  individualValuation :=    K.individualValuation
  atomicConceptValuation := λ a x => ((K.atomicConceptValuation (a, +ₚ)) x, (K.atomicConceptValuation (a, -ₚ)) x)
  roleValuation :=          λ r x y => ((K.roleValuation r) x y, 𝔢)

instance : ToAC (ℐᵂᴷ σᵂᴷ) (ℐᴬᶜ σ) := ⟨wkToAC⟩




-- MARK: WK Lemmas
/- # WK Lemmas -/

private theorem existsKIndexed_paper {D} (r c : D → V₃) :
    existsKIndexed r c = paperExists (Set.range (fun x => (r x, c x))) := by
  classical
  have hm : (∀ p ∈ Set.range (fun x => (r x, c x)), p.1 = 𝔢 ∨ p.2 = 𝔢) ↔
      ¬ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.forall_mem_range, not_exists, not_and, not_not]
    exact forall_congr' (fun x => or_iff_not_imp_left)
  have ht : ((𝔱, 𝔱) ∈ Set.range (fun x => (r x, c x))) ↔
      ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by simp
  have hw : (∃ p ∈ Set.range (fun x => (r x, c x)), p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) ↔
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.exists_mem_range]
  unfold existsKIndexed paperExists
  by_cases hT : ∃ x, r x = 𝔱 ∧ c x = 𝔱
  · have hT' := ht.mpr hT
    simp [hT, hT']
  · by_cases hW : ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢
    · have hT' : (𝔱, 𝔱) ∉ Set.range (fun x => (r x, c x)) :=
        fun h => hT (ht.mp h)
      have hW' := hw.mpr hW
      have hM' : ¬ (∀ p ∈ Set.range (fun x => (r x, c x)),
          p.1 = 𝔢 ∨ p.2 = 𝔢) := fun h => (hm.mp h) hW
      simp only [hT, hT', hW, hW', hM', ite_false, ite_true,
        dite_false, dite_true, not_false_eq_true, true_and]
    · have hT' : (𝔱, 𝔱) ∉ Set.range (fun x => (r x, c x)) :=
        fun h => hT (ht.mp h)
      simp [hT, hT', hW]

private theorem forallKIndexed_paper {D} (r c : D → V₃) :
    forallKIndexed r c = paperForall (Set.range (fun x => (r x, c x))) := by
  classical
  have hm : (∀ p ∈ Set.range (fun x => (r x, c x)), p.1 = 𝔢 ∨ p.2 = 𝔢) ↔
      ¬ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.forall_mem_range, not_exists, not_and, not_not]
    exact forall_congr' (fun x => or_iff_not_imp_left)
  have hw : (∃ p ∈ Set.range (fun x => (r x, c x)), p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) ↔
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.exists_mem_range]
  have ht : ((𝔱, 𝔣) ∉ Set.range (fun x => (r x, c x)) ∧
      (𝔱, 𝔢) ∉ Set.range (fun x => (r x, c x))) ↔
      ∀ x, r x = 𝔱 → c x = 𝔱 := by
    simp only [Set.mem_range, Prod.mk.injEq, not_exists, not_and]
    constructor
    · rintro ⟨hf, he⟩ x hx
      have hf' := hf x hx
      have he' := he x hx
      cases hcx : c x <;> simp_all
    · intro h
      constructor <;> intro x hx <;> simp [h x hx]
  have htrue : ((𝔱, 𝔣) ∉ Set.range (fun x => (r x, c x)) ∧
      (𝔱, 𝔢) ∉ Set.range (fun x => (r x, c x)) ∧
      ∃ p ∈ Set.range (fun x => (r x, c x)), p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) ↔
      (∀ x, r x = 𝔱 → c x = 𝔱) ∧ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    rw [← and_assoc, ht, hw]
  have hv : ((𝔱, 𝔣) ∈ Set.range (fun x => (r x, c x)) ∨
      (𝔱, 𝔢) ∈ Set.range (fun x => (r x, c x))) ↔
      ∃ x, r x = 𝔱 ∧ c x ≠ 𝔱 := by
    simp only [Set.mem_range, Prod.mk.injEq, ← exists_or]
    constructor
    · rintro ⟨x, (⟨hr, hf⟩ | ⟨hr, he⟩)⟩
      · exact ⟨x, hr, by simp [hf]⟩
      · exact ⟨x, hr, by simp [he]⟩
    · rintro ⟨x, hr, hc⟩
      cases hcx : c x with
      | t => simp [hcx] at hc
      | e => exact ⟨x, Or.inr ⟨hr, hcx⟩⟩
      | f => exact ⟨x, Or.inl ⟨hr, hcx⟩⟩
  unfold forallKIndexed paperForall
  repeat (split) <;> first | rfl | grind only

private theorem existsKIndexed_t {D} (r c : D → V₃) :
    existsKIndexed r c = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  classical
  unfold existsKIndexed
  repeat (split) <;> simp_all

private theorem existsKIndexed_m {D} (r c : D → V₃) :
    existsKIndexed r c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold existsKIndexed
  repeat (split) <;> simp_all
  obtain ⟨x, hx, hy⟩ := ‹∃ x, r x = 𝔱 ∧ c x = 𝔱›
  exact ⟨x, by simp [hx], by simp [hy]⟩

private theorem forallKIndexed_t {D} (r c : D → V₃) :
    forallKIndexed r c = 𝔱 ↔ (∀ x, r x = 𝔱 → c x = 𝔱) ∧
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallKIndexed
  repeat (split) <;> simp_all

private theorem forallKIndexed_m {D} (r c : D → V₃) :
    forallKIndexed r c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallKIndexed
  repeat (split) <;> simp_all

/-- ¬v is 𝔱 iff v is neither 𝔢 nor 𝔱 -/
@[simp]
theorem negK_t (v : V₃) : ¬ₖv = 𝔱 ↔ v ≠ 𝔢 ∧ v ≠ 𝔱 := by
  cases v <;> decide

/-- v is not 𝔢 iff ¬v is not 𝔢 -/
@[simp]
theorem negK_m (v : V₃) : ¬ₖv ≠ 𝔢 ↔ v ≠ 𝔢 := by
  cases v <;> decide

/-- v ∧ₖ w is 𝔱 iff both v and w are 𝔱 -/
@[simp]
theorem andK_t (v w : V₃) : v ∧ₖ w = 𝔱 ↔ v = 𝔱 ∧ w = 𝔱 := by
  cases v <;> cases w <;> decide

/-- v ∧ₖ w is not 𝔢 iff both v and w are not 𝔢 -/
@[simp]
theorem andK_m (v w : V₃) : v ∧ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

/-- v ∨ₖ w is 𝔱 iff at least one of v and w is 𝔱 and both are not 𝔢 -/
@[simp]
theorem orK_t (v w : V₃) : v ∨ₖ w = 𝔱 ↔ (v = 𝔱 ∨ w = 𝔱) ∧ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp]
theorem orK_m (v w : V₃) : v ∨ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp]
theorem existsK_t {D} (r c : D → V₃) :
    ∃ₖ[r] c = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  change paperExists (Set.range (λ x => (r x, c x))) = 𝔱 ↔ _
  rw [← existsKIndexed_paper]
  exact existsKIndexed_t r c

@[simp]
theorem existsK_m {D} (r c : D → V₃) :
    ∃ₖ[r] c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  change paperExists (Set.range (λ x => (r x, c x)) ) ≠ 𝔢 ↔ _
  rw [← existsKIndexed_paper]
  exact existsKIndexed_m r c

@[simp]
theorem forallK_t {D} (r c : D → V₃) :
    ∀ₖ[r] c = 𝔱 ↔ (∀ x, r x = 𝔱 → c x = 𝔱) ∧
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  change paperForall (Set.range (λ x => (r x, c x))) = 𝔱 ↔ _
  rw [← forallKIndexed_paper]
  exact forallKIndexed_t r c

@[simp]
theorem forallK_m {D} (r c : D → V₃) :
    ∀ₖ[r] c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  change paperForall (Set.range (λ x => (r x, c x))) ≠ 𝔢 ↔ _
  rw [← forallKIndexed_paper]
  exact forallKIndexed_m r c

-- theorem existsK_paper {D} (r c : D → V₃) :
-- existsK r c = paperExists (Set.range (λ x => (r x, c x))) := by
--   rfl

-- theorem forallK_paper {D} (r c : D → V₃) :
-- forallK r c = paperForall (Set.range (λ x => (r x, c x))) := by
--   rfl

-- MARK: AC to WK
/-! ## AC to weak Kleene -/



theorem acToWK_wkToAC (K : ℐᵂᴷ σᵂᴷ) : (Kᴬᶜ)ᵂᴷ = K := by
  cases K with
  | mk D inhabited individuals atoms roles =>
      simp only [acToWK, wkToAC, ToAC.acIze, ToWK.wkIze]
      congr 1
      funext a x
      rcases a with ⟨a, side⟩
      cases side <;> rfl

theorem acConceptCoordinates (I : ℐᴬᶜ σ) (c : 𝒞 σ) (s : Side) (x : I.D) :
(@evalConceptK _ (Iᵂᴷ) (cᵖ s)) x = ((@evalConceptA _ I c) x)[s] := by
  induction c generalizing s x with
  | top => cases s <;> rfl
  | bot => cases s <;> rfl
  | atom a => cases s <;> rfl
  | neg c ih => cases s <;> simp only
    [polarizeConcept, evalConceptA, negA, GetElem.getElem, coordinate, ih]
  | conj c d ihc ihd =>
      cases s <;> simp only
        [polarizeConcept, evalConceptK, evalConceptA, andA, GetElem.getElem, coordinate, ihc, ihd]
  | disj c d ihc ihd =>
      cases s <;> simp only
        [polarizeConcept, evalConceptK, evalConceptA, orA, GetElem.getElem, coordinate, ihc, ihd]
  | ex r c ih =>
      cases s with
      | positive => exact congrArg₂ existsK rfl (funext (ih +ₚ))
      | negative => exact congrArg₂ forallK rfl (funext (ih -ₚ))
  | all r c ih =>
      cases s with
      | positive => exact congrArg₂ forallK rfl (funext (ih +ₚ))
      | negative => exact congrArg₂ existsK rfl (funext (ih -ₚ))

theorem acSentenceSupport (I : ℐᴬᶜ σ) (s : Φ σ) :
    @evalSentenceK _ (Iᵂᴷ) (projectSentence σ s) = (@evalSentenceA _ I s)[+ₚ] := by
  have hc (c : 𝒞 σ) :
      (@evalConceptK _ (Iᵂᴷ) (cᵖ⁺)) = fun x => ((@evalConceptA _ I c) x)[+ₚ] :=
    funext (acConceptCoordinates I c +ₚ)
  cases s <;> simp only [InterpretCurrent.interpret, Interpret.interpret, projectSentence, evalSentenceK, evalSentenceA, forallA, andA, hc] <;> rfl

theorem acSentenceSupport_iff (I : ℐᴬᶜ σ) (s : Φ σ) :
    (Iᵂᴷ ⊨ᴷ projectSentence σ s) ↔ (I ⊨ᴬ s) := by
  change @evalSentenceK _ (Iᵂᴷ) (projectSentence σ s) = 𝔱 ↔ (@evalSentenceA _ I s)[+ₚ] = 𝔱
  rw [acSentenceSupport]

/-- The explicit WK entailment intermediate used in the final theorem. -/
theorem entailmentA_iff_projectedWK (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᴬ Δ) ↔ (Γᵂᴷ ⊨ᴷ Δᵂᴷ) := by
  constructor
  · intro h K hΓ q hq
    have hround : (Kᴬᶜ)ᵂᴷ = K := acToWK_wkToAC K
    rcases List.mem_map.mp hq with ⟨s, hs, rfl⟩
    have hsource : ∀ p ∈ Γ, Kᴬᶜ ⊨ᴬ p := by
      intro p hp
      have hk := hΓ (projectSentence σ p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      exact (acSentenceSupport_iff Kᴬᶜ p).mp (hround ▸ hk)
    have hout := h Kᴬᶜ hsource s hs
    exact hround ▸ (acSentenceSupport_iff Kᴬᶜ s).mpr hout
  · intro h I hΓ s hs
    have hprojected : ∀ p ∈ Γᵂᴷ, Iᵂᴷ ⊨ᴷ p := by
      intro p hp
      rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
      exact (acSentenceSupport_iff I q).mpr (hΓ q hq)
    have hout := h Iᵂᴷ hprojected (projectSentence σ s)
      (List.mem_map.mpr ⟨s, hs, rfl⟩)
    exact (acSentenceSupport_iff I s).mp hout

-- MARK: WK to C
/-! ## WK to classical ALCH with universal role and role intersection -/

inductive Bit where
| truth
| meaningful
deriving DecidableEq, Repr

notation "𝕋" => Bit.truth
notation "𝕄" => Bit.meaningful

/-
Given a signature σ, the target signature σᵀ is defined by
pairing each original concept and role with a bit
indicator (truth or meaningful).
-/
abbrev targetSignature (σ : Signature) : Signature where
  Nc := σ.Nc × Bit
  Nr := σ.Nr × Bit
  Ni := σ.Ni

postfix:max "ᵀ" => targetSignature

class ToTau (α : Type u) (γ : outParam (Type w)) where
  tau : α → γ

postfix:max "^τ" => ToTau.tau

class ToMu (α : Type u) (γ : outParam (Type w)) where
  mu : α → γ

postfix:max "^μ" => ToMu.mu

/-- The meaningfulness component of a translated concept. -/
def∇ translateMu {σ : Signature} : 𝒞 σ → 𝒞ᵁ σᵀ
| ⊤
| ⊥ => ⊤
| [a]ₐ => [(a, 𝕄)]ₐ
| ¬ₜc => ∇ c
| c ⊓ₜ d | c ⊔ₜ d => (∇ c) ⊓ₜ (∇ d)
| ∃[r] c | ∀[r] c => ∃[[(r, 𝕄)]ᵣ] (∇ c)

instance (σ : Signature) : ToMu (𝒞 σ) (𝒞ᵁ σᵀ) := ⟨translateMu⟩

/-- The truth component of a translated concept. -/
def∇ translateTau {σ : Signature} : 𝒞 σ → 𝒞ᵁ σᵀ
| ⊤ => ⊤
| ⊥ => ⊥
| [a]ₐ => [(a, 𝕋)]ₐ
| ¬ₜ c => c^μ ⊓ₜ ¬ₜ(∇ c)
| c ⊓ₜ d => (∇ c) ⊓ₜ (∇ d)
| c ⊔ₜ d => ((∇ c) ⊔ₜ (∇ d)) ⊓ₜ (c^μ ⊓ₜ d^μ)
| ∃[r] c => ∃[[(r, 𝕋)]ᵣ] (∇ c)
| ∀[r] c => (∀[[(r, 𝕋)]ᵣ] (∇ c)) ⊓ₜ ∃[[(r, 𝕄)]ᵣ] c^μ

instance (σ : Signature) : ToTau (𝒞 σ) (𝒞ᵁ σᵀ) := ⟨translateTau⟩

@[simp] theorem concept_mu (c : 𝒞 σ) : c^μ = translateMu c := rfl
@[simp] theorem concept_tau (c : 𝒞 σ) : c^τ = translateTau c := rfl

/--
We can express that C is nonempty in classical ALC using
the universal role. ⊤ ⊑ ∃[𝒰] c -> ∀x, ∃y, c(y) -> ∃y, c(y)
-/
def nonempty (c : 𝒞ᵁ σ) : Φᵁ σ :=
  ⊤ ⊑ ∃[𝒰] c

/--
Given a classical interpretation I and a concept c,
I entails nonemptiness of c iff there exists an element x
in the domain of I such that x satisfies c.
-/
@[simp]
theorem nonempty_iff (I : ℐᶜ σ) (c : 𝒞ᵁ σ) :
(I ⊨ᶜ (nonempty c)) ↔ ∃ x, (@evalConceptC _ I c) x := by
  simp only [InterpretCurrent.interpret, Interpret.interpret, nonempty, evalSentenceC, evalConceptC, evalRoleC, true_implies, true_and]
  constructor
  · intro h
    obtain ⟨x⟩ := I.inhabited
    exact h x
  · intro h _
    exact h

/-- Intersection forces both roles to hold on the same ordered pair. -/
def overlap (r s : σ.Nr) : Φᵁ σ :=
  nonempty (∃[([r]ᵣ ⊓ᵣ [s]ᵣ)] ⊤)

/--
Given a classical interpretation I and two roles r and s,
I entails that r and s overlap iff there exist elements x and y
in the domain of I such that both r and s relate x to y.
-/
@[simp] theorem overlap_iff (I : ℐᶜ σ) (r s : σ.Nr) :
(I ⊨ᶜ (overlap r s)) ↔ ∃ x y, (I.roleValuation r) x y ∧ (I.roleValuation s) x y := by
  simp only [InterpretCurrent.interpret, Interpret.interpret, overlap, nonempty_iff, evalConceptC, evalRoleC, and_true]
  rfl

def translateInclusion (σ : Signature) (c d : 𝒞 σ) : List (Φᵁ σᵀ) :=
  [ c^τ ⊑ d^τ, nonempty (c^μ ⊓ₜ d^μ) ]

def translateSentence (σ : Signature) : Φ σ → List (Φᵁ σᵀ)
| a :ₐ c => [a :ₐ c^τ]
| (a, b) :ᵣ r => [(a, b) :ᵣ [(r, 𝕋)]ᵣ]
| c ⊑ d => translateInclusion σ c d
| c ≡ d => translateInclusion σ c d ++ translateInclusion σ d c
| r ⊑ᵣ s => [[(r, 𝕋)]ᵣ ⊑ᵣ [(s, 𝕋)]ᵣ, overlap (r, 𝕄) (s, 𝕄)]

def atomBridge (σ : Signature) (a : σ.Nc) : Φᵁ σᵀ :=
  [(a, 𝕋)]ₐ ⊑ [(a, 𝕄)]ₐ

def roleBridge (σ : Signature) (r : σ.Nr) : Φᵁ σᵀ :=
  [(r, 𝕋)]ᵣ ⊑ᵣ [(r, 𝕄)]ᵣ

def conceptBridges (σ : Signature) : 𝒞 σ → List (Φᵁ σᵀ)
| ⊤
| ⊥ => []
| [a]ₐ => [atomBridge σ a]
| ¬ₜ c => conceptBridges σ c
| c ⊓ₜ d | c ⊔ₜ d => conceptBridges σ c ++ conceptBridges σ d
| ∃[r] c | ∀[r] c => roleBridge σ r :: conceptBridges σ c

def sentenceBridges (σ : Signature) : Φ σ → List (Φᵁ σᵀ)
| _ :ₐ c => conceptBridges σ c
| (_, _) :ᵣ r => [roleBridge σ r]
| c ⊑ d | c ≡ d => conceptBridges σ c ++ conceptBridges σ d
| r ⊑ᵣ s => [roleBridge σ r, roleBridge σ s]

def translateWK (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ σᵀ) := Γ.flatMap (translateSentence σ)

def bridgesWK (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ σᵀ) := Γ.flatMap (sentenceBridges σ)

def encodeWK (I : ℐᵂᴷ σ) : ℐᶜ σᵀ where
  D := I.D
  inhabited := I.inhabited
  individualValuation := I.individualValuation
  atomicConceptValuation := λ (a, bit) x => match bit with
    | 𝕋 => (I.atomicConceptValuation a) x = 𝔱
    | 𝕄 => (I.atomicConceptValuation a) x ≠ 𝔢
  roleValuation := λ (r, bit) x y => match bit with
    | 𝕋 => (I.roleValuation r) x y = 𝔱
    | 𝕄 => (I.roleValuation r) x y ≠ 𝔢

instance : ToC (ℐᵂᴷ σ) (ℐᶜ σᵀ) := ⟨encodeWK⟩

noncomputable def propValue (truth meaningful : Prop) : V₃ := by
  classical
  exact if truth then 𝔱 else if meaningful then 𝔣 else 𝔢

@[simp] theorem propValue_truth (truth meaningful : Prop) :
    propValue truth meaningful = 𝔱 ↔ truth := by
  classical
  unfold propValue
  repeat (split) <;> simp_all

@[simp] theorem propValue_meaningful (truth meaningful : Prop)
    (h : truth → meaningful) : propValue truth meaningful ≠ 𝔢 ↔ meaningful := by
  classical
  unfold propValue
  repeat (split) <;> simp_all

noncomputable def decodeTarget (J : ℐᶜ σᵀ) : ℐᵂᴷ σ where
  D := J.D
  inhabited := J.inhabited
  individualValuation := J.individualValuation
  atomicConceptValuation := fun a x =>
    propValue ((J.atomicConceptValuation (a, 𝕋)) x)
      ((J.atomicConceptValuation (a, 𝕄)) x)
  roleValuation := fun r x y =>
    propValue ((J.roleValuation (r, 𝕋)) x y) ((J.roleValuation (r, 𝕄)) x y)

noncomputable instance : ToWK (ℐᶜ σᵀ) (ℐᵂᴷ σ) := ⟨decodeTarget⟩

theorem translateConceptEncode (I : ℐᵂᴷ σ) (c : 𝒞 σ) (x : I.D) :
    ((@evalConceptC _ (Iᶜ) (c^τ)) x ↔ (@evalConceptK _ I c) x = 𝔱) ∧
    ((@evalConceptC _ (Iᶜ) (c^μ)) x ↔ (@evalConceptK _ I c) x ≠ 𝔢) := by
  induction c generalizing x with
  | top | bot =>
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK]
      decide
  | atom a =>
      simp only [InterpretCurrent.interpret, Interpret.interpret, concept_tau, concept_mu, ToC.cIze, translateTau, translateMu,
        evalConceptC, evalConceptK, encodeWK, true_and]
  | neg c ih =>
      simp only [concept_tau, concept_mu] at ih
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK,
        (ih x).1, (ih x).2, negK_t, negK_m, true_and]
  | conj c d ihc ihd =>
      simp only [concept_tau, concept_mu] at ihc ihd
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK,
        (ihc x).1, (ihc x).2, (ihd x).1, (ihd x).2, andK_t, andK_m, true_and]
  | disj c d ihc ihd =>
      simp only [concept_tau, concept_mu] at ihc ihd
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK,
        (ihc x).1, (ihc x).2, (ihd x).1, (ihd x).2, orK_t, orK_m, true_and]
  | ex r c ih =>
      simp only [InterpretCurrent.interpret, evalConceptK, existsK_t, existsK_m]
      exact ⟨exists_congr (fun y => and_congr Iff.rfl (ih y).1),
        exists_congr (fun y => and_congr Iff.rfl (ih y).2)⟩
  | all r c ih =>
      simp only [InterpretCurrent.interpret, evalConceptK, forallK_t, forallK_m]
      refine ⟨and_congr ?_ ?_, ?_⟩
      · exact forall_congr' (fun y => imp_congr Iff.rfl (ih y).1)
      · exact exists_congr (fun y => and_congr Iff.rfl (ih y).2)
      · exact exists_congr (fun y => and_congr Iff.rfl (ih y).2)

theorem encodedAtomBridge (I : ℐᵂᴷ σ) (a : σ.Nc) :
    (encodeWK I) ⊨ᶜ (atomBridge σ a) := by
  simp only [InterpretCurrent.interpret, Interpret.interpret, atomBridge, evalSentenceC, evalConceptC, encodeWK]
  intro x h
  rw [h]
  decide

theorem encodedRoleBridge (I : ℐᵂᴷ σ) (r : σ.Nr) :
    (encodeWK I) ⊨ᶜ (roleBridge σ r) := by
  simp only [InterpretCurrent.interpret, Interpret.interpret, roleBridge, evalSentenceC, evalRoleC, encodeWK]
  intro x y h
  rw [h]
  decide

theorem encodedConceptBridges (I : ℐᵂᴷ σ) (c : 𝒞 σ) :
    ∀ q ∈ conceptBridges σ c, (encodeWK I) ⊨ᶜ q := by
  induction c with
  | top | bot => intro q hq; cases hq
  | atom a =>
      simpa only [conceptBridges, List.mem_singleton, forall_eq] using
        encodedAtomBridge I a
  | neg c ih => exact ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      simpa only [conceptBridges, List.mem_append, or_imp, forall_and] using And.intro ihc ihd
  | ex r c ih | all r c ih =>
      simpa only [conceptBridges, List.mem_cons, forall_eq_or_imp] using
        And.intro (encodedRoleBridge I r) ih

theorem encodedSentenceBridges (I : ℐᵂᴷ σ) (s : Φ σ) :
    ∀ q ∈ sentenceBridges σ s, (encodeWK I) ⊨ᶜ q := by
  cases s with
  | isa a c => exact encodedConceptBridges I c
  | role a b r =>
      simpa only [sentenceBridges, List.mem_singleton, forall_eq] using
        encodedRoleBridge I r
  | sub c d | equiv c d =>
      simpa only [sentenceBridges, List.mem_append, or_imp, forall_and] using
        And.intro (encodedConceptBridges I c) (encodedConceptBridges I d)
  | rsub r s =>
      intro q hq
      simp only [sentenceBridges, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact encodedRoleBridge I r
      · exact encodedRoleBridge I s

/-- Bridges are needed only for the names occurring in the concept being decoded. -/
theorem decodeConceptLocal (J : ℐᶜ σᵀ)
    (c : 𝒞 σ)
    (h : ∀ q ∈ conceptBridges σ c, J ⊨ᶜ q) (x : J.D) :
    ((@evalConceptC _ J (c^τ)) x ↔ (@evalConceptK _ (decodeTarget J) c) x = 𝔱) ∧
    ((@evalConceptC _ J (c^μ)) x ↔ (@evalConceptK _ (decodeTarget J) c) x ≠ 𝔢) := by
  induction c generalizing x with
  | top | bot =>
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK]
      decide
  | atom a =>
      have ha : ∀ y, (J.atomicConceptValuation (a, 𝕋)) y →
          (J.atomicConceptValuation (a, 𝕄)) y :=
        h (atomBridge σ a) (by simp only [conceptBridges, List.mem_singleton])
      exact ⟨(propValue_truth _ _).symm, (propValue_meaningful _ _ (ha x)).symm⟩
  | neg c ih =>
      have hc := ih h
      simp only [concept_tau, concept_mu] at hc
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, negK_t, negK_m, true_and]
  | conj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp only [concept_tau, concept_mu] at hc hd
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, (hd x).1, (hd x).2, andK_t, andK_m, true_and]
  | disj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp only [concept_tau, concept_mu] at hc hd
      simp only [concept_tau, concept_mu, translateTau, translateMu, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, (hd x).1, (hd x).2, orK_t, orK_m, true_and]
  | ex r c ih =>
      have hr : ∀ y z, (J.roleValuation (r, 𝕋)) y z →
          (J.roleValuation (r, 𝕄)) y z :=
        h (roleBridge σ r) (by simp only [conceptBridges, List.mem_cons, eq_self, true_or])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [InterpretCurrent.interpret, evalConceptK, existsK_t, existsK_m]
      exact ⟨exists_congr (fun y => and_congr (propValue_truth _ _).symm (hc y).1),
        exists_congr (fun y => and_congr (propValue_meaningful _ _ (hr x y)).symm
          (hc y).2)⟩
  | all r c ih =>
      have hr : ∀ y z, (J.roleValuation (r, 𝕋)) y z →
          (J.roleValuation (r, 𝕄)) y z :=
        h (roleBridge σ r) (by simp only [conceptBridges, List.mem_cons, eq_self, true_or])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [InterpretCurrent.interpret, evalConceptK, forallK_t, forallK_m]
      refine ⟨and_congr ?_ ?_, ?_⟩
      · exact forall_congr' (fun y =>
          imp_congr (propValue_truth _ _).symm (hc y).1)
      · exact exists_congr (fun y =>
          and_congr (propValue_meaningful _ _ (hr x y)).symm (hc y).2)
      · exact exists_congr (fun y =>
          and_congr (propValue_meaningful _ _ (hr x y)).symm (hc y).2)

private theorem allMemAppend {α : Type} (P : α → Prop) (xs ys : List α) :
    (∀ x ∈ xs ++ ys, P x) ↔ (∀ x ∈ xs, P x) ∧ (∀ x ∈ ys, P x) := by
  simp only [List.mem_append, or_imp, forall_and]

private theorem translateInclusion_iff (J : ℐᶜ σᵀ)
    (c d : 𝒞 σ) :
    (∀ q ∈ translateInclusion σ c d, J ⊨ᶜ q) ↔
      (∀ x, (@evalConceptC _ J (c^τ)) x →
        (@evalConceptC _ J (d^τ)) x) ∧
      ∃ x, (@evalConceptC _ J (c^μ)) x ∧
        (@evalConceptC _ J (d^μ)) x := by
  simp only [translateInclusion, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  rw [nonempty_iff]
  rfl

theorem translateInclusionEncode (I : ℐᵂᴷ σ) (c d : 𝒞 σ) :
    (∀ q ∈ translateInclusion σ c d, (encodeWK I) ⊨ᶜ q) ↔
      ∀ₖ[(@evalConceptK _ I c)] (@evalConceptK _ I d) = 𝔱 := by
  rw [translateInclusion_iff, forallK_t]
  exact and_congr
    (forall_congr' (fun x => imp_congr (translateConceptEncode I c x).1
      (translateConceptEncode I d x).1))
    (exists_congr (fun x => and_congr (translateConceptEncode I c x).2
      (translateConceptEncode I d x).2))

theorem decodeInclusionLocal (J : ℐᶜ σᵀ)
    (c d : 𝒞 σ)
    (hc : ∀ q ∈ conceptBridges σ c, J ⊨ᶜ q)
    (hd : ∀ q ∈ conceptBridges σ d, J ⊨ᶜ q) :
    (∀ q ∈ translateInclusion σ c d, J ⊨ᶜ q) ↔
      ∀ₖ[(@evalConceptK _ (decodeTarget J) c)] (@evalConceptK _ (decodeTarget J) d) = 𝔱 := by
  rw [translateInclusion_iff, forallK_t]
  exact and_congr
    (forall_congr' (fun x => imp_congr (decodeConceptLocal J c hc x).1
      (decodeConceptLocal J d hd x).1))
    (exists_congr (fun x => and_congr (decodeConceptLocal J c hc x).2
      (decodeConceptLocal J d hd x).2))

theorem translateSentenceEncode (I : ℐᵂᴷ σ) (s : Φ σ) :
    (∀ q ∈ translateSentence σ s, (encodeWK I) ⊨ᶜ q) ↔ I ⊨ᴷ s := by
  cases s with
  | isa a c =>
      simp only [InterpretCurrent.interpret, translateSentence, List.mem_singleton, forall_eq, evalSentenceC,
        satisfiesK]
      exact (translateConceptEncode I c ((I.individualValuation a))).1
  | role a b r =>
      simp only [InterpretCurrent.interpret, Interpret.interpret, translateSentence, List.mem_singleton, forall_eq, evalSentenceC, evalRoleC,
        encodeWK, satisfiesK, evalSentenceK]
  | sub c d => exact translateInclusionEncode I c d
  | equiv c d =>
      simp only [InterpretCurrent.interpret, Interpret.interpret, translateSentence, allMemAppend, translateInclusionEncode,
        satisfiesK, evalSentenceK]
      rw [andK_t]
  | rsub r s =>
      simp only [translateSentence, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      rw [overlap_iff]
      simp only [InterpretCurrent.interpret, Interpret.interpret, evalSentenceC, evalRoleC, encodeWK, satisfiesK, evalSentenceK]
      rw [forallK_t]
      simp only [InterpretCurrent.Result, Interpret.Result, Prod.forall, Prod.exists]

theorem decodeSentenceLocal (J : ℐᶜ σᵀ)
    (s : Φ σ)
    (h : ∀ q ∈ sentenceBridges σ s, J ⊨ᶜ q) :
    (∀ q ∈ translateSentence σ s, J ⊨ᶜ q) ↔ (decodeTarget J) ⊨ᴷ s := by
  cases s with
  | isa a c =>
      simp only [InterpretCurrent.interpret, translateSentence, List.mem_singleton, forall_eq, evalSentenceC,
        satisfiesK]
      exact (decodeConceptLocal J c h ((J.individualValuation a))).1
  | role a b r =>
      simp only [InterpretCurrent.interpret, Interpret.interpret, translateSentence, List.mem_singleton, forall_eq, evalSentenceC, evalRoleC,
        decodeTarget, satisfiesK, evalSentenceK]
      exact (propValue_truth _ _).symm
  | sub c d =>
      exact decodeInclusionLocal J c d
        (fun q hq => h q (List.mem_append_left _ hq))
        (fun q hq => h q (List.mem_append_right _ hq))
  | equiv c d =>
      have hc : ∀ q ∈ conceptBridges σ c, J ⊨ᶜ q :=
        fun q hq => h q (List.mem_append_left _ hq)
      have hd : ∀ q ∈ conceptBridges σ d, J ⊨ᶜ q :=
        fun q hq => h q (List.mem_append_right _ hq)
      simp only [InterpretCurrent.interpret, Interpret.interpret, translateSentence, allMemAppend, decodeInclusionLocal J c d hc hd,
        decodeInclusionLocal J d c hd hc, satisfiesK, evalSentenceK]
      rw [andK_t]
  | rsub r s =>
      have hr : ∀ x y, (J.roleValuation (r, 𝕋)) x y →
          (J.roleValuation (r, 𝕄)) x y :=
        h (roleBridge σ r) (by simp only [sentenceBridges, List.mem_cons, eq_self, true_or])
      have hs : ∀ x y, (J.roleValuation (s, 𝕋)) x y →
          (J.roleValuation (s, 𝕄)) x y :=
        h (roleBridge σ s) (by simp only [sentenceBridges, List.mem_cons,
          eq_self, true_or, or_true])
      simp only [translateSentence, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      rw [overlap_iff]
      simp only [InterpretCurrent.interpret, Interpret.interpret, evalSentenceC, evalRoleC, satisfiesK,
        evalSentenceK, decodeTarget]
      rw [forallK_t]
      simp only [InterpretCurrent.Result, Interpret.Result, decodeTarget, Prod.forall, Prod.exists, propValue_truth,
        fun x y => propValue_meaningful _ _ (hr x y),
        fun x y => propValue_meaningful _ _ (hs x y)]

private theorem allMemFlatMap {α β : Type} (P : β → Prop) (f : α → List β)
    (xs : List α) :
    (∀ y ∈ xs.flatMap f, P y) ↔ ∀ x ∈ xs, ∀ y ∈ f x, P y := by
  constructor
  · intro h x hx y hy
    exact h y (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
  · intro h y hy
    obtain ⟨x, hx, hy⟩ := List.mem_flatMap.mp hy
    exact h x hx y hy

theorem translateKBEncode (I : ℐᵂᴷ σ) (Γ : List (Φ σ)) :
    (∀ q ∈ translateWK σ Γ, (encodeWK I) ⊨ᶜ q) ↔
      ∀ s ∈ Γ, I ⊨ᴷ s := by
  simp only [translateWK, allMemFlatMap, translateSentenceEncode]

theorem encodedKBBridges (I : ℐᵂᴷ σ) (Γ : List (Φ σ)) :
    ∀ q ∈ bridgesWK σ Γ, (encodeWK I) ⊨ᶜ q := by
  rw [bridgesWK, allMemFlatMap]
  exact fun s _ => encodedSentenceBridges I s

theorem decodeKBLocal (J : ℐᶜ σᵀ)
    (Γ : List (Φ σ))
    (h : ∀ q ∈ bridgesWK σ Γ, J ⊨ᶜ q) :
    (∀ q ∈ translateWK σ Γ, J ⊨ᶜ q) ↔
      ∀ s ∈ Γ, (decodeTarget J) ⊨ᴷ s := by
  rw [translateWK, allMemFlatMap]
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  exact decodeSentenceLocal J s (fun q hq => h q (List.mem_flatMap.mpr ⟨s, hs, hq⟩))

/-- Classical models need bridges for the vocabulary of both premises and conclusions. -/
theorem entailmentK_iff_classical (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᴷ Δ) ↔
      ((translateWK σ Γ ++ bridgesWK σ Γ ++ bridgesWK σ Δ) ⊨ᶜ translateWK σ Δ) := by
  constructor
  · intro h J hJ
    rw [allMemAppend, allMemAppend] at hJ
    rcases hJ with ⟨⟨hΓ, hBΓ⟩, hBΔ⟩
    apply (decodeKBLocal J Δ hBΔ).mpr
    exact h (decodeTarget J) ((decodeKBLocal J Γ hBΓ).mp hΓ)
  · intro h I hI
    apply (translateKBEncode I Δ).mp
    apply h (encodeWK I)
    rw [allMemAppend, allMemAppend]
    exact ⟨⟨(translateKBEncode I Γ).mpr hI, encodedKBBridges I Γ⟩,
      encodedKBBridges I Δ⟩

-- MARK: AC to C
/-! ## The composed AC translation -/

/-- Translate a source KB through WK into the derived classical signature. -/
def T (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ (σᵂᴷ)ᵀ) :=
  translateWK σᵂᴷ Γᵂᴷ

/-- Bridges for the names used by the polarized source KB. -/
def B (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ (σᵂᴷ)ᵀ) :=
  bridgesWK σᵂᴷ Γᵂᴷ

/-- AC entailment is exactly classical entailment of the translated KBs,
with the bridges of both KBs included among the premises. -/
theorem MainResult (σ : Signature) (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᴬ Δ) ↔ ((T σ Γ ++ B σ Γ ++ B σ Δ) ⊨ᶜ T σ Δ) := by
  calc
    (Γ ⊨ᴬ Δ) ↔ (Γᵂᴷ ⊨ᴷ Δᵂᴷ)                  := entailmentA_iff_projectedWK Γ Δ
    _ ↔ ((T σ Γ ++ B σ Γ ++ B σ Δ) ⊨ᶜ T σ Δ) := entailmentK_iff_classical Γᵂᴷ Δᵂᴷ

end ALCHAC
