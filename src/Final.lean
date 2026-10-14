import DefDel
import Utils

namespace ALCHAC

-- MARK: Notation

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

class PiTranslation (α : Type u) (γ : outParam (Type w)) where
  piIze : α → γ

prefix:max "π " => PiTranslation.piIze

class TauTranslation (α : Type u) (γ : outParam (Type w)) where
  tau : α → γ

prefix:max  "τ " => TauTranslation.tau

class MuTranslation (α : Type u) (γ : outParam (Type w)) where
  mu : α → γ

prefix:max "μ " => MuTranslation.mu

class BridgeTranslation (α : Type u) (γ : outParam (Type w)) where
  bridge : α → γ

prefix:max "𝒟" => BridgeTranslation.bridge


postfix:max "*" => List

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
noncomputable def existsK (X : Set V₃²) : V₃ := by
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
noncomputable def forallK (X : Set V₃²) : V₃ := by
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

prefix:75 "∃ₖ " => existsK
prefix:75 "∀ₖ " => forallK

-- MARK: AC Operators
/- # AC Operators -/

def negA (v : V₃²) : V₃² := (v.2, v.1)
def andA (v w : V₃²) : V₃² := (v.1 ∧ₖ w.1, v.2 ∨ₖ w.2)
def orA (v w : V₃²) : V₃² := (v.1 ∨ₖ w.1, v.2 ∧ₖ w.2)

prefix:70 "∼ₐ " => negA
infixl:70 " ∧ₐ " => andA
infixl:65 " ∨ₐ " => orA

/-- Project the positive coordinates of AC role/concept pairs. -/
def acPositive (X : Set (V₃² × V₃²)) : Set V₃² :=
  Set.image (fun q => (q.1.1, q.2.1)) X

/-- Project the role's positive and the concept's negative coordinates. -/
def acNegative (X : Set (V₃² × V₃²)) : Set V₃² :=
  Set.image (fun q => (q.1.1, q.2.2)) X

noncomputable def existsA (X : Set (V₃² × V₃²)) : V₃² :=
  (∃ₖ (acPositive X), ∀ₖ (acNegative X))

noncomputable def forallA (X : Set (V₃² × V₃²)) : V₃² :=
  (∀ₖ (acPositive X), ∃ₖ (acNegative X))

prefix:75 "∃ₐ " => existsA
prefix:75 "∀ₐ " => forallA

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

Both parameters are outParams so the current interpretation determines
the signature and truth-value type during instance search.
(This is needed for our ·ᴵ notation)
-/
structure Interpretation (σ : outParam Signature) (V : outParam Type) where
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

/--
The type of Analytic Containment Interpretations.
Uses pairs of three-valued Kleene (`V₃²`) for valuations.
-/
abbrev ACInterpretation (σ : Signature) :=
  Interpretation σ V₃²
notation "ℐᴬᶜ" => ACInterpretation

/-! ## Interpretation Notation -/

/--
Operator for allowing superscript I notation for interpretations
-/
class Interpret (σ : Signature) (V : Type) (α : Type u) where
  Result : Interpretation σ V → Type
  interpret (I : Interpretation σ V) : α → Result I

/-- ·ᴵ for interpretations of individuals -/
instance : Interpret σ V σ.Ni :=
  ⟨(·.D), (·.individualValuation)⟩

/-- ·ᴵ for interpretations of atomic role names -/
instance : Interpret σ V σ.Nr :=
  ⟨λ I => I.D → I.D → V, (·.roleValuation)⟩

/-- ·ᴵ for interpretations of atomic concept names -/
instance : Interpret σ V σ.Nc :=
  ⟨λ I => I.D → V, (·.atomicConceptValuation)⟩


/-- Infer the signature and truth-value type from the interpretation in scope. -/
abbrev Interpret.current {V : Type}
[I : Interpretation σ V] [h : Interpret σ V α] (a : α) :
h.Result I := h.interpret I a

postfix:max "ᴵ" => Interpret.current


/--
Interpret an expression under an explicitly
supplied interpretation. We need to use this if
we have multiple interpretations in scope and want to
specify which one to use.
-/
scoped notation:80 a:81 "^" I:80 => Interpret.interpret I a


/-- The domain of the current interpretation. -/
abbrev Interpret.domain {V : Type}
[I : Interpretation σ V] : Type := I.D

notation "Δᴵ" => Interpret.domain

-- MARK: Classical Semantics
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
def entailmentC (Γ Δ : (Φᵁ σ)*) : Prop :=
  ∀ I, (∀ ψ ∈ Γ, I ⊨ᶜ ψ) → (∀ φ ∈ Δ, I ⊨ᶜ φ)

notation Γ " ⊨ᶜ " Δ => entailmentC Γ Δ

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
| ∃[R] C, x => ∃ₖ {(Rᴵ x y, ∇ C y) | y : Δᴵ}
| ∀[R] C, x => ∀ₖ {(Rᴵ x y, ∇ C y) | y : Δᴵ}

/-- ·ᴵ for ALCHRU concepts in weak Kleene semantics -/
noncomputable instance : Interpret σ V₃ (𝒞 σ) :=
  ⟨(·.D → V₃), λ_=> evalConceptK⟩

/-- Weak Kleene sentence semantics for ALCHRU. -/
noncomputable def evalSentenceK [ℐᵂᴷ σ] : Φ σ → V₃
| a :ₐ C => Cᴵ aᴵ
| (a, b) :ᵣ r => rᴵ aᴵ bᴵ
| C ⊑ D => ∀ₖ {(Cᴵ x, Dᴵ x) | x : Δᴵ}
| C ≡ D => (∀ₖ {(Cᴵ x, Dᴵ x) | x : Δᴵ}) ∧ₖ
    (∀ₖ {(Dᴵ x, Cᴵ x) | x : Δᴵ})
| R ⊑ᵣ S => ∀ₖ {(Rᴵ p.1 p.2, Sᴵ p.1 p.2) | p : Δᴵ × Δᴵ}

/-- ·ᴵ for ALCHRU sentences in weak Kleene semantics -/
noncomputable instance : Interpret σ V₃ (Φ σ) :=
  ⟨λ_=>V₃, λ_=> evalSentenceK⟩

/-- Satisfaction relation for weak Kleene semantics -/
def satisfiesK [ℐᵂᴷ σ] (φ : Φ σ) : Prop :=
  φᴵ = 𝔱

notation  I "⊨ᵂᴷ " S => @satisfiesK _ I S

/-- Entailment for weak Kleene semantics -/
def entailmentK (Γ Δ : (Φ σ)*) : Prop :=
  ∀ (I : ℐᵂᴷ σ), (∀ ψ ∈ Γ, I ⊨ᵂᴷ ψ) → (∀ φ ∈ Δ, I ⊨ᵂᴷ φ)

notation  Γ " ⊨ᵂᴷ " Δ => entailmentK Γ Δ

-- MARK: AC Semantics
/- # Analytic Containment Semantics -/

noncomputable def∇ evalConceptA [ℐᴬᶜ σ] : 𝒞 σ → Δᴵ → V₃²
| ⊤, _ => (𝔱, 𝔣)
| ⊥, _ => (𝔣, 𝔱)
| [a]ₐ, x => aᴵ x
| ¬ₜ c, x => ∼ₐ(∇ c x)
| c ⊓ₜ d, x => (∇ c x) ∧ₐ (∇ d x)
| c ⊔ₜ d, x => (∇ c x) ∨ₐ (∇ d x)
| ∃[r] c, x => ∃ₐ {(rᴵ x y, ∇ c y) | y : Δᴵ}
| ∀[r] c, x => ∀ₐ {(rᴵ x y, ∇ c y) | y : Δᴵ}

/-- ·ᴵ for ALCH concepts in AC semantics -/
noncomputable instance : Interpret σ V₃² (𝒞 σ) :=
  ⟨(·.D → V₃²), λ_=>evalConceptA⟩

/-- AC sentence semantics for ALCH. -/
noncomputable def evalSentenceA [ℐᴬᶜ σ] : Φ σ → V₃²
| a :ₐ c => cᴵ aᴵ
| (a, b) :ᵣ r => rᴵ aᴵ bᴵ
| c ⊑ d => ∀ₐ {(cᴵ x, dᴵ x) | x : Δᴵ}
| c ≡ d => (∀ₐ {(cᴵ x, dᴵ x) | x : Δᴵ}) ∧ₐ
    (∀ₐ {(dᴵ x, cᴵ x) | x : Δᴵ})
| r ⊑ᵣ s => ∀ₐ {(rᴵ p.1 p.2, sᴵ p.1 p.2) | p : Δᴵ × Δᴵ}

/-- ·ᴵ for ALCH sentences in AC semantics -/
noncomputable instance : Interpret σ V₃² (Φ σ) :=
  ⟨λ_=>V₃²,λ_=>evalSentenceA⟩

/-- Satisfaction relation for AC semantics -/
def satisfiesA [ℐᴬᶜ σ] (φ : Φ σ) : Prop :=
  (φᴵ : V₃²).1 = 𝔱

notation  I "⊨ᴬᶜ " S => @satisfiesA _ I S

/-- Entailment for AC semantics -/
def entailmentA (Γ Δ : (Φ σ)*) : Prop :=
  ∀ (I : ℐᴬᶜ σ), (∀ ψ ∈ Γ, I ⊨ᴬᶜ ψ) → (∀ φ ∈ Δ, I ⊨ᴬᶜ φ)

notation  Γ " ⊨ᴬᶜ " Δ => entailmentA Γ Δ

-- MARK: AC to WK
/-! # AC to WK Translation -/
/-!
We want a translation π such that (Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ʷᴷ π Δ).

We use the same idea from the mutual
π ν translation in the original paper,
modifying the signature to have π and ν
side indicators for concepts, and turning
ALCH concepts into their weak Kleene counterparts. We
prefer + and - over pi and nu for notational
(no unicode for superscript pi and nu)

Some examples of the π translation:
π (a : ¬(A ⊓ ∃[r] B)) = a : [(A, -ₚ)]ₐ ⊔ₜ ∀[r] [(B, -ₚ)]ₐ
π (C ⊑ ∀[r] D) = [C, +ₚ]ₐ ⊑ ∀[r] [D, +ₚ]ₐ
-/

/--
WK side indicator for polarizing concepts (+ₚ or -ₚ).
-/
inductive Side where
| positive --pi
| negative --nu
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
piConcept recursively transforms an ALCH concept into its
weak Kleene counterpart based on the given side indicator
(+ₚ or -ₚ). Note that we don't use a seperate ν translation;
the side indicator is passed directly to piConcept.
-/
def∇ piConcept {σ : Signature} : 𝒞 σ → Side → 𝒞 σᵂᴷ
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

-- Think of this as superscript pi
notation C "⁺" => piConcept C +ₚ
-- Think of this as superscript nu
notation C "⁻" => piConcept C -ₚ
postfix:max "ᵖ" => piConcept

/--
transforms an ALCH sentence over the original signature
σ to its weak Kleene counterpart over the signature σᵂᴷ
by polarizing all concepts positively.
-/
def piSentence : Φ σ → Φ σᵂᴷ
| a :ₐ c => a :ₐ c⁺
| (a, b) :ᵣ r => (a, b) :ᵣ r
| c ⊑ d => c⁺ ⊑ d⁺
| c ≡ d => c⁺ ≡ d⁺
| r ⊑ᵣ s => r ⊑ᵣ s

/-- π φ notationfor sentences -/
instance : PiTranslation (Φ σ) (Φ σᵂᴷ) where
  piIze := piSentence

/-- Transforms a set of ALCH sentences over the original
signature to their weak Kleene counterparts over the
signature σᵂᴷ -/
abbrev piSentenceSet : (Φ σ)* → (Φ σᵂᴷ)* :=
  List.map piSentence

instance : PiTranslation (Φ σ)* (Φ σᵂᴷ)* where
  piIze := piSentenceSet

-- MARK: WK to C
/-! # Weak Kleene to Classical Translation -/
/-!
Similar idea to the original tau / mu translation
with some fixes. We modify the signature to include a bit
indicator for each concept and role, representing
if the concept or role is true or meaningful.

The core distinction is that we can use the universal role
to express nonemptiness of concepts and overlap of roles,
and then use this information to encode the wk
semantics through the translation.
-/

inductive Bit where
| truth
| meaningful
deriving DecidableEq, Repr

-- supserscript tau on atomic concepts
notation "𝕋" => Bit.truth
-- supserscript mu on atomic concepts
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

/-- The meaningfulness component of a translated concept. -/
def∇ muConcept : 𝒞 σ → 𝒞ᵁ σᵀ
| ⊤ => ⊤
| ⊥ => ⊤
| [a]ₐ => [(a, 𝕄)]ₐ
| ¬ₜc => ∇ c
| c ⊓ₜ d => (∇ c) ⊓ₜ (∇ d)
| c ⊔ₜ d => (∇ c) ⊓ₜ (∇ d)
| ∃[r] c => ∃[[(r, 𝕄)]ᵣ] (∇ c)
| ∀[r] c => ∃[[(r, 𝕄)]ᵣ] (∇ c)

instance : MuTranslation (𝒞 σ) (𝒞ᵁ σᵀ) := ⟨muConcept⟩

/-- The truth component of a translated concept. -/
def∇ tauConcept : 𝒞 σ → 𝒞ᵁ σᵀ
| ⊤ => ⊤
| ⊥ => ⊥
| [a]ₐ => [(a, 𝕋)]ₐ
| ¬ₜc => μ c ⊓ₜ ¬ₜ(∇ c)
| c ⊓ₜ d => (∇ c) ⊓ₜ (∇ d)
| c ⊔ₜ d => ((∇ c) ⊔ₜ (∇ d)) ⊓ₜ (μ c ⊓ₜ μ d)
| ∃[r] c => ∃[[(r, 𝕋)]ᵣ] (∇ c)
| ∀[r] c => (∀[[(r, 𝕋)]ᵣ] (∇ c)) ⊓ₜ ∃[[(r, 𝕄)]ᵣ] (μ c)

/-- τ for concepts -/
instance : TauTranslation (𝒞 σ) (𝒞ᵁ σᵀ) := ⟨tauConcept⟩

/--
We can express that C is nonempty in classical ALC using
the universal role. ⊤ ⊑ ∃[𝒰] c -> ∀x, ∃y, c(y) -> ∃y, c(y)
-/
def nonempty (c : 𝒞ᵁ σ) : Φᵁ σ :=
  ⊤ ⊑ ∃[𝒰] c

prefix:max "∃₁" => nonempty


/--
Intersection forces both roles to hold on the same pair.
Classically this resolves
∃₁(∃[(r ⊓ᵣ s)] ⊤) ->
-/
def overlap (r s : σ.Nr) : Φᵁ σ :=
  ∃₁(∃[([r]ᵣ ⊓ᵣ [s]ᵣ)] ⊤)

infixl:70 " ⨅⁺ " => overlap


def tauSubsumption (c d : 𝒞 σ) : (Φᵁ σᵀ)* :=
  [τ c ⊑ τ d, ∃₁(μ c ⊓ₜ μ d)]


def tauSentence : Φ σ → (Φᵁ σᵀ)*
| a :ₐ c => [a :ₐ τ c]
| (a, b) :ᵣ r => [(a, b) :ᵣ [(r, 𝕋)]ᵣ]
| c ⊑ d => tauSubsumption c d
| c ≡ d => tauSubsumption c d ++ tauSubsumption d c
| r ⊑ᵣ s => [[(r, 𝕋)]ᵣ ⊑ᵣ [(s, 𝕋)]ᵣ, (r, 𝕄) ⨅⁺ (s, 𝕄)]

instance : TauTranslation (Φ σ) (Φᵁ σᵀ)* :=
  ⟨tauSentence⟩

def tauSentenceSet (Γ : (Φ σ)*) : (Φᵁ σᵀ)* :=
  Γ.flatMap (tauSentence)

instance : TauTranslation (Φ σ)* (Φᵁ σᵀ)* :=
  ⟨tauSentenceSet⟩

-- MARK: WK To C Bridges
/-!
It is not enough to simply translate concepts and roles;
we also need to ensure that the truth and meaningfulness
components are properly related through bridge axioms.
-/

/--
Bridge axiom for atomic concepts.
Ensures that the truth component
implies the meaningfulness component.
-/
def atomicConceptBridge (a : σ.Nc) : Φᵁ σᵀ :=
  [(a, 𝕋)]ₐ ⊑ [(a, 𝕄)]ₐ

instance : BridgeTranslation (σ.Nc) (Φᵁ σᵀ) :=
⟨atomicConceptBridge⟩

/--
Bridge axiom for atomic roles.
Ensures that the truth component
implies the meaningfulness component.
-/
def atomicRoleBridge (r : σ.Nr) : Φᵁ σᵀ :=
  [(r, 𝕋)]ᵣ ⊑ᵣ [(r, 𝕄)]ᵣ

instance : BridgeTranslation (σ.Nr) (Φᵁ σᵀ) :=
 ⟨atomicRoleBridge⟩

/--
Bridge axioms for concepts.
Ensures that the truth and meaningfulness components
are properly related for complex concepts.
-/
def∇ conceptBridges : 𝒞 σ → (Φᵁ σᵀ)*
| ⊤ => []
| ⊥ => []
| [a]ₐ => [𝒟 a]
| ¬ₜ c => ∇ c
| c ⊓ₜ d => ∇ c ++ ∇ d
| c ⊔ₜ d => ∇ c ++ ∇ d
| ∃[r] c => [𝒟 r] ++ ∇ c
| ∀[r] c => [𝒟 r] ++ ∇ c

instance : BridgeTranslation (𝒞 σ) (Φᵁ σᵀ)* :=
 ⟨conceptBridges⟩

def sentenceBridges : Φ σ → (Φᵁ σᵀ)*
| _ :ₐ c => 𝒟 c
| (_, _) :ᵣ r => [𝒟 r]
| c ⊑ d => 𝒟 c ++ 𝒟 d
| c ≡ d => 𝒟 c ++ 𝒟 d
| r ⊑ᵣ s => [𝒟 r, 𝒟 s]

instance : BridgeTranslation (Φ σ) (Φᵁ σᵀ)* :=
 ⟨sentenceBridges⟩

def sentenceSetBridges (Γ : (Φ σ)*) : (Φᵁ σᵀ)* :=
  Γ.flatMap (sentenceBridges)

instance : BridgeTranslation ((Φ σ)*) (Φᵁ σᵀ)* :=
 ⟨sentenceSetBridges⟩


-- MARK: WK Lemmas
/- # WK Lemmas -/

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

/-- ∃ₖ X is true iff X contains (𝔱, 𝔱). -/
private theorem existsK_true (X : Set V₃²) :
∃ₖ X = 𝔱 ↔ (𝔱, 𝔱) ∈ X := by
  classical
  unfold existsK
  repeat (split <;> (try rfl) <;> (try grind only))

/-- ∃ₖ X is meaningful when a pair is fully meaningful. -/
private theorem existsK_meaningful (X : Set V₃²) :
∃ₖ X ≠ 𝔢 ↔ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold existsK
  repeat (split <;> (try rfl) <;> (try grind only))

/-- ∀ₖ X is true exactly under its set-based true clause. -/
private theorem forallK_true (X : Set V₃²) :
∀ₖ X = 𝔱 ↔ (𝔱, 𝔣) ∉ X ∧ (𝔱, 𝔢) ∉ X ∧ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold forallK
  repeat (split <;> (try rfl) <;> (try grind only))

/-- ∀ₖ X is meaningful exactly when a pair is fully meaningful. -/
private theorem forallK_meaningful (X : Set V₃²) :
∀ₖ X ≠ 𝔢 ↔ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold forallK
  repeat (split <;> (try rfl) <;> (try grind only))


@[simp]
theorem existsK_t {D : Type} (r c : D → V₃) :
∃ₖ {(r x, c x) | x : D} = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  rw [existsK_true]
  simp

@[simp]
theorem existsK_m {D : Type} (r c : D → V₃) :
∃ₖ {(r x, c x) | x : D} ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  rw [existsK_meaningful]
  simp only [Set.exists_mem_ofValues]

@[simp]
theorem forallK_t {D : Type} (r c : D → V₃) :
∀ₖ {(r x, c x) | x : D} = 𝔱 ↔
(∀ x, r x = 𝔱 → c x = 𝔱) ∧ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  have ht : ((𝔱, 𝔣) ∉ {(r x, c x) | x : D} ∧
      (𝔱, 𝔢) ∉ {(r x, c x) | x : D}) ↔
      ∀ x, r x = 𝔱 → c x = 𝔱 := by
    simp only [Set.mem_ofValues, Prod.mk.injEq, not_exists, not_and]
    constructor
    · rintro ⟨hf, he⟩ x hx
      have hf' := hf x hx
      have he' := he x hx
      cases hcx : c x <;> simp_all
    · intro h
      constructor <;> intro x hx <;> simp [h x hx]
  rw [forallK_true, ← and_assoc, ht]
  simp only [Set.exists_mem_ofValues]

@[simp]
theorem forallK_m {D : Type} (r c : D → V₃) :
    ∀ₖ {(r x, c x) | x : D} ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  rw [forallK_meaningful]
  simp only [Set.exists_mem_ofValues]

-- MARK: Other Lemmas

/--
Given a classical interpretation I and a concept c,
I entails nonemptiness of c iff there exists an element x
in the domain of I such that x satisfies c.
-/
@[simp]
theorem nonempty_iff [I : ℐᶜ σ] (c : 𝒞ᵁ σ) :
(I ⊨ᶜ ∃₁c) ↔ ∃ x, cᴵ x := by
  simp only [Interpret.current, Interpret.interpret,
  nonempty, evalSentenceC, evalConceptC, evalRoleC,
  true_implies, true_and]
  constructor
  · intro h
    obtain ⟨x⟩ := I.inhabited
    exact h x
  · intro h _
    exact h

/--
Given a classical interpretation I and two roles r and s,
I entails that r and s overlap iff there exist elements x and y
in the domain of I such that both r and s relate x to y.
-/
@[simp] theorem overlap_iff [I : ℐᶜ σ] (r s : σ.Nr) :
(I ⊨ᶜ (r ⨅⁺ s)) ↔ ∃ x y, rᴵ x y ∧ sᴵ x y := by
  simp only [Interpret.current, Interpret.interpret,
  overlap, nonempty_iff, evalConceptC, evalRoleC, and_true]


-- MARK: AC to WK
/-! ## AC to weak Kleene Theorems -/
/-! In this section we prove the forwards
AC to WK translation preserves the interpretation of
concepts and roles. IE
Γ ⊨ᴬᶜ Δ → π Γ ⊨ᵂᴷ π Δ
-/

def coordinate (v : V₃²) : Side → V₃
| +ₚ => v.1
| -ₚ => v.2

-- So we can use v[+ₚ] and v[-ₚ] to access the
-- respective components of a V₃² vector.
instance : GetElem (V₃²) Side V₃ (λ _ _ => True) where
  getElem := λ v s _ => coordinate v s

@[instance_reducible]
def acToWK [I : ℐᴬᶜ σ] : ℐᵂᴷ σᵂᴷ where
  D :=                      Δᴵ
  inhabited :=              I.inhabited
  individualValuation :=    λ x => xᴵ
  atomicConceptValuation := λ (a, s) x => (aᴵ x)[s]
  roleValuation :=          λ r x y => (rᴵ x y)[+ₚ]

instance : ToWK (ℐᴬᶜ σ) (ℐᵂᴷ σᵂᴷ) := ⟨@acToWK σ⟩

@[instance_reducible]
def wkToAC [I : ℐᵂᴷ σᵂᴷ] : ℐᴬᶜ σ where
  D :=                      Δᴵ
  inhabited :=              I.inhabited
  individualValuation :=    λ x => xᴵ
  atomicConceptValuation := λ a x =>
    let pos : σᵂᴷ.Nc := ⟨a, +ₚ⟩
    let neg : σᵂᴷ.Nc := ⟨a, -ₚ⟩
    (posᴵ x, negᴵ x)
  roleValuation :=          λ r x y => (rᴵ x y, 𝔢)

instance : ToAC (ℐᵂᴷ σᵂᴷ) (ℐᴬᶜ σ) := ⟨@wkToAC σ⟩

theorem acToWK_wkToAC (K : ℐᵂᴷ σᵂᴷ) : (Kᴬᶜ)ᵂᴷ = K := by
  cases K with
  | mk D inhabited individuals atoms roles =>
      simp only [acToWK, ToWK.wkIze]
      congr 1
      funext a x
      rcases a with ⟨a, side⟩
      cases side <;> rfl

theorem acConceptCoordinates (I : ℐᴬᶜ σ) (c : 𝒞 σ)
(s : Side) (x : Δᴵ) :
((cᵖ s)^(Iᵂᴷ)) x = ((c^I) x)[s] := by
  simp only [Interpret.interpret]
  induction c generalizing s x with
  | top => cases s <;> rfl
  | bot => cases s <;> rfl
  | atom a => cases s <;> rfl
  | neg c ih => cases s <;> simp only [
     piConcept, evalConceptA, negA, GetElem.getElem,
     coordinate, ih]
  | conj c d ihc ihd =>
      cases s <;> simp only [
        piConcept, evalConceptK, evalConceptA, andA,
        GetElem.getElem, coordinate, ihc, ihd]
  | disj c d ihc ihd =>
      cases s <;> simp only [
        piConcept, evalConceptK, evalConceptA, orA,
        GetElem.getElem, coordinate, ihc, ihd]
  | ex r c ih =>
      cases s <;> simp only [
        piConcept, evalConceptK, evalConceptA, existsA,
        acPositive, acNegative, Set.image_ofValues, ih,
        GetElem.getElem, coordinate] <;> rfl
  | all r c ih =>
      cases s <;> simp only [
        piConcept, evalConceptK, evalConceptA, forallA,
        acPositive, acNegative, Set.image_ofValues, ih,
        GetElem.getElem, coordinate] <;> rfl

theorem acSentenceSupport (I : ℐᴬᶜ σ) (s : Φ σ) :
(π s)^(Iᵂᴷ) = coordinate (s^I) +ₚ := by
  have hc (c : 𝒞 σ) :
      (c⁺)^(Iᵂᴷ) = fun x => ((c^I) x)[+ₚ] :=
    funext (acConceptCoordinates (I := I) c +ₚ)
  simp only [Interpret.interpret] at hc
  cases s <;> simp only [
    Interpret.domain, Interpret.current,
    Interpret.interpret, PiTranslation.piIze, piSentence,
    evalSentenceK, evalSentenceA, forallA, andA, hc,
    acPositive, Set.image_ofValues, GetElem.getElem,
    coordinate] <;> rfl

theorem acSentenceSupport_iff (I : ℐᴬᶜ σ) (s : Φ σ) :
(Iᵂᴷ ⊨ᵂᴷ π s) ↔ (I ⊨ᴬᶜ s) := by
  change (π s)^(Iᵂᴷ) = 𝔱 ↔ coordinate (s^I) +ₚ = 𝔱
  rw [acSentenceSupport]

theorem A_implies_pi_WK (Γ Δ : List (Φ σ)) :
(Γ ⊨ᴬᶜ Δ) → (π Γ ⊨ᵂᴷ π Δ) := by
  intro h K hΓ q hq
  have hround : (Kᴬᶜ)ᵂᴷ = K := acToWK_wkToAC K
  rcases List.mem_map.mp hq with ⟨s, hs, rfl⟩
  have hsource : ∀ p ∈ Γ, Kᴬᶜ ⊨ᴬᶜ p := by
    intro p hp
    have hk := hΓ (π p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    exact (acSentenceSupport_iff Kᴬᶜ p).mp (hround ▸ hk)
  have hout := h Kᴬᶜ hsource s hs
  exact hround ▸ (acSentenceSupport_iff Kᴬᶜ s).mpr hout


theorem pi_WK_implies_A (Γ Δ : List (Φ σ)) :
(π Γ ⊨ᵂᴷ π Δ) → (Γ ⊨ᴬᶜ Δ) := by
  intro h I hΓ s hs
  have hprojected : ∀ p ∈ π Γ, Iᵂᴷ ⊨ᵂᴷ p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact (acSentenceSupport_iff I q).mpr (hΓ q hq)
  have hout := h Iᵂᴷ hprojected (piSentence s)
    (List.mem_map.mpr ⟨s, hs, rfl⟩)
  exact (acSentenceSupport_iff I s).mp hout

/-- The explicit WK entailment intermediate used in the final theorem. -/
theorem A_iff_pi_WK (Γ Δ : List (Φ σ)) :
(Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ᵂᴷ π Δ) :=
  Iff.intro (A_implies_pi_WK Γ Δ) (pi_WK_implies_A Γ Δ)


-- MARK: WK to C
/-! ## WK to classical ALCH with universal role and role intersection -/

@[simp] theorem concept_mu (c : 𝒞 σ) : μ c = muConcept c := rfl
@[simp] theorem concept_tau (c : 𝒞 σ) : τ c = tauConcept c := rfl

@[instance_reducible]
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

noncomputable def propValue (t m : Prop) : V₃ := by
  classical
  exact if t then 𝔱 else if m then 𝔣 else 𝔢

@[simp] theorem propValue_truth (t m : Prop) :
    propValue t m = 𝔱 ↔ t := by
  classical
  unfold propValue
  repeat (split) <;> simp_all

@[simp] theorem propValue_meaningful (t m : Prop)
    (h : t → m) : propValue t m ≠ 𝔢 ↔ m := by
  classical
  unfold propValue
  repeat (split) <;> simp_all

@[instance_reducible]
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
  (((τ c)^(Iᶜ)) x ↔ (c^I) x = 𝔱) ∧
  (((μ c)^(Iᶜ)) x ↔ (c^I) x ≠ 𝔢) := by
  simp only [Interpret.interpret]
  induction c generalizing x with
  | top | bot =>
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK]
      decide
  | atom a =>
      simp only [Interpret.current, Interpret.interpret, concept_tau, concept_mu, ToC.cIze, tauConcept, muConcept,
        evalConceptC, evalConceptK, encodeWK, true_and]
  | neg c ih =>
      simp only [concept_tau, concept_mu] at ih
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK,
        (ih x).1, (ih x).2, negK_t, negK_m, true_and]
  | conj c d ihc ihd =>
      simp only [concept_tau, concept_mu] at ihc ihd
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK,
        (ihc x).1, (ihc x).2, (ihd x).1, (ihd x).2, andK_t, andK_m, true_and]
  | disj c d ihc ihd =>
      simp only [concept_tau, concept_mu] at ihc ihd
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK,
        (ihc x).1, (ihc x).2, (ihd x).1, (ihd x).2, orK_t, orK_m, true_and]
  | ex r c ih =>
      simp only [Interpret.current, Interpret.interpret, evalConceptC, evalRoleC, concept_tau, concept_mu, tauConcept, muConcept, ToC.cIze, encodeWK, evalConceptK, existsK_t, existsK_m]
      exact ⟨exists_congr (fun y => and_congr Iff.rfl (ih y).1),
        exists_congr (fun y => and_congr Iff.rfl (ih y).2)⟩
  | all r c ih =>
      simp only [Interpret.current, Interpret.interpret, evalConceptC, evalRoleC, concept_tau, concept_mu, tauConcept, muConcept, ToC.cIze, encodeWK, evalConceptK, forallK_t, forallK_m]
      refine ⟨and_congr ?_ ?_, ?_⟩
      · exact forall_congr' (fun y => imp_congr Iff.rfl (ih y).1)
      · exact exists_congr (fun y => and_congr Iff.rfl (ih y).2)
      · exact exists_congr (fun y => and_congr Iff.rfl (ih y).2)

theorem encodedatomicConceptBridge (I : ℐᵂᴷ σ) (a : σ.Nc) :
    (encodeWK I) ⊨ᶜ (atomicConceptBridge a) := by
  simp only [Interpret.current, Interpret.interpret, atomicConceptBridge, evalSentenceC, evalConceptC, encodeWK]
  intro x h
  rw [h]
  decide

theorem encodedatomicRoleBridge (I : ℐᵂᴷ σ) (r : σ.Nr) :
    (encodeWK I) ⊨ᶜ (atomicRoleBridge r) := by
  simp only [Interpret.current, Interpret.interpret, atomicRoleBridge, evalSentenceC, evalRoleC, encodeWK]
  intro x y h
  rw [h]
  decide

theorem encodedConceptBridges (I : ℐᵂᴷ σ) (c : 𝒞 σ) :
    ∀ q ∈ conceptBridges c, (encodeWK I) ⊨ᶜ q := by
  induction c with
  | top | bot => intro q hq; cases hq
  | atom a =>
      simpa only [conceptBridges, BridgeTranslation.bridge, List.mem_singleton, forall_eq] using
        encodedatomicConceptBridge I a
  | neg c ih => exact ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      simpa only [conceptBridges, BridgeTranslation.bridge, List.mem_append, or_imp, forall_and] using And.intro ihc ihd
  | ex r c ih | all r c ih =>
      simpa only [conceptBridges, BridgeTranslation.bridge, List.mem_append,
        List.mem_singleton, or_imp, forall_and, forall_eq] using
        And.intro (encodedatomicRoleBridge I r) ih

theorem encodedSentenceBridges (I : ℐᵂᴷ σ) (s : Φ σ) :
    ∀ q ∈ sentenceBridges s, (encodeWK I) ⊨ᶜ q := by
  cases s with
  | isa a c => exact encodedConceptBridges I c
  | role a b r =>
      simpa only [sentenceBridges, BridgeTranslation.bridge, List.mem_singleton, forall_eq] using
        encodedatomicRoleBridge I r
  | sub c d | equiv c d =>
      simpa only [sentenceBridges, BridgeTranslation.bridge, List.mem_append, or_imp, forall_and] using
        And.intro (encodedConceptBridges I c) (encodedConceptBridges I d)
  | rsub r s =>
      intro q hq
      simp only [sentenceBridges, BridgeTranslation.bridge, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact encodedatomicRoleBridge I r
      · exact encodedatomicRoleBridge I s

/-- Bridges are needed only for the names occurring in the concept being decoded. -/
theorem decodeConceptLocal (J : ℐᶜ σᵀ)
    (c : 𝒞 σ)
    (h : ∀ q ∈ conceptBridges c, J ⊨ᶜ q) (x : J.D) :
    (((τ c)^J) x ↔ (c^(decodeTarget J)) x = 𝔱) ∧
    (((μ c)^J) x ↔ (c^(decodeTarget J)) x ≠ 𝔢) := by
  simp only [Interpret.interpret]
  induction c generalizing x with
  | top | bot =>
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK]
      decide
  | atom a =>
      have ha : ∀ y, (J.atomicConceptValuation (a, 𝕋)) y →
          (J.atomicConceptValuation (a, 𝕄)) y :=
        h (atomicConceptBridge a) (by simp only [conceptBridges, BridgeTranslation.bridge, List.mem_singleton])
      exact ⟨(propValue_truth _ _).symm, (propValue_meaningful _ _ (ha x)).symm⟩
  | neg c ih =>
      have hc := ih h
      simp only [concept_tau, concept_mu] at hc
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, negK_t, negK_m, true_and]
  | conj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp only [concept_tau, concept_mu] at hc hd
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, (hd x).1, (hd x).2, andK_t, andK_m, true_and]
  | disj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp only [concept_tau, concept_mu] at hc hd
      simp only [concept_tau, concept_mu, tauConcept, muConcept, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, (hd x).1, (hd x).2, orK_t, orK_m, true_and]
  | ex r c ih =>
      have hr : ∀ y z, (J.roleValuation (r, 𝕋)) y z →
          (J.roleValuation (r, 𝕄)) y z :=
        h (atomicRoleBridge r) (by simp [conceptBridges, BridgeTranslation.bridge])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [Interpret.current, Interpret.interpret, evalConceptC, evalRoleC, concept_tau, concept_mu, tauConcept, muConcept, decodeTarget, evalConceptK]
      rw [existsK_t, existsK_m]
      exact ⟨exists_congr (fun y => and_congr (propValue_truth _ _).symm (hc y).1),
        exists_congr (fun y => and_congr (propValue_meaningful _ _ (hr x y)).symm
          (hc y).2)⟩
  | all r c ih =>
      have hr : ∀ y z, (J.roleValuation (r, 𝕋)) y z →
          (J.roleValuation (r, 𝕄)) y z :=
        h (atomicRoleBridge r) (by simp [conceptBridges, BridgeTranslation.bridge])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [Interpret.current, Interpret.interpret, evalConceptC, evalRoleC, concept_tau, concept_mu, tauConcept, muConcept, decodeTarget, evalConceptK]
      rw [forallK_t, forallK_m]
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

private theorem translateInclusion_iff (J : ℐᶜ σᵀ) (c d : 𝒞 σ) :
    (∀ q ∈ tauSubsumption c d, J ⊨ᶜ q) ↔
      (∀ x, ((τ c)^J) x →
        ((τ d)^J) x) ∧
      ∃ x, ((μ c)^J) x ∧
        ((μ d)^J) x := by
  simp only [tauSubsumption, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  rw [nonempty_iff]
  rfl

theorem translateInclusionEncode (I : ℐᵂᴷ σ) (c d : 𝒞 σ) :
    (∀ q ∈ tauSubsumption c d, (encodeWK I) ⊨ᶜ q) ↔
      ∀ₖ {((c^I) x, (d^I) x) | x : I.D} = 𝔱 := by
  simp only [Interpret.interpret]
  rw [translateInclusion_iff, forallK_t]
  exact and_congr
    (forall_congr' (fun x => imp_congr (translateConceptEncode I c x).1
      (translateConceptEncode I d x).1))
    (exists_congr (fun x => and_congr (translateConceptEncode I c x).2
      (translateConceptEncode I d x).2))

theorem decodeInclusionLocal (J : ℐᶜ σᵀ)
    (c d : 𝒞 σ)
    (hc : ∀ q ∈ conceptBridges c, J ⊨ᶜ q)
    (hd : ∀ q ∈ conceptBridges d, J ⊨ᶜ q) :
    (∀ q ∈ tauSubsumption c d, J ⊨ᶜ q) ↔
      ∀ₖ {((c^(decodeTarget J)) x, (d^(decodeTarget J)) x) | x : J.D} = 𝔱 := by
  simp only [Interpret.interpret]
  rw [translateInclusion_iff, forallK_t]
  exact and_congr
    (forall_congr' (fun x => imp_congr (decodeConceptLocal J c hc x).1
      (decodeConceptLocal J d hd x).1))
    (exists_congr (fun x => and_congr (decodeConceptLocal J c hc x).2
      (decodeConceptLocal J d hd x).2))

theorem tauSentenceEncode (I : ℐᵂᴷ σ) (s : Φ σ) :
    (∀ q ∈ tauSentence s, (encodeWK I) ⊨ᶜ q) ↔ I ⊨ᵂᴷ s := by
  cases s with
  | isa a c =>
      simp only [Interpret.current, tauSentence, List.mem_singleton, forall_eq, evalSentenceC,
        satisfiesK]
      exact (translateConceptEncode I c ((I.individualValuation a))).1
  | role a b r =>
      simp only [Interpret.current, Interpret.interpret, tauSentence, List.mem_singleton, forall_eq, evalSentenceC, evalRoleC,
        encodeWK, satisfiesK, evalSentenceK]
  | sub c d => exact translateInclusionEncode I c d
  | equiv c d =>
      simp only [Interpret.current, Interpret.interpret, tauSentence, allMemAppend, translateInclusionEncode,
        satisfiesK, evalSentenceK]
      rw [andK_t]
  | rsub r s =>
      simp only [tauSentence, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      rw [overlap_iff (I := encodeWK I)]
      simp only [Interpret.domain, Interpret.current, Interpret.interpret, evalSentenceC, evalRoleC, encodeWK, satisfiesK, evalSentenceK]
      rw [forallK_t]
      simp only [Prod.forall, Prod.exists]

theorem decodeSentenceLocal (J : ℐᶜ σᵀ)
    (s : Φ σ)
    (h : ∀ q ∈ sentenceBridges s, J ⊨ᶜ q) :
    (∀ q ∈ tauSentence s, J ⊨ᶜ q) ↔ (decodeTarget J) ⊨ᵂᴷ s := by
  cases s with
  | isa a c =>
      simp only [Interpret.current, tauSentence, List.mem_singleton, forall_eq, evalSentenceC,
        satisfiesK]
      exact (decodeConceptLocal J c h ((J.individualValuation a))).1
  | role a b r =>
      simp only [Interpret.current, Interpret.interpret, tauSentence, List.mem_singleton, forall_eq, evalSentenceC, evalRoleC,
        decodeTarget, satisfiesK, evalSentenceK]
      exact (propValue_truth _ _).symm
  | sub c d =>
      exact decodeInclusionLocal J c d
        (fun q hq => h q (List.mem_append_left _ hq))
        (fun q hq => h q (List.mem_append_right _ hq))
  | equiv c d =>
      have hc : ∀ q ∈ conceptBridges c, J ⊨ᶜ q :=
        fun q hq => h q (List.mem_append_left _ hq)
      have hd : ∀ q ∈ conceptBridges d, J ⊨ᶜ q :=
        fun q hq => h q (List.mem_append_right _ hq)
      simp only [Interpret.current, Interpret.interpret, tauSentence, allMemAppend, decodeInclusionLocal J c d hc hd,
        decodeInclusionLocal J d c hd hc, satisfiesK, evalSentenceK]
      rw [andK_t]
      rfl
  | rsub r s =>
      have hr : ∀ x y, (J.roleValuation (r, 𝕋)) x y →
          (J.roleValuation (r, 𝕄)) x y :=
        h (atomicRoleBridge r) (by simp only [sentenceBridges, BridgeTranslation.bridge, List.mem_cons, eq_self, true_or])
      have hs : ∀ x y, (J.roleValuation (s, 𝕋)) x y →
          (J.roleValuation (s, 𝕄)) x y :=
        h (atomicRoleBridge s) (by simp only [sentenceBridges, BridgeTranslation.bridge, List.mem_cons,
          eq_self, true_or, or_true])
      simp only [tauSentence, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      rw [overlap_iff]
      simp only [Interpret.domain, Interpret.current, Interpret.interpret, evalSentenceC, evalRoleC, satisfiesK,
        evalSentenceK, decodeTarget]
      rw [forallK_t]
      simp only [Prod.forall, Prod.exists, propValue_truth,
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
    (∀ q ∈ tauSentenceSet Γ, (encodeWK I) ⊨ᶜ q) ↔
      ∀ s ∈ Γ, I ⊨ᵂᴷ s := by
  simp only [tauSentenceSet, allMemFlatMap, tauSentenceEncode]

theorem encodedKBBridges (I : ℐᵂᴷ σ) (Γ : List (Φ σ)) :
    ∀ q ∈ sentenceSetBridges Γ, (encodeWK I) ⊨ᶜ q := by
  rw [sentenceSetBridges, allMemFlatMap]
  exact fun s _ => encodedSentenceBridges I s

theorem decodeKBLocal (J : ℐᶜ σᵀ)
    (Γ : List (Φ σ))
    (h : ∀ q ∈ sentenceSetBridges Γ, J ⊨ᶜ q) :
    (∀ q ∈ tauSentenceSet Γ, J ⊨ᶜ q) ↔
      ∀ s ∈ Γ, (decodeTarget J) ⊨ᵂᴷ s := by
  rw [tauSentenceSet, allMemFlatMap]
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  exact decodeSentenceLocal J s (fun q hq => h q (List.mem_flatMap.mpr ⟨s, hs, hq⟩))

/-- Classical models need bridges for the vocabulary of both premises and conclusions. -/
theorem entailmentK_iff_classical (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᵂᴷ Δ) ↔
      ((tauSentenceSet Γ ++ sentenceSetBridges Γ ++ sentenceSetBridges Δ) ⊨ᶜ tauSentenceSet Δ) := by
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
  tauSentenceSet (π Γ)

/-- Bridges for the names used by the polarized source KB. -/
def B (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ (σᵂᴷ)ᵀ) :=
  sentenceSetBridges (π Γ)

/-- AC entailment is exactly classical entailment of the translated KBs,
with the bridges of both KBs included among the premises. -/
theorem MainResult (σ : Signature) (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᴬᶜ Δ) ↔ ((T σ Γ ++ B σ Γ ++ B σ Δ) ⊨ᶜ T σ Δ) := by
  calc
    (Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ᵂᴷ π Δ)                  := A_iff_pi_WK Γ Δ
    _ ↔ ((T σ Γ ++ B σ Γ ++ B σ Δ) ⊨ᶜ T σ Δ) := entailmentK_iff_classical (π Γ) (π Δ)

end ALCHAC
