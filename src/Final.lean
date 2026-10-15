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


postfix:max "*" => Set

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

/--
Use v⁺ and v⁻ to access the positive and
negative components of a V₃² vector.
-/
postfix:max "⁺" => Prod.fst
postfix:max "⁻" => Prod.snd

/--
WK side indicator, used for accessing the positive or
negative component of a V₃² vector.
-/
inductive Side where
| positive --pi
| negative --nu
deriving DecidableEq, Repr

notation "+ₚ" => Side.positive
notation "-ₚ" => Side.negative

def V32.coordinate (v : V₃²) : Side → V₃
| +ₚ => v⁺
| -ₚ => v⁻

/--
v[s] overload for V₃² vectors.
We can use v[+ₚ] and v[-ₚ] to access the positive and
negative components respectively, but this is primarily used
parameterize sides in theorems.
Note v[+ₚ] = v⁺ and v[-ₚ] = v⁻.
-/
instance : GetElem (V₃²) Side V₃ (λ _ _ => True) where
  getElem := λ v s _ => v.coordinate s


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

@[simp]
def negA (v : V₃²) : V₃² := (v⁻, v⁺)
@[simp]
def andA (v w : V₃²) : V₃² := (v⁺ ∧ₖ w⁺, v⁻ ∨ₖ w⁻)
@[simp]
def orA (v w : V₃²) : V₃² := (v⁺ ∨ₖ w⁺, v⁻ ∧ₖ w⁻)

prefix:70 "∼ₐ " => negA
infixl:70 " ∧ₐ " => andA
infixl:65 " ∨ₐ " => orA

/-- Project the positive coordinates of AC role/concept pairs. -/
def acPositive (X : Set (V₃² × V₃²)) : Set V₃² :=
  Set.image (λ q => (q.1.1, q.2.1)) X

/-- Project the role's positive and the concept's negative coordinates. -/
def acNegative (X : Set (V₃² × V₃²)) : Set V₃² :=
  Set.image (λ q => (q.1.1, q.2.2)) X

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

notation  I "⊨ᶜ " φ => @evalSentenceC _ I φ

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

notation  I "⊨ᵂᴷ " φ => @satisfiesK _ I φ

/-- Entailment for weak Kleene semantics -/
def entailmentK (Γ Δ : (Φ σ)*) : Prop :=
  ∀ (I : ℐᵂᴷ σ), (∀ ψ ∈ Γ, I ⊨ᵂᴷ ψ) → (∀ φ ∈ Δ, I ⊨ᵂᴷ φ)

notation  Γ " ⊨ᵂᴷ " Δ => entailmentK Γ Δ

-- MARK: AC Semantics
/- # Analytic Containment Semantics -/

@[simp]
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
  (φᴵ)⁺ = 𝔱

notation  I "⊨ᴬᶜ " φ => @satisfiesA _ I φ

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

instance : Interpret σᵂᴷ V (σ.Nc × Side) :=
  ⟨λ I => I.D → V, (·.atomicConceptValuation)⟩

/--
piConcept recursively transforms an ALCH concept into its
weak Kleene counterpart based on the given side indicator
(+ₚ or -ₚ). Note that we don't use a seperate ν translation;
the side indicator is passed directly to piConcept.
π is `piConcept C +ₚ`, while ν would be `piConcept C -ₚ`,
but we really only need the π translation for our purposes.
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

/-- π c notation for sentences -/
instance : PiTranslation (𝒞 σ) (𝒞 σᵂᴷ) where
  piIze C := piConcept C +ₚ

/--
transforms an ALCH sentence over the original signature
σ to its weak Kleene counterpart over the signature σᵂᴷ
by applying the π translation to each concept within
the sentence.
-/
def piSentence : Φ σ → Φ σᵂᴷ
| a :ₐ c => a :ₐ π c
| (a, b) :ᵣ r => (a, b) :ᵣ r
| c ⊑ d => π c ⊑ π d
| c ≡ d => π c ≡ π d
| r ⊑ᵣ s => r ⊑ᵣ s

/-- π φ notationfor sentences -/
instance : PiTranslation (Φ σ) (Φ σᵂᴷ) where
  piIze := piSentence

/-- Transforms a set of ALCH sentences over the original
signature to their weak Kleene counterparts over the
signature σᵂᴷ -/
abbrev piSentenceSet : (Φ σ)* → (Φ σᵂᴷ)* :=
  Set.image piSentence

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

We also add bridge axioms to connect the truth and
meaningfulness components of concepts and roles.
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

instance : Interpret σᵀ V (σ.Nc × Bit) :=
  ⟨λ I => I.D → V, (·.atomicConceptValuation)⟩

instance : Interpret σᵀ V (σ.Nr × Bit) :=
  ⟨λ I => I.D → I.D → V, (·.roleValuation)⟩

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

/--
translation for subsumption sentences C ⊑ D into
the target signature.

-/
def tauSubsumption (c d : 𝒞 σ) : (Φᵁ σᵀ)* :=
  {τ c ⊑ τ d} ∪ {∃₁(μ c ⊓ₜ μ d)}

/--
Translation of ALCH sentences into ALCHU sentences with
the target signature.
-/
def tauSentence : Φ σ → (Φᵁ σᵀ)*
| a :ₐ c => ({show Φᵁ σᵀ from a :ₐ τ c} : (Φᵁ σᵀ)*)
| (a, b) :ᵣ r => ({show Φᵁ σᵀ from (a, b) :ᵣ [(r, 𝕋)]ᵣ} : (Φᵁ σᵀ)*)
| c ⊑ d => tauSubsumption c d
| c ≡ d => tauSubsumption c d ∪ tauSubsumption d c
| r ⊑ᵣ s => {[(r, 𝕋)]ᵣ ⊑ᵣ [(s, 𝕋)]ᵣ} ∪ {(r, 𝕄) ⨅⁺ (s, 𝕄)}

instance : TauTranslation (Φ σ) (Φᵁ σᵀ)* :=
  ⟨tauSentence⟩

def tauSentenceSet (Γ : (Φ σ)*) : (Φᵁ σᵀ)* :=
  Set.bind Γ tauSentence

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
| ⊤ => ∅
| ⊥ => ∅
| [a]ₐ => {𝒟 a}
| ¬ₜ c => ∇ c
| c ⊓ₜ d => ∇ c ∪ ∇ d
| c ⊔ₜ d => ∇ c ∪ ∇ d
| ∃[r] c => {𝒟 r} ∪ ∇ c
| ∀[r] c => {𝒟 r} ∪ ∇ c

instance : BridgeTranslation (𝒞 σ) (Φᵁ σᵀ)* :=
 ⟨conceptBridges⟩

def sentenceBridges : Φ σ → (Φᵁ σᵀ)*
| _ :ₐ c => 𝒟 c
| (_, _) :ᵣ r => {𝒟 r}
| c ⊑ d => 𝒟 c ∪ 𝒟 d
| c ≡ d => 𝒟 c ∪ 𝒟 d
| r ⊑ᵣ s => {𝒟 r} ∪ {𝒟 s}

instance : BridgeTranslation (Φ σ) (Φᵁ σᵀ)* :=
 ⟨sentenceBridges⟩

def sentenceSetBridges (Γ : (Φ σ)*) : (Φᵁ σᵀ)* :=
  Set.bind Γ sentenceBridges

instance : BridgeTranslation ((Φ σ)*) (Φᵁ σᵀ)* :=
 ⟨sentenceSetBridges⟩

-- MARK: Theorems
/-! # Theorems -/
/-!
Beginning here we prove our main result:
(Γ ⊨ᴬᶜ Δ) ↔ ((τ (π Γ) ∪ 𝒟 (π Γ) ∪ 𝒟 (π Δ)) ⊨ᶜ τ (π Δ))
Where π is our AC to WK translation,
τ is our WK to C translation,
and 𝒟 represents the bridge axioms.

Proof Sketch: We break the proof into two lemmas,
first showing we can translate the AC entailment
into the WK framework:
Γ ⊨ᴬᶜ Δ ↔ π Γ ⊨ᵂᴷ π Δ
and then demonstrating that
the WK translation, together with the bridge axioms,
entails the corresponding classical entailment
(Γ ⊨ᵂᴷ Δ) ↔ ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ)
-/

-- MARK: WK Lemmas
/- ## WK Lemmas -/

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

/--
v ∨ₖ w is 𝔱 iff at least one of v and w is 𝔱
and both are not 𝔢
-/
@[simp]
theorem orK_t (v w : V₃) :
v ∨ₖ w = 𝔱 ↔ (v = 𝔱 ∨ w = 𝔱) ∧ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp]
theorem orK_m (v w : V₃) : v ∨ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

/-- ∃ₖ X is true iff X contains (𝔱, 𝔱). -/
@[simp] theorem existsK_t (X : Set V₃²) :
∃ₖ X = 𝔱 ↔ (𝔱, 𝔱) ∈ X := by
  classical
  unfold existsK
  repeat (split <;> (try rfl) <;> (try grind only))

/-- ∃ₖ X is meaningful when a pair is fully meaningful. -/
@[simp] theorem existsK_m (X : Set V₃²) :
∃ₖ X ≠ 𝔢 ↔ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold existsK
  repeat (split <;> (try rfl) <;> (try grind only))

/-- ∀ₖ X is true exactly under its set-based true clause. -/
private theorem forallK_true (X : Set V₃²) :
∀ₖ X = 𝔱 ↔
(𝔱, 𝔣) ∉ X ∧ (𝔱, 𝔢) ∉ X ∧ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold forallK
  repeat (split <;> (try rfl) <;> (try grind only))

/-- ∀ₖ X is meaningful exactly when a pair is fully meaningful. -/
@[simp] theorem forallK_m (X : Set V₃²) :
∀ₖ X ≠ 𝔢 ↔ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold forallK
  repeat (split <;> (try rfl) <;> (try grind only))

theorem forallK_t_aux (X : Set V₃²) :
((𝔱, 𝔣) ∉ X ∧ (𝔱, 𝔢) ∉ X) ↔ ∀ p ∈ X, p.1 = 𝔱 → p.2 = 𝔱 := by
  constructor
  · rintro ⟨hf, he⟩ ⟨r, c⟩ hp hr
    change r = 𝔱 at hr
    subst r
    cases c <;> simp_all
  · intro h
    constructor
    · intro hp
      have := h (𝔱, 𝔣) hp rfl
      contradiction
    · intro hp
      have := h (𝔱, 𝔢) hp rfl
      contradiction

/--
∀ₖ X is true iff every true role coordinate has a true
concept coordinate and X contains a fully meaningful pair.
-/
@[simp]
theorem forallK_t (X : Set V₃²) :
∀ₖ X = 𝔱 ↔
(∀ p ∈ X, p.1 = 𝔱 → p.2 = 𝔱) ∧
∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  rw [forallK_true, ←and_assoc, forallK_t_aux]

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

-- MARK: AC to WK Theorems
/-! ## AC to Weak Kleene Theorems -/
/-!
In this section we prove π preserves entailment.
Γ ⊨ᴬᶜ Δ ↔ π Γ ⊨ᵂᴷ π Δ

Proof.
We give a construction ·○ on AC interpretations to
WK interpretations such that we have for
concepts c and individuals x:
((c^I) x)⁺ = (π c)^(○I) x
Which we lift to sentences
(π φ)^(○I) = (φ^I)⁺
And then lift to entailment:
(I ⊨ᴬᶜ φ) ↔ (○I ⊨ᵂᴷ (π φ))
from which we obtain
Γ ⊨ᴬᶜ Δ ↔ π Γ ⊨ᵂᴷ π Δ
-/

/--
Construction ○· from AC interpretations to
WK interpretations on the translated signature σᵂᴷ.
-/
@[instance_reducible]
def acToWK [I : ℐᴬᶜ σ] : ℐᵂᴷ σᵂᴷ where
  D :=                      Δᴵ
  inhabited :=              I.inhabited
  individualValuation :=    λ x => xᴵ
  atomicConceptValuation := λ (a, s) x => (aᴵ x)[s]
  roleValuation :=          λ r x y => (rᴵ x y)⁺

prefix:max "○" => λx => @acToWK _ x

/--
Construction ●· from WK interpretations on
the translated signature σᵂᴷ to AC interpretations on σ.
-/
@[instance_reducible]
def wkToAC [I : ℐᵂᴷ σᵂᴷ] : ℐᴬᶜ σ where
  D :=                      Δᴵ
  inhabited :=              I.inhabited
  individualValuation :=    λ x => xᴵ
  atomicConceptValuation := λ a x => ((a, +ₚ)ᴵ x, (a, -ₚ)ᴵ x)
  roleValuation :=          λ r x y => (rᴵ x y, 𝔢)

prefix:max "●" => λx => @wkToAC _ x

/--
○ and ● are inverses of each other.
-/
theorem acToWK_wkToAC (I : ℐᵂᴷ σᵂᴷ) : ○●I = I := by
  cases I with
  | mk D inhabited individuals atoms roles =>
      simp only [acToWK]
      congr 1
      funext a x
      rcases a with ⟨a, side⟩
      cases side <;> rfl

/--
Given an AC interpretation I, an individual x in Δᴵ,
an ALCH concept C, we have that our translations π and
ν preserve the positive and negative coordinates in their
in the WK ○I interpretation.

((c^I) x)⁺ = ((π c)^(○I)) x
((c^I) x)⁻ = ((ν c)^(○I)) x

Note that we prove a general side independent version
despite only needing ((c^I) x)⁺ = ((π c)^(○I)) x,
since the proof is much nicer.
-/
theorem acConceptCoordinates (I : ℐᴬᶜ σ) (c : 𝒞 σ)
(x : I.D) (s : Side) :
((piConcept c s)^(○I)) x = ((c^I) x)[s] := by
  simp only [Interpret.interpret]
  induction c generalizing s x with
  | top | bot | atom => cases s <;> rfl
  | neg c ih =>
      cases s <;> simp only
        [piConcept, evalConceptA, negA, GetElem.getElem,
         V32.coordinate, ih]
  | conj c d ihc ihd =>
      cases s <;> simp only
        [piConcept, evalConceptK, evalConceptA, andA,
          GetElem.getElem, V32.coordinate, ihc, ihd]
  | disj c d ihc ihd =>
      cases s <;> simp only
        [piConcept, evalConceptK, evalConceptA, orA,
          GetElem.getElem, V32.coordinate, ihc, ihd]
  | ex r c ih =>
      cases s <;> simp only
        [piConcept, evalConceptK, evalConceptA, existsA,
          acPositive, acNegative, Set.image_ofValues, ih,
          GetElem.getElem, V32.coordinate] <;> rfl
  | all r c ih =>
      cases s <;> simp only
        [piConcept, evalConceptK, evalConceptA, forallA,
          acPositive, acNegative, Set.image_ofValues, ih,
          GetElem.getElem, V32.coordinate] <;> rfl

/-- Translating a concept preserves its positive AC coordinate. -/
theorem acConceptSupport (I : ℐᴬᶜ σ) (c : 𝒞 σ) (x : Δᴵ) :
((π c)^(○I)) x = ((c^I) x)⁺ :=
  acConceptCoordinates I c x +ₚ

theorem acSentenceSupport (I : ℐᴬᶜ σ) (φ : Φ σ) :
(π φ)^(○I) = (φ^I)⁺ := by
  have hc (c : 𝒞 σ) : (π c)^(○I) = λ x => ((c^I) x)⁺ :=
    funext (acConceptSupport (I := I) c)
  simp only [Interpret.interpret, PiTranslation.piIze] at hc
  cases φ <;> simp only [
    Interpret.domain, Interpret.current,
    Interpret.interpret, PiTranslation.piIze, piSentence,
    evalSentenceK, evalSentenceA, forallA, andA, hc,
    acPositive, Set.image_ofValues] <;> rfl

theorem acSentenceSupport_iff (I : ℐᴬᶜ σ) (φ : Φ σ) :
(I ⊨ᴬᶜ φ) ↔ (○I ⊨ᵂᴷ π φ) := by
  change (φ^I)⁺ = 𝔱 ↔ (π φ)^(○I) = 𝔱
  rw [acSentenceSupport]

theorem A_implies_pi_WK (Γ Δ : (Φ σ)*) :
(Γ ⊨ᴬᶜ Δ) → (π Γ ⊨ᵂᴷ π Δ) := by
  intro h I hΓ ψ hψ
  have hround : ○●I = I := acToWK_wkToAC I
  rcases Set.mem_image.mp hψ with ⟨φ, hφ, rfl⟩
  have hsource : ∀ ψ ∈ Γ, ●I ⊨ᴬᶜ ψ := by
    intro ψ hψ
    have htranslated := hΓ (π ψ) (Set.mem_image.mpr ⟨ψ, hψ, rfl⟩)
    exact (acSentenceSupport_iff (●I) ψ).mpr (hround ▸ htranslated)
  have hout := h (●I) hsource φ hφ
  exact hround ▸ (acSentenceSupport_iff (●I) φ).mp hout

theorem pi_WK_implies_A (Γ Δ : (Φ σ)*) :
(π Γ ⊨ᵂᴷ π Δ) → (Γ ⊨ᴬᶜ Δ) := by
  intro h I hΓ φ hφ
  have hprojected : ∀ ψ ∈ π Γ, ○I ⊨ᵂᴷ ψ := by
    intro ψ hψ
    rcases Set.mem_image.mp hψ with ⟨φ, hφ, rfl⟩
    exact (acSentenceSupport_iff I φ).mp (hΓ φ hφ)
  have hout := h (○I) hprojected (π φ)
    (Set.mem_image.mpr ⟨φ, hφ, rfl⟩)
  exact (acSentenceSupport_iff I φ).mpr hout

/-- The explicit WK entailment intermediate used in the final theorem. -/
theorem A_iff_pi_WK (Γ Δ : (Φ σ)*) :
(Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ᵂᴷ π Δ) :=
  Iff.intro (A_implies_pi_WK Γ Δ) (pi_WK_implies_A Γ Δ)


-- MARK: WK to C
/-! ## WK to classical ALCH -/
/--
In this section, we prove that τ and bridging axioms 𝒟
correctly translate WK entailment into classical ALCH
entailment.

(Γ ⊨ᵂᴷ Δ) ↔ ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ)

Proof Sketch:
The core idea is that we define a construction
□· on WK interpretations such that for concepts c we have
((τ c)^(□I)) x ↔ (c^I) x = 𝔱 and
((μ c)^(□I)) x ↔ (c^I) x ≠ 𝔢
along with an ■· construction such that
((τ c)^I) x ↔ (c^■I) x = 𝔱 and
((μ c)^I) x ↔ (c^■I) x ≠ 𝔢

for □· we lift to satisfaction
(∀ φ ∈ τ Γ, □I ⊨ᶜ φ) ↔ ∀ φ ∈ Γ, I ⊨ᵂᴷ φ
and have for the bridging axioms 𝒟 that
∀ ψ ∈ 𝒟 Γ, □I ⊨ᶜ ψ

for ■· we have the following satisfaction lifting
that depends on our aditional bridging axioms 𝒟.
(∀ ψ ∈ 𝒟 φ, I ⊨ᶜ ψ) →
(∀ ψ ∈ τ φ, I ⊨ᶜ ψ) ↔ ■I ⊨ᵂᴷ φ

These three together then allow us to show
(Γ ⊨ᵂᴷ Δ) ↔ ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ)
-/

-- MARK: Lemmas

@[simp]
theorem concept_mu (c : 𝒞 σ) : μ c = muConcept c := rfl
@[simp]
theorem concept_tau (c : 𝒞 σ) : τ c = tauConcept c := rfl

theorem allMemUnion {α : Type} (P : α → Prop) (xs ys : α*) :
(∀ x ∈ xs ∪ ys, P x) ↔ (∀ x ∈ xs, P x) ∧ (∀ x ∈ ys, P x) := by
  simp only [Set.mem_union, or_imp, forall_and]

theorem translateInclusion_iff (I : ℐᶜ σᵀ) (c d : 𝒞 σ) :
(∀ ψ ∈ tauSubsumption c d, I ⊨ᶜ ψ) ↔
(∀ x, ((τ c)^I) x → ((τ d)^I) x) ∧
∃ x, ((μ c)^I) x ∧ ((μ d)^I) x := by
  simp only [tauSubsumption, Set.mem_union, Set.mem_singleton,
    forall_eq_or_imp, forall_eq]
  rw [nonempty_iff]
  rfl

private theorem allMemBind {α β : Type} (P : β → Prop) (f : α → β*)
(xs : α*) :
(∀ y ∈ Set.bind xs f, P y) ↔ ∀ x ∈ xs, ∀ y ∈ f x, P y := by
  constructor
  · intro h x hx y hy
    exact h y (Set.mem_bind.mpr ⟨x, hx, hy⟩)
  · intro h y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_bind.mp hy
    exact h x hx y hy

-- MARK: Encoding
/-!
In this section we prove:
((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ) → (Γ ⊨ᵂᴷ Δ)
-/

/--
Our □· construction maps WK interpretations
to classical ALCH interpretations.
-/
@[instance_reducible]
def encodeWK [I : ℐᵂᴷ σ] : ℐᶜ σᵀ where
  D := Δᴵ
  inhabited := I.inhabited
  individualValuation := λ x => xᴵ
  atomicConceptValuation :=
  λ (a, bit) x => match bit with
  | 𝕋 =>  aᴵ x = 𝔱
  | 𝕄 =>  aᴵ x ≠ 𝔢
  roleValuation :=
  λ (r, bit) x y => match bit with
  | 𝕋 =>  rᴵ x y = 𝔱
  | 𝕄 =>  rᴵ x y ≠ 𝔢

prefix:max "□" => λI => @encodeWK _ I

theorem translateConceptEncode (I : ℐᵂᴷ σ) (c : 𝒞 σ) (x : I.D) :
(((τ c)^(□I)) x ↔ (c^I) x = 𝔱) ∧
(((μ c)^(□I)) x ↔ (c^I) x ≠ 𝔢) := by
  simp only [Interpret.interpret]
  induction c generalizing x with
  | top | bot =>
      simp only [
        concept_tau, concept_mu, tauConcept, muConcept,
        evalConceptC, evalConceptK]
      decide
  | atom a =>
      simp only [Interpret.current, Interpret.interpret,
        concept_tau, concept_mu, tauConcept, muConcept,
        evalConceptC, evalConceptK, encodeWK, true_and]
  | neg c ih =>
      simp only [concept_tau, concept_mu] at ih
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK, (ih x).1,
        (ih x).2, negK_t, negK_m, true_and]
  | conj c d ihc ihd =>
      simp only [concept_tau, concept_mu] at ihc ihd
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK, (ihc x).1,
        (ihc x).2, (ihd x).1, (ihd x).2, andK_t, andK_m,
        true_and]
  | disj c d ihc ihd =>
      simp only [concept_tau, concept_mu] at ihc ihd
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK, (ihc x).1,
        (ihc x).2, (ihd x).1, (ihd x).2, orK_t, orK_m,
        true_and]
  | ex r c ih =>
      simp only [Interpret.current, Interpret.interpret,
        evalConceptC, evalRoleC, concept_tau, concept_mu,
        tauConcept, muConcept, encodeWK, evalConceptK,
        existsK_t, existsK_m, Set.exists_mem_ofValues]
      simp only [Set.mem_ofValues, Prod.mk.injEq]
      exact ⟨exists_congr (λ y => and_congr Iff.rfl (ih y).1),
        exists_congr (λ y => and_congr Iff.rfl (ih y).2)⟩
  | all r c ih =>
      simp only [Interpret.current, Interpret.interpret,
        evalConceptC, evalRoleC, concept_tau, concept_mu,
        tauConcept, muConcept, encodeWK, evalConceptK,
        forallK_t, forallK_m, Set.forall_mem_ofValues,
        Set.exists_mem_ofValues]
      refine ⟨and_congr ?_ ?_, ?_⟩
      · exact forall_congr' (λ y => imp_congr Iff.rfl (ih y).1)
      · exact exists_congr (λ y => and_congr Iff.rfl (ih y).2)
      · exact exists_congr (λ y => and_congr Iff.rfl (ih y).2)

theorem encodedatomicConceptBridge (I : ℐᵂᴷ σ) (a : σ.Nc) :
□I ⊨ᶜ 𝒟 a := by
  simp only [Interpret.current, Interpret.interpret,
    BridgeTranslation.bridge, atomicConceptBridge,
    evalSentenceC, evalConceptC, encodeWK]
  intro x h
  rw [h]
  decide

theorem encodedatomicRoleBridge (I : ℐᵂᴷ σ) (r : σ.Nr) :
□I ⊨ᶜ 𝒟 r := by
  simp only [Interpret.current, Interpret.interpret,
    BridgeTranslation.bridge, atomicRoleBridge,
    evalSentenceC, evalRoleC, encodeWK]
  intro x y h
  rw [h]
  decide

theorem encodedConceptBridges (I : ℐᵂᴷ σ) (c : 𝒞 σ) :
∀ φ ∈ 𝒟 c, □I ⊨ᶜ φ := by
  induction c with
  | top | bot => intro ψ hψ; cases hψ
  | atom a =>
      simpa only [conceptBridges, BridgeTranslation.bridge,
        Set.mem_singleton, forall_eq] using
        encodedatomicConceptBridge I a
  | neg c ih => exact ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      simpa only [conceptBridges, BridgeTranslation.bridge,
        Set.mem_union, or_imp, forall_and] using
        And.intro ihc ihd
  | ex r c ih | all r c ih =>
      simpa only [conceptBridges, BridgeTranslation.bridge,
        Set.mem_union, Set.mem_singleton, or_imp,
        forall_and, forall_eq] using
        And.intro (encodedatomicRoleBridge I r) ih

theorem encodedSentenceBridges (I : ℐᵂᴷ σ) (φ : Φ σ) :
∀ ψ ∈ 𝒟 φ, □I ⊨ᶜ ψ := by
  cases φ with
  | isa a c => exact encodedConceptBridges I c
  | role a b r =>
      simpa only [sentenceBridges, BridgeTranslation.bridge,
        Set.mem_singleton, forall_eq] using
        encodedatomicRoleBridge I r
  | sub c d | equiv c d =>
      simpa only [sentenceBridges, BridgeTranslation.bridge,
        Set.mem_union, or_imp, forall_and] using
        And.intro (encodedConceptBridges I c)
        (encodedConceptBridges I d)
  | rsub r s =>
      intro ψ hψ
      simp only [sentenceBridges, BridgeTranslation.bridge,
        Set.mem_union, Set.mem_singleton] at hψ
      rcases hψ with rfl | rfl
      · exact encodedatomicRoleBridge I r
      · exact encodedatomicRoleBridge I s

theorem translateInclusionEncode (I : ℐᵂᴷ σ) (c d : 𝒞 σ) :
(∀ ψ ∈ tauSubsumption c d, □I ⊨ᶜ ψ) ↔
∀ₖ {((c^I) x, (d^I) x) | x : I.D} = 𝔱 := by
  simp only [Interpret.interpret]
  rw [translateInclusion_iff, forallK_t]
  simp only [Set.forall_mem_ofValues, Set.exists_mem_ofValues]
  exact and_congr
    (forall_congr' (λ x => imp_congr (translateConceptEncode I c x).1
      (translateConceptEncode I d x).1))
    (exists_congr (λ x => and_congr (translateConceptEncode I c x).2
      (translateConceptEncode I d x).2))

theorem tauSentenceEncode (I : ℐᵂᴷ σ) (φ : Φ σ) :
(∀ ψ ∈ τ φ, □I ⊨ᶜ ψ) ↔ I ⊨ᵂᴷ φ := by
  cases φ with
  | isa a c =>
      simp only [Interpret.current, TauTranslation.tau,
        tauSentence, Set.mem_singleton, forall_eq,
        evalSentenceC, satisfiesK]
      exact (translateConceptEncode I c ((I.individualValuation a))).1
  | role a b r =>
      simp only [Interpret.current, Interpret.interpret,
        TauTranslation.tau, tauSentence, Set.mem_singleton,
        forall_eq, evalSentenceC, evalRoleC, encodeWK,
        satisfiesK, evalSentenceK]
  | sub c d => exact translateInclusionEncode I c d
  | equiv c d =>
      simp only [Interpret.current, Interpret.interpret,
        TauTranslation.tau, tauSentence, allMemUnion,
        translateInclusionEncode, satisfiesK, evalSentenceK]
      rw [andK_t]
  | rsub r s =>
      simp only [TauTranslation.tau,tauSentence,
        Set.mem_union, Set.mem_singleton,
        forall_eq_or_imp, forall_eq]
      rw [overlap_iff (I := @encodeWK _ I)]
      simp only [Interpret.domain, Interpret.current,
        Interpret.interpret, evalSentenceC, evalRoleC,
        encodeWK, satisfiesK, evalSentenceK]
      rw [forallK_t]
      simp only [Set.forall_mem_ofValues, Set.exists_mem_ofValues]
      simp only [Prod.forall, Prod.exists]

theorem translateKBEncode (I : ℐᵂᴷ σ) (Γ : (Φ σ)*) :
(∀ φ ∈ τ Γ, □I ⊨ᶜ φ) ↔ ∀ φ ∈ Γ, I ⊨ᵂᴷ φ := by
  simp only [TauTranslation.tau, tauSentenceSet, allMemBind]
  exact forall_congr' (λ φ => imp_congr Iff.rfl (tauSentenceEncode I φ))

theorem encodedKBBridges (I : ℐᵂᴷ σ) (Γ : (Φ σ)*) :
∀ ψ ∈ 𝒟 Γ, □I ⊨ᶜ ψ := by
  simp [BridgeTranslation.bridge]
  rw [sentenceSetBridges, allMemBind]
  exact λ φ _ => encodedSentenceBridges I φ

theorem classical_imp_entailmentK (Γ Δ : (Φ σ)*) :
((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ) → (Γ ⊨ᵂᴷ Δ) := by
  intro h I hI
  apply (translateKBEncode I Δ).mp
  apply h (□I)
  rw [allMemUnion, allMemUnion]
  exact ⟨⟨(translateKBEncode I Γ).mpr hI, encodedKBBridges I Γ⟩,
    encodedKBBridges I Δ⟩

-- MARK: Decoding
/-!
In this section we prove
((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ) → (Γ ⊨ᵂᴷ Δ)
-/

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
noncomputable def decodeTarget [I : ℐᶜ σᵀ] : ℐᵂᴷ σ where
  D := Δᴵ
  inhabited := I.inhabited
  individualValuation := λ x => xᴵ
  atomicConceptValuation :=
    λ a x => propValue ((a, 𝕋)ᴵ x) ((a, 𝕄)ᴵ x)
  roleValuation :=
    λ r x y => propValue ((r, 𝕋)ᴵ x y) ((r, 𝕄)ᴵ x y)

prefix:max "■" => λ I => @decodeTarget _ I

/--
Bridges are needed only for the names occurring in the
concept being decoded.
-/
theorem decodeConceptLocal (I : ℐᶜ σᵀ) (c : 𝒞 σ)
(h : ∀ ψ ∈ 𝒟 c, I ⊨ᶜ ψ) (x : I.D) :
(((τ c)^I) x ↔ (c^■I) x = 𝔱) ∧
(((μ c)^I) x ↔ (c^■I) x ≠ 𝔢) := by
  simp only [Interpret.interpret]
  induction c generalizing x with
  | top | bot =>
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK]
      decide
  | atom a =>
      have ha : ∀ y, ((a, 𝕋)^I) y → ((a, 𝕄)^I) y :=
        h (atomicConceptBridge a)
        (by simp only [conceptBridges,
        BridgeTranslation.bridge, Set.mem_singleton])
      exact ⟨(propValue_truth _ _).symm,
        (propValue_meaningful _ _ (ha x)).symm⟩
  | neg c ih =>
      have hc := ih h
      simp only [concept_tau, concept_mu] at hc
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK,
        (hc x).1, (hc x).2, negK_t, negK_m, true_and]
  | conj c d ihc ihd =>
      have hc := ihc (λ ψ hψ => h ψ (Set.mem_union_left _ hψ))
      have hd := ihd (λ ψ hψ => h ψ (Set.mem_union_right _ hψ))
      simp only [concept_tau, concept_mu] at hc hd
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK, (hc x).1,
        (hc x).2, (hd x).1, (hd x).2, andK_t, andK_m, true_and]
  | disj c d ihc ihd =>
      have hc := ihc (λ ψ hψ => h ψ (Set.mem_union_left _ hψ))
      have hd := ihd (λ ψ hψ => h ψ (Set.mem_union_right _ hψ))
      simp only [concept_tau, concept_mu] at hc hd
      simp only [concept_tau, concept_mu, tauConcept,
        muConcept, evalConceptC, evalConceptK, (hc x).1,
        (hc x).2, (hd x).1, (hd x).2, orK_t, orK_m, true_and]
  | ex r c ih =>
      have hr : ∀ y z, ((r, 𝕋)ᴵ) y z → ((r, 𝕄)ᴵ) y z :=
        h (atomicRoleBridge r)
        (by simp [conceptBridges, BridgeTranslation.bridge])
      have hc := ih (λ ψ hψ => h ψ (Or.inr hψ))
      simp only [Interpret.current, Interpret.interpret,
        evalConceptC, evalRoleC, concept_tau, concept_mu,
        tauConcept, muConcept, decodeTarget, evalConceptK]
      simp only [existsK_t, existsK_m, Set.exists_mem_ofValues]
      simp only [Set.mem_ofValues, Prod.mk.injEq]
      exact ⟨exists_congr
        (λ y => and_congr (propValue_truth _ _).symm (hc y).1),
        exists_congr (λ y => and_congr
          (propValue_meaningful _ _ (hr x y)).symm (hc y).2)⟩
  | all r c ih =>
      have hr : ∀ y z, ((r, 𝕋)ᴵ) y z → ((r, 𝕄)ᴵ) y z :=
        h (atomicRoleBridge r)
        (by simp [conceptBridges, BridgeTranslation.bridge])
      have hc := ih (λ ψ hψ => h ψ (Or.inr hψ))
      simp only [Interpret.current, Interpret.interpret,
        evalConceptC, evalRoleC, concept_tau, concept_mu,
        tauConcept, muConcept, decodeTarget, evalConceptK]
      simp only [forallK_t, forallK_m,
        Set.forall_mem_ofValues, Set.exists_mem_ofValues]
      refine ⟨and_congr ?_ ?_, ?_⟩
      · exact forall_congr' (λ y =>
          imp_congr (propValue_truth _ _).symm (hc y).1)
      · exact exists_congr (λ y =>
          and_congr (propValue_meaningful _ _ (hr x y)).symm (hc y).2)
      · exact exists_congr (λ y =>
          and_congr (propValue_meaningful _ _ (hr x y)).symm (hc y).2)

theorem decodeInclusionLocal (I : ℐᶜ σᵀ)
(c d : 𝒞 σ)
(hc : ∀ ψ ∈ 𝒟 c, I ⊨ᶜ ψ)
(hd : ∀ ψ ∈ 𝒟 d, I ⊨ᶜ ψ) :
(∀ ψ ∈ tauSubsumption c d, I ⊨ᶜ ψ) ↔
∀ₖ {((c^(■I)) x, (d^(■I)) x) | x : I.D} = 𝔱 := by
  simp only [Interpret.interpret]
  rw [translateInclusion_iff, forallK_t]
  simp only [Set.forall_mem_ofValues, Set.exists_mem_ofValues]
  exact and_congr
    (forall_congr' (λ x => imp_congr (decodeConceptLocal I c hc x).1
      (decodeConceptLocal I d hd x).1))
    (exists_congr (λ x => and_congr (decodeConceptLocal I c hc x).2
      (decodeConceptLocal I d hd x).2))

theorem decodeSentenceLocal (I : ℐᶜ σᵀ) (φ : Φ σ)
(h : ∀ ψ ∈ 𝒟 φ, I ⊨ᶜ ψ) :
(∀ ψ ∈ τ φ, I ⊨ᶜ ψ) ↔ ■I ⊨ᵂᴷ φ := by
  cases φ with
  | isa a c =>
      simp only [Interpret.current, TauTranslation.tau,
        tauSentence, Set.mem_singleton, forall_eq,
        evalSentenceC, satisfiesK]
      exact (decodeConceptLocal I c h ((I.individualValuation a))).1
  | role a b r =>
      simp only [Interpret.current, Interpret.interpret,
        TauTranslation.tau, tauSentence, Set.mem_singleton,
        forall_eq, evalSentenceC, evalRoleC, decodeTarget,
        satisfiesK, evalSentenceK]
      exact (propValue_truth _ _).symm
  | sub c d =>
      exact decodeInclusionLocal I c d
        (λ ψ hψ => h ψ (Set.mem_union_left _ hψ))
        (λ ψ hψ => h ψ (Set.mem_union_right _ hψ))
  | equiv c d =>
      have hc : ∀ ψ ∈ conceptBridges c, I ⊨ᶜ ψ :=
        λ ψ hψ => h ψ (Set.mem_union_left _ hψ)
      have hd : ∀ ψ ∈ conceptBridges d, I ⊨ᶜ ψ :=
        λ ψ hψ => h ψ (Set.mem_union_right _ hψ)
      simp only [Interpret.current, Interpret.interpret,
        TauTranslation.tau, tauSentence, allMemUnion,
        decodeInclusionLocal I c d hc hd,
        decodeInclusionLocal I d c hd hc,
        satisfiesK, evalSentenceK]
      rw [andK_t]
      rfl
  | rsub r s =>
      have hr : ∀ x y, (I.roleValuation (r, 𝕋)) x y →
          (I.roleValuation (r, 𝕄)) x y :=
        h (atomicRoleBridge r) (by simp only [sentenceBridges, BridgeTranslation.bridge, Set.mem_union, Set.mem_singleton, eq_self, true_or])
      have hs : ∀ x y, (I.roleValuation (s, 𝕋)) x y →
          (I.roleValuation (s, 𝕄)) x y :=
        h (atomicRoleBridge s) (by simp only [sentenceBridges, BridgeTranslation.bridge, Set.mem_union, Set.mem_singleton,
          eq_self, or_true])
      simp only [TauTranslation.tau, tauSentence,
        Set.mem_union, Set.mem_singleton, forall_eq_or_imp,
        forall_eq]
      rw [overlap_iff]
      simp only [Interpret.domain, Interpret.current, Interpret.interpret, evalSentenceC, evalRoleC, satisfiesK,
        evalSentenceK, decodeTarget]
      rw [forallK_t]
      simp only [Set.forall_mem_ofValues, Set.exists_mem_ofValues]
      simp only [Prod.forall, Prod.exists, propValue_truth,
        λ x y => propValue_meaningful _ _ (hr x y),
        λ x y => propValue_meaningful _ _ (hs x y)]

theorem decodeKBLocal (I : ℐᶜ σᵀ) (Γ : (Φ σ)*)
(h : ∀ ψ ∈ 𝒟 Γ, I ⊨ᶜ ψ) :
(∀ ψ ∈ τ Γ, I ⊨ᶜ ψ) ↔ ∀ φ ∈ Γ, ■I ⊨ᵂᴷ φ := by
  simp [TauTranslation.tau]
  rw [tauSentenceSet, allMemBind]
  apply forall_congr'
  intro φ
  apply forall_congr'
  intro hφ
  exact decodeSentenceLocal I φ (λ ψ hψ => h ψ (Set.mem_bind.mpr ⟨φ, hφ, hψ⟩))

theorem entailmentK_imp_classical (Γ Δ : (Φ σ)*) :
(Γ ⊨ᵂᴷ Δ) → ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ)  := by
  intro h I hI
  rw [allMemUnion, allMemUnion] at hI
  rcases hI with ⟨⟨hΓ, hBΓ⟩, hBΔ⟩
  apply (decodeKBLocal I Δ hBΔ).mpr
  exact h (■I) ((decodeKBLocal I Γ hBΓ).mp hΓ)

-- MARK: WK to C

/-- Main WK to C entailment result -/
theorem entailmentK_iff_classical (Γ Δ : (Φ σ)*) :
(Γ ⊨ᵂᴷ Δ) ↔ ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ) :=
  Iff.intro
  (entailmentK_imp_classical Γ Δ)
  (classical_imp_entailmentK Γ Δ)

-- MARK: AC to C
/-! ## The composed AC translation -/

/-- AC entailment is exactly classical entailment of the translated KBs,
with the bridges of both KBs included among the premises. -/
theorem MainResult (σ : Signature) (Γ Δ : (Φ σ)*) :
(Γ ⊨ᴬᶜ Δ) ↔ ((τ (π Γ) ∪ 𝒟 (π Γ) ∪ 𝒟 (π Δ)) ⊨ᶜ τ (π Δ)) := by
  calc
    (Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ᵂᴷ π Δ)                  := A_iff_pi_WK Γ Δ
    _         ↔ ((τ (π Γ) ∪ 𝒟 (π Γ) ∪ 𝒟 (π Δ)) ⊨ᶜ τ (π Δ))    := entailmentK_iff_classical (π Γ) (π Δ)

end ALCHAC
