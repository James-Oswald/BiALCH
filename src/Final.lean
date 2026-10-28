import DefDel
import Utils

/-!
\section{Background}

This document formalizes the translation of analytic-containment entailment
through weak Kleene semantics into classical $\mathcal{ALCHRU}$ entailment.
-/

namespace ALCHAC

--myne:appendix_start Overloaded Notation Classes

-- MARK: Notation
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
--myne:appendix_end

-- MARK: Truth Values
/-! \subsection{$\mathsf{WK}$ and $\mathsf{AC}$} -/
/-! \subsubsection{Truth Values and Pairs} -/

/--
@name Truth values and pairs
@capture block
@nl
The classical truth values $V_2$ are $\{\mathsf{True},\mathsf{False}\}$; the weak Kleene truth values $V_3$ are ${\mathfrak{t}, \mathfrak{e}, \mathfrak{f}}$. The AC truth values $V_3^2$ are pairs of Weak Kleene truth values.
@formula
$$V_2:=\mathsf{Prop},\quad V_3:=\{\mathfrak{t},\mathfrak{e},\mathfrak{f}\},\quad V_3^2:=V_3\times V_3$$
-/
abbrev V₂ := Prop

inductive V₃ where
| t
| e
| f
deriving DecidableEq, Repr

notation "𝔱" => V₃.t
notation "𝔢" => V₃.e
notation "𝔣" => V₃.f

abbrev V32 := V₃ × V₃
notation "V₃²" => V32
--myne:end

/--
@name Weak Kleene side access
@capture block
@nl
For a pair $(v^+,v^-)$ in $V_3^2$, the postfixes $+$ and $-$ select its first and second coordinates. The side-indexed accessor selects either coordinate using a value of type `Side`.
@formula
$$v[+_{\mathrm p}]:=v^+,\quad v[-_{\mathrm p}]:=v^-$$
-/
postfix:max "⁺" => Prod.fst
postfix:max "⁻" => Prod.snd

inductive Side where
| positive --pi
| negative --nu
deriving DecidableEq, Repr

notation "+ₚ" => Side.positive
notation "-ₚ" => Side.negative

def V32.coordinate (v : V₃²) : Side → V₃
| +ₚ => v⁺
| -ₚ => v⁻

instance : GetElem (V₃²) Side V₃ (λ _ _ => True) where
  getElem := λ v s _ => v.coordinate s
--myne:end


-- MARK: WK Operators
/-! \subsubsection{Weak Kleene Operators} -/

/--
@name Weak Kleene connectives
@capture block
@nl
Each connective takes values in $V_3$. Negation exchanges $\mathfrak{t}$ and $\mathfrak{f}$ and leaves $\mathfrak{e}$ unchanged. Conjunction and disjunction return $\mathfrak{e}$ whenever either input is $\mathfrak{e}$; when both inputs are in $\{\mathfrak{t},\mathfrak{f}\}$, they use the ordinary two-valued tables.
@formula
$$
\begin{array}{c|c}
v & \neg_K v\\\hline
\mathfrak{t} & \mathfrak{f}\\
\mathfrak{e} & \mathfrak{e}\\
\mathfrak{f} & \mathfrak{t}
\end{array}
\qquad
\begin{array}{c|ccc}
\wedge_K & \mathfrak{t} & \mathfrak{e} & \mathfrak{f}\\\hline
\mathfrak{t} & \mathfrak{t} & \mathfrak{e} & \mathfrak{f}\\
\mathfrak{e} & \mathfrak{e} & \mathfrak{e} & \mathfrak{e}\\
\mathfrak{f} & \mathfrak{f} & \mathfrak{e} & \mathfrak{f}
\end{array}
\qquad
\begin{array}{c|ccc}
\vee_K & \mathfrak{t} & \mathfrak{e} & \mathfrak{f}\\\hline
\mathfrak{t} & \mathfrak{t} & \mathfrak{e} & \mathfrak{t}\\
\mathfrak{e} & \mathfrak{e} & \mathfrak{e} & \mathfrak{e}\\
\mathfrak{f} & \mathfrak{t} & \mathfrak{e} & \mathfrak{f}
\end{array}
$$
-/

def negK : V₃ → V₃
| 𝔱 => 𝔣
| 𝔢 => 𝔢
| 𝔣 => 𝔱

def andK : V₃ → V₃ → V₃
| 𝔢, _
| _, 𝔢 => 𝔢
| 𝔱, 𝔱 => 𝔱
| _, _ => 𝔣

def orK : V₃ → V₃ → V₃
| 𝔢, _
| _, 𝔢 => 𝔢
| 𝔣, 𝔣 => 𝔣
| _, _ => 𝔱

prefix:70 "¬ₖ " => negK
infixl:70 " ∧ₖ " => andK
infixl:65 " ∨ₖ " => orK
--myne:end

/-!
These restricted weak Kleene quantifiers address problems with quantification in systems related to weak Kleene logic discussed by Ferguson \cite{DBLP:conf/tableaux/Ferguson21}.
-/

/-
For the restricted

-/


/--
@name Restricted weak Kleene existential
@nl
The restricted weak Kleene existential quantifier evaluates
A
@formula
$$\exists_K X:=\begin{cases}
\mathfrak{t} & \text{if }(\mathfrak{t},\mathfrak{t})\in X,\\
\mathfrak{e} & \text{if }\begin{gathered}
(\mathfrak{t},\mathfrak{t})\notin X\land\\
\forall(v,w)\in X,\ v=\mathfrak{e}\lor w=\mathfrak{e}
\end{gathered},\\
\mathfrak{f} & \text{if }(\mathfrak{t},\mathfrak{t})\notin X\land\exists(v,w)\in X,\ v,w\ne\mathfrak{e}
\end{cases}$$
-/

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

/--
@name Restricted weak Kleene universal
@nl
A restricted weak Kleene universal evaluates $\forall r.C$ at an element $x$ by combining the role and concept values for every candidate $y$. In interpretation $I$, its input is $X=\{(r^I(x,y),C^I(y)):y\in\Delta^I\}\subseteq V_3^2$, with the role value first. It returns $\mathfrak{t}$ when neither $(\mathfrak{t},\mathfrak{f})$ nor $(\mathfrak{t},\mathfrak{e})$ occurs and some pair has no $\mathfrak{e}$ coordinate. It returns $\mathfrak{e}$ when every pair has an $\mathfrak{e}$ coordinate, and $\mathfrak{f}$ when one of those two counterexample pairs occurs and some pair has no $\mathfrak{e}$ coordinate. An empty candidate set yields $\mathfrak{e}$.
@formula
$$\forall_K X:=\begin{cases}
\mathfrak{t} & \text{if }(\mathfrak{t},\mathfrak{f})\notin X\land(\mathfrak{t},\mathfrak{e})\notin X\land\exists(v,w)\in X,\ v,w\ne\mathfrak{e},\\
\mathfrak{e} & \text{if }\forall(v,w)\in X,\ v=\mathfrak{e}\lor w=\mathfrak{e},\\
\mathfrak{f} & \text{if }((\mathfrak{t},\mathfrak{f})\in X\lor(\mathfrak{t},\mathfrak{e})\in X)\land\exists(v,w)\in X,\ v,w\ne\mathfrak{e}
\end{cases}$$
-/

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

/--
@name Restricted quantifier notation
@capture block
@nl
These notations apply the restricted existential and universal operations to the pairs formed from role valuations at $(x,y)$ and concept evaluations at $y$ for the candidates in a quantified formula.
-/
prefix:75 "∃ₖ " => existsK
prefix:75 "∀ₖ " => forallK
--myne:end

-- MARK: AC Operators
/-! \subsubsection{Analytic Containment Operators} -/

/--
@name Analytic containment connectives
@capture block
@nl
An analytic-containment value is a pair $(v^+,v^-)$ in $V_3^2$. Negation swaps its coordinates. Conjunction combines the positive coordinates with weak Kleene conjunction and the negative coordinates with weak Kleene disjunction; disjunction uses the dual pair of operations.
@formula
$$\begin{aligned}
\sim_A(v^+,v^-) &:= (v^-,v^+),\\
(v^+,v^-)\wedge_A(w^+,w^-) &:= (v^+\wedge_K w^+,v^-\vee_K w^-),\\
(v^+,v^-)\vee_A(w^+,w^-) &:= (v^+\vee_K w^+,v^-\wedge_K w^-)
\end{aligned}$$
-/
@[simp]
def negA (v : V₃²) : V₃² := (v⁻, v⁺)
@[simp]
def andA (v w : V₃²) : V₃² := (v⁺ ∧ₖ w⁺, v⁻ ∨ₖ w⁻)
@[simp]
def orA (v w : V₃²) : V₃² := (v⁺ ∨ₖ w⁺, v⁻ ∧ₖ w⁻)

prefix:70 "∼ₐ " => negA
infixl:70 " ∧ₐ " => andA
infixl:65 " ∨ₐ " => orA
--myne:end

/-!
Analytic-containment interpretations use two coordinates to represent bilateral evaluations. Related work analyzes these systems through parallel positive and negative components and characterizes $\mathsf{S}^*$ by excluding pairs with an undefined coordinate on only one side \cite{DBLP:journals/logcom/Ferguson16}.
-/

/--
@name Analytic containment quantifiers
@capture block
@nl
An AC existential or universal restriction returns a pair: its positive coordinate records the result of one WK quantifier, and its negative coordinate records the dual result. To evaluate $\exists R.C$ or $\forall R.C$ at $x$ in interpretation $I$, form $X=\{(R^I(x,y),C^I(y)):y\in\Delta^I\}$, where each entry is a pair of AC values. $P^+(X)$ keeps the positive coordinates of both entries; $P^-(X)$ keeps the role's positive coordinate and the concept's negative coordinate. The existential uses $\exists_K$ on $P^+(X)$ and $\forall_K$ on $P^-(X)$; the universal uses $\forall_K$ and $\exists_K$, respectively. The notations $\exists_A$ and $\forall_A$ name these operations.
@formula
$$\begin{aligned}
P^+(X) &:= \{(r^+,c^+):(r,c)\in X\},\\
P^-(X) &:= \{(r^+,c^-):(r,c)\in X\},\\
\exists_A X &:= (\exists_K P^+(X),\forall_K P^-(X)),\\
\forall_A X &:= (\forall_K P^+(X),\exists_K P^-(X))
\end{aligned}$$
-/

def acPositive (X : Set (V₃² × V₃²)) : Set V₃² :=
  Set.image (λ q => (q.1.1, q.2.1)) X

def acNegative (X : Set (V₃² × V₃²)) : Set V₃² :=
  Set.image (λ q => (q.1.1, q.2.2)) X

noncomputable def existsA (X : Set (V₃² × V₃²)) : V₃² :=
  (∃ₖ (acPositive X), ∀ₖ (acNegative X))

noncomputable def forallA (X : Set (V₃² × V₃²)) : V₃² :=
  (∀ₖ (acPositive X), ∃ₖ (acNegative X))
prefix:75 "∃ₐ " => existsA
prefix:75 "∀ₐ " => forallA
--myne:end

-- MARK: Language
/-! \subsection{$\mathcal{ALCH}$ and $\mathcal{ALCHRU}$ Languages} -/
/-! \subsubsection{Signatures} -/
/--
@name Signature
@nl
A signature $\sigma=(N_C,N_R,N_I)$ consists of the sets of atomic concept names, atomic role names, and individual names, respectively.
@formula
$$\sigma:=(N_C,N_R,N_I)$$
-/
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
@name $\mathcal{ALCHRU}$ role grammar
@capture block
@nl
An $\mathcal{ALCHRU}$ role is built from an atomic role, the universal role $\mathcal{U}$, or the intersection of two roles. The grammar defines exactly which expressions may appear as roles in $\mathcal{ALCHRU}$ concepts and sentences.
@formula
$$\mathcal{R} ::= r \mid \mathcal{U} \mid \mathcal{R}\sqcap\mathcal{R}$$
-/
inductive∇ ALCHRU_Role (σ : Signature) where
| atom : σ.Nr → ∇
| universal : ∇
| inter : ∇ → ∇ → ∇

notation "ℛᵁ" => ALCHRU_Role
notation "[" r "]ᵣ" => ALCHRU_Role.atom r
infixl:70 " ⊓ᵣ " => ALCHRU_Role.inter
notation "𝒰" => ALCHRU_Role.universal
--myne:end

/--
@name Concept grammar for $\mathcal{ALCH}$ and $\mathcal{ALCHRU}$
@capture block
@nl
The nonterminal $\mathcal{C}$ describes $\mathcal{ALCH}$ concepts, whose quantifiers use atomic roles $r$. The nonterminal $\mathcal{C}^U$ describes $\mathcal{ALCHRU}$ concepts, whose quantifiers may use any role $R$ from the role grammar, including universal roles and intersections.
@formula
$$\begin{aligned}
\mathcal{C} &::= \top \mid \bot \mid A \mid \neg\mathcal{C} \mid \mathcal{C}\sqcap\mathcal{C} \mid \mathcal{C}\sqcup\mathcal{C} \mid \exists r.\mathcal{C} \mid \forall r.\mathcal{C},\\
\mathcal{C}^U &::= \top \mid \bot \mid A \mid \neg\mathcal{C}^U \mid \mathcal{C}^U\sqcap\mathcal{C}^U \mid \mathcal{C}^U\sqcup\mathcal{C}^U \mid \exists R.\mathcal{C}^U \mid \forall R.\mathcal{C}^U
\end{aligned}$$
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

/-- $\mathcal{ALCH}$ concepts over atomic roles. -/
-- Classical concepts use atomic roles only.
abbrev ALCH_Concept (σ : Signature) := Concept σ σ.Nr
notation "𝒞" => ALCH_Concept

-- $\mathcal{ALCHRU}$ concepts use the extended role language.
abbrev ALCHRU_Concept (σ : Signature) := Concept σ (ℛᵁ σ)
notation "𝒞ᵁ" => ALCHRU_Concept

variable {σ : Signature}

-- Concept notations
instance : Top (Concept σ R) := ⟨.top⟩
instance : Bot (Concept σ R) := ⟨.bot⟩
instance : Coe σ.Nc (Concept σ R) := ⟨Concept.atom⟩

notation "[" a "]ₐ" => Concept.atom a
infixl:70 " ⊓ₜ " => Concept.conj
infixl:65 " ⊔ₜ " => Concept.disj
notation "¬ₜ " c:75 => Concept.neg c
notation "∃[" r "]" c:75 => Concept.ex r c
notation "∀[" r "]" c:75 => Concept.all r c
--myne:end

/--
@name Sentence grammar for $\mathcal{ALCH}$ and $\mathcal{ALCHRU}$
@capture block
@nl
The grammar for $\Phi$ allows concept and role assertions, concept inclusions and equivalences, and inclusions between atomic roles. The grammar for $\Phi^U$ has the same sentence forms but allows any $\mathcal{ALCHRU}$ role in role assertions and role inclusions; here $r,s$ are atomic roles and $R,S$ are arbitrary $\mathcal{ALCHRU}$ roles.
@formula
$$\begin{aligned}
\Phi &::= i:\mathcal{C} \mid (i,j):r \mid \mathcal{C}\sqsubseteq\mathcal{C} \mid \mathcal{C}\equiv\mathcal{C} \mid r\sqsubseteq s,\\
\Phi^U &::= i:\mathcal{C}^U \mid (i,j):R \mid \mathcal{C}^U\sqsubseteq\mathcal{C}^U \mid \mathcal{C}^U\equiv\mathcal{C}^U \mid R\sqsubseteq S
\end{aligned}$$
-/
inductive∇ Sentence (σ : Signature) (R : Type) where
| isa : σ.Ni → Concept σ R → ∇
| role : σ.Ni → σ.Ni → R → ∇
| sub : Concept σ R → Concept σ R → ∇
| equiv : Concept σ R → Concept σ R → ∇
| rsub : R → R → ∇
deriving Repr

-- $\mathcal{ALCH}$ sentences over atomic roles.
abbrev ALCH_Sentence (σ : Signature) := Sentence σ σ.Nr
notation "Φ" => ALCH_Sentence

-- $\mathcal{ALCHRU}$ sentences over $\mathcal{ALCHRU}$ roles.
abbrev ALCHRU_Sentence (σ : Signature) := Sentence σ (ℛᵁ σ)
notation "Φᵁ" => ALCHRU_Sentence

-- Sentence notations
notation a " :ₐ " c:50 => Sentence.isa a c
notation "(" a ", " b ")" " :ᵣ " r:50 => Sentence.role a b r
infix:50 " ⊑ " => Sentence.sub
infix:50 " ≡ " => Sentence.equiv
infix:50 " ⊑ᵣ " => Sentence.rsub
--myne:end

-- MARK: Interpretations
/-! \subsection{Semantics} -/

/--
@name Interpretations
@capture block
@nl
An interpretation $\mathcal I$ for a signature $\sigma=(N_C,N_R,N_I)$ is a tuple $(\Delta^{\mathcal I},\eta^{\mathcal I},\kappa^{\mathcal I},\rho^{\mathcal I})$. Here $\Delta^{\mathcal I}$ is a nonempty domain; $\eta^{\mathcal I}$ assigns each individual name $a$ to $a^{\mathcal I}\in\Delta^{\mathcal I}$; $\kappa^{\mathcal I}$ assigns each atomic concept name $c$ the $V$-valued predicate $c^{\mathcal I}$; and $\rho^{\mathcal I}$ assigns each atomic role name $r$ the $V$-valued binary relation $r^{\mathcal I}$. Thus $c$ ranges over atomic concept names and $r$ over atomic role names. Taking $V=V_2$, $V=V_3$, or $V=V_3^2$ gives the classical, weak Kleene, or analytic-containment semantics, respectively.
@formula
$$\begin{aligned}
\mathcal I&:=(\Delta^{\mathcal I},\eta^{\mathcal I},\kappa^{\mathcal I},\rho^{\mathcal I}),\qquad \Delta^{\mathcal I}\ne\varnothing,\\
\eta^{\mathcal I}&:N_I\to\Delta^{\mathcal I},\\
\kappa^{\mathcal I}&:N_C\to(\Delta^{\mathcal I}\to V),\\
\rho^{\mathcal I}&:N_R\to(\Delta^{\mathcal I}\times\Delta^{\mathcal I}\to V)
\end{aligned}$$
-/
-- Both parameters are outParams so the current interpretation determines
-- the signature and truth-value type during instance search. This supports
-- inference for the `·ᴵ` notation.
structure Interpretation (σ : outParam Signature) (V : outParam Type) where
  D : Type
  inhabited : Nonempty D
  individualValuation : σ.Ni → D
  atomicConceptValuation : σ.Nc → D → V
  roleValuation : σ.Nr → D → D → V

attribute [class] Interpretation

abbrev CInterpretation (σ : Signature) :=
  Interpretation σ V₂
notation "ℐᶜ" => CInterpretation

abbrev WKInterpretation (σ : Signature) :=
  Interpretation σ V₃
notation "ℐᵂᴷ" => WKInterpretation

abbrev ACInterpretation (σ : Signature) :=
  Interpretation σ V₃²
notation "ℐᴬᶜ" => ACInterpretation

-- Operator for allowing superscript I notation for interpretations.
class Interpret (σ : Signature) (V : Type) (α : Type u) where
  Result : Interpretation σ V → Type
  interpret (I : Interpretation σ V) : α → Result I

-- The ·ᴵ notation for individuals.
instance : Interpret σ V σ.Ni :=
  ⟨(·.D), (·.individualValuation)⟩

-- The ·ᴵ notation for atomic role names.
instance : Interpret σ V σ.Nr :=
  ⟨λ I => I.D → I.D → V, (·.roleValuation)⟩

-- The ·ᴵ notation for atomic concept names.
instance : Interpret σ V σ.Nc :=
  ⟨λ I => I.D → V, (·.atomicConceptValuation)⟩

-- Infer the signature and value type from the interpretation in scope.
abbrev Interpret.current {V : Type}
[I : Interpretation σ V] [h : Interpret σ V α] (a : α) :
h.Result I := h.interpret I a

postfix:max "ᴵ" => Interpret.current

-- Use this notation to select an interpretation when several are in scope.
scoped notation:80 a:81 "^" I:80 => Interpret.interpret I a

-- The domain of the current interpretation.
abbrev Interpret.domain {V : Type}
[I : Interpretation σ V] : Type := I.D

notation "Δᴵ" => Interpret.domain
--myne:end

-- MARK: Classical Semantics
/-! \subsubsection{Classical Semantics} -/

/--
@name Classical role semantics
@capture block
@nl
We lift a classical interpretation to the role language. Let $\mathcal I$ be a classical interpretation. The universal role relates every pair of domain elements, and role intersection holds of a pair exactly when both roles do. Here $r$ is an atomic role name.
@formula
$$\begin{aligned}
\mathcal U^{\mathcal I}(x,y)&:=\top,\\
(R\sqcap S)^{\mathcal I}(x,y)&:=R^{\mathcal I}(x,y)\land S^{\mathcal I}(x,y)
\end{aligned}$$
-/

def∇ evalRoleC [ℐᶜ σ] : ℛᵁ σ → Δᴵ → Δᴵ → V₂
| [r]ᵣ, x, y => rᴵ x y
| 𝒰, _, _ => True
| r ⊓ᵣ s, x, y => ∇ r x y ∧ ∇ s x y

-- Interpretation of ALCHRU role expressions in the classical semantics.
instance : Interpret σ V₂ (ℛᵁ σ) :=
  ⟨λ I => I.D → I.D → V₂, λ_=>evalRoleC⟩
--myne:end

/--
@name Classical concept semantics
@capture block
@nl
We lift a classical interpretation to the concept language. Let $\mathcal I$ be a classical interpretation. The clauses give the truth conditions for the constants, Boolean connectives, and quantifiers of $\mathcal{ALCHRU}$ concepts. Here $c$ is an atomic concept name.
@formula
$$\begin{aligned}
\top^{\mathcal I}(x)&:=\top,\\
\bot^{\mathcal I}(x)&:=\bot,\\
(\neg C)^{\mathcal I}(x)&:=\neg C^{\mathcal I}(x),\\
(C\sqcap D)^{\mathcal I}(x)&:=C^{\mathcal I}(x)\land D^{\mathcal I}(x),\\
(C\sqcup D)^{\mathcal I}(x)&:=C^{\mathcal I}(x)\lor D^{\mathcal I}(x),\\
(\exists R.C)^{\mathcal I}(x)&:=\exists y\,(R^{\mathcal I}(x,y)\land C^{\mathcal I}(y)),\\
(\forall R.C)^{\mathcal I}(x)&:=\forall y\,(R^{\mathcal I}(x,y)\rightarrow C^{\mathcal I}(y))
\end{aligned}$$
-/
def∇ evalConceptC [ℐᶜ σ] : 𝒞ᵁ σ → Δᴵ → V₂
| ⊤, _ => True
| ⊥, _ => False
| [C]ₐ, x => Cᴵ x
| ¬ₜC, x => ¬(∇ C x)
| C ⊓ₜ D, x => (∇ C x) ∧ (∇ D x)
| C ⊔ₜ D, x => ∇ C x ∨ (∇ D x)
| ∃[R] C, x => ∃ y, Rᴵ x y ∧ ∇ C y
| ∀[R] C, x => ∀ y, Rᴵ x y → ∇ C y

-- Interpretation of ALCHRU concepts in the classical semantics.
instance : Interpret σ V₂ (𝒞ᵁ σ) :=
  ⟨(·.D → V₂), λ_=> evalConceptC⟩
--myne:end

/--
@name Classical sentence semantics
@capture block
@nl
We lift a classical interpretation to the sentence language. Let $\mathcal I$ be a classical interpretation. Extend it to sentences by evaluating assertions at their named individuals, inclusions pointwise over the domain, and role inclusions over all pairs. Here $c$ and $r$ are atomic concept and role names, respectively; $C,D$ and $R,S$ range over the concepts and roles allowed in $\mathcal{ALCHRU}$ sentences.
@formula
$$\begin{aligned}
(i:C)^{\mathcal I}&:=C^{\mathcal I}(i^{\mathcal I}),\\
((i,j):R)^{\mathcal I}&:=R^{\mathcal I}(i^{\mathcal I},j^{\mathcal I}),\\
(C\sqsubseteq D)^{\mathcal I}&:=\forall x\in\Delta^{\mathcal I},\ C^{\mathcal I}(x)\rightarrow D^{\mathcal I}(x),\\
(C\equiv D)^{\mathcal I}&:=\forall x\in\Delta^{\mathcal I},\ C^{\mathcal I}(x)\leftrightarrow D^{\mathcal I}(x),\\
(R\sqsubseteq S)^{\mathcal I}&:=\forall x,y\in\Delta^{\mathcal I},\ R^{\mathcal I}(x,y)\rightarrow S^{\mathcal I}(x,y)
\end{aligned}$$
-/

def evalSentenceC [ℐᶜ σ] : Φᵁ σ → V₂
| a :ₐ C => Cᴵ aᴵ
| (a, b) :ᵣ R => Rᴵ aᴵ bᴵ
| C ⊑ D => ∀ x, Cᴵ x → Dᴵ x
| C ≡ D => ∀ x, Cᴵ x ↔ Dᴵ x
| R ⊑ᵣ S => ∀ x y, Rᴵ x y → Sᴵ x y

notation  I "⊨ᶜ " φ => @evalSentenceC _ I φ
--myne:end

/--
@name Classical entailment
@capture block
@nl
For knowledge bases $\Gamma$ and $\Delta$, classical entailment holds when every classical interpretation that satisfies every sentence in $\Gamma$ also satisfies every sentence in $\Delta$.
@formula
$$\Gamma\models_C\Delta := \forall \mathcal I,\ (\mathcal I\models_C\Gamma\rightarrow \mathcal I\models_C\Delta)$$
-/

def entailmentC (Γ Δ : (Φᵁ σ)*) : Prop :=
  ∀ I, (∀ ψ ∈ Γ, I ⊨ᶜ ψ) → (∀ φ ∈ Δ, I ⊨ᶜ φ)

notation Γ " ⊨ᶜ " Δ => entailmentC Γ Δ
--myne:end

-- MARK: WK Semantics
/-! \subsubsection{Weak Kleene Semantics} -/

/--
@name Weak Kleene concept semantics
@capture block
@nl
We lift a weak Kleene interpretation to the concept language. Let $\mathcal I$ be a weak Kleene interpretation. The Boolean constructors use the weak Kleene operations; the quantifiers aggregate pairs formed from role and concept values over the domain. Here $r$ is an atomic role name and $c$ is an atomic concept name.
@formula
$$\begin{aligned}
\top^{\mathcal I}(x)&:=\mathfrak{t},\\
\bot^{\mathcal I}(x)&:=\mathfrak{f},\\
(\neg C)^{\mathcal I}(x)&:=\neg_K C^{\mathcal I}(x),\\
(C\sqcap D)^{\mathcal I}(x)&:=C^{\mathcal I}(x)\wedge_K D^{\mathcal I}(x),\\
(C\sqcup D)^{\mathcal I}(x)&:=C^{\mathcal I}(x)\vee_K D^{\mathcal I}(x),\\
(\exists r.C)^{\mathcal I}(x)&:=\exists_K\{(r^{\mathcal I}(x,y),C^{\mathcal I}(y))\mid y\in\Delta^{\mathcal I}\},\\
(\forall r.C)^{\mathcal I}(x)&:=\forall_K\{(r^{\mathcal I}(x,y),C^{\mathcal I}(y))\mid y\in\Delta^{\mathcal I}\}
\end{aligned}$$
-/

noncomputable def∇ evalConceptK [ℐᵂᴷ σ] : 𝒞 σ → Δᴵ → V₃
| ⊤, _ => 𝔱
| ⊥, _ => 𝔣
| [a]ₐ, x => aᴵ x
| ¬ₜ C, x => ¬ₖ(∇ C x)
| C ⊓ₜ D, x => (∇ C x) ∧ₖ (∇ D x)
| C ⊔ₜ D, x => (∇ C x) ∨ₖ (∇ D x)
| ∃[R] C, x => ∃ₖ {(Rᴵ x y, ∇ C y) | y : Δᴵ}
| ∀[R] C, x => ∀ₖ {(Rᴵ x y, ∇ C y) | y : Δᴵ}

-- Interpretation of ALCH concepts in the weak Kleene semantics.
noncomputable instance : Interpret σ V₃ (𝒞 σ) :=
  ⟨(·.D → V₃), λ_=> evalConceptK⟩
--myne:end

/--
@name Weak Kleene sentence semantics
@capture block
@nl
We lift a weak Kleene interpretation to the sentence language. Let $\mathcal I$ be a weak Kleene interpretation. Assertions inherit the value at the named individuals. Concept inclusions, equivalences, and role inclusions aggregate their pointwise value pairs with the restricted universal quantifier. Here $c$ and $r$ are atomic concept and role names, respectively, and $C,D$ are arbitrary $\mathcal{ALCH}$ concepts.
@formula
$$\begin{aligned}
(i:C)^{\mathcal I}&:=C^{\mathcal I}(i^{\mathcal I}),\\
((i,j):r)^{\mathcal I}&:=r^{\mathcal I}(i^{\mathcal I},j^{\mathcal I}),\\
(C\sqsubseteq D)^{\mathcal I}&:=\forall_K\{(C^{\mathcal I}(x),D^{\mathcal I}(x)):x\in\Delta^{\mathcal I}\},\\
(C\equiv D)^{\mathcal I}&:=
\begin{gathered}
\forall_K\{(C^{\mathcal I}(x),D^{\mathcal I}(x)):x\in\Delta^{\mathcal I}\}\\
\wedge_K\forall_K\{(D^{\mathcal I}(x),C^{\mathcal I}(x)):x\in\Delta^{\mathcal I}\}
\end{gathered},\\
(r\sqsubseteq s)^{\mathcal I}&:=\forall_K\{(r^{\mathcal I}(x,y),s^{\mathcal I}(x,y))\mid x,y\in\Delta^{\mathcal I}\}
\end{aligned}$$
-/

noncomputable def evalSentenceK [ℐᵂᴷ σ] : Φ σ → V₃
| a :ₐ C => Cᴵ aᴵ
| (a, b) :ᵣ r => rᴵ aᴵ bᴵ
| C ⊑ D => ∀ₖ {(Cᴵ x, Dᴵ x) | x : Δᴵ}
| C ≡ D => (∀ₖ {(Cᴵ x, Dᴵ x) | x : Δᴵ}) ∧ₖ
    (∀ₖ {(Dᴵ x, Cᴵ x) | x : Δᴵ})
| R ⊑ᵣ S => ∀ₖ {(Rᴵ p.1 p.2, Sᴵ p.1 p.2) | p : Δᴵ × Δᴵ}

-- Interpretation of ALCH sentences in the weak Kleene semantics.
noncomputable instance : Interpret σ V₃ (Φ σ) :=
  ⟨λ_=>V₃, λ_=> evalSentenceK⟩
--myne:end

/--
@name Weak Kleene satisfaction
@capture block
@nl
A weak Kleene interpretation $\mathcal I$ satisfies a sentence $\varphi$ exactly when its value under $\mathcal I$ is $\mathfrak{t}$:
@formula
$$\mathcal I\models_K\varphi:=\varphi^{\mathcal I}=\mathfrak{t}$$
-/

def satisfiesK [ℐᵂᴷ σ] (φ : Φ σ) : Prop :=
  φᴵ = 𝔱

notation  I "⊨ᵂᴷ " φ => @satisfiesK _ I φ
--myne:end

/--
@name Weak Kleene entailment
@capture block
@nl
For weak Kleene knowledge bases $\Gamma$ and $\Delta$, entailment holds when every interpretation that gives each sentence of $\Gamma$ the value $\mathfrak{t}$ also gives each sentence of $\Delta$ the value $\mathfrak{t}$.
@formula
$$\Gamma\models_K\Delta := \forall \mathcal I,\ (\mathcal I\models_K\Gamma\rightarrow \mathcal I\models_K\Delta)$$
-/

def entailmentK (Γ Δ : (Φ σ)*) : Prop :=
  ∀ (I : ℐᵂᴷ σ), (∀ ψ ∈ Γ, I ⊨ᵂᴷ ψ) → (∀ φ ∈ Δ, I ⊨ᵂᴷ φ)

notation  Γ " ⊨ᵂᴷ " Δ => entailmentK Γ Δ
--myne:end

-- MARK: AC Semantics
/-! \subsubsection{Analytic Containment Semantics} -/

/--
@name Analytic containment concept semantics
@capture block
@nl
We lift an analytic-containment interpretation to the concept language. Let $\mathcal I$ be an analytic-containment interpretation. The connectives act coordinatewise, and the restricted quantifiers aggregate pairs formed from role and concept values over the domain. Here $r$ is an atomic role name and $c$ is an atomic concept name.
@formula
$$\begin{aligned}
\top^{\mathcal I}(x)&:=(\mathfrak{t},\mathfrak{f}),\\
\bot^{\mathcal I}(x)&:=(\mathfrak{f},\mathfrak{t}),\\
(\neg C)^{\mathcal I}(x)&:=\sim_A C^{\mathcal I}(x),\\
(C\sqcap D)^{\mathcal I}(x)&:=C^{\mathcal I}(x)\wedge_A D^{\mathcal I}(x),\\
(C\sqcup D)^{\mathcal I}(x)&:=C^{\mathcal I}(x)\vee_A D^{\mathcal I}(x),\\
(\exists r.C)^{\mathcal I}(x)&:=\exists_A\{(r^{\mathcal I}(x,y),C^{\mathcal I}(y))\mid y\in\Delta^{\mathcal I}\},\\
(\forall r.C)^{\mathcal I}(x)&:=\forall_A\{(r^{\mathcal I}(x,y),C^{\mathcal I}(y))\mid y\in\Delta^{\mathcal I}\}
\end{aligned}$$
-/
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

-- Interpretation of ALCH concepts in analytic-containment semantics.
noncomputable instance : Interpret σ V₃² (𝒞 σ) :=
  ⟨(·.D → V₃²), λ_=>evalConceptA⟩
--myne:end

/--
@name Analytic containment sentence semantics
@capture block
@nl
We lift an analytic-containment interpretation to the sentence language. Let $\mathcal I$ be an analytic-containment interpretation. Assertions inherit the value at the named individuals. Inclusions aggregate the pointwise pair values; equivalence conjoins the two directed inclusions, and role inclusion aggregates over all ordered pairs. Here $c$ and $r$ are atomic concept and role names, respectively, and $C,D$ are arbitrary $\mathcal{ALCH}$ concepts.
@formula
$$\begin{aligned}
(i:C)^{\mathcal I}&:=C^{\mathcal I}(i^{\mathcal I}),\\
((i,j):r)^{\mathcal I}&:=r^{\mathcal I}(i^{\mathcal I},j^{\mathcal I}),\\
(C\sqsubseteq D)^{\mathcal I}&:=\forall_A\{(C^{\mathcal I}(x),D^{\mathcal I}(x)):x\in\Delta^{\mathcal I}\},\\
(C\equiv D)^{\mathcal I}&:=
\begin{gathered}
\forall_A\{(C^{\mathcal I}(x),D^{\mathcal I}(x)):x\in\Delta^{\mathcal I}\}\\
\wedge_A\forall_A\{(D^{\mathcal I}(x),C^{\mathcal I}(x)):x\in\Delta^{\mathcal I}\}
\end{gathered},\\
(r\sqsubseteq s)^{\mathcal I}&:=\forall_A\{(r^{\mathcal I}(x,y),s^{\mathcal I}(x,y))\mid x,y\in\Delta^{\mathcal I}\}
\end{aligned}$$
-/

noncomputable def evalSentenceA [ℐᴬᶜ σ] : Φ σ → V₃²
| a :ₐ c => cᴵ aᴵ
| (a, b) :ᵣ r => rᴵ aᴵ bᴵ
| c ⊑ d => ∀ₐ {(cᴵ x, dᴵ x) | x : Δᴵ}
| c ≡ d => (∀ₐ {(cᴵ x, dᴵ x) | x : Δᴵ}) ∧ₐ
    (∀ₐ {(dᴵ x, cᴵ x) | x : Δᴵ})
| r ⊑ᵣ s => ∀ₐ {(rᴵ p.1 p.2, sᴵ p.1 p.2) | p : Δᴵ × Δᴵ}

-- Interpretation of ALCH sentences in analytic-containment semantics.
noncomputable instance : Interpret σ V₃² (Φ σ) :=
  ⟨λ_=>V₃²,λ_=>evalSentenceA⟩
--myne:end

/--
@name Analytic containment satisfaction
@capture block
@nl
An analytic-containment interpretation $\mathcal I$ satisfies $\varphi$ exactly when the positive coordinate of $\varphi^{\mathcal I}$ is $\mathfrak{t}$:
@formula
$$\mathcal I\models_A\varphi:=(\varphi^{\mathcal I})^+=\mathfrak{t}$$
-/

def satisfiesA [ℐᴬᶜ σ] (φ : Φ σ) : Prop :=
  (φᴵ)⁺ = 𝔱

notation  I "⊨ᴬᶜ " φ => @satisfiesA _ I φ
--myne:end

/--
@name Analytic containment entailment
@capture block
@nl
For analytic-containment knowledge bases $\Gamma$ and $\Delta$, entailment holds when every interpretation satisfying all premises also satisfies all conclusions, using the positive-coordinate satisfaction condition above.
@formula
$$\Gamma\models_A\Delta := \forall \mathcal I,\ (\mathcal I\models_A\Gamma\rightarrow \mathcal I\models_A\Delta)$$
-/

def entailmentA (Γ Δ : (Φ σ)*) : Prop :=
  ∀ (I : ℐᴬᶜ σ), (∀ ψ ∈ Γ, I ⊨ᴬᶜ ψ) → (∀ φ ∈ Δ, I ⊨ᴬᶜ φ)

notation  Γ " ⊨ᴬᶜ " Δ => entailmentA Γ Δ
--myne:end

-- MARK: AC to WK
/-! \section{Translations} -/
/-! \subsection{AC to Weak Kleene} -/
/-!
The translation $\pi$ preserves and reflects entailment between analytic
containment and weak Kleene semantics. It uses positive and negative copies
of each atomic concept, indexed by $+$ and $-$, while retaining the roles.
The side-indexed concept translation handles negation by exchanging sides.
-/

/--
@name Weak Kleene signature
@capture block
@nl
The weak Kleene signature replaces each atomic concept name by its positive and negative copies while preserving role and individual names. These instances transport interpretations of atomic concepts to the corresponding names in the translated signature.
@formula
$$N_C^{WK}:=N_C\times\{+,-\},\quad N_R^{WK}:=N_R,\quad N_I^{WK}:=N_I$$
-/
abbrev wkSignature (σ : Signature) : Signature where
  Nc := σ.Nc × Side
  Nr := σ.Nr
  Ni := σ.Ni

instance toWKSignature : ToWK Signature Signature where
  wkIze := wkSignature

instance : Interpret σᵂᴷ V (σ.Nc × Side) :=
  ⟨λ I => I.D → V, (·.atomicConceptValuation)⟩
--myne:end

/--
@name Side-indexed AC translation
@capture block
@nl
For a concept $C$ and side $s\in\{+,-\}$, $\pi^s(C)$ is a weak Kleene concept whose value matches coordinate $s$ of the AC value of $C$. The recursion swaps sides under negation, uses the dual connective for the negative side, and exchanges existential with universal restrictions there.
@formula
$$\begin{array}{c|c}
\text{Positive} & \text{Negative}\\\hline
\pi^+(\top):=\top & \pi^-(\top):=\bot\\
\pi^+(\bot):=\bot & \pi^-(\bot):=\top\\
\pi^+(A):=A^+ & \pi^-(A):=A^-\\
\pi^+(\neg C):=\pi^-(C) & \pi^-(\neg C):=\pi^+(C)\\
\pi^+(C\sqcap D):=\pi^+(C)\sqcap\pi^+(D) & \pi^-(C\sqcap D):=\pi^-(C)\sqcup\pi^-(D)\\
\pi^+(C\sqcup D):=\pi^+(C)\sqcup\pi^+(D) & \pi^-(C\sqcup D):=\pi^-(C)\sqcap\pi^-(D)\\
\pi^+(\exists r.C):=\exists r.\pi^+(C) & \pi^-(\exists r.C):=\forall r.\pi^-(C)\\
\pi^+(\forall r.C):=\forall r.\pi^+(C) & \pi^-(\forall r.C):=\exists r.\pi^-(C)
\end{array}$$
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

instance : PiTranslation (𝒞 σ) (𝒞 σᵂᴷ) where
  piIze C := piConcept C +ₚ
--myne:end

/--
@name AC sentence translation
@capture block
@nl
The sentence translation replaces each concept by its positive weak Kleene copy. It leaves role assertions and role inclusions unchanged and translates concept inclusions and equivalences using those positive copies.
@formula
$$\begin{aligned}
\pi(i:C)&:=i:\pi^+(C),\\
\pi((i,j):r)&:=(i,j):r,\\
\pi(C\sqsubseteq D)&:=\pi^+(C)\sqsubseteq\pi^+(D),\\
\pi(C\equiv D)&:=\pi^+(C)\equiv\pi^+(D),\\
\pi(r\sqsubseteq s)&:=r\sqsubseteq s
\end{aligned}$$
-/

def piSentence : Φ σ → Φ σᵂᴷ
| a :ₐ c => a :ₐ π c
| (a, b) :ᵣ r => (a, b) :ᵣ r
| c ⊑ d => π c ⊑ π d
| c ≡ d => π c ≡ π d
| r ⊑ᵣ s => r ⊑ᵣ s

instance : PiTranslation (Φ σ) (Φ σᵂᴷ) where
  piIze := piSentence
--myne:end

/--
@name AC knowledge base translation
@capture block
@nl
The translation applies $\pi$ to every sentence in a knowledge base and collects the results in the translated signature.
@formula
$$\pi(\Gamma):=\{\pi(\varphi):\varphi\in\Gamma\}$$
-/
abbrev piSentenceSet : (Φ σ)* → (Φ σᵂᴷ)* :=
  Set.image piSentence

instance : PiTranslation (Φ σ)* (Φ σᵂᴷ)* where
  piIze := piSentenceSet
--myne:end

-- MARK: WK to C
/-! \subsection{Weak Kleene to Classical} -/
/-!
Similar idea to the original tau / mu translation
with some fixes. We modify the signature to include a bit
indicator for each atomic concept and role. At each element (for a concept)
or ordered pair of elements (for a role), the two copies record whether its
valuation is $\mathfrak{t}$ and whether that valuation differs from $\mathfrak{e}$.

The core distinction is that we can use the universal role
to express $\exists_1 C$ and $r\sqcap^+s$,
and then use this information to encode the wk
semantics through the translation.

We also add bridge axioms to connect the truth and
meaningfulness components of concepts and roles.
-/

/--
@name Truth and meaningfulness signature copies
@capture block
@nl
The target signature gives every atomic concept and role a truth copy and a meaningfulness copy, while preserving individual names. The truth and meaningfulness markers identify those two copies.
@formula
$$N_C^T:=N_C\times\{\mathsf T,\mathsf M\},\quad N_R^T:=N_R\times\{\mathsf T,\mathsf M\},\quad N_I^T:=N_I$$
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
--myne:end

/--
@name Meaningfulness translation
@capture block
@nl
For each domain element, $\mu(C)$ holds exactly when the weak Kleene value of $C$ differs from $\mathfrak{e}$. Its recursive clauses build this classical concept from the meaningfulness copies of atomic concepts and roles.
@formula
$$\begin{aligned}
\mu(\top)&:=\top,\\
\mu(\bot)&:=\top,\\
\mu(A)&:=A^{\mathsf M},\\
\mu(\neg C)&:=\mu(C),\\
\mu(C\sqcap D)&:=\mu(C)\sqcap\mu(D),\\
\mu(C\sqcup D)&:=\mu(C)\sqcap\mu(D),\\
\mu(\exists r.C)&:=\exists r^{\mathsf M}.\mu(C),\\
\mu(\forall r.C)&:=\exists r^{\mathsf M}.\mu(C)
\end{aligned}$$
-/

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
--myne:end

/--
@name Truth translation
@capture block
@nl
For each domain element, $\tau(C)$ holds exactly when the weak Kleene value of $C$ is $\mathfrak{t}$. Its clauses use the truth and meaningfulness copies together where the weak Kleene connective requires them.
@formula
$$\begin{aligned}
\tau(\top)&:=\top,\\
\tau(\bot)&:=\bot,\\
\tau(A)&:=A^{\mathsf T},\\
\tau(\neg C)&:=\mu(C)\sqcap\neg\tau(C),\\
\tau(C\sqcap D)&:=\tau(C)\sqcap\tau(D),\\
\tau(C\sqcup D)&:=(\tau(C)\sqcup\tau(D))\sqcap(\mu(C)\sqcap\mu(D)),\\
\tau(\exists r.C)&:=\exists r^{\mathsf T}.\tau(C),\\
\tau(\forall r.C)&:=(\forall r^{\mathsf T}.\tau(C))\sqcap\exists r^{\mathsf M}.\mu(C)
\end{aligned}$$
-/

def∇ tauConcept : 𝒞 σ → 𝒞ᵁ σᵀ
| ⊤ => ⊤
| ⊥ => ⊥
| [a]ₐ => [(a, 𝕋)]ₐ
| ¬ₜc => μ c ⊓ₜ ¬ₜ(∇ c)
| c ⊓ₜ d => (∇ c) ⊓ₜ (∇ d)
| c ⊔ₜ d => ((∇ c) ⊔ₜ (∇ d)) ⊓ₜ (μ c ⊓ₜ μ d)
| ∃[r] c => ∃[[(r, 𝕋)]ᵣ] (∇ c)
| ∀[r] c => (∀[[(r, 𝕋)]ᵣ] (∇ c)) ⊓ₜ ∃[[(r, 𝕄)]ᵣ] (μ c)

/-- The $\tau$ notation for concepts. -/
instance : TauTranslation (𝒞 σ) (𝒞ᵁ σᵀ) := ⟨tauConcept⟩
--myne:end

/--
@name Concept nonemptiness sentence
@capture block
@nl
For a classical concept $C$, the sentence $\exists_1 C$ holds exactly when some domain element belongs to $C$.
@formula
$$\exists_1 C:=\top\sqsubseteq\exists\mathcal U.C$$
-/

def nonempty (c : 𝒞ᵁ σ) : Φᵁ σ :=
  ⊤ ⊑ ∃[𝒰] c

prefix:max "∃₁" => nonempty
--myne:end

/--
@name Nonemptiness has a witness
@nl
For any classical concept $C$, $\exists_1 C$ holds exactly when some domain element belongs to $C$; that element is its witness.
@formula
$$I\models_C\exists_1 C\leftrightarrow\exists x\in\Delta^I,\ C^I(x)$$
@proof
Expand the universal role and use the interpretation domain being inhabited.
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
@name Role overlap sentence
@capture block
@nl
For atomic roles $r$ and $s$, $r\sqcap^+s$ holds exactly when there are domain elements $x,y$ related by both $r$ and $s$. It is the nonemptiness test for their intersection.
@formula
$$r\sqcap^+s:=\exists_1(\exists(r\sqcap s).\top)$$
-/

def overlap (r s : σ.Nr) : Φᵁ σ :=
  ∃₁(∃[([r]ᵣ ⊓ᵣ [s]ᵣ)] ⊤)

infixl:70 " ⨅⁺ " => overlap
--myne:end

/--
@name Role overlap has a common edge
@nl
For atomic roles $r$ and $s$, $r\sqcap^+s$ holds exactly when there are elements $x,y$ with both $r(x,y)$ and $s(x,y)$. Thus $r\sqcap^+s$ detects a shared edge, not merely separate nonempty roles.
@formula
$$I\models_C(r\sqcap^+s)\leftrightarrow\exists x,y\in\Delta^I,\ r^I(x,y)\land s^I(x,y)$$
@proof
Expand overlap and apply the nonemptiness characterization.
-/

@[simp] theorem overlap_iff [I : ℐᶜ σ] (r s : σ.Nr) :
(I ⊨ᶜ (r ⨅⁺ s)) ↔ ∃ x y, rᴵ x y ∧ sᴵ x y := by
  simp only [Interpret.current, Interpret.interpret,
  overlap, nonempty_iff, evalConceptC, evalRoleC, and_true]



/--
@name Weak Kleene sentence translation
@capture block
@nl
The map $\tau$ sends each $\mathcal{ALCH}$ sentence to a set of classical $\mathcal{ALCHRU}$ sentences over the truth and meaningfulness copies of its atomic symbols. For an inclusion $C\sqsubseteq D$, it requires both $\tau(C)\sqsubseteq\tau(D)$ and a nonempty intersection of their meaningfulness concepts, expressed by $\exists_1(\mu(C)\sqcap\mu(D))$. Equivalence applies this condition in both directions. A role inclusion requires truth-copy inclusion and uses the overlap notation $r^{\mathsf M}\sqcap^+s^{\mathsf M}$ for its meaningfulness copies.
@formula
$$\begin{aligned}
\tau(i:C)&:=\{i:\tau(C)\},\\
\tau((i,j):r)&:=\{(i,j):r^{\mathsf T}\},\\
\tau(C\sqsubseteq D)&:=\{\tau(C)\sqsubseteq\tau(D),\ \exists_1(\mu(C)\sqcap\mu(D))\},\\
\tau(C\equiv D)&:=\{\tau(C)\sqsubseteq\tau(D),\ \exists_1(\mu(C)\sqcap\mu(D))\}\\
&\qquad\cup\{\tau(D)\sqsubseteq\tau(C),\ \exists_1(\mu(D)\sqcap\mu(C))\},\\
\tau(r\sqsubseteq s)&:=\{r^{\mathsf T}\sqsubseteq s^{\mathsf T},\ r^{\mathsf M}\sqcap^+s^{\mathsf M}\}
\end{aligned}$$
-/

def tauSubsumption (c d : 𝒞 σ) : (Φᵁ σᵀ)* :=
  {τ c ⊑ τ d} ∪ {∃₁(μ c ⊓ₜ μ d)}

def tauSentence : Φ σ → (Φᵁ σᵀ)*
| a :ₐ c => ({show Φᵁ σᵀ from a :ₐ τ c} : (Φᵁ σᵀ)*)
| (a, b) :ᵣ r => ({show Φᵁ σᵀ from (a, b) :ᵣ [(r, 𝕋)]ᵣ} : (Φᵁ σᵀ)*)
| c ⊑ d => tauSubsumption c d
| c ≡ d => tauSubsumption c d ∪ tauSubsumption d c
| r ⊑ᵣ s => {[(r, 𝕋)]ᵣ ⊑ᵣ [(s, 𝕋)]ᵣ} ∪ {(r, 𝕄) ⨅⁺ (s, 𝕄)}

instance : TauTranslation (Φ σ) (Φᵁ σᵀ)* :=
  ⟨tauSentence⟩
--myne:end

/--
@name Weak Kleene knowledge base translation
@capture block
@nl
The translation of a knowledge base is the union of the sentence translations of its members.
@formula
$$\tau(\Gamma):=\bigcup_{\varphi\in\Gamma}\tau(\varphi)$$
-/
def tauSentenceSet (Γ : (Φ σ)*) : (Φᵁ σᵀ)* :=
  Set.bind Γ tauSentence

instance : TauTranslation (Φ σ)* (Φᵁ σᵀ)* :=
  ⟨tauSentenceSet⟩
--myne:end

-- MARK: WK To C Bridges
/-!
It is not enough to simply translate concepts and roles;
we also need to ensure that the truth and meaningfulness
components are properly related through bridge axioms.
-/

/--
@name Atomic concept bridge
@capture block
@nl
At each element, membership in the truth copy of an atomic concept implies membership in its meaningfulness copy. Equivalently, if the WK valuation of that atomic concept is $\mathfrak{t}$ at the element, it is not $\mathfrak{e}$ there.
@formula
$$\mathcal{D}(a):=[(a,\mathsf T)]\sqsubseteq[(a,\mathsf M)]$$
-/

def atomicConceptBridge (a : σ.Nc) : Φᵁ σᵀ :=
  [(a, 𝕋)]ₐ ⊑ [(a, 𝕄)]ₐ

instance : BridgeTranslation (σ.Nc) (Φᵁ σᵀ) :=
⟨atomicConceptBridge⟩
--myne:end

/--
@name Atomic role bridge
@capture block
@nl
At each ordered pair of elements, membership in the truth copy of an atomic role implies membership in its meaningfulness copy. Equivalently, if the WK valuation of that atomic role is $\mathfrak{t}$ at the pair, it is not $\mathfrak{e}$ there.
@formula
$$\mathcal{D}(r):=[(r,\mathsf T)]\sqsubseteq[(r,\mathsf M)]$$
-/

def atomicRoleBridge (r : σ.Nr) : Φᵁ σᵀ :=
  [(r, 𝕋)]ᵣ ⊑ᵣ [(r, 𝕄)]ᵣ

instance : BridgeTranslation (σ.Nr) (Φᵁ σᵀ) :=
 ⟨atomicRoleBridge⟩
--myne:end

/--
@name Concept bridge axioms
@capture block
@nl
The bridge set $\mathcal D(C)$ contains the atomic concept and role bridge sentences for every name occurring in $C$. For a compound concept it is the union of the bridge sets for its parts, together with the role bridge for a quantified restriction.
@formula
$$\begin{aligned}
\mathcal D(\top)&:=\varnothing,\\
\mathcal D(\bot)&:=\varnothing,\\
\mathcal D(A)&:=\{A^{\mathsf T}\sqsubseteq A^{\mathsf M}\},\\
\mathcal D(\neg C)&:=\mathcal D(C),\\
\mathcal D(C\sqcap D)&:=\mathcal D(C)\cup\mathcal D(D),\\
\mathcal D(C\sqcup D)&:=\mathcal D(C)\cup\mathcal D(D),\\
\mathcal D(\exists r.C)&:=\{r^{\mathsf T}\sqsubseteq r^{\mathsf M}\}\cup\mathcal D(C),\\
\mathcal D(\forall r.C)&:=\{r^{\mathsf T}\sqsubseteq r^{\mathsf M}\}\cup\mathcal D(C)
\end{aligned}$$
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
--myne:end

/--
@name Sentence bridge axioms
@capture block
@nl
The bridge set of a sentence contains the bridge axioms for every atomic concept and role name that occurs in it.
@formula
$$\begin{aligned}
\mathcal D(i:C)&:=\mathcal D(C),\\
\mathcal D((i,j):r)&:=\{\mathcal D(r)\},\\
\mathcal D(C\sqsubseteq D)&:=\mathcal D(C)\cup\mathcal D(D),\\
\mathcal D(C\equiv D)&:=\mathcal D(C)\cup\mathcal D(D),\\
\mathcal D(r\sqsubseteq s)&:=\{\mathcal D(r)\}\cup\{\mathcal D(s)\}
\end{aligned}$$
-/
def sentenceBridges : Φ σ → (Φᵁ σᵀ)*
| _ :ₐ c => 𝒟 c
| (_, _) :ᵣ r => {𝒟 r}
| c ⊑ d => 𝒟 c ∪ 𝒟 d
| c ≡ d => 𝒟 c ∪ 𝒟 d
| r ⊑ᵣ s => {𝒟 r} ∪ {𝒟 s}

instance : BridgeTranslation (Φ σ) (Φᵁ σᵀ)* :=
 ⟨sentenceBridges⟩
--myne:end

/--
@name Knowledge base bridge axioms
@capture block
@nl
The bridge set of a knowledge base is the union of the bridge sets of its sentences.
@formula
$$\mathcal{D}(\Gamma):=\bigcup_{\varphi\in\Gamma}\mathcal{D}(\varphi)$$
-/
def sentenceSetBridges (Γ : (Φ σ)*) : (Φᵁ σᵀ)* :=
  Set.bind Γ sentenceBridges

instance : BridgeTranslation ((Φ σ)*) (Φᵁ σᵀ)* :=
 ⟨sentenceSetBridges⟩
--myne:end

-- MARK: Theorems
/-! \section{Correctness Theorems} -/
/-!
The main result composes the AC-to-WK translation $\pi$ with the WK-to-classical
translation $\tau$. The bridge set $\mathcal D$ relates truth and
meaningfulness copies. We establish equivalence at each translation stage,
then compose those equivalences for knowledge-base entailment.
-/

-- MARK: WK Lemmas
--myne:appendix_start Weak Kleene Lemmas

/--
@name WK negation returns $\mathfrak{t}$
@nl
Negation returns $\mathfrak{t}$ precisely when its input is $\mathfrak{f}$.
@formula
$$\neg_K v=\mathfrak{t}\leftrightarrow v\ne\mathfrak{e}\land v\ne\mathfrak{t}$$
@proof
Check the three possible weak Kleene values.
-/

@[simp]
theorem negK_t (v : V₃) : ¬ₖv = 𝔱 ↔ v ≠ 𝔢 ∧ v ≠ 𝔱 := by
  cases v <;> decide

/--
@name WK negation preserves meaningfulness
@nl
Negation changes the sign of a value but does not change whether that value differs from $\mathfrak{e}$.
@formula
$$\neg_K v\ne\mathfrak{e}\leftrightarrow v\ne\mathfrak{e}$$
@proof
Check each of the three possible input values.
-/

@[simp]
theorem negK_m (v : V₃) : ¬ₖv ≠ 𝔢 ↔ v ≠ 𝔢 := by
  cases v <;> decide

/--
@name WK conjunction returns $\mathfrak{t}$
@nl
Conjunction returns $\mathfrak{t}$ exactly when both inputs are $\mathfrak{t}$.
@formula
$$v\wedge_K w=\mathfrak{t}\leftrightarrow v=\mathfrak{t}\land w=\mathfrak{t}$$
@proof
Check the finite pairs of weak Kleene values.
-/

@[simp]
theorem andK_t (v w : V₃) : v ∧ₖ w = 𝔱 ↔ v = 𝔱 ∧ w = 𝔱 := by
  cases v <;> cases w <;> decide

/--
@name WK conjunction is meaningful
@nl
The conjunction differs from $\mathfrak{e}$ exactly when both input values differ from $\mathfrak{e}$.
@formula
$$v\wedge_K w\ne\mathfrak{e}\leftrightarrow v\ne\mathfrak{e}\land w\ne\mathfrak{e}$$
@proof
Check the finite pairs of weak Kleene values.
-/

@[simp]
theorem andK_m (v w : V₃) : v ∧ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

/--
@name WK disjunction returns $\mathfrak{t}$
@nl
Disjunction returns $\mathfrak{t}$ when at least one input is $\mathfrak{t}$ and neither is $\mathfrak{e}$.
@formula
$$v\vee_K w=\mathfrak{t}\leftrightarrow(v=\mathfrak{t}\lor w=\mathfrak{t})\land v,w\ne\mathfrak{e}$$
@proof
Check the finite pairs of weak Kleene values.
-/

@[simp]
theorem orK_t (v w : V₃) :
v ∨ₖ w = 𝔱 ↔ (v = 𝔱 ∨ w = 𝔱) ∧ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

/--
@name WK disjunction is meaningful
@nl
The disjunction differs from $\mathfrak{e}$ exactly when both input values differ from $\mathfrak{e}$.
@formula
$$v\vee_K w\ne\mathfrak{e}\leftrightarrow v\ne\mathfrak{e}\land w\ne\mathfrak{e}$$
@proof
Check the finite pairs of weak Kleene values.
-/
@[simp]
theorem orK_m (v w : V₃) : v ∨ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

/--
@name Restricted existential returns $\mathfrak{t}$
@nl
The restricted existential returns $\mathfrak{t}$ exactly when a pair of $\mathfrak{t}$ values occurs.
@formula
$$\exists_K X=\mathfrak{t}\leftrightarrow(\mathfrak{t},\mathfrak{t})\in X$$
@proof
Unfold the quantifier and eliminate the remaining conditional branches.
-/

@[simp] theorem existsK_t (X : Set V₃²) :
∃ₖ X = 𝔱 ↔ (𝔱, 𝔱) ∈ X := by
  classical
  unfold existsK
  repeat (split <;> (try rfl) <;> (try grind only))

/--
@name Restricted existential meaningfulness
@nl
The restricted existential differs from $\mathfrak{e}$ exactly when at least one candidate pair has both coordinates different from $\mathfrak{e}$. For a set $X$ of role-concept value pairs, this means $X$ contains such a pair.
@formula
$$\exists_K X\ne\mathfrak{e}\leftrightarrow\exists(v,w)\in X:\ v,w\ne\mathfrak{e}$$
@proof
Unfold the quantifier and analyze the $\mathfrak{t}$, $\mathfrak{e}$, and $\mathfrak{f}$ cases.
-/

@[simp] theorem existsK_m (X : Set V₃²) :
∃ₖ X ≠ 𝔢 ↔ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold existsK
  repeat (split <;> (try rfl) <;> (try grind only))

/--
@name Restricted universal returns $\mathfrak{t}$
@nl
For $X\subseteq V_3^2$, the restricted universal returns $\mathfrak{t}$ exactly when neither $(\mathfrak{t},\mathfrak{f})$ nor $(\mathfrak{t},\mathfrak{e})$ occurs in $X$, and $X$ contains at least one pair whose coordinates both differ from $\mathfrak{e}$.
@formula
$$\forall_K X=\mathfrak{t}\leftrightarrow(\mathfrak{t},\mathfrak{f})\notin X\land(\mathfrak{t},\mathfrak{e})\notin X\land\exists(v,w)\in X:\ v,w\ne\mathfrak{e}$$
@proof
Unfold the quantifier and discharge the other conditional branches.
-/

private theorem forallK_true (X : Set V₃²) :
∀ₖ X = 𝔱 ↔
(𝔱, 𝔣) ∉ X ∧ (𝔱, 𝔢) ∉ X ∧ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold forallK
  repeat (split <;> (try rfl) <;> (try grind only))

/--
@name Restricted universal meaningfulness
@nl
The restricted universal differs from $\mathfrak{e}$ exactly when at least one candidate pair has both coordinates different from $\mathfrak{e}$. For a set $X$ of role-concept value pairs, this means $X$ contains such a pair.
@formula
$$\forall_K X\ne\mathfrak{e}\leftrightarrow\exists(v,w)\in X:\ v,w\ne\mathfrak{e}$$
@proof
Unfold the quantifier and analyze its three conditional outcomes.
-/

@[simp] theorem forallK_m (X : Set V₃²) :
∀ₖ X ≠ 𝔢 ↔ ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  classical
  unfold forallK
  repeat (split <;> (try rfl) <;> (try grind only))

/--
@name Universal counterexample condition
@nl
For a set $X$ of role-concept value pairs, excluding $(\mathfrak{t},\mathfrak{f})$ and $(\mathfrak{t},\mathfrak{e})$ is equivalent to requiring a $\mathfrak{t}$ concept coordinate whenever the role coordinate is $\mathfrak{t}$.
@formula
$$(\mathfrak{t},\mathfrak{f}),(\mathfrak{t},\mathfrak{e})\notin X\leftrightarrow\forall(r,c)\in X,\ r=\mathfrak{t}\rightarrow c=\mathfrak{t}$$
@proof
Forwards, split on the concept value; backwards, apply the stated implication to either forbidden pair.
-/
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
@name Restricted universal returns $\mathfrak{t}$
@nl
The universal returns $\mathfrak{t}$ when every $\mathfrak{t}$ role coordinate has a $\mathfrak{t}$ concept coordinate and a pair without an $\mathfrak{e}$ coordinate occurs.
@formula
$$\forall_K X=\mathfrak{t}\leftrightarrow\bigl(\forall(r,c)\in X,\ r=\mathfrak{t}\rightarrow c=\mathfrak{t}\bigr)\land\exists(r,c)\in X:\ r,c\ne\mathfrak{e}$$
@proof
Combine the set-based truth clause with the counterexample characterization.
-/

@[simp]
theorem forallK_t (X : Set V₃²) :
∀ₖ X = 𝔱 ↔
(∀ p ∈ X, p.1 = 𝔱 → p.2 = 𝔱) ∧
∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 := by
  rw [forallK_true, ←and_assoc, forallK_t_aux]

/--
@name Universal membership over bound sets
@nl
For a source set $S$ and a set-valued map $F$, the bound set $\bigcup_{x\in S}F(x)$ satisfies a property everywhere exactly when each $F(x)$ satisfies it everywhere for every $x\in S$.
@formula
$$\forall y\in\operatorname{bind}(X,f),\ P(y)\iff\forall x\in X,\forall y\in f(x),\ P(y)$$
@proof
Unpack and repack the witness in bound-set membership.
-/
private theorem allMemBind {α β : Type} (P : β → Prop) (f : α → β*)
(xs : α*) :
(∀ y ∈ Set.bind xs f, P y) ↔ ∀ x ∈ xs, ∀ y ∈ f x, P y := by
  constructor
  · intro h x hx y hy
    exact h y (Set.mem_bind.mpr ⟨x, hx, hy⟩)
  · intro h y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_bind.mp hy
    exact h x hx y hy

--myne:appendix_end

-- MARK: Other Lemmas

-- MARK: AC to WK Theorems
/-! \subsection{AC to Weak Kleene Theorems} -/
/-!
The projection $\circ I$ of an AC interpretation records both concept
coordinates as separate WK atoms. Structural induction on concepts shows
that this projection preserves each selected coordinate. The sentence and
entailment results then follow from that correspondence and the reverse
lifting $\bullet I$.
-/

/--
@name AC interpretation projection
@nl
Given an analytic-containment interpretation $\mathcal I$, the projection to the weak Kleene signature keeps the same domain and individual assignment. It interprets each side-indexed concept name $(c,s)$ by coordinate $s$ of $c^\mathcal I$, and each atomic role $r$ by the positive coordinate of $r^\mathcal I$. Here $c\in N_C$, $r\in N_R$, and $s\in\{+,-\}$.
@formula
$$\begin{aligned}
\Delta^{\circ\mathcal I}&:=\Delta^\mathcal I,\\
a^{\circ\mathcal I}&:=a^\mathcal I,\\
(c,s)^{\circ\mathcal I}(x)&:=\bigl(c^\mathcal I(x)\bigr)^s,\\
r^{\circ\mathcal I}(x,y)&:=\bigl(r^\mathcal I(x,y)\bigr)^+.
\end{aligned}$$
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
@name Lift WK interpretations to AC
@nl
Given a weak Kleene interpretation $\mathcal I$ over the side-indexed concept signature, the lift to analytic containment keeps the same domain and individual assignment. It combines the two copies of each atomic concept $c$ into the positive and negative coordinates of $c$, and places each atomic role's WK value in its positive coordinate with $\mathfrak{e}$ in its negative coordinate. Here $c\in N_C$ ranges over atomic concepts and $r\in N_R$ over atomic roles.
@formula
$$\begin{aligned}
\Delta^{\bullet\mathcal I}&:=\Delta^\mathcal I,\\
a^{\bullet\mathcal I}&:=a^\mathcal I,\\
c^{\bullet\mathcal I}(x)&:=\bigl((c,+)^\mathcal I(x),(c,-)^\mathcal I(x)\bigr),\\
r^{\bullet\mathcal I}(x,y)&:=\bigl(r^\mathcal I(x,y),\mathfrak{e}\bigr).
\end{aligned}$$
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
@name Projection after lifting
@nl
If a WK interpretation is first lifted to AC and then projected back, every atomic concept and role valuation, along with the domain and individual assignment, is recovered unchanged.
@formula
$$\circ(\bullet I)=I$$
@proof
Compare interpretation fields; split on the side of each atomic concept copy.
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
@name AC concept coordinates are preserved
@nl
For every concept $C$, domain element $x$, and side $s$, evaluating $\pi^s(C)$ in the projected WK interpretation gives coordinate $s$ of the original AC value of $C$ at $x$.
@formula
$$(\pi^s(C))^{\circ\mathcal I}(x)=(C^\mathcal I(x))^s$$
@proof
Proceed by structural induction on the concept, splitting by side and simplifying each connective and quantifier case.
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

/--
@name Positive AC concept support
@nl
For every $\mathcal{ALCH}$ concept and domain element, its positive WK translation evaluated in the projection equals the first coordinate of its AC value.
@formula
$$(\pi(C))^{\circ I}(x)=(C^I(x))^+$$
@proof
Specialize the side-independent coordinate theorem to the positive side.
-/

theorem acConceptSupport (I : ℐᴬᶜ σ) (c : 𝒞 σ) (x : Δᴵ) :
((π c)^(○I)) x = ((c^I) x)⁺ :=
  acConceptCoordinates I c x +ₚ

/--
@name Positive AC sentence support
@nl
For every $\mathcal{ALCH}$ sentence, the translated WK sentence has the same value as the positive coordinate of the AC sentence value in the projected interpretation.
@formula
$$(\pi(\varphi))^{\circ I}=(\varphi^I)^+$$
@proof
Use the concept-coordinate theorem and split on the sentence constructors.
-/
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

/--
@name AC and WK satisfaction correspond
@nl
For each AC interpretation and $\mathcal{ALCH}$ sentence, satisfaction on the AC side is equivalent to satisfaction of its positive translation in the projected WK interpretation.
@formula
$$I\models^{\mathsf{AC}}\varphi\iff\circ I\models^{\mathsf{WK}}\pi(\varphi)$$
@proof
Rewrite satisfaction using the sentence-support equality.
-/
theorem acSentenceSupport_iff (I : ℐᴬᶜ σ) (φ : Φ σ) :
(I ⊨ᴬᶜ φ) ↔ (○I ⊨ᵂᴷ π φ) := by
  change (φ^I)⁺ = 𝔱 ↔ (π φ)^(○I) = 𝔱
  rw [acSentenceSupport]

/--
@name AC entailment implies translated WK entailment
@nl
If an AC knowledge base entails another, their positive WK translations are entailed in every projected WK interpretation; the theorem establishes this forward preservation for arbitrary premise and conclusion sets.
@formula
$$\Gamma\models^{\mathsf{AC}}\Delta\implies\pi(\Gamma)\models^{\mathsf{WK}}\pi(\Delta)$$
@proof
Lift a WK counterinterpretation to AC, use sentence satisfaction correspondence, and project it back.
-/
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

/--
@name Translated WK entailment implies AC entailment
@nl
If the positive WK translations entail one another, lifting a WK counterexample would give an AC counterexample. The theorem rules this out and recovers entailment between the original AC knowledge bases.
@formula
$$\pi(\Gamma)\models^{\mathsf{WK}}\pi(\Delta)\implies\Gamma\models^{\mathsf{AC}}\Delta$$
@proof
Project an arbitrary AC interpretation to WK and use sentence satisfaction correspondence.
-/
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

/--
@name AC and translated WK entailment coincide
@nl
For any premise and conclusion knowledge bases, AC entailment holds exactly when their positive WK translations are entailed. The two preceding results establish the forward and reverse directions.
@formula
$$\Gamma\models^{\mathsf{AC}}\Delta\iff\pi(\Gamma)\models^{\mathsf{WK}}\pi(\Delta)$$
@proof
Combine the two entailment directions.
-/

theorem A_iff_pi_WK (Γ Δ : (Φ σ)*) :
(Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ᵂᴷ π Δ) :=
  Iff.intro (A_implies_pi_WK Γ Δ) (pi_WK_implies_A Γ Δ)


-- MARK: WK to C
/-! \subsection{Weak Kleene to Classical Theorems} -/
/-!
The classical encoding $\Box I$ uses truth and meaningfulness predicates
for every WK atom. Structural induction on concepts shows that $\tau(C)$
expresses truth and $\mu(C)$ expresses meaningfulness. The decoding
$\blacksquare I$ reverses this correspondence wherever the bridge axioms
for the relevant names hold.
-/

-- MARK: Lemmas

@[simp]
theorem concept_mu (c : 𝒞 σ) : μ c = muConcept c := rfl
@[simp]
theorem concept_tau (c : 𝒞 σ) : τ c = tauConcept c := rfl

/--
@name Universal membership over unions
@nl
For a predicate $P$ and sets $A,B$, every element of $A\cup B$ satisfies $P$ exactly when every element of $A$ satisfies $P$ and every element of $B$ satisfies $P$.
@formula
$$(\forall x\in X\cup Y,\ P(x))\iff(\forall x\in X,\ P(x))\land(\forall x\in Y,\ P(x))$$
@proof
Apply the set utility theorem that universal membership distributes over union.
-/
theorem allMemUnion {α : Type} (P : α → Prop) (xs ys : α*) :
    (∀ x ∈ xs ∪ ys, P x) ↔ (∀ x ∈ xs, P x) ∧ (∀ x ∈ ys, P x) :=
  Set.forall_mem_union P xs ys

/--
@name Translated subsumption obligations
@nl
In a classical interpretation, satisfying $\tau(C\sqsubseteq D)$ means both that $\tau(C)$ is included in $\tau(D)$ and that some element satisfies both $\mu(C)$ and $\mu(D)$. The witness supplies an element where both source concepts differ from $\mathfrak{e}$.
@formula
$$I\models^{\mathsf{C}}\tau(C\sqsubseteq D)\iff(\tau(C))^I\subseteq(\tau(D))^I\land\exists x,\ (\mu(C))^I(x)\land(\mu(D))^I(x)$$
@proof
Expand the two translated sentences and use the nonemptiness characterization.
-/
theorem translateInclusion_iff (I : ℐᶜ σᵀ) (c d : 𝒞 σ) :
(∀ ψ ∈ tauSubsumption c d, I ⊨ᶜ ψ) ↔
(∀ x, ((τ c)^I) x → ((τ d)^I) x) ∧
∃ x, ((μ c)^I) x ∧ ((μ d)^I) x := by
  simp only [tauSubsumption, Set.mem_union, Set.mem_singleton,
    forall_eq_or_imp, forall_eq]
  rw [nonempty_iff]
  rfl

-- MARK: Encoding
/-!
The encoding yields the direction from translated classical entailment to
weak Kleene entailment.
-/

/--
@name Encode WK interpretations classically
@nl
Given a weak Kleene interpretation $\mathcal I$, the classical encoding uses the same domain and individual assignment. For each atomic concept $c\in N_C$ and atomic role $r\in N_R$, its truth copy holds exactly where the WK value is $\mathfrak{t}$, and its meaningfulness copy holds exactly where the WK value differs from $\mathfrak{e}$.
@formula
$$\begin{aligned}
\Delta^{\Box\mathcal I}&:=\Delta^\mathcal I,\\
a^{\Box\mathcal I}&:=a^\mathcal I,\\
(c,\mathsf T)^{\Box\mathcal I}(x)&:=c^\mathcal I(x)=\mathfrak{t},\\
(c,\mathsf M)^{\Box\mathcal I}(x)&:=c^\mathcal I(x)\ne\mathfrak{e},\\
(r,\mathsf T)^{\Box\mathcal I}(x,y)&:=r^\mathcal I(x,y)=\mathfrak{t},\\
(r,\mathsf M)^{\Box\mathcal I}(x,y)&:=r^\mathcal I(x,y)\ne\mathfrak{e}.
\end{aligned}$$
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

/--
@name Encoding preserves concept truth and meaning
@nl
For every concept $C$ and element $x$, the encoded classical extension of $\tau(C)$ agrees with whether $C^I(x)=\mathfrak{t}$, and the extension of $\mu(C)$ agrees with whether $C^I(x)\ne\mathfrak{e}$.
@formula
$$(\tau(C))^{\Box I}(x)\iff C^I(x)=\mathfrak{t},\qquad(\mu(C))^{\Box I}(x)\iff C^I(x)\ne\mathfrak{e}$$
@proof
Prove both claims together by structural induction on the concept; the quantified cases use the restricted-quantifier characterizations.
-/
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

/--
@name Encoded concept bridge
@nl
In the encoding of any WK interpretation, every element in an atomic concept's $\mathfrak{t}$ copy is also in its copy for values different from $\mathfrak{e}$, so each atomic concept bridge holds.
@formula
$$\Box I\models^{\mathsf{C}}\mathcal{D}(a)$$
@proof
Truth of an atomic value directly implies its meaningfulness.
-/
theorem encodedatomicConceptBridge (I : ℐᵂᴷ σ) (a : σ.Nc) :
□I ⊨ᶜ 𝒟 a := by
  simp only [Interpret.current, Interpret.interpret,
    BridgeTranslation.bridge, atomicConceptBridge,
    evalSentenceC, evalConceptC, encodeWK]
  intro x h
  rw [h]
  decide

/--
@name Encoded role bridge
@nl
In the encoding of any WK interpretation, every pair in an atomic role's $\mathfrak{t}$ copy is also in its copy for values different from $\mathfrak{e}$, so each atomic role bridge holds.
@formula
$$\Box I\models^{\mathsf{C}}\mathcal{D}(r)$$
@proof
Truth of an atomic role value directly implies its meaningfulness.
-/
theorem encodedatomicRoleBridge (I : ℐᵂᴷ σ) (r : σ.Nr) :
□I ⊨ᶜ 𝒟 r := by
  simp only [Interpret.current, Interpret.interpret,
    BridgeTranslation.bridge, atomicRoleBridge,
    evalSentenceC, evalRoleC, encodeWK]
  intro x y h
  rw [h]
  decide

/--
@name Encoded concept bridges
@nl
The encoding satisfies every atomic bridge in $\mathcal D(C)$, because each bridge follows from the corresponding encoded valuation; structural recursion gathers exactly those bridges for the names used by $C$.
@formula
$$\forall\psi\in\mathcal{D}(C),\ \Box I\models^{\mathsf{C}}\psi$$
@proof
Induct on the concept, combining bridge sets at binary and quantified constructors.
-/
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

/--
@name Encoded sentence bridges
@nl
For any sentence, the bridge set collects the atomic bridges for its concepts and roles. The encoding satisfies all of them, including both sides of inclusions and equivalences.
@formula
$$\forall\psi\in\mathcal{D}(\varphi),\ \Box I\models^{\mathsf{C}}\psi$$
@proof
Split by sentence constructor and use the concept and atomic role bridge results.
-/
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
      simpa only [sentenceBridges, BridgeTranslation.bridge,
        Set.mem_union, Set.mem_singleton, or_imp, forall_and, forall_eq] using
        And.intro (encodedatomicRoleBridge I r) (encodedatomicRoleBridge I s)

/--
@name Encoded subsumption correspondence
@nl
For an inclusion $C\sqsubseteq D$, the encoded classical interpretation satisfies both translated obligations exactly when the weak Kleene sentence value is $\mathfrak{t}$. The extra nonemptiness obligation accounts for the restricted universal's requirement that some pair have no $\mathfrak{e}$ coordinate.
@formula
$$\Box I\models^{\mathsf{C}}\tau(C\sqsubseteq D)\iff\forall_K\{(C^I(x),D^I(x)):x\in\Delta^I\}=\mathfrak{t}$$
@proof
Expand the inclusion and meaningfulness witness, then apply concept encoding and the universal-quantifier truth theorem.
-/
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

/--
@name Encoded sentence correspondence
@nl
For each $\mathcal{ALCH}$ sentence $\varphi$, the classical encoding satisfies every sentence in $\tau(\varphi)$ exactly when the original WK interpretation assigns $\mathfrak{t}$ to $\varphi$. The proof handles assertions, inclusions, equivalences, and role inclusions separately.
@formula
$$\Box I\models^{\mathsf{C}}\tau(\varphi)\iff I\models^{\mathsf{WK}}\varphi$$
@proof
Split by sentence form; use concept encoding, inclusion correspondence, and the role-overlap witness.
-/
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

/--
@name Encoded knowledge-base correspondence
@nl
The encoding satisfies a translated knowledge base exactly when the WK interpretation satisfies the original knowledge base.
@formula
$$\Box I\models^{\mathsf{C}}\tau(\Gamma)\iff I\models^{\mathsf{WK}}\Gamma$$
@proof
Distribute satisfaction over the bound translation set and apply sentence correspondence pointwise.
-/
theorem translateKBEncode (I : ℐᵂᴷ σ) (Γ : (Φ σ)*) :
(∀ φ ∈ τ Γ, □I ⊨ᶜ φ) ↔ ∀ φ ∈ Γ, I ⊨ᵂᴷ φ := by
  simp only [TauTranslation.tau, tauSentenceSet, allMemBind]
  exact forall_congr' (λ φ => imp_congr Iff.rfl (tauSentenceEncode I φ))

/--
@name Encoded knowledge-base bridges
@nl
For a knowledge base $\Gamma$, the encoding satisfies every bridge sentence in $\mathcal D(\Gamma)$. These are precisely the atomic concept and role constraints needed to interpret all names that occur in $\Gamma$.
@formula
$$\forall\psi\in\mathcal{D}(\Gamma),\ \Box I\models^{\mathsf{C}}\psi$$
@proof
Distribute bridge membership over the knowledge base and apply the sentence bridge theorem.
-/
theorem encodedKBBridges (I : ℐᵂᴷ σ) (Γ : (Φ σ)*) :
∀ ψ ∈ 𝒟 Γ, □I ⊨ᶜ ψ := by
  simp [BridgeTranslation.bridge]
  rw [sentenceSetBridges, allMemBind]
  exact λ φ _ => encodedSentenceBridges I φ

/--
@name Classical translation entails WK consequence
@nl
Suppose the classical translations of $\Gamma$ and $\Delta$, together with both bridge sets, entail $\tau(\Delta)$. Any WK interpretation satisfying $\Gamma$ can be encoded classically; the encoded model then satisfies the translated conclusions, which gives the required WK consequence.
@formula
$$\tau(\Gamma)\cup\mathcal{D}(\Gamma)\cup\mathcal{D}(\Delta)\models^{\mathsf{C}}\tau(\Delta)\implies\Gamma\models^{\mathsf{WK}}\Delta$$
@proof
Encode an arbitrary WK interpretation; its translated premises and both bridge sets hold, so the classical consequence decodes to the desired WK conclusions.
-/
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
The decoding yields the direction from weak Kleene entailment to translated
classical entailment.
-/

noncomputable def propValue (t m : V₂) : V₃ := by
  classical
  exact if t then 𝔱 else if m then 𝔣 else 𝔢

/--
@name Decoded $\mathfrak{t}$ value
@nl
The decoding function $\delta(t,m)$ returns a WK truth value from the truth predicate $t$ and meaningfulness predicate $m$. It returns $\mathfrak{t}$ exactly when $t$ holds.
@formula
$$\delta(t,m)=\mathfrak{t}\iff t$$
@proof
Split on the two predicates in the definition of $\delta$.
-/
@[simp] theorem propValue_truth (t m : V₂) :
propValue t m = 𝔱 ↔ t := by
  classical
  unfold propValue
  repeat (split) <;> simp_all

/--
@name Decoded meaningfulness
@nl
Assume $t$ implies $m$ in the decoder's two classical predicates. Then the decoded value differs from $\mathfrak{e}$ exactly when $m$ holds, so the second predicate records meaningfulness.
@formula
$$(t\rightarrow m)\implies(\delta(t,m)\ne\mathfrak{e}\iff m)$$
@proof
Split on the two predicates and use the bridge implication.
-/
@[simp] theorem propValue_meaningful (t m : V₂)
(h : t → m) : propValue t m ≠ 𝔢 ↔ m := by
  classical
  unfold propValue
  repeat (split) <;> simp_all

/--
@name Decode classical interpretations as WK interpretations
@nl
Given a classical interpretation $\mathcal I$ of the truth and meaningfulness copies, decoding keeps its domain and individual assignment. For each atomic concept $c\in N_C$ and atomic role $r\in N_R$, it returns $\mathfrak{t}$ when the truth copy holds, $\mathfrak{f}$ when only the meaningfulness copy holds, and $\mathfrak{e}$ when neither holds.
@formula
$$\begin{aligned}
\delta(t,m)&:=\begin{cases}
\mathfrak{t}&t,\\
\mathfrak{f}&\neg t\land m,\\
\mathfrak{e}&\neg t\land\neg m,
\end{cases}\\
\Delta^{\blacksquare\mathcal I}&:=\Delta^\mathcal I,\\
a^{\blacksquare\mathcal I}&:=a^\mathcal I,\\
c^{\blacksquare\mathcal I}(x)&:=\delta\bigl((c,\mathsf T)^\mathcal I(x),(c,\mathsf M)^\mathcal I(x)\bigr),\\
r^{\blacksquare\mathcal I}(x,y)&:=\delta\bigl((r,\mathsf T)^\mathcal I(x,y),(r,\mathsf M)^\mathcal I(x,y)\bigr).
\end{aligned}$$
-/
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
@name Local concept decoding
@nl
For a concept $C$ in a classical interpretation satisfying $\mathcal D(C)$, the predicates $\tau(C)$ and $\mu(C)$ decode to the same WK value as evaluating $C$ in the interpretation decoded from that model.
@formula
$$I\models^{\mathsf{C}}\mathcal{D}(C)\implies\bigl((\tau(C))^I(x)\iff C^{\blacksquare I}(x)=\mathfrak{t}\bigr)\land\bigl((\mu(C))^I(x)\iff C^{\blacksquare I}(x)\ne\mathfrak{e}\bigr)$$
@proof
Use structural induction on the concept; atomic and quantified cases draw only on the bridges of names occurring in that concept.
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

/--
@name Local inclusion decoding
@nl
For concepts $C,D$, assume the classical model satisfies their bridge sets. Then the translated inclusion and its witness hold exactly when the decoded WK interpretation gives $C\sqsubseteq D$ the value $\mathfrak{t}$.
@formula
$$I\models^{\mathsf{C}}\mathcal{D}(C)\cup\mathcal{D}(D)\implies\bigl(I\models^{\mathsf{C}}\tau(C\sqsubseteq D)\iff\blacksquare I\models^{\mathsf{WK}} C\sqsubseteq D\bigr)$$
@proof
Expand translated inclusion and its witness, then use local concept decoding and restricted universal truth.
-/
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

/--
@name Local sentence decoding
@nl
For any source sentence $\varphi$, assume the classical model satisfies $\mathcal D(\varphi)$. It satisfies every sentence in $\tau(\varphi)$ exactly when the decoded WK interpretation assigns $\mathfrak{t}$ to $\varphi$.
@formula
$$I\models^{\mathsf{C}}\mathcal{D}(\varphi)\implies\bigl(I\models^{\mathsf{C}}\tau(\varphi)\iff\blacksquare I\models^{\mathsf{WK}}\varphi\bigr)$$
@proof
Split by sentence form, using local concept decoding for concepts and atomic bridges for roles.
-/
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

/--
@name Local knowledge-base decoding
@nl
For a knowledge base $\Gamma$, assume the classical model satisfies all bridges in $\mathcal D(\Gamma)$. It then satisfies all sentences in $\tau(\Gamma)$ exactly when the decoded WK interpretation satisfies every sentence in $\Gamma$.
@formula
$$I\models^{\mathsf{C}}\mathcal{D}(\Gamma)\implies\bigl(I\models^{\mathsf{C}}\tau(\Gamma)\iff\blacksquare I\models^{\mathsf{WK}}\Gamma\bigr)$$
@proof
Distribute membership over the bound translation set and apply local sentence decoding to each source sentence.
-/
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

/--
@name WK consequence implies classical translation
@nl
Weak Kleene entailment implies classical entailment once the bridges of both knowledge bases are premises.
@formula
$$\Gamma\models^{\mathsf{WK}}\Delta\implies\tau(\Gamma)\cup\mathcal{D}(\Gamma)\cup\mathcal{D}(\Delta)\models^{\mathsf{C}}\tau(\Delta)$$
@proof
Decode an arbitrary classical interpretation satisfying the translated premises and bridges; use WK entailment and decode the conclusions.
-/
theorem entailmentK_imp_classical (Γ Δ : (Φ σ)*) :
(Γ ⊨ᵂᴷ Δ) → ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ)  := by
  intro h I hI
  rw [allMemUnion, allMemUnion] at hI
  rcases hI with ⟨⟨hΓ, hBΓ⟩, hBΔ⟩
  apply (decodeKBLocal I Δ hBΔ).mpr
  exact h (■I) ((decodeKBLocal I Γ hBΓ).mp hΓ)

-- MARK: WK to C

/--
@name WK and classical entailment coincide
@nl
For any premise and conclusion knowledge bases, the WK consequence holds exactly when their classical translations entail one another after adding the bridges for both sides. The two directions are proved by encoding WK models and decoding classical models.
@formula
$$\Gamma\models^{\mathsf{WK}}\Delta\iff\tau(\Gamma)\cup\mathcal{D}(\Gamma)\cup\mathcal{D}(\Delta)\models^{\mathsf{C}}\tau(\Delta)$$
@proof
Combine the encoding and decoding entailment directions.
-/

theorem entailmentK_iff_classical (Γ Δ : (Φ σ)*) :
(Γ ⊨ᵂᴷ Δ) ↔ ((τ Γ ∪ 𝒟 Γ ∪ 𝒟 Δ) ⊨ᶜ τ Δ) :=
  Iff.intro
  (entailmentK_imp_classical Γ Δ)
  (classical_imp_entailmentK Γ Δ)

-- MARK: AC to C
/-! \subsection{The Composed AC Translation} -/

/--
@name AC to classical entailment theorem
@nl
For any AC knowledge bases $\Gamma,\Delta$, entailment is equivalent to classical entailment from the translation of $\pi(\Gamma)$ plus the bridge sets for both projected knowledge bases to the translation of $\pi(\Delta)$. This composes the AC-to-WK and WK-to-classical results.
@formula
$$\Gamma\models^{\mathsf{AC}}\Delta\iff\tau(\pi(\Gamma))\cup\mathcal{D}(\pi(\Gamma))\cup\mathcal{D}(\pi(\Delta))\models^{\mathsf{C}}\tau(\pi(\Delta))$$
@proof
Compose the AC-to-WK and WK-to-classical entailment equivalences.
-/

theorem MainResult (σ : Signature) (Γ Δ : (Φ σ)*) :
(Γ ⊨ᴬᶜ Δ) ↔ ((τ (π Γ) ∪ 𝒟 (π Γ) ∪ 𝒟 (π Δ)) ⊨ᶜ τ (π Δ)) := by
  calc
    (Γ ⊨ᴬᶜ Δ) ↔ (π Γ ⊨ᵂᴷ π Δ)                  := A_iff_pi_WK Γ Δ
    _         ↔ ((τ (π Γ) ∪ 𝒟 (π Γ) ∪ 𝒟 (π Δ)) ⊨ᶜ τ (π Δ))    := entailmentK_iff_classical (π Γ) (π Δ)

end ALCHAC
