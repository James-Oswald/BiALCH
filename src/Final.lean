
import Mathlib
import DefDel

namespace ALCHAC

-- Weak kleene truth values
inductive V₃ where
| t
| e
| f
deriving DecidableEq, Repr

notation "𝔱" => V₃.t
notation "𝔢" => V₃.e
notation "𝔣" => V₃.f

-- Finiteness of the weak kleene truth values
instance : Fintype V₃ where
  elems := {.t, .e, .f}
  complete x := by cases x <;> tauto

-- Pairs of weak kleene truth values
abbrev V₃2 := V₃ × V₃
notation "V₃²" => V₃2

-- We can decide membership in a set of pairs
-- (needed so restricted Weak Kleene quantifiers are well defined)
noncomputable instance (X : Set V₃²) (x : V₃²) : Decidable (x ∈ X) :=
  Classical.propDecidable _

-- Weak kleene logical connectives
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

/-- The paper's restricted existential quantifier, including its stated case order. -/
noncomputable def paperExists (X : Set V₃²) : V₃ :=
  if H1: ⟨𝔱, 𝔱⟩ ∈ X then
    𝔱
  else if H2: ∀ x ∈ X, x.1 = 𝔢 ∨ x.2 = 𝔢 then
    𝔢
  else if H3: ⟨𝔱, 𝔱⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔣
  else by grind only -- Impossible case

/-- The paper's restricted universal quantifier, including its stated case order. -/
noncomputable def paperForall (X : Set V₃²) : V₃ :=
  if H1: ⟨𝔱, 𝔣⟩ ∉ X ∧ ⟨𝔱, 𝔢⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔱
  else if H2: ∀ x ∈ X, x.1 = 𝔢 ∨ x.2 = 𝔢 then
    𝔢
  else if H3: (⟨𝔱, 𝔣⟩ ∈ X ∨ ⟨𝔱, 𝔢⟩ ∈ X) ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔣
  else by grind only

/-- Apply the paper's set-based quantifier to the indexed family of value pairs. -/
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
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by simp
  unfold existsKIndexed paperExists
  split_ifs <;> first | rfl | grind only

private theorem forallKIndexed_paper {D} (r c : D → V₃) :
    forallKIndexed r c = paperForall (Set.range (fun x => (r x, c x))) := by
  classical
  have hm : (∀ p ∈ Set.range (fun x => (r x, c x)), p.1 = 𝔢 ∨ p.2 = 𝔢) ↔
      ¬ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.forall_mem_range, not_exists, not_and, not_not]
    exact forall_congr' (fun x => or_iff_not_imp_left)
  have hw : (∃ p ∈ Set.range (fun x => (r x, c x)), p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) ↔
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by simp
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
  split_ifs <;> first | rfl | grind only

private theorem existsKIndexed_t {D} (r c : D → V₃) :
    existsKIndexed r c = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  classical
  unfold existsKIndexed
  split_ifs <;> simp_all

private theorem existsKIndexed_m {D} (r c : D → V₃) :
    existsKIndexed r c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold existsKIndexed
  split_ifs <;> simp_all
  obtain ⟨x, hx, hy⟩ := ‹∃ x, r x = 𝔱 ∧ c x = 𝔱›
  exact ⟨x, by simp [hx], by simp [hy]⟩

private theorem forallKIndexed_t {D} (r c : D → V₃) :
    forallKIndexed r c = 𝔱 ↔ (∀ x, r x = 𝔱 → c x = 𝔱) ∧
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallKIndexed
  split_ifs <;> simp_all

private theorem forallKIndexed_m {D} (r c : D → V₃) :
    forallKIndexed r c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallKIndexed
  split_ifs <;> simp_all

@[simp]
theorem negK_t (v : V₃) : ¬ₖv = 𝔱 ↔ v ≠ 𝔢 ∧ v ≠ 𝔱 := by
  cases v <;> decide

@[simp]
theorem negK_m (v : V₃) : ¬ₖv ≠ 𝔢 ↔ v ≠ 𝔢 := by
  cases v <;> decide

@[simp]
theorem andK_t (v w : V₃) : v ∧ₖ w = 𝔱 ↔ v = 𝔱 ∧ w = 𝔱 := by
  cases v <;> cases w <;> decide

@[simp]
theorem andK_m (v w : V₃) : v ∧ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

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

theorem existsK_paper {D} (r c : D → V₃) :
existsK r c = paperExists (Set.range (λ x => (r x, c x))) := by
  rfl

theorem forallK_paper {D} (r c : D → V₃) :
forallK r c = paperForall (Set.range (λ x => (r x, c x))) := by
  rfl

-- AC operators

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

structure Signature where
  Nc : Type
  [reprNc : Repr Nc]
  Nr : Type
  [reprNr : Repr Nr]
  Ni : Type
  [reprNi : Repr Ni]

attribute [instance] Signature.reprNc Signature.reprNr Signature.reprNi

inductive Concept (σ : Signature) (R : Type) where
| top
| bot
| atom : σ.Nc → Concept σ R
| neg : Concept σ R → Concept σ R
| conj : Concept σ R → Concept σ R → Concept σ R
| disj : Concept σ R → Concept σ R → Concept σ R
| ex : R → Concept σ R → Concept σ R
| all : R → Concept σ R → Concept σ R
deriving Repr

inductive ALCHRU_Role (σ : Signature) where
| atom : σ.Nr → ALCHRU_Role σ
| universal : ALCHRU_Role σ
| inter : ALCHRU_Role σ -> ALCHRU_Role σ -> ALCHRU_Role σ
notation "ℛᵁ" => ALCHRU_Role

inductive Sentence (σ : Signature) (R : Type) where
| isa : σ.Ni → Concept σ R → Sentence σ R
| role : σ.Ni → σ.Ni → R → Sentence σ R
| sub : Concept σ R → Concept σ R → Sentence σ R
| equiv : Concept σ R → Concept σ R → Sentence σ R
| rsub : R → R → Sentence σ R
deriving Repr

abbrev ALCH_Concept (σ : Signature) := Concept σ σ.Nr
notation "𝒞" => ALCH_Concept
abbrev ALCHRU_Concept (σ : Signature) := Concept σ (ALCHRU_Role σ)
notation "𝒞ᵁ" => ALCHRU_Concept

abbrev ALCH_Sentence (σ : Signature) := Sentence σ σ.Nr
notation "Φ" => ALCH_Sentence
abbrev ALCHRU_Sentence (σ : Signature) := Sentence σ (ALCHRU_Role σ)
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

-- Role Notations
notation "[" r "]ᵣ" => ALCHRU_Role.atom r
infixl:70 " ⊓ᵣ " => ALCHRU_Role.inter
notation "𝒰" => ALCHRU_Role.universal

-- Sentence Notations
notation a " :ₐ " c:50 => Sentence.isa a c
notation "(" a ", " b ")" " :ᵣ " r:50 => Sentence.role a b r
infix:50 " ⊑ " => Sentence.sub
infix:50 " ≡ " => Sentence.equiv
infix:50 " ⊑ᵣ " => Sentence.rsub

-- ALCH Examples
example (A B : σ.Nc) (r : σ.Nr) : 𝒞 σ :=
  A ⊓ₜ (∃[r] B) ⊓ₜ (∀[r] ¬ₜ A)

example (a : σ.Ni) (A : σ.Nc) (r : σ.Nr) : Φ σ :=
  (a :ₐ (A ⊓ₜ (∃[r] A)))

example (a b : σ.Ni) (r : σ.Nr) : Φ σ :=
  (a, b) :ᵣ r

example (r s : σ.Nr) : Φ σ := r ⊑ᵣ s

-- ALCHRU Examples with compound roles and universal roles

example (A B : σ.Nc) (r s : ALCHRU_Role σ) : 𝒞ᵁ σ :=
  A ⊓ₜ (∃[r ⊓ᵣ s] B) ⊓ₜ (∀[𝒰] A)

instance : Coe σ.Nr (ALCHRU_Role σ) := ⟨ALCHRU_Role.atom⟩


/-- Nonempty domains; no unique-name assumption. -/
structure Interpretation (σ : Signature) (V : Type) where
  D : Type
  inhabited : Nonempty D
  individualValuation : σ.Ni → D
  atomicConceptValuation : σ.Nc → D → V
  roleValuation : σ.Nr → D → D → V

-- Classical Interpretations use the two-valued Boolean domain (Prop)
abbrev CInterpretation (σ : Signature) := Interpretation σ Prop
notation "ℐᶜ" => CInterpretation
-- Weak Kleene Interpretations use the three-valued Kleene domain (V₃)
abbrev WKInterpretation (σ : Signature) := Interpretation σ V₃
notation "ℐᵂᴷ" => WKInterpretation
-- Anylitic Containment use pairs of three-valued Kleene domains (V₃²)
abbrev ACInterpretation (σ : Signature) := Interpretation σ V₃²
notation "ℐᴬᶜ" => ACInterpretation

notation r "^ᵃʳ" I => Interpretation.roleValuation I r
notation a "^ᵃᶜ" I => Interpretation.atomicConceptValuation I a
set_option quotPrecheck false in
notation a "^ⁱ" I => (I).individualValuation a

-- Classical Semantics

-- Classical Role Evaluation for ALCHRU
def roleC (I : ℐᶜ σ) : ℛᵁ σ → I.D → I.D → Prop
| [r]ᵣ, x, y => (r^ᵃʳI) x y
| 𝒰, _, _ => True
| r ⊓ᵣ s, x, y => roleC I r x y ∧ roleC I s x y

notation r "^ʳᶜ" I => roleC I r

-- Classical Concept Evaluation on ALCHRU concepts
def∇ evalC (I : ℐᶜ σ) : 𝒞ᵁ σ → I.D → Prop
| ⊤, _ => True
| ⊥, _ => False
| [a]ₐ, x => (a^ᵃᶜ I) x
| ¬ₜc, x => ¬(∇ c x)
| c ⊓ₜ d, x => (∇ c x) ∧ (∇ d x)
| c ⊔ₜ d, x => ∇ c x ∨ (∇ d x)
| ∃[r] c, x => ∃ y, (r^ʳᶜ I) x y ∧ ∇ c y
| ∀[r] c, x => ∀ y, (r^ʳᶜ I) x y → ∇ c y

notation c "^ᶜᶜ" I => evalC I c

/--
Classical sentence semantics for ALCHRU.
-/
def sentenceC (I : ℐᶜ σ) : Φᵁ σ → Prop
| a :ₐ c => (c^ᶜᶜ I) (a^ⁱ I)
| (a, b) :ᵣ r => (r^ʳᶜ I) (a^ⁱ I) (b^ⁱ I)
| c ⊑ d => ∀ x, (c^ᶜᶜ I) x → (d^ᶜᶜ I) x
| c ≡ d => ∀ x, (c^ᶜᶜ I) x ↔ (d^ᶜᶜ I) x
| r ⊑ᵣ s => ∀ x y, (r^ʳᶜ I) x y → (s^ʳᶜ I) x y

notation  I "⊨ᶜₘ " S => sentenceC I S

def entailmentC (Γ Δ : List (Φᵁ σ)) : Prop :=
  ∀ I, (∀ ψ ∈ Γ, I ⊨ᶜₘ ψ) → (∀ φ ∈ Δ, I ⊨ᶜₘ φ)

notation  Γ " ⊨ᶜ " Δ => entailmentC Γ Δ


/--
Weak Kleene concept semantics for ALCHRU.
-/
noncomputable def∇ evalK (I : ℐᵂᴷ σ) : 𝒞 σ → I.D → V₃
| ⊤, _ => 𝔱
| ⊥, _ => 𝔣
| [a]ₐ, x => (a^ᵃᶜ I) x
| ¬ₜ c, x => ¬ₖ(∇ c x)
| c ⊓ₜ d, x => (∇ c x) ∧ₖ (∇ d x)
| c ⊔ₜ d, x => (∇ c x) ∨ₖ (∇ d x)
| ∃[r] c, x => ∃ₖ[(r^ᵃʳ I) x] (∇ c)
| ∀[r] c, x => ∀ₖ[(r^ᵃʳ I) x] (∇ c)

notation c "^ᶜᴷ" I => evalK I c

/--
Weak Kleene sentence semantics for ALCHRU.
-/
noncomputable def sentenceK (I : ℐᵂᴷ σ) : Φ σ → V₃
| a :ₐ c => (c^ᶜᴷ I) (a^ⁱ I)
| (a, b) :ᵣ r => (r^ᵃʳ I) (a^ⁱ I) (b^ⁱ I)
| c ⊑ d => ∀ₖ[c^ᶜᴷ I] (d^ᶜᴷ I)
| c ≡ d => (∀ₖ[c^ᶜᴷ I] (d^ᶜᴷ I)) ∧ₖ (∀ₖ[d^ᶜᴷ I] (c^ᶜᴷ I))
| r ⊑ᵣ s => ∀ₖ[(λ p : I.D × I.D => (r^ᵃʳ I) p.1 p.2)] (λ p => (s^ᵃʳ I) p.1 p.2)

def satisfiesK (I : ℐᵂᴷ σ) (φ : Φ σ) : Prop :=
  (sentenceK I φ) = 𝔱

notation  I "⊨ᴷₘ " S => satisfiesK I S

def entailmentK (Γ Δ : List (Φ σ)) : Prop :=
  ∀ (I : ℐᵂᴷ σ), (∀ ψ ∈ Γ, I ⊨ᴷₘ ψ) → (∀ φ ∈ Δ, I ⊨ᴷₘ φ)

notation  Γ " ⊨ᴷ " Δ => entailmentK Γ Δ

noncomputable def∇ evalA (I : ℐᴬᶜ σ) : 𝒞 σ → I.D → V₃²
| ⊤, _ => (𝔱, 𝔣)
| ⊥, _ => (𝔣, 𝔱)
| [a]ₐ, x => (a^ᵃᶜ I) x
| ¬ₜ c, x => ∼ₐ(∇ c x)
| c ⊓ₜ d, x => (∇ c x) ∧ₐ (∇ d x)
| c ⊔ₜ d, x => (∇ c x) ∨ₐ (∇ d x)
| ∃[r] c, x => ∃ₐ[(r^ᵃʳ I) x] (∇ c)
| ∀[r] c, x => ∀ₐ[(r^ᵃʳ I) x] (∇ c)

notation c "^ᶜᴬ" I => evalA I c

noncomputable def sentenceA (I : ℐᴬᶜ σ) : Φ σ → V₃²
| a :ₐ c => (c^ᶜᴬ I) (a^ⁱ I)
| (a, b) :ᵣ r => (r^ᵃʳ I) (a^ⁱ I) (b^ⁱ I)
| c ⊑ d => ∀ₐ[c^ᶜᴬ I] (d^ᶜᴬ I)
| c ≡ d => (∀ₐ[c^ᶜᴬ I] (d^ᶜᴬ I)) ∧ₐ (∀ₐ[d^ᶜᴬ I] (c^ᶜᴬ I))
| r ⊑ᵣ s => ∀ₐ[(λ p : I.D × I.D => (r^ᵃʳ I) p.1 p.2)] (λ p => (s^ᵃʳ I) p.1 p.2)

def satisfiesA (I : ℐᴬᶜ σ) (φ : Φ σ) : Prop :=
  (sentenceA I φ).1 = 𝔱

notation  I "⊨ᴬₘ " S => satisfiesA I S

def entailmentA (Γ Δ : List (Φ σ)) : Prop :=
  ∀ (I : ℐᴬᶜ σ), (∀ ψ ∈ Γ, I ⊨ᴬₘ ψ) → (∀ φ ∈ Δ, I ⊨ᴬₘ φ)

notation  Γ " ⊨ᴬ " Δ => entailmentA Γ Δ

/-! ## AC to weak Kleene -/

inductive Side where
| positive
| negative
deriving DecidableEq, Repr

notation "+ₚ" => Side.positive
notation "-ₚ" => Side.negative

--Operator overload for superscript WK
class ToWK (α : Type u) (γ : outParam (Type w)) where
  wkIze : α → γ

postfix:max "ᵂᴷ" => ToWK.wkIze

--Operator overload for superscript AC
class ToAC (α : Type u) (γ : outParam (Type w)) where
  acIze : α → γ

postfix:max "ᴬᶜ" => ToAC.acIze

class ToC (α : Type u) (γ : outParam (Type w)) where
  cIze : α → γ

postfix:max "ᶜ" => ToC.cIze

/-
Given a signature σ, the weak Kleene signature σᵂᴷ is defined by
pairing each original concept with a side indicator (+ₚ or -ₚ)
-/
abbrev wkSignature (σ : Signature) : Signature where
  Nc := σ.Nc × Side
  Nr := σ.Nr
  Ni := σ.Ni

-- So we can use σᵂᴷ as shorthand for the weak kleene signature of σ
instance toWKSignature : ToWK Signature Signature where
  wkIze := wkSignature


-- Polarize recursively transforms an ALCH concept into its weak
-- Kleene counterpart based on the given side indicator (+ₚ or -ₚ).
def∇ polarize {σ : Signature} : 𝒞 σ → Side → 𝒞 σᵂᴷ
| ⊤, +ₚ => ⊤
| ⊤, -ₚ => ⊥
| ⊥, +ₚ => ⊥
| ⊥, -ₚ => ⊤
| [a]ₐ, side => [(a, side)]ₐ
| ¬ₜ c, +ₚ => ∇ c -ₚ
| ¬ₜ c, -ₚ => ∇ c +ₚ
| c ⊓ₜ d, +ₚ => (∇ c +ₚ) ⊓ₜ (∇ d +ₚ)
| c ⊓ₜ d, -ₚ => (∇ c -ₚ) ⊔ₜ (∇ d -ₚ)
| c ⊔ₜ d, +ₚ => (∇ c +ₚ) ⊔ₜ (∇ d +ₚ)
| c ⊔ₜ d, -ₚ => (∇ c -ₚ) ⊓ₜ (∇ d -ₚ)
| ∃[r] c, +ₚ => ∃[r] ∇ c +ₚ
| ∃[r] c, -ₚ => ∀[r] ∇ c -ₚ
| ∀[r] c, +ₚ => ∀[r] ∇ c +ₚ
| ∀[r] c, -ₚ => ∃[r] ∇ c -ₚ

notation C "ᵖ⁺" => polarize C +ₚ
notation C "ᵖ⁻" => polarize C -ₚ
postfix:max "ᵖ" => polarize

/--
Projects an ALCH sentence over the original signature σ to its weak Kleene counterpart
over the signature σᵂᴷ by polarizing all concepts positively.
-/
def projectSentence (σ : Signature) : Φ σ → Φ σᵂᴷ
| a :ₐ c => a :ₐ cᵖ⁺
| (a, b) :ᵣ r => (a, b) :ᵣ r
| c ⊑ d => cᵖ⁺ ⊑ dᵖ⁺
| c ≡ d => cᵖ⁺ ≡ dᵖ⁺
| r ⊑ᵣ s => r ⊑ᵣ s

abbrev projectSentenceSet (σ : Signature) : List (Φ σ) → List (Φ σᵂᴷ) :=
  List.map (projectSentence σ)

instance : ToWK (List (Φ σ)) (List (Φ σᵂᴷ)) where
  wkIze := projectSentenceSet _

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
  atomicConceptValuation := λ (a, s) x => ((a^ᵃᶜ I) x)[s]
  roleValuation :=          λ r x y => ((r^ᵃʳI) x y)[+ₚ]

instance : ToWK (ℐᴬᶜ σ) (ℐᵂᴷ σᵂᴷ) := ⟨acToWK⟩

def wkToAC (K : ℐᵂᴷ σᵂᴷ) : ℐᴬᶜ σ where
  D :=                      K.D
  inhabited :=              K.inhabited
  individualValuation :=    K.individualValuation
  atomicConceptValuation := λ a x => (((a, +ₚ)^ᵃᶜ K) x, ((a, -ₚ)^ᵃᶜ K) x)
  roleValuation :=          λ r x y => ((r^ᵃʳ K) x y, 𝔢)

instance : ToAC (ℐᵂᴷ σᵂᴷ) (ℐᴬᶜ σ) := ⟨wkToAC⟩

theorem acToWK_wkToAC (K : ℐᵂᴷ σᵂᴷ) : (Kᴬᶜ)ᵂᴷ = K := by
  cases K with
  | mk D inhabited individuals atoms roles =>
      simp only [acToWK, wkToAC, ToAC.acIze, ToWK.wkIze]
      congr 1
      funext a x
      rcases a with ⟨a, side⟩
      cases side <;> rfl

theorem acConceptCoordinates (I : ℐᴬᶜ σ) (c : 𝒞 σ) (s : Side) (x : I.D) :
((cᵖ s)^ᶜᴷ (Iᵂᴷ)) x = ((c^ᶜᴬ I) x)[s] := by
  induction c generalizing s x with
  | top => cases s <;> rfl
  | bot => cases s <;> rfl
  | atom a => cases s <;> rfl
  | neg c ih => cases s <;> simp only
    [polarize, evalA, negA, GetElem.getElem, coordinate, ih]
  | conj c d ihc ihd =>
      cases s <;> simp only
        [polarize, evalK, evalA, andA, GetElem.getElem, coordinate, ihc, ihd]
  | disj c d ihc ihd =>
      cases s <;> simp only
        [polarize, evalK, evalA, orA, GetElem.getElem, coordinate, ihc, ihd]
  | ex r c ih =>
      cases s with
      | positive => exact congrArg₂ existsK rfl (funext (ih +ₚ))
      | negative => exact congrArg₂ forallK rfl (funext (ih -ₚ))
  | all r c ih =>
      cases s with
      | positive => exact congrArg₂ forallK rfl (funext (ih +ₚ))
      | negative => exact congrArg₂ existsK rfl (funext (ih -ₚ))

theorem acSentenceSupport (I : ℐᴬᶜ σ) (s : Φ σ) :
    sentenceK (acToWK I) (projectSentence σ s) = (sentenceA I s)[+ₚ] := by
  have hc (c : 𝒞 σ) :
      evalK (acToWK I) (polarize c +ₚ) = fun x => (evalA I c x).1 :=
    funext (acConceptCoordinates I c +ₚ)
  cases s <;> simp only [projectSentence, sentenceK, sentenceA, forallA, andA, hc] <;> rfl

/-- The explicit WK entailment intermediate used in the final theorem. -/
theorem entailmentA_iff_projectedWK (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᴬ Δ) ↔ (Γᵂᴷ ⊨ᴷ Δᵂᴷ) := by
  constructor
  · intro h K hΓ q hq
    have hround : acToWK (wkToAC K) = K := acToWK_wkToAC K
    rcases List.mem_map.mp hq with ⟨s, hs, rfl⟩
    have hsource : ∀ p ∈ Γ, satisfiesA (wkToAC K) p := by
      intro p hp
      have hk := hΓ (projectSentence σ p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      change (sentenceA (wkToAC K) p)[+ₚ] = 𝔱
      rw [← acSentenceSupport, hround]
      exact hk
    have hout := h (wkToAC K) hsource s hs
    change (sentenceA (wkToAC K) s)[+ₚ] = 𝔱 at hout
    rw [← acSentenceSupport, hround] at hout
    exact hout
  · intro h I hΓ s hs
    have hprojected : ∀ p ∈ Γ.map (projectSentence σ), satisfiesK (acToWK I) p := by
      intro p hp
      rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
      simpa [satisfiesK, satisfiesA, acSentenceSupport, GetElem.getElem, coordinate]
        using hΓ q hq
    have hout := h (acToWK I) hprojected (projectSentence σ s)
      (List.mem_map.mpr ⟨s, hs, rfl⟩)
    simpa [satisfiesK, satisfiesA, acSentenceSupport, GetElem.getElem, coordinate]
      using hout

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

/-- A truth concept and a meaningfulness concept for each WK concept. -/
def∇ translateConcept (σ : Signature) : 𝒞 σ → 𝒞ᵁ σᵀ × 𝒞ᵁ σᵀ
| ⊤ => (⊤, ⊤)
| ⊥ => (⊥, ⊤)
| [a]ₐ => ([(a, 𝕋)]ₐ, [(a, 𝕄)]ₐ)
| ¬ₜ c => ((∇ c).2 ⊓ₜ ¬ₜ(∇ c).1, (∇ c).2)
| c ⊓ₜ d => ((∇ c).1 ⊓ₜ (∇ d).1, (∇ c).2 ⊓ₜ (∇ d).2)
| c ⊔ₜ d => (((∇ c).1 ⊔ₜ (∇ d).1) ⊓ₜ ((∇ c).2 ⊓ₜ (∇ d).2), (∇ c).2 ⊓ₜ (∇ d).2)
| ∃[r] c => (∃[[(r, 𝕋)]ᵣ] (∇ c).1, ∃[[(r, 𝕄)]ᵣ] (∇ c).2)
| ∀[r] c => (∀[[(r, 𝕋)]ᵣ] (∇ c).1 ⊓ₜ ∃[[(r, 𝕄)]ᵣ] (∇ c).2, ∃[[(r, 𝕄)]ᵣ] (∇ c).2)

/--
We can express that C is nonempty in classical ALC using
the universal role. ⊤ ⊑ ∃[𝒰] c -> ∀x, ∃y, c(y) -> ∃y, c(y)
-/
def nonemptyAxiom (c : 𝒞ᵁ σ) : Φᵁ σ :=
  ⊤ ⊑ ∃[𝒰] c

@[simp]
theorem nonemptyAxiom_iff (I : ℐᶜ σ) (c : 𝒞ᵁ σ) :
    sentenceC I (nonemptyAxiom c) ↔ ∃ x, evalC I c x := by
  simp only [nonemptyAxiom, sentenceC, evalC, roleC, true_implies, true_and]
  constructor
  · intro h
    obtain ⟨x⟩ := I.inhabited
    exact h x
  · intro h _
    exact h

/-- Intersection forces both roles to hold on the same ordered pair. -/
def overlapAxiom (r s : σ.Nr) : Φᵁ σ :=
  nonemptyAxiom (∃[([r]ᵣ ⊓ᵣ [s]ᵣ)] ⊤)

@[simp] theorem overlapAxiom_iff (I : ℐᶜ σ) (r s : σ.Nr) :
    sentenceC I (overlapAxiom r s) ↔
      ∃ x y, I.roleValuation r x y ∧ I.roleValuation s x y := by
  simp [overlapAxiom, evalC, roleC]

def translateInclusion (σ : Signature) (c d : 𝒞 σ) :
    List (Φᵁ σᵀ) :=
  [ (translateConcept σ c).1 ⊑ (translateConcept σ d).1,
    nonemptyAxiom ((translateConcept σ c).2 ⊓ₜ (translateConcept σ d).2) ]

def translateSentence (σ : Signature) : Φ σ →
    List (Φᵁ σᵀ)
| a :ₐ c => [a :ₐ (translateConcept σ c).1]
| (a, b) :ᵣ r => [(a, b) :ᵣ [(r, 𝕋)]ᵣ]
| c ⊑ d => translateInclusion σ c d
| c ≡ d => translateInclusion σ c d ++ translateInclusion σ d c
| r ⊑ᵣ s =>
    [[(r, 𝕋)]ᵣ ⊑ᵣ [(s, 𝕋)]ᵣ,
      overlapAxiom (r, 𝕄) (s, 𝕄)]

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

def encodeWK (I : WKInterpretation σ) : CInterpretation σᵀ where
  D := I.D
  inhabited := I.inhabited
  individualValuation := I.individualValuation
  atomicConceptValuation := fun (a, bit) x => match bit with
    | .truth => I.atomicConceptValuation a x = 𝔱
    | .meaningful => I.atomicConceptValuation a x ≠ 𝔢
  roleValuation := fun (r, bit) x y => match bit with
    | .truth => I.roleValuation r x y = 𝔱
    | .meaningful => I.roleValuation r x y ≠ 𝔢

noncomputable def propValue (truth meaningful : Prop) : V₃ := by
  classical
  exact if truth then 𝔱 else if meaningful then 𝔣 else 𝔢

@[simp] theorem propValue_truth (truth meaningful : Prop) :
    propValue truth meaningful = 𝔱 ↔ truth := by
  classical
  unfold propValue
  split_ifs <;> simp_all

@[simp] theorem propValue_meaningful (truth meaningful : Prop)
    (h : truth → meaningful) : propValue truth meaningful ≠ 𝔢 ↔ meaningful := by
  classical
  unfold propValue
  split_ifs <;> simp_all

noncomputable def decodeTarget (J : CInterpretation σᵀ) :
    WKInterpretation σ where
  D := J.D
  inhabited := J.inhabited
  individualValuation := J.individualValuation
  atomicConceptValuation := fun a x =>
    propValue (J.atomicConceptValuation (a, .truth) x)
      (J.atomicConceptValuation (a, .meaningful) x)
  roleValuation := fun r x y =>
    propValue (J.roleValuation (r, .truth) x y) (J.roleValuation (r, .meaningful) x y)

theorem translateConceptEncode (I : WKInterpretation σ) (c : 𝒞 σ) (x : I.D) :
    (evalC (encodeWK I) (translateConcept σ c).1 x ↔ evalK I c x = 𝔱) ∧
    (evalC (encodeWK I) (translateConcept σ c).2 x ↔ evalK I c x ≠ 𝔢) := by
  induction c generalizing x with
  | top => simp [translateConcept, evalC, evalK]
  | bot => simp [translateConcept, evalC, evalK]
  | atom a => simp [translateConcept, evalC, evalK, encodeWK]
  | neg c ih =>
      simp [translateConcept, evalC, evalK, (ih x).1, (ih x).2]
  | conj c d ihc ihd =>
      simp [translateConcept, evalC, evalK, (ihc x).1, (ihc x).2,
        (ihd x).1, (ihd x).2]
  | disj c d ihc ihd =>
      simp [translateConcept, evalC, evalK, (ihc x).1, (ihc x).2,
        (ihd x).1, (ihd x).2]
  | ex r c ih =>
      simp only [translateConcept, evalC, roleC, evalK, existsK_t, existsK_m]
      exact ⟨exists_congr (fun y => and_congr Iff.rfl (ih y).1),
        exists_congr (fun y => and_congr Iff.rfl (ih y).2)⟩
  | all r c ih =>
      simp only [translateConcept, evalC, roleC, evalK, forallK_t, forallK_m]
      refine ⟨and_congr ?_ ?_, ?_⟩
      · exact forall_congr' (fun y => imp_congr Iff.rfl (ih y).1)
      · exact exists_congr (fun y => and_congr Iff.rfl (ih y).2)
      · exact exists_congr (fun y => and_congr Iff.rfl (ih y).2)

theorem encodedAtomBridge (I : WKInterpretation σ) (a : σ.Nc) :
    sentenceC (encodeWK I) (atomBridge σ a) := by
  simp only [atomBridge, sentenceC, evalC, encodeWK]
  intro x h
  simp [h]

theorem encodedRoleBridge (I : WKInterpretation σ) (r : σ.Nr) :
    sentenceC (encodeWK I) (roleBridge σ r) := by
  simp only [roleBridge, sentenceC, roleC, encodeWK]
  intro x y h
  simp [h]

theorem encodedConceptBridges (I : WKInterpretation σ) (c : 𝒞 σ) :
    ∀ q ∈ conceptBridges σ c, sentenceC (encodeWK I) q := by
  induction c with
  | top | bot => simp [conceptBridges]
  | atom a => simpa [conceptBridges] using encodedAtomBridge I a
  | neg c ih => exact ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      simpa only [conceptBridges, List.mem_append, or_imp, forall_and] using And.intro ihc ihd
  | ex r c ih | all r c ih =>
      simpa [conceptBridges] using And.intro (encodedRoleBridge I r) ih

theorem encodedSentenceBridges (I : WKInterpretation σ) (s : Φ σ) :
    ∀ q ∈ sentenceBridges σ s, sentenceC (encodeWK I) q := by
  cases s with
  | isa a c => exact encodedConceptBridges I c
  | role a b r => simpa [sentenceBridges] using encodedRoleBridge I r
  | sub c d | equiv c d =>
      simpa only [sentenceBridges, List.mem_append, or_imp, forall_and] using
        And.intro (encodedConceptBridges I c) (encodedConceptBridges I d)
  | rsub r s =>
      simpa [sentenceBridges] using And.intro (encodedRoleBridge I r) (encodedRoleBridge I s)

/-- Bridges are needed only for the names occurring in the concept being decoded. -/
theorem decodeConceptLocal (J : CInterpretation σᵀ)
    (c : 𝒞 σ)
    (h : ∀ q ∈ conceptBridges σ c, sentenceC J q) (x : J.D) :
    (evalC J (translateConcept σ c).1 x ↔ evalK (decodeTarget J) c x = 𝔱) ∧
    (evalC J (translateConcept σ c).2 x ↔ evalK (decodeTarget J) c x ≠ 𝔢) := by
  induction c generalizing x with
  | top => simp [translateConcept, evalC, evalK]
  | bot => simp [translateConcept, evalC, evalK]
  | atom a =>
      have ha : ∀ y, J.atomicConceptValuation (a, .truth) y →
          J.atomicConceptValuation (a, .meaningful) y := by
        simpa [atomBridge, sentenceC, evalC] using
          h (atomBridge σ a) (by simp [conceptBridges])
      exact ⟨(propValue_truth _ _).symm, (propValue_meaningful _ _ (ha x)).symm⟩
  | neg c ih =>
      have hc := ih h
      simp [translateConcept, evalC, evalK, (hc x).1, (hc x).2]
  | conj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateConcept, evalC, evalK, (hc x).1, (hc x).2,
        (hd x).1, (hd x).2]
  | disj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateConcept, evalC, evalK, (hc x).1, (hc x).2,
        (hd x).1, (hd x).2]
  | ex r c ih =>
      have hr : ∀ y z, J.roleValuation (r, .truth) y z →
          J.roleValuation (r, .meaningful) y z := by
        simpa [roleBridge, sentenceC, roleC] using
          h (roleBridge σ r) (by simp [conceptBridges])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [translateConcept, evalC, roleC, evalK, existsK_t, existsK_m]
      exact ⟨exists_congr (fun y => and_congr (propValue_truth _ _).symm (hc y).1),
        exists_congr (fun y => and_congr (propValue_meaningful _ _ (hr x y)).symm
          (hc y).2)⟩
  | all r c ih =>
      have hr : ∀ y z, J.roleValuation (r, .truth) y z →
          J.roleValuation (r, .meaningful) y z := by
        simpa [roleBridge, sentenceC, roleC] using
          h (roleBridge σ r) (by simp [conceptBridges])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp only [translateConcept, evalC, roleC, evalK, forallK_t, forallK_m]
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

private theorem translateInclusion_iff (J : CInterpretation σᵀ)
    (c d : 𝒞 σ) :
    (∀ q ∈ translateInclusion σ c d, sentenceC J q) ↔
      (∀ x, evalC J (translateConcept σ c).1 x →
        evalC J (translateConcept σ d).1 x) ∧
      ∃ x, evalC J (translateConcept σ c).2 x ∧
        evalC J (translateConcept σ d).2 x := by
  simp only [translateInclusion, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  rw [nonemptyAxiom_iff]
  rfl

theorem translateInclusionEncode (I : WKInterpretation σ) (c d : 𝒞 σ) :
    (∀ q ∈ translateInclusion σ c d, sentenceC (encodeWK I) q) ↔
      forallK (evalK I c) (evalK I d) = 𝔱 := by
  rw [translateInclusion_iff, forallK_t]
  exact and_congr
    (forall_congr' (fun x => imp_congr (translateConceptEncode I c x).1
      (translateConceptEncode I d x).1))
    (exists_congr (fun x => and_congr (translateConceptEncode I c x).2
      (translateConceptEncode I d x).2))

theorem decodeInclusionLocal (J : CInterpretation σᵀ)
    (c d : 𝒞 σ)
    (hc : ∀ q ∈ conceptBridges σ c, sentenceC J q)
    (hd : ∀ q ∈ conceptBridges σ d, sentenceC J q) :
    (∀ q ∈ translateInclusion σ c d, sentenceC J q) ↔
      forallK (evalK (decodeTarget J) c) (evalK (decodeTarget J) d) = 𝔱 := by
  rw [translateInclusion_iff, forallK_t]
  exact and_congr
    (forall_congr' (fun x => imp_congr (decodeConceptLocal J c hc x).1
      (decodeConceptLocal J d hd x).1))
    (exists_congr (fun x => and_congr (decodeConceptLocal J c hc x).2
      (decodeConceptLocal J d hd x).2))

theorem translateSentenceEncode (I : WKInterpretation σ) (s : Φ σ) :
    (∀ q ∈ translateSentence σ s, sentenceC (encodeWK I) q) ↔ satisfiesK I s := by
  cases s with
  | isa a c =>
      simp only [translateSentence, List.mem_singleton, forall_eq, sentenceC,
        satisfiesK, sentenceK]
      exact (translateConceptEncode I c (I.individualValuation a)).1
  | role a b r => simp [translateSentence, sentenceC, roleC, encodeWK, satisfiesK, sentenceK]
  | sub c d => exact translateInclusionEncode I c d
  | equiv c d =>
      simp only [translateSentence, allMemAppend, translateInclusionEncode,
        satisfiesK, sentenceK, andK_t]
  | rsub r s =>
      simp only [translateSentence, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      rw [overlapAxiom_iff]
      simp [sentenceC, roleC, encodeWK, satisfiesK, sentenceK,
        forallK_t, Prod.forall, Prod.exists]

theorem decodeSentenceLocal (J : CInterpretation σᵀ)
    (s : Φ σ)
    (h : ∀ q ∈ sentenceBridges σ s, sentenceC J q) :
    (∀ q ∈ translateSentence σ s, sentenceC J q) ↔ satisfiesK (decodeTarget J) s := by
  cases s with
  | isa a c =>
      simp only [translateSentence, List.mem_singleton, forall_eq, sentenceC,
        satisfiesK, sentenceK]
      exact (decodeConceptLocal J c h (J.individualValuation a)).1
  | role a b r =>
      simp [translateSentence, sentenceC, roleC, decodeTarget, satisfiesK, sentenceK]
  | sub c d =>
      exact decodeInclusionLocal J c d
        (fun q hq => h q (List.mem_append_left _ hq))
        (fun q hq => h q (List.mem_append_right _ hq))
  | equiv c d =>
      have hc : ∀ q ∈ conceptBridges σ c, sentenceC J q :=
        fun q hq => h q (List.mem_append_left _ hq)
      have hd : ∀ q ∈ conceptBridges σ d, sentenceC J q :=
        fun q hq => h q (List.mem_append_right _ hq)
      simp only [translateSentence, allMemAppend, decodeInclusionLocal J c d hc hd,
        decodeInclusionLocal J d c hd hc, satisfiesK, sentenceK, andK_t]
  | rsub r s =>
      have hr : ∀ x y, J.roleValuation (r, .truth) x y →
          J.roleValuation (r, .meaningful) x y := by
        simpa [roleBridge, sentenceC, roleC] using
          h (roleBridge σ r) (by simp [sentenceBridges])
      have hs : ∀ x y, J.roleValuation (s, .truth) x y →
          J.roleValuation (s, .meaningful) x y := by
        simpa [roleBridge, sentenceC, roleC] using
          h (roleBridge σ s) (by simp [sentenceBridges])
      simp only [translateSentence, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      rw [overlapAxiom_iff]
      simp [sentenceC, roleC, satisfiesK,
        sentenceK, forallK_t, Prod.forall, Prod.exists, decodeTarget,
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

theorem translateKBEncode (I : WKInterpretation σ) (Γ : List (Φ σ)) :
    (∀ q ∈ translateWK σ Γ, sentenceC (encodeWK I) q) ↔
      ∀ s ∈ Γ, satisfiesK I s := by
  simp only [translateWK, allMemFlatMap, translateSentenceEncode]

theorem encodedKBBridges (I : WKInterpretation σ) (Γ : List (Φ σ)) :
    ∀ q ∈ bridgesWK σ Γ, sentenceC (encodeWK I) q := by
  rw [bridgesWK, allMemFlatMap]
  exact fun s _ => encodedSentenceBridges I s

theorem decodeKBLocal (J : CInterpretation σᵀ)
    (Γ : List (Φ σ))
    (h : ∀ q ∈ bridgesWK σ Γ, sentenceC J q) :
    (∀ q ∈ translateWK σ Γ, sentenceC J q) ↔
      ∀ s ∈ Γ, satisfiesK (decodeTarget J) s := by
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
    have hparts := (allMemAppend (sentenceC J) _ _).mp hJ
    have hleft := (allMemAppend (sentenceC J) _ _).mp hparts.1
    apply (decodeKBLocal J Δ hparts.2).mpr
    exact h (decodeTarget J) ((decodeKBLocal J Γ hleft.2).mp hleft.1)
  · intro h I hI
    apply (translateKBEncode I Δ).mp
    apply h (encodeWK I)
    apply (allMemAppend (sentenceC (encodeWK I)) _ _).mpr
    refine ⟨?_, encodedKBBridges I Δ⟩
    exact (allMemAppend (sentenceC (encodeWK I)) _ _).mpr
      ⟨(translateKBEncode I Γ).mpr hI, encodedKBBridges I Γ⟩

/-! ## The composed AC translation -/

/-- Translate a source KB through WK into the derived classical signature. -/
def T (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ (targetSignature (wkSignature σ))) :=
  translateWK (wkSignature σ) (Γ.map (projectSentence σ))

/-- Bridges for the names used by the polarized source KB. -/
def B (σ : Signature) (Γ : List (Φ σ)) :
    List (Φᵁ (targetSignature (wkSignature σ))) :=
  bridgesWK (wkSignature σ) (Γ.map (projectSentence σ))

/-- AC entailment is exactly classical entailment of the translated KBs,
with the bridges of both KBs included among the premises. -/
theorem MainResult (σ : Signature) (Γ Δ : List (Φ σ)) :
    (Γ ⊨ᴬ Δ) ↔ ((T σ Γ ++ B σ Γ ++ B σ Δ) ⊨ᶜ T σ Δ) := by
  exact (entailmentA_iff_projectedWK Γ Δ).trans
    (entailmentK_iff_classical (Γ.map (projectSentence σ)) (Δ.map (projectSentence σ)))

end ALCHAC
