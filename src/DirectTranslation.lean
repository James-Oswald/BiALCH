import Mathlib

namespace DirectTranslation

-- Weak kleene truth values
inductive V3 where
| t
| e
| f
deriving DecidableEq, Repr

notation "𝔱" => V3.t
notation "𝔢" => V3.e
notation "𝔣" => V3.f

-- Finiteness of the weak kleene truth values
instance : Fintype V3 where
  elems := {.t, .e, .f}
  complete x := by cases x <;> tauto

-- Pairs of weak kleene truth values
abbrev V32 := V3 × V3

-- We can decide membership in a set of pairs
-- (needed so restricted Weak Kleene quantifiers are well defined)
noncomputable instance (X : Set V32) (x : V32) : Decidable (x ∈ X) :=
  Classical.propDecidable _

-- Weak kleene logical connectives
def negK : V3 → V3
| 𝔱 => 𝔣
| 𝔢 => 𝔢
| 𝔣 => 𝔱

def andK : V3 → V3 → V3
| 𝔢, _
| _, 𝔢 => 𝔢
| 𝔱, 𝔱 => 𝔱
| _, _ => 𝔣

def orK : V3 → V3 → V3
| 𝔢, _
| _, 𝔢 => 𝔢
| 𝔣, 𝔣 => 𝔣
| _, _ => 𝔱

prefix:70 "¬ₖ " => negK
infixl:70 " ∧ₖ " => andK
infixl:65 " ∨ₖ " => orK

/-- The paper's restricted existential quantifier, including its stated case order. -/
noncomputable def paperExists (X : Set V32) : V3 :=
  if H1: ⟨𝔱, 𝔱⟩ ∈ X then
    𝔱
  else if H2: ∀ x ∈ X, x.1 = 𝔢 ∨ x.2 = 𝔢 then
    𝔢
  else if H3: ⟨𝔱, 𝔱⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔣
  else by grind only -- Impossible case

/-- The paper's restricted universal quantifier, including its stated case order. -/
noncomputable def paperForall (X : Set V32) : V3 :=
  if H1: ⟨𝔱, 𝔣⟩ ∉ X ∧ ⟨𝔱, 𝔢⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔱
  else if H2: ∀ x ∈ X, x.1 = 𝔢 ∨ x.2 = 𝔢 then
    𝔢
  else if H3: (⟨𝔱, 𝔣⟩ ∈ X ∨ ⟨𝔱, 𝔢⟩ ∈ X) ∧ ∃ x ∈ X, x.1 ≠ 𝔢 ∧ x.2 ≠ 𝔢 then
    𝔣
  else by grind only

/-- Apply the paper's set-based quantifier to the indexed family of value pairs. -/
noncomputable def existsK {D : Type} (r c : D → V3) : V3 :=
  paperExists (Set.range (λ x => (r x, c x)))

noncomputable def forallK {D : Type} (r c : D → V3) : V3 :=
  paperForall (Set.range (λ x => (r x, c x)))

notation "∃ₖ[" r "]" c:75 => existsK r c
notation "∀ₖ[" r "]" c:75 => forallK r c

-- The following indexed-family characterizations are used only to state and
-- prove convenient truth/meaningfulness lemmas. The semantic operators above are
-- defined by the paper's set clauses.
private noncomputable def existsKIndexed {D : Type} (r c : D → V3) : V3 := by
  classical
  exact if ∃ x, r x = 𝔱 ∧ c x = 𝔱 then 𝔱
    else if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then 𝔣
    else 𝔢

private noncomputable def forallKIndexed {D : Type} (r c : D → V3) : V3 := by
  classical
  exact if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then
    if ∀ x, r x = 𝔱 → c x = 𝔱 then 𝔱 else 𝔣
    else 𝔢

private theorem existsKIndexed_paper {D} (r c : D → V3) :
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

private theorem forallKIndexed_paper {D} (r c : D → V3) :
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

private theorem existsKIndexed_t {D} (r c : D → V3) :
    existsKIndexed r c = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  classical
  unfold existsKIndexed
  split_ifs <;> simp_all

private theorem existsKIndexed_m {D} (r c : D → V3) :
    existsKIndexed r c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold existsKIndexed
  split_ifs <;> simp_all
  obtain ⟨x, hx, hy⟩ := ‹∃ x, r x = 𝔱 ∧ c x = 𝔱›
  exact ⟨x, by simp [hx], by simp [hy]⟩

private theorem forallKIndexed_t {D} (r c : D → V3) :
    forallKIndexed r c = 𝔱 ↔ (∀ x, r x = 𝔱 → c x = 𝔱) ∧
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallKIndexed
  split_ifs <;> simp_all

private theorem forallKIndexed_m {D} (r c : D → V3) :
    forallKIndexed r c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallKIndexed
  split_ifs <;> simp_all

@[simp]
theorem negK_t (v : V3) : ¬ₖv = 𝔱 ↔ v ≠ 𝔢 ∧ v ≠ 𝔱 := by
  cases v <;> decide

@[simp]
theorem negK_m (v : V3) : ¬ₖv ≠ 𝔢 ↔ v ≠ 𝔢 := by
  cases v <;> decide

@[simp]
theorem andK_t (v w : V3) : v ∧ₖ w = 𝔱 ↔ v = 𝔱 ∧ w = 𝔱 := by
  cases v <;> cases w <;> decide

@[simp]
theorem andK_m (v w : V3) : v ∧ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp]
theorem orK_t (v w : V3) : v ∨ₖ w = 𝔱 ↔ (v = 𝔱 ∨ w = 𝔱) ∧ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp]
theorem orK_m (v w : V3) : v ∨ₖ w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp]
theorem existsK_t {D} (r c : D → V3) :
    ∃ₖ[r] c = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  change paperExists (Set.range (λ x => (r x, c x))) = 𝔱 ↔ _
  rw [← existsKIndexed_paper]
  exact existsKIndexed_t r c

@[simp]
theorem existsK_m {D} (r c : D → V3) :
    ∃ₖ[r] c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  change paperExists (Set.range (λ x => (r x, c x)) ) ≠ 𝔢 ↔ _
  rw [← existsKIndexed_paper]
  exact existsKIndexed_m r c

@[simp]
theorem forallK_t {D} (r c : D → V3) :
    ∀ₖ[r] c = 𝔱 ↔ (∀ x, r x = 𝔱 → c x = 𝔱) ∧
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  change paperForall (Set.range (λ x => (r x, c x))) = 𝔱 ↔ _
  rw [← forallKIndexed_paper]
  exact forallKIndexed_t r c

@[simp]
theorem forallK_m {D} (r c : D → V3) :
    ∀ₖ[r] c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  change paperForall (Set.range (λ x => (r x, c x))) ≠ 𝔢 ↔ _
  rw [← forallKIndexed_paper]
  exact forallKIndexed_m r c

theorem existsK_paper {D} (r c : D → V3) :
existsK r c = paperExists (Set.range (λ x => (r x, c x))) := by
  rfl

theorem forallK_paper {D} (r c : D → V3) :
forallK r c = paperForall (Set.range (λ x => (r x, c x))) := by
  rfl

-- AC operators

def negA (v : V32) : V32 := (v.2, v.1)
def andA (v w : V32) : V32 := (v.1 ∧ₖ w.1, v.2 ∨ₖ w.2)
def orA (v w : V32) : V32 := (v.1 ∨ₖ w.1, v.2 ∧ₖ w.2)

prefix:70 "∼ₐ " => negA
infixl:70 " ∧ₐ " => andA
infixl:65 " ∨ₐ " => orA

noncomputable def existsA {D : Type} (r c : D → V32) : V32 :=
  (∃ₖ[(fun x => (r x).1)] (fun x => (c x).1),
   ∀ₖ[(fun x => (r x).1)] (fun x => (c x).2))

noncomputable def forallA {D : Type} (r c : D → V32) : V32 :=
  (∀ₖ[(fun x => (r x).1)] (fun x => (c x).1),
   ∃ₖ[(fun x => (r x).1)] (fun x => (c x).2))

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

inductive Concept (σ : Signature) where
| top
| bot
| atom : σ.Nc → Concept σ
| neg : Concept σ → Concept σ
| conj : Concept σ → Concept σ → Concept σ
| disj : Concept σ → Concept σ → Concept σ
| ex : σ.Nr → Concept σ → Concept σ
| all : σ.Nr → Concept σ → Concept σ
deriving Repr

inductive Sentence (σ : Signature) where
| isa : σ.Ni → Concept σ → Sentence σ
| edge : σ.Ni → σ.Ni → σ.Nr → Sentence σ
| sub : Concept σ → Concept σ → Sentence σ
| equiv : Concept σ → Concept σ → Sentence σ
| rsub : σ.Nr → σ.Nr → Sentence σ
deriving Repr

variable {σ : Signature}

instance : Top (Concept σ) := ⟨.top⟩
instance : Bot (Concept σ) := ⟨.bot⟩
instance : Coe σ.Nc (Concept σ) := ⟨Concept.atom⟩
notation "⟦" a "⟧ₜ" => Concept.atom a
infixl:70 " ⊓ₜ " => Concept.conj
infixl:65 " ⊔ₜ " => Concept.disj
notation "¬ₜ " c:75 => Concept.neg c
notation "∃[" r "]" c:75 => Concept.ex r c
notation "∀[" r "]" c:75 => Concept.all r c

notation a " :ₐ " c:50 => Sentence.isa a c
notation "(" a ", " b ")" " :ᵣ " r:50 => Sentence.edge a b r
infix:50 " ⊑ " => Sentence.sub
infix:50 " ≡ " => Sentence.equiv
infix:50 " ⊑ᵣ " => Sentence.rsub

example (A B : σ.Nc) (r : σ.Nr) : Concept σ :=
  A ⊓ₜ (∃[r] B) ⊓ₜ (∀[r] ¬ₜ A)

example (a : σ.Ni) (A : σ.Nc) (r : σ.Nr) : Sentence σ :=
  (a :ₐ (A ⊓ₜ (∃[r] A)))

example (a b : σ.Ni) (r : σ.Nr) : Sentence σ :=
  (a, b) :ᵣ r

example (r s : σ.Nr) : Sentence σ := r ⊑ᵣ s

/-- Nonempty domains; no unique-name assumption. -/
structure Interpretation (σ : Signature) (V : Type) where
  D : Type
  inhabited : Nonempty D
  individual : σ.Ni → D
  atom : σ.Nc → D → V
  role : σ.Nr → D → D → V

-- Classical Semantics

-- Concept evaluation function for classical semantics
def evalC (J : Interpretation σ Prop) : Concept σ → J.D → Prop
| ⊤, _ => True
| ⊥, _ => False
| ⟦a⟧ₜ, x => J.atom a x
| ¬ₜc, x => ¬ evalC J c x
| c ⊓ₜ d, x => evalC J c x ∧ evalC J d x
| c ⊔ₜ d, x => evalC J c x ∨ evalC J d x
| ∃[r] c, x => ∃ y, J.role r x y ∧ evalC J c y
| ∀[r] c, x => ∀ y, J.role r x y → evalC J c y


/-- Classical sentence semantics, with no additional query constructors. -/
def sentenceC (I : Interpretation σ Prop) : Sentence σ → Prop
| a :ₐ c => evalC I c (I.individual a)
| (a, b) :ᵣ r => I.role r (I.individual a) (I.individual b)
| c ⊑ d => ∀ x, evalC I c x → evalC I d x
| c ≡ d => ∀ x, evalC I c x ↔ evalC I d x
| r ⊑ᵣ s => ∀ x y, I.role r x y → I.role s x y

notation  I "⊨ᶜₘ " S => sentenceC I S

def entailmentC (Γ Δ: List (Sentence σ)) : Prop :=
  ∀ I, ∀ φ ∈ Δ, (∀ ψ ∈ Γ, I ⊨ᶜₘ ψ) → I ⊨ᶜₘ φ

notation  Γ " ⊨ᶜ " Δ => entailmentC Γ Δ

/-
Concept evaluation function for Kleene semantics.
-/
noncomputable def evalK (I : Interpretation σ V3) : Concept σ → I.D → V3
| ⊤, _ => 𝔱
| ⊥, _ => 𝔣
| ⟦a⟧ₜ, x => I.atom a x
| ¬ₜ c, x => ¬ₖ (evalK I c x)
| c ⊓ₜ d, x => evalK I c x ∧ₖ evalK I d x
| c ⊔ₜ d, x => evalK I c x ∨ₖ evalK I d x
| ∃[r] c, x => ∃ₖ[I.role r x] (evalK I c)
| ∀[r] c, x => ∀ₖ[I.role r x] (evalK I c)

noncomputable def sentenceK (I : Interpretation σ V3) : Sentence σ → V3
| a :ₐ c => evalK I c (I.individual a)
| (a, b) :ᵣ r => I.role r (I.individual a) (I.individual b)
| c ⊑ d => ∀ₖ[evalK I c] (evalK I d)
| c ≡ d => (∀ₖ[evalK I c] (evalK I d)) ∧ₖ (∀ₖ[evalK I d] (evalK I c))
| r ⊑ᵣ s => ∀ₖ[(λ p : I.D × I.D => I.role r p.1 p.2)] (λ p => I.role s p.1 p.2)

def satisfiesK (I : Interpretation σ V3) (φ : Sentence σ) : Prop :=
  (sentenceK I φ) = 𝔱

notation  I "⊨ᴷₘ " S => satisfiesK I S

def entailmentK (Γ Δ : List (Sentence σ)) : Prop :=
  ∀ I, ∀ φ ∈ Δ, (∀ ψ ∈ Γ, I ⊨ᴷₘ ψ) → I ⊨ᴷₘ φ

notation  Γ " ⊨ᴷ " Δ => entailmentK Γ Δ

-- AC entailment

structure ACInterpretation (σ : Signature) extends Interpretation σ V32 where
  topNegative : D → V3
  bottomPositive : D → V3

noncomputable def evalA (I : ACInterpretation σ) : Concept σ → I.D → V32
| ⊤, x => (𝔱, I.topNegative x)
| ⊥, x => (I.bottomPositive x, 𝔱)
| ⟦a⟧ₜ, x => I.atom a x
| ¬ₜ c, x => ∼ₐ(evalA I c x)
| c ⊓ₜ d, x => evalA I c x ∧ₐ evalA I d x
| c ⊔ₜ d, x => evalA I c x ∨ₐ evalA I d x
| ∃[r] c, x => ∃ₐ[I.role r x] (evalA I c)
| ∀[r] c, x => ∀ₐ[I.role r x] (evalA I c)

noncomputable def sentenceA (I : ACInterpretation σ) : Sentence σ → V32
| a :ₐ c => evalA I c (I.individual a)
| (a, b) :ᵣ r => I.role r (I.individual a) (I.individual b)
| c ⊑ d => ∀ₐ[evalA I c] (evalA I d)
| c ≡ d => (∀ₐ[evalA I c] (evalA I d)) ∧ₐ
    (∀ₐ[evalA I d] (evalA I c))
| r ⊑ᵣ s => ∀ₐ[(λ p : I.D × I.D => I.role r p.1 p.2)]
    (λ p => I.role s p.1 p.2)

def satisfiesA (I : ACInterpretation σ) (φ : Sentence σ) : Prop :=
  (sentenceA I φ).1 = 𝔱

notation  I "⊨ᴬₘ " S => satisfiesA I S

def entailmentA (Γ Δ : List (Sentence σ)) : Prop :=
  ∀ I, ∀ φ ∈ Δ, (∀ ψ ∈ Γ, I ⊨ᴬₘ ψ) → I ⊨ᴬₘ φ

notation  Γ " ⊨ᴬ " Δ => entailmentA Γ Δ

/-! ## Executable target language and compiler -/

inductive Side where
| positive
| negative
deriving DecidableEq, Repr

inductive ACAtom (Nc : Type) where
| signed : Nc → Side → ACAtom Nc
| topNegative
| bottomPositive
deriving Repr

def wkSignature (σ : Signature) : Signature where
  Nc := ACAtom σ.Nc
  Nr := σ.Nr
  Ni := σ.Ni

def polarize (σ : Signature) : Concept σ → Side → Concept (wkSignature σ)
| .top, .positive => .top
| .top, .negative => .atom .topNegative
| .bot, .positive => .atom .bottomPositive
| .bot, .negative => .top
| .atom a, side => .atom (.signed a side)
| .neg c, .positive => polarize σ c .negative
| .neg c, .negative => polarize σ c .positive
| .conj c d, .positive => .conj (polarize σ c .positive) (polarize σ d .positive)
| .conj c d, .negative => .disj (polarize σ c .negative) (polarize σ d .negative)
| .disj c d, .positive => .disj (polarize σ c .positive) (polarize σ d .positive)
| .disj c d, .negative => .conj (polarize σ c .negative) (polarize σ d .negative)
| .ex r c, .positive => .ex r (polarize σ c .positive)
| .ex r c, .negative => .all r (polarize σ c .negative)
| .all r c, .positive => .all r (polarize σ c .positive)
| .all r c, .negative => .ex r (polarize σ c .negative)

def projectSentence (σ : Signature) : Sentence σ → Sentence (wkSignature σ)
| .isa a c => .isa a (polarize σ c .positive)
| .edge a b r => .edge a b r
| .sub c d => .sub (polarize σ c .positive) (polarize σ d .positive)
| .equiv c d => .equiv (polarize σ c .positive) (polarize σ d .positive)
| .rsub r s => .rsub r s

inductive Bit where
| truth
| meaningful
deriving DecidableEq, Repr

def targetSignature (σ : Signature) : Signature where
  Nc := σ.Nc × Bit
  Nr := σ.Nr × Bit
  Ni := σ.Ni

def encodeWK (σ : Signature) (I : Interpretation σ V3) :
    Interpretation (targetSignature σ) Prop where
  D := I.D
  inhabited := I.inhabited
  individual := I.individual
  atom := fun (a, b) x => match b with
    | .truth => I.atom a x = 𝔱
    | .meaningful => I.atom a x ≠ 𝔢
  role := fun (r, b) x y => match b with
    | .truth => I.role r x y = 𝔱
    | .meaningful => I.role r x y ≠ 𝔢

noncomputable def propValue (truth meaningful : Prop) : V3 := by
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

noncomputable def decodeTarget (σ : Signature)
    (J : Interpretation (targetSignature σ) Prop) : Interpretation σ V3 where
  D := J.D
  inhabited := J.inhabited
  individual := J.individual
  atom := fun a x => propValue (J.atom (a, .truth) x) (J.atom (a, .meaningful) x)
  role := fun r x y => propValue (J.role (r, .truth) x y) (J.role (r, .meaningful) x y)

inductive Query (σ : Signature) where
| sentence : Sentence σ → Query σ
| some : Concept σ → Query σ
| overlap : σ.Nr → σ.Nr → Query σ
| both : Query σ → Query σ → Query σ

def holdsQuery (I : Interpretation σ Prop) : Query σ → Prop
| .sentence s => sentenceC I s
| .some c => ∃ x, evalC I c x
| .overlap r s => ∃ x y, I.role r x y ∧ I.role s x y
| .both p q => holdsQuery I p ∧ holdsQuery I q

def queryEntailment (P : List (Query σ)) (Q : List (Query σ)) : Prop :=
  ∀ I, (∀ p ∈ P, holdsQuery I p) → ∀ q ∈ Q, holdsQuery I q

structure ClassicalProblem (σ : Signature) where
  premises : List (Query (targetSignature σ))
  conclusions : List (Query (targetSignature σ))

def problemEntailment (P : ClassicalProblem σ) : Prop :=
  queryEntailment P.premises P.conclusions

def translateConcept (σ : Signature) : Concept σ →
    Concept (targetSignature σ) × Concept (targetSignature σ)
| .top => (.top, .top)
| .bot => (.bot, .top)
| .atom a => (.atom (a, .truth), .atom (a, .meaningful))
| .neg c =>
    let (t, m) := translateConcept σ c
    (.conj m (.neg t), m)
| .conj c d =>
    let (t, m) := translateConcept σ c
    let (u, n) := translateConcept σ d
    (.conj t u, .conj m n)
| .disj c d =>
    let (t, m) := translateConcept σ c
    let (u, n) := translateConcept σ d
    (.conj (.disj t u) (.conj m n), .conj m n)
| .ex r c =>
    let (t, m) := translateConcept σ c
    (.ex (r, .truth) t, .ex (r, .meaningful) m)
| .all r c =>
    let (t, m) := translateConcept σ c
    (.conj (.all (r, .truth) t) (.ex (r, .meaningful) m),
      .ex (r, .meaningful) m)

def translateInclusion (σ : Signature) (c d : Concept σ) : Query (targetSignature σ) :=
  let (ct, cm) := translateConcept σ c
  let (dt, dm) := translateConcept σ d
  .both (.sentence (.sub ct dt)) (.some (.conj cm dm))

def translateSentence (σ : Signature) : Sentence σ → Query (targetSignature σ)
| .isa a c => .sentence (.isa a (translateConcept σ c).1)
| .edge a b r => .sentence (.edge a b (r, .truth))
| .sub c d => translateInclusion σ c d
| .equiv c d => .both (translateInclusion σ c d) (translateInclusion σ d c)
| .rsub r s =>
    .both (.sentence (.rsub (r, .truth) (s, .truth)))
      (.overlap (r, .meaningful) (s, .meaningful))

def atomBridge (σ : Signature) (a : σ.Nc) : Query (targetSignature σ) :=
  .sentence (.sub (.atom (a, .truth)) (.atom (a, .meaningful)))

def roleBridge (σ : Signature) (r : σ.Nr) : Query (targetSignature σ) :=
  .sentence (.rsub (r, .truth) (r, .meaningful))

theorem encodedAtomBridge (σ : Signature) (I : Interpretation σ V3)
    (a : σ.Nc) : holdsQuery (encodeWK σ I) (atomBridge σ a) := by
  simp [holdsQuery, atomBridge, sentenceC, evalC, encodeWK]
  intro x hx
  cases hv : I.atom a x <;> simp_all

theorem encodedRoleBridge (σ : Signature) (I : Interpretation σ V3)
    (r : σ.Nr) : holdsQuery (encodeWK σ I) (roleBridge σ r) := by
  simp [holdsQuery, roleBridge, sentenceC, encodeWK]
  intro x y hx
  cases hv : I.role r x y <;> simp_all

def conceptBridges (σ : Signature) : Concept σ → List (Query (targetSignature σ))
| .top | .bot => []
| .atom a => [atomBridge σ a]
| .neg c => conceptBridges σ c
| .conj c d | .disj c d => conceptBridges σ c ++ conceptBridges σ d
| .ex r c | .all r c => roleBridge σ r :: conceptBridges σ c

def sentenceBridges (σ : Signature) : Sentence σ → List (Query (targetSignature σ))
| .isa _ c => conceptBridges σ c
| .edge _ _ r => [roleBridge σ r]
| .sub c d | .equiv c d => conceptBridges σ c ++ conceptBridges σ d
| .rsub r s => [roleBridge σ r, roleBridge σ s]

def compileWK (σ : Signature) (Γ Δ : List (Sentence σ)) : ClassicalProblem σ where
  premises := (Γ ++ Δ).flatMap (sentenceBridges σ) ++ Γ.map (translateSentence σ)
  conclusions := Δ.map (translateSentence σ)

def compileAC (σ : Signature) (Γ Δ : List (Sentence σ)) :
    ClassicalProblem (wkSignature σ) :=
  compileWK (wkSignature σ) (Γ.map (projectSentence σ)) (Δ.map (projectSentence σ))

def coordinate (v : V32) : Side → V3
| .positive => v.1
| .negative => v.2

def acToWK (σ : Signature) (I : ACInterpretation σ) :
    Interpretation (wkSignature σ) V3 where
  D := I.D
  inhabited := I.inhabited
  individual := I.individual
  atom := fun a x => match a with
    | .signed a side => coordinate (I.atom a x) side
    | .topNegative => I.topNegative x
    | .bottomPositive => I.bottomPositive x
  role := fun r x y => (I.role r x y).1

abbrev wkToAC (σ : Signature) (I : Interpretation (wkSignature σ) V3) :
    ACInterpretation σ where
  D := I.D
  inhabited := I.inhabited
  individual := I.individual
  atom := fun a x => (I.atom (.signed a .positive) x, I.atom (.signed a .negative) x)
  role := fun r x y => (I.role r x y, 𝔢)
  topNegative := fun x => I.atom .topNegative x
  bottomPositive := fun x => I.atom .bottomPositive x

theorem acToWK_wkToAC (σ : Signature) (I : Interpretation (wkSignature σ) V3) :
    acToWK σ (wkToAC σ I) = I := by
  cases I with
  | mk D inhabited individual atom role =>
      simp only [acToWK, wkToAC, coordinate]
      rw [Interpretation.mk.injEq]
      constructor
      · rfl
      · constructor
        · exact HEq.rfl
        · constructor
          · have hfun : (fun a x =>
                match a with
                | .signed a side =>
                    match side with
                    | .positive => atom (.signed a .positive) x
                    | .negative => atom (.signed a .negative) x
                | .topNegative => atom .topNegative x
                | .bottomPositive => atom .bottomPositive x) = atom := by
              funext a x
              cases a with
              | signed a side => cases side <;> rfl
              | topNegative => rfl
              | bottomPositive => rfl
            exact hfun ▸ HEq.rfl
          · exact HEq.rfl

theorem acConceptCoordinates (σ : Signature) (I : ACInterpretation σ)
    (c : Concept σ) (side : Side) (x : I.D) :
    evalK (acToWK σ I) (polarize σ c side) x = coordinate (evalA I c x) side := by
  induction c generalizing side x with
  | top => cases side <;> rfl
  | bot => cases side <;> rfl
  | atom a => cases side <;> rfl
  | neg c ih =>
      cases side with
      | positive => exact ih .negative x
      | negative => exact ih .positive x
  | conj c d ihc ihd =>
      cases side <;>
        simp [polarize, evalK, evalA, coordinate, andA, ihc, ihd]
  | disj c d ihc ihd =>
      cases side <;>
        simp [polarize, evalK, evalA, coordinate, orA, ihc, ihd]
  | ex r c ih =>
      cases side with
      | positive => exact congrArg₂ existsK rfl (funext (ih .positive))
      | negative => exact congrArg₂ forallK rfl (funext (ih .negative))
  | all r c ih =>
      cases side with
      | positive => exact congrArg₂ forallK rfl (funext (ih .positive))
      | negative => exact congrArg₂ existsK rfl (funext (ih .negative))

theorem acSentenceSupport (σ : Signature) (I : ACInterpretation σ)
    (s : Sentence σ) :
    sentenceK (acToWK σ I) (projectSentence σ s) = (sentenceA I s).1 := by
  have hc (c : Concept σ) :
      evalK (acToWK σ I) (polarize σ c .positive) = fun x => (evalA I c x).1 :=
    funext (acConceptCoordinates σ I c .positive)
  cases s <;>
    simp only [projectSentence, sentenceK, sentenceA, forallA, andA, hc] <;> rfl

theorem translateConceptEncode (σ : Signature) (I : Interpretation σ V3)
    (c : Concept σ) (x : I.D) :
    (evalC (encodeWK σ I) (translateConcept σ c).1 x ↔ evalK I c x = 𝔱) ∧
    (evalC (encodeWK σ I) (translateConcept σ c).2 x ↔ evalK I c x ≠ 𝔢) := by
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
      cases htc : translateConcept σ c with
      | mk tc mc =>
        have ht (y : I.D) : evalC (encodeWK σ I) tc y ↔ evalK I c y = 𝔱 := by
          simpa [htc] using (ih y).1
        have hm (y : I.D) : evalC (encodeWK σ I) mc y ↔ evalK I c y ≠ 𝔢 := by
          simpa [htc] using (ih y).2
        simp only [translateConcept, htc, evalC, evalK]
        constructor
        · rw [existsK_t]
          constructor
          · rintro ⟨y, hr, hc⟩
            exact ⟨y, hr, (ht y).mp hc⟩
          · rintro ⟨y, hr, hc⟩
            exact ⟨y, hr, (ht y).mpr hc⟩
        · rw [existsK_m]
          constructor
          · rintro ⟨y, hr, hc⟩
            exact ⟨y, hr, (hm y).mp hc⟩
          · rintro ⟨y, hr, hc⟩
            exact ⟨y, hr, (hm y).mpr hc⟩
  | all r c ih =>
      cases htc : translateConcept σ c with
      | mk tc mc =>
        have ht (y : I.D) : evalC (encodeWK σ I) tc y ↔ evalK I c y = 𝔱 := by
          simpa [htc] using (ih y).1
        have hm (y : I.D) : evalC (encodeWK σ I) mc y ↔ evalK I c y ≠ 𝔢 := by
          simpa [htc] using (ih y).2
        simp only [translateConcept, htc, evalC, evalK]
        constructor
        · rw [forallK_t]
          constructor
          · rintro ⟨hall, ⟨y, hr, hc⟩⟩
            exact ⟨(fun z hz => (ht z).mp (hall z hz)),
              ⟨y, hr, (hm y).mp hc⟩⟩
          · rintro ⟨hall, ⟨y, hr, hc⟩⟩
            exact ⟨(fun z hz => (ht z).mpr (hall z hz)),
              ⟨y, hr, (hm y).mpr hc⟩⟩
        · rw [forallK_m]
          constructor
          · rintro ⟨y, hr, hc⟩
            exact ⟨y, hr, (hm y).mp hc⟩
          · rintro ⟨y, hr, hc⟩
            exact ⟨y, hr, (hm y).mpr hc⟩

theorem translateSentenceEncode (σ : Signature) (I : Interpretation σ V3)
    (s : Sentence σ) :
    holdsQuery (encodeWK σ I) (translateSentence σ s) ↔ sentenceK I s = 𝔱 := by
  cases s with
  | isa a c =>
      simpa [translateSentence, holdsQuery, sentenceC, sentenceK, encodeWK] using
        (translateConceptEncode σ I c (I.individual a)).1
  | edge a b r =>
      simp [translateSentence, holdsQuery, sentenceC, sentenceK, encodeWK]
  | sub c d =>
      have hc := fun x => translateConceptEncode σ I c x
      have hd := fun x => translateConceptEncode σ I d x
      change
        ((∀ x, evalC (encodeWK σ I) (translateConcept σ c).1 x →
            evalC (encodeWK σ I) (translateConcept σ d).1 x) ∧
          ∃ x, evalC (encodeWK σ I) (translateConcept σ c).2 x ∧
            evalC (encodeWK σ I) (translateConcept σ d).2 x) ↔
          (∀ₖ[evalK I c] (evalK I d)) = 𝔱
      rw [forallK_t]
      constructor
      · rintro ⟨hsub, ⟨x, hcm, hdm⟩⟩
        exact ⟨(fun y hy => (hd y).1.mp (hsub y ((hc y).1.mpr hy))),
          ⟨x, (hc x).2.mp hcm, (hd x).2.mp hdm⟩⟩
      · rintro ⟨hsub, ⟨x, hcm, hdm⟩⟩
        exact ⟨(fun y hy => (hd y).1.mpr (hsub y ((hc y).1.mp hy))),
          ⟨x, (hc x).2.mpr hcm, (hd x).2.mpr hdm⟩⟩
  | equiv c d =>
      have hc := fun x => translateConceptEncode σ I c x
      have hd := fun x => translateConceptEncode σ I d x
      change
        (((∀ x, evalC (encodeWK σ I) (translateConcept σ c).1 x →
              evalC (encodeWK σ I) (translateConcept σ d).1 x) ∧
            ∃ x, evalC (encodeWK σ I) (translateConcept σ c).2 x ∧
              evalC (encodeWK σ I) (translateConcept σ d).2 x) ∧
          ((∀ x, evalC (encodeWK σ I) (translateConcept σ d).1 x →
              evalC (encodeWK σ I) (translateConcept σ c).1 x) ∧
            ∃ x, evalC (encodeWK σ I) (translateConcept σ d).2 x ∧
              evalC (encodeWK σ I) (translateConcept σ c).2 x)) ↔
          ((∀ₖ[evalK I c] (evalK I d)) ∧ₖ (∀ₖ[evalK I d] (evalK I c))) = 𝔱
      rw [andK_t, forallK_t, forallK_t]
      constructor
      · rintro ⟨⟨hsub₁, ⟨x, hcm, hdm⟩⟩, ⟨hsub₂, ⟨y, hdm', hcm'⟩⟩⟩
        exact ⟨⟨(fun z hz => (hd z).1.mp (hsub₁ z ((hc z).1.mpr hz))),
            ⟨x, (hc x).2.mp hcm, (hd x).2.mp hdm⟩⟩,
          ⟨(fun z hz => (hc z).1.mp (hsub₂ z ((hd z).1.mpr hz))),
            ⟨y, (hd y).2.mp hdm', (hc y).2.mp hcm'⟩⟩⟩
      · rintro ⟨⟨hsub₁, ⟨x, hcm, hdm⟩⟩, ⟨hsub₂, ⟨y, hdm', hcm'⟩⟩⟩
        exact ⟨⟨(fun z hz => (hd z).1.mpr (hsub₁ z ((hc z).1.mp hz))),
            ⟨x, (hc x).2.mpr hcm, (hd x).2.mpr hdm⟩⟩,
          ⟨(fun z hz => (hc z).1.mpr (hsub₂ z ((hd z).1.mp hz))),
            ⟨y, (hd y).2.mpr hdm', (hc y).2.mpr hcm'⟩⟩⟩
  | rsub r s =>
      simp [translateSentence, holdsQuery, sentenceC, sentenceK, encodeWK, forallK_t]

theorem encodedConceptBridgesHold (σ : Signature) (I : Interpretation σ V3)
    (c : Concept σ) :
    ∀ q ∈ conceptBridges σ c, holdsQuery (encodeWK σ I) q := by
  induction c with
  | top | bot => simp [conceptBridges]
  | atom a =>
      intro q hq
      simp only [conceptBridges, List.mem_singleton] at hq
      subst q
      exact encodedAtomBridge σ I a
  | neg c ih => exact ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      intro q hq
      simp only [conceptBridges, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ihc q hq
      · exact ihd q hq
  | ex r c ih | all r c ih =>
      intro q hq
      simp only [conceptBridges, List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        exact encodedRoleBridge σ I r
      · exact ih q hq

theorem encodedBridgesHold (σ : Signature) (I : Interpretation σ V3)
    (s : Sentence σ) :
    ∀ q ∈ sentenceBridges σ s, holdsQuery (encodeWK σ I) q := by
  cases s with
  | isa a c => exact encodedConceptBridgesHold σ I c
  | edge a b r =>
      intro q hq
      simp only [sentenceBridges, List.mem_singleton] at hq
      subst q
      exact encodedRoleBridge σ I r
  | sub c d | equiv c d =>
      intro q hq
      simp only [sentenceBridges, List.mem_append] at hq
      rcases hq with hq | hq
      · exact encodedConceptBridgesHold σ I c q hq
      · exact encodedConceptBridgesHold σ I d q hq
  | rsub r s =>
      intro q hq
      simp only [sentenceBridges, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact encodedRoleBridge σ I _

theorem decodeConceptLocal (σ : Signature)
    (J : Interpretation (targetSignature σ) Prop) (c : Concept σ)
    (h : ∀ q ∈ conceptBridges σ c, holdsQuery J q) (x : J.D) :
    (evalC J (translateConcept σ c).1 x ↔ evalK (decodeTarget σ J) c x = 𝔱) ∧
    (evalC J (translateConcept σ c).2 x ↔ evalK (decodeTarget σ J) c x ≠ 𝔢) := by
  induction c generalizing x with
  | top => simp [translateConcept, evalC, evalK]
  | bot => simp [translateConcept, evalC, evalK]
  | atom a =>
      have ha : ∀ y, J.atom (a, .truth) y → J.atom (a, .meaningful) y := by
        have hb := h (atomBridge σ a) (by simp [conceptBridges, atomBridge])
        simpa [holdsQuery, atomBridge, sentenceC, evalC] using hb
      change (J.atom (a, .truth) x ↔
          propValue (J.atom (a, .truth) x) (J.atom (a, .meaningful) x) = 𝔱) ∧
        (J.atom (a, .meaningful) x ↔
          propValue (J.atom (a, .truth) x) (J.atom (a, .meaningful) x) ≠ 𝔢)
      exact ⟨(propValue_truth _ _).symm,
        (propValue_meaningful _ _ (ha x)).symm⟩
  | neg c ih =>
      have hc := ih h
      simp [translateConcept, evalC, evalK, (hc x).1, (hc x).2]
  | conj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateConcept, evalC, evalK, (hc x).1, (hc x).2, (hd x).1, (hd x).2]
  | disj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateConcept, evalC, evalK, (hc x).1, (hc x).2, (hd x).1, (hd x).2]
  | ex r c ih =>
      have hr : ∀ y z, J.role (r, .truth) y z → J.role (r, .meaningful) y z := by
        have hb := h (roleBridge σ r) (by simp [conceptBridges, roleBridge])
        simpa [holdsQuery, roleBridge, sentenceC] using hb
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [translateConcept, evalC, evalK, decodeTarget, fun y => (hc y).1,
        fun y => (hc y).2,
        fun y z => propValue_meaningful _ _ (hr y z)]
  | all r c ih =>
      have hr : ∀ y z, J.role (r, .truth) y z → J.role (r, .meaningful) y z := by
        have hb := h (roleBridge σ r) (by simp [conceptBridges, roleBridge])
        simpa [holdsQuery, roleBridge, sentenceC] using hb
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [translateConcept, evalC, evalK, decodeTarget, forallK_t, forallK_m,
        fun y => (hc y).1, fun y => (hc y).2,
        fun y z => propValue_meaningful _ _ (hr y z)]

theorem decodeSentenceLocal (σ : Signature)
    (J : Interpretation (targetSignature σ) Prop) (s : Sentence σ)
    (h : ∀ q ∈ sentenceBridges σ s, holdsQuery J q) :
    holdsQuery J (translateSentence σ s) ↔ sentenceK (decodeTarget σ J) s = 𝔱 := by
  cases s with
  | isa a c =>
      exact (decodeConceptLocal σ J c h (J.individual a)).1
  | edge a b r =>
      simp [translateSentence, holdsQuery, sentenceC, sentenceK, decodeTarget]
  | sub c d =>
      have hc := decodeConceptLocal σ J c (fun q hq => h q (List.mem_append_left _ hq))
      have hd := decodeConceptLocal σ J d (fun q hq => h q (List.mem_append_right _ hq))
      change
        ((∀ x, evalC J (translateConcept σ c).1 x →
            evalC J (translateConcept σ d).1 x) ∧
          ∃ x, evalC J (translateConcept σ c).2 x ∧
            evalC J (translateConcept σ d).2 x) ↔
          (∀ₖ[evalK (decodeTarget σ J) c] (evalK (decodeTarget σ J) d)) = 𝔱
      rw [forallK_t]
      constructor
      · rintro ⟨hsub, ⟨x, hcm, hdm⟩⟩
        exact ⟨(fun y hy => (hd y).1.mp (hsub y ((hc y).1.mpr hy))),
          ⟨x, (hc x).2.mp hcm, (hd x).2.mp hdm⟩⟩
      · rintro ⟨hsub, ⟨x, hcm, hdm⟩⟩
        exact ⟨(fun y hy => (hd y).1.mpr (hsub y ((hc y).1.mp hy))),
          ⟨x, (hc x).2.mpr hcm, (hd x).2.mpr hdm⟩⟩
  | equiv c d =>
      have hc := decodeConceptLocal σ J c (fun q hq => h q (List.mem_append_left _ hq))
      have hd := decodeConceptLocal σ J d (fun q hq => h q (List.mem_append_right _ hq))
      change
        (((∀ x, evalC J (translateConcept σ c).1 x →
              evalC J (translateConcept σ d).1 x) ∧
            ∃ x, evalC J (translateConcept σ c).2 x ∧
              evalC J (translateConcept σ d).2 x) ∧
          ((∀ x, evalC J (translateConcept σ d).1 x →
              evalC J (translateConcept σ c).1 x) ∧
            ∃ x, evalC J (translateConcept σ d).2 x ∧
              evalC J (translateConcept σ c).2 x)) ↔
          ((∀ₖ[evalK (decodeTarget σ J) c] (evalK (decodeTarget σ J) d)) ∧ₖ
            (∀ₖ[evalK (decodeTarget σ J) d] (evalK (decodeTarget σ J) c))) = 𝔱
      rw [andK_t, forallK_t, forallK_t]
      constructor
      · rintro ⟨⟨hsub₁, ⟨x, hcm, hdm⟩⟩, ⟨hsub₂, ⟨y, hdm', hcm'⟩⟩⟩
        exact ⟨⟨(fun z hz => (hd z).1.mp (hsub₁ z ((hc z).1.mpr hz))),
            ⟨x, (hc x).2.mp hcm, (hd x).2.mp hdm⟩⟩,
          ⟨(fun z hz => (hc z).1.mp (hsub₂ z ((hd z).1.mpr hz))),
            ⟨y, (hd y).2.mp hdm', (hc y).2.mp hcm'⟩⟩⟩
      · rintro ⟨⟨hsub₁, ⟨x, hcm, hdm⟩⟩, ⟨hsub₂, ⟨y, hdm', hcm'⟩⟩⟩
        exact ⟨⟨(fun z hz => (hd z).1.mpr (hsub₁ z ((hc z).1.mp hz))),
            ⟨x, (hc x).2.mpr hcm, (hd x).2.mpr hdm⟩⟩,
          ⟨(fun z hz => (hc z).1.mpr (hsub₂ z ((hd z).1.mp hz))),
            ⟨y, (hd y).2.mpr hdm', (hc y).2.mpr hcm'⟩⟩⟩
  | rsub r t =>
      have hr : ∀ x y, J.role (r, .truth) x y → J.role (r, .meaningful) x y := by
        have hb := h (roleBridge σ r) (by simp [sentenceBridges, roleBridge])
        simpa [holdsQuery, roleBridge, sentenceC] using hb
      have ht : ∀ x y, J.role (t, .truth) x y → J.role (t, .meaningful) x y := by
        have hb := h (roleBridge σ t) (by simp [sentenceBridges, roleBridge])
        simpa [holdsQuery, roleBridge, sentenceC] using hb
      have hmR x y :
          propValue (J.role (r, .truth) x y) (J.role (r, .meaningful) x y) ≠ 𝔢 ↔
            J.role (r, .meaningful) x y := propValue_meaningful _ _ (hr x y)
      have hmT x y :
          propValue (J.role (t, .truth) x y) (J.role (t, .meaningful) x y) ≠ 𝔢 ↔
            J.role (t, .meaningful) x y := propValue_meaningful _ _ (ht x y)
      simp [translateSentence, holdsQuery, sentenceC, sentenceK, decodeTarget,
        forallK_t, propValue_truth, hmR, hmT]

theorem entailmentA_implies_problemEntailment {σ : Signature}
    (Γ Δ : List (Sentence σ)) :
    (Γ ⊨ᴬ Δ) → problemEntailment (compileAC σ Γ Δ) := by
  intro hAC J hPrem q hq
  let K := decodeTarget (wkSignature σ) J
  have hBridges (s : Sentence (wkSignature σ))
      (hs : s ∈ Γ.map (projectSentence σ) ++ Δ.map (projectSentence σ)) :
      ∀ b ∈ sentenceBridges (wkSignature σ) s, holdsQuery J b := by
    intro b hb
    have hbmem : b ∈ (compileAC σ Γ Δ).premises := by
      change b ∈
        ((Γ.map (projectSentence σ) ++ Δ.map (projectSentence σ)).flatMap
            (sentenceBridges (wkSignature σ)) ++
          (Γ.map (projectSentence σ)).map (translateSentence (wkSignature σ)))
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨s, hs, hb⟩
    exact hPrem b hbmem
  have hGammaK : ∀ φ ∈ Γ, sentenceK K (projectSentence σ φ) = 𝔱 := by
    intro φ hφ
    have htranslated : holdsQuery J
        (translateSentence (wkSignature σ) (projectSentence σ φ)) := by
      apply hPrem
      change translateSentence (wkSignature σ) (projectSentence σ φ) ∈
        ((Γ.map (projectSentence σ) ++ Δ.map (projectSentence σ)).flatMap
            (sentenceBridges (wkSignature σ)) ++
          (Γ.map (projectSentence σ)).map (translateSentence (wkSignature σ)))
      apply List.mem_append_right
      apply List.mem_map.mpr
      exact ⟨projectSentence σ φ, List.mem_map.mpr ⟨φ, hφ, rfl⟩, rfl⟩
    exact (decodeSentenceLocal (wkSignature σ) J (projectSentence σ φ)
      (hBridges (projectSentence σ φ)
        (List.mem_append_left _ (List.mem_map.mpr ⟨φ, hφ, rfl⟩)))).mp htranslated
  let I := wkToAC σ K
  have hGammaA : ∀ φ ∈ Γ, satisfiesA I φ := by
    intro φ hφ
    change (sentenceA I φ).1 = 𝔱
    rw [← acSentenceSupport σ I φ, acToWK_wkToAC]
    exact hGammaK φ hφ
  rcases List.mem_map.mp hq with ⟨s, hs, rfl⟩
  rcases List.mem_map.mp hs with ⟨φ, hφ, rfl⟩
  have hφA : satisfiesA I φ := hAC I φ hφ hGammaA
  have hφK : sentenceK K (projectSentence σ φ) = 𝔱 := by
    calc
      sentenceK K (projectSentence σ φ) =
          sentenceK (acToWK σ I) (projectSentence σ φ) := by
        rw [← acToWK_wkToAC σ K]
      _ = (sentenceA I φ).1 := acSentenceSupport σ I φ
      _ = 𝔱 := hφA
  exact (decodeSentenceLocal (wkSignature σ) J (projectSentence σ φ)
    (hBridges (projectSentence σ φ)
      (List.mem_append_right _ (List.mem_map.mpr ⟨φ, hφ, rfl⟩)))).mpr hφK

theorem problemEntailment_implies_entailmentA {σ : Signature}
    (Γ Δ : List (Sentence σ)) :
    problemEntailment (compileAC σ Γ Δ) → Γ ⊨ᴬ Δ := by
  intro hproblem I φ hφ hΓ
  let K := acToWK σ I
  let J := encodeWK (wkSignature σ) K
  have hPrem : ∀ p ∈ (compileAC σ Γ Δ).premises, holdsQuery J p := by
    intro p hp
    change p ∈
      ((Γ.map (projectSentence σ) ++ Δ.map (projectSentence σ)).flatMap
          (sentenceBridges (wkSignature σ)) ++
        (Γ.map (projectSentence σ)).map (translateSentence (wkSignature σ))) at hp
    rcases List.mem_append.mp hp with hbridge | htranslated
    · rcases List.mem_flatMap.mp hbridge with ⟨s, hs, hq⟩
      rcases List.mem_append.mp hs with hs | hs
      · rcases List.mem_map.mp hs with ⟨source, hsource, rfl⟩
        exact encodedBridgesHold (wkSignature σ) K (projectSentence σ source) p hq
      · rcases List.mem_map.mp hs with ⟨source, hsource, rfl⟩
        exact encodedBridgesHold (wkSignature σ) K (projectSentence σ source) p hq
    · rcases List.mem_map.mp htranslated with ⟨s, hs, rfl⟩
      rcases List.mem_map.mp hs with ⟨source, hsource, rfl⟩
      have hsourceTruth : sentenceK K (projectSentence σ source) = 𝔱 := by
        rw [acSentenceSupport]
        exact hΓ source hsource
      exact (translateSentenceEncode (wkSignature σ) K (projectSentence σ source)).mpr
        hsourceTruth
  have hqmem : translateSentence (wkSignature σ) (projectSentence σ φ) ∈
      (compileAC σ Γ Δ).conclusions := by
    change translateSentence (wkSignature σ) (projectSentence σ φ) ∈
      (Δ.map (projectSentence σ)).map (translateSentence (wkSignature σ))
    apply List.mem_map.mpr
    exact ⟨projectSentence σ φ, List.mem_map.mpr ⟨φ, hφ, rfl⟩, rfl⟩
  have htranslated := hproblem J hPrem _ hqmem
  have hsourceTruth : sentenceK K (projectSentence σ φ) = 𝔱 :=
    (translateSentenceEncode (wkSignature σ) K (projectSentence σ φ)).mp htranslated
  rw [acSentenceSupport] at hsourceTruth
  exact hsourceTruth

/-- A uniform finite-input compiler into a source-derived classical signature. -/
theorem translation_exists {σ : Signature} :
    ∀ Γ Δ : List (Sentence σ),
      (Γ ⊨ᴬ Δ) ↔ problemEntailment (compileAC σ Γ Δ) := by
  intro Γ Δ
  constructor
  · intro hAC
    exact entailmentA_implies_problemEntailment Γ Δ hAC
  · exact problemEntailment_implies_entailmentA Γ Δ


end DirectTranslation
