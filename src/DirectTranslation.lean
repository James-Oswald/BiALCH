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

abbrev Translation (σ₁ σ₂ : Signature): Type := List (Sentence σ₁) → List (Sentence σ₂)

theorem translation_exists {σ₁ σ₂ : Signature} (Γ Δ : List (Sentence σ₁)) :
∃ τ : Translation σ₁ σ₂, (Γ ⊨ᴬ Δ) ↔ (τ Γ) ⊨ᶜ (τ Δ) :=
  sorry

end DirectTranslation

-- /-- A self-inclusion already requires a meaningful instance. -/
-- theorem self_inclusion_truth (I : ACModel Nc Nr Ni) (c : Concept Nc Nr) :
--     (sentenceA I (c ⊑ c)).1 = 𝔱 ↔ ∃ x, (evalA I c x).1 ≠ 𝔢 := by
--   simp [sentenceA, forallA]

-- /-!
-- ## Obstruction to exact interpretation in the same models

-- A disconnected, unnamed component can supply the meaningful instance required
-- by an AC inclusion. Every classical sentence true in the larger model remains
-- true in its named component. This rules out modelwise definitions under the
-- correspondence below, not arbitrary uniform entailment translations.
-- -/
-- def small : Model Unit Unit Unit Prop where
--   D := Unit
--   inhabited := inferInstance
--   individual _ := ()
--   atom _ _ := False
--   role _ _ _ := False

-- def large : Model Unit Unit Unit Prop where
--   D := Bool
--   inhabited := inferInstance
--   individual _ := false
--   atom _ x := x = true
--   role _ _ _ := False

-- theorem component_concept (c : Concept Unit Unit) :
--     evalC large c false ↔ evalC small c () := by
--   induction c with
--   | top => rfl
--   | bot => rfl
--   | atom a => simp [evalC, large, small]
--   | neg c ih => exact not_congr ih
--   | conj c d ihc ihd => exact and_congr ihc ihd
--   | disj c d ihc ihd => exact or_congr ihc ihd
--   | ex r c ih => simp [evalC, large, small]
--   | all r c ih => simp [evalC, large, small]

-- theorem component_sentence (s : Sentence Unit Unit Unit) :
--     sentenceC large s → sentenceC small s := by
--   cases s with
--   | isa a c => exact (component_concept c).mp
--   | edge a b r => exact id
--   | sub c d =>
--     intro h x hc
--     exact (component_concept d).mp (h false ((component_concept c).mpr hc))
--   | equiv c d =>
--     intro h x
--     exact (component_concept c).symm.trans ((h false).trans (component_concept d))
--   | rsub r s => simp [sentenceC, small]

-- /-- Even an infinite ALCH theory cannot define nonemptiness in these same models. -/
-- theorem no_theory_defines_nonempty :
--     ¬ ∃ T : Set (Sentence Unit Unit Unit),
--       ∀ J : Model Unit Unit Unit Prop,
--         (∀ s ∈ T, sentenceC J s) ↔ ∃ x, J.atom () x := by
--   rintro ⟨T, hT⟩
--   have hl : ∀ s ∈ T, sentenceC large s := (hT large).mpr ⟨true, rfl⟩
--   have hs : ∀ s ∈ T, sentenceC small s :=
--     fun s hs => component_sentence s (hl s hs)
--   obtain ⟨x, hx⟩ := (hT small).mp hs
--   exact hx

-- /-- Interpret a classical atom as meaningful-false when it holds, undefined
-- otherwise. Preserve the domain and individual denotations. -/
-- noncomputable def decodeExample (J : Model Unit Unit Unit Prop) :
--     ACModel Unit Unit Unit := by
--   classical
--   exact {
--     D := J.D
--     inhabited := J.inhabited
--     individual := J.individual
--     atom := fun a x => (if J.atom a x then 𝔣 else 𝔢, 𝔢)
--     role := fun _ _ _ => (𝔢, 𝔢)
--     topNegative := fun _ => 𝔢
--     bottomPositive := fun _ => 𝔢 }

-- theorem decoded_self_inclusion (J : Model Unit Unit Unit Prop) :
--     (sentenceA (decodeExample J) (⟦()⟧ₜ ⊑ ⟦()⟧ₜ)).1 = 𝔱 ↔
--       ∃ x, J.atom () x := by
--   classical
--   rw [self_inclusion_truth]
--   simp [evalA, decodeExample]

-- /-- This rules out only modelwise translation under `decodeExample`.
-- It does not assert impossibility of every uniform entailment translation. -/
-- theorem no_modelwise_inclusion_translation :
--     ¬ ∃ T : Set (Sentence Unit Unit Unit),
--       ∀ J : Model Unit Unit Unit Prop,
--         (∀ s ∈ T, sentenceC J s) ↔
--           (sentenceA (decodeExample J) (⟦()⟧ₜ ⊑ ⟦()⟧ₜ)).1 = 𝔱 := by
--   rintro ⟨T, hT⟩
--   apply no_theory_defines_nonempty
--   exact ⟨T, fun J => (hT J).trans (decoded_self_inclusion J)⟩

-- #print axioms no_modelwise_inclusion_translation
