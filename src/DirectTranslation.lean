import Mathlib

/-!
# Obstruction to direct modelwise AC-to-classical translation

This development uses the ordinary `Sentence` grammar for the classical target.
There are no existential assertions, blank nodes, or query constructors.
The final obstruction concerns exact modelwise translation of inclusions under
the explicitly defined `decodeExample` correspondence. It is not a claim about
all possible uniform entailment reductions. A complete uniform translation is
not established in this file.
-/

namespace DirectTranslation

inductive V3 where
  | t
  | e
  | f
  deriving DecidableEq, Repr

notation "𝔱" => V3.t
notation "𝔢" => V3.e
notation "𝔣" => V3.f

abbrev V32 := V3 × V3

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

/-- Restricted quantifiers on indexed families; agreement with the paper below. -/
noncomputable def existsK {D : Type} (r c : D → V3) : V3 := by
  classical
  exact if ∃ x, r x = 𝔱 ∧ c x = 𝔱 then 𝔱
    else if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then 𝔣
    else 𝔢

noncomputable def forallK {D : Type} (r c : D → V3) : V3 := by
  classical
  exact if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then
    if ∀ x, r x = 𝔱 → c x = 𝔱 then 𝔱 else 𝔣
    else 𝔢

notation "∃ₖ[" r "]" c:75 => existsK r c
notation "∀ₖ[" r "]" c:75 => forallK r c

@[simp] theorem negK_t (v : V3) : negK v = 𝔱 ↔ v ≠ 𝔢 ∧ v ≠ 𝔱 := by
  cases v <;> decide
@[simp] theorem negK_m (v : V3) : negK v ≠ 𝔢 ↔ v ≠ 𝔢 := by
  cases v <;> decide
@[simp] theorem andK_t (v w : V3) : andK v w = 𝔱 ↔ v = 𝔱 ∧ w = 𝔱 := by
  cases v <;> cases w <;> decide
@[simp] theorem andK_m (v w : V3) : andK v w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide
@[simp] theorem orK_t (v w : V3) :
    orK v w = 𝔱 ↔ (v = 𝔱 ∨ w = 𝔱) ∧ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide
@[simp] theorem orK_m (v w : V3) : orK v w ≠ 𝔢 ↔ v ≠ 𝔢 ∧ w ≠ 𝔢 := by
  cases v <;> cases w <;> decide

@[simp] theorem existsK_t {D} (r c : D → V3) :
    ∃ₖ[r] c = 𝔱 ↔ ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by
  classical
  unfold existsK
  split_ifs <;> simp_all
@[simp] theorem existsK_m {D} (r c : D → V3) :
    ∃ₖ[r] c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold existsK
  split_ifs <;> simp_all
  obtain ⟨x, hx, hy⟩ := ‹∃ x, r x = 𝔱 ∧ c x = 𝔱›
  exact ⟨x, by simp [hx], by simp [hy]⟩
@[simp] theorem forallK_t {D} (r c : D → V3) :
    ∀ₖ[r] c = 𝔱 ↔ (∀ x, r x = 𝔱 → c x = 𝔱) ∧
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallK
  split_ifs <;> simp_all
@[simp] theorem forallK_m {D} (r c : D → V3) :
    ∀ₖ[r] c ≠ 𝔢 ↔ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
  classical
  unfold forallK
  split_ifs <;> simp_all

/-- Definition 8's literal cases, with `𝔢` extending them to the empty set. -/
noncomputable def paperExists (X : Set V32) : V3 := by
  classical
  exact if (𝔱, 𝔱) ∈ X then 𝔱
    else if ∀ p ∈ X, p.1 = 𝔢 ∨ p.2 = 𝔢 then 𝔢
    else if ∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢 then 𝔣
    else 𝔢

noncomputable def paperForall (X : Set V32) : V3 := by
  classical
  exact if ((𝔱, 𝔣) ∉ X ∧ (𝔱, 𝔢) ∉ X) ∧
      (∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) then 𝔱
    else if ∀ p ∈ X, p.1 = 𝔢 ∨ p.2 = 𝔢 then 𝔢
    else if (∃ p ∈ X, (p.1 = 𝔱 ∧ p.2 = 𝔣) ∨ (p.1 = 𝔱 ∧ p.2 = 𝔢)) ∧
        (∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) then 𝔣
    else 𝔢

theorem existsK_paper {D} (r c : D → V3) :
    existsK r c = paperExists (Set.range (fun x => (r x, c x))) := by
  classical
  have hm : (∀ p ∈ Set.range (fun x => (r x, c x)), p.1 = 𝔢 ∨ p.2 = 𝔢) ↔
      ¬ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.forall_mem_range, not_exists, not_and, not_not]
    exact forall_congr' (fun x => or_iff_not_imp_left)
  have ht : ((𝔱, 𝔱) ∈ Set.range (fun x => (r x, c x))) ↔
      ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by simp
  have hw : (∃ p ∈ Set.range (fun x => (r x, c x)), p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) ↔
      ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by simp
  simp only [existsK, paperExists, ht, hm, hw]
  split_ifs <;> rfl

theorem forallK_paper {D} (r c : D → V3) :
    forallK r c = paperForall (Set.range (fun x => (r x, c x))) := by
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
  have hv : (∃ p ∈ Set.range (fun x => (r x, c x)),
      (p.1 = 𝔱 ∧ p.2 = 𝔣) ∨ (p.1 = 𝔱 ∧ p.2 = 𝔢)) ↔
      ∃ x, r x = 𝔱 ∧ c x ≠ 𝔱 := by
    simp [Set.mem_range]
    constructor
    · rintro ⟨x, (⟨hr, hf⟩ | ⟨hr, he⟩)⟩
      · exact ⟨x, hr, by simp [hf]⟩
      · exact ⟨x, hr, by simp [he]⟩
    · rintro ⟨x, hr, hc⟩
      cases hcx : c x with
      | t => simp [hcx] at hc
      | e => exact ⟨x, Or.inr ⟨hr, hcx⟩⟩
      | f => exact ⟨x, Or.inl ⟨hr, hcx⟩⟩
  simp only [forallK, paperForall, ht, hm, hw, hv]
  split_ifs <;> simp_all

inductive Concept (Nc Nr : Type) where
  | top | bot
  | atom : Nc → Concept Nc Nr
  | neg : Concept Nc Nr → Concept Nc Nr
  | conj : Concept Nc Nr → Concept Nc Nr → Concept Nc Nr
  | disj : Concept Nc Nr → Concept Nc Nr → Concept Nc Nr
  | ex : Nr → Concept Nc Nr → Concept Nc Nr
  | all : Nr → Concept Nc Nr → Concept Nc Nr
  deriving Repr
inductive Sentence (Nc Nr Ni : Type) where
  | isa : Ni → Concept Nc Nr → Sentence Nc Nr Ni
  | edge : Ni → Ni → Nr → Sentence Nc Nr Ni
  | sub : Concept Nc Nr → Concept Nc Nr → Sentence Nc Nr Ni
  | equiv : Concept Nc Nr → Concept Nc Nr → Sentence Nc Nr Ni
  | rsub : Nr → Nr → Sentence Nc Nr Ni

instance : Top (Concept Nc Nr) := ⟨.top⟩
instance : Bot (Concept Nc Nr) := ⟨.bot⟩
instance : Coe Nc (Concept Nc Nr) := ⟨Concept.atom⟩
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

example (A B : Nc) (r : Nr) : Concept Nc Nr :=
  A ⊓ₜ (∃[r] B) ⊓ₜ (∀[r] ¬ₜ A)

example (a : Ni) (A : Nc) (r : Nr) : Sentence Nc Nr Ni :=
  (a :ₐ (A ⊓ₜ (∃[r] A)))

example (a b : Ni) (r : Nr) : Sentence Nc Nr Ni :=
  (a, b) :ᵣ r

example (r s : Nr) : Sentence Nc Nr Ni := r ⊑ᵣ s

/-- Nonempty domains; no unique-name assumption. -/
structure Model (Nc Nr Ni V : Type) where
  D : Type
  inhabited : Nonempty D
  individual : Ni → D
  atom : Nc → D → V
  role : Nr → D → D → V
variable {Nc Nr Ni : Type}

noncomputable def evalK (I : Model Nc Nr Ni V3) : Concept Nc Nr → I.D → V3
  | ⊤, _ => 𝔱
  | ⊥, _ => 𝔣
  | ⟦a⟧ₜ, x => I.atom a x
  | ¬ₜ c, x => ¬ₖ (evalK I c x)
  | c ⊓ₜ d, x => evalK I c x ∧ₖ evalK I d x
  | c ⊔ₜ d, x => evalK I c x ∨ₖ evalK I d x
  | ∃[r] c, x => ∃ₖ[I.role r x] (evalK I c)
  | ∀[r] c, x => ∀ₖ[I.role r x] (evalK I c)

noncomputable def sentenceK (I : Model Nc Nr Ni V3) : Sentence Nc Nr Ni → V3
  | a :ₐ c => evalK I c (I.individual a)
  | (a, b) :ᵣ r => I.role r (I.individual a) (I.individual b)
  | c ⊑ d => ∀ₖ[evalK I c] (evalK I d)
  | c ≡ d => (∀ₖ[evalK I c] (evalK I d)) ∧ₖ
      (∀ₖ[evalK I d] (evalK I c))
  | r ⊑ᵣ s => ∀ₖ[(fun p : I.D × I.D => I.role r p.1 p.2)]
      (fun p => I.role s p.1 p.2)

-- Ordinary classical semantics, independent of source values.
def evalC (J : Model Nc Nr Ni Prop) : Concept Nc Nr → J.D → Prop
  | ⊤, _ => True
  | ⊥, _ => False
  | ⟦a⟧ₜ, x => J.atom a x
  | ¬ₜ c, x => ¬ evalC J c x
  | c ⊓ₜ d, x => evalC J c x ∧ evalC J d x
  | c ⊔ₜ d, x => evalC J c x ∨ evalC J d x
  | ∃[r] c, x => ∃ y, J.role r x y ∧ evalC J c y
  | ∀[r] c, x => ∀ y, J.role r x y → evalC J c y

inductive Side where
  | positive | negative
  deriving DecidableEq

def coord (v : V32) : Side → V3
  | .positive => v.1
  | .negative => v.2

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

structure ACModel (Nc Nr Ni : Type) extends Model Nc Nr Ni V32 where
  topNegative : D → V3
  bottomPositive : D → V3

noncomputable def evalA (I : ACModel Nc Nr Ni) : Concept Nc Nr → I.D → V32
  | ⊤, x => (𝔱, I.topNegative x)
  | ⊥, x => (I.bottomPositive x, 𝔱)
  | ⟦a⟧ₜ, x => I.atom a x
  | ¬ₜ c, x => ∼ₐ (evalA I c x)
  | c ⊓ₜ d, x => evalA I c x ∧ₐ evalA I d x
  | c ⊔ₜ d, x => evalA I c x ∨ₐ evalA I d x
  | ∃[r] c, x => ∃ₐ[I.role r x] (evalA I c)
  | ∀[r] c, x => ∀ₐ[I.role r x] (evalA I c)

noncomputable def sentenceA (I : ACModel Nc Nr Ni) : Sentence Nc Nr Ni → V32
  | a :ₐ c => evalA I c (I.individual a)
  | (a, b) :ᵣ r => I.role r (I.individual a) (I.individual b)
  | c ⊑ d => ∀ₐ[evalA I c] (evalA I d)
  | c ≡ d => (∀ₐ[evalA I c] (evalA I d)) ∧ₐ
      (∀ₐ[evalA I d] (evalA I c))
  | r ⊑ᵣ s => ∀ₐ[(fun p : I.D × I.D => I.role r p.1 p.2)]
      (fun p => I.role s p.1 p.2)

/-- Classical sentence semantics, with no additional query constructors. -/
def sentenceC (J : Model Nc Nr Ni Prop) : Sentence Nc Nr Ni → Prop
  | a :ₐ c => evalC J c (J.individual a)
  | (a, b) :ᵣ r => J.role r (J.individual a) (J.individual b)
  | c ⊑ d => ∀ x, evalC J c x → evalC J d x
  | c ≡ d => ∀ x, evalC J c x ↔ evalC J d x
  | r ⊑ᵣ s => ∀ x y, J.role r x y → J.role s x y

/-- A self-inclusion already requires a meaningful instance. -/
theorem self_inclusion_truth (I : ACModel Nc Nr Ni) (c : Concept Nc Nr) :
    (sentenceA I (c ⊑ c)).1 = 𝔱 ↔ ∃ x, (evalA I c x).1 ≠ 𝔢 := by
  simp [sentenceA, forallA]

/-!
## Obstruction to exact interpretation in the same models

A disconnected, unnamed component can supply the meaningful instance required
by an AC inclusion. Every classical sentence true in the larger model remains
true in its named component. This rules out modelwise definitions under the
correspondence below, not arbitrary uniform entailment translations.
-/
def small : Model Unit Unit Unit Prop where
  D := Unit
  inhabited := inferInstance
  individual _ := ()
  atom _ _ := False
  role _ _ _ := False

def large : Model Unit Unit Unit Prop where
  D := Bool
  inhabited := inferInstance
  individual _ := false
  atom _ x := x = true
  role _ _ _ := False

theorem component_concept (c : Concept Unit Unit) :
    evalC large c false ↔ evalC small c () := by
  induction c with
  | top => rfl
  | bot => rfl
  | atom a => simp [evalC, large, small]
  | neg c ih => exact not_congr ih
  | conj c d ihc ihd => exact and_congr ihc ihd
  | disj c d ihc ihd => exact or_congr ihc ihd
  | ex r c ih => simp [evalC, large, small]
  | all r c ih => simp [evalC, large, small]

theorem component_sentence (s : Sentence Unit Unit Unit) :
    sentenceC large s → sentenceC small s := by
  cases s with
  | isa a c => exact (component_concept c).mp
  | edge a b r => exact id
  | sub c d =>
    intro h x hc
    exact (component_concept d).mp (h false ((component_concept c).mpr hc))
  | equiv c d =>
    intro h x
    exact (component_concept c).symm.trans ((h false).trans (component_concept d))
  | rsub r s => simp [sentenceC, small]

/-- Even an infinite ALCH theory cannot define nonemptiness in these same models. -/
theorem no_theory_defines_nonempty :
    ¬ ∃ T : Set (Sentence Unit Unit Unit),
      ∀ J : Model Unit Unit Unit Prop,
        (∀ s ∈ T, sentenceC J s) ↔ ∃ x, J.atom () x := by
  rintro ⟨T, hT⟩
  have hl : ∀ s ∈ T, sentenceC large s := (hT large).mpr ⟨true, rfl⟩
  have hs : ∀ s ∈ T, sentenceC small s :=
    fun s hs => component_sentence s (hl s hs)
  obtain ⟨x, hx⟩ := (hT small).mp hs
  exact hx

/-- Interpret a classical atom as meaningful-false when it holds, undefined
otherwise. Preserve the domain and individual denotations. -/
noncomputable def decodeExample (J : Model Unit Unit Unit Prop) :
    ACModel Unit Unit Unit := by
  classical
  exact {
    D := J.D
    inhabited := J.inhabited
    individual := J.individual
    atom := fun a x => (if J.atom a x then 𝔣 else 𝔢, 𝔢)
    role := fun _ _ _ => (𝔢, 𝔢)
    topNegative := fun _ => 𝔢
    bottomPositive := fun _ => 𝔢 }

theorem decoded_self_inclusion (J : Model Unit Unit Unit Prop) :
    (sentenceA (decodeExample J) (⟦()⟧ₜ ⊑ ⟦()⟧ₜ)).1 = 𝔱 ↔
      ∃ x, J.atom () x := by
  classical
  rw [self_inclusion_truth]
  simp [evalA, decodeExample]

/-- This rules out only modelwise translation under `decodeExample`.
It does not assert impossibility of every uniform entailment translation. -/
theorem no_modelwise_inclusion_translation :
    ¬ ∃ T : Set (Sentence Unit Unit Unit),
      ∀ J : Model Unit Unit Unit Prop,
        (∀ s ∈ T, sentenceC J s) ↔
          (sentenceA (decodeExample J) (⟦()⟧ₜ ⊑ ⟦()⟧ₜ)).1 = 𝔱 := by
  rintro ⟨T, hT⟩
  apply no_theory_defines_nonempty
  exact ⟨T, fun J => (hT J).trans (decoded_self_inclusion J)⟩

#print axioms no_modelwise_inclusion_translation
end DirectTranslation
