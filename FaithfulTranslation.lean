import Mathlib

/-!
# A repaired, coupled translation of weak Kleene and AC ALCH

Independent of `Basic.lean` (which contains an unfinished theorem). The values,
connective tables and grammar are adapted from it; its translation is not used.

TARGET: classical ALCH with existential Boolean conjunctive queries.
`some C` means ∃x.C(x); `overlap r s` means ∃x y.r(x,y) ∧ s(x,y).
Translated sentences are finite conjunctions of axioms and these queries.
This is NOT ordinary ALCH named-assertion entailment. In particular a fresh name
in a query cannot replace an existential quantifier. Premise witnesses can be
implemented by fresh names. Everything has explicit semantics below.

Each weak Kleene symbol has two classical copies T and M with T ⊆ M, in ONE
knowledge base. Decode t on T, f on M \ T, and e outside M. For concepts:

  (C ∧ D)T = CT ∩ DT                 (C ∧ D)M = CM ∩ DM
  (C ∨ D)T = (CT ∪ DT) ∩ CM ∩ DM    (C ∨ D)M = CM ∩ DM
  (¬ C)T   = CM ∩ ¬CT               (¬ C)M   = CM
  (∃r.C)T  = ∃rT.CT                 (∃r.C)M  = ∃rM.CM
  (∀r.C)T  = (∀rT.CT) ∩ ∃rM.CM     (∀r.C)M  = ∃rM.CM

A GCI C ⊑ D becomes CT ⊑ DT AND some (CM ∩ DM).
A role inclusion r ⊑ s becomes rT ⊑ sT AND overlap rM sM.
These local witnesses, and the coupling axioms, are essential.

AC is decomposed into positive/negative weak Kleene coordinates, sharing
positive roles in restrictions. The paper permits top=(t,v), bottom=(v,t);
`Basic.lean` instead uses `default=t`, fixing both constants to (t,t).
Here the unspecified coordinates may vary by domain element, independently.

The main theorems quantify over all nonempty domains, not just finite models,
and include inconsistent knowledge bases. No complexity classification or S*
closure claim is made here.
-/

namespace FaithfulTranslation

/--
Type of three weak Kleene (WK) truth values
-/
inductive V3 where
| t
| e
| f
deriving DecidableEq, Repr

notation "𝔱" => V3.t
notation "𝔢" => V3.e
notation "𝔣" => V3.f

abbrev V32 := V3 × V3

/--
Weak Kleene truth tables
-/
def negK : V3 → V3
| 𝔱 => .f
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

/--
Restricted WK quantifiers on indexed families;
agreement with the paper below.
-/
noncomputable def existsK {D : Type} (r c : D → V3) : V3 := by
  classical
  exact if ∃ x, r x = 𝔱 ∧ c x = 𝔱 then 𝔱
    else if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then 𝔣 else 𝔢

noncomputable def forallK {D : Type} (r c : D → V3) : V3 := by
  classical
  exact if ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 then
    if ∀ x, r x = 𝔱 → c x = 𝔱 then 𝔱 else 𝔣
    else 𝔢

notation "∃ₖ[" r "]" c:75 => existsK r c
notation "∀ₖ[" r "]" c:75 => forallK r c

@[simp] theorem negK_t (A : V3) :
¬ₖA = 𝔱 ↔ A ≠ 𝔢 ∧ A ≠ 𝔱 := by
  cases A <;> decide

@[simp] theorem negK_f (A : V3) :
¬ₖA = 𝔣 ↔ A = 𝔱 := by
  cases A <;> decide

@[simp] theorem negK_m (A : V3) :
¬ₖA ≠ 𝔢 ↔ A ≠ 𝔢 := by
  cases A <;> decide

@[simp] theorem andK_t (A B : V3) :
A ∧ₖ B = 𝔱 ↔ A = 𝔱 ∧ B = 𝔱 := by
  cases A <;> cases B <;> decide

@[simp] theorem andK_m (A B : V3) :
A ∧ₖ B ≠ 𝔢 ↔ A ≠ 𝔢 ∧ B ≠ 𝔢 := by
  cases A <;> cases B <;> decide

@[simp] theorem orK_t (A B : V3) :
A ∨ₖ B = 𝔱 ↔ (A = 𝔱 ∨ B = 𝔱) ∧ A ≠ 𝔢 ∧ B ≠ 𝔢 := by
  cases A <;> cases B <;> decide

@[simp] theorem orK_m (A B : V3) :
A ∨ₖ B ≠ 𝔢 ↔ A ≠ 𝔢 ∧ B ≠ 𝔢 := by
  cases A <;> cases B <;> decide

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

/-- Definition 8's literal cases, including a harmless empty-set extension. -/
noncomputable def paperExists (X : Set V32) : V3 := by
  classical
  exact if (𝔱, 𝔱) ∈ X then
    𝔱
  else if ∀ p ∈ X, p.1 = 𝔢 ∨ p.2 = 𝔢 then
    𝔢
  else
    𝔣

noncomputable def paperForall (X : Set V32) : V3 := by
  classical
  exact if ((𝔱, 𝔣) ∉ X ∧ (𝔱, 𝔢) ∉ X) ∧ (∃ p ∈ X, p.1 ≠ 𝔢 ∧ p.2 ≠ 𝔢) then
    𝔱
  else if ∀ p ∈ X, p.1 = 𝔢 ∨ p.2 = 𝔢
  then 𝔢 else 𝔣

theorem existsK_paper {D} (r c : D → V3) :
    existsK r c = paperExists (Set.range (fun x => (r x, c x))) := by
  classical
  have hm : (∀ p ∈ Set.range (fun x => (r x, c x)), p.1 = 𝔢 ∨ p.2 = 𝔢) ↔
      ¬ ∃ x, r x ≠ 𝔢 ∧ c x ≠ 𝔢 := by
    simp only [Set.forall_mem_range, not_exists, not_and, not_not]
    exact forall_congr' (fun x => or_iff_not_imp_left)
  have ht : ((V3.t, V3.t) ∈ Set.range (fun x => (r x, c x))) ↔
      ∃ x, r x = 𝔱 ∧ c x = 𝔱 := by simp
  simp only [existsK, paperExists, ht, hm]
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
  simp only [forallK, paperForall, ht, hm, hw]
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
  | ⊤, _ => .t
  | ⊥, _ => .f
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

/-- `both` is ordinary meta-level conjunction. -/
inductive Query (Nc Nr Ni : Type) where
  | isa : Ni → Concept Nc Nr → Query Nc Nr Ni
  | edge : Ni → Ni → Nr → Query Nc Nr Ni
  | sub : Concept Nc Nr → Concept Nc Nr → Query Nc Nr Ni
  | rsub : Nr → Nr → Query Nc Nr Ni
  | some : Concept Nc Nr → Query Nc Nr Ni
  | overlap : Nr → Nr → Query Nc Nr Ni
  | both : Query Nc Nr Ni → Query Nc Nr Ni → Query Nc Nr Ni

notation a " :ₐᵠ " c:50 => Query.isa a c
notation "(" a ", " b ")" " :ᵣᵠ " r:50 => Query.edge a b r
infix:50 " ⊑ᵠ " => Query.sub
infix:50 " ⊑ᵣᵠ " => Query.rsub
notation "∃ᵠ " c:75 => Query.some c
infix:70 " ⋈ᵠ " => Query.overlap
infixl:65 " ∧ᵠ " => Query.both

def holds (J : Model Nc Nr Ni Prop) : Query Nc Nr Ni → Prop
  | a :ₐᵠ c => evalC J c (J.individual a)
  | (a, b) :ᵣᵠ r => J.role r (J.individual a) (J.individual b)
  | c ⊑ᵠ d => ∀ x, evalC J c x → evalC J d x
  | r ⊑ᵣᵠ s => ∀ x y, J.role r x y → J.role s x y
  | ∃ᵠ c => ∃ x, evalC J c x
  | r ⋈ᵠ s => ∃ x y, J.role r x y ∧ J.role s x y
  | p ∧ᵠ q => holds J p ∧ holds J q

inductive Bit where
  | truth | meaningful
  deriving DecidableEq
abbrev TC (Nc Nr : Type) := Concept (Nc × Bit) (Nr × Bit)
abbrev TM (Nc Nr Ni : Type) := Model (Nc × Bit) (Nr × Bit) Ni Prop

/-- Truth and meaningfulness concepts are computed together. -/
def translateC : Concept Nc Nr → TC Nc Nr × TC Nc Nr
  | ⊤ => (⊤, ⊤)
  | ⊥ => (⊥, ⊤)
  | ⟦a⟧ₜ => (⟦(a, Bit.truth)⟧ₜ, ⟦(a, Bit.meaningful)⟧ₜ)
  | ¬ₜ c => let (t, m) := translateC c; (m ⊓ₜ (¬ₜ t), m)
  | c ⊓ₜ d => let (t, m) := translateC c; let (u, n) := translateC d
                (t ⊓ₜ u, m ⊓ₜ n)
  | c ⊔ₜ d => let (t, m) := translateC c; let (u, n) := translateC d
                ((t ⊔ₜ u) ⊓ₜ (m ⊓ₜ n), m ⊓ₜ n)
  | (∃[r] c) => let (t, m) := translateC c
               (∃[(r, .truth)] t, ∃[(r, .meaningful)] m)
  | (∀[r] c) => let (t, m) := translateC c
                ((∀[(r, Bit.truth)]t) ⊓ₜ (∃[(r, Bit.meaningful)] m),
                  ∃[(r, .meaningful)] m)

def translateS : Sentence Nc Nr Ni → Query (Nc × Bit) (Nr × Bit) Ni
  | a :ₐ c => a :ₐᵠ (translateC c).1
  | (a, b) :ᵣ r => (a, b) :ᵣᵠ (r, .truth)
  | c ⊑ d => ((translateC c).1 ⊑ᵠ (translateC d).1) ∧ᵠ
      (∃ᵠ ((translateC c).2 ⊓ₜ (translateC d).2))
  | c ≡ d =>
      (((translateC c).1 ⊑ᵠ (translateC d).1) ∧ᵠ
        (∃ᵠ ((translateC c).2 ⊓ₜ (translateC d).2))) ∧ᵠ
      (((translateC d).1 ⊑ᵠ (translateC c).1) ∧ᵠ
        (∃ᵠ ((translateC d).2 ⊓ₜ (translateC c).2)))
  | r ⊑ᵣ s => ((r, .truth) ⊑ᵣᵠ (s, .truth)) ∧ᵠ
      ((r, .meaningful) ⋈ᵠ (s, .meaningful))

/-- Syntactic bridge axioms; all hold in the same classical model. -/
def Bridge : Set (Query (Nc × Bit) (Nr × Bit) Ni) :=
  { q | (∃ a, q = (⟦(a, Bit.truth)⟧ₜ ⊑ᵠ ⟦(a, Bit.meaningful)⟧ₜ)) ∨
        (∃ r, q = ((r, .truth) ⊑ᵣᵠ (r, .meaningful))) }
def Coherent (J : TM Nc Nr Ni) : Prop :=
  (∀ a x, J.atom (a, .truth) x → J.atom (a, .meaningful) x) ∧
  (∀ r x y, J.role (r, .truth) x y → J.role (r, .meaningful) x y)

theorem bridge_iff (J : TM Nc Nr Ni) :
    (∀ q ∈ Bridge, holds J q) ↔ Coherent J := by
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), fun r => h _ (Or.inr ⟨r, rfl⟩)⟩
  · rintro ⟨hc, hr⟩ q (⟨a, rfl⟩ | ⟨r, rfl⟩)
    · exact hc a
    · exact hr r

/-- Encode without changing the domain or individuals. -/
def encode (I : Model Nc Nr Ni V3) : TM Nc Nr Ni where
  D := I.D
  inhabited := I.inhabited
  individual := I.individual
  atom := fun (a, b) x => match b with
    | .truth => I.atom a x = .t
    | .meaningful => I.atom a x ≠ .e
  role := fun (r, b) x y => match b with
    | .truth => I.role r x y = .t
    | .meaningful => I.role r x y ≠ .e

@[simp] theorem encode_atom_t (I : Model Nc Nr Ni V3) (a : Nc) (x : I.D) :
    (encode I).atom (a, .truth) x ↔ I.atom a x = .t := Iff.rfl
@[simp] theorem encode_atom_m (I : Model Nc Nr Ni V3) (a : Nc) (x : I.D) :
    (encode I).atom (a, .meaningful) x ↔ I.atom a x ≠ .e := Iff.rfl
@[simp] theorem encode_role_t (I : Model Nc Nr Ni V3) (r : Nr) (x y : I.D) :
    (encode I).role (r, .truth) x y ↔ I.role r x y = .t := Iff.rfl
@[simp] theorem encode_role_m (I : Model Nc Nr Ni V3) (r : Nr) (x y : I.D) :
    (encode I).role (r, .meaningful) x y ↔ I.role r x y ≠ .e := Iff.rfl
@[simp] theorem encode_individual (I : Model Nc Nr Ni V3) (a : Ni) :
    (encode I).individual a = I.individual a := rfl

theorem encode_coherent (I : Model Nc Nr Ni V3) : Coherent (encode I) := by
  constructor <;> intros <;> simp_all [encode]

noncomputable def value (t m : Prop) : V3 := by
  classical
  exact if t then .t else if m then .f else .e
@[simp] theorem value_t (t m : Prop) : value t m = .t ↔ t := by
  classical
  unfold value
  split_ifs <;> simp_all
@[simp] theorem value_m (t m : Prop) (h : t → m) : value t m ≠ .e ↔ m := by
  classical
  unfold value
  split_ifs <;> simp_all
noncomputable def decode (J : TM Nc Nr Ni) : Model Nc Nr Ni V3 where
  D := J.D
  inhabited := J.inhabited
  individual := J.individual
  atom := fun a x => value (J.atom (a, .truth) x) (J.atom (a, .meaningful) x)
  role := fun r x y => value (J.role (r, .truth) x y) (J.role (r, .meaningful) x y)

theorem concept_decode (J : TM Nc Nr Ni) (h : Coherent J)
    (c : Concept Nc Nr) (x : J.D) :
    (evalC J (translateC c).1 x ↔ evalK (decode J) c x = .t) ∧
    (evalC J (translateC c).2 x ↔ evalK (decode J) c x ≠ .e) := by
  induction c generalizing x with
  | top => simp [translateC, evalC, evalK]
  | bot => simp [translateC, evalC, evalK]
  | atom a => simp [translateC, evalC, evalK, decode, value_m _ _ (h.1 a x)]
  | neg c ih => simp [translateC, evalC, evalK, (ih x).1, (ih x).2]
  | conj c d ihc ihd => simp [translateC, evalC, evalK, (ihc x).1, (ihc x).2,
      (ihd x).1, (ihd x).2]
  | disj c d ihc ihd => simp [translateC, evalC, evalK, (ihc x).1, (ihc x).2,
      (ihd x).1, (ihd x).2]
  | ex r c ih => simp [translateC, evalC, evalK, decode, fun y => (ih y).1,
      fun y => (ih y).2, fun y => value_m _ _ (h.2 r x y)]
  | all r c ih => simp [translateC, evalC, evalK, decode, fun y => (ih y).1,
      fun y => (ih y).2, fun y => value_m _ _ (h.2 r x y)]

theorem sentence_decode (J : TM Nc Nr Ni) (h : Coherent J) (s : Sentence Nc Nr Ni) :
    holds J (translateS s) ↔ sentenceK (decode J) s = .t := by
  cases s <;> simp [translateS, holds, sentenceK, evalC, decode,
    fun c x => (concept_decode J h c x).1, fun c x => (concept_decode J h c x).2,
    fun r x y => value_m _ _ (h.2 r x y)]

/-- The model conversion is a retraction, not merely a satisfiability argument. -/
theorem decode_encode (I : Model Nc Nr Ni V3) : decode (encode I) = I := by
  cases I with
  | mk D hn names atoms roles =>
    simp only [decode, encode]
    congr 1
    · funext a x
      cases atoms a x <;> simp [value]
    · funext r x y
      cases roles r x y <;> simp [value]

theorem sentence_encode (I : Model Nc Nr Ni V3) (s : Sentence Nc Nr Ni) :
    holds (encode I) (translateS s) ↔ sentenceK I s = .t := by
  have h := sentence_decode (encode I) (encode_coherent I) s
  simpa only [decode_encode] using h

def EntailsK (K : Set (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) : Prop :=
  ∀ I : Model Nc Nr Ni V3, (∀ p ∈ K, sentenceK I p = .t) → sentenceK I s = .t

def EntailsC (K : Set (Query Nc Nr Ni)) (q : Query Nc Nr Ni) : Prop :=
  ∀ J : Model Nc Nr Ni Prop, (∀ p ∈ K, holds J p) → holds J q

def translateKB (K : Set (Sentence Nc Nr Ni)) :
    Set (Query (Nc × Bit) (Nr × Bit) Ni) := Bridge ∪ translateS '' K

/-- Repaired weak Kleene entailment: ONE coupled classical KB. -/
theorem wk_entailment_iff (K : Set (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :
    EntailsK K s ↔ EntailsC (translateKB K) (translateS s) := by
  constructor
  · intro h J hJ
    have hc : Coherent J := (bridge_iff J).1 (fun q hq => hJ q (Or.inl hq))
    apply (sentence_decode J hc s).2
    apply h (decode J)
    intro p hp
    exact (sentence_decode J hc p).1 (hJ _ (Or.inr ⟨p, hp, rfl⟩))
  · intro h I hI
    apply (sentence_encode I s).1
    apply h (encode I)
    rintro q (hb | ⟨p, hp, rfl⟩)
    · exact (bridge_iff (encode I)).2 (encode_coherent I) q hb
    · exact (sentence_encode I p).2 (hI p hp)


/-! ## Bilateral AC semantics and its coordinate decomposition -/

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
  | ⊤, x => (.t, I.topNegative x)
  | ⊥, x => (I.bottomPositive x, .t)
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

/-- A disjoint namespace supplies fresh symbols without any freshness assumptions. -/
inductive ACAtom (Nc : Type) where
  | signed : Nc → Side → ACAtom Nc
  | topNegative
  | bottomPositive

def polarize : Concept Nc Nr → Side → Concept (ACAtom Nc) Nr
  | ⊤, .positive => ⊤
  | ⊤, .negative => ⟦.topNegative⟧ₜ
  | ⊥, .positive => ⟦.bottomPositive⟧ₜ
  | ⊥, .negative => ⊤
  | ⟦a⟧ₜ, side => ⟦.signed a side⟧ₜ
  | (¬ₜ c), .positive => polarize c .negative
  | (¬ₜ c), .negative => polarize c .positive
  | c ⊓ₜ d, .positive => polarize c .positive ⊓ₜ polarize d .positive
  | c ⊓ₜ d, .negative => polarize c .negative ⊔ₜ polarize d .negative
  | c ⊔ₜ d, .positive => polarize c .positive ⊔ₜ polarize d .positive
  | c ⊔ₜ d, .negative => polarize c .negative ⊓ₜ polarize d .negative
  | ∃[r] c, .positive => ∃[r] polarize c .positive
  | ∃[r] c, .negative => ∀[r] polarize c .negative
  | ∀[r] c, .positive => ∀[r] polarize c .positive
  | ∀[r] c, .negative => ∃[r] polarize c .negative

def projectSentence : Sentence Nc Nr Ni → Sentence (ACAtom Nc) Nr Ni
  | a :ₐ c => a :ₐ (polarize c .positive)
  | (a, b) :ᵣ r => (a, b) :ᵣ r
  | c ⊑ d => polarize c .positive ⊑ polarize d .positive
  | c ≡ d => polarize c .positive ≡ polarize d .positive
  | r ⊑ᵣ s => r ⊑ᵣ s

/-- Negative role coordinates do not occur in support of any source sentence.
Both concept coordinates are retained, including those of arbitrary negations. -/
def acToWK (I : ACModel Nc Nr Ni) : Model (ACAtom Nc) Nr Ni V3 where
  D := I.D
  inhabited := I.inhabited
  individual := I.individual
  atom := fun a x => match a with
    | .signed a side => coord (I.atom a x) side
    | .topNegative => I.topNegative x
    | .bottomPositive => I.bottomPositive x
  role := fun r x y => (I.role r x y).1

def wkToAC (W : Model (ACAtom Nc) Nr Ni V3) : ACModel Nc Nr Ni where
  D := W.D
  inhabited := W.inhabited
  individual := W.individual
  atom := fun a x => (W.atom (.signed a .positive) x, W.atom (.signed a .negative) x)
  role := fun r x y => (W.role r x y, .e)
  topNegative := W.atom .topNegative
  bottomPositive := W.atom .bottomPositive

/-- Every intermediate interpretation has a source AC realization. -/
theorem acToWK_wkToAC (W : Model (ACAtom Nc) Nr Ni V3) :
    acToWK (wkToAC W) = W := by
  cases W
  simp only [acToWK, wkToAC]
  congr 1
  funext a x
  cases a with
  | signed a side => cases side <;> rfl
  | topNegative => rfl
  | bottomPositive => rfl

/-- Exact coordinate values, a stronger invariant than designated truth. -/
theorem ac_concept_coordinates (I : ACModel Nc Nr Ni) (c : Concept Nc Nr)
    (side : Side) (x : I.D) :
    evalK (acToWK I) (polarize c side) x = coord (evalA I c x) side := by
  induction c generalizing side x with
  | top => cases side <;> rfl
  | bot => cases side <;> rfl
  | atom a => cases side <;> rfl
  | neg c ih =>
      cases side with
      | positive => exact ih .negative x
      | negative => exact ih .positive x
  | conj c d ihc ihd =>
      cases side <;> simp [polarize, evalK, evalA, coord, andA,
        ihc, ihd, coord]
  | disj c d ihc ihd =>
      cases side <;> simp [polarize, evalK, evalA, coord, orA,
        ihc, ihd, coord]
  | ex r c ih =>
      cases side with
      | positive => exact congrArg₂ existsK rfl (funext (ih .positive))
      | negative => exact congrArg₂ forallK rfl (funext (ih .negative))
  | all r c ih =>
      cases side with
      | positive => exact congrArg₂ forallK rfl (funext (ih .positive))
      | negative => exact congrArg₂ existsK rfl (funext (ih .negative))

/-- Correctly typed counterpart of the paper's coordinate lemma. -/
theorem ac_sentence_support (I : ACModel Nc Nr Ni) (s : Sentence Nc Nr Ni) :
    sentenceK (acToWK I) (projectSentence s) = (sentenceA I s).1 := by
  have hc (c : Concept Nc Nr) : evalK (acToWK I) (polarize c .positive) =
      fun x => (evalA I c x).1 := funext (ac_concept_coordinates I c .positive)
  cases s <;> simp only [projectSentence, sentenceK, sentenceA, forallA, andA, hc] <;> rfl

def EntailsA (K : Set (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) : Prop :=
  ∀ I : ACModel Nc Nr Ni, (∀ p ∈ K, (sentenceA I p).1 = .t) →
    (sentenceA I s).1 = .t

theorem ac_wk_entailment_iff (K : Set (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :
    EntailsA K s ↔ EntailsK (projectSentence '' K) (projectSentence s) := by
  constructor
  · intro h W hW
    have hI : ∀ p ∈ K, (sentenceA (wkToAC W) p).1 = .t := by
      intro p hp
      rw [← ac_sentence_support, acToWK_wkToAC]
      exact hW _ ⟨p, hp, rfl⟩
    have hs := h (wkToAC W) hI
    rwa [← ac_sentence_support, acToWK_wkToAC] at hs
  · intro h I hI
    rw [← ac_sentence_support]
    apply h (acToWK I)
    rintro _ ⟨p, hp, rfl⟩
    rw [ac_sentence_support]
    exact hI p hp

def translateAC (s : Sentence Nc Nr Ni) := translateS (projectSentence s)
def translateACKB (K : Set (Sentence Nc Nr Ni)) := translateKB (projectSentence '' K)

/-- CENTRAL THEOREM. AC ALCH entailment is preserved AND reflected by a
syntactic translation into one classical ALCH theory with explicit existential
queries. This includes arbitrary nested negation, arbitrary complex concepts in
GCIs/assertions, role inclusions, free constant coordinates, and inconsistent KBs. -/
theorem ac_entailment_iff (K : Set (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :
    EntailsA K s ↔ EntailsC (translateACKB K) (translateAC s) :=
  (ac_wk_entailment_iff K s).trans (wk_entailment_iff _ _)


/-! ## A finite, input-dependent translation (no infinite signature axioms)

Only bridge axioms for symbols occurring in the premises OR the query are needed.
The following list-based compiler works even when the ambient signature is
infinite. Duplicated axioms are harmless and can be removed in an implementation.
-/

def atomBridge (a : Nc) : Query (Nc × Bit) (Nr × Bit) Ni :=
  ⟦(a, .truth)⟧ₜ ⊑ᵠ ⟦(a, .meaningful)⟧ₜ
def roleBridge (r : Nr) : Query (Nc × Bit) (Nr × Bit) Ni :=
  (r, .truth) ⊑ᵣᵠ (r, .meaningful)

def conceptBridges : Concept Nc Nr → List (Query (Nc × Bit) (Nr × Bit) Ni)
  | ⊤ | ⊥ => []
  | ⟦a⟧ₜ => [atomBridge a]
  | ¬ₜ c => conceptBridges c
  | c ⊓ₜ d | c ⊔ₜ d => conceptBridges c ++ conceptBridges d
  | ∃[r] c | ∀[r] c => roleBridge r :: conceptBridges c

def sentenceBridges : Sentence Nc Nr Ni → List (Query (Nc × Bit) (Nr × Bit) Ni)
  | _ :ₐ c => conceptBridges c
  | (_, _) :ᵣ r => [roleBridge r]
  | c ⊑ d | c ≡ d => conceptBridges c ++ conceptBridges d
  | r ⊑ᵣ s => [roleBridge r, roleBridge s]

/-- Structural lemma under exactly the bridges used by this concept. -/
theorem concept_decode_local (J : TM Nc Nr Ni) (c : Concept Nc Nr)
    (h : ∀ q ∈ conceptBridges c, holds J q) (x : J.D) :
    (evalC J (translateC c).1 x ↔ evalK (decode J) c x = .t) ∧
    (evalC J (translateC c).2 x ↔ evalK (decode J) c x ≠ .e) := by
  induction c generalizing x with
  | top => simp [translateC, evalC, evalK]
  | bot => simp [translateC, evalC, evalK]
  | atom a =>
      have ha : ∀ y, J.atom (a, .truth) y → J.atom (a, .meaningful) y :=
        h (atomBridge a) (by simp [conceptBridges])
      simp [translateC, evalC, evalK, decode, value_m _ _ (ha x)]
  | neg c ih =>
      have hc := ih h
      simp [translateC, evalC, evalK, (hc x).1, (hc x).2]
  | conj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateC, evalC, evalK, (hc x).1, (hc x).2, (hd x).1, (hd x).2]
  | disj c d ihc ihd =>
      have hc := ihc (fun q hq => h q (List.mem_append_left _ hq))
      have hd := ihd (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateC, evalC, evalK, (hc x).1, (hc x).2, (hd x).1, (hd x).2]
  | ex r c ih =>
      have hr : ∀ x y, J.role (r, .truth) x y → J.role (r, .meaningful) x y :=
        h (roleBridge r) (by simp [conceptBridges])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [translateC, evalC, evalK, decode, fun y => (hc y).1,
        fun y => (hc y).2, fun y => value_m _ _ (hr x y)]
  | all r c ih =>
      have hr : ∀ x y, J.role (r, .truth) x y → J.role (r, .meaningful) x y :=
        h (roleBridge r) (by simp [conceptBridges])
      have hc := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
      simp [translateC, evalC, evalK, decode, fun y => (hc y).1,
        fun y => (hc y).2, fun y => value_m _ _ (hr x y)]

theorem sentence_decode_local (J : TM Nc Nr Ni) (s : Sentence Nc Nr Ni)
    (h : ∀ q ∈ sentenceBridges s, holds J q) :
    holds J (translateS s) ↔ sentenceK (decode J) s = .t := by
  cases s with
  | isa a c => exact (concept_decode_local J c h (J.individual a)).1
  | edge a b r => simp [translateS, holds, sentenceK, decode]
  | sub c d =>
      have hc := concept_decode_local J c (fun q hq => h q (List.mem_append_left _ hq))
      have hd := concept_decode_local J d (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateS, holds, sentenceK, evalC, fun x => (hc x).1,
        fun x => (hc x).2, fun x => (hd x).1, fun x => (hd x).2]
      rfl
  | equiv c d =>
      have hc := concept_decode_local J c (fun q hq => h q (List.mem_append_left _ hq))
      have hd := concept_decode_local J d (fun q hq => h q (List.mem_append_right _ hq))
      simp [translateS, holds, sentenceK, evalC, fun x => (hc x).1,
        fun x => (hc x).2, fun x => (hd x).1, fun x => (hd x).2]
      rfl
  | rsub r s =>
      have hr : ∀ x y, J.role (r, .truth) x y → J.role (r, .meaningful) x y :=
        h (roleBridge r) (by simp [sentenceBridges])
      have hs : ∀ x y, J.role (s, .truth) x y → J.role (s, .meaningful) x y :=
        h (roleBridge s) (by simp [sentenceBridges])
      simp [translateS, holds, sentenceK, decode,
        fun x y => value_m _ _ (hr x y), fun x y => value_m _ _ (hs x y)]

theorem conceptBridges_subset (c : Concept Nc Nr) :
    ∀ q ∈ conceptBridges (Ni := Ni) c, q ∈ Bridge := by
  induction c with
  | top | bot => simp [conceptBridges]
  | atom a => simp only [conceptBridges, List.mem_singleton]; rintro q rfl; exact Or.inl ⟨a, rfl⟩
  | neg c ih => exact ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact ihc q hq
      · exact ihd q hq
  | ex r c ih | all r c ih =>
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inr ⟨r, rfl⟩
      · exact ih q hq

theorem sentenceBridges_subset (s : Sentence Nc Nr Ni) :
    ∀ q ∈ sentenceBridges s, q ∈ Bridge := by
  cases s with
  | isa a c => exact conceptBridges_subset c
  | edge a b r =>
      simp only [sentenceBridges, List.mem_singleton]
      rintro q rfl
      exact Or.inr ⟨r, rfl⟩
  | sub c d | equiv c d =>
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact conceptBridges_subset c q hq
      · exact conceptBridges_subset d q hq
  | rsub r s =>
      simp only [sentenceBridges, List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl | rfl)
      · exact Or.inr ⟨r, rfl⟩
      · exact Or.inr ⟨s, rfl⟩

/-- A completely finite compiler. It includes the query's bridges, not its truth. -/
def compileWK (K : List (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :
    List (Query (Nc × Bit) (Nr × Bit) Ni) :=
  (s :: K).flatMap sentenceBridges ++ K.map translateS

theorem wk_finite_entailment_iff (K : List (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :
    EntailsK {p | p ∈ K} s ↔
      EntailsC {q | q ∈ compileWK K s} (translateS s) := by
  constructor
  · intro h J hJ
    have hb (p : Sentence Nc Nr Ni) (hp : p ∈ s :: K) :
        ∀ q ∈ sentenceBridges p, holds J q := by
      intro q hq
      apply hJ q
      apply List.mem_append_left
      exact List.mem_flatMap.2 ⟨p, hp, hq⟩
    apply (sentence_decode_local J s (hb s (by simp))).2
    apply h (decode J)
    intro p hp
    apply (sentence_decode_local J p (hb p (List.mem_cons_of_mem _ hp))).1
    apply hJ
    exact List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)
  · intro h I hI
    apply (sentence_encode I s).1
    apply h (encode I)
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨p, _, hq⟩ := List.mem_flatMap.1 hq
      exact (bridge_iff (encode I)).2 (encode_coherent I) q (sentenceBridges_subset p q hq)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (sentence_encode I p).2 (hI p hp)

def compileAC (K : List (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :=
  compileWK (K.map projectSentence) (projectSentence s)

/-- MAIN FINITE-INPUT THEOREM. No finiteness assumption on names or models. -/
theorem ac_finite_entailment_iff (K : List (Sentence Nc Nr Ni)) (s : Sentence Nc Nr Ni) :
    EntailsA {p | p ∈ K} s ↔
      EntailsC {q | q ∈ compileAC K s} (translateAC s) := by
  have himage : projectSentence '' {p | p ∈ K} = {p | p ∈ K.map projectSentence} := by
    ext p
    simp
  rw [ac_wk_entailment_iff, himage]
  exact wk_finite_entailment_iff _ _


/-! ## Regression theorems and boundary cases -/

/-- Reviewer 2's inconsistent weak Kleene KB entails every sentence. -/
theorem wk_bottom_entails (a : Ni) (s : Sentence Nc Nr Ni) :
    EntailsK {a :ₐ ⊥} s := by
  intro I h
  have hb := h (a :ₐ ⊥) (Set.mem_singleton _)
  simp [sentenceK, evalK] at hb

/-- The repaired target also entails every translated query in that case. -/
theorem translated_bottom_entails (a : Ni) (s : Sentence Nc Nr Ni) :
    EntailsC {q | q ∈ compileWK [a :ₐ ⊥] s} (translateS s) := by
  apply (wk_finite_entailment_iff _ _).1
  simpa using wk_bottom_entails a s

/-- A meaningful pair (f,f) is a legitimate universal witness. -/
theorem universal_false_false :
    ∀ₖ[(fun _ : Unit => V3.f)] (fun _ => V3.f) = .t := by
  simp [forallK]

/-- Without a jointly meaningful witness the restricted universal is e,
even though there is no true antecedent and the classical universal is true. -/
theorem universal_unknown_guard :
    ∀ₖ[(fun _ : Unit => V3.e)] (fun _ => V3.t) = .e := by
  simp [forallK]

/-- The atomwise star construction from the old argument does not lift. -/
def starValue : V3 → V3
  | .e => .e
  | _ => .t

theorem star_counterexample :
    let r : Bool → V3 := fun _ => .f
    let c : Bool → V3 := fun b => if b then .e else .f
    ∀ₖ[r] c = .t ∧
      ∀ₖ[(fun b => starValue (r b))] (fun b => starValue (c b)) = .f := by
  simp [forallK, starValue, Bool.exists_bool, Bool.forall_bool]

/-- A named individual need not be the witness of an existential query. -/
def unnamedWitness : Model Unit Unit Unit Prop where
  D := Bool
  inhabited := inferInstance
  individual := fun _ => false
  atom := fun _ x => x = true
  role := fun _ _ _ => False

theorem existential_is_not_a_fresh_named_query :
    holds unnamedWitness (∃ᵠ ⟦()⟧ₜ) ∧
      ¬ holds unnamedWitness (() :ₐᵠ ⟦()⟧ₜ) := by
  simp [holds, evalC, unnamedWitness]

/-- Inconsistent support and refutation of A do not force support of B. -/
def inconsistentAC : ACModel Bool Unit Unit where
  D := Unit
  inhabited := inferInstance
  individual := fun _ => ()
  atom := fun a _ => if a then (.t, .t) else (.f, .f)
  role := fun _ _ _ => (.f, .f)
  topNegative := fun _ => .f
  bottomPositive := fun _ => .f

def contradictionKB : List (Sentence Bool Unit Unit) :=
  [() :ₐ ⟦true⟧ₜ, () :ₐ (¬ₜ ⟦true⟧ₜ)]

theorem ac_nonexplosive :
    ¬ EntailsA {p | p ∈ contradictionKB} (() :ₐ ⟦false⟧ₜ) := by
  intro h
  have hp : ∀ p ∈ ({p | p ∈ contradictionKB} : Set (Sentence Bool Unit Unit)),
      (sentenceA inconsistentAC p).1 = .t := by
    intro p hp
    simp only [Set.mem_ofPred_eq, contradictionKB, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  have hbad := h inconsistentAC hp
  simp [sentenceA, evalA, inconsistentAC] at hbad

/-- The classical encoding preserves this failure of explosion. -/
theorem translated_ac_nonexplosive :
    ¬ EntailsC {q | q ∈ compileAC contradictionKB (() :ₐ ⟦false⟧ₜ)}
      (translateAC (() :ₐ ⟦false⟧ₜ)) :=
  mt (ac_finite_entailment_iff _ _).2 ac_nonexplosive

/-!
## How to use and interpret the result

* `compileAC K s` is a finite list, computable from the source syntax alone.
  `translateAC s` is the query. `ac_finite_entailment_iff` is the main result.
* `concept_decode_local` proves both T and M invariants simultaneously by
  structural induction. In the universal case, the no-counterexample condition
  uses rT, while the witness condition uses rM. Mixing them is unsound.
* `ac_concept_coordinates` proves exact equality of both coordinates, not only
  preservation of designated values. `acToWK_wkToAC` ensures every intermediate
  model has a source realization; `decode_encode` gives the other model direction.
* There is no satisfiability assumption on K. Model conversion therefore handles
  vacuous entailment correctly, unlike the two-independent-KBs proposal.
* For a premise `some C`, use one fresh individual with assertion C. For a premise
  `overlap r s`, use two fresh individuals a,b and BOTH r(a,b), s(a,b). Allocate
  names per existential occurrence, with no distinctness constraints. Existential
  witnesses may coincide. This is an equisatisfiable expansion, not a replacement
  of existential QUERIES by arbitrary named assertions.
* An implementation can ask ordinary ALCH entailment for the ordinary conjuncts
  and Boolean conjunctive query entailment for the existential conjuncts, always
  against the SAME translated premises. The target extension is explicit; this
  file does not establish a reduction to ordinary ALCH axiom entailment alone,
  nor an impossibility theorem for such a further reduction.
* Tree inlining in `translateC` can duplicate subterms. This file deliberately
  makes no linear-size or PSPACE/EXPTIME completeness claim. Sharing subexpressions
  using fresh concept definitions is a separate implementation/proof obligation.
* This file addresses AC (nine bilateral values built from three values) and the
  intermediate three-valued weak Kleene logic. It does not silently restrict AC
  to the five-valued S* subset.
-/

-- Kernel dependency audit: these should list only Lean's standard logical axioms.
#print axioms wk_finite_entailment_iff
#print axioms ac_finite_entailment_iff
#print axioms translated_ac_nonexplosive

end FaithfulTranslation
