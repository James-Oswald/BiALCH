

import Mathlib

namespace BiALCH


abbrev V2 := Prop

inductive V3 where
| t
| e
| f
deriving Inhabited, Repr, DecidableEq, Encodable

instance : Fintype V3 where
  elems := {.t, .e, .f}
  complete x := by cases x <;> simp

abbrev V32 := V3 × V3

-- We can decide membership in a set of pairs
noncomputable instance (X : Set V32) (x : V32) : Decidable (x ∈ X) :=
  Classical.propDecidable _

-- Freshness class for generating fresh names
class HasFresh (α : Type u) : Type u where
  fresh : Finset α → α
  fresh_notMem (s : Finset α) : fresh s ∉ s

def HasFresh.fresh2 {α : Type u} [HasFresh α] [DecidableEq α] (s : Finset α) : α × α :=
  let f1 := HasFresh.fresh s
  let s' := insert f1 s
  let f2 := HasFresh.fresh s'
  ⟨f1, f2⟩

lemma HasFresh.fresh2_notMem {α : Type u} [HasFresh α] [DecidableEq α] (s : Finset α) :
let ⟨f1, f2⟩ := HasFresh.fresh2 s; f1 ∉ s ∧ f2 ∉ s ∧ f1 ≠ f2 := by
  dsimp [HasFresh.fresh2]
  refine ⟨HasFresh.fresh_notMem s, ?_, ?_⟩
  · intro hf2
    exact HasFresh.fresh_notMem (insert (HasFresh.fresh s) s)
      (Finset.mem_insert_of_mem hf2)
  · intro hEq
    apply HasFresh.fresh_notMem (insert (HasFresh.fresh s) s)
    rw [← hEq]
    exact Finset.mem_insert_self _ _

variable {Nc : Type} [DecidableEq Nc] [Repr Nc] [Inhabited Nc] [HasFresh Nc] [Encodable Nc]
variable {Nr : Type} [DecidableEq Nr] [Repr Nr] [Inhabited Nr] [HasFresh Nr] [Encodable Nr]
variable {Ni : Type} [DecidableEq Ni] [Repr Ni] [Inhabited Ni] [HasFresh Ni] [Encodable Ni]

/-- ALCH Concepts -/
inductive Concept where
| top     : Concept
| bot     : Concept
| atomic  : Nc → Concept
| neg     : Concept → Concept
| conj    : Concept → Concept → Concept
| disj    : Concept → Concept → Concept
| exis    : Nr → Concept → Concept
| univ    : Nr → Concept → Concept
deriving Inhabited, Repr, DecidableEq, Encodable

instance : Top (@Concept Nc Nr) := ⟨Concept.top⟩
instance : Bot (@Concept Nc Nr) := ⟨Concept.bot⟩
infixl:70 " ⊓ₜ " => Concept.conj
infixl:65 " ⊔ₜ " => Concept.disj
notation "¬ₜ " c:75 => Concept.neg c
notation "∃[" r "]" c:75 => Concept.exis r c
notation "∀[" r "]" c:75 => Concept.univ r c
instance : Coe Nc (@Concept Nc Nr) := ⟨Concept.atomic⟩

example (A B: Nc) (R : Nr) : @Concept Nc Nr := A ⊓ₜ ∃[R] B ⊓ₜ (∀[R] ¬ₜA)

-- Atomic Role Language
inductive RoleA where
| atomic : Nr → RoleA
deriving DecidableEq, Encodable, Repr

-- Intersection Role Language
inductive RoleI where
| atomic : Nr → RoleI
| inter : RoleI → RoleI → RoleI
deriving DecidableEq, Encodable, Repr

infixl:70 " ⊓ᵣ " => RoleI.inter

/-- Positive Concept Grammar -/
inductive ConceptP where
| top     : ConceptP
| atomic  : Nc → ConceptP
| conj    : ConceptP → ConceptP → ConceptP
| disj    : ConceptP → ConceptP → ConceptP
| exis    : Nr → ConceptP → ConceptP
| univ    : Nr → ConceptP → ConceptP
deriving DecidableEq, Encodable

instance : Top (@ConceptP Nc Nr) := ⟨ConceptP.top⟩
infixl:70 " ⊓ₜ " => ConceptP.conj
infixl:65 " ⊔ₜ " => ConceptP.disj
notation "∃[" r "]" c:75 => ConceptP.exis r c
notation "∀[" r "]" c:75 => ConceptP.univ r c
instance : Coe Nc (@ConceptP Nc Nr) := ⟨ConceptP.atomic⟩

/-- General Sentences -/
inductive Sentence (C R : Type) where
| assert_c : Ni → C → Sentence C R
| assert_r : Ni → Ni → R → Sentence C R
| subsume  : C → C → Sentence C R
| equiv    : C → C → Sentence C R
deriving Repr, Inhabited, DecidableEq, Encodable

notation a " :ₐ " c:50 => Sentence.assert_c a c
notation "(" a ", " b ")" " :ᵣ " r:50 => Sentence.assert_r a b r
infix:50 " ⊑ " => Sentence.subsume
infix:50 " ≡ " => Sentence.equiv

/-- ALCH Sentences -/
inductive SentenceH (C R: Type) where
| assert_c : Ni → C → SentenceH C R
| assert_r : Ni → Ni → R → SentenceH C R
| blank_assert_c : C -> SentenceH C R
| blank_assert_r : R -> SentenceH C R
| subsume  : C → C → SentenceH C R
| equiv    : C → C → SentenceH C R
| role_inc : Nr → Nr → SentenceH C R
deriving Repr, Inhabited, DecidableEq, Encodable

notation a " :ₐ " c:50 => SentenceH.assert_c a c
notation "_:ₐ" => SentenceH.blank_assert_c
notation "_:ᵣ" => SentenceH.blank_assert_r
notation "(" a ", " b ")" " :ᵣ " r:50 => SentenceH.assert_r a b r
infix:50 " ⊑ " => SentenceH.subsume
infix:50 " ≡ " => SentenceH.equiv
infix:50 " ⊑ᵣ " => SentenceH.role_inc

/-- A structural linear order obtained from the syntax's injective encoding. -/
instance SentenceH.instLinearOrder {C R : Type}
    [Encodable C] [Encodable R] : LinearOrder (@SentenceH Nr Ni C R) :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

def SentenceH.inames {C R : Type} : @SentenceH Nr Ni C R → Finset Ni
| .assert_c a _ => {a}
| .blank_assert_c _ => ∅
| .blank_assert_r _ => ∅
| .assert_r a b _ => {a, b}
| .subsume _ _ => ∅
| .equiv _ _ => ∅
| .role_inc _ _ => ∅

def FinsetSentenceH.inames {C R : Type} [Encodable C] [Encodable R] :
    Finset (@SentenceH Nr Ni C R) → Finset Ni
| S => (S.sort (fun φ ψ => φ ≤ ψ)).foldl
    (fun acc φ => acc ∪ φ.inames) ∅


-- Base Language ALCH
abbrev ALCH := @SentenceH Nr Ni (@Concept Nc Nr) (@RoleA Nr)
-- Intermediate and target Language, ALCH⁺(∩)
abbrev ALCHPI := @SentenceH Nr Ni (@ConceptP Nc Nr) (@RoleI Nr)

structure Interp where
  Δ : Type
  Δ_inhabited : Inhabited Δ
  individual_map : Ni → Δ
  concept_map : Nc → Δ → V2
  role_map    : Nr → Δ → Δ → V2

def Interp.C (i : @Interp Nc Nr Ni) : @ConceptP Nc Nr -> i.Δ -> V2
| ⊤, _ => True
| .atomic nc, d => i.concept_map nc d
| C ⊓ₜ D, d => i.C C d ∧ i.C D d
| C ⊔ₜ D, d => i.C C d ∨ i.C D d
| ∃[r] C, d => ∃ d', i.C C d' ∧ i.role_map r d d'
| ∀[r] C, d => ∀ d', i.role_map r d d' → i.C C d'

def Interp.R (i : @Interp Nc Nr Ni) : @RoleI Nr → i.Δ → i.Δ → V2
| .atomic r, d₁, d₂ => i.role_map r d₁ d₂
| .inter r s, d₁, d₂ => i.R r d₁ d₂ ∧ i.R s d₁ d₂

def Interp.S (i : @Interp Nc Nr Ni) : @ALCHPI Nc Nr Ni → V2
| a :ₐ C => i.C C (i.individual_map a)
| _:ₐ C => ∃ d, i.C C d
| _:ᵣ r => ∃ d d', i.R r d d'
| (a, b) :ᵣ r => i.R r (i.individual_map a) (i.individual_map b)
| C ⊑ D => ∀ d, i.C C d → i.C D d
| C ≡ D => i.S (C ⊑ D) ∧ i.S (D ⊑ C)
| r ⊑ᵣ s => ∀ d d', i.role_map r d d' → i.role_map s d d'
termination_by s => match s with | .equiv _ _ => 1 | _ => 0

def Interp.satisfies (i : @Interp Nc Nr Ni) (φ : @ALCHPI Nc Nr Ni) : Prop :=
  i.S φ
infix:50 " ⊨ " => Interp.satisfies

def Interp.satisfies_all (i : @Interp Nc Nr Ni) (K : Finset (@ALCHPI Nc Nr Ni)) : Prop :=
  ∀ φ ∈ K, i ⊨ φ
infix:50 " ⊨ " => Interp.satisfies_all

def entails (K : Finset (@ALCHPI Nc Nr Ni)) (φ : @ALCHPI Nc Nr Ni) : Prop :=
  ∀ i : @Interp Nc Nr Ni, i ⊨ K → i ⊨ φ
infix:50 " ⊨ " => entails

-- -- Phase 2: wK and AC Semantics

def wK_neg : V3 → V3
| .t => .f
| .e => .e
| .f => .t

prefix :70 "¬ₖ " => wK_neg

def wK_conj : V3 → V3 → V3
| .t, .t => .t
| .t, .e => .e
| .t, .f => .f
| .e, .t => .e
| .e, .e => .e
| .e, .f => .e
| .f, .t => .f
| .f, .e => .e
| .f, .f => .f

infix :70 " ∧ₖ " => wK_conj

def wK_disj : V3 → V3 → V3
| .t, .t => .t
| .t, .e => .e
| .t, .f => .t
| .e, .t => .e
| .e, .e => .e
| .e, .f => .e
| .f, .t => .t
| .f, .e => .e
| .f, .f => .f
infix :70 " ∨ₖ " => wK_disj

/-- Restricted Weak Kleene existential quantifier -/
noncomputable def wK_exists (X : Set V32) : V3 :=
  if H1: ⟨.t, .t⟩ ∈ X then .t
  else if H2: ∀ x ∈ X, x.1 = .e ∨ x.2 = .e then .e
  else if H3: ⟨.t, .t⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ .e ∧ x.2 ≠ .e then .f
  else by grind only
notation "∃ₖ " X => wK_exists X


noncomputable def wK_forall (X : Set V32) : V3 :=
  if H1: ⟨.t, .f⟩ ∉ X ∧ ⟨.t, .e⟩ ∉ X ∧ ∃ x ∈ X, x.1 ≠ .e ∧ x.2 ≠ .e then .t
  else if H2: ∀ x ∈ X, x.1 = .e ∨ x.2 = .e then .e
  else if H3: (⟨.t, .f⟩ ∈ X ∨ ⟨.t, .e⟩ ∈ X) ∧ ∃ x ∈ X, x.1 ≠ .e ∧ x.2 ≠ .e then .f
  else by grind only
notation "∀ₖ " X => wK_forall X

def ac_neg (v : V32) : V3 × V3 :=
  ⟨v.2, v.1⟩
prefix:70 "∼ₐ " => ac_neg

def ac_conj (v1 v2 : V32) : V3 × V3 :=
  ⟨v1.1 ∧ₖ v2.1, v1.2 ∨ₖ v2.2⟩
infix :70 " ∧ₐ " => ac_conj

def ac_disj (v1 v2 : V32) : V3 × V3 :=
  ⟨v1.1 ∨ₖ v2.1, v1.2 ∧ₖ v2.2⟩
infix :65 " ∨ₐ " => ac_disj

def pi_sel_aux (v : V32) (i : Fin 2) : V3 :=
  if i = 0 then v.1 else v.2

def pi_sel (v : V32 × V32) (i j : Fin 2) : V32 :=
  ⟨pi_sel_aux v.1 i, pi_sel_aux v.2 j⟩

def pi_sel_img (X : Set (V32 × V32)) (i j : Fin 2) : Set V32 :=
  { pi_sel v i j | v ∈ X }

noncomputable def ac_exists (X : Set (V32 × V32)) : V32 :=
  ⟨∃ₖ pi_sel_img X 0 0, ∀ₖ pi_sel_img X 0 1⟩
prefix:70 "∃ₐ " => ac_exists

noncomputable def ac_forall (X : Set (V32 × V32)) : V32 :=
  ⟨∀ₖ pi_sel_img X 0 0, ∃ₖ pi_sel_img X 0 1⟩
prefix:70 "∀ₐ " => ac_forall

/-- Weak Kleene Interpretation -/
structure WKInterp  where
  Δ : Type
  Δ_inhabited : Inhabited Δ
  individual_map : Ni → Δ
  concept_map : Nc → Δ → V3
  role_map    : Nr → Δ → Δ → V3

/-- Weak Kleene Interpretations On Concepts -/
noncomputable def WKInterp.C (I : @WKInterp Nc Nr Ni) : @ConceptP Nc Nr → I.Δ → V3
| ⊤, _ => .t
| .atomic nc, d => I.concept_map nc d
| C ⊓ₜ D, d => (I.C C d) ∧ₖ (I.C D d)
| C ⊔ₜ D, d => (I.C C d) ∨ₖ (I.C D d)
| ∃[r] C, d => ∃ₖ { ⟨I.role_map r d d', I.C C d'⟩ | d' : I.Δ }
| ∀[r] C, d => ∀ₖ { ⟨I.role_map r d d', I.C C d'⟩ | d' : I.Δ }

/-- Weak Kleene interpretations of intersection roles. -/
def WKInterp.R (I : @WKInterp Nc Nr Ni) : @RoleI Nr → I.Δ → I.Δ → V3
| .atomic r, d₁, d₂ => I.role_map r d₁ d₂
| .inter r s, d₁, d₂ => I.R r d₁ d₂ ∧ₖ I.R s d₁ d₂

/-- Weak Kleene Interpretations On Sentences -/
noncomputable def WKInterp.S (I : @WKInterp Nc Nr Ni) : @ALCHPI Nc Nr Ni → V3
|  a :ₐ C => I.C C (I.individual_map a)
| (a, b) :ᵣ r => I.R r (I.individual_map a) (I.individual_map b)
| C ⊑ D => ∀ₖ { ⟨I.C C d, I.C D d⟩ | d : I.Δ }
| C ≡ D => (I.S (C ⊑ D)) ∧ₖ (I.S (D ⊑ C))
| r ⊑ᵣ s => ∀ₖ { ⟨I.role_map r p.1 p.2, I.role_map s p.1 p.2⟩ | p : I.Δ × I.Δ }
termination_by s => match s with | .equiv _ _ => 1 | _ => 0

def WKInterp.satisfies (I : @WKInterp Nc Nr Ni) (s : @ALCHPI Nc Nr Ni) : Prop :=
  I.S s = .t
infix:50 " ⊨ₖ " => WKInterp.satisfies

def WKInterp.satisfies_all (I : @WKInterp Nc Nr Ni) (K : Set (@ALCHPI Nc Nr Ni)) : Prop :=
  ∀ s ∈ K, I ⊨ₖ s
infix:50 " ⊨ₖ " => WKInterp.satisfies_all

def entails_wk (K : Set (@ALCHPI Nc Nr Ni)) (s : @ALCHPI Nc Nr Ni) : Prop :=
  ∀ I : @WKInterp Nc Nr Ni, I ⊨ₖ K → I ⊨ₖ s
infix:50 " ⊨ₖ " => entails_wk

structure ACInterp  where
  Δ : Type
  Δ_inhabited : Inhabited Δ
  individual_map : Ni → Δ
  concept_map : @Concept Nc Nr → Δ → V32
  role_map    : Nr → Δ → Δ → V32

noncomputable def ACInterp.C (I : @ACInterp Nc Nr Ni) : @Concept Nc Nr → I.Δ → V32
| .top, _ => ⟨.t, default⟩
| .bot, _ => ⟨default, .t⟩
| .atomic nc, d => I.concept_map nc d
| ¬ₜ C, d =>  ∼ₐ I.C C d
| C ⊓ₜ D, d => (I.C C d) ∧ₐ (I.C D d)
| C ⊔ₜ D, d => (I.C C d) ∨ₐ (I.C D d)
| ∃[r] C, d => ∃ₐ { ⟨I.role_map r d d', I.C C d'⟩ | d' : I.Δ }
| ∀[r] C, d => ∀ₐ { ⟨I.role_map r d d', I.C C d'⟩ | d' : I.Δ }

noncomputable def ACInterp.S (I : @ACInterp Nc Nr Ni) : @ALCH Nc Nr Ni → V32
|  a :ₐ C => I.C C (I.individual_map a)
| (a, b) :ᵣ .atomic r => I.role_map r (I.individual_map a) (I.individual_map b)
| C ⊑ D => ∀ₐ { ⟨I.C C d, I.C D d⟩ | d : I.Δ }
| C ≡ D => (I.S (C ⊑ D)) ∧ₐ (I.S (D ⊑ C))
| r ⊑ᵣ s => ∀ₐ { ⟨I.role_map r p.1 p.2, I.role_map s p.1 p.2⟩ | p : I.Δ × I.Δ }
termination_by s => match s with | .equiv _ _ => 1 | _ => 0

def ACInterp.satisfies (I : @ACInterp Nc Nr Ni) (s : @ALCH Nc Nr Ni) : Prop :=
  (I.S s).1 = .t
infix:50 " ⊨ₐ " => ACInterp.satisfies

def ACInterp.satisfies_all (I : @ACInterp Nc Nr Ni) (K : Set (@ALCH Nc Nr Ni)) : Prop :=
  ∀ s ∈ K, I ⊨ₐ s
infix:50 " ⊨ₐ " => ACInterp.satisfies_all

def entails_ac (K : Set (@ALCH Nc Nr Ni)) (s : @ALCH Nc Nr Ni) : Prop :=
  ∀ I : @ACInterp Nc Nr Ni, I ⊨ₐ K → I ⊨ₐ s
infix:50 " ⊨ₐ " => entails_ac

noncomputable def StarInterp (I : @WKInterp Nc Nr Ni) : @WKInterp Nc Nr Ni where
  Δ := I.Δ
  Δ_inhabited := I.Δ_inhabited
  individual_map := I.individual_map
  concept_map := fun C d => if I.concept_map C d ≠ .e then .t else .e
  role_map := fun r d1 d2 => if I.role_map r d1 d2 ≠ .e then .t else .e

-- lemma StarInterp_lifts (I : @WKInterp Nc Nr Ni) (φ : @ALCHPI Nc Nr Ni) :
--   (StarInterp I).S φ = if I.S φ ≠ .e then .t else .e := by
--   sorry

/-- `StarInterp_lifts` is false for the restricted universal semantics.

At `false`, the pair of values for `A` and `B` is `(f, f)`; at `true`, it is
`(f, e)`.  Thus `I.S (A ⊑ B) = t`.  After applying `StarInterp`, the pairs
become `(t, t)` and `(t, e)`, so the same subsumption has value `f`, rather than
the `t` predicted by `StarInterp_lifts`. -/
theorem not_StarInterp_lifts :
    let I : @WKInterp Bool Unit Unit :=
      { Δ := Bool
        Δ_inhabited := inferInstance
        individual_map := fun _ => false
        concept_map := fun C d =>
          match C, d with
          | false, _ => .f
          | true, false => .f
          | true, true => .e
        role_map := fun _ _ _ => .f }
    let φ : @ALCHPI Bool Unit Unit :=
      (ConceptP.atomic false) ⊑ (ConceptP.atomic true)
    (StarInterp I).S φ ≠ if I.S φ ≠ .e then .t else .e := by
  dsimp
  simp only [WKInterp.S, WKInterp.C, StarInterp, wK_forall]
  simp
  split_ifs <;> decide

structure TauBase where
  c : Nc → Nc
  r : Nr → Nr
  c_injective : Function.Injective c
  r_injective : Function.Injective r

structure PiBase where
  c : Nc → Nc
  r : Nr → Nr
  -- These may need to be bijective

def TauBase.R (τ : @TauBase Nc Nr) : @RoleI Nr → @RoleI Nr
| .atomic r => .atomic (τ.r r)
| r ⊓ᵣ s => (τ.R r) ⊓ᵣ (τ.R s)

omit [DecidableEq Nc] [Repr Nc] [Inhabited Nc] [HasFresh Nc]
    [DecidableEq Nr] [Repr Nr] [Inhabited Nr] [HasFresh Nr] in
lemma TauBase.R_injective (τ : @TauBase Nc Nr) : Function.Injective τ.R := by
  intro R
  induction R with
  | atomic r =>
      intro S h
      cases S with
      | atomic s =>
          injection h with hrs
          exact congrArg RoleI.atomic (τ.r_injective hrs)
      | inter _ _ => cases h
  | inter r s ihr ihs =>
      intro S h
      cases S with
      | atomic _ => cases h
      | inter r' s' =>
          injection h with hr hs
          exact congrArg₂ RoleI.inter (ihr hr) (ihs hs)

def TauBase.C (τ : @TauBase Nc Nr) : @ConceptP Nc Nr → @ConceptP Nc Nr
| ⊤ => ⊤
| .atomic C => τ.c C
| C ⊓ₜ D => (τ.C C) ⊓ₜ (τ.C D)
| C ⊔ₜ D => (τ.C C) ⊔ₜ (τ.C D)
| ∃[r] C => ∃[τ.r r] (τ.C C)
| ∀[r] C => ∀[τ.r r] (τ.C C)

omit [DecidableEq Nc] [Repr Nc] [Inhabited Nc] [HasFresh Nc]
    [DecidableEq Nr] [Repr Nr] [Inhabited Nr] [HasFresh Nr] in
lemma TauBase.C_injective (τ : @TauBase Nc Nr) : Function.Injective τ.C := by
  intro C
  induction C with
  | top => intro D h; cases D <;> cases h; rfl
  | atomic c =>
      intro D h
      cases D with
      | atomic d =>
          injection h with hcd
          exact congrArg ConceptP.atomic (τ.c_injective hcd)
      | top | conj _ _ | disj _ _ | exis _ _ | univ _ _ => cases h
  | conj C D ihC ihD =>
      intro E h
      cases E with
      | conj C' D' =>
          injection h with hC hD
          exact congrArg₂ ConceptP.conj (ihC hC) (ihD hD)
      | top | atomic _ | disj _ _ | exis _ _ | univ _ _ => cases h
  | disj C D ihC ihD =>
      intro E h
      cases E with
      | disj C' D' =>
          injection h with hC hD
          exact congrArg₂ ConceptP.disj (ihC hC) (ihD hD)
      | top | atomic _ | conj _ _ | exis _ _ | univ _ _ => cases h
  | exis r C ihC =>
      intro D h
      cases D with
      | exis s D =>
          injection h with hrs hC
          exact congrArg₂ ConceptP.exis (τ.r_injective hrs) (ihC hC)
      | top | atomic _ | conj _ _ | disj _ _ | univ _ _ => cases h
  | univ r C ihC =>
      intro D h
      cases D with
      | univ s D =>
          injection h with hrs hC
          exact congrArg₂ ConceptP.univ (τ.r_injective hrs) (ihC hC)
      | top | atomic _ | conj _ _ | disj _ _ | exis _ _ => cases h

def ALCHPI.Tau (τ : @TauBase Nc Nr) : @ALCHPI Nc Nr Ni → @ALCHPI Nc Nr Ni
| a :ₐ C => a :ₐ (τ.C C)
| (a, b) :ᵣ r => (a, b) :ᵣ τ.R r
| C ⊑ D => (τ.C C) ⊑ (τ.C D)
| C ≡ D => (τ.C C) ≡ (τ.C D)
| r ⊑ᵣ s => (τ.r r) ⊑ᵣ (τ.r s)

omit [DecidableEq Nc] [Repr Nc] [Inhabited Nc] [HasFresh Nc]
    [DecidableEq Nr] [Repr Nr] [Inhabited Nr] [HasFresh Nr]
    [DecidableEq Ni] [Repr Ni] [Inhabited Ni] [HasFresh Ni] in
lemma ALCHPI.Tau_injective (τ : @TauBase Nc Nr) :
    Function.Injective (ALCHPI.Tau (Ni := Ni) τ) := by
  intro φ ψ h
  cases φ with
  | assert_c a C =>
      cases ψ with
      | assert_c b D =>
          injection h with hab hCD
          exact congrArg₂ SentenceH.assert_c hab (τ.C_injective hCD)
      | assert_r _ _ _ | subsume _ _ | equiv _ _ | role_inc _ _ => cases h
  | assert_r a b r =>
      cases ψ with
      | assert_r c d s =>
          injection h with hac hbd hrs
          have hrs' := τ.R_injective hrs
          cases hac
          cases hbd
          cases hrs'
          rfl
      | assert_c _ _ | subsume _ _ | equiv _ _ | role_inc _ _ => cases h
  | subsume C D =>
      cases ψ with
      | subsume E F =>
          injection h with hCE hDF
          exact congrArg₂ SentenceH.subsume (τ.C_injective hCE) (τ.C_injective hDF)
      | assert_c _ _ | assert_r _ _ _ | equiv _ _ | role_inc _ _ => cases h
  | equiv C D =>
      cases ψ with
      | equiv E F =>
          injection h with hCE hDF
          exact congrArg₂ SentenceH.equiv (τ.C_injective hCE) (τ.C_injective hDF)
      | assert_c _ _ | assert_r _ _ _ | subsume _ _ | role_inc _ _ => cases h
  | role_inc r s =>
      cases ψ with
      | role_inc r' s' =>
          injection h with hr hs
          exact congrArg₂ SentenceH.role_inc (τ.r_injective hr) (τ.r_injective hs)
      | assert_c _ _ | assert_r _ _ _ | subsume _ _ | equiv _ _ => cases h

def ALCHPI.Tau_all (τ : @TauBase Nc Nr) (S : Finset (@ALCHPI Nc Nr Ni)) : Finset (@ALCHPI Nc Nr Ni) :=
  S.map ⟨ALCHPI.Tau τ, ALCHPI.Tau_injective τ⟩

def PiBase.R (π : @PiBase Nc Nr) : @RoleI Nr → @RoleI Nr
| .atomic r => .atomic (π.r r)
| r ⊓ᵣ s => (π.R r) ⊓ᵣ (π.R s)

def PiBase.C (π : @PiBase Nc Nr) : @ConceptP Nc Nr → @ConceptP Nc Nr
| ⊤ => ⊤
| .atomic C => π.c C
| C ⊓ₜ D => (π.C C) ⊓ₜ (π.C D)
| C ⊔ₜ D => (π.C C) ⊓ₜ (π.C D)
| ∃[r] C => ∃[π.r r] (π.C C)
| ∀[r] C => ∃[π.r r] (π.C C)

def ALCHPI.Pi (π : @PiBase Nc Nr) (F : Finset Ni) : @ALCHPI Nc Nr Ni → @ALCHPI Nc Nr Ni × Finset Ni
| a :ₐ C => (a :ₐ (π.C C), F)
| (a, b) :ᵣ .atomic r => ((a, b) :ᵣ .atomic (π.r r), F)
| C ⊑ D => let f1 := HasFresh.fresh F; (f1 :ₐ (π.C C) ⊓ₜ (π.C D), F ∪ {f1})
| C ≡ D => let f1 := HasFresh.fresh F; (f1 :ₐ (π.C C) ⊓ₜ (π.C D), F ∪ {f1})
| r ⊑ᵣ s => let ⟨f1,f2⟩ := HasFresh.fresh2 F ; ((f1, f2) :ᵣ (.atomic (π.r r)) ⊓ᵣ (.atomic (π.r s)), F ∪ {f1, f2})
| (a, b) :ᵣ r ⊓ᵣ s => ((a, b) :ᵣ (π.R r) ⊓ᵣ (π.R s), ∅)


def ALCHPI.Pi_all (π : @PiBase Nc Nr) (F : Finset Ni) (S : Finset (@ALCHPI Nc Nr Ni)) : Finset (@ALCHPI Nc Nr Ni) × Finset Ni :=
  S.sort (fun φ ψ => φ ≤ ψ) |>.foldl (fun (acc : Finset (@ALCHPI Nc Nr Ni) × Finset Ni) φ =>
    let (φ', F') := ALCHPI.Pi π acc.2 φ
    (acc.1 ∪ {φ'}, F')) (∅, F)

theorem wk_c_faithful (K : Finset (@ALCHPI Nc Nr Ni)) (φ : @ALCHPI Nc Nr Ni) (τ : @TauBase Nc Nr) (π : @PiBase Nc Nr) :
  let Kτ := ALCHPI.Tau_all τ K
  let φτ := ALCHPI.Tau τ φ
  let (Kπ, Fπ) := ALCHPI.Pi_all π (FinsetSentenceH.inames Kτ ∪ φτ.inames) K
  let (φπ, Fφ) := ALCHPI.Pi π Fπ φτ
  K ⊨ₖ φ ↔ Kπ ⊨ φπ ∧ Kτ ⊨ φτ := by
  sorry

end BiALCH
