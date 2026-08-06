

import Mathlib

namespace BiALCH

abbrev V2 := Prop

inductive V3 where
| t
| e
| f
deriving Inhabited, Repr, DecidableEq

instance : Fintype V3 where
  elems := {.t, .e, .f}
  complete x := by cases x <;> simp

abbrev V32 := V3 × V3

-- We can decide membership in a set of pairs
noncomputable instance (X : Set V32) (x : V32) : Decidable (x ∈ X) :=
  Classical.propDecidable _

variable {Nc : Type} [DecidableEq Nc] [Repr Nc] [Inhabited Nc]
variable {Nr : Type} [DecidableEq Nr] [Repr Nr] [Inhabited Nr]
variable {Ni : Type} [DecidableEq Ni] [Repr Ni] [Inhabited Ni]

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
deriving Inhabited, Repr

def Concept.complexity : @Concept Nc Nr → Nat
| .top | .bot | .atomic _ => 0
| .neg C | .exis _ C | .univ _ C => C.complexity + 1
| .conj C D | .disj C D => C.complexity + D.complexity + 1

instance : Top (@Concept Nc Nr) := ⟨Concept.top⟩
instance : Bot (@Concept Nc Nr) := ⟨Concept.bot⟩
infixl:70 " ⊓ₜ " => Concept.conj
infixl:65 " ⊔ₜ " => Concept.disj
notation "¬ₜ " c:75 => Concept.neg c
notation "∃[" r "]" c:75 => Concept.exis r c
notation "∀[" r "]" c:75 => Concept.univ r c
instance : Coe Nc (@Concept Nc Nr) := ⟨Concept.atomic⟩

example (A B: Nc) (R : Nr) : @Concept Nc Nr := A ⊓ₜ ∃[R] B ⊓ₜ (∀[R] ¬ₜA)

/-- ALCH Sentences -/
inductive Sentence where
| assert_c : Ni → @Concept Nc Nr → Sentence
| assert_r : Ni → Ni → Nr → Sentence
| subsume  : @Concept Nc Nr → @Concept Nc Nr → Sentence
| equiv    : @Concept Nc Nr → @Concept Nc Nr → Sentence
| role_inc : Nr → Nr → Sentence
deriving Repr, Inhabited

notation a " :ₐ " c:50 => Sentence.assert_c a c
notation "(" a ", " b ")" " :ᵣ " r:50 => Sentence.assert_r a b r
infix:50 " ⊑ " => Sentence.subsume
infix:50 " ≡ " => Sentence.equiv
infix:50 " ⊑ᵣ " => Sentence.role_inc

def Sentence.complexity : @Sentence Nc Nr Ni → Nat
| .assert_c _ C => C.complexity + 1
| .assert_r _ _ _ => 0
| .subsume C D | .equiv C D => C.complexity + D.complexity + 2
| .role_inc _ _ => 1

structure Interp where
  Δ : Type
  Δ_inhabited : Inhabited Δ
  individual_map : Ni → Δ
  concept_map : Nc → Δ → V2
  role_map    : Nr → Δ → Δ → V2

def Interp.C (i : @Interp Nc Nr Ni) : @Concept Nc Nr -> i.Δ -> V2
| ⊤, _ => True
| .bot, _ => False
| .atomic nc, d => i.concept_map nc d
| ¬ₜ C, d => ¬ i.C C d
| C ⊓ₜ D, d => i.C C d ∧ i.C D d
| C ⊔ₜ D, d => i.C C d ∨ i.C D d
| ∃[r] C, d => ∃ d', i.C C d' ∧ i.role_map r d d'
| ∀[r] C, d => ∀ d', i.role_map r d d' → i.C C d'

def Interp.S (i : @Interp Nc Nr Ni) : @Sentence Nc Nr Ni → V2
|  a :ₐ C => i.C C (i.individual_map a)
| (a, b) :ᵣ r => i.role_map r (i.individual_map a) (i.individual_map b)
| C ⊑ D => ∀ d, i.C C d → i.C D d
| C ≡ D => i.S (C ⊑ D) ∧ i.S (D ⊑ C)
| r ⊑ᵣ s => ∀ d d', i.role_map r d d' → i.role_map s d d'
termination_by s => match s with | .equiv _ _ => 1 | _ => 0

def Interp.satisfies (i : @Interp Nc Nr Ni) (s : @Sentence Nc Nr Ni) : Prop :=
  i.S s
infix:50 " ⊨ " => Interp.satisfies

def Interp.satisfies_all (i : @Interp Nc Nr Ni) (K : Set (@Sentence Nc Nr Ni)) : Prop :=
  ∀ s ∈ K, i ⊨ s
infix:50 " ⊨ " => Interp.satisfies_all

def entails (K : Set (@Sentence Nc Nr Ni)) (s : @Sentence Nc Nr Ni) : Prop :=
  ∀ i : @Interp Nc Nr Ni, i ⊨ K → i ⊨ s
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
  concept_map : @Concept Nc Nr → Δ → V3
  role_map    : Nr → Δ → Δ → V3

/-- Weak Kleene Interpretations On Concepts -/
noncomputable def WKInterp.C (I : @WKInterp Nc Nr Ni) : @Concept Nc Nr → I.Δ → V3
| .top, _ => .t
| .bot, _ => .f
| .atomic nc, d => I.concept_map nc d
| ¬ₜ C, d =>  ¬ₖ I.C C d
| C ⊓ₜ D, d => (I.C C d) ∧ₖ (I.C D d)
| C ⊔ₜ D, d => (I.C C d) ∨ₖ (I.C D d)
| ∃[r] C, d => ∃ₖ { ⟨I.role_map r d d', I.C C d'⟩ | d' : I.Δ }
| ∀[r] C, d => ∀ₖ { ⟨I.role_map r d d', I.C C d'⟩ | d' : I.Δ }

/-- Weak Kleene Interpretations On Sentences -/
noncomputable def WKInterp.S (I : @WKInterp Nc Nr Ni) : @Sentence Nc Nr Ni → V3
|  a :ₐ C => I.C C (I.individual_map a)
| (a, b) :ᵣ r => I.role_map r (I.individual_map a) (I.individual_map b)
| C ⊑ D => ∀ₖ { ⟨I.C C d, I.C D d⟩ | d : I.Δ }
| C ≡ D => (I.S (C ⊑ D)) ∧ₖ (I.S (D ⊑ C))
| r ⊑ᵣ s => ∀ₖ { ⟨I.role_map r p.1 p.2, I.role_map s p.1 p.2⟩ | p : I.Δ × I.Δ }
termination_by s => match s with | .equiv _ _ => 1 | _ => 0

def WKInterp.satisfies (I : @WKInterp Nc Nr Ni) (s : @Sentence Nc Nr Ni) : Prop :=
  I.S s = .t
infix:50 " ⊨ₖ " => WKInterp.satisfies

def WKInterp.satisfies_all (I : @WKInterp Nc Nr Ni) (K : Set (@Sentence Nc Nr Ni)) : Prop :=
  ∀ s ∈ K, I ⊨ₖ s
infix:50 " ⊨ₖ " => WKInterp.satisfies_all

def entails_wk (K : Set (@Sentence Nc Nr Ni)) (s : @Sentence Nc Nr Ni) : Prop :=
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

noncomputable def ACInterp.S (I : @ACInterp Nc Nr Ni) : @Sentence Nc Nr Ni → V32
|  a :ₐ C => I.C C (I.individual_map a)
| (a, b) :ᵣ r => I.role_map r (I.individual_map a) (I.individual_map b)
| C ⊑ D => ∀ₐ { ⟨I.C C d, I.C D d⟩ | d : I.Δ }
| C ≡ D => (I.S (C ⊑ D)) ∧ₐ (I.S (D ⊑ C))
| r ⊑ᵣ s => ∀ₐ { ⟨I.role_map r p.1 p.2, I.role_map s p.1 p.2⟩ | p : I.Δ × I.Δ }
termination_by s => match s with | .equiv _ _ => 1 | _ => 0

def ACInterp.satisfies (I : @ACInterp Nc Nr Ni) (s : @Sentence Nc Nr Ni) : Prop :=
  (I.S s).1 = .t
infix:50 " ⊨ₐ " => ACInterp.satisfies

def ACInterp.satisfies_all (I : @ACInterp Nc Nr Ni) (K : Set (@Sentence Nc Nr Ni)) : Prop :=
  ∀ s ∈ K, I ⊨ₐ s
infix:50 " ⊨ₐ " => ACInterp.satisfies_all

def entails_ac (K : Set (@Sentence Nc Nr Ni)) (s : @Sentence Nc Nr Ni) : Prop :=
  ∀ I : @ACInterp Nc Nr Ni, I ⊨ₐ K → I ⊨ₐ s
infix:50 " ⊨ₐ " => entails_ac





-- /-- Bilateral ($\mathsf{AC}$) Interpretation -/
-- structure BilateralInterp (Σ : Signature) where
--   domain : Type
--   concept_map : Concept Σ → (domain → BilateralValue)
--   role_map    : Σ.nr → (domain → domain → BilateralValue)

-- /-- Recursive evaluation for WK interpretation -/
-- def eval_wk {Σ : Signature} (I : WKInterp Σ) (C : Concept Σ) (a : I.domain) : TruthValue3 :=
--   match C with
--   | .top        => .t
--   | .bot        => .f
--   | .atomic nc  => I.concept_map (.atomic nc) a
--   | .neg C'     => wK_neg (eval_wk I C' a)
--   | .conj C1 C2 => wK_conj (eval_wk I C1 a) (eval_wk I C2 a)
--   | .disj C1 C2 => wK_disj (eval_wk I C1 a) (eval_wk I C2 a)
--   | .exis r C'  =>
--       let X := { ⟨I.role_map r a b, eval_wk I C' b⟩ | b ∈ I.domain }
--       wK_exists X
--   | .univ r C'  =>
--       let X := { ⟨I.role_map r a b, eval_wk I C' b⟩ | b ∈ I.domain }
--       wK_forall X

-- /-- Recursive evaluation for Bilateral interpretation -/
-- def eval_bilat {Σ : Signature} (I : BilateralInterp Σ) (C : Concept Σ) (a : I.domain) : BilateralValue :=
--   match C with
--   | .top        => ⟨.t, .u⟩ -- Based on "I(a:top) = <vt, v>" where v is any wK value. Using .u as default.
--   | .bot        => ⟨.u, .t⟩ -- Based on "I(a:bot) = <v, vt>"
--   | .atomic nc  => I.concept_map (.atomic nc) a
--   | .neg C'     => ac_neg (eval_bilat I C' a)
--   | .conj C1 C2 => ac_conj (eval_bilat I C1 a) (eval_bilat I C2 a)
--   | .disj C1 C2 => ac_disj (eval_bilat I C1 a) (eval_bilat I C2 a)
--   | .exis r C'  =>
--       let X := { ⟨eval_bilat_role I r a b, eval_bilat_fixed I C' b⟩ | b ∈ I.domain }
--       ac_exists X
--   | .univ r C'  =>
--       let X := { ⟨eval_bilat_role I r a b, eval_bilat_fixed I C' b⟩ | b ∈ I.domain }
--       ac_forall X

-- /-- Wait, the bilateral interpretation requires evaluation of roles as well -/
-- def eval_bilat_role {Σ : Signature} (I : BilateralInterp Σ) (r : Σ.nr) (a b : I.domain) : BilateralValue :=
--   I.role_map r a b

-- /-- Corrected recursive evaluation for Bilateral concepts -/
-- def eval_bilat_fixed {Σ : Signature} (I : BilateralInterp Σ) (C : Concept Σ) (a : I.domain) : BilateralValue :=
--   match C with
--   | .top        => ⟨.t, .u⟩
--   | .bot        => ⟨.u, .t⟩
--   | .atomic nc  => I.concept_map (.atomic nc) a
--   | .neg C'     => ac_neg (eval_bilat_fixed I C' a)
--   | .conj C1 C2 => ac_conj (eval_bilat_fixed I C1 a) (eval_bilat_fixed I C2 a)
--   | .disj C1 C2 => ac_disj (eval_bilat_fixed I C1 a) (eval_bilat_fixed I C2 a)
--   | .exis r C'  =>
--       let X := { ⟨eval_bilat_role I r a b, eval_bilat_fixed I C' b⟩ | b ∈ I.domain }
--       ac_exists X
--   | .univ r C'  =>
--       let X := { ⟨eval_bilat_role I r a b, eval_bilat_fixed I C' b⟩ | b ∈ I.domain }
--       ac_forall X

-- /-- Satisfaction for Bilateral Logic -/
-- def satisfies_bilat {Σ : Signature} (I : BilateralInterp Σ) (C : Concept Σ) (a : I.domain) : Prop :=
--   (eval_bilat_fixed I C a).1 = .t

-- /-- satisfaction for WK logic -/
-- def satisfies_wk {Σ : Signature} (I : WKInterp Σ) (C : Concept Σ) (a : I.domain) : Prop :=
--   eval_wk I C a = .t

-- /-- Satisfaction for Sentences in Bilateral Logic -/
-- def satisfies_sentence_bilat {Σ : Signature} (I : BilateralInterp Σ) (S : Sentence Σ) : Prop :=
--   match S with
--   | .assert_c a C     => satisfies_bilat I C a
--   | .assert_r a b r   => (I.role_map r a b).1 = .t
--   | .subsume C D     =>
--       let X := { ⟨eval_bilat_fixed I C a, eval_bilat_fixed I D a⟩ | a ∈ I.domain }
--       (ac_forall X).1 = .t
--   | .equiv C D       =>
--       let X1 := { ⟨eval_bilat_fixed I C a, eval_bilat_fixed I D a⟩ | a ∈ I.domain }
--       let X2 := { ⟨eval_bilat_fixed I D a, eval_bilat_fixed I C a⟩ | a ∈ I.domain }
--       (ac_conj (ac_forall X1) (ac_forall X2)).1 = .t
--   | .role_inc r s    =>
--       let X := { ⟨I.role_map r a b, I.role_map s a b⟩ | a, b ∈ I.domain }
--       (ac_forall X).1 = .t

-- /-- Correcting the coordinate access in satisfies_sentence_bilat -/
-- /-- Since ac_forall returns BilateralValue (pair), we use (.1) to get first coord -/
-- -- Phase 5: Formal Verification Theorems

-- /-- The star-interpretation mapping TruthValue3 to {t, u} -/
-- def star_val (v : TruthValue3) : TruthValue3 :=
--   if v ≠ .u then .t else .u

-- /-- Lemma 1: I*(\varphi) = t iff I(\varphi) \neq e -/
-- theorem lemma_star_meaning {Σ : Signature} (I : WKInterp Σ) (C : Concept Σ) (a : I.domain) :
--   (eval_wk I C a ≠ .u) \iff (eval_wk I C a = .t) := by
--   sorry -- Proof by induction on Concept

-- /-- Definition of an AC Knowledge Base -/
-- structure KnowledgeBase (Σ : Signature) where
--   TBox : Set (Sentence Σ)
--   ABox : Set (Sentence Σ)

-- /-- Bilateral Entailment -/
-- def entails_bilat {Σ : Signature} (K : KnowledgeBase Σ) (S : Sentence Σ) : Prop :=
--   \forall I : BilateralInterp Σ,
--     ( \forall s \in K.TBox \cup K.ABox, satisfies_sentence_bilat I s ) \implies satisfies_sentence_bilat I S

-- /-- Theorem: Faithful Translation from AC to Classical -/
-- theorem theorem_faithful_translation {Σ : Signature} (K : KnowledgeBase Σ) (S : Sentence Σ) :
--   entails_bilat K S \iff
--     ( /* classical entailment for tau-pi translation */ true \land /* classical entailment for mu-pi translation */ true ) := by
--   sorry

-- /-- Daniels emulation set -/
-- def daniels_emulation {Σ : Signature} (K : KnowledgeBase Σ) (S : Sentence Σ) : Set (Sentence Σ) :=
--   { } -- This would contain the equivalences C^mu\pi \equiv C^mu\nu etc.

end BiALCH
