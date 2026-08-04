

import Mathlib

namespace BiALCH

abbrev V2 := Bool

inductive V3 where
| t
| e
| f
deriving Repr, DecidableEq

variable {Nc : Type} [DecidableEq Nc] [Repr Nc] [Inhabited Nc] [Fintype Nc]
variable {Nr : Type} [DecidableEq Nr] [Repr Nr] [Inhabited Nr] [Fintype Nr]
variable {Ni : Type} [DecidableEq Ni] [Repr Ni] [Inhabited Ni] [Fintype Ni]

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
  Δ_fintype : Fintype Δ
  individual_map : Ni → Δ
  concept_map : Nc → Δ → V2
  role_map    : Nr → Δ → Δ → V2

def Interp.I (i : @Interp Nc Nr Ni) : @Sentence Nc Nr Ni → V2
| _ :ₐ ⊤ => true
| _ :ₐ ⊥ => false
| a :ₐ .atomic nc => i.concept_map nc (i.individual_map a)
| a :ₐ ¬ₜC => ¬i.I (a :ₐ C)
| a :ₐ C1 ⊓ₜ C2 => i.I (a :ₐ C1) ∧ i.I (a :ₐ C2)
| a :ₐ C1 ⊔ₜ C2 => i.I (a :ₐ C1) ∨ i.I (a :ₐ C2)
| a :ₐ ∃[r] C => ∃ b, i.I (b :ₐ C) ∧ i.I ((a, b) :ᵣ r)
| a :ₐ ∀[r] C => ∀ b, i.I (b :ₐ C) → i.I ((a, b) :ᵣ r)
| (a, b) :ᵣ r => i.role_map r (i.individual_map a) (i.individual_map b)
| C1 ⊑ C2 => ∀ a, i.I (a :ₐ C1) → i.I (a :ₐ C2)
| C1 ≡ C2 => ∀ a, i.I (a :ₐ C1) ↔ i.I (a :ₐ C2)
| r1 ⊑ᵣ r2 => ∀ a b, i.I ((a, b) :ᵣ r1) → i.I ((a, b) :ᵣ r2)
termination_by s => s.complexity
decreasing_by
  all_goals simp only [Sentence.complexity, Concept.complexity]; omega


postfix:100 "ᴵ " => Interp.I

def Interp.satisfies (i : @Interp Nc Nr Ni) (s : @Sentence Nc Nr Ni) : Bool :=
  i.I s




-- -- Phase 2: wK and AC Semantics

-- /-- Weak Kleene negation -/
-- def wK_neg (v : TruthValue3) : TruthValue3 :=
--   match v with
--   | .t => .f
--   | .u => .u
--   | .f => .t

-- /-- Weak Kleene conjunction -/
-- def wK_conj (v1 v2 : TruthValue3) : TruthValue3 :=
--   match v1, v2 with
--   | .t, .t => .t
--   | .t, .u => .u
--   | .t, .f => .f
--   | .u, .t => .u
--   | .u, .u => .u
--   | .u, .f => .u
--   | .f, .t => .f
--   | .f, .u => .u
--   | .f, .f => .f

-- /-- Weak Kleene disjunction -/
-- def wK_disj (v1 v2 : TruthValue3) : TruthValue3 :=
--   match v1, v2 with
--   | .t, .t => .t
--   | .t, .u => .u
--   | .t, .f => .t
--   | .u, .t => .u
--   | .u, .u => .u
--   | .u, .f => .u
--   | .f, .t => .t
--   | .f, .u => .u
--   | .f, .f => .f

-- /-- Restricted Weak Kleene existential quantifier -/
-- def wK_exists (X : Set (TruthValue3 × TruthValue3)) : TruthValue3 :=
--   if X.Exists (λ p => p == ⟨.t, .t⟩) then .t
--   else if X.Forall (λ p => p.1 == .u ∨ p.2 == .u) then .u
--   else .f

-- /-- Restricted Weak Kleene universal quantifier -/
-- def wK_forall (X : Set (TruthValue3 × TruthValue3)) : TruthValue3 :=
--   let no_bad := not (X.Exists (λ p => p == ⟨.t, .f⟩ ∨ p == ⟨.t, .u⟩))
--   let some_meaningful := X.Exists (λ p => p.1 ≠ .u ∧ p.2 ≠ .u)
--   if no_bad ∧ some_meaningful then .t
--   else if X.Forall (λ p => p.1 == .u ∨ p.2 == .u) then .u
--   else .f

-- /-- Bilateral truth values for AC logic -/
-- def BilateralValue := TruthValue3 × TruthValue3

-- /-- AC negation -/
-- def ac_neg (v : BilateralValue) : BilateralValue :=
--   ⟨v.2, v.1⟩

-- /-- AC conjunction -/
-- def ac_conj (v1 v2 : BilateralValue) : BilateralValue :=
--   ⟨wK_conj v1.1 v2.1, wK_disj v1.2 v2.2⟩

-- /-- AC disjunction -/
-- def ac_disj (v1 v2 : BilateralValue) : BilateralValue :=
--   ⟨wK_disj v1.1 v2.1, wK_conj v1.2 v2.2⟩

-- /-- Projection helper for bilateral quantifiers -/
-- def pi (i j : Nat) (v1 v2 : BilateralValue) : TruthValue3 :=
--   let coords1 := [v1.1, v1.2]
--   let coords2 := [v2.1, v2.2]
--   match i, j with
--   | 0, 0 => v1.1
--   | 0, 1 => v1.2 -- This is wrong based on paper: "ith coordinate of <u0, v0> and jth coordinate of <u1, v1>"
--   | _, _  => .u

-- /-- Let's fix pi to actually be the projection from (v1, v2) to TruthValue3 -/
-- def proj (i j : Nat) (p : BilateralValue × BilateralValue) : TruthValue3 :=
--   match i, j with
--   | 0, 0 => p.1.1
--   | 0, 1 => p.1.2 -- This is also wrong based on paper: "ith coordinate of <u0, v0> and the jth coordinate of <u1, v1>"
--   | _, _  => .u

-- -- Phase 3: Interpretations and Satisfaction

-- /-- Classical Interpretation -/
-- structure ClassicalInterp (Σ : Signature) where
--   domain : Type
--   concept_map : Concept Σ → (domain → TruthValue2)
--   role_map    : Σ.nr → (domain → domain → TruthValue2)

-- /-- Weak Kleene Interpretation -/
-- structure WKInterp (Σ : Signature) where
--   domain : Type
--   concept_map : Concept Σ → (domain → TruthValue3)
--   role_map    : Σ.nr → (domain → domain → TruthValue3)

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
