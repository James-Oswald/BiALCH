import Final

/-! `decideEntailment` searches finite signed branches for an ALCHRU
countermodel. The filtration below supplies a sufficient finite domain size,
and `decideEntailment_correct` connects the executable result to `entailmentC`. -/


namespace ALCHAC.ClassicalTableau

/-- A fully expanded, clash-free signed tableau branch. Positive and negative
labels are kept separately; `decided` makes the branch maximal. The expansion
rules cover all ALCHRU concept and role constructors. -/
structure Branch (σ : Signature) where
  Node : Type
  nonempty : Nonempty Node
  name : σ.Ni → Node
  posConcept : Node → 𝒞ᵁ σ → Prop
  negConcept : Node → 𝒞ᵁ σ → Prop
  posRole : Node → Node → ℛᵁ σ → Prop
  negRole : Node → Node → ℛᵁ σ → Prop
  concept_decided : ∀ x c, posConcept x c ∨ negConcept x c
  concept_clash : ∀ x c, ¬(posConcept x c ∧ negConcept x c)
  role_decided : ∀ x y r, posRole x y r ∨ negRole x y r
  role_clash : ∀ x y r, ¬(posRole x y r ∧ negRole x y r)
  top_pos : ∀ x, posConcept x ⊤
  bot_neg : ∀ x, negConcept x ⊥
  neg_pos : ∀ x c, posConcept x (¬ₜ c) ↔ negConcept x c
  conj_pos : ∀ x c d, posConcept x (c ⊓ₜ d) ↔
    posConcept x c ∧ posConcept x d
  disj_pos : ∀ x c d, posConcept x (c ⊔ₜ d) ↔
    posConcept x c ∨ posConcept x d
  ex_pos : ∀ x r c, posConcept x (∃[r] c) ↔
    ∃ y, posRole x y r ∧ posConcept y c
  all_pos : ∀ x r c, posConcept x (∀[r] c) ↔
    ∀ y, posRole x y r → posConcept y c
  universal_pos : ∀ x y, posRole x y 𝒰
  inter_pos : ∀ x y r s, posRole x y (r ⊓ᵣ s) ↔
    posRole x y r ∧ posRole x y s

variable {σ : Signature}

theorem Branch.negConcept_iff (B : Branch σ) (x : B.Node) (c : 𝒞ᵁ σ) :
    B.negConcept x c ↔ ¬B.posConcept x c := by
  constructor
  · intro hn hp
    exact B.concept_clash x c ⟨hp, hn⟩
  · intro hn
    rcases B.concept_decided x c with hp | hneg
    · exact False.elim (hn hp)
    · exact hneg

theorem Branch.negRole_iff (B : Branch σ) (x y : B.Node) (r : ℛᵁ σ) :
    B.negRole x y r ↔ ¬B.posRole x y r := by
  constructor
  · intro hn hp
    exact B.role_clash x y r ⟨hp, hn⟩
  · intro hn
    rcases B.role_decided x y r with hp | hneg
    · exact False.elim (hn hp)
    · exact hneg

theorem Branch.neg_neg (B : Branch σ) (x : B.Node) (c : 𝒞ᵁ σ) :
    B.negConcept x (¬ₜ c) ↔ B.posConcept x c := by
  classical
  rw [B.negConcept_iff, B.neg_pos, B.negConcept_iff]
  exact not_not

theorem Branch.neg_conj (B : Branch σ) (x : B.Node) (c d : 𝒞ᵁ σ) :
    B.negConcept x (c ⊓ₜ d) ↔ B.negConcept x c ∨ B.negConcept x d := by
  classical
  rw [B.negConcept_iff, B.conj_pos, B.negConcept_iff, B.negConcept_iff]
  constructor
  · intro h
    by_cases hc : B.posConcept x c
    · exact Or.inr (fun hd => h ⟨hc, hd⟩)
    · exact Or.inl hc
  · intro h hc
    cases h with
    | inl hn => exact hn hc.1
    | inr hn => exact hn hc.2

theorem Branch.neg_disj (B : Branch σ) (x : B.Node) (c d : 𝒞ᵁ σ) :
    B.negConcept x (c ⊔ₜ d) ↔ B.negConcept x c ∧ B.negConcept x d := by
  rw [B.negConcept_iff, B.disj_pos, B.negConcept_iff, B.negConcept_iff]
  exact not_or

theorem Branch.neg_inter (B : Branch σ) (x y : B.Node) (r s : ℛᵁ σ) :
    B.negRole x y (r ⊓ᵣ s) ↔ B.negRole x y r ∨ B.negRole x y s := by
  classical
  rw [B.negRole_iff, B.inter_pos, B.negRole_iff, B.negRole_iff]
  constructor
  · intro h
    by_cases hr : B.posRole x y r
    · exact Or.inr (fun hs => h ⟨hr, hs⟩)
    · exact Or.inl hr
  · intro h hrs
    cases h with
    | inl hn => exact hn hrs.1
    | inr hn => exact hn hrs.2

theorem Branch.neg_ex (B : Branch σ) (x : B.Node)
    (r : ℛᵁ σ) (c : 𝒞ᵁ σ) :
    B.negConcept x (∃[r] c) ↔
      ∀ y, B.negRole x y r ∨ B.negConcept y c := by
  classical
  constructor
  · intro h y
    by_cases hr : B.posRole x y r
    · apply Or.inr
      apply (B.negConcept_iff y c).2
      intro hc
      exact ((B.negConcept_iff x (∃[r] c)).1 h)
        ((B.ex_pos x r c).2 ⟨y, hr, hc⟩)
    · exact Or.inl ((B.negRole_iff x y r).2 hr)
  · intro h
    apply (B.negConcept_iff x (∃[r] c)).2
    intro hex
    obtain ⟨y, hr, hc⟩ := (B.ex_pos x r c).1 hex
    rcases h y with hnr | hnc
    · exact ((B.negRole_iff x y r).1 hnr) hr
    · exact ((B.negConcept_iff y c).1 hnc) hc

theorem Branch.neg_all (B : Branch σ) (x : B.Node)
    (r : ℛᵁ σ) (c : 𝒞ᵁ σ) :
    B.negConcept x (∀[r] c) ↔
      ∃ y, B.posRole x y r ∧ B.negConcept y c := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hnone
    have hall : ∀ y, B.posRole x y r → B.posConcept y c := by
      intro y hr
      apply Classical.byContradiction
      intro hnc
      exact hnone ⟨y, hr, (B.negConcept_iff y c).2 hnc⟩
    exact ((B.negConcept_iff x (∀[r] c)).1 h) ((B.all_pos x r c).2 hall)
  · rintro ⟨y, hr, hnc⟩
    apply (B.negConcept_iff x (∀[r] c)).2
    intro hall
    exact ((B.negConcept_iff y c).1 hnc) ((B.all_pos x r c).1 hall y hr)

/-- The interpretation extracted from the atomic labels of an open branch. -/
@[instance_reducible] def Branch.canonical (B : Branch σ) : ℐᶜ σ where
  D := B.Node
  inhabited := B.nonempty
  individualValuation := B.name
  atomicConceptValuation := fun a x => B.posConcept x [a]ₐ
  roleValuation := fun r x y => B.posRole x y [r]ᵣ

theorem Branch.role_truth (B : Branch σ) (r : ℛᵁ σ)
    (x y : B.Node) :
    @evalRoleC σ B.canonical r x y ↔ B.posRole x y r := by
  induction r with
  | atom a => rfl
  | universal =>
      change True ↔ B.posRole x y 𝒰
      exact ⟨fun _ => B.universal_pos x y, fun _ => True.intro⟩
  | inter r s ihr ihs =>
      change (@evalRoleC σ B.canonical r x y ∧
        @evalRoleC σ B.canonical s x y) ↔ B.posRole x y (r ⊓ᵣ s)
      rw [ihr, ihs]
      exact (B.inter_pos x y r s).symm

theorem Branch.concept_truth (B : Branch σ) (c : 𝒞ᵁ σ)
    (x : B.Node) :
    @evalConceptC σ B.canonical c x ↔ B.posConcept x c := by
  induction c generalizing x with
  | top =>
      change True ↔ B.posConcept x ⊤
      exact ⟨fun _ => B.top_pos x, fun _ => True.intro⟩
  | bot =>
      change False ↔ B.posConcept x ⊥
      exact ⟨False.elim, fun hp => False.elim
        (B.concept_clash x ⊥ ⟨hp, B.bot_neg x⟩)⟩
  | atom a => rfl
  | neg c ih =>
      change (¬@evalConceptC σ B.canonical c x) ↔ B.posConcept x (¬ₜ c)
      calc
        (¬@evalConceptC σ B.canonical c x) ↔ ¬B.posConcept x c := not_congr (ih x)
        _ ↔ B.negConcept x c := (B.negConcept_iff x c).symm
        _ ↔ B.posConcept x (¬ₜ c) := (B.neg_pos x c).symm
  | conj c d ihc ihd =>
      change (@evalConceptC σ B.canonical c x ∧
        @evalConceptC σ B.canonical d x) ↔ B.posConcept x (c ⊓ₜ d)
      rw [ihc x, ihd x]
      exact (B.conj_pos x c d).symm
  | disj c d ihc ihd =>
      change (@evalConceptC σ B.canonical c x ∨
        @evalConceptC σ B.canonical d x) ↔ B.posConcept x (c ⊔ₜ d)
      rw [ihc x, ihd x]
      exact (B.disj_pos x c d).symm
  | ex r c ih =>
      change (∃ y, @evalRoleC σ B.canonical r x y ∧
        @evalConceptC σ B.canonical c y) ↔ B.posConcept x (∃[r] c)
      constructor
      · rintro ⟨y, hr, hc⟩
        exact (B.ex_pos x r c).2 ⟨y, (B.role_truth r x y).1 hr, (ih y).1 hc⟩
      · intro hp
        obtain ⟨y, hr, hc⟩ := (B.ex_pos x r c).1 hp
        exact ⟨y, (B.role_truth r x y).2 hr, (ih y).2 hc⟩
  | all r c ih =>
      change (∀ y, @evalRoleC σ B.canonical r x y →
        @evalConceptC σ B.canonical c y) ↔ B.posConcept x (∀[r] c)
      constructor
      · intro h
        apply (B.all_pos x r c).2
        intro y hr
        exact (ih y).1 (h y ((B.role_truth r x y).2 hr))
      · intro hp y hr
        exact (ih y).2 ((B.all_pos x r c).1 hp y ((B.role_truth r x y).1 hr))

/-- A sentence's signed-tableau truth conditions. -/
def Branch.asserts (B : Branch σ) : Φᵁ σ → Prop
  | a :ₐ c => B.posConcept (B.name a) c
  | (a, b) :ᵣ r => B.posRole (B.name a) (B.name b) r
  | c ⊑ d => ∀ x, B.posConcept x c → B.posConcept x d
  | c ≡ d => ∀ x, B.posConcept x c ↔ B.posConcept x d
  | r ⊑ᵣ s => ∀ x y, B.posRole x y r → B.posRole x y s

theorem Branch.sentence_truth (B : Branch σ) (φ : Φᵁ σ) :
    @evalSentenceC σ B.canonical φ ↔ B.asserts φ := by
  cases φ with
  | isa a c => exact B.concept_truth c (B.name a)
  | role a b r => exact B.role_truth r (B.name a) (B.name b)
  | sub c d =>
      change (∀ x, @evalConceptC σ B.canonical c x →
        @evalConceptC σ B.canonical d x) ↔
        (∀ x, B.posConcept x c → B.posConcept x d)
      constructor
      · intro h x hc
        exact (B.concept_truth d x).1 (h x ((B.concept_truth c x).2 hc))
      · intro h x hc
        exact (B.concept_truth d x).2 (h x ((B.concept_truth c x).1 hc))
  | equiv c d =>
      change (∀ x, @evalConceptC σ B.canonical c x ↔
        @evalConceptC σ B.canonical d x) ↔
        (∀ x, B.posConcept x c ↔ B.posConcept x d)
      constructor
      · intro h x
        exact (B.concept_truth c x).symm.trans ((h x).trans (B.concept_truth d x))
      · intro h x
        exact (B.concept_truth c x).trans ((h x).trans (B.concept_truth d x).symm)
  | rsub r s =>
      change (∀ x y, @evalRoleC σ B.canonical r x y →
        @evalRoleC σ B.canonical s x y) ↔
        (∀ x y, B.posRole x y r → B.posRole x y s)
      constructor
      · intro h x y hr
        exact (B.role_truth s x y).1 (h x y ((B.role_truth r x y).2 hr))
      · intro h x y hr
        exact (B.role_truth s x y).2 (h x y ((B.role_truth r x y).1 hr))

/-- Turn any classical interpretation into a fully expanded signed branch. -/
noncomputable def fromModel (I : ℐᶜ σ) : Branch σ := by
  classical
  exact {
    Node := I.D
    nonempty := I.inhabited
    name := I.individualValuation
    posConcept := fun x c => @evalConceptC σ I c x
    negConcept := fun x c => ¬@evalConceptC σ I c x
    posRole := fun x y r => @evalRoleC σ I r x y
    negRole := fun x y r => ¬@evalRoleC σ I r x y
    concept_decided := fun x c => Classical.em _
    concept_clash := fun _ _ h => h.2 h.1
    role_decided := fun x y r => Classical.em _
    role_clash := fun _ _ _ h => h.2 h.1
    top_pos := fun _ => trivial
    bot_neg := fun _ h => h
    neg_pos := fun _ _ => Iff.rfl
    conj_pos := fun _ _ _ => Iff.rfl
    disj_pos := fun _ _ _ => Iff.rfl
    ex_pos := fun _ _ _ => Iff.rfl
    all_pos := fun _ _ _ => Iff.rfl
    universal_pos := fun _ _ => trivial
    inter_pos := fun _ _ _ _ => Iff.rfl
  }

theorem fromModel_asserts (I : ℐᶜ σ) (φ : Φᵁ σ) :
    (fromModel I).asserts φ ↔ I ⊨ᶜ φ := by
  cases φ <;> rfl

/-- An open branch satisfies every premise and refutes one conclusion. -/
def Open (B : Branch σ) (Γ Δ : (Φᵁ σ)*) : Prop :=
  (∀ ψ ∈ Γ, B.asserts ψ) ∧ ∃ φ ∈ Δ, ¬B.asserts φ

/-- The tableau proves the entailment when no open saturated branch remains. -/
def proves (Γ Δ : (Φᵁ σ)*) : Prop :=
  ¬∃ B : Branch σ, Open B Γ Δ

theorem sound {Γ Δ : (Φᵁ σ)*} (h : proves Γ Δ) : Γ ⊨ᶜ Δ := by
  intro I hΓ φ hφ
  classical
  apply Classical.byContradiction
  intro hbad
  apply h
  refine ⟨fromModel I, ?_, ?_⟩
  · intro ψ hψ
    exact (fromModel_asserts I ψ).2 (hΓ ψ hψ)
  · exact ⟨φ, hφ, fun hb => hbad ((fromModel_asserts I φ).1 hb)⟩

theorem complete {Γ Δ : (Φᵁ σ)*} (h : Γ ⊨ᶜ Δ) : proves Γ Δ := by
  rintro ⟨B, hΓ, φ, hφ, hbad⟩
  have hmodel : ∀ ψ ∈ Γ, B.canonical ⊨ᶜ ψ := by
    intro ψ hψ
    exact (B.sentence_truth ψ).2 (hΓ ψ hψ)
  exact hbad ((B.sentence_truth φ).1 (h B.canonical hmodel φ hφ))

theorem proves_iff_entailmentC (Γ Δ : (Φᵁ σ)*) :
    proves Γ Δ ↔ Γ ⊨ᶜ Δ :=
  ⟨sound, complete⟩

/-- A subsumption and a concept assertion close the branch against the
corresponding assertion. This proof uses only the tableau labels. -/
theorem subsumption_example (a : σ.Ni) (c d : 𝒞ᵁ σ) :
    proves ({a :ₐ c} ∪ {c ⊑ d}) {a :ₐ d} := by
  intro h
  obtain ⟨B, hΓ, φ, hφ, hneg⟩ := h
  have hc : B.posConcept (B.name a) c := by
    exact hΓ (a :ₐ c) (Or.inl rfl)
  have hcd : ∀ x, B.posConcept x c → B.posConcept x d := by
    exact hΓ (c ⊑ d) (Or.inr rfl)
  have hφ : φ = (a :ₐ d) := hφ
  subst φ
  exact hneg (hcd (B.name a) hc)

end ALCHAC.ClassicalTableau

namespace ALCHAC.ClassicalTableau.Search

/-- A finite indexed signature for executable proof search. -/
def signature (concepts roles individuals : Nat) : Signature where
  Nc := Fin concepts
  Nr := Fin roles
  Ni := Fin individuals

/-- A finite branch stores the atomic concept and role labels. Every other
label is expanded by `conceptValue` and `roleValue`. -/
structure Branch (nc nr ni n : Nat) where
  individual : Fin ni → Fin (n + 1)
  conceptAtom : Fin nc → Fin (n + 1) → Bool
  roleAtom : Fin nr → Fin (n + 1) → Fin (n + 1) → Bool

@[instance_reducible] def Branch.asModel {nc nr ni n : Nat} (B : Branch nc nr ni n) :
    ℐᶜ (signature nc nr ni) where
  D := Fin (n + 1)
  inhabited := ⟨0⟩
  individualValuation := B.individual
  atomicConceptValuation := fun a x => B.conceptAtom a x = true
  roleValuation := fun r x y => B.roleAtom r x y = true

def roleValue {nc nr ni n : Nat} (B : Branch nc nr ni n) :
    ℛᵁ (signature nc nr ni) → Fin (n + 1) → Fin (n + 1) → Bool
  | [r]ᵣ, x, y => B.roleAtom r x y
  | 𝒰, _, _ => true
  | r ⊓ᵣ s, x, y => roleValue B r x y && roleValue B s x y

def conceptValue {nc nr ni n : Nat} (B : Branch nc nr ni n) :
    𝒞ᵁ (signature nc nr ni) → Fin (n + 1) → Bool
  | ⊤, _ => true
  | ⊥, _ => false
  | [a]ₐ, x => B.conceptAtom a x
  | ¬ₜ c, x => !conceptValue B c x
  | c ⊓ₜ d, x => conceptValue B c x && conceptValue B d x
  | c ⊔ₜ d, x => conceptValue B c x || conceptValue B d x
  | ∃[r] c, x =>
      (List.finRange (n + 1)).any fun y => roleValue B r x y && conceptValue B c y
  | ∀[r] c, x =>
      (List.finRange (n + 1)).all fun y => !roleValue B r x y || conceptValue B c y

def sentenceValue {nc nr ni n : Nat} (B : Branch nc nr ni n) :
    Φᵁ (signature nc nr ni) → Bool
  | a :ₐ c => conceptValue B c (B.individual a)
  | (a, b) :ᵣ r => roleValue B r (B.individual a) (B.individual b)
  | c ⊑ d => (List.finRange (n + 1)).all fun x =>
      !conceptValue B c x || conceptValue B d x
  | c ≡ d => (List.finRange (n + 1)).all fun x =>
      conceptValue B c x == conceptValue B d x
  | r ⊑ᵣ s => (List.finRange (n + 1)).all fun x =>
      (List.finRange (n + 1)).all fun y =>
        !roleValue B r x y || roleValue B s x y

private theorem boolImp (p q : Bool) :
    (!p || q) = true ↔ (p = true → q = true) := by
  cases p <;> cases q <;> decide

private theorem boolIff (p q : Bool) :
    (p == q) = true ↔ (p = true ↔ q = true) := by
  cases p <;> cases q <;> decide

private theorem boolNotTrue (p : Bool) :
    Bool.not p = true ↔ p ≠ true := by
  cases p <;> decide

theorem roleValue_correct {nc nr ni n : Nat} (B : Branch nc nr ni n)
    (r : ℛᵁ (signature nc nr ni)) (x y : Fin (n + 1)) :
    roleValue B r x y = true ↔ @evalRoleC (signature nc nr ni) B.asModel r x y := by
  induction r with
  | atom a => rfl
  | universal => simp [roleValue, evalRoleC]
  | inter r s ihr ihs =>
      simp [roleValue, evalRoleC, Bool.and_eq_true, ihr, ihs]

theorem conceptValue_correct {nc nr ni n : Nat} (B : Branch nc nr ni n)
    (c : 𝒞ᵁ (signature nc nr ni)) (x : Fin (n + 1)) :
    conceptValue B c x = true ↔ @evalConceptC (signature nc nr ni) B.asModel c x := by
  induction c generalizing x with
  | top => simp [conceptValue, evalConceptC]
  | bot => simp [conceptValue, evalConceptC]
  | atom a => rfl
  | neg c ih =>
      simp [conceptValue, evalConceptC, Bool.eq_false_iff, ih]
  | conj c d ihc ihd =>
      simp [conceptValue, evalConceptC, Bool.and_eq_true, ihc, ihd]
  | disj c d ihc ihd =>
      simp [conceptValue, evalConceptC, Bool.or_eq_true, ihc, ihd]
  | ex r c ih =>
      change ((List.finRange (n + 1)).any fun y =>
        roleValue B r x y && conceptValue B c y) = true ↔
        ∃ y, @evalRoleC (signature nc nr ni) B.asModel r x y ∧
          @evalConceptC (signature nc nr ni) B.asModel c y
      rw [List.any_eq_true]
      constructor
      · rintro ⟨y, _, hy⟩
        simp only [Bool.and_eq_true] at hy
        have ⟨hr, hc⟩ := hy
        exact ⟨y, (roleValue_correct B r x y).1 hr, (ih y).1 hc⟩
      · rintro ⟨y, hr, hc⟩
        refine ⟨y, List.mem_finRange y, ?_⟩
        simp only [Bool.and_eq_true]
        exact ⟨(roleValue_correct B r x y).2 hr, (ih y).2 hc⟩
  | all r c ih =>
      change ((List.finRange (n + 1)).all fun y =>
        !roleValue B r x y || conceptValue B c y) = true ↔
        ∀ y, @evalRoleC (signature nc nr ni) B.asModel r x y →
          @evalConceptC (signature nc nr ni) B.asModel c y
      rw [List.all_eq_true]
      constructor
      · intro h y hr
        exact (ih y).1 ((boolImp _ _).1 (h y (List.mem_finRange y))
          ((roleValue_correct B r x y).2 hr))
      · intro h y _
        apply (boolImp _ _).2
        intro hr
        exact (ih y).2 (h y ((roleValue_correct B r x y).1 hr))

theorem sentenceValue_correct {nc nr ni n : Nat} (B : Branch nc nr ni n)
    (φ : Φᵁ (signature nc nr ni)) :
    sentenceValue B φ = true ↔ B.asModel ⊨ᶜ φ := by
  cases φ with
  | isa a c => exact conceptValue_correct B c (B.individual a)
  | role a b r => exact roleValue_correct B r (B.individual a) (B.individual b)
  | sub c d =>
      change ((List.finRange (n + 1)).all fun x =>
        !conceptValue B c x || conceptValue B d x) = true ↔
        (∀ x, @evalConceptC (signature nc nr ni) B.asModel c x →
          @evalConceptC (signature nc nr ni) B.asModel d x)
      rw [List.all_eq_true]
      constructor
      · intro h x hc
        exact (conceptValue_correct B d x).1 ((boolImp _ _).1
          (h x (List.mem_finRange x)) ((conceptValue_correct B c x).2 hc))
      · intro h x _
        apply (boolImp _ _).2
        intro hc
        exact (conceptValue_correct B d x).2
          (h x ((conceptValue_correct B c x).1 hc))
  | equiv c d =>
      change ((List.finRange (n + 1)).all fun x =>
        conceptValue B c x == conceptValue B d x) = true ↔
        (∀ x, @evalConceptC (signature nc nr ni) B.asModel c x ↔
          @evalConceptC (signature nc nr ni) B.asModel d x)
      rw [List.all_eq_true]
      constructor
      · intro h x
        exact (conceptValue_correct B c x).symm.trans
          (((boolIff _ _).1 (h x (List.mem_finRange x))).trans
            (conceptValue_correct B d x))
      · intro h x _
        exact (boolIff _ _).2 ((conceptValue_correct B c x).trans
          ((h x).trans (conceptValue_correct B d x).symm))
  | rsub r s =>
      change ((List.finRange (n + 1)).all fun x =>
        (List.finRange (n + 1)).all fun y =>
          !roleValue B r x y || roleValue B s x y) = true ↔
        (∀ x y, @evalRoleC (signature nc nr ni) B.asModel r x y →
          @evalRoleC (signature nc nr ni) B.asModel s x y)
      rw [List.all_eq_true]
      constructor
      · intro h x y hr
        have hxy := (List.all_eq_true).1 (h x (List.mem_finRange x)) y
          (List.mem_finRange y)
        exact (roleValue_correct B s x y).1
          ((boolImp _ _).1 hxy ((roleValue_correct B r x y).2 hr))
      · intro h x _
        apply (List.all_eq_true).2
        intro y _
        apply (boolImp _ _).2
        intro hr
        exact (roleValue_correct B s x y).2
          (h x y ((roleValue_correct B r x y).1 hr))

/-- Enumerate all functions out of `Fin n` using a supplied list of values. -/
def functions (values : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n + 1 => values.flatMap fun head =>
      (functions values n).map fun tail => Fin.cases head tail

theorem functions_complete (values : List α) (hvalues : ∀ a : α, a ∈ values)
    (n : Nat) (f : Fin n → α) : f ∈ functions values n := by
  induction n with
  | zero =>
      change f ∈ [Fin.elim0]
      apply List.mem_singleton.mpr
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      change f ∈ values.flatMap (fun head =>
        (functions values n).map fun tail => Fin.cases head tail)
      apply List.mem_flatMap.mpr
      refine ⟨f 0, hvalues (f 0), ?_⟩
      apply List.mem_map.mpr
      refine ⟨fun i => f i.succ, ih _, ?_⟩
      funext i
      exact Fin.cases (by rfl) (fun _ => by rfl) i

private theorem bool_complete (b : Bool) : b ∈ [false, true] := by
  cases b <;> simp

/-- Enumerate every branch on a fixed nonempty finite domain. -/
def branches (nc nr ni n : Nat) : List (Branch nc nr ni n) := Id.run do
  let nodes := List.finRange (n + 1)
  let bits := functions [false, true] (n + 1)
  let concepts := functions bits nc
  let roles := functions (functions bits (n + 1)) nr
  let individuals := functions nodes ni
  return individuals.flatMap fun i =>
    concepts.flatMap fun c =>
      roles.map fun r => ⟨i, c, r⟩

theorem branches_complete {nc nr ni n : Nat} (B : Branch nc nr ni n) :
    B ∈ branches nc nr ni n := by
  let nodes := List.finRange (n + 1)
  let bits := functions [false, true] (n + 1)
  let concepts := functions bits nc
  let roles := functions (functions bits (n + 1)) nr
  let individuals := functions nodes ni
  have hnodes : ∀ x : Fin (n + 1), x ∈ nodes := List.mem_finRange
  have hbits : ∀ f : Fin (n + 1) → Bool, f ∈ bits :=
    functions_complete [false, true] bool_complete (n + 1)
  have hconcepts : ∀ f : Fin nc → Fin (n + 1) → Bool, f ∈ concepts :=
    functions_complete bits hbits nc
  have hroleRows : ∀ f : Fin (n + 1) → Fin (n + 1) → Bool,
      f ∈ functions bits (n + 1) :=
    functions_complete bits hbits (n + 1)
  have hroles : ∀ f : Fin nr → Fin (n + 1) → Fin (n + 1) → Bool,
      f ∈ roles :=
    functions_complete (functions bits (n + 1)) hroleRows nr
  have hindividuals : ∀ f : Fin ni → Fin (n + 1), f ∈ individuals :=
    functions_complete nodes hnodes ni
  change B ∈ individuals.flatMap (fun i =>
    concepts.flatMap fun c => roles.map fun r => ⟨i, c, r⟩)
  apply List.mem_flatMap.mpr
  refine ⟨B.individual, hindividuals B.individual, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨B.conceptAtom, hconcepts B.conceptAtom, ?_⟩
  apply List.mem_map.mpr
  exact ⟨B.roleAtom, hroles B.roleAtom, rfl⟩

noncomputable def fromFiniteModel {nc nr ni n : Nat}
    (I : ℐᶜ (signature nc nr ni))
    (hD : I.D = Fin (n + 1)) : Branch nc nr ni n := by
  classical
  exact {
    individual := fun a => cast hD (I.individualValuation a)
    conceptAtom := fun a x => decide (I.atomicConceptValuation a (cast hD.symm x))
    roleAtom := fun r x y => decide
      (I.roleValuation r (cast hD.symm x) (cast hD.symm y))
  }

theorem fromFiniteModel_role {nc nr ni n : Nat}
    (I : ℐᶜ (signature nc nr ni)) (hD : I.D = Fin (n + 1))
    (r : ℛᵁ (signature nc nr ni)) (x y : Fin (n + 1)) :
    @evalRoleC (signature nc nr ni) (fromFiniteModel I hD).asModel r x y ↔
      @evalRoleC (signature nc nr ni) I r (cast hD.symm x) (cast hD.symm y) := by
  classical
  induction r with
  | atom a =>
      change (decide (I.roleValuation a (cast hD.symm x) (cast hD.symm y)) = true) ↔
        I.roleValuation a (cast hD.symm x) (cast hD.symm y)
      exact decide_eq_true_iff
  | universal => simp [evalRoleC]
  | inter _ _ ihr ihs =>
      change (_ ∧ _) ↔ (_ ∧ _)
      exact and_congr ihr ihs

private theorem cast_roundtrip_left {A B : Type} (h : A = B) (x : A) :
    cast h.symm (cast h x) = x := by
  cases h
  rfl

private theorem cast_roundtrip_right {A B : Type} (h : A = B) (x : B) :
    cast h (cast h.symm x) = x := by
  cases h
  rfl

theorem fromFiniteModel_concept {nc nr ni n : Nat}
    (I : ℐᶜ (signature nc nr ni)) (hD : I.D = Fin (n + 1))
    (c : 𝒞ᵁ (signature nc nr ni)) (x : Fin (n + 1)) :
    @evalConceptC (signature nc nr ni) (fromFiniteModel I hD).asModel c x ↔
      @evalConceptC (signature nc nr ni) I c (cast hD.symm x) := by
  classical
  induction c generalizing x with
  | top | bot => rfl
  | atom a =>
      change (decide (I.atomicConceptValuation a (cast hD.symm x)) = true) ↔
        I.atomicConceptValuation a (cast hD.symm x)
      exact decide_eq_true_iff
  | neg _ ih => exact not_congr (ih x)
  | conj _ _ ihc ihd => exact and_congr (ihc x) (ihd x)
  | disj _ _ ihc ihd => exact or_congr (ihc x) (ihd x)
  | ex r c ih =>
      change (∃ y : Fin (n + 1),
        @evalRoleC (signature nc nr ni) (fromFiniteModel I hD).asModel r x y ∧
        @evalConceptC (signature nc nr ni) (fromFiniteModel I hD).asModel c y) ↔
        (∃ y : I.D, @evalRoleC (signature nc nr ni) I r (cast hD.symm x) y ∧
          @evalConceptC (signature nc nr ni) I c y)
      constructor
      · rintro ⟨y, hr, hc⟩
        exact ⟨cast hD.symm y, (fromFiniteModel_role I hD r x y).1 hr,
          (ih y).1 hc⟩
      · rintro ⟨y, hr, hc⟩
        refine ⟨cast hD y, ?_, ?_⟩
        · exact (fromFiniteModel_role I hD r x (cast hD y)).2
            (by rw [cast_roundtrip_left]; exact hr)
        · exact (ih (cast hD y)).2 (by rw [cast_roundtrip_left]; exact hc)
  | all r c ih =>
      change (∀ y : Fin (n + 1),
        @evalRoleC (signature nc nr ni) (fromFiniteModel I hD).asModel r x y →
        @evalConceptC (signature nc nr ni) (fromFiniteModel I hD).asModel c y) ↔
        (∀ y : I.D, @evalRoleC (signature nc nr ni) I r (cast hD.symm x) y →
          @evalConceptC (signature nc nr ni) I c y)
      constructor
      · intro h y hr
        have hnew : @evalRoleC (signature nc nr ni)
            (fromFiniteModel I hD).asModel r x (cast hD y) :=
          (fromFiniteModel_role I hD r x (cast hD y)).2
            (by rw [cast_roundtrip_left]; exact hr)
        have hc := (ih (cast hD y)).1 (h (cast hD y) hnew)
        rw [cast_roundtrip_left] at hc
        exact hc
      · intro h y hr
        exact (ih y).2 (h (cast hD.symm y)
          ((fromFiniteModel_role I hD r x y).1 hr))

theorem fromFiniteModel_sentence {nc nr ni n : Nat}
    (I : ℐᶜ (signature nc nr ni)) (hD : I.D = Fin (n + 1))
    (φ : Φᵁ (signature nc nr ni)) :
    @evalSentenceC (signature nc nr ni) (fromFiniteModel I hD).asModel φ ↔
      @evalSentenceC (signature nc nr ni) I φ := by
  classical
  cases φ with
  | isa a c =>
      change @evalConceptC (signature nc nr ni) (fromFiniteModel I hD).asModel c
        (cast hD (I.individualValuation a)) ↔
        @evalConceptC (signature nc nr ni) I c (I.individualValuation a)
      simpa only [cast_roundtrip_left] using
        (fromFiniteModel_concept I hD c (cast hD (I.individualValuation a)))
  | role a b r =>
      change @evalRoleC (signature nc nr ni) (fromFiniteModel I hD).asModel r
        (cast hD (I.individualValuation a))
        (cast hD (I.individualValuation b)) ↔
        @evalRoleC (signature nc nr ni) I r
          (I.individualValuation a) (I.individualValuation b)
      simpa only [cast_roundtrip_left] using
        (fromFiniteModel_role I hD r (cast hD (I.individualValuation a))
          (cast hD (I.individualValuation b)))
  | sub c d =>
      constructor
      · intro h x hc
        have hcx := (fromFiniteModel_concept I hD c (cast hD x)).2
          (by rw [cast_roundtrip_left]; exact hc)
        have hdx := (fromFiniteModel_concept I hD d (cast hD x)).1
          (h (cast hD x) hcx)
        rw [cast_roundtrip_left] at hdx
        exact hdx
      · intro h x hc
        exact (fromFiniteModel_concept I hD d x).2
          (h (cast hD.symm x) ((fromFiniteModel_concept I hD c x).1 hc))
  | equiv c d =>
      constructor
      · intro h x
        have hc := fromFiniteModel_concept I hD c (cast hD x)
        have hd := fromFiniteModel_concept I hD d (cast hD x)
        rw [cast_roundtrip_left] at hc hd
        exact hc.symm.trans ((h (cast hD x)).trans hd)
      · intro h x
        exact (fromFiniteModel_concept I hD c x).trans
          ((h (cast hD.symm x)).trans (fromFiniteModel_concept I hD d x).symm)
  | rsub r s =>
      constructor
      · intro h x y hr
        have hrxy := (fromFiniteModel_role I hD r (cast hD x) (cast hD y)).2
          (by rw [cast_roundtrip_left, cast_roundtrip_left]; exact hr)
        have hsxy := (fromFiniteModel_role I hD s (cast hD x) (cast hD y)).1
          (h (cast hD x) (cast hD y) hrxy)
        rw [cast_roundtrip_left, cast_roundtrip_left] at hsxy
        exact hsxy
      · intro h x y hr
        exact (fromFiniteModel_role I hD s x y).2
          (h (cast hD.symm x) (cast hD.symm y)
            ((fromFiniteModel_role I hD r x y).1 hr))

/-- Depth-first choice over all functions, stopping as soon as a branch works. -/
def chooseFunction (choose : (α → Bool) → Bool) :
    (n : Nat) → ((Fin n → α) → Bool) → Bool
  | 0, p => p Fin.elim0
  | n + 1, p => choose fun head =>
      chooseFunction choose n fun tail => p (Fin.cases head tail)

def chooseBool (p : Bool → Bool) : Bool := p false || p true

def chooseFin (n : Nat) (p : Fin n → Bool) : Bool :=
  (List.finRange n).any p

def chooseRow (n : Nat) : ((Fin n → Bool) → Bool) → Bool :=
  chooseFunction chooseBool n

def chooseMatrix (n : Nat) :
    ((Fin n → Fin n → Bool) → Bool) → Bool :=
  chooseFunction (chooseRow n) n

def counterexampleAt (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Bool :=
  chooseFunction (chooseFin (n + 1)) ni fun i =>
    chooseFunction (chooseRow (n + 1)) nc fun c =>
      chooseFunction (chooseMatrix (n + 1)) nr fun r =>
        let B : Branch nc nr ni n := ⟨i, c, r⟩
        premises.toList.all (sentenceValue B) &&
          conclusions.toList.any (fun φ => !sentenceValue B φ)

/-- A closed tableau has no finite branch satisfying all premises while
falsifying any conclusion. -/
def closesAt (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Bool :=
  !counterexampleAt nc nr ni n premises conclusions

def entailsAt (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Prop :=
  ∀ B : Branch nc nr ni n,
    (∀ ψ ∈ premises.toList, B.asModel ⊨ᶜ ψ) →
    (∀ φ ∈ conclusions.toList, B.asModel ⊨ᶜ φ)

private theorem chooseBool_correct (p : Bool → Bool) :
    chooseBool p = true ↔ ∃ b, p b = true := by
  cases hp : p false <;> cases hq : p true <;>
    simp [chooseBool, hp, hq]

private theorem chooseFin_correct (n : Nat) (p : Fin n → Bool) :
    chooseFin n p = true ↔ ∃ x, p x = true := by
  simp only [chooseFin, List.any_eq_true]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, List.mem_finRange x, hx⟩

private theorem chooseFunction_correct (choose : (α → Bool) → Bool)
    (hchoose : ∀ p, choose p = true ↔ ∃ a, p a = true)
    (n : Nat) (p : (Fin n → α) → Bool) :
    chooseFunction choose n p = true ↔ ∃ f, p f = true := by
  induction n with
  | zero =>
      constructor
      · intro hp
        exact ⟨Fin.elim0, hp⟩
      · rintro ⟨f, hp⟩
        have hf : f = Fin.elim0 := by
          funext i
          exact Fin.elim0 i
        simpa [chooseFunction, ← hf] using hp
  | succ n ih =>
      change (choose (fun head => chooseFunction choose n
        (fun tail => p (Fin.cases head tail))) = true) ↔ _
      rw [hchoose]
      constructor
      · rintro ⟨head, htail⟩
        obtain ⟨tail, hp⟩ := (ih _).1 htail
        exact ⟨Fin.cases head tail, hp⟩
      · rintro ⟨f, hf⟩
        refine ⟨f 0, (ih _).2 ⟨fun i => f i.succ, ?_⟩⟩
        have heq : Fin.cases (f 0) (fun i => f i.succ) = f := by
          funext i
          exact Fin.cases (by rfl) (fun _ => by rfl) i
        rw [heq]
        exact hf

private theorem chooseRow_correct (n : Nat)
    (p : (Fin n → Bool) → Bool) :
    chooseRow n p = true ↔ ∃ f, p f = true :=
  chooseFunction_correct chooseBool chooseBool_correct n p

private theorem chooseMatrix_correct (n : Nat)
    (p : (Fin n → Fin n → Bool) → Bool) :
    chooseMatrix n p = true ↔ ∃ f, p f = true :=
  chooseFunction_correct (chooseRow n) (chooseRow_correct n) n p

private theorem counterexampleAt_correct (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    counterexampleAt nc nr ni n premises conclusions = true ↔
      ∃ B : Branch nc nr ni n,
        premises.toList.all (sentenceValue B) = true ∧
          conclusions.toList.any (fun φ => !sentenceValue B φ) = true := by
  unfold counterexampleAt
  rw [chooseFunction_correct (chooseFin (n + 1)) (chooseFin_correct (n + 1))]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨c, hc⟩ := (chooseFunction_correct (chooseRow (n + 1))
      (chooseRow_correct (n + 1)) nc _).1 hi
    obtain ⟨r, hr⟩ := (chooseFunction_correct (chooseMatrix (n + 1))
      (chooseMatrix_correct (n + 1)) nr _).1 hc
    refine ⟨⟨i, c, r⟩, ?_⟩
    simpa only [Bool.and_eq_true] using hr
  · rintro ⟨B, hB⟩
    refine ⟨B.individual, ?_⟩
    apply (chooseFunction_correct (chooseRow (n + 1))
      (chooseRow_correct (n + 1)) nc _).2
    refine ⟨B.conceptAtom, ?_⟩
    apply (chooseFunction_correct (chooseMatrix (n + 1))
      (chooseMatrix_correct (n + 1)) nr _).2
    refine ⟨B.roleAtom, ?_⟩
    simpa only [Bool.and_eq_true] using hB

private theorem allPremises_correct {nc nr ni n : Nat}
    (B : Branch nc nr ni n)
    (premises : Array (Φᵁ (signature nc nr ni))) :
    premises.toList.all (sentenceValue B) = true ↔
      ∀ ψ ∈ premises.toList, B.asModel ⊨ᶜ ψ := by
  rw [List.all_eq_true]
  constructor
  · intro h ψ hψ
    exact (sentenceValue_correct B ψ).1 (h ψ hψ)
  · intro h ψ hψ
    exact (sentenceValue_correct B ψ).2 (h ψ hψ)

private theorem failedConclusion_correct {nc nr ni n : Nat}
    (B : Branch nc nr ni n)
    (conclusions : Array (Φᵁ (signature nc nr ni))) :
    conclusions.toList.any (fun φ => !sentenceValue B φ) = true ↔
      ∃ φ ∈ conclusions.toList, ¬ B.asModel ⊨ᶜ φ := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨φ, hφ, hb⟩
    rw [boolNotTrue] at hb
    exact ⟨φ, hφ, fun h => hb ((sentenceValue_correct B φ).2 h)⟩
  · rintro ⟨φ, hφ, hn⟩
    refine ⟨φ, hφ, ?_⟩
    rw [boolNotTrue]
    exact fun hb => hn ((sentenceValue_correct B φ).1 hb)

theorem closesAt_correct (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    closesAt nc nr ni n premises conclusions = true ↔
      entailsAt nc nr ni n premises conclusions := by
  unfold closesAt entailsAt
  rw [boolNotTrue]
  constructor
  · intro h B hΓ φ hφ
    classical
    apply Classical.byContradiction
    intro hn
    apply h
    apply (counterexampleAt_correct nc nr ni n premises conclusions).2
    refine ⟨B, ?_⟩
    exact ⟨(allPremises_correct B premises).2 hΓ,
      (failedConclusion_correct B conclusions).2 ⟨φ, hφ, hn⟩⟩
  · intro h hb
    obtain ⟨B, hb⟩ := (counterexampleAt_correct nc nr ni n premises conclusions).1 hb
    have hΓ := (allPremises_correct B premises).1 hb.1
    obtain ⟨φ, hφ, hn⟩ := (failedConclusion_correct B conclusions).1 hb.2
    exact hn (h B hΓ φ hφ)

/-- Embed the finite input arrays into `Final.lean`'s set-based entailment. -/
def asSet {nc nr ni : Nat}
    (entries : Array (Φᵁ (signature nc nr ni))) : (Φᵁ (signature nc nr ni))* :=
  fun φ => φ ∈ entries.toList

/-- A checked open branch is a countermodel to full classical entailment. -/
theorem checkedBranch_disproves_entailmentC {nc nr ni n : Nat}
    (B : Branch nc nr ni n)
    (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (h : premises.toList.all (sentenceValue B) = true ∧
      conclusions.toList.any (fun φ => !sentenceValue B φ) = true) :
    ¬ (asSet premises ⊨ᶜ asSet conclusions) := by
  intro hentails
  have hΓ : ∀ ψ ∈ premises.toList, B.asModel ⊨ᶜ ψ := by
    intro ψ hψ
    exact (sentenceValue_correct B ψ).1 ((List.all_eq_true).1 h.1 ψ hψ)
  obtain ⟨φ, hφ, hbad⟩ := (List.any_eq_true).1 h.2
  have hφ' : B.asModel ⊨ᶜ φ := hentails B.asModel hΓ φ hφ
  have hgood := (sentenceValue_correct B φ).2 hφ'
  simp [hgood] at hbad

/-- Every full classical entailment closes at every finite domain size. -/
theorem entailmentC_implies_closesAt (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (h : asSet premises ⊨ᶜ asSet conclusions) :
    closesAt nc nr ni n premises conclusions = true := by
  apply (closesAt_correct nc nr ni n premises conclusions).2
  intro B hΓ φ hφ
  exact h B.asModel hΓ φ hφ

/-- A counterbranch returned by finite search disproves full entailment. -/
theorem openAt_disproves_entailmentC (nc nr ni n : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (h : closesAt nc nr ni n premises conclusions = false) :
    ¬(asSet premises ⊨ᶜ asSet conclusions) := by
  intro hentails
  have hclose := entailmentC_implies_closesAt nc nr ni n premises conclusions hentails
  rw [h] at hclose
  cases hclose

/-- Search all nonempty domains with at most `maxNodes` elements. -/
def closesThrough (nc nr ni maxNodes : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Bool :=
  (List.range maxNodes).all fun n => closesAt nc nr ni n premises conclusions

-- Tiny runnable examples. The first closes; the second has a counterbranch.
#eval closesAt 1 0 1 0
  #[((0 : Fin 1) :ₐ [(0 : Fin 1)]ₐ)]
  #[((0 : Fin 1) :ₐ [(0 : Fin 1)]ₐ)]

#eval closesAt 1 0 1 0
  #[((0 : Fin 1) :ₐ [(0 : Fin 1)]ₐ)]
  #[((0 : Fin 1) :ₐ ¬ₜ [(0 : Fin 1)]ₐ)]

end ALCHAC.ClassicalTableau.Search

namespace ALCHAC.ClassicalTableau.SmallModel

open Search

variable {nc nr ni : Nat}

abbrev Pattern (F : List (𝒞ᵁ (signature nc nr ni))) := Fin F.length → Bool
abbrev Profile (nr : Nat) := Fin nr → Bool
abbrev Domain (F : List (𝒞ᵁ (signature nc nr ni))) :=
  Fin ni ⊕ (Pattern F × Profile nr)

noncomputable def pattern (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (x : I.D) : Pattern F := by
  classical
  exact fun i => decide (@evalConceptC (signature nc nr ni) I (F.get i) x)

noncomputable def profile (I : ℐᶜ (signature nc nr ni))
    (x y : I.D) : Profile nr := by
  classical
  exact fun r => decide (I.roleValuation r x y)

theorem same_pattern (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni)))
    {x y : I.D} (hxy : pattern I F x = pattern I F y)
    {c : 𝒞ᵁ (signature nc nr ni)} (hc : c ∈ F) :
    @evalConceptC (signature nc nr ni) I c x ↔
      @evalConceptC (signature nc nr ni) I c y := by
  classical
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
  have h := congrArg (fun p : Pattern F => p i) hxy
  simp only [pattern, hi] at h
  constructor
  · intro hx
    apply decide_eq_true_iff.mp
    rw [← h]
    exact decide_eq_true_iff.mpr hx
  · intro hy
    apply decide_eq_true_iff.mp
    rw [h]
    exact decide_eq_true_iff.mpr hy

noncomputable def representative (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (p : Pattern F) : I.D := by
  classical
  exact if h : ∃ x, pattern I F x = p then Classical.choose h
    else Classical.choice I.inhabited

theorem representative_pattern (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (p : Pattern F)
    (h : ∃ x, pattern I F x = p) :
    pattern I F (representative I F p) = p := by
  simp only [representative, dif_pos h]
  exact Classical.choose_spec h

noncomputable def point (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) : Domain F → I.D
  | .inl a => I.individualValuation a
  | .inr (p, _) => representative I F p

noncomputable def requestedProfile (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (u v : Domain F) : Profile nr :=
  match v with
  | .inl _ => profile I (point I F u) (point I F v)
  | .inr (_, q) => q

noncomputable def pair (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (u v : Domain F) : I.D × I.D := by
  classical
  exact if h : ∃ q : I.D × I.D,
      pattern I F q.1 = pattern I F (point I F u) ∧
      pattern I F q.2 = pattern I F (point I F v) ∧
      profile I q.1 q.2 = requestedProfile I F u v
  then Classical.choose h
  else (point I F u, point I F v)

theorem pair_patterns (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (u v : Domain F) :
    pattern I F (pair I F u v).1 = pattern I F (point I F u) ∧
      pattern I F (pair I F u v).2 = pattern I F (point I F v) := by
  classical
  by_cases h : ∃ q : I.D × I.D,
      pattern I F q.1 = pattern I F (point I F u) ∧
      pattern I F q.2 = pattern I F (point I F v) ∧
      profile I q.1 q.2 = requestedProfile I F u v
  · simpa only [pair, dif_pos h] using
      (And.intro (Classical.choose_spec h).1 (Classical.choose_spec h).2.1)
  · simp only [pair, dif_neg h]
    exact ⟨trivial, trivial⟩

theorem pair_profile (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (u v : Domain F)
    (h : ∃ q : I.D × I.D,
      pattern I F q.1 = pattern I F (point I F u) ∧
      pattern I F q.2 = pattern I F (point I F v) ∧
      profile I q.1 q.2 = requestedProfile I F u v) :
    profile I (pair I F u v).1 (pair I F u v).2 =
      requestedProfile I F u v := by
  classical
  simp only [pair, dif_pos h]
  exact (Classical.choose_spec h).2.2

@[instance_reducible] noncomputable def model (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) : ℐᶜ (signature nc nr ni) where
  D := Domain F
  inhabited := ⟨.inr (fun _ => false, fun _ => false)⟩
  individualValuation := .inl
  atomicConceptValuation := fun a u => I.atomicConceptValuation a (point I F u)
  roleValuation := fun r u v => I.roleValuation r (pair I F u v).1 (pair I F u v).2

theorem role_model (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (r : ℛᵁ (signature nc nr ni))
    (u v : Domain F) :
    @evalRoleC (signature nc nr ni) (model I F) r u v ↔
      @evalRoleC (signature nc nr ni) I r (pair I F u v).1 (pair I F u v).2 := by
  induction r with
  | atom a => rfl
  | universal => simp [evalRoleC]
  | inter r s ihr ihs =>
      change (_ ∧ _) ↔ (_ ∧ _)
      exact and_congr ihr ihs

theorem role_profile (I : ℐᶜ (signature nc nr ni))
    (r : ℛᵁ (signature nc nr ni)) (x y x' y' : I.D)
    (h : profile I x y = profile I x' y') :
    @evalRoleC (signature nc nr ni) I r x y ↔
      @evalRoleC (signature nc nr ni) I r x' y' := by
  induction r with
  | atom a =>
      classical
      have ha := congrArg (fun p : Profile nr => p a) h
      simp only [profile] at ha
      constructor
      · intro hr
        apply decide_eq_true_iff.mp
        change decide (I.roleValuation a x' y') = true
        rw [← ha]
        exact decide_eq_true_iff.mpr hr
      · intro hr
        apply decide_eq_true_iff.mp
        change decide (I.roleValuation a x y) = true
        rw [ha]
        exact decide_eq_true_iff.mpr hr
  | universal => simp [evalRoleC]
  | inter r s ihr ihs =>
      change (_ ∧ _) ↔ (_ ∧ _)
      exact and_congr ihr ihs

structure Closed (F : List (𝒞ᵁ (signature nc nr ni))) : Prop where
  neg : ∀ c, (¬ₜ c) ∈ F → c ∈ F
  conj_left : ∀ c d, (c ⊓ₜ d) ∈ F → c ∈ F
  conj_right : ∀ c d, (c ⊓ₜ d) ∈ F → d ∈ F
  disj_left : ∀ c d, (c ⊔ₜ d) ∈ F → c ∈ F
  disj_right : ∀ c d, (c ⊔ₜ d) ∈ F → d ∈ F
  ex : ∀ r c, (∃[r] c) ∈ F → c ∈ F
  all : ∀ r c, (∀[r] c) ∈ F → c ∈ F

private theorem generic_pattern (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (y : I.D) (q : Profile nr) :
    pattern I F (point I F (.inr (pattern I F y, q))) = pattern I F y := by
  change pattern I F (representative I F (pattern I F y)) = pattern I F y
  exact representative_pattern I F _ ⟨y, rfl⟩

private theorem edge_to_generic (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (u : Domain F)
    (y : I.D) (r : ℛᵁ (signature nc nr ni))
    (hr : @evalRoleC (signature nc nr ni) I r (point I F u) y) :
    @evalRoleC (signature nc nr ni) (model I F) r u
      (.inr (pattern I F y, profile I (point I F u) y)) := by
  let v : Domain F := .inr (pattern I F y, profile I (point I F u) y)
  have hv : pattern I F (point I F v) = pattern I F y :=
    generic_pattern I F y _
  have hex : ∃ q : I.D × I.D,
      pattern I F q.1 = pattern I F (point I F u) ∧
      pattern I F q.2 = pattern I F (point I F v) ∧
      profile I q.1 q.2 = requestedProfile I F u v := by
    refine ⟨⟨point I F u, y⟩, rfl, hv.symm, ?_⟩
    rfl
  have hp := pair_profile I F u v hex
  have hrole : @evalRoleC (signature nc nr ni) I r
      (pair I F u v).1 (pair I F u v).2 := by
    apply (role_profile I r _ _ _ _ hp).2
    exact hr
  exact (role_model I F r u v).2 hrole

theorem concept_model (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (hF : Closed F) :
    ∀ c, c ∈ F → ∀ u : Domain F,
      @evalConceptC (signature nc nr ni) (model I F) c u ↔
        @evalConceptC (signature nc nr ni) I c (point I F u) := by
  intro c
  induction c with
  | top => intro _ _; rfl
  | bot => intro _ _; rfl
  | atom a => intro _ _; rfl
  | neg c ih =>
      intro hc u
      change (¬@evalConceptC (signature nc nr ni) (model I F) c u) ↔
        ¬@evalConceptC (signature nc nr ni) I c (point I F u)
      exact not_congr (ih (hF.neg c hc) u)
  | conj c d ihc ihd =>
      intro hc u
      change (_ ∧ _) ↔ (_ ∧ _)
      exact and_congr (ihc (hF.conj_left c d hc) u)
        (ihd (hF.conj_right c d hc) u)
  | disj c d ihc ihd =>
      intro hc u
      change (_ ∨ _) ↔ (_ ∨ _)
      exact or_congr (ihc (hF.disj_left c d hc) u)
        (ihd (hF.disj_right c d hc) u)
  | ex r c ih =>
      intro hc u
      have hchild := hF.ex r c hc
      change (∃ v, @evalRoleC (signature nc nr ni) (model I F) r u v ∧
        @evalConceptC (signature nc nr ni) (model I F) c v) ↔
        (∃ y, @evalRoleC (signature nc nr ni) I r (point I F u) y ∧
          @evalConceptC (signature nc nr ni) I c y)
      constructor
      · rintro ⟨v, hr, hcv⟩
        let q := pair I F u v
        have hpair := pair_patterns I F u v
        have hrold := (role_model I F r u v).1 hr
        have hcy : @evalConceptC (signature nc nr ni) I c q.2 :=
          (same_pattern I F hpair.2 hchild).2 ((ih hchild v).1 hcv)
        have hex : @evalConceptC (signature nc nr ni) I (∃[r] c) q.1 :=
          ⟨q.2, hrold, hcy⟩
        exact (same_pattern I F hpair.1 hc).1 hex
      · rintro ⟨y, hr, hcy⟩
        let v : Domain F := .inr (pattern I F y, profile I (point I F u) y)
        refine ⟨v, edge_to_generic I F u y r hr, ?_⟩
        apply (ih hchild v).2
        exact (same_pattern I F (generic_pattern I F y _) hchild).2 hcy
  | all r c ih =>
      intro hc u
      have hchild := hF.all r c hc
      change (∀ v, @evalRoleC (signature nc nr ni) (model I F) r u v →
        @evalConceptC (signature nc nr ni) (model I F) c v) ↔
        (∀ y, @evalRoleC (signature nc nr ni) I r (point I F u) y →
          @evalConceptC (signature nc nr ni) I c y)
      constructor
      · intro h y hr
        let v : Domain F := .inr (pattern I F y, profile I (point I F u) y)
        have hcv := h v (edge_to_generic I F u y r hr)
        have hcp := (ih hchild v).1 hcv
        exact (same_pattern I F (generic_pattern I F y _) hchild).1 hcp
      · intro h v hr
        let q := pair I F u v
        have hpair := pair_patterns I F u v
        have hrold := (role_model I F r u v).1 hr
        have hall : @evalConceptC (signature nc nr ni) I (∀[r] c) q.1 :=
          (same_pattern I F hpair.1 hc).2 h
        have hcq : @evalConceptC (signature nc nr ni) I c q.2 :=
          hall q.2 hrold
        apply (ih hchild v).2
        exact (same_pattern I F hpair.2 hchild).1 hcq

def Covers (F : List (𝒞ᵁ (signature nc nr ni))) :
    Φᵁ (signature nc nr ni) → Prop
  | _ :ₐ c => c ∈ F
  | (_, _) :ᵣ _ => True
  | c ⊑ d | c ≡ d => c ∈ F ∧ d ∈ F
  | _ ⊑ᵣ _ => True

private theorem role_on_original_pair (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (u v : Domain F)
    (x y : I.D)
    (hx : pattern I F x = pattern I F (point I F u))
    (hy : pattern I F y = pattern I F (point I F v))
    (hp : profile I x y = requestedProfile I F u v)
    (r : ℛᵁ (signature nc nr ni)) :
    @evalRoleC (signature nc nr ni) (model I F) r u v ↔
      @evalRoleC (signature nc nr ni) I r x y := by
  have hex : ∃ q : I.D × I.D,
      pattern I F q.1 = pattern I F (point I F u) ∧
      pattern I F q.2 = pattern I F (point I F v) ∧
      profile I q.1 q.2 = requestedProfile I F u v :=
    ⟨⟨x, y⟩, hx, hy, hp⟩
  exact (role_model I F r u v).trans
    (role_profile I r _ _ x y ((pair_profile I F u v hex).trans hp.symm))

private theorem named_role (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni)))
    (a b : Fin ni) (r : ℛᵁ (signature nc nr ni)) :
    @evalRoleC (signature nc nr ni) (model I F) r (.inl a) (.inl b) ↔
      @evalRoleC (signature nc nr ni) I r
        (I.individualValuation a) (I.individualValuation b) := by
  apply role_on_original_pair I F (.inl a) (.inl b)
    (I.individualValuation a) (I.individualValuation b) rfl rfl
  rfl

private theorem generic_role (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni)))
    (x y : I.D) (q : Profile nr) (r : ℛᵁ (signature nc nr ni)) :
    @evalRoleC (signature nc nr ni) (model I F) r
      (.inr (pattern I F x, q)) (.inr (pattern I F y, profile I x y)) ↔
      @evalRoleC (signature nc nr ni) I r x y := by
  apply role_on_original_pair I F _ _ x y
  · exact (generic_pattern I F x q).symm
  · exact (generic_pattern I F y _).symm
  · rfl

theorem sentence_model (I : ℐᶜ (signature nc nr ni))
    (F : List (𝒞ᵁ (signature nc nr ni))) (hF : Closed F)
    (φ : Φᵁ (signature nc nr ni)) (hφ : Covers F φ) :
    @evalSentenceC (signature nc nr ni) (model I F) φ ↔
      @evalSentenceC (signature nc nr ni) I φ := by
  cases φ with
  | isa a c =>
      exact concept_model I F hF c hφ (.inl a)
  | role a b r =>
      exact named_role I F a b r
  | sub c d =>
      constructor
      · intro h x hc
        let u : Domain F := .inr (pattern I F x, fun _ => false)
        have hpat := generic_pattern I F x (fun _ => false)
        have hcu : @evalConceptC (signature nc nr ni) I c (point I F u) :=
          (same_pattern I F hpat hφ.1).2 hc
        have hnew := (concept_model I F hF c hφ.1 u).2 hcu
        have hdu := (concept_model I F hF d hφ.2 u).1 (h u hnew)
        exact (same_pattern I F hpat hφ.2).1 hdu
      · intro h u hc
        have hcu := (concept_model I F hF c hφ.1 u).1 hc
        exact (concept_model I F hF d hφ.2 u).2 (h (point I F u) hcu)
  | equiv c d =>
      constructor
      · intro h x
        let u : Domain F := .inr (pattern I F x, fun _ => false)
        have hpat := generic_pattern I F x (fun _ => false)
        exact (same_pattern I F hpat hφ.1).symm.trans
          ((concept_model I F hF c hφ.1 u).symm.trans
            ((h u).trans ((concept_model I F hF d hφ.2 u).trans
              (same_pattern I F hpat hφ.2))))
      · intro h u
        exact (concept_model I F hF c hφ.1 u).trans
          ((h (point I F u)).trans
            (concept_model I F hF d hφ.2 u).symm)
  | rsub r s =>
      constructor
      · intro h x y hr
        let u : Domain F := .inr (pattern I F x, fun _ => false)
        let v : Domain F := .inr (pattern I F y, profile I x y)
        have heq := generic_role I F x y (fun _ => false)
        exact (heq s).1 (h u v ((heq r).2 hr))
      · intro h u v hr
        have hrold := (role_model I F r u v).1 hr
        exact (role_model I F s u v).2
          (h (pair I F u v).1 (pair I F u v).2 hrold)

def subconcepts : 𝒞ᵁ (signature nc nr ni) → List (𝒞ᵁ (signature nc nr ni))
  | .top => [.top]
  | .bot => [.bot]
  | .atom a => [.atom a]
  | .neg c => .neg c :: subconcepts c
  | .conj c d => .conj c d :: (subconcepts c ++ subconcepts d)
  | .disj c d => .disj c d :: (subconcepts c ++ subconcepts d)
  | .ex r c => .ex r c :: subconcepts c
  | .all r c => .all r c :: subconcepts c

theorem self_mem_subconcepts (c : 𝒞ᵁ (signature nc nr ni)) :
    c ∈ subconcepts c := by
  cases c <;> simp [subconcepts]

theorem subconcepts_trans (c : 𝒞ᵁ (signature nc nr ni)) :
    ∀ d, d ∈ subconcepts c →
      ∀ e, e ∈ subconcepts d → e ∈ subconcepts c := by
  induction c with
  | top | bot | atom _ =>
      intro d hd e he
      simp only [subconcepts, List.mem_singleton] at hd
      subst d
      exact he
  | neg c ih | ex _ c ih | all _ c ih =>
      intro d hd e he
      simp only [subconcepts, List.mem_cons] at hd ⊢
      rcases hd with rfl | hd
      · simpa only [subconcepts, List.mem_cons] using he
      · exact Or.inr (ih d hd e he)
  | conj c d ihc ihd | disj c d ihc ihd =>
      intro a ha e he
      simp only [subconcepts, List.mem_cons, List.mem_append] at ha ⊢
      rcases ha with rfl | ha
      · simpa only [subconcepts, List.mem_cons, List.mem_append] using he
      · rcases ha with hc | hd
        · exact Or.inr (Or.inl (ihc a hc e he))
        · exact Or.inr (Or.inr (ihd a hd e he))

def sentenceConcepts : Φᵁ (signature nc nr ni) →
    List (𝒞ᵁ (signature nc nr ni))
  | _ :ₐ c => subconcepts c
  | (_, _) :ᵣ _ => []
  | c ⊑ d | c ≡ d => subconcepts c ++ subconcepts d
  | _ ⊑ᵣ _ => []

theorem sentenceConcepts_trans (φ : Φᵁ (signature nc nr ni)) :
    ∀ c, c ∈ sentenceConcepts φ →
      ∀ d, d ∈ subconcepts c → d ∈ sentenceConcepts φ := by
  cases φ with
  | isa a c =>
      intro d hd e he
      exact subconcepts_trans c d hd e he
  | role a b r =>
      intro d hd
      cases hd
  | sub c d | equiv c d =>
      intro a ha e he
      change a ∈ subconcepts c ++ subconcepts d at ha
      change e ∈ subconcepts c ++ subconcepts d
      rcases List.mem_append.mp ha with hc | hd
      · exact List.mem_append.mpr (Or.inl (subconcepts_trans c a hc e he))
      · exact List.mem_append.mpr (Or.inr (subconcepts_trans d a hd e he))
  | rsub r s =>
      intro c hc
      cases hc

def closure (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    List (𝒞ᵁ (signature nc nr ni)) :=
  (premises.toList ++ conclusions.toList).flatMap sentenceConcepts

theorem closure_trans (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    ∀ c, c ∈ closure premises conclusions →
      ∀ d, d ∈ subconcepts c → d ∈ closure premises conclusions := by
  intro c hc d hd
  obtain ⟨φ, hφ, hcφ⟩ := List.mem_flatMap.mp hc
  apply List.mem_flatMap.mpr
  exact ⟨φ, hφ, sentenceConcepts_trans φ c hcφ d hd⟩

theorem closure_closed (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    Closed (closure premises conclusions) := by
  let F := closure premises conclusions
  have ht := closure_trans premises conclusions
  constructor
  · intro c hc
    apply ht (¬ₜ c) hc c
    simp only [subconcepts, List.mem_cons]
    exact Or.inr (self_mem_subconcepts c)
  · intro c d hc
    apply ht (c ⊓ₜ d) hc c
    simp only [subconcepts, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (self_mem_subconcepts c))
  · intro c d hc
    apply ht (c ⊓ₜ d) hc d
    simp only [subconcepts, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (self_mem_subconcepts d))
  · intro c d hc
    apply ht (c ⊔ₜ d) hc c
    simp only [subconcepts, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inl (self_mem_subconcepts c))
  · intro c d hc
    apply ht (c ⊔ₜ d) hc d
    simp only [subconcepts, List.mem_cons, List.mem_append]
    exact Or.inr (Or.inr (self_mem_subconcepts d))
  · intro r c hc
    apply ht (∃[r] c) hc c
    simp only [subconcepts, List.mem_cons]
    exact Or.inr (self_mem_subconcepts c)
  · intro r c hc
    apply ht (∀[r] c) hc c
    simp only [subconcepts, List.mem_cons]
    exact Or.inr (self_mem_subconcepts c)

theorem closure_covers (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (φ : Φᵁ (signature nc nr ni))
    (hφ : φ ∈ premises.toList ++ conclusions.toList) :
    Covers (closure premises conclusions) φ := by
  have hmem : ∀ c, c ∈ sentenceConcepts φ →
      c ∈ closure premises conclusions := by
    intro c hc
    exact List.mem_flatMap.mpr ⟨φ, hφ, hc⟩
  cases φ with
  | isa a c =>
      exact hmem c (self_mem_subconcepts c)
  | role a b r => trivial
  | sub c d | equiv c d =>
      exact ⟨hmem c (List.mem_append.mpr
        (Or.inl (self_mem_subconcepts c))),
        hmem d (List.mem_append.mpr
        (Or.inr (self_mem_subconcepts d)))⟩
  | rsub r s => trivial

theorem model_preserves_premise (I : ℐᶜ (signature nc nr ni))
    (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (φ : Φᵁ (signature nc nr ni)) (hφ : φ ∈ premises.toList) :
    @evalSentenceC (signature nc nr ni)
      (model I (closure premises conclusions)) φ ↔ I ⊨ᶜ φ := by
  apply sentence_model I _ (closure_closed premises conclusions) φ
  exact closure_covers premises conclusions φ (List.mem_append.mpr (Or.inl hφ))

theorem model_preserves_conclusion (I : ℐᶜ (signature nc nr ni))
    (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (φ : Φᵁ (signature nc nr ni)) (hφ : φ ∈ conclusions.toList) :
    @evalSentenceC (signature nc nr ni)
      (model I (closure premises conclusions)) φ ↔ I ⊨ᶜ φ := by
  apply sentence_model I _ (closure_closed premises conclusions) φ
  exact closure_covers premises conclusions φ (List.mem_append.mpr (Or.inr hφ))

def allPatterns (F : List (𝒞ᵁ (signature nc nr ni))) : List (Pattern F) :=
  Search.functions [false, true] F.length

def allProfiles (nr : Nat) : List (Profile nr) :=
  Search.functions [false, true] nr

def allNodes (F : List (𝒞ᵁ (signature nc nr ni))) : List (Domain F) :=
  (List.finRange ni).map Sum.inl ++
    (allPatterns F).flatMap fun p => (allProfiles nr).map fun q => Sum.inr (p, q)

theorem allNodes_complete (F : List (𝒞ᵁ (signature nc nr ni)))
    (u : Domain F) : u ∈ allNodes F := by
  have hbits (b : Bool) : b ∈ [false, true] := by cases b <;> simp
  cases u with
  | inl a =>
      apply List.mem_append.mpr
      apply Or.inl
      exact List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩
  | inr pq =>
      obtain ⟨p, q⟩ := pq
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_flatMap.mpr
      refine ⟨p, Search.functions_complete [false, true] hbits F.length p, ?_⟩
      exact List.mem_map.mpr
        ⟨q, Search.functions_complete [false, true] hbits nr q, rfl⟩

def nodeList (F : List (𝒞ᵁ (signature nc nr ni))) : List (Domain F) :=
  .inr (fun _ => false, fun _ => false) :: allNodes F

theorem nodeList_complete (F : List (𝒞ᵁ (signature nc nr ni)))
    (u : Domain F) : u ∈ nodeList F :=
  List.mem_cons.mpr (Or.inr (allNodes_complete F u))

noncomputable def indexOf (xs : List α) (x : α) (hx : x ∈ xs) : Fin xs.length :=
  Classical.choose (List.mem_iff_get.mp hx)

theorem get_indexOf (xs : List α) (x : α) (hx : x ∈ xs) :
    xs.get (indexOf xs x hx) = x :=
  Classical.choose_spec (List.mem_iff_get.mp hx)

@[instance_reducible] noncomputable def pullback
    (I : ℐᶜ (signature nc nr ni)) (xs : List I.D)
    (hne : xs ≠ []) (hcomplete : ∀ x : I.D, x ∈ xs) :
    ℐᶜ (signature nc nr ni) where
  D := Fin xs.length
  inhabited := by
    cases xs with
    | nil => contradiction
    | cons _ _ => exact ⟨0⟩
  individualValuation := fun a =>
    indexOf xs (I.individualValuation a) (hcomplete _)
  atomicConceptValuation := fun a i => I.atomicConceptValuation a (xs.get i)
  roleValuation := fun r i j => I.roleValuation r (xs.get i) (xs.get j)

theorem pullback_role (I : ℐᶜ (signature nc nr ni))
    (xs : List I.D) (hne : xs ≠ []) (hcomplete : ∀ x : I.D, x ∈ xs)
    (r : ℛᵁ (signature nc nr ni)) (i j : Fin xs.length) :
    @evalRoleC (signature nc nr ni) (pullback I xs hne hcomplete) r i j ↔
      @evalRoleC (signature nc nr ni) I r (xs.get i) (xs.get j) := by
  induction r with
  | atom _ => rfl
  | universal => simp [evalRoleC]
  | inter _ _ ihr ihs =>
      change (_ ∧ _) ↔ (_ ∧ _)
      exact and_congr ihr ihs

theorem pullback_concept (I : ℐᶜ (signature nc nr ni))
    (xs : List I.D) (hne : xs ≠ []) (hcomplete : ∀ x : I.D, x ∈ xs)
    (c : 𝒞ᵁ (signature nc nr ni)) (i : Fin xs.length) :
    @evalConceptC (signature nc nr ni) (pullback I xs hne hcomplete) c i ↔
      @evalConceptC (signature nc nr ni) I c (xs.get i) := by
  induction c generalizing i with
  | top | bot | atom _ => rfl
  | neg _ ih => exact not_congr (ih i)
  | conj _ _ ihc ihd => exact and_congr (ihc i) (ihd i)
  | disj _ _ ihc ihd => exact or_congr (ihc i) (ihd i)
  | ex r c ih =>
      change (∃ j, @evalRoleC (signature nc nr ni) (pullback I xs hne hcomplete) r i j ∧
        @evalConceptC (signature nc nr ni) (pullback I xs hne hcomplete) c j) ↔
        (∃ y, @evalRoleC (signature nc nr ni) I r (xs.get i) y ∧
          @evalConceptC (signature nc nr ni) I c y)
      constructor
      · rintro ⟨j, hr, hc⟩
        exact ⟨xs.get j, (pullback_role I xs hne hcomplete r i j).1 hr,
          (ih j).1 hc⟩
      · rintro ⟨y, hr, hc⟩
        let j := indexOf xs y (hcomplete y)
        have hj : xs.get j = y := get_indexOf xs y (hcomplete y)
        refine ⟨j, ?_, ?_⟩
        · exact (pullback_role I xs hne hcomplete r i j).2
            (by rw [hj]; exact hr)
        · exact (ih j).2 (by rw [hj]; exact hc)
  | all r c ih =>
      change (∀ j, @evalRoleC (signature nc nr ni) (pullback I xs hne hcomplete) r i j →
        @evalConceptC (signature nc nr ni) (pullback I xs hne hcomplete) c j) ↔
        (∀ y, @evalRoleC (signature nc nr ni) I r (xs.get i) y →
          @evalConceptC (signature nc nr ni) I c y)
      constructor
      · intro h y hr
        let j := indexOf xs y (hcomplete y)
        have hj : xs.get j = y := get_indexOf xs y (hcomplete y)
        have hrj : @evalRoleC (signature nc nr ni) (pullback I xs hne hcomplete) r i j :=
          (pullback_role I xs hne hcomplete r i j).2
            (by rw [hj]; exact hr)
        rw [← hj]
        exact (ih j).1 (h j hrj)
      · intro h j hr
        exact (ih j).2 (h (xs.get j)
          ((pullback_role I xs hne hcomplete r i j).1 hr))

theorem pullback_sentence (I : ℐᶜ (signature nc nr ni))
    (xs : List I.D) (hne : xs ≠ []) (hcomplete : ∀ x : I.D, x ∈ xs)
    (φ : Φᵁ (signature nc nr ni)) :
    @evalSentenceC (signature nc nr ni) (pullback I xs hne hcomplete) φ ↔
      I ⊨ᶜ φ := by
  cases φ with
  | isa a c =>
      have hi : xs.get (indexOf xs (I.individualValuation a) (hcomplete _)) =
          I.individualValuation a := get_indexOf xs _ (hcomplete _)
      change (@evalConceptC (signature nc nr ni) (pullback I xs hne hcomplete) c
        (indexOf xs (I.individualValuation a) (hcomplete _))) ↔
        @evalConceptC (signature nc nr ni) I c (I.individualValuation a)
      simpa only [hi] using
        (pullback_concept I xs hne hcomplete c
          (indexOf xs (I.individualValuation a) (hcomplete _)))
  | role a b r =>
      have ha : xs.get (indexOf xs (I.individualValuation a) (hcomplete _)) =
          I.individualValuation a := get_indexOf xs _ (hcomplete _)
      have hb : xs.get (indexOf xs (I.individualValuation b) (hcomplete _)) =
          I.individualValuation b := get_indexOf xs _ (hcomplete _)
      change (@evalRoleC (signature nc nr ni) (pullback I xs hne hcomplete) r
        (indexOf xs (I.individualValuation a) (hcomplete _))
        (indexOf xs (I.individualValuation b) (hcomplete _))) ↔
        @evalRoleC (signature nc nr ni) I r
          (I.individualValuation a) (I.individualValuation b)
      simpa only [ha, hb] using
        (pullback_role I xs hne hcomplete r
          (indexOf xs (I.individualValuation a) (hcomplete _))
          (indexOf xs (I.individualValuation b) (hcomplete _)))
  | sub c d =>
      constructor
      · intro h x hc
        let i := indexOf xs x (hcomplete x)
        have hi : xs.get i = x := get_indexOf xs x (hcomplete x)
        have hci : @evalConceptC (signature nc nr ni)
            (pullback I xs hne hcomplete) c i :=
          (pullback_concept I xs hne hcomplete c i).2 (by rw [hi]; exact hc)
        have hdi := (pullback_concept I xs hne hcomplete d i).1 (h i hci)
        rw [hi] at hdi
        exact hdi
      · intro h i hc
        exact (pullback_concept I xs hne hcomplete d i).2
          (h (xs.get i) ((pullback_concept I xs hne hcomplete c i).1 hc))
  | equiv c d =>
      constructor
      · intro h x
        let i := indexOf xs x (hcomplete x)
        have hi : xs.get i = x := get_indexOf xs x (hcomplete x)
        rw [← hi]
        exact (pullback_concept I xs hne hcomplete c i).symm.trans
          ((h i).trans (pullback_concept I xs hne hcomplete d i))
      · intro h i
        exact (pullback_concept I xs hne hcomplete c i).trans
          ((h (xs.get i)).trans
            (pullback_concept I xs hne hcomplete d i).symm)
  | rsub r s =>
      constructor
      · intro h x y hr
        let i := indexOf xs x (hcomplete x)
        let j := indexOf xs y (hcomplete y)
        have hi : xs.get i = x := get_indexOf xs x (hcomplete x)
        have hj : xs.get j = y := get_indexOf xs y (hcomplete y)
        have hrij : @evalRoleC (signature nc nr ni)
            (pullback I xs hne hcomplete) r i j :=
          (pullback_role I xs hne hcomplete r i j).2
            (by rw [hi, hj]; exact hr)
        have hsij := (pullback_role I xs hne hcomplete s i j).1 (h i j hrij)
        rw [hi, hj] at hsij
        exact hsij
      · intro h i j hr
        exact (pullback_role I xs hne hcomplete s i j).2
          (h (xs.get i) (xs.get j)
            ((pullback_role I xs hne hcomplete r i j).1 hr))

/-- The tableau searches the finite domain supplied by the filtration above. -/
def proves (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Bool :=
  Search.closesAt nc nr ni
    (allNodes (closure premises conclusions)).length premises conclusions

theorem proves_iff_entailmentC
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    proves premises conclusions = true ↔
      Search.asSet premises ⊨ᶜ Search.asSet conclusions := by
  constructor
  · intro h I hΓ φ hφ
    classical
    let F := closure premises conclusions
    let K := model I F
    let xs := nodeList F
    have hne : xs ≠ [] := by simp [xs, nodeList]
    have hxs : ∀ x : K.D, x ∈ xs := nodeList_complete F
    let J := pullback K xs hne hxs
    have hD : J.D = Fin ((allNodes F).length + 1) := rfl
    let B := Search.fromFiniteModel J hD
    have hpres (ψ : Φᵁ (signature nc nr ni))
        (hψ : ψ ∈ premises.toList ++ conclusions.toList) :
        @evalSentenceC (signature nc nr ni) B.asModel ψ ↔ I ⊨ᶜ ψ := by
      calc
        @evalSentenceC (signature nc nr ni) B.asModel ψ ↔
            @evalSentenceC (signature nc nr ni) J ψ :=
          Search.fromFiniteModel_sentence J hD ψ
        _ ↔ @evalSentenceC (signature nc nr ni) K ψ :=
          pullback_sentence K xs hne hxs ψ
        _ ↔ I ⊨ᶜ ψ :=
          sentence_model I F (closure_closed premises conclusions) ψ
            (closure_covers premises conclusions ψ hψ)
    have hclosed : Search.entailsAt nc nr ni (allNodes F).length
        premises conclusions :=
      (Search.closesAt_correct nc nr ni (allNodes F).length
        premises conclusions).1 h
    have hB : ∀ ψ ∈ premises.toList, B.asModel ⊨ᶜ ψ := by
      intro ψ hψ
      exact (hpres ψ (List.mem_append.mpr (Or.inl hψ))).2 (hΓ ψ hψ)
    have hresult : B.asModel ⊨ᶜ φ := hclosed B hB φ hφ
    exact (hpres φ (List.mem_append.mpr (Or.inr hφ))).1 hresult
  · intro h
    exact Search.entailmentC_implies_closesAt nc nr ni
      (allNodes (closure premises conclusions)).length premises conclusions h

/-! Direct tableau closure rules avoid enumerating large filtrations for atomic
contradictions, excluded middle, role inclusions, and ABox/TBox steps. -/

instance (nc nr ni : Nat) : DecidableEq (signature nc nr ni).Nc :=
  inferInstanceAs (DecidableEq (Fin nc))
instance (nc nr ni : Nat) : DecidableEq (signature nc nr ni).Nr :=
  inferInstanceAs (DecidableEq (Fin nr))
instance (nc nr ni : Nat) : DecidableEq (signature nc nr ni).Ni :=
  inferInstanceAs (DecidableEq (Fin ni))

def atomContradiction {nc nr ni : Nat} : Φᵁ (signature nc nr ni) → Bool
  | _ :ₐ ([p]ₐ ⊓ₜ ¬ₜ [q]ₐ) => decide (p = q)
  | _ => false

theorem atomContradiction_absurd {nc nr ni : Nat}
    (I : ℐᶜ (signature nc nr ni)) (φ : Φᵁ (signature nc nr ni))
    (h : atomContradiction φ = true) : ¬ I ⊨ᶜ φ := by
  unfold atomContradiction at h
  split at h
  · rename_i a p q
    have hpq : p = q := by simpa using h
    subst q
    change ¬(I.atomicConceptValuation p (I.individualValuation a) ∧
      ¬ I.atomicConceptValuation p (I.individualValuation a))
    exact fun hp => hp.2 hp.1
  · simp at h

def excludedMiddle {nc nr ni : Nat} : Φᵁ (signature nc nr ni) → Bool
  | _ :ₐ ([p]ₐ ⊔ₜ ¬ₜ [q]ₐ) => decide (p = q)
  | _ => false

theorem excludedMiddle_valid {nc nr ni : Nat}
    (I : ℐᶜ (signature nc nr ni)) (φ : Φᵁ (signature nc nr ni))
    (h : excludedMiddle φ = true) : I ⊨ᶜ φ := by
  unfold excludedMiddle at h
  split at h
  · rename_i a p q
    have hpq : p = q := by simpa using h
    subst q
    change I.atomicConceptValuation p (I.individualValuation a) ∨
      ¬ I.atomicConceptValuation p (I.individualValuation a)
    exact Classical.em _
  · simp at h

def roleClash {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni))) : Bool :=
  Γ.toList.any fun allφ =>
    match allφ with
    | a :ₐ ∀[[s]ᵣ] [c]ₐ =>
        Γ.toList.any fun negφ =>
          match negφ with
          | b :ₐ ¬ₜ [d]ₐ =>
              decide (c = d) &&
                Γ.toList.any fun fact =>
                  match fact with
                  | (a', b') :ᵣ [r]ᵣ =>
                      decide (a = a') && decide (b = b') &&
                        (decide (r = s) || Γ.toList.any fun inc =>
                          match inc with
                          | [r']ᵣ ⊑ᵣ [s']ᵣ =>
                              decide (r = r') && decide (s = s')
                          | _ => false)
                  | _ => false
          | _ => false
    | _ => false

theorem roleClash_absurd {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni))) (h : roleClash Γ = true)
    (I : ℐᶜ (signature nc nr ni))
    (hΓ : ∀ ψ ∈ Γ.toList, I ⊨ᶜ ψ) : False := by
  simp only [roleClash, List.any_eq_true] at h
  obtain ⟨allφ, hallmem, hall⟩ := h
  split at hall <;> try cases hall
  rename_i a s c
  rw [List.any_eq_true] at hall
  obtain ⟨negφ, hnegmem, hneg⟩ := hall
  split at hneg <;> try cases hneg
  rename_i b d
  simp only [Bool.and_eq_true] at hneg
  obtain ⟨hcd, hfacts⟩ := hneg
  have hcd' : c = d := decide_eq_true_iff.mp hcd
  subst d
  rw [List.any_eq_true] at hfacts
  obtain ⟨fact, hfactmem, hfact⟩ := hfacts
  split at hfact <;> try cases hfact
  rename_i a' b' r
  simp only [Bool.and_eq_true] at hfact
  obtain ⟨⟨haa, hbb⟩, hrole⟩ := hfact
  have haa' : a = a' := decide_eq_true_iff.mp haa
  have hbb' : b = b' := decide_eq_true_iff.mp hbb
  subst a'
  subst b'
  have hAll := hΓ _ hallmem
  have hNeg := hΓ _ hnegmem
  have hFact := hΓ _ hfactmem
  change ∀ y, I.roleValuation s (I.individualValuation a) y →
    I.atomicConceptValuation c y at hAll
  change ¬ I.atomicConceptValuation c (I.individualValuation b) at hNeg
  change I.roleValuation r (I.individualValuation a) (I.individualValuation b) at hFact
  have hEdge : I.roleValuation s (I.individualValuation a)
      (I.individualValuation b) := by
    simp only [Bool.or_eq_true] at hrole
    rcases hrole with hrs | hincl
    · have hrs' : r = s := decide_eq_true_iff.mp hrs
      subst s
      exact hFact
    · rw [List.any_eq_true] at hincl
      obtain ⟨inc, hincmem, hinc⟩ := hincl
      split at hinc <;> try cases hinc
      rename_i r' s'
      simp only [Bool.and_eq_true] at hinc
      obtain ⟨hrr, hss⟩ := hinc
      have hrr' : r = r' := decide_eq_true_iff.mp hrr
      have hss' : s = s' := decide_eq_true_iff.mp hss
      subst r'
      subst s'
      have hIncl := hΓ _ hincmem
      change ∀ x y, I.roleValuation r x y → I.roleValuation s x y at hIncl
      exact hIncl _ _ hFact
  exact hNeg (hAll _ hEdge)

def roleFactFollows {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni))) :
    Φᵁ (signature nc nr ni) → Bool
  | (a, b) :ᵣ [s]ᵣ =>
      Γ.toList.any fun fact =>
        match fact with
        | (a', b') :ᵣ [r]ᵣ =>
            decide (a = a') && decide (b = b') &&
              (decide (r = s) || Γ.toList.any fun inc =>
                match inc with
                | [r']ᵣ ⊑ᵣ [s']ᵣ =>
                    decide (r = r') && decide (s = s')
                | _ => false)
        | _ => false
  | _ => false

theorem roleFactFollows_sound {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni)))
    (I : ℐᶜ (signature nc nr ni))
    (hΓ : ∀ ψ ∈ Γ.toList, I ⊨ᶜ ψ)
    (φ : Φᵁ (signature nc nr ni)) (h : roleFactFollows Γ φ = true) :
    I ⊨ᶜ φ := by
  unfold roleFactFollows at h
  split at h <;> try cases h
  rename_i a b s
  rw [List.any_eq_true] at h
  obtain ⟨fact, hfactmem, hfact⟩ := h
  split at hfact <;> try cases hfact
  rename_i a' b' r
  simp only [Bool.and_eq_true] at hfact
  obtain ⟨⟨haa, hbb⟩, hrole⟩ := hfact
  have haa' : a = a' := decide_eq_true_iff.mp haa
  have hbb' : b = b' := decide_eq_true_iff.mp hbb
  subst a'
  subst b'
  have hFact := hΓ _ hfactmem
  change I.roleValuation r (I.individualValuation a) (I.individualValuation b) at hFact
  change I.roleValuation s (I.individualValuation a) (I.individualValuation b)
  simp only [Bool.or_eq_true] at hrole
  rcases hrole with hrs | hincl
  · have hrs' : r = s := decide_eq_true_iff.mp hrs
    subst s
    exact hFact
  · rw [List.any_eq_true] at hincl
    obtain ⟨inc, hincmem, hinc⟩ := hincl
    split at hinc <;> try cases hinc
    rename_i r' s'
    simp only [Bool.and_eq_true] at hinc
    obtain ⟨hrr, hss⟩ := hinc
    have hrr' : r = r' := decide_eq_true_iff.mp hrr
    have hss' : s = s' := decide_eq_true_iff.mp hss
    subst r'
    subst s'
    have hIncl := hΓ _ hincmem
    change ∀ x y, I.roleValuation r x y → I.roleValuation s x y at hIncl
    exact hIncl _ _ hFact
def atomFollows {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni))) :
    Φᵁ (signature nc nr ni) → Bool
  | a :ₐ [c]ₐ =>
      Γ.toList.any fun assertion =>
        match assertion with
        | a' :ₐ [p]ₐ =>
            decide (a = a') &&
              (decide (p = c) || Γ.toList.any fun inc =>
                match inc with
                | [p']ₐ ⊑ [c']ₐ =>
                    decide (p = p') && decide (c = c')
                | _ => false)
        | _ => false
  | _ => false

theorem atomFollows_sound {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni)))
    (I : ℐᶜ (signature nc nr ni))
    (hΓ : ∀ ψ ∈ Γ.toList, I ⊨ᶜ ψ)
    (φ : Φᵁ (signature nc nr ni)) (h : atomFollows Γ φ = true) :
    I ⊨ᶜ φ := by
  unfold atomFollows at h
  split at h <;> try cases h
  rename_i a c
  rw [List.any_eq_true] at h
  obtain ⟨assertion, hassertmem, hassert⟩ := h
  split at hassert <;> try cases hassert
  rename_i a' p
  simp only [Bool.and_eq_true] at hassert
  obtain ⟨haa, hconcept⟩ := hassert
  have haa' : a = a' := decide_eq_true_iff.mp haa
  subst a'
  have hAssert := hΓ _ hassertmem
  change I.atomicConceptValuation p (I.individualValuation a) at hAssert
  change I.atomicConceptValuation c (I.individualValuation a)
  simp only [Bool.or_eq_true] at hconcept
  rcases hconcept with hpc | hincl
  · have hpc' : p = c := decide_eq_true_iff.mp hpc
    subst c
    exact hAssert
  · rw [List.any_eq_true] at hincl
    obtain ⟨inc, hincmem, hinc⟩ := hincl
    split at hinc <;> try cases hinc
    rename_i p' c'
    simp only [Bool.and_eq_true] at hinc
    obtain ⟨hpp, hcc⟩ := hinc
    have hpp' : p = p' := decide_eq_true_iff.mp hpp
    have hcc' : c = c' := decide_eq_true_iff.mp hcc
    subst p'
    subst c'
    have hIncl := hΓ _ hincmem
    change ∀ x, I.atomicConceptValuation p x → I.atomicConceptValuation c x at hIncl
    exact hIncl _ hAssert

def existentialFollows {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni))) :
    Φᵁ (signature nc nr ni) → Bool
  | a :ₐ ∃[[r]ᵣ] [c]ₐ =>
      Γ.toList.any fun fact =>
        match fact with
        | (a', b) :ᵣ [r']ᵣ =>
            decide (a = a') && decide (r = r') &&
              atomFollows Γ (b :ₐ [c]ₐ)
        | _ => false
  | _ => false

theorem existentialFollows_sound {nc nr ni : Nat}
    (Γ : Array (Φᵁ (signature nc nr ni)))
    (I : ℐᶜ (signature nc nr ni))
    (hΓ : ∀ ψ ∈ Γ.toList, I ⊨ᶜ ψ)
    (φ : Φᵁ (signature nc nr ni)) (h : existentialFollows Γ φ = true) :
    I ⊨ᶜ φ := by
  unfold existentialFollows at h
  split at h <;> try cases h
  rename_i a r c
  rw [List.any_eq_true] at h
  obtain ⟨fact, hfactmem, hfact⟩ := h
  split at hfact <;> try cases hfact
  rename_i a' b r'
  simp only [Bool.and_eq_true] at hfact
  obtain ⟨⟨haa, hrr⟩, hconcept⟩ := hfact
  have haa' : a = a' := decide_eq_true_iff.mp haa
  have hrr' : r = r' := decide_eq_true_iff.mp hrr
  subst a'
  subst r'
  have hFact := hΓ _ hfactmem
  change I.roleValuation r (I.individualValuation a) (I.individualValuation b) at hFact
  have hConcept := atomFollows_sound Γ I hΓ (b :ₐ [c]ₐ) hconcept
  change I.atomicConceptValuation c (I.individualValuation b) at hConcept
  change ∃ y, I.roleValuation r (I.individualValuation a) y ∧
    I.atomicConceptValuation c y
  exact ⟨I.individualValuation b, hFact, hConcept⟩

/-- A conclusion discharged by excluded middle or a direct ABox/TBox step. -/
def directConclusion {nc nr ni : Nat}
    (premises : Array (Φᵁ (signature nc nr ni)))
    (φ : Φᵁ (signature nc nr ni)) : Bool :=
  excludedMiddle φ || roleFactFollows premises φ ||
    atomFollows premises φ || existentialFollows premises φ

theorem directConclusion_sound {nc nr ni : Nat}
    (premises : Array (Φᵁ (signature nc nr ni)))
    (I : ℐᶜ (signature nc nr ni))
    (hΓ : ∀ ψ ∈ premises.toList, I ⊨ᶜ ψ)
    (φ : Φᵁ (signature nc nr ni))
    (h : directConclusion premises φ = true) : I ⊨ᶜ φ := by
  simp only [directConclusion, Bool.or_eq_true] at h
  rcases h with ((hvalid | hrole) | hatom) | hex
  · exact excludedMiddle_valid I φ hvalid
  · exact roleFactFollows_sound premises I hΓ φ hrole
  · exact atomFollows_sound premises I hΓ φ hatom
  · exact existentialFollows_sound premises I hΓ φ hex

/-- Closure rules whose branches are valid or inconsistent in every model. -/
def directClosure {nc nr ni : Nat}
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Bool :=
  (premises.toList.any atomContradiction || roleClash premises) ||
    conclusions.toList.all (directConclusion premises)

theorem directClosure_sound {nc nr ni : Nat}
    (premises conclusions : Array (Φᵁ (signature nc nr ni)))
    (h : directClosure premises conclusions = true) :
    Search.asSet premises ⊨ᶜ Search.asSet conclusions := by
  intro I hΓ φ hφ
  change ∀ ψ ∈ premises.toList, I ⊨ᶜ ψ at hΓ
  change φ ∈ conclusions.toList at hφ
  simp only [directClosure, Bool.or_eq_true] at h
  rcases h with (hclash | hrole) | hvalid
  · obtain ⟨ψ, hψ, hbad⟩ := (List.any_eq_true).1 hclash
    exact False.elim ((atomContradiction_absurd I ψ hbad) (hΓ ψ hψ))
  · exact False.elim (roleClash_absurd premises hrole I hΓ)
  · exact directConclusion_sound premises I hΓ φ
      ((List.all_eq_true).1 hvalid φ hφ)

/-- Executable ALCHRU entailment checker for finite indexed signatures. -/
def decideEntailment (nc nr ni : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) : Bool :=
  if directClosure premises conclusions then true
  else if Search.closesAt nc nr ni 0 premises conclusions then
    proves premises conclusions
  else false

theorem decideEntailment_correct (nc nr ni : Nat)
    (premises conclusions : Array (Φᵁ (signature nc nr ni))) :
    decideEntailment nc nr ni premises conclusions = true ↔
      Search.asSet premises ⊨ᶜ Search.asSet conclusions := by
  constructor
  · intro h
    by_cases hd : directClosure premises conclusions = true
    · exact directClosure_sound premises conclusions hd
    · by_cases h0 : Search.closesAt nc nr ni 0 premises conclusions = true
      · apply (proves_iff_entailmentC premises conclusions).1
        simpa [decideEntailment, hd, h0] using h
      · have hf : Search.closesAt nc nr ni 0 premises conclusions = false := by
          cases hx : Search.closesAt nc nr ni 0 premises conclusions <;>
            simp_all
        simp [decideEntailment, hd, hf] at h
  · intro h
    by_cases hd : directClosure premises conclusions = true
    · simp [decideEntailment, hd]
    · have h0 := Search.entailmentC_implies_closesAt nc nr ni 0
        premises conclusions h
      have hp := (proves_iff_entailmentC premises conclusions).2 h
      simp [decideEntailment, hd, h0, hp]

-- Runnable examples: a valid entailment, a countermodel, and a role tautology.
#eval decideEntailment 1 0 1
  #[((0 : Fin 1) :ₐ [(0 : Fin 1)]ₐ)]
  #[((0 : Fin 1) :ₐ [(0 : Fin 1)]ₐ)]

#eval decideEntailment 1 0 1
  #[((0 : Fin 1) :ₐ [(0 : Fin 1)]ₐ)]
  #[((0 : Fin 1) :ₐ ¬ₜ [(0 : Fin 1)]ₐ)]

#eval decideEntailment 0 1 1
  #[((0 : Fin 1), (0 : Fin 1)) :ᵣ [(0 : Fin 1)]ᵣ]
  #[((0 : Fin 1), (0 : Fin 1)) :ᵣ ([(0 : Fin 1)]ᵣ ⊓ᵣ 𝒰)]


end ALCHAC.ClassicalTableau.SmallModel
