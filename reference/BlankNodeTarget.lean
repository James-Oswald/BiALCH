import DirectTranslation

/-!
# ALCH target language with existential blank nodes

This file is a draft target for the source translation in `DirectTranslation.lean`.
Target concepts reuse `DirectTranslation.Concept` and are interpreted classically
by `evalC`. Source concepts continue to use `evalK`, including its weak Kleene
disjunction. The compiler keeps those interpretations separate: a source
disjunction is translated into a target disjunction together with its
meaningfulness condition.

Blank nodes occur in ordinary class and role assertions. Their labels are scoped
to one target graph and have one shared existential assignment throughout that
graph. Thus a blank-node class assertion says that the asserted class is
nonempty, while two role assertions using the same pair of blank nodes say that
the roles overlap on a pair. These are target graph semantics, not separate
query-language constructors.
-/

namespace DirectTranslation.BlankNodeTarget

inductive Individual (σ : Signature) where
| named : σ.Ni → Individual σ
| blank : Nat → Individual σ

inductive Sentence (σ : Signature) where
| classAssertion : Individual σ → Concept σ → Sentence σ
| roleAssertion : Individual σ → Individual σ → σ.Nr → Sentence σ
| conceptInclusion : Concept σ → Concept σ → Sentence σ
| roleInclusion : σ.Nr → σ.Nr → Sentence σ

abbrev Graph (σ : Signature) := List (Sentence σ)

/-- Target concepts use the classical interpretation, separately from `evalK`. -/
abbrev evalConcept (J : Interpretation σ Prop) : Concept σ → J.D → Prop := evalC J

/-- A partial assignment keeps unused blank labels genuinely unassigned. -/
def evalIndividual (J : Interpretation σ Prop) (ρ : Nat → Option J.D) :
    Individual σ → Option J.D
| .named a => some (J.individual a)
| .blank n => ρ n

def holdsSentence (J : Interpretation σ Prop) (ρ : Nat → Option J.D) :
    Sentence σ → Prop
| .classAssertion a c =>
    ∃ x, evalIndividual J ρ a = some x ∧ evalConcept J c x
| .roleAssertion a b r =>
    ∃ x y, evalIndividual J ρ a = some x ∧
      evalIndividual J ρ b = some y ∧ J.role r x y
| .conceptInclusion c d =>
    ∀ x, evalConcept J c x → evalConcept J d x
| .roleInclusion r s =>
    ∀ x y, J.role r x y → J.role s x y

/-- Blank nodes in a graph share a single existential assignment. -/
def holdsGraph (J : Interpretation σ Prop) (G : Graph σ) : Prop :=
  ∃ ρ : Nat → Option J.D, ∀ a ∈ G, holdsSentence J ρ a

def graphEntailment (P Q : List (Graph σ)) : Prop :=
  ∀ J, (∀ G ∈ P, holdsGraph J G) → ∀ G ∈ Q, holdsGraph J G

structure Problem (σ : Signature) where
  premises : List (Graph σ)
  conclusions : List (Graph σ)

def entails (P : Problem σ) : Prop :=
  graphEntailment P.premises P.conclusions

private def blankClassGraph (c : Concept σ) : Graph σ :=
  [.classAssertion (.blank 0) c]

private def blankRoleOverlapGraph (r s : σ.Nr) : Graph σ :=
  [ .roleAssertion (.blank 0) (.blank 1) r
  , .roleAssertion (.blank 0) (.blank 1) s
  ]

theorem blankClassGraph_iff (J : Interpretation σ Prop) (c : Concept σ) :
    holdsGraph J (blankClassGraph c) ↔ ∃ x, evalConcept J c x := by
  constructor
  · rintro ⟨ρ, hρ⟩
    have h := hρ (.classAssertion (.blank 0) c) (by simp [blankClassGraph])
    rcases h with ⟨x, hx, hc⟩
    exact ⟨x, hc⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun n => if n = 0 then some x else none, ?_⟩
    intro a ha
    simp only [blankClassGraph, List.mem_singleton] at ha
    subst a
    exact ⟨x, by simp [evalIndividual], hx⟩

theorem blankRoleOverlapGraph_iff (J : Interpretation σ Prop) (r s : σ.Nr) :
    holdsGraph J (blankRoleOverlapGraph r s) ↔
      ∃ x y, J.role r x y ∧ J.role s x y := by
  constructor
  · rintro ⟨ρ, hρ⟩
    have hr := hρ (.roleAssertion (.blank 0) (.blank 1) r) (by
      simp [blankRoleOverlapGraph])
    have hs := hρ (.roleAssertion (.blank 0) (.blank 1) s) (by
      simp [blankRoleOverlapGraph])
    rcases hr with ⟨x, y, hx₀, hy₀, hxy⟩
    rcases hs with ⟨x', y', hx₁, hy₁, hxy'⟩
    have hxx : x = x' := Option.some.inj (hx₀.symm.trans hx₁)
    have hyy : y = y' := Option.some.inj (hy₀.symm.trans hy₁)
    subst x'
    subst y'
    exact ⟨x, y, hxy, hxy'⟩
  · rintro ⟨x, y, hxy, hxy'⟩
    refine ⟨fun n => if n = 0 then some x else if n = 1 then some y else none, ?_⟩
    intro a ha
    simp only [blankRoleOverlapGraph, List.mem_cons] at ha
    rcases ha with ha | ha
    · cases ha
      exact ⟨x, y, by simp [evalIndividual], by simp [evalIndividual], hxy⟩
    · rcases ha with ha | ha
      · cases ha
        exact ⟨x, y, by simp [evalIndividual], by simp [evalIndividual], hxy'⟩
      · simp at ha

private theorem holdsGraph_consConceptInclusion (J : Interpretation σ Prop)
    (c d : Concept σ) (G : Graph σ) :
    holdsGraph J (.conceptInclusion c d :: G) ↔
      (∀ x, evalConcept J c x → evalConcept J d x) ∧ holdsGraph J G := by
  constructor
  · rintro ⟨ρ, hρ⟩
    constructor
    · have h := hρ (.conceptInclusion c d) (by simp)
      simpa [holdsSentence] using h
    · exact ⟨ρ, by
        intro a ha
        exact hρ a (by simp [ha])⟩
  · rintro ⟨ht, ⟨ρ, hρ⟩⟩
    refine ⟨ρ, ?_⟩
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with ha | ha
    · cases ha
      exact ht
    · exact hρ a ha

private theorem holdsGraph_consRoleInclusion (J : Interpretation σ Prop)
    (r s : σ.Nr) (G : Graph σ) :
    holdsGraph J (.roleInclusion r s :: G) ↔
      (∀ x y, J.role r x y → J.role s x y) ∧ holdsGraph J G := by
  constructor
  · rintro ⟨ρ, hρ⟩
    constructor
    · have h := hρ (.roleInclusion r s) (by simp)
      simpa [holdsSentence] using h
    · exact ⟨ρ, by
        intro a ha
        exact hρ a (by simp [ha])⟩
  · rintro ⟨ht, ⟨ρ, hρ⟩⟩
    refine ⟨ρ, ?_⟩
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with ha | ha
    · cases ha
      exact ht
    · exact hρ a ha

private theorem holdsGraph_namedClass (J : Interpretation σ Prop)
    (a : σ.Ni) (c : Concept σ) :
    holdsGraph J [.classAssertion (.named a) c] ↔
      evalConcept J c (J.individual a) := by
  simp [holdsGraph, holdsSentence, evalIndividual]

private theorem holdsGraph_namedRole (J : Interpretation σ Prop)
    (a b : σ.Ni) (r : σ.Nr) :
    holdsGraph J [.roleAssertion (.named a) (.named b) r] ↔
      J.role r (J.individual a) (J.individual b) := by
  simp [holdsGraph, holdsSentence, evalIndividual]

private def meaningfulAtom (σ : Signature) (a : σ.Nc) :
    Concept (targetSignature σ) :=
  .atom (a, .meaningful)

private def truthAtom (σ : Signature) (a : σ.Nc) :
    Concept (targetSignature σ) :=
  .atom (a, .truth)

private def roleConcept (σ : Signature) (r : σ.Nr) (b : Bit) :
    (targetSignature σ).Nr := (r, b)

/-- Reuse the existing coordinate translation; only the target sentence layer
    is changed here. -/
abbrev translateConcept (σ : Signature) := DirectTranslation.translateConcept σ

private def classAxiom (a : (targetSignature σ).Ni)
    (c : Concept (targetSignature σ)) : Graph (targetSignature σ) :=
  [.classAssertion (.named a) c]

private def conceptInclusionGraph (c d : Concept (targetSignature σ)) :
    Graph (targetSignature σ) := [.conceptInclusion c d]

private def atomBridge (σ : Signature) (a : σ.Nc) :
    Graph (targetSignature σ) :=
  [.conceptInclusion (truthAtom σ a) (meaningfulAtom σ a)]

private def roleBridge (σ : Signature) (r : σ.Nr) :
    Graph (targetSignature σ) :=
  [.roleInclusion (roleConcept σ r .truth) (roleConcept σ r .meaningful)]

private def meaningfulWitness (σ : Signature)
    (c d : Concept (targetSignature σ)) : Graph (targetSignature σ) :=
  blankClassGraph (.conj c d)

private def roleOverlapWitness (σ : Signature) (r s : σ.Nr) :
    Graph (targetSignature σ) :=
  blankRoleOverlapGraph (roleConcept σ r .meaningful) (roleConcept σ s .meaningful)

def translateSentence (σ : Signature) : DirectTranslation.Sentence σ →
    Graph (targetSignature σ)
  | .isa a c =>
      classAxiom a (translateConcept σ c).1
  | .edge a b r =>
      [.roleAssertion (.named a) (.named b) (roleConcept σ r .truth)]
  | .sub c d =>
      let (ct, cm) := translateConcept σ c
      let (dt, dm) := translateConcept σ d
      conceptInclusionGraph ct dt ++ meaningfulWitness σ cm dm
  | .equiv c d =>
      let (ct, cm) := translateConcept σ c
      let (dt, dm) := translateConcept σ d
      conceptInclusionGraph ct dt ++ conceptInclusionGraph dt ct ++
        meaningfulWitness σ cm dm
  | .rsub r s =>
      [.roleInclusion (roleConcept σ r .truth) (roleConcept σ s .truth)] ++
        blankRoleOverlapGraph (roleConcept σ r .meaningful) (roleConcept σ s .meaningful)

def conceptBridges (σ : Signature) : Concept σ → List (Graph (targetSignature σ))
  | .top | .bot => []
  | .atom a => [atomBridge σ a]
  | .neg c => conceptBridges σ c
  | .conj c d | .disj c d => conceptBridges σ c ++ conceptBridges σ d
  | .ex r c | .all r c => roleBridge σ r :: conceptBridges σ c

def sentenceBridges (σ : Signature) : DirectTranslation.Sentence σ →
    List (Graph (targetSignature σ))
  | .isa _ c => conceptBridges σ c
  | .edge _ _ r => [roleBridge σ r]
  | .sub c d | .equiv c d => conceptBridges σ c ++ conceptBridges σ d
  | .rsub r s => [roleBridge σ r, roleBridge σ s]

private theorem atomBridgeGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop) (a : τ.Nc) :
    holdsGraph J (atomBridge τ a) ↔
      holdsQuery J (DirectTranslation.atomBridge τ a) := by
  simp [atomBridge, DirectTranslation.atomBridge, holdsGraph, holdsSentence,
    holdsQuery, DirectTranslation.sentenceC, evalConcept, evalIndividual]
  rfl

private theorem roleBridgeGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop) (r : τ.Nr) :
    holdsGraph J (roleBridge τ r) ↔
      holdsQuery J (DirectTranslation.roleBridge τ r) := by
  simp [roleBridge, DirectTranslation.roleBridge, holdsGraph, holdsSentence,
    holdsQuery, DirectTranslation.sentenceC, evalIndividual, roleConcept]

private theorem allMemAppend_iff {α : Type} (xs ys : List α) (P : α → Prop) :
    (∀ x ∈ xs ++ ys, P x) ↔ (∀ x ∈ xs, P x) ∧ (∀ x ∈ ys, P x) := by
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (List.mem_append_left _ hx)
    · intro x hx
      exact h x (List.mem_append_right _ hx)
  · rintro ⟨hx, hy⟩ x h
    simp only [List.mem_append] at h
    rcases h with h | h
    · exact hx x h
    · exact hy x h

private theorem conceptBridgesGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop) (c : DirectTranslation.Concept τ) :
    (∀ g ∈ conceptBridges τ c, holdsGraph J g) ↔
      (∀ q ∈ DirectTranslation.conceptBridges τ c, holdsQuery J q) := by
  induction c with
  | top => simp [conceptBridges, DirectTranslation.conceptBridges]
  | bot => simp [conceptBridges, DirectTranslation.conceptBridges]
  | atom a =>
      simp [conceptBridges, DirectTranslation.conceptBridges, atomBridgeGraphQuery]
  | neg c ih =>
      simpa [conceptBridges, DirectTranslation.conceptBridges] using ih
  | conj c d ihc ihd =>
      simp only [conceptBridges, DirectTranslation.conceptBridges,
        allMemAppend_iff]
      exact and_congr ihc ihd
  | disj c d ihc ihd =>
      simp only [conceptBridges, DirectTranslation.conceptBridges,
        allMemAppend_iff]
      exact and_congr ihc ihd
  | ex r c ih =>
      simp [conceptBridges, DirectTranslation.conceptBridges,
        roleBridgeGraphQuery, ih]
  | all r c ih =>
      simp [conceptBridges, DirectTranslation.conceptBridges,
        roleBridgeGraphQuery, ih]

private theorem sentenceBridgesGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop) (s : DirectTranslation.Sentence τ) :
    (∀ g ∈ sentenceBridges τ s, holdsGraph J g) ↔
      (∀ q ∈ DirectTranslation.sentenceBridges τ s, holdsQuery J q) := by
  cases s with
  | isa a c => exact conceptBridgesGraphQuery τ J c
  | edge a b r =>
      simp [sentenceBridges, DirectTranslation.sentenceBridges,
        roleBridgeGraphQuery]
  | sub c d | equiv c d =>
      simp only [sentenceBridges, DirectTranslation.sentenceBridges,
        allMemAppend_iff]
      exact and_congr (conceptBridgesGraphQuery τ J c)
        (conceptBridgesGraphQuery τ J d)
  | rsub r s =>
      simp [sentenceBridges, DirectTranslation.sentenceBridges,
        roleBridgeGraphQuery]

private theorem translatedSentenceGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop) (s : DirectTranslation.Sentence τ) :
    holdsGraph J (translateSentence τ s) ↔
      holdsQuery J (DirectTranslation.translateSentence τ s) := by
  cases s with
  | isa a c =>
      let a' : (targetSignature τ).Ni := a
      change holdsGraph J [.classAssertion (.named a')
        (DirectTranslation.translateConcept τ c).1] ↔ _
      rw [holdsGraph_namedClass]
      rfl
  | edge a b r =>
      let a' : (targetSignature τ).Ni := a
      let b' : (targetSignature τ).Ni := b
      change holdsGraph J
        [.roleAssertion (.named a') (.named b') (roleConcept τ r .truth)] ↔ _
      rw [holdsGraph_namedRole]
      rfl
  | sub c d =>
      let ct := DirectTranslation.translateConcept τ c
      let dt := DirectTranslation.translateConcept τ d
      change holdsGraph J (.conceptInclusion (DirectTranslation.translateConcept τ c).1
        (DirectTranslation.translateConcept τ d).1 ::
        blankClassGraph (.conj (DirectTranslation.translateConcept τ c).2
          (DirectTranslation.translateConcept τ d).2)) ↔ _
      rw [holdsGraph_consConceptInclusion, blankClassGraph_iff]
      change (∀ x, evalC J ct.1 x → evalC J dt.1 x) ∧
          (∃ x, evalC J ct.2 x ∧ evalC J dt.2 x) ↔ _
      rfl
  | equiv c d =>
      let ct := DirectTranslation.translateConcept τ c
      let dt := DirectTranslation.translateConcept τ d
      change holdsGraph J (.conceptInclusion (DirectTranslation.translateConcept τ c).1
        (DirectTranslation.translateConcept τ d).1 ::
        .conceptInclusion (DirectTranslation.translateConcept τ d).1
          (DirectTranslation.translateConcept τ c).1 ::
        blankClassGraph (.conj (DirectTranslation.translateConcept τ c).2
          (DirectTranslation.translateConcept τ d).2)) ↔ _
      rw [holdsGraph_consConceptInclusion, holdsGraph_consConceptInclusion,
        blankClassGraph_iff]
      change ((∀ x, evalC J ct.1 x → evalC J dt.1 x) ∧
          (∀ x, evalC J dt.1 x → evalC J ct.1 x) ∧
          (∃ x, evalC J ct.2 x ∧ evalC J dt.2 x)) ↔ _
      constructor
      · rintro ⟨hcd, hdc, ⟨x, hcx, hdx⟩⟩
        exact ⟨⟨hcd, ⟨x, hcx, hdx⟩⟩, ⟨hdc, ⟨x, hdx, hcx⟩⟩⟩
      · rintro ⟨⟨hcd, _⟩, ⟨hdc, ⟨x, hdx, hcx⟩⟩⟩
        exact ⟨hcd, hdc, ⟨x, hcx, hdx⟩⟩
  | rsub r s =>
      let rt := roleConcept τ r .truth
      let st := roleConcept τ s .truth
      let rm := roleConcept τ r .meaningful
      let sm := roleConcept τ s .meaningful
      change holdsGraph J (.roleInclusion (roleConcept τ r .truth)
        (roleConcept τ s .truth) :: blankRoleOverlapGraph
          (roleConcept τ r .meaningful) (roleConcept τ s .meaningful)) ↔ _
      rw [holdsGraph_consRoleInclusion, blankRoleOverlapGraph_iff]
      change (∀ x y, J.role rt x y → J.role st x y) ∧
          (∃ x y, J.role rm x y ∧ J.role sm x y) ↔ _
      rfl

private theorem sentenceGraphsGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop)
    (S : List (DirectTranslation.Sentence τ)) :
    (∀ g ∈ S.map (translateSentence τ), holdsGraph J g) ↔
      (∀ q ∈ S.map (DirectTranslation.translateSentence τ), holdsQuery J q) := by
  induction S with
  | nil => simp
  | cons s ss ih =>
      simp [translatedSentenceGraphQuery]

private theorem sentenceBridgeGraphsGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop)
    (S : List (DirectTranslation.Sentence τ)) :
    (∀ g ∈ S.flatMap (sentenceBridges τ), holdsGraph J g) ↔
      (∀ q ∈ S.flatMap (DirectTranslation.sentenceBridges τ), holdsQuery J q) := by
  induction S with
  | nil => simp
  | cons s ss ih =>
      simp only [List.flatMap_cons, allMemAppend_iff]
      exact and_congr (sentenceBridgesGraphQuery τ J s) ih

/-- The effective compiler for an ordinary weak-Kleene source signature. -/
def compileWK (σ : Signature)
    (Γ Δ : List (DirectTranslation.Sentence σ)) :
    Problem (targetSignature σ) where
  premises := (Γ ++ Δ).flatMap (sentenceBridges σ) ++ Γ.map (translateSentence σ)
  conclusions := Δ.map (translateSentence σ)

/-- Compile AC sentences by first projecting their positive support to WK. -/
def compileAC (σ : Signature)
    (Γ Δ : List (DirectTranslation.Sentence σ)) :
    Problem (targetSignature (wkSignature σ)) :=
  compileWK (wkSignature σ) (Γ.map (projectSentence σ)) (Δ.map (projectSentence σ))

structure Translation (σ : Signature) where
  bridges : List (Graph (targetSignature (wkSignature σ)))
  sentences : List (Graph (targetSignature (wkSignature σ)))

/-- Compile a finite source sentence set, recording its coherence bridges. -/
def translation (σ : Signature) (Γ : List (DirectTranslation.Sentence σ)) :
    Translation σ where
  bridges := (Γ.map (projectSentence σ)).flatMap
    (sentenceBridges (wkSignature σ))
  sentences := (Γ.map (projectSentence σ)).map
    (translateSentence (wkSignature σ))

/-- Entailment assumes the bridges for both signatures, then the translated
    premises must entail each translated conclusion graph. -/
def blankNodeEntailment (P Q : Translation σ) : Prop :=
  graphEntailment (P.bridges ++ Q.bridges ++ P.sentences) Q.sentences

private theorem compiledPremisesGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop)
    (Γ Δ : List (DirectTranslation.Sentence τ)) :
    (∀ g ∈ ((Γ ++ Δ).flatMap (sentenceBridges τ) ++
        Γ.map (translateSentence τ)), holdsGraph J g) ↔
      (∀ q ∈ ((Γ ++ Δ).flatMap (DirectTranslation.sentenceBridges τ) ++
        Γ.map (DirectTranslation.translateSentence τ)), holdsQuery J q) := by
  simp only [List.flatMap_append, allMemAppend_iff]
  exact and_congr
    (and_congr (sentenceBridgeGraphsGraphQuery τ J Γ)
      (sentenceBridgeGraphsGraphQuery τ J Δ))
    (sentenceGraphsGraphQuery τ J Γ)

private theorem compiledConclusionsGraphQuery (τ : Signature)
    (J : Interpretation (targetSignature τ) Prop)
    (Δ : List (DirectTranslation.Sentence τ)) :
    (∀ g ∈ Δ.map (translateSentence τ), holdsGraph J g) ↔
      (∀ q ∈ Δ.map (DirectTranslation.translateSentence τ), holdsQuery J q) :=
  sentenceGraphsGraphQuery τ J Δ

theorem blankNodeEntailment_iff_problemEntailment {σ : Signature}
    (Γ Δ : List (DirectTranslation.Sentence σ)) :
    blankNodeEntailment (translation σ Γ) (translation σ Δ) ↔
      DirectTranslation.problemEntailment (DirectTranslation.compileAC σ Γ Δ) := by
  let τ := wkSignature σ
  have hprem (J : Interpretation (targetSignature τ) Prop) :
      (∀ g ∈ (translation σ Γ).bridges ++ (translation σ Δ).bridges ++
        (translation σ Γ).sentences, holdsGraph J g) ↔
      (∀ q ∈ (DirectTranslation.compileAC σ Γ Δ).premises, holdsQuery J q) := by
    simpa [translation, DirectTranslation.compileAC, DirectTranslation.compileWK,
      τ] using compiledPremisesGraphQuery τ J
        (Γ.map (projectSentence σ)) (Δ.map (projectSentence σ))
  have hconcl (J : Interpretation (targetSignature τ) Prop) :
      (∀ g ∈ (translation σ Δ).sentences, holdsGraph J g) ↔
      (∀ q ∈ (DirectTranslation.compileAC σ Γ Δ).conclusions, holdsQuery J q) := by
    simpa [translation, DirectTranslation.compileAC, DirectTranslation.compileWK,
      τ] using compiledConclusionsGraphQuery τ J (Δ.map (projectSentence σ))
  unfold blankNodeEntailment graphEntailment
  unfold DirectTranslation.problemEntailment DirectTranslation.queryEntailment
  constructor
  · intro h J hp q hq
    have hgp := (hprem J).2 hp
    have hgc := h J hgp
    exact (hconcl J).1 hgc q hq
  · intro h J hp g hg
    have hqp := (hprem J).1 hp
    have hqc := h J hqp
    exact (hconcl J).2 hqc g hg

/-- The main adequacy statement for the blank-node ALCH target. -/
theorem translation_exists {σ : Signature} :
    ∀ Γ Δ : List (DirectTranslation.Sentence σ),
      DirectTranslation.entailmentA Γ Δ ↔
        blankNodeEntailment (translation σ Γ) (translation σ Δ) := by
  intro Γ Δ
  exact Iff.trans (DirectTranslation.translation_exists Γ Δ)
    (blankNodeEntailment_iff_problemEntailment Γ Δ).symm

end DirectTranslation.BlankNodeTarget
