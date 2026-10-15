import Final

open ALCHAC

namespace TranslationRender

inductive Atom where
  | A | B | C | GoodStandingAcc | SecureAcc | FraudRisk
  deriving Repr

inductive Role where
  | r | s | hasCreditCardDebt | hasMortgageDebt | hasDebt
  deriving Repr

inductive Individual where
  | alice | bob | applicant | mortgageAccount | creditAccount
  deriving Repr

def σ : Signature where
  Nc := Atom
  Nr := Role
  Ni := Individual

-- Short names keep the examples in TranslationDemo focused on their KBs.
def A : 𝒞 σ := [Atom.A]ₐ
def B : 𝒞 σ := [Atom.B]ₐ
def C : 𝒞 σ := [Atom.C]ₐ
def GoodStandingAcc : 𝒞 σ := [Atom.GoodStandingAcc]ₐ
def SecureAcc : 𝒞 σ := [Atom.SecureAcc]ₐ
def FraudRisk : 𝒞 σ := [Atom.FraudRisk]ₐ
abbrev r : σ.Nr := Role.r
abbrev s : σ.Nr := Role.s
abbrev hasCreditCardDebt : σ.Nr := Role.hasCreditCardDebt
abbrev hasMortgageDebt : σ.Nr := Role.hasMortgageDebt
abbrev hasDebt : σ.Nr := Role.hasDebt
abbrev alice : σ.Ni := Individual.alice
abbrev bob : σ.Ni := Individual.bob
abbrev applicant : σ.Ni := Individual.applicant
abbrev mortgageAccount : σ.Ni := Individual.mortgageAccount
abbrev creditAccount : σ.Ni := Individual.creditAccount

private def atomName : Atom → String
  | .A => "A"
  | .B => "B"
  | .C => "C"
  | .GoodStandingAcc => "GoodStandingAcc"
  | .SecureAcc => "SecureAcc"
  | .FraudRisk => "FraudRisk"

private def roleName : Role → String
  | .r => "r"
  | .s => "s"
  | .hasCreditCardDebt => "hasCreditCardDebt"
  | .hasMortgageDebt => "hasMortgageDebt"
  | .hasDebt => "hasDebt"

private def individualName : Individual → String
  | .alice => "alice"
  | .bob => "bob"
  | .applicant => "applicant"
  | .mortgageAccount => "mortgageAccount"
  | .creditAccount => "creditAccount"

private def sideName : Side → String
  | +ₚ => "⁺"
  | -ₚ => "⁻"

private def bitName : Bit → String
  | 𝕋 => "ₜ"
  | 𝕄 => "ₘ"

private def renderConcept {sig : Signature} {R : Type}
    (atom : sig.Nc → String) (role : R → String) :
    Concept sig R → String
  | ⊤ => "⊤"
  | ⊥ => "⊥"
  | [a]ₐ => atom a
  | ¬ₜ c => "¬(" ++ renderConcept atom role c ++ ")"
  | c ⊓ₜ d => "(" ++ renderConcept atom role c ++ " ⊓ " ++
      renderConcept atom role d ++ ")"
  | c ⊔ₜ d => "(" ++ renderConcept atom role c ++ " ⊔ " ++
      renderConcept atom role d ++ ")"
  | ∃[r] c => "∃" ++ role r ++ "." ++ renderConcept atom role c
  | ∀[r] c => "∀" ++ role r ++ "." ++ renderConcept atom role c

private def targetRole : ℛᵁ (σᵂᴷ)ᵀ → String
  | [r]ᵣ => roleName r.1 ++ bitName r.2
  | 𝒰 => "𝒰"
  | p ⊓ᵣ q => "(" ++ targetRole p ++ " ⊓ᵣ " ++ targetRole q ++ ")"

private def acConcept : 𝒞 σ → String :=
  renderConcept atomName roleName

private def wkConcept : 𝒞 σᵂᴷ → String :=
  renderConcept
    (fun (a : (σᵂᴷ).Nc) => atomName a.1 ++ sideName a.2)
    roleName

private def classicalConcept : 𝒞ᵁ (σᵂᴷ)ᵀ → String :=
  renderConcept
    (fun (a : ((σᵂᴷ)ᵀ).Nc) =>
      atomName a.1.1 ++ sideName a.1.2 ++ bitName a.2)
    targetRole

private def renderSentence {sig : Signature} {R : Type}
    (individual : sig.Ni → String) (concept : Concept sig R → String)
    (role : R → String) : Sentence sig R → String
  | a :ₐ c => individual a ++ " :ₐ " ++ concept c
  | (a, b) :ᵣ r => "(" ++ individual a ++ ", " ++ individual b ++
      ") :ᵣ " ++ role r
  | c ⊑ d => concept c ++ " ⊑ " ++ concept d
  | c ≡ d => concept c ++ " ≡ " ++ concept d
  | r ⊑ᵣ s => role r ++ " ⊑ᵣ " ++ role s

private def acSentence : Φ σ → String :=
  renderSentence individualName acConcept roleName

private def wkSentence : Φ σᵂᴷ → String :=
  renderSentence individualName wkConcept roleName

private def classicalSentence : Φᵁ (σᵂᴷ)ᵀ → String :=
  renderSentence individualName classicalConcept targetRole

-- Lists enumerate the finite clauses of a Set for display.
private def truthClauses : Φ σᵂᴷ → List (Φᵁ (σᵂᴷ)ᵀ)
  | a :ₐ c => [a :ₐ τ c]
  | (a, b) :ᵣ role => [(a, b) :ᵣ [(role, 𝕋)]ᵣ]
  | c ⊑ d => [τ c ⊑ τ d, ∃₁(μ c ⊓ₜ μ d)]
  | c ≡ d =>
      [τ c ⊑ τ d, ∃₁(μ c ⊓ₜ μ d)] ++
        [τ d ⊑ τ c, ∃₁(μ d ⊓ₜ μ c)]
  | role₁ ⊑ᵣ role₂ =>
      [[(role₁, 𝕋)]ᵣ ⊑ᵣ [(role₂, 𝕋)]ᵣ,
        (role₁, 𝕄) ⨅⁺ (role₂, 𝕄)]

private def conceptBridges : 𝒞 σᵂᴷ → List (Φᵁ (σᵂᴷ)ᵀ)
  | ⊤ | ⊥ => []
  | [a]ₐ => [atomicConceptBridge a]
  | ¬ₜ c => conceptBridges c
  | c ⊓ₜ d | c ⊔ₜ d => conceptBridges c ++ conceptBridges d
  | ∃[role] c | ∀[role] c => atomicRoleBridge role :: conceptBridges c

private def bridgeClauses : Φ σᵂᴷ → List (Φᵁ (σᵂᴷ)ᵀ)
  | _ :ₐ c => conceptBridges c
  | (_, _) :ᵣ role => [atomicRoleBridge role]
  | c ⊑ d | c ≡ d => conceptBridges c ++ conceptBridges d
  | role₁ ⊑ᵣ role₂ => [atomicRoleBridge role₁, atomicRoleBridge role₂]

private def rowsSet {α : Type} (rows : List α) : α* :=
  fun x => x ∈ rows

private theorem rowsSet_nil {α : Type} : rowsSet ([] : List α) = ∅ := by
  funext x
  apply propext
  simp only [rowsSet, List.not_mem_nil]
  change False ↔ False
  rfl

private theorem rowsSet_singleton {α : Type} (a : α) :
    rowsSet [a] = {a} := by
  funext x
  apply propext
  simp only [rowsSet, List.mem_cons, List.not_mem_nil, or_false]
  rfl

private theorem rowsSet_pair {α : Type} (a b : α) :
    rowsSet [a, b] = {a} ∪ {b} := by
  funext x
  apply propext
  simp only [rowsSet, List.mem_cons, List.not_mem_nil, or_false]
  rfl

private theorem rowsSet_append {α : Type} (xs ys : List α) :
    rowsSet (xs ++ ys) = rowsSet xs ∪ rowsSet ys := by
  funext x
  apply propext
  exact List.mem_append

private theorem rowsSet_cons {α : Type} (a : α) (xs : List α) :
    rowsSet (a :: xs) = {a} ∪ rowsSet xs := by
  funext x
  apply propext
  exact List.mem_cons

private theorem truthClauses_correct (φ : Φ σᵂᴷ) :
    rowsSet (truthClauses φ) = τ φ := by
  cases φ <;> funext ψ <;> apply propext <;>
    simp only [rowsSet, truthClauses, TauTranslation.tau,
      tauSentence, tauSubsumption, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] <;> rfl

private theorem conceptBridges_correct (c : 𝒞 σᵂᴷ) :
    rowsSet (conceptBridges c) = 𝒟 c := by
  induction c with
  | top | bot => simp [conceptBridges, rowsSet_nil, BridgeTranslation.bridge,
      ALCHAC.conceptBridges]
  | atom a => simp [conceptBridges, rowsSet_singleton, BridgeTranslation.bridge,
      ALCHAC.conceptBridges]
  | neg c ih => simpa [conceptBridges, BridgeTranslation.bridge,
      ALCHAC.conceptBridges] using ih
  | conj c d ihc ihd | disj c d ihc ihd =>
      simp [conceptBridges, BridgeTranslation.bridge,
        ALCHAC.conceptBridges, rowsSet_append, ihc, ihd]
  | ex role c ih | all role c ih =>
      simp [conceptBridges, BridgeTranslation.bridge,
        ALCHAC.conceptBridges, rowsSet_cons, ih]

private theorem bridgeClauses_correct (φ : Φ σᵂᴷ) :
    rowsSet (bridgeClauses φ) = 𝒟 φ := by
  cases φ <;> simp [bridgeClauses, BridgeTranslation.bridge,
    sentenceBridges, rowsSet_singleton, rowsSet_pair, rowsSet_append,
    conceptBridges_correct]

private def block (title : String) (rows : List String) : String :=
  title ++ "\n" ++
    (if rows.isEmpty then "  ∅" else
      String.intercalate "\n" (rows.map (fun row => "  " ++ row)))

/-- An array enumerates a finite AC KB; its semantic value is a Set. -/
def asSet (entries : Array (Φ σ)) : (Φ σ)* :=
  fun φ => φ ∈ entries.toList

/-- Display the two stages and the classical entailment produced by MainResult. -/
def renderReduction (premises conclusions : Array (Φ σ)) : String := Id.run do
  let sourceΓ := premises.toList
  let sourceΔ := conclusions.toList
  let wkΓ := sourceΓ.map piSentence
  let wkΔ := sourceΔ.map piSentence
  let classicalΓ :=
    (wkΓ.flatMap truthClauses ++
      wkΓ.flatMap bridgeClauses ++
      wkΔ.flatMap bridgeClauses).map classicalSentence |>.eraseDups
  let classicalΔ := (wkΔ.flatMap truthClauses).map classicalSentence |>.eraseDups
  return String.intercalate "\n\n" [
    block "AC Γ" (sourceΓ.map acSentence),
    block "AC Δ" (sourceΔ.map acSentence),
    block "WK πΓ" (wkΓ.map wkSentence),
    block "WK πΔ" (wkΔ.map wkSentence),
    block "Classical premises τ(πΓ) ∪ 𝒟(πΓ) ∪ 𝒟(πΔ)" classicalΓ,
    block "Classical conclusions τ(πΔ)" classicalΔ]

def showReduction (premises conclusions : Array (Φ σ)) : IO Unit :=
  IO.println (renderReduction premises conclusions)

/-- The displayed KBs are the sets used by the main theorem. -/
theorem reductionCorrect (premises conclusions : Array (Φ σ)) :
    (asSet premises ⊨ᴬᶜ asSet conclusions) ↔
      ((τ (π (asSet premises)) ∪
        𝒟 (π (asSet premises)) ∪
        𝒟 (π (asSet conclusions))) ⊨ᶜ
        τ (π (asSet conclusions))) :=
  MainResult σ (asSet premises) (asSet conclusions)

end TranslationRender
