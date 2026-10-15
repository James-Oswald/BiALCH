import TranslationRender

open ALCHAC TranslationRender

#eval showReductionAndEntailments
  #[alice :ₐ A]
  #[alice :ₐ ¬ₜA]

-- Excluded middle is not forced by an unknown atomic concept.
#eval showReductionAndEntailments
  #[alice :ₐ ⊤]
  #[alice :ₐ (A ⊔ₜ ¬ₜ A)]

-- A contradiction need not entail an unrelated assertion (ex falso).
#eval showReductionAndEntailments
  #[alice :ₐ (A ⊓ₜ ¬ₜ A)]
  #[bob :ₐ B]

-- The paper's loan applicant and credit-card account example.
-- The credit account has conflicting evidence about good standing;
-- the conflict does not support an unrelated fraud-risk conclusion.
#eval showReductionAndEntailments
  #[hasCreditCardDebt ⊑ᵣ hasDebt,
    hasMortgageDebt ⊑ᵣ hasDebt,
    (applicant, creditAccount) :ᵣ hasCreditCardDebt,
    (applicant, mortgageAccount) :ᵣ hasMortgageDebt,
    applicant :ₐ ∀[hasDebt] GoodStandingAcc,
    mortgageAccount :ₐ (GoodStandingAcc ⊓ₜ SecureAcc),
    creditAccount :ₐ ¬ₜ GoodStandingAcc]
  #[applicant :ₐ FraudRisk]

#eval showReductionAndEntailments
  #[alice :ₐ ∃[r] (A ⊔ₜ B)]
  #[alice :ₐ ∀[r] (¬ₜ B)]

#eval showReductionAndEntailments
  #[A ⊑ B, B ≡ C]
  #[alice :ₐ C]

#eval showReductionAndEntailments
  #[r ⊑ᵣ s, (alice, bob) :ᵣ r]
  #[(alice, bob) :ᵣ s]

-- Assertions together with concept inclusions.
#eval showReductionAndEntailments
  #[alice :ₐ A,
    bob :ₐ B,
    (alice, bob) :ᵣ r,
    A ⊑ ∃[r] B,
    B ⊑ C]
  #[alice :ₐ ∃[r] C,
    bob :ₐ C]

-- Negation, equivalence, and role inclusion in the same KB.
#eval showReductionAndEntailments
  #[alice :ₐ ¬ₜ (A ⊓ₜ ∃[r] B),
    bob :ₐ (A ⊔ₜ ¬ₜ C),
    A ≡ ∀[s] B,
    B ⊑ ¬ₜ C,
    (alice, bob) :ᵣ s,
    r ⊑ᵣ s]
  #[alice :ₐ ∀[s] (¬ₜ C),
    bob :ₐ ¬ₜ A,
    (alice, bob) :ᵣ r]

-- A larger mixture of quantified concepts and role facts.
#eval showReductionWithClassicalCandidate largeClassicalCounterbranch
  #[alice :ₐ ∀[r] (¬ₜ A ⊔ₜ B),
    bob :ₐ ∃[s] (C ⊓ₜ ¬ₜ B),
    A ⊑ ∃[r] (B ⊔ₜ C),
    B ≡ ¬ₜ C,
    C ⊑ ∀[s] A,
    (alice, bob) :ᵣ r,
    (bob, alice) :ᵣ s,
    r ⊑ᵣ s]
  #[alice :ₐ ∃[s] C,
    bob :ₐ ∀[r] B,
    A ⊑ C,
    (alice, bob) :ᵣ s]
