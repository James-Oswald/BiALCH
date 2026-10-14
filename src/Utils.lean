
import Init

/-
This is a small utility library that inclides the few
basic definitions we would use from Mathlib.

It includes:

1) Mathlib Sets, Set X := X -> Prop, and helpers
2) Top and Bot classes with notations ⊤ and ⊥
3) Some simple theorems about equality and classical logic

-/

-- MARK: Mathlib Sets
universe u v w

abbrev Set (α : Type u) := α → Prop

instance {α : Type u} : Membership α (Set α) :=
  ⟨fun s a => s a⟩

namespace Set

/-- The set of values obtained by varying an argument over its type. -/
def ofValues {α : Type u} {β : Type v} (f : α → β) : Set β :=
  fun b => ∃ a, f a = b

@[simp] theorem mem_ofValues {α : Type u} {β : Type v}
    {f : α → β} {b : β} :
    b ∈ ofValues f ↔ ∃ a, f a = b := Iff.rfl

@[simp] theorem forall_mem_ofValues {α : Type u} {β : Type v}
    {f : α → β} {P : β → Prop} :
    (∀ b ∈ ofValues f, P b) ↔ ∀ a, P (f a) := by
  constructor
  · intro h a
    exact h (f a) ⟨a, rfl⟩
  · intro h b hb
    obtain ⟨a, rfl⟩ := hb
    exact h a

@[simp] theorem exists_mem_ofValues {α : Type u} {β : Type v}
    {f : α → β} {P : β → Prop} :
    (∃ b ∈ ofValues f, P b) ↔ ∃ a, P (f a) := by
  constructor
  · rintro ⟨b, ⟨a, rfl⟩, hb⟩
    exact ⟨a, hb⟩
  · rintro ⟨a, ha⟩
    exact ⟨f a, ⟨a, rfl⟩, ha⟩

/-- The image of a set under a function. -/
def image {A : Type u} {B : Type v} (g : A → B) (X : Set A) : Set B :=
  fun b => ∃ a ∈ X, g a = b

/-- Projecting a set of values gives the values of the composite function. -/
@[simp] theorem image_ofValues {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) :
    image g (ofValues f) = ofValues (fun a => g (f a)) := by
  funext c
  exact propext exists_mem_ofValues

/-- A set of values indexed by an inhabited type is nonempty. -/
theorem ofValues_nonempty {α : Type u} {β : Type v} [Nonempty α]
    (f : α → β) : ∃ b, b ∈ ofValues f := by
  obtain ⟨a⟩ := ‹Nonempty α›
  exact ⟨f a, a, rfl⟩

end Set

/-- `{f x | x : α}` is the set of values of `f` on the whole type `α`. -/
syntax:arg "{" term " | " ident " : " term "}" : term
macro_rules
  | `({ $value:term | $x:ident : $α:term }) =>
      `(Set.ofValues (fun $x : $α => $value))

-- MARK: Top and Bot

/- Concept syntax only needs distinguished top and bottom elements. -/
class Top (α : Type u) where
  top : α

class Bot (α : Type u) where
  bot : α

notation "⊤" => Top.top
notation "⊥" => Bot.bot

attribute [match_pattern] Top.top Bot.bot

-- MARK: Lemmas

theorem congrArg₂ {α : Sort u} {β : Sort v} {γ : Sort w}
    (f : α → β → γ) {x x' : α} {y y' : β}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by
  cases hx
  cases hy
  rfl

theorem not_not {p : Prop} : ¬¬p ↔ p := Classical.not_not

theorem or_iff_not_imp_left {p q : Prop} : p ∨ q ↔ (¬p → q) :=
  Classical.or_iff_not_imp_left
