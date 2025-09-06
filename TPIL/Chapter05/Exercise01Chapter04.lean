/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 5 Exercises

## Exercise 2

### Chapter 4

#### Exercise 4.1
-/

section

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor <;> intro h
  · constructor <;> intro x
    · exact (h x).1
    · exact (h x).2
  · intro x
    exact ⟨h.1 x, h.2 x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hpq hp x
  exact (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, (p x ∨ q x) := by
  intro h x
  cases h with
  | inl hp => left; exact hp x
  | inr hq => right; exact hq x

end

/-!
#### Exercise 4.2
-/

section

set_option linter.unusedVariables false

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro w
  constructor <;> intro h
  · exact h w
  · intro; assumption

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  · intro h
    cases (Classical.em r) with
    | inl hr => right; assumption
    | inr hnr =>
      left
      intro x
      cases (h x) with
      | inl hpx => assumption
      | inr hr => exfalso; contradiction
  · intro h x
    cases h with
    | inl hpx => left; exact hpx x
    | inr hr => right; assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  · intro h hr x
    exact h x hr
  · intro h x hr
    exact h hr x

-- alternative proof
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor <;>
  { intro h a b;
    exact h b a }

end

/-!
#### Exercise 4.3
-/

section

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False := by
  have hnsbb : ¬shaves barber barber := by
    intro hsbb
    have hnsbb : ¬shaves barber barber := by exact (h barber).mp hsbb
    contradiction
  have hsbb : shaves barber barber := by
    exact (h barber).mpr hnsbb
  contradiction

end

/-!
#### Exercise 4.4

There's no point in using tactics for these definitions.

#### Exercise 4.5
-/

section

set_option linter.unusedVariables false

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro ⟨_, hr⟩
  assumption

example (a : α) : r → (∃ x : α, r) := by
  intro h
  exists a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  · intro ⟨w, ⟨hpw, hr⟩⟩
    exact ⟨⟨w, hpw⟩, hr⟩
  · intro ⟨⟨w, hpw⟩, hr⟩
    exact ⟨w, ⟨hpw, hr⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro ⟨w, hpqw⟩
    cases hpqw with
    | inl hpw => left; exists w
    | inr hqw => right; exists w
  · intro h
    match h with
    | .inl ⟨w, hpw⟩ => exists w; left; assumption
    | .inr ⟨w, hqw⟩ => exists w; right; assumption

example : (∀ x, p x) ↔ ¬(∃ x, ¬p x) := by
  constructor
  · intro h ⟨w, hnpw⟩
    apply hnpw
    exact h w
  · intro h x
    apply byContradiction
    intro hnpx
    apply h
    exists x

example : (∃ x, p x) ↔ ¬(∀ x, ¬p x) := by
  constructor
  · intro ⟨w, hpw⟩ h
    exact h w hpw
  · intro h
    apply byContradiction
    intro hnexp
    apply h
    intro x hpx
    apply hnexp
    exists x

example : (¬∃ x, p x) ↔ (∀ x, ¬p x) := by
  constructor
  · intro hnexp x hpx
    apply hnexp
    exists x
  · intro h ⟨w, hpw⟩
    exact h w hpw

example : (¬∀ x, p x) ↔ (∃ x, ¬p x) := by
  constructor
  · intro h
    apply byContradiction
    intro hnexnp
    apply h
    intro x
    apply byContradiction
    intro hnpx
    apply hnexnp
    exists x
  · intro ⟨w, hnpw⟩ h
    apply hnpw
    exact h w

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  · intro h ⟨w, hpw⟩
    exact h w hpw
  · intro h x hpx
    exact h ⟨x, hpx⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  · intro ⟨w, hw⟩ h
    apply hw
    exact h w
  · intro h
    cases (em r) with
    | inl hr =>
      exists a
      intro
      assumption
    | inr hnr =>
      have hnap : ¬∀ x, p x := by
        intro hap
        apply hnr
        exact h hap
      have hexnp : ∃ x, ¬p x := by
        apply byContradiction
        intro hnexnp
        apply hnap
        intro x
        apply byContradiction
        intro hnpx
        apply hnexnp
        exists x
      let ⟨w, hnpw⟩ := hexnp
      exists w
      intro hpw
      contradiction

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  · intro ⟨w, hw⟩ hr
    exists w
    exact hw hr
  · intro h
    cases (em r) with
    | inl hr =>
      let ⟨w, hpw⟩ := h hr
      exists w
      intro
      assumption
    | inr hnr =>
      exists a
      intro hr
      contradiction

end
