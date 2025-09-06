/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 5 Exercises

## Exercise 1

### Chapter 3

#### Exercise 3.1
-/

section

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor <;>
  intro h <;>
  exact ⟨h.2, h.1⟩

example : p ∨ q ↔ q ∨ p := by
  constructor <;>
  intro h <;>
  { cases h
    · right; assumption
    · left; assumption }

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor <;>
  intro h
  · exact ⟨h.1.1, ⟨h.1.2, h.2⟩⟩
  · exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor <;>
  intro h
  · cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => left; assumption
      | inr hq => right; left; assumption
    | inr hr => right; right; assumption
  · cases h with
    | inl hp => left; left; assumption
    | inr hqr =>
      cases hqr with
      | inl hq => left; right; assumption
      | inr hr => right; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor <;> intro h
  · cases h.2 with
    | inl hq => left; exact ⟨h.1, hq⟩
    | inr hr => right; exact ⟨h.1, hr⟩
  · cases h with
    | inl hpq => exact ⟨hpq.1, Or.inl hpq.2⟩
    | inr hpr => exact ⟨hpr.1, Or.inr hpr.2⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor <;> intro h
  · match h with
    | Or.inl hp  => constructor <;> left <;> assumption
    | Or.inr ⟨hq, hr⟩ => constructor <;> right <;> assumption
  · match h.1, h.2 with
    | Or.inl hp, _ => left <;> assumption
    | _, Or.inl hp => left <;> assumption
    | Or.inr hq, Or.inr hr => right <;> exact ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  · intro h hpq
    exact h hpq.1 hpq.2
  · intro h hp hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h hpq
    cases hpq with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

-- this example follows from the previous one
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h hpq
    cases hpq with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h hpq
  cases h with
  | inl hp => exact hp hpq.1
  | inr hq => exact hq hpq.2

example : ¬(p ∧ ¬p) := by
  intro h
  exact h.2 h.1

example : p ∧ ¬q → ¬(p → q) := by
  intro h hpq
  exact h.2 (hpq h.1)

example : ¬p → (p → q) := by
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp => contradiction
  | inr hq => assumption

example : p ∨ False ↔ p := by
  constructor <;> intro h
  · cases h with
    | inl hp => assumption
    | inr _ => contradiction
  · left; assumption

example : p ∧ False ↔ False := by
  constructor
  · exact And.right
  · exact False.elim

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
  exact hnq (h hp)

end

/-!
#### Exercise 3.2
-/

section

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases (em p) with
  | inl hp =>
    cases h hp with
    | inl hq => left; intro; assumption
    | inr hr => right; intro; assumption
  | inr hnp => left; intro hp; contradiction

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp => right; intro hq; exact h ⟨hp, hq⟩
  | inr hnp => left; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  cases (em p) with
  | inl hp =>
    have hnq : ¬q := by intro hq; apply h; intro; assumption
    exact ⟨hp, hnq⟩
  | inr hnp =>
    have hpq : p → q := by intro hp; exfalso; contradiction
    contradiction

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (em p) with
  | inl hp => right; exact h hp
  | inr hnp => left; assumption

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  apply byContradiction
  intro hnq
  exact h hnq hp

example : p ∨ ¬p := by
  exact em p

example : ((p → q) → p) → p := by
  intro h
  apply byContradiction
  intro hnp
  have hpq : p → q := by intro hp; exfalso; exact hnp hp
  exact hnp (h hpq)

end

/-!
#### Exercise 3.3
-/

example (p : Prop) : ¬(p ↔ ¬p) := by
  intro h
  have hnp : ¬p := by intro hp; exact h.mp hp hp
  have hp : p := by exact h.mpr hnp
  exact hnp hp
