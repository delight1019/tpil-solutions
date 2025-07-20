/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Exam 2

This examination covers Chapter 6 of the text, focusing on implicit lambdas.

## Problem 1

Prove the following examples without using tactics:
-/

example : True ↔ ∀ {p : Prop}, p → p :=
  sorry

example : False ↔ ∀ {p : Prop}, p :=
  sorry

example {p q : Prop} : p ∧ q ↔ ∀ {r : Prop}, (p → q → r) → r :=
  sorry

example {p q : Prop} : p ∨ q ↔ ∀ {r : Prop}, (p → r) → (q → r) → r :=
  sorry

example {α : Sort u} {p : α → Prop} : (∃ (x : α), p x) ↔ ∀ {r : Prop}, (∀ (w : α), p w → r) → r :=
  sorry
