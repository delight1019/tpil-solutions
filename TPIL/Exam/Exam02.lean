/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/
import TPIL.Exam.Exam01

/-!
# Exam 2

This examination covers Chapters 5 and 6 of the text, focusing on classical logic and implicit
lambdas.

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

/-!
## Problem 2: Drinker Paradox Revisited

Use either of the two lemmas in the `Drinker` namespace, `exists_or_left` or `exists_or_right`, to
prove the theorem `Paradox.drinker` again.
-/

namespace Drinker

theorem exists_or_left {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, b ∨ p x) ↔ b ∨ (∃ x, p x) :=
  Iff.intro
    (fun ⟨w, h⟩ ↦ h.elim Or.inl (fun hp ↦ Or.inr ⟨w, hp⟩))
    (fun h ↦ h.elim
      (fun hb ↦ ⟨a, Or.inl hb⟩)
      (fun ⟨w, hp⟩ ↦ ⟨w, Or.inr hp⟩))

theorem exists_or_right {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, p x ∨ b) ↔ (∃ x, p x) ∨ b :=
  Iff.intro
    (fun ⟨w, h⟩ ↦ h.elim (fun hp ↦ Or.inl ⟨w, hp⟩) Or.inr)
    (fun h ↦ h.elim
      (fun ⟨w, hp⟩ ↦ ⟨w, Or.inl hp⟩)
      (fun hb ↦ ⟨a, Or.inr hb⟩))

end Drinker

section

variable {Pub : Type} [Drinker Pub]

open Drinker Classical

/-- There is someone in the pub such that, if the person is drinking, then everyone in the pub is
drinking. -/
theorem Paradox.drinker' (someone : Pub) :
    ∃ (x : Pub), IsDrinking x → ∀ (y : Pub), IsDrinking y := by
  simp only [Decidable.imp_iff_not_or]
  show ∃ x, ¬IsDrinking x ∨ ∀ (y : Pub), IsDrinking y
  sorry
  /- uncomment the following lines:
  show (∃ x, ¬IsDrinking x) ∨ ∀ y, IsDrinking y
  rw [← not_forall]
  show (¬∀ x, IsDrinking x) ∨ ∀ y, IsDrinking y
  apply Decidable.not_or_self
  -/

end
