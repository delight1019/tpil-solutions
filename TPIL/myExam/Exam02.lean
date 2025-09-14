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
    Iff.intro
    (fun _ : True => show ∀ {p : Prop}, p → p from
      @fun _ =>
      fun hp => hp
    )
    (fun _ => True.intro)

example : False ↔ ∀ {p : Prop}, p :=
    Iff.intro
    (fun h : False => False.elim h)
    (fun h : ∀ {p : Prop}, p => show False from
      absurd (@h True) (@h ¬True)
    )

-- alternative proof
example : False ↔ ∀ {p : Prop}, p :=
  Iff.intro
    (fun h : False => False.elim h)
    (fun h : ∀ {p : Prop}, p => show False from h)

example {p q : Prop} : p ∧ q ↔ ∀ {r : Prop}, (p → q → r) → r :=
    Iff.intro
    (fun h : p ∧ q => show ∀ {r : Prop}, (p → q → r) → r from
      @fun r =>
      fun hpqr : p → q → r =>
      hpqr h.left h.right
    )
    (fun h : ∀ {r : Prop}, (p → q → r) → r => show p ∧ q from
      have hp : p :=
        @h p (fun hp2 => fun _ => show p from hp2)
      have hq : q :=
        @h q (fun _ => fun hq2 => show q from hq2)
      ⟨hp, hq⟩
    )

example {p q : Prop} : p ∨ q ↔ ∀ {r : Prop}, (p → r) → (q → r) → r :=
  Iff.intro
    (fun h : p ∨ q => show ∀ {r : Prop}, (p → r) → (q → r) → r from
      @fun r =>
      fun hpr : p → r =>
      fun hqr : q → r =>
      h.elim
        (fun hp : p => hpr hp)
        (fun hq : q => hqr hq)
    )
    (fun h : ∀ {r : Prop}, (p → r) → (q → r) → r => show p ∨ q from
      have hpq := @h (p ∨ q)
      hpq (fun hp => show p ∨ q from Or.inl hp)
          (fun hq => show p ∨ q from Or.inr hq)
    )

example {α : Sort u} {p : α → Prop} : (∃ (x : α), p x) ↔ ∀ {r : Prop}, (∀ (w : α), p w → r) → r :=
  Iff.intro
    (fun h : ∃ (x : α), p x => show ∀ {r : Prop}, (∀ (w : α), p w → r) → r from
      @fun r =>
      fun h1 : ∀ (w : α), p w → r =>
      h.elim
        (fun w =>
         fun hpw : p w =>
         h1 w hpw
        )
    )
    (fun h : ∀ {r : Prop}, (∀ (w : α), p w → r) → r => show ∃ (x : α), p x from
      have con := @h (∃ x, p x)
      con (fun w hpw => ⟨w, hpw⟩)
    )

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
  rw [exists_or_right someone]
  show (∃ x, ¬IsDrinking x) ∨ ∀ y, IsDrinking y
  rw [← not_forall]
  show (¬∀ x, IsDrinking x) ∨ ∀ y, IsDrinking y
  apply Decidable.not_or_self

end
