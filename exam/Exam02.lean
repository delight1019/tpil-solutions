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
      let hp : Prop := True
      absurd (@h hp) (@h ¬hp)
    )

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
