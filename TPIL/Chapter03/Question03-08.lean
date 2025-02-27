/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 3 Quiz

## Question 3
-/

example {p q : Prop} (hp : p) (hpq : p → q) : q :=
  hpq hp

/-!
## Question 4
-/

example {α : Sort u} {β : Sort v} (a : α) (f : α → β) : β :=
  f a

/-!
## Question 5
-/

example {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  And.intro hp hq

example {p q : Prop} (h : p ∧ q) : p :=
  And.left h

example {p q : Prop} (h : p ∧ q) : q :=
  And.right h

/-!
## Question 6
-/

example {α : Sort u} {β : Sort v} (a : α) (b : β) : α ×' β :=
  PProd.mk a b

example {α : Sort u} {β : Sort v} (p : α ×' β) : α :=
  PProd.fst p

example {α : Sort u} {β : Sort v} (p : α ×' β) : β :=
  PProd.snd p

/-!
## Question 7
-/

example {p q : Prop} (hp : p) : p ∨ q :=
  Or.inl hp

example {p q : Prop} (hq : q) : p ∨ q :=
  Or.inr hq

example {p q r : Prop} (h : p ∨ q) (left : p → r) (right : q → r) : r :=
  Or.elim h left right

/-!
## Question 8
-/

example {α : Sort u} {β : Sort v} (a : α) : α ⊕' β :=
  PSum.inl a

example {α : Sort u} {β : Sort v} (b : β) : α ⊕' β :=
  PSum.inr b

example {α : Sort u} {β : Sort v} {γ : Sort w} (s : α ⊕' β) (f : α → γ) (g : β → γ) : γ :=
  match s with
  | .inl a => f a
  | .inr b => g b
