/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 4 Quiz

## Question 4
-/

section

universe u

variable {α : Sort u} {p : α → Prop} {q : Prop}

example (h : ∀ (x : α), p x) (a : α) : p a :=
  h a

example (w : α) (h : p w) : ∃ (x : α), p x :=
  Exists.intro w h

example (h₁ : ∃ (x : α), p x) (h₂ : ∀ (x : α), p x → q) : q :=
  Exists.elim h₁ h₂

end

/-!
## Question 5
-/

section

universe u v w

variable {α : Sort u} {β : α → Sort v}

example (f : (x : α) → β x) (a : α) : β a :=
  f a

example (a : α) (b : β a) : (x : α) ×' β x :=
  PSigma.mk a b

example {γ : Sort w} (p : (x : α) ×' β x) (f : (x : α) → β x → γ) : γ :=
  match p with
  | .mk a b => f a b

end
