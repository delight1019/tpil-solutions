/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 3 Quiz

## Question 10
-/

example {p : Prop} (h : ¬p) : p → False :=
  h

example {p : Prop} (h : p → False) : ¬p :=
  h

example {p : Prop} (hp : p) (hnp : ¬p) : False :=
  hnp hp

example {p : Prop} (h : False) : p :=
  False.elim h

example {p q : Prop} (hp : p) (hnp : ¬p) : q :=
  False.elim (hnp hp) -- alternative proof: absurd hp hnp

/-!
## Question 11
-/

example {α : Sort u} (x : Empty) : α :=
  Empty.elim x

/-!
## Question 12
-/

example {p q : Prop} (mp : p → q) (mpr : q → p) : p ↔ q :=
  Iff.intro mp mpr

example {p q : Prop} (h : p ↔ q) : p → q :=
  Iff.mp h

example {p q : Prop} (h : p ↔ q) : q → p :=
  Iff.mpr h

/-!
## Question 13
-/

example {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) : (α → β) ×' (β → α) :=
  PProd.mk f g

example {α : Sort u} {β : Sort v} (p : (α → β) ×' (β → α)) : α → β :=
  PProd.fst p

example {α : Sort u} {β : Sort v} (p : (α → β) ×' (β → α)) : β → α :=
  PProd.snd p

/-!
## Question 14
-/

namespace Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  byCases
    (fun hp : p ↦ hp)
    (fun hnp : ¬p ↦ absurd hnp h)

theorem em_of_dne {p : Prop} : p ∨ ¬p :=
  dne (show ¬¬(p ∨ ¬p) from
    fun h : ¬(p ∨ ¬p) ↦
      have hnp : ¬p := fun hp : p ↦ show False from
        h (show p ∨ ¬p from Or.inl hp)
      have hnnp : ¬¬p := fun hnp : ¬p ↦ show False from
        h (show p ∨ ¬p from Or.inr hnp)
      show False from hnnp hnp)

end Classical

/-- See this proof after reading Chapter 4 of TPIL. -/
theorem em_of_dne (dne : ∀ {p : Prop}, ¬¬p → p) : ∀ {p : Prop}, p ∨ ¬p :=
  fun {p : Prop} ↦ dne (show ¬¬(p ∨ ¬p) from
    fun h : ¬(p ∨ ¬p) ↦
      have hnp : ¬p := fun hp : p ↦ show False from
        h (show p ∨ ¬p from Or.inl hp)
      have hnnp : ¬¬p := fun hnp : ¬p ↦ show False from
        h (show p ∨ ¬p from Or.inr hnp)
      show False from hnnp hnp)
