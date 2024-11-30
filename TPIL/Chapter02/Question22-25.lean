/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 2 Quiz

## Question 22
-/

namespace Question22

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

/-
def Question22.compose : (α β γ : Type) → (β → γ) → (α → β) → α → γ :=
fun α β γ g f x ↦ g (f x)
-/
#print compose

/-
def Question22.doTwice : (α : Type) → (α → α) → α → α :=
fun α h x ↦ h (h x)
-/
#print doTwice

/-
def Question22.doThrice : (α : Type) → (α → α) → α → α :=
fun α h x ↦ h (h (h x))
-/
#print doThrice

end Question22

/-!
## Question 23
-/

namespace Question23

section

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)

end

#eval List.tail [0, 1, 2, 3] -- output: [1, 2, 3]
#eval List.reverse [1, 2, 3] -- [3, 2, 1]
#eval compose (List Nat) (List Nat) (List Nat) List.reverse List.tail [0, 1, 2, 3] -- [3, 2, 1]

end Question23

/-!
## Question 24
-/

#eval  List.cons 0 [1, 2, 3] -- output: [0, 1, 2, 3]
#check List.cons 0 [1, 2, 3] -- List Nat

#eval  List.cons true [] -- [true]
#check List.cons true [] -- List Bool

#eval  List.cons "Lean" ["4"] -- ["Lean", "4"]
#check List.cons "Lean" ["4"] -- List String

/-!
## Question 25

The statements (a)-(d) are all true.
-/

#print List.cons -- output: constructor List.cons.{u} : {α : Type u} → α → List α → List α
