/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 2 Quiz

## Question 17
-/

def q17 (f : List Char → Nat) (g : (List Char → Nat) → (String → Nat)) (s : String) : Nat :=
  (g f) s
