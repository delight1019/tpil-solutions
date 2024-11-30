/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 2 Quiz

## Question 13
-/

#eval (λ x : Int => -x + 2) 3 -- output: -1

/-!
## Question 14
-/

def Nat.toBool (n : Nat) : Bool := if n = 0 then false else true

#eval Nat.toBool 0 -- output: false
#eval Nat.toBool 1 -- true
#eval Nat.toBool 2 -- true
