/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 2 Quiz

## Question 19

Only `f` and `g` are alpha-equivalent.
-/

namespace Question19

def a (n : Nat) := n ^ 2 + 1

def f (a : Nat → Nat) (n : Nat) := a (a n)
def g (b : Nat → Nat) (n : Nat) := b (b n)
def h (a : Nat → Nat) (n : Nat) := Question19.a (a n)

#eval f (fun n : Nat ↦ n) 0 -- output: 0
#eval h (fun n : Nat ↦ n) 0 -- 1

end Question19

/-!
## Question 20
-/

namespace Question20

def Nat.min (n m : Nat) := if n ≤ m then n else m

end Question20
