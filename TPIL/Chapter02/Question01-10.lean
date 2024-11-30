/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 2 Quiz

## Question 1
-/

#check -2        -- output: Int
#check 3.14      -- Float
#check 'L'       -- Char
#check "Lean"    -- String
#check [0, 1, 2] -- List Nat
#check 1 + 1 = 2 -- Prop

/-!
## Question 2
-/

#eval -3 / 5               -- output: -1
#eval Float.sin 0.0        -- 0.000000
#eval Char.toNat 'L'       -- 76
#eval String.length "Lean" -- 4
#eval List.tail [0, 1, 2]  -- [1, 2]
#eval 1.0 + 1.0 == 2.0     -- true

/-!
## Question 3
-/

namespace Question03

def f (x : Nat) := 2 * x - 1
#eval f 1

end Question03

/-!
## Questions 4-5
-/

def q04a : Bool → Bool := fun b : Bool ↦ b
def q04b : (Bool → Bool) → Bool := fun f : Bool → Bool ↦ f true
def q04c : Bool → (Bool → Bool) := fun b1 : Bool ↦ (fun b2 : Bool ↦ b1 && !b2)
def q04d : Bool → Bool → Bool := q04c

def q05a : Bool × Bool := (true, false)
def q05b : (Bool × Bool) × Bool := ((false, true), false)
def q05c : Bool × (Bool × Bool) := (true, (false, false))
def q05d : Bool × Bool × Bool := q05c

/-!
## Question 6
-/

#eval Nat.succ 0  -- output: 1
#eval Nat.add 3 7 -- 10
#eval ('L', 4).1  -- 'L'
#eval ('L', 4).2  -- 4

/-!
## Question 7
-/

#check Bool → Bool -- output: Type
#check Bool × Bool -- Type

/-!
## Question 8
-/

def Type.id : Type → Type := fun x : Type ↦ x

#check Type.id Nat -- output: Type

/-!
## Question 9
-/

def q09a : Prod (Type 0) (Type 1) := (List Char × Prop, Type → Nat)
def q09b : Type 2 → Type 3 := fun α : Type 2 ↦ (α → Type 2)

/-!
## Question 10
-/

def q10a.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  fun α : Type u ↦ (fun β : Type v ↦ (fun γ : Type w ↦ α → β → γ))

def q10b.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  fun α : Type u ↦ (fun β : Type v ↦ (fun γ : Type w ↦ α × β × γ))
