/-
Copyright (c) 2024 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 2 Quiz

## Questions 34-35
-/

namespace «Question34-35»

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

#eval (f Nat (fun _n => Int) 1 (-1)).1 -- output: 1
#eval (f Nat (fun _n => Int) 1 (-1)).2 -- -1

end «Question34-35»

/-!
## Question 36
-/

#eval  @List.nil Nat -- output: []
#check @List.nil Nat -- List Nat

#eval  List.append [0, 1] [2, 3] -- [0, 1, 2, 3]
#check List.append [0, 1] [2, 3] -- List Nat

/-!
## Question 37
-/

#eval @List.cons Nat 0 [1, 2, 3]     -- output: [0, 1, 2, 3]
#eval @List.append Nat [0, 1] [2, 3] -- [0, 1, 2, 3]

#eval @List.cons String "Lean" ["4"]     -- ["Lean", "4"]
#eval @List.append String ["Lean"] ["4"] -- ["Lean", "4"]

/-!
## Question 38
-/

namespace Question38

def id {α : Sort u} (a : α) := a

end Question38
