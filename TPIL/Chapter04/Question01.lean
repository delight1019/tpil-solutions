/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 4 Quiz

## Question 1
-/

namespace Question01

universe u

variable {α : Sort u}

def p (x : α) : Prop := ∀ (q : α → Prop), ¬q x

theorem forall_not_p (x : α) : ¬p x :=
  fun (hp : p x) ↦ show False from hp p hp

/-- alternative proof of theorem `forall_not_p` -/
example (x : α) : ¬p x :=
  fun (hp : p x) ↦ hp (fun _ ↦ True) True.intro

end Question01
