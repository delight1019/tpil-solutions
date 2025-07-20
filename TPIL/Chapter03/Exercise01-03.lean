/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 3 Exercises

## Exercise 1
-/

section

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q ↦ show q ∧ p from And.intro h.2 h.1)
    (fun h : q ∧ p ↦ show p ∧ q from And.intro h.2 h.1)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q ↦ show q ∨ p from
      Or.elim h
        (show p → q ∨ p from Or.inr)
        (show q → q ∨ p from Or.inl))
    (fun h : q ∨ p ↦ show p ∨ q from
      Or.elim h
        (show q → p ∨ q from Or.inr)
        (show p → p ∨ q from Or.inl))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h ↦ h.elim
      (fun hpq ↦ hpq.elim Or.inl (fun hqr ↦ Or.inr (Or.inl hqr)))
      (fun hr  ↦ Or.inr (Or.inr hr)))
    (fun h ↦ h.elim
      (fun hp  ↦ Or.inl (Or.inl hp))
      (fun hqr ↦ hqr.elim (fun hq ↦ Or.inl (Or.inr hq)) Or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h ↦ h.2.elim
      (fun hq ↦ Or.inl ⟨h.1, hq⟩)
      (fun hr ↦ Or.inr ⟨h.1, hr⟩))
    (fun h ↦ h.elim
      (fun hpq ↦ ⟨hpq.1, Or.inl hpq.2⟩)
      (fun hpr ↦ ⟨hpr.1, Or.inr hpr.2⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h ↦ h.elim
      (fun hp  ↦ ⟨Or.inl hp, Or.inl hp⟩)
      (fun hqr ↦ ⟨Or.inr hqr.1, Or.inr hqr.2⟩))
    (fun h ↦ h.1.elim
      Or.inl
      (h.2.elim
        (fun hp _  ↦ Or.inl hp)
        (fun hr hq ↦ Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨fun h hpq ↦ h hpq.1 hpq.2, fun h hp hq ↦ h ⟨hp, hq⟩⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h ↦ ⟨fun hp ↦ h (Or.inl hp), fun hq ↦ h (Or.inr hq)⟩)
    (fun h hpq ↦ hpq.elim h.1 h.2)

-- this example follows from the previous one
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h ↦ ⟨fun hp ↦ h (Or.inl hp), fun hq ↦ h (Or.inr hq)⟩)
    (fun h hpq ↦ hpq.elim h.1 h.2)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h hpq ↦ h.elim
    (fun hnp ↦ hnp hpq.1)
    (fun hnq ↦ hnq hpq.2)

example : ¬(p ∧ ¬p) :=
  fun h ↦ h.2 h.1

example : p ∧ ¬q → ¬(p → q) :=
  fun h hpq ↦ h.2 (hpq h.1)

example : ¬p → (p → q) :=
  fun hnp hp ↦ False.elim (hnp hp) -- alternative proof: absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun h hp ↦ h.elim
    (fun hnp ↦ absurd hp hnp)
    (fun hq ↦ hq) -- alternative proof: id

example : p ∨ False ↔ p :=
  ⟨fun h ↦ h.elim id False.elim, Or.inl⟩

example : p ∧ False ↔ False :=
  ⟨And.right, False.elim⟩

example : (p → q) → (¬q → ¬p) :=
  fun h hnq hp ↦ hnq (h hp)

end

/-!
## Exercise 2
-/

section

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h ↦ (em q).elim -- you can replace `(em q).elim` with `byCases`
    (fun hq  ↦ Or.inl (fun _ ↦ hq))
    (fun hnq ↦ Or.inr (fun hp ↦ (h hp).elim (fun hq ↦ absurd hq hnq) id))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h ↦ byCases
    (fun hp : p ↦
      have hnq : ¬q := fun hq ↦ h ⟨hp, hq⟩
      Or.inr hnq)
    (fun hnp : ¬p ↦ Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h ↦ byCases
    (fun hp : p ↦
      have hnq : ¬q := fun hq ↦
        have hpq : p → q := fun _ ↦ hq
        show False from h hpq
      show p ∧ ¬q from ⟨hp, hnq⟩)
    (fun hnp : ¬p ↦
      have hpq : p → q := fun hp ↦ absurd hp hnp
      show p ∧ ¬q from absurd hpq h)

example : (p → q) → (¬p ∨ q) :=
  fun h ↦ byCases
    (fun hp : p ↦ Or.inr (h hp))
    (fun hnp : ¬p ↦ Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  fun h hp ↦ byContradiction (fun hnq ↦ h hnq hp)

example : p ∨ ¬p :=
  em p

example : ((p → q) → p) → p :=
  fun h ↦ byContradiction (fun hnp ↦
    have hpq : p → q := fun hp ↦ absurd hp hnp
    hnp (h hpq))

end

/-!
## Exercise 3
-/

example (p : Prop) : ¬(p ↔ ¬p) :=
  fun h ↦
    have hnp : ¬p := fun hp ↦ h.mp hp hp
    have hp : p := h.mpr hnp
    show False from hnp hp
