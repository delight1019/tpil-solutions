/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Exam 1

This examination covers Chapters 2 to 4 of the text, focusing on proving universal and existential
statements.

## Problem 1

Give an example of a term of each type listed below.
-/

universe u v w

example {α : Sort u} {β : Sort v} {φ : α → β → Sort w} (f : (x : α) → (y : β) → φ x y) :
    (y : β) → (x : α) → φ x y :=
  sorry

example {α : Type u} {β : Type v} (p : α × β) : β × α :=
  sorry

/-!
## Problem 2

Prove the following examples:
-/

example : True ↔ ∀ (p : Prop), p → p :=
  sorry

example : False ↔ ∀ (p : Prop), p :=
  sorry

example {p q : Prop} : p ∧ q ↔ ∀ (r : Prop), (p → q → r) → r :=
  sorry

example {p q : Prop} : p ∨ q ↔ ∀ (r : Prop), (p → r) → (q → r) → r :=
  sorry

example {α : Sort u} {p : α → Prop} : (∃ (x : α), p x) ↔ ∀ (r : Prop), (∀ (w : α), p w → r) → r :=
  sorry

/-!
## Problem 3

Prove the following examples:
-/

example {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, b ∨ p x) ↔ b ∨ (∃ x, p x) :=
  sorry

example {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, p x ∨ b) ↔ (∃ x, p x) ∨ b :=
  sorry

/-!
## Problem 4: Barber Paradox

Prove the theorem `Paradox.barber` below:
-/

/-- A class for formalizing the barber paradox. -/
class Barber (Human : Type u) where
  Shaves : Human → Human → Prop

section

variable {Human : Type u} [Barber Human]

namespace Barber

infixl:55 " shaves " => Shaves

/-- The barber is the one who shaves all those, and those only, who do not shave themselves. -/
def IsBarber (x : Human) : Prop :=
  ∀ (y : Human), x shaves y ↔ ¬y shaves y

end Barber

open Barber

/-- There is no barber who shaves all those, and those only, who do not shave themselves. -/
theorem Paradox.barber : ¬∃ (x : Human), IsBarber x :=
  sorry

end

/-!
## Problem 5: Spear and Shield Paradox

Prove the theorem `Paradox.spearShield` below:
-/

/-- A class for formalizing the spear and shield paradox, which originated from a story in the
classical Chinese philosophical work known as Han Feizi (韓非子). -/
class SpearShield (Spear : Type u) (Shield : Type v) where
  CanPierce : Spear → Shield → Prop

section

infix:55 " can_pierce " => SpearShield.CanPierce

variable {Spear : Type u} {Shield : Type u} [SpearShield Spear Shield]

/-- A man trying to sell a spear and a shield claimed that his spear could pierce any shield and
then claimed that his shield could not be pierced. When asked about what would happen if he took his
spear to strike his shield, the seller could not answer. -/
theorem Paradox.spearShield
    (h₁ : ∃ (spr : Spear), ∀ (shd : Shield),  spr can_pierce shd)
    (h₂ : ∃ (shd : Shield), ∀ (spr : Spear), ¬spr can_pierce shd) : False :=
  sorry

end

/-!
## Problem 6: Drinker Paradox

Prove the theorem `Paradox.drinker` below:
-/

/-- A class for formalizing the drinker paradox. -/
class Drinker (Pub : Type) where
  IsDrinking : Pub → Prop

section

variable {Pub : Type} [Drinker Pub]

open Drinker Classical

/-- There is someone in the pub such that, if the person is drinking, then everyone in the pub is
drinking. -/
theorem Paradox.drinker (someone : Pub) : ∃ (x : Pub), IsDrinking x → ∀ (y : Pub), IsDrinking y :=
  sorry -- HINT: use theorems `byCases` and `not_forall`

end
