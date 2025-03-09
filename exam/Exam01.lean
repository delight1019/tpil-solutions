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

example {α : Sort u} {β : Sort v} {φ : α → β → Sort w} (f : (x : α) → (y : β) → φ x y) : (y : β) → (x : α) → φ x y :=
  fun hy : β => fun hx : α => f hx hy

example {α : Type u} {β : Type v} (p : α × β) : β × α :=
  ⟨p.snd, p.fst⟩

/-!
## Problem 2

Prove the following examples:
-/

example : True ↔ ∀ (p : Prop), p → p :=
  Iff.intro
    (fun _ : True => show ∀ (p : Prop), p → p from
      fun _ =>
      fun hp => hp
    )
    (fun _ => True.intro)

example : False ↔ ∀ (p : Prop), p :=
  Iff.intro
    (fun h: False => False.elim h)
    (fun h : ∀ (p : Prop), p => show False from
      let hp : Prop := True
      absurd (h hp) (h ¬hp)
    )

example {p q : Prop} : p ∧ q ↔ ∀ (r : Prop), (p → q → r) → r :=
  Iff.intro
    (fun h : p ∧ q => show ∀ (r : Prop), (p → q → r) → r from
      fun hr =>
      fun hpqr : p → q → hr =>
      hpqr h.left h.right
    )
    (fun h : ∀ (r : Prop), (p → q → r) → r => show p ∧ q from
      have hp : p :=
        h p (fun p => fun _ => p) /- ? -/
      have hq : q :=
        h q (fun _ => fun q => q)
      ⟨hp, hq⟩
    )

example {p q : Prop} : p ∨ q ↔ ∀ (r : Prop), (p → r) → (q → r) → r :=
  Iff.intro
    (fun h : p ∨ q => show ∀ (r : Prop), (p → r) → (q → r) → r from
      fun hr =>
      fun hpr : p → hr =>
      fun hqr : q → hr =>
      h.elim
        (fun hp : p => hpr hp)
        (fun hq : q => hqr hq)
    )
    (fun h : ∀ (r : Prop), (p → r) → (q → r) → r => show p ∨ q from
      Classical.byCases
        (fun hp : p => Or.inl hp)
        (fun hnp : ¬p =>
          have hq : q :=
            h q (fun p => q) (fun q => q)
          Or.inr hq
        )
    )

example {α : Sort u} {p : α → Prop} : (∃ (x : α), p x) ↔ ∀ (r : Prop), (∀ (w : α), p w → r) → r :=
  Iff.intro
    (fun h  : ∃ (x : α), p x => show ∀ (r : Prop), (∀ (w : α), p w → r) → r from
      fun hr =>
      fun h1 : ∀ (w : α), p w → hr => show hr from
        h.elim
          (fun w =>
           fun hpw : p w =>
           h1 w hpw
          )
    )
    (fun h : ∀ (r : Prop), (∀ (w : α), p w → r) → r => show ∃ (x : α), p x from
      sorry
    )

/-!
## Problem 3

Prove the following examples:
-/

example {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, b ∨ p x) ↔ b ∨ (∃ x, p x) :=
  Iff.intro
    (fun h : ∃ x, b ∨ p x => show b ∨ (∃ x, p x) from
      Exists.elim h
        (fun w =>
         fun h1 : b ∨ p w =>
         Or.elim h1
          (fun hb : b => Or.inl hb)
          (fun hpw : p w => Or.inr ⟨w, hpw⟩)
        )
    )
    (fun  h : b ∨ (∃ x, p x) => show (∃ x, b ∨ p x) from
      Or.elim h
        (fun hb : b => ⟨a, Or.inl hb⟩)
        (fun hpx : ∃ x, p x =>
          Exists.elim hpx
            (fun w =>
             fun hpw : p w =>
             ⟨w, Or.inr hpw⟩
            )
        )
    )

example {α : Sort u} {p : α → Prop} {b : Prop} (a : α) :
    (∃ x, p x ∨ b) ↔ (∃ x, p x) ∨ b :=
  Iff.intro
    (fun h : ∃ x, p x ∨ b => show (∃ x, p x) ∨ b from
      Exists.elim h
        (fun w =>
         fun h1 : p w ∨ b =>
         Or.elim h1
          (fun hpw : p w => Or.inl ⟨w, hpw⟩)
          (fun hb : b => Or.inr hb)
        )
    )
    (fun h : (∃ x, p x) ∨ b => show (∃ x, p x ∨ b) from
      Or.elim h
        (fun h1 : ∃ x, p x =>
          Exists.elim h1
            (fun w =>
             fun hpw : p w => ⟨w, Or.inl hpw⟩
            )
        )
        (fun hb : b => ⟨a, Or.inr hb⟩)
    )
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
  fun nCon : ∃ (x : Human), IsBarber x => show False from
    Exists.elim nCon
      (fun w =>
       fun barberW : IsBarber w =>
       let wsw := w shaves w
       have h1 : wsw → ¬wsw := (barberW w).mp
       have h2 : ¬wsw → wsw := (barberW w).mpr
       have hnwsw : ¬wsw := fun hwsw : wsw => h1 hwsw hwsw
       have hwsw : wsw := h2 hnwsw
       show False from hnwsw hwsw
      )
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
  h₁.elim
    (fun hspr =>
     fun hsprPierceShd : ∀ (shd : Shield), hspr can_pierce shd =>
     h₂.elim
      (fun hshd =>
       fun hnsprPierceShd : ∀ (spr : Spear), ¬spr can_pierce hshd => show False from
       have hsps : hspr can_pierce hshd := hsprPierceShd hshd
       have hnsps : ¬hspr can_pierce hshd := hnsprPierceShd hspr
       show False from hnsps hsps
      )
    )

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

-- HINT: use theorems `byCases` and `not_forall`
theorem Paradox.drinker (someone : Pub) : ∃ (x : Pub), IsDrinking x → ∀ (y : Pub), IsDrinking y :=
  byCases
    (fun allDrinking : ∀ (y : Pub), IsDrinking y =>
      ⟨someone, fun someone => allDrinking⟩
    )
    (fun nAllDrinking : ¬∀ (y : Pub), IsDrinking y =>
      ⟨someone, fun h : IsDrinking someone =>
        sorry
      ⟩
    )
end
