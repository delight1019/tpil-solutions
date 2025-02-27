/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 4

## Universal and Existential Quantifiers
-/

/-- A class for explaining the introduction and elimination rules for universal and existential
quantifiers. -/
class Mortal (Human : Type) where
  bulhwi : Human
  IsMortal : Human → Prop
  IsGodlike : Human → Prop
  forall_isMortal (x : Human) : IsMortal x
  not_isMortal_of_isGodlike {x : Human} (h : IsGodlike x) : ¬IsMortal x

namespace Mortal

variable {Human : Type} [Mortal Human]

-- Every human is mortal.
#check (forall_isMortal : ∀ (x : Human), IsMortal x)

/-- Bulhwi is Mortal. -/
theorem isMortal_bulhwi : IsMortal (bulhwi : Human) :=
  forall_isMortal bulhwi

/-- There exists a human who is mortal. -/
theorem exists_isMortal : ∃ (x : Human), IsMortal x :=
  Exists.intro bulhwi isMortal_bulhwi -- Bulhwi is a human and he is mortal.

/-- There is no human who is godlike. -/
theorem not_exists_isGodlike : ¬∃ (x : Human), IsGodlike x :=
  fun h : ∃ (x : Human), IsGodlike x ↦
    h.elim (fun (w : Human) (hw : IsGodlike w) ↦ show False from
      (show ¬IsMortal w from not_isMortal_of_isGodlike hw)
        (show IsMortal w from forall_isMortal w))

/-- Every human is not godlike. -/
theorem not_isGodlike (x : Human) : ¬IsGodlike x :=
  fun h : IsGodlike x ↦ show False from
    (show ¬∃ (x : Human), IsGodlike x from not_exists_isGodlike)
      (show ∃ (x : Human), IsGodlike x from ⟨x, h⟩)

end Mortal
