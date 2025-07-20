/-
This work is waived of all rights, including copyright, according to the CC0 Public Domain
Dedication. See the LICENSE-CC0 file or https://creativecommons.org/publicdomain/zero/1.0/.
-/

/-!
# Chapter 4

## Predicates
-/

/-- A class for explaining the notion of a unary predicate. -/
class Invincible (Being : Type) where
  bulhwi : Being
  mark   : Being
  IsInvincible : Being → Prop
  not_bulhwi_isInvincible : ¬IsInvincible bulhwi
  mark_isInvincible : IsInvincible mark

namespace Invincible

variable {Being : Type} [Invincible Being]

-- Bulhwi and Mark are beings.
#check (bulhwi : Being)
#check (mark : Being)

-- `IsInvincible` is a unary predicate.
#check (IsInvincible : Being → Prop)

-- `IsInvincible bulhwi` is a proposition.
#check IsInvincible (bulhwi : Being)

-- `IsInvincible mark` is a proposition.
#check IsInvincible (mark : Being)

-- Bulhwi isn't invincible.
example : ¬IsInvincible (bulhwi : Being) :=
  not_bulhwi_isInvincible

-- Mark is invincible.
example : IsInvincible (mark : Being) :=
  mark_isInvincible

end Invincible

/-!
## Relations
-/

/-- A class for explaining the notion of a binary relation. -/
class HighSchool (Being : Type) where
  jentry  : Being
  michael : Being
  kit   : Being
  Likes : Being → Being → Prop
  michael_likes_jentry : Likes michael jentry
  jentry_likes_kit : Likes jentry kit

namespace HighSchool

variable {Being : Type} [HighSchool Being]

-- Jentry, Michael, and Kit are beings.
#check (jentry  : Being)
#check (michael : Being)
#check (kit : Being)

-- `Likes` is a binary relation on `Being`.
#check (Likes : Being → Being → Prop)

-- `Likes michael jentry` is a proposition.
#check Likes michael (jentry : Being)

-- `Likes jentry kit` is a proposition.
#check Likes jentry (kit : Being)

-- Michael likes Jentry.
example : Likes michael (jentry : Being) :=
  michael_likes_jentry

-- Jentry likes Kit.
example : Likes jentry (kit : Being) :=
  jentry_likes_kit

end HighSchool
