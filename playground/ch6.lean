section
variable (x y : Nat)

def double := x + x

#check double y

#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y

#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end


-- namespace Foo
-- def bar : Nat := 1
-- end Foo

-- open Foo

-- #check bar

-- #check Foo.bar


def String.add (a b : String) : String := a ++ b
def Bool.add (a b : Bool) : Bool := a != b
def add (α β : Type) : Type := Sum α β

open Bool
open String

-- This reference is ambiguous:
-- #check add

#check String.add
#check Bool.add
#check _root_.add

#check add "hello" "world"
#check add true false
#check add Nat Nat


protected def Foo.bar : Nat := 1

open Foo

#check Foo.bar


-- open Nat (succ zero gcd)

-- #check zero
-- #eval gcd 15 6


-- open Nat hiding succ gcd

-- #check zero
-- #eval Nat.gcd 15 6


open Nat renaming mul → times, add → plus

#eval plus (times 2 2) 3

export Nat (succ add sub)


def isPrefix (l₁ : List α)(l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

-- @[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as := ⟨[], by simp⟩

-- example : isPrefix [1, 2, 3] [1, 2, 3] := by simp

-- attribute [simp] List.isPrefix_self


-- section

-- theorem List.isPrefix_self (as : List α) : isPrefix as as := ⟨[], by simp⟩

-- attribute [local simp] List.isPrefix_self

-- example : isPrefix [1, 2, 3] [1, 2, 3] := by simp

-- end

instance : LE (List α) where le := isPrefix

theorem List.isPrefix_self (as : List α) : as ≤ as := ⟨[], by simp⟩
