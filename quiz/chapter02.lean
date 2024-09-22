namespace Question01
  /- a -/ #check -2 -- Int
  /- b -/ #check 3.14 -- Float
  /- c -/ #check 'L' -- Char
  /- d -/ #check "Lean" -- String
  /- e -/ #check [0, 1, 2] -- List Nat
  /- f -/ #check 1 + 1 = 2 -- Prop
end Question01

namespace Question02
  /- a -/ #eval -3 / 5 -- -1
  /- b -/ #eval Float.sin 0.0 -- 0.0
  /- c -/ #eval Char.toNat 'L' -- 76
  /- d -/ #eval String.length "Lean" -- 4
  /- e -/ #eval List.tail [0, 1, 2] -- [1, 2]
  /- f -/ #eval 1.0 + 1.0 == 2.0 -- true
end Question02

namespace Question03
  def f (x : Nat) := 2 * x - 1
  #eval f 1 -- 1
end Question03

namespace Question04
  def a (x : Bool) : Bool := !x
  def b (f : Bool → Bool) : Bool := true
  def c (x : Bool) : Bool → Bool := a
  def d (x : Bool) : Bool → Bool := a

  #check a
  #check b
  #check c
  #check d
end Question04

namespace Question05
  def a : Bool × Bool := (true, false)
  def b : (Bool × Bool) × Bool := ((true, false), true)
  def c : Bool × (Bool × Bool) := (true, true, true)
  def d : Bool × Bool × Bool := (true, true, true)

  #check a
  #check b
  #check c
  #check d
end Question05

namespace Question06
  /- a -/ #eval Nat.succ 0 -- 1
  /- b -/ #eval Nat.add 3 7 -- 10
  /- c -/ #eval ('L', 4).1 -- 'L'
  /- d -/ #eval ('L', 4).2 -- 4
end Question06

namespace Question07
  /- a -/ #check Bool → Bool -- Type
  /- b -/ #check Bool × Bool -- Type
end Question07

namespace Question08
  def Type.id : Type → Type := fun x : Type ↦ x
  #check Type.id Nat -- Type
end Question08

namespace Question09
  def a : Prod (Type 0) (Type 1) := (Nat, Nat → Type)
  def b (x : Type 2) : Type 3 := Nat → Type 2
end Question09

namespace Question10
  def f.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
    fun (x : Type u) => fun (y : Type v) => fun (z : Type w) => Prod (Prod x y) z

  def g.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
    fun (x : Type u) => fun (y : Type v) => fun (z : Type w) => x → (y → z)
end Question10

namespace Question11
  -- X
end Question11

namespace Question12
  -- X
end Question12

namespace Question13
  #eval (λ x : Int => -x + 2) 3 -- -1
end Question13

namespace Question14
  def f (x : Int) : Bool :=
    if x != 0 then true
    else false
end Question14

namespace Question15
  -- No, It's Identity function
end Question15

namespace Question16
  -- No, It's constant function
end Question16

namespace Question17
  def q17 (f : List Char -> Nat) (g : (List Char -> Nat) -> (String -> Nat)) (s : String) : Nat
    := (g f) s
end Question17

namespace Question18
  -- Yes, It's alpha-equivalent
end Question18

namespace Question19
  def a (n : Nat) := n ^ 2 + 1

  def f (a : Nat → Nat) (n : Nat) := a (a n)
  def g (b : Nat → Nat) (n : Nat) := b (b n)
  def h (a : Nat → Nat) (n : Nat) := Question19.a (a n)

  -- f and g are alpha-equivalent
end Question19

namespace Question20
  def f (x : Nat) (y : Nat) : Nat :=
    if x ≤ y then x
    else y

  #check f
end Question20

namespace Question21
  /-
    foo에서 a는 Nat의 abbreviation으로 선언되었기 때문에 fun x : a 구절에서 a는 Nat으로 취급되지만,
    bar에서 a는 변수이므로 fun x : a 선언에서 x의 타입이 될 수 없어 문제가 발생한다.
  -/
end Question21

namespace Question22
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))

  #print compose -- def Question22.compose : (α β γ : Type) → (β → γ) → (α → β) → α → γ := fun α β γ g f x => g (f x)
  #print doTwice -- def Question22.doTwice : (α : Type) → (α → α) → α → α := fun α h x => h (h x)
  #print doThrice -- def Question22.doThrice : (α : Type) → (α → α) → α → α := fun α h x => h (h (h x))
end Question22

namespace Question23
  section
    variable (α β γ : Type)
    variable (g : β → γ) (f : α → β) (h : α → α)
    variable (x : α)

    def compose := g (f x)
  end

  #check List.tail
  #check List.reverse

  #eval List.tail [0, 1, 2, 3]
  #eval List.reverse [1, 2, 3]
  #eval compose (List _) (List _) (List _) List.reverse List.tail [0, 1, 2, 3]
end Question23

namespace Question24
  /- a -/
  #eval List.cons 0 [1, 2, 3] -- [0, 1, 2, 3]
  #check List.cons 0 [1, 2, 3] -- List Nat

  /- b -/
  #eval List.cons true [] -- [true]
  #check List.cons true [] -- List Bool

  /- c -/
  #eval List.cons "Lean" ["4"] -- ["Lean", "4"]
  #check List.cons "Lean" ["4"] -- List String
end Question24

namespace Question25
  #print List.cons
  /- a -/ -- O
  /- b -/ -- O
  /- c -/ -- O
  /- d -/ -- O
end Question25

namespace Question26
  /- a -/ -- O
  /- b -/ -- O
  /- c -/ -- X
end Question26

namespace Question27
  /- a -/ -- O
  /- b -/ -- O
  /- c -/ -- X
  /- d -/ -- O
  /- e -/ -- X
end Question27

namespace Question28
  -- O
end Question28

namespace Question29
  -- O
end Question29

namespace Question30
  -- O
end Question30

namespace Question31
  -- Yes, It's the same
end Question31

namespace Question32
  -- X
end Question32

namespace Question33
  -- X
end Question33

namespace Question34
  universe u v

  def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × (β a) := ⟨a, b⟩
end Question34

namespace Question35
  def f := Question34.f

  /- a -/ #eval (f Nat (fun _n => Int) 1 (-1)).1 -- 1
  /- b -/ #eval (f Nat (fun _n => Int) 1 (-1)).2 -- -1
end Question35

namespace Question36
  /- a -/
  #eval @List.nil Nat -- []
  #check @List.nil Nat -- List Nat

  /- b -/
  #eval List.append [0, 1] [2, 3] -- [0, 1, 2, 3]
  #check List.append [0, 1] [2, 3] -- List Nat
end Question36

namespace Question37
  /- a -/ #eval @List.cons Nat 0 [1, 2, 3] -- [0, 1, 2, 3]
  /- b -/ #eval @List.append Nat [0, 1] [2, 3] -- [0, 1, 2, 3]
  /- c -/ #eval @List.cons String "Lean" ["4"] -- ["Lean", "4"]
  /- d -/ #eval @List.append String ["Lean"] ["4"] -- ["Lean", "4"]
end Question37

namespace Question38
  def Q38 {α : Type u} (a : α) : Prod Nat α := (0, a)
end Question38
