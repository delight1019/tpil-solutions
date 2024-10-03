# Chapter 2 Quiz

## Question 1

Use the `#check` command to give the type of each expression listed below.

\(a\) `-2` \
\(b\) `3.14` \
\(c\) `'L'` \
\(d\) `"Lean"` \
\(e\) `[0, 1, 2]` \
\(f\) `1 + 1 = 2`

## Question 2

Use the `#eval` command to give the value of each expression listed below.

\(a\) `-3 / 5` \
\(b\) `Float.sin 0.0` \
\(c\) `Char.toNat 'L'` \
\(d\) `String.length "Lean"` \
\(e\) `List.tail [0, 1, 2]` \
\(f\) `1.0 + 1.0 == 2.0`

## Question 3

There's an error in the following code. Fix the expression after the `#eval`
command to evaluate it.

```lean
namespace Question03

def f (x : Nat) := 2 * x - 1
#eval f(1)

end Question03
```

## Question 4

Use the `def` keyword to declare a new constant of each type listed below.

\(a\) `Bool → Bool` \
\(b\) `(Bool → Bool) → Bool` \
\(c\) `Bool → (Bool → Bool)` \
\(d\) `Bool → Bool → Bool`

## Question 5

Use the `def` keyword to declare a new constant of each type listed below.

\(a\) `Bool × Bool` \
\(b\) `(Bool × Bool) × Bool` \
\(c\) `Bool × (Bool × Bool)` \
\(d\) `Bool × Bool × Bool`

## Question 6

Give the value of each expression listed below.

\(a\) `Nat.succ 0` \
\(b\) `Nat.add 3 7` \
\(c\) `('L', 4).1` \
\(d\) `('L', 4).2`

## Question 7

Give the type of each expression listed below.

\(a\) `Bool → Bool` \
\(b\) `Bool × Bool`

## Question 8

Let `Type.id` be a function from `Type` to `Type` defined as follows:

```lean
def Type.id : Type → Type := fun x : Type ↦ x
```

Give the type of the expression `Type.id Nat`.

## Question 9

Define a constant of each type listed below.

\(a\) `Prod (Type 0) (Type 1)` \
\(b\) `Type 2 → Type 3`

## Question 10

Define the following two universe-polymorphic functions, replacing each `sorry`
identifier with an actual definition. The functions `f` and `g` shouldn't be
definitionally equal.

```lean
namespace Question10

def f.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  sorry

def g.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  sorry

end Question10
```

## Question 11

Is the function `Type.id` of [Question 8](#question-8) universe-polymorphic?

## Question 12

Are the constants you defined in [Question 9](#question-9) universe-polymorphic?

## Question 13

Give the value of the expression `(λ x : Int => -x + 2) 3`.

## Question 14

Define a function that takes a natural number as input and returns `true` if the
number is non-zero and `false` if the number is zero.

## Question 15

Is the expression `fun x : Nat ↦ x` a *constant* function?

## Question 16

Is the expression `fun x : Nat ↦ 0` the *identity* function on `Nat`?

## Question 17

Define the following function, replacing the `sorry` identifier with an actual
expression *containing* the arguments `f`, `g`, and `s`.

```lean
def q17 (f : List Char → Nat) (g : (List Char → Nat) → (String → Nat)) (s : String) : Nat :=
  sorry
```

## Question 18

Are the following functions alpha-equivalent?

* `fun (s : String) (n : Nat) ↦ String.drop s n`
* `fun (bulhwi : String) (cha : Nat) ↦ String.drop bulhwi cha`

## Question 19

Which of the following functions are alpha-equivalent?

```lean
namespace Question19

def a (n : Nat) := n ^ 2 + 1

def f (a : Nat → Nat) (n : Nat) := a (a n)
def g (b : Nat → Nat) (n : Nat) := b (b n)
def h (a : Nat → Nat) (n : Nat) := Question19.a (a n)

end Question19
```

## Question 20

Define a function that takes two natural numbers as input arguments and returns
the one less than or equal to the other.

Note that you can type the less-than-or-equal-to sign `≤` with `\le`.

## Question 21

Why does the definition of `foo` below type check, but the definition of `bar`
doesn't?

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```

## Question 22

Use the `#print` command to check each definition of the following functions:

```lean
namespace Question22

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

end Question22
```

## Question 23

There's an error in the following code. Fix the expression after the last
`#eval` command by providing the missing arguments to the function `compose`.

```lean
namespace Question23

section

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)

end

#eval List.tail [0, 1, 2, 3] -- output: [1, 2, 3]
#eval List.reverse [1, 2, 3] -- [3, 2, 1]
#eval compose List.reverse List.tail [0, 1, 2, 3]

end Question23
```

## Question 24

Give the value and type of each expression listed below.

\(a\) `List.cons 0 [1, 2, 3]` \
\(b\) `List.cons true []` \
\(c\) `List.cons "Lean" ["4"]`

## Question 25

Use the `print` command to check the type of the function `List.cons`, then
answer by true or false each of the following statements about the function.

\(a\) It is universe-polymorphic. \
\(b\) It is parametrically polymorphic. \
\(c\) It is a dependent function. \
\(d\) It has a dependent function type.

## Question 26

Answer by true or false each of the following statements about the function
`Type.id` of [Question 8](#question-8).

\(a\) It is parametrically polymorphic. \
\(b\) It is a dependent function. \
\(c\) It has a dependent function type.

## Question 27

Answer by true or false each of the following statements about the constants you
defined in [Question 9](#question-9).

\(a\) At least one of them is parametrically polymorphic. \
\(b\) At least one of them is a dependent function. \
\(c\) At least one of them has a dependent function type. \
\(d\) At least one of them is a dependent product. \
\(e\) At least one of them has a dependent product type.

## Question 28

Given `α : Type` and `β : α → Type`, is the type `(a : α) → β a` a dependent
function type?

## Question 29

Given `α : Type` and `β : α → Type`, is the type `(a : α) × β a` a dependent
product type?

## Question 30

Given `α : Type` and `β : α → Type`, is the type `Σ (a : α), β a` a sigma type?

## Question 31

Are the types of [Question 29](#question-29) and [Question 30](#question-30) the
same?

## Question 32

Is the type `(α : Type) → Prop` a dependent function type?

## Question 33

Is the type `(α : Type) × Prop` a dependent product type?

## Question 34

There's an error in the following code. Fix the definition of the dependent
function `f`.

```lean
namespace Question34

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  (a, b)

end Question34
```

## Question 35

Give the value of each of the following expressions, where `f` is the function
defined in [Question 34](#question-34).

\(a\) `(f Nat (fun _n => Int) 1 (-1)).1` \
\(b\) `(f Nat (fun _n => Int) 1 (-1)).2`

## Question 36

Give the value and type of each expression listed below.

\(a\) `@List.nil Nat` \
\(b\) `List.append [0, 1] [2, 3]`

## Question 37

Replace the underscore in each expression listed below with an appropriate type,
then check the value of each expression.

\(a\) `@List.cons _ 0 [1, 2, 3]` \
\(b\) `@List.append _ [0, 1] [2, 3]` \
\(c\) `@List.cons _ "Lean" ["4"]` \
\(d\) `@List.append _ ["Lean"] ["4"]`

## Question 38

Give an example of a function that takes one or more implicit arguments.
