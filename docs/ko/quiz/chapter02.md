# 2장 퀴즈

## 문제 1

`#check` 명령어를 이용해, 아래에 나열된 식의 유형을 각각 구하라.

\(a\) `-2` \
\(b\) `3.14` \
\(c\) `'L'` \
\(d\) `"Lean"` \
\(e\) `[0, 1, 2]` \
\(f\) `1 + 1 = 2`

## 문제 2

`#eval` 명령어를 이용해, 아래에 나열된 식의 값을 각각 구하라.

\(a\) `-3 / 5` \
\(b\) `Float.sin 0.0` \
\(c\) `Char.toNat 'L'` \
\(d\) `String.length "Lean"` \
\(e\) `List.tail [0, 1, 2]` \
\(f\) `1.0 + 1.0 == 2.0`

## 문제 3

다음 코드에 오류가 있다. `#eval` 명령어 뒤의 식을 고쳐 그 값을 계산하라.

```lean
namespace Question03

def f (x : Nat) := 2 * x - 1
#eval f(1)

end Question03
```

## 문제 4

`def` 핵심어를 이용해, 아래의 유형에 속하는 새로운 상수를 각각 선언하라.

\(a\) `Bool → Bool` \
\(b\) `(Bool → Bool) → Bool` \
\(c\) `Bool → (Bool → Bool)` \
\(d\) `Bool → Bool → Bool`

## 문제 5

`def` 핵심어를 이용해, 아래의 유형에 속하는 새로운 상수를 각각 선언하라.

\(a\) `Bool × Bool` \
\(b\) `(Bool × Bool) × Bool` \
\(c\) `Bool × (Bool × Bool)` \
\(d\) `Bool × Bool × Bool`

## 문제 6

아래에 나열된 식의 값을 각각 구하라.

\(a\) `Nat.succ 0` \
\(b\) `Nat.add 3 7` \
\(c\) `('L', 4).1` \
\(d\) `('L', 4).2`

## 문제 7

아래에 나열된 식의 유형을 각각 구하라.

\(a\) `Bool → Bool` \
\(b\) `Bool × Bool`

## 문제 8

`Type`에서 `Type`으로의 함수 `Type.id`를 다음과 같이 정의하자.

```lean
def Type.id : Type → Type := fun x : Type ↦ x
```

식 `Type.id Nat`의 유형을 구하라.

## 문제 9

아래의 유형에 속하는 상수를 각각 정의하라.

\(a\) `Prod (Type 0) (Type 1)` \
\(b\) `Type 2 → Type 3`

## 문제 10

각 `sorry` 식별자를 실제 정의로 바꿔 다음의 두 세계 다형적 함수를 정의하라. 두 함수 `f`와 `g`가 정의상 같으면 안 된다.

```lean
namespace Question10

def f.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  sorry

def g.{u, v, w} : Type u → Type v → Type w → Type (max u v w) :=
  sorry

end Question10
```

## 문제 11

[문제 8](#question-8)의 함수 `Type.id`는 세계 다형적인가?

## 문제 12

[문제 9](#question-9)에서 정의된 상수들은 세계 다형적인가?

## 문제 13

식 `(λ x : Int => -x + 2) 3`의 값을 구하라.

## 문제 14

자연수를 입력값으로 받아, 그 수가 영이 아니면 `true`를 반환하고, 그 수가 영이면 `false`를 반환하는 함수를 정의하라.

## 문제 15

식 `fun x : Nat ↦ x`는 *상수* 함수인가?

## 문제 16

식 `fun x : Nat ↦ 0`은 `Nat`에 대한 *항등* 함수인가?

## 문제 17

`sorry` 식별자를 실제 식으로 바꿔 다음 함수를 정의하라. 그 식은 세 인수 `f`, `g`, `s`를 *포함해야* 한다.

```lean
def q17 (f : List Char → Nat) (g : (List Char → Nat) → (String → Nat)) (s : String) : Nat :=
  sorry
```

## 문제 18

다음 함수들은 알파 동등한가?

* `fun (s : String) (n : Nat) ↦ String.drop s n`
* `fun (bulhwi : String) (cha : Nat) ↦ String.drop bulhwi cha`

## 문제 19

다음 중 어느 함수들이 알파 동등한가?

```lean
namespace Question19

def a (n : Nat) := n ^ 2 + 1

def f (a : Nat → Nat) (n : Nat) := a (a n)
def g (b : Nat → Nat) (n : Nat) := b (b n)
def h (a : Nat → Nat) (n : Nat) := Question19.a (a n)

end Question19
```

## 문제 20

두 자연수를 입력값으로 받아, 둘 중에서 다른 것보다 작거나 그것과 같은 자연수를 반환하는 함수를 정의하라.

작거나 같음 부호 `≤`는 `\le`로 입력할 수 있음을 유념하라.

## 문제 21

왜 아래에 나온 `foo`의 정의는 유형 확인이 잘되지만, `bar`의 정의는 그렇지 않은가?

```lean
def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
```

## 문제 22

`#print` 명령어를 이용해, 다음 함수들의 정의를 확인하라.

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

## 문제 23

다음 코드에 오류가 있다. 마지막 `#eval` 명령어 뒤의 식에, 함수 `compose`의 인수 중 빠진 것을 넣어 그 식을 고쳐라.

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

## 문제 24

아래에 나열된 식의 값과 유형을 각각 구하라.

\(a\) `List.cons 0 [1, 2, 3]` \
\(b\) `List.cons true []` \
\(c\) `List.cons "Lean" ["4"]`

## 문제 25

`print` 명령어를 이용해 함수 `List.cons`의 유형을 확인하라. 그런 뒤, 이 함수에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 이 함수는 세계 다형적이다. \
\(b\) 이 함수는 매개 변수 다형적이다. \
\(c\) 이 함수는 의존 함수이다. \
\(d\) 이 함수는 의존 함수형에 속한다.

## 문제 26

[문제 8](#question-8)의 함수 `Type.id`에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 이 함수는 매개 변수 다형적이다. \
\(b\) 이 함수는 의존 함수이다. \
\(c\) 이 함수는 의존 함수형에 속한다.

## 문제 27

[문제 9](#question-9)에서 정의된 상수들에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 이 상수들 중 적어도 하나는 매개 변수 다형적이다. \
\(b\) 이 상수들 중 적어도 하나는 의존 함수이다. \
\(c\) 이 상수들 중 적어도 하나는 의존 함수형에 속한다. \
\(d\) 이 상수들 중 적어도 하나는 의존곱이다. \
\(e\) 이 상수들 중 적어도 하나는 의존곱형에 속한다.

## 문제 28

유형 `α : Type`와 `β : α → Type`가 주어져 있을 때, 유형 `(a : α) → β a`는 의존 함수형인가?

## 문제 29

유형 `α : Type`와 `β : α → Type`가 주어져 있을 때, 유형 `(a : α) × β a`는 의존곱형인가?

## 문제 30

유형 `α : Type`와 `β : α → Type`가 주어져 있을 때, 유형 `Σ (a : α), β a`는 시그마형인가?

## 문제 31

[문제 29](#question-29)와 [문제 30](#question-30)에 나온 두 유형은 서로 같은가?

## 문제 32

유형 `(α : Type) → Prop`은 의존 함수형인가?

## 문제 33

유형 `(α : Type) × Prop`은 의존곱형인가?

## 문제 34

다음 코드에 오류가 있다. 의존 함수 `f`의 정의를 고쳐라.

```lean
namespace Question34

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  (a, b)

end Question34
```

## 문제 35

다음 식의 값을 각각 구하라. 여기서 `f`는 [문제 34](#question-34)에서 정의된 함수이다.

\(a\) `(f Nat (fun _n => Int) 1 (-1)).1` \
\(b\) `(f Nat (fun _n => Int) 1 (-1)).2`

## 문제 36

아래에 나열된 식의 값과 유형을 각각 구하라.

\(a\) `@List.nil Nat` \
\(b\) `List.append [0, 1] [2, 3]`

## 문제 37

아래에 나열된 식에 있는 밑줄을 각각 적절한 유형으로 바꾼 다음, 그 식의 값을 확인하라.

\(a\) `@List.cons _ 0 [1, 2, 3]` \
\(b\) `@List.append _ [0, 1] [2, 3]` \
\(c\) `@List.cons _ "Lean" ["4"]` \
\(d\) `@List.append _ ["Lean"] ["4"]`

## 문제 38

암시적 인수를 하나 이상 받는 함수의 예를 들라.
