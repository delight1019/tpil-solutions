# 3장 퀴즈

## 문제 1

두 항 `p : Prop`와 `t : p`에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 항 `p`는 유형이다. \
\(b\) 항 `p`는 참인 명제이다. \
\(c\) 항 `t`는 어떤 명제의 증명이다.

## 문제 2

두 항 `p q : Prop`와 `t : p → q`에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 유형 `p → q`는 함수형이다. \
\(b\) 유형 `p → q`는 함의이다. \
\(c\) 항 `t`는 `p`에서 `q`로의 함수이다. \
\(d\) 항 `t`는 명제 `p → q`의 증명이다.

## 문제 3

다음 보기를 증명하라.

```lean
example {p q : Prop} (hp : p) (hpq : p → q) : q :=
  sorry
```

## 문제 4

다음 유형에 속하는 항의 보기를 들어라.

```lean
example {α : Sort u} {β : Sort v} (a : α) (f : α → β) : β :=
  sorry
```

## 문제 5

다음 보기를 증명하라.

```lean
example {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  sorry

example {p q : Prop} (h : p ∧ q) : p :=
  sorry

example {p q : Prop} (h : p ∧ q) : q :=
  sorry
```

## 문제 6

아래에 나열된 유형에 속하는 항의 보기를 각각 들어라.

다형적 곱유형 `PProd`에 관한 정보는 다음 문서에서 확인할 수 있다. <https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#PProd>

`PProd.mk`가 `PProd`의 구성자의 이름임을 유념하라.

```lean
example {α : Sort u} {β : Sort v} (a : α) (b : β) : α ×' β :=
  sorry

example {α : Sort u} {β : Sort v} (p : α ×' β) : α :=
  sorry

example {α : Sort u} {β : Sort v} (p : α ×' β) : β :=
  sorry
```

## 문제 7

다음 보기를 증명하라.

```lean
example {p q : Prop} (hp : p) : p ∨ q :=
  sorry

example {p q : Prop} (hq : q) : p ∨ q :=
  sorry

example {p q r : Prop} (h : p ∨ q) (left : p → r) (right : q → r) : r :=
  sorry
```

## 문제 8

아래에 나열된 유형에 속하는 항의 보기를 각각 들어라.

다형적 합유형 `PSum`에 관한 정보는 다음 문서에서 확인할 수 있다. <https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#PSum>

```lean
example {α : Sort u} {β : Sort v} (a : α) : α ⊕' β :=
  sorry

example {α : Sort u} {β : Sort v} (b : β) : α ⊕' β :=
  sorry

example {α : Sort u} {β : Sort v} {γ : Sort w} (s : α ⊕' β) (f : α → γ) (g : β → γ) : γ :=
  match s with
  | .inl a => sorry
  | .inr b => sorry
```

## 문제 9

두 항 `p : Prop`와 `t : ¬p`에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 명제 `¬p`은 `p → False`와 정의상 같다. \
\(b\) 항 `t`는 `p`에서 `False`로의 함수이다. \
\(c\) 항 `t`는 `p`의 부정 `¬p`의 증명이다.

## 문제 10

다음 보기를 증명하라.

```lean
example {p : Prop} (h : ¬p) : p → False :=
  sorry

example {p : Prop} (h : p → False) : ¬p :=
  sorry

example {p : Prop} (hp : p) (hnp : ¬p) : False :=
  sorry

example {p : Prop} (h : False) : p :=
  sorry

example {p q : Prop} (hp : p) (hnp : ¬p) : q :=
  sorry
```

## 문제 11

`Empty.elim`를 이용해, 다음 유형에 속하는 항의 보기를 들어라.

`Empty.elim`에 관한 정보는 다음 문서에서 확인할 수 있다. <https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Empty.elim>

```lean
example {α : Sort u} (x : Empty) : α :=
  sorry
```

## 문제 12

다음 보기를 증명하라.

```lean
example {p q : Prop} (mp : p → q) (mpr : q → p) : p ↔ q :=
  sorry

example {p q : Prop} (h : p ↔ q) : p → q :=
  sorry

example {p q : Prop} (h : p ↔ q) : q → p :=
  sorry
```

## 문제 13

아래에 나열된 유형에 속하는 항의 보기를 각각 들어라.

```lean
example {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) : (α → β) ×' (β → α) :=
  sorry

example {α : Sort u} {β : Sort v} (p : (α → β) ×' (β → α)) : α → β :=
  sorry

example {α : Sort u} {β : Sort v} (p : (α → β) ×' (β → α)) : β → α :=
  sorry
```

## 문제 14

이중 부정 제거 원리에서 배중률을 도출할 수 있음을 보여라.
