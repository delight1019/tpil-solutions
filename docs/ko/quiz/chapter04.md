# 4장 퀴즈

## 문제 1

`sorry` 식별자를 실제 증명으로 바꿔 다음 정리를 증명하라.

```lean
namespace Question01

universe u

variable {α : Sort u}

def p (x : α) : Prop := ∀ (q : α → Prop), ¬q x

theorem forall_not_p (x : α) : ¬p x :=
  sorry

end Question01
```

## 문제 2

[문제 1](#문제-1)에 나온 술어 `p`의 정의는 비서술적인가?

## 문제 3

동치 관계에 대한 다음 진술이 참인지 거짓인지 각각 판단하라.

\(a\) 같음 관계는 동치 관계이다. \
\(b\) 자연수에 대한 작거나 같음 관계 `· ≤ · : Nat → Nat → Prop`는 동치 관계이다.

## 문제 4

다음 보기를 증명하라.

```lean
section

universe u

variable {α : Sort u} {p : α → Prop} {q : Prop}

example (h : ∀ (x : α), p x) (a : α) : p a :=
  sorry

example (w : α) (h : p w) : ∃ (x : α), p x :=
  sorry

example (h₁ : ∃ (x : α), p x) (h₂ : ∀ (x : α), p x → q) : q :=
  sorry

end
```

## 문제 5

아래에 나열된 유형에 속하는 항의 보기를 각각 들어라.

다형적 의존곱형 `PSigma`에 관한 정보는 다음 문서에서 확인할 수 있다. <https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#PSigma>

`PSigma.mk`가 `PSigma`의 구성자의 이름임을 유념하라.

```lean
section

universe u v w

variable {α : Sort u} {β : α → Sort v}

example (f : (x : α) → β x) (a : α) : β a :=
  sorry

example (a : α) (b : β a) : (x : α) ×' β x :=
  sorry

example {γ : Sort w} (p : (x : α) ×' β x) (f : (x : α) → β x → γ) : γ :=
  match p with
  | .mk a b => sorry

end
```
