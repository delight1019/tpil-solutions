# Chapter 4 Quiz

## Question 1

Prove the following theorem, replacing the `sorry` identifier with an actual
proof:

```lean
namespace Question01

universe u

variable {α : Sort u}

def p (x : α) : Prop := ∀ (q : α → Prop), ¬q x

theorem forall_not_p (x : α) : ¬p x :=
  sorry

end Question01
```

## Question 2

Is the definition of the predicate `p` from [Question 1](#question-1)
impredicative?

## Question 3

Answer by true or false each of the following statements about equivalence
relations.

\(a\) The equality relation is an equivalence relation. \
\(b\) The less-than-or-equal-to relation on natural numbers, `· ≤ · : Nat → Nat
→ Prop`, is an equivalence relation.

## Question 4

Prove the following examples:

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

## Question 5

Give an example of a term of each type listed below.

For information about the polymorphic type of dependent pairs `PSigma`, see
<https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#PSigma>.

Note that `PSigma.mk` is the name of the constructor for `PSigma`.

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
