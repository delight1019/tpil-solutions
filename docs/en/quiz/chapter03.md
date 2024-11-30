# Chapter 3 Quiz

## Question 1

Answer by true or false each of the following statements about the terms `p :
Prop` and `t : p`.

\(a\) The term `p` is a type. \
\(b\) The term `p` is a true proposition. \
\(c\) The term `t` is a proof of some proposition.

## Question 2

Answer by true or false each of the following statements about the terms `p q :
Prop` and `t : p → q`.

\(a\) The type `p → q` is a function type. \
\(b\) The type `p → q` is an implication. \
\(c\) The term `t` is a function from `p` to `q`. \
\(d\) The term `t` is a proof of the proposition `p → q`.

## Question 3

Prove the following example:

```lean
example {p q : Prop} (hp : p) (hpq : p → q) : q :=
  sorry
```

## Question 4

Give an example of a term of the following type:

```lean
example {α : Sort u} {β : Sort v} (a : α) (f : α → β) : β :=
  sorry
```

## Question 5

Prove the following examples:

```lean
example {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  sorry

example {p q : Prop} (h : p ∧ q) : p :=
  sorry

example {p q : Prop} (h : p ∧ q) : q :=
  sorry
```

## Question 6

Give an example of a term of each type listed below.

For information about the polymorphic product type `PProd`, see
<https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#PProd>.

Note that `PProd.mk` is the name of the constructor for `PProd`.

```lean
example {α : Sort u} {β : Sort v} (a : α) (b : β) : α ×' β :=
  sorry

example {α : Sort u} {β : Sort v} (p : α ×' β) : α :=
  sorry

example {α : Sort u} {β : Sort v} (p : α ×' β) : β :=
  sorry
```

## Question 7

Prove the following examples:

```lean
example {p q : Prop} (hp : p) : p ∨ q :=
  sorry

example {p q : Prop} (hq : q) : p ∨ q :=
  sorry

example {p q r : Prop} (h : p ∨ q) (left : p → r) (right : q → r) : r :=
  sorry
```

## Question 8

Give an example of a term of each type listed below.

For information about the polymorphic sum type `PSum`, see
<https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#PSum>.

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

## Question 9

Answer by true or false each of the following statements about the terms `p :
Prop` and `t : ¬p`.

\(a\) The proposition `¬p` is definitionally equal to `p → False`. \
\(b\) The term `t` is a function from `p` to `False`. \
\(c\) The term `t` is a proof of `¬p`, the negation of `p`.

## Question 10

Prove the following examples:

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

## Question 11

Use `Empty.elim` to give an example of a term of the following type.

For information about `Empty.elim`, see
<https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Empty.elim>.

```lean
example {α : Sort u} (x : Empty) : α :=
  sorry
```

## Question 12

Prove the following examples:

```lean
example {p q : Prop} (mp : p → q) (mpr : q → p) : p ↔ q :=
  sorry

example {p q : Prop} (h : p ↔ q) : p → q :=
  sorry

example {p q : Prop} (h : p ↔ q) : q → p :=
  sorry
```

## Question 13

Give an example of a term of each type listed below:

```lean
example {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) : (α → β) ×' (β → α) :=
  sorry

example {α : Sort u} {β : Sort v} (p : (α → β) ×' (β → α)) : α → β :=
  sorry

example {α : Sort u} {β : Sort v} (p : (α → β) ×' (β → α)) : β → α :=
  sorry
```

## Question 14

Show that the law of excluded middle can be derived from the principle of
double-negation elimination.
