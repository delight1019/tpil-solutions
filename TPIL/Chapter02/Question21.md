# Solutions to Chapter 2 Quiz

## Question 21

In the definition of `foo`, the instance of `a` in the expression `fun x : a =>
x + 2` is a syntactic abbreviation for `Nat`. Therefore, the variable `x` has
type `Nat`, so Lean can infer the type of `x + 2`, which is also `Nat`.

However, in the definition of `bar`, the expression `(fun a => fun x : a => x +
2)` has to make sense even when the value of the variable `a` isn't `Nat`.
Therefore, the variable `x` may not have type `Nat`, so Lean can't infer the
type of `x + 2`.
