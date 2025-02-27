# Predicate Logic

## Quantifiers

### Universal Quantifiers

* Name: universal quantifier
* Symbol: `∀` (read as "for all")
* Editor shortcut: `\forall`
* Meaning: given a type `α` and a unary predicate `p : α → Prop`, the
  proposition `∀ (x : α), p x` stands for "For all `x` of type `α`, `p x`
  holds."
* Definition in Lean: if `p` is an arbitrary expression, `∀ (x : α), p` is an
  alternative notation for `(x : α) → p`.
* Rules of inference
  - Introduction rule: if `p x` holds for every term `x : α`, then `∀ (x : α), p
    x` holds. (*universal generalization*)
  - Elimination rule: given `a : α`, `p a` follows from `∀ (x : α), p x`.
    (*universal instantiation*)

### Existential Quantifiers

* Name: existential quantifier
* Name in Lean: `Exists`
* Symbol: `∃` (read as "exists")
* Editor shortcut: `\ex`, `\exists`
* Meaning: given a type `α` and a unary predicate `p : α → Prop`, the
  proposition `∃ (x : α), p x` stands for "There exists a term `x` of type `α`
  where `p x` holds."
* Rules of inference
  - Introduction rule: given `a : α`, `∃ (x : α), p x` follows from `p a`.
    (*existential introduction*)
  - Elimination rule: `q` follows from `∃ (x : α), p x` and `∀ (a : α), p a →
    q`. (*existential elimination*)
