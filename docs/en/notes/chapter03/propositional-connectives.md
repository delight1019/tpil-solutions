# Propositional Logic

## Truth and Falsity

### Truth

* Names: truth, true proposition
* Name in Lean: `True`
* Rule of inference
  - Introduction rule: `True` is true. (`True.intro`)

### Falsity

* Names: falsity, false proposition, empty proposition
* Name in Lean: `False`
* Rule of inference
  - Elimination rule: any proposition follows from a contradiction.
    (`False.elim`, also known as *ex falso quodlibet (EFQ)* or *the principle of
    explosion*)

## Propositional Connectives

### Negation

* Names: negation, logical not
* Name in Lean: `Not`
* Symbol: `¬` (read as "not")
* Editor shortcut: `\not`, `\neg`
* Meaning: given `p : Prop`, the proposition `¬p` stands for "It is not the case
  that `p`."
* Definition in Lean: `¬p` is defined to be `p → False`.
* Rules of inference
  - Introduction rule: if a contradiction follows from `p`, then `¬p` holds.
    (*refutation by contradiction*)
  - Elimination rule: a contradiction follows from `p` and `¬p`.

### Conjunction

* Names: conjunction, logical and
* Name in Lean: `And`
* Symbol: `∧` (read as "and")
* Editor shortcut: `\and`
* Meaning: given `p q : Prop`, the proposition `p ∧ q` stands for "Both `p` and
  `q`."
* Rules of inference
  - Introduction rule: `p ∧ q` follows from `p` and `q`. (`And.intro`)
  - Elimination rules
    + `p` follows from `p ∧ q`. (`And.left`)
    + `q` follows from `p ∧ q`. (`And.right`)

### Disjunction

* Names: disjunction, logical or
* Name in Lean: `Or`
* Symbol: `∨` (read as "or")
* Editor shortcut: `\or`
* Meaning: given `p q : Prop`, the proposition `p ∨ q` stands for "Either `p` or
  `q`."
* Rules of inference
  - Introduction rules
    + `p ∨ q` follows from `p`. (`Or.inl`)
    + `p ∨ q` follows from `q`. (`Or.inr`)
  - Elimination rule: `r` follows from `p ∨ q`, `p → r`, and `q → r`.
    (`Or.elim`, also known as *proof by cases*)

### Implication

* Names: implication, material implication, material conditional, logical
  conditional
* Symbol: `→` (read as "implies")
* Editor shortcut: `\to`, `\r`, `\imp`
* Meaning: given `p q : Prop`, the proposition `p → q` stands for "If `p`, then
  `q`."
* Rules of inference
  - Introduction rule: if `q` follows from `p`, then `p → q` holds.
  - Elimination rule: `q` follows from `p` and `p → q`. (*modus ponens*)

#### Notes on Implication

* Necessary condition: `p → q` also stands for "`p` only if `q`," that is, `q`
  is a necessary condition for `p` to be true.
* Conversion: `q → p` is the converse of `p → q`.
* Inversion: `¬p → ¬q` is the inverse of `p → q`.
* Contraposition: `¬q → ¬p` is the contraposition of `p → q`.

### Equivalence

* Names: equivalence, logical biconditional, material biconditional
* Name in Lean: `Iff` (abbreviation of "if and only if")
* Symbol: `↔` (read as "if and only if")
* Editor shortcut: `\iff`, `\lr`
* Meaning: given `p q : Prop`, the proposition `p ↔ q` stands for "`p` if and
  only if `q`" (often abbreviated as "`p` iff `q`").
* Rules of inference
  - Introduction rule: `p ↔ q` follows from `p → q` and `q → p`. (`Iff.intro`)
  - Elimination rules
    + `p → q` follows from `p ↔ q`. (`Iff.mp`, modus ponens for iff)
    + `q → p` follows from `p ↔ q`. (`Iff.mpr`, reversed modus ponens for iff)
