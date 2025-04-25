/- Ch 03 -/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    exact ⟨h.right, h.left⟩
  . intro h
    exact ⟨h.right, h.left⟩

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  . intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hpq hr => exact ⟨hpq.left, ⟨hpq.right, hr⟩⟩
  . intro h
    cases h with
    | intro hp hqr => exact ⟨⟨hp, hqr.left⟩, hqr.right⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  . intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr hqr =>
      cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩
  . intro h
    cases h with
    | inl hpq => exact ⟨hpq.left, (Or.inl hpq.right)⟩
    | inr hpr => exact ⟨hpr.left, (Or.inr hpr.right)⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact ⟨(Or.inl hp), (Or.inl hp)⟩
    | inr hqr => exact ⟨(Or.inr hqr.left), (Or.inr hqr.right)⟩
  . intro h
    cases h with
    | intro hpq hpr =>
      cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq =>
        cases hpr with
        | inl hp => exact Or.inl hp
        | inr hr => exact Or.inr ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h
    intro hpq
    exact (h hpq.left) (hpq.right)
  . intro h
    intro hp
    intro hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    have hptr : p → r := by
      intro hp
      exact h (Or.inl hp)
    have hqtr : q → r := by
      intro hq
      exact h (Or.inr hq)
    exact ⟨hptr, hqtr⟩
  . intro h
    intro hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply And.intro
    . intro hp
      exact h (Or.inl hp)
    . intro hq
      exact h (Or.inr hq)
  . intro h
    intro hpq
    have := h.left
    have := h.right
    cases hpq with
    | inl hp => contradiction
    | inr hq => contradiction

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  intro hpq
  have := hpq.left
  have := hpq.right
  cases h with
  | inl hp => contradiction
  | inr hq => contradiction

example : ¬(p ∧ ¬p) := by
  simp

example : p ∧ ¬q → ¬(p → q) := by
  simp

example : ¬p → (p → q) := by
  intro hnp
  intro hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h
  intro hp
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  simp

example : p ∧ False ↔ False := by
  simp

example : (p → q) → (¬q → ¬p) := by
  intro h
  intro hnq
  intro hp
  have := h hp
  contradiction


-- Classical
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  by_cases hp : p
  . have hqr := h hp
    cases hqr with
    | inl hq =>
      left
      intro hp'
      exact hq
    | inr hr =>
      right
      intro hp'
      exact hr
  . left
    intro hp'
    contradiction


example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_cases hp : p
  . right
    intro hq
    exact h ⟨hp, hq⟩
  . left
    exact hp

example : ¬(p → q) → p ∧ ¬q := by
  simp

example : (p → q) → (¬p ∨ q) := by
  intro h
  by_cases hp : p
  . right
    exact h hp
  . left
    exact hp

example : (¬q → ¬p) → (p → q) := by
  intro h
  intro hp
  by_cases hq : q
  . exact hq
  . have := h hq
    contradiction

example : p ∨ ¬p := by
  by_cases hp : p
  . left; exact hp
  . right; exact hp

example : (((p → q) → p) → p) := by
  intro h
  by_cases hp : p
  . exact hp
  . have hpq : p → q := by
      intro hp'
      contradiction
    exact h hpq

-- Probe ¬(p ↔ ¬p) without using classical logic
example : ¬(p ↔ ¬p) := by
  intro h
  have ptnp : p → ¬p := h.mp
  have nptp : ¬p → p := h.mpr
  have hnp : ¬p := by
    intro hp
    have := ptnp hp
    contradiction
  have := nptp hnp
  contradiction
