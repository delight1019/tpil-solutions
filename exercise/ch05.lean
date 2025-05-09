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
  . intro h hpq
    exact (h hpq.left) (hpq.right)
  . intro h hp hq
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
  intro hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  cases h with
  | inl hnp => contradiction
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  simp

example : p ∧ False ↔ False := by
  simp

example : (p → q) → (¬q → ¬p) := by
  intro h hnq hp
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
  intro h hp
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



/- Ch 04 -/

-- 1
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    have hp : ∀ x, p x := by
      intro w
      exact (h w).left
    have hq : ∀ x, q x := by
      intro w
      exact (h w).right
    exact ⟨hp, hq⟩
  . intro h
    have hp := h.left
    have hq := h.right
    intro w
    exact ⟨(hp w), (hq w)⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro f g w
  exact (f w) (g w)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h w
  cases h with
  | inl hp => left; exact hp w
  | inr hq => right; exact hq w

-- 2
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro a
  apply Iff.intro
  . intro h
    exact h a
  . intro h w
    exact h

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    by_cases hr : r
    . exact Or.inr hr
    . left
      intro w
      exact (h w).resolve_right hr
  . intro h w
    cases h with
    | inl hp => exact Or.inl (hp w)
    | inr hr => exact Or.inr hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr w
    exact (h w) hr
  . intro h w hr
    exact (h hr) w

-- 3
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have hbarber := h barber
  let sbb := shaves barber barber
  have hnsbb : ¬sbb := by
    intro hsbb
    have hnsbb := hbarber.mp hsbb
    contradiction
  have hsbb : sbb := hbarber.mpr hnsbb
  contradiction

-- 4
def even (n : Nat) : Prop := by
  exact (n % 2 = 0)

def prime (n : Nat) : Prop := by
  exact n >= 2 ∧ (∀ x : Nat, x > 1 ∧ x < n → n % x ≠ 0)

def infinitely_many_primes : Prop := by
  exact ∀ n : Nat, ∃ x, (x > n) ∧ (prime x)

def Fermat_prime (n : Nat) : Prop := by
  exact prime n ∧ ∃ x, n = 2^2^x + 1

def infinitely_many_Fermat_primes : Prop := by
  exact ∀ n : Nat, ∃ x, (x > n) ∧ (Fermat_prime x)

def goldbach_conjecture : Prop := by
  exact ∀ n, (n > 2) ∧ (even n) → ∃ x y, (prime x) ∧ (prime y) ∧ (x + y = n)

def Goldbach's_weak_conjecture : Prop := by
  exact ∀ n, (n > 5) ∧ ¬ even n → ∃ x y z, (prime x) ∧ (prime y) ∧ (prime z) ∧ (x + y + z = n)

def Fermat's_last_theorem : Prop := by
  exact ∀ n, (n ≥ 3) → ¬ ∃ a b c : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n

-- 5
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  simp

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  simp

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro x hpq =>
      cases hpq with
      | inl hp =>
        left
        exact ⟨x, hp⟩
      | inr hq =>
        right
        exact ⟨x, hq⟩
  . intro h
    cases h with
    | inl hp =>
      cases hp with
      | intro x hx => exact ⟨x, Or.inl hx⟩
    | inr hq =>
      cases hq with
      | intro x hx => exact ⟨x, Or.inr hx⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  simp

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  simp

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  simp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  simp

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  simp

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro h
    cases h with
    | intro x hpr =>
      intro f
      exact hpr (f x)
  . intro h
    by_cases hap : ∀ x, p x
    . exact ⟨a, fun _ => h hap⟩
    . show ∃ x, p x → r
      admit


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro x hrp =>
      intro hr
      exact ⟨x, hrp hr⟩
  . intro h
    by_cases hr : r
    . apply Exists.elim (h hr)
      . intro w
        intro hp
        exact ⟨w, fun _ => hp⟩
    . exact ⟨a, fun hr => by contradiction⟩


/- Ch 05 -/
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> (try constructor) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
