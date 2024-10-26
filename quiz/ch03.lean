variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => show q ∧ p from ⟨h.right, h.left⟩)
    (fun h : q ∧ p => show p ∧ q from ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => show q ∨ p from
      Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq))
    (fun h : q ∨ p => show p ∨ q from
      Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp))

--  associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      have pnq : p ∧ q := h.left
      show p ∧ (q ∧ r) from
        And.intro pnq.left ⟨pnq.right, h.right⟩)
    (fun h : p ∧ (q ∧ r) =>
      have qnr : q ∧ r := h.right
      show (p ∧ q) ∧ r from
        And.intro ⟨h.left, qnr.left⟩ qnr.right)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      show p ∨ (q ∨ r) from
        Or.elim h
          (fun hpoq : p ∨ q => show p ∨ (q ∨ r) from
            Or.elim hpoq
              (fun hp : p => Or.inl hp)
              (fun hq : q => Or.inr (Or.inl hq))
            )
          (fun hr : r => Or.inr (Or.inr hr))
      )
    (fun h : p ∨ (q ∨ r) =>
      show (p ∨ q) ∨ r from
        Or.elim h
          (fun hp : p => Or.inl (Or.inl hp))
          (fun hqor : q ∨ r => show (p ∨ q) ∨ r from
            Or.elim hqor
              (fun hq : q => Or.inl (Or.inr hq))
              (fun hr : r => Or.inr hr)
            )
      )

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      have qor : q ∨ r := h.right
      Or.elim qor
        (fun hq : q => show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r => show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩)
    )
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun pnq : p ∧ q => show p ∧ (q ∨ r) from ⟨pnq.left, Or.inl pnq.right⟩)
        (fun pnr : p ∧ r => show p ∧ (q ∨ r) from ⟨pnr.left, Or.inr pnr.right⟩)
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h : p ∨ (q ∧ r) =>
      Or.elim h
        (fun hp : p => show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inl hp, Or.inl hp⟩)
        (fun hqnr : q ∧ r => show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hqnr.left, Or.inr hqnr.right⟩)
    )
    (fun h : (p ∨ q) ∧ (p ∨ r) =>
      have hpoq : p ∨ q := h.left
      have hpor : p ∨ r := h.right
      Or.elim hpoq
        (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
        (fun hq : q =>
          Or.elim hpor
            (fun hp : p => show p ∨ (q ∧ r) from Or.inl hp)
            (fun hr : r => show p ∨ (q ∧ r) from Or.inr ⟨hq, hr⟩)
        )
    )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : (p → (q → r)) => show (p ∧ q → r) from
      fun hpnq : (p ∧ q) =>
      show r from (h hpnq.left) hpnq.right
    )
    (fun h : (p ∧ q → r) => show (p → (q → r)) from
      fun hp : p =>
      fun hq : q =>
      show r from h ⟨hp, hq⟩
    )

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h : ((p ∨ q) → r) => show (p → r) ∧ (q → r) from
      ⟨(fun hp : p => show r from h (Or.inl hp)), (fun hq : q => show r from h (Or.inr hq))⟩
    )
    (fun h : (p → r) ∧ (q → r) =>
      have hptr : p → r := h.left
      have hqtr : q → r := h.right
      show ((p ∨ q) → r) from
        fun hpoq : p ∨ q =>
          Or.elim hpoq
            (fun hp : p => show r from hptr hp)
            (fun hq : q => show r from hqtr hq)
    )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) => show ¬p ∧ ¬q from
      ⟨(fun hp : p => show False from h (Or.inl hp)), (fun hq : q => show False from h (Or.inr hq))⟩
    )
    (fun h : ¬p ∧ ¬q =>
      have hnp : ¬p := h.left
      have hnq : ¬q := h.right
      show ¬(p ∨ q) from
        fun hpoq : p ∨ q => show False from
          Or.elim hpoq
            (fun hp : p => show False from hnp hp)
            (fun hq : q => show False from hnq hq)
    )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    (fun h : ¬p ∨ ¬q =>
      Or.elim h
        (fun hnp : ¬p => show ¬(p ∧ q) from
          fun hpnq : p ∧ q =>
            have hp : p := hpnq.left
            show False from hnp hp
        )
        (fun hnq : ¬q => show ¬(p ∧ q) from
          fun hpnq : p ∧ q =>
            have hq : q := hpnq.right
            show False from hnq hq
        )
    )

example : ¬(p ∧ ¬p) :=
  fun t : p ∧ ¬p =>
    have hp : p := t.left
    have hnp : ¬p := t.right
    show False from hnp hp

example : p ∧ ¬q → ¬(p → q) :=
  fun t : p ∧ ¬q =>
    have hp : p := t.left
    have hnq : ¬q := t.right
    show ¬(p → q) from
      fun hptq : p → q => show False from hnq (hptq hp)

example : ¬p → (p → q) :=
  fun hnp : ¬p =>
    fun hp : p => show q from False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  fun t : ¬p ∨ q =>
    fun hp : p =>
      Or.elim t
        (fun hnp : ¬p => show q from False.elim (hnp hp))
        (fun hq : q => show q from hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun h : p ∨ False => show p from
      Or.elim h
        (fun hp : p => show p from hp)
        (fun f : False => show p from False.elim f)
      )
    (fun h : p => show p ∨ False from Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h : p ∧ False => show False from h.right)
    (fun h : False => show p ∧ False from False.elim h)

example : (p → q) → (¬q → ¬p) :=
  fun hptq : p → q =>
  fun hnq : ¬q =>
  show ¬p from
    fun hp : p => show False from hnq (hptq hp)

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r => show (p → q) ∨ (p → r) from
    Or.elim (em p)
      (fun hp : p =>
        have hqor : q ∨ r := h hp
        show (p → q) ∨ (p → r) from
          Or.elim hqor
            (fun hq : q => Or.inl (show p → q from
              fun _ : p => show q from hq))
            (fun hr : r => Or.inr (show p → r from
              fun _ : p => show r from hr))
      )
      (fun hnp : ¬p => Or.inl (show p → q from
        fun hp : p => show q from False.elim (hnp hp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h : ¬(p ∧ q) => show ¬p ∨ ¬q from
    Or.elim (em p)
      (fun hp : p => Or.inr (show ¬q from
        fun hq : q => show False from h ⟨hp, hq⟩))
      (fun hnp : ¬p => Or.inl hnp)

example : ¬(p → q) → p ∧ ¬q :=
  fun h : ¬(p → q) => show p ∧ ¬q from
    Or.elim (em q)
      (fun hq : q => absurd (fun _ : p => hq) h)
      (fun hnq : ¬q =>
        Or.elim (em p)
          (fun hp : p => show p ∧ ¬q from ⟨hp, hnq⟩)
          (fun hnp : ¬p => absurd (fun hp : p => absurd hp hnp) h) --?
      )

example : (p → q) → (¬p ∨ q) :=
  fun h : p → q => show ¬p ∨ q from
    Or.elim (em p)
      (fun hp : p => Or.inr (h hp))
      (fun hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) :=
  fun h : ¬q → ¬p =>
  fun hp : p => show q from
    Or.elim (em q)
      (fun hq : q => show q from hq)
      (fun hnq : ¬q => show q from False.elim ((h hnq) hp))

example : p ∨ ¬p :=
  Or.elim (em p)
    (fun hp : p => Or.inl hp)
    (fun hnp : ¬p => Or.inr hnp)

example : (((p → q) → p) → p) :=
  fun h : (p → q) → p => show p from
    Or.elim (em p)
      (fun hp : p => show p from hp)
      (fun hnp : ¬p => show p from
        h (fun hp : p => absurd hp hnp))

-- Prove ¬(p ↔ ¬p) without using classical logic
example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    have hptn : p → ¬p := h.mp
    have hntp : ¬p → p := h.mpr
    show False from
      absurd (fun hp : p => absurd hp (hptn hp))
             (fun hnp : ¬p => absurd (hntp hnp) hnp) --??
