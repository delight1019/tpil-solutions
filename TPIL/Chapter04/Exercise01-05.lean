/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

/-!
# Chapter 4 Exercises

## Exercise 1
-/

section

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩)
    (fun h x ↦ ⟨h.1 x, h.2 x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp x ↦ (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, (p x ∨ q x) :=
  fun h x ↦ h.elim
    (fun hp ↦ Or.inl (hp x))
    (fun hq ↦ Or.inr (hq x))

end

/- There exists a pair of the predicates `p` and `q` where the reverse implication of the previous
example is false. Therefore, the reverse isn't derivable. -/
example : ∃ (p q : Nat → Prop), ¬((∀ x, p x ∨ q x) → (∀ x, p x) ∨ (∀ x, q x)) :=
  let p (n : Nat) := n ≥ 2;
  let q (n : Nat) := n < 2;
  have hapq : ∀ x, p x ∨ q x :=
    fun n ↦ Or.symm (Nat.lt_or_ge n 2)
  have hnp : ¬∀ x, p x :=
    fun hp ↦
      have h2eq0 : 2 = 0 := Nat.eq_zero_of_le_zero (hp 0)
      show False from Nat.succ_ne_zero 1 h2eq0
  have hnq : ¬∀ x, q x :=
    fun hq ↦ Nat.lt_irrefl 2 (hq 2)
  have hnpq : ¬((∀ x, p x) ∨ (∀ x, q x)) :=
    fun hapaq ↦ hapaq.elim hnp hnq
  ⟨p, q, not_imp_of_and_not ⟨hapq, hnpq⟩⟩

/-!
## Exercise 2
-/

section

set_option linter.unusedVariables false

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun w ↦ ⟨fun h ↦ h w, fun h _ ↦ h⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h ↦ Classical.byCases
      (fun hr : r ↦ Or.inr hr)
      (fun hnr : ¬r ↦ Or.inl (fun x ↦ show p x from
        (h x).elim id (fun hr ↦ show p x from absurd hr hnr))))
    (fun h x ↦ h.elim
      (fun hap ↦ Or.inl (hap x))
      (fun hr  ↦ Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨fun h hr x ↦ h x hr, fun h x hr ↦ h hr x⟩

end

/-!
## Exercise 3
-/

section

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬shaves x x) : False :=
  have hnsbb : ¬shaves barber barber :=
    fun hsbb : shaves barber barber ↦
      have hnsbb : ¬shaves barber barber := (h barber).mp hsbb
      show False from hnsbb hsbb
  have hsbb : shaves barber barber :=
    (h barber).mpr hnsbb
  show False from hnsbb hsbb

end

/-!
## Exercise 4
-/

def even (n : Nat) : Prop := ∃ m : Nat, n = 2 * m

def prime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m : Nat, (∃ p : Nat, n = m * p) → m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ m : Nat, prime m ∧ n < m

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ m : Nat, n = 2 ^ (2 ^ m) + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, ∃ m : Nat, Fermat_prime m ∧ n < m

def goldbach_conjecture : Prop :=
  ∀ n : Nat, even n ∧ n > 2 → ∃ m p : Nat, (prime m ∧ prime p) ∧ n = m + p

def goldbach_weak_conjecture : Prop :=
  ∀ n : Nat, ¬even n ∧ n > 5 →
  ∃ m p q : Nat, (prime m ∧ prime p ∧ prime q) ∧ n = m + p + q

def fermat_last_theorem : Prop :=
  ∀ n : Nat, n > 2 →
  ¬∃ a b c : Nat, (a > 0 ∧ b > 0 ∧ c > 0) ∧ a ^ n + b ^ n = c ^ n

/-!
## Exercise 5
-/

section

set_option linter.unusedVariables false

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun h ↦ h.elim (fun _ hr ↦ hr)

-- alternative proof
example : (∃ x : α, r) → r :=
  fun h ↦ h.elim (fun _ ↦ id)

example (a : α) : r → (∃ x : α, r) :=
  fun hr ↦ ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h ↦ h.elim (fun w hw ↦ ⟨⟨w, hw.1⟩, hw.2⟩))
    (fun h ↦ h.1.elim (fun w hw ↦ ⟨w, hw, h.2⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun h ↦ h.elim (fun w hw ↦ hw.elim
      (fun hpw ↦ Or.inl ⟨w, hpw⟩)
      (fun hqw ↦ Or.inr ⟨w, hqw⟩)))
    (fun h ↦ h.elim
      (fun hexp ↦ hexp.elim (fun w hpw ↦ ⟨w, Or.inl hpw⟩))
      (fun hexq ↦ hexq.elim (fun w hqw ↦ ⟨w, Or.inr hqw⟩)))

example : (∀ x, p x) ↔ ¬(∃ x, ¬p x) :=
  Iff.intro
    (fun h ⟨w, hnpw⟩ ↦ hnpw (h w))
    (fun h x ↦ show p x from byContradiction (fun hnpx ↦ h ⟨x, hnpx⟩))

example : (∃ x, p x) ↔ ¬(∀ x, ¬p x) :=
  Iff.intro
    (fun ⟨w, hw⟩ hanp ↦ hanp w hw)
    (fun h ↦ show ∃ x, p x from byContradiction (fun hnexp ↦
      have hanp : ∀ x, ¬p x := fun x hpx ↦ hnexp ⟨x, hpx⟩
      show False from h hanp))

example : (¬∃ x, p x) ↔ (∀ x, ¬p x) :=
  Iff.intro
    (fun h x hpx ↦ h ⟨x, hpx⟩)
    (fun hanp ⟨x, hpx⟩ ↦ hanp x hpx)

example : (¬∀ x, p x) ↔ (∃ x, ¬p x) :=
  Iff.intro
    (fun h ↦ show ∃ x, ¬p x from byContradiction (fun hnexnp ↦
      have hap : ∀ x, p x := fun x ↦ show p x from byContradiction (fun hnpx ↦ hnexnp ⟨x, hnpx⟩)
      show False from h hap))
    (fun ⟨x, hnpx⟩ hap ↦ hnpx (hap x))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h ⟨x, hpx⟩ ↦ h x hpx)
    (fun h x hpx ↦ h ⟨x, hpx⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨x, hpxr⟩ hap ↦ hpxr (hap x))
    (fun h ↦ byCases
      (fun hexnp : ∃ x, ¬p x ↦
        let ⟨x, hnpx⟩ := hexnp
        ⟨x, fun hpx ↦ show r from absurd hpx hnpx⟩)
      (fun hnexnp : ¬∃ x, ¬p x ↦
        have hap : ∀ x, p x := fun x ↦ show p x from byContradiction (fun hnpx ↦
          show False from hnexnp ⟨x, hnpx⟩)
        ⟨a, fun _ ↦ h hap⟩))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨x, hrpx⟩ hr ↦ ⟨x, hrpx hr⟩)
    (fun h ↦ byCases
      (fun hr : r ↦
        let ⟨w, hpw⟩ := h hr
        ⟨w, fun _ ↦ hpw⟩)
      (fun hnr : ¬r ↦
        ⟨a, fun hr ↦ show p a from absurd hr hnr⟩))

end
