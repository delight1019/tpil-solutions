example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

namespace transitive
  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ x y z, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r a b c
  #check trans_r a b c hab
  #check trans_r a b c hab hbc
end transitive

namespace transitive2
  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r hab
  #check trans_r hab hbc
end transitive2

namespace equivalence_relation
  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd
end equivalence_relation

#check Eq.refl
#check Eq.symm
#check Eq.trans

namespace equality_relation
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)

  example : a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

  example : a = d := (hab.trans hcb.symm).trans hcd
end equality_relation

namespace reflexibity
  variable (α β : Type)

  example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
  example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
  example : 2 + 3 = 5 := Eq.refl _

  example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
  example (a : α) (b : β) : (a, b).1 = a := rfl
  example : 2 + 3 = 5 := rfl
end reflexibity

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

namespace auxiliary_rules
  variable (α : Type)
  variable (a b : α)
  variable (f g : α → Nat)
  variable (h₁ : a = b)
  variable (h₂ : f = g)

  example : f a = f b := congrArg f h₁
  example : f a = g a := congrFun h₂ a
  example : f a = g b := congr h₂ h₁
end auxiliary_rules

namespace common_identities
  variable (a b c : Nat)

  example : a + 0 = a := Nat.add_zero a
  example : 0 + a = a := Nat.zero_add a
  example : a * 1 = a := Nat.mul_one a
  example : 1 * a = a := Nat.one_mul a
  example : a + b = b + a := Nat.add_comm a b
  example : a + b + c = a + (b + c) := Nat.add_assoc a b c
  example : a * b = b * a := Nat.mul_comm a b
  example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
  example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
  example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
  example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
  example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
end common_identities

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

namespace calculational_proofs
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  theorem T : a = e :=
    calc
      a = b     := h1
      _ = c + 1 := h2
      _ = d + 1 := congrArg Nat.succ h3
      _ = 1 + d := Nat.add_comm d 1
      _ = e := Eq.symm h4
end calculational_proofs

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3

/- Later -/
namespace Trans_type_calc

def divides (x y : Nat) : Prop :=
  ∃ k, k * x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

end Trans_type_calc

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y               := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)           := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y             := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc]

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

namespace infer_exists_intro
  variable (g : Nat → Nat → Nat)
  variable (hg : g 0 0 = 0)

  theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.explicit true
  #print gex1
  #print gex2
  #print gex3
  #print gex4
end infer_exists_intro

namespace exists_elim
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    Exists.elim h
      (fun w =>
       fun hw : p w ∧ q w =>
       show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
end exists_elim

namespace exists_match
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    let ⟨w, hpw, hqw⟩ := h
    ⟨w, hqw, hpw⟩

  example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
    fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
end exists_match

namespace even
  def is_even (a : Nat) := ∃ b, a = 2 * b

  theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
    Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
      Exists.intro (w1 + w2)
        (calc a + b
          _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
          _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

  theorem even_plus_even2 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    match h1, h2 with
    | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨(w1 + w2), by rw [hw1, hw2, Nat.mul_add]⟩
end even

namespace classical
  open Classical
  variable (p : α → Prop)

  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction
      (fun h1 : ¬ ∃ x, p x =>
        have h2 : ∀ x, ¬ p x :=
          fun x =>
          fun h3 : p x =>
          have h4 : ∃ x, p x := ⟨x, h3⟩
          show False from h1 h4
        show False from h h2
      )
end classical

namespace this

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

end this

namespace french

variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2 ›

end french
