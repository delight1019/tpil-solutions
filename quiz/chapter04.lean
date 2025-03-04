namespace Question01

universe u
variable {α : Sort u}

def p (x : α) : Prop := ∀ (q : α → Prop), ¬q x

theorem not_exists_p : ¬∃ (x : α), p x :=
  fun h : ∃ (x : α), p x =>
    Exists.elim h
      (fun w =>
       fun hp : p w => show False from
        let q : α → Prop := p
        (show ¬q w from hp q) -- Why not ?? (show ¬q w from (p w) q)
        (show q w from hp)
      )

theorem forall_not_p (x : α) : ¬p x :=
  fun h : p x => show False from
    (show ¬∃ x, p x from not_exists_p)
    (show ∃ x, p x from ⟨x, h⟩)

end Question01

namespace Question02
/- a -/ /- O -/
end Question02

namespace Question03
/- a -/ /- O -/
/- b -/ /- X, Not symmetric -/
end Question03

namespace Question04

universe u
variable {α : Sort u} {p : α → Prop} {q : Prop}

example (h : ∀ (x : α), p x) (a : α) : p a :=
  h a

example (w : α) (h : p w) : ∃ (x : α), p x :=
  ⟨w, h⟩

example (h₁ : ∃ (x : α), p x) (h₂ : ∀ (x : α), p x → q) : q :=
  Exists.elim h₁
    (fun w =>
     fun hpw : p w =>
     h₂ w hpw)

end Question04

namespace Question05

universe u v w
variable {α : Sort u} {β : α → Sort v}

example (f : (x : α) → β x) (a : α) : β a :=
  f a

example (a : α) (b : β a) : (x : α) ×' β x :=
  PSigma.mk a b

example {γ : Sort w} (p : (x : α) ×' β x) (f : (x : α) → β x → γ) : γ :=
  match p with
  | .mk a b => f a b

end Question05
