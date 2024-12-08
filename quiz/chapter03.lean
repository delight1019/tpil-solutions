namespace Question01
/- a -/ /- O -/
/- b -/ /- O -/
/- c -/ /- O -/
end Question01


namespace Question02
/- a -/ /- O -/
/- b -/ /- O -/
/- c -/ /- O -/
/- d -/ /- O -/
end Question02


namespace Question03

example {p q: Prop} (hp : p) (hpq : p → q) : q :=
  hpq hp

end Question03


namespace Question04

example {α : Sort u} {β : Sort v} (a : α) (f : α → β) : β :=
  f a

end Question04


namespace Question05

example {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  And.intro hp hq

example {p q : Prop} (h : p ∧ q) : p :=
  And.left h

example {p q : Prop} (h : p ∧ q) : q :=
  And.right h

end Question05


namespace Question06

example {α : Sort u}{β : Sort v} (a : α)(b : β) : α ×' β :=
  PProd.mk a b

example {α : Sort u}{β : Sort v} (p : α ×' β) : α :=
  p.1

example {α : Sort u}{β : Sort v} (p : α ×' β) : β :=
  p.2

end Question06


namespace Question07

example {p q : Prop} (hp : p) : p ∨ q :=
  Or.inl hp

example {p q : Prop} (hq : q) : p ∨ q :=
  Or.inr hq

example {p q r : Prop} (h : p ∨ q) (left : p → r) (right : q → r) : r :=
  Or.elim h
    (fun hp : p => show r from left hp)
    (fun hq : q => show r from right hq)

end Question07


namespace Question08

example {α : Sort u}{β : Sort v} (a : α) : α ⊕' β :=
  PSum.inl a

example {α : Sort u}{β : Sort v} (b : β) : α ⊕' β :=
  PSum.inr b

example {α : Sort u}{β : Sort v}{γ : Sort w} (s : α ⊕' β) (f : α → γ) (g : β → γ) : γ :=
  match s with
  | .inl a => f a
  | .inr b => g b

end Question08


namespace Question09

/- a -/ /- O -/
/- b -/ /- O -/
/- c -/ /- O -/

end Question09


namespace Question10

example {p : Prop} (h : ¬p) : p → False :=
  h

example {p : Prop} (h : p → False) : ¬p :=
  h

example {p : Prop} (hp : p) (hnp : ¬p) : False :=
  hnp hp

example {p : Prop} (h : False) : p :=
  False.elim h

example {p q : Prop} (hp : p) (hnp : ¬p) : q :=
  False.elim (hnp hp)

end Question10


namespace Question11

example {α : Sort u} (x : Empty) : α :=
  Empty.elim x

end Question11


namespace Question12

example {p q : Prop} (mp : p → q) (mpr : q → p) : p ↔ q :=
  Iff.intro
    (fun hp : p => show q from mp hp)
    (fun hq : q => show p from mpr hq)

example {p q : Prop} (h : p ↔ q) : p → q :=
  h.mp

example {p q : Prop} (h : p ↔ q) : q → p :=
  h.mpr

end Question12


namespace Question13

example {α : Sort u}{β : Sort v} (f : α → β) (g : β → α) : (α → β) ×' (β → α) :=
  PProd.mk f g

example {α : Sort u}{β : Sort v} (p : α ×' β) : α :=
  p.fst

example {α : Sort u}{β : Sort v} (p : (α → β) ×' (β → α)) : β → α :=
  p.snd

end Question13


namespace Question14

/- the law of excluded middle : p ∨ ¬p -/
/- principle of double-negation elimination : ¬¬p → p -/

example (dne : {p : Prop} → ¬¬p → p) : p ∨ ¬p :=
  dne (
    fun hn : ¬(p ∨ ¬p) => show False from
      hn (Or.inr (fun hp : p => show False from hn (Or.inl hp)))
  )

end Question14
