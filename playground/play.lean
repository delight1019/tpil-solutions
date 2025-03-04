variable (h : ∀ {p : Prop}, p → p)
#check h

variable (h2 : ∀ {p : Prop}, p)
#check h2

example : ∀ {p : Prop}, p :=
  let h : Prop := False
  False.elim h
