/- Existential Quantifier -/
namespace existential_quantifier

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) :=
  fun hr : r => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun ⟨w, hpx, hr⟩ => ⟨⟨w, hpx⟩, hr⟩)
    (fun ⟨⟨w, hpx⟩, hr⟩ => ⟨w, hpx, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨w, poq⟩ =>
      Or.elim poq
        (fun hp : p w => Or.inl ⟨w, hp⟩)
        (fun hq : q w => Or.inr ⟨w, hq⟩)
    )
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun hp : (∃ x, p x) =>
          Exists.elim hp
            (fun w =>
             fun hpw : p w =>
             show (∃ x, p x ∨ q x) from ⟨w, Or.inl hpw⟩
            )
        )
        (fun hq : (∃ x, q x) =>
          Exists.elim hq
            (fun w =>
             fun hqw : q w =>
             show (∃ x, p x ∨ q x) from ⟨w, Or.inr hqw⟩)
        )
    )



example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ∀ x, p x =>
      fun nCon : ∃ x, ¬ p x => show False from
        Exists.elim nCon
          (fun w =>
           fun hnp : ¬ p w => show False from
            absurd (fun hpw : p w => absurd hpw hnp)
                   (fun hnpw : ¬ p w => absurd (h w) hnpw)
          )
    )
    (fun h : ¬ (∃ x, ¬ p x) =>
      fun z : α => show p z from
        byContradiction
          (fun hnp : ¬ p z =>
            have h2 : ∃ x, ¬ p x := ⟨z, hnp⟩
            show False from h h2
          )
    )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h : ∃ x, p x =>
      Exists.elim h
        (fun w =>
         fun hp : p w =>
         fun nCon : ∀ x, ¬ p x => show False from absurd hp (nCon w)
        )
    )
    (fun h : ¬ (∀ x, ¬ p x) =>
      byContradiction
        (fun h1 : ¬ (∃ x, p x) =>
          have h2 : ∀ x, ¬ p x :=
            fun x =>
            fun hp : p x =>
            have h3 : ∃ x, p x := ⟨x, hp⟩
            show False from h1 h3
          show False from h h2
        )
    )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬ (∃ x, p x) =>
      fun z => show ¬ p z from
        fun hp : p z =>
          have h2 : ∃ x, p x := ⟨z, hp⟩
          show False from h h2
    )
    (fun h : ∀ x, ¬ p x =>
      fun nCon : ∃ x, p x =>
        Exists.elim nCon
          (fun w =>
           fun hp : p w =>
           show False from (h w) hp
          )
    )

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h : ¬ ∀ x, p x => show ∃ x, ¬ p x from
      byContradiction
        (fun nCon : ¬ ∃ x, ¬ p x =>
          have h2 : ∀ x, p x :=
            fun x =>
            fun hnp : ¬ p x =>
            have h3 : ∃ x, ¬ p x := ⟨x, hnp⟩
            show False from nCon h3
          show False from h h2
        )
    )
    (sorry)

end existential_quantifier
