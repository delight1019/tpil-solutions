namespace Exercise_1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h : ∀ x, p x ∧ q x =>
      ⟨fun z => (h z).left, fun z => (h z).right⟩
    )
    (fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun z => ⟨(h.left z), (h.right z)⟩
    )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : ∀ x, p x → q x =>
  fun h2 : ∀ x, p x =>
  fun z => show q z from
  ((h z) (h2 z))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    Or.elim h
      (fun hp : ∀ x, p x =>
        fun z => show p z ∨ q z from Or.inl (hp z)
      )
      (fun hq : ∀ x, q x =>
        fun z => show p z ∨ q z from Or.inr (hq z)
      )

/-
  마지막 example에서 역이 성립하지 않는 이유:
  p(x1), ¬q(x1), ¬p(x2), q(x2)인 x1, x2가 있고, 다른 x에 대해선 p(x), q(x)가 성립한다고 하자.
  이 때 가정인 ∀ x, p x ∨ q x는 참이지만 (∀ x, p x), (∀ x, q x)는 모두 거짓이다.
-/

/-- 불휘: 다음 보기도 참고해 주세요. -/
example : ∃ (α : Type) (p q : α → Prop), ¬((∀ x, p x ∨ q x) → (∀ x, p x) ∨ ∀ x, q x) :=
  let p (n : Nat) : Prop := n = 0
  let q (n : Nat) : Prop := n > 0
  let hpq : ∀ (n : Nat), p n ∨ q n := Nat.eq_zero_or_pos
  have hnp : ¬∀ n, p n := fun hp : ∀ n, p n => show False from
    (show 1 ≠ 0 from Nat.succ_ne_self 0)
      (show 1 = 0 from hp 1)
  have hnq : ¬∀ n, q n := fun hq : ∀ n, q n => show False from
    (show 0 ≠ 0 from Nat.pos_iff_ne_zero.mp (show 0 > 0 from hq 0))
      (show 0 = 0 from rfl)
  have hn : ¬((∀ x, p x ∨ q x) → (∀ x, p x) ∨ ∀ x, q x) :=
    not_imp_of_and_not ⟨hpq, not_or.mpr ⟨hnp, hnq⟩⟩
  ⟨Nat, p, q, hn⟩

end Exercise_1

namespace Exercise_2

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun ha : α => show (∀ x : α, r) ↔ r from
    Iff.intro
      (fun h : ∀ x : α, r => h ha)
      (fun h : r => show ∀ x : α, r from
        fun _ => show r from h
      )

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun h : ∀ x, p x ∨ r => show (∀ x, p x) ∨ r from
      byCases
        (fun hr : r => Or.inr hr)
        (fun hnr : ¬ r => Or.inl (fun z => show p z from
          (h z).resolve_right hnr
          /- 불휘: 다른 풀이
          (show p z ∨ r from h z).elim
            (fun hp : p z => hp)
            (fun hr : r => show p z from absurd hr hnr)
          -/
        ))
    )
    (fun h : (∀ x, p x) ∨ r =>
      fun z => show p z ∨ r from
        Or.elim h
          (fun hp : ∀ x, p x => Or.inl (hp z))
          (fun hr : r => Or.inr hr)
    )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun h : ∀ x, r → p x =>
      fun hr : r =>
      fun z => show p z from
      (h z) hr
    )
    (fun h : r → ∀ x, p x =>
      fun z =>
      fun hr : r => show p z from
      (h hr) z
    )


end Exercise_2

namespace Exercise_3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hbarber : shaves barber barber ↔ ¬ shaves barber barber := h barber
  let sbb := shaves barber barber
  have hp : sbb → ¬ sbb := hbarber.mp
  have hnp : ¬ sbb → sbb := hbarber.mpr
  show False from
    absurd (fun hsbb : sbb => absurd hsbb (hp hsbb))
           (fun hnsbb : ¬ sbb => absurd (hnp hnsbb) hnsbb)

-- 불휘: 다른 풀이
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hbarber : shaves barber barber ↔ ¬ shaves barber barber := h barber
  let sbb := shaves barber barber
  have hnsbb : ¬ sbb := fun hsbb : sbb => hbarber.mp hsbb hsbb
  have hsbb : sbb := hbarber.mpr hnsbb
  show False from hnsbb hsbb

end Exercise_3

namespace Exercise_4

def even (n : Nat) : Prop := ∃ k, 2 * k = n

/-- 불휘: `\ne`로 `≠`를 입력할 수 있습니다. -/
def prime (n : Nat) : Prop := n ≥ 2 ∧ (∀ x : Nat, x > 1 ∧ x < n → n % x ≠ 0)

/-- 불휘: `0`은 소수가 아니므로 술어 `prime`의 정의가 잘못됐습니다. 정의를 새로 작성해 주세요. -/
example : ¬prime 0 :=
  fun h : prime 0 => show False from h.right 2 (by decide) (by decide)

def infinitely_many_primes : Prop :=
  ∀ n : Nat, ∃ x, (x > n) ∧ (prime x)

-- def Fermat_prime (n : Nat) : Prop := prime (2^2^n + 1)

/-- 불휘: `2 ^ 2 ^ n + 1` 말고 `n`이 페르마 소수여야 합니다. -/
def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ x, n = 2^2^x + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat, ∃ x, (x > n) ∧ (Fermat_prime x)

def goldbach_conjecture : Prop :=
  ∀ n, (n > 2) ∧ (even n) → ∃ x y, (prime x) ∧ (prime y) ∧ (x + y = n)

def Goldbach's_weak_conjecture : Prop :=
  ∀ n, (n > 5) ∧ ¬ even n → ∃ x y z, (prime x) ∧ (prime y) ∧ (prime z) ∧ (x + y + z = n)

def Fermat's_last_theorem : Prop :=
  ∀ n, (n ≥ 3) → ¬ ∃ a b c : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^n + b^n = c^n

end Exercise_4

namespace Exercise_5

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
            /- 불휘: 다른 풀이
            hnp (h w)
            -/
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
    (fun h : ¬ ∀ x, p x =>
      byContradiction
      (fun nCon : ¬ (∃ x, ¬ p x) =>
        have nh : ∀ x, p x :=
          fun z => show p z from
            byContradiction
            (fun hnp : ¬ p z =>
             have h1 : ∃ x, ¬ p x := ⟨z, hnp⟩
             show False from nCon h1
            )
        show False from h nh
      )
    )
    (fun h : ∃ x, ¬ p x =>
      fun nCon : ∀ x, p x =>
        Exists.elim h
          (fun w =>
           fun hnp : ¬ p w => absurd (nCon w) hnp
          )
    )



example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun h : ∀ x, p x → r =>
      fun ⟨w, (hp : p w)⟩ => show r from
      (h w) hp
    )
    (fun h : (∃ x, p x) → r =>
      fun z => show p z → r from
      fun hpz : p z => show r from
      h ⟨z, hpz⟩
    )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨w, (hpr : p w → r)⟩ =>
     fun hp : ∀ x, p x => show r from
     hpr (hp w)
    )
    (fun h : (∀ x, p x) → r => show ∃ x, p x → r from
      byCases
        (fun hap : ∀ x, p x => ⟨a, λ _ => h hap⟩)
        (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ exists x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex
                  )
              show False from hnap hap
            )
        )
    )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (fun ⟨w, (hrp : r → p w)⟩ =>
     fun hr : r =>
      ⟨w, hrp hr⟩
    )
    (fun h : r → ∃ x, p x => show ∃ x, r → p x from
      byCases
        (fun hr : r =>
          Exists.elim (h hr)
          (fun w => fun hp : p w =>
            ⟨w, fun _ => hp⟩
          )
        )
        (fun hnr : ¬ r =>
         ⟨a, fun hr => absurd hr hnr⟩
        )
    )

end Exercise_5
