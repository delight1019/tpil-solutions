# Propositional Logic

## Propositions

### The Usages of the Term 'Proposition'

> The term ‘proposition’ has a broad use in contemporary philosophy. It is used
> to refer to some or all of the following: the primary bearers of truth-value,
> the objects of belief and other “propositional attitudes” (i.e., what is
> believed, doubted, etc.), the referents of that-clauses, and the meanings of
> sentences. (McGrath and Frank 2024)

### Propositions in School Mathematics in South Korea

> 문장 ‘2는 소수이다.’는 참이고, 식 ‘`√2 + √3 = √5`’는 거짓이다. 이와 같이 참,
> 거짓을 명확하게 판별할 수 있는 문장이나 식을 **명제**라고 한다. (전인태 n.d.,
> 83)
>
> The sentence ‘2 is prime’ is true and the expression ‘`√2 + √3 = √5`’ is
> false. We refer to a sentence or expression whose truth or falsehood can be
> clearly determined, like these examples, as a *proposition*.

### Questions about Usages of the Term 'Proposition'

#### Is the Sentence 'Bulhwi Cha loves himself' a Proposition?

High school mathematics teachers in South Korea would answer no. On the
contrary, it seems the authors of the entry "Propositions" in the Stanford
Encyclopedia of Philosophy (SEP) would answer yes, judging from the following
quotations:

> E.g., if the proposition that `a` loves `b` is the ordered triple `<loving, a,
> b>`,
> it is distinct from the proposition that `b` loves `a`, which would be the ordered
> triple `<loving, b, a>`. (McGrath and Frank 2024)

> Is the proposition that John loves Mary different from the proposition that
> Mary is loved by John? (ibid.)

#### Is Goldbach's Conjecture a Proposition?

Goldbach's conjecture states that every even natural number greater than 2 is
the sum of two prime numbers. We don't know whether it's true or false as of
2024, so high school mathematics teachers in South Korea would *have to* answer
no.

However, the conjecture can be defined as a proposition in the Lean theorem
prover as follows:

```lean
import Mathlib.Data.Nat.Prime.Defs

def goldbach_conjecture : Prop :=
  ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, (Prime p ∧ Prime q) ∧ n = p + q
```

### My Closing Thoughts

I don't think the usage of the term 'proposition' in Korean high school
mathematics coincides with those in contemporary philosophy or interactive
theorem provers like Lean.

One can't clearly determine what the verb phrase 'clearly determine' really
means, so Korean high school mathematics doesn't make it easier for students to
understand the notion of a proposition.

### Appendix: Korean High School Mathematics Teachers' Thoughts

Recently, a high school student from Korea [asked][ask] two math teachers which
of the following is a proposition: (a) a subjective value judgment and (b) a
mathematical statement whose truth value we don't know yet. Both responded that
(a) isn't a proposition.

However, they were divided on whether (b) is a proposition. One of them said
that (b) is also a proposition since we *can* determine its truth or falsehood.
The other argued that *linguistically* speaking ("국어적으로 해석한다면"), we can
determine the truth or falsehood of (b), but *mathematically* speaking, it can't
be a proposition.

## References

* McGrath, Matthew and Devin Frank, "Propositions", *The Stanford Encyclopedia
  of Philosophy* (Fall 2024 Edition), Edward N. Zalta & Uri Nodelman (eds.), URL
  = <https://plato.stanford.edu/archives/fall2024/entries/propositions/>.
* 전인태, 김동재, 최은아 등. 게재일 불명. “고등학교 공통수학2.” 천재교과서.
  2024년 10월 21일에 마지막으로 접속함.
  <https://text.tsherpa.co.kr/modal/preview_file.html?filePath=/00_%EA%B5%90%EA%B3%BC%EC%84%9C%ED%99%8D%EB%B3%B4%EA%B4%80_%EA%B3%A0%EB%93%B1/%EA%B5%90%EA%B3%BC%EC%84%9CPDF/03_%EC%88%98%ED%95%99/%EC%B2%9C%EC%9E%AC_%EA%B3%A0%EB%93%B1_%EA%B3%B5%ED%86%B5%EC%88%98%ED%95%992(%EC%A0%84%EC%9D%B8%ED%83%9C)_%EA%B5%90%EA%B3%BC%EC%84%9C.pdf>.

[ask]: https://forum.owlofsogang.com/t/topic/5357/13
