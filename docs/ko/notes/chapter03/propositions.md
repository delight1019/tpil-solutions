# 명제 논리

## 명제

### '명제' 용어의 쓰임새

> 동시대 철학에서 ‘명제’ 용어는 폭넓게 쓰인다. 이 용어는 다음 중 일부 또는 전부를 가리키는 데 쓰인다. 진릿값의 주요 담지자, 믿음이나 다른 ‘명제적 태도’의 대상(믿기는 것, 의심되는 것 등), that절의 지시 대상물, 문장의 의미. (McGrath and Frank 2024)

### 한국 학교 수학에서의 명제

> 문장 ‘2는 소수이다.’는 참이고, 식 ‘`√2 + √3 = √5`’는 거짓이다. 이와 같이 참,
> 거짓을 명확하게 판별할 수 있는 문장이나 식을 **명제**라고 한다. (전인태 n.d.,
> 83)
>
> The sentence ‘2 is prime’ is true and the expression ‘`√2 + √3 = √5`’ is
> false. We refer to a sentence or expression whose truth or falsehood can be
> clearly determined, like these examples, as a *proposition*.

### '명제' 용어의 쓰임새에 관한 물음

#### 문장 '차불휘는 자기 자신을 사랑한다.'는 명제인가?

한국의 고등학교 수학 교사들은 그렇지 않다고 답할 것입니다. 이와 달리, 다음 인용문으로 미루어 보면 스탠퍼드 철학 백과사전(SEP) '명제' 항목의 저자들은 그렇다고 답할 듯합니다.


> 예를 들어, `a`가 `b`를 사랑한다는 명제가 순서세짝 `<사랑함, a, b>`라면, `b`가 `a`를 사랑한다는 명제는 순서세짝 `<사랑함, b, a>`가 될 것이고, 이 두 명제는 별개이다. (McGrath and Frank 2024)

> 존이 매리를 사랑한다는 명제는 매리가 존의 사랑을 받는다는 명제와 다른가? (같은 문서 항목)

#### 골드바흐의 추측은 명제인가?

골드바흐의 추측은 2보다 큰 모든 짝수가 두 소수의 합이라는 진술입니다. 2024년 현재 우리는 아직 이 추측이 참인지 거짓인지 모르니, 한국의 고등학교 수학 교사들은 그렇지 않다고 답할 것입니다.

그러나 이 추측은 린 정리 증명기를 이용해 다음 명제로 정의할 수 있습니다.

```lean
import Mathlib.Data.Nat.Prime.Defs

def goldbach_conjecture : Prop :=
  ∀ n : ℕ, Even n ∧ n > 2 → ∃ p q : ℕ, (Prime p ∧ Prime q) ∧ n = p + q
```

### 제 결론

저는 한국 고등학교 수학에서 '명제' 용어가 쓰이는 방법이 동시대 철학에서의 용법이나 린 같은 상호 작용 정리 증명기에서의 용법과 일치한다고 생각하지 않습니다.

"명확하게 판별하다"라는 동사구가 무슨 뜻인지는 명확하게 판별할 수 없습니다. 그래서 한국 고등학교 수학에서의 명제 개념은 학생들이 이해하기 더 쉽지 않습니다.

### 부록: 한국 고등학교 수학 교사들의 생각

최근에 한국의 어느 한 고등학생이 두 수학 교사분에게 (1) 주관적 가치 판단, (2) 진릿값을 아직 모르는 수학 진술 가운데 무엇이 명제인지 [질문했습니다][ask]. 두 분 모두 (1)은 명제가 아니라고 답했습니다.

그러나 (2)가 명제인지를 둘러싸고 두 분의 의견이 갈렸습니다. 한 분은 우리가 (2)의 진릿값을 모르더라도 그것의 참과 거짓을 판별'할 수' 있기 때문에 이 또한 명제라고 말씀하셨습니다.
다른 분은 (2)를 '국어적으로' 해석한다면 그것의 참과 거짓을 판별할 수 있지만, '수학적으로' 해석한다면 진릿값을 모르는 진술은 명제가 될 수 없다고 주장하셨습니다.

## 참고 문헌

* McGrath, Matthew and Devin Frank, "Propositions", *The Stanford Encyclopedia
of Philosophy* (Fall 2024 Edition), Edward N. Zalta & Uri Nodelman (eds.), URL
= <https://plato.stanford.edu/archives/fall2024/entries/propositions/>.
* 전인태, 김동재, 최은아 등. 게재일 불명. “고등학교 공통수학2.” 천재교과서.
2024년 10월 21일에 마지막으로 접속함.
<https://text.tsherpa.co.kr/modal/preview_file.html?filePath=/00_%EA%B5%90%EA%B3%BC%EC%84%9C%ED%99%8D%EB%B3%B4%EA%B4%80_%EA%B3%A0%EB%93%B1/%EA%B5%90%EA%B3%BC%EC%84%9CPDF/03_%EC%88%98%ED%95%99/%EC%B2%9C%EC%9E%AC_%EA%B3%A0%EB%93%B1_%EA%B3%B5%ED%86%B5%EC%88%98%ED%95%992(%EC%A0%84%EC%9D%B8%ED%83%9C)_%EA%B5%90%EA%B3%BC%EC%84%9C.pdf>.

[ask]: https://forum.owlofsogang.com/t/topic/5357/13
