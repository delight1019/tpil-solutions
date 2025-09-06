# tpil-solutions

[English (영어)](./README.md) | 한국어

[제러미 아비가드][ja] 님, [레오나르두 지 모라][ldm] 님, [공순호][sk] 님 그리고 [제바스티안 울리히][su] 님이 저술하고, [린 커뮤니티][lean-comm]의 기여를 받아 개정된 ["린 4로 하는 정리 증명"][tpil]의 제 연습 문제 풀이가 이 저장소에 들어 있습니다.

이 저작물의 대부분은 [아파치 라이선스, 버전 2.0](./LICENSE)의 조건에 따라 배포됐습니다. 그러나 이 저장소에는 [자유 이용 저작물](./LICENSE-CC0)인 린 파일도 있습니다.

퀴즈와 시험도 이 저장소에 포함했고, 각 퀴즈의 문제 풀이도 있습니다.

[오메가T(OmegaT)][omt]를 이용해 영어 문서를 한국어로 번역했습니다. 오메가T 프로젝트는 [`docs`](./docs) 디렉터리에 있습니다. 오메가T로 마크다운 파일을 구문 분석 하려면 [오메가T를 위한 오카피(Okapi) 필터 플러그인][okapi]을 설치해야 됩니다.

## 디렉터리와 파일

* [`docs`](./docs): 보충 학습 자료와 퀴즈를 포함한 마크다운 문서.
  * [`en`](./docs/en): 영어로 작성한 원문.
    * [`notes`](./docs/en/notes)
      * `ChapterXX`: 교재의 XX장에서 설명된 개념에 관한 제 보충 학습 자료.
    * [`quiz`](./docs/en/quiz)
      * `chapterXX.md`: 교재의 XX장을 학습자가 잘 이해했는지 확인하려고 제가 만든 퀴즈.
  * [`ko`](./docs/ko): `en` 디렉터리에 있는 원문을 한국어로 번역한 문서. 하위 디렉터리 구조는 `en`과 똑같습니다.

* [`TPIL`](./TPIL): 연습 문제와 퀴즈 문항의 제 풀이. 교재에서 다룬 개념들의 보기를 드는 린 파일도 여기에 있습니다.
  * `ChapterXX`: 교재 XX장.
    * `Question*`: 제 퀴즈 문항의 풀이.
    * `Exercise*`: 교재 XX장의 연습 문제 풀이.
  * [`Exam`](./TPIL/Exam): 제가 추가로 만든 교재 시험 문제.

## 기여하기

제 풀이에 있는 오류를 고치고 싶다면, <~chabulhwi/lean-books-discuss@lists.sr.ht>에 전자 우편을 보내 주세요. 이는 [lean-books][lean-books]
프로젝트와 관련된 최종 이용자들의 논의와 질문을 보관하는 한국어 메일링 리스트[전자 우편 수신자 목록]입니다.

[tpil]: https://lean-lang.org/theorem_proving_in_lean4/title_page.html
[ja]: https://www.andrew.cmu.edu/user/avigad/
[ldm]: https://leodemoura.github.io/about.html
[sk]: https://soonhokong.github.io/
[su]: https://sebasti.a.nullri.ch/
[lean-comm]: https://leanprover-community.github.io/
[omt]: https://omegat.org/
[okapi]: https://okapiframework.org/wiki/index.php/Okapi_Filters_Plugin_for_OmegaT
[lean-books]: https://sr.ht/~chabulhwi/lean-books/
