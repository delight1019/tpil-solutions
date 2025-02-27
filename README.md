# tpil-solutions

English | [한국어[Korean]](./README.ko.md)

This is the repository for my solutions to the exercises in ["Theorem Proving in
Lean 4"][tpil] by [Jeremy Avigad][ja], [Leonardo de Moura][ldm], [Soonho
Kong][sk] and [Sebastian Ullrich][su], with contributions from the [Lean
Community][lean-comm].

Most of the content has been released under the terms of [Apache License Version
2.0](./LICENSE). However, this repository also contains a Lean file in the
[public domain](./LICENSE-CC0).

I've also included a quiz for each chapter of the text in this repository, along
with my solutions to the questions in each quiz.

I use [OmegaT][omt] to translate English documentation into Korean. The OmegaT
project is in the [`docs`](./docs) directory. You need to install the [Okapi
filters plugin for OmegaT][okapi] to make OmegaT parse Markdown files.

## Directories and files

* [`docs`](./docs): Markdown documents including notes and quizzes.
  * [`en`](./docs/en): Source documents written in English.
    * [`notes`](./docs/en/notes)
      * `ChapterXX`: My notes about the concepts explained in Chapter XX of the
        text.
    * [`quiz`](./docs/en/quiz)
      * `chapterXX.md`: My additional quiz for Chapter XX of the text.
  * [`ko`](./docs/ko): Korean translation of the source documents in the `en`
    directory. It has the same subdirectory structure as `en`.

* [`TPIL`](./TPIL): My solutions to the exercises and questions. This directory
  also contains Lean files providing examples of the concepts discussed in the
  text.
  * `ChapterXX`: Chapter XX of the text.
    * `Question*`: Solutions to the question(s) of my quiz.
    * `Exercise*`: Solutions to the exercise(s) in the chapter.
  * [`Exam`](./TPIL/Exam): My additional examinations for the text.

## Contributing

If you've found errors in my solutions and want to fix them, please send an
email to <~chabulhwi/lean-books-discuss@lists.sr.ht>. It's my mailing list for
end-user discussion and questions related to the [lean-books][lean-books]
project.

[tpil]: https://lean-lang.org/theorem_proving_in_lean4/title_page.html
[ja]: https://www.andrew.cmu.edu/user/avigad/
[ldm]: https://leodemoura.github.io/about.html
[sk]: https://soonhokong.github.io/
[su]: https://sebasti.a.nullri.ch/
[lean-comm]: https://leanprover-community.github.io/
[omt]: https://omegat.org/
[okapi]: https://okapiframework.org/wiki/index.php/Okapi_Filters_Plugin_for_OmegaT
[lean-books]: https://sr.ht/~chabulhwi/lean-books/
