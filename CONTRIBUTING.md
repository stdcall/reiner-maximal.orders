# Building and editing

Run `just build` to create the PDF, `just check` for the complete validation
suite, and `just fmt` to format Typst with the editor settings. Machine
settings belong in an untracked `.env` file. Fonts and their licences are
included under `assets/fonts`; system fonts are not used.

The mathematical checks are described in `checks/README.md`:
`just check-sage` runs the exact computations with SageMath, and
`just check-lean` compiles and audits the Lean proofs, against a prebuilt
mathlib checkout of the pinned commit given by `LEAN_MATHLIB` in `.env`, or
in `checks/lean` after `lake build` there. A change of mathematics in a
passage listed in `checks/lean-proofs.json` calls for a review of the proof
linked to it.

## Structure and numbering

Chapter files contain plain markup included by `content/main.typ`, one
file per section: `content/CC-SS-slug.typ` (chapter, section); the
chapter's own heading and introduction are in `content/CC-00-slug.typ`.
Import `main-defs.typ` and `statements.typ`.

- Chapters (`= Title <ch:…>`) are numbered 1–9. Sections (`== Title
  <sec:…>`) are numbered continuously through the book, 1–41; call
  `#continue-sections()` between a chapter introduction and its first
  section. An introduction whose displays are numbered in the series
  of the first section, "(17.1)", begins with `#open-section()`. Subsections (`=== Title <ss:…>`) are lettered within their
  section: 1a, 1b, … The exercises of a section follow
  `#heading(level: 3, numbering: none, outlined: false)[Exercises]`.
- Theorems, lemmas, corollaries, propositions, definitions, remarks,
  examples and numbered displays share one counter within each section:
  `(section.item)`. Exercises have a separate counter within their
  section.
- Every numbered object carries a literal, stable semantic label immediately
  after it; references use native `@label` syntax and print the computed
  number: `@th:…` gives "(1.4)", `@exc:…` gives "1.3" ("3" within its own
  section), `@sec:…` "4", `@ss:…` "4a", `@ch:…` "6". A part of a
  statement is cited as `@th:…[(iv)]`, printed "(2.21(iv))". A page of this
  edition is cited by the object on it: `page~@eq:…[page]`. A numbered
  display is an equation followed by an `eq:` label; unnumbered displays
  are unlabelled. A display numbered after another one, "(9.6a)", is
  `#display-variant([@eq:…], suffix: "a", $ … $) <eq:…>`.

## Statements

- `#theorem[…]`, `#lemma[…]`, `#corollary[…]`, `#proposition[…]`: name in
  small capitals, text in italics. `major: true` prints the boldface name
  that marks one of the major results of the book (see the Preface).
  `kind:` replaces the printed name ("Gauss' Lemma"); `title:` adds an
  attribution in parentheses ("Schilling").
- `#definition[…]`, `#remark[…]`, `#example[…]`: name in italics, text in
  roman; `kind: "Definitions"`, `"Remarks"`, `"Comments"` and so on as
  printed. `#definition(formal: true)` is printed like a theorem.
  `#example(plain: true)` keeps the name in roman. `numbered: false` for
  unnumbered remarks.
- `#proof[…]`; `#exercise[…] <exc:…>` with an inline
  `#hint[@exc:…][…] <hint:…>`: the brackets and the word "Hint" are
  generated, and the exercise number and the hint link to each other. An attributed hint,
  "[Hint (Berger–Reiner [1]): …]", takes `title: […]`.
- Lists of conditions are native enumerations, numbered (i), (ii), … by
  default; other forms use `enum(numbering: "(a)", …)`.
- The author's footnotes are native footnotes, marked with a dagger.
  Editorial notes use `#ed-note[…]`.

## Notation

Operators of the book are defined in `main-defs.typ`: `charpol`,
`minpol`, `redcharpol` ("char. pol.", …), `Hom`, `End`, `Ext`, `Tor`,
`nr`, `tr`, `rad`, `card`, `diag`, `Gal`, `lcm` ("L.C.M."); `bold(Z)` for
the boldface number systems; `dsum` for the dotted summation sign of the
external direct sum and `dotplus` for its binary form; `lrmaps(f, g)` for a pair of opposite maps in a
line of text; `samegenus` for the genus relation "M v N" (§27); `index`, `res` and `normal` (▵, as printed) for §29; `inv`, `Pic`, `Picent`, `Outcent`, `LFP`
for §§30–38; `eichler(R)` for "Eichler/R", in the style of the
surrounding text; `lmodule(A, M)` for
${}_A M$. Inside `cases(...)` a bare comma separates cases: write a comma that
belongs to a case as `","`. Keep visible function arguments outside
subscripts, for example
`$f_i lr((x))$` or `$h_i (X)$`. Do not type numbers or layout adjustments
in chapter files; fix typography in the common style.

## Index and bibliography

Subject index entries are generated from `#idx(...)` marks beside the
passages. For a named object use `#idx("Term", target: [@th:name])`; the
locator then follows the beginning of that object.

Bibliographic descriptions are stored only in `references.bib`, with stable
surname-and-year keys. The printed list keeps the book's author groups,
numbered within each author: "Deuring [@bib:Deuring1935]" prints
"Deuring [1]". A range "Harada [1–5]" is written with its ends,
`[@bib:Harada1963a–@bib:Harada1963e]`, followed by
`#bib-mentions(<bib:…>, …)` for the works inside the range. A locator inside the brackets, `[@bib:Bourbaki1964, Ch.~5,
§~1]`, is a place in the cited work. The generated bibliography includes
page links for text mentions.

## Pagination

The cover is outside the page count. The preliminary series begins with the
list of the series on page ii and the title page on page iii, followed by
the Preface, the Acknowledgements, the Contents and the Permanent notation.
The text begins a new arabic series at 1. Typesetting reflows the text: its
folios need not match those of the printed book. The foreword of the 2003
reissue is not included.

## Corrections

Confirmed textual emendations are recorded in `corrections.json`, which
also supplies the separate corrections PDF; its entries quote the printed
page numbers.
