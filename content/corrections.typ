// Readable list of the confirmed deviations of this edition from the
// printed book (corrections.json), built as a separate PDF. An entry prints
// its id, printed page, place, the printed reading, the correction and the
// reason; `verified_by` (how the correction was checked) stays in the
// journal.
//
// `original`, `corrected` and `reason` are Typst markup: most entries quote
// formulas, so they are evaluated with the book's own definitions.
#import "main-defs.typ" as book-defs
#import "book-style.typ": inline-equation, mod-spacing

// The entries quote numbers as printed: the objects and the bibliography
// are not in this separate document, so references are plain quoted text.
#show: book-defs.reference-rules
#let book-scope = dictionary(book-defs)
#let entries = json("../corrections.json").entries
#let markup(field) = eval(field, mode: "markup", scope: book-scope)

#set document(
  title: "Reiner: Maximal Orders. Corrections",
  author: "Irving Reiner",
  date: none,
)
#set page(
  width: 176mm,
  height: 250mm,
  margin: (x: 20mm, top: 21mm, bottom: 21mm),
  footer: context align(center, text(size: 10pt, counter(page).display())),
)
#set text(font: "Libertinus Serif", size: 11pt, lang: "en", region: "gb")
#set par(justify: true, leading: 0.65em, spacing: 0.8em)
#show math.equation: set text(font: "STIX Two Math")
#show math.equation: it => {
  show ":": math.class("punctuation", ":")
  show "∼": math.scripts
  show "≥": sym.gt.eq.slant
  show "≤": sym.lt.eq.slant
  it
}
#show math.equation.where(block: false): inline-equation
#show math.equation: mod-spacing

#align(center, text(size: 16pt)[Corrections])

I.~Reiner, _Maximal Orders_, London Mathematical Society Monographs, New Series
28, Clarendon Press, Oxford, 2003. This edition corrects the misprints and
errors listed below; page numbers are those of the printed book.

// The entries go by the page of the book and are grouped under the part of
// the book they belong to, with a heading and a bookmark for each;
// an entry names its own place only where it is narrower than the part.
#show heading: set text(size: 12pt)
#show heading: set block(above: 1.6em, below: 0.8em)

#if entries.len() == 0 [
  No corrections have been recorded yet.
] else {
  let section = none
  for entry in entries {
    if entry.section != section {
      section = entry.section
      heading(level: 1, section)
    }
    block(breakable: false, above: 1em)[
      #metadata((correction: entry.id))
      *#entry.id* · p. #entry.printed_page#if (
        entry.place != entry.section
      ) [, #markup(entry.place)]

      Printed: #markup(entry.original)

      Corrected: #markup(entry.corrected)

      #text(size: 10pt, markup(entry.reason))
    ]
  }
}
