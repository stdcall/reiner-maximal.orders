#import "numbering.typ": restart-counters, section-counter
#import "statements.typ": numbered-display
#import "main-defs.typ": reference-rules
#import "note-layout.typ": bookmark-title, contains-note, keep-note-runs
#import "note-layout.typ": without-notes
#import "note-layout.typ": heading-above, paragraph-context

#let running-chapter = state("running-chapter", [])
#let running-section = state("running-section", [])
#let body-margin = (x: 17mm, top: 19mm, bottom: 18mm)
#let opening-page() = {
  query(heading.where(level: 1))
    .map(it => it.location().page())
    .contains(here().page())
}
#let folio() = text(size: 9pt, counter(page).display())
// Running heads: the chapter on even pages; on odd pages the section in
// force at the top of the page (or a section beginning there).
#let running-header = context {
  if opening-page() { return }
  if calc.even(counter(page).get().first()) {
    grid(
      columns: (2em, 1fr, 2em),
      align: (left, center, right),
      folio(), smallcaps(running-chapter.get()), [],
    )
  } else {
    let leading = query(heading.where(level: 2)).find(it => (
      it.numbering != none
        and it.location().page() == here().page()
        and it.location().position().y <= body-margin.top + 0.1pt
    ))
    let section = if leading != none {
      [#counter(heading).at(leading.location()).last(). #without-notes(
          leading.body,
        )]
    } else if running-section.get() == [] {
      running-chapter.get()
    } else { running-section.get() }
    grid(
      columns: (2em, 1fr, 2em),
      align: (left, center, right),
      [], smallcaps(section), folio(),
    )
  }
}
// An inline formula taller than the text line takes the room it needs, so
// that it does not run into the neighbouring lines; also used by the
// corrections list.
#let inline-equation(it) = context {
  let ink = measure({
    set text(top-edge: "bounds", bottom-edge: "bounds")
    it
  })
  let equation = if ink.height > 1em.to-absolute() {
    text(top-edge: "bounds", bottom-edge: "bounds", it)
  } else { it }
  // Keep short inline relations intact at line/page boundaries; long
  // equations retain native mathematical line breaking.
  if ink.width <= 12em.to-absolute() { box(equation) } else { equation }
}

// "(mod …)" keeps its distance from the term before it, as \pmod does in
// TeX: 8mu in a line of text, 18mu in a display; also used by the
// corrections list.
#let mod-spacing(it) = {
  let gap = if it.block { 1em } else { 8em / 18 }
  let starts-with-mod(lr) = {
    if not lr.body.has("children") { return false }
    let parts = lr.body.children.filter(c => c.func() != [ ].func())
    (
      parts.len() > 1
        and parts.at(1).func() == math.op
        and parts.at(1).text == [mod]
    )
  }
  show math.lr: lr => if starts-with-mod(lr) { h(gap) + lr } else { lr }
  it
}

#let book-style(body) = {
  set page(
    width: 152mm,
    height: 229mm,
    margin: body-margin,
    header: text(size: 8.5pt, running-header),
    footer: context if opening-page() { align(center, folio()) },
  )
  set text(font: "Libertinus Serif", size: 10.5pt, lang: "en", region: "us")
  set par(
    justify: true,
    leading: 0.58em,
    first-line-indent: 1.1em,
    spacing: 0.65em,
  )
  // Short unfinished prose introduces the next block. Keep its native par
  // with that block; complete sentences and longer prose retain normal flow.
  // A short paragraph that follows another paragraph ("Next we note") is a
  // new, indented paragraph: it is left in the native flow, which keeps its
  // indent; a block would drop it. The kept one continues a sentence after
  // a display or a block, flush left as Typst sets it.
  show selector.or(
    block,
    enum,
    list,
    terms,
    table,
    figure,
    heading,
    outline,
    math.equation.where(block: true),
  ): it => {
    it
    paragraph-context.update("flush")
  }
  show par: it => context {
    let before = paragraph-context.get()
    let words(body) = {
      if type(body) == str { return body }
      if type(body) != content { return "" }
      if body.has("text") { return words(body.text) }
      if body.has("children") { return body.children.map(words).join() }
      if body.has("child") { return words(body.child) }
      if body.has("body") { return words(body.body) }
      ""
    }
    let has-math(body) = {
      if type(body) != content { return false }
      if body.func() == math.equation { return true }
      if body.has("children") { return body.children.any(has-math) }
      if body.has("child") { return has-math(body.child) }
      if body.has("body") { return has-math(body.body) }
      false
    }
    let plain = words(it.body).trim()
    if (
      before != "paragraph"
        and plain != ""
        and plain.len() <= 80
        and plain.split(regex("\\s+")).len() <= 12
        and not plain.ends-with(regex("[.!?;][)\\]\"”’]*$"))
        and not has-math(it.body)
    ) {
      block(above: par.spacing, below: par.spacing, sticky: true, it)
    } else { it }
    paragraph-context.update("paragraph")
  }
  show link: set text(fill: black)
  // A hyphen joined to the preceding word or formula ("-module",
  // "$B$-$B$-bimodule") never begins a line.
  show regex("^-(\p{L}|$)"): it => sym.wj + it
  show "–": it => sym.wj + it + sym.wj
  // Lists of conditions and cases are numbered (i), (ii), ... in upright
  // type, also in italic statements, as in the book; other forms are given
  // by `enum(numbering: ...)`.
  set enum(numbering: (..n) => text(style: "normal", numbering("(i)", ..n)))
  // The author's footnotes are marked with a dagger, as printed.
  set footnote(numbering: _ => "†")
  // Bookmarks and the contents carry the printed numbers: "Chapter 1.",
  // "1." for a section and "1a" for a subsection.
  set heading(numbering: (..n) => {
    let numbers = n.pos()
    if numbers.len() == 1 {
      "Chapter " + str(numbers.first()) + "."
    } else if numbers.len() == 2 {
      str(numbers.at(1)) + "."
    } else {
      str(numbers.at(1)) + numbering("a", numbers.last())
    }
  })
  show heading.where(level: 1): it => {
    bookmark-title(it)
    pagebreak(weak: true)
    let numbered = it.numbering != none
    running-chapter.update(without-notes(it.body))
    running-section.update([])
    if numbered {
      context {
        let chapter = counter(heading).at(it.location()).first()
        [#metadata((
          kind: "numbered",
          family: "heading",
          level: 1,
          number: (chapter,),
        ))<numbered>]
      }
    }
    block(width: 100%, above: 12mm, below: 9mm, align(center, {
      set par(first-line-indent: 0pt, justify: false)
      text(size: 16pt, weight: "bold", {
        if numbered {
          str(counter(heading).at(it.location()).first()) + ". "
        }
        it.body
      })
    }))
  }
  show heading.where(level: 2): it => {
    bookmark-title(it)
    if it.numbering != none {
      restart-counters(2)
      context {
        let n = section-counter.get().first()
        [#metadata((
          kind: "numbered",
          family: "heading",
          level: 2,
          number: (n,),
        ))<numbered>]
        running-section.update([#n. #without-notes(it.body)])
        block(
          width: 100%,
          above: heading-above(2),
          below: 3.5mm,
          sticky: true,
          align(center, text(
            size: 10.5pt,
            weight: "bold",
            tracking: 0.03em,
            [#n. #upper(it.body)],
          )),
        )
      }
    } else {
      block(
        width: 100%,
        above: heading-above(2, numbered: false),
        below: 2mm,
        sticky: true,
        strong(it.body),
      )
    }
  }
  show heading.where(level: 3): it => {
    bookmark-title(it)
    if it.numbering == none {
      // "Exercises" at the end of a section.
      block(
        width: 100%,
        above: heading-above(3),
        below: 2.5mm,
        sticky: true,
        align(center, strong(upper(it.body))),
      )
    } else {
      context {
        let n = numbering("a", counter(heading).at(it.location()).last())
        [#metadata((
          kind: "numbered",
          family: "heading",
          level: 3,
          number: (section-counter.get().first(), n),
        ))<numbered>]
        block(
          width: 100%,
          above: heading-above(3),
          below: 2.5mm,
          sticky: true,
          align(center, strong[#section-counter.display()#n #it.body]),
        )
      }
    }
  }
  show heading: set par(first-line-indent: 0pt, justify: false)
  show outline: set par(first-line-indent: 0pt)
  show outline.entry: set block(breakable: false)
  show outline.entry: it => {
    if contains-note(it.body()) {
      link(it.element.location(), it.indented(it.prefix(), {
        without-notes(it.body())
        box(width: 1fr, it.fill)
        it.page()
      }))
    } else { it }
  }
  set math.equation(numbering: none, supplement: none)
  show math.equation: set text(font: "STIX Two Math")
  show math.equation.where(block: false): inline-equation
  show math.equation: mod-spacing

  // The book prints slanted inequality signs.
  show math.equation: it => {
    show ":": math.class("punctuation", ":")
    show "∼": math.scripts
    show "≥": sym.gt.eq.slant
    show "≤": sym.lt.eq.slant
    it
  }
  show math.equation.where(block: true): it => {
    if (
      it.has("label")
        and str(it.label).starts-with("eq:")
        and it.numbering == none
    ) {
      numbered-display(it)
    } else { it }
  }
  set table(stroke: 0.4pt, inset: (x: 0.4em, y: 0.45em))
  show table: set align(center)
  set table.cell(breakable: false)
  show footnote.entry: it => {
    context metadata((
      kind: "footnote-placement",
      marker-page: it.note.location().page(),
      entry-page: it.location().page(),
    ))
    it
  }
  show: reference-rules
  keep-note-runs(body)
}
