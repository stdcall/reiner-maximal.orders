#import "numbering.typ": (
  case-counter, case-number-format, family-counter, item-counter,
  numbered-record, object-number, record, record-number,
)
#import "note-layout.typ": contains-note, keep-note-runs

#let number-text(body) = text(weight: "semibold", body)

// Parenthetical comments retain the author's roman text inside a statement.
#let statement-comment(body) = text(style: "normal", body)

// Preserve a deliberately vacant position in the shared statement series.
#let numbering-gap() = item-counter.step()

#let sequence = [].func()
#let join-pieces(pieces) = sequence(
  pieces
    .map(it => {
      if it.func() == sequence and not it.has("label") { it.children } else {
        (it,)
      }
    })
    .flatten(),
)

#let prepend-heading(body, head) = {
  let flatten(it) = {
    if it.func() == sequence and not it.has("label") {
      it.children.map(flatten).flatten()
    } else { (it,) }
  }
  let pieces = flatten(body)
  // Named lists prepend invisible counter/state updates to their native enum.
  // Inspect the first layout element, preserving that prelude in its order.
  let invisible = (
    [ ].func(),
    parbreak,
    metadata,
    counter("heading-probe").update(0).func(),
    state("heading-probe", 0).update(0).func(),
  )
  let first = pieces.position(it => it.func() not in invisible)
  if first == none { return join-pieces((head, body)) }
  let opening = pieces.at(first)
  let advertised-block = pieces
    .slice(0, first)
    .any(it => (
      it.func() == metadata and it.value == (kind: "block-opening")
    ))
  let block-opening = (
    advertised-block
      or opening.func()
        in (
          block,
          enum,
          list,
          terms,
          table,
          grid,
          figure,
          heading,
          align,
        )
      or (opening.func() == math.equation and opening.block)
  )
  let lead = if block-opening and head != [] {
    context block(above: 0pt, below: par.leading, sticky: true, head)
  } else { head }
  join-pieces((..pieces.slice(0, first), lead, ..pieces.slice(first)))
}

#let keep-opening-display(body) = {
  if body.func() != sequence { return body }
  let children = body.children
  let first = children.position(it => (
    it.func() == math.equation and it.block
  ))
  if first == none { return body }
  let lead = children.slice(0, first)
  if lead.any(it => (
    it.func() in (parbreak, block, table, list, enum, heading)
  )) {
    return body
  }
  // Only a short opening (about three lines) is kept with its display; a
  // longer one may break across pages like any paragraph, instead of
  // moving whole to the next page.
  let text-length(it) = {
    if type(it) == str { return it.len() }
    if type(it) != content { return 0 }
    if it.has("text") { return text-length(it.text) }
    if it.has("children") {
      return it.children.map(text-length).sum(default: 0)
    }
    if it.has("child") { return text-length(it.child) }
    if it.has("body") { return text-length(it.body) }
    0
  }
  if text-length(sequence(lead)) > 240 { return body }
  join-pieces((
    context block(
      width: 100%,
      above: 0pt,
      below: par.leading,
      sticky: true,
      sequence(lead),
    ),
    ..children.slice(first),
  ))
}

#let statement(
  kind,
  family,
  body,
  italic: false,
  title: none,
  numbered: true,
  variant: none,
  name-style: smallcaps,
  note: none,
  zeroth: false,
  suffix: "′",
) = {
  // `zeroth: true`: the book numbers an introductory statement before the
  // first item of a section 0, "(4.0)"; the series is not advanced.
  if numbered and variant == none and not zeroth {
    family-counter(family).step()
  }
  let head = context {
    let base = if variant != none {
      let refs(it) = {
        if it.func() == ref { (it.target,) } else if it.has("children") {
          it.children.map(refs).flatten()
        } else if it.has("body") { refs(it.body) } else { () }
      }
      let targets = refs(variant)
      assert(
        targets.len() == 1,
        message: "A theorem variant names its base by one native reference",
      )
      let base = numbered-record(targets.first())
      assert(
        base != none
          and base.value.family == family
          and base.value.kind != "unnumbered",
        message: "A theorem variant requires a numbered theorem",
      )
      (target: targets.first(), record: base)
    }
    if variant != none {
      [#metadata((
        kind: "variant",
        family: family,
        number: record-number(base.record),
        base: str(base.target),
        suffix: suffix,
      ))<numbered>]
    } else if numbered { record(family) } else {
      [#metadata((
        kind: "unnumbered",
        family: family,
        number: none,
        name: if kind == none { "Statement" } else { kind },
      ))<numbered>]
    }
    let number = if variant != none {
      record-number(base.record).map(str).join(".") + suffix
    } else if numbered {
      object-number(family, here()).map(str).join(".")
    }
    let prefix = if numbered { [(#number-text(number)) ] } else { [] }
    let name = if kind != none { name-style(kind) } else { [] }
    let title-part = if title != none { [ (#title)] } else { [] }
    // An author's footnote on the name of the statement: "Corollary†."
    if note != none { name += footnote(note) }
    let period = if kind != none or title != none { [.] } else { [] }
    text(style: "normal", prefix + name + title-part + period + [ ])
  }
  // Full width: a block shrinks to its content, which would push a display
  // after only short lines to the left.
  block(width: 100%, above: 1.2em, below: 1.1em, breakable: true, {
    set text(style: "italic") if italic
    keep-note-runs(prepend-heading(body, head))
  })
}
// Statements share the series (section.item) with the numbered displays.
// Theorems, lemmas and corollaries print their name in small capitals and
// their text in italics; a boldface name (`major: true`) marks one of the
// major results of the book, as explained in the preface. Definitions,
// remarks, comments and examples print their name in italics and their text
// in roman. `kind` replaces the name where the book prints another one:
// "Gauss' Lemma", "Definitions", "Remarks", "Comments"; `title` adds an
// attribution: "(Schilling)".
#let major-name(name) = strong(name)
#let theorem-like(
  kind,
  family,
  body,
  major,
  title,
  numbered,
  note,
  zeroth: false,
) = statement(
  kind,
  family,
  body,
  italic: true,
  title: title,
  numbered: numbered,
  name-style: if major { major-name } else { smallcaps },
  note: note,
  zeroth: zeroth,
)
#let theorem(
  kind: "Theorem",
  major: false,
  title: none,
  numbered: true,
  note: none,
  zeroth: false,
  body,
) = theorem-like(
  kind,
  "th",
  body,
  major,
  title,
  numbered,
  note,
  zeroth: zeroth,
)
// A theorem numbered after another one, "(6.3a)": `suffix: "a"`.
#let theorem-variant(base, suffix: "′", body) = statement(
  "Theorem",
  "th",
  body,
  italic: true,
  variant: base,
  suffix: suffix,
)
#let lemma(
  kind: "Lemma",
  major: false,
  title: none,
  numbered: true,
  note: none,
  body,
) = theorem-like(kind, "lem", body, major, title, numbered, note)
#let proposition(
  kind: "Proposition",
  major: false,
  title: none,
  numbered: true,
  note: none,
  body,
) = theorem-like(kind, "prop", body, major, title, numbered, note)
#let corollary(
  kind: "Corollary",
  major: false,
  title: none,
  numbered: true,
  note: none,
  body,
) = theorem-like(kind, "cor", body, major, title, numbered, note)
// `formal: true` prints a definition as a theorem: small capitals and an
// italic text. `plain: true` prints the name of an example in roman, as in
// "(1.15) Examples of integrally closed domains."
#let definition(kind: "Definition", formal: false, title: none, body) = (
  statement(
    kind,
    "def",
    body,
    italic: formal,
    title: title,
    name-style: if formal { smallcaps } else { emph },
  )
)
// A numbered paragraph without a name, "(4.1) R is a hereditary ring, ...",
// such as one of several equivalent defining conditions.
// `variant: [@def:…]` with `suffix: "a"` numbers a supplement to a numbered
// definition, "(4.19a)", without advancing the series.
#let condition(variant: none, suffix: "′", body) = statement(
  none,
  "def",
  body,
  variant: variant,
  suffix: suffix,
)
#let remark(kind: "Remark", title: none, numbered: true, body) = statement(
  kind,
  "rem",
  body,
  title: title,
  numbered: numbered,
  name-style: emph,
)
#let example(
  kind: "Example",
  plain: false,
  title: none,
  numbered: true,
  body,
) = statement(
  kind,
  "exm",
  body,
  title: title,
  numbered: numbered,
  name-style: if plain { it => it } else { emph },
)
#let hint-link(from, number, target) = metadata((
  kind: "hint-link",
  from: from,
  number: number,
  position: here().position(),
  target-position: if target != none { target.position() },
))

// `tag: "2a"` numbers an exercise inserted after another one, "2a.",
// without advancing the series.
#let exercise(tag: none, body) = {
  if tag == none { family-counter("exc").step() }
  block(width: 100%, above: 0.4em, below: 0.4em, context {
    let number = object-number("exc", here(), tag: tag)
    let hints = query(metadata.where(value: (
      kind: "hint",
      family: "exc",
      number: number,
    )))
    assert(hints.len() <= 1, message: "An exercise has more than one hint")
    let target = if hints.len() == 1 { hints.first().location() }
    let words = strong[#number.last().]
    // The number is indented like a new paragraph, as in the book.
    let head = (
      h(par.first-line-indent.amount)
        + box(context {
          record("exc", tag: tag)
          hint-link("problem", number, target)
          if target == none { words } else { link(target, words) }
        })
        + [ ]
    )
    keep-opening-display(prepend-heading(body, head))
  })
}

// Inline hints retain the authors' bracketed form. The exercise's number
// leads to the hint; its word "Hint" leads back to the exercise.
#let close-hint(body) = {
  let pieces = if body.func() == sequence { body.children } else { (body,) }
  let last = pieces
    .enumerate()
    .rev()
    .find(pair => (
      pair.last().func() not in ([ ].func(), parbreak)
    ))
  if (
    last != none and last.last().func() == math.equation and last.last().block
  ) {
    let (index, equation) = last
    let fields = equation.fields()
    let _ = fields.remove("body")
    let target = fields.remove("label", default: none)
    let closed = math.equation(
      ..fields,
      equation.body + math.upright("]"),
    )
    if target != none { closed = [#closed#target] }
    // Keep a separate last paragraph's tail with the concluding display.
    // The first inline paragraph stays with the hint's inline heading.
    let end = index
    while end > 0 and pieces.at(end - 1).func() in ([ ].func(), parbreak) {
      end -= 1
    }
    let start = end
    while start > 0 {
      let previous = pieces.at(start - 1)
      if (
        previous.func() in (parbreak, block, enum, list, table, heading)
          or (previous.func() == math.equation and previous.block)
      ) { break }
      start -= 1
    }
    if start == end or start == 0 {
      join-pieces((..pieces.slice(0, index), closed))
    } else {
      // A paragraph that follows another paragraph keeps its indent, which
      // the enclosing block would otherwise drop.
      let before = start - 1
      while before > 0 and pieces.at(before).func() == [ ].func() {
        before -= 1
      }
      let previous = if before >= 1 { pieces.at(before - 1) }
      let after-paragraph = (
        pieces.at(before).func() == parbreak
          and previous != none
          and previous.func()
            not in (parbreak, block, enum, list, table, heading)
          and not (previous.func() == math.equation and previous.block)
      )
      let run = sequence(pieces.slice(start, end))
      join-pieces((
        ..pieces.slice(0, start),
        context block(
          above: par.spacing,
          below: par.leading,
          breakable: true,
          sticky: true,
          if after-paragraph {
            par(
              first-line-indent: (
                amount: par.first-line-indent.amount,
                all: true,
              ),
              run,
            )
          } else { run },
        ),
        closed,
      ))
    }
  } else if last != none and last.last().func() in (enum, list) {
    let (index, listing) = last
    let fields = listing.fields()
    let children = fields.remove("children")
    let target = fields.remove("label", default: none)
    let item = children.pop()
    let item-fields = item.fields()
    let inner = item-fields.remove("body")
    let item-target = item-fields.remove("label", default: none)
    let closed-item = item.func()(close-hint(inner), ..item-fields)
    if item-target != none { closed-item += item-target }
    children.push(closed-item)
    let closed = listing.func()(..fields, ..children)
    if target != none { closed += target }
    join-pieces((..pieces.slice(0, index), closed))
  } else { body + [\]] }
}

// `title:` attributes the hint, "[Hint (Berger–Reiner [1]): …]".
#let hint(problem, body, title: none) = {
  let refs(it) = {
    if it.func() == ref { (it.target,) } else if it.has("children") {
      it.children.map(refs).flatten()
    } else if it.has("body") { refs(it.body) } else { () }
  }
  let targets = refs(problem)
  assert(
    targets.len() == 1 and str(targets.first()).starts-with("exc:"),
    message: "Name the exercise by one native reference",
  )
  text(context {
    let found = numbered-record(targets.first())
    let number = if found == none { ("?",) } else { record-number(found) }
    [#metadata((kind: "hint", family: "exc", number: number))<numbered>]
    let head = context {
      let target = if found != none { found.location() }
      hint-link("hint", number, target)
      let word = if target == none { [Hint] } else { link(target, [Hint]) }
      if title == none { [#word:] } else { [#word (#title):] }
    }
    [\[#head #close-hint(body)]
  })
}
#let proof(body, head: emph[Proof.]) = {
  let contents = keep-opening-display(keep-note-runs(prepend-heading(
    body,
    if head == none {
      []
    } else {
      [#head ]
    },
  )))
  if contains-note(body) {
    // A split enclosing block can defer a note until a later page. Keep
    // note-bearing proofs in the native page flow, with their note runs
    // grouped before layout.
    parbreak()
    contents
    parbreak()
  } else {
    block(width: 100%, above: 1.1em, below: 1.1em, breakable: true, {
      contents
    })
  }
}

// Named cases retain native list numbering. Their separate counter lets
// references follow an inserted case without changing theorem numbers.
#let case-list(numbering: "(1)", ..items) = {
  // Context hides its resulting enum from structural opening detection.
  metadata((kind: "block-opening"))
  context {
    let previous = case-counter.get()
    let previous-format = case-number-format.get()
    case-counter.update(0)
    case-number-format.update(if type(numbering) == str { numbering } else {
      "(1)"
    })
    // Markers upright, also in italic statements, as printed.
    let marker = if type(numbering) == str {
      (..n) => text(style: "normal", std.numbering(numbering, ..n))
    } else { numbering }
    enum(numbering: marker, ..items.pos())
    case-counter.update(previous)
    case-number-format.update(previous-format)
  }
}
#let case(body) = {
  case-counter.step()
  text(context {
    record("case", number-format: case-number-format.get())
    body
  })
}

// `variant: true` marks the display of a `display-variant`: its number
// follows the label of the base display (checked by the lint, T013).
#let tagged-display(body, tag, variant: false) = {
  let natural = measure(math.equation(math.display(body))).width
  let reserve = measure(tag).width + 0.75em.to-absolute()
  layout(size => {
    // Wide displays use the right side of the available line so that
    // the left-hand number remains separate from the mathematical body.
    let alignment = if natural > size.width - 2 * reserve { right } else {
      center
    }
    show math.equation: set align(alignment)
    let display = math.equation(
      block: true,
      numbering: _ => tag,
      number-align: start + horizon,
      body,
    )
    if variant [#display<display-variant>] else { display }
  })
}

// A display numbered after a preceding one, "(9.6a)":
// `#display-variant([@eq:…], suffix: "a", $ … $) <eq:…>`. The series is not
// advanced; the number follows the base display.
#let display-variant(variant, suffix: "a", it) = context {
  let refs(it) = {
    if it.func() == ref { (it.target,) } else if it.has("children") {
      it.children.map(refs).flatten()
    } else if it.has("body") { refs(it.body) } else { () }
  }
  let targets = refs(variant)
  assert(
    targets.len() == 1,
    message: "A display variant names its base by one native reference",
  )
  let base = numbered-record(targets.first())
  assert(
    base != none and base.value.family == "eq",
    message: "A display variant requires a numbered display",
  )
  [#metadata((
    kind: "variant",
    family: "eq",
    number: record-number(base),
    base: str(targets.first()),
    suffix: suffix,
  ))<numbered>]
  let number = record-number(base).map(str).join(".") + suffix
  tagged-display(it.body, [(#number)], variant: true)
}

#let numbered-display(it) = {
  family-counter("eq").step()
  context {
    record("eq")
    let number = object-number("eq", here()).map(str).join(".")
    tagged-display(it.body, [(#number)])
  }
}

#let numbered-table(body, introduction: none) = {
  family-counter("eq").step()
  let numbered = block(above: 0.6em, below: 0.6em, breakable: false, {
    context {
      record("eq")
      let number = object-number("eq", here()).map(str).join(".")
      block(below: 0.5em)[(#number-text(number)):]
    }
    block(width: 100%, align(center, body))
  })
  if introduction == none { numbered } else {
    block(above: 0pt, below: 0pt, breakable: false, {
      introduction
      numbered
    })
  }
}

#let bib-item(body, tag: none) = {
  if tag == none { family-counter("bib").step() }
  block(above: 0.35em, below: 0.35em, context {
    record("bib", tag: tag)
    let n = object-number("bib", here(), tag: tag).last()
    prepend-heading(body, [#n. ])
  })
}
#let bib-group(body) = {
  family-counter("bib").update(0)
  heading(level: 2, numbering: none, outlined: false, body)
}
