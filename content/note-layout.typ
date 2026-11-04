// Keep each continuous text run containing a footnote together before page
// layout. Preserve styled wrappers and existing label spans.
#let contains-note(body) = {
  if type(body) != content { return false }
  if body.func() == footnote { return true }
  if body.has("children") and body.children.any(contains-note) { return true }
  if body.has("child") and contains-note(body.child) { return true }
  body.has("body") and contains-note(body.body)
}
#let sequence = [].func()
// A kept heading and its first paragraph form one outer block. Its top
// spacing must equal the heading's own spacing, which collapses inside it.
#let heading-above(level, numbered: true) = if level == 2 and numbered {
  5mm
} else { 4mm }
// A title is repeated in running heads and the contents. Its note belongs
// only to the original heading; preserve the remaining styled title text.
#let without-notes(body) = {
  if type(body) != content or not contains-note(body) { return body }
  if body.func() == footnote { return [] }
  if body.func() == sequence {
    return sequence(body.children.map(without-notes))
  }
  let fields = body.fields()
  let _ = fields.remove("label", default: none)
  if body.has("child") {
    let child = fields.remove("child")
    let styles = fields.remove("styles")
    return body.func()(without-notes(child), styles, ..fields)
  }
  if body.has("body") {
    let inner = fields.remove("body")
    return body.func()(without-notes(inner), ..fields)
  }
  body
}
#let title-text(body) = {
  if body.has("text") { return body.text }
  if body.func() in ([ ].func(), linebreak) { return " " }
  if body.has("children") { return body.children.map(title-text).join() }
  if body.has("child") { return title-text(body.child) }
  if body.has("body") { return title-text(body.body) }
  panic("Unsupported content in a heading with a note: " + repr(body))
}
// Mathematics in a heading: its bookmark shows Unicode subscripts where an
// exact one exists, "K₀ of maximal orders".
#let subscript-digits = (
  "0": "₀",
  "1": "₁",
  "2": "₂",
  "3": "₃",
  "4": "₄",
  "5": "₅",
  "6": "₆",
  "7": "₇",
  "8": "₈",
  "9": "₉",
  "n": "ₙ",
  "i": "ᵢ",
  "j": "ⱼ",
  "r": "ᵣ",
)
#let has-math(body) = {
  if type(body) != content { return false }
  if body.func() == math.equation { return true }
  if body.has("children") { return body.children.any(has-math) }
  if body.has("child") { return has-math(body.child) }
  if body.has("body") { return has-math(body.body) }
  false
}
#let math-title-text(body) = {
  if type(body) == str { return body }
  if body.has("text") { return body.text }
  if body.func() == math.attach {
    let base = math-title-text(body.base)
    let b = body.at("b", default: none)
    if b == none { return base }
    let sub = math-title-text(b)
    let mapped = sub.clusters().map(c => subscript-digits.at(c, default: none))
    return if mapped.any(m => m == none) { base + "_" + sub } else {
      base + mapped.join()
    }
  }
  if body.func() in ([ ].func(), linebreak) { return " " }
  if body.has("children") { return body.children.map(math-title-text).join() }
  if body.has("child") { return math-title-text(body.child) }
  if body.has("body") { return math-title-text(body.body) }
  ""
}
#let bookmark-title(it) = if (
  has-math(it.body)
    and not contains-note(it.body)
    and (it.bookmarked == true or (it.bookmarked == auto and it.outlined))
) {
  context {
    let prefix = if it.numbering == none { "" } else {
      numbering(it.numbering, ..counter(heading).at(it.location())) + " "
    }
    metadata((
      kind: "bookmark-title",
      position: it.location().position(),
      title: prefix + math-title-text(it.body),
    ))
  }
} else if (
  contains-note(it.body)
    and (it.bookmarked == true or (it.bookmarked == auto and it.outlined))
) {
  context {
    let prefix = if it.numbering == none { "" } else {
      numbering(it.numbering, ..counter(heading).at(it.location())) + " "
    }
    metadata((
      kind: "bookmark-title",
      position: it.location().position(),
      title: prefix + title-text(without-notes(it.body)),
    ))
  }
}
#let keep-note-runs(body) = {
  if body.has("label") or not contains-note(body) { return body }
  if body.func() != sequence {
    if body.has("child") {
      let fields = body.fields()
      let child = fields.remove("child")
      let styles = fields.remove("styles")
      return body.func()(keep-note-runs(child), styles, ..fields)
    }
    return body
  }
  let children = body.children
  let result = ()
  let i = 0
  let empty = [ ].func()
  let boundary(it) = {
    if it.func() == sequence { return it.children.any(boundary) }
    if it.has("child") { return boundary(it.child) }
    (
      it.func()
        in (
          parbreak,
          block,
          grid,
          table,
          figure,
          list,
          enum,
          terms,
          list.item,
          enum.item,
          terms.item,
          heading,
          pagebreak,
          colbreak,
        )
        or (it.func() == math.equation and it.block)
    )
  }
  // A paragraph that follows a kept note run is still a new paragraph: the
  // enclosing block of the run would drop its native indent.
  let indent-next = false
  while i < children.len() {
    let child = children.at(i)
    let grouped = false
    if indent-next and child.func() not in (empty, parbreak) {
      if not boundary(child) and not contains-note(child) {
        let stop = i + 1
        while stop < children.len() and not boundary(children.at(stop)) {
          stop += 1
        }
        let run = sequence(children.slice(i, stop))
        if not contains-note(run) {
          result.push(context par(
            first-line-indent: (
              amount: par.first-line-indent.amount,
              all: true,
            ),
            run,
          ))
          i = stop
          grouped = true
        }
      }
      indent-next = false
    }
    if (
      child.func() == heading
        and child
          .fields()
          .at(
            "level",
            default: child.fields().at("depth", default: 1),
          )
          in (2, 3)
    ) {
      let start = i + 1
      while (
        start < children.len()
          and (
            children.at(start).func() in (empty, parbreak)
          )
      ) { start += 1 }
      let stop = start
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      if (
        contains-note(child)
          or contains-note(sequence(children.slice(start, stop)))
      ) {
        let level = child
          .fields()
          .at(
            "level",
            default: child.fields().at("depth", default: 1),
          )
        result.push(block(
          above: heading-above(
            level,
            numbered: child.fields().at("numbering", default: auto) != none,
          ),
          breakable: false,
          sequence(children.slice(i, stop)),
        ))
        i = stop
        grouped = true
        indent-next = true
      }
    }
    if not grouped and child.func() == math.equation and child.block {
      let stop = i + 1
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      let tail = sequence(children.slice(i + 1, stop))
      if contains-note(tail) {
        result.push(block(breakable: false, sequence(children.slice(i, stop))))
        i = stop
        grouped = true
        indent-next = true
      }
    }
    if not grouped and not boundary(child) {
      let stop = i + 1
      while stop < children.len() and not boundary(children.at(stop)) {
        stop += 1
      }
      let run = sequence(children.slice(i, stop))
      if contains-note(run) {
        // A new paragraph after another paragraph keeps its native indent,
        // which the enclosing block would otherwise drop.
        let before = i - 1
        while before >= 0 and children.at(before).func() == empty {
          before -= 1
        }
        let after-paragraph = (
          before >= 1
            and children.at(before).func() == parbreak
            and not boundary(children.at(before - 1))
        )
        // Text alone in a block is not a paragraph (Typst 0.15): build an
        // explicit one.
        result.push(block(breakable: false, if after-paragraph {
          context par(
            first-line-indent: (
              amount: par.first-line-indent.amount,
              all: true,
            ),
            run,
          )
        } else { run }))
        i = stop
        grouped = true
        indent-next = true
      }
    }
    if not grouped {
      result.push(keep-note-runs(child))
      i += 1
    }
  }
  sequence(result)
}

// Whether the next paragraph follows another paragraph ("paragraph") or a
// display, a list, a heading or another block ("flush"); book-style.typ.
#let paragraph-context = state("paragraph-context", "flush")
