#import "numbering.typ": (
  numbered-record, open-section, record-number, section-counter,
)

#let editorial-notes = sys.inputs.at("editorial-notes", default: "on") != "off"

// Page anchors of the printed edition: `n` is the page of the source file,
// the folio is that of the printed book (the arabic series loses the blank
// page 386).
#let source(n, printed: none) = context {
  let front = (
    "ii",
    "iii",
    "vii",
    "viii",
    "ix",
    "x",
    "xi",
    "xii",
    "xiii",
  )
  let folio = if printed != none { str(printed) } else if n <= 9 {
    front.at(n - 1)
  } else if n <= 394 { str(n - 9) } else { str(n - 8) }
  metadata((
    kind: "source",
    file-page: n,
    printed-page: folio,
    position: here().position(),
  ))
}

#let number-text(body) = text(weight: "semibold", style: "normal", body)

// A reference names its target by a native label. A supplement in
// parentheses, such as `@th:flat[(iv)]`, is a part of the cited statement
// and is printed inside its number: (2.21(iv)). Any other supplement is a
// descriptive reference and is printed as given.
// A part "(iv)", a range of parts "(i)–(iv)" or two parts "(ii), (iii)".
#let part-pattern = regex(
  "^\(([ivxl]+|[a-z]|[0-9]+)\)((–|, ?)\(([ivxl]+|[a-z]|[0-9]+)\))?$",
)
#let plain-text(body) = {
  if type(body) == str { return body }
  if type(body) != content { return "" }
  if body.has("text") { return body.text }
  if body.has("children") { return body.children.map(plain-text).join() }
  if body.has("child") { return plain-text(body.child) }
  if body.has("body") { return plain-text(body.body) }
  ""
}

#let reference-body(it, caption) = context {
  let target = str(it.target)
  let prefix = target.split(":").first()
  if prefix == "bib" {
    metadata((kind: "bibliographic-mention", target: target))
  }
  let supplement = if caption { plain-text(it.supplement).trim() } else { "" }
  let part = if caption and supplement.match(part-pattern) != none {
    supplement
  }
  // `@th:…[Theorem]` names the object as the book sometimes does,
  // "Theorem 2.6", without the parentheses of "(2.6)".
  let named = (
    caption
      and supplement
        in (
          "Theorem",
          "Lemma",
          "Corollary",
          "Proposition",
          "Definition",
          "Remark",
          "Example",
          "Formula",
        )
  )
  let item = if it.element != none { numbered-record(it.target) }
  let number = if item != none { record-number(item) }
  let unnumbered = item != none and item.value.kind == "unnumbered"
  let pending = item == none
  let printed = if pending { "?" } else if unnumbered {
    item.value.name
  } else if prefix == "case" {
    let format = item.value.at("number-format", default: "(1)")
    numbering(format.trim(".", at: end, repeat: false), ..number)
  } else if prefix in ("ch", "sec") {
    str(number.first())
  } else if prefix == "bib" {
    str(number.last())
  } else if prefix == "ss" {
    str(number.first()) + str(number.last())
  } else if (
    prefix == "exc" and number.first() == section-counter.get().first()
  ) {
    // Within its own section an exercise is cited by its number alone.
    str(number.last())
  } else {
    number.map(str).join(".") + item.value.at("suffix", default: "")
  }
  let bracketed = (
    prefix
      in (
        "eq",
        "th",
        "lem",
        "prop",
        "cor",
        "def",
        "rem",
        "exm",
      )
  )
  let body = if named { [#supplement~#number-text(printed)] } else if (
    caption and part == none
  ) { it.supplement } else if unnumbered {
    printed
  } else if bracketed {
    [(#number-text(printed)#if part != none { it.supplement })]
  } else if part != none {
    [#number-text(printed)#it.supplement]
  } else { number-text(printed) }
  let destination = if pending { none } else if (
    it.element.func() == math.equation
  ) {
    it.element.location()
  } else { item.location() }
  // `page~@…[page]` gives the page of the object in this edition, as in
  // "see page 55".
  if caption and supplement == "page" and not pending {
    body = str(counter(page).at(destination).first())
  }
  metadata((
    kind: "cross-reference",
    target: target,
    resolved: not pending,
    printed: printed,
    position: here().position(),
    target-position: if not pending { destination.position() },
  ))
  if pending { body } else { link(destination, body) }
}

#let reference-rules(body) = {
  show ref: it => {
    let caption = it.supplement not in (auto, none, [])
    // The text font also inside a formula ("by (9.12)" in a chain of
    // equalities), so that the number is semibold as everywhere else.
    let shown = text(font: "Libertinus Serif", reference-body(it, caption))
    // A reference stays on one line: a number, also with a part "(2.8(i))"
    // or a name "Theorem 2.6", and a descriptive one ("Nakayama's Lemma").
    // The box also fixes the position recorded by `reference-body`: an
    // unboxed one in a short paragraph kept with the next display does not
    // converge.
    box(shown)
  }
  body
}

#let idx(target: none, ..path) = {
  assert(path.named().len() == 0 and path.pos().len() > 0)
  let refs(body) = {
    if body.func() == ref { (body.target,) } else if body.has("children") {
      body.children.map(refs).flatten()
    } else if body.has("body") { refs(body.body) } else { () }
  }
  let destination = if target == none { () } else { refs(target) }
  assert(
    target == none or destination.len() == 1,
    message: "An index target must contain one native reference",
  )
  let value = (kind: "index-mark", path: path.pos())
  if target != none { value.insert("target", str(destination.first())) }
  [#metadata(value)<index-mark>]
}

#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = if editorial-notes {
  editorial-note-counter.step()
  context {
    let mark = "*" + str(editorial-note-counter.get().first())
    footnote(numbering: _ => mark)[#body~—~_Ed._]
    counter(footnote).update(n => n - 1)
  }
}

// Operators and names of the book. Multi-word names keep the author's
// abbreviation points: char. pol., min. pol., red. char. pol.
#let Hom = math.op("Hom")
#let cok = math.op("cok")
#let End = math.op("End")
#let Aut = math.op("Aut")
#let Ext = math.op("Ext")
#let Tor = math.op("Tor")
#let Gal = math.op("Gal")
#let Cl = math.op("Cl")
#let ann = math.op("ann")
#let rad = math.op("rad")
#let card = math.op("card")
// The category of abelian groups.
#let Ab = math.cal("Ab")
#let diag = math.op("diag")
#let tr = math.op("tr")
#let nr = math.op("nr")
#let ord = math.op("ord")
#let rank = math.op("rank")
#let disc = math.op("disc")
#let hd = math.op("hd")
#let charpol = math.op("char. pol.")
#let minpol = math.op("min. pol.")
#let redcharpol = math.op("red. char. pol.")
#let lcm = math.op("L.C.M.")
#let GL = math.class("normal", math.upright("GL"))
#let SL = math.class("normal", math.upright("SL"))
// The external direct sum: a summation sign with a dot, and the dotted plus.
#let dsum = math.limits(math.attach(sym.sum, tr: sym.dot.c), inline: false)
#let dotplus = math.class("binary", sym.plus.dot)
// The genus relation "M v N" (§27), a roman v as printed.
#let samegenus = math.class("relation", math.upright("v"))
// A pair of maps in opposite directions inside a line of text, "A ⇄ B" with
// the label of the upper arrow above it and that of the lower one below.
#let lrmaps(top, bottom) = math.class(
  "relation",
  math.attach(
    math.limits(sym.arrows.rl),
    t: top,
    b: bottom,
  ),
)
// A module written with its ring on the left: ${}_Lambda M$.
#let lmodule(ring, module) = math.attach(module, bl: ring)
// Upright bold letters, as the number systems Z, Q, R, C, H are printed.
#let bold(body) = math.upright(math.bold(body))
// Bold italic, as the matrix of a form is printed: bolditalic(tau).
#let bolditalic(body) = math.bold(body)
#let algint = math.op("alg. int.")
// The works inside a cited range, "Harada [1–5]": invisible mentions for
// the page lists of the bibliography.
#let bib-mentions(..keys) = for key in keys.pos() {
  metadata((kind: "bibliographic-mention", target: str(key)))
}
#let index = math.op("index")
#let res = math.op("res")
#let inv = math.op("inv")
#let Pic = math.op("Pic")
#let Picent = math.op("Picent")
#let Outcent = math.op("Outcent")
// "A = Eichler/R" (§34): the word in the text font and the style of the
// surrounding text, italic in a statement.
#let eichler(ring) = math.class("normal", context text(
  font: "Libertinus Serif",
  style: text.style,
  [Eichler/#box($ring$)],
))
#let Out = math.op("Out")
#let In = math.op("In")
#let Autcent = math.op("Autcent")
#let LFP = math.italic("LFP")
// The sign of a normal subgroup, a small triangle as printed: "H ▵ G".
#let normal = math.class("relation", sym.triangle.stroked.small.t)

// The date and the signature closing a preface.
#let signature(date, name) = block(above: 1.2em, grid(
  columns: (1fr, auto),
  emph(date), name,
))

#let editorial-bibliography = context if (
  editorial-notes and query(cite).len() > 0
) {
  bibliography("../editorial.bib", title: [Editorial references])
}
