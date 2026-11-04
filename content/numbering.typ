// Chapters and sections are arabic; sections run continuously through the
// book, subsections are lettered within a section (1a, 1b, ...).
// Statements and numbered displays share the series (section.item).
#let section-counter = counter("book-section")
#let item-counter = counter("book-item")
#let exercise-counter = counter("book-exercise")
#let bibliography-counter = counter("book-bibliography")
#let illustration-counter = counter("book-illustration")
#let remark-counter = counter("book-remark")
#let case-counter = counter("book-case")
#let case-number-format = state("case-number-format", "(1)")

// Called between a chapter's introduction and its first section. The
// heading counter keeps the continuous section series across chapters.
// The book numbers the displays of a chapter introduction in the series of
// the chapter's first section, "(17.1)" before the heading of §17:
// `#open-section()` at the start of such an introduction begins that series,
// and the next section heading continues it. The open series is kept in the
// counters themselves, so that the heading needs no contextual test: the
// section counter carries a second level 1, and the item counter is raised by
// `opened-items` (removed by `item-number`).
#let opened-items = 10000
#let item-number(value) = calc.rem(value, opened-items)
#let open-section() = {
  section-counter.update((..n) => (n.pos().first() + 1, 1))
  item-counter.update(opened-items)
  exercise-counter.update(0)
  illustration-counter.update(0)
  remark-counter.update(0)
}

#let continue-sections() = context {
  let numbers = section-counter.get()
  let section = numbers.first() - if numbers.len() > 1 { 1 } else { 0 }
  counter(heading).update((..numbers) => (numbers.pos().first(), section))
}

#let place-key(location) = (
  counter(heading).at(location).at(0, default: 0),
  section-counter.at(location).first(),
)

#let family-counter(family) = if family == "exc" {
  exercise-counter
} else if family == "case" { case-counter } else if family == "bib" {
  bibliography-counter
} else { item-counter }

#let restart-counters(level) = if level == 2 {
  section-counter.update((..n) => {
    let numbers = n.pos()
    if numbers.len() > 1 { (numbers.first(),) } else {
      (numbers.first() + 1,)
    }
  })
  item-counter.update(n => if n >= opened-items { n - opened-items } else {
    0
  })
  exercise-counter.update(0)
  illustration-counter.update(0)
  remark-counter.update(0)
}

#let object-number(family, location, tag: none, series: none) = {
  let own = if tag != none { tag } else {
    let counting = if series == "illustration" {
      illustration-counter
    } else if (
      series == "remark"
    ) { remark-counter } else {
      family-counter(family)
    }
    item-number(counting.at(location).first())
  }
  if family in ("bib", "case") { (own,) } else {
    (section-counter.at(location).first(), own)
  }
}

#let numbered-record(target) = {
  if query(target).len() != 1 { return none }
  query(selector(<numbered>).within(target)).at(0, default: none)
}

#let record-number(item) = {
  let value = item.value
  if value.kind in ("hint", "variant") { value.number } else if (
    value.kind == "unnumbered"
  ) {
    none
  } else if value.family == "heading" {
    if value.level == 1 {
      (counter(heading).at(item.location()).first(),)
    } else if value.level == 2 {
      (section-counter.at(item.location()).first(),)
    } else {
      (
        section-counter.at(item.location()).first(),
        numbering("a", counter(heading).at(item.location()).last()),
      )
    }
  } else {
    object-number(
      value.family,
      item.location(),
      tag: value.at("tag", default: none),
      series: value.at("series", default: none),
    )
  }
}

#let record(family, ..flags) = context [#metadata((
  kind: "numbered",
  family: family,
  ..flags.named(),
  number: object-number(
    family,
    here(),
    tag: flags.named().at("tag", default: none),
    series: flags.named().at("series", default: none),
  ),
))<numbered>]
