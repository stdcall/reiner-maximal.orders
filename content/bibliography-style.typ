#import "bibliography-data.typ": bibliography-data
#import "statements.typ": bib-group as reset-bib-group

// The book's References: works grouped under their authors, "Albert, A. A.",
// numbered within a group. Every description is generated from
// references.bib.
//
// annotation preserves the original compound punctuation, substituting
// {title}, {pages}, etc. from this record and {Key.pages} from a related
// component. As printed, titles are roman (a book title is quoted in the
// template), the journal is in italics with a series number such as "(2)"
// in roman, and the volume of a journal is bold. {journal} prints the
// verified abbreviation shortjournal; userb holds an original journal
// spelling, printed where shortjournal has not been verified. userc names
// the part associated with a DOI. `_..._` is italics, `$...$` mathematics.
#let rich-bib-text(value) = {
  // An abbreviation stays with the number or word after it: "No. 143".
  let value = value
    .replace("'", "’")
    .replace("--", "–")
    .replace(
      regex("\\b(No|Ch|Vol|pp|ed)\\. "),
      m => m.text.slice(0, -1) + "\u{00a0}",
    )
  let position = 0
  for match in value.matches(
    regex("_[^_]+_|\\$[^$]+\\$|[A-Z][₀₁₂₃₄₅₆₇₈₉]+"),
  ) {
    value.slice(position, match.start)
    let part = match.text
    if part.starts-with("_") {
      emph(part.slice(1, -1))
    } else if part.starts-with("$") {
      eval(part, mode: "markup")
    } else {
      let digits = "₀₁₂₃₄₅₆₇₈₉".clusters()
      let subscript = part
        .slice(1)
        .clusters()
        .map(c => str(digits.position(d => d == c)))
        .join()
      eval("$" + part.first() + "_" + subscript + "$", mode: "markup")
    }
    position = match.end
  }
  value.slice(position)
}
// A journal in italics; its series number stays roman: "Ann. of Math. (2)".
#let journal-name(value) = {
  let series = value.match(regex("^(.*\\S) (\\([0-9]+\\))$"))
  if series == none { emph(rich-bib-text(value)) } else {
    [#emph(rich-bib-text(series.captures.first())) #series.captures.last()]
  }
}
// Names as in a group heading: the surname in small capitals, then the
// initials, "Artin, E., Nesbitt, C. J., Thrall, R. M.".
#let print-names(value) = {
  value
    .split(" and ")
    .map(name => {
      let (surname, ..given) = name.replace("'", "’").split(", ")
      if given.len() == 0 { smallcaps(surname) } else {
        [#smallcaps(surname), #given.join(", ")]
      }
    })
    .join(", ")
}
#let bib-group(key) = context {
  let entry = bibliography-data.at(key)
  let shown = print-names(entry.author)
  if "nameaddon" in entry { shown += ", " + entry.nameaddon }
  // The book sets the group heading in the size and weight of the text.
  // The unnumbered level-2 heading is larger and in bold: an explicit size
  // and weight replace the heading's, and a negative `strong` delta cancels
  // the strong of its show rule (deltas add up).
  let size = text.size
  reset-bib-group(strong(delta: -300, text(
    size: size,
    weight: "regular",
    shown,
  )))
}
#let bib-backlinks(target) = context {
  let refs = query(metadata.where(value: (
    kind: "bibliographic-mention",
    target: target,
  ))).filter(mention => {
    let loc = mention.location()
    let enters = query(
      selector(metadata.where(value: (
        kind: "bibliography-boundary",
        enter: true,
      ))).before(loc),
    ).len()
    let exits = query(
      selector(metadata.where(value: (
        kind: "bibliography-boundary",
        enter: false,
      ))).before(loc),
    ).len()
    enters <= exits
  })
  let seen = ()
  let pages = ()
  for mention in refs {
    let loc = mention.location()
    if not seen.contains(loc.page()) {
      seen.push(loc.page())
      let position = loc.position()
      let destination = (
        page: position.page,
        x: position.x,
        y: calc.max(0pt, position.y - 8pt),
      )
      let pattern = loc.page-numbering()
      let folio = counter(page).at(loc)
      let shown = if pattern == none { str(folio.first()) } else {
        numbering(pattern, ..folio)
      }
      pages.push(box({
        metadata((
          kind: "page-reference",
          resolved: true,
          target: "bib-mention:" + target,
          target-position: position,
          // Typst adds 10pt above the coordinate destination as well.
          destination-offset-pt: 18,
          description: shown,
        ))
        link(destination, shown)
      }))
    }
  }
  if pages.len() > 0 { [ #text(size: 9pt)[\[#pages.join(", ")\]]] }
}
#let background-reading(body) = block(inset: (left: 1em), body)

#let bib-description(key) = {
  let entry = bibliography-data.at(key)
  let template = entry
    .annotation
    .split("\"")
    .enumerate()
    .map(pair => {
      let (i, part) = pair
      if i == 0 { part } else {
        (if calc.odd(i) { "“" } else { "”" }) + part
      }
    })
    .join()
  let position = 0
  for match in template.matches(regex("\\{([^{}]+)\\}")) {
    rich-bib-text(template.slice(position, match.start))
    let token = match.captures.first().split(".")
    let data = if token.len() == 1 { entry } else {
      assert(
        token.first() in entry.at("related", default: "").split(","),
        message: "Template references an unrelated bibliography record",
      )
      bibliography-data.at(token.first())
    }
    let field = token.last()
    assert(field in data, message: "No field " + field + " in " + key)
    if field == "journal" {
      journal-name(data.at("shortjournal", default: data.at(
        "userb",
        default: data.journal,
      )))
    } else if field == "volume" and "journal" in data {
      strong(rich-bib-text(data.volume))
    } else {
      rich-bib-text(data.at(field))
    }
    position = match.end
  }
  rich-bib-text(template.slice(position))
  if entry.at("language", default: none) == "russian" { [ (Russian).] }
  // The DOIs of the work and of its related parts, separated by semicolons.
  let dois = ()
  for component in (
    (key,) + entry.at("related", default: "").split(",").filter(k => k != "")
  ) {
    let record = bibliography-data.at(component)
    if "doi" in record {
      let part = if "userc" in record { " (" + record.userc + ")" } else { "" }
      dois.push(link(
        "https://doi.org/" + record.doi,
        "DOI" + part + ": " + record.doi,
      ))
    }
  }
  if dois.len() > 0 [ #dois.join("; ")]
  bib-backlinks("bib:" + key)
}
