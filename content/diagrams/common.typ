// Commutative diagrams share the book's type and arrow style. Grid nodes
// and maps are supplied by each diagram; distinct arrowheads and dashed
// maps are specified at their edges.
#import "@preview/fletcher:0.5.8": diagram, edge, node

// `spacing` is the gap between neighbouring cells, each as wide as its
// widest node: wide nodes keep arrows of the same visible length.
#let cd(spacing: 0pt, node-inset: 1mm, ..args) = {
  set text(top-edge: "bounds", bottom-edge: "bounds")
  stack(diagram(
    spacing: spacing,
    node-shape: rect,
    node-inset: node-inset,
    edge-stroke: 0.45pt,
    label-size: 1em,
    label-sep: 0.25em,
    ..args,
  ))
}

// Two rows of maps joined by vertical maps, as in a morphism of exact
// sequences. `top` and `bottom` list the objects of the rows; `top-maps`
// and `bottom-maps` the labels of the arrows between consecutive objects
// (`[]` for an unlabelled arrow, `none` for no arrow); `down` the labels of
// the vertical maps under each column (`[]` unlabelled, `none` absent).
// Labels of the top row are above it, those of the bottom row below it, and
// those of the vertical maps on their left (`down-side: right`: on their
// right), as printed in the book.
// `dotted-down` and `dotted-bottom` list the columns or arrows printed dotted;
// `upward: true` turns the vertical maps upwards (a contravariant image).
// A wide ladder takes a smaller `gap` and node `inset` to fit the line.
#let ladder(
  top,
  bottom,
  down,
  top-maps: none,
  bottom-maps: none,
  dotted-down: (),
  dotted-bottom: (),
  upward: false,
  down-side: left,
  gap: 5mm,
  row: 9mm,
  inset: 1mm,
) = {
  let n = top.len()
  assert(bottom.len() == n and down.len() == n)
  let top-maps = if top-maps == none { range(n - 1).map(_ => []) } else {
    top-maps
  }
  let bottom-maps = if bottom-maps == none {
    range(n - 1).map(_ => [])
  } else { bottom-maps }
  let items = ()
  // `none` leaves a place of a row empty.
  for (x, object) in top.enumerate() {
    if object != none { items.push(node((x, 0), object)) }
  }
  for (x, object) in bottom.enumerate() {
    if object != none { items.push(node((x, 1), object)) }
  }
  for (x, label) in top-maps.enumerate() {
    if label != none { items.push(edge((x, 0), (x + 1, 0), label, "->")) }
  }
  for (x, label) in bottom-maps.enumerate() {
    if label != none {
      let style = if x in dotted-bottom { "..>" } else { "->" }
      items.push(edge((x, 1), (x + 1, 1), label, style, label-side: right))
    }
  }
  for (x, label) in down.enumerate() {
    if label != none {
      let style = if x in dotted-down { "..>" } else { "->" }
      // `down-side: right` prints the labels of the vertical maps on
      // their right, as some ladders of the book do.
      let side = if down-side == left { (left, right) } else { (right, left) }
      if upward {
        items.push(edge((x, 1), (x, 0), label, style, label-side: side.at(0)))
      } else {
        items.push(edge((x, 0), (x, 1), label, style, label-side: side.at(1)))
      }
    }
  }
  cd(spacing: (gap, row), node-inset: inset, ..items)
}
