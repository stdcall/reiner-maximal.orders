#import "common.typ": cd, edge, node

// A commutative square: top row a -> b, bottom row c -> d. As printed in this
// chapter, the labels of both vertical maps stand on their left. The label of
// the bottom map stands above it, or below it with `bottom-below: true`.
#let left-labelled-square(
  a,
  b,
  c,
  d,
  top,
  bottom,
  left-map,
  right-map,
  bottom-below: false,
) = cd(
  spacing: (12mm, 9mm),
  node((0, 0), a),
  node((1, 0), b),
  node((0, 1), c),
  node((1, 1), d),
  edge((0, 0), (1, 0), top, "->", label-side: left),
  edge(
    (0, 1),
    (1, 1),
    bottom,
    "->",
    label-side: if bottom-below { right } else { left },
  ),
  edge((0, 0), (0, 1), left-map, "->", label-side: right),
  edge((1, 0), (1, 1), right-map, "->", label-side: right),
)

// A pair of maps in opposite directions between two objects, the first
// labelled above, the second below.
#let arrow-pair(source, target, forward, backward) = cd(
  spacing: (12mm, 0mm),
  node((0, 0), source),
  node((1, 0), target),
  edge((0, 0), (1, 0), forward, "->", shift: 2pt, label-side: left),
  edge((1, 0), (0, 0), backward, "->", shift: 2pt, label-side: left),
)
