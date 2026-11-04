#import "common.typ": cd, edge, node

// Maps in opposite directions lifted from a pair of maps between reductions:
// the dashed lifts above, the reduction maps down.
#let lifted-pair(top, bottom, lifts, maps) = cd(
  spacing: (22mm, 14mm),
  node((0, 0), top.at(0)),
  node((1, 0), top.at(1)),
  node((0, 1), bottom.at(0)),
  node((1, 1), bottom.at(1)),
  edge((0, 0), (1, 0), lifts.at(0), "-->", shift: 3pt, label-side: left),
  edge((1, 0), (0, 0), lifts.at(1), "-->", shift: 3pt, label-side: left),
  edge((0, 1), (1, 1), maps.at(0), "->", shift: 3pt, label-side: left),
  edge((1, 1), (0, 1), maps.at(1), "->", shift: 3pt, label-side: left),
  edge((0, 0), (0, 1), "->"),
  edge((1, 0), (1, 1), "->"),
)

// Lifting the isomorphisms f̄, ḡ of (6.18).
#let lifted-isomorphism = lifted-pair(
  ($A e_1$, $A e_2$),
  ($overline(A) overline(e)_1$, $overline(A) overline(e)_2$),
  ($f$, $g$),
  ($overline(f)$, $overline(g)$),
)
