#import "common.typ": cd, edge, node

// Exercise 40.2(iv): naturality of the evaluation maps φ_M, φ_N. As printed,
// the labels of both rows stand above their arrows and those of the vertical
// maps on their left.
#let evaluation-square = cd(
  spacing: (14mm, 12mm),
  node((0, 0), $M$),
  node((1, 0), $N$),
  node((0, 1), $M^(**)$),
  node((1, 1), $N^(**),$),
  edge((0, 0), (1, 0), $f$, "->", label-side: left),
  edge((0, 1), (1, 1), $f^(**)$, "->", label-side: left),
  edge((0, 0), (0, 1), $phi_M$, "->", label-side: right),
  edge((1, 0), (1, 1), $phi_N$, "->", label-side: right),
)
