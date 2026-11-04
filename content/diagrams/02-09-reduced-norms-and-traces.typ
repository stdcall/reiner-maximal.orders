#import "common.typ": cd, edge, node

// The map h' of (9.3), defined by the commutativity of the square: dashed.
#let conjugate-splitting = cd(
  spacing: (10mm, 9mm),
  node((0, 0), $E times.o_K A$),
  node((1, 0), $E' times.o_K A$),
  node((0, 1), $M_n (E)$),
  node((1, 1), $M_n (E').$),
  edge((0, 0), (1, 0), $f times.o 1$, "->", label-side: left),
  edge((0, 1), (1, 1), $f^*$, "->", label-side: left),
  edge((0, 0), (0, 1), $h$, "->", label-side: right),
  edge((1, 0), (1, 1), $h'$, "-->", label-side: right),
)
