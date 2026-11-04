#import "common.typ": cd, edge, node
#import "../main-defs.typ": dotplus

// A commutative triangle: a map followed by a vertical map, and their
// composite along the diagonal.
#let triangle(source, middle, target, top, side, diagonal) = cd(
  cell-size: (15mm, 12mm),
  node((0, 0), source),
  node((1, 0), middle),
  node((1, 1), target),
  edge((0, 0), (1, 0), top, "->"),
  edge((1, 0), (1, 1), side, "->", label-side: left),
  edge((0, 0), (1, 1), diagonal, "->", label-side: right),
)

// The defining triangles of f_* and f^*, (2.3).
#let induced-covariant = triangle(
  $X$,
  $L$,
  $M,$,
  $phi$,
  $f$,
  $f_* phi$,
)
#let induced-contravariant = cd(
  cell-size: (15mm, 12mm),
  node((0, 0), $L$),
  node((0, 1), $M$),
  node((1, 1), $X.$),
  edge((0, 0), (0, 1), $f$, "->", label-side: right),
  edge((0, 1), (1, 1), $psi$, "->", label-side: right),
  edge((0, 0), (1, 1), $f^* psi$, "->", label-side: left),
)
#let induced-maps = grid(
  columns: 2,
  column-gutter: 2cm,
  align: bottom,
  induced-covariant, induced-contravariant,
)

// A commutative square: top row a -> b, bottom row c -> d, vertical maps on
// the left and right. Labels of the vertical maps face outwards; the label
// of the bottom row is below it.
#let square(a, b, c, d, top, left-map, right-map, bottom) = cd(
  spacing: (9mm, 8mm),
  node((0, 0), a),
  node((1, 0), b),
  node((0, 1), c),
  node((1, 1), d),
  edge((0, 0), (1, 0), top, "->"),
  edge((0, 0), (0, 1), left-map, "->", label-side: right),
  edge((1, 0), (1, 1), right-map, "->", label-side: left),
  edge((0, 1), (1, 1), bottom, "->", label-side: right),
)

// Lifting property of a projective module (2.14(iii)): P maps down to Y,
// the bottom row X -> Y -> 0 is exact, and the dashed h lifts f to X.
#let projective-lifting = cd(
  cell-size: (11mm, 16mm),
  node((1, 0), $P$),
  node((0, 1), $X$),
  node((1, 1), $Y$),
  node((2, 1), $0,$),
  edge((1, 0), (1, 1), $f$, "->", label-side: left),
  edge((1, 0), (0, 1), $h$, "-->", label-side: right),
  edge((0, 1), (1, 1), $g$, "->", label-side: right),
  edge((1, 1), (2, 1), "->"),
)

// The proof of (2.16): tensoring a monomorphism f with F = X ⊕ X'.
#let flat-summand = {
  let tensor(module, factor) = $#module times.o_Lambda #factor$
  let row(y, factor, last) = (
    node((0, y), tensor($F$, factor)),
    node((1, y), $tilde.equiv$),
    node((2, y), tensor($X$, factor)),
    node((3, y), $dotplus$),
    node((4, y), tensor($X'$, last)),
  )
  cd(
    cell-size: (6mm, 12mm),
    ..row(0, $L$, $L$),
    ..row(1, $M$, $M.$),
    edge((0, 0), (0, 1), $1_F times.o f$, "->", label-side: left),
    edge((2, 0), (2, 1), $1_X times.o f$, "->", label-side: left),
    edge((4, 0), (4, 1), $1_(X') times.o f$, "->", label-side: left),
  )
}
