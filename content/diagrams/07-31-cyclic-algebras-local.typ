#import "common.typ": cd, edge, node
#import "../main-defs.typ": bold, inv

// (31.9): the Hasse invariants of K and of a finite extension E of K. The
// labels of the horizontal maps are above them; the left vertical map is
// labelled on its left, the right one on its right.
#let invariant-square = cd(
  spacing: (14mm, 11mm),
  node((0, 0), $B(K)$),
  node((1, 0), $bold(Q) slash bold(Z)$),
  node((0, 1), $B(E)$),
  node((1, 1), $bold(Q) slash bold(Z),$),
  edge((0, 0), (1, 0), $inv_K$, "->", label-side: left),
  edge((0, 1), (1, 1), $inv_E$, "->", label-side: left),
  edge((0, 0), (0, 1), $E times.o_K$, "->", label-side: right),
  edge((1, 0), (1, 1), $(E : K)$, "->", label-side: left),
)

// Proof of (31.9): the composite E W over the intersection F = E ∩ W, with
// the degrees m' of W/F and E W/E and k of F/K beside the lines. The lines
// meet at F; "= E ∩ W" follows F as in a formula, outside the lattice.
#let composite-lattice = context {
  // Centre of "= E ∩ W" relative to that of F in the formula F = E ∩ W.
  let whole = measure($F = E inter W$).width
  let tail = measure($= E inter W$).width
  let shift = whole - tail / 2 - measure($F$).width / 2
  cd(
    spacing: (7mm, 9mm),
    node((1, 0), $E dot W$),
    node((0, 1), $W$),
    node((2, 1), $E$),
    node((1, 2), $F$),
    node((rel: (shift, 0pt), to: (1, 2)), $= E inter W$),
    node((1, 3), $K$),
    edge((1, 0), (0, 1)),
    edge((1, 0), (2, 1), $m'$, label-side: left, label-size: 0.7em),
    edge((0, 1), (1, 2), $m'$, label-side: right, label-size: 0.7em),
    edge((2, 1), (1, 2)),
    edge((1, 2), (1, 3), $k$, label-side: right, label-size: 0.7em),
  )
}

// The lattice with the facts it illustrates printed to its right, the pair
// centred on the line like a display.
#let beside(lattice, facts) = block(width: 100%, align(center, grid(
  columns: 2,
  column-gutter: 4em,
  align: horizon,
  lattice, facts,
)))

// The lattice of fields of Exercise 31.1, without degrees.
#let field-lattice = cd(
  spacing: (6mm, 7mm),
  node((1, 0), $E dot W$),
  node((0, 1), $W$),
  node((2, 1), $E$),
  node((1, 2), $F$),
  node((1, 3), $K$),
  edge((1, 0), (0, 1)),
  edge((1, 0), (2, 1)),
  edge((0, 1), (1, 2)),
  edge((2, 1), (1, 2)),
  edge((1, 2), (1, 3)),
)

// Proof of (31.12): the exact row 1 -> B(E/K) -> B(K) -> B(E) over the
// invariant maps; the bottom map, multiplication by n, is labelled below it.
// The labels of the vertical maps stand on their right.
#let relative-brauer-diagram = cd(
  spacing: (7mm, 9mm),
  node((0, 0), $1$),
  node((1, 0), $B(E slash K)$),
  node((2, 0), $B(K)$),
  node((3, 0), $B(E)$),
  node((2, 1), $bold(Q) slash bold(Z)$),
  node((3, 1), $bold(Q) slash bold(Z),$),
  edge((0, 0), (1, 0), "->"),
  edge((1, 0), (2, 0), "->"),
  edge((2, 0), (3, 0), "->"),
  edge((2, 0), (2, 1), $inv_K$, "->", label-side: left),
  edge((3, 0), (3, 1), $inv_E$, "->", label-side: left),
  edge((2, 1), (3, 1), $n$, "->", label-side: right),
)

// Hint to Exercise 31.3: the relative Brauer groups of K ⊂ E ⊂ F over their
// groups of invariants. The labels of the vertical maps stand on their
// right; the map multiplying by n is labelled below the bottom row.
#let relative-brauer-ladder = cd(
  spacing: (6mm, 9mm),
  node((0, 0), $1$),
  node((1, 0), $B(E slash K)$),
  node((2, 0), $B(F slash K)$),
  node((3, 0), $B(F slash E)$),
  node((4, 0), $1$),
  node((0, 1), $1$),
  node((1, 1), $1/n bold(Z) slash bold(Z)$),
  node((2, 1), $1/(m n) bold(Z) slash bold(Z)$),
  node((3, 1), $1/m bold(Z) slash bold(Z)$),
  node((4, 1), $1.$),
  edge((0, 0), (1, 0), "->"),
  edge((1, 0), (2, 0), "->"),
  edge((2, 0), (3, 0), "->"),
  edge((3, 0), (4, 0), "->"),
  edge((0, 1), (1, 1), "->"),
  edge((1, 1), (2, 1), "->"),
  edge((2, 1), (3, 1), $n$, "->", label-side: right),
  edge((3, 1), (4, 1), "->"),
  edge((1, 0), (1, 1), $inv_K$, "->", label-side: left),
  edge((2, 0), (2, 1), $inv_K$, "->", label-side: left),
  edge((3, 0), (3, 1), $inv_E$, "->", label-side: left),
)
