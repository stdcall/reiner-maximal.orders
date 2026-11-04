#import "common.typ": cd, edge, node
#import "../main-defs.typ": Cl, bold

// (36.7): the exact sequences (36.4) for Λ and for Γ ≅ M_n(Λ), joined by φ
// and by the maps induced by the Morita equivalences. As printed, the labels
// of both rows stand above their arrows and those of the vertical maps on
// their left.
#let k0-morita-ladder = {
  let top = ($0$, $Cl Lambda$, $K_0 (Lambda)$, $K_0 (A)$, $0$)
  let bottom = ($0$, $Cl Gamma$, $K_0 (Gamma)$, $K_0 (B)$, $0,$)
  let top-maps = ([], $mu$, $psi$, [])
  let bottom-maps = ([], $mu'$, $psi'$, [])
  let down = (none, $phi$, $L times.o_Lambda dot$, $V times.o_A dot$, none)
  let items = ()
  for (x, object) in top.enumerate() { items.push(node((x, 0), object)) }
  for (x, object) in bottom.enumerate() { items.push(node((x, 1), object)) }
  for (x, label) in top-maps.enumerate() {
    items.push(edge((x, 0), (x + 1, 0), label, "->", label-side: left))
  }
  for (x, label) in bottom-maps.enumerate() {
    items.push(edge((x, 1), (x + 1, 1), label, "->", label-side: left))
  }
  for (x, label) in down.enumerate() {
    if label != none {
      items.push(edge((x, 0), (x, 1), label, "->", label-side: right))
    }
  }
  cd(spacing: (7mm, 11mm), ..items)
}

// A commutative square whose horizontal maps are labelled above, as are both
// rows in (36.9); the left vertical map is labelled on its left, the right
// one on its right.
#let square-above(a, b, c, d, top, bottom, left-map, right-map) = cd(
  spacing: (8mm, 10mm),
  node((0, 0), a),
  node((1, 0), b),
  node((0, 1), c),
  node((1, 1), d),
  edge((0, 0), (1, 0), top, "->", label-side: left),
  edge((0, 1), (1, 1), bottom, "->", label-side: left),
  edge((0, 0), (0, 1), left-map, "->", label-side: right),
  edge((1, 0), (1, 1), right-map, "->", label-side: left),
)

// (36.9 i): the isomorphisms r_A and r_B with Z commute with V ⊗_A ·.
#let rank-square = square-above(
  $K_0 (A)$,
  $bold(Z)$,
  $K_0 (B)$,
  $bold(Z).$,
  $r_A$,
  $r_B$,
  $V times.o_A dot$,
  $1$,
)

// (36.10): the reduced norm isomorphisms ν, ν' onto the ray class group
// commute with φ.
#let norm-square = square-above(
  $Cl Lambda$,
  $Cl_A R$,
  $Cl Gamma$,
  $Cl_A R$,
  $nu$,
  $nu'$,
  $phi$,
  $1$,
)
