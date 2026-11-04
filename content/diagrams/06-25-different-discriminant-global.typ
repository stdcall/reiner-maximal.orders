#import "common.typ": cd, edge, node

// Step 5 of the proof of (25.4): the fields K ⊂ L ⊂ D with the rings
// R ⊂ S ⊂ Δ beside them, and the residue tower R̄ ⊂ S̄ ⊂ C ⊂ Δ̄. The degrees
// are printed small beside the lines; C lies halfway between Δ̄ and S̄.
#let residue-towers = cd(
  spacing: (8mm, 11mm),
  node((0, 0), $D$),
  node((1, 0), $Delta$),
  node((0, 1), $L$),
  node((1, 1), $S$),
  node((0, 2), $K$),
  node((1, 2), $R$),
  node((2.5, 0), $overline(Delta)$),
  node((2.5, 0.5), $C$),
  node((2.5, 1), $overline(S)$),
  node((2.5, 2), $overline(R)$),
  edge((0, 0), (1, 0)),
  edge((0, 1), (1, 1)),
  edge((0, 2), (1, 2)),
  edge((0, 0), (0, 1), $n^2$, label-side: right, label-size: 0.7em),
  edge((0, 1), (0, 2), $k$, label-side: right, label-size: 0.7em),
  edge((1, 0), (1, 1)),
  edge((1, 1), (1, 2)),
  edge((2.5, 0), (2.5, 0.5), $m^2$, label-side: left, label-size: 0.7em),
  edge((2.5, 0.5), (2.5, 1), $t^2$, label-side: left, label-size: 0.7em),
  edge((2.5, 1), (2.5, 2), $k$, label-side: left, label-size: 0.7em),
)
