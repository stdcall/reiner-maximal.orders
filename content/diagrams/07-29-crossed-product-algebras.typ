#import "common.typ": cd, edge, node

// A field diagram with its description (`side`) to the right, both centered
// vertically, as in the proofs of (29.13) and (29.16).
#let with-side(picture, side) = grid(
  columns: 2,
  column-gutter: 12mm,
  align: horizon,
  picture, side,
)

// Proof of (29.13): the composite EL of E and L over F = E ∩ L, above K, with
// the description of the galois groups to the right of L and E.
#let composite-fields(side) = with-side(
  cd(
    spacing: (5mm, 4mm),
    node((1, 0), $E L$),
    node((0, 1), $L$),
    node((2, 1), $E$),
    node((1, 2), $F$),
    node((1, 3), $K$),
    edge((1, 0), (0, 1)),
    edge((1, 0), (2, 1)),
    edge((0, 1), (1, 2)),
    edge((2, 1), (1, 2)),
    edge((1, 2), (1, 3)),
  ),
  side,
)

// Proof of (29.16): the tower K ⊂ L ⊂ E with the degrees r, s on the right;
// on the left, bars mark the groups G (whole tower), H (from E to L, solid)
// and Ḡ (from L to K, dashed). The definitions stand to the right.
#let inflation-tower(side) = with-side(
  cd(
    spacing: (5mm, 4.5mm),
    node((0, 1), $G$),
    node((2, 0.5), $H$),
    node((2, 1.5), $overline(G)$),
    node((4, 0), $E$),
    node((4, 1), $L$),
    node((4, 2), $K$),
    edge((1, -0.2), (1, 2.2)),
    edge((3, -0.2), (3, 0.95)),
    edge((3, 1.05), (3, 2.2), "--"),
    edge((4, 0), (4, 1), $r$, label-side: left),
    edge((4, 1), (4, 2), $s$, label-side: left),
  ),
  side,
)

// Proof of (29.24): the fields K ⊂ E ⊂ L with a Sylow p-subgroup H of G,
// the algebras S = E ⊗_K D and D beside E and K, and the dimensions. Dashed
// bars mark G (whole tower) and H (from L to E).
#let sylow-fields = cd(
  spacing: (6mm, 7mm),
  node((0, 1.2), $G$),
  node((2, 0.5), $H$),
  node((4, 0), $L$),
  node((4, 1), $E$),
  node((4, 2.4), $K$),
  node((5.5, 0.4), $S$),
  node((5.5, 1.8), $D$),
  edge((1, -0.2), (1, 2.6), "--"),
  edge((3, -0.2), (3, 1.1), "--"),
  edge((4, 0), (4, 1), $p^r$, label-side: right, label-size: 0.7em),
  edge((4, 1), (4, 2.4), $q$, label-side: right, label-size: 0.7em),
  edge((4, 1), (5.5, 0.4), $m^2$, label-side: left, label-size: 0.7em),
  edge((4, 2.4), (5.5, 1.8), $m^2$, label-side: left, label-size: 0.7em),
  edge((5.5, 0.4), (5.5, 1.8)),
)
