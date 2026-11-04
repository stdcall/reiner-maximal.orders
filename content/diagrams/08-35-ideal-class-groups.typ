#import "common.typ": cd, edge, node
#import "../main-defs.typ": Hom, dotplus

// Proof of (35.8): the R-isomorphisms of φ(X) and φ(Λ^(r)) with r copies of
// X and of Λ^(r), in two rows; the vertical arrows are the inclusions, from
// φ(X) and from the sum of the copies of X.
#let hom-inclusions = cd(
  spacing: (0pt, 7mm),
  node((0, 0), $phi(X)$),
  node((1, 0), $= Hom_Lambda (Lambda^((r)), X) tilde.equiv$),
  node((2, 0), $X dotplus dots.c dotplus X$),
  node((3, 0), [($r$ copies)]),
  node((0, 1), $phi(Lambda^((r)))$),
  node((1, 1), $= Hom_Lambda (Lambda^((r)), Lambda^((r))) tilde.equiv$),
  node((2, 1), $Lambda^((r)) dotplus dots.c dotplus Lambda^((r))$),
  node((3, 1), [($r$ copies),]),
  edge((0, 0), (0, 1), "->"),
  edge((2, 0), (2, 1), "->"),
)
