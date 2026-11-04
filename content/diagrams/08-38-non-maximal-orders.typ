#import "common.typ": cd, edge, node
#import "../main-defs.typ": Cl

// (38.6): the monomorphisms μ, μ' of the locally free class groups of Λ and
// of M_n(Λ) into K_0, joined by φ and by L ⊗_Λ ·. As printed, the labels of
// both rows stand above their arrows and those of the vertical maps on their
// left.
#let class-group-k0-square = cd(
  spacing: (5mm, 10mm),
  node((0, 0), $Cl Lambda$),
  node((1, 0), $K_0 (Lambda)$),
  node((0, 1), $Cl M_n (Lambda)$),
  node((1, 1), $K_0 (M_n (Lambda)),$),
  edge((0, 0), (1, 0), $mu$, "->", label-side: left),
  edge((0, 1), (1, 1), $mu'$, "->", label-side: left),
  edge((0, 0), (0, 1), $phi$, "->", label-side: right),
  edge((1, 0), (1, 1), $L times.o_Lambda dot$, "->", label-side: right),
)
