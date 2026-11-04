#import "common.typ": cd, edge, node
#import "../main-defs.typ": (
  Aut, Autcent, Cl, In, Out, Outcent, Pic, Picent, bold,
)

// (37.3): the two squares expressing the associativity of the isomorphisms
// (37.2), side by side (the empty column 2 separates them); no map is
// labelled.
#let invertibility-squares = {
  let squares = (
    (
      $M times.o_Delta N times.o_Lambda M$,
      $Lambda times.o_Lambda M$,
      $M times.o_Delta Delta$,
      $M,$,
    ),
    (
      $N times.o_Lambda M times.o_Delta N$,
      $Delta times.o_Delta N$,
      $N times.o_Lambda Lambda$,
      $N.$,
    ),
  )
  let items = ()
  for (i, (a, b, c, d)) in squares.enumerate() {
    let x = 3 * i
    items += (
      node((x, 0), a),
      node((x + 1, 0), b),
      node((x, 1), c),
      node((x + 1, 1), d),
      edge((x, 0), (x + 1, 0), "->"),
      edge((x, 1), (x + 1, 1), "->"),
      edge((x, 0), (x, 1), "->"),
      edge((x + 1, 0), (x + 1, 1), "->"),
    )
  }
  cd(spacing: (6mm, 11mm), ..items)
}

// (37.25): ρ along the top, ω down on the right, ω′ along the diagonal; the
// labels of ω and ω′ stand on the left of their arrows, as printed.
#let normalizer-triangle = cd(
  spacing: (10mm, 11mm),
  node((0, 0), $N(Lambda) slash u(Lambda) thin u(K C)$),
  node((1, 0), $Outcent Lambda$),
  node((1, 1), $Picent Lambda,$),
  edge((0, 0), (1, 0), $rho$, "->", label-side: left),
  edge((1, 0), (1, 1), $omega$, "->", label-side: right),
  edge((0, 0), (1, 1), $omega'$, "->", label-side: right),
)

// Two rows of groups joined by vertical maps. As printed in this section, the
// labels of both rows stand above their arrows and those of the vertical maps
// on their left. `none` leaves a place of a row, an arrow of a row or a
// vertical map empty; `[]` is an unlabelled arrow.
#let ladder-above(
  top,
  bottom,
  down,
  top-maps: none,
  bottom-maps: none,
  gap: 5mm,
  row: 11mm,
) = {
  let top-maps = if top-maps == none {
    range(top.len() - 1).map(_ => [])
  } else {
    top-maps
  }
  let bottom-maps = if bottom-maps == none {
    range(bottom.len() - 1).map(_ => [])
  } else { bottom-maps }
  let items = ()
  for (x, object) in top.enumerate() {
    if object != none { items.push(node((x, 0), object)) }
  }
  for (x, object) in bottom.enumerate() {
    if object != none { items.push(node((x, 1), object)) }
  }
  for (x, label) in top-maps.enumerate() {
    if label != none {
      items.push(edge((x, 0), (x + 1, 0), label, "->", label-side: left))
    }
  }
  for (x, label) in bottom-maps.enumerate() {
    if label != none {
      items.push(edge((x, 1), (x + 1, 1), label, "->", label-side: left))
    }
  }
  for (x, label) in down.enumerate() {
    if label != none {
      items.push(edge((x, 0), (x, 1), label, "->", label-side: right))
    }
  }
  cd(spacing: (gap, row), ..items)
}

// (37.37): the exact sequences of (37.34) for Λ and for Γ = M_n (Λ).
#let picent-class-ladder = ladder-above(
  ($1$, $Outcent Lambda$, $Picent Lambda$, $Cl Lambda$),
  ($1$, $Outcent Gamma$, $Picent Gamma$, $Cl Gamma,$),
  (none, $alpha$, $beta$, $gamma$),
  top-maps: ([], $omega$, $theta$),
  bottom-maps: ([], $omega'$, $theta'$),
)

// Proof of (37.36 iii): the square of θ, θ′ with β and γ, to which the Snake
// Lemma is applied.
#let snake-ladder = ladder-above(
  (none, $1$, $Picent Lambda$, $Picent Gamma$, $1.$),
  ($0$, $ker gamma$, $Cl Lambda$, $Cl Gamma$, none),
  (none, [], $theta$, $theta'$, none),
  top-maps: (none, [], $beta$, []),
  bottom-maps: ([], [], $gamma$, none),
)

// Exercise 37.5: the outer automorphism groups mapped into the Picard groups.
#let out-pic-ladder = ladder-above(
  ($1$, $Out_C Lambda$, $Out_R Lambda$, $Aut_R C$),
  ($1$, $Picent Lambda$, $Pic_R Lambda$, $Aut_R C.$),
  (none, $omega$, $omega'$, $1$),
  bottom-maps: ([], [], $Phi$),
  row: 9mm,
)

// Exercise 37.15: the sequence (37.33) over the isomorphism Cl_A R ≅ Cl Λ.
#let class-group-ladder = ladder-above(
  (
    $1$,
    $Cl R$,
    $Picent Lambda$,
    $limits(product)_P bold(Z) slash m_P bold(Z)$,
    $1$,
  ),
  ($1$, $Cl_A R$, $Cl Lambda$, $1$, none),
  (none, $t_n$, $theta$, [], none),
  bottom-maps: ([], [], [], none),
  row: 9mm,
)

// Hint to Exercise 37.4: the maps ψ₁, ψ₂, ψ₃ along the top, and η, η′ down
// from the third and fourth terms, labelled on the right as printed.
#let azumaya-maps = {
  let pic = $Pic_R Lambda$
  let opp = $E^circle.stroked.tiny$
  cd(
    spacing: (7mm, 9mm),
    node((0, 0), pic),
    node((1, 0), $pic times.o E$),
    node((2, 0), $pic times.o E times.o opp$),
    node((3, 0), $pic times.o E times.o opp times.o E$),
    node((2, 1), pic),
    node((3, 1), $pic times.o E.$),
    edge((0, 0), (1, 0), $psi_1$, "->", label-side: left),
    edge((1, 0), (2, 0), $psi_2$, "->", label-side: left),
    edge((2, 0), (3, 0), $psi_3$, "->", label-side: left),
    edge((2, 1), (3, 1), $psi_1$, "->", label-side: left),
    edge((2, 0), (2, 1), $eta$, "->", label-side: left),
    edge((3, 0), (3, 1), $eta'$, "->", label-side: left),
  )
}
