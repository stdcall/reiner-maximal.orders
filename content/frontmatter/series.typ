#import "../main-defs.typ": source

// The publisher's list of the series, facing the title page.
#let series-page() = {
  set page(header: none, footer: none)
  set par(justify: false, first-line-indent: 0pt)
  source(1)
  text(size: 11pt, tracking: 0.12em, weight: "semibold")[
    LONDON MATHEMATICAL SOCIETY MONOGRAPHS \
    NEW SERIES
  ]
  v(1mm)
  line(length: 100%, stroke: 0.4pt)
  v(-1mm)
  text(size: 9pt, style: "italic")[
    Previous volumes of the LMS Monographs were published by Academic Press, to
    whom all enquiries should be addressed. Volumes in the New Series will be
    published by Oxford University Press throughout the world.
  ]
  v(-1mm)
  line(length: 100%, stroke: 0.4pt)
  v(2mm)
  set text(size: 9.5pt)
  [NEW SERIES]
  set enum(indent: 0.6em, body-indent: 0.6em, spacing: 0.5em)
  set par(hanging-indent: 0.8em)
  enum(
    numbering: "1.",
    [_Diophantine inequalities_ R.~C.~Baker],
    [_The Schur multiplier_ Gregory Karpilovsky],
    [_Existentially closed groups_ Graham Higman and Elizabeth Scott],
    [_The asymptotic solution of linear differential systems_ M.~S.~P.~Eastham],
    [_The restricted Burnside problem_ Michael Vaughan-Lee],
    [_Pluripotential theory_ Maciej Klimek],
    [_Free Lie algebras_ Christophe Reutenauer],
    [_The restricted Burnside problem (2nd edition)_ Michael Vaughan-Lee],
    [_The geometry of topological stability_ Andrew du Plessis and Terry Wall],
    [_Spectral decompositions and analytic sheaves._ J.~Eschmeier and
      M.~Putinar],
    [_An atlas of Brauer characters_ C.~Jansen, K.~Lux, R.~Parker, and
      R.~Wilson],
    [_Fundamentals of semigroup theory_ John M.~Howie],
    [_Area, lattice points, and exponential sums_ M.~N.~Huxley],
    [_Super-real fields_ H.~Garth Dales and W.~Hugh Woodin],
    [_Integrability, self-duality and twistor theory_ L.~J.~Mason and
      N.~M.~J.~Woodhouse],
    [_Categories of symmetries and infinite-dimensional groups_ Yu.~A.~Neretin],
    [_Interpolation, identification, and sampling_ Jonathan R.~Partington],
    [_Metric number theory_ Glyn Harman],
    [_Profinite groups_ John S.~Wilson],
    [_An introduction to local spectral theory_ Kjeld B.~Laursen and Michael
      M.~Neumann],
    [_Characters of finite Coxeter groups and Iwahori-Hecke algebras_
      M.~Geck and G.~Pfeiffer],
    [_Classical harmonic analysis and locally compact groups_ Hans Reiter and
      Jan D.~Stegeman],
    [_Operator spaces_ E.~G.~Effros and Z.-J.~Ruan],
    [_Banach algebras and automatic continuity_ H.~G.~Dales],
    [_The mysteries of the real prime_ M.~J.~Shai Haran],
    [_Analytic theory of polynomials_ Q.~I.~Rahman and G.~Schmeisser],
    [_The structure of groups of prime power order_ C.~R.~Leedham-Green and
      S.~McKay],
    [_Maximal orders_ I.~Reiner (reissue)],
    [_Harmonic morphisms between Riemannian manifolds_ P.~Baird and J.~C.~Wood],
  )
  pagebreak()
}
