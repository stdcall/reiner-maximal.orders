// The cover of the 2003 reissue: navy cloth, a thin gold circle and gold
// lettering. Positions are fractions of the page, as on the cover.
#let cover() = {
  let width = 152mm
  let height = 229mm
  let navy = rgb(0, 31, 52)
  let gold = rgb(182, 164, 116)
  page(
    width: width,
    height: height,
    margin: 0pt,
    numbering: none,
    header: none,
    footer: none,
    fill: navy,
  )[
    #counter(page).update(0)
    #set text(font: "Libertinus Serif", fill: gold)
    #set par(leading: 0.6em, first-line-indent: 0pt)
    #let diameter = 0.554 * height
    #place(top + center, dy: 0.05 * height)[
      #align(center)[
        #set text(size: 10.5pt, weight: "semibold", tracking: 0.02em)
        LONDON MATHEMATICAL SOCIETY MONOGRAPHS \
        NEW SERIES #sym.bullet 28
      ]
    ]
    #place(top + center, dy: 0.443 * height - diameter / 2)[
      #circle(radius: diameter / 2, stroke: 1.1pt + gold)
    ]
    #place(top + center, dy: 0.352 * height)[
      #text(size: 32pt, weight: "bold")[Maximal Orders]
    ]
    #place(top + center, dy: 0.551 * height)[
      #text(size: 14pt, weight: "bold", tracking: 0.03em)[I. REINER]
    ]
    #place(top + center, dy: 0.922 * height)[
      #text(size: 13.5pt, weight: "bold", tracking: 0.03em)[
        OXFORD SCIENCE PUBLICATIONS
      ]
    ]
  ]
  pagebreak()
}
