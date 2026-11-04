#import "../main-defs.typ": source

#let title-page() = {
  set page(header: none, footer: none)
  set par(justify: false, first-line-indent: 0pt)
  source(2)
  text(size: 22pt, weight: "bold")[Maximal Orders]
  v(-2mm)
  line(length: 72%, stroke: 0.5pt)
  v(7mm)
  text(size: 13pt)[I. Reiner]
  linebreak()
  text(size: 9.5pt, style: "italic")[University of Illinois]
  v(1fr)
  text(size: 12pt, tracking: 0.25em)[CLARENDON PRESS #sym.bullet OXFORD]
  linebreak()
  text(size: 11pt)[2003]
  v(8mm)
  pagebreak()
}
