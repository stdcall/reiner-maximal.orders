#import "@preview/cetz:0.5.2": canvas, draw

// The proof of (32.11): the tower of fields K ⊂ E_0 ⊂ F = E_(n-1) ⊂ L = E_n,
// left-aligned and joined by vertical lines under the letter L. On its
// left, one dashed line for each subgroup H_(n-1) ⊂ H ⊂ G of Gal(L/K), from
// L down to the field fixed by the subgroup, with its name on the left.
#let subgroup-tower = context {
  // Each field and its leading letter, which marks the field's height; the
  // tower line runs under the first one.
  let fields = (
    ($L = E_n$, $L$),
    ($F = E_(n-1)$, $F$),
    ($E_0$, $E$),
    ($K$, $K$),
  )
  // Each subgroup and the index of the field it fixes, nearest line first.
  let subgroups = (($H_(n-1)$, 1), ($H$, 2), ($G$, 3))
  let step = 2.2em.to-absolute() / 1pt // between consecutive fields
  let clear = 0.3em.to-absolute() / 1pt // between a line and its label
  let pad = 0.15em.to-absolute() / 1pt // dashed lines beyond their fields
  let gap = 0.35em.to-absolute() / 1pt // tower lines short of the fields
  let rule = 0.45pt
  canvas(length: 1pt, {
    import draw: *
    for (i, (field, letter)) in fields.enumerate() {
      content((0, -i * step), field, anchor: "base-west")
      let marker = "f" + str(i)
      content((0, -i * step), hide(letter), anchor: "base-west", name: marker)
    }
    for i in range(fields.len() - 1) {
      line(
        (rel: (0, -gap), to: ("f0.south", "|-", "f" + str(i) + ".south")),
        (rel: (0, gap), to: ("f0.south", "|-", "f" + str(i + 1) + ".north")),
        stroke: rule,
      )
    }
    // Lines from right to left, each clear of the label on its right.
    let x = -2 * clear
    for (name, fixed) in subgroups {
      let line-name = "g" + str(fixed)
      line(
        (rel: (0, pad), to: ((x, 0), "|-", "f0.north")),
        (rel: (0, -pad), to: ((x, 0), "|-", "f" + str(fixed) + ".south")),
        stroke: (thickness: rule, dash: "dashed"),
        name: line-name,
      )
      content((rel: (-clear, 0), to: line-name + ".mid"), name, anchor: "east")
      x -= measure(name).width / 1pt + 4 * clear
    }
  })
}
