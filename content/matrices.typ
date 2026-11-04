#let labeled-matrix(
  data,
  row-labels: (),
  column-labels: (),
  prefix: none,
  augment: none,
  delim: "(",
) = context {
  assert(data.len() > 0, message: "A labeled matrix needs rows")
  let nrows = data.len()
  let ncols = data.first().len()
  assert(data.all(row => row.len() == ncols))
  assert(row-labels.len() == nrows)
  assert(column-labels.len() == ncols)
  let normalize(value) = {
    if type(value) == content and value.func() == math.equation {
      value.body
    } else if type(value) in (int, float) {
      str(value)
    } else { value }
  }
  let formula(value) = math.equation(math.display(normalize(value)))
  let widths = range(ncols).map(j => {
    calc.max(
      ..(
        data.map(row => measure(formula(row.at(j))).width)
          + (measure(formula(column-labels.at(j))).width,)
      ),
    )
  })
  let heights = range(nrows).map(i => {
    calc.max(
      ..(
        data.at(i).map(value => measure(formula(value)).height)
          + (measure(formula(row-labels.at(i))).height,)
      ),
    )
  })
  let cell(value, width: auto, height: auto) = box(
    width: width,
    height: height,
    align(center + horizon, formula(value)),
  )
  let header = math.display(math.mat(
    delim: none,
    ..(
      column-labels
        .enumerate()
        .map(((j, value)) => cell(value, width: widths.at(j))),
    ),
  ))
  let labels = math.display(math.mat(
    delim: none,
    ..row-labels
      .enumerate()
      .map(((i, value)) => (cell(value, height: heights.at(i)),)),
  ))
  let body = math.display(math.mat(
    delim: delim,
    augment: augment,
    ..data
      .enumerate()
      .map(((i, row)) => row
        .enumerate()
        .map(((j, value)) => cell(
          value,
          width: widths.at(j),
          height: heights.at(i),
        ))),
  ))
  math.display(math.mat(
    delim: none,
    ([], [], header),
    (if prefix == none { [] } else { normalize(prefix) }, labels, body),
  ))
}
