# Tiling

A Lean/Mathlib project for translational tilings of normed additive groups, with `ℤ`, `ℝ`, and
finite-dimensional Euclidean spaces as the primary examples.

A `Prototile E` is a nonempty measurable subset of `E`; unbounded prototiles are allowed. A
labelled prototile family is a function `P → Prototile E`; keeping the label type `P` separate from
geometric support lets us treat each permitted orientation of a shape as a distinct prototile
while using translations as the only placement operation.

A placement is a pair `(x, p) : E × P`. A set of placements is a measurable tiling when its
translated supports are locally finite, pairwise almost-everywhere disjoint, and cover almost
every point. All compatibility information is encoded geometrically in the prototile supports.

The tiling layer uses Mathlib's `[MeasureSpace E]`, so its canonical measure `volume` is implicit.
Mathlib supplies the expected Lebesgue measure automatically on `ℝ` and finite products `Fin n → ℝ`.
Mathlib does not choose a default measure on `ℤ`, so this project installs `Measure.count` as
`volume` on `ℤ`. Mathlib's finite-product construction then supplies `volume` on `Fin n → ℤ`, and
`Tiling.Measure.pi_count` proves that this product measure is counting measure on the product.
Thus both real and integer Euclidean spaces work automatically after importing `Tiling`.
