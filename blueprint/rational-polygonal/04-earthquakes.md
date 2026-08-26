# 4. Discrete earthquakes

## Canonical decomposition

Let `F` tile `ℤ²` with translation set `T`, and let `v ≠ 0`.  Translation by `v` sends each point
`f+t` to a uniquely represented point `f'+t'`.  The quake graph joins translation vertices `t,t'`
when such a one-step transfer occurs (and uses the symmetric closure).  Tectonic plates are the
connected components of this graph.

This construction proves the paper's footnote rather than assuming it:

- components partition `T`;
- the carrier `F + P` of every component is `ℤv`-periodic;
- any subset of a component with `ℤv`-periodic carrier is empty or the whole component; and
- any decomposition satisfying the two clauses of Definition 4.1 has exactly these components.

## Earthquake shifts

Assign an integer displacement along `v` to every tectonic plate.  Because each plate carrier is
invariant and the carriers partition the exactly tiled universe, independent shifts preserve the
tiling.  The special family `Tᵏ` fixes one plate and shifts every other plate by `k v`.

## Lemma 4.2

Apply the proved uniform Greenfeld--Tao structure theorem to every `Tᵏ`, using one common lattice
and one common finite list of pairwise incommensurable periods.  On each lattice coset, pigeonhole
two of the first `m+1` quake shifts which select the same period.

For each non-quake-parallel period `hⱼ`, split a fixed plate into:

- the complete `hⱼ`-orbits, already `hⱼ`-periodic; and
- the incomplete orbits.

The two equal period selections move every incomplete orbit by a nonzero multiple of the quake
direction.  Multiplying the finitely many coset-specific displacements gives one common nonzero
quake-parallel period.  The residual part of the plate has that period.  Thus every plate is a
disjoint union using the same finite list of period directions.

All signs and zero cases in the paper's product
`∏Γ (kΓ-k'Γ)` are normalized in Lean by using the positive differences `k'Γ-kΓ`; nonzeroness is
proved before forming the product.

## Continuous compatibility

After sliding a rational polygonal tiling to an integer tiling, every old continuous plate becomes
a subset of the integer translation set.  A rational sliding-direction theorem supplies a nonzero
integer vector parallel to the real sliding line.  Lemma 3.1(iii) then makes its raster carrier
periodic, so the continuous plate is a union of canonical discrete quake components.  Lemma 4.2
decomposes those components using one finite period list.  Translating the plates back preserves
their periods.

