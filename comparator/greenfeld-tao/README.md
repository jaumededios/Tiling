# A Mathlib-only comparator for the Greenfeld--Tao main theorems

This directory presents the main results of Rachel Greenfeld and Terence Tao, *The Structure of
Translational Tilings in `Z^d`* ([arXiv:2010.03254v3](https://arxiv.org/abs/2010.03254v3)), in a
single expository challenge file for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## The trusted mathematical vocabulary

`GreenfeldTaoChallenge.lean` imports only `Mathlib`. It defines:

1. `Lattice d = Fin d → ℤ` and `Plane = Lattice 2`;
2. the number of representations `x = f + a` with `f ∈ F` and `a ∈ A`;
3. level-`k`, level-one, and whole-lattice translational tilings;
4. periodic sets, one-periodic sets, and finite weak-periodic decompositions;
5. the cosetwise finite-direction periodicity used in qualitative Theorem 1.4.

It then states six headline results:

- level-one planar tilings of periodic targets are weakly periodic (Theorem 1.3(i));
- such tilings use at most `|F| - 1` period directions, coset by coset (qualitative Theorem 1.4);
- an eight-point tile has a non-weakly-periodic level-four tiling (Theorem 1.3(ii));
- every tileable periodic planar target has a periodic tiling (qualitative Theorem 1.5);
- one Boolean algorithm decides whether a finite planar tile tiles `ℤ²` (qualitative Corollary 1.6);
- periodic representation counts have the bounded directional decomposition of Theorem 1.7.

The challenge deliberately omits explicit period bounds, search-cost recurrences, HNF encodings,
circle polynomials, and number-theoretic constants. Those belong to the reusable proof library, not
to the shortest readable statements of the results.

## Comparator architecture

| file | purpose |
|---|---|
| `GreenfeldTaoChallenge.lean` | trusted, single-file, Mathlib-only statements with `sorry` proofs |
| `GreenfeldTaoSolution.lean` | the repeated definitions and explicit bridge to `TranslationalTilings.Main` |
| `config.json` | the six checked theorem names and standard permitted axioms |
| `PrintAxioms.lean` | a quick local trust audit |

The bridge proves that the elementary representation-count definition agrees with the production
finite convolution, converts the two periodicity vocabularies, translates weak-periodic
decompositions in both directions, and then invokes the paper-facing production theorems.

## Checks

From the repository root:

```bash
lake build GreenfeldTaoChallenge GreenfeldTaoSolution
lake env lean comparator/greenfeld-tao/PrintAxioms.lean
```

For the full acceptance test, run the official Comparator binary on
`comparator/greenfeld-tao/config.json`. Success ends with `Your solution is okay!`.
