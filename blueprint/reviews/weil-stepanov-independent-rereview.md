# Independent rereview: Weil--Stepanov prerequisite

## Frozen snapshot and evidence

- Re-reviewed chapter: `blueprint/05a-weil-stepanov.md`
- Frozen chapter SHA-256:
  `b76690764d091448163d0895571a647f9d5ff3b3b6ea0a6509c5221e6b648f38`
- Chapter length: 2,041 lines
- Cochrane--Pinner PDF SHA-256:
  `b7f6a6318cb322f361ed66e815e2ebb753bee0054d148878505d6a0065a975de`
- Cochrane--Pinner text-extract SHA-256:
  `2826c88880b4f437394a04d0f3e7e255dd80767a8e45ca7fb1de263bfeace997`
- Dedicated signature validator SHA-256:
  `7117cb8a1bf281cf2d24b2dde4bcc3e15975a2af23f948a1a7c5b76b615e716d`
- Strict generator SHA-256:
  `b1de3ea89f6d4af19cdeaf775f9fe33024a16d8a37026e4f5da44e5e80987a1c`
- Generated integrated validator SHA-256:
  `32c65c3e91bf108728a0d2b16f1c8098ad4c3ddbd0fd97a72b0212413f89c780`
- Declaration ledger SHA-256:
  `183d77007bc17fac1cf2cd217e245925f915f5e631bc3bb9f60175a3ca280c83`
- Pinned Mathlib commit:
  `db584cd6d46c92f209a44c0f1c829460d327499d`

The workspace root is not a Git worktree, so the chapter hash above is the
review identity. I reread all 2,041 current lines rather than relying on the
author repair descriptions. I reread Cochrane--Pinner Section 2 and printed
pages 10--14 from the text extraction and visually checked printed pages 4--5
and 10--14. The important source anchors are (2.1)--(2.3) on printed page 5,
Lemma 3.1 and Theorem 3.1 on printed page 11, Lemma 3.2 on printed pages
12--13, and the Hasse-system count and fiber estimates on printed pages
13--14.

The following checks succeeded:

```text
python3 blueprint/validation/generate_integrated.py --check
lake env lean blueprint/validation/BlueprintIntegrated.lean
lake env lean tmp/BlueprintWeilStepanov.lean
```

The Lean commands were run from the pinned Tiling checkout with the two files
passed by absolute path. The generated and dedicated validators use exact-type
axiom stubs for bodyless blueprint theorems. They are signature, namespace,
import, and dependency-order evidence only; they are not proof evidence.

Priorities below are `P0` for a false public theorem or trust violation, `P1`
for an implementation or acceptance blocker, and `P2` for a material but
localized proof/API defect. No `P0` counterexample was found in the frozen
chapter.

## Findings

1. **[P1, W5 remains open] The repository snapshot manifest still cannot
   identify or validate the corrected analytic snapshot.**

   **Evidence.** `blueprint/SNAPSHOT.sha256` still has SHA-256
   `e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb`.
   It has no entry for `05a-weil-stepanov.md`,
   `05b-chen-complete-sums.md`, `validation/generate_integrated.py`,
   `validation/BlueprintIntegrated.lean`, or
   `validation/declaration-coverage.tsv`. Running
   `sha256sum -c blueprint/SNAPSHOT.sha256` fails all fourteen entries which it
   does contain. This violates `blueprint/11-refereeing-standard.md:28-34` and
   `:67-72`. The direct hash at the top makes this report unambiguous, but it
   does not repair the repository's stated common-snapshot gate.

   **Exact repair.** After the chapter-level P2 below is disposed and the
   corrected chapters are frozen, regenerate the manifest with all reviewed
   chapters and the three required validation assets. Require all of

   ```text
   sha256sum -c blueprint/SNAPSHOT.sha256
   python3 blueprint/validation/generate_integrated.py --check
   lake env lean blueprint/validation/BlueprintIntegrated.lean
   ```

   to succeed. Two independent approvals must then name the same regenerated
   snapshot. This is root-owned and must not be silently treated as repaired by
   the chapter's standalone hash.

2. **[P2, new] The terminal `n=1` step lacks the explicit bridge from the
   extension-field sum to the literal `ZMod p` sum.**

   **Anchor.** Chapter lines 664--672 define
   `extensionExponentialSum psi f 1` as a sum over `GaloisField p 1`, with the
   field trace in the character. Lines 1951--1958 instead conclude an equality
   about `sum x : ZMod p, psi (f.eval x)`. Lines 1978--1984 say only that the
   `n=1` identity supplies this equality. No displayed theorem performs the
   reindexing, polynomial-evaluation transport, or degree-one trace
   identification, and a repository search finds no project bridge.

   Pinned Mathlib does provide the necessary components, so this is localized
   rather than theorem-sized: `GaloisField.equivZmodP` is in
   `Mathlib/FieldTheory/Finite/GaloisField.lean:147`, while
   `Algebra.trace_eq_of_algEquiv` and `Algebra.trace_self_apply` provide trace
   compatibility and the degree-one target trace. Successful elaboration of
   the terminal axiom stub does not prove that omitted bridge.

   **Exact repair.** Insert before the terminal API a theorem of the following
   shape and make `exists_prime_addChar_reciprocalRoots_le` invoke it:

   ```lean
   theorem extensionExponentialSum_one_eq_sum
       {p : ℕ} [Fact p.Prime]
       (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
       extensionExponentialSum psi f 1 =
         ∑ x : ZMod p, psi (f.eval x)
   ```

   Reindex the finite sum by `GaloisField.equivZmodP p`; use that this algebra
   equivalence commutes with the base algebra map and hence with `eval₂`, then
   rewrite the trace using `Algebra.trace_eq_of_algEquiv` followed by
   `Algebra.trace_self_apply`. The reverse equality orientation is equally
   acceptable. Under the assigned acceptance rule, an undisposed P2 prevents
   approval even though the terminal public theorem is mathematically true.

## W1--W7 disposition

### W1: resolved -- the finite Euler recurrence and orbit accounting are now recursive

Chapter lines 563--651 replace the formal infinite Euler product by literal
cutoff-finite polynomials. For `n<=cutoff`, a choice of a multiplicity in each
geometric factor is exactly a normalized irreducible factor multiset of total
degree `n`; `normalizedIrreducibleFactors_prod`, its exact degree sum, and
`monicWeight_eq_prod_normalizedIrreducibleFactors` supply reconstruction and
the repeated-factor weight. The local identity

```text
X * derivative(sum_(a=0)^(M/r) w^a X^(ar))
 = (sum_(a=0)^(M/r) w^a X^(ar))
   * (sum_(b=1)^(M/r) r*w^b X^(br))  mod X^(M+1)
```

has the correct cutoff and positive sign. Coefficient `m` gives

```text
m*T_m = sum_(j=1)^m markedFactorSum(j)*T_(m-j).
```

The `m=0` coefficient and empty product are separately stated.

Lines 680--765 now expose the finite-field content which Cochrane--Pinner
(2.3) compresses into “the conjugates.” For monic irreducible `G` and `m!=0`,
the minpoly fiber is nonempty exactly when `natDegree G | m`, then has exactly
`natDegree G` elements and is one Galois orbit. The phase is the sum along the
Frobenius orbit. `FiniteField.algebraMap_trace_eq_sum_pow` and divisibility of
the orbit length split the `m` trace terms into `m/r` identical blocks, so the
character value is the `m/r` power of the minpoly weight. Summing the exact
fibers gives `markedFactorSum_eq_extensionExponentialSum` with the required
factor `r`; no multiplicity is lost.

Lines 772--843 give the reverse-root Newton recurrence with the negative sign,
identify all L-coefficients with `T_m`, and state the strong-induction
convolution comparison with `T_0=1`. Thus
`artinLPolynomial_trace_identity` is now a short composite. This matches
Cochrane--Pinner printed page 5, formulas (2.1)--(2.3), but avoids convergence
and an unbounded Euler product. I find the new boundary sufficient for a
sorry-free implementation plan.

### W2: resolved -- the trace-only linear system is literal and correctly counted

Chapter lines 1209--1481 define the source

```text
Fin p -> Fin (K+1) -> Fin S -> ZMod p
```

and the target

```text
Fin R -> Fin (S+d*(p-1)*p^(u-1)+K) -> ZMod p.
```

The coefficient decoder is injective coefficientwise. The reduced Hasse
polynomial, three linear maps, strict degree bound, fiber evaluation theorem,
two exact finranks, nonzero kernel, zero-polynomial recovery, and packaging
into nonzero coefficient data are all explicit.

The counts are correct: the source finrank is `p*S*(K+1)` and the target
finrank is exactly

```text
R*(S+d*(p-1)*p^(u-1)+K).
```

With `R=p*K`, cancellation reduces strict dimension slack to

```text
K*d*(p-1)*p^(u-1) + K^2 < S.
```

For even `n=2u`, the two terms are bounded by
`((p-1)/(2p))*S` and `S/(4*d^2*p^2)`; odd `n=2u+1` has an additional factor of
`p` of slack. The stated large-`n` hypotheses also give `K>0`, `R>0`,
`R<p^u`, and the strict norm degree. This is the exact pure-additive
specialization of the mixed count on Cochrane--Pinner printed page 14 after
removing the Kummer coordinate.

On a trace fiber, `Phi(x)=b-lowerTrace(x)` and `x^(p^n)=x`. For `r<R<p^u`,
Hasse derivatives freeze every upper Frobenius factor and the
`X^(p^n*j)` factor, leaving only the Hasse derivative of the coefficient
polynomial. The reduced polynomial therefore has the displayed degree and
evaluates to the auxiliary Hasse derivative. This closes the earlier
rank-nullity/evaluation gap.

### W3: resolved -- the translation-product descent now has every algebraic step

Lines 1490--1755 correctly distinguish the initial translation product from a
field norm. The fixed-ring argument is valid over `F_p[X]`: translation
invariance forces the leading outer exponent to be divisible by `p`; subtract
the leading coefficient times `(T^p-T)^a` and induct on outer degree. Since
`deg_T P<p`, the product has outer degree at most `p*(p-1)`, so its quotient in
`T^p-T` has degree at most `p-1`. Each product coefficient uses `p` inner
coefficients of degree `<S`, and the same leading-term induction only takes
linear combinations with prime-field scalars, preserving the strict `<p*S`
filtration.

At `Phi`, the zero translation factor supplies divisibility by `X^(p^n)`.
The identity

```text
Phi^p-Phi = f^(p^n)-f^(p^u)
```

and `X^(p^n) | f^(p^n)-C(f(0))` justify the exact
`Polynomial.sub_dvd_eval_sub` congruence to the zero-block argument
`C(f(0))-f^(p^u)`. The strict bound

```text
p*S + d*p^u*(p-1) < p^n
```

then makes the zero-block quotient polynomial identically zero.

The transported Artin--Schreier polynomial is explicitly irreducible. After
evaluation at one algebraic root, `Finset.prod_eq_zero_iff` chooses one
translation factor. Its translated root has the degree-`p` minpoly, so a
mapped polynomial of outer degree `<p` which vanishes there is zero; coefficient
map injectivity returns `P=0`. Finally, the displayed strong induction on
`j : Fin (K+1)` factors off `X^(p^n*j)`, obtains the next zero-block
divisibility, and eliminates every block. This is the missing Lean-level
content behind Cochrane--Pinner Lemma 3.2's “dividing and repeating.”

### W4: resolved -- the Artin--Schreier root criterion uses the correct Galois proof

Lines 876--1050 now use a chosen splitting-field root. Differences of roots
lie in the prime subfield, so one root generates the splitting field. The
automorphism shift is an injective additive homomorphism from the Galois group
to that prime subfield. Its cardinal, hence the minpoly degree, divides the
prime `p` and is `1` or `p`. Reducibility is therefore equivalent to a base
root. The chapter explicitly rejects the former false translate-product claim
and retains the `F_5`, `T(T-1)` counterexample.

For the rational-function specialization, clearing a normalized coprime
denominator in `h^p-h=g` forces the denominator to be a unit. A nonconstant
polynomial `A` has `deg(A^p-A)=p*deg A`, while a constant has constant
difference; neither equals a polynomial of degree strictly between zero and
`p`. This proves the needed irreducibility without curve absolute
irreducibility or a class-field theorem.

### W6: resolved -- simultaneous alignment and the root-radius limit are separated

Lines 1863--1918 now state `exists_unbounded_aligned_powers` and
`exists_normalized_powerSum_tendsto_maximalMultiplicity`. The finite-box proof
is sound: among `(B+1)*q^s+1` consecutive powers in `q^s` boxes, some box
contains at least `B+2` indices, so its first and last indices differ by more
than `B`; equal boxes make every quotient phase close to one. Taking `B` to be
the preceding exponent yields a strictly increasing sequence. Maximal roots
are aligned with multiplicity, smaller normalized roots tend to zero, and a
hypothetical maximum radius greater than `R` contradicts the normalized power
sum bound. The empty multiset and `R=0` cases are harmless.

### W7: resolved -- the internal/public boundary now matches the prose

`waringVariable` is literally `private` at lines 338--340. The generalized
`monicPhase_affine_last` at lines 490--498 is a characteristic-independent
`CommRing` polynomial identity and retains only the natural degree positivity
and coordinate-range hypotheses. Character nontriviality and `d<p` occur in
the following orthogonality theorem where they are actually used.

## Edge cases and terminal-sign audit

- The L-polynomial definition uses `range (max 1 f.natDegree)`, so a constant
  polynomial gives exactly `1`; its constant coefficient and degree bound are
  true. No minpoly-orbit or trace theorem is stated at extension degree zero.
- `upperTracePolynomial_eval_eq_of_trace_eq` correctly requires `n!=0` and
  `u<=n`. At `n=0` both polynomial sums can be empty while the trace hypothesis
  holds, so omitting the first hypothesis would be false. Stepanov parameters
  imply `n>0` before this theorem is used.
- If `deg f=1`, the leading coefficient makes `x |-> Tr(a*x)` a nonzero linear
  functional by `FiniteField.trace_to_zmod_nondegenerate`; every affine fiber
  has `p^(n-1)` elements for `n>0`, and every positive-degree extension sum is
  zero. If `p=2`, `0<deg f<p` forces exactly this branch, so no impossible
  degree-at-least-two parameters are constructed.
- Hasse vanishing agrees with root multiplicity, including `R=0`, and the
  cardinality-times-multiplicity inequality counts distinct fiber elements.
- Dividing the auxiliary degree by `R=p*K` gives exactly
  `p^(n-1)+(S+d*(p-1)*p^(n-1))/R`. The `p` trace fibers partition all `p^n`
  elements, so upper bounds on the other `p-1` fibers give the matching lower
  bound.
- The recurrence comparison has the correct sign:
  `S_n=-sum omega^n`. For `g=eraseConstant f`, the trace identity gives
  `S_n(f)=psi(f(0))^n*S_n(g)`, so at `n=1` the reciprocal roots are twisted by
  `psi(f(0))` and the minus sign remains. `ZMod.stdAddChar` is the positive
  standard character and is nontrivial for prime `p`; the Chapter 05b consumer
  uses the same normalization.
- No curve Riemann hypothesis, class-field result, Riemann--Roch theorem, or
  imported restatement of the desired Weil bound appears in the accepted
  dependency route. The remaining work is elementary algebra, finite-field
  theory, finite linear algebra, and compactness/pigeonhole reasoning.

## Verdict

**BLOCK.** The repaired public mathematical statements appear true. W1--W4,
W6, and W7 are adequately repaired, and no hidden curve-RH or class-field
dependency remains. However, W5 is still an open `P1` acceptance-gate failure,
and the terminal proof has the new localized `P2` degree-one-field bridge
omission. The assigned standard permits approval only with no P0/P1 and with
all P2 dispositions adequate, so this frozen hash cannot be approved.

After both repairs, the changed chapter/manifest snapshot needs a new hash and
fresh independent verification. This report cannot self-approve an authored
repair.
