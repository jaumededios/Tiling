# Independent follow-up: Weil--Stepanov degree-one bridge

## Reviewed snapshot and scope

- Chapter: `blueprint/05a-weil-stepanov.md`
- Reviewed chapter SHA-256:
  `69f505f840db34a06c803f6a1c1304abceec0848070c47586a7794eb7f1879d6`
- Chapter length: 2,077 lines
- Previous independently reviewed chapter SHA-256:
  `b76690764d091448163d0895571a647f9d5ff3b3b6ea0a6509c5221e6b648f38`
- Previous rereview report SHA-256:
  `2501fff095eaa7acd44a3bc983354dd85e923c3e3be6bcea4e6928ed4b142a20`
- Dedicated signature validator SHA-256:
  `85d3d3473f7594be57d108c61d8672fd7c6b83d578f2517b4ae6f7df596c91ca`
- Strict generator SHA-256:
  `b1de3ea89f6d4af19cdeaf775f9fe33024a16d8a37026e4f5da44e5e80987a1c`
- Generated integrated validator SHA-256:
  `fd5bbde39f388b90d23c81a51728f8e84258960068475bf508aa0cee9db82cf7`
- Declaration ledger SHA-256:
  `790622481593ba3f179f77f05c9c5b419df1d115ee882cf0702812fc19d519e6`
- Pinned Mathlib commit:
  `db584cd6d46c92f209a44c0f1c829460d327499d`

The workspace root is not a Git worktree, so the chapter hash is the review
identity. This follow-up is limited to the localized repair requested after
the full 2,041-line independent rereview: the new checked degree-one bridge,
its terminal use and sign, the comparator/checklist update, and regression of
the already cleared W1--W4, W6, and W7 boundaries. No chapter file was edited
by this review.

The following checks all succeeded against the pinned toolchain:

```text
python3 blueprint/validation/generate_integrated.py --check
lake env lean blueprint/validation/BlueprintIntegrated.lean
lake env lean tmp/BlueprintWeilStepanov.lean
```

The Lean commands used absolute paths from the pinned Tiling checkout. The
strict validator header contains the exact reviewed chapter hash. The
declaration ledger records
`TranslationalTilings.Stepanov.extensionExponentialSum_one_eq_primeSum` as a
`checked-body`, not an exact-type axiom stub.

## New P2 disposition: resolved and independently verified

The prior P2 asked for a literal bridge between
`extensionExponentialSum psi f 1`, whose finite sum is indexed by
`GaloisField p 1`, and the terminal sum indexed by `ZMod p`. Chapter lines
673--690 now state and prove exactly:

```lean
theorem extensionExponentialSum_one_eq_primeSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    extensionExponentialSum psi f 1 =
      ∑ x : ZMod p, psi (f.eval x)
```

The checked body is mathematically and Lean-API correct:

1. `Fintype.ofFinite` installs the actual finite indexing instance for
   `GaloisField p 1`.
2. `e := GaloisField.equivZmodP p` is the pinned algebra equivalence over the
   same base `ZMod p`; no type-level identification is assumed.
3. `Fintype.sum_equiv e.toEquiv` reindexes the whole finite sum bijectively, so
   no element or multiplicity is lost.
4. After unfolding `traceLiftAddChar`, the summand goal is precisely equality
   of the character applied to the extension trace and to `f.eval (e x)`.
5. Rewriting by `Algebra.trace_eq_of_algEquiv e` in the displayed reverse
   direction changes the extension trace into the trace of the transported
   element in `ZMod p` over itself. `Algebra.trace_self_apply` reduces that
   trace to the transported element.
6. `Polynomial.aeval_algHom_apply e x f`, with
   `Polynomial.aeval_def`, transports the coefficient map and evaluation in
   the required direction, giving exactly `f.eval (e x)`.

Thus the theorem has a real proof term using the intended pinned Mathlib APIs
and no project theorem-strength assumption. The dedicated and strict
validators both compile that body. The declaration is placed immediately
after `extensionExponentialSum`, which is the natural reusable seam.

The terminal proof prose at lines 2008--2017 now invokes the bridge before
passing from the `n=1` extension identity to the literal prime-field sum. The
source-to-Lean comparator has its own degree-one row at line 2032, and the
acceptance checklist requires the bridge at lines 2063--2066. The eventual
terminal implementation is still represented by an exact-type axiom stub in
the blueprint validator, as intended for a bodyless blueprint theorem; this
does not weaken the fact that the newly added prerequisite itself is checked.

## Terminal sign and edge regression

The sign remains correct. For `g=eraseConstant f`, the trace identity is

```text
extensionExponentialSum psi g 1 = -sum omega.
```

The new bridge changes only the index type and trace presentation, not the
value or sign, so the literal prime-field sum of `g` is also `-sum omega`.
The constant-twist identity gives

```text
primeSum(f) = psi(f(0)) * primeSum(g)
            = -sum (psi(f(0))*omega).
```

Since the twist has norm one, root norm bounds are unchanged. The public
terminal API therefore still has the correct displayed minus sign and the
bound `(natDegree f-1)*sqrt p`. `ZMod.stdAddChar` retains the same positive
normalization used by Chapter 05b.

The bridge is unconditional in `f` and `psi` and needs only `Fact p.Prime`, so
it introduces no new degree or characteristic edge. In particular, degree one
and `p=2` still follow through the zero extension sum/empty root multiset
branch. No extension theorem is asserted at `n=0`.

## W1--W7 regression disposition

| Finding | Disposition at SHA-256 `69f505...` |
|---|---|
| W1 | **Resolved.** The cutoff-finite Euler coefficient/log-derivative recurrences, exact minpoly fiber/orbit cardinalities, trace-weight power, marked-factor/extension-sum identity, reverse-root Newton recurrence, and convolution induction remain present with their previous signs and hypotheses. The new bridge is inserted after the extension-sum definition and does not alter this graph. |
| W2 | **Resolved.** The literal coefficient source, constraint target, reduced Hasse evaluation, exact finranks, nonzero kernel, and decoder remain present. The counts remain `p*S*(K+1)` variables versus `R*(S+d*(p-1)*p^(u-1)+K)` equations. |
| W3 | **Resolved.** The translation fixed-ring quotient and coefficient filtration, zero-block congruence and degree forcing, one-factor selection, degree-`p` minpoly descent, and strong induction through every auxiliary block remain explicit. |
| W4 | **Resolved.** The Artin--Schreier criterion still uses the splitting-field root and injective Galois shift into the prime subfield, followed by the rational-function denominator/degree exclusion; the false arbitrary-factor translation product is not reintroduced. |
| W5 | **Open, root-owned.** This is a repository snapshot-manifest issue, not a remaining defect in this chapter's mathematical dependency graph. |
| W6 | **Resolved.** The finite-box unbounded aligned-powers theorem and the maximal-versus-smaller-root limit remain separate, multiplicity-aware seams. |
| W7 | **Resolved.** `waringVariable` remains literally private, and `monicPhase_affine_last` remains the characteristic-independent `CommRing` identity with character assumptions confined to the cancellation theorem. |

No P0, P1, or undisposed P2 finding remains against the chapter itself at the
reviewed hash.

## Repository snapshot status

W5 remains factually open. `blueprint/SNAPSHOT.sha256` still has SHA-256
`e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb`,
omits 05a, 05b, and the three required integrated-validation assets, and
`sha256sum -c blueprint/SNAPSHOT.sha256` still reports failure for all fourteen
listed entries. The strict generated validator is current and hash-bound, but
it is not a replacement for the common repository manifest required by
`blueprint/11-refereeing-standard.md`.

## Verdict

**CHAPTER APPROVE, independently, at SHA-256
`69f505f840db34a06c803f6a1c1304abceec0848070c47586a7794eb7f1879d6`,
apart from root-owned W5.** The localized P2 is genuinely repaired, W1--W4,
W6, and W7 remain resolved, the terminal sign is correct, and no chapter-level
P0/P1/P2 or hidden curve-RH/class-field dependency remains.

**REPOSITORY-LEVEL VERDICT: BLOCK until W5 is repaired and independently
snapshot-checked.** Regenerating the manifest does not authorize this referee
to self-approve later chapter changes; any material chapter change requires a
new hash-bound review.
