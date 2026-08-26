# Independent referee report: Weil--Stepanov prerequisite

## Reviewed snapshot, evidence, and standard

- Reviewed chapter: `blueprint/05a-weil-stepanov.md`
- Chapter SHA-256:
  `6b21e03f6e63f662eb6e3ab81b281f1eca01cf029ebbd3b9fdedac9f1b9df4d0`
- Cochrane--Pinner PDF SHA-256:
  `b7f6a6318cb322f361ed66e815e2ebb753bee0054d148878505d6a0065a975de`
- Cochrane--Pinner text extract SHA-256:
  `2826c88880b4f437394a04d0f3e7e255dd80767a8e45ca7fb1de263bfeace997`
- Diagnostic signature file SHA-256:
  `7b780bf8683e38b5a7a60ba8b1f1d38f2f4ca275911eea9679b80d18828298c5`
- Pinned Mathlib commit:
  `db584cd6d46c92f209a44c0f1c829460d327499d`

The workspace root is not a Git worktree, so the chapter hash, rather than a
commit, fixes this review. The chapter changed during the review from hash
`54d480...` to the hash above. I discarded the findings against the earlier
file, reread all 1,005 lines, and rechecked the repaired constant-polynomial
and initial-translate passages before writing this report.

I read all fifteen pages of `tmp/pdfs/cochrane-pinner-stepmix.pdf` through its
complete text extraction and visually checked the formula-heavy printed pages
11--14. I compared in particular source (1.3), (2.1)--(2.3), Lemmas 3.1--3.2,
and Theorem 3.1. I also inspected the pinned Mathlib declarations used for
additive characters, `GaloisField`, trace, polynomial roots/reverse, Hasse
derivatives, Taylor expansion, and `RatFunc` valuation. The diagnostic file
and the generated integrated validator both elaborate in the pinned checkout;
their bodyless declarations are axiom stubs and were used only as type and
namespace evidence, never as proof evidence.

Priorities are `P0` for a false public result or trust violation, `P1` for a
recursive proof or integration blocker, and `P2` for a material but localized
API/proof defect. No `P0` counterexample was found against a public theorem in
the final hash. The findings below concern whether the chapter is sufficiently
recursive and exact to authorize a sorry-free implementation.

## Findings

1. **[P1] The Artin L-series trace identity is still a theorem-sized prose
   assertion, not a recursively specified Lean proof boundary.**

   **Anchor and evidence.** Chapter lines 437--484 compress the coefficientwise
   Euler product, unique monic factorization, formal logarithmic derivative,
   irreducible/minimal-polynomial orbit accounting in `GaloisField p n`, and
   reverse-root comparison into one paragraph before stating
   `artinLPolynomial_trace_identity`. Cochrane--Pinner printed pp. 4--5,
   extract lines 266--345, make the same paper-level passage from (2.1)--(2.2)
   to (2.3). Pinned Mathlib supplies UFD polynomials, roots, minpolynomials,
   finite fields, and trace, but it supplies neither this weighted Artin series
   nor the required coefficient/orbit theorem; the chapter itself correctly
   records that absence at lines 146--150.

   The sentence “a monic polynomial has a unique multiset of monic irreducible
   factors” does not yet specify the bridge from `MonicDegreePolynomial` to
   Mathlib factorization, a finite-by-degree encoding of irreducibles, or the
   multiplicity with which each irreducible orbit occurs in
   `GaloisField p n`. Nor is a formal power series, truncated Euler product, or
   coefficient recurrence defined. Consequently an implementer must design a
   substantial new interface before the displayed theorem can even be split
   into Lean-sized obligations.

   **Exact repair.** Add the following dependency-ordered internal audit API
   (names may vary, types may use finite truncations rather than an infinite
   product):

   - an equivalence/injective reconstruction between
     `MonicDegreePolynomial k n` and monic degree-`n` polynomials;
   - a finite factorization theorem giving the multiset of normalized monic
     irreducible factors and proving `monicWeight` is the corresponding
     product;
   - the marked-factor coefficient recurrence, for `m>0`,
     `m*T_m = sum_(j=1)^m S_j*T_(m-j)`, where `S_j` is the displayed extension
     exponential sum;
   - the finite-field orbit theorem saying that a monic irreducible `G` occurs
     among minpolynomials in `GaloisField p m` iff `natDegree G | m`, and then
     occurs in an orbit of exactly `natDegree G` elements, with its weight
     identified using `FiniteField.algebraMap_trace_eq_sum_pow`;
   - the reverse-root Newton recurrence
     `m*T_m = -sum_(j=1)^m P_j*T_(m-j)` for
     `P_j=sum omega^j`;
   - an induction from `T_0=1` comparing the two recurrences and yielding
     `S_m=-P_m`.

   This recurrence route avoids convergence and an unbounded formal product
   while making every coefficient and sign explicit. Alternatively define a
   truncated `PowerSeries` Euler product and state the same coefficient
   theorems. In either route the current terminal trace identity should become
   a short composition of named results rather than the sole boundary for all
   of Section 2.

2. **[P1] The direct trace-only linear system has the correct scalar count,
   but no coefficient vector, linear constraint map, or rank argument is
   specified.**

   **Anchor and evidence.** Chapter lines 575--630 define the numerical data,
   and lines 669--704 say that the auxiliary has
   `p*S*(K+1)` scalar coefficients and at most
   `R*(S+d*(p-1)*p^(u-1)+K)` equations. The arithmetic is correct. With
   `R=pK`, cancellation gives exactly

   `K*d*(p-1)*p^(u-1) + K^2 < S`.

   For even `n=2u`, the two terms are bounded respectively by
   `((p-1)/(2p))*S` and `S/(4*d^2*p^2)`; the odd case has an additional factor
   of `p` of slack. The positivity conditions imply `u>=3`, `S>0`, `K>0`, and
   `R>0`. Thus this finding is not a numerical objection.

   The implementation obstruction is that
   `AdditiveAuxiliaryCoefficients` is a structure of polynomials carrying a
   proof field `natDegree < S`; it is not the finite-dimensional vector space
   to which rank-nullity can be applied. The reduced Hasse polynomial and the
   asserted coefficient equations are not defined. Cochrane--Pinner printed
   pp. 13--14, extract lines 1244--1305, explicitly count the mixed system's
   variables and equations, but the direct trace-only system is a new
   specialization owned by this chapter and cannot be inherited from that
   source.

   **Exact repair.** Before `exists_additive_stepanov_coefficients`, define

   ```text
   CoeffVector(par) = Fin p -> Fin (K+1) -> Fin S -> ZMod p
   D(par) = S + d*(p-1)*p^(u-1) + K
   ConstraintTarget(par) = Fin R -> Fin D -> ZMod p.
   ```

   Define a linear `coeffVectorToAuxiliary`, a linear map
   `additiveConstraint : CoeffVector par ->ₗ ConstraintTarget par`, and the
   reduced polynomial for each `r<R`. State and prove:

   - its evaluation on a trace fiber equals the `r`th Hasse derivative of the
     mapped auxiliary;
   - its degree is strictly below `D`;
   - the source finrank is exactly `p*S*(K+1)` and target finrank is exactly
     `R*D` (or at most that value);
   - `dimension_ok` gives a nonzero kernel vector;
   - conversion of that vector gives `e.Nonzero` and all required Hasse
     vanishings.

   This also forces the proof to use `R_lt_frobenius` at the exact point where
   the `Phi` and `X^(p^n*j)` factors freeze. Without these interfaces, the
   displayed theorem still hides the central new linear-algebra construction.

3. **[P1] The corrected norm descent has the right idea and degree bound, but
   it skips the invariant-product theorem, the zero-factor step, the precise
   Artin--Schreier transport, and the block induction needed in Lean.**

   **Anchor and evidence.** Chapter lines 706--773 correctly repair the
   important mistake that the initial `Z=Phi` might be algebraic: it lies in
   `F_p(X)`, and the product is over its translations, not field conjugates.
   This matches the mechanism in Cochrane--Pinner Lemma 3.2, printed pp.
   12--13, extract lines 1083--1242. The strict bound

   `p*S + d*p^u*(p-1) < p^n`

   is also the correct pure-additive replacement for the source's larger mixed
   norm degree.

   The remaining jump is at chapter lines 748--758. From the reduced
   translation product being the zero base polynomial, the prose immediately
   invokes linear independence and concludes that every `e_(i,0)` is zero.
   A product equal to zero yields only that one factor is zero; it does not
   make every factor zero. The source explicitly selects some factor
   (`I,J`) before using the two extension degrees (extract lines 1197--1242).
   Here one must likewise select a `beta` and then use a degree-`p` minimal
   polynomial. Moreover, translation-invariance implying membership in
   `F_p[X][T^p-T]`, including the `T^p-T` degree at most `p-1`, is not a pinned
   Mathlib theorem identified by the chapter.

   **Exact repair.** Add and prove, in order:

   - a translation-product invariant theorem
     `prod_beta P(T+beta) = Q(T^p-T)` for `deg_T P<p`, with
     `deg_(T^p-T) Q <= p-1` and the required coefficient-degree bound;
   - the congruence modulo `X^(p^n)` identifying its zero block with
     `prod_beta P_0(z+beta)` for
     `z^p-z=f(0)-f^(p^u)`;
   - a transported irreducibility corollary for that latter polynomial. If
     `s=f+f^p+...+f^(p^(u-1))`, then `w=z+s` satisfies
     `w^p-w+(f-f(0))=0`; apply Section 3 to `eraseConstant f` and explicitly
     transport irreducibility through `T |-> T+s`;
   - after the product is zero in the resulting field, choose
     `beta` with `P_0(z+beta)=0`; use `minpoly.dvd`,
     `natDegree P_0<p`, and the degree-`p` minpoly to obtain `P_0=0`, hence all
     `e_(i,0)=0`;
   - a finite induction on `j<=K` after division by `X^(p^n)`, rather than the
     sentence “repeat”.

   The acceptance checklist should call the first object a *translation
   product*, not a “conjugate norm product”; only the later irreducible
   extension supports genuine conjugates and a field norm.

4. **[P1] The stated proof of the Artin--Schreier reducibility criterion
   contains a false factor-product claim.**

   **Anchor.** Chapter lines 504--512 say that a factor's translations have
   equal degree and “their product is the whole polynomial”, then infer that a
   proper factor forces a linear factor because `p` is prime. Cochrane--Pinner
   Lemma 3.1, printed p. 11 and extract lines 985--1006, does not make this
   argument; it invokes a separate absolute-irreducibility criterion. The
   chapter intentionally replaces that criterion, so its replacement must be
   correct on its own.

   **Counterexample to the proof sentence.** Over `F_5`, let
   `F(T)=T^5-T` and take the proper factor `H(T)=T(T-1)`. As `a` runs through
   `F_5`, every root of `F` occurs in exactly two translated factors
   `H(T+a)`. Hence

   `prod_(a in F_5) H(T+a) = (T^5-T)^2`,

   not `T^5-T`. The desired irreducibility theorem is nevertheless true; it
   is this proof sentence that is false.

   **Exact repair.** Pick one root `alpha` of `T^p-T-c`. Since all roots are
   `alpha+a`, `a in F_p`, the field `K(alpha)` already contains the full
   splitting field, and the polynomial is separable. The Galois group embeds
   into the additive group of `F_p` via
   `sigma(alpha)=alpha+a_sigma`. Its order, equivalently the degree of the
   minpoly of `alpha`, therefore divides the prime `p`, so it is `1` or `p`.
   Reducibility forces degree `<p`, hence degree one and a root in `K`.
   Conversely a root gives reducibility. State this criterion as a named
   theorem before the finite-pole argument. The denominator-valuation and
   infinity-degree steps at lines 513--525 can then prove that no such rational
   root exists when `0<deg f<p`.

5. **[P1] The repository snapshot manifest cannot identify or validate this
   chapter.**

   **Anchor and evidence.** At review time
   `blueprint/SNAPSHOT.sha256` has SHA-256
   `e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb`.
   It contains no entry for `05a-weil-stepanov.md`, `05b`, or any of the three
   validation assets required by `blueprint/11-refereeing-standard.md:28-34`.
   Running `sha256sum -c blueprint/SNAPSHOT.sha256` reports failure for all
   fourteen listed paths. Thus the direct chapter hash at the top of this
   report is usable, but the project's stated two-referee same-snapshot gate
   is not.

   **Exact repair.** After the chapter and all concurrent repairs stabilize,
   regenerate `blueprint/SNAPSHOT.sha256` with entries for every reviewed
   chapter and for `validation/generate_integrated.py`,
   `validation/BlueprintIntegrated.lean`, and
   `validation/declaration-coverage.tsv`. Require both
   `sha256sum -c blueprint/SNAPSHOT.sha256` and
   `python3 blueprint/validation/generate_integrated.py --check` to pass before
   asking two referees to approve a common snapshot.

6. **[P2] The simultaneous-power lemma needs a named compactness/Dirichlet
   seam and an import decision.**

   **Anchor and evidence.** The theorem `norm_le_of_power_sum_bound` is true,
   and chapter lines 882--891 correctly avoid phase cancellation by aligning
   all maximal-modulus roots with multiplicity. But “simultaneous Dirichlet
   approximation supplies `q_m`” is the only boundary for this new result.
   Pinned Mathlib's `AddCircle.exists_norm_nsmul_le` is one-dimensional and
   lives in `Mathlib.NumberTheory.WellApproximable`, which is not in the listed
   import union. It does not directly give the simultaneous finite-product
   statement used here.

   **Exact repair.** State and prove a helper for a finite family of unit
   complex numbers:

   ```text
   exists_unbounded_aligned_powers
     (u : Fin s -> Circle) :
     exists n : Nat -> Nat,
       StrictMono n and forall i, u i ^ n m -> 1.
   ```

   Prove it either by a finite-box pigeonhole argument with an explicit common
   exponent, or by recurrence of powers in the compact group `Fin s -> Circle`.
   Add the required Mathlib import if the existing one-circle theorem is used.
   Then state the maximal/smaller-root limit split as a separate lemma and make
   `norm_le_of_power_sum_bound` a short corollary.

7. **[P2] Two displayed internal APIs do not match their claimed abstraction
   boundary.**

   **Anchor and evidence.** At lines 259--265 the prose calls
   `waringVariable` implementation-internal, but the Markdown displays a
   public `noncomputable def`; the dedicated diagnostic validator makes it
   `private`, while the strict generated validator necessarily exposes it.
   At lines 347--357, `monicPhase_affine_last` carries `psi`, `hpsi`, `hf0`,
   and `d<p`, although the conclusion contains no character and the affine
   polynomial identity needs none of those assumptions. The constant term is
   independent of the updated `u_d`, and the small-characteristic hypotheses
   belong only in the following orthogonality theorem.

   **Exact repair.** Mark `waringVariable` literally `private` in the chapter
   and regenerate the validators. Generalize the affine theorem to a
   `CommRing` polynomial (or at least remove `psi`, `hpsi`, `hf0`, and `d<p`),
   retaining only `natDegree f=d`, `0<d`, and `d<=n`. Keep the prime-field,
   nontrivial-character hypotheses in
   `artinCoefficient_eq_zero_of_degree_le`, where they are mathematically
   used.

## Verified mathematical points with no finding

- **Sharp source constant.** Cochrane--Pinner (1.3), extract lines 27--35, has
  constant `deg(f)+ell-1`; for a polynomial pure additive sum, `M=deg f` and
  `L=ell=0`, giving exactly `(deg f-1)*sqrt p`. The chapter does not obtain the
  sharp result from the weaker ACK Appendix A.5 display.

- **Degree zero and degree one.** The repaired definition using
  `range (max 1 f.natDegree)` makes the constant-polynomial L-object exactly
  `1`, so `artinLPolynomial_coeff_zero`, its degree bound, and the constant
  regression are true. For `deg f=1`, multiplication by the nonzero leading
  coefficient and translation give a zero character sum. Over extensions,
  `FiniteField.trace_to_zmod_nondegenerate` supplies the nonzero trace
  functional. Consequently the point-count statement also handles degree one
  without Stepanov parameters. When `p=2`, `0<deg f<p` forces precisely this
  branch.

- **Newton--Waring formulas.** The recursive sign
  `s_m=-(m*u_m+sum_(j<m)u_j*s_(m-j))`, the location of `u_d`, and the affine
  coefficient `-d*leadingCoeff f` agree with the source Waring formulas on
  printed p. 6, extract lines 376--390. The cancellation for every `n>=d` is
  valid because `0<d<p` makes that coefficient nonzero and every nontrivial
  additive character on the prime field stays nontrivial after a unit shift.

- **Artin--Schreier theorem and transport.** The public irreducibility theorem
  is true. A finite pole of a rational solution `h` would have order multiplied
  by `p` in `h^p-h`, forcing `h` to be a polynomial; its positive degree would
  make `deg(h^p-h)` divisible by `p`, impossible for `0<deg f<p`. The later
  formula with `s=f+...+f^(p^(u-1))` really transforms
  `z^p-z=f(0)-f^(p^u)` into
  `w^p-w+(f-f(0))=0`. Findings 3--4 concern the missing exact Lean interfaces,
  not the truth of these facts.

- **Hasse multiplicity.** The definition of `VanishesToOrderAtLeast`, its
  equivalence with `R<=rootMultiplicity`, and the degree divided by
  multiplicity bound are correct, including `R=0`. The freezing formula is
  correct for `r<p^m`; in positive characteristic the lower base-`p` digits
  force `choose (j*p^m) r=0` for `0<r<p^m`, and `r=0` is immediate.

- **Trace-only parameter arithmetic.** For `d>=2`, `d<p`, and large `n`, the
  chosen `K=floor(p^(u-2)/(2d))` is positive and at least `2d`,
  `R=pK<p^u`, and both `dimension_ok` and `norm_degree_ok` hold for even and
  odd `n`. The characteristic-two case cannot enter this branch. The source's
  mixed count on printed p. 14 is
  `q(q-1)S(K+1)` variables and
  `R(S+d(q-1)q^(u-1)+...+K)` equations; deleting the Kummer/norm coordinate
  yields exactly the chapter's `p*S*(K+1)` and displayed pure-additive
  equation count.

- **Fiber upper and lower estimates.** Mapping a nonzero auxiliary into
  `GaloisField p n` preserves nonzeroness. Dividing its degree bound by
  `R=pK` gives exactly
  `p^(n-1)+(S+d(p-1)p^(n-1))/R`. The `p` fibers partition all `p^n` elements;
  summing the upper bound over the other `p-1` fibers gives the claimed lower
  bound. The estimate is therefore uniform in `b` and of order
  `(sqrt p)^n` after the even/odd split.

- **Root-radius deduction.** The simultaneous-alignment argument proves the
  stated upper root bound; no lower bound or leading L-coefficient is needed.
  Multiplicities are handled correctly because every maximal phase is aligned
  near one before the smaller roots are discarded.

- **Constant twist, trace sign, and standard character.** For
  `g=eraseConstant f`,
  `S_n(psi,f)=psi(f(0))^n*S_n(psi,g)` and every character value has norm one.
  Since `L(z)=prod_i(1-omega_i*z)`, the coefficient comparison gives
  `S_n=-sum_i omega_i^n`; at `n=1`, twisting the roots by
  `t=psi(f(0))` therefore preserves the displayed minus sign.
  Pinned `ZMod.stdAddChar` is the positive character
  `exp(2*pi*I*j/p)`, matching Chapter 05b's residue enumeration, and
  `ZMod.isPrimitive_stdAddChar` makes it nontrivial for prime `p`.

- **Trust boundary.** No curve Riemann hypothesis, class-field theorem,
  Riemann--Roch theorem, or imported restatement of the desired Weil bound is
  hidden in the displayed dependency graph. The unresolved work in Findings
  1--4 is elementary algebra, finite-field orbit accounting, finite linear
  algebra, and Stepanov norm descent, but it is still theorem-sized work that
  must be recursively exposed before implementation approval.

## Verdict

**BLOCK.** The final public theorem statements appear mathematically true and
the delicate numerical specialization of Cochrane--Pinner is sound. There is
no remaining curve-RH or class-field dependency. However, four independent
`P1` proof boundaries still prevent a clean-room conclusion that the chapter
is sufficient for a sorry-free Lean implementation: the Artin trace identity,
the direct trace-only constraint system, the nonzero translation-product
descent, and the flawed proof of the Artin--Schreier root criterion. The stale
repository snapshot manifest is an additional acceptance-gate blocker.

A repaired, newly hashed snapshot needs a fresh independent review. This
report cannot self-approve any authored repair.
