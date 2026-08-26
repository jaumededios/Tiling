# PM7 independent follow-up: Chen and terminal complete sums

Date: 2026-08-24

This is the separate author-independent follow-up to
`pm7-production-chen-terminal-independent-rereview.md`.  It does not overwrite
the blocking verdict on the earlier Chen hash.  The reviewer authored neither
production module and did not edit any reviewed production or validator source.

## Corrected snapshot

- `TranslationalTilings/NumberTheory/ChenCompleteSum.lean`:
  `df9fc411e36e60c1e0affba9945800304297a77d23b01adec5edc47777bec0ec`;
- `TranslationalTilings/NumberTheory/CompleteExponentialSum.lean`:
  `49cb393764e53f1e89f373ca09245bb6fbd88fe858e8c77215d463f4da35098c`.

The validator hashes are unchanged from the blocking report.  This is a
bounded production/validator approval, not a global repository snapshot
approval: the concurrent repository-wide `blueprint/SNAPSHOT.sha256` still
names an earlier tree.

## Verdict

**APPROVE** the corrected bounded PM7 snapshot.  No P0--P3 finding remains.

## Blocking finding disposition

The three inaccurate public comments are repaired exactly:

- `factorizationScalarLookup` now documents off-support default `0`, matching
  its `if ... else 0` body;
- `factorizationScalarLookup_of_not_mem` now documents default `0`, matching
  its conclusion;
- `chenLargePrimeThreshold_le` now documents `(d + 1) ^ 6`, matching the
  theorem's exported right-hand side.

The surrounding definitions, theorem statements, and bodies remain conformant
to the unchanged generated validator.  No mathematical or API change was
needed.

## Independent follow-up evidence

- Chen direct compile with `-DwarningAsError=true`: exit 0, no output, 7.49s.
- Terminal direct compile with `-DwarningAsError=true`: exit 0, no output,
  3.39s.
- Joint Lake build: success, 3,414 jobs.
- The downstream build through `TranslationalTilings.Analysis.PolynomialRigidity`
  rebuilt Chen, terminal, and their consumer chain and completed successfully
  at 3,432 jobs.
- Appending `#lint only docBlame` through stdin, without changing production,
  found zero errors in Chen's 120 declarations plus 207 automatically generated
  declarations and zero errors in the terminal file's 27 declarations plus 16
  automatically generated declarations.
- There are exactly 82 module/declaration documentation comments across the two
  sources: one module comment and one public-declaration comment for each of the
  exact 60+20 owned boundary.
- A fresh independent source/ledger comparison found exactly 60 Chen and 20
  terminal public declarations, with empty source-only and ledger-only sets.
- Byte-for-byte production/validator comparison of `#check @name` output passed
  for all 80 names.  Byte-for-byte `#print` comparison passed for all 13 public
  definitions, abbreviations, and structures.
- Both lookup theorems remain members of the production `simp` extension.
- `generate_integrated.py --check`, `generate_modules.py --check`, and the
  validator-local generated-hash check all exited zero; the module check again
  reported 29 modules, 869 declarations, and an acyclic DAG.
- A fresh trust check on the stationary descent, CRT certificate, conditional
  global theorem, Weil discharge, and two effective terminal endpoints reported
  only `propext`, `Classical.choice`, and `Quot.sound`.  The preceding full PM7
  pass already checked all 80 owned declarations.
- Forbidden-trust, validator-import, resource-override, retained `#lint`/
  `docBlame`, and trailing-whitespace scans were empty.

## Final disposition

The prior P2 attribute-parser/ownership repair remains accepted, and the P3
documentation repair now accurately describes the public Lean API.  The
conditional Chen boundary, unconditional terminal discharge, composite
quadratic join, explicit effective constant, and sole downstream integral
consumer remain stable.  No proof, API, dependency, documentation, or trust
change is requested for these hashes.
