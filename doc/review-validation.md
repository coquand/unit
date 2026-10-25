# Validation of the current checker

This record concerns the checker at revision `ea91747`, in which
`split` values and data types are compared only by code identity and
convertible dynamic arguments. No branch, motive or constructor telescope is
compared. It does not reproduce Table 1's four historical variants.

Removing the split branch-comparison fallback exposed three cross-level uses
of Boolean tests in `core`, and two failures in coefficient naturality in
`CechHigher`, shared by `em`, `cca` and `ccacoh`. The repairs give the
Boolean operations one definition in `core/Base.seg`, and the tuple
operations one definition independent of the coefficient group in
`sag/cca/Cochains.seg`. Removing the comparison of constructor telescopes
for data types required no change. The negative regression in
`examples/primrec.seg` rejects equality of the same split instantiated at
different unused arguments.

## Provenance

- Recorded at: `2026-10-25T12:31:48.285963+00:00`.
- Revision: `ea9174794ebc1f38abe64de4f18317c03f75ca17`. Exact source and input hashes are in [manifest.json](review-validation/manifest.json).
- Platform: `macOS-27.0.1-arm64-arm-64bit-Mach-O`. CPU model and RAM were not captured; this is validation, not a controlled performance comparison.
- Compiler: GHC `9.6.7`; Cabal `3.14.2.0`; build profile `-O1`.
- Build command, from the repository root: `cabal build exe:seg --offline`.
- Executable SHA-256: `860448719b350edda610b988dc7187120765ad52cd4e170c6601804ada91890a`.
- The CPU times below come from the checker's whole-run summary, loading included; they are not the per-declaration timings of the historical table.
- Input files changed during the run: none.

## Results

| Entry point | Declarations | Failed | Whole-run CPU time |
| --- | ---: | ---: | ---: |
| [core/All.seg](review-validation/core.log) | 18051 | 0 | 46.52 s |
| [sag/chatelet/All.seg](review-validation/sag-chatelet.log) | 15555 | 0 | 6.72 s |
| [sag/stone/All.seg](review-validation/sag-stone.log) | 3269 | 0 | 0.97 s |
| [sag/stoneseq/All.seg](review-validation/sag-stoneseq.log) | 4453 | 0 | 1.30 s |
| [sag/cca/All.seg](review-validation/sag-cca.log) | 8421 | 0 | 2.77 s |
| [sag/ccacoh/All.seg](review-validation/sag-ccacoh.log) | 8515 | 0 | 3.86 s |
| [sag/em/All.seg](review-validation/sag-em.log) | 3252 | 0 | 1.70 s |

The regression output matches `tests.expected` exactly. That expected output
includes the diagnostic failures in `locks.seg` (`byDeps`) and `unfilled.seg`,
which fail by design.

## Reproduce

From the `unit` repository root:

```sh
cabal build exe:seg --offline
python3 doc/review-validation/run.py
```

The runner records exact commands, exit codes, logs, input hashes and elapsed
wall times in [manifest.json](review-validation/manifest.json). Given labels
(`regressions`, `core`, `sag-chatelet`, ...), it runs only those checks and
merges them into a manifest of the same revision, inputs and executable, so
that the validation can be made in several short runs; this record was made
in two. These finite checks do not establish soundness or completeness of
conversion.

## Historical measurements

The original revision, machine and build settings for Table 1 have not been
identified in the available measurement record. The historical counts and CPU
times remain labelled preliminary in the paper. The results above use a
different conversion of splits and data types and some shared definitions;
they should not be substituted for a reconstruction of the historical
experiments.
