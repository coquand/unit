# Validation after review revisions

This record concerns the current checker after removing the split branch-comparison fallback. It does not reproduce Table 1’s four historical variants.

Split values compare only by code identity and convertible dynamic arguments. No branch or motive comparison is performed. The negative regression in `examples/primrec.seg` rejects equality of the same split instantiated at different unused arguments.

The rerun initially exposed three cross-level uses of Boolean tests in `core`, and two failures in coefficient naturality in `CechHigher`, shared by `em`, `cca` and `ccacoh`. The repairs give Boolean operations one definition in `core/Base.seg`, and tuple operations one definition independent of the coefficient group in `sag/cca/Cochains.seg`. The final results below include these repairs.

## Provenance

- Recorded at: `2026-10-25T11:27:27.836526+00:00`.
- Checkout base: `7951ba7647c7c99bafb253d89b98aba8c00a230c`, with working-tree changes. Exact source and input hashes are in [manifest.json](review-validation/manifest.json).
- Platform: `macOS-27.0.1-arm64-arm-64bit-Mach-O`; architecture `arm64`. CPU model and RAM were not captured; this is validation, not a controlled performance comparison.
- Compiler: GHC `9.6.7`; Cabal `3.14.2.0`; build profile `-O1`.
- Build command, from the repository root: `cabal build exe:seg --offline`.
- Executable SHA-256: `0d136a68bbeecd2c99e74d3979985ee965b8af6461ebbbcc4caee606155f5f43`.
- No diagnostic counters were enabled in these development reruns. The CPU times below come from the checker’s normal whole-run summary, including loading; they are not the per-declaration timings of the historical table.
- Input files changed during the final run: none.

## Results

| Entry point | Declarations | Failed | Whole-run CPU time |
| --- | ---: | ---: | ---: |
| [core/All.seg](review-validation/core.log) | 18051 | 0 | 46.88 s |
| [sag/chatelet/All.seg](review-validation/sag-chatelet.log) | 15555 | 0 | 6.90 s |
| [sag/stone/All.seg](review-validation/sag-stone.log) | 3269 | 0 | 1.00 s |
| [sag/stoneseq/All.seg](review-validation/sag-stoneseq.log) | 4453 | 0 | 1.35 s |
| [sag/cca/All.seg](review-validation/sag-cca.log) | 8421 | 0 | 2.86 s |
| [sag/ccacoh/All.seg](review-validation/sag-ccacoh.log) | 8515 | 0 | 3.96 s |
| [sag/em/All.seg](review-validation/sag-em.log) | 3252 | 0 | 1.71 s |

The regression output matches `tests.expected` exactly. That expected output includes the existing diagnostic failures in `locks.seg` (`byDeps`) and `unfilled.seg`; these are not new failures. The updated `primrec.seg` checks all pass.

## Reproduce

From the `unit` repository root:

```sh
cabal build exe:seg --offline
python3 doc/review-validation/run.py
```

The runner records exact commands, exit codes, logs, input hashes and elapsed wall times in [manifest.json](review-validation/manifest.json). It checks the regression output against `tests.expected` and reports inputs modified during the run. These finite checks do not establish soundness or completeness of conversion.

## Historical measurements

The original revision, machine and build settings for Table 1 have not been identified in the available measurement record. The historical counts and CPU times remain labelled preliminary in the paper. The new results above use a different split comparison and some shared definitions; they should not be substituted for a reconstruction of the historical experiments.
