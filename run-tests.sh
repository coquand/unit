#!/bin/sh
# run-tests.sh -- the regression tests: every example (the summary line and
# the conversion fallback count) and the read-back tests of doc/PRIMREC.md 5.4.
# Compare with tests.expected:   ./run-tests.sh | diff tests.expected -
ROOT=$(cd "$(dirname "$0")" && pwd)
SEG=$(cd "$ROOT" && cabal list-bin exe:seg 2>/dev/null)
for f in "$ROOT"/examples/*.seg; do
  out=$(cd "$(dirname "$f")" && timeout 30 "$SEG" "$(basename "$f")" 2>&1)
  printf '%s\n' "$out" | grep -E 'declarations,|^split conversion fallback|^SCOPE ERROR|^OK$|^FAILED|^INTERNAL' | sed 's/, [0-9.]* s$//'
done
for d in ack skipN; do
  echo "quote-test $d:"
  (cd "$ROOT/examples" && timeout 30 "$SEG" primrec.seg --quote-test $d 2>&1)
done
