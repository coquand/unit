#!/bin/sh
# run-tests.sh -- the regression tests: every example's summary line,
# the read-back tests of doc/PRIMREC.md 5.4, and the summary line of
# each development in domain/.
# Compare with tests.expected:   ./run-tests.sh | diff tests.expected -
ROOT=$(cd "$(dirname "$0")" && pwd)
SEG=$(cd "$ROOT" && cabal list-bin exe:seg 2>/dev/null)
for f in "$ROOT"/examples/*.seg; do
  out=$(cd "$(dirname "$f")" && timeout 30 "$SEG" "$(basename "$f")" 2>&1)
  printf '%s\n' "$out" | grep -E 'declarations,|^SCOPE ERROR|^OK$|^FAILED|^INTERNAL' | sed 's/, [0-9.]* s$//'
done
for d in ack skipN; do
  echo "quote-test $d:"
  (cd "$ROOT/examples" && timeout 30 "$SEG" primrec.seg --quote-test $d 2>&1)
done
echo "quote-test vsum (indexed):"
(cd "$ROOT/examples" && timeout 30 "$SEG" indexed.seg --quote-test vsum 2>&1)
for f in "$ROOT"/domain/*/All.seg; do
  echo "$(basename "$(dirname "$f")"):"
  (cd "$(dirname "$f")" && timeout 30 "$SEG" All.seg 2>&1) | grep -E 'declarations,|^SCOPE ERROR|^OK$|^FAILED|^INTERNAL' | sed 's/, [0-9.]* s$//'
done
