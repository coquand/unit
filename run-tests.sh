#!/bin/sh
# check every example; each must print OK
OUT=$(mktemp); SEG=$(cabal list-bin seg 2>/dev/null)
for f in examples/*.seg; do
  if timeout 60 $SEG "$f" > "$OUT" 2>&1; then echo "ok   $f"; else echo "FAIL $f"; cat "$OUT"; fi
done
