#!/bin/sh
# Compile every policy and list the enforcement rules (+cause / -suppress)
# of the generated EF program.
ENFFLASH=${ENFFLASH:-$(cd "$(dirname "$0")/../.." && pwd)/_build/default/bin/enfflash.exe}
OUT=${OUT:-build}
mkdir -p "$OUT"
for f in policies/b*.mfotl policies/all.mfotl; do
  [ -f "$f" ] || continue
  b=$(basename "$f" .mfotl)
  if "$ENFFLASH" -sig policies/banking.sig -formula "$f" -no-run -output "$OUT/$b.ef" > "$OUT/$b.log" 2>&1; then
    rules=$(grep -oE '^rule [-+][A-Za-z]+' "$OUT/$b.ef" | grep -vE '[+-](Sup|Cau)_?' | sed 's/rule //' | sort | uniq -c | tr -s ' ' | tr '\n' ' ')
    printf '%-28s OK   %s\n' "$b" "$rules"
  else
    printf '%-28s FAIL\n' "$b"; grep -v WARNING "$OUT/$b.log" | tail -3
  fi
done
