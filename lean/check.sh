#!/bin/bash
# Local incremental single-file check against this project's built Mathlib
# (run `lake exe cache get && lake build` once first). Set MATHLIB_PROJECT to
# borrow another lake project's built Mathlib instead.
set -e
LEAN_DIR="$(cd "$(dirname "$0")" && pwd)"
MATHLIB_PROJECT="${MATHLIB_PROJECT:-$LEAN_DIR}"
LP=$(cd "$MATHLIB_PROJECT" && lake env printenv LEAN_PATH)
export LEAN_PATH="$LEAN_DIR/.build:$LP"
mkdir -p "$LEAN_DIR/.build/UniversalWords"
for m in "$@"; do
  echo "── $m"
  lean -R "$LEAN_DIR" "$LEAN_DIR/UniversalWords/$m.lean" \
       -o "$LEAN_DIR/.build/UniversalWords/$m.olean" \
       -i "$LEAN_DIR/.build/UniversalWords/$m.ilean"
done
echo "ALL OK"
