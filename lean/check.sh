#!/bin/bash
# Local incremental check against an already-built Mathlib on this machine.
# Set MATHLIB_PROJECT to any lake project whose Mathlib is built.
# (Portable route for other machines: `lake exe cache get && lake build`.)
set -e
LEAN_DIR="$(cd "$(dirname "$0")" && pwd)"
MATHLIB_PROJECT="${MATHLIB_PROJECT:-$HOME/groups/gruppelib}"
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
