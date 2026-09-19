#!/usr/bin/env bash
# Reproduce the verification of JSP-000584 from a clean checkout.
set -euo pipefail

echo "== toolchain =="
lean --version
lake --version

echo "== fetching pinned dependencies (revisions come from lake-manifest.json) =="
lake exe cache get

echo "== clean build =="
rm -rf .lake/build/lib/lean/JSP584
lake build JSP584

echo "== source hygiene: no sorry / native_decide / custom axioms =="
if grep -rnE '\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^axiom ' JSP584.lean JSP584/; then
  echo "FAIL: forbidden construct found"; exit 1
fi
echo "OK: source is clean"

echo "== axiom audit =="
lake env lean JSP584/Audit.lean 2>&1 | grep "depends on axioms" -A3
