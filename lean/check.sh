#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
lake="${PM_ARCH_LAKE_BIN:-lake}"
"$lake" build
"$lake" env lean AuditStrict.lean
"$lake" env lean Audit.lean
"$lake" env lean classification/Audit.lean
