#!/usr/bin/env bash
# Verify that the same strict audit rejects admitted and newly axiomatized proofs.
set -euo pipefail
cd -- "$(dirname -- "$0")"
audit_lake="${PM_ARCH_LAKE_BIN:-lake}"
audit_tmp="$(mktemp -d "${TMPDIR:-/tmp}/pmarch-audit.XXXXXX")"
trap 'rm -rf -- "$audit_tmp"' EXIT
for kind in admitted axiom; do
  {
    printf 'import PMArch\nimport Lean\n'
    if [[ "$kind" == admitted ]]; then
      printf 'theorem PMArch.auditNegative : False := by sorry\n'
    else
      printf 'axiom PMArch.auditNegative : False\n'
    fi
    sed '1,2d' AuditStrict.lean
  } > "$audit_tmp/Negative.lean"
  if "$audit_lake" env lean "$audit_tmp/Negative.lean" > "$audit_tmp/result.log" 2>&1; then
    cat "$audit_tmp/result.log"
    printf 'ERROR: strict audit accepted %s negative control\n' "$kind" >&2
    exit 1
  fi
  if ! grep -q 'Unapproved axiom' "$audit_tmp/result.log"; then
    cat "$audit_tmp/result.log"
    printf 'ERROR: negative control failed for an unrelated reason\n' >&2
    exit 1
  fi
  printf 'Strict audit rejected %s negative control\n' "$kind"
done
