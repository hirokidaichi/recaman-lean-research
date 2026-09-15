#!/usr/bin/env bash
# Negative and positive tests for the research-harness gates (INC-20260915-01).
# Run from the repository root: bash scripts/test_harness_gates.sh
set -euo pipefail
cd "$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP" docs/statement_audits/E-99[0-9].md' EXIT
REG=docs/EVIDENCE_REGISTRY.tsv
fail=0
expect_fail() { # name, command...
  local name="$1"; shift
  if "$@" >/dev/null 2>"$TMP/err"; then echo "FAIL (passed but should fail): $name"; fail=1
  else echo "ok   (rejected): $name  -- $(head -1 "$TMP/err")"; fi
}
expect_pass() {
  local name="$1"; shift
  if "$@" >/dev/null 2>"$TMP/err"; then echo "ok   (accepted): $name"
  else echo "FAIL (rejected but should pass): $name -- $(head -1 "$TMP/err")"; fail=1; fi
}
row() { printf 'E-%s\tPROVED-LEAN\ttest\tclaim\tRecaman/AuditSalvage.lean\t%s\tgate\n' "$1" "$2"; }
SUBST=Recaman.TwelveGateT6Unconditional.tight_avoiding_le_two_all_lag_three_general
WRAP=Recaman.a_zero_eq_zero

# --- positive: the live registry passes all gates
expect_pass "live registry" python3 scripts/harness_gate.py --check-registry "$REG"
expect_pass "live protected claims" python3 scripts/harness_gate.py --check-protected "$REG" docs/PROTECTED_CLAIMS.tsv

# --- G1 unresolved symbol
{ cat "$REG"; row 990 Recaman.no_such_theorem_xyz; } > "$TMP/g1.tsv"
expect_fail "G1 unresolved symbol" python3 scripts/harness_gate.py --check-registry "$TMP/g1.tsv"

# --- G2/G3 pure-arithmetic tautology (a real tautology compiled into a scratch module)
mkdir -p "$TMP/mod"
cat > "$TMP/pure.lean" <<'LEAN'
namespace Recaman
theorem gate_test_taut (card_U card_D k : Nat) (h_rem : card_U - k ≤ card_D - k) (hkU : k ≤ card_U) (hkD : k ≤ card_D) : card_U ≤ card_D := by omega
theorem gate_test_xx (k : Nat) : k = k := rfl
end Recaman
LEAN
expect_fail "lint-module: pure-arithmetic module has no substantive theorem" python3 scripts/harness_gate.py --lint-module "$TMP/pure.lean"

# --- G3 wrapper-only row
{ cat "$REG"; row 991 "$WRAP"; } > "$TMP/g3.tsv"
expect_fail "G3 wrapper-only symbols" python3 scripts/harness_gate.py --check-registry "$TMP/g3.tsv"

# --- G4 name inflation (rename a substantive theorem's row to an inflated module via a scratch copy is not
#     possible without a module; test the regex through a row citing a real theorem in an inflated name)
{ cat "$REG"; row 992 Recaman.grand_permanent_high_internal_blocker_synthesis; } > "$TMP/g4.tsv"
python3 scripts/harness_gate.py --check-registry "$TMP/g4.tsv" >/dev/null 2>"$TMP/err" && { echo "FAIL: G4 inflated name accepted"; fail=1; } || \
  { grep -q 'G4' "$TMP/err" && echo "ok   (rejected): G4 inflated name -- $(grep G4 "$TMP/err" | head -1)" || { echo "FAIL: G4 not the reason"; fail=1; }; }

# --- G5 statement audit missing, then present
{ cat "$REG"; row 993 "$SUBST"; } > "$TMP/g5.tsv"
expect_fail "G5 missing statement audit" python3 scripts/harness_gate.py --check-registry "$TMP/g5.tsv"
python3 scripts/harness_gate.py --audit-template E-993 "$TMP/g5.tsv" > docs/statement_audits/E-993.md
expect_pass "G5 statement audit present with verbatim signature" python3 scripts/harness_gate.py --check-registry "$TMP/g5.tsv"
sed -i '' 's/lag u = 3 ∨ lag u = 7/lag u = 3/' docs/statement_audits/E-993.md
expect_fail "G5 statement audit with altered signature" python3 scripts/harness_gate.py --check-registry "$TMP/g5.tsv"
rm -f docs/statement_audits/E-993.md

# --- P protected label changed silently
sed 's/^E-070\tCONJECTURED/E-070\tPROVED-LEAN/' "$REG" > "$TMP/p.tsv"
expect_fail "P protected label E-070 promoted without approval file change" python3 scripts/harness_gate.py --check-protected "$TMP/p.tsv" docs/PROTECTED_CLAIMS.tsv

if [[ "$fail" -eq 0 ]]; then echo "harness gate tests: all passed"; else echo "harness gate tests: FAILURES" >&2; exit 1; fi
