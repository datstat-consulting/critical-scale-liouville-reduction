#!/usr/bin/env bash
set -euo pipefail
FILE=${1:-FixedShiftLiouville.lean}
printf 'axiom: '; grep -Ec '\baxiom\b' "$FILE" || true
printf 'sorry: '; grep -Ec '\bsorry\b' "$FILE" || true
printf 'admit: '; grep -Ec '\badmit\b' "$FILE" || true
