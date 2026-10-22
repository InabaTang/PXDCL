#!/bin/bash
# Apply all mixed clause fixes to the Cadical solver.
# Run from the cadical/ directory.
set -e

SRC=src

echo "=== Applying mixed clause fixes ==="

# ── 1. propagate.cpp ── add mixed clause two-watch propagation ──
# Find the insertion point: after the XOR watch loop
LINE=$(grep -n "//printf.*xor_propagations end" $SRC/propagate.cpp | head -1 | cut -d: -f1)
if [ -z "$LINE" ]; then
  # Alternative: find "const const_watch_iterator eow = ws.end ()"
  LINE=$(grep -n "const const_watch_iterator eow = ws.end ()" $SRC/propagate.cpp | head -1 | cut -d: -f1)
  LINE=$((LINE - 1))
fi
echo "  propagate.cpp insertion at line $LINE"

# Add mixed clause loop + parity tracking
# (This is too complex for sed; need manual insertion)
# For now, verify the file is intact
echo "  propagate.cpp needs manual insertion of mixed clause propagation loop"

# ── 2. analyze.cpp ── add mixed clause analysis + skip reordering ──
echo "  analyze.cpp needs mixed clause handling"

# ── 3. backtrack.cpp ── add parity revert ──
LINE=$(grep -n "SEGA.*decrement\|Mixed clause parity revert\|unassign(lit)" $SRC/backtrack.cpp | head -1 | cut -d: -f1)
echo "  backtrack.cpp at line $LINE"

# ── 4. decide.cpp ── add guards + explicit conflict scan ──
echo "  decide.cpp needs guards and conflict scan"

# ── 5. collect.cpp ── add GC null-out + flush mixed watches ──
echo "  collect.cpp needs GC fixes"

# ── Summary ──
echo ""
echo "=== Manual changes still needed ==="
echo "  propagate.cpp: mixed clause two-watch loop (~80 lines)"
echo "  analyze.cpp: XOR-style flip + skip reordering (~30 lines)"
echo "  backtrack.cpp: parity revert (~10 lines)"
echo "  decide.cpp: guards + explicit conflict scan (~30 lines)"
echo "  collect.cpp: GC null-out + flush_mixed_watches (~20 lines)"
echo ""
echo "Total: ~170 lines across 5 files"
