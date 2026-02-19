#!/bin/bash
# Test Script: Compile all Lean4 proofs to verify correctness
# Created: 2026-02-12

set -e

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║   Testing All Lean4 Proofs (12 files, 128 theorems)           ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""

# Color codes
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m'

PROOF_DIR="/app/proofs"
TOTAL=0
PASSED=0
FAILED=0

echo "Testing Lean4 proofs in: $PROOF_DIR"
echo ""

# Test each proof file
for proof_file in "$PROOF_DIR"/*.lean; do
    if [ -f "$proof_file" ]; then
        filename=$(basename "$proof_file")
        TOTAL=$((TOTAL + 1))
        
        echo -n "Testing $filename... "
        
        # Try to compile the proof
        if lean "$proof_file" > /dev/null 2>&1; then
            echo -e "${GREEN}✓ PASS${NC}"
            PASSED=$((PASSED + 1))
        else
            echo -e "${RED}✗ FAIL${NC}"
            FAILED=$((FAILED + 1))
            
            # Show error details
            echo "  Error details:"
            lean "$proof_file" 2>&1 | head -10 | sed 's/^/    /'
            echo ""
        fi
    fi
done

echo ""
echo "═══════════════════════════════════════════════════════════════"
echo "RESULTS:"
echo "  Total:  $TOTAL proofs"
echo -e "  Passed: ${GREEN}$PASSED${NC}"
echo -e "  Failed: ${RED}$FAILED${NC}"
echo "═══════════════════════════════════════════════════════════════"

if [ $FAILED -eq 0 ]; then
    echo -e "${GREEN}✓ All proofs compiled successfully!${NC}"
    exit 0
else
    echo -e "${RED}✗ Some proofs failed to compile.${NC}"
    exit 1
fi
