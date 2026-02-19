#!/bin/bash

echo "╔════════════════════════════════════════╗"
echo "║  zkEVM Circuit Verifier - Demo        ║"
echo "╚════════════════════════════════════════╝"
echo ""

# Step 1: Parse circuits
echo "▶ Step 1: Parsing circuits..."
echo ""

for circuit in circuits/*.py; do
    if [ -f "$circuit" ]; then
        python3 -m src.parser "$circuit"
    fi
done

echo ""
echo "✓ All circuits parsed"
echo ""

# Step 2: Verify proofs
echo "▶ Step 2: Verifying proofs with Lean4..."
echo ""

python3 -m src.verifier

echo ""

# Step 3: Generate reports
echo "▶ Step 3: Generating verification reports..."
echo ""

python3 -m src.reporter

echo ""
echo "╔════════════════════════════════════════╗"
echo "║     VERIFICATION COMPLETE ✅            ║"
echo "╚════════════════════════════════════════╝"
echo ""
echo "📄 View reports:"
echo "   ls reports/"
echo "   cat reports/summary.md"
echo ""
echo "🔍 View proofs:"
echo "   ls proofs/"
echo "   cat proofs/add_proof.lean"
echo ""
echo "📚 Read documentation:"
echo "   cat README.md"
echo "   cat docs/ARCHITECTURE.md"
echo ""
