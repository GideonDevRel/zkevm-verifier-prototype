#!/bin/bash

echo "╔════════════════════════════════════════╗"
echo "║  zkEVM Circuit Verifier - Installation ║"
echo "╚════════════════════════════════════════╝"
echo ""

# Check if Lean4 is installed
if ! command -v lean &> /dev/null; then
    echo "📦 Lean4 not found. Installing..."
    echo ""
    
    # Install Lean4 via elan
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    
    # Source profile to get lean in PATH
    if [ -f ~/.profile ]; then
        source ~/.profile
    fi
    if [ -f ~/.bashrc ]; then
        source ~/.bashrc
    fi
    
    echo ""
    echo "✓ Lean4 installed"
else
    echo "✓ Lean4 already installed: $(lean --version)"
fi

echo ""

# Check if Python3 is installed
if ! command -v python3 &> /dev/null; then
    echo "❌ Python3 not found. Please install Python 3.7+ first."
    exit 1
else
    echo "✓ Python3 found: $(python3 --version)"
fi

echo ""

# Install Python dependencies (minimal)
if [ -f requirements.txt ]; then
    echo "📦 Installing Python dependencies..."
    pip3 install -r requirements.txt --quiet
    echo "✓ Dependencies installed"
else
    echo "⚠ No requirements.txt found (optional)"
fi

echo ""
echo "╔════════════════════════════════════════╗"
echo "║     Installation Complete! ✅           ║"
echo "╚════════════════════════════════════════╝"
echo ""
echo "Next steps:"
echo "  1. Run demo: ./demo.sh"
echo "  2. Read docs: cat README.md"
echo ""
