#!/bin/bash
# Quick start script for Docker deployment

set -e

echo "🐳 zkEVM Circuit Formal Verification Framework"
echo "   Docker Quick Start"
echo ""

# Check if Docker is installed
if ! command -v docker &> /dev/null; then
    echo "❌ Error: Docker is not installed"
    echo "   Install from: https://docs.docker.com/get-docker/"
    exit 1
fi

# Check if Docker Compose is installed
if ! command -v docker-compose &> /dev/null; then
    echo "❌ Error: Docker Compose is not installed"
    echo "   Install from: https://docs.docker.com/compose/install/"
    exit 1
fi

echo "✅ Docker detected"
echo "✅ Docker Compose detected"
echo ""

# Build image
echo "🔨 Building Docker image..."
docker-compose build

echo ""
echo "✅ Build complete!"
echo ""

# Run tests
echo "🧪 Running tests..."
docker-compose run --rm test

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "🎉 Quick start complete!"
echo ""
echo "Available commands:"
echo ""
echo "  # Run full demo"
echo "  docker-compose run --rm zkevm-verifier ./docker-demo.sh"
echo ""
echo "  # Interactive shell"
echo "  docker-compose run --rm zkevm-verifier bash"
echo ""
echo "  # Run specific circuit"
echo "  docker-compose run --rm zkevm-verifier python3 -c 'from circuits import poseidon; print(poseidon.poseidon_circuit)'"
echo ""
echo "  # View proofs"
echo "  docker-compose run --rm zkevm-verifier cat /app/proofs/Poseidon.lean"
echo ""
echo "  # Stop all containers"
echo "  docker-compose down"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
