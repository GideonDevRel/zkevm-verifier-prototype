# Dockerfile for zkEVM Circuit Formal Verification Framework
# Lean stdlib only (no Mathlib) - Fast build!

FROM ubuntu:22.04

# Prevent interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    python3 \
    python3-pip \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Install Lean 4.14.0 via elan
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.14.0
ENV PATH="/root/.elan/bin:${PATH}"

# Set working directory
WORKDIR /app

# Copy lakefile and toolchain first (for caching)
COPY lean-toolchain lakefile.lean ./

# Initialize Lake project
RUN lake update

# Copy all source files
COPY circuits/ ./circuits/
COPY src/ ./src/
COPY zkEVM/ ./zkEVM/
COPY proofs/ ./proofs/
COPY reports/ ./reports/
COPY *.sh ./
COPY *.md ./
COPY LICENSE ./
COPY requirements.txt ./

# Install Python dependencies
RUN pip3 install --no-cache-dir -r requirements.txt

# Build all Lean proofs (stdlib only - fast!)
RUN lake build zkEVM

# Make scripts executable
RUN chmod +x *.sh

# Set Python path
ENV PYTHONPATH=/app

# Create output directories
RUN mkdir -p /app/output/proofs /app/output/reports

# Verify installation
RUN python3 -c "import sys; sys.path.insert(0, '/app'); from circuits import add, multiply, range_check, poseidon, ecc_add; print('✓ All circuits loaded')"
RUN lake build zkEVM && echo "✓ All proofs verified"

# Default command
CMD ["/bin/bash"]

# Metadata
LABEL maintainer="zkEVM Verification Team"
LABEL description="Formal verification framework for zkEVM circuits (Lean stdlib only)"
LABEL version="2.0.0-stdlib"
