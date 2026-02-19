# Tutorial: Using the zkEVM Circuit Verifier

## Getting Started

This tutorial walks you through using the zkEVM Circuit Verifier prototype.

## Installation

### Step 1: Check Prerequisites

```bash
# Check Python 3
python3 --version
# Should be 3.7 or higher

# Check if Lean4 is installed
lean --version
# If not installed, the install script will handle it
```

### Step 2: Run Installation

```bash
./install.sh
```

This will:
- Install Lean4 (if not present)
- Install Python dependencies (minimal)
- Verify everything works

## Running the Demo

### Quick Demo

```bash
./demo.sh
```

This runs the complete pipeline:
1. Parse all circuits in `circuits/`
2. Generate Lean4 proofs in `proofs/`
3. Verify all proofs
4. Generate reports in `reports/`

## Understanding the Output

### Parser Output

```
✓ Parsed circuit: Circuit(add): 2 inputs, 1 outputs
✓ Generated proofs/add_proof.lean
```

**What happened:**
- Read `circuits/add.py`
- Extracted circuit definition
- Generated Lean4 code
- Wrote to `proofs/add_proof.lean`

### Verifier Output

```
✅ PASS - add_proof.lean
```

**What happened:**
- Ran `lean proofs/add_proof.lean`
- Lean4 compiler verified the proof
- Mathematical correctness guaranteed

### Reporter Output

```
✓ Generated reports/add_report.md
✓ Generated reports/summary.md
```

**What happened:**
- Created verification certificate
- Documented formal guarantees
- Generated summary of all circuits

## Exploring the Results

### View Generated Proof

```bash
cat proofs/add_proof.lean
```

You'll see:
```lean
-- Auto-generated proof for circuit: add

def add_circuit (a b : Nat) : Nat := a + b

theorem add_correct (a b : Nat) :
  add_circuit a b = a + b := by
  rfl
```

**Understanding the proof:**
- `def add_circuit` - Function definition
- `theorem add_correct` - Correctness statement
- `by rfl` - Proof by reflexivity (trivial equality)

### View Verification Report

```bash
cat reports/add_report.md
```

Contains:
- Circuit specification
- Verification method
- Formal correctness statement
- Security guarantees

### View Summary

```bash
cat reports/summary.md
```

Shows:
- All circuits verified
- Success rates
- Next steps for production

## Creating Your Own Circuit

### Step 1: Define Circuit

Create `circuits/square.py`:

```python
"""Square circuit example"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

square_circuit = Circuit(
    name="square",
    description="Square a field element",
    inputs=["x: Field"],
    outputs=["y: Field"],
    constraints=["y = x * x"]
)
```

### Step 2: Generate Proof

```bash
python -m src.parser circuits/square.py
```

Output:
```
✓ Parsed circuit: Circuit(square): 1 inputs, 1 outputs
✓ Generated proofs/square_proof.lean
```

### Step 3: Verify

```bash
python -m src.verifier
```

Output:
```
✅ PASS - square_proof.lean
```

### Step 4: Generate Report

```bash
python -m src.reporter
```

Output:
```
✓ Generated reports/square_report.md
```

### Step 5: View Results

```bash
cat reports/square_report.md
```

## Understanding Circuits

### Circuit Structure

```python
Circuit(
    name="example",           # Circuit identifier
    description="...",        # Human-readable description
    inputs=["a: Field"],      # Input variables
    outputs=["b: Field"],     # Output variables
    constraints=["b = a"]     # Constraint equations
)
```

### Supported Constraints (Prototype)

**Addition:**
```python
constraints=["c = a + b"]
```

**Multiplication:**
```python
constraints=["c = a * b"]
```

**Comparison:**
```python
constraints=["valid = (value <= max)"]
```

### Complex Constraints (Future)

Not yet supported in prototype:
```python
# Memory operations
constraints=["mem[addr] = value"]

# Cryptographic operations
constraints=["hash = keccak256(input)"]

# State transitions
constraints=["state_new = apply(state_old, tx)"]
```

## Troubleshooting

### Error: Lean4 not found

**Solution:**
```bash
./install.sh
source ~/.profile
```

### Error: Module not found

**Solution:**
```bash
# Make sure you're in project root
cd zkevm-verifier-prototype

# Run with python -m
python -m src.parser circuits/add.py
```

### Error: Verification failed

**Check:**
1. Lean4 proof syntax correct?
2. Circuit constraints valid?
3. Run: `lean proofs/<circuit>_proof.lean` manually

### Error: No circuits found

**Check:**
1. Are .py files in `circuits/` directory?
2. Do they define Circuit objects?
3. Run: `ls circuits/`

## Advanced Usage

### Manual Steps

Instead of `./demo.sh`, run each step:

```bash
# Step 1: Parse one circuit
python -m src.parser circuits/add.py

# Step 2: Verify one proof
lean proofs/add_proof.lean

# Step 3: Verify all proofs
python -m src.verifier

# Step 4: Generate reports
python -m src.reporter
```

### Modifying Generated Proofs

1. Generate proof: `python -m src.parser circuits/add.py`
2. Edit: `vim proofs/add_proof.lean`
3. Verify: `lean proofs/add_proof.lean`
4. If it compiles, proof is valid!

### Batch Processing

```bash
# Parse all circuits
for circuit in circuits/*.py; do
    python -m src.parser "$circuit"
done

# Verify all at once
python -m src.verifier

# Generate all reports
python -m src.reporter
```

## Next Steps

### Learn Lean4

**Resources:**
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Lean4 Documentation](https://lean-lang.org/documentation/)
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)

### Study zkSNARKs/zkSTARKs

**Resources:**
- [Vitalik's zkSNARK Intro](https://vitalik.eth.limo/general/2021/01/26/snarks.html)
- [StarkWare Docs](https://docs.starkware.co/)
- [RISC Zero Docs](https://dev.risczero.com/)

### Contribute to Production Version

After grant funding:
- Help build Rust implementation
- Add new circuit types
- Improve proof generation
- Write documentation

## Tips & Best Practices

### Circuit Naming

- Use lowercase, underscores
- Be descriptive: `memory_read` not `mr`
- Consistent naming helps reports

### Constraint Writing

- Keep constraints simple in prototype
- One operation per constraint
- Test with simple values first

### Debugging

- Start with simplest possible circuit
- Verify each part works
- Build up complexity gradually

### Documentation

- Add good descriptions to circuits
- Comment complex constraints
- Explain purpose in circuit file

## Common Patterns

### Arithmetic Circuit

```python
Circuit(
    name="operation",
    inputs=["a: Field", "b: Field"],
    outputs=["c: Field"],
    constraints=["c = a op b"]  # op = +, *, etc.
)
```

### Comparison Circuit

```python
Circuit(
    name="check",
    inputs=["x: Field", "y: Field"],
    outputs=["result: Bool"],
    constraints=["result = (x <= y)"]
)
```

### Transform Circuit

```python
Circuit(
    name="transform",
    inputs=["input: Field"],
    outputs=["output: Field"],
    constraints=["output = f(input)"]
)
```

## FAQ

**Q: Can I use this in production?**  
A: No, this is a prototype. Production version requires grant funding.

**Q: Does this work with real zkVMs?**  
A: Not yet. Prototype uses simple circuits. Production will integrate with OpenVM, SP1, etc.

**Q: How long does verification take?**  
A: <1 second per simple circuit. Complex circuits would take longer.

**Q: Can I verify my zkEVM circuits with this?**  
A: Yes, but you'd need to adapt them to the Circuit format. Production version will support direct import.

**Q: Is the verification sound?**  
A: Yes! Lean4 provides mathematical guarantees. However, the Circuit → Lean translation layer should be audited.

---

**Happy verifying! 🎉**

For questions or issues, see README.md for contact information.
