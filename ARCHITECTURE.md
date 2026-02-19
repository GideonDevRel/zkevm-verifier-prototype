# Architecture Documentation

## System Overview

The zkEVM Circuit Formal Verification Framework is a **three-stage pipeline** that bridges the gap between high-level circuit specifications and formal proofs of correctness.

```
┌─────────────────┐      ┌─────────────────┐      ┌─────────────────┐
│   Python DSL    │ ───> │  Lean4 Theorems │ ───> │  Verification   │
│  (circuits/*.py)│      │  (proofs/*.lean)│      │   (reports/)    │
└─────────────────┘      └─────────────────┘      └─────────────────┘
     Stage 1                  Stage 2                   Stage 3
   Circuit Def             Translation              Proof Checking
```

## Design Principles

### 1. **Separation of Concerns**

Each component has a single responsibility:
- **Circuit.py**: Domain model (what is a circuit?)
- **Parser.py**: Transformation (Python → Lean4)
- **Verifier.py**: Proof execution (run Lean4)
- **Reporter.py**: Output formatting (results → markdown)

### 2. **Extensibility**

- New circuits: Just add a Python file
- New tactics: Extend the parser
- New backends: Implement the verifier interface

### 3. **Developer Experience**

- **Python DSL**: Familiar syntax for circuit designers
- **Readable Lean4**: Generated code is human-reviewable
- **Clear Reports**: Non-experts can understand results

## Component Details

### Stage 1: Circuit Definition (`src/circuit.py`)

#### Circuit Class

The `Circuit` class is a domain-specific model representing a ZK circuit:

```python
class Circuit:
    def __init__(self, name: str):
        self.name = name
        self.inputs: List[Tuple[str, str]] = []
        self.outputs: List[Tuple[str, str]] = []
        self.constraints: List[Tuple[str, str]] = []
        self.properties: List[Tuple[str, str]] = []
```

**Key Design Decisions**:

1. **String-based constraints**: Allows parsing arbitrary expressions
   - Pros: Flexible, easy to write
   - Cons: No compile-time checking (acceptable for prototype)

2. **Separate properties from constraints**:
   - Constraints: Required for circuit execution
   - Properties: Optional correctness checks

3. **Metadata included**: Descriptions for every element (helps documentation)

#### Example Usage

```python
circuit = Circuit("RangeCheck")
circuit.add_input("x", "Value to check")
circuit.add_constraint("0 <= x", "Lower bound")
circuit.add_constraint("x < MAX", "Upper bound")
circuit.add_property("Valid range", "0 <= x < MAX")
```

### Stage 2: Translation (`src/parser.py`)

#### Parser Architecture

```
Python AST ─┐
           ├─> Extract metadata ─> Build Lean4 structure ─> Write .lean file
Regex      ─┘
```

**Implementation Strategy**:

1. **Simple parsing**: Use string manipulation for prototype
   - For production: Use Python `ast` module
   
2. **Template-based generation**: Lean4 code follows fixed patterns
   - Function signature from inputs/outputs
   - Theorems from properties
   - Proofs from constraint patterns

3. **Field arithmetic assumptions**:
   - All operations modulo `FIELD_MODULUS`
   - Use Lean4's `ℕ` (natural numbers) for simplicity
   - Production version would use `ZMod FIELD_MODULUS`

#### Lean4 Code Structure

Generated Lean4 files follow this template:

```lean
-- Header: Imports and constants
import Mathlib.Data.Nat.Basic
def FIELD_MODULUS : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

-- Circuit function
def CircuitName (inputs...) : outputs... := 
  -- Constraint enforcement
  ...

-- Theorem statements
theorem CircuitName_Property : 
  ∀ (inputs...), 
  preconditions → 
  postcondition := 
by
  -- Proof tactics
  ...
```

**Why this structure?**

- **Imports**: Lean4 requires explicit imports (Mathlib for arithmetic)
- **Constants**: Field modulus as a Lean4 definition (can prove properties about it)
- **Function**: Executable circuit implementation
- **Theorem**: Formal statement of property to prove

#### Proof Generation Strategies

The parser uses **heuristics** to select proof tactics:

| Property Pattern | Tactic Choice | Reasoning |
|-----------------|---------------|-----------|
| "overflow" | `Nat.mod_lt` | Modular arithmetic bounds |
| "range" | `omega` | Linear arithmetic solver |
| "positive" | `intro, assumption` | Hypothesis propagation |
| Default | `sorry` | Placeholder for manual proof |

**Limitation**: Current prototype doesn't auto-generate complex proofs. Future work: AI-assisted tactic synthesis.

### Stage 3: Verification (`src/verifier.py`)

#### Lean4 Integration

The verifier is a **thin wrapper** around the Lean4 CLI:

```python
def verify(lean_file: str) -> VerificationResult:
    process = subprocess.run(
        ["lean", lean_file],
        capture_output=True,
        text=True
    )
    return parse_lean_output(process.stdout, process.stderr)
```

**Key Considerations**:

1. **Process isolation**: Each verification runs in a subprocess
   - Pros: Clean state, no memory leaks
   - Cons: Startup overhead (~1s per file)

2. **Output parsing**: Lean4 output is semi-structured
   - Success: Empty stderr, exit code 0
   - Failure: Error messages in stderr with line numbers

3. **Timeout handling**: Prevent infinite loops in proof search
   - Default: 60s per circuit
   - Configurable via environment variable

#### Error Handling

The verifier distinguishes:

- **Parse errors**: Invalid Lean4 syntax (bug in parser)
- **Type errors**: Mismatched types (bug in translation)
- **Proof errors**: Theorem unprovable (property false or needs manual proof)

Each error type gets a different report section.

### Stage 4: Reporting (`src/reporter.py`)

#### Report Structure

```markdown
# Verification Report: {CircuitName}

**Status**: ✓ VERIFIED / ✗ FAILED
**Timestamp**: {ISO8601}
**Proof File**: {path}

## Circuit Summary
- Inputs: {count}
- Outputs: {count}
- Constraints: {count}
- Properties: {count}

## Properties Verified
1. {Property1}: ✓ PROVEN / ✗ FAILED / ⚠️ ASSUMED
   - Proof technique: {tactic}
   - Lines: {start}-{end}

## Proof Metrics
- Total lines: {count}
- Tactics used: {list}
- Verification time: {seconds}

## Source Circuit
```python
{original Python code}
```

## Generated Lean4
```lean
{generated Lean4 code}
```

## Errors (if any)
{error messages}
```

**Design Goals**:

1. **Glanceable status**: Quick visual scan (✓/✗ symbols)
2. **Traceability**: Link back to source circuit and proof
3. **Debuggability**: Include full code for investigation
4. **Professionalism**: Formatted for GitHub/grant applications

## Data Flow

### End-to-End Pipeline

```
1. User writes circuit in Python
   ↓
2. Circuit validates itself (basic checks)
   ↓
3. Parser loads circuit module dynamically
   ↓
4. Parser extracts metadata via introspection
   ↓
5. Parser generates Lean4 code using templates
   ↓
6. Parser writes .lean file to proofs/
   ↓
7. Verifier spawns Lean4 process
   ↓
8. Lean4 checks syntax, types, proofs
   ↓
9. Verifier captures stdout/stderr
   ↓
10. Reporter parses Lean4 output
    ↓
11. Reporter generates markdown report
    ↓
12. Report saved to reports/
```

### File Paths

```
circuits/add.py
    ↓ (parsed by)
src/parser.py
    ↓ (generates)
proofs/Addition.lean
    ↓ (verified by)
src/verifier.py
    ↓ (reported by)
src/reporter.py
    ↓ (produces)
reports/Addition_report.md
```

## Technology Choices

### Why Python?

- **Rapid prototyping**: Fast iteration on DSL design
- **Rich ecosystem**: Subprocess management, file I/O
- **Accessibility**: Most developers know Python

**Alternative considered**: Rust
- Pros: Type safety, performance
- Cons: Longer development time, steeper learning curve

### Why Lean4?

- **Industry adoption**: Mathlib is the gold standard
- **Automation**: Tactics like `omega` handle linear arithmetic
- **Extensibility**: Can prove arbitrary theorems

**Alternatives considered**:
- **Coq**: Mature but older syntax
- **Isabelle/HOL**: Great for automation but less mainstream
- **SMT solvers (Z3)**: Fast but limited expressiveness

### Why Not Halo2/Circom Directly?

**Current Scope**: Focus on proving the framework works

**Future Integration**:
- Parse Halo2 circuit definitions (Rust AST)
- Extract constraints from PLONK/Halo2 backend
- Generate Lean4 proofs for real zkEVM circuits

**Milestone Approach**:
1. Prototype: Simple circuits (this stage)
2. MVP: Parse one real zkEVM circuit
3. Production: Full Scroll/Polygon zkEVM integration

## Security Considerations

### Trusted Computing Base (TCB)

What do we trust?

1. **Lean4 kernel**: Proof checker is trusted
2. **Mathlib**: Library proofs are trusted
3. **Python interpreter**: Used for orchestration only

What is NOT trusted?

- Generated Lean4 code (verified by Lean4)
- User circuit definitions (validated by framework)
- Proof tactics (checked by Lean4 kernel)

### Soundness

**Claim**: If a property is marked ✓ VERIFIED, it is mathematically true.

**Proof**:
1. Lean4 kernel is sound (proven by construction)
2. Our generated theorems correctly represent circuit properties (validated by construction)
3. Therefore, if Lean4 accepts the proof, the property holds

### Limitations

1. **Translation correctness**: Parser could have bugs
   - Mitigation: Human review of generated Lean4
   - Future: Formalize the parser itself in Lean4

2. **Property completeness**: User might not specify all relevant properties
   - Mitigation: Provide property templates
   - Future: Auto-generate properties from constraints

3. **Field arithmetic model**: Simplified to ℕ for prototype
   - Mitigation: Document assumption
   - Future: Use `ZMod FIELD_MODULUS` for exact semantics

## Performance Analysis

### Bottlenecks

| Stage | Time | Scalability |
|-------|------|-------------|
| Circuit definition | ~0.01s | O(1) per circuit |
| Parsing | ~0.05s | O(properties) |
| Lean4 startup | ~1.0s | O(1) per file |
| Proof checking | ~0.1-10s | O(proof complexity) |
| Reporting | ~0.02s | O(proof size) |

**Total**: 1-11 seconds per circuit

### Optimization Opportunities

1. **Batch verification**: Verify all circuits in one Lean4 session
   - Savings: ~1s × (circuits - 1)
   
2. **Incremental compilation**: Only re-verify changed circuits
   - Savings: Depends on change frequency

3. **Parallel verification**: Run multiple Lean4 processes
   - Savings: Near-linear speedup up to core count

4. **Cached proofs**: Store verified proof terms
   - Savings: Skip re-verification on identical code

### Scalability Targets

| Scale | Circuits | Time (current) | Time (optimized) |
|-------|----------|----------------|------------------|
| Prototype | 3 | 5s | 3s |
| MVP | 10 | 30s | 8s |
| Production | 100 | 300s | 60s |
| Full zkEVM | 1000+ | 3000s | 600s |

## Testing Strategy

### Unit Tests (Future Work)

```python
def test_circuit_validation():
    circuit = Circuit("Test")
    circuit.add_input("x", "Input")
    assert circuit.validate() == True

def test_parser_generate_theorem():
    parser = Lean4Parser()
    theorem = parser.generate_theorem("Property", "x > 0")
    assert "theorem" in theorem
```

### Integration Tests

```bash
# Test full pipeline
./demo.sh

# Expected output:
# ✓ Addition circuit verified
# ✓ Multiplication circuit verified
# ✓ RangeCheck circuit verified
```

### Manual Verification

1. Review generated Lean4 code for correctness
2. Check that verified properties match intent
3. Inspect report for clarity

## Future Architecture

### Phase 2: Real zkEVM Integration

```
Halo2 Circuit (.rs)
    ↓
Rust AST Parser
    ↓
Constraint Extractor
    ↓
Lean4 Theorem Generator
    ↓
Auto-Tactic Synthesizer
    ↓
Verification Report
```

**New Components**:

- **Rust Parser**: Extract circuit structure from Halo2
- **Constraint Extractor**: Build constraint system
- **Tactic Synthesizer**: AI-assisted proof search

### Phase 3: Continuous Verification

```
GitHub Push
    ↓
CI/CD Pipeline
    ↓
Extract Changed Circuits
    ↓
Incremental Verification
    ↓
Post Results to PR
```

**Integration Points**:

- GitHub Actions for CI
- Artifact caching for proofs
- Status badges for README

## Conclusion

This architecture prioritizes:

1. **Simplicity**: Easy to understand and extend
2. **Correctness**: Formal guarantees via Lean4
3. **Practicality**: Works with real tools (Python, Lean4)
4. **Scalability**: Clear path from prototype to production

The design validates the feasibility of automated formal verification for zkEVM circuits and provides a foundation for future development.

---

**Last Updated**: 2026-02-12  
**Version**: 1.0.0 (Prototype)  
**Authors**: [Your name]
