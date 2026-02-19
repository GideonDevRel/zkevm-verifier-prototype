# Architecture Documentation

## System Overview

The zkEVM Circuit Verifier uses a pipeline architecture to convert high-level circuit definitions into formally verified Lean4 proofs.

```
┌─────────────────────────────────────────────────────────────┐
│                    zkEVM Circuit Verifier                    │
│                                                              │
│  ┌────────────┐      ┌────────────┐      ┌──────────────┐  │
│  │  Circuit   │────▶ │   Parser   │────▶ │  Lean4 Code  │  │
│  │ Definition │      │            │      │  Generator   │  │
│  │  (Python)  │      │            │      │              │  │
│  └────────────┘      └────────────┘      └──────┬───────┘  │
│                                                  │          │
│                                                  ▼          │
│  ┌────────────┐      ┌────────────┐      ┌──────────────┐  │
│  │ Verification│◀────│  Verifier  │◀────│  Lean4 Proof │  │
│  │   Report   │      │            │      │    (.lean)   │  │
│  │ (.md)      │      │            │      │              │  │
│  └────────────┘      └────────────┘      └──────────────┘  │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

## Components

### 1. Circuit Definition (`src/circuit.py`)

**Purpose:** Represents a zkEVM circuit with inputs, outputs, and constraints.

**Key Class:**
```python
class Circuit:
    def __init__(self, name, description, inputs, outputs, constraints):
        ...
```

**Responsibilities:**
- Store circuit metadata
- Provide variable extraction methods
- Serialize to dictionary format

### 2. Parser (`src/parser.py`)

**Purpose:** Convert Python circuit definitions to Lean4 theorems.

**Key Functions:**
- `parse_circuit_file(filepath)` - Load Circuit from Python file
- `circuit_to_lean(circuit)` - Generate Lean4 code

**Process:**
1. Load Python file dynamically
2. Extract Circuit object
3. Generate Lean4 function definition
4. Generate correctness theorem
5. Generate soundness theorem
6. Write to `proofs/` directory

**Output Example:**
```lean
def add_circuit (a b : Nat) : Nat := a + b

theorem add_correct (a b : Nat) :
  add_circuit a b = a + b := by rfl
```

### 3. Verifier (`src/verifier.py`)

**Purpose:** Run Lean4 compiler to verify proofs.

**Key Functions:**
- `verify_proof(lean_file)` - Verify single proof
- `verify_all_proofs(proofs_dir)` - Verify all proofs in directory

**Process:**
1. Find all `.lean` files in `proofs/`
2. Run `lean <file>` for each
3. Check return code (0 = success)
4. Collect results

**Dependencies:**
- Lean4 must be installed
- Proof files must exist

### 4. Reporter (`src/reporter.py`)

**Purpose:** Generate human-readable verification reports.

**Key Functions:**
- `generate_report(circuit, ...)` - Single circuit report
- `generate_summary_report(...)` - Overall summary
- `generate_all_reports()` - Process all circuits

**Output Format:** Markdown (`.md`) files

**Report Sections:**
- Circuit specification
- Verification method
- Formal statement
- Verification result
- Security guarantees

## Data Flow

### Step-by-Step Execution

**1. User runs `./demo.sh`**

**2. Parser Phase:**
```bash
python -m src.parser circuits/add.py
```
- Loads `add.py`
- Extracts `add_circuit` object
- Generates `proofs/add_proof.lean`

**3. Verification Phase:**
```bash
python -m src.verifier
```
- Finds `proofs/add_proof.lean`
- Runs `lean proofs/add_proof.lean`
- Collects result: ✅ PASS or ❌ FAIL

**4. Reporting Phase:**
```bash
python -m src.reporter
```
- Reads verification results
- Loads original circuit definitions
- Generates `reports/add_report.md`
- Generates `reports/summary.md`

## Technology Stack

### Core Technologies

**Python 3.7+**
- Circuit DSL
- Orchestration logic
- Report generation

**Lean4 Theorem Prover**
- Formal verification
- Proof checking
- Mathematical guarantees

**Bash Scripts**
- Installation automation
- Demo orchestration

### Why These Choices?

**Python:**
- ✅ Easy to write and understand
- ✅ Fast prototyping
- ✅ Good for DSL design
- ❌ Not production-grade (would use Rust for production)

**Lean4:**
- ✅ Industry standard for formal verification
- ✅ Strong type system
- ✅ Active community
- ✅ Good documentation
- ✅ Used in serious projects (CompCert, seL4)

## Extension Points

### Adding New Circuit Types

**1. Create circuit file:**
```python
# circuits/my_circuit.py
from src.circuit import Circuit

my_circuit = Circuit(...)
```

**2. Parser handles automatically**
- No code changes needed
- Just run `./demo.sh`

### Improving Proof Generation

**Location:** `src/parser.py` → `circuit_to_lean()`

**Current:** Simple template-based generation

**Future:**
- Parse constraint syntax properly
- Support complex operations
- Handle multiple constraints
- Generate sophisticated proofs

### Adding soundcalc Integration

**Plan:**
1. Add `soundcalc_config` to Circuit class
2. Parse soundcalc parameters
3. Call soundcalc API in `reporter.py`
4. Include security estimate in reports

**Implementation:**
```python
# In circuit.py
class Circuit:
    def __init__(self, ..., soundcalc_config=None):
        self.soundcalc_config = soundcalc_config

# In reporter.py
def generate_report(...):
    if circuit.soundcalc_config:
        security_bits = call_soundcalc(circuit)
        report += f"Security: {security_bits} bits"
```

## Performance Considerations

**Current (Prototype):**
- Verification time: <1 second per circuit
- Memory usage: Minimal
- Disk space: ~100KB per circuit

**Production Targets:**
- Verification time: <10 seconds for complex circuits
- Memory usage: <1GB
- Disk space: ~10MB per circuit (with all artifacts)

## Security Model

**Threat Model:**
- Buggy circuits could allow proof forgery
- Attackers could steal funds from zkRollups
- Mathematical proofs prevent this

**Trust Assumptions:**
- Lean4 compiler is correct (proven track record)
- Circuit → Lean translation is correct (auditable)
- No bugs in theorem prover itself

**Verification Level:**
- **Functional correctness:** Guaranteed by proofs
- **Soundness:** Proven mathematically
- **Completeness:** Circuits compute as specified

## Limitations (Prototype)

**1. Simple Circuits Only**
- Currently: Addition, multiplication, range checks
- Needed: Memory, crypto, state transitions

**2. Manual Proof Structure**
- Generated proofs follow templates
- Complex proofs need more sophistication

**3. No Multi-zkVM Support**
- Currently: Generic circuit format
- Needed: OpenVM, SP1, RISC Zero, etc.

**4. No CI/CD Integration**
- Currently: Manual execution
- Needed: GitHub Actions, automatic verification

**5. Python Performance**
- Currently: Acceptable for prototype
- Needed: Rust implementation for production

## Future Architecture

**Production System:**

```
┌──────────────────────────────────────────────────┐
│          zkEVM Verification Framework            │
│                                                  │
│  ┌────────────────┐         ┌────────────────┐  │
│  │  zkVM Imports  │         │  Lean4 Engine  │  │
│  │  - OpenVM      │────────▶│  - Verification│  │
│  │  - SP1         │         │  - Proof Gen   │  │
│  │  - RISC Zero   │         │  - Library     │  │
│  └────────────────┘         └────────┬───────┘  │
│          │                           │          │
│          ▼                           ▼          │
│  ┌────────────────┐         ┌────────────────┐  │
│  │   soundcalc    │         │  CI/CD Hooks   │  │
│  │   Integration  │         │  - GitHub      │  │
│  └────────────────┘         └────────────────┘  │
│                                                  │
└──────────────────────────────────────────────────┘
```

**Key Improvements:**
1. Rust core (performance)
2. LLZK IR support (zkVM interop)
3. soundcalc tight integration
4. Verified component library
5. Automated CI/CD
6. Multi-architecture support

---

**Document Version:** 1.0  
**Last Updated:** February 2026  
**Status:** Prototype Architecture
