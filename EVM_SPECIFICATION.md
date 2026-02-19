# EVM Opcode Specifications

**Yellow Paper Conformance for zkEVM Circuit Verification**

This document defines the Ethereum Virtual Machine arithmetic opcodes that our framework will verify in zkEVM circuit implementations.

---

## 🎯 Two-Layer Verification Approach

### Layer 1: Circuit Properties (✅ Current Prototype)
- Proves circuits are internally consistent
- No overflow/underflow in field arithmetic
- Correct constraint satisfaction
- Mathematical soundness

### Layer 2: EVM Conformance (🎯 Milestone 1 Target)
- Proves circuits implement EVM opcodes correctly
- Matches Ethereum Yellow Paper specification
- Validates against Ethereum test suite
- Equivalence with reference implementations (geth, erigon)

---

## 📚 Yellow Paper Reference

**Source**: Ethereum Yellow Paper (Section 9.4 - Arithmetic Operations)  
**Document**: https://ethereum.github.io/yellowpaper/paper.pdf  
**Version**: Berlin/London/Latest

All opcodes operate on 256-bit words (Word256 = unsigned integers mod 2^256)

---

## 🔢 Arithmetic Opcodes (7 Total)

### 1. ADD (0x01) - Addition

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256)
Output: (a + b) mod 2^256
Gas:    3
Stack:  Pop 2, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ (μ_s[0] + μ_s[1]) mod 2^256
```

**Properties to Verify**:
- ✅ Result is always < 2^256 (no overflow exception)
- ✅ Commutative: ADD(a, b) = ADD(b, a)
- ✅ Associative: ADD(ADD(a, b), c) = ADD(a, ADD(b, c))
- ✅ Identity: ADD(a, 0) = a
- ✅ Overflow wraps: ADD(2^256 - 1, 1) = 0

**Test Vectors**:
- ADD(5, 10) = 15
- ADD(2^256 - 1, 1) = 0 (wrap around)
- ADD(0, 0) = 0

---

### 2. MUL (0x02) - Multiplication

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256)
Output: (a × b) mod 2^256
Gas:    5
Stack:  Pop 2, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ (μ_s[0] × μ_s[1]) mod 2^256
```

**Properties to Verify**:
- ✅ Result is always < 2^256
- ✅ Commutative: MUL(a, b) = MUL(b, a)
- ✅ Associative: MUL(MUL(a, b), c) = MUL(a, MUL(b, c))
- ✅ Identity: MUL(a, 1) = a
- ✅ Zero: MUL(a, 0) = 0
- ✅ Overflow wraps: MUL(2^128, 2^128) mod 2^256

**Test Vectors**:
- MUL(5, 10) = 50
- MUL(2^128, 2^128) = 0 (overflow wraps to 0)
- MUL(a, 0) = 0

---

### 3. SUB (0x03) - Subtraction

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256)
Output: (a - b) mod 2^256
Gas:    3
Stack:  Pop 2, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ (μ_s[0] - μ_s[1]) mod 2^256
```

**Properties to Verify**:
- ✅ Result is always < 2^256
- ✅ Underflow wraps: SUB(0, 1) = 2^256 - 1
- ✅ Identity: SUB(a, 0) = a
- ✅ Self-subtract: SUB(a, a) = 0
- ✅ Inverse of ADD: SUB(ADD(a, b), b) = a

**Test Vectors**:
- SUB(10, 5) = 5
- SUB(0, 1) = 2^256 - 1 (underflow wraps)
- SUB(a, a) = 0

---

### 4. DIV (0x04) - Integer Division

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256)
Output: a ÷ b (integer division), or 0 if b = 0
Gas:    5
Stack:  Pop 2, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ {
  0           if μ_s[1] = 0
  μ_s[0] ÷ μ_s[1]  otherwise (floor division)
}
```

**Properties to Verify**:
- ✅ Result is always < 2^256
- ✅ Division by zero returns 0 (not exception!)
- ✅ Identity: DIV(a, 1) = a
- ✅ Zero dividend: DIV(0, b) = 0 (for b ≠ 0)
- ✅ Floor division: DIV(7, 3) = 2 (not 2.33...)
- ✅ Self-divide: DIV(a, a) = 1 (for a ≠ 0)

**Test Vectors**:
- DIV(10, 2) = 5
- DIV(10, 3) = 3 (floor division)
- DIV(10, 0) = 0 (division by zero)
- DIV(0, 10) = 0

---

### 5. MOD (0x05) - Modulo

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256)
Output: a mod b, or 0 if b = 0
Gas:    5
Stack:  Pop 2, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ {
  0           if μ_s[1] = 0
  μ_s[0] mod μ_s[1]  otherwise
}
```

**Properties to Verify**:
- ✅ Result is always < b (if b ≠ 0)
- ✅ Modulo by zero returns 0
- ✅ Identity: MOD(a, b) < b (for b ≠ 0)
- ✅ Self-modulo: MOD(a, a) = 0 (for a ≠ 0)
- ✅ Relation to DIV: a = DIV(a, b) × b + MOD(a, b)

**Test Vectors**:
- MOD(10, 3) = 1
- MOD(10, 5) = 0
- MOD(10, 0) = 0 (modulo by zero)
- MOD(7, 7) = 0

---

### 6. ADDMOD (0x08) - Modular Addition

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256), N (Word256)
Output: (a + b) mod N, or 0 if N = 0
Gas:    8
Stack:  Pop 3, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ {
  0                     if μ_s[2] = 0
  (μ_s[0] + μ_s[1]) mod μ_s[2]  otherwise
}
```

**Properties to Verify**:
- ✅ Result is always < N (if N ≠ 0)
- ✅ Modulo by zero returns 0
- ✅ Commutative: ADDMOD(a, b, N) = ADDMOD(b, a, N)
- ✅ No intermediate overflow: can add numbers up to 2^256-1
- ✅ Different from ADD then MOD: ADDMOD(2^256-1, 2^256-1, 100) ≠ 0

**Key Insight**: 
ADDMOD computes (a + b) mod N **without intermediate overflow**.
This is different from MOD(ADD(a, b), N) which would overflow!

**Test Vectors**:
- ADDMOD(5, 10, 7) = 1 (15 mod 7)
- ADDMOD(2^256-1, 2^256-1, 100) = 98 (no overflow!)
- ADDMOD(10, 5, 0) = 0 (modulo by zero)

---

### 7. MULMOD (0x09) - Modular Multiplication

**Yellow Paper**: Section 9.4.1

**Specification**:
```
Input:  a (Word256), b (Word256), N (Word256)
Output: (a × b) mod N, or 0 if N = 0
Gas:    8
Stack:  Pop 3, Push 1
```

**Formal Definition**:
```
μ'_s[0] ≡ {
  0                     if μ_s[2] = 0
  (μ_s[0] × μ_s[1]) mod μ_s[2]  otherwise
}
```

**Properties to Verify**:
- ✅ Result is always < N (if N ≠ 0)
- ✅ Modulo by zero returns 0
- ✅ Commutative: MULMOD(a, b, N) = MULMOD(b, a, N)
- ✅ No intermediate overflow: can multiply numbers up to 2^256-1
- ✅ Different from MUL then MOD

**Key Insight**:
MULMOD computes (a × b) mod N **without intermediate overflow**.
The product a × b could be up to 2^512, but result is mod N.

**Test Vectors**:
- MULMOD(5, 10, 7) = 1 (50 mod 7)
- MULMOD(2^200, 2^200, 2^256-1) = (computed without overflow)
- MULMOD(10, 5, 0) = 0 (modulo by zero)

---

## 📊 Opcode Summary Table

| Opcode | Hex | Name | Gas | Stack Change | Special Case |
|--------|-----|------|-----|--------------|--------------|
| ADD | 0x01 | Addition | 3 | -2, +1 | Overflow wraps |
| MUL | 0x02 | Multiplication | 5 | -2, +1 | Overflow wraps |
| SUB | 0x03 | Subtraction | 3 | -2, +1 | Underflow wraps |
| DIV | 0x04 | Division | 5 | -2, +1 | Div by 0 → 0 |
| MOD | 0x05 | Modulo | 5 | -2, +1 | Mod by 0 → 0 |
| ADDMOD | 0x08 | Modular Add | 8 | -3, +1 | No intermediate overflow |
| MULMOD | 0x09 | Modular Mul | 8 | -3, +1 | No intermediate overflow |

---

## 🔬 Verification Methodology

### For Each Opcode, We Prove:

#### 1. Circuit Correctness (Layer 1 - Current Prototype)
```lean
theorem ADD_circuit_no_overflow :
  ∀ (a b : ℕ), a < 2^256 → b < 2^256 →
  ADD_circuit a b < 2^256
```

#### 2. EVM Specification Conformance (Layer 2 - Milestone 1)
```lean
-- Formalize Yellow Paper spec
def EVM_ADD_spec (a b : Word256) : Word256 :=
  (a.val + b.val) mod (2^256)

-- Prove circuit matches spec
theorem ADD_circuit_matches_EVM :
  ∀ (a b : Word256),
  ADD_circuit a b = EVM_ADD_spec a b
```

#### 3. Test Vector Validation (Layer 3 - Empirical)
```python
# Ethereum test suite
def validate_against_ethereum_tests():
    for test in ethereum_test_suite["ADD"]:
        expected = test["expected"]
        actual = ADD_circuit.execute(test["inputs"])
        assert actual == expected
```

---

## 🎯 Milestone 1 Deliverables

### Target: Verify 7 EVM Arithmetic Opcodes

For each opcode (ADD, MUL, SUB, DIV, MOD, ADDMOD, MULMOD):

1. ✅ **Circuit Implementation** (Python DSL)
2. ✅ **Yellow Paper Specification** (Lean4 formalization)
3. ✅ **Equivalence Proof** (Circuit = Spec)
4. ✅ **Test Vector Validation** (Ethereum test suite)
5. ✅ **Verification Report** (Markdown documentation)

**Success Criteria**:
- All 7 opcodes formally verified
- All Ethereum test vectors pass (10,000+ tests)
- Complete documentation with proofs
- < 10 minutes verification time per opcode

---

## 🚀 Integration with zkEVM Projects

### Scroll zkEVM
- Parse Halo2 circuit for ADD opcode
- Extract constraints
- Prove: Scroll's ADD circuit = EVM ADD spec
- Report: "✅ Scroll ADD opcode verified"

### Polygon zkEVM
- Parse PLONK circuit for MULMOD opcode
- Extract constraints
- Prove: Polygon's MULMOD circuit = EVM MULMOD spec
- Report: "✅ Polygon MULMOD opcode verified"

---

## 📚 References

### Official Specifications
1. **Ethereum Yellow Paper**: https://ethereum.github.io/yellowpaper/paper.pdf
2. **EVM Opcodes Reference**: https://evm.codes
3. **Ethereum Test Suite**: https://github.com/ethereum/tests

### Implementations
1. **Geth (Go)**: https://github.com/ethereum/go-ethereum
2. **Erigon (Go)**: https://github.com/ledgerwatch/erigon
3. **Reth (Rust)**: https://github.com/paradigmxyz/reth

### Related Work
1. **KEVM**: K Framework EVM semantics
2. **Verified EVM**: Coq-verified EVM
3. **soundcalc**: EF's calculator verification (similar approach)

---

## ⚠️ Important Notes

### Division by Zero
**Yellow Paper**: Division and modulo by zero return 0 (not exception!)
```
DIV(a, 0) = 0
MOD(a, 0) = 0
ADDMOD(a, b, 0) = 0
MULMOD(a, b, 0) = 0
```

This is different from most programming languages!

### Overflow Behavior
**All operations wrap around 2^256**:
```
ADD(2^256 - 1, 1) = 0
SUB(0, 1) = 2^256 - 1
MUL(2^200, 2^200) = (result mod 2^256)
```

No exceptions are thrown - results wrap silently!

### ADDMOD/MULMOD Special Cases
These compute **without intermediate overflow**:
```
ADDMOD(2^256-1, 2^256-1, N)   // Can add full 256-bit numbers
MULMOD(2^200, 2^200, N)       // Product is 2^400, still works
```

This is why they cost 8 gas instead of 3/5.

---

## 🎓 Why This Matters

### For zkEVM Security
- ✅ Proves circuits match Ethereum behavior exactly
- ✅ Catches subtle bugs (overflow, underflow, edge cases)
- ✅ Ensures zkEVM is truly "EVM-equivalent"

### For Auditing
- ✅ Replaces manual review with mathematical proof
- ✅ Reduces audit cost from $50K+ to $0 (compile-time)
- ✅ Provides continuous verification (every commit)

### For Ethereum Foundation
- ✅ Addresses top priority (zkEVM security)
- ✅ Aligns with soundcalc and verified-zkevm.org
- ✅ Provides missing piece (circuit-level verification)

---

**Status**: Specification complete, ready for implementation  
**Next**: Implement circuits and proofs (Milestone 1)  
**Timeline**: 3 months for all 7 opcodes + Halo2 integration

---

*zkEVM Circuit Formal Verification Framework*  
*Version 1.0.0 | February 2026*
