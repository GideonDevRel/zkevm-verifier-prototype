"""
EVM ADD Opcode Circuit (0x01)
Yellow Paper: Section 9.4.1 - Addition

Specification:
    Input: a, b (Word256)
    Output: (a + b) mod 2^256
    Gas: 3
    Stack: Pop 2, Push 1

Properties:
    - Overflow wraps around (no exception)
    - Commutative: ADD(a, b) = ADD(b, a)
    - Associative: (a + b) + c = a + (b + c)
    - Identity: ADD(a, 0) = a
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_add_circuit = Circuit(
    name="evm_add",
    description="EVM ADD opcode (0x01) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # First operand from stack",
        "b: Word256  # Second operand from stack"
    ],
    outputs=[
        "result: Word256  # (a + b) mod 2^256"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ (μ_s[0] + μ_s[1]) mod 2^256",
        "",
        "# Word256 = unsigned integer in range [0, 2^256)",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions (from stack)",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "",
        "# Operation: Addition with modular wrap",
        "result = (a + b) % WORD_MAX",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "",
        "# Properties to verify:",
        "# 1. No overflow exception (wraps around)",
        "# 2. Commutative: ADD(a,b) = ADD(b,a)",
        "# 3. Associative: ADD(ADD(a,b),c) = ADD(a,ADD(b,c))",
        "# 4. Identity: ADD(a, 0) = a",
        "# 5. Wrap test: ADD(WORD_MAX-1, 1) = 0",
        "",
        "# Gas cost: 3 (constant)",
        "# Stack effect: Pop 2, Push 1 (net: -1)",
        "",
        "# Test vectors (from Ethereum test suite):",
        "# ADD(5, 10) = 15",
        "# ADD(2^256 - 1, 1) = 0 (overflow wraps)",
        "# ADD(0, 0) = 0"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_add_circuit.name}")
    print(f"Description: {evm_add_circuit.description}")
    print(f"Inputs: {len(evm_add_circuit.inputs)}")
    print(f"Outputs: {len(evm_add_circuit.outputs)}")
    print(f"Constraints: {len(evm_add_circuit.constraints)}")
    print(f"\nYellow Paper: Section 9.4.1")
    print(f"Opcode: 0x01 (ADD)")
    print(f"Gas cost: 3")
    print(f"EVM equivalence: μ'_s[0] ≡ (μ_s[0] + μ_s[1]) mod 2^256")
