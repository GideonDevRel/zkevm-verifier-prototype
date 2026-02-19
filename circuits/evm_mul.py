"""
EVM MUL Opcode Circuit (0x02)
Yellow Paper: Section 9.4.1 - Multiplication

Specification:
    Input: a, b (Word256)
    Output: (a × b) mod 2^256
    Gas: 5
    Stack: Pop 2, Push 1

Properties:
    - Overflow wraps around (no exception)
    - Commutative: MUL(a, b) = MUL(b, a)
    - Associative: (a × b) × c = a × (b × c)
    - Identity: MUL(a, 1) = a
    - Zero: MUL(a, 0) = 0
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_mul_circuit = Circuit(
    name="evm_mul",
    description="EVM MUL opcode (0x02) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # First operand from stack",
        "b: Word256  # Second operand from stack"
    ],
    outputs=[
        "result: Word256  # (a × b) mod 2^256"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ (μ_s[0] × μ_s[1]) mod 2^256",
        "",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "",
        "# Operation: Multiplication with modular wrap",
        "result = (a * b) % WORD_MAX",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "",
        "# Properties to verify:",
        "# 1. No overflow exception (wraps around)",
        "# 2. Commutative: MUL(a,b) = MUL(b,a)",
        "# 3. Associative: MUL(MUL(a,b),c) = MUL(a,MUL(b,c))",
        "# 4. Identity: MUL(a, 1) = a",
        "# 5. Zero: MUL(a, 0) = 0",
        "# 6. Overflow: MUL(2^128, 2^128) wraps to 0",
        "",
        "# Gas cost: 5",
        "# Stack effect: Pop 2, Push 1 (net: -1)",
        "",
        "# Test vectors:",
        "# MUL(5, 10) = 50",
        "# MUL(2^128, 2^128) = 0 (overflow wraps)",
        "# MUL(a, 0) = 0",
        "# MUL(a, 1) = a"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_mul_circuit.name}")
    print(f"Description: {evm_mul_circuit.description}")
    print(f"Yellow Paper: Section 9.4.1")
    print(f"Opcode: 0x02 (MUL)")
    print(f"Gas cost: 5")
