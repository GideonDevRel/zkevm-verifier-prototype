"""
EVM SUB Opcode Circuit (0x03)
Yellow Paper: Section 9.4.1 - Subtraction

Specification:
    Input: a, b (Word256)
    Output: (a - b) mod 2^256
    Gas: 3
    Stack: Pop 2, Push 1

Properties:
    - Underflow wraps around (no exception)
    - SUB(0, 1) = 2^256 - 1
    - Identity: SUB(a, 0) = a
    - Self-subtract: SUB(a, a) = 0
    - Inverse of ADD: SUB(ADD(a, b), b) = a
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_sub_circuit = Circuit(
    name="evm_sub",
    description="EVM SUB opcode (0x03) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # Minuend (value to subtract from)",
        "b: Word256  # Subtrahend (value to subtract)"
    ],
    outputs=[
        "result: Word256  # (a - b) mod 2^256"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ (μ_s[0] - μ_s[1]) mod 2^256",
        "",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "",
        "# Operation: Subtraction with modular wrap",
        "# If a < b, result wraps: (a - b) + WORD_MAX",
        "result = (a - b) % WORD_MAX",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "",
        "# Properties to verify:",
        "# 1. No underflow exception (wraps around)",
        "# 2. Underflow test: SUB(0, 1) = 2^256 - 1",
        "# 3. Identity: SUB(a, 0) = a",
        "# 4. Self-subtract: SUB(a, a) = 0",
        "# 5. Inverse of ADD: SUB(ADD(a, b), b) = a (mod 2^256)",
        "",
        "# Gas cost: 3",
        "# Stack effect: Pop 2, Push 1 (net: -1)",
        "",
        "# Test vectors:",
        "# SUB(10, 5) = 5",
        "# SUB(0, 1) = 2^256 - 1 (underflow wraps)",
        "# SUB(a, a) = 0",
        "# SUB(5, 10) = 2^256 - 5 (wraps around)"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_sub_circuit.name}")
    print(f"Description: {evm_sub_circuit.description}")
    print(f"Yellow Paper: Section 9.4.1")
    print(f"Opcode: 0x03 (SUB)")
    print(f"Gas cost: 3")
