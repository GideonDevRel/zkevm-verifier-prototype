"""
EVM DIV Opcode Circuit (0x04)
Yellow Paper: Section 9.4.1 - Integer Division

Specification:
    Input: a, b (Word256)
    Output: a ÷ b (floor division), or 0 if b = 0
    Gas: 5
    Stack: Pop 2, Push 1

Properties:
    - Division by zero returns 0 (not exception!)
    - Floor division (integer division)
    - DIV(10, 3) = 3 (not 3.33...)
    - Identity: DIV(a, 1) = a
    - Self-divide: DIV(a, a) = 1 (if a ≠ 0)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_div_circuit = Circuit(
    name="evm_div",
    description="EVM DIV opcode (0x04) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # Dividend (value to divide)",
        "b: Word256  # Divisor (divide by this value)"
    ],
    outputs=[
        "result: Word256  # a ÷ b (floor division) or 0 if b = 0"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ { 0 if μ_s[1] = 0, μ_s[0] ÷ μ_s[1] otherwise }",
        "",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "",
        "# Operation: Integer division (floor division)",
        "if b == 0:",
        "    # IMPORTANT: Division by zero returns 0 (no exception!)",
        "    result = 0",
        "else:",
        "    # Floor division (truncate towards zero)",
        "    result = a // b",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "if b != 0:",
        "    assert result <= a  # Quotient never exceeds dividend",
        "",
        "# Properties to verify:",
        "# 1. Division by zero returns 0 (Yellow Paper special case)",
        "# 2. Floor division: DIV(10, 3) = 3",
        "# 3. Identity: DIV(a, 1) = a",
        "# 4. Zero dividend: DIV(0, b) = 0 (for b ≠ 0)",
        "# 5. Self-divide: DIV(a, a) = 1 (for a ≠ 0)",
        "# 6. Relation: a = DIV(a, b) × b + MOD(a, b)",
        "",
        "# Gas cost: 5",
        "# Stack effect: Pop 2, Push 1 (net: -1)",
        "",
        "# Test vectors:",
        "# DIV(10, 2) = 5",
        "# DIV(10, 3) = 3 (floor division)",
        "# DIV(10, 0) = 0 (special case: division by zero)",
        "# DIV(0, 10) = 0",
        "# DIV(7, 7) = 1"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_div_circuit.name}")
    print(f"Description: {evm_div_circuit.description}")
    print(f"Yellow Paper: Section 9.4.1")
    print(f"Opcode: 0x04 (DIV)")
    print(f"Gas cost: 5")
    print(f"⚠️  IMPORTANT: Division by zero returns 0 (not exception!)")
