"""
EVM MOD Opcode Circuit (0x05)
Yellow Paper: Section 9.4.1 - Modulo Operation

Specification:
    Input: a, b (Word256)
    Output: a mod b, or 0 if b = 0
    Gas: 5
    Stack: Pop 2, Push 1

Properties:
    - Modulo by zero returns 0 (not exception!)
    - Result is always < b (if b ≠ 0)
    - Self-modulo: MOD(a, a) = 0 (for a ≠ 0)
    - Relation to DIV: a = DIV(a, b) × b + MOD(a, b)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_mod_circuit = Circuit(
    name="evm_mod",
    description="EVM MOD opcode (0x05) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # Dividend (value to take modulo of)",
        "b: Word256  # Modulus"
    ],
    outputs=[
        "result: Word256  # a mod b, or 0 if b = 0"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ { 0 if μ_s[1] = 0, μ_s[0] mod μ_s[1] otherwise }",
        "",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "",
        "# Operation: Modulo operation",
        "if b == 0:",
        "    # IMPORTANT: Modulo by zero returns 0 (no exception!)",
        "    result = 0",
        "else:",
        "    result = a % b",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "if b != 0:",
        "    assert result < b  # Remainder is always less than modulus",
        "",
        "# Properties to verify:",
        "# 1. Modulo by zero returns 0 (Yellow Paper special case)",
        "# 2. Result bound: MOD(a, b) < b (for b ≠ 0)",
        "# 3. Self-modulo: MOD(a, a) = 0 (for a ≠ 0)",
        "# 4. Zero: MOD(0, b) = 0 (for b ≠ 0)",
        "# 5. Identity: MOD(a, WORD_MAX) = a",
        "# 6. Relation to DIV: a = DIV(a, b) × b + MOD(a, b)",
        "",
        "# Gas cost: 5",
        "# Stack effect: Pop 2, Push 1 (net: -1)",
        "",
        "# Test vectors:",
        "# MOD(10, 3) = 1",
        "# MOD(10, 5) = 0",
        "# MOD(10, 0) = 0 (special case: modulo by zero)",
        "# MOD(7, 7) = 0",
        "# MOD(5, 10) = 5"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_mod_circuit.name}")
    print(f"Description: {evm_mod_circuit.description}")
    print(f"Yellow Paper: Section 9.4.1")
    print(f"Opcode: 0x05 (MOD)")
    print(f"Gas cost: 5")
    print(f"⚠️  IMPORTANT: Modulo by zero returns 0 (not exception!)")
