"""
EVM ADDMOD Opcode Circuit (0x08)
Yellow Paper: Section 9.4.1 - Modular Addition

Specification:
    Input: a, b, N (Word256)
    Output: (a + b) mod N, or 0 if N = 0
    Gas: 8
    Stack: Pop 3, Push 1

Key Feature:
    Computes (a + b) mod N WITHOUT intermediate overflow!
    This is different from MOD(ADD(a, b), N) which would overflow.

Properties:
    - No intermediate overflow (can add 2^256-1 + 2^256-1)
    - Modulo by zero returns 0
    - Commutative: ADDMOD(a, b, N) = ADDMOD(b, a, N)
    - Result always < N (if N ≠ 0)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_addmod_circuit = Circuit(
    name="evm_addmod",
    description="EVM ADDMOD opcode (0x08) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # First operand",
        "b: Word256  # Second operand",
        "N: Word256  # Modulus"
    ],
    outputs=[
        "result: Word256  # (a + b) mod N, or 0 if N = 0"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ { 0 if μ_s[2] = 0, (μ_s[0] + μ_s[1]) mod μ_s[2] otherwise }",
        "",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "assert 0 <= N < WORD_MAX",
        "",
        "# Operation: Modular addition WITHOUT intermediate overflow",
        "if N == 0:",
        "    # IMPORTANT: Modulo by zero returns 0",
        "    result = 0",
        "else:",
        "    # KEY INSIGHT: Compute (a + b) mod N without overflow",
        "    # The sum a + b could be up to 2^257 - 2",
        "    # But we compute directly: (a + b) mod N",
        "    # WITHOUT first computing (a + b) mod 2^256",
        "    result = (a + b) % N",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "if N != 0:",
        "    assert result < N",
        "",
        "# WHY ADDMOD ≠ MOD(ADD(a, b), N):",
        "# Example: a = 2^256 - 1, b = 2^256 - 1, N = 100",
        "# ADD(a, b) = (2^256-1 + 2^256-1) mod 2^256 = 2^256 - 2 (overflow!)",
        "# MOD(ADD(a, b), N) = MOD(2^256 - 2, 100) = 98",
        "# But actual a + b = 2^257 - 2",
        "# ADDMOD(a, b, N) = (2^257 - 2) mod 100 = 98",
        "# In this case they match, but the computation is different!",
        "",
        "# Better example: a = 2^256 - 1, b = 1, N = 2^256",
        "# ADD would wrap: (2^256-1 + 1) mod 2^256 = 0",
        "# ADDMOD computes: (2^256) mod 2^256 = 0",
        "# They match here too, but conceptually different!",
        "",
        "# The key is ADDMOD allows arbitrary modulus N,",
        "# not just 2^256, so it's more general.",
        "",
        "# Properties to verify:",
        "# 1. No intermediate overflow (works for any a, b < 2^256)",
        "# 2. Modulo by zero returns 0",
        "# 3. Commutative: ADDMOD(a, b, N) = ADDMOD(b, a, N)",
        "# 4. Result bound: result < N (for N ≠ 0)",
        "# 5. Associative (under fixed N)",
        "",
        "# Gas cost: 8 (more expensive due to arbitrary modulus)",
        "# Stack effect: Pop 3, Push 1 (net: -2)",
        "",
        "# Test vectors:",
        "# ADDMOD(5, 10, 7) = 1 (15 mod 7)",
        "# ADDMOD(2^256-1, 2^256-1, 100) = 98 (no overflow!)",
        "# ADDMOD(10, 5, 0) = 0 (modulo by zero)",
        "# ADDMOD(3, 4, 5) = 2 (7 mod 5)"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_addmod_circuit.name}")
    print(f"Description: {evm_addmod_circuit.description}")
    print(f"Yellow Paper: Section 9.4.1")
    print(f"Opcode: 0x08 (ADDMOD)")
    print(f"Gas cost: 8")
    print(f"🔑 KEY: Computes WITHOUT intermediate overflow!")
    print(f"   ADDMOD(2^256-1, 2^256-1, N) works correctly")
