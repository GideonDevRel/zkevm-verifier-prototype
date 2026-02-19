"""
EVM MULMOD Opcode Circuit (0x09)
Yellow Paper: Section 9.4.1 - Modular Multiplication

Specification:
    Input: a, b, N (Word256)
    Output: (a × b) mod N, or 0 if N = 0
    Gas: 8
    Stack: Pop 3, Push 1

Key Feature:
    Computes (a × b) mod N WITHOUT intermediate overflow!
    This is different from MOD(MUL(a, b), N) which would overflow.
    
    The product a × b can be up to 2^512, but MULMOD handles it!

Properties:
    - No intermediate overflow (can multiply 2^256-1 × 2^256-1)
    - Modulo by zero returns 0
    - Commutative: MULMOD(a, b, N) = MULMOD(b, a, N)
    - Result always < N (if N ≠ 0)
"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

evm_mulmod_circuit = Circuit(
    name="evm_mulmod",
    description="EVM MULMOD opcode (0x09) - Yellow Paper Section 9.4.1",
    inputs=[
        "a: Word256  # First operand",
        "b: Word256  # Second operand",
        "N: Word256  # Modulus"
    ],
    outputs=[
        "result: Word256  # (a × b) mod N, or 0 if N = 0"
    ],
    constraints=[
        "# Yellow Paper Specification",
        "# μ'_s[0] ≡ { 0 if μ_s[2] = 0, (μ_s[0] × μ_s[1]) mod μ_s[2] otherwise }",
        "",
        "WORD_MAX = 2^256",
        "",
        "# Preconditions",
        "assert 0 <= a < WORD_MAX",
        "assert 0 <= b < WORD_MAX",
        "assert 0 <= N < WORD_MAX",
        "",
        "# Operation: Modular multiplication WITHOUT intermediate overflow",
        "if N == 0:",
        "    # IMPORTANT: Modulo by zero returns 0",
        "    result = 0",
        "else:",
        "    # KEY INSIGHT: Compute (a × b) mod N without overflow",
        "    # The product a × b could be up to 2^512 - 2*2^256 + 1",
        "    # Example: (2^256 - 1) × (2^256 - 1) = 2^512 - 2^257 + 1",
        "    # But we compute directly: (a × b) mod N",
        "    # WITHOUT first computing (a × b) mod 2^256",
        "    result = (a * b) % N",
        "",
        "# Postcondition",
        "assert 0 <= result < WORD_MAX",
        "if N != 0:",
        "    assert result < N",
        "",
        "# WHY MULMOD ≠ MOD(MUL(a, b), N):",
        "# Example: a = 2^200, b = 2^200, N = 2^256 - 1",
        "# a × b = 2^400 (way bigger than 2^256!)",
        "# MUL(a, b) = (2^400) mod 2^256 (wraps multiple times)",
        "# MOD(MUL(a, b), N) would use the wrapped value",
        "# But MULMOD(a, b, N) = (2^400) mod (2^256 - 1) (correct full product)",
        "",
        "# This is critical for cryptographic operations:",
        "# - Modular exponentiation",
        "# - Elliptic curve operations",
        "# - RSA-like calculations",
        "",
        "# Properties to verify:",
        "# 1. No intermediate overflow (product can be 2^512)",
        "# 2. Modulo by zero returns 0",
        "# 3. Commutative: MULMOD(a, b, N) = MULMOD(b, a, N)",
        "# 4. Result bound: result < N (for N ≠ 0)",
        "# 5. Associative (under fixed N)",
        "# 6. Distributive: MULMOD(a, ADDMOD(b,c,N), N) = ADDMOD(MULMOD(a,b,N), MULMOD(a,c,N), N)",
        "",
        "# Gas cost: 8 (expensive due to 512-bit arithmetic)",
        "# Stack effect: Pop 3, Push 1 (net: -2)",
        "",
        "# Test vectors:",
        "# MULMOD(5, 10, 7) = 1 (50 mod 7)",
        "# MULMOD(2^200, 2^200, 2^256-1) = (computed without overflow)",
        "# MULMOD(10, 5, 0) = 0 (modulo by zero)",
        "# MULMOD(3, 4, 5) = 2 (12 mod 5)",
        "",
        "# Implementation note:",
        "# In zkSNARKs, this requires 512-bit arithmetic or",
        "# clever tricks to avoid intermediate overflow.",
        "# This is one of the more complex opcodes to verify!"
    ]
)

if __name__ == "__main__":
    print(f"Circuit: {evm_mulmod_circuit.name}")
    print(f"Description: {evm_mulmod_circuit.description}")
    print(f"Yellow Paper: Section 9.4.1")
    print(f"Opcode: 0x09 (MULMOD)")
    print(f"Gas cost: 8")
    print(f"🔑 KEY: Handles 512-bit products WITHOUT overflow!")
    print(f"   MULMOD(2^200, 2^200, N) works correctly")
    print(f"   This is critical for cryptographic operations")
