"""Addition circuit example"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

add_circuit = Circuit(
    name="add",
    description="Addition of two field elements",
    inputs=["a: Field", "b: Field"],
    outputs=["c: Field"],
    constraints=[
        "c = a + b"
    ]
)
