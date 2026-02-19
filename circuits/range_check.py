"""Range check circuit example"""

import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.circuit import Circuit

range_check_circuit = Circuit(
    name="range_check",
    description="Verify that a value is within range [0, max]",
    inputs=["value: Field", "max: Field"],
    outputs=["valid: Bool"],
    constraints=[
        "valid = (value <= max)"
    ]
)
