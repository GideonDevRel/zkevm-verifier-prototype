"""
Circuit definition and manipulation.
Represents a zero-knowledge circuit with inputs, outputs, and constraints.
"""

class Circuit:
    """Represents a circuit to be verified"""
    
    def __init__(self, name, description, inputs, outputs, constraints):
        """
        Initialize a circuit.
        
        Args:
            name: Circuit name (e.g., "add")
            description: Human-readable description
            inputs: List of input specifications (e.g., ["a: Field", "b: Field"])
            outputs: List of output specifications (e.g., ["c: Field"])
            constraints: List of constraint equations (e.g., ["c = a + b"])
        """
        self.name = name
        self.description = description
        self.inputs = inputs
        self.outputs = outputs
        self.constraints = constraints
    
    def to_dict(self):
        """Convert to dictionary for serialization"""
        return {
            'name': self.name,
            'description': self.description,
            'inputs': self.inputs,
            'outputs': self.outputs,
            'constraints': self.constraints
        }
    
    def get_input_vars(self):
        """Extract input variable names"""
        return [inp.split(':')[0].strip() for inp in self.inputs]
    
    def get_output_vars(self):
        """Extract output variable names"""
        return [out.split(':')[0].strip() for out in self.outputs]
    
    def __str__(self):
        return f"Circuit({self.name}): {len(self.inputs)} inputs, {len(self.outputs)} outputs, {len(self.constraints)} constraints"
    
    def __repr__(self):
        return self.__str__()
