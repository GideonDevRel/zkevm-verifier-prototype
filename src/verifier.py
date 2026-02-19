"""
Run Lean4 verification on generated proofs.
Executes the Lean4 compiler and checks for successful verification.
"""

import subprocess
import os
import sys

def verify_proof(lean_file):
    """
    Verify a Lean4 proof file.
    
    Args:
        lean_file: Path to .lean file
    
    Returns:
        tuple: (success: bool, output: str)
    """
    
    if not os.path.exists(lean_file):
        return False, f"File not found: {lean_file}"
    
    try:
        result = subprocess.run(
            ['lean', lean_file],
            capture_output=True,
            text=True,
            timeout=30
        )
        
        success = result.returncode == 0
        output = result.stdout + result.stderr
        
        return success, output
    
    except subprocess.TimeoutExpired:
        return False, "Verification timeout (>30s)"
    except FileNotFoundError:
        return False, "Lean4 not installed. Run: ./install.sh"
    except Exception as e:
        return False, f"Error: {str(e)}"

def verify_all_proofs(proofs_dir="proofs"):
    """
    Verify all .lean files in directory.
    
    Args:
        proofs_dir: Directory containing .lean files
    
    Returns:
        dict: filename -> (success, output)
    """
    
    if not os.path.exists(proofs_dir):
        print(f"Warning: Directory not found: {proofs_dir}")
        return {}
    
    results = {}
    
    lean_files = [f for f in os.listdir(proofs_dir) if f.endswith('.lean')]
    
    if not lean_files:
        print(f"Warning: No .lean files found in {proofs_dir}")
        return {}
    
    for filename in lean_files:
        filepath = os.path.join(proofs_dir, filename)
        success, output = verify_proof(filepath)
        results[filename] = (success, output)
    
    return results

def main():
    """Main entry point for verifier"""
    
    print("Running Lean4 verification...")
    print()
    
    results = verify_all_proofs()
    
    if not results:
        print("No proofs to verify. Run: python -m src.parser circuits/*.py")
        sys.exit(1)
    
    total = len(results)
    passed = sum(1 for success, _ in results.values() if success)
    
    for filename, (success, output) in results.items():
        status = "✅ PASS" if success else "❌ FAIL"
        print(f"{status} - {filename}")
        if not success:
            print(f"  Error: {output[:200]}")
            print()
    
    print()
    print(f"Results: {passed}/{total} proofs verified")
    
    if passed == total:
        print("✓ All verifications passed!")
        sys.exit(0)
    else:
        print("✗ Some verifications failed")
        sys.exit(1)

if __name__ == "__main__":
    main()
