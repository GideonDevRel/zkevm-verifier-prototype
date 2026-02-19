import Lake
open Lake DSL

package «zkevm-verifier» where
  -- zkEVM Circuit Formal Verification Framework
  -- Version: 2.0.0 (Lean stdlib only)

@[default_target]
lean_lib zkEVM where
  globs := #[.submodules `zkEVM]
  -- EVM opcode formal proofs
