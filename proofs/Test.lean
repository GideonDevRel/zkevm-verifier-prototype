/-
  Simple test to verify Mathlib integration
-/

import Mathlib.Data.Nat.Basic

def Word256 : Type := Fin (2^256)

@[ext]
theorem Word256.ext {a b : Word256} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

def evm_add (a b : Word256) : Word256 := 
  ⟨(a.val + b.val) % (2^256), Nat.mod_lt _ (Nat.two_pow_pos 256)⟩

theorem evm_add_soundness (a b : Word256) :
  ∃ result : Word256, result = evm_add a b := by
  exists evm_add a b

#check evm_add_soundness

-- Test that it compiles
#eval (1 : Nat) + 1
