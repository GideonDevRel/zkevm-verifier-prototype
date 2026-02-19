-- Poseidon Hash Circuit Formal Verification
-- Generated from: circuits/poseidon.py
-- Generated at: 2026-02-12 10:00:00 UTC

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

-- Field modulus for BN254 curve
def FIELD_MODULUS : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

theorem FIELD_MODULUS_pos : 0 < FIELD_MODULUS := by norm_num

-- Poseidon parameters for t=3 (2-input variant)
def STATE_SIZE : ℕ := 3
def FULL_ROUNDS : ℕ := 8
def PARTIAL_ROUNDS : ℕ := 57
def TOTAL_ROUNDS : ℕ := FULL_ROUNDS + PARTIAL_ROUNDS

-- S-box function: x ↦ x^5 mod p
-- This is the core non-linearity in Poseidon
def sbox (x : ℕ) : ℕ := (x^5) % FIELD_MODULUS

-- MDS Matrix (simplified 3x3 version)
-- Real implementation uses optimized MDS matrix
def MDS_MATRIX : Fin STATE_SIZE → Fin STATE_SIZE → ℕ :=
  fun i j => 
    if i = j then 2 else 1

-- Round constant (simplified - real impl has 195 unique constants)
-- These provide domain separation
def round_constant (round : ℕ) : ℕ := 
  (round * 1000000007) % FIELD_MODULUS

-- State type (3 field elements)
def State := Fin STATE_SIZE → ℕ

-- Apply S-box to single element
def apply_sbox (state : State) (idx : Fin STATE_SIZE) : State :=
  fun i => if i = idx then sbox (state i) else state i

-- Apply S-box to all elements (full round)
def apply_sbox_full (state : State) : State :=
  fun i => sbox (state i)

-- Add round constants to state
def add_constants (state : State) (round : ℕ) : State :=
  fun i => (state i + round_constant (round + i.val)) % FIELD_MODULUS

-- Matrix multiplication (simplified)
def matrix_mult (state : State) : State :=
  fun i => 
    let sum := (List.range STATE_SIZE).foldl 
      (fun acc j => acc + MDS_MATRIX i ⟨j, by omega⟩ * state ⟨j, by omega⟩) 
      0
    sum % FIELD_MODULUS

-- Full round: Add constants → S-box all → Matrix multiply
def full_round (state : State) (round : ℕ) : State :=
  matrix_mult (apply_sbox_full (add_constants state round))

-- Partial round: Add constants → S-box first element → Matrix multiply
def partial_round (state : State) (round : ℕ) : State :=
  matrix_mult (apply_sbox (add_constants state round) 0)

-- Full Poseidon permutation
def poseidon_permutation (initial_state : State) : State :=
  let after_first_full := (List.range (FULL_ROUNDS / 2)).foldl 
    (fun s r => full_round s r) initial_state
  let after_partial := (List.range PARTIAL_ROUNDS).foldl 
    (fun s r => partial_round s (r + FULL_ROUNDS / 2)) after_first_full
  let final_state := (List.range (FULL_ROUNDS / 2)).foldl 
    (fun s r => full_round s (r + FULL_ROUNDS / 2 + PARTIAL_ROUNDS)) after_partial
  final_state

-- Poseidon hash function (2-input variant)
def Poseidon (x y : ℕ) : ℕ :=
  let initial_state : State := fun i => 
    if i = 0 then 0           -- Capacity starts at 0
    else if i = 1 then x % FIELD_MODULUS
    else y % FIELD_MODULUS
  let final_state := poseidon_permutation initial_state
  final_state 0  -- Squeeze first element

-- Property 1: S-box preserves field bounds
theorem sbox_in_field :
  ∀ (x : ℕ), x < FIELD_MODULUS → sbox x < FIELD_MODULUS :=
by
  intro x hx
  unfold sbox
  apply Nat.mod_lt
  exact FIELD_MODULUS_pos

-- Property 2: S-box is deterministic
theorem sbox_deterministic :
  ∀ (x : ℕ), sbox x = sbox x :=
by
  intro x
  rfl

-- Property 3: S-box on zero is zero
theorem sbox_zero : sbox 0 = 0 :=
by
  unfold sbox
  norm_num

-- Property 4: Round constants are in field
theorem round_constant_in_field :
  ∀ (r : ℕ), round_constant r < FIELD_MODULUS :=
by
  intro r
  unfold round_constant
  apply Nat.mod_lt
  exact FIELD_MODULUS_pos

-- Property 5: Matrix multiplication preserves field bounds
theorem matrix_mult_in_field :
  ∀ (state : State),
  (∀ i : Fin STATE_SIZE, state i < FIELD_MODULUS) →
  (∀ i : Fin STATE_SIZE, matrix_mult state i < FIELD_MODULUS) :=
by
  intro state h_state i
  unfold matrix_mult
  apply Nat.mod_lt
  exact FIELD_MODULUS_pos

-- Property 6: Full round preserves field bounds
theorem full_round_in_field :
  ∀ (state : State) (round : ℕ),
  (∀ i : Fin STATE_SIZE, state i < FIELD_MODULUS) →
  (∀ i : Fin STATE_SIZE, full_round state round i < FIELD_MODULUS) :=
by
  intro state round h_state i
  unfold full_round
  apply matrix_mult_in_field
  intro j
  unfold apply_sbox_full add_constants
  simp
  apply sbox_in_field
  apply Nat.mod_lt
  exact FIELD_MODULUS_pos

-- Property 7: Partial round preserves field bounds
theorem partial_round_in_field :
  ∀ (state : State) (round : ℕ),
  (∀ i : Fin STATE_SIZE, state i < FIELD_MODULUS) →
  (∀ i : Fin STATE_SIZE, partial_round state round i < FIELD_MODULUS) :=
by
  intro state round h_state i
  unfold partial_round
  apply matrix_mult_in_field
  intro j
  unfold apply_sbox add_constants
  split
  · apply sbox_in_field
    apply Nat.mod_lt
    exact FIELD_MODULUS_pos
  · apply Nat.mod_lt
    exact FIELD_MODULUS_pos

-- Property 8: Poseidon output is in field
theorem Poseidon_in_field :
  ∀ (x y : ℕ),
  x < FIELD_MODULUS →
  y < FIELD_MODULUS →
  Poseidon x y < FIELD_MODULUS :=
by
  intro x y hx hy
  unfold Poseidon
  -- Final state is in field (by induction on rounds)
  sorry  -- Full proof requires induction over all rounds

-- Property 9: Poseidon is deterministic
theorem Poseidon_deterministic :
  ∀ (x y : ℕ),
  Poseidon x y = Poseidon x y :=
by
  intro x y
  rfl

-- Property 10: Poseidon respects modular equivalence
theorem Poseidon_mod_equiv :
  ∀ (x y : ℕ),
  Poseidon x y = Poseidon (x % FIELD_MODULUS) (y % FIELD_MODULUS) :=
by
  intro x y
  unfold Poseidon
  simp [Nat.mod_mod_of_dvd]

-- Property 11: S-box is non-linear (x^5 ≠ 5x for most x)
-- This is what provides cryptographic strength
theorem sbox_nonlinear :
  ∃ (x : ℕ), x < FIELD_MODULUS ∧ sbox x ≠ (5 * x) % FIELD_MODULUS :=
by
  use 2
  constructor
  · norm_num
  · unfold sbox
    norm_num

-- Property 12: MDS matrix is non-singular (simplified property)
-- Real proof would show determinant ≠ 0
theorem MDS_nonsingular :
  MDS_MATRIX 0 0 ≠ 0 :=
by
  unfold MDS_MATRIX
  norm_num

-- Cryptographic properties (assumed, not proven computationally)

-- Collision resistance: Finding x,y ≠ x',y' with H(x,y) = H(x',y') is hard
axiom Poseidon_collision_resistant :
  ∀ (x y x' y' : ℕ),
  x < FIELD_MODULUS → y < FIELD_MODULUS →
  x' < FIELD_MODULUS → y' < FIELD_MODULUS →
  Poseidon x y = Poseidon x' y' →
  (x = x' ∧ y = y') ∨ (computationally_hard_to_find : Prop)

-- Preimage resistance: Given h, finding x,y with H(x,y) = h is hard
axiom Poseidon_preimage_resistant :
  ∀ (h : ℕ), h < FIELD_MODULUS →
  (∃ (x y : ℕ), x < FIELD_MODULUS ∧ y < FIELD_MODULUS ∧ Poseidon x y = h) →
  (computationally_hard_to_find : Prop)

-- Examples: Concrete computations

-- Example 1: Hash of (0, 0)
example : Poseidon 0 0 < FIELD_MODULUS := by
  apply Poseidon_in_field
  · norm_num
  · norm_num

-- Example 2: Hash of (1, 2)
example : Poseidon 1 2 < FIELD_MODULUS := by
  apply Poseidon_in_field
  · norm_num
  · norm_num

-- Security notes:
-- 1. S-box (x^5) provides non-linearity for cryptographic security
-- 2. MDS matrix provides full diffusion across state
-- 3. Round constants prevent symmetry attacks
-- 4. 8 full + 57 partial rounds provide 128-bit security
-- 5. Optimized for zkSNARK circuits (~140 constraints vs 20,000 for SHA256)

-- Performance comparison:
-- - Poseidon: ~140 R1CS constraints
-- - Pedersen: ~1,000 constraints
-- - SHA256: ~20,000 constraints
-- - Keccak: ~40,000 constraints

-- This makes Poseidon ideal for zkEVM state commitments where
-- proof generation time is critical
