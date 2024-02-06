import Mathlib

open Polynomial nonZeroDivisors

variable (R : Type*) [CommRing R] (P : R[X])

theorem McCoy : P ∉ R[X]⁰ ↔ ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  constructor
  · sorry
  · intro h h1
    cases' h with a h3
    cases' h3 with h4 h5
    rw [mem_nonZeroDivisors_iff] at h1
    specialize h1 (C a)
    have h6 : a • P = ( C a ) * P := by
      exact smul_eq_C_mul a
    rw [h6] at h5
    have h7:= h1 h5
    have h8 : a = 0 := by
      exact C_eq_zero.mp h7
    exact h4 h8
