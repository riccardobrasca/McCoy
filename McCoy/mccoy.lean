import Mathlib

open Polynomial nonZeroDivisors

variable (R : Type*) [CommRing R] (P : R[X])

theorem McCoy : P ∉ R[X]⁰ ↔ ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  sorry
