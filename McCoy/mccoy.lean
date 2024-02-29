import Mathlib

open Polynomial nonZeroDivisors

variable {R : Type* } [CommRing R] (P : R[X])

def Ann := {Q | Q * P= 0 ∧ Q ≠ 0}

lemma Ann_nonvide (h : P ∉ R[X]⁰) : Ann P ≠ ∅ := by
  intro hvide
  apply h
  rw [mem_nonZeroDivisors_iff]
  intro Q hQ
  by_contra! hQ0
  have hQmem : Q ∈ Ann P := by
    dsimp [Ann]
    constructor
    · exact hQ
    · exact hQ0
  rw [hvide] at hQmem
  exact hQmem
  done

def Anndeg := natDegree '' (Ann P)

lemma Anndeg_nonvide (h : P ∉ R[X]⁰) : Anndeg P ≠ ∅ := by
  dsimp [Anndeg]
  simp
  exact Ann_nonvide P h
  done

noncomputable
def m := sInf (Anndeg P)

lemma Lemma1 {Q : R[X]} (h : Q ∈ Ann P) : m P ≤ natDegree Q := by
  dsimp[m]
  exact Nat.sInf_le (Exists.intro Q { left := h, right := rfl })
  done

lemma Lemma2 (h : P ∉ R[X]⁰) : ∃ Q ∈ Ann P, natDegree Q = m P := by
  dsimp[m]
  have hnonvide : Set.Nonempty (Anndeg P) := by
    have := Anndeg_nonvide P h
    exact Set.nmem_singleton_empty.mp this
  have := Nat.sInf_mem hnonvide
  dsimp [Anndeg] at this
  simp at this
  exact this
  done

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
  done
