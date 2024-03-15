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

lemma Lemma3 (h : P ∉ R[X]⁰) (h' : m P = 0 ) : ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  have := Lemma2 P h
  rw [h'] at this
  dsimp [Ann] at this
  cases' this with Q hQ
  have h'Q : ∃ (x : R), Polynomial.C x = Q := by
   rw [Polynomial.natDegree_eq_zero] at hQ
   exact hQ.right
  cases' h'Q with x hx
  symm at hx
  rw [hx] at hQ
  rw [<-Polynomial.smul_eq_C_mul] at hQ
  simp
  rw [C_eq_zero] at hQ
  use x
  constructor
  · exact hQ.1.2
  · exact hQ.1.1
  done

lemma Lemma4 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ Ann P) :
    ∃ i, Q.leadingCoeff * P.coeff i ≠ 0 := by
  by_contra!
  have hP : leadingCoeff Q • P = 0 := by
    exact leadingCoeff_eq_zero.mp (this (natDegree (leadingCoeff Q • P)))
  have hceoffQ : C (leadingCoeff Q) ∈ Ann P := by
    dsimp [Ann]
    constructor
    · rw [Polynomial.smul_eq_C_mul] at hP
      exact hP
    · simp
      dsimp[Ann] at hQ
      exact hQ.2
  apply h'
  have hm : m P ≤ 0 := by
    dsimp[m]
    simp
    left
    dsimp[Anndeg]
    simp
    use C ( leadingCoeff Q)
    constructor
    · assumption
    · simp
  exact Nat.le_zero.mp hm
  done
lemma Lemma5 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ Ann P) :
    ∃ i, P.coeff i • Q ≠ 0 := by
  obtain ⟨i, hi⟩ := Lemma4 P h' Q hQ
  use i
  rw [<- Polynomial.leadingCoeff_ne_zero, Polynomial.smul_eq_C_mul,
    Polynomial.leadingCoeff_mul', Polynomial.leadingCoeff_C, mul_comm]
  · exact hi
  · rw [Polynomial.leadingCoeff_C, mul_comm]
    exact hi





  sorry
  done



theorem McCoy : P ∉ R[X]⁰ ↔ ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  constructor
  · intro h
    apply  Lemma3 P h
    by_contra! Hm
    have H'm := Lemma4 P Hm
    cases' Lemma2 P h with Q hQ
    cases' hQ with hQP hQdeg
    dsimp[Ann] at hQP
    cases' hQP with hQP1 hQP2
    let l := natDegree (leadingCoeff Q • P)
    sorry
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
