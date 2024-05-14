import Mathlib

open Polynomial nonZeroDivisors BigOperators

variable {R : Type* } [CommSemiring R] (P : R[X])

def Ann := {Q | Q * P= 0 ∧ Q ≠ 0}

lemma Ann_nonvide (h : P ∉ R[X]⁰) : Ann P ≠ ∅ := by
  intro hvide
  refine h (fun Q hQ => ?_)
  by_contra! hQ0
  have hQmem : Q ∈ Ann P := ⟨hQ, hQ0⟩
  rw [hvide] at hQmem
  exact hQmem
lemma Anndeg_nonvide (h : P ∉ R[X]⁰) : natDegree '' (Ann P) ≠ ∅ := by
  simp [Ann_nonvide P h]

noncomputable
def m := sInf (natDegree '' (Ann P))

lemma Lemma3 (h : P ∉ R[X]⁰) (h' : m P = 0 ) : ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  have : ∃ Q ∈ Ann P, natDegree Q = m P := Nat.sInf_mem (Set.nmem_singleton_empty.mp (Anndeg_nonvide P h))
  rw [h'] at this
  dsimp [Ann] at this
  cases' this with Q hQ
  have ⟨x, hx⟩ : ∃ (x : R), Polynomial.C x = Q := by
   rw [Polynomial.natDegree_eq_zero] at hQ
   exact hQ.right
  rw [← hx, ← Polynomial.smul_eq_C_mul, C_eq_zero] at hQ
  exact ⟨x, hQ.1.2, hQ.1.1⟩

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
  have hm : m P ≤ 0 := by
    dsimp[m]
    simp
    left
    exact ⟨C ( leadingCoeff Q), ‹_›, by simp⟩
  exact h' <| Nat.le_zero.mp hm

lemma Lemma5 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ Ann P) :
    ∃ i, P.coeff i • Q ≠ 0 := by
  obtain ⟨i, hi⟩ := Lemma4 P h' Q hQ
  use i
  rw [<- Polynomial.leadingCoeff_ne_zero, Polynomial.smul_eq_C_mul,
    Polynomial.leadingCoeff_mul', Polynomial.leadingCoeff_C, mul_comm]
  · exact hi
  · rw [Polynomial.leadingCoeff_C, mul_comm]
    exact hi

noncomputable
def l (Q : R[X]) := sSup {i | P.coeff i • Q ≠ 0}

lemma Lemma6 (Q : R[X]) (hQ : Q ∈ Ann P) : (P.coeff (l P Q) • Q) * P = 0 := by
  rw [Polynomial.smul_eq_C_mul, mul_assoc]
  dsimp [Ann] at hQ
  rw [hQ.1, mul_zero]

lemma Lemma7 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ Ann P) :
    P.coeff (l P Q) • Q ≠ 0 := by
  have : l P Q ∈ { i | P.coeff i • Q ≠ 0 } := by
    apply Nat.sSup_mem (Lemma5 P h' Q hQ)
    · use P.natDegree
      intro i hi
      by_contra! H
      apply hi
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt H, zero_smul]
  exact this

open Finset Nat
lemma Lemma11 (Q : R[X]) (hmQ : natDegree Q = m P) :
  (Q * P).coeff (l P Q + m P) = P.coeff (l P Q) •  leadingCoeff Q := by
  rw [mul_comm Q, Polynomial.coeff_mul]
  have h1 : ∀ i, ∀j , ( l P Q < i) → P.coeff i * Q.coeff j = 0 := by
    intro k j H
    dsimp [l] at H
    have H' : P.coeff k • Q = 0 := by
      by_contra!
      rw [lt_iff_not_le] at H
      apply H
      apply le_csSup
      · use P.natDegree
        intro i hi
        by_contra! H
        apply hi
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt H, zero_smul]
      · exact this
    rw [<-Polynomial.C_mul'] at H'
    rw [<-Polynomial.coeff_C_mul]
    exact Mathlib.Tactic.ComputeDegree.coeff_congr (congrFun (congrArg coeff H') j) rfl rfl
  have h2 : ∀ i, ∀j , ( m P < j) → P.coeff i * Q.coeff j = 0 := by
    intro k j H
    rw [<-hmQ] at H
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt H, mul_zero]
  rw [sum_antidiagonal_eq_sum_range_succ (fun i j ↦ P.coeff i * Q.coeff j), ← succ_add, sum_range_add,
    sum_range_succ]
  have h3 : coeff P (l P Q) * coeff Q (l P Q + m P - l P Q) = coeff P (l P Q) • leadingCoeff Q := by
    simp [leadingCoeff, hmQ]
  rw [h3, add_comm _ (coeff P (l P Q) • leadingCoeff Q), add_assoc]
  simp only [smul_eq_mul]
  nth_rewrite 2 [← add_zero (coeff P (l P Q) * leadingCoeff Q)]
  rw [← zero_add (0 : R)]
  congr
  · apply Finset.sum_eq_zero
    intro k hk
    apply h2
    simp only [mem_range] at hk
    rw [add_comm, Nat.add_sub_assoc hk.le]
    simp only [lt_add_iff_pos_right, tsub_pos_iff_lt]
    exact hk
  · exact Finset.sum_eq_zero (fun k _ ↦ h1 _ _ (by omega))

lemma Lemma8 (Q : R[X]) (hQ : Q ∈ Ann P) (hmQ : natDegree Q = m P) :
    P.coeff (l P Q) •  Q.leadingCoeff = 0 := by
  rw [← Lemma11 _ _ hmQ, hQ.1]
  simp

lemma Lemma9 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ Ann P) (hmQ : natDegree Q = m P) :
    natDegree (P.coeff (l P Q) • Q) < natDegree Q := by
  refine lt_of_le_of_ne (natDegree_smul_le (coeff P (l P Q)) Q) (fun h ↦ ?_)
  have := Lemma8 P Q hQ hmQ
  rw [← coeff_natDegree, ← h, ← coeff_smul, coeff_natDegree, leadingCoeff_eq_zero] at this
  exact Lemma7 P h' Q hQ this

theorem McCoy : P ∉ R[X]⁰ ↔ ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  refine ⟨fun h ↦ Lemma3 P h ?_,
    fun ⟨a, ha, h⟩ h1 ↦ ha <| C_eq_zero.1 <| (h1 (C a)) <| smul_eq_C_mul a ▸ h⟩
  by_contra! Hm
  cases' Nat.sInf_mem (Set.nmem_singleton_empty.mp (Anndeg_nonvide P h)) with Q hQ
  cases' hQ with hQP hQdeg
  let Q' := P.coeff (l P Q) • Q
  have hQ' : Q' ∈ Ann P := ⟨Lemma6 P Q hQP, Lemma7 P Hm Q hQP⟩
  have key : natDegree Q' < natDegree Q := by exact Lemma9 P Hm Q hQP hQdeg
  rw [hQdeg] at key
  have hdegQ' : natDegree Q' ∈ natDegree '' (Ann P) := by
    use Q'
  rw [lt_iff_not_le] at key
  exact key <| Nat.sInf_le hdegQ'
