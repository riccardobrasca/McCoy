import Mathlib

open Polynomial nonZeroDivisors BigOperators

variable {R : Type* } [CommSemiring R] (P : R[X])

lemma Ann_nonvide (h : P ∉ R[X]⁰) : {Q | Q * P = 0 ∧ Q ≠ 0} ≠ ∅ := by
  intro hvide
  refine h (fun Q hQ => ?_)
  by_contra! hQ0
  have hQmem : Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0} := ⟨hQ, hQ0⟩
  rw [hvide] at hQmem
  exact hQmem

lemma Anndeg_nonvide (h : P ∉ R[X]⁰) : natDegree '' {Q | Q * P = 0 ∧ Q ≠ 0} ≠ ∅ := by
  simp [Ann_nonvide P h]

noncomputable
def m := sInf (natDegree '' ({Q | Q * P = 0 ∧ Q ≠ 0}))

lemma Lemma3 (h : P ∉ R[X]⁰) (h' : m P = 0 ) : ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  have : ∃ Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0}, natDegree Q = m P :=
    Nat.sInf_mem (Set.nmem_singleton_empty.mp (Anndeg_nonvide P h))
  rw [h'] at this
  dsimp only [ne_eq, Set.mem_setOf_eq] at this
  rcases this with ⟨Q, hQ⟩
  have ⟨x, hx⟩ : ∃ (x : R), C x = Q := by
   rw [natDegree_eq_zero] at hQ
   exact hQ.right
  rw [← hx, ← smul_eq_C_mul, C_eq_zero] at hQ
  exact ⟨x, hQ.1.2, hQ.1.1⟩

lemma Lemma4 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0}) :
    ∃ i, Q.leadingCoeff * P.coeff i ≠ 0 := by
  by_contra!
  refine h' <| Nat.le_zero.mp ?_
  simp [m]
  left
  refine ⟨C ( leadingCoeff Q), ⟨?_, by simp [hQ.2]⟩, by simp⟩
  rw [← smul_eq_C_mul]
  exact leadingCoeff_eq_zero.mp (this (natDegree (leadingCoeff Q • P)))


lemma Lemma5 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0}) :
    ∃ i, P.coeff i • Q ≠ 0 := by
  obtain ⟨i, hi⟩ := Lemma4 P h' Q hQ
  use i
  rw [← leadingCoeff_ne_zero, smul_eq_C_mul, leadingCoeff_mul', leadingCoeff_C, mul_comm]
  · exact hi
  · rw [leadingCoeff_C, mul_comm]
    exact hi

noncomputable
def l (Q : R[X]) := sSup {i | P.coeff i • Q ≠ 0}

lemma Lemma6 (Q : R[X]) (hQ : Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0}) : (P.coeff (l P Q) • Q) * P = 0 := by
  rw [smul_eq_C_mul, mul_assoc, hQ.1, mul_zero]

lemma Lemma7 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0}) :
    P.coeff (l P Q) • Q ≠ 0 := by
  show l P Q ∈ { i | P.coeff i • Q ≠ 0 }
  refine Nat.sSup_mem (Lemma5 P h' Q hQ) ⟨P.natDegree, fun i hi ↦ ?_⟩
  by_contra! H
  apply hi
  rw [coeff_eq_zero_of_natDegree_lt H, zero_smul]

open Finset Nat
lemma Lemma11 (Q : R[X]) (hmQ : natDegree Q = m P) :
  (Q * P).coeff (l P Q + m P) = P.coeff (l P Q) •  leadingCoeff Q := by
  rw [mul_comm Q, coeff_mul]
  have h1 : ∀ i, ∀j , ( l P Q < i) → P.coeff i * Q.coeff j = 0 := by
    intro k j H
    dsimp [l] at H
    have H' : P.coeff k • Q = 0 := by
      by_contra!
      rw [lt_iff_not_le] at H
      refine H (le_csSup ⟨P.natDegree, fun i hi ↦ ?_⟩ ?_)
      · by_contra! H
        apply hi
        rw [coeff_eq_zero_of_natDegree_lt H, zero_smul]
      · exact this
    rw [← C_mul'] at H'
    simp [← coeff_C_mul, H']
  have h2 : ∀ i, ∀j , ( m P < j) → P.coeff i * Q.coeff j = 0 := by
    intro k j H
    rw [← hmQ] at H
    rw [coeff_eq_zero_of_natDegree_lt H, mul_zero]
  rw [sum_antidiagonal_eq_sum_range_succ (fun i j ↦ P.coeff i * Q.coeff j), ← succ_add, sum_range_add,
    sum_range_succ]
  have h3 : coeff P (l P Q) * coeff Q (l P Q + m P - l P Q) = coeff P (l P Q) • leadingCoeff Q := by
    simp [leadingCoeff, hmQ]
  rw [h3, add_comm _ (coeff P (l P Q) • leadingCoeff Q), add_assoc]
  simp only [smul_eq_mul]
  nth_rewrite 2 [← add_zero (coeff P (l P Q) * leadingCoeff Q)]
  rw [← zero_add (0 : R)]
  congr
  · refine Finset.sum_eq_zero (fun k hk ↦ h2 _ _ ?_)
    simp only [mem_range] at hk
    rw [add_comm, Nat.add_sub_assoc hk.le]
    simpa
  · exact Finset.sum_eq_zero (fun k _ ↦ h1 _ _ (by omega))

lemma Lemma9 (h' : m P ≠ 0) (Q : R[X]) (hQ : Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0}) (hmQ : natDegree Q = m P) :
    natDegree (P.coeff (l P Q) • Q) < natDegree Q := by
  refine lt_of_le_of_ne (natDegree_smul_le (coeff P (l P Q)) Q) (fun h ↦ Lemma7 P h' Q hQ ?_)
  rw [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, h, coeff_natDegree]
  simp only [← Lemma11 _ _ hmQ, hQ.1, coeff_zero]

theorem McCoy : P ∉ R[X]⁰ ↔ ∃ (a : R), a ≠ 0 ∧ a • P = 0 := by
  refine ⟨fun h ↦ Lemma3 P h ?_,
    fun ⟨a, ha, h⟩ h1 ↦ ha <| C_eq_zero.1 <| (h1 (C a)) <| smul_eq_C_mul a ▸ h⟩
  by_contra! Hm
  rcases Nat.sInf_mem (Set.nmem_singleton_empty.mp (Anndeg_nonvide P h)) with ⟨Q, hQP, hQdeg⟩
  have hQ' : P.coeff (l P Q) • Q ∈ {Q | Q * P = 0 ∧ Q ≠ 0} := ⟨Lemma6 P Q hQP, Lemma7 P Hm Q hQP⟩
  have key : natDegree (P.coeff (l P Q) • Q) < natDegree Q := by exact Lemma9 P Hm Q hQP hQdeg
  rw [hQdeg] at key
  have hdegQ' : natDegree (P.coeff (l P Q) • Q) ∈ natDegree '' ({Q | Q * P = 0 ∧ Q ≠ 0}) := by
    use P.coeff (l P Q) • Q
  rw [lt_iff_not_le] at key
  exact key <| Nat.sInf_le hdegQ'
