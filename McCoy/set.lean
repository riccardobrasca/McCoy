import Mathlib

open Set

example (T : Type*) (A B C : Set T) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) :
    A ⊆ B := by
  intro x hx
  have h4 : A ⊆ A ∪ C := by
    exact fun ⦃a⦄ a_1 ↦ Or.inl a_1
  cases' h1 (h4 hx) with a b
  · exact a
  · have c := And.intro (hx) (b)
    exact mem_of_mem_inter_left (h2 c)
