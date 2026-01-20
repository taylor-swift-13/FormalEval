
Definition largest_divisor_spec (n : int) (result : int) : Prop :=
  (n > 1 → (∃ i : int, 2 ≤ i < n ∧ n mod i = 0) → 
   result = n / (MAX i | 2 ≤ i < n ∧ n mod i = 0)) ∧
  (n > 1 → (∀ i : int, 2 ≤ i < n → n mod i ≠ 0) → result = 1) ∧
  (n ≤ 1 → result = 1).
