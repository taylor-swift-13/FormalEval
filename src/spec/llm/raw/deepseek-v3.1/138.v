
Definition is_equal_to_sum_even_spec (n : nat) (result : bool) : Prop :=
  result = (n >= 8 && Nat.even n).
