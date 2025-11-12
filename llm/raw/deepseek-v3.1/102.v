
Definition choose_num_spec (x : nat) (y : nat) (result : Z) : Prop :=
  (x > y) -> result = -1 /\
  (x <= y) -> (exists n, x <= n <= y /\ Even n) -> result = Z.of_nat (max_even_in_range x y) /\
  (x <= y) -> (forall n, x <= n <= y -> ~Even n) -> result = -1.
