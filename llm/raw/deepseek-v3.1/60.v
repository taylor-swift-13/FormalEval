
Require Import ZArith.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = ((n + 1) * n) / 2.
