
Require Import ZArith.

Definition starts_one_ends_spec (n : Z) (count : Z) : Prop :=
  n = 1 -> count = 1 /\
  n > 1 -> count = 18 * 10 ^ (n - 2).
