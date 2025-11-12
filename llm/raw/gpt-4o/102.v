
Require Import ZArith.

Definition choose_num_spec (x y result : Z) : Prop :=
  (x > y -> result = -1) /\
  (x = y -> result = (if Z.even y then y else -1)) /\
  (x < y -> result = (if Z.even y then y else y - 1)).
