
Require Import List ZArith.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  forall m : Z,
    (m > 1 -> In m factors -> exists k : Z, k > 0 /\ n = k * fold_left Z.mul factors 1) /\
    (forall p : Z, In p factors -> prime p) /\
    fold_left Z.mul factors 1 = n.
