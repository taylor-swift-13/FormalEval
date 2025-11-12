
Require Import List ZArith.
Import ListNotations.

Definition factorize_spec (n : Z) (factors : list Z) : Prop :=
  n > 1 /\
  (forall p, In p factors -> prime p) /\
  (forall i, (i < length factors - 1)%nat -> nth i factors 0 <= nth (i + 1) factors 0) /\
  prod_list factors = n.
