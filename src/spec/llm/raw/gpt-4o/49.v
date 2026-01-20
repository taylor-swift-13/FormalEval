
Require Import ZArith.

Definition modp_spec (n p res : Z) : Prop :=
  res = Z.pow 2 n mod p.
