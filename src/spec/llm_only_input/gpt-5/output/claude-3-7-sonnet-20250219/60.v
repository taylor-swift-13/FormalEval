Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_n_spec_test_1 :
  sum_to_n_spec 1%Z 1%Z.
Proof.
  unfold sum_to_n_spec.
  now compute.
Qed.