Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_499994_test : sum_to_n_spec 499994 124997250015.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.