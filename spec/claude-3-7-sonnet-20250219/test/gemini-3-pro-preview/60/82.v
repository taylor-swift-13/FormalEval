Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example test_sum_to_n_39: sum_to_n_spec 39 780.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.