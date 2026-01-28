Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example test_sum_to_n_54: sum_to_n_spec 54 1485.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.