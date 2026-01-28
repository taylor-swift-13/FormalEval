Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example test_sum_to_n_17: sum_to_n_spec 17 153.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.