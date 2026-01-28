Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_25 : sum_to_n_spec 25 325.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.