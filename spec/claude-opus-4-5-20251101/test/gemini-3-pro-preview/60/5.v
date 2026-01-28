Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_100 : sum_to_n_spec 100 5050.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.