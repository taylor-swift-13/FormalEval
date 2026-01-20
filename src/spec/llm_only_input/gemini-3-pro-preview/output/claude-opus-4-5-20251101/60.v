Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n : sum_to_n_spec 1 1.
Proof.
  unfold sum_to_n_spec.
  compute.
  reflexivity.
Qed.