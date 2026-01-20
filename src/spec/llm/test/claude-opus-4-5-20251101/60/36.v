Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_90 : sum_to_n_spec 90 4095.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.