Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_66 : sum_to_n_spec 66 2211.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.