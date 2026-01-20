Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_3 : sum_to_n_spec 3 6.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.