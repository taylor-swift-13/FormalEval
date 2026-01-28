Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n_212 : sum_to_n_spec 212%Z 22578%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.