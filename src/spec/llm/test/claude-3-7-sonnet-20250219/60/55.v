Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_54_test : sum_to_n_spec 54 1485.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.