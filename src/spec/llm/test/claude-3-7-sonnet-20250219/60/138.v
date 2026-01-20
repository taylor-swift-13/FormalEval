Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_532176_test : sum_to_n_spec 532176 141605913576.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.