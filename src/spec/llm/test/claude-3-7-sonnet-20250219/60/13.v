Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_50_test : sum_to_n_spec 50 1275.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.