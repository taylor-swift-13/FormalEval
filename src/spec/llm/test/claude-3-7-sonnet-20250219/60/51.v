Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_28_test : sum_to_n_spec 28 406.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.