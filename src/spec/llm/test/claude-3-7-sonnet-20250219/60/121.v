Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_1000001_test : sum_to_n_spec 1000001 500001500001.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.