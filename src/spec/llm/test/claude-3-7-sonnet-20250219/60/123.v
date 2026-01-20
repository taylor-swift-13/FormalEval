Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_999998_test : sum_to_n_spec 999998 499998500001.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.