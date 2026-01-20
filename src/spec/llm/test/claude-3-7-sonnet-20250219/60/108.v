Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_499998_test : sum_to_n_spec 499998 124999250001.
Proof.
  unfold sum_to_n_spec.
  replace (124999250001) with ((499998 * (499998 + 1)) / 2) by reflexivity.
  reflexivity.
Qed.