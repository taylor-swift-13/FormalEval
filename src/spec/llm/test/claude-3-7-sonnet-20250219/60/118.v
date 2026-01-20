Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_999999_test : sum_to_n_spec 999999 499999500000.
Proof.
  unfold sum_to_n_spec.
  replace (499999500000) with ((999999 * (999999 + 1)) / 2) by reflexivity.
  reflexivity.
Qed.