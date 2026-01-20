Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_1_test : sum_to_n_spec 1 1.
Proof.
  unfold sum_to_n_spec.
  (* Compute (1 * (1 + 1)) / 2 *)
  simpl.
  reflexivity.
Qed.