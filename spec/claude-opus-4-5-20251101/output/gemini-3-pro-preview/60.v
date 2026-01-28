Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_1 : sum_to_n_spec 1 1.
Proof.
  unfold sum_to_n_spec.
  (* The goal becomes: 1 = (1 * (1 + 1)) / 2 *)
  (* The right hand side evaluates to (1 * 2) / 2 = 2 / 2 = 1 *)
  reflexivity.
Qed.