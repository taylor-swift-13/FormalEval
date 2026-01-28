Require Import Arith Lia.

(* Definition of the specification *)
Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output : nat) : Prop :=
  2 * output = n * (n + 1).

(* Test case proof *)
Example problem_60_test_case:
  problem_60_spec 996 496506.
Proof.
  unfold problem_60_spec.
  replace (996 * (996 + 1)) with 992012 by lia.
  lia.
Qed.