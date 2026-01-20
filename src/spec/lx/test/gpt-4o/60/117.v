Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_to_n_spec (n output: Z) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_499996 :
  sum_to_n_spec 499996 124998250006.
Proof.
  unfold sum_to_n_spec.
  compute.
  reflexivity.
Qed.