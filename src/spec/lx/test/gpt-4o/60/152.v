Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition sum_to_n_spec (n output: Z) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_532173 :
  sum_to_n_spec 532173 141604317051.
Proof.
  unfold sum_to_n_spec.
  simpl.
  (* Simplify both sides of the equation *)
  compute.
  reflexivity.
Qed.