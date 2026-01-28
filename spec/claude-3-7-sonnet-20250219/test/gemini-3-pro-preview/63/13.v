Require Import Arith.Arith.

Fixpoint fibfib_aux (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => a
  | 1 => b
  | 2 => c
  | S n' => fibfib_aux n' b c (a + b + c)
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  res = fibfib_aux n 0 0 1.

Example fibfib_test_case : fibfib_spec 25 755476.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.