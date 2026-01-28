Require Import Arith.Arith.

Fixpoint fibfib_iter (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => a
  | S k => fibfib_iter k b c (a + b + c)
  end.

Definition fibfib (n : nat) : nat :=
  fibfib_iter n 0 0 1.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 15 1705.
Proof.
  reflexivity.
Qed.