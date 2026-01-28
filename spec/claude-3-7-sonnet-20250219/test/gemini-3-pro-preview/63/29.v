Require Import Arith.Arith.

Fixpoint fibfib_iter (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib (n : nat) : nat :=
  fibfib_iter n 0 0 1.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 16 3136.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.