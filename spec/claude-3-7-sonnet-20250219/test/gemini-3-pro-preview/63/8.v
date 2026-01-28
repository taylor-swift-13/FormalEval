Require Import Arith.Arith.

Fixpoint fibfib_iter (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => c
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | _ => fibfib_iter (n - 2) 0 0 1
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 20 35890.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.