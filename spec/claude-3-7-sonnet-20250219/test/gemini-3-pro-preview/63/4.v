Require Import Arith.Arith.

Fixpoint fibfib_aux (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => a
  | S n' => fibfib_aux n' b c (a + b + c)
  end.

Definition fibfib (n : nat) : nat :=
  fibfib_aux n 0 0 1.

Example fibfib_test_case : fibfib 8 = 24.
Proof.
  reflexivity.
Qed.