Require Import Arith.Arith.

Fixpoint fibfib_iter (n : nat) (a b c : nat) : nat :=
  match n with
  | 0 => c
  | S n' => fibfib_iter n' b c (a + b + c)
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  match n with
  | 0 => res = 0
  | 1 => res = 0
  | _ => res = fibfib_iter (n - 2) 0 0 1
  end.

Example fibfib_test_case : fibfib_spec 24 410744.
Proof.
  reflexivity.
Qed.