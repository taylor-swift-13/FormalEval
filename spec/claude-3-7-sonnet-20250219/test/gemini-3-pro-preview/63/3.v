Require Import Arith.Arith.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
      match n' with
      | 0 => 0
      | S n'' =>
          match n'' with
          | 0 => 1
          | S n''' => fibfib n' + fibfib n'' + fibfib n'''
          end
      end
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 5 4.
Proof.
  unfold fibfib_spec.
  simpl.
  reflexivity.
Qed.