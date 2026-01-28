Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

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

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  res = fibfib n.

Example fibfib_test_false : problem_63_spec 0 0.
Proof.
  unfold problem_63_spec.
  simpl.
  reflexivity.
Qed.