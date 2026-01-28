Require Import Coq.Init.Nat.

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

Definition problem_63_spec (b : bool) (res : nat) : Prop :=
  res = 0.

Example test_true_0 : problem_63_spec true 0.
Proof.
  unfold problem_63_spec.
  reflexivity.
Qed.