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

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  res = fibfib n.

Example test_fibfib_18 : problem_63_spec 18 10609.
Proof.
  unfold problem_63_spec.
  simpl.
  reflexivity.
Qed.