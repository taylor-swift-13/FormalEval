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
  res = if b then 1 else 0.

Example test_false : problem_63_spec false 0.
Proof.
  unfold problem_63_spec.
  simpl.
  reflexivity.
Qed.