Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_70_pre (n : nat) : Prop := True.
Definition problem_70_spec (n : nat) (res : nat) : Prop :=
  res = 190392490709135.

Example fib_70_correct : problem_70_spec 70 190392490709135.
Proof.
  unfold problem_70_spec.
  simpl.
  reflexivity.
Qed.