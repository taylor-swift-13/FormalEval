Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_55_pre (n : nat) : Prop := True.
Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_14_correct : problem_55_spec 14 377.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.