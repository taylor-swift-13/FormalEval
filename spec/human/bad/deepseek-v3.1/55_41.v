Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_514229_pre (n : nat) : Prop := True.
Definition problem_514229_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_29_correct : problem_514229_spec 29 514229.
Proof.
  unfold problem_514229_spec.
  simpl.
  reflexivity.
Qed.