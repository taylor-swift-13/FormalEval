Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_54_pre (n : nat) : Prop := True.
Definition problem_54_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_12_correct : problem_54_spec 12 144.
Proof.
  unfold problem_54_spec.
  simpl.
  reflexivity.
Qed.