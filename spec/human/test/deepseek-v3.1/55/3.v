Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_21_pre (n : nat) : Prop := True.
Definition problem_21_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_8_correct : problem_21_spec 8 21.
Proof.
  unfold problem_21_spec.
  simpl.
  reflexivity.
Qed.