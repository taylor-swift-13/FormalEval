Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_1134903170_pre (n : nat) : Prop := True.
Definition problem_1134903170_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_45_correct : problem_1134903170_spec 45 1134903170.
Proof.
  unfold problem_1134903170_spec.
  reflexivity.
Qed.