Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_61_pre (n : nat) : Prop := True.
Definition problem_61_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_61_correct : problem_61_spec 61 2504730781961.
Proof.
  unfold problem_61_spec.
  reflexivity.
Qed.