Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_72_pre (n : nat) : Prop := True.
Definition problem_72_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_72_correct : problem_72_spec 72 498454011879264.
Proof.
  unfold problem_72_spec.
  simpl.
  reflexivity.
Qed.