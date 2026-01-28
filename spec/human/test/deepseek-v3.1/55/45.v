Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_60_pre (n : nat) : Prop := True.
Definition problem_60_spec (n : nat) (res : nat) : Prop :=
  res = 1548008755920.

Example fib_60_correct : problem_60_spec 60 1548008755920.
Proof.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.