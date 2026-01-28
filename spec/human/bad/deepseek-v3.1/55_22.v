Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_62_pre (n : nat) : Prop := True.
Definition problem_62_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

Example fib_62_correct : problem_62_spec 62 4052739537881.
Proof.
  unfold problem_62_spec.
  reflexivity.
Qed.