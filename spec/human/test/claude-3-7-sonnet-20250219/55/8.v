Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_55_pre (b : bool) : Prop := True.

Definition problem_55_spec (b : bool) (res : nat) : Prop :=
  res = if b then 1 else 0.

Example test_true : problem_55_spec true 1.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.