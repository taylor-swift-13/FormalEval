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

Example test_fib_18 : problem_55_spec 18 2584.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.

Example test_fib_1 : problem_55_spec 1 1.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.

Example test_fib_8 : problem_55_spec 8 21.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.