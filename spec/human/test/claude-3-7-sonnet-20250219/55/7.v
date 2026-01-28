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
  match b with
  | true => fib 1
  | false => 0
  end = res.

Example test_fib_false : problem_55_spec false 0.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.