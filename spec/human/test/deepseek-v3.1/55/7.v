Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_false_pre (b : bool) : Prop := True.
Definition problem_false_spec (b : bool) (res : nat) : Prop :=
  match b with
  | true => False
  | false => res = 0
  end.

Example problem_false_output : problem_false_spec false 0.
Proof.
  unfold problem_false_spec.
  simpl.
  reflexivity.
Qed.