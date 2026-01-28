Require Import Coq.Init.Nat.

Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

Definition problem_1_pre (b : bool) : Prop := True.
Definition problem_1_spec (b : bool) (res : nat) : Prop :=
  match b with
  | true => res = 1
  | false => res = 0
  end.

Example input_true_output_1 : problem_1_spec true 1.
Proof.
  unfold problem_1_spec.
  simpl.
  reflexivity.
Qed.