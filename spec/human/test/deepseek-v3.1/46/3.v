Require Import Coq.Arith.Arith.
Require Import Lia.

Fixpoint fib4 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
    match n1 with
    | 0 => 0
    | S n2 =>
      match n2 with
      | 0 => 2
      | S n3 =>
        match n3 with
        | 0 => 0
        | S n4 => fib4 n1 + fib4 n2 + fib4 n3 + fib4 n4
        end
      end
    end
  end.

Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  output = fib4 input.

Example fib4_test_10 : problem_46_spec 10 104.
Proof.
  unfold problem_46_spec.
  simpl.
  reflexivity.
Qed.