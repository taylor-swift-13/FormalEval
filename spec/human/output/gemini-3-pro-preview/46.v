Require Import Coq.Arith.Arith.

(* 使用 Fixpoint 表示 fib4 序列 *)
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

Example test_problem_46 : problem_46_spec 5 4.
Proof.
  unfold problem_46_spec.
  (* 
     fib4 5 
     = fib4 4 + fib4 3 + fib4 2 + fib4 1
     = (fib4 3 + fib4 2 + fib4 1 + fib4 0) + 0 + 2 + 0
     = (0 + 2 + 0 + 0) + 2
     = 4
  *)
  simpl.
  reflexivity.
Qed.