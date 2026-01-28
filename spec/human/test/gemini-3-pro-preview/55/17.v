Require Import Coq.Init.Nat.

(*
  fib 是一个递归函数，定义了斐波那契数列。
*)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
    | 0 => 1
    | S n'' => fib n'' + fib n'
    end
  end.

(*
  fib_spec 是对 fib 函数的程序规约。
*)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  res = fib n.

(* Test case: input = 3, output = 2 *)
Example problem_55_test : problem_55_spec 3 2.
Proof.
  (* Unfold the specification definition *)
  unfold problem_55_spec.
  
  (* Simplify the execution of fib 3 *)
  simpl.
  
  (* Prove that 2 = 2 *)
  reflexivity.
Qed.