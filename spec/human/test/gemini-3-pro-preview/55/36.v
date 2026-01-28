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

(* Test case: input = 28, output = 317811 *)
Example problem_55_test : problem_55_spec 28 317811.
Proof.
  (* Unfold the specification definition *)
  unfold problem_55_spec.
  
  (* Use vm_compute to avoid timeout with naive recursion *)
  vm_compute.
  
  (* Prove that 317811 = 317811 *)
  reflexivity.
Qed.