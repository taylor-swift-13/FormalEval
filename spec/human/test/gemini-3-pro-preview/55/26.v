Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Open Scope Z_scope.

(*
  fib 是一个递归函数，定义了斐波那契数列。
*)
Fixpoint fib_aux (n : nat) (a b : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fib_aux n' b (a + b)
  end.

Definition fib (n : nat) : Z :=
  fib_aux n 0 1.

(*
  fib_spec 是对 fib 函数的程序规约。
*)
Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  res = fib (Z.to_nat n).

(* Test case: input = 61, output = 2504730781961 *)
Example problem_55_test : problem_55_spec 61 2504730781961.
Proof.
  (* Unfold the specification definition *)
  unfold problem_55_spec.
  
  (* Simplify the execution of fib 61 *)
  vm_compute.
  
  (* Prove that 2504730781961 = 2504730781961 *)
  reflexivity.
Qed.