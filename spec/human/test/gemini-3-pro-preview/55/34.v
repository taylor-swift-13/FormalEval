Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(*
  fib is a recursive function defining the Fibonacci sequence.
  We use a tail-recursive implementation on Z to handle large inputs efficiently
  and avoid timeouts during verification.
*)
Fixpoint fib_iter (n : nat) (a b : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fib_iter n' b (a + b)
  end.

Definition fib (n : nat) : Z :=
  fib_iter n 0 1.

(*
  fib_spec is the specification for the fib function.
*)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  res = fib n.

(* Test case: input = 75, output = 2111485077978050 *)
Example problem_55_test : problem_55_spec 75%nat 2111485077978050.
Proof.
  (* Unfold the specification definition *)
  unfold problem_55_spec.
  
  (* Compute the value of fib 75 efficiently using vm_compute *)
  vm_compute.
  
  (* Prove that the result matches the expected value *)
  reflexivity.
Qed.