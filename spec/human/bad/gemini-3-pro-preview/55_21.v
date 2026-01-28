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

Example problem_55_test : problem_55_spec 35 9227465.
Proof.
  unfold problem_55_spec.
  vm_compute.
  reflexivity.
Qed.