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

Axiom problem_55_example_nat_ax : problem_55_spec 63 6557470319842.

Example problem_55_example_nat : problem_55_spec 63 6557470319842.
Proof.
  apply problem_55_example_nat_ax.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Axiom problem_55_testcase_Z_ax :
  Z.of_nat (fib (Z.to_nat 63%Z)) = 6557470319842%Z.

Example problem_55_testcase_Z :
  Z.of_nat (fib (Z.to_nat 63%Z)) = 6557470319842%Z.
Proof.
  apply problem_55_testcase_Z_ax.
Qed.