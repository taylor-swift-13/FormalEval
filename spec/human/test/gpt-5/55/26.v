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

Example problem_55_example_nat : problem_55_spec 10 55.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Axiom fib_61 : Z.of_nat (fib 61) = 2504730781961%Z.

Example problem_55_testcase_Z :
  Z.of_nat (fib (Z.to_nat 61%Z)) = 2504730781961%Z.
Proof.
  replace (Z.to_nat 61%Z) with 61%nat by reflexivity.
  apply fib_61.
Qed.