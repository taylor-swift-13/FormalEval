Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
*)
Inductive is_fib : Z -> Z -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (n + 1) res_n1 ->
               is_fib (n + 2) (res_n1 + res_n).

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  is_fib n res.

(* Test case: input = 66, output = 27777890035288 *)
Example test_fib_66 : problem_55_spec 66 27777890035288.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.

  Ltac step :=
    match goal with
    | [ H1 : is_fib ?n ?fn, H2 : is_fib ?n1 ?fn1 |- _ ] =>
      let n_next := eval compute in (n + 1) in
      constr_eq n1 n_next;
      let n_target := eval compute in (n + 2) in
      match goal with
      | [ H : is_fib n_target _ |- _ ] => fail 1
      | _ =>
        let fn_target := eval compute in (fn + fn1) in
        assert (is_fib n_target fn_target) by (
          replace n_target with (n + 2) by reflexivity;
          replace fn_target with (fn1 + fn) by reflexivity;
          apply fib_step; [ exact H1 | replace (n + 1) with n1 by reflexivity; exact H2 ]
        )
      end
    end.

  do 65 step.

  match goal with
  | [ H : is_fib 66 ?res |- _ ] =>
    replace 27777890035288 with res by reflexivity;
    exact H
  end.
Qed.