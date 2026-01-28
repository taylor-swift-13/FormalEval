Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
  We use Z for the result to handle large numbers.
*)
Inductive is_fib : nat -> Z -> Prop :=
  | fib_zero : is_fib 0%nat 0
  | fib_one  : is_fib 1%nat 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  is_fib n res.

(* Test case: input = 64, output = 10610209857723 *)
Example test_fib_64 : problem_55_spec 64%nat 10610209857723.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0%nat 0) by apply fib_zero.
  assert (H1: is_fib 1%nat 1) by apply fib_one.
  
  do 63 (
    match goal with
    | [ Hn : is_fib ?n ?rn, HSn : is_fib (S ?n) ?rSn |- _ ] =>
      let next_val := eval compute in (rSn + rn) in
      assert (is_fib (S (S n)) next_val) 
        by (replace next_val with (rSn + rn) by reflexivity; apply (fib_step n rn rSn Hn HSn));
      clear Hn
    end
  ).
  
  match goal with
  | [ H : is_fib 64%nat _ |- _ ] => exact H
  end.
Qed.