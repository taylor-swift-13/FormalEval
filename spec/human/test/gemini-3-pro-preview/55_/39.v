Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
*)
Inductive is_fib : nat -> Z -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  is_fib (Z.to_nat n) res.

(* Test case: input = 45, output = 1134903170 *)
Example test_fib_45 : problem_55_spec 45 1134903170.
Proof.
  unfold problem_55_spec.
  simpl.
  (* We build the proof bottom-up to avoid exponential branching in the proof tree *)
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.

  do 44 (
    match goal with
    | [ H1 : is_fib ?n ?fn, H2 : is_fib (S ?n) ?fn1 |- _ ] =>
      let next_val := eval compute in (fn1 + fn) in
      let next_n := eval compute in (S (S n)) in
      assert (is_fib next_n next_val) by (
        replace next_val with (fn1 + fn) by reflexivity;
        apply fib_step; assumption
      );
      clear H1
    end
  ).

  assumption.
Qed.