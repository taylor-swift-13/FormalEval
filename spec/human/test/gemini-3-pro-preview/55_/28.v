Require Import Coq.Init.Nat.

(*
  is_fib is a logical relation defining the Fibonacci sequence using first-order logic rules.
  It asserts "res is the n-th Fibonacci number".
*)
Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

(* Pre: no special constraints for `fib` *)
Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

(* Test case: input = 4, output = 3 *)
Example test_fib_4 : problem_55_spec 4 3.
Proof.
  unfold problem_55_spec.
  (* We build the proof bottom-up to avoid exponential branching in the proof tree *)
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.
  
  assert (H2: is_fib 2 1).
  { replace 1 with (1 + 0) by reflexivity.
    apply fib_step; assumption. }
    
  assert (H3: is_fib 3 2).
  { replace 2 with (1 + 1) by reflexivity.
    apply fib_step; assumption. }
    
  (* Finally, prove for 4 *)
  replace 3 with (2 + 1) by reflexivity.
  apply fib_step.
  - exact H2.
  - exact H3.
Qed.