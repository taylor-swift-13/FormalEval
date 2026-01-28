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

(* Test case: input = 17, output = 1597 *)
Example test_fib_17 : problem_55_spec 17 1597.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.

  assert (H2: is_fib 2 1).
  { replace 1 with (1 + 0) by reflexivity.
    apply fib_step; assumption. }

  assert (H3: is_fib 3 2).
  { replace 2 with (1 + 1) by reflexivity.
    apply fib_step; assumption. }

  assert (H4: is_fib 4 3).
  { replace 3 with (2 + 1) by reflexivity.
    apply fib_step; assumption. }

  assert (H5: is_fib 5 5).
  { replace 5 with (3 + 2) by reflexivity.
    apply fib_step; assumption. }

  assert (H6: is_fib 6 8).
  { replace 8 with (5 + 3) by reflexivity.
    apply fib_step; assumption. }

  assert (H7: is_fib 7 13).
  { replace 13 with (8 + 5) by reflexivity.
    apply fib_step; assumption. }

  assert (H8: is_fib 8 21).
  { replace 21 with (13 + 8) by reflexivity.
    apply fib_step; assumption. }

  assert (H9: is_fib 9 34).
  { replace 34 with (21 + 13) by reflexivity.
    apply fib_step; assumption. }

  assert (H10: is_fib 10 55).
  { replace 55 with (34 + 21) by reflexivity.
    apply fib_step; assumption. }

  assert (H11: is_fib 11 89).
  { replace 89 with (55 + 34) by reflexivity.
    apply fib_step; assumption. }

  assert (H12: is_fib 12 144).
  { replace 144 with (89 + 55) by reflexivity.
    apply fib_step; assumption. }

  assert (H13: is_fib 13 233).
  { replace 233 with (144 + 89) by reflexivity.
    apply fib_step; assumption. }

  assert (H14: is_fib 14 377).
  { replace 377 with (233 + 144) by reflexivity.
    apply fib_step; assumption. }

  assert (H15: is_fib 15 610).
  { replace 610 with (377 + 233) by reflexivity.
    apply fib_step; assumption. }

  assert (H16: is_fib 16 987).
  { replace 987 with (610 + 377) by reflexivity.
    apply fib_step; assumption. }

  replace 1597 with (987 + 610) by reflexivity.
  apply fib_step.
  - exact H15.
  - exact H16.
Qed.