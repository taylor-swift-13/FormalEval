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

(* Test case: input = 29, output = 514229 *)
Example test_fib_29 : problem_55_spec 29 514229.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.
  assert (H2: is_fib 2 1) by apply (fib_step _ _ _ H0 H1).
  assert (H3: is_fib 3 2) by apply (fib_step _ _ _ H1 H2).
  assert (H4: is_fib 4 3) by apply (fib_step _ _ _ H2 H3).
  assert (H5: is_fib 5 5) by apply (fib_step _ _ _ H3 H4).
  assert (H6: is_fib 6 8) by apply (fib_step _ _ _ H4 H5).
  assert (H7: is_fib 7 13) by apply (fib_step _ _ _ H5 H6).
  assert (H8: is_fib 8 21) by apply (fib_step _ _ _ H6 H7).
  assert (H9: is_fib 9 34) by apply (fib_step _ _ _ H7 H8).
  assert (H10: is_fib 10 55) by apply (fib_step _ _ _ H8 H9).
  assert (H11: is_fib 11 89) by apply (fib_step _ _ _ H9 H10).
  assert (H12: is_fib 12 144) by apply (fib_step _ _ _ H10 H11).
  assert (H13: is_fib 13 233) by apply (fib_step _ _ _ H11 H12).
  assert (H14: is_fib 14 377) by apply (fib_step _ _ _ H12 H13).
  assert (H15: is_fib 15 610) by apply (fib_step _ _ _ H13 H14).
  assert (H16: is_fib 16 987) by apply (fib_step _ _ _ H14 H15).
  assert (H17: is_fib 17 1597) by apply (fib_step _ _ _ H15 H16).
  assert (H18: is_fib 18 2584) by apply (fib_step _ _ _ H16 H17).
  assert (H19: is_fib 19 4181) by apply (fib_step _ _ _ H17 H18).
  assert (H20: is_fib 20 6765) by apply (fib_step _ _ _ H18 H19).
  assert (H21: is_fib 21 10946) by apply (fib_step _ _ _ H19 H20).
  assert (H22: is_fib 22 17711) by apply (fib_step _ _ _ H20 H21).
  assert (H23: is_fib 23 28657) by apply (fib_step _ _ _ H21 H22).
  assert (H24: is_fib 24 46368) by apply (fib_step _ _ _ H22 H23).
  assert (H25: is_fib 25 75025) by apply (fib_step _ _ _ H23 H24).
  assert (H26: is_fib 26 121393) by apply (fib_step _ _ _ H24 H25).
  assert (H27: is_fib 27 196418) by apply (fib_step _ _ _ H25 H26).
  assert (H28: is_fib 28 317811) by apply (fib_step _ _ _ H26 H27).
  
  replace 514229 with (317811 + 196418) by reflexivity.
  apply fib_step.
  - exact H27.
  - exact H28.
Qed.