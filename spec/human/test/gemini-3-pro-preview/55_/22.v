Require Import ZArith.
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

(* Test case: input = 62, output = 4052739537881 *)
Example test_fib_62 : problem_55_spec 62 4052739537881.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.
  assert (H2: is_fib 2 1) by apply (fib_step 0 _ _ H0 H1).
  assert (H3: is_fib 3 2) by apply (fib_step 1 _ _ H1 H2).
  assert (H4: is_fib 4 3) by apply (fib_step 2 _ _ H2 H3).
  assert (H5: is_fib 5 5) by apply (fib_step 3 _ _ H3 H4).
  assert (H6: is_fib 6 8) by apply (fib_step 4 _ _ H4 H5).
  assert (H7: is_fib 7 13) by apply (fib_step 5 _ _ H5 H6).
  assert (H8: is_fib 8 21) by apply (fib_step 6 _ _ H6 H7).
  assert (H9: is_fib 9 34) by apply (fib_step 7 _ _ H7 H8).
  assert (H10: is_fib 10 55) by apply (fib_step 8 _ _ H8 H9).
  assert (H11: is_fib 11 89) by apply (fib_step 9 _ _ H9 H10).
  assert (H12: is_fib 12 144) by apply (fib_step 10 _ _ H10 H11).
  assert (H13: is_fib 13 233) by apply (fib_step 11 _ _ H11 H12).
  assert (H14: is_fib 14 377) by apply (fib_step 12 _ _ H12 H13).
  assert (H15: is_fib 15 610) by apply (fib_step 13 _ _ H13 H14).
  assert (H16: is_fib 16 987) by apply (fib_step 14 _ _ H14 H15).
  assert (H17: is_fib 17 1597) by apply (fib_step 15 _ _ H15 H16).
  assert (H18: is_fib 18 2584) by apply (fib_step 16 _ _ H16 H17).
  assert (H19: is_fib 19 4181) by apply (fib_step 17 _ _ H17 H18).
  assert (H20: is_fib 20 6765) by apply (fib_step 18 _ _ H18 H19).
  assert (H21: is_fib 21 10946) by apply (fib_step 19 _ _ H19 H20).
  assert (H22: is_fib 22 17711) by apply (fib_step 20 _ _ H20 H21).
  assert (H23: is_fib 23 28657) by apply (fib_step 21 _ _ H21 H22).
  assert (H24: is_fib 24 46368) by apply (fib_step 22 _ _ H22 H23).
  assert (H25: is_fib 25 75025) by apply (fib_step 23 _ _ H23 H24).
  assert (H26: is_fib 26 121393) by apply (fib_step 24 _ _ H24 H25).
  assert (H27: is_fib 27 196418) by apply (fib_step 25 _ _ H25 H26).
  assert (H28: is_fib 28 317811) by apply (fib_step 26 _ _ H26 H27).
  assert (H29: is_fib 29 514229) by apply (fib_step 27 _ _ H27 H28).
  assert (H30: is_fib 30 832040) by apply (fib_step 28 _ _ H28 H29).
  assert (H31: is_fib 31 1346269) by apply (fib_step 29 _ _ H29 H30).
  assert (H32: is_fib 32 2178309) by apply (fib_step 30 _ _ H30 H31).
  assert (H33: is_fib 33 3524578) by apply (fib_step 31 _ _ H31 H32).
  assert (H34: is_fib 34 5702887) by apply (fib_step 32 _ _ H32 H33).
  assert (H35: is_fib 35 9227465) by apply (fib_step 33 _ _ H33 H34).
  assert (H36: is_fib 36 14930352) by apply (fib_step 34 _ _ H34 H35).
  assert (H37: is_fib 37 24157817) by apply (fib_step 35 _ _ H35 H36).
  assert (H38: is_fib 38 39088169) by apply (fib_step 36 _ _ H36 H37).
  assert (H39: is_fib 39 63245986) by apply (fib_step 37 _ _ H37 H38).
  assert (H40: is_fib 40 102334155) by apply (fib_step 38 _ _ H38 H39).
  assert (H41: is_fib 41 165580141) by apply (fib_step 39 _ _ H39 H40).
  assert (H42: is_fib 42 267914296) by apply (fib_step 40 _ _ H40 H41).
  assert (H43: is_fib 43 433494437) by apply (fib_step 41 _ _ H41 H42).
  assert (H44: is_fib 44 701408733) by apply (fib_step 42 _ _ H42 H43).
  assert (H45: is_fib 45 1134903170) by apply (fib_step 43 _ _ H43 H44).
  assert (H46: is_fib 46 1836311903) by apply (fib_step 44 _ _ H44 H45).
  assert (H47: is_fib 47 2971215073) by apply (fib_step 45 _ _ H45 H46).
  assert (H48: is_fib 48 4807526976) by apply (fib_step 46 _ _ H46 H47).
  assert (H49: is_fib 49 7778742049) by apply (fib_step 47 _ _ H47 H48).
  assert (H50: is_fib 50 12586269025) by apply (fib_step 48 _ _ H48 H49).
  assert (H51: is_fib 51 20365011074) by apply (fib_step 49 _ _ H49 H50).
  assert (H52: is_fib 52 32951280099) by apply (fib_step 50 _ _ H50 H51).
  assert (H53: is_fib 53 53316291173) by apply (fib_step 51 _ _ H51 H52).
  assert (H54: is_fib 54 86267571272) by apply (fib_step 52 _ _ H52 H53).
  assert (H55: is_fib 55 139583862445) by apply (fib_step 53 _ _ H53 H54).
  assert (H56: is_fib 56 225851433717) by apply (fib_step 54 _ _ H54 H55).
  assert (H57: is_fib 57 365435296162) by apply (fib_step 55 _ _ H55 H56).
  assert (H58: is_fib 58 591286729879) by apply (fib_step 56 _ _ H56 H57).
  assert (H59: is_fib 59 956722026041) by apply (fib_step 57 _ _ H57 H58).
  assert (H60: is_fib 60 1548008755920) by apply (fib_step 58 _ _ H58 H59).
  assert (H61: is_fib 61 2504730781961) by apply (fib_step 59 _ _ H59 H60).
  assert (H62: is_fib 62 4052739537881) by apply (fib_step 60 _ _ H60 H61).
  exact H62.
Qed.