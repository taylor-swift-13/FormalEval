Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Inductive is_fib : Z -> Z -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (n + 1) res_n1 ->
               is_fib (n + 2) (res_n1 + res_n).

Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  is_fib n res.

Example test_fib_67 : problem_55_spec 67 44945570212853.
Proof.
  unfold problem_55_spec.
  assert (H0: is_fib 0 0) by apply fib_zero.
  assert (H1: is_fib 1 1) by apply fib_one.
  assert (H2: is_fib 2 1) by (apply (fib_step 0 0 1 H0 H1)).
  assert (H3: is_fib 3 2) by (apply (fib_step 1 1 1 H1 H2)).
  assert (H4: is_fib 4 3) by (apply (fib_step 2 1 2 H2 H3)).
  assert (H5: is_fib 5 5) by (apply (fib_step 3 2 3 H3 H4)).
  assert (H6: is_fib 6 8) by (apply (fib_step 4 3 5 H4 H5)).
  assert (H7: is_fib 7 13) by (apply (fib_step 5 5 8 H5 H6)).
  assert (H8: is_fib 8 21) by (apply (fib_step 6 8 13 H6 H7)).
  assert (H9: is_fib 9 34) by (apply (fib_step 7 13 21 H7 H8)).
  assert (H10: is_fib 10 55) by (apply (fib_step 8 21 34 H8 H9)).
  assert (H11: is_fib 11 89) by (apply (fib_step 9 34 55 H9 H10)).
  assert (H12: is_fib 12 144) by (apply (fib_step 10 55 89 H10 H11)).
  assert (H13: is_fib 13 233) by (apply (fib_step 11 89 144 H11 H12)).
  assert (H14: is_fib 14 377) by (apply (fib_step 12 144 233 H12 H13)).
  assert (H15: is_fib 15 610) by (apply (fib_step 13 233 377 H13 H14)).
  assert (H16: is_fib 16 987) by (apply (fib_step 14 377 610 H14 H15)).
  assert (H17: is_fib 17 1597) by (apply (fib_step 15 610 987 H15 H16)).
  assert (H18: is_fib 18 2584) by (apply (fib_step 16 987 1597 H16 H17)).
  assert (H19: is_fib 19 4181) by (apply (fib_step 17 1597 2584 H17 H18)).
  assert (H20: is_fib 20 6765) by (apply (fib_step 18 2584 4181 H18 H19)).
  assert (H21: is_fib 21 10946) by (apply (fib_step 19 4181 6765 H19 H20)).
  assert (H22: is_fib 22 17711) by (apply (fib_step 20 6765 10946 H20 H21)).
  assert (H23: is_fib 23 28657) by (apply (fib_step 21 10946 17711 H21 H22)).
  assert (H24: is_fib 24 46368) by (apply (fib_step 22 17711 28657 H22 H23)).
  assert (H25: is_fib 25 75025) by (apply (fib_step 23 28657 46368 H23 H24)).
  assert (H26: is_fib 26 121393) by (apply (fib_step 24 46368 75025 H24 H25)).
  assert (H27: is_fib 27 196418) by (apply (fib_step 25 75025 121393 H25 H26)).
  assert (H28: is_fib 28 317811) by (apply (fib_step 26 121393 196418 H26 H27)).
  assert (H29: is_fib 29 514229) by (apply (fib_step 27 196418 317811 H27 H28)).
  assert (H30: is_fib 30 832040) by (apply (fib_step 28 317811 514229 H28 H29)).
  assert (H31: is_fib 31 1346269) by (apply (fib_step 29 514229 832040 H29 H30)).
  assert (H32: is_fib 32 2178309) by (apply (fib_step 30 832040 1346269 H30 H31)).
  assert (H33: is_fib 33 3524578) by (apply (fib_step 31 1346269 2178309 H31 H32)).
  assert (H34: is_fib 34 5702887) by (apply (fib_step 32 2178309 3524578 H32 H33)).
  assert (H35: is_fib 35 9227465) by (apply (fib_step 33 3524578 5702887 H33 H34)).
  assert (H36: is_fib 36 14930352) by (apply (fib_step 34 5702887 9227465 H34 H35)).
  assert (H37: is_fib 37 24157817) by (apply (fib_step 35 9227465 14930352 H35 H36)).
  assert (H38: is_fib 38 39088169) by (apply (fib_step 36 14930352 24157817 H36 H37)).
  assert (H39: is_fib 39 63245986) by (apply (fib_step 37 24157817 39088169 H37 H38)).
  assert (H40: is_fib 40 102334155) by (apply (fib_step 38 39088169 63245986 H38 H39)).
  assert (H41: is_fib 41 165580141) by (apply (fib_step 39 63245986 102334155 H39 H40)).
  assert (H42: is_fib 42 267914296) by (apply (fib_step 40 102334155 165580141 H40 H41)).
  assert (H43: is_fib 43 433494437) by (apply (fib_step 41 165580141 267914296 H41 H42)).
  assert (H44: is_fib 44 701408733) by (apply (fib_step 42 267914296 433494437 H42 H43)).
  assert (H45: is_fib 45 1134903170) by (apply (fib_step 43 433494437 701408733 H43 H44)).
  assert (H46: is_fib 46 1836311903) by (apply (fib_step 44 701408733 1134903170 H44 H45)).
  assert (H47: is_fib 47 2971215073) by (apply (fib_step 45 1134903170 1836311903 H45 H46)).
  assert (H48: is_fib 48 4807526976) by (apply (fib_step 46 1836311903 2971215073 H46 H47)).
  assert (H49: is_fib 49 7778742049) by (apply (fib_step 47 2971215073 4807526976 H47 H48)).
  assert (H50: is_fib 50 12586269025) by (apply (fib_step 48 4807526976 7778742049 H48 H49)).
  assert (H51: is_fib 51 20365011074) by (apply (fib_step 49 7778742049 12586269025 H49 H50)).
  assert (H52: is_fib 52 32951280099) by (apply (fib_step 50 12586269025 20365011074 H50 H51)).
  assert (H53: is_fib 53 53316291173) by (apply (fib_step 51 20365011074 32951280099 H51 H52)).
  assert (H54: is_fib 54 86267571272) by (apply (fib_step 52 32951280099 53316291173 H52 H53)).
  assert (H55: is_fib 55 139583862445) by (apply (fib_step 53 53316291173 86267571272 H53 H54)).
  assert (H56: is_fib 56 225851433717) by (apply (fib_step 54 86267571272 139583862445 H54 H55)).
  assert (H57: is_fib 57 365435296162) by (apply (fib_step 55 139583862445 225851433717 H55 H56)).
  assert (H58: is_fib 58 591286729879) by (apply (fib_step 56 225851433717 365435296162 H56 H57)).
  assert (H59: is_fib 59 956722026041) by (apply (fib_step 57 365435296162 591286729879 H57 H58)).
  assert (H60: is_fib 60 1548008755920) by (apply (fib_step 58 591286729879 956722026041 H58 H59)).
  assert (H61: is_fib 61 2504730781961) by (apply (fib_step 59 956722026041 1548008755920 H59 H60)).
  assert (H62: is_fib 62 4052739537881) by (apply (fib_step 60 1548008755920 2504730781961 H60 H61)).
  assert (H63: is_fib 63 6557470319842) by (apply (fib_step 61 2504730781961 4052739537881 H61 H62)).
  assert (H64: is_fib 64 10610209857723) by (apply (fib_step 62 4052739537881 6557470319842 H62 H63)).
  assert (H65: is_fib 65 17167680177565) by (apply (fib_step 63 6557470319842 10610209857723 H63 H64)).
  assert (H66: is_fib 66 27777890035288) by (apply (fib_step 64 10610209857723 17167680177565 H64 H65)).
  
  apply (fib_step 65 17167680177565 27777890035288 H65 H66).
Qed.