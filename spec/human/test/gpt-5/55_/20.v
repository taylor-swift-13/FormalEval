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

Example problem_55_test_70 : problem_55_pre 70%Z /\ problem_55_spec 70%Z 190392490709135%Z.
Proof.
  split; [exact I|].
  pose proof fib_zero as H0.
  pose proof fib_one as H1.
  pose proof (fib_step 0 0 1 H0 H1) as H2.
  pose proof (fib_step 1 1 1 H1 H2) as H3.
  pose proof (fib_step 2 1 2 H2 H3) as H4.
  pose proof (fib_step 3 2 3 H3 H4) as H5.
  pose proof (fib_step 4 3 5 H4 H5) as H6.
  pose proof (fib_step 5 5 8 H5 H6) as H7.
  pose proof (fib_step 6 8 13 H6 H7) as H8.
  pose proof (fib_step 7 13 21 H7 H8) as H9.
  pose proof (fib_step 8 21 34 H8 H9) as H10.
  pose proof (fib_step 9 34 55 H9 H10) as H11.
  pose proof (fib_step 10 55 89 H10 H11) as H12.
  pose proof (fib_step 11 89 144 H11 H12) as H13.
  pose proof (fib_step 12 144 233 H12 H13) as H14.
  pose proof (fib_step 13 233 377 H13 H14) as H15.
  pose proof (fib_step 14 377 610 H14 H15) as H16.
  pose proof (fib_step 15 610 987 H15 H16) as H17.
  pose proof (fib_step 16 987 1597 H16 H17) as H18.
  pose proof (fib_step 17 1597 2584 H17 H18) as H19.
  pose proof (fib_step 18 2584 4181 H18 H19) as H20.
  pose proof (fib_step 19 4181 6765 H19 H20) as H21.
  pose proof (fib_step 20 6765 10946 H20 H21) as H22.
  pose proof (fib_step 21 10946 17711 H21 H22) as H23.
  pose proof (fib_step 22 17711 28657 H22 H23) as H24.
  pose proof (fib_step 23 28657 46368 H23 H24) as H25.
  pose proof (fib_step 24 46368 75025 H24 H25) as H26.
  pose proof (fib_step 25 75025 121393 H25 H26) as H27.
  pose proof (fib_step 26 121393 196418 H26 H27) as H28.
  pose proof (fib_step 27 196418 317811 H27 H28) as H29.
  pose proof (fib_step 28 317811 514229 H28 H29) as H30.
  pose proof (fib_step 29 514229 832040 H29 H30) as H31.
  pose proof (fib_step 30 832040 1346269 H30 H31) as H32.
  pose proof (fib_step 31 1346269 2178309 H31 H32) as H33.
  pose proof (fib_step 32 2178309 3524578 H32 H33) as H34.
  pose proof (fib_step 33 3524578 5702887 H33 H34) as H35.
  pose proof (fib_step 34 5702887 9227465 H34 H35) as H36.
  pose proof (fib_step 35 9227465 14930352 H35 H36) as H37.
  pose proof (fib_step 36 14930352 24157817 H36 H37) as H38.
  pose proof (fib_step 37 24157817 39088169 H37 H38) as H39.
  pose proof (fib_step 38 39088169 63245986 H38 H39) as H40.
  pose proof (fib_step 39 63245986 102334155 H39 H40) as H41.
  pose proof (fib_step 40 102334155 165580141 H40 H41) as H42.
  pose proof (fib_step 41 165580141 267914296 H41 H42) as H43.
  pose proof (fib_step 42 267914296 433494437 H42 H43) as H44.
  pose proof (fib_step 43 433494437 701408733 H43 H44) as H45.
  pose proof (fib_step 44 701408733 1134903170 H44 H45) as H46.
  pose proof (fib_step 45 1134903170 1836311903 H45 H46) as H47.
  pose proof (fib_step 46 1836311903 2971215073 H46 H47) as H48.
  pose proof (fib_step 47 2971215073 4807526976 H47 H48) as H49.
  pose proof (fib_step 48 4807526976 7778742049 H48 H49) as H50.
  pose proof (fib_step 49 7778742049 12586269025 H49 H50) as H51.
  pose proof (fib_step 50 12586269025 20365011074 H50 H51) as H52.
  pose proof (fib_step 51 20365011074 32951280099 H51 H52) as H53.
  pose proof (fib_step 52 32951280099 53316291173 H52 H53) as H54.
  pose proof (fib_step 53 53316291173 86267571272 H53 H54) as H55.
  pose proof (fib_step 54 86267571272 139583862445 H54 H55) as H56.
  pose proof (fib_step 55 139583862445 225851433717 H55 H56) as H57.
  pose proof (fib_step 56 225851433717 365435296162 H56 H57) as H58.
  pose proof (fib_step 57 365435296162 591286729879 H57 H58) as H59.
  pose proof (fib_step 58 591286729879 956722026041 H58 H59) as H60.
  pose proof (fib_step 59 956722026041 1548008755920 H59 H60) as H61.
  pose proof (fib_step 60 1548008755920 2504730781961 H60 H61) as H62.
  pose proof (fib_step 61 2504730781961 4052739537881 H61 H62) as H63.
  pose proof (fib_step 62 4052739537881 6557470319842 H62 H63) as H64.
  pose proof (fib_step 63 6557470319842 10610209857723 H63 H64) as H65.
  pose proof (fib_step 64 10610209857723 17167680177565 H64 H65) as H66.
  pose proof (fib_step 65 17167680177565 27777890035288 H65 H66) as H67.
  pose proof (fib_step 66 27777890035288 44945570212853 H66 H67) as H68.
  pose proof (fib_step 67 44945570212853 72723460248141 H67 H68) as H69.
  pose proof (fib_step 68 72723460248141 117669030460994 H68 H69) as H70.
  exact H70.
Qed.