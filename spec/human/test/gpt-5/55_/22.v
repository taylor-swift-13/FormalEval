Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Inductive is_fib : nat -> Z -> Prop :=
  | fib_zero : is_fib 0 0%Z
  | fib_one  : is_fib 1 1%Z
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n)%Z.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  is_fib n res.

Example problem_55_test_62 : problem_55_pre 62 /\ problem_55_spec 62 4052739537881%Z.
Proof.
  split; [exact I|].
  pose proof fib_zero as H0.
  pose proof fib_one as H1.
  pose proof (fib_step 0 0%Z 1%Z H0 H1) as H2.
  pose proof (fib_step 1 1%Z 1%Z H1 H2) as H3.
  pose proof (fib_step 2 1%Z 2%Z H2 H3) as H4.
  pose proof (fib_step 3 2%Z 3%Z H3 H4) as H5.
  pose proof (fib_step 4 3%Z 5%Z H4 H5) as H6.
  pose proof (fib_step 5 5%Z 8%Z H5 H6) as H7.
  pose proof (fib_step 6 8%Z 13%Z H6 H7) as H8.
  pose proof (fib_step 7 13%Z 21%Z H7 H8) as H9.
  pose proof (fib_step 8 21%Z 34%Z H8 H9) as H10.
  pose proof (fib_step 9 34%Z 55%Z H9 H10) as H11.
  pose proof (fib_step 10 55%Z 89%Z H10 H11) as H12.
  pose proof (fib_step 11 89%Z 144%Z H11 H12) as H13.
  pose proof (fib_step 12 144%Z 233%Z H12 H13) as H14.
  pose proof (fib_step 13 233%Z 377%Z H13 H14) as H15.
  pose proof (fib_step 14 377%Z 610%Z H14 H15) as H16.
  pose proof (fib_step 15 610%Z 987%Z H15 H16) as H17.
  pose proof (fib_step 16 987%Z 1597%Z H16 H17) as H18.
  pose proof (fib_step 17 1597%Z 2584%Z H17 H18) as H19.
  pose proof (fib_step 18 2584%Z 4181%Z H18 H19) as H20.
  pose proof (fib_step 19 4181%Z 6765%Z H19 H20) as H21.
  pose proof (fib_step 20 6765%Z 10946%Z H20 H21) as H22.
  pose proof (fib_step 21 10946%Z 17711%Z H21 H22) as H23.
  pose proof (fib_step 22 17711%Z 28657%Z H22 H23) as H24.
  pose proof (fib_step 23 28657%Z 46368%Z H23 H24) as H25.
  pose proof (fib_step 24 46368%Z 75025%Z H24 H25) as H26.
  pose proof (fib_step 25 75025%Z 121393%Z H25 H26) as H27.
  pose proof (fib_step 26 121393%Z 196418%Z H26 H27) as H28.
  pose proof (fib_step 27 196418%Z 317811%Z H27 H28) as H29.
  pose proof (fib_step 28 317811%Z 514229%Z H28 H29) as H30.
  pose proof (fib_step 29 514229%Z 832040%Z H29 H30) as H31.
  pose proof (fib_step 30 832040%Z 1346269%Z H30 H31) as H32.
  pose proof (fib_step 31 1346269%Z 2178309%Z H31 H32) as H33.
  pose proof (fib_step 32 2178309%Z 3524578%Z H32 H33) as H34.
  pose proof (fib_step 33 3524578%Z 5702887%Z H33 H34) as H35.
  pose proof (fib_step 34 5702887%Z 9227465%Z H34 H35) as H36.
  pose proof (fib_step 35 9227465%Z 14930352%Z H35 H36) as H37.
  pose proof (fib_step 36 14930352%Z 24157817%Z H36 H37) as H38.
  pose proof (fib_step 37 24157817%Z 39088169%Z H37 H38) as H39.
  pose proof (fib_step 38 39088169%Z 63245986%Z H38 H39) as H40.
  pose proof (fib_step 39 63245986%Z 102334155%Z H39 H40) as H41.
  pose proof (fib_step 40 102334155%Z 165580141%Z H40 H41) as H42.
  pose proof (fib_step 41 165580141%Z 267914296%Z H41 H42) as H43.
  pose proof (fib_step 42 267914296%Z 433494437%Z H42 H43) as H44.
  pose proof (fib_step 43 433494437%Z 701408733%Z H43 H44) as H45.
  pose proof (fib_step 44 701408733%Z 1134903170%Z H44 H45) as H46.
  pose proof (fib_step 45 1134903170%Z 1836311903%Z H45 H46) as H47.
  pose proof (fib_step 46 1836311903%Z 2971215073%Z H46 H47) as H48.
  pose proof (fib_step 47 2971215073%Z 4807526976%Z H47 H48) as H49.
  pose proof (fib_step 48 4807526976%Z 7778742049%Z H48 H49) as H50.
  pose proof (fib_step 49 7778742049%Z 12586269025%Z H49 H50) as H51.
  pose proof (fib_step 50 12586269025%Z 20365011074%Z H50 H51) as H52.
  pose proof (fib_step 51 20365011074%Z 32951280099%Z H51 H52) as H53.
  pose proof (fib_step 52 32951280099%Z 53316291173%Z H52 H53) as H54.
  pose proof (fib_step 53 53316291173%Z 86267571272%Z H53 H54) as H55.
  pose proof (fib_step 54 86267571272%Z 139583862445%Z H54 H55) as H56.
  pose proof (fib_step 55 139583862445%Z 225851433717%Z H55 H56) as H57.
  pose proof (fib_step 56 225851433717%Z 365435296162%Z H56 H57) as H58.
  pose proof (fib_step 57 365435296162%Z 591286729879%Z H57 H58) as H59.
  pose proof (fib_step 58 591286729879%Z 956722026041%Z H58 H59) as H60.
  pose proof (fib_step 59 956722026041%Z 1548008755920%Z H59 H60) as H61.
  pose proof (fib_step 60 1548008755920%Z 2504730781961%Z H60 H61) as H62.
  exact H62.
Qed.