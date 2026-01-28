Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Inductive is_fib : Z -> Z -> Prop :=
  | fib_zero : is_fib 0%Z 0%Z
  | fib_one  : is_fib 1%Z 1%Z
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (n + 1)%Z res_n1 ->
               is_fib (n + 2)%Z (res_n1 + res_n)%Z.

Definition problem_55_pre (n : Z) : Prop := True.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  is_fib n res.

Example problem_55_test_36 : problem_55_pre 36%Z /\ problem_55_spec 36%Z 14930352%Z.
Proof.
  split; [exact I|].
  pose proof fib_zero as H0.
  pose proof fib_one as H1.
  pose proof (fib_step 0%Z 0%Z 1%Z H0 H1) as H2.
  pose proof (fib_step 1%Z 1%Z 1%Z H1 H2) as H3.
  pose proof (fib_step 2%Z 1%Z 2%Z H2 H3) as H4.
  pose proof (fib_step 3%Z 2%Z 3%Z H3 H4) as H5.
  pose proof (fib_step 4%Z 3%Z 5%Z H4 H5) as H6.
  pose proof (fib_step 5%Z 5%Z 8%Z H5 H6) as H7.
  pose proof (fib_step 6%Z 8%Z 13%Z H6 H7) as H8.
  pose proof (fib_step 7%Z 13%Z 21%Z H7 H8) as H9.
  pose proof (fib_step 8%Z 21%Z 34%Z H8 H9) as H10.
  pose proof (fib_step 9%Z 34%Z 55%Z H9 H10) as H11.
  pose proof (fib_step 10%Z 55%Z 89%Z H10 H11) as H12.
  pose proof (fib_step 11%Z 89%Z 144%Z H11 H12) as H13.
  pose proof (fib_step 12%Z 144%Z 233%Z H12 H13) as H14.
  pose proof (fib_step 13%Z 233%Z 377%Z H13 H14) as H15.
  pose proof (fib_step 14%Z 377%Z 610%Z H14 H15) as H16.
  pose proof (fib_step 15%Z 610%Z 987%Z H15 H16) as H17.
  pose proof (fib_step 16%Z 987%Z 1597%Z H16 H17) as H18.
  pose proof (fib_step 17%Z 1597%Z 2584%Z H17 H18) as H19.
  pose proof (fib_step 18%Z 2584%Z 4181%Z H18 H19) as H20.
  pose proof (fib_step 19%Z 4181%Z 6765%Z H19 H20) as H21.
  pose proof (fib_step 20%Z 6765%Z 10946%Z H20 H21) as H22.
  pose proof (fib_step 21%Z 10946%Z 17711%Z H21 H22) as H23.
  pose proof (fib_step 22%Z 17711%Z 28657%Z H22 H23) as H24.
  pose proof (fib_step 23%Z 28657%Z 46368%Z H23 H24) as H25.
  pose proof (fib_step 24%Z 46368%Z 75025%Z H24 H25) as H26.
  pose proof (fib_step 25%Z 75025%Z 121393%Z H25 H26) as H27.
  pose proof (fib_step 26%Z 121393%Z 196418%Z H26 H27) as H28.
  pose proof (fib_step 27%Z 196418%Z 317811%Z H27 H28) as H29.
  pose proof (fib_step 28%Z 317811%Z 514229%Z H28 H29) as H30.
  pose proof (fib_step 29%Z 514229%Z 832040%Z H29 H30) as H31.
  pose proof (fib_step 30%Z 832040%Z 1346269%Z H30 H31) as H32.
  pose proof (fib_step 31%Z 1346269%Z 2178309%Z H31 H32) as H33.
  pose proof (fib_step 32%Z 2178309%Z 3524578%Z H32 H33) as H34.
  pose proof (fib_step 33%Z 3524578%Z 5702887%Z H33 H34) as H35.
  pose proof (fib_step 34%Z 5702887%Z 9227465%Z H34 H35) as H36.
  exact H36.
Qed.