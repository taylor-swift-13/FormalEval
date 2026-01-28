Require Import Coq.Arith.Arith.

(* 使用归纳关系表示 fib4 序列*)
Inductive fib4_at : nat -> nat -> Prop :=
| fib4_at_0 : fib4_at 0 0
| fib4_at_1 : fib4_at 1 0
| fib4_at_2 : fib4_at 2 2
| fib4_at_3 : fib4_at 3 0
| fib4_at_SSSS : forall i a b c d,
    fib4_at i a ->
    fib4_at (S i) b ->
    fib4_at (S (S i)) c ->
    fib4_at (S (S (S i))) d ->
    fib4_at (S (S (S (S i)))) (a + b + c + d).

(* Pre: no additional constraints for `fib4` *)
Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

Example problem_46_test : problem_46_spec 23 526768.
Proof.
  unfold problem_46_spec.
  pose proof fib4_at_0 as H0.
  pose proof fib4_at_1 as H1.
  pose proof fib4_at_2 as H2.
  pose proof fib4_at_3 as H3.
  pose proof (fib4_at_SSSS 0 0 0 2 0 H0 H1 H2 H3) as H4.
  pose proof (fib4_at_SSSS 1 0 2 0 2 H1 H2 H3 H4) as H5.
  pose proof (fib4_at_SSSS 2 2 0 2 4 H2 H3 H4 H5) as H6.
  pose proof (fib4_at_SSSS 3 0 2 4 8 H3 H4 H5 H6) as H7.
  pose proof (fib4_at_SSSS 4 2 4 8 14 H4 H5 H6 H7) as H8.
  pose proof (fib4_at_SSSS 5 4 8 14 28 H5 H6 H7 H8) as H9.
  pose proof (fib4_at_SSSS 6 8 14 28 54 H6 H7 H8 H9) as H10.
  pose proof (fib4_at_SSSS 7 14 28 54 104 H7 H8 H9 H10) as H11.
  pose proof (fib4_at_SSSS 8 28 54 104 200 H8 H9 H10 H11) as H12.
  pose proof (fib4_at_SSSS 9 54 104 200 386 H9 H10 H11 H12) as H13.
  pose proof (fib4_at_SSSS 10 104 200 386 744 H10 H11 H12 H13) as H14.
  pose proof (fib4_at_SSSS 11 200 386 744 1434 H11 H12 H13 H14) as H15.
  pose proof (fib4_at_SSSS 12 386 744 1434 2764 H12 H13 H14 H15) as H16.
  pose proof (fib4_at_SSSS 13 744 1434 2764 5328 H13 H14 H15 H16) as H17.
  pose proof (fib4_at_SSSS 14 1434 2764 5328 10270 H14 H15 H16 H17) as H18.
  pose proof (fib4_at_SSSS 15 2764 5328 10270 19796 H15 H16 H17 H18) as H19.
  pose proof (fib4_at_SSSS 16 5328 10270 19796 38158 H16 H17 H18 H19) as H20.
  pose proof (fib4_at_SSSS 17 10270 19796 38158 73552 H17 H18 H19 H20) as H21.
  pose proof (fib4_at_SSSS 18 19796 38158 73552 141776 H18 H19 H20 H21) as H22.
  pose proof (fib4_at_SSSS 19 38158 73552 141776 273282 H19 H20 H21 H22) as H23.
  exact H23.
Qed.