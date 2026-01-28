Require Import Coq.Arith.Arith.

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

Definition problem_46_pre (input : nat) : Prop := True.

Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

Example problem_46_test : problem_46_spec 11 200.
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
  exact H11.
Qed.