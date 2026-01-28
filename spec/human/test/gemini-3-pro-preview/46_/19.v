Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

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

Example test_fib4_14 : problem_46_spec 14 1434.
Proof.
  unfold problem_46_spec.
  assert (H0: fib4_at 0 0) by apply fib4_at_0.
  assert (H1: fib4_at 1 0) by apply fib4_at_1.
  assert (H2: fib4_at 2 2) by apply fib4_at_2.
  assert (H3: fib4_at 3 0) by apply fib4_at_3.
  assert (H4: fib4_at 4 2) by (replace 2 with (0 + 0 + 2 + 0) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H5: fib4_at 5 4) by (replace 4 with (0 + 2 + 0 + 2) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H6: fib4_at 6 8) by (replace 8 with (2 + 0 + 2 + 4) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H7: fib4_at 7 14) by (replace 14 with (0 + 2 + 4 + 8) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H8: fib4_at 8 28) by (replace 28 with (2 + 4 + 8 + 14) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H9: fib4_at 9 54) by (replace 54 with (4 + 8 + 14 + 28) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H10: fib4_at 10 104) by (replace 104 with (8 + 14 + 28 + 54) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H11: fib4_at 11 200) by (replace 200 with (14 + 28 + 54 + 104) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H12: fib4_at 12 386) by (replace 386 with (28 + 54 + 104 + 200) by reflexivity; apply fib4_at_SSSS; assumption).
  assert (H13: fib4_at 13 744) by (replace 744 with (54 + 104 + 200 + 386) by reflexivity; apply fib4_at_SSSS; assumption).
  replace 1434 with (104 + 200 + 386 + 744) by reflexivity.
  apply fib4_at_SSSS; assumption.
Qed.