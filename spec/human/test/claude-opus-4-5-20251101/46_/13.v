Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

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

Example problem_46_test : problem_46_spec 15 2764.
Proof.
  unfold problem_46_spec.
  assert (H4: fib4_at 4 2).
  { replace 2 with (0 + 0 + 2 + 0) by reflexivity.
    apply (fib4_at_SSSS 0 0 0 2 0); [apply fib4_at_0 | apply fib4_at_1 | apply fib4_at_2 | apply fib4_at_3]. }
  assert (H5: fib4_at 5 4).
  { replace 4 with (0 + 2 + 0 + 2) by reflexivity.
    apply (fib4_at_SSSS 1 0 2 0 2); [apply fib4_at_1 | apply fib4_at_2 | apply fib4_at_3 | exact H4]. }
  assert (H6: fib4_at 6 8).
  { replace 8 with (2 + 0 + 2 + 4) by reflexivity.
    apply (fib4_at_SSSS 2 2 0 2 4); [apply fib4_at_2 | apply fib4_at_3 | exact H4 | exact H5]. }
  assert (H7: fib4_at 7 14).
  { replace 14 with (0 + 2 + 4 + 8) by reflexivity.
    apply (fib4_at_SSSS 3 0 2 4 8); [apply fib4_at_3 | exact H4 | exact H5 | exact H6]. }
  assert (H8: fib4_at 8 28).
  { replace 28 with (2 + 4 + 8 + 14) by reflexivity.
    apply (fib4_at_SSSS 4 2 4 8 14); [exact H4 | exact H5 | exact H6 | exact H7]. }
  assert (H9: fib4_at 9 54).
  { replace 54 with (4 + 8 + 14 + 28) by reflexivity.
    apply (fib4_at_SSSS 5 4 8 14 28); [exact H5 | exact H6 | exact H7 | exact H8]. }
  assert (H10: fib4_at 10 104).
  { replace 104 with (8 + 14 + 28 + 54) by reflexivity.
    apply (fib4_at_SSSS 6 8 14 28 54); [exact H6 | exact H7 | exact H8 | exact H9]. }
  assert (H11: fib4_at 11 200).
  { replace 200 with (14 + 28 + 54 + 104) by reflexivity.
    apply (fib4_at_SSSS 7 14 28 54 104); [exact H7 | exact H8 | exact H9 | exact H10]. }
  assert (H12: fib4_at 12 386).
  { replace 386 with (28 + 54 + 104 + 200) by reflexivity.
    apply (fib4_at_SSSS 8 28 54 104 200); [exact H8 | exact H9 | exact H10 | exact H11]. }
  assert (H13: fib4_at 13 744).
  { replace 744 with (54 + 104 + 200 + 386) by reflexivity.
    apply (fib4_at_SSSS 9 54 104 200 386); [exact H9 | exact H10 | exact H11 | exact H12]. }
  assert (H14: fib4_at 14 1434).
  { replace 1434 with (104 + 200 + 386 + 744) by reflexivity.
    apply (fib4_at_SSSS 10 104 200 386 744); [exact H10 | exact H11 | exact H12 | exact H13]. }
  replace 2764 with (200 + 386 + 744 + 1434) by reflexivity.
  apply (fib4_at_SSSS 11 200 386 744 1434); [exact H11 | exact H12 | exact H13 | exact H14].
Qed.