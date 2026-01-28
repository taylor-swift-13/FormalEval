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

Example problem_46_test : problem_46_spec 7 14.
Proof.
  unfold problem_46_spec.
  assert (H4: fib4_at 4 2).
  {
    replace 2 with (0 + 0 + 2 + 0) by reflexivity.
    apply (fib4_at_SSSS 0 0 0 2 0).
    - apply fib4_at_0.
    - apply fib4_at_1.
    - apply fib4_at_2.
    - apply fib4_at_3.
  }
  assert (H5: fib4_at 5 4).
  {
    replace 4 with (0 + 2 + 0 + 2) by reflexivity.
    apply (fib4_at_SSSS 1 0 2 0 2).
    - apply fib4_at_1.
    - apply fib4_at_2.
    - apply fib4_at_3.
    - exact H4.
  }
  assert (H6: fib4_at 6 8).
  {
    replace 8 with (2 + 0 + 2 + 4) by reflexivity.
    apply (fib4_at_SSSS 2 2 0 2 4).
    - apply fib4_at_2.
    - apply fib4_at_3.
    - exact H4.
    - exact H5.
  }
  replace 14 with (0 + 2 + 4 + 8) by reflexivity.
  apply (fib4_at_SSSS 3 0 2 4 8).
  - apply fib4_at_3.
  - exact H4.
  - exact H5.
  - exact H6.
Qed.