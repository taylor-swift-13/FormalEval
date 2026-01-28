Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Inductive relation definition for fib4 sequence *)
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

(* Pre-condition *)
Definition problem_46_pre (input : nat) : Prop := True.

(* Post-condition specification *)
Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

(* Test case proof *)
Example test_fib4_17 : problem_46_spec 17 10270.
Proof.
  unfold problem_46_spec.
  assert (H0: fib4_at 0 0) by apply fib4_at_0.
  assert (H1: fib4_at 1 0) by apply fib4_at_1.
  assert (H2: fib4_at 2 2) by apply fib4_at_2.
  assert (H3: fib4_at 3 0) by apply fib4_at_3.
  assert (H4: fib4_at 4 2) by (apply (fib4_at_SSSS 0 _ _ _ _ H0 H1 H2 H3)).
  assert (H5: fib4_at 5 4) by (apply (fib4_at_SSSS 1 _ _ _ _ H1 H2 H3 H4)).
  assert (H6: fib4_at 6 8) by (apply (fib4_at_SSSS 2 _ _ _ _ H2 H3 H4 H5)).
  assert (H7: fib4_at 7 14) by (apply (fib4_at_SSSS 3 _ _ _ _ H3 H4 H5 H6)).
  assert (H8: fib4_at 8 28) by (apply (fib4_at_SSSS 4 _ _ _ _ H4 H5 H6 H7)).
  assert (H9: fib4_at 9 54) by (apply (fib4_at_SSSS 5 _ _ _ _ H5 H6 H7 H8)).
  assert (H10: fib4_at 10 104) by (apply (fib4_at_SSSS 6 _ _ _ _ H6 H7 H8 H9)).
  assert (H11: fib4_at 11 200) by (apply (fib4_at_SSSS 7 _ _ _ _ H7 H8 H9 H10)).
  assert (H12: fib4_at 12 386) by (apply (fib4_at_SSSS 8 _ _ _ _ H8 H9 H10 H11)).
  assert (H13: fib4_at 13 744) by (apply (fib4_at_SSSS 9 _ _ _ _ H9 H10 H11 H12)).
  assert (H14: fib4_at 14 1434) by (apply (fib4_at_SSSS 10 _ _ _ _ H10 H11 H12 H13)).
  assert (H15: fib4_at 15 2764) by (apply (fib4_at_SSSS 11 _ _ _ _ H11 H12 H13 H14)).
  assert (H16: fib4_at 16 5328) by (apply (fib4_at_SSSS 12 _ _ _ _ H12 H13 H14 H15)).
  apply (fib4_at_SSSS 13 _ _ _ _ H13 H14 H15 H16).
Qed.