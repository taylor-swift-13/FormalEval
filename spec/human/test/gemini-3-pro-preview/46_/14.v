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
Example test_fib4_20 : problem_46_spec 20 73552.
Proof.
  unfold problem_46_spec.
  assert (H0: fib4_at 0 0) by apply fib4_at_0.
  assert (H1: fib4_at 1 0) by apply fib4_at_1.
  assert (H2: fib4_at 2 2) by apply fib4_at_2.
  assert (H3: fib4_at 3 0) by apply fib4_at_3.
  assert (H4 := fib4_at_SSSS 0 _ _ _ _ H0 H1 H2 H3). simpl in H4.
  assert (H5 := fib4_at_SSSS 1 _ _ _ _ H1 H2 H3 H4). simpl in H5.
  assert (H6 := fib4_at_SSSS 2 _ _ _ _ H2 H3 H4 H5). simpl in H6.
  assert (H7 := fib4_at_SSSS 3 _ _ _ _ H3 H4 H5 H6). simpl in H7.
  assert (H8 := fib4_at_SSSS 4 _ _ _ _ H4 H5 H6 H7). simpl in H8.
  assert (H9 := fib4_at_SSSS 5 _ _ _ _ H5 H6 H7 H8). simpl in H9.
  assert (H10 := fib4_at_SSSS 6 _ _ _ _ H6 H7 H8 H9). simpl in H10.
  assert (H11 := fib4_at_SSSS 7 _ _ _ _ H7 H8 H9 H10). simpl in H11.
  assert (H12 := fib4_at_SSSS 8 _ _ _ _ H8 H9 H10 H11). simpl in H12.
  assert (H13 := fib4_at_SSSS 9 _ _ _ _ H9 H10 H11 H12). simpl in H13.
  assert (H14 := fib4_at_SSSS 10 _ _ _ _ H10 H11 H12 H13). simpl in H14.
  assert (H15 := fib4_at_SSSS 11 _ _ _ _ H11 H12 H13 H14). simpl in H15.
  assert (H16 := fib4_at_SSSS 12 _ _ _ _ H12 H13 H14 H15). simpl in H16.
  assert (H17 := fib4_at_SSSS 13 _ _ _ _ H13 H14 H15 H16). simpl in H17.
  assert (H18 := fib4_at_SSSS 14 _ _ _ _ H14 H15 H16 H17). simpl in H18.
  assert (H19 := fib4_at_SSSS 15 _ _ _ _ H15 H16 H17 H18). simpl in H19.
  assert (H20 := fib4_at_SSSS 16 _ _ _ _ H16 H17 H18 H19). simpl in H20.
  exact H20.
Qed.