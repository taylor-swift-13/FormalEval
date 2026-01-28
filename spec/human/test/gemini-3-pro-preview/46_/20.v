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
Example test_fib4_18 : problem_46_spec 18 19796.
Proof.
  unfold problem_46_spec.
  
  assert (H0: fib4_at 0 0) by apply fib4_at_0.
  assert (H1: fib4_at 1 0) by apply fib4_at_1.
  assert (H2: fib4_at 2 2) by apply fib4_at_2.
  assert (H3: fib4_at 3 0) by apply fib4_at_3.

  assert (H4: fib4_at 4 2).
  { replace 2 with (0 + 0 + 2 + 0) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H5: fib4_at 5 4).
  { replace 4 with (0 + 2 + 0 + 2) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H6: fib4_at 6 8).
  { replace 8 with (2 + 0 + 2 + 4) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H7: fib4_at 7 14).
  { replace 14 with (0 + 2 + 4 + 8) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H8: fib4_at 8 28).
  { replace 28 with (2 + 4 + 8 + 14) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H9: fib4_at 9 54).
  { replace 54 with (4 + 8 + 14 + 28) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H10: fib4_at 10 104).
  { replace 104 with (8 + 14 + 28 + 54) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H11: fib4_at 11 200).
  { replace 200 with (14 + 28 + 54 + 104) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H12: fib4_at 12 386).
  { replace 386 with (28 + 54 + 104 + 200) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H13: fib4_at 13 744).
  { replace 744 with (54 + 104 + 200 + 386) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H14: fib4_at 14 1434).
  { replace 1434 with (104 + 200 + 386 + 744) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H15: fib4_at 15 2764).
  { replace 2764 with (200 + 386 + 744 + 1434) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H16: fib4_at 16 5328).
  { replace 5328 with (386 + 744 + 1434 + 2764) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H17: fib4_at 17 10270).
  { replace 10270 with (744 + 1434 + 2764 + 5328) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  assert (H18: fib4_at 18 19796).
  { replace 19796 with (1434 + 2764 + 5328 + 10270) by reflexivity.
    apply fib4_at_SSSS; assumption. }

  exact H18.
Qed.