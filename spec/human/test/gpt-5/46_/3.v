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

Example problem_46_test : problem_46_spec 10 104.
Proof.
  unfold problem_46_spec.
  assert (H4: fib4_at 4 2).
  { eapply fib4_at_SSSS with (i:=0) (a:=0) (b:=0) (c:=2) (d:=0).
    - exact fib4_at_0.
    - exact fib4_at_1.
    - exact fib4_at_2.
    - exact fib4_at_3.
  }
  assert (H5: fib4_at 5 4).
  { eapply fib4_at_SSSS with (i:=1) (a:=0) (b:=2) (c:=0) (d:=2).
    - exact fib4_at_1.
    - exact fib4_at_2.
    - exact fib4_at_3.
    - exact H4.
  }
  assert (H6: fib4_at 6 8).
  { eapply fib4_at_SSSS with (i:=2) (a:=2) (b:=0) (c:=2) (d:=4).
    - exact fib4_at_2.
    - exact fib4_at_3.
    - exact H4.
    - exact H5.
  }
  assert (H7: fib4_at 7 14).
  { eapply fib4_at_SSSS with (i:=3) (a:=0) (b:=2) (c:=4) (d:=8).
    - exact fib4_at_3.
    - exact H4.
    - exact H5.
    - exact H6.
  }
  assert (H8: fib4_at 8 28).
  { eapply fib4_at_SSSS with (i:=4) (a:=2) (b:=4) (c:=8) (d:=14).
    - exact H4.
    - exact H5.
    - exact H6.
    - exact H7.
  }
  assert (H9: fib4_at 9 54).
  { eapply fib4_at_SSSS with (i:=5) (a:=4) (b:=8) (c:=14) (d:=28).
    - exact H5.
    - exact H6.
    - exact H7.
    - exact H8.
  }
  eapply fib4_at_SSSS with (i:=6) (a:=8) (b:=14) (c:=28) (d:=54).
  - exact H6.
  - exact H7.
  - exact H8.
  - exact H9.
Qed.