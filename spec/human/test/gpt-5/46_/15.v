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

Example problem_46_test : problem_46_spec 19 38158.
Proof.
  unfold problem_46_spec.
  assert (H4 : fib4_at 4 2).
  { eapply fib4_at_SSSS with (i:=0) (a:=0) (b:=0) (c:=2) (d:=0).
    - exact fib4_at_0.
    - exact fib4_at_1.
    - exact fib4_at_2.
    - exact fib4_at_3. }
  assert (H5 : fib4_at 5 4).
  { eapply fib4_at_SSSS with (i:=1) (a:=0) (b:=2) (c:=0) (d:=2).
    - exact fib4_at_1.
    - exact fib4_at_2.
    - exact fib4_at_3.
    - exact H4. }
  assert (H6 : fib4_at 6 8).
  { eapply fib4_at_SSSS with (i:=2) (a:=2) (b:=0) (c:=2) (d:=4).
    - exact fib4_at_2.
    - exact fib4_at_3.
    - exact H4.
    - exact H5. }
  assert (H7 : fib4_at 7 14).
  { eapply fib4_at_SSSS with (i:=3) (a:=0) (b:=2) (c:=4) (d:=8).
    - exact fib4_at_3.
    - exact H4.
    - exact H5.
    - exact H6. }
  assert (H8 : fib4_at 8 28).
  { eapply fib4_at_SSSS with (i:=4) (a:=2) (b:=4) (c:=8) (d:=14).
    - exact H4.
    - exact H5.
    - exact H6.
    - exact H7. }
  assert (H9 : fib4_at 9 54).
  { eapply fib4_at_SSSS with (i:=5) (a:=4) (b:=8) (c:=14) (d:=28).
    - exact H5.
    - exact H6.
    - exact H7.
    - exact H8. }
  assert (H10 : fib4_at 10 104).
  { eapply fib4_at_SSSS with (i:=6) (a:=8) (b:=14) (c:=28) (d:=54).
    - exact H6.
    - exact H7.
    - exact H8.
    - exact H9. }
  assert (H11 : fib4_at 11 200).
  { eapply fib4_at_SSSS with (i:=7) (a:=14) (b:=28) (c:=54) (d:=104).
    - exact H7.
    - exact H8.
    - exact H9.
    - exact H10. }
  assert (H12 : fib4_at 12 386).
  { eapply fib4_at_SSSS with (i:=8) (a:=28) (b:=54) (c:=104) (d:=200).
    - exact H8.
    - exact H9.
    - exact H10.
    - exact H11. }
  assert (H13 : fib4_at 13 744).
  { eapply fib4_at_SSSS with (i:=9) (a:=54) (b:=104) (c:=200) (d:=386).
    - exact H9.
    - exact H10.
    - exact H11.
    - exact H12. }
  assert (H14 : fib4_at 14 1434).
  { eapply fib4_at_SSSS with (i:=10) (a:=104) (b:=200) (c:=386) (d:=744).
    - exact H10.
    - exact H11.
    - exact H12.
    - exact H13. }
  assert (H15 : fib4_at 15 2764).
  { eapply fib4_at_SSSS with (i:=11) (a:=200) (b:=386) (c:=744) (d:=1434).
    - exact H11.
    - exact H12.
    - exact H13.
    - exact H14. }
  assert (H16 : fib4_at 16 5328).
  { eapply fib4_at_SSSS with (i:=12) (a:=386) (b:=744) (c:=1434) (d:=2764).
    - exact H12.
    - exact H13.
    - exact H14.
    - exact H15. }
  assert (H17 : fib4_at 17 10270).
  { eapply fib4_at_SSSS with (i:=13) (a:=744) (b:=1434) (c:=2764) (d:=5328).
    - exact H13.
    - exact H14.
    - exact H15.
    - exact H16. }
  assert (H18 : fib4_at 18 19796).
  { eapply fib4_at_SSSS with (i:=14) (a:=1434) (b:=2764) (c:=5328) (d:=10270).
    - exact H14.
    - exact H15.
    - exact H16.
    - exact H17. }
  eapply fib4_at_SSSS with (i:=15) (a:=2764) (b:=5328) (c:=10270) (d:=19796).
  - exact H15.
  - exact H16.
  - exact H17.
  - exact H18.
Qed.