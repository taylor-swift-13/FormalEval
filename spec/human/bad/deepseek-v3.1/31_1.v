Require Import Arith.
Require Import ZArith.
Require Import Bool.
Require Import Omega.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_6 : problem_31_spec 6 false.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  * intro H.
    destruct H as [H1 H2].
    exfalso.
    assert (H3 : 6 mod 2 = 0).
    { simpl. reflexivity. }
    apply H2 in H3.
    destruct H3 as [H3|H4].
    + omega.
    + omega.
  * intro H.
    discriminate H.
Qed.