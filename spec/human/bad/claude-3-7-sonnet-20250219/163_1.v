Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Even.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.SetoidList.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Definitions from the specification *)

Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

Example problem_163_test :
  problem_163_spec 2 10 [2;4;6;8].
Proof.
  unfold problem_163_spec.
  split.
  - intros d.
    split.
    + (* -> direction *)
      intros H_in.
      simpl in H_in.
      repeat match goal with
             | [ H : In ?x (?y :: ?l) |- _ ] => destruct H as [H | H]; [subst|]
             end; try contradiction; clear H_in.
      all: repeat split; try lia.
      all: now apply Even_double_spec.
    + (* <- direction *)
      intros [Hmin [Hmax [Hlt Heven]]].
      (* We want to prove d ∈ [2;4;6;8] *)
      assert (d = 2 \/ d = 4 \/ d = 6 \/ d = 8).
      {
        (* d >= 2, d <= 10, d < 10, so d ≤ 9 *)
        assert (d <= 9) by lia.
        destruct d eqn:Ed.
        - lia.
        - destruct d eqn:Ed1.
          + lia.
          + destruct d eqn:Ed2.
            * lia.
            * destruct d eqn:Ed3.
              -- lia.
              -- destruct d eqn:Ed4.
                 ++ lia.
                 ++ destruct d eqn:Ed5.
                    ** lia.
                    ** destruct d eqn:Ed6.
                       --- lia.
                       --- destruct d eqn:Ed7.
                           +++ lia.
                           +++ destruct d eqn:Ed8.
                                *** lia.
                                *** lia.
      }
      destruct H as [-> | [-> | [-> | ->]]]; simpl; auto.
  - split.
    + (* Sorted le [2;4;6;8] *)
      repeat constructor; lia.
    + (* NoDup [2;4;6;8] *)
      repeat constructor; congruence.
Qed.