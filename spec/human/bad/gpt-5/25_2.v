Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_25_pre (input : nat) : Prop := True.

Definition problem_25_spec (input : nat) (output : list nat) : Prop :=
  Sorted le output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.

Example problem_25_test : problem_25_spec 4 [2;2].
Proof.
  split.
  - constructor.
    + constructor.
      * constructor.
      * constructor.
    + constructor.
  - split.
    + simpl. reflexivity.
    + constructor.
      * unfold IsPrime.
        split.
        { lia. }
        { intros d H.
          destruct d as [|d].
          - simpl in H. discriminate.
          - destruct d as [|d].
            + simpl in H. left. reflexivity.
            + destruct d as [|d].
              * simpl in H. right. reflexivity.
              * assert (2 < S (S (S d))) by lia.
                rewrite Nat.mod_small in H by assumption.
                discriminate.
        }
      * constructor.
        - unfold IsPrime.
          split.
          { lia. }
          { intros d H.
            destruct d as [|d].
            - simpl in H. discriminate.
            - destruct d as [|d].
              + simpl in H. left. reflexivity.
              + destruct d as [|d].
                * simpl in H. right. reflexivity.
                * assert (2 < S (S (S d))) by lia.
                  rewrite Nat.mod_small in H by assumption.
                  discriminate.
          }
        - constructor.
Qed.