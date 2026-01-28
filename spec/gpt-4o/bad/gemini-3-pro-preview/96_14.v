Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 17 [2; 3; 5; 7; 11; 13].
Proof.
  unfold count_up_to_spec.
  split.
  - intros x H_in.
    repeat (destruct H_in as [H_eq | H_in]; [ subst x | ]).
    + split; [lia | intros d Hd; lia].
    + split; [lia | intros d Hd; do 3 (destruct d; try lia); simpl; discriminate].
    + split; [lia | intros d Hd; do 5 (destruct d; try lia); simpl; discriminate].
    + split; [lia | intros d Hd; do 7 (destruct d; try lia); simpl; discriminate].
    + split; [lia | intros d Hd; do 11 (destruct d; try lia); simpl; discriminate].
    + split; [lia | intros d Hd; do 13 (destruct d; try lia); simpl; discriminate].
    + contradiction.
  - intros x H_bound H_prime.
    do 17 (destruct x; try lia).
    + simpl; auto.
    + simpl; auto.
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
    + simpl; auto.
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
    + simpl; auto.
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
    + exfalso. specialize (H_prime 3). apply H_prime; [lia | reflexivity].
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
    + simpl; auto.
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
    + simpl; auto.
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
    + exfalso. specialize (H_prime 3). apply H_prime; [lia | reflexivity].
    + exfalso. specialize (H_prime 2). apply H_prime; [lia | reflexivity].
Qed.