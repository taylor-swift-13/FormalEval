Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 12 [2; 3; 5; 7; 11].
Proof.
  unfold count_up_to_spec.
  split.
  - intros x H_in.
    simpl in H_in.
    destruct H_in as [H | [H | [H | [H | [H | H]]]]]; subst.
    + split. lia. intros d Hd. lia.
    + split. lia. intros d Hd. assert (d = 2) by lia. subst. simpl. discriminate.
    + split. lia. intros d Hd. assert (d = 2 \/ d = 3 \/ d = 4) as [-> | [-> | ->]] by lia; simpl; discriminate.
    + split. lia. intros d Hd. assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as [-> | [-> | [-> | [-> | ->]]]] by lia; simpl; discriminate.
    + split. lia. intros d Hd. assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]] by lia; simpl; discriminate.
    + contradiction.
  - intros x H_bound H_prime.
    assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11) as H_cases by lia.
    destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + simpl. left. reflexivity.
    + simpl. right. left. reflexivity.
    + exfalso. specialize (H_prime 2). simpl in H_prime. apply H_prime; lia.
    + simpl. right. right. left. reflexivity.
    + exfalso. specialize (H_prime 2). simpl in H_prime. apply H_prime; lia.
    + simpl. right. right. right. left. reflexivity.
    + exfalso. specialize (H_prime 2). simpl in H_prime. apply H_prime; lia.
    + exfalso. specialize (H_prime 3). simpl in H_prime. apply H_prime; lia.
    + exfalso. specialize (H_prime 2). simpl in H_prime. apply H_prime; lia.
    + simpl. right. right. right. right. left. reflexivity.
Qed.