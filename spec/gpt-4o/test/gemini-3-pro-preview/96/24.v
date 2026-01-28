Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 13 [2; 3; 5; 7; 11].
Proof.
  unfold count_up_to_spec.
  split.
  
  - intros x H_in.
    simpl in H_in.
    destruct H_in as [H | [H | [H | [H | [H | H]]]]].
    
    + subst x. split. lia.
      intros d Hd. lia.
      
    + subst x. split. lia.
      intros d Hd. assert (d = 2) by lia.
      subst. simpl. discriminate.

    + subst x. split. lia.
      intros d Hd. 
      assert (d = 2 \/ d = 3 \/ d = 4) as H_cases by lia.
      repeat (destruct H_cases as [H_eq | H_cases]; [subst; simpl; discriminate | ]).
      subst. simpl. discriminate.

    + subst x. split. lia.
      intros d Hd.
      assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_cases by lia.
      repeat (destruct H_cases as [H_eq | H_cases]; [subst; simpl; discriminate | ]).
      subst. simpl. discriminate.

    + subst x. split. lia.
      intros d Hd.
      assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) as H_cases by lia.
      repeat (destruct H_cases as [H_eq | H_cases]; [subst; simpl; discriminate | ]).
      subst. simpl. discriminate.

    + contradiction.

  - intros x H_bound H_prime.
    assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12) as H_cases by lia.
    destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]].
    
    + simpl. left. reflexivity.
    
    + simpl. right. left. reflexivity.
    
    + exfalso. specialize (H_prime 2).
      assert (2 <= 2 < 4) by lia.
      apply H_prime in H. simpl in H. contradiction.
      
    + simpl. right. right. left. reflexivity.
    
    + exfalso. specialize (H_prime 2).
      assert (2 <= 2 < 6) by lia.
      apply H_prime in H. simpl in H. contradiction.
      
    + simpl. right. right. right. left. reflexivity.
    
    + exfalso. specialize (H_prime 2).
      assert (2 <= 2 < 8) by lia.
      apply H_prime in H. simpl in H. contradiction.
      
    + exfalso. specialize (H_prime 3).
      assert (2 <= 3 < 9) by lia.
      apply H_prime in H. simpl in H. contradiction.
      
    + exfalso. specialize (H_prime 2).
      assert (2 <= 2 < 10) by lia.
      apply H_prime in H. simpl in H. contradiction.
      
    + simpl. right. right. right. right. left. reflexivity.
    
    + exfalso. specialize (H_prime 2).
      assert (2 <= 2 < 12) by lia.
      apply H_prime in H. simpl in H. contradiction.
Qed.