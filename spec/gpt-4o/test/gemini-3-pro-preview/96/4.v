Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition count_up_to_spec (n : nat) (ans : list nat) : Prop :=
  (forall x, In x ans -> 2 <= x < n /\ (forall d, 2 <= d < x -> x mod d <> 0)) /\
  (forall x, 2 <= x < n -> (forall d, 2 <= d < x -> x mod d <> 0) -> In x ans).

Example test_case : count_up_to_spec 10 [2; 3; 5; 7].
Proof.
  unfold count_up_to_spec.
  split.
  
  (* Part 1: Prove that all elements in [2; 3; 5; 7] are primes < 10 *)
  - intros x H_in.
    simpl in H_in.
    destruct H_in as [H2 | [H3 | [H5 | [H7 | H_absurd]]]].
    
    (* Case x = 2 *)
    + subst x.
      split.
      * lia.
      * intros d H_range. lia.
        
    (* Case x = 3 *)
    + subst x.
      split.
      * lia.
      * intros d H_range.
        assert (d = 2) by lia. subst d.
        simpl. discriminate.

    (* Case x = 5 *)
    + subst x.
      split.
      * lia.
      * intros d H_range.
        assert (d = 2 \/ d = 3 \/ d = 4) as H_d by lia.
        destruct H_d as [? | [? | ?]]; subst d; simpl; discriminate.

    (* Case x = 7 *)
    + subst x.
      split.
      * lia.
      * intros d H_range.
        assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as H_d by lia.
        destruct H_d as [? | [? | [? | [? | ?]]]]; subst d; simpl; discriminate.
        
    (* Case False *)
    + contradiction.

  (* Part 2: Prove that all primes < 10 are in [2; 3; 5; 7] *)
  - intros x H_bound H_prime.
    assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) as H_cases by lia.
    destruct H_cases as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    
    (* x = 2 *)
    + subst x. simpl. auto.
      
    (* x = 3 *)
    + subst x. simpl. auto.
      
    (* x = 4 (composite) *)
    + subst x.
      exfalso.
      specialize (H_prime 2).
      apply H_prime; [lia | reflexivity].

    (* x = 5 *)
    + subst x. simpl. auto.

    (* x = 6 (composite) *)
    + subst x.
      exfalso.
      specialize (H_prime 2).
      apply H_prime; [lia | reflexivity].

    (* x = 7 *)
    + subst x. simpl. auto.

    (* x = 8 (composite) *)
    + subst x.
      exfalso.
      specialize (H_prime 2).
      apply H_prime; [lia | reflexivity].

    (* x = 9 (composite) *)
    + subst x.
      exfalso.
      specialize (H_prime 3).
      apply H_prime; [lia | reflexivity].
Qed.